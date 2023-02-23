// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use proc_macro2::{Span, TokenStream};
use quote::quote;
use std::collections::HashSet;
use syn::{parse_quote, DeriveInput};
use synstructure::decl_derive;

decl_derive!([Fold] => derive_fold);
decl_derive!([Visit] => derive_visit);
decl_derive!([Operation, attributes(core_op, symbol)] => derive_operation_all);

/// Gets the path to the `amzn-smt-ir` crate, returning `crate` in case it is the current crate.
fn smt_ir_crate_path() -> syn::Path {
    match proc_macro_crate::crate_name("amzn-smt-ir").expect("must depend on amzn-smt-ir") {
        proc_macro_crate::FoundCrate::Itself => parse_quote!(aws_smt_ir),
        proc_macro_crate::FoundCrate::Name(name) => {
            let name = syn::Ident::new(&name, proc_macro2::Span::call_site());
            parse_quote!(#name)
        }
    }
}

/// Determines whether `input` is annotated with the `#[core_op]` attribute.
fn has_core_op_attr(input: &DeriveInput) -> bool {
    input.attrs.iter().any(|a| a.path.is_ident("core_op"))
}

// Determine a variant's symbol (its representation in SMT-LIB) -- either the lowercased name of
// the variant or the contents of an attached `symbol` attribute, if present e.g. `#[symbol("=>")]`.
fn variant_symbol(variant: &synstructure::VariantInfo) -> syn::LitStr {
    let ast = variant.ast();
    (ast.attrs.iter())
        .find(|attr| attr.path.is_ident("symbol"))
        .and_then(|attr| attr.parse_args().ok())
        .unwrap_or_else(|| {
            let name = ast.ident.to_string().to_lowercase();
            parse_quote!(#name)
        })
}

/// Derives `Debug`, `Display`, and `Operation` for an operator enum e.g. `Foo<Term>`
/// and `From` for `Op`.
fn derive_operation_all(mut s: synstructure::Structure) -> TokenStream {
    s.add_bounds(synstructure::AddBounds::None)
        .bind_with(|_| synstructure::BindStyle::Move);
    let debug = derive_fmt_any(&s, parse_quote!(std::fmt::Debug));
    let display = derive_fmt_any(&s, parse_quote!(std::fmt::Display));
    let from = derive_from(&s);
    let operation = derive_operation(&s);
    let iterate = derive_iterate(&s);
    quote! {
        #debug
        #display
        #from
        #operation
        #iterate
    }
}

fn index_array(ty: &syn::Type) -> Option<&syn::Expr> {
    match ty {
        syn::Type::Array(syn::TypeArray { len, .. }) => Some(len),
        _ => None,
    }
}

/// Derives an `Operation` implementation for an operator.
fn derive_operation(s: &synstructure::Structure) -> TokenStream {
    let smt_ir = smt_ir_crate_path();

    #[allow(non_snake_case)]
    let (Term, Logic, Operation, Parse, NumArgs, InvalidOp, QualIdentifier, IIndex, TryFrom, Vec) = (
        quote!(#smt_ir::Term),
        quote!(#smt_ir::Logic),
        quote!(#smt_ir::term::Operation),
        quote!(#smt_ir::term::args::Parse),
        quote!(#smt_ir::term::args::NumArgs),
        quote!(#smt_ir::term::InvalidOp),
        quote!(#smt_ir::QualIdentifier),
        quote!(#smt_ir::IIndex),
        quote!(std::convert::TryFrom),
        quote!(std::vec::Vec),
    );

    let mut bindings = vec![];

    let parse_match_arms: Vec<_> = (s.variants().iter())
        .enumerate()
        .map(|(idx, variant)| {
            let symbol = variant_symbol(variant);
            let mut num_indices = None;
            let mut min_args = vec![];
            let mut max_args = vec![];

            // For each field in the variant, try to parse it from the iterator of arguments
            let constructed = variant.construct(|field, _| {
                let ty = &field.ty;

                // Check for array of indices
                if let Some(len) = index_array(ty) {
                    num_indices = Some(len.clone());
                    quote! {{
                        let indices: std::vec::Vec<_> = func.indices().iter().map(#IIndex::from).collect();
                        #TryFrom::try_from(indices).unwrap()
                    }}
                } else {
                    min_args.push(quote!(<#ty as #NumArgs>::MIN_ARGS));
                    max_args.push(quote!(<#ty as #NumArgs>::MAX_ARGS));
                    quote!(#Parse::from_iter(&mut iter).unwrap())
                }
            });

            let min_args = quote!((0 #(+ #min_args)*));
            let max_args = quote!((0 #(+ #max_args)*));
            let num_indices = num_indices.unwrap_or_else(|| parse_quote!(0));
            let min_args_ident = syn::Ident::new(&format!("MIN_ARGS_{}", idx), Span::call_site());
            let max_args_ident = syn::Ident::new(&format!("MAX_ARGS_{}", idx), Span::call_site());
            let num_indices_ident = syn::Ident::new(&format!("INDICES_{}", idx), Span::call_site());
            bindings.push(quote!(let #min_args_ident = #min_args;));
            bindings.push(quote!(let #max_args_ident = #max_args;));
            bindings.push(quote!(let #num_indices_ident = #num_indices;));

            // Construct a match arm e.g. `"and" => { ... }` where `...` constructs the variant from
            // a slice of arguments.
            quote! {
                (#symbol, num_args) if func.indices().len() == #num_indices_ident && (#min_args_ident..=#max_args_ident).contains(&num_args) => {
                    let mut iter = args.into_iter();
                    #constructed
                }
            }
        })
        .collect();

    let parse_fn = quote! {
        fn parse(func: #QualIdentifier, args: #Vec<#Term<L>>) -> std::result::Result<Self, #InvalidOp<L>> {
            #(#bindings)*
            #[deny(unreachable_patterns)]
            Ok(match (func.sym_str(), args.len()) {
                #(#parse_match_arms)*
                _ => return Err(#InvalidOp { func, args })
            })
        }
    };

    let func_match_arms = s.each_variant(|variant| {
        let symbol = variant_symbol(variant);
        quote!(#symbol.into())
    });

    let func_fn = quote! {
        fn func(&self) -> #smt_ir::ISymbol {
            match self {
                #func_match_arms
            }
        }
    };

    let mut where_clause = None;
    s.add_trait_bounds(
        &parse_quote!(#Parse<L>),
        &mut where_clause,
        synstructure::AddBounds::Fields,
    );
    if has_core_op_attr(s.ast()) {
        s.gen_impl(quote! {
            gen impl<L: #Logic> #Operation<L> for @Self
            #where_clause,
                <L as #Logic>::Op: #Operation<L>,
            {
                #parse_fn
                #func_fn
            }
        })
    } else {
        s.gen_impl(quote! {
            gen impl<L: #Logic> #Operation<L> for @Self #where_clause {
                #parse_fn
                #func_fn
            }
        })
    }
}

fn bound_argument_fields(
    s: &synstructure::Structure,
    clause: &mut syn::WhereClause,
    mut bound: impl FnMut(&syn::Type) -> syn::WherePredicate,
) {
    let mut seen = HashSet::new();

    for variant in s.variants() {
        for binding in variant.bindings() {
            let ty = &binding.ast().ty;
            if seen.insert(ty) && index_array(ty).is_none() {
                clause.predicates.push(bound(ty));
            }
        }
    }
}

/// Derives an `Iterate` implementation for an operator.
fn derive_iterate(s: &synstructure::Structure) -> TokenStream {
    let smt_ir = smt_ir_crate_path();

    #[allow(non_snake_case)]
    let (Term, Logic, Iterate, Args) = (
        quote!(#smt_ir::Term),
        quote!(#smt_ir::Logic),
        quote!(#smt_ir::term::args::Iterate),
        quote!(#smt_ir::term::args::Arguments),
    );

    fn argument_iter_branches(
        s: &synstructure::Structure,
        mut iterate: impl FnMut(&synstructure::BindingInfo) -> TokenStream,
    ) -> TokenStream {
        s.each_variant(|v| {
            let mut bindings = (v.bindings().iter())
                .skip_while(|field| index_array(&field.ast().ty).is_some())
                .map(&mut iterate);
            let mut iter = bindings
                .next()
                .unwrap_or_else(|| quote!(std::iter::empty()));
            for new in bindings {
                iter = quote!(#iter.chain(#new))
            }
            // TODO: instead of boxing, could also make an enum -- might be worth it
            quote!(std::boxed::Box::new(#iter))
        })
    }

    let mut where_clause = syn::WhereClause {
        where_token: Default::default(),
        predicates: Default::default(),
    };

    bound_argument_fields(
        s,
        &mut where_clause,
        |ty| parse_quote!(#ty: #Iterate<'a, L>),
    );

    let args_branches = argument_iter_branches(s, |field| quote!(#Iterate::<L>::terms(#field)));
    let into_args_branches =
        argument_iter_branches(s, |field| quote!(#Iterate::<L>::into_terms(#field)));

    s.gen_impl(quote! {
        gen impl<'a, L: #Logic> #Iterate<'a, L> for @Self
        #where_clause
        {
            type Terms = std::boxed::Box<dyn std::iter::Iterator<Item = &'a #Term<L>> + 'a>;
            type IntoTerms = std::boxed::Box<dyn std::iter::Iterator<Item = #Term<L>> + 'a>;

            fn terms(&'a self) -> Self::Terms {
                match self {
                    #args_branches
                }
            }

            fn into_terms(self) -> Self::IntoTerms {
                match self {
                    #into_args_branches
                }
            }
        }

        gen impl<'a, L: #Logic> #Args<'a, L> for @Self #where_clause {}
    })
}

/// Derives a `Debug` or `Display` implementation for an operator enum depending on the trait path
/// passed as `trait_path`.
fn derive_fmt_any(s: &synstructure::Structure, trait_path: syn::Path) -> TokenStream {
    let smt_ir = smt_ir_crate_path();

    #[allow(non_snake_case)]
    let Format = quote!(#smt_ir::term::args::Format);

    let fmt_body = s.each_variant(|variant| {
        let symbol = variant_symbol(variant);
        let bindings = variant.bindings();
        if bindings.is_empty() {
            quote!(std::write!(f, #symbol))
        } else {
            let mut fmt_indices = None;
            let fmt_fields: Vec<_> = bindings
                .iter()
                .filter_map(|field| {
                    if index_array(&field.ast().ty).is_some() {
                        fmt_indices = Some(quote! {
                            for index in #field {
                                std::write!(f, " {}", index)?;
                            }
                        });
                        None
                    } else {
                        Some(quote! {
                            std::write!(f, " ")?;
                            #Format::fmt(#field, f, #trait_path::fmt)
                        })
                    }
                })
                .collect();
            let fmt_func = if let Some(fmt_indices) = fmt_indices {
                quote! {
                    std::write!(f, "(_ {}", #symbol)?;
                    #fmt_indices
                    std::write!(f, ")")
                }
            } else {
                quote!(std::write!(f, #symbol))
            };
            quote! {
                std::write!(f, "(")?;
                #fmt_func?;
                #(#fmt_fields?;)*
                std::write!(f, ")")
            }
        }
    });

    let mut where_clause = None;
    s.add_trait_bounds(
        &parse_quote!(std::fmt::Debug),
        &mut where_clause,
        synstructure::AddBounds::Generics,
    );
    s.add_trait_bounds(
        &parse_quote!(std::fmt::Display),
        &mut where_clause,
        synstructure::AddBounds::Generics,
    );
    s.add_trait_bounds(
        &parse_quote!(#Format),
        &mut where_clause,
        synstructure::AddBounds::Generics,
    );
    s.gen_impl(quote! {
        extern crate std;
        gen impl #trait_path for @Self #where_clause {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    #fmt_body
                }
            }
        }
    })
}

/// Derives `Fold` and `SuperFold` for an operator enum e.g. `Foo<Term>`.
fn derive_fold(mut s: synstructure::Structure) -> TokenStream {
    let smt_ir = smt_ir_crate_path();
    let name = &s.ast().ident; // E.g. `Foo`

    #[allow(non_snake_case)]
    let (Logic, Fold, SuperFold, Folder) = (
        quote!(#smt_ir::Logic),
        quote!(#smt_ir::fold::Fold),
        quote!(#smt_ir::fold::SuperFold),
        quote!(#smt_ir::fold::Folder),
    );

    s.add_bounds(synstructure::AddBounds::None)
        .bind_with(|_| synstructure::BindStyle::Move);

    let impl_fold = s.gen_impl(quote! {
        extern crate std;
        gen impl<L: #Logic<Op = Self>, Out> #Fold<L, Out> for @Self {
            type Output = Out;

            fn fold_with<F, M>(
                self,
                folder: &mut F,
            ) -> std::result::Result<Self::Output, F::Error>
            where
                F: #Folder<L, M, Output = Out>,
            {
                folder.fold_theory_op(self.into())
            }
        }
    });

    let impl_super_fold = {
        // Bound each generic parameter to implement `Fold`
        let mut where_clause = None;
        s.add_trait_bounds(
            &parse_quote!(#Fold<L, Out>),
            &mut where_clause,
            synstructure::AddBounds::Generics,
        );

        // For each variant, construct a new version by folding each of the fields
        let body = s.each_variant(|vi| {
            vi.construct(|_, idx| {
                let field = &vi.bindings()[idx];
                quote!(#Fold::fold_with(#field, folder)?)
            })
        });

        // If input type is `Foo<A, B>`, output `Foo<<A as Fold>::Output, <B as Fold>::Output>`
        let out_params = s
            .referenced_ty_params()
            .into_iter()
            .map(|ty| quote!(<#ty as #Fold<L, Out>>::Output));

        s.gen_impl(quote! {
            extern crate std;
            gen impl<L: #Logic, Out> #SuperFold<L, Out> for @Self #where_clause {
                type Output = #name<#(#out_params),*>;

                fn super_fold_with<F, M>(
                    self,
                    folder: &mut F,
                ) -> std::result::Result<Self::Output, F::Error>
                where
                    F: #Folder<L, M, Output = Out>,
                {
                    Ok(match self { #body })
                }
            }
        })
    };

    quote! {
        #impl_fold
        #impl_super_fold
    }
}

/// For a given operator `O`, derives `From<O>` for `Op`.
fn derive_from(s: &synstructure::Structure) -> TokenStream {
    let smt_ir = smt_ir_crate_path();
    let name = &s.ast().ident;
    let params = s.referenced_ty_params();
    let ty = quote!(#name<#(#params),*>);

    #[allow(non_snake_case)]
    let (From, Into, Logic, IOp, Term) = (
        quote!(std::convert::From),
        quote!(std::convert::Into),
        quote!(#smt_ir::Logic),
        quote!(#smt_ir::IOp),
        quote!(#smt_ir::Term),
    );

    if has_core_op_attr(s.ast()) {
        quote! {
            // impl<#(#params,)* L: #Logic> #From<#ty> for #Term<L> {
            //     fn from(op: #ty) -> Self {
            //         Self::CoreOp(op)
            //     }
            // }
        }
    } else {
        quote! {
            impl<#(#params,)* L: #Logic> #From<#ty> for #IOp<L>
            where
                #ty: #Into<L::Op>,
            {
                fn from(op: #ty) -> Self {
                    #IOp::new(op.into())
                }
            }
            impl<#(#params,)* L: #Logic> #From<#ty> for #Term<L>
            where
                #ty: #Into<L::Op>,
            {
                fn from(op: #ty) -> Self {
                    let op: L::Op = op.into();
                    Self::OtherOp(op.into())
                }
            }
        }
    }
}

/// Derives `Visit` and `SuperVisit` for an operator enum e.g. `Foo<Term>`.
fn derive_visit(mut s: synstructure::Structure) -> TokenStream {
    let smt_ir = smt_ir_crate_path();

    #[allow(non_snake_case)]
    let (Logic, Visit, SuperVisit, Visitor, ControlFlow) = (
        quote!(#smt_ir::Logic),
        quote!(#smt_ir::visit::Visit),
        quote!(#smt_ir::visit::SuperVisit),
        quote!(#smt_ir::visit::Visitor),
        quote!(#smt_ir::visit::ControlFlow),
    );

    s.add_bounds(synstructure::AddBounds::None);

    let impl_super_visit = {
        // Bound each field to implement `Visit`
        let mut where_clause = None;
        s.add_trait_bounds(
            &parse_quote!(#Visit<L>),
            &mut where_clause,
            synstructure::AddBounds::Fields,
        );

        // For each variant, visit each of the fields
        let body = s.each(|field| quote!(#smt_ir::try_break!(#Visit::visit_with(#field, visitor))));

        s.gen_impl(quote! {
            gen impl<L: #Logic> #SuperVisit<L> for @Self #where_clause {
                fn super_visit_with<V: #Visitor<L>>(
                    &self,
                    visitor: &mut V,
                ) -> #ControlFlow<V::BreakTy> {
                    match self { #body }
                    #ControlFlow::Continue(())
                }
            }
        })
    };

    quote! {
        #impl_super_visit
    }
}
