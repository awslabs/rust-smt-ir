// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    args,
    fold::{Fold, InterLogicFolder, SuperFold},
    model::{DefineFun, Model},
    CoreOp, Ctx, FreshVarError, ILet, IOp, IQuantifier, ISort, ISymbol, IVar, Logic,
    QualIdentifier, Script, Sorted, Symbol, Term, UnknownSort, Void, IUF, UF,
};
use itertools::Itertools;
use std::collections::HashMap;

struct Ackermannizer<'a, U: Logic> {
    ctx: &'a mut Ctx,
    uf_vars: HashMap<UF<Term<U>>, MappedApplication<U>>,
    arg_vars: HashMap<Term<U>, IVar<U::Var>>,
}

struct MappedApplication<U: Logic> {
    arg_sorts: Vec<ISort>,
    sort: ISort,
    corresponding_var: IVar<U::Var>,
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum AckermannizationError<T: Logic, U: Logic> {
    #[error(transparent)]
    FreshVar(#[from] FreshVarError),
    #[error(transparent)]
    UnknownSort(#[from] UnknownSort<Term<U>>),
    #[error("Ackermannization cannot handle quantifiers: {0}")]
    Quantifier(IQuantifier<T>),
}

impl<'a, U: Logic<Var = QualIdentifier>> Ackermannizer<'a, U> {
    fn new(ctx: &'a mut Ctx) -> Self {
        Self {
            ctx,
            uf_vars: Default::default(),
            arg_vars: Default::default(),
        }
    }

    fn purify_arg<T: Logic>(&mut self, t: Term<U>) -> Result<Term<U>, AckermannizationError<T, U>> {
        Ok(match t {
            Term::Constant(..) | Term::Variable(..) => t,
            _ => {
                use std::collections::hash_map::Entry;
                match self.arg_vars.entry(t) {
                    Entry::Occupied(entry) => entry.get().into(),
                    Entry::Vacant(entry) => {
                        let sort = entry.key().sort(self.ctx)?;
                        let var = self.ctx.fresh_var(sort)?;
                        entry.insert(var).clone().into()
                    }
                }
            }
        })
    }

    fn reconstruct_uninterpreted_funcs(
        uf_vars: HashMap<UF<Term<U>>, MappedApplication<U>>,
        arg_vars: HashMap<Term<U>, IVar<QualIdentifier>>,
        model: Model<U>,
    ) -> Model<U> {
        let substs: Vec<_> = (model.defns())
            .map(|defn| {
                debug_assert!(
                    defn.args.is_empty(),
                    "Ackermannization eliminates uninterpreted functions"
                );
                (defn.sym.clone(), defn.body.clone())
            })
            .collect();

        let mut uf_vars: HashMap<_, _> = uf_vars
            .into_iter()
            .map(|(t, data)| {
                (
                    data.corresponding_var.sym().clone(),
                    (data.arg_sorts, data.sort, t),
                )
            })
            .collect();
        let arg_vars: HashMap<_, _> = arg_vars.iter().map(|(t, v)| (v.sym(), t)).collect();
        let mut uf_piecewise_defns: HashMap<_, HashMap<_, _>> = HashMap::new();
        let mut defns = vec![];

        for defn in model.into_defns() {
            if let Some((arg_sorts, sort, uf)) = uf_vars.remove(&defn.sym) {
                let outputs = uf_piecewise_defns
                    .entry((uf.func, arg_sorts, sort))
                    .or_default();
                let args: Vec<_> = (Vec::from(uf.args).into_iter())
                    .map(|t| t.substitute(&substs))
                    .collect();
                let body = defn.body.substitute(&substs);
                outputs.insert(args, body);
            } else if !arg_vars.contains_key(&defn.sym) {
                defns.push(defn);
            }
        }

        let params = (0..)
            .map(|x| format!("x!{}", x))
            .map(|x| ISymbol::from(Symbol(x)));
        let uf_defns = uf_piecewise_defns
            .into_iter()
            .map(|((func, arg_sorts, sort), outputs)| {
                let mut outputs = outputs.into_iter();
                let first = outputs.next().unwrap().1;
                let body = outputs.fold(first, |e, (args, out)| {
                    let args_match = CoreOp::And(
                        (params.clone().zip(args))
                            .map(|(param, arg)| {
                                Term::from(CoreOp::Eq(args![
                                    IVar::from(QualIdentifier::from(param)).into(),
                                    arg,
                                ]))
                            })
                            .collect(),
                    )
                    .into();
                    CoreOp::Ite(args_match, out, e).into()
                });
                DefineFun {
                    sym: func.sym().clone(),
                    args: params.clone().zip(arg_sorts).collect(),
                    sort,
                    body: body.substitute(&substs),
                }
            });
        defns.into_iter().chain(uf_defns).collect()
    }
}

impl<T, U> InterLogicFolder<T> for Ackermannizer<'_, U>
where
    T: Logic<UninterpretedFunc = UF<Term<T>>, Var = QualIdentifier>,
    U: Logic<Var = QualIdentifier>,
    Void: Into<IUF<U>>,
    T::Op: SuperFold<T, Term<U>, Output = U::Op>,
{
    type Error = AckermannizationError<T, U>;
    type U = U;

    fn context(&self) -> Option<&Ctx> {
        Some(self.ctx)
    }

    fn context_mut(&mut self) -> Option<&mut Ctx> {
        Some(self.ctx)
    }

    fn fold_uninterpreted_func(&mut self, uf: IUF<T>) -> Result<Term<U>, Self::Error> {
        let mut uf = uf.super_fold_with(self)?;
        uf.args = (Vec::from(uf.args).into_iter())
            .map(|arg| self.purify_arg(arg))
            .collect::<Result<_, _>>()?;
        use std::collections::hash_map::Entry;
        let ctx = &mut self.ctx;
        let var = match self.uf_vars.entry(uf) {
            Entry::Occupied(entry) => entry.get().corresponding_var.clone(),
            Entry::Vacant(entry) => {
                let arg_sorts = entry
                    .key()
                    .args
                    .iter()
                    .map(|t| t.sort(ctx))
                    .collect::<Result<_, _>>()?;
                let sort = entry.key().sort(ctx)?;
                let var = ctx.fresh_var(sort.clone())?;
                entry.insert(MappedApplication {
                    arg_sorts,
                    sort,
                    corresponding_var: var.clone(),
                });
                var
            }
        };
        Ok(var.into())
    }

    fn fold_var(&mut self, var: IVar<T::Var>) -> Result<Term<Self::U>, Self::Error> {
        Ok(var.into())
    }

    fn fold_theory_op(&mut self, op: IOp<T>) -> Result<Term<Self::U>, Self::Error> {
        op.super_fold_with(self).map(Into::into)
    }

    fn fold_let(&mut self, l: ILet<T>) -> Result<Term<Self::U>, Self::Error> {
        l.term.clone().substitute(&l.bindings).fold_with(self)
    }

    fn fold_quantifier(
        &mut self,
        quantifier: IQuantifier<T>,
    ) -> Result<Term<Self::U>, Self::Error> {
        Err(AckermannizationError::Quantifier(quantifier))
    }
}

pub fn ackermannize<T, U>(
    ctx: &mut Ctx,
    script: Script<Term<T>>,
) -> Result<(Script<Term<U>>, impl FnOnce(Model<U>) -> Model<U>), AckermannizationError<T, U>>
where
    T: Logic<UninterpretedFunc = UF<Term<T>>, Var = QualIdentifier>,
    U: Logic<Var = QualIdentifier>,
    Void: Into<IUF<U>>,
    T::Op: SuperFold<T, Term<U>, Output = U::Op>,
{
    let mut folder = Ackermannizer::<U>::new(ctx);
    let mut script = script.try_fold(&mut folder)?;
    let grouped = folder
        .uf_vars
        .iter()
        .into_group_map_by(|(op, data)| (&op.func, &data.arg_sorts, &data.sort));
    let uf_constraints = grouped.iter().flat_map(|(_, applications)| {
        applications
            .iter()
            .map(|(uf, data)| (uf, &data.corresponding_var))
            .tuple_combinations::<(_, _)>()
            .map(|((uf_a, var_a), (uf_b, var_b))| {
                // a = b => f(a) = f(b)
                let args_eq = (uf_a.args.iter().cloned())
                    .zip(uf_b.args.iter().cloned())
                    .map(|(a, b)| CoreOp::Eq([a, b].into()).into())
                    .collect();
                let out_eq = CoreOp::Eq([var_a.into(), var_b.into()].into()).into();
                Term::from(CoreOp::Imp([CoreOp::And(args_eq).into(), out_eq].into()))
            })
    });
    let new_constraints = (folder.arg_vars.iter())
        .map(|(t, var)| Term::from(CoreOp::Eq([t.clone(), var.into()].into())))
        .chain(uf_constraints);
    script.add_asserts(new_constraints);
    let (uf_vars, arg_vars) = (folder.uf_vars, folder.arg_vars);
    Ok((script, |model| {
        Ackermannizer::reconstruct_uninterpreted_funcs(uf_vars, arg_vars, model)
    }))
}

#[cfg(test)]
mod test {
    use super::*;
    use aws_smt_ir::{Logic, QualIdentifier, Script, Term, Void, UF};

    #[allow(non_camel_case_types)]
    #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
    struct QF;

    impl Logic for QF {
        type Var = QualIdentifier;
        type Op = Void;
        type Quantifier = Void;
        type UninterpretedFunc = Void;
    }

    #[allow(non_camel_case_types)]
    #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
    struct QF_UF;

    impl Logic for QF_UF {
        type Var = QualIdentifier;
        type Op = Void;
        type Quantifier = Void;
        type UninterpretedFunc = UF<Term<Self>>;
    }

    #[test]
    fn ackermannization() {
        let smt = "
            (declare-fun f (Bool) Bool)
            (declare-const x Bool)
            (declare-const y Bool)
            (declare-const z Bool)
            (assert (and (= y (f z)) (= x (f (f z))) (not (= x (f y)))))
        ";
        let script = Script::<Term<QF_UF>>::parse(smt.as_bytes()).unwrap();
        let (script, _) = ackermannize::<_, QF>(&mut Ctx::default(), script).unwrap();
        // TODO: actually test something
        println!("{}", script);
    }
}
