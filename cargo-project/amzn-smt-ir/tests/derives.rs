#![allow(dead_code)]

use amzn_smt_ir::{
    fold::{Fold, Folder, SuperFold},
    visit::{SuperVisit, Visit, Visitor},
    Logic, Operation,
};

macro_rules! foldable {
    ($t:ident<$($param:ident),*>) => {
        impl<$($param),*> $t<$($param),*> {
            fn fold<L: Logic<Op = Self>>(self, mut folder: impl Folder<L>) {
                let _ = self.fold_with(&mut folder);
            }
            fn super_fold<L: Logic, Out>(self, mut folder: impl Folder<L, Output = Out>)
            where
                $($param: Fold<L, Out>),*
            {
                let _ = self.super_fold_with(&mut folder);
            }
        }
    };
}

macro_rules! visitable {
    ($t:ident<$($param:ident),*>) => {
        impl<$($param),*> $t<$($param),*> {
            fn super_visit<L: Logic>(&self, mut visitor: impl Visitor<L>)
            where
                Self: Visit<L>,
                $($param: Visit<L>),*
            {
                let _ = self.super_visit_with(&mut visitor);
            }
        }
    };
}

#[derive(Operation, Fold, Visit)]
enum One<A> {
    A(A),
}
foldable!(One<A>);
visitable!(One<A>);

#[derive(Operation, Fold, Visit)]
enum Two<A, B> {
    A(A),
    B(B),
}
foldable!(Two<A, B>);
visitable!(Two<A, B>);

#[derive(Operation, Fold, Visit)]
enum TwoReversed<A, B> {
    B(B),
    A(A),
}
foldable!(TwoReversed<A, B>);
visitable!(TwoReversed<A, B>);

#[derive(Operation, Fold, Visit)]
enum Pair<A, B> {
    A(A, B),
}
foldable!(Pair<A, B>);
visitable!(Pair<A, B>);
