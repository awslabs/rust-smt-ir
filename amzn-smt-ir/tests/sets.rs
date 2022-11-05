use amzn_smt_ir::{logic::*, Command as IRCommand, CoreOp, Script, Term};

type IRTerm = Term<ALL>;
// type IRUF = UF<ALL>;

fn parse_term(t: &Term) {
    println!("The parsed term is: {t:?}");
    match t {
        Term::CoreOp(i) => {
            println!("Term {i:?} is a CoreOp");
            match i.as_ref() {
                CoreOp::Eq(args) => {
                    println!("Eq args are: {args:?}");
                    parse_term(&args[1]);
                }
                _ => {}
            }
        }
        Term::UF(iuf) => {
            let uf = iuf.as_ref();
            let fs = &uf.func;
            let args = &uf.args;
            println!("Uninterpreted function: {fs:?} has args {args:?}")
        }
        Term::OtherOp(i) => {
            let ir = i.as_ref();
            println!("Term {ir:?} is an OtherOp");
            match i.as_ref() {
                all::Op::String(s) => {
                    println!("String operation term is: {s:?}");
                }
                all::Op::Set(x) => {
                    println!("Set operation term is: {x:?}");
                    //parse_term(t);
                }
                _ => {}
            }
        }
        Term::Constant(_c) => {
            println!("Term is a constant");
        }
        Term::Variable(i) => {
            println!("Term is a variable");
            let iv = i.as_ref();
            let sym = iv.sym();
            let indices = iv.indices();
            println!("IV: {iv:?}, sym: {sym:?}, indices: {indices:?}");
        }
        Term::Let(_il) => {
            println!("Term is a let binding");
        }
        Term::Match(_im) => {
            println!("Term is a match.");
        }
        Term::Quantifier(_q) => {
            println!("Term is a quantifier");
        }
    }
}

#[test]
fn test_cvc5_set_parsing() {
    let smt: &str = include_str!("../../benches/set_types.cvc5.smt2");
    let script: Script<IRTerm> = Script::<IRTerm>::parse(smt.as_bytes()).unwrap();
    println!("The script that was read is: {:?}", script);
    for i in script.into_iter() {
        println!("The command is: {:?}", i);
        match i {
            IRCommand::Assert { term: t } => {
                parse_term(&t);
            }
            _ => {}
        }
    }
}
