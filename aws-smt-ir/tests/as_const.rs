use aws_smt_ir::{logic::*, Script, Term};
type IRTerm = Term<ALL>;

#[test]
fn test_parse1() {
    let file: &str = include_str!("examples/test-coercion1.smt2");
    let script: Script<IRTerm> = Script::<IRTerm>::parse(file.as_bytes()).unwrap();
    for c in script.into_iter() {
        println!("Command: {c}")
    }
}

#[test]
fn test_parse2() {
    let file: &str = include_str!("examples/test-coercion2.smt2");
    let script: Script<IRTerm> = Script::<IRTerm>::parse(file.as_bytes()).unwrap();
    for c in script.into_iter() {
        println!("Command: {c}")
    }
}

#[test]
fn test_parse3() {
    let file: &str = include_str!("examples/test-coercion3.smt2");
    let script: Script<IRTerm> = Script::<IRTerm>::parse(file.as_bytes()).unwrap();
    for c in script.into_iter() {
        println!("Command: {c}")
    }
}

#[test]
fn test_parse4() {
    let file: &str = include_str!("examples/test-coercion4.smt2");
    let script: Script<IRTerm> = Script::<IRTerm>::parse(file.as_bytes()).unwrap();
    for c in script.into_iter() {
        println!("Command: {c}")
    }
}
