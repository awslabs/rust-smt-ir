use amzn_smt_ir::{logic::*, Script, Term};

#[test]
fn test_cvc5_set_parsing() {
    let smt: &str = include_str!("../../benches/set_types.cvc5.smt2");
    let script: Script<Term<ALL>> = Script::<Term<ALL>>::parse(smt.as_bytes()).unwrap();
    println!("The script that was read is: {}", script);
}
