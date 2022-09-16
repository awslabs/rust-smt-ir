use aws_smt_ir::{logic::*, Script, Term};

#[test]
fn main() {
    let smt = include_str!("../../benches/mathsat/FISCHER11-16-fair.smt2");
    let script = Script::<Term<QF_LIA>>::parse(smt.as_bytes()).unwrap();
    let mut num_terms = 0;
    for _ in script {
        num_terms += 1;
    }
    println!("{}", num_terms);
}
