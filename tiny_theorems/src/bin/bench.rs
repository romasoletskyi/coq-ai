use std::fs::File;
use std::io::{BufReader, ErrorKind};
use std::{collections::HashMap, path::Path};

use anyhow::{bail, Error, Result};

use tiny_theorems::{
    env::{Env, EnvError},
    theorem::{Theorem, TheoremParser},
};

fn check_theorem(env: &mut Env, theorem: &Theorem) -> Result<()> {
    env.load_statement(&theorem.statement).unwrap();
    for step in &theorem.proof {
        env.step(step.clone())?;
    }
    if let Some(_) = env.current_state() {
        bail!(EnvError::UnsolvedGoals.to_string());
    } else {
        Ok(())
    }
}

fn name_error(err: Error) -> String {
    let mut s = err.to_string();
    if s.starts_with("can't find hypothesis") {
        s = "can't find hypothesis".to_string();
    }
    s
}

fn main() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("dataset")
        .join("generated")
        .join("augtrain-repeat-3-big.v");
    let mut file = BufReader::new(File::open(path).unwrap());
    let mut parser = TheoremParser::new(&mut file);

    let mut env = Env::new();
    let mut fail = 0;
    let mut errors: HashMap<String, Vec<usize>> = HashMap::new();
    let mut theorems = Vec::new();

    loop {
        match parser.next() {
            Err(err) => {
                if let Some(io_err) = err.downcast_ref::<std::io::Error>() {
                    if io_err.kind() == ErrorKind::UnexpectedEof {
                        break;
                    }
                }
                errors
                    .entry(name_error(err))
                    .or_default()
                    .push(theorems.len());
                fail += 1;
                theorems.push(None);
            }
            Result::Ok(theorem) => {
                if let Err(err) = check_theorem(&mut env, &theorem) {
                    errors
                        .entry(name_error(err))
                        .or_default()
                        .push(theorems.len());
                    fail += 1;
                    env.reset();
                }
                theorems.push(Some(theorem));
            }
        }
    }

    println!(
        "Passed {} / {} theorems",
        theorems.len() - fail,
        theorems.len()
    );
    for (err, indices) in &errors {
        println!(
            "{} : {} {:?}",
            err,
            indices.len(),
            indices[..10.min(indices.len())].to_vec()
        );
    }

    let mut err_indices: Vec<usize> = Vec::new();
    for (_, indices) in &errors {
        err_indices.extend(indices);
    }
    err_indices.sort();
    println!("error indices {:?}", err_indices[..10].to_vec());
}

mod tests {
    use crate::check_theorem;
    use std::io::Cursor;
    use tiny_theorems::{env::Env, theorem::TheoremParser};

    fn check(data: &str) {
        let mut cursor = Cursor::new(data.as_bytes());
        let mut parser = TheoremParser::new(&mut cursor);
        let theorem = parser.next().unwrap();

        let mut env = Env::new();
        check_theorem(&mut env, &theorem).unwrap();
    }

    #[test]
    fn basic() {
        check("Theorem xdfqyj: forall (W D U B N : Prop), (W -> B -> D) -> ((D -> U) -> W) -> ((B -> D) -> W -> N) -> ((N -> D) -> U) -> (B -> D -> U) -> N.
        Proof.
        intros W D U B N. intros HWBD HDUW HBDWN HNDU HBDU. apply HBDWN. 
          - intros HB. apply HWBD. 
            + apply HDUW. intros HD. apply HBDU. 
              * apply HB. 
              * apply HD. 
            + apply HB. 
          - apply HDUW. intros HD0. apply HNDU. intros HN. apply HD0. 
        Qed.");
    }
}
