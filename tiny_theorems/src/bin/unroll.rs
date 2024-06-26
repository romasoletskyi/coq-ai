use std::fs::File;
use std::io::{BufReader, BufWriter, ErrorKind, Write};
use std::path::Path;
use std::sync::Arc;

use anyhow::{bail, Result};

use tiny_theorems::{
    env::{Env, EnvError},
    solver::{print_state, ProofStep, State},
    theorem::{Theorem, TheoremParser},
};

fn print_step(step: &ProofStep, state: Arc<State>) -> Result<String> {
    let mut buf = BufWriter::new(Vec::new());
    print_state(&mut buf, &state)?;
    write!(buf, "{}", step)?;
    Ok(String::from_utf8(buf.into_inner()?)?)
}

fn unroll_theorem(env: &mut Env, theorem: &Theorem) -> Result<Vec<String>> {
    env.load_statement(&theorem.statement).unwrap();
    let mut states = Vec::new();
    for step in &theorem.proof {
        match step {
            ProofStep::Bullet(_) => {}
            _ => states.push(print_step(step, env.current_state().unwrap().clone())?),
        };
        env.step(step.clone())?;
    }
    if let Some(_) = env.current_state() {
        bail!(EnvError::UnsolvedGoals.to_string());
    } else {
        Ok(states)
    }
}

fn main() {
    let max_proof_length = 25;
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("dataset")
        .join("unroll.v");
    let mut file = BufWriter::new(File::create(path).unwrap());
    let mut env = Env::new();
    let mut counter = 0;

    for name in ["augletter.v"] {
        let original_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("dataset")
            .join(name);
        let mut original = BufReader::new(File::open(original_path).unwrap());
        let mut parser = TheoremParser::new(&mut original);

        loop {
            let result = parser.next();
            match &result {
                Err(e) => {
                    if let Some(io_err) = e.downcast_ref::<std::io::Error>() {
                        if io_err.kind() == ErrorKind::UnexpectedEof {
                            break;
                        }
                    }
                }
                _ => {}
            }
            if let Ok(theorem) = result {
                if theorem.proof.len() < max_proof_length {
                    if counter % 10 == 0 {
                        match unroll_theorem(&mut env, &theorem) {
                            Ok(steps) => {
                                writeln!(&mut file, "[THEOREM]").unwrap();
                                for step in steps {
                                    writeln!(&mut file, "{}", step).unwrap();
                                }
                            }
                            Err(err) => {
                                println!("{}", err);
                                env.reset();
                            }
                        }
                    }
                    counter += 1;
                }
            }
        }
    }
    println!("Collected {} theorems", counter / 10);
}

mod tests {
    use crate::unroll_theorem;
    use std::io::Cursor;
    use tiny_theorems::{env::Env, theorem::TheoremParser};

    fn check(data: &str) {
        let mut cursor = Cursor::new(data.as_bytes());
        let mut parser = TheoremParser::new(&mut cursor);
        let theorem = parser.next().unwrap();

        let mut env = Env::new();
        for state in unroll_theorem(&mut env, &theorem).unwrap() {
            println!("{}", state);
        }
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
