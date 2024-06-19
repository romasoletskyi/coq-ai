use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufReader, BufWriter, ErrorKind, Write};
use std::iter::zip;
use std::path::Path;

use rand::{seq::SliceRandom, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use tiny_theorems::{
    env::Env,
    gen::Statement,
    refiner::rename_statement,
    solver::{name_simple_hypothesis, unfold_expression, use_tactic, ProofStep},
    theorem::{Theorem, TheoremNameGenerator, TheoremParser},
};

fn generate_prop_symbols<R: Rng + ?Sized>(rng: &mut R, size: usize) -> Vec<char> {
    let mut props = Vec::new();
    for ch in 'A'..'[' {
        if ch != 'H' {
            props.push(ch);
        }
    }
    props.shuffle(rng);
    props[..size].to_vec()
}

fn augment<R: Rng + ?Sized>(rng: &mut R, theorem: &Theorem, name: String) -> Theorem {
    let props = generate_prop_symbols(rng, theorem.props.len());

    let mut map = HashMap::new();
    for (&a, &b) in zip(&theorem.props, &props) {
        map.insert(a, b);
    }

    let mut statement = rename_statement(&theorem.statement, &|x| *map.get(x).unwrap());
    let mut hyp_indices: Vec<_> = (0..statement.hyp.len()).collect();
    hyp_indices.shuffle(rng);
    statement.hyp = hyp_indices
        .iter()
        .map(|&x| statement.hyp[x].clone())
        .collect();
    statement = Statement::new(statement.to_expression());

    let mut hyp_map: HashMap<String, String> = HashMap::new();
    let mut proof = vec![];
    let mut namer = name_simple_hypothesis();
    let mut initial = true;
    let mut env = Env::new();
    env.load_statement(&statement).unwrap();

    for step in &theorem.proof {
        let step = match step {
            ProofStep::Bullet(level) => ProofStep::Bullet(*level),
            ProofStep::Apply(hyp) => {
                ProofStep::Apply(hyp_map.get(hyp).expect(&format!("{}", theorem)).clone())
            }
            ProofStep::Intros(intros) => {
                let state = env.current_state().unwrap();
                let (aug_intros, _) = unfold_expression(state.goal.clone());
                let mut names = Vec::new();
                for (i, aug_intro) in aug_intros.iter().enumerate() {
                    let name = namer(&aug_intro);
                    names.push(name.clone());
                    if initial {
                        hyp_map.insert(intros[hyp_indices[i]].clone(), name);
                    } else {
                        hyp_map.insert(intros[i].clone(), name);
                    }
                }
                if initial {
                    initial = false;
                }
                ProofStep::Intros(names)
            }
        };
        env.step(step.clone()).unwrap();
        proof.push(step);
    }

    Theorem::new(name, props, statement, proof)
}

fn main() {
    let max_proof_length = 25;
    let mut theorems = Vec::new();

    for name in ["letter3.v", "letter4.v", "letter5.v"] {
        let original_path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("dataset")
            .join(name);
        let mut original = BufReader::new(File::open(original_path).unwrap());
        let mut parser = TheoremParser::new(&mut original);

        let mut count = 0;
        loop {
            let result = parser.next();
            match &result {
                Err(e) => {
                    if let Some(io_err) = e.downcast_ref::<io::Error>() {
                        if io_err.kind() == ErrorKind::UnexpectedEof {
                            break;
                        }
                    }
                }
                _ => {}
            }

            if let Ok(theorem) = result {
                if theorem.proof.len() < max_proof_length {
                    theorems.push(theorem);
                }
                count += 1;
            }
        }
        println!("Processed {} theorems in file {}", count, name);
    }
    println!("Collected {} theorems", theorems.len());

    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("dataset")
        .join("augletter.v");
    let mut file = BufWriter::new(File::create(path).unwrap());

    let sample = 10;
    let mut name_gen = TheoremNameGenerator::new();
    let mut rng = ChaCha8Rng::from_entropy();

    for theorem in theorems {
        for _ in 0..sample {
            write!(
                &mut file,
                "{}",
                augment(&mut rng, &theorem, name_gen.generate_name())
            )
            .unwrap();
        }
    }
}

mod tests {
    use crate::augment;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;
    use std::io::Cursor;
    use tiny_theorems::theorem::TheoremParser;

    fn check(data: &str) {
        let mut cursor = Cursor::new(data.as_bytes());
        let mut parser = TheoremParser::new(&mut cursor);
        let theorem = parser.next().unwrap();

        let mut rng = ChaCha8Rng::from_entropy();
        println!("{}", augment(&mut rng, &theorem, "vjifjg".to_string()));
    }

    #[test]
    fn basic() {
        check("Theorem weofxf: forall (A B C : Prop), ((A -> B) -> B) -> ((A -> C) -> C) -> (A -> B) -> (B -> A -> C) -> (C -> B -> A) -> A.
        Proof.
        intros A B C. intros HABB HACC HAB HBAC HCBA. apply HCBA. 
          - apply HACC. intros HA. apply HBAC. 
            + apply HAB. apply HA. 
            + apply HA. 
          - apply HABB. intros HA0. apply HAB. apply HA0. 
        Qed.");
    }
}
