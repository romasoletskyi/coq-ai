use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::iter::zip;
use std::path::Path;

use rand::{seq::SliceRandom, Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use tiny_theorems::{
    theorem::{Theorem, TheoremNameGenerator, TheoremParser}, 
    refine::rename_statement, 
    solver::{ProofStep, State, name_simple_hypothesis, unfold_expression, use_tactic}, gen::Statement,
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
    statement.hyp = hyp_indices.iter().map(|&x| statement.hyp[x].clone()).collect();
    statement = Statement::new(statement.to_expression());

    let mut hyp_map: HashMap<String, String> = HashMap::new();
    let mut proof = vec![];
    let mut states = vec![State::new(statement.goal.clone())];
    let mut namer = name_simple_hypothesis();
    let mut initial = true;

    for step in &theorem.proof {
        let state = states.pop().unwrap();
        let step = match step {
            ProofStep::Bullet(level) => ProofStep::Bullet(*level),
            ProofStep::Apply(hyp) => ProofStep::Apply(hyp_map.get(hyp).unwrap().clone()),
            ProofStep::Intros(intros) => {
                let (map_intros, _) = unfold_expression(state.goal.clone());
                let mut names = Vec::new();
                for (i, map_intro) in map_intros.iter().enumerate() {
                    let name = namer(&map_intro);
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
        if let Some(tactic) = step.clone().into() {
            for state in use_tactic(&state, &tactic).unwrap().into_iter().rev() {
                states.push((*state).clone());
            }
        } else {
            states.push(state);
        }
        proof.push(step);
    }    

    Theorem::new(name, props, statement, proof)
}

fn main() {
    let original_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("dataset")
        .join("letter3.v");
    let mut original = File::open(original_path).unwrap();

    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("dataset")
        .join("augletter3.v");
    let mut file = File::create(path).unwrap();

    let sample = 100;
    let mut parser = TheoremParser::new(&mut original);
    let mut name_gen = TheoremNameGenerator::new();
    let mut rng = ChaCha8Rng::from_entropy();

    while let Ok(theorem) = parser.next() {
        for _ in 0..sample {
            write!(
                &mut file,
                "{}",
                augment(&mut rng, &theorem, name_gen.generate_name())
            ).unwrap();
        }
    }
}
