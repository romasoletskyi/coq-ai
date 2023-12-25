use std::fs::{File, OpenOptions};
use std::io::{BufWriter, Read, Write};
use std::path::Path;
use std::sync::mpsc;
use std::thread;

use tiny_theorems::gen::{
    generate_prop_symbols, Mutator, Statement, StatementBank, StatementGenerator, TheoremPrinter,
    UniqueStatement,
};
use tiny_theorems::parser::{parse, tokenize};
use tiny_theorems::refine::NormalStatement;
use tiny_theorems::utility::share;

fn parse_theorems(data: &str) -> Vec<(String, Statement)> {
    let mut theorems = Vec::new();
    for line in data.split('\n') {
        if line.starts_with("Theorem") {
            let (head, body) = line.split_once(',').expect(line);
            let name = head.split_once(':').unwrap().0.split_once(' ').unwrap().1;

            let tokens = tokenize(body.trim_start().trim_end_matches('.')).unwrap();
            let expr = parse(&tokens).unwrap();
            let statement = NormalStatement::new(Statement::new(expr));

            theorems.push((name.to_string(), statement.into()))
        }
    }
    theorems
}

fn main() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("dataset")
        .join("letter4.v");

    let mut printer = TheoremPrinter::new();
    let mut seen = StatementBank::new();

    if path.exists() {
        let mut file = File::open(path.clone()).unwrap();
        let mut buf = String::new();
        file.read_to_string(&mut buf).unwrap();

        let theorems = parse_theorems(&buf);
        for (name, statement) in theorems {
            printer.insert_name(name);
            seen.insert(&statement);
        }

        println!("Loaded {} theorems", seen.hashes.len());
    }

    let mut file = BufWriter::new(
        OpenOptions::new()
            .append(true)
            .create(true)
            .open(path)
            .unwrap(),
    );

    let sample = 10;
    let pool = 1000;
    let thread_num = 8;

    let symbols = generate_prop_symbols(4);
    let mut statements = vec![StatementGenerator::initalize_statement(&symbols)];

    let (output_sender, output_receiver) = mpsc::channel();
    let mut input_senders = Vec::new();
    let mut handles = Vec::new();

    for _ in 0..thread_num {
        let mut gen = StatementGenerator::new(
            symbols.clone(),
            2,
            Mutator::new(vec![0.2, 0.2, 0.2, 0.2, 0.1, 0.1], 0.5),
            0,
        );
        let output_sender = output_sender.clone();
        let (input_sender, input_receiver) = mpsc::channel::<Vec<_>>();
        input_senders.push(input_sender);

        handles.push(thread::spawn(move || {
            while let Ok(input) = input_receiver.recv() {
                let statements: Vec<_> = input
                    .into_iter()
                    .map(|x: UniqueStatement| x.into())
                    .collect();
                let mutated: Vec<(UniqueStatement, _)> = statements
                    .iter()
                    .flat_map(|statement| gen.mutate_statement(statement, sample))
                    .map(|(st, proof)| (st.into(), proof))
                    .collect();
                output_sender.send(mutated).unwrap();
            }
        }));
    }

    for _ in 0..1000 {
        let shared_statements = share(statements, thread_num);
        let workers = shared_statements.len();

        for i in 0..workers {
            input_senders[i]
                .send(
                    shared_statements[i]
                        .iter()
                        .map(|x| x.clone().into())
                        .collect(),
                )
                .unwrap();
        }
        let mut mutated: Vec<(Statement, _)> = output_receiver
            .iter()
            .take(workers)
            .flatten()
            .map(|(st, proof)| (st.into(), proof))
            .collect();

        mutated.sort_by(|a, b| {
            let pass_a = seen.contains(&a.0);
            let pass_b = seen.contains(&b.0);
            (pass_a, b.1.len()).cmp(&(pass_b, a.1.len()))
        });
        mutated.dedup_by(|a, b| a.0.eq(&b.0));

        let total_seen = seen.len();
        let cut_len = mutated.len().min(pool);

        for (statement, proof) in &mutated {
            if !seen.contains(statement) {
                seen.insert(statement);
                printer
                    .print(&mut file, &symbols, statement, proof)
                    .unwrap();
            }
        }

        print!("{} ", seen.len() - total_seen);
        std::io::stdout().flush().unwrap();

        statements = mutated[..cut_len]
            .iter()
            .map(|(statement, _)| statement)
            .cloned()
            .collect();
    }

    for sender in input_senders {
        drop(sender);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
