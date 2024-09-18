## Tiny theorems

Generator of propositional logic theorems with proofs in Coq and a notebook to train a transformer to write proofs for these theorems.

### Instructions

1. Generate propositional logic theorems with `cargo run --bin gen_massive`. Change path name if needed. Line `let symbols = generate_prop_symbols(4);` in `bin/gen_massive.rs` means that 4 symbols are used.
2. Augment them with `cargo run --bin augment`.
3. Unroll each theorem into <state, tactic> pairs using `cargo run --bin unroll`.
4. You can check neural network generations with `cargo run --bin bench`.

### Generation algorithm

1. Start from obvious A -> A
2. Mutate by adding new hypothesis A -> (A -> B) -> (B -> C) -> A
3. Mutate final goal to something provable A -> (A -> B) -> (B -> C) -> C
4. Find shortest proof of new statement
5. Perform evolutionary selection by choosing statements with longer proofs
6. Normalize statement and remove duplicates

It's possible to generate millions of 4,5-letter statements with this algorithm. 

### Training results

There are two modes of the dataset. Mode A is a usual theorem with proof in Coq. Mode B is an unrolled theorem consisting of <state, tactic> pairs. For better generalization, we augment dataset by renaming letters and bound number of proof steps per theorem to be not more than 25. We train 1.6M transformer on these datasets and get 1@pass rate for closing the theorem to be 32% for Mode A vs 97% for Mode B. A possible hypothesis is that it's hard for the transformer to keep track of state in deep theorems and doing it automatically in Mode B greatly helps. Choosing the right tactic is a much simpler problem in this setting than tracking the current proof state.

