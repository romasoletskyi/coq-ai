use crate::{
    env,
    gen::Statement,
    parser::{parse, tokenize},
    solver::print_state,
    theorem::TheoremParser,
};
use pyo3::prelude::*;
use std::io::BufWriter;

#[pyclass]
pub struct Env {
    env: env::Env,
}

#[pymethods]
impl Env {
    #[new]
    pub fn new(data: &str) -> PyResult<Self> {
        let tokens = tokenize(&data)?;
        let expr = parse(tokens.as_slice())?;
        let statement = Statement::new(expr).into();
        let mut env = env::Env::new();
        env.load_statement(&statement)?;
        Ok(Env { env })
    }

    pub fn step(&mut self, data: &str) -> PyResult<()> {
        for step in TheoremParser::parse_tactic(data.trim_end_matches('.'))? {
            self.env.step(step)?;
        }
        Ok(())
    }

    pub fn current_state(&self) -> PyResult<Option<String>> {
        let mut buf = BufWriter::new(Vec::new());
        match self.env.current_state() {
            Some(state) => {
                print_state(&mut buf, state)?;
            },
            None => return Ok(None)
        }
        Ok(Some(String::from_utf8(buf.into_inner()?)?))
    }
}
