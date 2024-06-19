pub mod env;
pub mod gen;
pub mod parser;
pub mod pyenv;
pub mod refiner;
pub mod solver;
pub mod theorem;
pub mod utility;
pub mod valid;

use crate::pyenv::Env;
use pyo3::prelude::*;

#[pymodule]
fn tiny_theorems(_: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Env>()?;
    Ok(())
}
