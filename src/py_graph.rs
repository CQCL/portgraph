//! Python bindings for the crate's types.

use pyo3::prelude::PyAnyMethods;
use pyo3::{Bound, FromPyObject, PyAny, PyResult};
use pyo3::{IntoPy, PyErr, PyObject, Python};

use crate::{LinkError, NodeIndex, PortIndex};

impl<'py> FromPyObject<'py> for NodeIndex {
    fn extract_bound(x: &Bound<'py, PyAny>) -> PyResult<Self> {
        let index: usize = x.extract()?;
        Ok(Self::new(index))
    }
}

impl<'py> FromPyObject<'py> for PortIndex {
    fn extract_bound(x: &Bound<'py, PyAny>) -> PyResult<Self> {
        let index: usize = x.extract()?;
        Ok(Self::new(index))
    }
}

impl IntoPy<PyObject> for NodeIndex {
    fn into_py(self, py: Python<'_>) -> PyObject {
        self.index().into_py(py)
    }
}

impl IntoPy<PyObject> for PortIndex {
    fn into_py(self, py: Python<'_>) -> PyObject {
        self.index().into_py(py)
    }
}

impl From<LinkError> for PyErr {
    fn from(s: LinkError) -> Self {
        pyo3::exceptions::PyRuntimeError::new_err(s.to_string())
    }
}
