use pyo3::{types::PyInt, IntoPy, PyErr, PyObject, Python};

use crate::{substitute::RewriteError, LinkError, NodeIndex, PortIndex};

impl From<PyInt> for NodeIndex {
    fn from(x: PyInt) -> Self {
        Self::new(x.extract().unwrap())
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

impl std::convert::From<LinkError> for PyErr {
    fn from(s: LinkError) -> Self {
        pyo3::exceptions::PyRuntimeError::new_err(s.to_string())
    }
}

impl std::convert::From<RewriteError> for PyErr {
    fn from(s: RewriteError) -> Self {
        pyo3::exceptions::PyRuntimeError::new_err(s.to_string())
    }
}
