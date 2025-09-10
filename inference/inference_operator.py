# inference_operator.py
"""
Backwards compatibility module for InferenceOperator.

This module provides the old InferenceOperator interface while delegating
to the new InferenceManager implementation.

TODO: Remove this file after full migration to InferenceManager.
"""

import warnings

from inference.inference_manager import (
    InferenceManager as _InferenceManager,
)
from inference.inference_manager import (
    create_epistemic_state,
    create_inference_instance,
)


class InferenceOperator(_InferenceManager):
    """
    Deprecated: Use InferenceManager instead.

    This class is provided for backwards compatibility only.
    Please migrate to using InferenceManager directly.
    """

    def __init__(self, *args, **kwargs):
        warnings.warn(
            "InferenceOperator is deprecated. Use InferenceManager instead.",
            DeprecationWarning,
            stacklevel=2,
        )
        super().__init__(*args, **kwargs)


# Also emit a warning when the module is imported
warnings.warn(
    "The 'inference.inference_operator' module is deprecated. "
    "Use 'inference.inference_manager' and 'InferenceManager' instead.",
    DeprecationWarning,
    stacklevel=2,
)

__all__ = [
    "InferenceOperator",
    "create_epistemic_state",
    "create_inference_instance",
]
