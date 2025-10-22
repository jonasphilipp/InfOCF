# API Reference

Welcome to the InfOCF API documentation. This library provides comprehensive support for reasoning with conditional belief bases using various non-monotonic inference operators.

## Quick Start

For most users, the main entry point is the [`InferenceManager`](api/inference.md#inference.inference_manager.InferenceManager) class:

```python
from inference.inference_manager import InferenceManager
from parser.Wrappers import parse_belief_base, parse_queries

# Option 1: Parse from files (recommended for complex examples)
belief_base = parse_belief_base("path/to/belief_base.ckb")
queries = parse_queries("path/to/queries.cl")

# Option 2: Parse from strings (useful for quick testing)
belief_base = parse_belief_base("signature\\na,b\\n\\nconditionals\\nkb{(a|b)}")
queries = parse_queries("(b|a)")

# Create inference manager and run queries
manager = InferenceManager(belief_base, "system-z")
results = manager.inference(queries)
```

## API Structure

### Core Components
- **[InferenceManager](api/inference.md#inference.inference_manager.InferenceManager)**: Main interface for inference operations
- **[Parser Wrappers](api/parser.md)**: Input parsing and validation
- **[PreOCF](api/preocf.md)**: Preprocessing and optimization

### Inference Systems
- **P-Entailment**
- **System Z**
- **C-Inference**
- **System W**
- **Lexicographic Inference**

## Main Package

::: infocf
