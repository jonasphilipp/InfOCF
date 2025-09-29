## Facts and Consistency Diagnostics

Goal: Use System Z extended mode with facts and interpret diagnostics.

You will:
- Initialize System Z with/without facts with extended partitioning
- Inspect partitions/layers
- Run and interpret `consistency_diagnostics`

Snippets (planned to be included from `show_preocf.py`):

### Extended System Z partition (no facts)
```python
# Will include from ../../show_preocf.py once markers exist:
# [docs:diagnostics:extended-no-facts:start] ... :end
```

### System Z with facts (examples A–E)
Note: Handling facts requires extended partitioning. Use `PreOCF.init_system_z(..., facts=[...], extended=True)`.
```python
# Will include from ../../show_preocf.py once markers exist:
# [docs:diagnostics:with-facts:start] ... :end
```

References: `PreOCF.init_system_z(..., extended=True)`, `consistency_diagnostics`, `format_diagnostics`.
