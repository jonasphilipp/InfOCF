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
Note: When facts are provided, System Z automatically uses extended partitioning (unless you explicitly pass `extended=False`). You typically do not need to set `extended=True` yourself.

Current behavior: facts are represented by adding weak constraints of the form `(Bottom|¬φ)` to the belief base. If the augmented base is inconsistent, initialization raises immediately with verbose diagnostics; the diagnostics are also saved in metadata under `consistency_diagnostics`.
```python
# Will include from ../../show_preocf.py once markers exist:
# [docs:diagnostics:with-facts:start] ... :end
```

References: `PreOCF.init_system_z(..., extended=True)`, `consistency_diagnostics`, `format_diagnostics`.
