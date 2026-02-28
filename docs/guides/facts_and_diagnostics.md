## Facts and Consistency Diagnostics

Goal: Use System Z extended mode with facts and interpret diagnostics.

You will:
- Initialize System Z with/without facts with extended partitioning
- Inspect partitions/layers
- Run and interpret `consistency_diagnostics`

### Extended System Z partition (no facts)

*Source: [`scripts/show_preocf.py`](../../scripts/show_preocf.py)*

```python
{%
   include "../../scripts/show_preocf.py"
   start="[docs:diagnostics:extended-no-facts:start]"
   end="[docs:diagnostics:extended-no-facts:end]"
%}
```

### System Z with facts (examples A–E)

*Source: [`scripts/show_preocf.py`](../../scripts/show_preocf.py)*

Note: When facts are provided, System Z automatically uses extended partitioning (unless you explicitly pass `extended=False`). You typically do not need to set `extended=True` yourself.

Current behavior: facts are represented by adding weak constraints of the form `(Bottom|¬φ)` to the belief base. If the augmented base is inconsistent, initialization raises immediately with verbose diagnostics; the diagnostics are also saved in metadata under `consistency_diagnostics`.

```python
{%
   include "../../scripts/show_preocf.py"
   start="[docs:diagnostics:with-facts:start]"
   end="[docs:diagnostics:with-facts:end]"
%}
```

References: `PreOCF.init_system_z(..., extended=True)`, `consistency_diagnostics`, `format_diagnostics`.
