## C-Revision Overview

Goal: Revise an existing ranking with new conditionals using `c_revision` and compare to c-representation.

You will:
- Build revision conditionals (with indices)
- Run `c_revision` with and without gamma_plus
- Compare gamma_minus to c-representation impacts (eta)
- Optionally: fix one gamma entry; incremental compilation

### C-revision basic flow

```python
{%
   include "../../scripts/show_preocf.py"
   start="[docs:c-revision:basic:start]"
   end="[docs:c-revision:basic:end]"
%}
```

### Fixed gamma showcase

```python
{%
   include "../../scripts/show_preocf.py"
   start="[docs:c-revision:fixed-gamma:start]"
   end="[docs:c-revision:fixed-gamma:end]"
%}
```

### Incremental compilation

```python
{%
   include "../../scripts/show_preocf.py"
   start="[docs:c-revision:incremental:start]"
   end="[docs:c-revision:incremental:end]"
%}
```

Notes:
- May require optional solver dependencies; keep snippets small.
- See API: `inference.c_revision`, `inference.c_revision_model`.
