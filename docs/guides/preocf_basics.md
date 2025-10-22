## PreOCF Basics

Goal: Understand ranks, world encoding, verbose views, and total preorders.

You will:
- Create a `PreOCF` (System Z)
- Compute some ranks and all ranks
- View ranks in verbose form and convert ranks ↔ TPO

### Create System Z and compute some ranks

```python
{%
   include "../../show_preocf.py"
   start="[docs:preocf-basics:system-z:start]"
   end="[docs:preocf-basics:system-z:end]"
%}
```

### Compute all ranks and verbose representation

```python
{%
   include "../../show_preocf.py"
   start="[docs:preocf-basics:verbose:start]"
   end="[docs:preocf-basics:verbose:end]"
%}
```

### Convert ranks to total preorder (TPO)

```python
{%
   include "../../show_preocf.py"
   start="[docs:preocf-basics:tpo:start]"
   end="[docs:preocf-basics:tpo:end]"
%}
```

References: API docs for `PreOCF`, `ranks2tpo`, `tpo2ranks`.
