## Quickstart

Audience: Users with no prior codebase knowledge.

When to use: You want to parse a small belief base, construct a `PreOCF`, compute ranks, and check a few conditionals within minutes.

What you'll learn:
- Parse belief bases and queries using `parser.Wrappers`
- Create a `PreOCF` (System Z)
- Compute ranks and check conditional acceptance

Prerequisites:
- Installed dev environment per `INSTALL.md`

Steps:
1) Parse a tiny belief base and queries
2) Build a `PreOCF` with System Z
3) Compute ranks and inspect a few worlds
4) Check conditional acceptance

Example code:

```python
{%
   include "../../show_preocf_minimal.py"
   start="[docs:quickstart-minimal:start]"
   end="[docs:quickstart-minimal:end]"
%}
```

Notes:
- The code above is included from `show_preocf_minimal.py` (single source of truth).
- For details, see API: `inference.preocf.PreOCF`, `parser.Wrappers`.
