# Documentation

## Build and serve docs locally

The documentation uses MkDocs (Material theme). Use uv to install tooling and run:

```bash
# Install dev tooling (MkDocs, theme, plugins)
uv sync --group dev

# Serve with live-reload (http://127.0.0.1:8000)
uv run mkdocs serve

# Build the static site into the `site/` directory
uv run mkdocs build
```

Notes:
- The site configuration is in `mkdocs.yml`.
- The docs homepage mirrors `README.md` via include-markdown.
