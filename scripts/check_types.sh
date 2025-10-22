#!/bin/bash
echo "=== Checking types ==="
uv run mypy inference/preocf.py --show-error-codes | tee mypy_current.txt
ERROR_COUNT=$(grep "error:" mypy_current.txt | wc -l)
echo "=== Error count: $ERROR_COUNT ==="
uv run pytest unittests/test_preocf*.py -q
