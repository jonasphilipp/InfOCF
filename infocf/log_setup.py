"""Centralized logging configuration for the InfoOCF project.

This module provides helper functions for configuring the global logging
infrastructure and retrieving loggers in a consistent way throughout the
code-base.

Usage
-----
>>> from infocf import get_logger, setup_logging
>>> setup_logging()  # typically once at program start-up
>>> logger = get_logger(__name__)
>>> logger.info("Hello from the logging system!")

The configuration honours the environment variable ``INFOCF_LOGLEVEL`` to
control the minimum emitted log level globally (defaults to ``INFO``).
"""

from __future__ import annotations

import logging
import logging.config
import os
from typing import Any, Dict, Optional

# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

_VALID_LEVELS = {
    "CRITICAL",
    "ERROR",
    "WARNING",
    "INFO",
    "DEBUG",
    "NOTSET",
}

_DEFAULT_FMT = "%(asctime)s - %(name)s - %(levelname)s - %(message)s"


def _default_config(base_level: str) -> Dict[str, Any]:
    """Generate a minimal dictConfig compatible configuration.

    Parameters
    ----------
    base_level:
        The root log level to set for the application.
    """
    return {
        "version": 1,
        "disable_existing_loggers": False,
        "formatters": {
            "standard": {
                "format": _DEFAULT_FMT,
            },
        },
        "handlers": {
            "console": {
                "class": "logging.StreamHandler",
                "formatter": "standard",
                "level": base_level,
            },
        },
        "root": {
            "level": base_level,
            "handlers": ["console"],
        },
    }


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

_configured: bool = False  # guard against multiple initialisations


def setup_logging(
    custom_config: Optional[Dict[str, Any]] = None, *, force: bool = False
) -> None:
    """Configure the logging system.

    This function should be called once early during program start-up. It is
    safe to call it multiple times; subsequent calls will be ignored unless
    *force* is set to ``True``.

    The *custom_config* argument allows callers to provide their own
    ``logging.dictConfig``-style dictionary. When *custom_config* is *None*, a
    sensible default configuration using a single *console* handler is
    applied.

    The environment variable ``INFOCF_LOGLEVEL`` may be used to override the
    root log level of both the default and custom configuration.
    """
    global _configured

    if _configured and not force:
        return

    # Determine the desired log level
    env_level = os.environ.get("INFOCF_LOGLEVEL", "INFO").upper()
    if env_level not in _VALID_LEVELS:
        env_level = "INFO"  # graceful fallback

    if custom_config is None:
        config = _default_config(env_level)
    else:
        # Copy user config to avoid mutating the original reference
        config = dict(custom_config)
        # Attempt to inject / override the root level if not explicitly set
        root_cfg = config.setdefault("root", {})
        root_cfg.setdefault("level", env_level)

    # Apply configuration
    logging.config.dictConfig(config)  # type: ignore[arg-type]
    _configured = True


def get_logger(name: Optional[str] = None) -> logging.Logger:  # noqa: D401
    """Return a logger with *name*, ensuring the system is initialised."""
    if not _configured:
        setup_logging()
    return logging.getLogger(name)


# Convenience: configure root logger automatically when module is imported by
# everyday scripts (but *after* allowing application code to override by
# calling setup_logging first).
if os.getenv("INFOCF_AUTO_LOG", "0") == "1":
    # Only auto-configure if explicitly requested to avoid surprises during
    # library usage or unit tests.
    setup_logging()
