"""Semantic roles. Preserve each role's meaning across every scene.

Adapted from the role-based aivm-secrets visualization system.
Colors are **presentation only**: status must also be written in text.
"""

from __future__ import annotations

DARK = {
    "background": "#0B1422",
    "surface": "#152638",
    "surface_soft": "#132132",
    "foreground": "#EFF6FB",
    "muted": "#B1C0CD",
    "guest": "#64C9F2",       # untrusted inputs / guest observer
    "broker": "#6FE0B7",      # host-controlled broker
    "provider": "#F7C06D",    # remote provider
    "secret": "#F27F8A",      # protected credential, forbidden release
    "policy": "#AF9EF7",      # manifest / current grant / selection
    "proved": "#78DBA9",      # scoped theorem
    "assumed": "#F4C474",     # environmental premise
    "open": "#FF947D",        # correspondence still open
    "neutral": "#C9D5E2",
}

LIGHT = {
    "background": "#F7FAFC",
    "surface": "#FFFFFF",
    "surface_soft": "#EBF2F8",
    "foreground": "#182B3C",
    "muted": "#576D7F",
    "guest": "#087CAA",
    "broker": "#14826B",
    "provider": "#9F6104",
    "secret": "#B4364A",
    "policy": "#6F50C4",
    "proved": "#137B51",
    "assumed": "#9A6307",
    "open": "#A33C32",
    "neutral": "#546D7D",
}

ROLES = frozenset(DARK) - {"background", "surface", "surface_soft", "foreground", "muted"}


def palette(theme: str = "dark") -> dict[str, str]:
    if theme == "dark":
        return DARK
    if theme == "light":
        return LIGHT
    raise ValueError(f"unknown theme {theme!r}; expected dark/light")
