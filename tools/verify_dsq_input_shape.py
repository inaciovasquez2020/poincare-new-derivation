#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path

ROOTS = [Path("lean"), Path("Regge"), Path("Poincare")]
TOKENS = ["dSq", "volume_sq", "is_valid"]

def main() -> None:
    hits: list[str] = []
    for root in ROOTS:
        if not root.exists():
            continue
        for p in root.rglob("*.lean"):
            text = p.read_text(encoding="utf-8", errors="replace")
            for token in TOKENS:
                if token in text:
                    hits.append(f"{p}:{token}")

    if not hits:
        raise SystemExit("DSQ_INPUT_SHAPE_SPEC_MISSING")

    print("DSQ_INPUT_SHAPE_SURFACE_FOUND")
    for h in hits[:40]:
        print(h)

if __name__ == "__main__":
    main()
