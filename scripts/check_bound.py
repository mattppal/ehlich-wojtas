#!/usr/bin/env python3
"""Check the Ehlich–Wojtas numerical bound and the n=2 case."""

from __future__ import annotations

import itertools
import sys


def ew_bound(n: int) -> int:
    if n % 4 != 2:
        raise ValueError(f"n ≡ 2 (mod 4) required, got {n}")
    return (2 * n - 2) * (n - 2) ** (n // 2 - 1)


def det2(a, b, c, d) -> int:
    return a * d - b * c


def check_formula() -> None:
    assert ew_bound(2) == 2, ew_bound(2)
    assert ew_bound(6) == 160, ew_bound(6)
    assert ew_bound(10) == 73728, ew_bound(10)


def check_n2() -> None:
    vals = (1, -1)
    max_abs = 0
    for a, b, c, d in itertools.product(vals, repeat=4):
        max_abs = max(max_abs, abs(det2(a, b, c, d)))
    assert max_abs == 2, max_abs


def main() -> int:
    check_formula()
    check_n2()
    print("bound formula and n=2 enumeration OK")
    print("  n=2 ->", ew_bound(2))
    print("  n=6 ->", ew_bound(6))
    print("  n=10 ->", ew_bound(10))
    return 0


if __name__ == "__main__":
    sys.exit(main())
