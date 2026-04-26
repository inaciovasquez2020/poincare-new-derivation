from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Sequence


@dataclass(frozen=True)
class DescentCertificate:
    theorem_id: str
    status: str
    initial_height: int
    final_height: int
    step_count: int
    strictly_descending: bool
    bound_respected: bool


def _height(value: int) -> int:
    value = int(value)
    if value < 0:
        raise ValueError("height must be a nonnegative integer")
    return value


def is_strict_descent_step(before: int, after: int) -> bool:
    return _height(after) < _height(before)


def is_strict_descent_chain(heights: Sequence[int]) -> bool:
    if not heights:
        raise ValueError("height chain must be nonempty")
    checked = [_height(h) for h in heights]
    return all(checked[i + 1] < checked[i] for i in range(len(checked) - 1))


def descent_length_bound(initial_height: int) -> int:
    return _height(initial_height)


def verify_descent_chain(heights: Sequence[int]) -> DescentCertificate:
    if not heights:
        raise ValueError("height chain must be nonempty")
    checked = [_height(h) for h in heights]
    strictly_descending = is_strict_descent_chain(checked)
    step_count = max(0, len(checked) - 1)
    initial_height = checked[0]
    final_height = checked[-1]
    return DescentCertificate(
        theorem_id="PND-CDT-1",
        status="PASS" if strictly_descending and step_count <= initial_height else "FAIL",
        initial_height=initial_height,
        final_height=final_height,
        step_count=step_count,
        strictly_descending=strictly_descending,
        bound_respected=step_count <= initial_height,
    )


def terminal_height(heights: Iterable[int]) -> int:
    checked = [_height(h) for h in heights]
    if not checked:
        raise ValueError("height chain must be nonempty")
    if not is_strict_descent_chain(checked):
        raise ValueError("chain is not strictly descending")
    return checked[-1]
