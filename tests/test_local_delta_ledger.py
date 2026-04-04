def defect(d: int) -> int:
    return abs(d - 6)

def delta_phi_one_to_four(old4):
    a, b, c, d = old4
    return (
        (defect(a + 2) - defect(a))
        + (defect(b + 2) - defect(b))
        + (defect(c + 2) - defect(c))
        + (defect(d + 2) - defect(d))
        + defect(4)
    )

def delta_phi_two_to_three(old3, old2):
    p, q, r = old3
    u, v = old2
    return (
        (defect(p - 1) - defect(p))
        + (defect(q - 1) - defect(q))
        + (defect(r - 1) - defect(r))
        + (defect(u + 1) - defect(u))
        + (defect(v + 1) - defect(v))
    )

assert delta_phi_one_to_four((6, 6, 6, 6)) == 10
assert delta_phi_one_to_four((5, 6, 7, 8)) == 8
x = delta_phi_one_to_four((3, 4, 9, 10))
assert delta_phi_one_to_four((10, 9, 4, 3)) == x
assert delta_phi_one_to_four((4, 10, 3, 9)) == x

assert delta_phi_two_to_three((6, 6, 6), (6, 6)) == 5
assert delta_phi_two_to_three((5, 6, 7), (6, 8)) == 3
y = delta_phi_two_to_three((4, 8, 9), (5, 7))
assert delta_phi_two_to_three((9, 4, 8), (5, 7)) == y
assert delta_phi_two_to_three((4, 8, 9), (7, 5)) == y

print("PASS")
