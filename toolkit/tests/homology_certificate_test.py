import numpy as np

def boundary1_matrix():
    return np.array([
        [1, 0, 1],
        [1, 1, 0]
    ]) % 2

def boundary2_matrix():
    return np.array([
        [1],
        [1],
        [1]
    ]) % 2

def rank_f2(M):
    M = M.copy() % 2
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        pivot = None
        for i in range(r, rows):
            if M[i, c] == 1:
                pivot = i
                break
        if pivot is None:
            continue
        M[[r, pivot]] = M[[pivot, r]]
        for i in range(rows):
            if i != r and M[i, c] == 1:
                M[i] ^= M[r]
        r += 1
    return r

def nullity_f2(M):
    return M.shape[1] - rank_f2(M)

def test_h1_certificate():
    d1 = boundary1_matrix()
    d2 = boundary2_matrix()

    z1 = nullity_f2(d1)
    b1 = rank_f2(d2)
    h1 = z1 - b1

    assert h1 == 0, f"H1 expected 0, got {h1}"

def test_boundary_squared_zero():
    d1 = boundary1_matrix()
    d2 = boundary2_matrix()
    assert np.all((d1 @ d2) % 2 == 0), "∂1∘∂2 ≠ 0"

if __name__ == "__main__":
    test_boundary_squared_zero()
    test_h1_certificate()
    print("PASS: homology certificates verified")
