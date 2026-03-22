import numpy as np

def eigenvalues(n):
    # 4D Laplacian eigenvalue growth ~ i^{1/2}
    i = np.arange(1, n+1)
    return i**0.5

def hs_sum(n, mass=0.0):
    lam = eigenvalues(n)
    if mass > 0:
        return np.sum(1.0/(lam + mass**2))
    return np.sum(1.0/lam)

def run(n=1_000_000):
    s0 = hs_sum(n, mass=0.0)
    s1 = hs_sum(n, mass=1.0)
    print({"n": n, "no_mass": float(s0), "with_mass": float(s1)})

if __name__ == "__main__":
    run()
