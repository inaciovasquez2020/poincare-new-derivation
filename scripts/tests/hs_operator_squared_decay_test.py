import numpy as np

def eigenvalues(n):
    i = np.arange(1, n+1)
    return i**0.5

def hs_sum_squared(n, mass=1.0):
    lam = eigenvalues(n)
    return np.sum(1.0 / (lam + mass**2)**2)

def run():
    for n in [10_000, 100_000, 1_000_000, 2_000_000]:
        val = hs_sum_squared(n, mass=1.0)
        print({"n": n, "hs_squared_sum": float(val)})

if __name__ == "__main__":
    run()
