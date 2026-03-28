# Minimal test for Integer Descent Bound (simulation)

def phi(T):
    return T["phi"]

def step(T):
    if T["phi"] == 0:
        return T
    return {"phi": T["phi"] - 1}

def run_test():
    T = {"phi": 10}
    seen = [phi(T)]
    for _ in range(20):
        T = step(T)
        seen.append(phi(T))
        if phi(T) == 0:
            print("PASS: reached zero defect")
            return True
    print("FAIL: did not terminate")
    return False

if __name__ == "__main__":
    run_test()
