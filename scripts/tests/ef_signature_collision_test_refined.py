import random
from collections import defaultdict

def random_signature(R=3, Delta=3, T=10):
    B_size = sum(Delta**i for i in range(R+1))
    frontier = random.randint(1, min(5, B_size))
    tau = tuple(sorted(random.randint(0, T-1) for _ in range(frontier)))
    shape = tuple(random.randint(0, 2) for _ in range(min(6, B_size)))
    return (frontier, tau, shape)

def run(trials=5_000_000):
    seen = {}
    collisions = 0
    for i in range(trials):
        sig = random_signature()
        if sig in seen:
            collisions += 1
        else:
            seen[sig] = 1
        if i % 500_000 == 0 and i > 0:
            print({"i": i, "collisions": collisions, "ratio": collisions/max(1,i)})
    print({"trials": trials, "collisions": collisions, "ratio": collisions/max(1,trials)})

if __name__ == "__main__":
    run()
