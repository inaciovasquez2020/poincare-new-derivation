import random

def random_signature(R=3, Delta=3, T=20):
    B_size = sum(Delta**i for i in range(R+1))
    frontier = random.randint(1, min(6, B_size))
    tau = tuple(sorted(random.randint(0, T-1) for _ in range(frontier)))
    shape = tuple(random.randint(0, 3) for _ in range(min(8, B_size)))
    boundary_order = tuple(random.sample(range(1000), frontier))
    adjacency_pattern = tuple((i, (i+1)%frontier) for i in range(frontier)) if frontier > 1 else ()
    return (frontier, tau, shape, boundary_order, adjacency_pattern)

def run(trials=5_000_000):
    seen = set()
    collisions = 0
    for i in range(trials):
        sig = random_signature()
        if sig in seen:
            collisions += 1
        else:
            seen.add(sig)
        if i % 500_000 == 0 and i > 0:
            print({"i": i, "collisions": collisions, "ratio": collisions/max(1,i)})
    print({"trials": trials, "collisions": collisions, "ratio": collisions/max(1,trials)})

if __name__ == "__main__":
    run()
