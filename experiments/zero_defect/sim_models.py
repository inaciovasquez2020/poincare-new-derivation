import random

class Model:
    def __init__(self, name, uses_invariant):
        self.name = name
        self.uses_invariant = uses_invariant

    def decide_S3(self, Phi, invariant):
        if self.uses_invariant:
            return (Phi == 0 and invariant == 0)
        return (Phi == 0)

def sample():
    Phi = random.choice([0, 1])
    invariant = random.choice([0, 1])
    truth = (invariant == 0)
    return Phi, invariant, truth

def run(n=10000):
    baseline = Model("original", False)
    repaired = Model("invariant", True)
    stats = {
        baseline.name: {"correct": 0, "total": 0},
        repaired.name: {"correct": 0, "total": 0},
    }

    for _ in range(n):
        Phi, invariant, truth = sample()
        for m in (baseline, repaired):
            pred = m.decide_S3(Phi, invariant)
            stats[m.name]["total"] += 1
            if pred == truth:
                stats[m.name]["correct"] += 1

    for name, v in stats.items():
        print(name, v["correct"] / v["total"])

if __name__ == "__main__":
    run()
