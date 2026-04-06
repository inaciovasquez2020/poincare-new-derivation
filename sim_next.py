import random

def sample():
    Phi = random.choice([0,1])
    inv = random.choice([0,1])
    complexity = random.choice([0,1])
    truth = (inv == 0 and complexity == 0)
    return Phi, inv, complexity, truth

def decide(Phi, inv, complexity):
    return Phi==0 and inv==0 and complexity==0

def run(n=10000):
    correct = 0
    for _ in range(n):
        Phi, inv, c, truth = sample()
        if decide(Phi, inv, c) == truth:
            correct += 1
    print("improved", correct/n)

if __name__ == "__main__":
    run()
