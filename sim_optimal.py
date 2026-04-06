import random

def sample():
    Phi = random.choice([0,1])
    H1 = random.choice([0,1])
    truth = (H1 == 0)
    return Phi, H1, truth

def decide(Phi, H1):
    return Phi == 0 and H1 == 0

def run(n=10000):
    correct = 0
    for _ in range(n):
        Phi, H1, truth = sample()
        if decide(Phi, H1) == truth:
            correct += 1
    print("optimal", correct/n)

if __name__ == "__main__":
    run()
