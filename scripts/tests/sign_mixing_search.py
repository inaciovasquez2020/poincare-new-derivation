import random
import time

def random_triangulation(n):
    deg = {i: random.randint(3,10) for i in range(n)}
    edges = []
    for _ in range(n*2):
        u = random.randint(0,n-1)
        v = random.randint(0,n-1)
        if u!=v:
            edges.append((u,v,3))
    return deg, edges

def has_sign_mixing(deg, edges):
    for (u,v,k) in edges:
        if k==3:
            if (deg[u]-6)*(deg[v]-6)<0:
                return True
    return False

def trial(n):
    deg, edges = random_triangulation(n)
    return has_sign_mixing(deg, edges)

start = time.time()
count = 0
trials = 0

while time.time() - start < 3600:
    trials += 1
    if trial(50):
        count += 1

print({"trials": trials, "success": count, "ratio": count/max(1,trials)})
