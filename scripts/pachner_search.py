# ... keep existing imports and class definitions ...

def canon(t):
    return tuple(sorted(t))

class Triangulation:
    # ... existing methods ...

    def apply_32(self, move):
        u, v = move.edge
        a, b, c = move.opposite_vertices

        new_tets = []
        removed = set()

        for t in self.tetrahedra:
            if u in t and v in t and len([x for x in t if x in (a, b, c)]) == 2:
                removed.add(tuple(t))
            else:
                new_tets.append(tuple(t))

        # add canonical tetrahedra
        new_tets.extend([
            canon((a, b, c, u)),
            canon((a, b, c, v)),
        ])

        # keep external tetrahedron already present (no duplication)
        return Triangulation([canon(t) for t in new_tets])

def random_lift_generator(n=10):
    import random
    return Triangulation([
        tuple(sorted(random.sample(range(n*3), 4)))
        for _ in range(n)
    ])

def adversarial_family_chain(k=3):
    return [random_lift_generator(n=10+i) for i in range(k)]

__all__ = [
    "Triangulation",
    "random_lift_generator",
    "adversarial_family_chain",
]
