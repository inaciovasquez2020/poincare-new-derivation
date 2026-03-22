def invariant_root_count(dsu):
    return len({dsu.find(x) for x in range(dsu.n)})

def delta_dsu(dsu, apply_pairing_step, pair, perm):
    dsu_before = dsu.copy()
    apply_pairing_step(dsu, pair, perm)
    return dsu_before, dsu

def is_noncollapsing(dsu_before, dsu_after):
    return invariant_root_count(dsu_after) == invariant_root_count(dsu_before)

def prune_condition(dsu_before, dsu_after):
    return invariant_root_count(dsu_after) < invariant_root_count(dsu_before)
