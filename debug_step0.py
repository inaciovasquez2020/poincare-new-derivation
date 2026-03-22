import sys, os
from copy import deepcopy

sys.path.append(os.path.join(os.getcwd(), "scripts/tests"))

import obstruction_enumeration_backtracking as m

def snapshot(dsu):
    return deepcopy(dsu)

def run():
    num_tets = 3
    faces = m.all_faces(num_tets)
    perms = m.ODD_TRI_PERMS
    first_pairs = []

    for pairing in m.face_pairings_dfs(faces):
        if not pairing:
            continue

        pair = pairing[0]

        for perm in perms:
            dsu = m.DSU(100)
            dsu_before = snapshot(dsu)

            # derive cc via same internal call path
            try:
                m.apply_pairing_step(dsu, pair, perm)
                changed = (snapshot(dsu) != dsu_before)
                print("CANDIDATE", {"pair": pair, "perm": perm, "cc": None})
                print("DSU_CHANGED_DEPTH0", changed)
            except Exception as e:
                print("CANDIDATE_FAIL", {"pair": pair, "perm": perm, "error": str(e)})
                continue

            try:
                if True:
                    first_pairs.append((pair, perm, None))
            except:
                pass

        break

    print("FIRST_PAIRS_COUNT", len(first_pairs))

    res = list(m.face_pairings_dfs(faces))
    print("DFS_RESULT_COUNT", len(res))

run()
