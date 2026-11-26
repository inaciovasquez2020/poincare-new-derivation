#!/usr/bin/env python3
"""Deterministic 104-witness archive digest; use --all to output witnesses."""
import hashlib
import json
import sys
import urf_u16_unlock_audit as base


def collect():
    records = []
    for tet in sorted(base.ORIGINAL):
        outcome = base.first_unlock(tet)
        assert outcome is not None
        depth, path, site, final_pre, _ = outcome
        assert depth == len(path)
        state = base.stabilize(tet)
        for kind, step in path:
            sites = base.legal_sites(state)
            assert step in (sites[0] if kind == '23' else sites[1])
            state = (base.flip23(state, step) if kind == '23'
                     else base.flip32(state, step))
            assert base.closed_links(state)
        assert state == final_pre and site in base.legal_sites(state)[1]
        assert 16 not in site[0]
        after = base.flip32(state, site)
        assert base.closed_links(after)
        records.append({'stellar_tetrahedron': tet,
                        'pre_unlock_moves': path,
                        'unlock_32': site,
                        'final_tetrahedra': len(after),
                        'phi_final': 4*(len(after)-17)})
    blob = json.dumps(records, sort_keys=True, separators=(',', ':')).encode('utf-8')
    return records, hashlib.sha256(blob).hexdigest()


if __name__ == '__main__':
    records, digest = collect()
    assert len(records) == 104
    assert digest == '2dfa073cacd7b673bb2daadc8cc1b52254ce643b205904d7dc8dc306945545d1'
    if '--all' in sys.argv[1:]:
        print(json.dumps(records, indent=2, sort_keys=True))
    else:
        print(json.dumps({'all_witnesses_count': len(records),
                          'all_witnesses_sha256': digest}, sort_keys=True))
