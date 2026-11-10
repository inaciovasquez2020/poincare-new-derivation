"""Regression checks for represented target collisions in 3-to-2 search.

These are finite candidate-generation checks, not manifold recognition or
a proof of universal Pachner descent. Run with:
    python3 -m unittest discover -s tests -p test_pachner_target_guard_unittest.py
"""
import unittest

from scripts.pachner_search import Triangulation


class Move32TargetCollisionTests(unittest.TestCase):
    def test_boundary_of_four_simplex_has_no_legal_32_target(self):
        # Every edge has three incident tetrahedra, but the two replacement
        # tetrahedra are already present in the five-facet 3-sphere.
        facets = [
            tuple(v for v in range(5) if v != omitted)
            for omitted in range(5)
        ]
        T = Triangulation(facets)
        self.assertEqual(len(T.edge_to_tets()), 10)
        self.assertTrue(all(len(ts) == 3 for ts in T.edge_to_tets().values()))
        self.assertEqual(T.candidate_32_moves(), [])

    def test_one_represented_target_blocks_its_edge(self):
        T = Triangulation([
            (0, 1, 2, 3),
            (0, 1, 2, 4),
            (0, 1, 3, 4),
            (0, 2, 3, 4),  # Existing replacement at endpoint 0.
        ])
        self.assertFalse(any(
            move.edge == (0, 1) for move in T.candidate_32_moves()
        ))

    def test_unrepresented_targets_retain_valid_local_candidate(self):
        T = Triangulation([
            (0, 1, 2, 3),
            (0, 1, 2, 4),
            (0, 1, 3, 4),
            (5, 2, 3, 4),
        ])
        candidates = [
            move for move in T.candidate_32_moves()
            if move.edge == (0, 1)
        ]
        self.assertEqual(len(candidates), 1)
        output = T.apply_32(candidates[0])
        self.assertEqual(
            set(output.tetrahedra),
            {(5, 2, 3, 4), (0, 2, 3, 4), (1, 2, 3, 4)},
        )
        self.assertEqual(len(output.tetrahedra), 3)


if __name__ == "__main__":
    unittest.main()
