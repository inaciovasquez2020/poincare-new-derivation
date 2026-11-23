/-!
G2 face-index projection, SINGLE-LEMMA verification candidate.
STATUS := NOT_RUN. This has NOT been compiled against Lean 4.30.0-rc1.

Usage: append this snippet to a temporary COPY of
  docs/certificates/g2-geometric-realization/G2WitnessFreeAffineVerified.lean
from the published branch work/first-nonzero-reentry-20261027.
Do not import that certificate alongside PR199G2VerifiedConeComplex: both
files define several identically named declarations.

The only proof goal is the definitional face projection. If `rfl` fails,
STOP immediately and inspect the elaborator's first error; do not add
further speculative patches. This file does not modify the repository.
-/

namespace Poincare.PR199G2

/-- Under the graph-incidence equivalence, the face of the inverse flag
is the represented triangular face corresponding to the graph edge. -/
theorem g2_flag_inverse_face_projection
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (F : AmbientEdgeCyclicFan K v x)
    (z :
      Σ g : FanUnorderedGraphEdge K v x,
        {sigma :
          {t : LinkTriangle //
            t ∈ vertexLinkStarTriangles K v x} //
          sigma ∈ g.1}) :
    ((barycentricFlagGraphEndpointEquiv hcore F).symm z).face =
      insert ((graphEdgeForFaceEquiv hcore F).symm z.1).1
        ({v, x} : Finset Nat) := by
  rfl

#print axioms g2_flag_inverse_face_projection

end Poincare.PR199G2