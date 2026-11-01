import Poincare.GlobalFanReentryModeLinkedStep

namespace Poincare

/-- Exact original U(16) 104-facet input from Zenodo 21980010,
PachnerDCG-1.0.0_1.zip, certificates/unflippable-complexes/u16-plus/input.json.
This is data only, not a sphere-recognition or cycle-exclusion theorem. -/
def zenodoU16Original : Triangulation :=
  { tets :=
      [⟨1, 2, 3, 6⟩, ⟨1, 2, 3, 9⟩, ⟨1, 2, 5, 10⟩, ⟨1, 2, 5, 16⟩,
       ⟨1, 2, 6, 8⟩, ⟨1, 2, 8, 16⟩, ⟨1, 2, 9, 10⟩, ⟨1, 3, 6, 13⟩,
       ⟨1, 3, 9, 12⟩, ⟨1, 3, 12, 13⟩, ⟨1, 4, 9, 11⟩, ⟨1, 4, 9, 16⟩,
       ⟨1, 4, 11, 15⟩, ⟨1, 4, 15, 16⟩, ⟨1, 5, 7, 10⟩, ⟨1, 5, 7, 16⟩,
       ⟨1, 6, 8, 14⟩, ⟨1, 6, 13, 14⟩, ⟨1, 7, 10, 15⟩, ⟨1, 7, 15, 16⟩,
       ⟨1, 8, 9, 12⟩, ⟨1, 8, 9, 16⟩, ⟨1, 8, 12, 14⟩, ⟨1, 9, 10, 11⟩,
       ⟨1, 10, 11, 15⟩, ⟨1, 12, 13, 14⟩, ⟨2, 3, 4, 7⟩, ⟨2, 3, 4, 10⟩,
       ⟨2, 3, 6, 11⟩, ⟨2, 3, 7, 9⟩, ⟨2, 3, 10, 11⟩, ⟨2, 4, 7, 14⟩,
       ⟨2, 4, 10, 13⟩, ⟨2, 4, 13, 14⟩, ⟨2, 5, 10, 12⟩, ⟨2, 5, 12, 16⟩,
       ⟨2, 6, 8, 11⟩, ⟨2, 7, 9, 15⟩, ⟨2, 7, 14, 15⟩, ⟨2, 8, 11, 16⟩,
       ⟨2, 9, 10, 13⟩, ⟨2, 9, 13, 15⟩, ⟨2, 10, 11, 12⟩, ⟨2, 11, 12, 16⟩,
       ⟨2, 13, 14, 15⟩, ⟨3, 4, 5, 8⟩, ⟨3, 4, 5, 11⟩, ⟨3, 4, 7, 12⟩,
       ⟨3, 4, 8, 10⟩, ⟨3, 4, 11, 12⟩, ⟨3, 5, 8, 15⟩, ⟨3, 5, 11, 14⟩,
       ⟨3, 5, 14, 15⟩, ⟨3, 6, 11, 13⟩, ⟨3, 7, 9, 12⟩, ⟨3, 8, 10, 16⟩,
       ⟨3, 8, 15, 16⟩, ⟨3, 10, 11, 14⟩, ⟨3, 10, 14, 16⟩, ⟨3, 11, 12, 13⟩,
       ⟨3, 14, 15, 16⟩, ⟨4, 5, 6, 9⟩, ⟨4, 5, 6, 12⟩, ⟨4, 5, 8, 13⟩,
       ⟨4, 5, 9, 11⟩, ⟨4, 5, 12, 13⟩, ⟨4, 6, 9, 16⟩, ⟨4, 6, 12, 15⟩,
       ⟨4, 6, 15, 16⟩, ⟨4, 7, 12, 14⟩, ⟨4, 8, 10, 13⟩, ⟨4, 11, 12, 15⟩,
       ⟨4, 12, 13, 14⟩, ⟨5, 6, 7, 10⟩, ⟨5, 6, 7, 13⟩, ⟨5, 6, 9, 14⟩,
       ⟨5, 6, 10, 12⟩, ⟨5, 6, 13, 14⟩, ⟨5, 7, 13, 16⟩, ⟨5, 8, 13, 15⟩,
       ⟨5, 9, 11, 14⟩, ⟨5, 12, 13, 16⟩, ⟨5, 13, 14, 15⟩, ⟨6, 7, 8, 11⟩,
       ⟨6, 7, 8, 14⟩, ⟨6, 7, 10, 15⟩, ⟨6, 7, 11, 13⟩, ⟨6, 7, 14, 15⟩,
       ⟨6, 9, 14, 16⟩, ⟨6, 10, 12, 15⟩, ⟨6, 14, 15, 16⟩, ⟨7, 8, 9, 12⟩,
       ⟨7, 8, 9, 15⟩, ⟨7, 8, 11, 16⟩, ⟨7, 8, 12, 14⟩, ⟨7, 8, 15, 16⟩,
       ⟨7, 11, 13, 16⟩, ⟨8, 9, 10, 13⟩, ⟨8, 9, 10, 16⟩, ⟨8, 9, 13, 15⟩,
       ⟨9, 10, 11, 14⟩, ⟨9, 10, 14, 16⟩, ⟨10, 11, 12, 15⟩, ⟨11, 12, 13, 16⟩] }


/-- Closed finite computation: the exact five link triangles of the
represented edge (2, 7) in the original 104-tetrahedron U(16) fixture.
This is the first independent certificate obligation, not a HighFanState. -/
theorem zenodoU16_edge27_linkStar :
    vertexLinkStarTriangles zenodoU16Original 2 7 =
      [⟨3, 4, 7⟩, ⟨3, 7, 9⟩, ⟨4, 7, 14⟩,
       ⟨7, 9, 15⟩, ⟨7, 14, 15⟩] := by
  decide

/-- Independently check the five adjacent link-triangle pairs that
close the edge-(2,7) cycle.  These are pure, explicitly witnessed
finite incidence statements; the ambient cyclic fan is constructed later. -/
theorem zenodoU16_edge27_cyclicAdjacency :
    VertexLinkStarAdjacent zenodoU16Original 2 7
      ⟨3, 4, 7⟩ ⟨3, 7, 9⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 2 7
      ⟨3, 7, 9⟩ ⟨7, 9, 15⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 2 7
      ⟨7, 9, 15⟩ ⟨7, 14, 15⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 2 7
      ⟨7, 14, 15⟩ ⟨4, 7, 14⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 2 7
      ⟨4, 7, 14⟩ ⟨3, 4, 7⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by decide, by decide, 3, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 9, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 15, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 14, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 4, by decide, by decide, by decide⟩


/-- Five explicit adjacent link-triangle pairs around the represented edge (4,9).
This checks local incidence only; a covering graph walk is not yet claimed. -/
theorem zenodoU16_edge49_cyclicAdjacency :
    VertexLinkStarAdjacent zenodoU16Original 4 9
      ⟨1, 9, 11⟩ ⟨5, 9, 11⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 4 9
      ⟨5, 9, 11⟩ ⟨5, 6, 9⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 4 9
      ⟨5, 6, 9⟩ ⟨6, 9, 16⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 4 9
      ⟨6, 9, 16⟩ ⟨1, 9, 16⟩ ∧
    VertexLinkStarAdjacent zenodoU16Original 4 9
      ⟨1, 9, 16⟩ ⟨1, 9, 11⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by decide, by decide, 11, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 5, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 6, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 16, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, 1, by decide, by decide, by decide⟩

/-- Exhaustive link-star computation for the represented edge (4,9)
in the exact 104-tetrahedron U(16) fixture. -/
theorem zenodoU16_edge49_linkStar :
    vertexLinkStarTriangles zenodoU16Original 4 9 =
      [⟨1, 9, 11⟩, ⟨1, 9, 16⟩, ⟨5, 6, 9⟩,
       ⟨5, 9, 11⟩, ⟨6, 9, 16⟩] := by
  decide

end Poincare
