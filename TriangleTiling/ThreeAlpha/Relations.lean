/-
Relations between the sides of the tile, and Laczkovich's graph `Γ_a`, for M. Beeson, *Triangle
tiling: the case 3α + 2β = π* (arXiv 1206.2229v4): `definition:essentialedgerelation` (i),
`definition:relationlattice`, `lemma:noboundarylink`. (`lemma:relationlattice`, about the rank of
`L`, is in `RelLattice.lean`.)

`Γ_a` is the isosceles paper's formalization of `definition:Gamma` (`IsLink`, with the `a` edges,
those opposite the angle `α`, as marked edges). "The tiling witnesses an `a`-relation" is
`WitnessesARel`, `definition:essentialedgerelation` (ii).
-/
import TriangleTiling.ThreeAlpha.Defs
import TriangleTiling.Tiling.Degree
import TriangleTiling.Isosceles.MarkedCount
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry

/-- **Definition `definition:essentialedgerelation` (i)**, `a`-relation: `j a = p b + q c` with
nonnegative integers `j, p, q` and `j > 0`. -/
def ARelation (a b c : ℝ) : Prop :=
  ∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * a = p * b + q * c

open Classical in
/-- **Definition `definition:essentialedgerelation` (ii)**, for `a`-relations: the tiling
witnesses an `a`-relation `j a = u b + v c` (`j > 0`, `u, v ≥ 0`). There is an interior segment
`PQ` with tiles on both sides with vertices at `P`, and tiles on both sides with vertices at `Q`
(`TermSeg`: `PQ` on the line `{g = c₀}`, with sides `g ≤ c₀` and `g ≥ c₀`), such that one side of
`PQ` has `j` more `a` edges than the other, and the other side has `u` more `b` edges and `v`
more `c` edges than the first. The `a`, `b`, `c` edges are those opposite the angles `α`, `β`,
`γ` (`edgeType`), and the edges on a side are those on `PQ` (`sideEdges`). -/
def WitnessesARel {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ) : Prop :=
  ∃ (g : Plane →ₗ[ℝ] ℝ) (c₀ : ℝ) (P Q : Plane), TermSeg D.toDissection g c₀ P Q ∧
    ((sideEdges D.toDissection (-g) (-c₀) P Q).filter (edgeType D α)).card
      < ((sideEdges D.toDissection g c₀ P Q).filter (edgeType D α)).card ∧
    ((sideEdges D.toDissection g c₀ P Q).filter (edgeType D β)).card
      ≤ ((sideEdges D.toDissection (-g) (-c₀) P Q).filter (edgeType D β)).card ∧
    ((sideEdges D.toDissection g c₀ P Q).filter (edgeType D γ)).card
      ≤ ((sideEdges D.toDissection (-g) (-c₀) P Q).filter (edgeType D γ)).card

/-- **Definition `definition:relationlattice`.** The relation lattice of the tile with sides
`a, b, c`: `L = {(P, Q, R) ∈ ℤ³ : P a + Q b + R c = 0}`. -/
def relLattice (a b c : ℝ) : Submodule ℤ (Fin 3 → ℤ) where
  carrier := {v | (v 0 : ℝ) * a + v 1 * b + v 2 * c = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply, Int.cast_add] at *
    linear_combination hx + hy
  zero_mem' := by simp
  smul_mem' := by
    intro k x hx
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, Int.cast_mul] at *
    linear_combination (k : ℝ) * hx

/-- **Lemma `lemma:noboundarylink`.** No link of `Γ_a` terminates at a point of the boundary of
`ABC`. (True of the links of any marked class of edges, in any dissection.) -/
theorem noboundarylink {N : ℕ} (D : CongruentDissection N) (φ : ℝ) {X Y : Plane}
    (h : IsLink D.toDissection (edgeType D φ) X Y) : Y ∉ frontier D.target.carrier := by
  obtain ⟨g, c, hl⟩ := h
  exact fun hf => hf.2 hl.end_interior

end TriangleTiling.ThreeAlpha
