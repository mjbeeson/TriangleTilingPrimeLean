/-
`lemma:longrun` of Beeson–Roșu, Section 11, first part: some maximal run on the side `S` is stopped
at both ends. Every edge on `S` that is not a `c` edge has its tile's `γ` angle at one of its ends;
no `γ` is at an end of `S`, and (`γ > π/2`) no two are at one point. Take the westmost edge with its
`γ` at its western end (or the end of `S`), and the last edge before it with its `γ` at its eastern
end (or the start of `S`): the edges between them are `c` edges, a run stopped at both ends.
(`IntervalChain.stopped_stretch`; the printed proof counts stopped ends of maximal runs.)
-/
import TriangleTiling.Prime.RunsRooted
import TriangleTiling.Prime.RunsGap

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

/-- The target lies on one side of its side `j, j+1`. -/
theorem target_side (T : Tri) (j : Fin 3) :
    ∀ y ∈ T.carrier, 0 ≤ cross (T.pts (j + 1) - T.pts j) (T.pts (j + 2) - T.pts j) *
      cross (T.pts (j + 1) - T.pts j) (y - T.pts j) := by
  intro y hy
  set A := T.pts j
  set w := T.pts (j + 1) - A
  set σ := cross w (T.pts (j + 2) - A)
  refine (convexHull_min (t := {y | 0 ≤ σ * cross w (y - A)}) ?_ ?_) hy
  · rintro _ ⟨i, rfl⟩
    show 0 ≤ σ * cross w (T.pts i - A)
    obtain e | e | e := fin3_cases3 i j
    · rw [e, sub_self]; simp [cross]
    · rw [e]; simp only [w]; rw [Erdos634.Geometry.cross_self, mul_zero]
    · rw [e]; exact mul_self_nonneg _
  · intro y1 hy1 y2 hy2 p q hp hq hpq
    simp only [Set.mem_setOf_eq] at hy1 hy2 ⊢
    have e : p • y1 + q • y2 - A = p • (y1 - A) + q • (y2 - A) := by
      have hA : A = p • A + q • A := by rw [← add_smul, hpq, one_smul]
      conv_lhs => rw [hA]
      rw [smul_sub, smul_sub]; abel
    rw [e, cross_add_right, cross_smul_right, cross_smul_right]
    nlinarith [mul_nonneg hp hy1, mul_nonneg hq hy2]

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- At a point of a side of `T`, at most one tile has its `γ` angle. -/
theorem gamma_unique_side {j : Fin 3} {Z : Plane}
    (hZ : Z ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1))) {t t' : Fin N}
    (h : HasAngle D t Z γ) (h' : HasAngle D t' Z γ) : t = t' := by
  classical
  by_contra hne
  set A := D.target.pts j
  set w := D.target.pts (j + 1) - A
  set σ := cross w (D.target.pts (j + 2) - A)
  have hw : w ≠ 0 := sub_ne_zero.mpr (tri_pts_succ_ne _ _).symm
  set g : Plane →ₗ[ℝ] ℝ := σ • crossL w
  have hσ : σ ≠ 0 := by
    have := D.target.det_ne_zero
    rw [← D.target.cross_edgeVec j, Tri.edgeVec_eq, Tri.edgeVec'_eq] at this; exact this
  have hg : g ≠ 0 := smul_ne_zero hσ (crossL_ne_zero hw)
  have hZw : cross w (Z - A) = 0 := by
    rw [segment_eq_image_lineMap] at hZ
    obtain ⟨s, -, rfl⟩ := hZ
    rw [AffineMap.lineMap_apply_module']
    simp only [add_sub_cancel_right, w, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero]
  have hX : ∀ u ∈ ({t, t'} : Finset (Fin N)), ∀ y ∈ (D.tile u).carrier, g Z ≤ g y := by
    intro u _ y hy
    have h0 : 0 ≤ σ * cross w (y - A) := target_side D.target j y (tile_subset_target D.toDissection u hy)
    simp only [g, LinearMap.smul_apply, crossL_apply, smul_eq_mul]
    rw [cross_sub_right w y A, mul_sub] at h0
    rw [cross_sub_right] at hZw
    have e : σ * cross w Z = σ * cross w A := by rw [show cross w Z = cross w A by linarith]
    linarith
  have := halfplane_sum_le D.toDissection hg _ hX
  rw [Finset.sum_pair hne, localAngle_of_hasAngle h, localAngle_of_hasAngle h'] at this
  have := hS.gamma_gt
  linarith

end RunSetting

end TriangleTiling.Prime
