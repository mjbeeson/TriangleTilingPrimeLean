/-
Points on the side `S` of `T`, for Section 11 of Beeson–Roșu: a point strictly between two points
of `S` is not a vertex of `T` and the tiles' angles there add up to `π`; near such a point a sector
on `T`'s side of `S` lies in `T`. Also: exact angle counts at a point (`lemma:angles`), and the two
sides at an `α` corner.
-/
import TriangleTiling.Prime.RunsBlockC

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

/-- A point of a closed sector is `X + pu + qv` with `p, q ≥ 0`. -/
theorem sectorC_decomp {X u v y : Plane} (hne : cross u v ≠ 0) (hy : y ∈ sectorC X u v) :
    ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ y = X + p • u + q • v := by
  have hd := decomp (U := X) hne y
  refine ⟨crdI X u v y, crdJ X u v y, ?_, ?_, hd⟩
  · rw [mem_sectorC] at hy
    unfold crdI
    have h := hy.2
    have hsq : 0 < cross u v * cross u v := mul_self_pos.mpr hne
    have : cross (y - X) v / cross u v = cross (y - X) v * cross u v / (cross u v * cross u v) := by
      field_simp
    rw [this]; exact div_nonneg h hsq.le
  · rw [mem_sectorC] at hy
    unfold crdJ
    have h := hy.1
    have hsq : 0 < cross u v * cross u v := mul_self_pos.mpr hne
    have : cross u (y - X) / cross u v = cross u (y - X) * cross u v / (cross u v * cross u v) := by
      field_simp
    rw [this]; exact div_nonneg h hsq.le

/-- `crdJ` in barycentric coordinates of a triangle whose side `j, j+1` is on `crdJ = 0`. -/
theorem crdJ_coord (T : Tri) {U I J : Plane} {j : Fin 3}
    (h0 : crdJ U I J (T.pts j) = 0) (h1 : crdJ U I J (T.pts (j + 1)) = 0) (y : Plane) :
    crdJ U I J y = T.basis.coord (j + 2) y * crdJ U I J (T.pts (j + 2)) := by
  have hy := T.basis.linear_combination_coord_eq_self y
  have hs := Tri.coord_sum T y
  rw [Fin.sum_univ_three] at hy
  simp only [Tri.basis_apply'] at hy
  have key : ∀ i : Fin 3, crdJ U I J y = T.basis.coord 0 y * crdJ U I J (T.pts 0) +
      T.basis.coord 1 y * crdJ U I J (T.pts 1) + T.basis.coord 2 y * crdJ U I J (T.pts 2) := by
    intro _
    unfold crdJ
    conv_lhs => rw [← hy]
    have hU : U = (T.basis.coord 0 y + T.basis.coord 1 y + T.basis.coord 2 y) • U := by
      rw [hs, one_smul]
    rw [show T.basis.coord 0 y • T.pts 0 + T.basis.coord 1 y • T.pts 1 + T.basis.coord 2 y • T.pts 2 - U
        = T.basis.coord 0 y • (T.pts 0 - U) + T.basis.coord 1 y • (T.pts 1 - U) +
          T.basis.coord 2 y • (T.pts 2 - U) by
      conv_lhs => rw [hU]
      simp only [add_smul, smul_sub]; abel]
    rw [cross_add_right, cross_add_right, cross_smul_right, cross_smul_right, cross_smul_right]
    ring
  rw [key 0]
  fin_cases j <;> simp at h0 h1 ⊢ <;> rw [h0, h1] <;> ring

section Side

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

omit hS in
/-- The third vertex of `T` is strictly north of `S`. -/
theorem third_north : 0 < crdJ U I J (D.target.pts (j + 2)) := by
  have h0 := hF.side _ (left_mem_segment ℝ _ _)
  have h1 := hF.side _ (right_mem_segment ℝ _ _)
  have hP2 : D.target.pts (j + 2) ∈ D.target.carrier := subset_convexHull ℝ _ ⟨_, rfl⟩
  refine lt_of_le_of_ne (hF.north _ hP2) fun h => ?_
  apply two_vertices_on_line D.target (lineF I J 0 1) (lineF I J 0 1 U)
    (lineF_ne_zero hF.hIJ (Or.inr one_ne_zero))
  intro i
  rw [lineF_apply U I J _ 0 1]
  rcases fin3_cases3 i j with e | e | e <;> rw [e]
  · rw [h0]; ring
  · rw [h1]; ring
  · rw [← h]; ring

omit hS in
/-- A point strictly between two points of the side `S` is not a vertex of `T`. -/
theorem not_vertex_of_between {U' V' X : Plane}
    (hU' : U' ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)))
    (hV' : V' ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1))) (hne : U' ≠ V')
    (hX : X ∈ openSegment ℝ U' V') : X ∉ Set.range D.target.pts := by
  have hXS : X ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) :=
    (convex_segment _ _).segment_subset hU' hV' (openSegment_subset_segment ℝ _ _ hX)
  have hc0 := hF.side X hXS
  rintro ⟨l, hl⟩
  set P₀ := D.target.pts j
  set P₁ := D.target.pts (j + 1)
  have hP : P₀ ≠ P₁ := tri_pts_succ_ne _ _
  rw [segment_eq_image_lineMap] at hU' hV'
  obtain ⟨t1, ⟨a1, b1⟩, rfl⟩ := hU'
  obtain ⟨t2, ⟨a2, b2⟩, rfl⟩ := hV'
  have ht : t1 ≠ t2 := by rintro rfl; exact hne rfl
  rw [openSegment_eq_image_lineMap] at hX
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hX
  have hcomp : AffineMap.lineMap (AffineMap.lineMap P₀ P₁ t1) (AffineMap.lineMap P₀ P₁ t2) θ =
      AffineMap.lineMap P₀ P₁ ((1 - θ) * t1 + θ * t2) := by
    simp only [AffineMap.lineMap_apply_module]; module
  rw [hcomp] at hl
  rw [hcomp] at hc0
  rcases fin3_cases3 l j with e | e | e
  · have hl' : AffineMap.lineMap P₀ P₁ (0 : ℝ) = AffineMap.lineMap P₀ P₁ ((1 - θ) * t1 + θ * t2) := by
      rw [AffineMap.lineMap_apply_zero, ← hl, e]
    have := AffineMap.lineMap_injective ℝ hP hl'
    rcases lt_or_gt_of_ne ht with h | h <;> nlinarith
  · have hl' : AffineMap.lineMap P₀ P₁ (1 : ℝ) = AffineMap.lineMap P₀ P₁ ((1 - θ) * t1 + θ * t2) := by
      rw [AffineMap.lineMap_apply_one, ← hl, e]
    have := AffineMap.lineMap_injective ℝ hP hl'
    rcases lt_or_gt_of_ne ht with h | h <;> nlinarith
  · have := third_north hF
    rw [← e, hl, hc0] at this; exact lt_irrefl _ this

omit hS in
/-- **At a point of `S` other than the vertices of `T` the angles add up to `π`.** -/
theorem target_pi_of_side {X : Plane} (hXT : X ∈ D.target.carrier) (hX0 : crdJ U I J X = 0)
    (hXv : X ∉ Set.range D.target.pts) : D.target.localAngle X = π := by
  apply D.target.localAngle_frontier _ hXv
  rw [frontier, D.target.isCompact.isClosed.closure_eq]
  exact ⟨hXT, not_interior_of_crdJ hF hX0⟩

omit hS in
/-- **Near a point of `S` other than the vertices of `T`, a sector on `T`'s side of `S` lies in
`T`.** -/
theorem hin_side {X u v : Plane} (hXT : X ∈ D.target.carrier) (hX0 : crdJ U I J X = 0)
    (hXv : X ∉ Set.range D.target.pts) (hne : cross u v ≠ 0) (hu : 0 ≤ cross I u / cross I J)
    (hv : 0 ≤ cross I v / cross I J) :
    ∃ r > (0 : ℝ), sectorC X u v ∩ ball X r ⊆ D.target.carrier := by
  set T := D.target
  have h0 := hF.side _ (left_mem_segment ℝ (T.pts j) (T.pts (j + 1)))
  have h1 := hF.side _ (right_mem_segment ℝ (T.pts j) (T.pts (j + 1)))
  have h2 := third_north hF
  have hcoord := crdJ_coord T h0 h1
  have hc2 : T.basis.coord (j + 2) X = 0 := by
    have := hcoord X; rw [hX0] at this
    exact ((mul_eq_zero.mp this.symm).resolve_right h2.ne')
  have hnn := (Tri.mem_carrier_iff_coord T X).mp hXT
  have hcj : 0 < T.basis.coord j X := by
    refine lt_of_le_of_ne (hnn j) fun h => hXv ⟨j + 1, ?_⟩
    have := TwoCs.eq_vertex_of_two_coords T (i := j) (j := j + 2) (l := j + 1)
      (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide)
      h.symm hc2
    exact this.symm
  have hcj1 : 0 < T.basis.coord (j + 1) X := by
    refine lt_of_le_of_ne (hnn (j + 1)) fun h => hXv ⟨j, ?_⟩
    have := TwoCs.eq_vertex_of_two_coords T (i := j + 1) (j := j + 2) (l := j)
      (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide)
      h.symm hc2
    exact this.symm
  obtain ⟨r, hr, hball⟩ := T.inter_ball_eq_halfplane (j + 2)
    (x := X) (by rw [show j + 2 + 1 = j by fin_cases j <;> rfl]; exact hcj)
    (by rw [show j + 2 + 2 = j + 1 by fin_cases j <;> rfl]; exact hcj1)
  refine ⟨r, hr, fun y ⟨hyC, hyB⟩ => ?_⟩
  have : y ∈ T.carrier ∩ ball X r := by
    rw [hball]
    refine ⟨?_, hyB⟩
    obtain ⟨p, q, hp, hq, rfl⟩ := sectorC_decomp hne hyC
    show 0 ≤ T.basis.coord (j + 2) (X + p • u + q • v)
    have e := hcoord (X + p • u + q • v)
    rw [crdJ_addv, crdJ_addv, hX0, cross_smul_right, cross_smul_right] at e
    have hpos : 0 ≤ p * cross I u / cross I J + q * cross I v / cross I J := by
      rw [mul_div_assoc, mul_div_assoc]; positivity
    have : 0 ≤ T.basis.coord (j + 2) (X + p • u + q • v) * crdJ U I J (T.pts (j + 2)) := by
      rw [← e]; linarith
    exact nonneg_of_mul_nonneg_left this h2
  exact this.1

end Side

/-! ### Exact angle counts -/

/-- Outside a triangle its local angle is `0`. -/
theorem Tri.localAngle_eq_zero_of_not_mem (T : Tri) {X : Plane} (hX : X ∉ T.carrier) :
    T.localAngle X = 0 := by
  classical
  have hneg : ∃ k, T.basis.coord k X < 0 := by
    by_contra h; push Not at h
    exact hX ((Tri.mem_carrier_iff_coord T X).mpr h)
  obtain ⟨k, hk⟩ := hneg
  rw [Tri.localAngle, dif_neg, if_neg, if_neg]
  · rintro ⟨m, hm, hpos⟩
    by_cases hkm : k = m
    · rw [hkm] at hk; linarith
    · linarith [hpos k hkm]
  · intro h; linarith [h k]
  · rintro ⟨l, rfl⟩; exact hX (subset_convexHull ℝ _ ⟨l, rfl⟩)


namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- The angles at `X` of any set of tiles add up to `pα + qβ`. -/
theorem combo_sum (F : Finset (Fin N)) (X : Plane) :
    ∃ p q : ℕ, ∑ i ∈ F, (D.tile i).localAngle X = p * α + q * β := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨p, q, h⟩ := ih
    rw [Finset.sum_insert hi, h]
    by_cases hX : X ∈ (D.tile i).carrier
    · obtain ⟨p', q', h', -, -⟩ := hS.combo hX
      exact ⟨p' + p, q' + q, by rw [h']; push_cast; ring⟩
    · have : (D.tile i).localAngle X = 0 := Tri.localAngle_eq_zero_of_not_mem _ hX
      exact ⟨p, q, by rw [this]; ring⟩

/-- **Exact count**: if the angles at `X` of all tiles add up to `Pα + Qβ`, those of any set of
tiles add up to `pα + qβ` with `p ≤ P`, `q ≤ Q`. -/
theorem sum_le_count {X : Plane} {P Q : ℕ}
    (htot : D.target.localAngle X = P * α + Q * β) (F : Finset (Fin N)) {p q : ℕ}
    (hF : ∑ i ∈ F, (D.tile i).localAngle X = p * α + q * β) : p ≤ P ∧ q ≤ Q := by
  classical
  obtain ⟨p', q', h'⟩ := hS.combo_sum Fᶜ X
  have := Finset.sum_add_sum_compl F (fun i => (D.tile i).localAngle X)
  rw [hF, h', D.sum_localAngle_eq, htot] at this
  have := hS.uniq (p := p + p') (q := q + q') (u := P) (v := Q) (by push_cast; linarith)
  omega

end RunSetting


end TriangleTiling.Prime
