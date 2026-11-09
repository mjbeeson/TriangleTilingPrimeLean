/-
`lemma:equilateralbound` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723): a
segment contained in an equilateral triangle with side `X` has length at most `X`, with equality
only if it is a side.

Statement checked by Beeson. The proof is the paper's: write a point in barycentric
coordinates and use the triangle inequality, whose equality case needs two parallel sides.
-/
import TriangleTiling.Tiling.Local

namespace TriangleTiling.Equilateral

open Erdos634.Geometry

namespace EquilateralBound

theorem sum_rot {E : Type*} [AddCommMonoid E] (f : Fin 3 → E) (k : Fin 3) :
    ∑ i, f i = f k + f (k + 1) + f (k + 2) := by
  rw [Fin.sum_univ_three]
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) k with rfl | rfl | rfl
  · rfl
  · rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]; abel
  · rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]; abel

/-- `P - Z` in barycentric coordinates of `P`. -/
theorem comb (T : Tri) (P Z : Plane) :
    P - Z = ∑ i, T.basis.coord i P • (T.pts i - Z) := by
  have h := T.basis.linear_combination_coord_eq_self P
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    T.basis.sum_coord_apply_eq_one P, one_smul]
  conv_lhs => rw [← h]
  rfl

/-- The distance from a vertex to a point of the triangle is at most the side, with equality only
at the other two vertices. -/
theorem vertex_bound (T : Tri) {X : ℝ} (hX : ∀ i j, i ≠ j → dist (T.pts i) (T.pts j) = X)
    (k : Fin 3) {Q : Plane} (hQ : Q ∈ T.carrier) :
    dist (T.pts k) Q ≤ X ∧ (dist (T.pts k) Q = X → Q = T.pts (k + 1) ∨ Q = T.pts (k + 2)) := by
  have hc := (Tri.mem_carrier_iff_coord T Q).mp hQ
  have hk1 : k + 1 ≠ k := by revert k; decide
  have hk2 : k + 2 ≠ k := by revert k; decide
  have hk12 : k + 1 ≠ k + 2 := by revert k; decide
  have hs := T.basis.sum_coord_apply_eq_one Q
  rw [sum_rot _ k] at hs
  set c := T.basis.coord k Q
  set a := T.basis.coord (k + 1) Q with ha_def
  set b := T.basis.coord (k + 2) Q with hb_def
  set u := T.pts (k + 1) - T.pts k
  set w := T.pts (k + 2) - T.pts k
  have hQk : Q - T.pts k = a • u + b • w := by
    rw [comb T Q (T.pts k), sum_rot _ k, sub_self, smul_zero, zero_add]
  have hu : ‖u‖ = X := by rw [← dist_eq_norm]; exact hX _ _ hk1
  have hw : ‖w‖ = X := by rw [← dist_eq_norm]; exact hX _ _ hk2
  have hXpos : 0 < X := by
    rw [← hX _ _ hk1]; exact dist_pos.mpr (T.indep.injective.ne hk1)
  have ha : 0 ≤ a := hc (k + 1)
  have hb : 0 ≤ b := hc (k + 2)
  have hc0 := hc k
  have hd : dist (T.pts k) Q = ‖a • u + b • w‖ := by rw [dist_comm, dist_eq_norm, hQk]
  have hn : ‖a • u‖ + ‖b • w‖ = (a + b) * X := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hu, hw]; ring
  have hle : ‖a • u + b • w‖ ≤ (a + b) * X := hn ▸ norm_add_le _ _
  refine ⟨by rw [hd]; nlinarith, fun heq => ?_⟩
  rw [hd] at heq
  have hab : a + b = 1 := by nlinarith
  have hsr : SameRay ℝ (a • u) (b • w) := by
    rw [sameRay_iff_norm_add]; nlinarith
  rcases ha.eq_or_lt with ha0 | ha0
  · right
    have hb1 : b = 1 := by linarith
    rw [← ha0, hb1, zero_smul, zero_add, one_smul] at hQk
    exact sub_left_injective (hQk.trans rfl)
  rcases hb.eq_or_lt with hb0 | hb0
  · left
    have ha1 : a = 1 := by linarith
    rw [← hb0, ha1, zero_smul, add_zero, one_smul] at hQk
    exact sub_left_injective (hQk.trans rfl)
  -- `u` and `w` would be parallel
  exfalso
  have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu; linarith
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ :=
    hsr.exists_pos (smul_ne_zero ha0.ne' hu0) (smul_ne_zero hb0.ne' hw0)
  set t := r₂ * b / (r₁ * a)
  have hut : u = t • w := by
    rw [smul_smul, smul_smul] at hr
    have hpos : r₁ * a ≠ 0 := by positivity
    calc u = (r₁ * a)⁻¹ • ((r₁ * a) • u) := by rw [smul_smul, inv_mul_cancel₀ hpos, one_smul]
      _ = t • w := by rw [hr, smul_smul]; congr 1; simp only [t]; field_simp
  have hline : T.pts (k + 1) = AffineMap.lineMap (T.pts k) (T.pts (k + 2)) t := by
    rw [AffineMap.lineMap_apply_module]
    have : T.pts (k + 1) = T.pts k + t • w := by rw [← hut]; simp only [u]; abel
    rw [this, smul_sub, sub_smul, one_smul]; abel
  have h1 := Tri.coord_vertex T (k + 1) (k + 1)
  rw [hline, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, if_neg hk1, if_neg hk12] at h1
  simp at h1

/-- The distance between two points of the triangle is at most the side; at equality the second
point is a vertex. -/
theorem point_bound (T : Tri) {X : ℝ} (hX : ∀ i j, i ≠ j → dist (T.pts i) (T.pts j) = X)
    {P Q : Plane} (hP : P ∈ T.carrier) (hQ : Q ∈ T.carrier) :
    dist P Q ≤ X ∧ (dist P Q = X → ∃ j, Q = T.pts j) := by
  have hc := (Tri.mem_carrier_iff_coord T P).mp hP
  have hs := T.basis.sum_coord_apply_eq_one P
  have hle : dist P Q ≤ ∑ i, T.basis.coord i P * dist (T.pts i) Q := by
    rw [dist_eq_norm, comb T P Q]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_of_nonneg (hc i), dist_eq_norm]
  have hterm : ∀ i ∈ Finset.univ, T.basis.coord i P * dist (T.pts i) Q ≤ T.basis.coord i P * X :=
    fun i _ => mul_le_mul_of_nonneg_left (vertex_bound T hX i hQ).1 (hc i)
  have hsumX : ∑ i, T.basis.coord i P * X = X := by rw [← Finset.sum_mul, hs, one_mul]
  refine ⟨hle.trans ((Finset.sum_le_sum hterm).trans hsumX.le), fun heq => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, 0 < T.basis.coord i P := by
    by_contra h
    push Not at h
    have : ∑ i, T.basis.coord i P ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hdi : dist (T.pts i) Q = X := by
    by_contra hne
    have hlt : dist (T.pts i) Q < X := lt_of_le_of_ne (vertex_bound T hX i hQ).1 hne
    have := Finset.sum_lt_sum hterm ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hi⟩
    linarith
  rcases (vertex_bound T hX i hQ).2 hdi with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

end EquilateralBound

open EquilateralBound in
/-- **Lemma `lemma:equilateralbound`.** Let `T` be an equilateral triangle with side `X`, and let
`PQ` be a segment contained in `T`. Then `|PQ| ≤ X`, with equality only if `PQ` is a side of `T`,
that is, `P` and `Q` are two different vertices of `T`. -/
theorem equilateralbound (T : Tri) {X : ℝ} (hX : ∀ i j, i ≠ j → dist (T.pts i) (T.pts j) = X)
    {P Q : Plane} (hPQ : segment ℝ P Q ⊆ T.carrier) :
    dist P Q ≤ X ∧ (dist P Q = X → ∃ i j, i ≠ j ∧ P = T.pts i ∧ Q = T.pts j) := by
  have hP := hPQ (left_mem_segment ℝ P Q)
  have hQ := hPQ (right_mem_segment ℝ P Q)
  refine ⟨(point_bound T hX hP hQ).1, fun heq => ?_⟩
  obtain ⟨j, rfl⟩ := (point_bound T hX hP hQ).2 heq
  obtain ⟨i, rfl⟩ := (point_bound T hX hQ hP).2 (by rw [dist_comm]; exact heq)
  refine ⟨i, j, fun hij => ?_, rfl, rfl⟩
  have hXpos : 0 < X := by
    rw [← hX 0 1 (by decide)]; exact dist_pos.mpr (T.indep.injective.ne (by decide))
  rw [hij, dist_self] at heq
  linarith

end TriangleTiling.Equilateral
