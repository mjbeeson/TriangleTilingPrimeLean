/-
**`lemma:trisector`** of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of
congruent triangles*, Section 13: the trisector decomposition of the isosceles-`β` triangle.

`ABC = T` with `A, B, C = pts 0, pts 1, pts 2`, base angles `β` at `A`, `C` and apex `3α` at `B`.
"`(a, b, c)` form the sides of a triangle with angles `(α, β, γ)`" is `a, b, c = d sin α, d sin β,
d sin γ` for some `d > 0`; "coprime integers" enters the printed proof only through
`lemma:gsquare`, whose conclusion `(a, b, c) = (km, k² - m², k²)` is taken as a hypothesis. `E`,
"the point where the trisector of the angle at `B` nearer `A` meets `AC`", is the point of the
segment `AC` with `∠ABE = α`. The last sentence (the other trisector, by reflection) is not
formalized.

Statement checked by Beeson.
-/
import TriangleTiling.Prime.TriquadMain

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

/-- The law of cosines for a triangle with sides proportional to the sines of its angles. -/
theorem cos_of_sines {α β γ d : ℝ} (hsum : α + β + γ = π) :
    (d * Real.sin α) ^ 2 = (d * Real.sin β) ^ 2 + (d * Real.sin γ) ^ 2 -
      2 * (d * Real.sin β) * (d * Real.sin γ) * Real.cos α := by
  have e : α = π - (β + γ) := by linarith
  rw [e, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_add, Real.cos_add]
  linear_combination (d ^ 2 * Real.sin β ^ 2) * Real.sin_sq_add_cos_sq γ +
    (d ^ 2 * Real.sin γ ^ 2) * Real.sin_sq_add_cos_sq β

/-- **Lemma `lemma:trisector`** (the trisector decomposition). Let `ABC` be the isosceles-`β`
triangle with base angles `β` at `A` and `C` and apex angle `3α` at `B`. Let `(a, b, c)` be coprime
integers forming the sides of a triangle with angles `(α, β, γ)`. Suppose `|AB| = |CB| = jkc`. Then
`|AC| = jm(b + 2c)`. Let `E` be the point where the trisector of the angle at `B` nearer `A` meets
`AC`. Then
(i) triangle `ABE` is similar to the tile, with ratio of similarity `jk`; in particular
`|AE| = jka` and `|BE| = jkb`;
(ii) triangle `EBC` has the triquadratic shape, with `2α` at `B`, `β` at `C` and `α + β` at `E`,
and its sides are given by `|BC| = jkc`, `|BE| = jkb`, and `|EC| = jm(b + c)`;
(iii) `|EC| = jm(b + c)`, and `|AE| + |EC| = |AC|`. -/
theorem trisector {T : Tri} {E : Plane} {α β γ a b c d : ℝ} {m k j : ℤ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α + β + γ = π) (hrel : 3 * α + 2 * β = π)
    (hd : 0 < d) (hsa : a = d * Real.sin α) (hsb : b = d * Real.sin β)
    (hsc : c = d * Real.sin γ) (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2) (hj : 0 < j)
    (hshape : T.angleAt 0 = β ∧ T.angleAt 1 = 3 * α ∧ T.angleAt 2 = β)
    (hAB : dist (T.pts 0) (T.pts 1) = j * k * c) (hCB : dist (T.pts 2) (T.pts 1) = j * k * c)
    (hE : E ∈ segment ℝ (T.pts 0) (T.pts 2)) (hEα : ∠ (T.pts 0) (T.pts 1) E = α) :
    dist (T.pts 0) (T.pts 2) = j * m * (b + 2 * c) ∧
    (∠ (T.pts 1) (T.pts 0) E = β ∧ ∠ (T.pts 0) E (T.pts 1) = γ ∧
      dist (T.pts 0) E = j * k * a ∧ dist (T.pts 1) E = j * k * b) ∧
    (∠ E (T.pts 1) (T.pts 2) = 2 * α ∧ ∠ (T.pts 1) (T.pts 2) E = β ∧
      ∠ (T.pts 2) E (T.pts 1) = α + β ∧ dist (T.pts 1) (T.pts 2) = j * k * c ∧
      dist (T.pts 1) E = j * k * b ∧ dist E (T.pts 2) = j * m * (b + c)) ∧
    (dist E (T.pts 2) = j * m * (b + c) ∧
      dist (T.pts 0) E + dist E (T.pts 2) = dist (T.pts 0) (T.pts 2)) := by
  set A := T.pts 0
  set B := T.pts 1
  set C := T.pts 2
  have hk : (0 : ℝ) < k := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (m : ℝ) < k := by exact_mod_cast hmk
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk' : (m : ℝ) < k := by exact_mod_cast hmk
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have sα := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have sγ := Real.sin_pos_of_pos_of_lt_pi hγ (by linarith)
  have nB : cross (A - B) (C - B) ≠ 0 := by
    have := cross_pts_ne T 1
    rw [cross_swap] at this
    exact fun h => this (by rw [show T.pts (1 + 2) = A from rfl, show T.pts (1 + 1) = C from rfl,
      h, neg_zero])
  have hBA : B ≠ A := fun h => by
    apply nB; rw [h, sub_self]; simp [cross]
  -- the angles of `ABC`
  have aA : ∠ B A C = β := by rw [← hshape.1, angleAt_eq]; rfl
  have aB : ∠ A B C = 3 * α := by
    rw [EuclideanGeometry.angle, InnerProductGeometry.angle_comm, ← hshape.2.1, angleAt_eq]; rfl
  have aC : ∠ A C B = β := by rw [← hshape.2.2, angleAt_eq]; rfl
  -- `E = A + t (C - A)` with `0 < t < 1`
  obtain ⟨t, ⟨t0, t1⟩, hEt⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, E = A + t • (C - A) := by
    rw [segment_eq_image_lineMap] at hE
    obtain ⟨t, ht, rfl⟩ := hE
    exact ⟨t, ht, by rw [AffineMap.lineMap_apply_module']; abel⟩
  have vEB : E - B = (1 - t) • (A - B) + t • (C - B) := by rw [hEt]; module
  have hEB : E - B ≠ 0 := by
    intro h0
    have e := congrArg (cross (A - B)) h0
    rw [vEB, cross_add_right, cross_smul_right, cross_smul_right, Erdos634.Geometry.cross_self,
      mul_zero, zero_add, Erdos634.Geometry.cross_zero_right] at e
    have ht0 : t = 0 := (mul_eq_zero.mp e).resolve_right nB
    rw [hEt, ht0, zero_smul, add_zero] at h0
    exact nB (by rw [h0]; simp [cross])
  have hEB' : E ≠ B := fun h => hEB (by rw [h, sub_self])
  -- `∠ABC = ∠ABE + ∠EBC`
  have hadd : ∠ A B C = ∠ A B E + ∠ E B C := by
    simp only [EuclideanGeometry.angle, vsub_eq_sub]
    apply angle_add_cone nB hEB
    rw [vEB, cross_add_right, cross_smul_right, cross_smul_right, Erdos634.Geometry.cross_self,
      cross_add_left', cross_smul_left, cross_smul_left, Erdos634.Geometry.cross_self]
    constructor <;> nlinarith [sq_nonneg (cross (A - B) (C - B))]
  have aEBC : ∠ E B C = 2 * α := by rw [aB, hEα] at hadd; linarith
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hEt
    rw [hEt, EuclideanGeometry.angle_self_of_ne hBA.symm] at hEα; linarith
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [one_smul, add_sub_cancel] at hEt
    rw [hEt, aB] at hEα; linarith
  have tpos : 0 < t := lt_of_le_of_ne t0 (Ne.symm ht0)
  have tlt : t < 1 := lt_of_le_of_ne t1 ht1
  -- triangle `ABE`
  have aBAE : ∠ B A E = β := by
    rw [← aA]; simp only [EuclideanGeometry.angle, vsub_eq_sub]
    rw [show E - A = t • (C - A) by rw [hEt]; abel,
      InnerProductGeometry.angle_smul_right_of_pos _ _ tpos]
  have aAEB : ∠ A E B = γ := by
    have := EuclideanGeometry.angle_add_angle_add_angle_eq_pi E hBA
    rw [hEα, EuclideanGeometry.angle_comm B E A, EuclideanGeometry.angle_comm E A B, aBAE] at this
    linarith
  -- triangle `EBC`
  have aBCE : ∠ B C E = β := by
    rw [EuclideanGeometry.angle_comm, ← aC]; simp only [EuclideanGeometry.angle, vsub_eq_sub]
    rw [show E - C = (1 - t) • (A - C) by rw [hEt]; module,
      InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith)]
  have aCEB : ∠ C E B = α + β := by
    have := EuclideanGeometry.angle_add_angle_add_angle_eq_pi C hEB'.symm
    rw [aEBC, aBCE] at this
    linarith
  -- lengths
  have hdc : c / Real.sin γ = d := by rw [hsc]; field_simp
  have dAE : dist A E = j * k * a := by
    have h := EuclideanGeometry.law_sin B E A
    rw [EuclideanGeometry.angle_comm B E A, aAEB, hEα, dist_comm E A, hAB] at h
    rw [hsa]
    apply mul_right_cancel₀ sγ.ne'
    rw [mul_comm, h, hsc]; ring
  have dBE : dist B E = j * k * b := by
    have h := EuclideanGeometry.law_sin E A B
    rw [EuclideanGeometry.angle_comm E A B, aBAE, EuclideanGeometry.angle_comm B E A, aAEB,
      hAB] at h
    rw [hsb]
    apply mul_right_cancel₀ sγ.ne'
    rw [mul_comm, ← h, hsc]; ring
  have hcosα : 2 * Real.cos α * k ^ 2 = 2 * k ^ 2 - m ^ 2 := by
    have h := cos_of_sines (d := d) hsum
    rw [← hsa, ← hsb, ← hsc, ha, hb, hc] at h
    have hb0 : (0 : ℝ) < k ^ 2 - m ^ 2 := by
      have := mul_pos (sub_pos.mpr hmk') (add_pos hk hm')
      linarith [show ((k : ℝ) - m) * (k + m) = k ^ 2 - m ^ 2 by ring]
    have : ((k : ℝ) ^ 2 - m ^ 2) * (2 * Real.cos α * k ^ 2 - (2 * k ^ 2 - m ^ 2)) = 0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb0.ne')
  have dEC : dist E C = j * m * (b + c) := by
    have h := EuclideanGeometry.law_sin B E C
    rw [EuclideanGeometry.angle_comm B E C, aCEB, EuclideanGeometry.angle_comm C B E, aEBC,
      hCB, show α + β = π - γ by linarith, Real.sin_pi_sub, Real.sin_two_mul] at h
    apply mul_right_cancel₀ sγ.ne'
    rw [mul_comm, h]
    have e2 : d * Real.sin α = m * k := by rw [← hsa, ha]
    linear_combination (2 * Real.sin α * Real.cos α * j * k) * hsc +
      (2 * j * k * Real.cos α * Real.sin γ) * e2 + (j * m * Real.sin γ) * hcosα -
      (j * m * Real.sin γ) * hb - (j * m * Real.sin γ) * hc
  have hAC : dist A C = j * m * (b + 2 * c) := by
    have hlc := EuclideanGeometry.law_cos B A C
    rw [aA, dist_comm B A, hAB, dist_comm B C, hCB, dist_comm C A] at hlc
    have hcosβ : 2 * Real.cos β * k ^ 3 = m * (3 * k ^ 2 - m ^ 2) := by
      have h := cos_of_sines (d := d) (show β + α + γ = π by linarith)
      rw [← hsa, ← hsb, ← hsc, ha, hb, hc] at h
      have : (m : ℝ) * (2 * Real.cos β * k ^ 3 - m * (3 * k ^ 2 - m ^ 2)) = 0 := by
        linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hm'.ne')
    have hY0 : 0 < dist A C := dist_pos.mpr (T.indep.injective.ne (by decide))
    have hY : dist A C = 2 * (j * k * c) * Real.cos β := by
      have : dist A C * (dist A C - 2 * (j * k * c) * Real.cos β) = 0 := by
        linear_combination -hlc
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hY0.ne')
    rw [hY, hc, hb]
    linear_combination (j : ℝ) * hcosβ
  refine ⟨hAC, ⟨aBAE, aAEB, dAE, dBE⟩, ⟨aEBC, aBCE, aCEB, by rw [dist_comm]; exact hCB, dBE, dEC⟩,
    dEC, ?_⟩
  exact dist_add_dist_of_mem_segment hE

end TriangleTiling.Prime
