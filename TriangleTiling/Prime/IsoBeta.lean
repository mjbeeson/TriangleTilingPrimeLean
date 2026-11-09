/-
Section 12 of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*: the shape `(β, β, 3α)`. `lemma:isobetasides`.

`ABC` is `D.target` with `A, B, C = pts 0, pts 1, pts 2`, base angles `β` at `A` and `C`, vertex
angle `3α` at `B`; `X = |AB|`, `Y = |AC|`. The integer `j` is that of the paper's equation
`N = j²(3k² - m²)` (`TriangleTiling3` Theorem 19, Lean `ThreeAlpha.notprime4`), taken as a hypothesis.

Statements checked by Beeson.
-/
import TriangleTiling.Prime.RunsLong
import TriangleTiling.ThreeAlpha.Areas

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

variable {N : ℕ}

/-- The model's corner angles, through the permutation of `TileSides`. -/
theorem model_sides {D : CongruentDissection N} {α β γ a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) :
    a * c * Real.sin β = ThreeAlpha.circumdiam D.model ^ 2 *
      (Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
        Real.sin (D.model.angleAt 2)) ∧
    b ^ 2 = a ^ 2 + c ^ 2 - 2 * a * c * Real.cos β := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  set d := ThreeAlpha.circumdiam D.model
  have hla := ThreeAlpha.lawsin D.model (σ 0)
  have hlc := ThreeAlpha.lawsin D.model (σ 2)
  rw [l0, h0] at hla; rw [l2, h2] at hlc
  have hprod : Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
      Real.sin (D.model.angleAt 2) = Real.sin α * Real.sin β * Real.sin γ := by
    rw [← h0, ← h1, ← h2]
    have := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
    simp only [Fin.prod_univ_three] at this
    linarith
  refine ⟨by rw [hprod, hla, hlc]; ring, ?_⟩
  -- the law of cosines at the `β` corner
  have hlc' := EuclideanGeometry.law_cos (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1))
    (D.model.pts (σ 1 + 2))
  have hang : ∠ (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1)) (D.model.pts (σ 1 + 2)) = β := h1
  have hopp : dist (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1 + 2)) = b := l1
  rw [hang, hopp] at hlc'
  have d01 : σ 1 ≠ σ 0 := σ.injective.ne (by decide)
  have d21 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have d02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have ea : D.model.oppLen (σ 0) = a := l0
  have ec : D.model.oppLen (σ 2) = c := l2
  have adj : ∀ v : Fin 3, dist (D.model.pts (v + 1)) (D.model.pts v) = D.model.oppLen (v + 2) ∧
      dist (D.model.pts (v + 2)) (D.model.pts v) = D.model.oppLen (v + 1) := by
    intro v; unfold Tri.oppLen
    fin_cases v <;> exact ⟨dist_comm _ _, rfl⟩
  obtain ⟨x1, x2⟩ := adj (σ 1)
  rcases fin3_others d01 d21 d02 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have y1 : dist (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1)) = c := by rw [x1, ← e2, ec]
    have y2 : dist (D.model.pts (σ 1 + 2)) (D.model.pts (σ 1)) = a := by rw [x2, ← e1, ea]
    rw [y1, y2] at hlc'; linarith
  · have y1 : dist (D.model.pts (σ 1 + 1)) (D.model.pts (σ 1)) = a := by rw [x1, ← e1, ea]
    have y2 : dist (D.model.pts (σ 1 + 2)) (D.model.pts (σ 1)) = c := by rw [x2, ← e2, ec]
    rw [y1, y2] at hlc'; linarith

/-- **Lemma `lemma:isobetasides`** (Isosceles-`β` side lengths). Let `ABC` be the isosceles
triangle with angles `(β, β, 3α)`, with `X` the length of each of its two equal sides and `Y` the
length of its base. Suppose `ABC` is `N`-tiled by `(a, b, c)`. Then `X = jk³ = jkc`,
`Y = jm(3k² - m²) = jm(b + 2c)`, `Y/X = a(b + 2c)/c²`, and `Y < 2X`.

`(a, b, c) = (mk, k² - m², k²)` as throughout the section, and `j > 0` with `N = j²(3k² - m²)`. -/
theorem isobetasides {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = π) (hm : 0 < m)
    (hmk : m < k) (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    {j : ℤ} (hj : 0 < j) (hN : (N : ℝ) = j ^ 2 * (3 * k ^ 2 - m ^ 2)) :
    dist (D.target.pts 1) (D.target.pts 2) = dist (D.target.pts 0) (D.target.pts 1) ∧
    dist (D.target.pts 0) (D.target.pts 1) = j * k ^ 3 ∧
    dist (D.target.pts 0) (D.target.pts 1) = j * k * c ∧
    dist (D.target.pts 0) (D.target.pts 2) = j * m * (3 * k ^ 2 - m ^ 2) ∧
    dist (D.target.pts 0) (D.target.pts 2) = j * m * (b + 2 * c) ∧
    dist (D.target.pts 0) (D.target.pts 2) / dist (D.target.pts 0) (D.target.pts 1) =
      a * (b + 2 * c) / c ^ 2 ∧
    dist (D.target.pts 0) (D.target.pts 2) < 2 * dist (D.target.pts 0) (D.target.pts 1) := by
  obtain ⟨hα, hβ, hγ, hsum⟩ := ThreeAlpha.tileSides_angles D hT
  obtain ⟨hA, hB, hC⟩ := hshape
  set T := D.target
  set X := dist (T.pts 0) (T.pts 1)
  set Y := dist (T.pts 0) (T.pts 2)
  set dT := ThreeAlpha.circumdiam T
  have hX : X = dT * Real.sin β := by
    have := ThreeAlpha.lawsin T 2; rw [hC] at this; rw [← this]; unfold Tri.oppLen; rfl
  have hBC : dist (T.pts 1) (T.pts 2) = dT * Real.sin β := by
    have := ThreeAlpha.lawsin T 0; rw [hA] at this; rw [← this]; rfl
  have hY : Y = dT * Real.sin (3 * α) := by
    have := ThreeAlpha.lawsin T 1; rw [hB] at this; rw [← this]; unfold Tri.oppLen
    exact dist_comm _ _
  -- the area equation `N a c = X Y`
  obtain ⟨hmodel, hcosb⟩ := model_sides hT
  have harea := ThreeAlpha.area_sines D
  rw [← hmodel, hA, hB, hC] at harea
  have hsb := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hNac : (N : ℝ) * (a * c) = X * Y := by
    rw [hX, hY]
    have := mul_right_cancel₀ hsb.ne' (show (N : ℝ) * (a * c) * Real.sin β =
      dT ^ 2 * Real.sin β * Real.sin (3 * α) * Real.sin β by linarith)
    linarith
  -- `Y = 2X cos β`
  have hlc := EuclideanGeometry.law_cos (T.pts 1) (T.pts 0) (T.pts 2)
  have hang : ∠ (T.pts 1) (T.pts 0) (T.pts 2) = β := hA
  rw [hang, hBC, dist_comm (T.pts 1) (T.pts 0), dist_comm (T.pts 2) (T.pts 0)] at hlc
  have hX0 : 0 < X := dist_pos.mpr (T.indep.injective.ne (by decide))
  have hY0 : 0 < Y := dist_pos.mpr (T.indep.injective.ne (by decide))
  rw [← hX] at hlc
  have hYX : Y = 2 * X * Real.cos β := by
    have : Y * (Y - 2 * X * Real.cos β) = 0 := by linear_combination -hlc
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  -- the tile's `cos β`
  have hk : (0 : ℝ) < k := by have : (0 : ℝ) < m := by exact_mod_cast hm
                              have : (m : ℝ) < k := by exact_mod_cast hmk
                              linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hcos : Real.cos β = m * (3 * k ^ 2 - m ^ 2) / (2 * k ^ 3) := by
    rw [ha, hb, hc] at hcosb
    rw [eq_div_iff (by positivity)]
    have : (m : ℝ) * (Real.cos β * (2 * k ^ 3) - m * (3 * k ^ 2 - m ^ 2)) = 0 := by
      linear_combination hcosb
    have := (mul_eq_zero.mp this).resolve_left hm'.ne'
    linarith
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have h3 : (0 : ℝ) < 3 * k ^ 2 - m ^ 2 := by
    have : (m : ℝ) < k := by exact_mod_cast hmk
    nlinarith
  -- `X = j k³`
  have hXv : X = j * k ^ 3 := by
    have h1 := hNac
    rw [hYX, hcos, hN, ha, hc] at h1
    have h' : X ^ 2 * (m * (3 * k ^ 2 - m ^ 2)) =
        (k : ℝ) ^ 3 * (X * (2 * X * (m * (3 * k ^ 2 - m ^ 2) / (2 * k ^ 3)))) := by
      field_simp
    rw [← h1] at h'
    have h2 : X ^ 2 * (m * (3 * k ^ 2 - m ^ 2)) =
        ((j : ℝ) * k ^ 3) ^ 2 * (m * (3 * k ^ 2 - m ^ 2)) := by rw [h']; ring
    have h3' := mul_right_cancel₀ (by positivity : (m : ℝ) * (3 * k ^ 2 - m ^ 2) ≠ 0) h2
    exact (sq_eq_sq₀ hX0.le (by positivity)).mp h3'
  have hYv : Y = j * m * (3 * k ^ 2 - m ^ 2) := by
    rw [hYX, hXv, hcos]; field_simp
  refine ⟨by rw [hBC, ← hX], hXv, by rw [hXv, hc]; ring, hYv, by rw [hYv, hb, hc]; ring, ?_, ?_⟩
  · rw [hYv, hXv, ha, hb, hc]; field_simp; ring
  · rw [hYX]
    have : Real.cos β < 1 := by
      rw [hcos, div_lt_one (by positivity)]
      have hmk' : (m : ℝ) < k := by exact_mod_cast hmk
      have : 0 < ((k : ℝ) - m) ^ 2 * (2 * k + m) := by
        have := sub_pos.mpr hmk'; positivity
      linarith [show ((k : ℝ) - m) ^ 2 * (2 * k + m) = 2 * k ^ 3 - m * (3 * k ^ 2 - m ^ 2) by ring]
    have := mul_lt_mul_of_pos_left this hX0
    linarith

end TriangleTiling.Prime
