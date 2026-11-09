/-
`lemma:no24` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723).

Statement checked by Beeson. For `N = 24`, `lemma:square60` leaves only the coloring
number `M = 4` (`(9N - M²)(N - M²)` is not a square for `M = 1, 2, 3`); then `sixty_main` gives
`{a/c, b/c} = {3/7, 8/7}` and the area equation `X² = Nab` gives `X = 24c/7`. The tile `(3, 8, 7)`
in the triangle of side `24` is ruled out by `no24geom` (`TriangleTiling/Equilateral/No24.lean`).
-/
import TriangleTiling.Laczkovich.EquilateralSixty
import TriangleTiling.Equilateral.No24

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha

/-- An integer whose square is strictly between `k²` and `(k + 1)²` is not a square. -/
theorem not_square_between (n k : ℤ) (h1 : k ^ 2 < n) (h2 : n < (k + 1) ^ 2) (hk : 0 ≤ k) :
    ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have hr : r * r = |r| * |r| := (abs_mul_abs_self r).symm
  rw [hr] at h1 h2
  have ha := abs_nonneg r
  have h3 : k < |r| := by nlinarith
  have h4 : |r| < k + 1 := by nlinarith
  omega

/-- **Lemma `lemma:no24`.** Suppose the equilateral triangle `ABC` is `N`-tiled by a tile
`(α, β, π/3)` with `α` not a rational multiple of `π`. Then `N ≠ 24`. -/
theorem no24 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hT : TileSides D α β (Real.pi / 3) a b c)
    (hα : IrrPi α) : N ≠ 24 := by
  intro hN
  subst hN
  have hβ := irr_beta_of_alpha D hT hα
  obtain ⟨-, -, hS, -, harea, e1, e2, pa, pb, pc, -⟩ := sixty_setup D hP hT hβ
  obtain ⟨i₀, hi₀⟩ := exists_atA_onAB D
  obtain ⟨ε, hε, h1⟩ := exists_colouring D hα hS i₀
  obtain ⟨hM0, hMlt, hsq⟩ := square60 D hP hT hα hε hi₀ h1
  obtain ⟨-, -, hs, hprod, -⟩ := sixty_main D hP hT hβ hε hi₀ h1
  set M : ℤ := ∑ i, ε i with hMdef
  -- `M = 4`.
  have hM4 : M = 4 := by
    have hMr : (M : ℝ) ^ 2 < 24 := by
      have h0 : (0 : ℝ) ≤ M := by exact_mod_cast hM0.le
      have := Real.sqrt_nonneg (24 : ℝ)
      have h24 : Real.sqrt ((24 : ℕ) : ℝ) ^ 2 = 24 := by
        rw [Real.sq_sqrt (by positivity)]; norm_num
      nlinarith
    have hM : M ^ 2 < 24 := by exact_mod_cast hMr
    have hle : M ≤ 4 := by nlinarith
    push_cast at hsq
    interval_cases M
    · exact absurd hsq (not_square_between _ 70 (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hsq (not_square_between _ 65 (by norm_num) (by norm_num) (by norm_num))
    · exact absurd hsq (not_square_between _ 55 (by norm_num) (by norm_num) (by norm_num))
    · rfl
  rw [show ((∑ i, ε i : ℤ) : ℝ) = 4 by rw [← hMdef, hM4]; norm_num] at hs hprod
  push_cast at hs hprod
  norm_num at hs hprod
  -- `a/c` and `b/c` are `3/7` and `8/7`.
  set u := c / 7 with hudef
  have hu : 0 < u := by positivity
  have hc : c = 7 * u := by rw [hudef]; ring
  have hroot : (a / c - 3 / 7) * (a / c - 8 / 7) = 0 := by
    have hb' : b / c = 11 / 7 - a / c := by linarith
    rw [hb'] at hprod
    linear_combination -hprod
  have hside : ∀ k, D.target.oppLen k = 24 * u := by
    have h0 : D.target.oppLen 0 = 24 * u := by
      have hpos := D.target.oppLen_pos 0
      rcases mul_eq_zero.mp hroot with h | h
      · have ha : a = 3 * u := by field_simp at h; linarith
        have hb : b = 8 * u := by
          have := hs; rw [← add_div, div_eq_iff pc.ne'] at this; linarith
        have : D.target.oppLen 0 ^ 2 = (24 * u) ^ 2 := by rw [harea, ha, hb]; push_cast; ring
        nlinarith
      · have ha : a = 8 * u := by field_simp at h; linarith
        have hb : b = 3 * u := by
          have := hs; rw [← add_div, div_eq_iff pc.ne'] at this; linarith
        have : D.target.oppLen 0 ^ 2 = (24 * u) ^ 2 := by rw [harea, ha, hb]; push_cast; ring
        nlinarith
    intro k
    fin_cases k
    · exact h0
    · exact e1.trans h0
    · exact e2.trans h0
  rcases mul_eq_zero.mp hroot with h | h
  · have ha : a = 3 * u := by field_simp at h; linarith
    have hb : b = 8 * u := by
      have := hs; rw [← add_div, div_eq_iff pc.ne'] at this; linarith
    rw [ha, hb, hc] at hT
    exact no24geom D hu hP hT hα hside
  · have ha : a = 8 * u := by field_simp at h; linarith
    have hb : b = 3 * u := by
      have := hs; rw [← add_div, div_eq_iff pc.ne'] at this; linarith
    rw [ha, hb, hc] at hT
    exact no24geom D hu hP (tileSides_swap D hT) hβ hside

end TriangleTiling.Equilateral
