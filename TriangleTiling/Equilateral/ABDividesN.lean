/-
`corollary:abdividesN` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723):
`N = m² ab`, so `N` is not prime. Statement checked by Beeson.

The proof is the paper's: the area equation `X² = Nab` and `X = m ab` (`abdividesX`). Neither
`a` nor `b` is `1`: `c² = a² + b² ± ab` is not a square when one of them is `1` and the other is
at least `2`, and `a = b` would force `α = β`.
-/
import TriangleTiling.Equilateral.ABDividesX
import TriangleTiling.ThreeAlpha.Components

namespace TriangleTiling.Equilateral

open Erdos634.Geometry TriangleTiling.ThreeAlpha

/-- `1 + b² + s b` (`s = ±1`) is not a square for `b ≥ 2`. -/
theorem not_sq_one {b c s : ℤ} (hb : 2 ≤ b) (hs : s = 1 ∨ s = -1) (hc : 0 ≤ c)
    (h : c ^ 2 = 1 + b ^ 2 + s * b) : False := by
  rcases hs with rfl | rfl
  · have h1 : b < c := by nlinarith
    have h2 : c < b + 1 := by nlinarith
    omega
  · have h1 : b - 1 < c := by nlinarith
    have h2 : c < b := by nlinarith
    omega

/-- **Corollary `corollary:abdividesN`.** Suppose the equilateral triangle `ABC` is tiled by a tile
with angles `(α, β, γ)`, where `α` is not a rational multiple of `π`, and `γ = π/3` or `2π/3`.
Suppose the tile has integer side lengths `(a, b, c)` with no common factor. Then `N = m² ab` for
some `m`. In particular, `N` is not prime. -/
theorem abdividesN {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ} {a b c : ℕ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hT : TileSides D α β γ a b c)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hγ : γ = Real.pi / 3 ∨ γ = 2 * Real.pi / 3)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ m : ℕ, N = m ^ 2 * (a * b) ∧ ¬ N.Prime := by
  obtain ⟨m, hm⟩ := abdividesX D hP hT hα hγ hgcd
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have hπ := Real.pi_pos
  have hs3 : 0 < Real.sin (Real.pi / 3) := by rw [Real.sin_pi_div_three]; positivity
  have hsγ : Real.sin γ = Real.sin (Real.pi / 3) := by
    rcases hγ with rfl | rfl
    · rfl
    · rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
  -- The area equation `X² = N a b`.
  have harea : D.target.oppLen 0 ^ 2 = N * a * b := by
    have h := area_sines D
    have hprod : Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
        Real.sin (D.model.angleAt 2) = Real.sin α * Real.sin β * Real.sin γ := by
      have e := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
      simp only [Fin.prod_univ_three] at e
      rw [← e, h0, h1, h2]
    rw [hprod, hP 0, hP 1, hP 2] at h
    have ha := lawsin D.model (σ 0)
    have hb := lawsin D.model (σ 1)
    rw [l0, h0] at ha
    rw [l1, h1] at hb
    have hX := lawsin D.target 0
    rw [hP 0] at hX
    rw [hsγ] at h
    have : ((N : ℝ) * a * b - D.target.oppLen 0 ^ 2) * Real.sin (Real.pi / 3) = 0 := by
      rw [ha, hb, hX]; linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  have pa : (0 : ℝ) < a := l0 ▸ D.model.oppLen_pos _
  have pb : (0 : ℝ) < b := l1 ▸ D.model.oppLen_pos _
  have hN : (N : ℝ) = m ^ 2 * (a * b) := by
    rw [hm] at harea
    have : (a : ℝ) * b ≠ 0 := by positivity
    apply mul_right_cancel₀ this
    linear_combination -harea
  have hN' : N = m ^ 2 * (a * b) := by exact_mod_cast hN
  refine ⟨m, hN', ?_⟩
  -- `a, b ≥ 2`.
  obtain ⟨s, hs, hcos⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + s * a * b := by
    have hl := D.model.lawCos_perm σ
    rw [l0, l1, l2, h2] at hl
    rcases hγ with rfl | rfl
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [Real.cos_pi_div_three] at hl
      have : ((c : ℤ) : ℝ) ^ 2 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (-1 : ℤ) * a * b := by
        push_cast; linarith
      exact_mod_cast this
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three] at hl
      have : ((c : ℤ) : ℝ) ^ 2 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + (1 : ℤ) * a * b := by
        push_cast; linarith
      exact_mod_cast this
  have hαβ : α ≠ β := by
    intro e
    have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) =
        Real.pi := by
      have e' := Equiv.sum_comp σ (fun k => D.model.angleAt k)
      simp only [Fin.sum_univ_three] at e'
      rw [e', D.model.angleAt_sum]
    rw [h0, h1, h2, ← e] at hsum
    apply hα
    rcases hγ with rfl | rfl
    · exact ⟨1 / 3, by push_cast; linarith⟩
    · exact ⟨1 / 6, by push_cast; linarith⟩
  have hab : a ≠ b := by
    have := sides_ne_of_angles_ne D ⟨σ, h0, h1, h2, l0, l1, l2⟩ hαβ
    exact_mod_cast this
  have ha0 : 0 < a := by exact_mod_cast pa
  have hb0 : 0 < b := by exact_mod_cast pb
  have ha2 : 2 ≤ a := by
    by_contra h
    have h1 : a = 1 := by omega
    subst h1
    have hb2 : 2 ≤ b := by omega
    exact not_sq_one (b := b) (c := c) (s := s) (by exact_mod_cast hb2) hs (by positivity)
      (by rw [hcos]; push_cast; ring)
  have hb2 : 2 ≤ b := by
    by_contra h
    have h1 : b = 1 := by omega
    subst h1
    exact not_sq_one (b := a) (c := c) (s := s) (by exact_mod_cast ha2) hs (by positivity)
      (by rw [hcos]; push_cast; ring)
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := D.target.oppLen_pos 0
    rw [hm] at this; simp at this
  rw [hN', show m ^ 2 * (a * b) = (m ^ 2 * a) * b by ring]
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hm0)
  exact Nat.not_prime_mul (by intro h; nlinarith) (by omega)

end TriangleTiling.Equilateral
