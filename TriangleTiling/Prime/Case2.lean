/-
Section 4 of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*: the shape `(α, 2α, 3β)` tiled by `(α, β, 2π/3)`. This file has the proof of
`theorem:case2` from the point where the sides of the tile are known to be commensurable
(`lemma:rationality3`, which needs Beeson–Zhang and is in `TriangleTiling.Laczkovich`).
-/
import TriangleTiling.Prime.Group2Base

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

/-- **`theorem:case2`, after commensurability.** Let `T` have angles `(α, 2α, 3β)` (at its vertices
`0, 1, 2`) and be `N`-tiled by `(α, β, 2π/3)` with sides `(a, b, c)`, and suppose
`(a, b, c) = μ(a', b', c')` with `a', b', c'` integers with no common factor. Then
`N = 3λ²(a' + 2b')(a' + b')` with `λ` a positive integer, and `N` is not prime. -/
theorem case2core {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = 2 * α)
    (hC : D.target.angleAt 2 = 3 * β) {μ : ℝ} (hμ : 0 < μ) {a' b' c' : ℕ}
    (hg : Nat.gcd (Nat.gcd a' b') c' = 1) (ea : a = μ * a') (eb : b = μ * b') (ec : c = μ * c') :
    ∃ l : ℕ, 0 < l ∧ N = 3 * l ^ 2 * (a' + 2 * b') * (a' + b') ∧ ¬ N.Prime := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  obtain ⟨ha, hb, hc, hc2, hαβ, sα, cα, sβ, cβ⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  have hc0 : c ≠ 0 := hc.ne'
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  -- the tile in integers
  have ha' : (0 : ℝ) < a' := by
    have := ea ▸ ha; exact pos_of_mul_pos_right this hμ.le
  have hb' : (0 : ℝ) < b' := by
    have := eb ▸ hb; exact pos_of_mul_pos_right this hμ.le
  have hc2' : (c' : ℝ) ^ 2 = (a' : ℝ) ^ 2 + a' * b' + b' ^ 2 := by
    rw [ea, eb, ec] at hc2
    have hμ2 : μ ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hμ2
    linear_combination hc2
  have hc2N : c' ^ 2 = a' ^ 2 + b' ^ 2 + a' * b' := by
    have : ((c' ^ 2 : ℕ) : ℝ) = ((a' ^ 2 + b' ^ 2 + a' * b' : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  -- The law of sines for `T`: `X : sin α = Y : sin 2α = Z : sin 3β`, and `sin 3β = sin 3α`.
  set dT := ThreeAlpha.circumdiam D.target
  have hX := ThreeAlpha.lawsin D.target 0
  have hY := ThreeAlpha.lawsin D.target 1
  have hZ := ThreeAlpha.lawsin D.target 2
  rw [hA] at hX; rw [hB] at hY; rw [hC] at hZ
  have h3β : sin (3 * β) = sin (3 * α) := by
    rw [show 3 * β = π - 3 * α by linarith, Real.sin_pi_sub]
  rw [h3β] at hZ
  set X := D.target.oppLen 0
  set Y := D.target.oppLen 1
  set Z := D.target.oppLen 2
  -- `sin² α = 3a²/(4c²)` and `3 - 4 sin² α = 3b(a + b)/c²`
  have hS2 : sin α ^ 2 = 3 * a ^ 2 / (4 * c ^ 2) := by
    rw [sα, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
  have h34 : 3 - 4 * sin α ^ 2 = 3 * b * (a + b) / c ^ 2 := by
    rw [hS2, eq_div_iff (pow_ne_zero 2 hc0)]
    have e : 4 * (3 * a ^ 2 / (4 * c ^ 2)) * c ^ 2 = 3 * a ^ 2 := by field_simp
    linear_combination 3 * hc2 - e
  -- `(X, Y, Z) = λ (c², c(a + 2b), 3b(a + b))`
  set lam := X / c ^ 2 with hlam
  have eX : X = lam * c ^ 2 := by rw [hlam]; field_simp
  have eY : Y = lam * (c * (a + 2 * b)) := by
    rw [hY, Real.sin_two_mul, cα, hlam, hX]
    field_simp
  have eZ : Z = lam * (3 * b * (a + b)) := by
    have : sin (3 * α) = sin α * (3 - 4 * sin α ^ 2) := by rw [Real.sin_three_mul]; ring
    rw [hZ, this, h34, hlam, hX]
    field_simp
  -- `λμ` is an integer, by `lemma:BLZ30` and `lemma:claude3`.
  have hgcd := BLZ30 hc2N hg
  obtain ⟨n, hn⟩ := lambda_int D σ hμ (l0.trans ea) (l1.trans eb) (l2.trans ec) hgcd
    (l := lam * μ)
    (by show X = _; rw [eX, ec]; push_cast; ring)
    (by show Y = _; rw [eY, ec, ea, eb]; push_cast; ring)
    (by show Z = _; rw [eZ, ea, eb]; push_cast; ring)
  -- The area equation: `N a² sin β sin γ = X² sin 2α sin 3α`.
  have hE := area_sines' D σ
  rw [h0, h1, h2, hA, hB, hC, h3β] at hE
  have hdm := ThreeAlpha.lawsin D.model (σ 0)
  rw [h0, l0] at hdm
  have E2 : (N : ℝ) * a ^ 2 * (sin β * sin (2 * π / 3)) =
      X ^ 2 * (sin (2 * α) * sin (3 * α)) := by
    rw [hdm, hX]; linear_combination sin α * hE
  have hβγ : sin β * sin (2 * π / 3) = 3 * b / (4 * c) := by
    rw [sβ, sin_two_pi_div_three]; field_simp; rw [Real.sq_sqrt (by norm_num)]; ring
  have h23 : sin (2 * α) * sin (3 * α) =
      2 * ((a + 2 * b) / (2 * c)) * (3 * a ^ 2 / (4 * c ^ 2)) * (3 * b * (a + b) / c ^ 2) := by
    rw [Real.sin_two_mul, show sin (3 * α) = sin α * (3 - 4 * sin α ^ 2) by
      rw [Real.sin_three_mul]; ring, h34, cα, ← hS2]
    ring
  rw [hβγ, h23, eX] at E2
  -- So `N = 3λ²(a + 2b)(a + b) = 3(λμ)²(a' + 2b')(a' + b')`.
  have hNr : (N : ℝ) = 3 * lam ^ 2 * (a + 2 * b) * (a + b) := by
    have hk : a ^ 2 * (3 * b / (4 * c)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hk
    rw [← mul_assoc, E2]
    field_simp
    try ring
  have hNn : N = 3 * n ^ 2 * (a' + 2 * b') * (a' + b') := by
    have : (N : ℝ) = 3 * (n : ℝ) ^ 2 * (a' + 2 * b') * (a' + b') := by
      rw [hNr, ← hn, ea, eb]; ring
    exact_mod_cast this
  have hn0 : 0 < n := by
    have hXpos : 0 < X := D.target.oppLen_pos 0
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero] at hn
      have : lam = 0 := by
        rcases mul_eq_zero.mp hn with h | h
        · exact h
        · exact absurd h hμ.ne'
      rw [eX, this, zero_mul] at hXpos
      exact lt_irrefl _ hXpos
    · exact h0
  refine ⟨n, hn0, hNn, ?_⟩
  -- `3 ∣ N` and `N ≥ 18`.
  rw [hNn, show 3 * n ^ 2 * (a' + 2 * b') * (a' + b') = 3 * (n ^ 2 * (a' + 2 * b') * (a' + b'))
    by ring]
  have ha1 : 1 ≤ a' := by exact_mod_cast ha'
  have hb1 : 1 ≤ b' := by exact_mod_cast hb'
  have hpos : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn0
  apply Nat.not_prime_mul (by norm_num)
  have : 6 ≤ n ^ 2 * (a' + 2 * b') * (a' + b') := by
    calc 6 = 1 * 3 * 2 := by norm_num
      _ ≤ n ^ 2 * (a' + 2 * b') * (a' + b') := by gcongr <;> omega
  omega

end TriangleTiling.Prime
