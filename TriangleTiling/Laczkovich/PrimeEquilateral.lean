/-
`theorem:equilateral` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of
congruent triangles* (Section 2): an equilateral triangle `N`-tiled with `N > 3` has `N` not prime.

Statement checked by Beeson. The proof is the paper's: by Laczkovich (Bonfioli's
`equilateral_classification`, from Laczkovich 2012 Theorem 3.3, UNAUDITED) the tile is one of
(i) `(π/3, π/3, π/3)`, (ii) `(π/6, π/6, 2π/3)`, (iii) `(π/6, π/2, π/3)`, (iv) `(α, β, π/3)`,
(v) `(α, β, 2π/3)` with `α` not a rational multiple of `π`. Case (i) is a reptiling
(`theorem:reptile`), so `N` is a square; (ii) and (iii) are the paper's argument with
`(p + q√3)²`; (iv) and (v) are the equilateral paper's Theorems 3 and 6 (`notprime60`,
`notprime120`).
-/
import TriangleTiling.Laczkovich.PrimeReptile
import TriangleTiling.Laczkovich.EquilateralSixty
import TriangleTiling.Laczkovich.EquilateralNotPrime120
import TriangleTiling.Prime.Group2Base
import Erdos634.Draft.LaczFormalL56Final

namespace TriangleTiling.Prime

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Real
open Erdos634.Draft.LaczFormal (TileAngles)

/-- If `(u + q√3)² = M` with `u, q, M` natural numbers, then `uq = 0` and `M = u² + 3q²`. -/
theorem sq_add_sqrt3 {u q M : ℕ} (h : ((u : ℝ) + q * √3) ^ 2 = M) :
    u * q = 0 ∧ M = u ^ 2 + 3 * q ^ 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : (M : ℝ) = u ^ 2 + 3 * q ^ 2 + 2 * u * q * √3 := by
    rw [← h]; linear_combination (q : ℝ) ^ 2 * h3
  have huq : u * q = 0 := by
    by_contra hne
    have hne' : (2 * u * q : ℝ) ≠ 0 := by
      have : (u * q : ℝ) ≠ 0 := by exact_mod_cast hne
      intro h0; apply this; linarith
    apply Nat.prime_three.irrational_sqrt
    refine ⟨((M : ℚ) - u ^ 2 - 3 * q ^ 2) / (2 * u * q), ?_⟩
    push_cast
    rw [div_eq_iff hne', e]; ring
  refine ⟨huq, ?_⟩
  have : (M : ℝ) = u ^ 2 + 3 * q ^ 2 := by
    rw [e]; have : (u : ℝ) * q = 0 := by exact_mod_cast huq
    linear_combination 2 * √3 * this
  exact_mod_cast this

/-- The sides of a tile whose angles are rational multiples of `π` given by `TileAngles`, in terms
of its circumdiameter (law of sines). -/
theorem oppLen_of_angles {N : ℕ} (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    D.model.oppLen (σ j) = ThreeAlpha.circumdiam D.model * sin (D.model.angleAt (σ j)) :=
  ThreeAlpha.lawsin D.model (σ j)

/-- A side of `T` is a sum of tile edges, each of length `x` or `x√3`: it is `(u + q√3) x`. -/
theorem side_sqrt3 {N : ℕ} (D : CongruentDissection N) {x : ℝ}
    (h : ∀ k, D.model.oppLen k = x ∨ D.model.oppLen k = x * √3) (k : Fin 3) :
    ∃ u q : ℕ, D.target.oppLen k = ((u : ℝ) + q * √3) * x := by
  obtain ⟨P, Q, R, hPQR, -⟩ := D.toDissection.side_walk_abc (k + 1) x (x * √3) x (fun j m => by
    rcases edge_len_mem D j m with e | e | e
    · rcases h 0 with h' | h'
      · left; rw [e]; exact h'
      · right; left; rw [e]; exact h'
    · rcases h 1 with h' | h'
      · left; rw [e]; exact h'
      · right; left; rw [e]; exact h'
    · rcases h 2 with h' | h'
      · left; rw [e]; exact h'
      · right; left; rw [e]; exact h')
  refine ⟨P + R, Q, ?_⟩
  have e : D.target.oppLen k = dist (D.target.pts (k + 1)) (D.target.pts (k + 1 + 1)) := by
    unfold Tri.oppLen; rw [add_assoc, show (1 : Fin 3) + 1 = 2 from rfl]
  rw [e, ← hPQR]; push_cast; ring

/-- **Theorem `theorem:equilateral`.** Let `T` be an equilateral triangle `N`-tiled, for `N > 3`.
Then the number of tiles `N` is not a prime. -/
theorem equilateral {N : ℕ} (D : CongruentDissection N) (hEq : ∀ k, D.target.angleAt k = π / 3)
    (hN : 3 < N) : ¬ N.Prime := by
  intro hp
  have hπ := Real.pi_pos
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 : 0 < √3 := by positivity
  -- The area equation, with all angles of `T` equal to `π/3`:
  -- `N d_R² sin α sin β sin γ = d_T² (√3/2)³`, and `X = d_T √3/2` for each side `X` of `T`.
  have hX := ThreeAlpha.lawsin D.target 0
  rw [hEq, Real.sin_pi_div_three] at hX
  have harea : ∀ σ : Equiv.Perm (Fin 3), (N : ℝ) * (ThreeAlpha.circumdiam D.model ^ 2 *
      (sin (D.model.angleAt (σ 0)) * sin (D.model.angleAt (σ 1)) * sin (D.model.angleAt (σ 2))))
      = ThreeAlpha.circumdiam D.target ^ 2 * (√3 / 2) ^ 3 := by
    intro σ
    rw [area_sines' D σ, hEq, hEq, hEq, Real.sin_pi_div_three]; ring
  set dT := ThreeAlpha.circumdiam D.target
  set dm := ThreeAlpha.circumdiam D.model
  have hdm : 0 < dm := ThreeAlpha.circumdiam_pos _
  rcases Erdos634.Draft.LaczFormal.equilateral_classification D hEq with
    ⟨α, hα, σ, h0, h1, h2⟩ | ⟨α, hα, σ, h0, h1, h2⟩ | h | ⟨σ, h0, h1, h2⟩ | ⟨σ, h0, h1, h2⟩
  · -- (iv): Theorem 3 of the equilateral paper
    exact Equilateral.notprime60 D hEq ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩ hα hp
  · -- (v): Theorem 6 of the equilateral paper
    exact Equilateral.notprime120 D hEq ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩ hα hp
  · -- (i): a reptiling, so `N` is a square (the tile is neither right nor `(π/6, π/3, π/2)`)
    obtain ⟨σ, h0, h1, h2⟩ := h
    have hm : ∀ k, D.model.angleAt k = π / 3 := by
      intro k; obtain ⟨j, rfl⟩ := σ.surjective k
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    have hsim : SimilarTM D := by
      refine ⟨dT / dm, Equiv.refl _, fun k => ⟨by rw [hEq, Equiv.refl_apply, hm], ?_⟩⟩
      rw [Equiv.refl_apply, ThreeAlpha.lawsin D.target k, ThreeAlpha.lawsin D.model k, hEq, hm]
      have hdm' : dm ≠ 0 := hdm.ne'
      field_simp
      rfl
    rcases reptile D hsim with ⟨r, hr⟩ | ⟨M, K, -, i, j, k, -, -, -, hk, -⟩ | ⟨-, τ, t0, t1, t2⟩
    · rw [hr] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨hq, e⟩ | ⟨hq, e⟩ <;>
        · subst e; exact Nat.not_prime_one hq
    · rw [hm] at hk; linarith
    · rw [hm] at t0; linarith
  · -- (ii): `(π/6, π/6, 2π/3)`, sides `x, x, x√3`
    set x := dm / 2
    have hside : ∀ k, D.model.oppLen k = x ∨ D.model.oppLen k = x * √3 := by
      intro k; obtain ⟨j, rfl⟩ := σ.surjective k
      rw [oppLen_of_angles]
      fin_cases j
      · left; show dm * sin (D.model.angleAt (σ 0)) = x; rw [h0, Real.sin_pi_div_six]; ring
      · left; show dm * sin (D.model.angleAt (σ 1)) = x; rw [h1, Real.sin_pi_div_six]; ring
      · right; show dm * sin (D.model.angleAt (σ 2)) = x * √3
        rw [h2, sin_two_pi_div_three]; ring
    obtain ⟨u, q, hXuq⟩ := side_sqrt3 D hside 0
    -- `N x² = X²`, so `N = (u + q√3)²`
    have hA := harea σ
    rw [h0, h1, h2, Real.sin_pi_div_six, sin_two_pi_div_three] at hA
    have hN2 : ((u : ℝ) + q * √3) ^ 2 = N := by
      have hx : 0 < x := by positivity
      have hdT : dT = 2 * D.target.oppLen 0 / √3 := by rw [hX]; field_simp
      rw [hdT, hXuq] at hA
      have e : dm = 2 * x := by simp only [x]; ring
      rw [e] at hA
      field_simp at hA
      rw [hA]; ring
    obtain ⟨huq, hNuq⟩ := sq_add_sqrt3 hN2
    rcases Nat.mul_eq_zero.mp huq with hu | hq
    · -- `N = 3q²`, prime only for `N = 3`
      subst hu
      rw [hNuq] at hp hN
      rcases Nat.prime_mul_iff.mp (by simpa using hp) with ⟨-, e⟩ | ⟨-, e⟩
      · simp [e] at hN
      · exact absurd e (by norm_num)
    · -- `N = u²`, a square
      subst hq
      rw [hNuq] at hp
      simp only [mul_zero, add_zero, pow_two] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨hq, e⟩ | ⟨hq, e⟩ <;>
        · subst e; exact Nat.not_prime_one hq
  · -- (iii): `(π/6, π/3, π/2)`, sides `x, x√3, 2x`
    set x := dm / 2
    have hside : ∀ k, D.model.oppLen k = x ∨ D.model.oppLen k = x * √3 ∨ D.model.oppLen k = 2 * x := by
      intro k; obtain ⟨j, rfl⟩ := σ.surjective k
      rw [oppLen_of_angles]
      fin_cases j
      · left; show dm * sin (D.model.angleAt (σ 0)) = x; rw [h0, Real.sin_pi_div_six]; ring
      · right; left; show dm * sin (D.model.angleAt (σ 1)) = x * √3
        rw [h1, Real.sin_pi_div_three]; ring
      · right; right; show dm * sin (D.model.angleAt (σ 2)) = 2 * x
        rw [h2, Real.sin_pi_div_two]; ring
    obtain ⟨P, Q, R, hPQR, -⟩ := D.toDissection.side_walk_abc (0 + 1) x (x * √3) (2 * x)
      (fun j m => by
        rcases edge_len_mem D j m with e | e | e <;> rw [e]
        · exact hside 0
        · exact hside 1
        · exact hside 2)
    set u := P + 2 * R with hu_def
    have hXuq : D.target.oppLen 0 = ((u : ℝ) + Q * √3) * x := by
      show dist (D.target.pts (0 + 1)) (D.target.pts (0 + 2)) = _
      rw [show (0 : Fin 3) + 2 = 0 + 1 + 1 from rfl, ← hPQR, hu_def]; push_cast; ring
    -- `2N x² = X²`, so `2N = (u + q√3)²`
    have hA := harea σ
    rw [h0, h1, h2, Real.sin_pi_div_six, Real.sin_pi_div_three, Real.sin_pi_div_two] at hA
    have hN2 : ((u : ℝ) + Q * √3) ^ 2 = ((2 * N : ℕ) : ℝ) := by
      have hx : 0 < x := by positivity
      have hdT : dT = 2 * D.target.oppLen 0 / √3 := by rw [hX]; field_simp
      rw [hdT, hXuq] at hA
      have e : dm = 2 * x := by simp only [x]; ring
      rw [e] at hA
      field_simp at hA
      rw [Nat.cast_mul, Nat.cast_two]
      linarith
    obtain ⟨huq, hNuq⟩ := sq_add_sqrt3 hN2
    rcases Nat.mul_eq_zero.mp huq with hu | hq
    · -- `2N = 3q²`: `q = 2w`, `N = 6w²`, not prime
      rw [hu] at hNuq
      have h2q : 2 ∣ Q := by
        have : 2 ∣ 3 * Q ^ 2 := ⟨N, by omega⟩
        exact Nat.prime_two.dvd_of_dvd_pow
          ((Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 2 3)).mp this)
      obtain ⟨w, rfl⟩ := h2q
      have : N = 2 * (3 * w ^ 2) := by nlinarith [hNuq]
      rw [this] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨-, e⟩ | ⟨-, e⟩
      · omega
      · omega
    · -- `2N = u²`: `u = 2w`, `N = 2w²`, prime only for `N = 2`
      rw [hq] at hNuq
      have h2u : 2 ∣ u := by
        have : 2 ∣ u ^ 2 := ⟨N, by omega⟩
        exact Nat.prime_two.dvd_of_dvd_pow this
      obtain ⟨w, hw⟩ := h2u
      rw [hw] at hNuq
      have : N = 2 * w ^ 2 := by nlinarith [hNuq]
      rw [this] at hp hN
      rcases Nat.prime_mul_iff.mp hp with ⟨-, e⟩ | ⟨-, e⟩
      · rw [e] at hN; omega
      · omega

end TriangleTiling.Prime
