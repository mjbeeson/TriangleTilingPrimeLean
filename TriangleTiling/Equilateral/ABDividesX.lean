/-
`theorem:abdividesX` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723): if an
equilateral triangle with side `X` is tiled by a tile with angles `(α, β, γ)`, `α ∉ ℚπ`,
`γ = π/3` or `2π/3`, and integer sides `(a, b, c)` with no common factor, then `ab ∣ X`.

Statement checked by Beeson. The proof is the paper's (due to J. P. Harries). For each
`n : ℤ` let `χₙ(θ₀ + kα + jπ/3) = (-1)^j` if `k = n` and `0` otherwise, `θ₀` the direction of
`AB`; this is the coefficient of `zⁿ` in the paper's `χ`. Each `χₙ` is odd, so Bonfioli's
`flux_cancel` gives `Σᵢ Φₙ(tᵢ) = Φₙ(∂ABC)` for every `n`. A tile contributes
`ε (d [k = n] + s c [k - τ = n])` with `ε, τ = ±1`, where `s = 1`, `d = a - b` if `γ = 2π/3` and
`s = -1`, `d = a + b` if `γ = π/3`; the boundary contributes `3X [n = 0]`. Substituting
`z = -s d c⁻¹` in `ℤ/3abℤ` kills every tile, since `c² - d² = 3sab`, so `3ab ∣ 3X`.
-/
import TriangleTiling.ThreeAlpha.PhiTiling

namespace TriangleTiling.Equilateral

open Erdos634.Geometry TriangleTiling.ThreeAlpha

namespace ABDividesX

/-! ### Number theory -/

theorem prime_ne_unit {p s : ℤ} (hp : Prime p) (hs : s = 1 ∨ s = -1) : ¬ p ∣ s := by
  intro h
  apply hp.not_unit
  rcases hs with rfl | rfl
  · exact isUnit_of_dvd_one h
  · exact isUnit_of_dvd_one (by simpa using h)

/-- A prime dividing `3` divides only multiples of `3`. -/
theorem three_of_dvd_three {p x : ℤ} (hp : Prime p) (h3 : p ∣ 3) (hx : p ∣ x) : (3 : ℤ) ∣ x := by
  have h := Int.natAbs_dvd_natAbs.mpr h3
  have hx' := Int.natAbs_dvd_natAbs.mpr hx
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ h) with h1 | h1
  · exact absurd (Int.isUnit_iff_natAbs_eq.mpr h1) hp.not_unit
  · rw [h1] at hx'
    exact Int.natAbs_dvd_natAbs.mp hx'

theorem isCoprime_of_primes {x y : ℤ} (h : ∀ p : ℤ, Prime p → p ∣ x → p ∣ y → False) :
    IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  obtain ⟨p, hp, hpd⟩ := Int.exists_prime_and_dvd (n := (Int.gcd x y : ℤ)) (by simpa using hg)
  exact h p hp (hpd.trans (Int.gcd_dvd_left x y)) (hpd.trans (Int.gcd_dvd_right x y))

theorem isUnit_of_isCoprime {n : ℕ} {x : ℤ} (h : IsCoprime x (n : ℤ)) : IsUnit (x : ZMod n) := by
  obtain ⟨u, v, huv⟩ := h
  have e := congrArg (fun t : ℤ => (t : ZMod n)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
    add_zero, Int.cast_one] at e
  exact isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact e⟩

/-- `c` and `d = a - s b` are units mod `3ab`. -/
theorem units {a b c s : ℤ} (hs : s = 1 ∨ s = -1)
    (hcos : c ^ 2 = a ^ 2 + b ^ 2 + s * a * b)
    (hprim : ∀ p : ℤ, Prime p → p ∣ a → p ∣ b → p ∣ c → False) {n : ℕ}
    (hn : (n : ℤ) = 3 * a * b) :
    IsUnit (c : ZMod n) ∧ IsUnit ((a - s * b : ℤ) : ZMod n) := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  set d := a - s * b with hd
  have hcd : c ^ 2 - d ^ 2 = 3 * s * a * b := by
    rw [hd]; linear_combination hcos - b ^ 2 * hs2
  have h3 : Prime (3 : ℤ) := Int.prime_three
  have pab : ∀ p : ℤ, Prime p → p ∣ a → p ∣ b → False := by
    intro p hp ha hb
    have h2 : p ∣ c ^ 2 := by
      rw [hcos]
      exact dvd_add (dvd_add (dvd_pow ha two_ne_zero) (dvd_pow hb two_ne_zero))
        (dvd_mul_of_dvd_right hb _)
    exact hprim p hp ha hb (hp.dvd_of_dvd_pow h2)
  have pac : ∀ p : ℤ, Prime p → p ∣ a → p ∣ c → False := by
    intro p hp ha hc
    have h2 : p ∣ b ^ 2 := by
      rw [show b ^ 2 = c ^ 2 - a ^ 2 - s * a * b by linear_combination -hcos]
      exact dvd_sub (dvd_sub (dvd_pow hc two_ne_zero) (dvd_pow ha two_ne_zero))
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha _) _)
    exact hprim p hp ha (hp.dvd_of_dvd_pow h2) hc
  have pbc : ∀ p : ℤ, Prime p → p ∣ b → p ∣ c → False := by
    intro p hp hb hc
    have h2 : p ∣ a ^ 2 := by
      rw [show a ^ 2 = c ^ 2 - b ^ 2 - s * a * b by linear_combination -hcos]
      exact dvd_sub (dvd_sub (dvd_pow hc two_ne_zero) (dvd_pow hb two_ne_zero))
        (dvd_mul_of_dvd_right hb _)
    exact hprim p hp (hp.dvd_of_dvd_pow h2) hb hc
  -- `3 ∤ c`
  have h3c : ¬ (3 : ℤ) ∣ c := by
    intro hc3
    have hd3 : (3 : ℤ) ∣ d := h3.dvd_of_dvd_pow (n := 2) (by
      rw [show d ^ 2 = c ^ 2 - 3 * (s * a * b) by linear_combination -hcd]
      exact dvd_sub (dvd_pow hc3 two_ne_zero) (dvd_mul_right _ _))
    obtain ⟨u, hu⟩ := hc3
    obtain ⟨v, hv⟩ := hd3
    have h9 : (3 : ℤ) ∣ s * (a * b) := ⟨u ^ 2 - v ^ 2, by
      have : c ^ 2 - d ^ 2 = 3 * (s * (a * b)) := by rw [hcd]; ring
      rw [hu, hv] at this; linarith⟩
    rcases h3.dvd_or_dvd h9 with h | h
    · exact prime_ne_unit h3 hs h
    rcases h3.dvd_or_dvd h with ha | hb
    · exact pab 3 h3 ha (by
        have : (3 : ℤ) ∣ s * b := by
          rw [show s * b = a - d by rw [hd]; ring]; exact dvd_sub ha ⟨v, hv⟩
        rcases h3.dvd_or_dvd this with h' | h'
        · exact absurd h' (prime_ne_unit h3 hs)
        · exact h')
    · exact pab 3 h3 (by
        rw [show a = d + s * b by rw [hd]; ring]
        exact dvd_add ⟨v, hv⟩ (dvd_mul_of_dvd_right hb _)) hb
  refine ⟨isUnit_of_isCoprime (isCoprime_of_primes fun p hp hc hn' => ?_),
    isUnit_of_isCoprime (isCoprime_of_primes fun p hp hdp hn' => ?_)⟩
  · rw [hn] at hn'
    rcases hp.dvd_or_dvd hn' with h | hb
    · rcases hp.dvd_or_dvd h with h | ha
      · exact h3c (three_of_dvd_three hp h hc)
      · exact pac p hp ha hc
    · exact pbc p hp hb hc
  · rw [hn] at hn'
    rcases hp.dvd_or_dvd hn' with h | hb
    · rcases hp.dvd_or_dvd h with h | ha
      · have hd3 := three_of_dvd_three hp h hdp
        apply h3c
        exact h3.dvd_of_dvd_pow (n := 2) (by
          rw [show c ^ 2 = d ^ 2 + 3 * (s * a * b) by linear_combination hcd]
          exact dvd_add (dvd_pow hd3 two_ne_zero) (dvd_mul_right _ _))
      · refine pab p hp ha ?_
        have : p ∣ s * b := by
          rw [show s * b = a - d by rw [hd]; ring]; exact dvd_sub ha hdp
        rcases hp.dvd_or_dvd this with h' | h'
        · exact absurd h' (prime_ne_unit hp hs)
        · exact h'
    · refine pab p hp ?_ hb
      rw [show a = d + s * b by rw [hd]; ring]
      exact dvd_add hdp (dvd_mul_of_dvd_right hb _)

/-- **The reduction mod `3ab`.** If the coefficients of the tiles add up to `K [m = 0]`, then
`K ≡ 0 (mod 3ab)`. -/
theorem zmod_core {ι : Type*} [Fintype ι] {a b c s : ℤ} (hs : s = 1 ∨ s = -1)
    (hcos : c ^ 2 = a ^ 2 + b ^ 2 + s * a * b)
    (hprim : ∀ p : ℤ, Prime p → p ∣ a → p ∣ b → p ∣ c → False) {n : ℕ}
    (hn : (n : ℤ) = 3 * a * b) (ε k τ : ι → ℤ) (hτ : ∀ i, τ i = 1 ∨ τ i = -1) (K : ℤ)
    (hcoef : ∀ m : ℤ, ∑ i, ε i * ((a - s * b) * (if k i = m then 1 else 0) +
        s * c * (if k i - τ i = m then 1 else 0)) = if m = 0 then K else 0) :
    (K : ZMod n) = 0 := by
  classical
  obtain ⟨hc, hd⟩ := units hs hcos hprim hn
  set d := a - s * b with hd'
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hcd : c ^ 2 - d ^ 2 = s * (3 * a * b) := by
    rw [hd']; linear_combination hcos - b ^ 2 * hs2
  have hn0 : ((3 * a * b : ℤ) : ZMod n) = 0 := by
    rw [← hn]; simp
  have hcz : (c : ZMod n) ^ 2 = (d : ZMod n) ^ 2 := by
    have e := congrArg (fun t : ℤ => (t : ZMod n)) hcd
    push_cast at e hn0
    rw [hn0, mul_zero] at e
    exact sub_eq_zero.mp e
  have hsz : (s : ZMod n) * s = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : ZMod n)) hs2
  -- the substitution `z ↦ u = -s d c⁻¹`
  set cu := hc.unit
  set du := hd.unit
  obtain ⟨su, hsu⟩ : ∃ su : (ZMod n)ˣ, (su : ZMod n) = s := by
    rcases hs with rfl | rfl
    · exact ⟨1, by simp⟩
    · exact ⟨-1, by simp⟩
  set u : (ZMod n)ˣ := -(su * du * cu⁻¹)
  have hcc : (c : ZMod n) * ↑cu⁻¹ = 1 := by
    rw [show (c : ZMod n) = cu from (hc.unit_spec).symm]; exact Units.mul_inv cu
  have hdd : (d : ZMod n) * ↑du⁻¹ = 1 := by
    rw [show (d : ZMod n) = du from (hd.unit_spec).symm]; exact Units.mul_inv du
  have hsinv : ((su⁻¹ : (ZMod n)ˣ) : ZMod n) = s := by
    have : (su : ZMod n) * ↑su⁻¹ = 1 := Units.mul_inv su
    rw [hsu] at this
    linear_combination (s : ZMod n) * this - (↑su⁻¹ : ZMod n) * hsz
  have hu : (u : ZMod n) = -(s * d * ↑cu⁻¹) := by
    simp only [u, Units.val_neg, Units.val_mul, hsu, cu, du, hd.unit_spec]
  have huinv : ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = -(s * c * ↑du⁻¹) := by
    simp only [u, inv_neg, mul_inv_rev, inv_inv, Units.val_neg, Units.val_mul, hsinv, cu,
      hc.unit_spec]
    ring
  have hz1 : (d : ZMod n) + s * c * u = 0 := by
    rw [hu]; linear_combination (-(d : ZMod n)) * hcc - (d : ZMod n) * (c : ZMod n) * ↑cu⁻¹ * hsz
  have hz2 : (d : ZMod n) + s * c * ↑(u⁻¹) = 0 := by
    rw [huinv]
    linear_combination (-((c : ZMod n) ^ 2 * ↑du⁻¹)) * hsz + (-(↑du⁻¹ : ZMod n)) * hcz
      + (-(d : ZMod n)) * hdd
  -- sum the coefficient identity against `uᵐ` over a finite set of exponents
  set S : Finset ℤ := insert 0 (Finset.univ.image k ∪ Finset.univ.image fun i => k i - τ i)
  have hkS : ∀ i, k i ∈ S := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hkτS : ∀ i, k i - τ i ∈ S := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun i => k i - τ i) (Finset.mem_univ i)))
  have key := congrArg (fun f : ℤ → ℤ => ∑ m ∈ S, ((f m : ℤ) : ZMod n) * ((u ^ m : (ZMod n)ˣ) : ZMod n))
    (funext hcoef)
  simp only at key
  -- right side: `K`
  have hR : ∑ m ∈ S, (((if m = 0 then K else 0 : ℤ) : ZMod n)) * ((u ^ m : (ZMod n)ˣ) : ZMod n)
      = K := by
    rw [Finset.sum_eq_single (0 : ℤ)]
    · simp
    · intro m _ hm; simp [hm]
    · intro h; exact absurd (Finset.mem_insert_self 0 _) h
  -- left side: `0`
  have hL : ∑ m ∈ S, ((∑ i, ε i * (d * (if k i = m then 1 else 0) +
        s * c * (if k i - τ i = m then 1 else 0)) : ℤ) : ZMod n) * ((u ^ m : (ZMod n)ˣ) : ZMod n)
      = 0 := by
    push_cast
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have e1 : ∑ m ∈ S, (ε i : ZMod n) * ((d : ZMod n) * (if k i = m then 1 else 0) +
        (s : ZMod n) * c * (if k i - τ i = m then 1 else 0)) * ((u ^ m : (ZMod n)ˣ) : ZMod n)
        = (ε i : ZMod n) * ((d : ZMod n) * ((u ^ k i : (ZMod n)ˣ) : ZMod n) +
          (s : ZMod n) * c * ((u ^ (k i - τ i) : (ZMod n)ˣ) : ZMod n)) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul,
        zero_mul]
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (hkS i), if_pos (hkτS i)]
      ring
    rw [e1, zpow_sub, Units.val_mul]
    rcases hτ i with h | h <;> rw [h]
    · simp only [zpow_one]
      rw [show (ε i : ZMod n) * ((d : ZMod n) * ↑(u ^ k i) + ↑s * ↑c * (↑(u ^ k i) * ↑u⁻¹))
          = ε i * ↑(u ^ k i) * (↑d + ↑s * ↑c * ↑u⁻¹) by ring, hz2, mul_zero]
    · simp only [zpow_neg, zpow_one, inv_inv]
      rw [show (ε i : ZMod n) * ((d : ZMod n) * ↑(u ^ k i) + ↑s * ↑c * (↑(u ^ k i) * ↑u))
          = ε i * ↑(u ^ k i) * (↑d + ↑s * ↑c * ↑u) by ring, hz1, mul_zero]
  rw [← hR, ← key, hL]


/-! ### The directions `θ₀ + kα + jπ/3` and the coefficient functions `χₙ` -/

section Chi

variable (α : ℝ) (θ₀ : Real.Angle)

/-- The direction `θ₀ + kα + jπ/3`. -/
noncomputable def ang (k j : ℤ) : Real.Angle := θ₀ + ((k * α + j * (Real.pi / 3) : ℝ) : Real.Angle)

/-- `χₙ(θ₀ + kα + jπ/3) = (-1)^j` if `k = n`, and `0` otherwise (also `0` off the coset): the
coefficient of `zⁿ` in the paper's `χ`. -/
noncomputable def chi (n : ℤ) (θ : Real.Angle) : ℝ :=
  open Classical in if h : ∃ j : ℤ, θ = ang α θ₀ n j then (-1 : ℝ) ^ h.choose else 0

variable {α θ₀}

theorem ang_add (k j k' j' : ℤ) :
    ang α θ₀ k j + ((k' * α + j' * (Real.pi / 3) : ℝ) : Real.Angle) = ang α θ₀ (k + k') (j + j') := by
  unfold ang; rw [add_assoc, ← Real.Angle.coe_add]; congr 2; push_cast; ring

theorem ang_add' {k j k' j' : ℤ} {t : ℝ} (ht : t = k' * α + j' * (Real.pi / 3)) :
    ang α θ₀ k j + (t : Real.Angle) = ang α θ₀ (k + k') (j + j') := by rw [ht, ang_add]

theorem ang_congr {k j k' j' : ℤ} (hk : k = k') (hj : j = j') : ang α θ₀ k j = ang α θ₀ k' j' := by
  rw [hk, hj]

theorem back {x y : Real.Angle} {t : ℝ} (h : y = x + (t : Real.Angle)) :
    x = y + ((-t : ℝ) : Real.Angle) := by
  rw [h, Real.Angle.coe_neg, add_neg_cancel_right]

theorem ang_inj (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) {k j k' j' : ℤ}
    (h : ang α θ₀ k j = ang α θ₀ k' j') : k = k' ∧ ∃ t : ℤ, j = j' + 6 * t := by
  unfold ang at h
  obtain ⟨t, ht⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (add_left_cancel h)
  have hk : k = k' := by
    by_contra hne
    have hne' : (3 * (k - k') : ℝ) ≠ 0 := by
      have : ((k - k' : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
      push_cast at this; positivity
    apply hα
    refine ⟨(6 * t - (j - j')) / (3 * (k - k')), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hne']
    linear_combination 3 * ht
  subst hk
  refine ⟨rfl, t, ?_⟩
  have e : (j : ℝ) * Real.pi = (j' + 6 * t) * Real.pi := by linear_combination 3 * ht
  exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero e

theorem chi_eval (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (n k j : ℤ) :
    chi α θ₀ n (ang α θ₀ k j) = if k = n then (-1 : ℝ) ^ j else 0 := by
  unfold chi
  by_cases hkn : k = n
  · subst hkn
    have h : ∃ j' : ℤ, ang α θ₀ k j = ang α θ₀ k j' := ⟨j, rfl⟩
    rw [dif_pos h, if_pos rfl]
    have hc := h.choose_spec
    generalize h.choose = j' at hc ⊢
    obtain ⟨-, t, ht⟩ := ang_inj hα hc
    rw [ht, zpow_add₀ (by norm_num), (show Even (6 * t) from ⟨3 * t, by ring⟩).neg_one_zpow,
      mul_one]
  · rw [if_neg hkn, dif_neg]
    rintro ⟨j', hj'⟩
    exact hkn (ang_inj hα hj').1

theorem chi_odd (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (n : ℤ) (θ : Real.Angle) :
    chi α θ₀ n (θ + (Real.pi : Real.Angle)) = - chi α θ₀ n θ := by
  have hpi : (Real.pi : ℝ) = ((0 : ℤ) : ℝ) * α + ((3 : ℤ) : ℝ) * (Real.pi / 3) := by push_cast; ring
  by_cases h : ∃ j, θ = ang α θ₀ n j
  · obtain ⟨j, rfl⟩ := h
    rw [ang_add' hpi, chi_eval hα, chi_eval hα, add_zero, if_pos rfl, if_pos rfl,
      zpow_add₀ (by norm_num)]
    norm_num
  · have h1 : chi α θ₀ n θ = 0 := by unfold chi; rw [dif_neg h]
    have h2 : chi α θ₀ n (θ + (Real.pi : Real.Angle)) = 0 := by
      unfold chi
      rw [dif_neg]
      rintro ⟨j, hj⟩
      apply h
      refine ⟨j - 3, ?_⟩
      have e := back hj.symm
      rw [ang_add' (k' := 0) (j' := -3) (by push_cast; ring)] at e
      rw [e]; exact ang_congr (by ring) (by ring)
    rw [h1, h2, neg_zero]

end Chi

/-! ### The tiles -/

/-- The triangle `T` has angles `(α, β, γ)` with opposite sides `(a, b, c)`. -/
def TriSides (T : Tri) (α β γ a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.angleAt (σ 1) = β ∧ T.angleAt (σ 2) = γ ∧
    T.oppLen (σ 0) = a ∧ T.oppLen (σ 1) = b ∧ T.oppLen (σ 2) = c

theorem tile_sides {N : ℕ} {D : CongruentDissection N} {α β γ a b c : ℝ}
    (h : TileSides D α β γ a b c) (i : Fin N) : TriSides (D.tile i) α β γ a b c := by
  obtain ⟨σ, h0, h1, h2, h0', h1', h2'⟩ := h
  obtain ⟨τ, hτ⟩ := (D.tiles_congruent i).exists_perm
  refine ⟨σ.trans τ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Equiv.trans_apply, (hτ _).1, (hτ _).2, Equiv.apply_symm_apply] <;> assumption

variable {α β γ a b c : ℝ} {g : ℤ}

theorem angle_sum {T : Tri} (h : TriSides T α β γ a b c) : α + β + γ = Real.pi := by
  obtain ⟨σ, h0, h1, h2, -⟩ := h
  have e := Equiv.sum_comp σ (fun k => T.angleAt k)
  simp only [Fin.sum_univ_three] at e
  rw [← h0, ← h1, ← h2, e, T.angleAt_sum]

/-- The exterior angles are in `ℤα + ℤπ/3`. -/
theorem ext_mem {T : Tri} (h : TriSides T α β γ a b c) (hg : γ = g * (Real.pi / 3)) (v : Fin 3) :
    ∃ k' j' : ℤ, Real.pi - T.angleAt v = k' * α + j' * (Real.pi / 3) := by
  have hs := angle_sum h
  obtain ⟨σ, h0, h1, h2, -⟩ := h
  obtain ⟨m, rfl⟩ := σ.surjective v
  rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) m with rfl | rfl | rfl
  · exact ⟨-1, 3, by rw [h0]; push_cast; ring⟩
  · exact ⟨1, g, by rw [h1]; push_cast; linear_combination -hs + hg⟩
  · exact ⟨0, 3 - g, by rw [h2, hg]; push_cast; ring⟩

/-- Once one edge of a tile is in the coset, all are. -/
theorem all_edges {T : Tri} (h : TriSides T α β γ a b c) (hg : γ = g * (Real.pi / 3))
    {θ₀ : Real.Angle} {w : Fin 3} {m j : ℤ} (h₀ : edir T w = ang α θ₀ m j) :
    ∀ v, ∃ m' j' : ℤ, edir T v = ang α θ₀ m' j' := by
  obtain ⟨s, -, ht⟩ := turn T
  have step : ∀ (w : Fin 3) (m j : ℤ), edir T w = ang α θ₀ m j →
      ∃ m' j' : ℤ, edir T (w + 1) = ang α θ₀ m' j' := by
    intro w m j hw
    have h' := ht (w + 2)
    rw [(by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) w, (by decide : ∀ x : Fin 3, x + 2 + 1 = x) w] at h'
    obtain ⟨k', j', e⟩ := ext_mem h hg (w + 2)
    exact ⟨m + s * k', j + s * j', by
      rw [h', hw, ang_add' (k' := s * k') (j' := s * j') (by rw [e]; push_cast; ring)]⟩
  obtain ⟨m1, j1, h1⟩ := step w m j h₀
  obtain ⟨m2, j2, h2⟩ := step (w + 1) m1 j1 h1
  intro v
  rcases (by decide : ∀ w v : Fin 3, v = w ∨ v = w + 1 ∨ v = w + 1 + 1) w v with
    rfl | rfl | rfl
  · exact ⟨m, j, h₀⟩
  · exact ⟨m1, j1, h1⟩
  · exact ⟨m2, j2, h2⟩

/-- The directions of the `b` and `c` edges from that of the `a` edge. -/
theorem tile_dirs {T : Tri} (h : TriSides T α β γ a b c) (hg : γ = g * (Real.pi / 3))
    {θ₀ : Real.Angle} {k j : ℤ} {σ : Equiv.Perm (Fin 3)} (_hσ0 : T.angleAt (σ 0) = α)
    (hσ1 : T.angleAt (σ 1) = β) (hσ2 : T.angleAt (σ 2) = γ)
    (hA : edir T (σ 0) = ang α θ₀ k j) :
    ∃ τ : ℤ, (τ = 1 ∨ τ = -1) ∧ edir T (σ 1) = ang α θ₀ k (j + τ * (3 - g)) ∧
      edir T (σ 2) = ang α θ₀ (k - τ) (j - τ * g) := by
  have hs := angle_sum h
  obtain ⟨s, hs1, ht⟩ := turn T
  set A := σ 0
  set B := σ 1
  set C := σ 2
  have hAB : A ≠ B := σ.injective.ne (by decide)
  have hAC : A ≠ C := σ.injective.ne (by decide)
  have hBC : B ≠ C := σ.injective.ne (by decide)
  have hcase : (B = A + 1 ∧ C = A + 2) ∨ (B = A + 2 ∧ C = A + 1) := by
    revert hAB hAC hBC; generalize A = x; generalize B = y; generalize C = z; revert x y z
    decide
  have hA2 := ht (A + 2)
  rw [(by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) A, (by decide : ∀ x : Fin 3, x + 2 + 1 = x) A] at hA2
  have hA1 := ht (A + 1)
  rw [(by decide : ∀ x : Fin 3, x + 1 + 2 = x) A, (by decide : ∀ x : Fin 3, x + 1 + 1 = x + 2) A] at hA1
  rcases hcase with ⟨hB, hC⟩ | ⟨hB, hC⟩
  · refine ⟨s, hs1, ?_, ?_⟩
    · rw [hB, hA2, ← hC, hσ2, hA, ang_add' (k' := 0) (j' := s * (3 - g)) (by rw [hg]; push_cast; ring)]
      exact ang_congr (by ring) rfl
    · rw [← hB, hσ1] at hA1
      rw [hC, back hA1, hA, ang_add' (k' := -s) (j' := -(s * g))
        (by rw [show β = Real.pi - γ - α by linarith, hg]; push_cast; ring)]
      exact ang_congr (by ring) (by ring)
  · refine ⟨-s, by rcases hs1 with h | h <;> simp [h], ?_, ?_⟩
    · rw [← hC, hσ2] at hA1
      rw [hB, back hA1, hA, ang_add' (k' := 0) (j' := -(s * (3 - g)))
        (by rw [hg]; push_cast; ring)]
      exact ang_congr (by ring) (by ring)
    · rw [hC, hA2, ← hB, hσ1, hA, ang_add' (k' := s) (j' := s * g)
        (by rw [show β = Real.pi - γ - α by linarith, hg]; push_cast; ring)]
      exact ang_congr (by ring) (by ring)

section Tiling

variable {N : ℕ} (D : CongruentDissection N) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
  (hT : TileSides D α β γ a b c) (hg : γ = g * (Real.pi / 3))
include hT hg

/-- **Every edge direction of the tiling is `θ₀ + kα + jπ/3`**, `θ₀` the direction of `AB`. -/
theorem edges_in_coset (i : Fin N) (v : Fin 3) :
    ∃ k j : ℤ, edir (D.tile i) v = ang α (baseDir D) k j := by
  classical
  obtain ⟨⟨i₀, k₀⟩, hmem⟩ : (D.toDissection.sideEdges 0).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hsum := D.toDissection.side_len_sum 0
    rw [hne, Finset.sum_empty] at hsum
    have : D.target.pts 0 ≠ D.target.pts (0 + 1) := fun e =>
      absurd (D.target.indep.injective e) (by decide)
    exact this (dist_eq_zero.mp hsum.symm)
  have hsub : D.toDissection.eSet (i₀, k₀) ⊆ D.target.edge 0 := by
    unfold Dissection.sideEdges at hmem
    exact (Finset.mem_filter.mp hmem).2
  have hdir : ((D.tile i₀).leftUnit k₀).angle = baseDir D := by
    have := D.toDissection.eDir_of_side hsub
    unfold baseDir
    exact congrArg Dir.angle this
  have hP : ∀ j, Relation.ReflTransGen (fun a b => D.toDissection.Adj a b) i₀ j →
      ∀ v : Fin 3, ∃ k j' : ℤ, edir (D.tile j) v = ang α (baseDir D) k j' := by
    intro j hj
    induction hj with
    | refl =>
      have h₀ : edir (D.tile i₀) (k₀ + 2) = ang α (baseDir D) 0 0 := by
        rw [← leftUnit_eq_edir, hdir]; simp [ang]
      exact all_edges (tile_sides hT i₀) hg h₀
    | @tail j₁ c' _ hbc ih =>
      obtain ⟨k, l, hkl⟩ := hbc.leftUnit_neg
      obtain ⟨m, e, hn⟩ := ih (k + 2)
      have h₀ : edir (D.tile c') (l + 2) = ang α (baseDir D) m (e + 3) := by
        rw [← leftUnit_eq_edir, show (D.tile c').leftUnit l = Dir.neg ((D.tile j₁).leftUnit k) from hkl,
          Dir.angle_neg, leftUnit_eq_edir, hn, ang_add' (k' := 0) (j' := 3) (by push_cast; ring),
          add_zero]
      exact all_edges (tile_sides hT c') hg h₀
  exact hP i (D.toDissection.adjConnected i₀ i) v

omit hT hg in
theorem PhiR_sides {T : Tri} {σ : Equiv.Perm (Fin 3)} (h0 : T.oppLen (σ 0) = a)
    (h1 : T.oppLen (σ 1) = b) (h2 : T.oppLen (σ 2) = c) (Φ : Real.Angle → ℝ) :
    PhiR Φ T = a * Φ (edir T (σ 0)) + b * Φ (edir T (σ 1)) + c * Φ (edir T (σ 2)) := by
  rw [PhiR_eq, ← Equiv.sum_comp σ, Fin.sum_univ_three, h0, h1, h2]

omit hT in
include hα in
/-- **One tile.** With `s = 1`, `d = a - b` if `γ = 2π/3` and `s = -1`, `d = a + b` if `γ = π/3`,
a tile contributes `ε (d [k = n] + s c [k - τ = n])` to `Φₙ`. -/
theorem tile_phi {A B C s : ℤ} (hT' : TileSides D α β γ A B C)
    (hgs : (g = 1 ∧ s = -1) ∨ (g = 2 ∧ s = 1)) (i : Fin N) :
    ∃ k τ ε : ℤ, (τ = 1 ∨ τ = -1) ∧ ∀ n : ℤ, PhiR (chi α (baseDir D) n) (D.tile i) =
      ((ε * ((A - s * B) * (if k = n then 1 else 0) + s * C * (if k - τ = n then 1 else 0)) : ℤ) : ℝ) := by
  have hTi := tile_sides hT' i
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hTi
  obtain ⟨k, j, hA⟩ := edges_in_coset D hT' hg i (σ 0)
  obtain ⟨τ, hτ, hB, hC⟩ := tile_dirs (tile_sides hT' i) hg h0 h1 h2 hA
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε : ℝ) = (-1 : ℝ) ^ j := by
    rcases Int.even_or_odd j with he | ho
    · exact ⟨1, by rw [he.neg_one_zpow]; norm_num⟩
    · exact ⟨-1, by rw [ho.neg_one_zpow]; norm_num⟩
  have pB : (-1 : ℝ) ^ (j + τ * (3 - g)) = -(s : ℝ) * (-1) ^ j := by
    rw [zpow_add₀ (by norm_num)]
    rcases hgs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hτ with rfl | rfl <;> norm_num
  have pC : (-1 : ℝ) ^ (j - τ * g) = (s : ℝ) * (-1) ^ j := by
    rw [sub_eq_add_neg, zpow_add₀ (by norm_num)]
    rcases hgs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hτ with rfl | rfl <;> norm_num
  refine ⟨k, τ, ε, hτ, fun n => ?_⟩
  rw [PhiR_sides l0 l1 l2, hA, hB, hC, chi_eval hα, chi_eval hα, chi_eval hα, pB, pC]
  split_ifs <;> push_cast <;> rw [hε] <;> ring

omit hT hg in
include hα in
/-- **The boundary:** `Φₙ(∂ABC) = 3X [n = 0]`. -/
theorem target_phi (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (n : ℤ) :
    PhiR (chi α (baseDir D) n) D.target = if 0 = n then 3 * D.target.oppLen 0 else 0 := by
  obtain ⟨s, hs, ht⟩ := turn D.target
  have e2 : edir D.target 2 = ang α (baseDir D) 0 0 := by
    rw [show (2 : Fin 3) = 0 + 2 from rfl, ← leftUnit_eq_edir]; simp [ang, baseDir]
  have h1 := ht 1
  rw [show (1 : Fin 3) + 2 = 0 from rfl, show (1 : Fin 3) + 1 = 2 from rfl, hP 1, e2,
    ang_add' (k' := 0) (j' := 2 * s) (by push_cast; ring)] at h1
  have h2 := ht 2
  rw [show (2 : Fin 3) + 2 = 1 from rfl, show (2 : Fin 3) + 1 = 0 from rfl, hP 2, h1,
    ang_add' (k' := 0) (j' := 2 * s) (by push_cast; ring)] at h2
  have hsin : Real.sin (Real.pi / 3) ≠ 0 := by rw [Real.sin_pi_div_three]; positivity
  have s01 := D.target.lawSin 0 1
  have s02 := D.target.lawSin 0 2
  rw [hP, hP] at s01 s02
  have o1 : D.target.oppLen 1 = D.target.oppLen 0 := mul_left_cancel₀ hsin s01
  have o2 : D.target.oppLen 2 = D.target.oppLen 0 := mul_left_cancel₀ hsin s02
  rw [PhiR_eq, Fin.sum_univ_three, h1, h2, e2, chi_eval hα, chi_eval hα, chi_eval hα, o1, o2]
  have ev : ∀ t : ℤ, (-1 : ℝ) ^ (2 * t) = 1 := fun t => (show Even (2 * t) from ⟨t, by ring⟩).neg_one_zpow
  rw [show (0 : ℤ) + 2 * s + 2 * s = 2 * (2 * s) by ring, show (0 : ℤ) + 2 * s = 2 * s by ring, ev, ev,
    zpow_zero]
  simp only [add_zero]
  split_ifs <;> ring

end Tiling

end ABDividesX

open ABDividesX in
/-- **Theorem `theorem:abdividesX`** (due to J. P. Harries). Suppose the equilateral triangle `ABC`
is tiled by a tile with angles `(α, β, γ)`, where `α` is not a rational multiple of `π`, and
`γ = π/3` or `2π/3`. Suppose the tile has integer side lengths `(a, b, c)` with no common factor.
Then `ab` divides the side length `X` of `ABC`. -/
theorem abdividesX {N : ℕ} (D : CongruentDissection N) {α β γ : ℝ} {a b c : ℕ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hT : TileSides D α β γ a b c)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hγ : γ = Real.pi / 3 ∨ γ = 2 * Real.pi / 3)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ m : ℕ, D.target.oppLen 0 = m * (a * b) := by
  classical
  -- `γ = gπ/3` and the sign `s`
  obtain ⟨g, s, hg, hgs⟩ : ∃ g s : ℤ, γ = g * (Real.pi / 3) ∧ ((g = 1 ∧ s = -1) ∨ (g = 2 ∧ s = 1)) := by
    rcases hγ with h | h
    · exact ⟨1, -1, by rw [h]; push_cast; ring, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨2, 1, by rw [h]; push_cast; ring, Or.inr ⟨rfl, rfl⟩⟩
  have hs : s = 1 ∨ s = -1 := by rcases hgs with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have hT' : TileSides D α β γ ((a : ℤ) : ℝ) ((b : ℤ) : ℝ) ((c : ℤ) : ℝ) := by
    simpa only [Int.cast_natCast] using hT
  -- the law of cosines: `c² = a² + b² + s ab`
  have hcos : (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + s * a * b := by
    obtain ⟨σ, -, -, h2, l0, l1, l2⟩ := hT
    have hl := D.model.lawCos_perm σ
    rw [l0, l1, l2, h2] at hl
    have hcosγ : Real.cos γ = -(s : ℝ) / 2 := by
      rcases hgs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hg]; push_cast; rw [one_mul, Real.cos_pi_div_three]; norm_num
      · rw [hg, show ((2 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi - Real.pi / 3 by push_cast; ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; push_cast; ring
    rw [hcosγ] at hl
    have : ((c : ℤ) : ℝ) ^ 2 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 + s * a * b := by push_cast; linarith
    exact_mod_cast this
  -- no common prime factor
  have hprim : ∀ p : ℤ, Prime p → p ∣ (a : ℤ) → p ∣ (b : ℤ) → p ∣ (c : ℤ) → False := by
    intro p hp ha hb hc
    have ha' := Int.natAbs_dvd_natAbs.mpr ha
    have hb' := Int.natAbs_dvd_natAbs.mpr hb
    have hc' := Int.natAbs_dvd_natAbs.mpr hc
    simp only [Int.natAbs_natCast] at ha' hb' hc'
    have h1 : p.natAbs ∣ 1 := hgcd ▸ Nat.dvd_gcd (Nat.dvd_gcd ha' hb') hc'
    exact hp.not_unit (Int.isUnit_iff_natAbs_eq.mpr (Nat.dvd_one.mp h1))
  -- the coefficients of the tiles
  choose k τ ε hτ hφ using tile_phi D hα hg hT' hgs
  have hsum : ∀ n : ℤ, ∑ i, PhiR (chi α (baseDir D) n) (D.tile i)
      = PhiR (chi α (baseDir D) n) D.target := fun n =>
    D.flux_cancel (fun d => chi α (baseDir D) n d.angle) (fun d => by
      simp only [Dir.angle_neg]; exact chi_odd hα n _)
  set K : ℤ := ∑ i, ε i * (((a : ℤ) - s * b) * (if k i = 0 then 1 else 0) +
    s * c * (if k i - τ i = 0 then 1 else 0))
  have hcoef : ∀ m : ℤ, ∑ i, ε i * (((a : ℤ) - s * b) * (if k i = m then 1 else 0) +
      s * c * (if k i - τ i = m then 1 else 0)) = if m = 0 then K else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm; rw [if_pos rfl]
    · rw [if_neg hm]
      have e := hsum m
      rw [target_phi D hα hP, if_neg (Ne.symm hm)] at e
      simp only [hφ] at e
      exact_mod_cast e
  have hK : (K : ℝ) = 3 * D.target.oppLen 0 := by
    have e := hsum 0
    rw [target_phi D hα hP, if_pos rfl] at e
    simp only [hφ] at e
    rw [← e]; simp only [K, Int.cast_sum]
  -- reduce mod `3ab`
  have hn : ((3 * a * b : ℕ) : ℤ) = 3 * (a : ℤ) * b := by push_cast; ring
  have hK0 := zmod_core hs hcos hprim hn ε k τ hτ K hcoef
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd K _).mp hK0
  rw [hn] at hq
  have hX : D.target.oppLen 0 = q * (a * b) := by
    have : (K : ℝ) = 3 * a * b * q := by rw [hq]; push_cast; ring
    linarith
  have hq0 : 0 ≤ q := by
    have hX0 := D.target.oppLen_pos 0
    have hab : (0 : ℝ) < a * b := by
      obtain ⟨σ, -, -, -, l0, l1, -⟩ := hT
      have p0 := D.model.oppLen_pos (σ 0)
      have p1 := D.model.oppLen_pos (σ 1)
      rw [l0] at p0; rw [l1] at p1
      positivity
    by_contra h
    have : (q : ℝ) < 0 := by exact_mod_cast not_le.mp h
    nlinarith
  exact ⟨q.toNat, by rw [hX]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hq0).symm⟩

end TriangleTiling.Equilateral
