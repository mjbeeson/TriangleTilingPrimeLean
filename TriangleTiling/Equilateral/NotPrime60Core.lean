/-
The arithmetic part of the proof of `theorem:notprime60` of M. Beeson, *Tiling an equilateral
triangle* (arXiv 1811.09723), as revised 2026-11-06.  Statements checked by Beeson.

The tile has integer sides `(a, b, c)` with no common factor and `c² = a² - ab + b²` (law of
cosines for `γ = π/3`); `M` is the coloring number, with `M² < N`; the coloring equation
`3X = M(a + b + c)` and the area equation `X² = Nab` combine to `(M(a + b + c))² = 9Nab`. With
`s = a + b + c`: `6Nc = s(3N - M²)`, `s` and `c` are relatively prime, so `t = 6N/s` is an integer
with `t(a + b - c) = 2M²` and `t²ab = 4M²N`. If `N ≥ 5` is prime then `t ∣ 6`, `N` divides `a`
(say), `a = Na'` with `a't < 3`, and each of the three cases is contradictory.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace TriangleTiling.Equilateral

/-- The three cases, when `N` divides `a`. -/
theorem notprime60_case {N a b c M t : ℕ} (hN : N.Prime) (hN5 : 5 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hcos : c ^ 2 + a * b = a ^ 2 + b ^ 2) (hab : a ≠ b)
    (ht0 : 0 < t) (ht : 6 * N = (a + b + c) * t) (hE2 : t * (a + b) = t * c + 2 * M ^ 2)
    (hE3 : t ^ 2 * (a * b) = 4 * M ^ 2 * N) (htri : a < b + c) (hNa : N ∣ a) : False := by
  obtain ⟨a', rfl⟩ := hNa
  have hN0 := hN.pos
  have ha' : 0 < a' := Nat.pos_of_mul_pos_left ha
  -- `a' t < 3`
  have h2a : 2 * (N * a') * t < (N * a' + b + c) * t :=
    Nat.mul_lt_mul_of_pos_right (by omega) ht0
  rw [← ht] at h2a
  have hat : a' * t < 3 := by
    have : N * (2 * (a' * t)) < N * 6 := by linarith
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  have ha3 : a' < 3 := lt_of_le_of_lt (Nat.le_mul_of_pos_right a' ht0) hat
  have ht3 : t < 3 := lt_of_le_of_lt (Nat.le_mul_of_pos_left t ha') hat
  interval_cases a' <;> interval_cases t <;> norm_num at hat
  · -- `t = 1`, `a' = 1`: `2N = 3M²`
    have hb' : b = 4 * M ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hN0; linarith
    generalize M ^ 2 = m at hb' hE2
    have h3 : 3 ∣ N := by omega
    rcases hN.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega
  · -- `t = 2`, `a' = 1`: `c = a`, so `a = b`
    have hb' : b = M ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 4 * N); linarith
    have hc : c = N := by
      generalize M ^ 2 = m at hb' hE2
      omega
    rw [hc] at hcos
    have : N * b = b * b := by nlinarith
    have := Nat.eq_of_mul_eq_mul_right hb this
    exact hab (by omega)
  · -- `t = 1`, `a' = 2`: `a` and `b` are even
    have hb' : b = 2 * M ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * N); linarith
    have h2a : 2 ∣ N * 2 := Dvd.intro_left N rfl
    have h2b : 2 ∣ b := ⟨M ^ 2, hb'⟩
    have h2c : 2 ∣ c := by
      apply Nat.prime_two.dvd_of_dvd_pow (n := 2)
      have h1 : 2 ∣ c ^ 2 + N * 2 * b := by
        rw [hcos]
        exact dvd_add (dvd_pow h2a two_ne_zero) (dvd_pow h2b two_ne_zero)
      exact (Nat.dvd_add_left (dvd_mul_of_dvd_left h2a b)).mp h1
    have := Nat.dvd_gcd (Nat.dvd_gcd h2a h2b) h2c
    rw [hgcd] at this
    omega

/-- **The arithmetic core of `theorem:notprime60`.** -/
theorem notprime60_core {N a b c M : ℕ} (hN : N.Prime) (hN5 : 5 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hcos : c ^ 2 + a * b = a ^ 2 + b ^ 2)
    (hab : a ≠ b) (hMN : M ^ 2 < N) (hsq : (M * (a + b + c)) ^ 2 = 9 * N * a * b) : False := by
  have hs0 : 0 < a + b + c := by omega
  -- `6Nc + sM² = 3Ns`
  have hkey : 6 * N * c + (a + b + c) * M ^ 2 = 3 * N * (a + b + c) := by
    have hsq' : ((M : ℤ) * (a + b + c)) ^ 2 = 9 * N * a * b := by exact_mod_cast hsq
    have hcos' : (c : ℤ) ^ 2 + a * b = a ^ 2 + b ^ 2 := by exact_mod_cast hcos
    have h : ((a + b + c : ℕ) : ℤ) * (6 * N * c + (a + b + c) * M ^ 2) =
        ((a + b + c : ℕ) : ℤ) * (3 * N * (a + b + c)) := by
      push_cast; linear_combination hsq' + 3 * (N : ℤ) * hcos'
    have h' := mul_left_cancel₀ (by exact_mod_cast hs0.ne' : ((a + b + c : ℕ) : ℤ) ≠ 0) h
    exact_mod_cast h'
  -- `s` and `c` are relatively prime
  have hcop : Nat.Coprime (a + b + c) c := by
    apply Nat.coprime_of_dvd
    intro p hp hps hpc
    have hpab : p ∣ a + b := (Nat.dvd_add_left hpc).mp hps
    have hfa : p ∣ a → False := by
      intro hpa
      have hpb := (Nat.dvd_add_right hpa).mp hpab
      have := Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) hpc
      rw [hgcd] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hfb : p ∣ b → False := fun hpb => hfa ((Nat.dvd_add_left hpb).mp hpab)
    have hs3 : (a + b) ^ 2 = c ^ 2 + 3 * (a * b) := by nlinarith
    have h3ab : p ∣ 3 * (a * b) :=
      (Nat.dvd_add_right (dvd_pow hpc two_ne_zero)).mp (by rw [← hs3]; exact dvd_pow hpab two_ne_zero)
    rcases (Nat.Prime.dvd_mul hp).mp h3ab with h3 | h3
    · have hp3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      subst hp3
      have h9a : 3 * 3 ∣ (a + b) ^ 2 := by rw [pow_two]; exact Nat.mul_dvd_mul hpab hpab
      have h9c : 3 * 3 ∣ c ^ 2 := by rw [pow_two]; exact Nat.mul_dvd_mul hpc hpc
      rw [hs3] at h9a
      have h9 : 3 * 3 ∣ 3 * (a * b) := (Nat.dvd_add_right h9c).mp h9a
      have h3' := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
      · exact hfa h
      · exact hfb h
    · rcases (Nat.Prime.dvd_mul hp).mp h3 with h | h
      · exact hfa h
      · exact hfb h
  -- `t = 6N/s`
  have hd : (a + b + c) ∣ 6 * N * c :=
    (Nat.dvd_add_left (Dvd.intro _ rfl : (a + b + c) ∣ (a + b + c) * M ^ 2)).mp
      (hkey ▸ Dvd.intro_left _ rfl)
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right hd
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; have := hN.pos; omega
    · exact h
  have htZ : (6 * N : ℤ) = (a + b + c) * t := by exact_mod_cast ht
  have hkeyZ : (6 * N * c + (a + b + c) * M ^ 2 : ℤ) = 3 * N * (a + b + c) := by
    exact_mod_cast hkey
  have hsqZ : ((M : ℤ) * (a + b + c)) ^ 2 = 9 * N * a * b := by exact_mod_cast hsq
  -- `tc + M² = 3N`
  have hE1 : t * c + M ^ 2 = 3 * N := by
    have h : ((a + b + c : ℕ) : ℤ) * (t * c + M ^ 2) = ((a + b + c : ℕ) : ℤ) * (3 * N) := by
      push_cast; linear_combination hkeyZ - (c : ℤ) * htZ
    exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hs0.ne' : ((a + b + c : ℕ) : ℤ) ≠ 0) h
  have hE1Z : (t * c + M ^ 2 : ℤ) = 3 * N := by exact_mod_cast hE1
  -- `t(a + b - c) = 2M²`
  have hE2 : t * (a + b) = t * c + 2 * M ^ 2 := by
    have h : (t * (a + b) : ℤ) = t * c + 2 * M ^ 2 := by
      linear_combination -htZ - 2 * hE1Z
    exact_mod_cast h
  -- `t²ab = 4M²N`
  have hE3 : t ^ 2 * (a * b) = 4 * M ^ 2 * N := by
    have h : ((9 * N : ℕ) : ℤ) * (t ^ 2 * (a * b)) = ((9 * N : ℕ) : ℤ) * (4 * M ^ 2 * N) := by
      push_cast
      linear_combination (-(t : ℤ) ^ 2) * hsqZ +
        -(M : ℤ) ^ 2 * ((a + b + c) * t + 6 * N) * htZ
    exact_mod_cast mul_left_cancel₀ (by have := hN.pos; positivity) h
  -- bounds on `t`
  have hcab : c < a + b := by
    by_contra h; push Not at h
    have h1 := Nat.mul_le_mul h h
    have h2 := Nat.mul_pos ha hb
    ring_nf at h1 hcos
    linarith
  have ht2M : t ≤ 2 * M ^ 2 := by
    have h1 := Nat.mul_le_mul_left t (hcab : c + 1 ≤ a + b)
    ring_nf at h1 hE2 ⊢
    linarith
  have htN : t < 2 * N := by linarith
  rcases Nat.coprime_or_dvd_of_prime hN t with hcopt | hNt
  · -- `t ∣ 6`, so `N ∣ ab`
    have hNab : N ∣ a * b := by
      have h1 : N ∣ t ^ 2 * (a * b) := hE3 ▸ Dvd.intro_left _ rfl
      exact (Nat.Coprime.pow_right 2 hcopt).dvd_of_dvd_mul_left h1
    have hatri : a < b + c := by
      by_contra h; push Not at h
      have h1 := Nat.mul_le_mul_left a h
      have h2 := Nat.mul_le_mul_left c h
      have h3 := Nat.mul_pos hb hc
      ring_nf at h1 h2 h3 hcos
      nlinarith
    have hbtri : b < a + c := by
      by_contra h; push Not at h
      have h1 := Nat.mul_le_mul_left b h
      have h2 := Nat.mul_le_mul_left c h
      have h3 := Nat.mul_pos ha hc
      ring_nf at h1 h2 h3 hcos
      nlinarith
    rcases (Nat.Prime.dvd_mul hN).mp hNab with hNa | hNb
    · exact notprime60_case hN hN5 ha hb hgcd hcos hab ht0 ht hE2 hE3 hatri hNa
    · refine notprime60_case (a := b) (b := a) hN hN5 hb ha (by rwa [Nat.gcd_comm b a]) (by linarith)
        (Ne.symm hab) ht0 (by rw [ht]; ring) (by linarith) (by rw [← hE3]; ring) hbtri hNb
  · -- `t = N`
    obtain ⟨k, rfl⟩ := hNt
    have hk : k = 1 := by
      have hk0 : 0 < k := Nat.pos_of_mul_pos_left ht0
      have : N * k < N * 2 := by linarith
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    subst hk
    have h1 : N * (a + b) < N * (c + 2) := by ring_nf at hE2 ⊢; linarith
    have h2 := Nat.lt_of_mul_lt_mul_left h1
    have h3 : a + b = c + 1 := by omega
    rw [h3] at hE2
    have h4 : N = 2 * M ^ 2 := by linarith
    have h5 : 2 ∣ N := ⟨M ^ 2, h4⟩
    rcases hN.eq_one_or_self_of_dvd 2 h5 with h | h <;> omega

/-- **Integer sides.** If `a C' = c A'` and `b C' = c B'` with `C' > 0`, then the same holds for
some `A, B, C` without a common factor. -/
theorem int_sides {a b c : ℝ} {A' B' C' : ℕ} (hC' : 0 < C') (ha : a * C' = c * A')
    (hb : b * C' = c * B') :
    ∃ A B C : ℕ, 0 < C ∧ Nat.gcd (Nat.gcd A B) C = 1 ∧ a * C = c * A ∧ b * C = c * B := by
  set g := Nat.gcd (Nat.gcd A' B') C'
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hC'
  have hgA : g ∣ A' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgB : g ∣ B' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgC : g ∣ C' := Nat.gcd_dvd_right _ _
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  refine ⟨A' / g, B' / g, C' / g, Nat.div_pos (Nat.le_of_dvd hC' hgC) hg, ?_, ?_, ?_⟩
  · rw [Nat.gcd_div hgA hgB, Nat.gcd_div (Nat.gcd_dvd_left _ _) hgC, Nat.div_self hg]
  · rw [Nat.cast_div hgC hgR, Nat.cast_div hgA hgR, mul_div_assoc', mul_div_assoc', ha]
  · rw [Nat.cast_div hgC hgR, Nat.cast_div hgB hgR, mul_div_assoc', mul_div_assoc', hb]

end TriangleTiling.Equilateral
