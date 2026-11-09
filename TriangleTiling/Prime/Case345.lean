/-
Sections 5–7 of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*: the shapes `(α, 2β, 2α + β)`, `(α, α + β, α + 2β)` and `(2α, 2β, α + β)` tiled by
`(α, β, 2π/3)`. This file has the proofs of `theorem:case3`, `theorem:case4` and `theorem:case5`
from the point where the sides of the tile are known to be commensurable (`lemma:rationality3`,
which needs Beeson–Zhang and is in `TriangleTiling.Laczkovich`).
-/
import TriangleTiling.Prime.Case2

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

/-- The tile `(a, b, c) = μ(a', b', c')` in integers: `a', b' ≥ 1` and `c'² = a'² + b'² + a'b'`. -/
theorem int_tile {a b c μ : ℝ} {a' b' c' : ℕ} (hμ : 0 < μ) (ha : 0 < a) (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ea : a = μ * a') (eb : b = μ * b') (ec : c = μ * c') :
    1 ≤ a' ∧ 1 ≤ b' ∧ c' ^ 2 = a' ^ 2 + b' ^ 2 + a' * b' := by
  have ha' : (0 : ℝ) < a' := by
    have := ea ▸ ha; exact pos_of_mul_pos_right this hμ.le
  have hb' : (0 : ℝ) < b' := by
    have := eb ▸ hb; exact pos_of_mul_pos_right this hμ.le
  have hc2' : (c' : ℝ) ^ 2 = (a' : ℝ) ^ 2 + a' * b' + b' ^ 2 := by
    rw [ea, eb, ec] at hc2
    have hμ2 : μ ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hμ2
    linear_combination hc2
  refine ⟨by exact_mod_cast ha', by exact_mod_cast hb', ?_⟩
  have : ((c' ^ 2 : ℕ) : ℝ) = ((a' ^ 2 + b' ^ 2 + a' * b' : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- If a prime `p` divides `2a + b` and `c`, where `c² = a² + ab + b²`, then `p` divides `3a²`
(modulo `p`, `b ≡ -2a` and `0 ≡ a² + ab + b² ≡ 3a²`). -/
theorem dvd_three_sq {a b c p : ℕ} (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b) (h1 : p ∣ 2 * a + b)
    (h2 : p ∣ c) : p ∣ 3 * a ^ 2 := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨u, hu⟩ := h2
  have hZ : ((c : ℤ)) ^ 2 = (a : ℤ) ^ 2 + b ^ 2 + a * b := by exact_mod_cast h
  have ht' : (2 * a + b : ℤ) = p * t := by exact_mod_cast ht
  have hu' : (c : ℤ) = p * u := by exact_mod_cast hu
  have : ((p : ℤ)) ∣ ((3 * a ^ 2 : ℕ) : ℤ) := ⟨p * u ^ 2 + 3 * a * t - p * t ^ 2, by
    push_cast
    have hb : (b : ℤ) = p * t - 2 * a := by linarith
    rw [hb, hu'] at hZ
    linear_combination -hZ⟩
  exact_mod_cast this

/-- The common factor argument of `theorem:case3`: `gcd(ac, b(2a + b), (a + b)c) = 1`. -/
theorem gcd_case3 {a b c : ℕ} (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.gcd (Nat.gcd (a * c) (b * (2 * a + b))) ((a + b) * c) = 1 := by
  obtain ⟨hab, hac, hbc⟩ := pairwisecoprimality h hg
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  have h1 : p ∣ a * c := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hdvd).1).1
  have h2 : p ∣ b * (2 * a + b) := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hdvd).1).2
  have nd : ∀ {x y}, Nat.Coprime x y → p ∣ x → p ∣ y → False := fun hxy hx hy =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hxy ▸ Nat.dvd_gcd hx hy))
  -- `p ∣ a` or `p ∣ c`, so `p ∤ b`, so `p ∣ 2a + b`
  have hpb : ¬ p ∣ b := fun hb => by
    rcases hp.dvd_mul.mp h1 with ha | hc
    · exact nd hab ha hb
    · exact nd hbc hb hc
  have h2ab : p ∣ 2 * a + b := (hp.dvd_mul.mp h2).resolve_left hpb
  -- `p ∤ a` (else `p ∣ b`), so `p ∣ c`
  have hpa : ¬ p ∣ a := fun ha =>
    hpb ((Nat.dvd_add_right (dvd_mul_of_dvd_right ha 2)).mp h2ab)
  have hpc : p ∣ c := (hp.dvd_mul.mp h1).resolve_left hpa
  -- modulo `p`, `0 ≡ 3a²`, so `p = 3`, contradicting `lemma:not3divc`
  rcases hp.dvd_mul.mp (dvd_three_sq h h2ab hpc) with h3 | h3
  · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst this
    exact not3divc (by rw [h]; ring) hg hpc
  · exact hpa (hp.dvd_of_dvd_pow h3)

/-- The common factor argument of `theorem:case4`: `gcd(a, c, a + b) = 1`. -/
theorem gcd_case4 {a b c : ℕ} (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.gcd (Nat.gcd a c) (a + b) = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  have ha : p ∣ a := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hdvd).1).1
  have hc : p ∣ c := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hdvd).1).2
  have hab : p ∣ a + b := (Nat.dvd_gcd_iff.mp hdvd).2
  have hb : p ∣ b := (Nat.dvd_add_right ha).mp hab
  exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hg ▸ Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc))

/-- The common factor argument of `theorem:case5`: `gcd(a(a + 2b), b(2a + b), c²) = 1`. -/
theorem gcd_case5 {a b c : ℕ} (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.gcd (Nat.gcd (a * (a + 2 * b)) (b * (2 * a + b))) (c ^ 2) = 1 := by
  obtain ⟨-, hac, hbc⟩ := pairwisecoprimality h hg
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  have h2 : p ∣ b * (2 * a + b) := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hdvd).1).2
  have hpc : p ∣ c := hp.dvd_of_dvd_pow (Nat.dvd_gcd_iff.mp hdvd).2
  have nd : ∀ {x y}, Nat.Coprime x y → p ∣ x → p ∣ y → False := fun hxy hx hy =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hxy ▸ Nat.dvd_gcd hx hy))
  -- `p ∣ c`, so `p ∤ a`, `p ∤ b`, so `p ∣ 2a + b`
  have hpa : ¬ p ∣ a := fun ha => nd hac ha hpc
  have hpb : ¬ p ∣ b := fun hb => nd hbc hb hpc
  have h2ab : p ∣ 2 * a + b := (hp.dvd_mul.mp h2).resolve_left hpb
  -- `0 ≡ 3a² (mod p)`, so `p = 3`, but `3 ∤ c`
  rcases hp.dvd_mul.mp (dvd_three_sq h h2ab hpc) with h3 | h3
  · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst this
    exact not3divc (by rw [h]; ring) hg hpc
  · exact hpa (hp.dvd_of_dvd_pow h3)

/-- **`theorem:case3`, after commensurability.** Let `T` have angles `(α, 2β, 2α + β)` (at its
vertices `0, 1, 2`) and be `N`-tiled by `(α, β, 2π/3)` with sides `(a, b, c)`, and suppose
`(a, b, c) = μ(a', b', c')` with `a', b', c'` integers with no common factor. Then
`N = λ²(2a' + b')(a' + b')` with `λ` a positive integer, and `N` is not prime. -/
theorem case3core {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = 2 * β)
    (hC : D.target.angleAt 2 = 2 * α + β) {μ : ℝ} (hμ : 0 < μ) {a' b' c' : ℕ}
    (hg : Nat.gcd (Nat.gcd a' b') c' = 1) (ea : a = μ * a') (eb : b = μ * b') (ec : c = μ * c') :
    ∃ l : ℕ, 0 < l ∧ N = l ^ 2 * (2 * a' + b') * (a' + b') ∧ ¬ N.Prime := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  obtain ⟨ha, hb, hc, hc2, hαβ, sα, cα, sβ, cβ⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  obtain ⟨ha1, hb1, hc2N⟩ := int_tile hμ ha hb hc2 ea eb ec
  have hsα : 0 < sin α := by rw [sα]; positivity
  -- The law of sines: `X : sin α = Y : sin 2β = Z : sin(2α + β)`.
  have hX := ThreeAlpha.lawsin D.target 0
  have hY := ThreeAlpha.lawsin D.target 1
  have hZ := ThreeAlpha.lawsin D.target 2
  set dT := ThreeAlpha.circumdiam D.target
  rw [hA] at hX; rw [hB] at hY; rw [hC] at hZ
  set X := D.target.oppLen 0
  set Y := D.target.oppLen 1
  set Z := D.target.oppLen 2
  have h2αβ : sin (2 * α + β) = √3 * (a + b) / (2 * c) := by
    rw [show 2 * α + β = α + π / 3 by linarith, Real.sin_add, sα, cα, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
    field_simp; ring
  -- `(X, Y, Z) = λ (ac, b(2a + b), (a + b)c)`
  have hdT : dT = X / sin α := by rw [hX]; field_simp
  set lam := X / (a * c) with hlam
  have eX : X = lam * (a * c) := by rw [hlam]; field_simp
  have eY : Y = lam * (b * (2 * a + b)) := by
    rw [hY, hdT, Real.sin_two_mul, sβ, cβ, hlam, sα]
    field_simp
    try ring
  have eZ : Z = lam * ((a + b) * c) := by
    rw [hZ, hdT, h2αβ, hlam, sα]
    field_simp
  -- `λμ` is an integer.
  obtain ⟨n, hn⟩ := lambda_int D σ hμ (l0.trans ea) (l1.trans eb) (l2.trans ec)
    (gcd_case3 hc2N hg) (l := lam * μ)
    (by show X = _; rw [eX, ea, ec]; push_cast; ring)
    (by show Y = _; rw [eY, ea, eb]; push_cast; ring)
    (by show Z = _; rw [eZ, ea, eb, ec]; push_cast; ring)
  -- The area equation: `N a² sin β sin γ = X² sin 2β sin(2α + β)`.
  have hE := area_sines' D σ
  rw [h0, h1, h2, hA, hB, hC] at hE
  have hdm := ThreeAlpha.lawsin D.model (σ 0)
  rw [h0, l0] at hdm
  have E2 : (N : ℝ) * a ^ 2 * (sin β * sin (2 * π / 3)) =
      X ^ 2 * (sin (2 * β) * sin (2 * α + β)) := by
    rw [hdm, hX]; linear_combination sin α * hE
  have hβγ : sin β * sin (2 * π / 3) = 3 * b / (4 * c) := by
    rw [sβ, sin_two_pi_div_three]; field_simp; rw [Real.sq_sqrt (by norm_num)]; ring
  have h2 : sin (2 * β) * sin (2 * α + β) = 3 * b * (2 * a + b) * (a + b) / (4 * c ^ 3) := by
    rw [Real.sin_two_mul, sβ, cβ, h2αβ]
    field_simp
    rw [show √3 ^ 2 = 3 from Real.sq_sqrt (by norm_num)]
    ring
  rw [hβγ, h2, eX] at E2
  have hNr : (N : ℝ) = lam ^ 2 * (2 * a + b) * (a + b) := by
    have hk : a ^ 2 * (3 * b / (4 * c)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hk
    rw [← mul_assoc, E2]
    field_simp
    try ring
  have hNn : N = n ^ 2 * (2 * a' + b') * (a' + b') := by
    have : (N : ℝ) = (n : ℝ) ^ 2 * (2 * a' + b') * (a' + b') := by
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
  -- a product of two integers each at least `2`
  rw [hNn]
  apply Nat.not_prime_mul _ (by omega)
  have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn0
  have : 3 ≤ n ^ 2 * (2 * a' + b') := by nlinarith
  omega

/-- **`theorem:case4`, after commensurability.** Let `T` have angles `(α, α + β, α + 2β)` (at its
vertices `0, 1, 2`) and be `N`-tiled by `(α, β, 2π/3)` with sides `(a, b, c)`, and suppose
`(a, b, c) = μ(a', b', c')` with `a', b', c'` integers with no common factor. Then
`N = λ²(a' + b')/b'` (that is, `N b' = λ²(a' + b')`) with `λ` a positive integer such that
`b' ∣ λ²`, and `N` is not prime. -/
theorem case4core {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α + β)
    (hC : D.target.angleAt 2 = α + 2 * β) {μ : ℝ} (hμ : 0 < μ) {a' b' c' : ℕ}
    (hg : Nat.gcd (Nat.gcd a' b') c' = 1) (ea : a = μ * a') (eb : b = μ * b') (ec : c = μ * c') :
    ∃ l : ℕ, 0 < l ∧ b' ∣ l ^ 2 ∧ N * b' = l ^ 2 * (a' + b') ∧ ¬ N.Prime := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  obtain ⟨ha, hb, hc, hc2, hαβ, sα, cα, sβ, cβ⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  obtain ⟨ha1, hb1, hc2N⟩ := int_tile hμ ha hb hc2 ea eb ec
  have hsα : 0 < sin α := by rw [sα]; positivity
  have hX := ThreeAlpha.lawsin D.target 0
  have hY := ThreeAlpha.lawsin D.target 1
  have hZ := ThreeAlpha.lawsin D.target 2
  set dT := ThreeAlpha.circumdiam D.target
  rw [hA] at hX; rw [hB, hαβ, Real.sin_pi_div_three] at hY; rw [hC] at hZ
  set X := D.target.oppLen 0
  set Y := D.target.oppLen 1
  set Z := D.target.oppLen 2
  have hα2β : sin (α + 2 * β) = √3 * (a + b) / (2 * c) := by
    rw [show α + 2 * β = π - (α + π / 3) by linarith, Real.sin_pi_sub, Real.sin_add, sα, cα,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    field_simp; ring
  -- `(X, Y, Z) = λ (a, c, a + b)`
  have hdT : dT = X / sin α := by rw [hX]; field_simp
  set lam := X / a with hlam
  have eX : X = lam * a := by rw [hlam]; field_simp
  have eY : Y = lam * c := by
    rw [hY, hdT, hlam, sα]
    field_simp
  have eZ : Z = lam * (a + b) := by
    rw [hZ, hdT, hα2β, hlam, sα]
    field_simp
  obtain ⟨n, hn⟩ := lambda_int D σ hμ (l0.trans ea) (l1.trans eb) (l2.trans ec)
    (gcd_case4 (c := c') (b := b') hg) (l := lam)
    (by show X = _; rw [eX, ea]; ring)
    (by show Y = _; rw [eY, ec]; ring)
    (by show Z = _; rw [eZ, ea, eb]; push_cast; ring)
  -- The area equation: `N a² sin β sin γ = X² sin(α + β) sin(α + 2β)`.
  have hE := area_sines' D σ
  rw [h0, h1, h2, hA, hB, hC, hαβ, Real.sin_pi_div_three] at hE
  have hdm := ThreeAlpha.lawsin D.model (σ 0)
  rw [h0, l0] at hdm
  have E2 : (N : ℝ) * a ^ 2 * (sin β * sin (2 * π / 3)) =
      X ^ 2 * (√3 / 2 * sin (α + 2 * β)) := by
    rw [hdm, hX]; linear_combination sin α * hE
  have hβγ : sin β * sin (2 * π / 3) = 3 * b / (4 * c) := by
    rw [sβ, sin_two_pi_div_three]; field_simp; rw [Real.sq_sqrt (by norm_num)]; ring
  have h2 : √3 / 2 * sin (α + 2 * β) = 3 * (a + b) / (4 * c) := by
    rw [hα2β]; field_simp; rw [Real.sq_sqrt (by norm_num)]; ring
  rw [hβγ, h2, eX] at E2
  -- `N b = λ²(a + b)`
  have hNr : (N : ℝ) * b = lam ^ 2 * (a + b) := by
    have hk : a ^ 2 * (3 / (4 * c)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hk
    have : (N : ℝ) * a ^ 2 * (3 * b / (4 * c)) = (lam * a) ^ 2 * (3 * (a + b) / (4 * c)) := E2
    field_simp at this ⊢
    linear_combination this
  have hNn : N * b' = n ^ 2 * (a' + b') := by
    have : (N : ℝ) * b' = (n : ℝ) ^ 2 * (a' + b') := by
      have hμ0 : μ ≠ 0 := hμ.ne'
      apply mul_left_cancel₀ hμ0
      rw [ea, eb] at hNr
      have : (n : ℝ) = lam := hn.symm
      rw [this]
      linear_combination hNr
    exact_mod_cast this
  have hn0 : 0 < n := by
    have hXpos : 0 < X := D.target.oppLen_pos 0
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero] at hn
      rw [eX, hn, zero_mul] at hXpos
      exact lt_irrefl _ hXpos
    · exact h0
  -- `gcd(a + b, b) = 1`, so `b ∣ λ²`
  have hab := (pairwisecoprimality hc2N hg).1
  have hcop : Nat.Coprime b' (a' + b') := by
    rw [Nat.coprime_comm, Nat.coprime_add_self_left]; exact hab
  have hdvd : b' ∣ n ^ 2 := hcop.dvd_of_dvd_mul_right ⟨N, by rw [← hNn]; ring⟩
  refine ⟨n, hn0, hdvd, hNn, fun hp => ?_⟩
  -- `a + b` divides `N`, so `a + b = N` (it exceeds `1`), but `a + b` is composite
  obtain ⟨m, hm⟩ := hdvd
  have hN : N = m * (a' + b') := by
    have hb0 : 0 < b' := by omega
    apply Nat.eq_of_mul_eq_mul_right hb0
    rw [hNn, hm]; ring
  have hd : (a' + b') ∣ N := ⟨m, by rw [hN]; ring⟩
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · omega
  · obtain ⟨-, hnp⟩ := claude4 (a := a') (b := b') (c := c') (by omega) (by omega)
      (by rw [hc2N]; ring)
    exact hnp (h1 ▸ hp)

/-- **`theorem:case5`, after commensurability.** Let `T` have angles `(2α, 2β, α + β)` (at its
vertices `0, 1, 2`) and be `N`-tiled by `(α, β, 2π/3)` with sides `(a, b, c)`, and suppose
`(a, b, c) = μ(a', b', c')` with `a', b', c'` integers with no common factor. Then
`N = λ²(a' + 2b')(2a' + b')` with `λ` a positive integer, and `N` is not prime. -/
theorem case5core {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = 2 * α) (hB : D.target.angleAt 1 = 2 * β)
    (hC : D.target.angleAt 2 = α + β) {μ : ℝ} (hμ : 0 < μ) {a' b' c' : ℕ}
    (hg : Nat.gcd (Nat.gcd a' b') c' = 1) (ea : a = μ * a') (eb : b = μ * b') (ec : c = μ * c') :
    ∃ l : ℕ, 0 < l ∧ N = l ^ 2 * (a' + 2 * b') * (2 * a' + b') ∧ ¬ N.Prime := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  obtain ⟨ha, hb, hc, hc2, hαβ, sα, cα, sβ, cβ⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  obtain ⟨ha1, hb1, hc2N⟩ := int_tile hμ ha hb hc2 ea eb ec
  have hs3 : (0 : ℝ) < √3 := by positivity
  have hX := ThreeAlpha.lawsin D.target 0
  have hY := ThreeAlpha.lawsin D.target 1
  have hZ := ThreeAlpha.lawsin D.target 2
  set dT := ThreeAlpha.circumdiam D.target
  rw [hA] at hX; rw [hB] at hY; rw [hC, hαβ, Real.sin_pi_div_three] at hZ
  set X := D.target.oppLen 0
  set Y := D.target.oppLen 1
  set Z := D.target.oppLen 2
  -- `(X, Y, Z) = λ (a(a + 2b), b(2a + b), c²)`
  have hdT : dT = 2 * Z / √3 := by rw [hZ]; field_simp
  set lam := Z / c ^ 2 with hlam
  have eZ : Z = lam * c ^ 2 := by rw [hlam]; field_simp
  have eX : X = lam * (a * (a + 2 * b)) := by
    rw [hX, hdT, Real.sin_two_mul, sα, cα, hlam]
    field_simp
    try ring
  have eY : Y = lam * (b * (2 * a + b)) := by
    rw [hY, hdT, Real.sin_two_mul, sβ, cβ, hlam]
    field_simp
    try ring
  obtain ⟨n, hn⟩ := lambda_int D σ hμ (l0.trans ea) (l1.trans eb) (l2.trans ec)
    (gcd_case5 hc2N hg) (l := lam * μ)
    (by show X = _; rw [eX, ea, eb]; push_cast; ring)
    (by show Y = _; rw [eY, ea, eb]; push_cast; ring)
    (by show Z = _; rw [eZ, ec]; push_cast; ring)
  -- The area equation: `N a² sin β sin γ · (√3/2)² = Z² sin α sin 2α sin 2β (√3/2)`.
  have hE := area_sines' D σ
  rw [h0, h1, h2, hA, hB, hC, hαβ, Real.sin_pi_div_three] at hE
  have hdm := ThreeAlpha.lawsin D.model (σ 0)
  rw [h0, l0] at hdm
  have E2 : (N : ℝ) * a ^ 2 * (sin β * sin (2 * π / 3)) * (√3 / 2) ^ 2 =
      Z ^ 2 * (sin α * (sin (2 * α) * sin (2 * β) * (√3 / 2))) := by
    rw [hdm, hZ]; linear_combination sin α * (√3 / 2) ^ 2 * hE
  have hβγ : sin β * sin (2 * π / 3) = 3 * b / (4 * c) := by
    rw [sβ, sin_two_pi_div_three]; field_simp; rw [Real.sq_sqrt (by norm_num)]; ring
  have h2 : sin α * (sin (2 * α) * sin (2 * β) * (√3 / 2)) =
      9 * a ^ 2 * b * (a + 2 * b) * (2 * a + b) / (16 * c ^ 5) := by
    rw [Real.sin_two_mul, Real.sin_two_mul, sα, cα, sβ, cβ]
    field_simp
    rw [show √3 ^ 4 = (√3 ^ 2) ^ 2 by ring, Real.sq_sqrt (by norm_num)]
    ring
  rw [hβγ, h2, eZ] at E2
  have hNr : (N : ℝ) = lam ^ 2 * (a + 2 * b) * (2 * a + b) := by
    have hk : a ^ 2 * (3 * b / (4 * c)) * (√3 / 2) ^ 2 ≠ 0 := by positivity
    apply mul_right_cancel₀ hk
    rw [← mul_assoc, ← mul_assoc, E2]
    field_simp
    rw [show √3 ^ 2 = 3 from Real.sq_sqrt (by norm_num)]
    ring
  have hNn : N = n ^ 2 * (a' + 2 * b') * (2 * a' + b') := by
    have : (N : ℝ) = (n : ℝ) ^ 2 * (a' + 2 * b') * (2 * a' + b') := by
      rw [hNr, ← hn, ea, eb]; ring
    exact_mod_cast this
  have hn0 : 0 < n := by
    have hZpos : 0 < Z := D.target.oppLen_pos 2
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero] at hn
      have : lam = 0 := by
        rcases mul_eq_zero.mp hn with h | h
        · exact h
        · exact absurd h hμ.ne'
      rw [eZ, this, zero_mul] at hZpos
      exact lt_irrefl _ hZpos
    · exact h0
  refine ⟨n, hn0, hNn, ?_⟩
  rw [hNn]
  apply Nat.not_prime_mul _ (by omega)
  have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn0
  have : 3 ≤ n ^ 2 * (a' + 2 * b') := by nlinarith
  omega

end TriangleTiling.Prime
