/-
Section 3 of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*: lemmas about a tile with a `2π/3` angle (`lemma:c120`, `lemma:claude`, `lemma:beta`,
`lemma:pairwisecoprimality`, `lemma:not3divc`, `lemma:BLZ30`, `lemma:claude4`) and about the side
lengths of the tiled triangle (`lemma:claude3`). `lemma:rationality3` is with the prior results.

Statements checked by Beeson. The proofs are the paper's.

A triangle `ABC` with angles `(α, β, γ)` at `A`, `B`, `C` has the opposite sides `a = |BC|`,
`b = |CA|`, `c = |AB|`.
-/
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TriangleTiling.Isosceles.NotPrime
import Erdos634.EdgeChain
import Erdos634.Draft.FluxTurn

namespace TriangleTiling.Prime

open EuclideanGeometry Real

section Trig

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The facts about a nondegenerate triangle used below. -/
private theorem tri_facts {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    0 < dist B C ∧ 0 < dist C A ∧ 0 < dist A B ∧
      0 < ∠ B A C ∧ 0 < ∠ A B C ∧ 0 < ∠ A C B ∧ ∠ B A C + ∠ A B C + ∠ A C B = π ∧
      sin (∠ A C B) * dist B C = sin (∠ B A C) * dist A B ∧
      dist A B ^ 2 = dist B C ^ 2 + dist C A ^ 2 - 2 * dist B C * dist C A * cos (∠ A C B) := by
  have h := affineIndependent_iff_not_collinear_set.mp hABC
  have h1 : ¬ Collinear ℝ ({B, A, C} : Set P) := by rwa [Set.insert_comm]
  have h2 : ¬ Collinear ℝ ({A, C, B} : Set P) := by rwa [Set.pair_comm]
  have hAB : A ≠ B := ne₁₂_of_not_collinear h
  have hAC : A ≠ C := ne₁₃_of_not_collinear h
  have hBC : B ≠ C := ne₂₃_of_not_collinear h
  have hsum := angle_add_angle_add_angle_eq_pi B hAC.symm
  rw [angle_comm C B A] at hsum
  have ls1 := law_sin A C B
  have lc := law_cos A C B
  simp only [dist_comm B A, dist_comm A C, dist_comm C B] at ls1 lc
  refine ⟨dist_pos.mpr hBC, dist_pos.mpr hAC.symm, dist_pos.mpr hAB, angle_pos_of_not_collinear h1,
    angle_pos_of_not_collinear h, angle_pos_of_not_collinear h2, by linarith, by linarith,
    by nlinarith [lc]⟩

theorem cos_two_pi_div_three : cos (2 * π / 3) = -(1 / 2) := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem sin_two_pi_div_three : sin (2 * π / 3) = √3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- **Lemma `lemma:c120`.** Let triangle `R` have angles `(α, β, γ)` and sides `(a, b, c)` opposite
those angles, respectively. Then `γ = 2π/3` if and only if `c² = a² + ab + b²`. In that case we
also have `c² - a² = b(a + b)`, `c² - b² = a(a + b)`, and `α` and `β` are both less than `π/3`. -/
theorem c120 {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) :
    (∠ A C B = 2 * π / 3 ↔
      dist A B ^ 2 = dist B C ^ 2 + dist B C * dist C A + dist C A ^ 2) ∧
    (∠ A C B = 2 * π / 3 →
      dist A B ^ 2 - dist B C ^ 2 = dist C A * (dist B C + dist C A) ∧
      dist A B ^ 2 - dist C A ^ 2 = dist B C * (dist B C + dist C A) ∧
      ∠ B A C < π / 3 ∧ ∠ A B C < π / 3) := by
  obtain ⟨ha, hb, -, hα, hβ, hγ, hsum, -, lc⟩ := tri_facts hABC
  have hiff : ∠ A C B = 2 * π / 3 ↔
      dist A B ^ 2 = dist B C ^ 2 + dist B C * dist C A + dist C A ^ 2 := by
    constructor
    · intro h
      rw [lc, h, cos_two_pi_div_three]; ring
    · intro h
      -- `cos γ = (a² + b² - c²)/(2ab) = -1/2`
      have hcos : cos (∠ A C B) = -(1 / 2) := by
        have hab : 0 < dist B C * dist C A := mul_pos ha hb
        have : 2 * (dist B C * dist C A) * cos (∠ A C B) = -(dist B C * dist C A) := by
          nlinarith [lc, h]
        field_simp
        nlinarith [this]
      rw [← cos_two_pi_div_three] at hcos
      exact Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
        ⟨by positivity, by linarith [Real.pi_pos]⟩ hcos
  refine ⟨hiff, fun h => ?_⟩
  have hc := hiff.mp h
  refine ⟨by rw [hc]; ring, by rw [hc]; ring, by linarith, by linarith⟩

/-- **Lemma `lemma:claude`.** Let triangle `R` have angles `(α, β, 2π/3)` and sides `(a, b, c)`
opposite those angles, respectively. Then `cos α = (a + 2b)/(2c)`, `sin α = a√3/(2c)`,
`sin 2α = a√3(a + 2b)/(2c²)`, and `sin 3α = (a√3/(2c)) · 3b(a + b)/c²`. -/
theorem claude {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) (hγ : ∠ A C B = 2 * π / 3) :
    cos (∠ B A C) = (dist B C + 2 * dist C A) / (2 * dist A B) ∧
    sin (∠ B A C) = dist B C * √3 / (2 * dist A B) ∧
    sin (2 * ∠ B A C) = dist B C * √3 * (dist B C + 2 * dist C A) / (2 * dist A B ^ 2) ∧
    sin (3 * ∠ B A C) = dist B C * √3 / (2 * dist A B) *
      (3 * dist C A * (dist B C + dist C A) / dist A B ^ 2) := by
  obtain ⟨ha, hb, hc, hα, -, -, -, ls, -⟩ := tri_facts hABC
  obtain ⟨hcsq, himp⟩ := c120 hABC
  obtain ⟨-, -, hα3, -⟩ := himp hγ
  have hc2 := hcsq.mp hγ
  set a := dist B C
  set b := dist C A
  set c := dist A B
  -- The law of sines.
  have hsin : sin (∠ B A C) = a * √3 / (2 * c) := by
    rw [hγ, sin_two_pi_div_three] at ls
    field_simp
    linarith
  -- `cos² α = (a + 2b)²/(4c²)`, and `cos α > 0` since `α < π/3`.
  have hcos : cos (∠ B A C) = (a + 2 * b) / (2 * c) := by
    have hpos : 0 < cos (∠ B A C) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsq : cos (∠ B A C) ^ 2 = ((a + 2 * b) / (2 * c)) ^ 2 := by
      rw [Real.cos_sq', hsin]
      field_simp
      rw [h3]
      nlinarith [hc2]
    have hr : 0 < (a + 2 * b) / (2 * c) := by positivity
    nlinarith [sq_nonneg (cos (∠ B A C) - (a + 2 * b) / (2 * c)),
      sq_nonneg (cos (∠ B A C) + (a + 2 * b) / (2 * c))]
  refine ⟨hcos, hsin, ?_, ?_⟩
  · rw [Real.sin_two_mul, hsin, hcos]
    field_simp
  · have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [Real.sin_three_mul, hsin]
    field_simp
    rw [h3]
    nlinarith [hc2]

/-- **Lemma `lemma:beta`.** Let triangle `R` have angles `(α, β, 2π/3)` and sides `(a, b, c)`
opposite those angles, respectively. Then `sin β = b√3/(2c)`, `cos β = (2a + b)/(2c)`,
`sin 2β = b√3(2a + b)/(2c²)`, `sin(2α + β) = √3(a + b)/(2c)`, and
`sin(α + 2β) = √3(a + b)/(2c)`. -/
theorem beta {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C]) (hγ : ∠ A C B = 2 * π / 3) :
    sin (∠ A B C) = dist C A * √3 / (2 * dist A B) ∧
    cos (∠ A B C) = (2 * dist B C + dist C A) / (2 * dist A B) ∧
    sin (2 * ∠ A B C) = dist C A * √3 * (2 * dist B C + dist C A) / (2 * dist A B ^ 2) ∧
    sin (2 * ∠ B A C + ∠ A B C) = √3 * (dist B C + dist C A) / (2 * dist A B) ∧
    sin (∠ B A C + 2 * ∠ A B C) = √3 * (dist B C + dist C A) / (2 * dist A B) := by
  -- The first three: switch the labels `a`, `b` and `α`, `β` (the triangle `BAC`).
  have hBAC : AffineIndependent ℝ ![B, A, C] := by
    rw [show (![B, A, C] : Fin 3 → P) = ![A, B, C] ∘ Equiv.swap 0 1 by
      ext i; fin_cases i <;> rfl]
    exact hABC.comp_embedding (Equiv.swap 0 1).toEmbedding
  have hγ' : ∠ B C A = 2 * π / 3 := by rw [angle_comm]; exact hγ
  obtain ⟨cβ, sβ, s2β, -⟩ := claude hBAC hγ'
  obtain ⟨cα, sα, -, -⟩ := claude hABC hγ
  obtain ⟨ha, hb, hc, hα, hβ, -, hsum, -, -⟩ := tri_facts hABC
  simp only [dist_comm A C, dist_comm C B, dist_comm B A] at cβ sβ s2β
  rw [hγ] at hsum
  refine ⟨sβ, by rw [cβ]; ring, by rw [s2β]; ring, ?_, ?_⟩
  · -- `2α + β = π/3 + α`
    rw [show 2 * ∠ B A C + ∠ A B C = ∠ B A C + π / 3 by linarith, Real.sin_add, sα, cα,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    field_simp
    ring
  · -- the two angles add up to `π`
    rw [show ∠ B A C + 2 * ∠ A B C = π - (2 * ∠ B A C + ∠ A B C) by linarith, Real.sin_pi_sub,
      show 2 * ∠ B A C + ∠ A B C = ∠ B A C + π / 3 by linarith, Real.sin_add, sα, cα,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    field_simp
    ring

end Trig

section Arith

/-- **Lemma `lemma:pairwisecoprimality`.** Suppose `c² = a² + b² + ab` and `(a, b, c)` have no
common divisor. Then `(a, b, c)` are pairwise relatively prime. -/
theorem pairwisecoprimality {a b c : ℕ} (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c := by
  have none : ∀ p, Nat.Prime p → p ∣ a → p ∣ b → p ∣ c → False := fun p hp ha hb hc =>
    hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hg ▸ Nat.dvd_gcd (Nat.dvd_gcd ha hb) hc))
  refine ⟨Nat.coprime_of_dvd fun p hp ha hb => ?_, Nat.coprime_of_dvd fun p hp ha hc => ?_,
    Nat.coprime_of_dvd fun p hp hb hc => ?_⟩
  · -- `p ∣ a`, `p ∣ b` give `p ∣ c²`, so `p ∣ c`
    refine none p hp ha hb (hp.dvd_of_dvd_pow (n := 2) ?_)
    rw [h]
    exact dvd_add (dvd_add (dvd_pow ha two_ne_zero) (dvd_pow hb two_ne_zero)) (dvd_mul_of_dvd_left ha _)
  · -- `p ∣ a`, `p ∣ c` give `p ∣ c² - a² - ab = b²`
    refine none p hp ha (hp.dvd_of_dvd_pow (n := 2) ?_) hc
    have h1 : p ∣ a ^ 2 + a * b := dvd_add (dvd_pow ha two_ne_zero) (dvd_mul_of_dvd_left ha _)
    have h2 : p ∣ a ^ 2 + a * b + b ^ 2 := by
      rw [show a ^ 2 + a * b + b ^ 2 = c ^ 2 by rw [h]; ring]; exact dvd_pow hc two_ne_zero
    exact (Nat.dvd_add_right h1).mp h2
  · -- similarly with `a` and `b` switched
    refine none p hp (hp.dvd_of_dvd_pow (n := 2) ?_) hb hc
    have h1 : p ∣ b ^ 2 + a * b := dvd_add (dvd_pow hb two_ne_zero) (dvd_mul_of_dvd_right hb _)
    have h2 : p ∣ b ^ 2 + a * b + a ^ 2 := by
      rw [show b ^ 2 + a * b + a ^ 2 = c ^ 2 by rw [h]; ring]; exact dvd_pow hc two_ne_zero
    exact (Nat.dvd_add_right h1).mp h2

/-- **Lemma `lemma:not3divc`.** Let `(a, b, c)` have no common factor and satisfy
`c² = a² + ab + b²`. Then `3 ∤ c`. -/
theorem not3divc {a b c : ℕ} (h : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) : ¬ 3 ∣ c := by
  have hac := (pairwisecoprimality (by rw [h]; ring) hg).2.1
  intro h3c
  -- `a² + ab + b² ≡ 0 (mod 3)` forces `a ≡ b (mod 3)`.
  have hz : ((a : ZMod 3)) ^ 2 + a * b + b ^ 2 = 0 := by
    have : ((c ^ 2 : ℕ) : ZMod 3) = 0 := by
      rw [(ZMod.natCast_eq_zero_iff _ 3)]; exact dvd_pow h3c two_ne_zero
    rw [h] at this; push_cast at this; exact this
  have hab : (a : ZMod 3) = b := by
    generalize (a : ZMod 3) = x at hz ⊢
    generalize (b : ZMod 3) = y at hz ⊢
    revert x y; decide
  -- So `b = a + 3t`, and `c² = 3a² + 9at + 9t² ≡ 3a² (mod 9)`.
  obtain ⟨t, ht⟩ : (3 : ℤ) ∣ (b : ℤ) - a := by
    have : ((((b : ℤ) - a : ℤ)) : ZMod 3) = 0 := by push_cast; rw [hab]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp this
  have hc2 : ((c : ℤ)) ^ 2 = 3 * a ^ 2 + 9 * a * t + 9 * t ^ 2 := by
    have : (b : ℤ) = a + 3 * t := by linarith
    have h' : ((c : ℤ)) ^ 2 = (a : ℤ) ^ 2 + a * b + b ^ 2 := by exact_mod_cast h
    rw [h', this]; ring
  -- `9 ∣ c²`, hence `3 ∣ a²` and `3 ∣ a`, contradicting `gcd(a, c) = 1`.
  obtain ⟨u, hu⟩ := h3c
  have h9 : (3 : ℤ) ∣ (a : ℤ) ^ 2 := ⟨u ^ 2 - a * t - t ^ 2, by
    have : ((c : ℤ)) ^ 2 = 9 * u ^ 2 := by
      rw [show ((c : ℤ)) = 3 * u by exact_mod_cast hu]; ring
    linarith [hc2, this]⟩
  have h3a : (3 : ℤ) ∣ a := Int.prime_three.dvd_of_dvd_pow h9
  have h3a' : 3 ∣ a := by exact_mod_cast h3a
  have := Nat.dvd_gcd h3a' ⟨u, hu⟩
  rw [hac] at this
  norm_num at this

/-- **Lemma `lemma:BLZ30`.** Suppose `c² = a² + b² + ab` and `(a, b, c)` have no common divisor.
Then `gcd(c², c(a + 2b), 3b(a + b)) = 1`. -/
theorem BLZ30 {a b c : ℕ} (h : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.gcd (Nat.gcd (c ^ 2) (c * (a + 2 * b))) (3 * b * (a + b)) = 1 := by
  obtain ⟨hab, -, hbc⟩ := pairwisecoprimality h hg
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hdvd
  have h1 : p ∣ c ^ 2 := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hdvd).1).1
  have h3 : p ∣ 3 * b * (a + b) := (Nat.dvd_gcd_iff.mp hdvd).2
  have hpc : p ∣ c := hp.dvd_of_dvd_pow h1
  by_cases hp3 : p = 3
  · -- contradicts `lemma:not3divc`
    subst hp3
    exact not3divc (by rw [h]; ring) hg hpc
  · -- `p ∣ b(a + b)`, `p ∤ b`, so `p ∣ a + b`; then `p ∣ a` and `p ∣ b`
    have hpb3 : p ∣ b * (a + b) := by
      rw [mul_assoc] at h3
      exact (Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hp Nat.prime_three).mpr hp3) h3)
    have hpb : ¬ p ∣ b := fun hpb => hp.one_lt.ne' (Nat.eq_one_of_dvd_one
      (hbc ▸ Nat.dvd_gcd hpb hpc))
    have hpab : p ∣ a + b := (hp.dvd_mul.mp hpb3).resolve_left hpb
    have hpa2 : p ∣ a ^ 2 := by
      have e : c ^ 2 = a ^ 2 + b * (a + b) := by rw [h]; ring
      have := dvd_pow hpc two_ne_zero (n := 2)
      rw [e] at this
      exact (Nat.dvd_add_left (dvd_mul_of_dvd_right hpab b)).mp this
    have hpa : p ∣ a := hp.dvd_of_dvd_pow hpa2
    exact hpb ((Nat.dvd_add_right hpa).mp hpab)

/-- **Lemma `lemma:claude4`.** Let `(a, b, c)` be positive integers satisfying
`c² = a² + ab + b²`. Then `a + b` is composite. -/
theorem claude4 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    1 < a + b ∧ ¬ (a + b).Prime := by
  refine ⟨by omega, fun hp => ?_⟩
  set p := a + b with hpdef
  have hZ : ((c : ℤ)) ^ 2 = (a : ℤ) ^ 2 + a * b + b ^ 2 := by exact_mod_cast h
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hp' : ((p : ℕ) : ℤ) = a + b := by push_cast [hpdef]; ring
  -- `0 < c < p`, since `c² = p² - ab`
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hcp : (c : ℤ) < p := by nlinarith
  -- `p ∣ (c - a)(c + a)`, since `c² - a² = b(a + b) = bp`
  have hdiv : ((p : ℕ) : ℤ) ∣ ((c : ℤ) - a) * (c + a) := ⟨b, by rw [hp']; nlinarith [hZ]⟩
  rcases Int.Prime.dvd_mul' hp hdiv with h1 | h1
  · -- `|c - a| < p` and `c ≠ a`, so `p ∤ c - a`
    have hne : (c : ℤ) - a ≠ 0 := by
      intro h0
      have : (c : ℤ) = a := by linarith
      rw [this] at hZ; nlinarith
    exact hne (Int.eq_zero_of_abs_lt_dvd h1 (by rw [abs_lt]; constructor <;> linarith))
  · -- `0 < c + a < 2p`, so `c + a = p = a + b`, `c = b`, and `a(a + b) = 0`
    obtain ⟨k, hk⟩ := h1
    rw [hp'] at hk
    have hk1 : k = 1 := by
      have h0 : 0 < k := by
        by_contra hk0; push Not at hk0; nlinarith
      have h2 : k < 2 := by
        by_contra hk2; push Not at hk2; nlinarith
      omega
    rw [hk1, mul_one] at hk
    have : (c : ℤ) = b := by linarith
    rw [this] at hZ
    nlinarith

end Arith

open Erdos634.Geometry

/-- **Lemma `lemma:claude3`.** Suppose triangle `T` is tiled by a triangle `R` with integer sides.
Let the side lengths `(X, Y, Z)` of `T` be proportional to coprime integers `(X₀, Y₀, Z₀)`. Then
`(X, Y, Z) = λ(X₀, Y₀, Z₀)` for some integer `λ`.

`T` is `D.target`, with sides `X, Y, Z = D.target.oppLen 0, 1, 2`; `R` is the tile, with sides
`D.model.oppLen 0, 1, 2`; "coprime" is `gcd(X₀, Y₀, Z₀) = 1`. -/
theorem claude3 {N : ℕ} (D : CongruentDissection N) (hint : ∀ k, ∃ n : ℕ, D.model.oppLen k = n)
    {X₀ Y₀ Z₀ : ℕ} (hg : Nat.gcd (Nat.gcd X₀ Y₀) Z₀ = 1) {l : ℝ}
    (hX : D.target.oppLen 0 = l * X₀) (hY : D.target.oppLen 1 = l * Y₀)
    (hZ : D.target.oppLen 2 = l * Z₀) :
    ∃ n : ℕ, l = n := by
  -- Each side of `T` is a linear integral combination of the sides of `R`, so an integer.
  obtain ⟨a, ha⟩ := hint 0
  obtain ⟨b, hb⟩ := hint 1
  obtain ⟨c, hc⟩ := hint 2
  have hside : ∀ k : Fin 3, ∃ n : ℕ, D.target.oppLen k = n := by
    intro k
    obtain ⟨P, Q, R, hPQR, -⟩ := D.toDissection.side_walk_abc (k + 1) a b c (fun j m => by
      rcases edge_len_mem D j m with h | h | h
      · left; rw [h, ← ha]; rfl
      · right; left; rw [h, ← hb]; rfl
      · right; right; rw [h, ← hc]; rfl)
    refine ⟨P * a + Q * b + R * c, ?_⟩
    have e : D.target.oppLen k = dist (D.target.pts (k + 1)) (D.target.pts (k + 1 + 1)) := by
      unfold Tri.oppLen; rw [add_assoc, show (1 : Fin 3) + 1 = 2 from rfl]
    rw [e, ← hPQR]; push_cast; ring
  obtain ⟨X, eX⟩ := hside 0
  obtain ⟨Y, eY⟩ := hside 1
  obtain ⟨Z, eZ⟩ := hside 2
  -- `l > 0`, and some `X₀, Y₀, Z₀` is positive.
  have hpos : ∀ k : Fin 3, 0 < D.target.oppLen k := fun k => by
    unfold Tri.oppLen
    exact dist_pos.mpr (D.target.indep.injective.ne (by fin_cases k <;> decide))
  have hX0 : 0 < X₀ := by
    rcases Nat.eq_zero_or_pos X₀ with h0 | h0
    · have := hpos 0; rw [hX, h0] at this; simp at this
    · exact h0
  have hl : 0 < l := by
    have := hpos 0; rw [hX] at this
    exact pos_of_mul_pos_left this (by positivity)
  -- `l = X/X₀` is rational: `l = p/q` with `p, q` coprime.
  set q : ℚ := (X : ℚ) / X₀ with hqdef
  have hlq : l = (q : ℝ) := by
    have : (X : ℝ) = l * X₀ := by rw [← eX, hX]
    rw [hqdef]; push_cast; field_simp; linarith
  have hq0 : 0 < q := by exact_mod_cast (hlq ▸ hl)
  -- `q (X, Y, Z) = p (X₀, Y₀, Z₀)`, so `q ∣ X₀, Y₀, Z₀`, so `q = 1`.
  have hden : ∀ (W W₀ : ℕ), (W : ℝ) = l * W₀ → q.den ∣ W₀ := by
    intro W W₀ hW
    have h1 : (W : ℚ) = q * W₀ := by exact_mod_cast (hlq ▸ hW)
    have h2 : (q.den : ℤ) * W = q.num * W₀ := by
      have hq : q * q.den = q.num := Rat.mul_den_eq_num q
      have : ((q.den : ℤ) * W : ℚ) = ((q.num * W₀ : ℤ) : ℚ) := by
        push_cast; rw [h1]; linear_combination (W₀ : ℚ) * hq
      exact_mod_cast this
    have h3 : (q.den : ℤ) ∣ q.num * W₀ := ⟨W, h2.symm⟩
    have h4 := (Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [Int.gcd_comm]; exact_mod_cast q.reduced)).dvd_of_dvd_mul_left h3
    exact_mod_cast h4
  have d1 := hden X X₀ (by rw [← eX, hX])
  have d2 := hden Y Y₀ (by rw [← eY, hY])
  have d3 := hden Z Z₀ (by rw [← eZ, hZ])
  have hd1 : q.den = 1 := by
    have := Nat.dvd_gcd (Nat.dvd_gcd d1 d2) d3
    rw [hg] at this
    exact Nat.eq_one_of_dvd_one this
  have hnum : (q.num : ℚ) = q := by
    have := Rat.num_div_den q
    rw [hd1] at this; simpa using this
  have hnn : 0 ≤ q.num := Rat.num_nonneg.mpr hq0.le
  have e1 : ((q.num.toNat : ℤ)) = q.num := Int.toNat_of_nonneg hnn
  have e2 : q = ((q.num.toNat : ℕ) : ℚ) := by
    rw [show ((q.num.toNat : ℕ) : ℚ) = ((q.num.toNat : ℤ) : ℚ) by norm_cast, e1, hnum]
  refine ⟨q.num.toNat, ?_⟩
  rw [hlq, e2]
  norm_cast

end TriangleTiling.Prime
