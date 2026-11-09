/-
The Group 2 shapes of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*: `lemma:RandT`, `lemma:rationality3`, and `theorem:case2`–`theorem:case5`.

Statements checked by Beeson. `lemma:RandT` is Bonfioli's `lemma1` (UNAUDITED; its second
claim uses his formalization of Laczkovich's classification, where the paper cites the first
paragraph of the proof of Laczkovich 1995, Theorem 5.3). `lemma:rationality3` follows the paper,
except that it uses Beeson–Zhang Theorem 1.1 (Bonfioli's `bz_thm11`, UNAUDITED), the case
`γ = 2π/3` of the Theorem 1.2 that the paper cites (`theorem:rationality`). The rest of the proofs
of `theorem:case2`–`case5` is in `TriangleTiling.Prime.Case2` and `Case345`.

"`T` has incommensurable angles" is `¬ CommAngles D.target`: not all ratios of the angles of `T`
are rational. "The sides `(a, b, c)` are commensurable" is `RationalTile a b c`.
-/
import TriangleTiling.Prime.Case345
import Erdos634.Draft.LaczFormalBZL7d6
import Erdos634.Draft.LaczFormalL2b

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real
open Erdos634.Draft.LaczFormal (CommAngles commAngles_iff)

/-- **Lemma `lemma:RandT`.** Let triangle `T` be tiled by triangle `R`. If `R` has commensurable
angles, so does `T`. Conversely, if `T` is not equilateral and has commensurable angles, so does
`R`. -/
theorem RandT {N : ℕ} (D : CongruentDissection N) :
    (CommAngles D.model → CommAngles D.target) ∧
      (¬ Erdos634.Draft.TheoremPConditional.Equilateral D → CommAngles D.target →
        CommAngles D.model) :=
  Erdos634.Draft.LaczFormal.lemma1 D

/-- Commensurable sides `a, b, c > 0` are `μ(a', b', c')` with `a', b', c'` integers with no
common factor. -/
theorem int_sides_of_rational {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ThreeAlpha.RationalTile a b c) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ a' b' c' : ℕ, Nat.gcd (Nat.gcd a' b') c' = 1 ∧
      a = μ * a' ∧ b = μ * b' ∧ c = μ * c' := by
  obtain ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, -⟩ := h
  have hq₁0 : 0 < q₁ := by exact_mod_cast (hq₁ ▸ div_pos ha hc)
  have hq₂0 : 0 < q₂ := by exact_mod_cast (hq₂ ▸ div_pos hb hc)
  -- `a/c = p₁/r₁`, `b/c = p₂/r₂`, so `(a, b, c) ∝ (p₁ r₂, p₂ r₁, r₁ r₂)`
  set p₁ := q₁.num.toNat
  set r₁ := q₁.den
  set p₂ := q₂.num.toNat
  set r₂ := q₂.den
  have e₁ : (q₁ : ℝ) = p₁ / r₁ := by
    have : (q₁.num.toNat : ℤ) = q₁.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq₁0.le)
    rw [← Rat.num_div_den q₁]; push_cast; rw [← this]; push_cast; rfl
  have e₂ : (q₂ : ℝ) = p₂ / r₂ := by
    have : (q₂.num.toNat : ℤ) = q₂.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq₂0.le)
    rw [← Rat.num_div_den q₂]; push_cast; rw [← this]; push_cast; rfl
  have hr₁ : (0 : ℝ) < r₁ := by exact_mod_cast q₁.den_pos
  have hr₂ : (0 : ℝ) < r₂ := by exact_mod_cast q₂.den_pos
  set A := p₁ * r₂
  set B := p₂ * r₁
  set C := r₁ * r₂
  have hC : 0 < C := Nat.mul_pos q₁.den_pos q₂.den_pos
  set g := Nat.gcd (Nat.gcd A B) C
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hC
  have dA : g ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have dB : g ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have dC : g ∣ C := Nat.gcd_dvd_right _ _
  refine ⟨c / C * g, by positivity, A / g, B / g, C / g, ?_, ?_, ?_, ?_⟩
  · rw [Nat.gcd_div dA dB, Nat.gcd_div (Nat.dvd_gcd dA dB) dC, Nat.div_self hg]
  · have : a = c * (p₁ / r₁) := by rw [← e₁, hq₁.symm]; field_simp
    rw [this, Nat.cast_div dA (by exact_mod_cast hg.ne')]
    simp only [A, C]; push_cast; field_simp
  · have : b = c * (p₂ / r₂) := by rw [← e₂, hq₂.symm]; field_simp
    rw [this, Nat.cast_div dB (by exact_mod_cast hg.ne')]
    simp only [B, C]; push_cast; field_simp
  · rw [Nat.cast_div dC (by exact_mod_cast hg.ne')]
    have : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
    field_simp

/-- **Lemma `lemma:rationality3`.** Suppose triangle `T` with incommensurable angles is tiled using
triangle `R` with angles `(α, β, 2π/3)`. Suppose `T` is not similar to `R`. Then the side lengths
`(a, b, c)` of `R` are commensurable.

"`T` is not similar to `R`" is Bonfioli's `NotSim D`: the angles of `T` are not those of `R` in any
order. -/
theorem rationality3 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hinc : ¬ CommAngles D.target) (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hns : Erdos634.Draft.LaczFormal.RG.NotSim D) : ThreeAlpha.RationalTile a b c := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := id hT
  obtain ⟨ha, hb, hc, -, hαβ, -⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  -- `R` has incommensurable angles, by `lemma:RandT`: so `α` is not a rational multiple of `π`.
  have hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * π := by
    rintro ⟨r, hr⟩
    apply hinc
    apply (RandT D).1
    rw [commAngles_iff]
    intro k
    obtain ⟨j, rfl⟩ := σ.surjective k
    fin_cases j
    · exact ⟨r, by simp only [Fin.zero_eta]; rw [h0, hr]⟩
    · exact ⟨1 / 3 - r, by simp only [Fin.mk_one]; rw [h1]; push_cast; linarith⟩
    · exact ⟨2 / 3, by
        show D.model.angleAt (σ 2) = _; rw [h2]; push_cast; ring⟩
  -- Beeson–Zhang: the sides are commensurable.
  have hdata : D.model.TwoPiThreeData α a b c :=
    ⟨σ, h0, l0, by rw [h1]; linarith, l1, h2, l2⟩
  obtain ⟨⟨p, q, hp, hq, hpq⟩, ⟨p', q', hp', hq', hpq'⟩⟩ :=
    Erdos634.Draft.LaczFormal.RG.bz_thm11 D hirr hdata hns
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0' : (0 : ℝ) < p' := by exact_mod_cast hp'
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  -- `pa = qb`, `p'a = q'c`
  refine ⟨⟨(q' : ℚ) / p', ?_⟩, ⟨(q' : ℚ) * p / (p' * q), ?_⟩, ⟨(q : ℚ) / p, ?_⟩⟩
  · push_cast; rw [div_eq_div_iff hc.ne' hp0'.ne']; linarith
  · push_cast; rw [div_eq_div_iff hc.ne' (by positivity)]; nlinarith
  · push_cast; rw [div_eq_div_iff hb.ne' hp0.ne']; linarith

/-- "`T` is not similar to the tile" when `T` has no `2π/3` angle. -/
theorem notSim_of_no120 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (h : ∀ k, D.target.angleAt k ≠ 2 * π / 3) : Erdos634.Draft.LaczFormal.RG.NotSim D := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨σ, -, -, h2, -⟩ := hT
  obtain ⟨k, hk⟩ := ρ.surjective (σ 2)
  exact h k (by rw [hρ k, hk, h2])

/-- An angle of `T` that is a rational multiple of `π` makes all three angles rational multiples
when the other two are integral combinations of it and `π`; used to see that `T` has no `2π/3`
angle. -/
theorem comm_of {N : ℕ} (D : CongruentDissection N) (h : ∀ k, ∃ q : ℚ, D.target.angleAt k = q * π) :
    CommAngles D.target := (commAngles_iff _).mpr h

/-- **Theorem `theorem:case2`.** Let triangle `T` have incommensurable angles `(α, 2α, 3β)`, and
suppose `T` is `N`-tiled by `(α, β, 2π/3)`. Then `N` is not a prime. Moreover
`N = 3λ²(a + 2b)(a + b)`, where `(a, b, c)` are integers with no common factor, proportional to the
sides of the tile, and `λ` is a positive integer.

The angles `α, 2α, 3β` are at the vertices `0, 1, 2` of `T`. -/
theorem case2 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hinc : ¬ CommAngles D.target) (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = 2 * α)
    (hC : D.target.angleAt 2 = 3 * β) :
    ¬ N.Prime ∧ ∃ a' b' c' l : ℕ, Nat.gcd (Nat.gcd a' b') c' = 1 ∧
      (∃ μ : ℝ, 0 < μ ∧ a = μ * a' ∧ b = μ * b' ∧ c = μ * c') ∧
      0 < l ∧ N = 3 * l ^ 2 * (a' + 2 * b') * (a' + b') := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := id hT
  obtain ⟨ha, hb, hc, -, hαβ, -⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  -- `T` has no `2π/3` angle, so it is not similar to the tile.
  have hno : ∀ k, D.target.angleAt k ≠ 2 * π / 3 := by
    intro k hk
    apply hinc
    have hπ := Real.pi_pos
    fin_cases k
    · -- `α = 2π/3` would make `2α > π`
      have := ThreeAlpha.tri_angle_lt_pi D.target 1
      simp only [Fin.zero_eta] at hk; rw [hA] at hk; rw [hB] at this; linarith
    · -- `2α = 2π/3`: `α = π/3`
      simp only [Fin.mk_one] at hk; rw [hB] at hk
      exact comm_of D (fun j => by
        fin_cases j
        · exact ⟨1 / 3, by rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, hA]; push_cast; linarith⟩
        · exact ⟨2 / 3, by rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, hB]; push_cast; linarith⟩
        · exact ⟨0, by
            rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, hC]; push_cast; linarith⟩)
    · -- `3β = 2π/3`: `β = 2π/9`
      have hk' : 3 * β = 2 * π / 3 := by rw [← hC]; exact hk
      exact comm_of D (fun j => by
        fin_cases j
        · exact ⟨1 / 9, by rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, hA]; push_cast; linarith⟩
        · exact ⟨2 / 9, by rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, hB]; push_cast; linarith⟩
        · exact ⟨2 / 3, by rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, hC]; push_cast; linarith⟩)
  -- By `lemma:rationality3` the sides are commensurable; scale them to integers.
  have hrat := rationality3 D hinc hT (notSim_of_no120 D hT hno)
  obtain ⟨μ, hμ, a', b', c', hg, ea, eb, ec⟩ := int_sides_of_rational ha hb hc hrat
  obtain ⟨l, hl, hN, hp⟩ := case2core D hT hA hB hC hμ hg ea eb ec
  exact ⟨hp, a', b', c', l, hg, ⟨μ, hμ, ea, eb, ec⟩, hl, hN⟩

/-- The angles `α, β` of the tile `(α, β, 2π/3)` lie strictly between `0` and `π/3`. -/
theorem tile_angles_lt {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c) :
    0 < α ∧ 0 < β ∧ α + β = π / 3 := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := id hT
  obtain ⟨-, -, -, -, hαβ, -⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  have p0 := Erdos634.MarchFlank.cornerAngle_pos D.model (σ 0)
  have p1 := Erdos634.MarchFlank.cornerAngle_pos D.model (σ 1)
  exact ⟨h0 ▸ p0, h1 ▸ p1, hαβ⟩

/-- **Theorem `theorem:case3`.** Let triangle `T` have incommensurable angles `(α, 2β, 2α + β)`,
and suppose `T` is `N`-tiled by `(α, β, 2π/3)`. Then `N` is not a prime. Moreover
`N = λ²(2a + b)(a + b)`, where `(a, b, c)` are integers with no common factor, proportional to the
sides of the tile, and `λ` is a positive integer.

The angles `α, 2β, 2α + β` are at the vertices `0, 1, 2` of `T`. -/
theorem case3 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hinc : ¬ CommAngles D.target) (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = 2 * β)
    (hC : D.target.angleAt 2 = 2 * α + β) :
    ¬ N.Prime ∧ ∃ a' b' c' l : ℕ, Nat.gcd (Nat.gcd a' b') c' = 1 ∧
      (∃ μ : ℝ, 0 < μ ∧ a = μ * a' ∧ b = μ * b' ∧ c = μ * c') ∧
      0 < l ∧ N = l ^ 2 * (2 * a' + b') * (a' + b') := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := id hT
  obtain ⟨ha, hb, hc, -, -, -⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  obtain ⟨hα, hβ, hαβ⟩ := tile_angles_lt D hT
  -- `T` has no `2π/3` angle: `α, 2β < 2π/3`, and `2α + β = 2π/3` would give `α = π/3`.
  have hno : ∀ k, D.target.angleAt k ≠ 2 * π / 3 := by
    intro k hk
    have hπ := Real.pi_pos
    fin_cases k
    · simp only [Fin.zero_eta] at hk; rw [hA] at hk; linarith
    · simp only [Fin.mk_one] at hk; rw [hB] at hk; linarith
    · have hk' : 2 * α + β = 2 * π / 3 := by rw [← hC]; exact hk
      apply hinc
      exact comm_of D (fun j => by
        fin_cases j
        · exact ⟨1 / 3, by rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, hA]; push_cast; linarith⟩
        · exact ⟨0, by rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, hB]; push_cast; linarith⟩
        · exact ⟨2 / 3, by rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, hC]; push_cast; linarith⟩)
  have hrat := rationality3 D hinc hT (notSim_of_no120 D hT hno)
  obtain ⟨μ, hμ, a', b', c', hg, ea, eb, ec⟩ := int_sides_of_rational ha hb hc hrat
  obtain ⟨l, hl, hN, hp⟩ := case3core D hT hA hB hC hμ hg ea eb ec
  exact ⟨hp, a', b', c', l, hg, ⟨μ, hμ, ea, eb, ec⟩, hl, hN⟩

/-- **Theorem `theorem:case4`.** Let triangle `T` have incommensurable angles
`(α, α + β, α + 2β)`, and suppose `T` is `N`-tiled by `(α, β, 2π/3)`. Then `N` is not a prime.
Moreover `N = λ²(a + b)/b`, where `(a, b, c)` are integers with no common factor, proportional to
the sides of the tile, and `λ` is a positive integer such that `b ∣ λ²`.

The angles `α, α + β, α + 2β` are at the vertices `0, 1, 2` of `T`; `N = λ²(a + b)/b` is written
`N b = λ²(a + b)`. -/
theorem case4 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hinc : ¬ CommAngles D.target) (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α + β)
    (hC : D.target.angleAt 2 = α + 2 * β) :
    ¬ N.Prime ∧ ∃ a' b' c' l : ℕ, Nat.gcd (Nat.gcd a' b') c' = 1 ∧
      (∃ μ : ℝ, 0 < μ ∧ a = μ * a' ∧ b = μ * b' ∧ c = μ * c') ∧
      0 < l ∧ b' ∣ l ^ 2 ∧ N * b' = l ^ 2 * (a' + b') := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := id hT
  obtain ⟨ha, hb, hc, -, -, -⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  obtain ⟨hα, hβ, hαβ⟩ := tile_angles_lt D hT
  -- `T` has no `2π/3` angle (`α + 2β = 2π/3` would give `β = π/3`).
  have hno : ∀ k, D.target.angleAt k ≠ 2 * π / 3 := by
    intro k hk
    have hπ := Real.pi_pos
    fin_cases k
    · simp only [Fin.zero_eta] at hk; rw [hA] at hk; linarith
    · simp only [Fin.mk_one] at hk; rw [hB] at hk; linarith
    · have hk' : α + 2 * β = 2 * π / 3 := by rw [← hC]; exact hk
      linarith
  have hrat := rationality3 D hinc hT (notSim_of_no120 D hT hno)
  obtain ⟨μ, hμ, a', b', c', hg, ea, eb, ec⟩ := int_sides_of_rational ha hb hc hrat
  obtain ⟨l, hl, hd, hN, hp⟩ := case4core D hT hA hB hC hμ hg ea eb ec
  exact ⟨hp, a', b', c', l, hg, ⟨μ, hμ, ea, eb, ec⟩, hl, hd, hN⟩

/-- **Theorem `theorem:case5`.** Let triangle `T` have incommensurable angles `(2α, 2β, α + β)`,
and suppose `T` is `N`-tiled by `(α, β, 2π/3)`. Then `N` is not a prime. Moreover
`N = λ²(a + 2b)(2a + b)`, where `(a, b, c)` are integers with no common factor, proportional to the
sides of the tile, and `λ` is a positive integer.

The angles `2α, 2β, α + β` are at the vertices `0, 1, 2` of `T`. -/
theorem case5 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hinc : ¬ CommAngles D.target) (hT : ThreeAlpha.TileSides D α β (2 * π / 3) a b c)
    (hA : D.target.angleAt 0 = 2 * α) (hB : D.target.angleAt 1 = 2 * β)
    (hC : D.target.angleAt 2 = α + β) :
    ¬ N.Prime ∧ ∃ a' b' c' l : ℕ, Nat.gcd (Nat.gcd a' b') c' = 1 ∧
      (∃ μ : ℝ, 0 < μ ∧ a = μ * a' ∧ b = μ * b' ∧ c = μ * c') ∧
      0 < l ∧ N = l ^ 2 * (a' + 2 * b') * (2 * a' + b') := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := id hT
  obtain ⟨ha, hb, hc, -, -, -⟩ := tile120 D.model σ h0 h1 h2 l0 l1 l2
  obtain ⟨hα, hβ, hαβ⟩ := tile_angles_lt D hT
  -- `T` has no `2π/3` angle, since `α, β < π/3`.
  have hno : ∀ k, D.target.angleAt k ≠ 2 * π / 3 := by
    intro k hk
    have hπ := Real.pi_pos
    fin_cases k
    · simp only [Fin.zero_eta] at hk; rw [hA] at hk; linarith
    · simp only [Fin.mk_one] at hk; rw [hB] at hk; linarith
    · have hk' : α + β = 2 * π / 3 := by rw [← hC]; exact hk
      linarith
  have hrat := rationality3 D hinc hT (notSim_of_no120 D hT hno)
  obtain ⟨μ, hμ, a', b', c', hg, ea, eb, ec⟩ := int_sides_of_rational ha hb hc hrat
  obtain ⟨l, hl, hN, hp⟩ := case5core D hT hA hB hC hμ hg ea eb ec
  exact ⟨hp, a', b', c', l, hg, ⟨μ, hμ, ea, eb, ec⟩, hl, hN⟩

end TriangleTiling.Prime
