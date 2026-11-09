/-
Section 10 of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*: lemmas valid for `3α + 2β = π` (`lemma:angles`, `lemma:nogammacorner`,
`lemma:anglesOK`, `lemma:gsquare`, `lemma:alphaoverpi`, `lemma:lattice`, `theorem:minlengths`,
`lemma:edgedecompositions`). `lemma:twocs` is in its own file.

Statements checked by Beeson. The proofs are the paper's; `theorem:minlengths` uses
Bonfioli's `BeesonColT29` (UNAUDITED), whose proofs are the printed lattice arguments, and
`lemma:nogammacorner` uses Bonfioli's corner angle counts `corner_fig` (the angle of `ABC` at a
vertex is the sum of the tile angles there).

A triangle `ABC` with angles `(α, β, γ)` at `A`, `B`, `C` has the opposite sides `a = |BC|`,
`b = |CA|`, `c = |AB|`.
-/
import TriangleTiling.ThreeAlpha.Basic
import TriangleTiling.ThreeAlpha.Defs
import Erdos634.Draft.BeesonShapesL5L6L11
import Erdos634.Draft.BeesonColT29
import Mathlib.NumberTheory.Niven

namespace TriangleTiling.Prime

open EuclideanGeometry Real

/-! ### Angles -/

/-- **Lemma `lemma:angles`.** Suppose `α` is not a rational multiple of `π` and `3α + 2β = π`.
Then each angle of the form `pα + qβ` can be expressed in that form for exactly one pair `(p, q)` of
nonnegative integers. Hence if a sector of angle `pα + qβ` is filled by tiles having `x` angles `α`,
`y` angles `β`, and `z` angles `γ`, then `x + 2z = p` and `y + z = q`. In particular a sector of
angle `α` or `β` is filled by one tile with that angle; of angle `α + β` by two tiles with angles
`α` and `β`; of angle `3α` by three tiles with angle `α`; of angle `α + 2β` by three tiles with
angles `α, β, β`.

"Filled" is read as the angle equation `xα + yβ + zγ = pα + qβ`, with `γ = 2α + β`. -/
theorem angles {α β : ℝ} (hirr : ¬ ∃ r : ℚ, α = r * π) (hrel : 3 * α + 2 * β = π) :
    (∀ p q u v : ℕ, (p : ℝ) * α + q * β = u * α + v * β → p = u ∧ q = v) ∧
    (∀ x y z p q : ℕ, (x : ℝ) * α + y * β + z * (2 * α + β) = p * α + q * β →
      x + 2 * z = p ∧ y + z = q) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + y * β + z * (2 * α + β) = α → x = 1 ∧ y = 0 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + y * β + z * (2 * α + β) = β → x = 0 ∧ y = 1 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + y * β + z * (2 * α + β) = α + β → x = 1 ∧ y = 1 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + y * β + z * (2 * α + β) = 3 * α → x = 3 ∧ y = 0 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + y * β + z * (2 * α + β) = α + 2 * β →
      x = 1 ∧ y = 2 ∧ z = 0) := by
  -- Uniqueness: `(p - u) α = (v - q) β` with `β/α` irrational unless `p = u`, `q = v`.
  have uniq : ∀ p q u v : ℕ, (p : ℝ) * α + q * β = u * α + v * β → p = u ∧ q = v := by
    intro p q u v h
    have hβ : β = (π - 3 * α) / 2 := by linarith
    rw [hβ] at h
    -- `(2(p - u) - 3(q - v)) α = (v - q) π`
    have key : ((2 * (p : ℝ) - 2 * u) - 3 * (q - v)) * α = (v - q) * π := by linarith
    by_cases hd : (2 * (p : ℝ) - 2 * u) - 3 * (q - v) = 0
    · have hqv : ((v : ℝ) - q) * π = 0 := by rw [← key, hd, zero_mul]
      have hqv' : (q : ℝ) = v := by
        rcases mul_eq_zero.mp hqv with h0 | h0
        · linarith
        · exact absurd h0 Real.pi_pos.ne'
      have hpu : (p : ℝ) = u := by rw [hqv'] at hd; linarith
      exact ⟨by exact_mod_cast hpu, by exact_mod_cast hqv'⟩
    · exfalso
      apply hirr
      refine ⟨((v : ℚ) - q) / ((2 * (p : ℚ) - 2 * u) - 3 * (q - v)), ?_⟩
      push_cast
      rw [div_mul_eq_mul_div, eq_div_iff hd]
      linarith [key]
  have fill : ∀ x y z p q : ℕ, (x : ℝ) * α + y * β + z * (2 * α + β) = p * α + q * β →
      x + 2 * z = p ∧ y + z = q := by
    intro x y z p q h
    have := uniq (x + 2 * z) (y + z) p q (by push_cast; linarith)
    exact this
  refine ⟨uniq, fill, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z h
    have := fill x y z 1 0 (by push_cast; linarith); omega
  · intro x y z h
    have := fill x y z 0 1 (by push_cast; linarith); omega
  · intro x y z h
    have := fill x y z 1 1 (by push_cast; linarith); omega
  · intro x y z h
    have := fill x y z 3 0 (by push_cast; linarith); omega
  · intro x y z h
    have := fill x y z 1 2 (by push_cast; linarith); omega

open Erdos634.Geometry Erdos634.BeesonColoring

/-- A tile with angles `(α, β, 2α + β)` opposite `(a, b, c)` is Bonfioli's `ThreeAlphaData`. -/
theorem threeAlphaData_of_tileSides {N : ℕ} {D : CongruentDissection N} {α β γ a b c : ℝ}
    (hγ : γ = 2 * α + β) (hT : ThreeAlpha.TileSides D α β γ a b c) :
    D.model.ThreeAlphaData α β a b c := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  exact ⟨σ, h0, l0, h1, l1, hγ ▸ h2, l2⟩

/-- **Lemma `lemma:nogammacorner`** (angles at the vertices). Suppose triangle `T` is tiled by a tile
with angles `(α, β, γ)`, where `3α + 2β = π` and `α` is not a rational multiple of `π`, and `T` is
not similar to the tile. Then no tile has its `γ` angle at a vertex of `T`.

`T` is `D.target`; "similar to the tile" is: its angles are `(α, β, γ)` in some order. -/
theorem nogammacorner {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = π) (hirr : ¬ ∃ r : ℚ, α = r * π)
    (hT : ThreeAlpha.TileSides D α β γ a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β γ) :
    ∀ (k : Fin 3) (i : Fin N) (l : Fin 3),
      (D.tile i).pts l = D.target.pts k → (D.tile i).angleAt l ≠ γ := by
  classical
  obtain ⟨σ, h0, h1, h2, -, -, -⟩ := id hT
  have hsum3 : α + β + γ = π := by
    have := cornerAngle_sum D.model
    have e : ∀ j, D.model.angleAt j = cornerAngle (D.model.pts (j + 1)) (D.model.pts j)
        (D.model.pts (j + 2)) := fun j => rfl
    have : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = π := by
      have hs : ∀ τ : Equiv.Perm (Fin 3), D.model.angleAt (τ 0) + D.model.angleAt (τ 1) +
          D.model.angleAt (τ 2) = D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 := by
        intro τ
        have := Fin.sum_univ_three (fun j => D.model.angleAt (τ j))
        rw [Equiv.sum_comp τ (fun j => D.model.angleAt j), Fin.sum_univ_three] at this
        linarith
      rw [hs, e 0, e 1, e 2]
      simpa using this
    rw [h0, h1, h2] at this; exact this
  have hγ : γ = 2 * α + β := by linarith
  have h3 := threeAlphaData_of_tileSides hγ hT
  subst hγ
  obtain ⟨-, fill, -, -, -, -, -⟩ := angles hirr hrel
  intro k i l hl hγi
  -- The corner figures: the angle of `T` at `j` is `x_j α + y_j β + z_j γ`.
  have fig := fun j => (corner_fig D hirr hrel h3 j).2
  set x := fun j => vcount D j α
  set y := fun j => vcount D j β
  set z := fun j => vcount D j (2 * α + β)
  -- A tile has its `γ` at vertex `k`, so `z_k ≥ 1`.
  have hzk : 1 ≤ z k := by
    show 1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α + β} : Finset (Fin N)).card
    apply Finset.card_pos.mpr
    refine ⟨i, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hl, Tri.localAngle_vertex]; exact hγi
  -- Each vertex is filled by at least one tile.
  have hpos : ∀ j, 1 ≤ x j + y j + z j := by
    intro j
    by_contra h0
    have hx : x j = 0 := by omega
    have hy : y j = 0 := by omega
    have hz : z j = 0 := by omega
    have := fig j
    simp only [x, y, z] at hx hy hz
    rw [hx, hy, hz] at this
    have hp : 0 < D.target.angleAt j := Erdos634.MarchFlank.cornerAngle_pos D.target j
    simp at this; linarith
  -- The angle sum of `T`: `π = Σ (x_j + 2 z_j) α + Σ (y_j + z_j) β`.
  have htsum : D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = π := by
    have := cornerAngle_sum D.target; exact this
  have hP := fill (x 0 + x 1 + x 2) (y 0 + y 1 + y 2) (z 0 + z 1 + z 2) 3 2 (by
    rw [← fig 0, ← fig 1, ← fig 2] at htsum
    push_cast; linarith)
  -- So `z_k = 1`, the other two vertices contribute `p + q ≥ 2`, hence `p = q = 1`, and the
  -- angle of `T` at `k` is `γ`; the other two angles are `α` and `β`.
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hp2 := hpos 2
  apply hns
  have ang : ∀ j, D.target.angleAt j = (x j : ℝ) * α + y j * β + z j * (2 * α + β) :=
    fun j => (fig j).symm
  have hα : ∀ j, x j = 1 → y j = 0 → z j = 0 → D.target.angleAt j = α := fun j a b c => by
    rw [ang, a, b, c]; push_cast; ring
  have hβ : ∀ j, x j = 0 → y j = 1 → z j = 0 → D.target.angleAt j = β := fun j a b c => by
    rw [ang, a, b, c]; push_cast; ring
  have hγ' : ∀ j, x j = 0 → y j = 0 → z j = 1 → D.target.angleAt j = 2 * α + β :=
    fun j a b c => by rw [ang, a, b, c]; push_cast; ring
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hzk
  · have e0 := hγ' 0 (by omega) (by omega) (by omega)
    rcases (by omega : (x 1 = 1 ∧ y 1 = 0 ∧ z 1 = 0 ∧ x 2 = 0 ∧ y 2 = 1 ∧ z 2 = 0) ∨
        (x 1 = 0 ∧ y 1 = 1 ∧ z 1 = 0 ∧ x 2 = 1 ∧ y 2 = 0 ∧ z 2 = 0)) with
      ⟨a1, b1, c1, a2, b2, c2⟩ | ⟨a1, b1, c1, a2, b2, c2⟩
    · right; right; right; right; left
      exact ⟨e0, hα 1 a1 b1 c1, hβ 2 a2 b2 c2⟩
    · right; right; right; right; right
      exact ⟨e0, hβ 1 a1 b1 c1, hα 2 a2 b2 c2⟩
  · have e1 := hγ' 1 (by omega) (by omega) (by omega)
    rcases (by omega : (x 0 = 1 ∧ y 0 = 0 ∧ z 0 = 0 ∧ x 2 = 0 ∧ y 2 = 1 ∧ z 2 = 0) ∨
        (x 0 = 0 ∧ y 0 = 1 ∧ z 0 = 0 ∧ x 2 = 1 ∧ y 2 = 0 ∧ z 2 = 0)) with
      ⟨a1, b1, c1, a2, b2, c2⟩ | ⟨a1, b1, c1, a2, b2, c2⟩
    · right; left
      exact ⟨hα 0 a1 b1 c1, e1, hβ 2 a2 b2 c2⟩
    · right; right; right; left
      exact ⟨hβ 0 a1 b1 c1, e1, hα 2 a2 b2 c2⟩
  · have e2 := hγ' 2 (by omega) (by omega) (by omega)
    rcases (by omega : (x 0 = 1 ∧ y 0 = 0 ∧ z 0 = 0 ∧ x 1 = 0 ∧ y 1 = 1 ∧ z 1 = 0) ∨
        (x 0 = 0 ∧ y 0 = 1 ∧ z 0 = 0 ∧ x 1 = 1 ∧ y 1 = 0 ∧ z 1 = 0)) with
      ⟨a1, b1, c1, a2, b2, c2⟩ | ⟨a1, b1, c1, a2, b2, c2⟩
    · left
      exact ⟨hα 0 a1 b1 c1, hβ 1 a2 b2 c2, e2⟩
    · right; right; left
      exact ⟨hβ 0 a1 b1 c1, hα 1 a2 b2 c2, e2⟩

/-! ### Parametrization -/

section Param

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Lemma `lemma:anglesOK`.** Suppose `3α + 2β = π`, and let `(a, b, c)` be the sides opposite
`(α, β, γ)` in a triangle with those angles. Then `γ = (π + α)/2`, `β = (π - 3α)/2`,
`a/c = 2 sin(α/2)`, `b/c = 2 cos α - 1 = 1 - (a/c)²`. Equivalently, `a² = c(c - b)`, and
`cos α = (b + c)/(2c)`.

The law-of-sines step (`a/c = 2 sin(α/2)`, `b/c = 1 - (a/c)²`) is TriangleTiling3's
`lemma:singamma`. -/
theorem anglesOK {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) :
    ∠ A C B = (π + ∠ B A C) / 2 ∧ ∠ A B C = (π - 3 * ∠ B A C) / 2 ∧
    dist B C / dist A B = 2 * sin (∠ B A C / 2) ∧
    dist C A / dist A B = 2 * cos (∠ B A C) - 1 ∧
    dist C A / dist A B = 1 - (dist B C / dist A B) ^ 2 ∧
    dist B C ^ 2 = dist A B * (dist A B - dist C A) ∧
    cos (∠ B A C) = (dist C A + dist A B) / (2 * dist A B) := by
  have hAC : A ≠ C := by
    intro h; apply (affineIndependent_iff_not_collinear_set.mp hABC)
    rw [h]; simp [collinear_pair]
  have hsum := angle_add_angle_add_angle_eq_pi B hAC.symm
  rw [angle_comm C B A] at hsum
  obtain ⟨-, h1, h2⟩ := ThreeAlpha.singamma hABC hrel
  have hc : 0 < dist A B := by
    apply dist_pos.mpr; intro h; apply (affineIndependent_iff_not_collinear_set.mp hABC)
    rw [h]; simp [collinear_pair]
  -- `(a/c)² = 4 sin²(α/2) = 2(1 - cos α)`
  have hsq : (2 * sin (∠ B A C / 2)) ^ 2 = 2 * (1 - cos (∠ B A C)) := by
    have h2c := Real.cos_two_mul (∠ B A C / 2)
    rw [show 2 * (∠ B A C / 2) = ∠ B A C by ring] at h2c
    have hs := Real.sin_sq_add_cos_sq (∠ B A C / 2)
    nlinarith
  have hb : dist C A / dist A B = 2 * cos (∠ B A C) - 1 := by rw [h2]; linarith
  refine ⟨by linarith, by linarith, h1, hb, by rw [h1, h2], ?_, ?_⟩
  · have e : dist C A / dist A B = 1 - (dist B C / dist A B) ^ 2 := by rw [h1, h2]
    field_simp at e
    nlinarith [e]
  · have := hb
    field_simp at this ⊢
    linarith

/-- **Lemma `lemma:gsquare`.** Suppose `3α + 2β = π`, and `(a, b, c)` are the sides of a triangle
with angles `(α, β, γ)`. Suppose `(a, b, c)` are integers with no common factor. Let `a/c = m/k` in
lowest terms. Then `(a, b, c) = (mk, k² - m², k²)`, and `k = gcd(a, c)` and `m = a/k` and `m < k`.

The same statement as TriangleTiling3's `lemma:gsquare`. -/
theorem gsquare {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) {a b c m k : ℕ}
    (ha : dist B C = a) (hb : dist C A = b) (hc : dist A B = c)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1)
    (hmk : Nat.Coprime m k) (hk : 0 < k) (hratio : a * k = m * c) :
    a = m * k ∧ b = k ^ 2 - m ^ 2 ∧ c = k ^ 2 ∧ k = Nat.gcd a c ∧ m = a / k ∧ m < k :=
  ThreeAlpha.gsquare hABC hrel ha hb hc hgcd hmk hk hratio

-- `hgcd` is part of the printed hypotheses; the proof does not need it.
set_option linter.unusedVariables false in
/-- **Lemma `lemma:alphaoverpi`.** Suppose `3α + 2β = π`, and `(a, b, c)` are the sides of a
triangle with angles `(α, β, γ)`. Suppose `(a, b, c)` are integers with no common factor. Then
`α/π` and `β/π` are irrational. -/
theorem alphaoverpi {A B C : P} (hABC : AffineIndependent ℝ ![A, B, C])
    (hrel : 3 * ∠ B A C + 2 * ∠ A B C = π) {a b c : ℕ}
    (ha : dist B C = a) (hb : dist C A = b) (hc : dist A B = c)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) :
    (¬ ∃ r : ℚ, ∠ B A C = r * π) ∧ ¬ ∃ r : ℚ, ∠ A B C = r * π := by
  have h := affineIndependent_iff_not_collinear_set.mp hABC
  have h1 : ¬ Collinear ℝ ({B, A, C} : Set P) := by rwa [Set.insert_comm]
  have h2 : ¬ Collinear ℝ ({A, C, B} : Set P) := by rwa [Set.pair_comm]
  have hAB : A ≠ B := ne₁₂_of_not_collinear h
  have hAC : A ≠ C := ne₁₃_of_not_collinear h
  have hBC : B ≠ C := ne₂₃_of_not_collinear h
  have hsum := angle_add_angle_add_angle_eq_pi B hAC.symm
  rw [angle_comm C B A] at hsum
  have hα0 := angle_pos_of_not_collinear h1
  have hβ0 := angle_pos_of_not_collinear h
  have hγ0 := angle_pos_of_not_collinear h2
  have ha0 : (0 : ℝ) < a := ha ▸ dist_pos.mpr hBC
  have hb0 : (0 : ℝ) < b := hb ▸ dist_pos.mpr hAC.symm
  have hc0 : (0 : ℝ) < c := hc ▸ dist_pos.mpr hAB
  -- By the law of cosines the cosines of the angles are rational.
  have hBA : dist B A = c := by rw [dist_comm, hc]
  have hCB : dist C B = a := by rw [dist_comm, ha]
  have hAC' : dist A C = b := by rw [dist_comm, hb]
  have cα : ∃ q : ℚ, cos (∠ B A C) = q := by
    have lc := law_cos B A C
    rw [ha, hBA, hb] at lc
    refine ⟨((c : ℚ) ^ 2 + b ^ 2 - a ^ 2) / (2 * c * b), ?_⟩
    push_cast; rw [eq_div_iff (by positivity)]; linear_combination lc
  have cβ : ∃ q : ℚ, cos (∠ A B C) = q := by
    have lc := law_cos A B C
    rw [hAC', hc, hCB] at lc
    refine ⟨((c : ℚ) ^ 2 + a ^ 2 - b ^ 2) / (2 * c * a), ?_⟩
    push_cast; rw [eq_div_iff (by positivity)]; linear_combination lc
  have cγ : ∃ q : ℚ, cos (∠ A C B) = q := by
    have lc := law_cos A C B
    rw [hc, hAC', ha] at lc
    refine ⟨((b : ℚ) ^ 2 + a ^ 2 - c ^ 2) / (2 * b * a), ?_⟩
    push_cast; rw [eq_div_iff (by positivity)]; linear_combination lc
  -- Niven: a rational multiple of `π` in `(0, π)` with rational cosine is `π/3`, `π/2` or `2π/3`.
  have niv : ∀ θ : ℝ, 0 < θ → θ < π → (∃ r : ℚ, θ = r * π) → (∃ q : ℚ, cos θ = q) →
      θ = π / 3 ∨ θ = π / 2 ∨ θ = 2 * π / 3 := by
    intro θ h0 hπ hr hq
    have hn := niven hr hq
    have hlt : cos θ < 1 := by
      rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hπ.le h0
    have hgt : -1 < cos θ := by
      rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
    have inj := fun (t : ℝ) (h0' : 0 ≤ t) (ht : t ≤ π) (e : cos θ = cos t) =>
      Real.injOn_cos ⟨h0.le, hπ.le⟩ ⟨h0', ht⟩ e
    have hπ0 := Real.pi_pos
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with e | e | e | e | e
    · linarith
    · right; right; apply inj _ (by positivity) (by linarith)
      rw [e, show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
      try norm_num
    · right; left; apply inj _ (by positivity) (by linarith); rw [e, Real.cos_pi_div_two]
      try norm_num
    · left; apply inj _ (by positivity) (by linarith); rw [e, Real.cos_pi_div_three]
      try norm_num
    · linarith
  -- If `α/π` (equivalently `β/π`) is rational, all three angles are, and the triangle is
  -- equilateral, contradicting `3α + 2β = π`.
  have key : (∃ r : ℚ, ∠ B A C = r * π) → False := by
    rintro ⟨r, hr⟩
    have hβr : ∃ s : ℚ, ∠ A B C = s * π :=
      ⟨(1 - 3 * r) / 2, by push_cast; linear_combination (hrel - 3 * hr) / 2⟩
    have hγr : ∃ s : ℚ, ∠ A C B = s * π :=
      ⟨(1 + r) / 2, by push_cast; linear_combination hsum - hr - (hrel - 3 * hr) / 2⟩
    rcases niv _ hα0 (by linarith) ⟨r, hr⟩ cα with e1 | e1 | e1 <;>
    rcases niv _ hβ0 (by linarith) hβr cβ with e2 | e2 | e2 <;>
    rcases niv _ hγ0 (by linarith) hγr cγ with e3 | e3 | e3 <;>
    · rw [e1, e2] at hrel; linarith [Real.pi_pos]
  refine ⟨key, fun ⟨s, hs⟩ => key ⟨(1 - 2 * s) / 3, by
    push_cast; linear_combination (hrel - 2 * hs) / 3⟩⟩

end Param

/-! ### The relation lattice

Throughout, `m` and `k` are coprime with `0 < m < k`, and `(a, b, c) = (mk, k² - m², k²)`. -/

/-- **Lemma `lemma:lattice`.** The relation lattice `K = {(x, y, z) ∈ ℤ³ : xa + yb + zc = 0}` is a
free abelian group of rank `2`, with basis `e₁ = (k, 0, -m)`, `e₂ = (m, k, -k)`. Consequently, for
every `(x, y, z) ∈ K`, `k ∣ y` and `m ∣ y + z`.

"Free of rank 2 with basis `e₁, e₂`": every point of `K` is `ξe₁ + ηe₂` for exactly one pair
`(ξ, η)`, and `e₁, e₂ ∈ K`. -/
theorem lattice {m k : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (k * (m * k) + 0 * (k ^ 2 - m ^ 2) + (-m) * k ^ 2 = 0 ∧
      m * (m * k) + k * (k ^ 2 - m ^ 2) + (-k) * k ^ 2 = 0) ∧
    (∀ x y z : ℤ, x * (m * k) + y * (k ^ 2 - m ^ 2) + z * k ^ 2 = 0 →
      ∃ ξ η : ℤ, x = ξ * k + η * m ∧ y = η * k ∧ z = -ξ * m - η * k) ∧
    (∀ ξ η ξ' η' : ℤ, ξ * k + η * m = ξ' * k + η' * m → η * k = η' * k → ξ = ξ' ∧ η = η') ∧
    (∀ x y z : ℤ, x * (m * k) + y * (k ^ 2 - m ^ 2) + z * k ^ 2 = 0 → k ∣ y ∧ m ∣ y + z) := by
  have hk : 0 < k := by linarith
  have gen : ∀ x y z : ℤ, x * (m * k) + y * (k ^ 2 - m ^ 2) + z * k ^ 2 = 0 →
      ∃ ξ η : ℤ, x = ξ * k + η * m ∧ y = η * k ∧ z = -ξ * m - η * k := by
    intro x y z h
    -- modulo `k`: `-y m² ≡ 0`, so `k ∣ y`
    have h1 : k ∣ y * m ^ 2 := ⟨x * m + y * k + z * k, by linear_combination -h⟩
    obtain ⟨η, hη⟩ := (hcop.pow_left (m := 2)).symm.dvd_of_dvd_mul_right h1
    -- `(x - ηm) m = -(z + ηk) k`, so `k ∣ x - ηm`
    have h2 : (x - η * m) * m = -(z + η * k) * k := by
      have : k * ((x - η * m) * m + (z + η * k) * k) = 0 := by
        rw [hη] at h; linear_combination h
      have := (mul_eq_zero.mp this).resolve_left hk.ne'
      linarith
    have h3 : k ∣ (x - η * m) * m := ⟨-(z + η * k), by rw [h2]; ring⟩
    obtain ⟨ξ, hξ⟩ := hcop.symm.dvd_of_dvd_mul_right h3
    refine ⟨ξ, η, by linarith, by rw [hη]; ring, ?_⟩
    have : k * (z + η * k + ξ * m) = 0 := by rw [hξ] at h2; linear_combination h2
    have := (mul_eq_zero.mp this).resolve_left hk.ne'
    linarith
  refine ⟨⟨by ring, by ring⟩, gen, ?_, ?_⟩
  · intro ξ η ξ' η' e1 e2
    have hη : η = η' := mul_right_cancel₀ hk.ne' e2
    subst hη
    exact ⟨mul_right_cancel₀ hk.ne' (by linarith), rfl⟩
  · intro x y z h
    obtain ⟨ξ, η, -, hy, hz⟩ := gen x y z h
    exact ⟨⟨η, by rw [hy]; ring⟩, ⟨-ξ, by rw [hy, hz]; ring⟩⟩

/-- **Theorem `theorem:minlengths`** (arithmetic of the relation lattice). Let `m, k` be coprime
positive integers with `m < k`, and put `a = mk`, `b = k² - m²`, `c = k²`. For positive integers `h`
and nonnegative integers `p, q`, call an identity of one of the nine forms below a relation of that
type, and require `p, q ≥ 1` in the three mixed forms. Then each type has solutions, and the least
value of the common quantity `ha`, `hb` or `hc` is:
`ha = pb + qc`: `mk[k⌊k/m⌋ + k - m]`; `ha = pb`: `ab`; `ha = qc`: `mk² = ka`;
`hb = pa + qc`: `kb`; `hb = pa`: `ab`; `hb = qc`: `bc`;
`hc = pa + qb`: `kc = k³`; `hc = pa`: `mc = mk²`; `hc = qb`: `bc`.

Each type is stated as: some relation of that type has the least value, and every relation of that
type has at least that value; `a, b, c` are written out. `⌊k/m⌋` is the integer quotient `k / m`. -/
theorem minlengths {m k : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    -- `ha = pb + qc`
    ((∃ h p q : ℤ, 1 ≤ h ∧ 1 ≤ p ∧ 1 ≤ q ∧ h * (m * k) = p * (k ^ 2 - m ^ 2) + q * k ^ 2 ∧
        h * (m * k) = m * k * (k * (k / m) + k - m)) ∧
      ∀ h p q : ℤ, 1 ≤ h → 1 ≤ p → 1 ≤ q → h * (m * k) = p * (k ^ 2 - m ^ 2) + q * k ^ 2 →
        m * k * (k * (k / m) + k - m) ≤ h * (m * k)) ∧
    -- `ha = pb`
    ((∃ h p : ℤ, 1 ≤ h ∧ 0 ≤ p ∧ h * (m * k) = p * (k ^ 2 - m ^ 2) ∧
        h * (m * k) = m * k * (k ^ 2 - m ^ 2)) ∧
      ∀ h p : ℤ, 1 ≤ h → 0 ≤ p → h * (m * k) = p * (k ^ 2 - m ^ 2) →
        m * k * (k ^ 2 - m ^ 2) ≤ h * (m * k)) ∧
    -- `ha = qc`
    ((∃ h q : ℤ, 1 ≤ h ∧ 0 ≤ q ∧ h * (m * k) = q * k ^ 2 ∧ h * (m * k) = k * (m * k)) ∧
      ∀ h q : ℤ, 1 ≤ h → 0 ≤ q → h * (m * k) = q * k ^ 2 → k * (m * k) ≤ h * (m * k)) ∧
    -- `hb = pa + qc`
    ((∃ h p q : ℤ, 1 ≤ h ∧ 1 ≤ p ∧ 1 ≤ q ∧ h * (k ^ 2 - m ^ 2) = p * (m * k) + q * k ^ 2 ∧
        h * (k ^ 2 - m ^ 2) = k * (k ^ 2 - m ^ 2)) ∧
      ∀ h p q : ℤ, 1 ≤ h → 1 ≤ p → 1 ≤ q → h * (k ^ 2 - m ^ 2) = p * (m * k) + q * k ^ 2 →
        k * (k ^ 2 - m ^ 2) ≤ h * (k ^ 2 - m ^ 2)) ∧
    -- `hb = pa`
    ((∃ h p : ℤ, 1 ≤ h ∧ 0 ≤ p ∧ h * (k ^ 2 - m ^ 2) = p * (m * k) ∧
        h * (k ^ 2 - m ^ 2) = m * k * (k ^ 2 - m ^ 2)) ∧
      ∀ h p : ℤ, 1 ≤ h → 0 ≤ p → h * (k ^ 2 - m ^ 2) = p * (m * k) →
        m * k * (k ^ 2 - m ^ 2) ≤ h * (k ^ 2 - m ^ 2)) ∧
    -- `hb = qc`
    ((∃ h q : ℤ, 1 ≤ h ∧ 0 ≤ q ∧ h * (k ^ 2 - m ^ 2) = q * k ^ 2 ∧
        h * (k ^ 2 - m ^ 2) = (k ^ 2 - m ^ 2) * k ^ 2) ∧
      ∀ h q : ℤ, 1 ≤ h → 0 ≤ q → h * (k ^ 2 - m ^ 2) = q * k ^ 2 →
        (k ^ 2 - m ^ 2) * k ^ 2 ≤ h * (k ^ 2 - m ^ 2)) ∧
    -- `hc = pa + qb`
    ((∃ h p q : ℤ, 1 ≤ h ∧ 1 ≤ p ∧ 1 ≤ q ∧ h * k ^ 2 = p * (m * k) + q * (k ^ 2 - m ^ 2) ∧
        h * k ^ 2 = k ^ 3) ∧
      ∀ h p q : ℤ, 1 ≤ h → 1 ≤ p → 1 ≤ q → h * k ^ 2 = p * (m * k) + q * (k ^ 2 - m ^ 2) →
        k ^ 3 ≤ h * k ^ 2) ∧
    -- `hc = pa`
    ((∃ h p : ℤ, 1 ≤ h ∧ 0 ≤ p ∧ h * k ^ 2 = p * (m * k) ∧ h * k ^ 2 = m * k ^ 2) ∧
      ∀ h p : ℤ, 1 ≤ h → 0 ≤ p → h * k ^ 2 = p * (m * k) → m * k ^ 2 ≤ h * k ^ 2) ∧
    -- `hc = qb`
    ((∃ h q : ℤ, 1 ≤ h ∧ 0 ≤ q ∧ h * k ^ 2 = q * (k ^ 2 - m ^ 2) ∧
        h * k ^ 2 = (k ^ 2 - m ^ 2) * k ^ 2) ∧
      ∀ h q : ℤ, 1 ≤ h → 0 ≤ q → h * k ^ 2 = q * (k ^ 2 - m ^ 2) →
        (k ^ 2 - m ^ 2) * k ^ 2 ≤ h * k ^ 2) := by
  have hk : 0 < k := by linarith
  have ha : 0 < m * k := by positivity
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  have hc : 0 < k ^ 2 := by positivity
  have ea : m * k = k * m := by ring
  -- In the pure types `p ≥ 0` and `h ≥ 1` force `p ≥ 1`.
  have pos : ∀ {h p X Y : ℤ}, 0 < X → 0 < Y → 1 ≤ h → 0 ≤ p → h * X = p * Y → 1 ≤ p := by
    intro h p X Y hX hY hh hp e
    by_contra hc; push Not at hc
    have : p = 0 := by omega
    rw [this, zero_mul] at e
    nlinarith
  have mono : ∀ {u v X : ℤ}, 0 < X → u ≤ v → u * X ≤ v * X := fun hX huv =>
    mul_le_mul_of_nonneg_right huv hX.le
  obtain ⟨⟨h1, p1, q1, hp1, hq1, e1, f1⟩, g1⟩ := Erdos634.BeesonColT29.t29_a_bc hm hmk hcop
  obtain ⟨⟨h2, p2, hh2, hp2, e2, f2⟩, g2⟩ := Erdos634.BeesonColT29.t29_a_b hm hmk hcop
  obtain ⟨⟨h3, q3, hh3, hq3, e3, f3⟩, g3⟩ := Erdos634.BeesonColT29.t29_a_c hm hmk hcop
  obtain ⟨⟨h4, p4, q4, hp4, hq4, e4, f4⟩, g4⟩ := Erdos634.BeesonColT29.t29_b_ac hm hmk hcop
  obtain ⟨⟨h5, p5, hh5, hp5, e5, f5⟩, g5⟩ := Erdos634.BeesonColT29.t29_b_a hm hmk hcop
  obtain ⟨⟨h6, q6, hh6, hq6, e6, f6⟩, g6⟩ := Erdos634.BeesonColT29.t29_b_c hm hmk hcop
  obtain ⟨⟨h7, p7, q7, hp7, hq7, e7, f7⟩, g7⟩ := Erdos634.BeesonColT29.t29_c_ab hm hmk hcop
  obtain ⟨⟨h8, p8, hh8, hp8, e8, f8⟩, g8⟩ := Erdos634.BeesonColT29.t29_c_a hm hmk hcop
  obtain ⟨⟨h9, q9, hh9, hq9, e9, f9⟩, g9⟩ := Erdos634.BeesonColT29.t29_c_b hm hmk hcop
  have hkm1 : 1 ≤ k * (k / m) + k - m := by
    have : 1 ≤ k / m := Int.le_ediv_of_mul_le hm (by linarith)
    nlinarith
  refine ⟨⟨⟨h1, p1, q1, by rw [f1]; exact hkm1, hp1, hq1, by rw [ea]; exact e1,
      by rw [f1]; try ring⟩, fun h p q hh hp hq e => ?_⟩,
    ⟨⟨h2, p2, hh2, by linarith, by rw [ea]; exact e2, by rw [f2]; try ring⟩,
      fun h p hh hp e => ?_⟩,
    ⟨⟨h3, q3, hh3, by linarith, by rw [ea]; exact e3, by rw [f3]; try ring⟩,
      fun h q hh hq e => ?_⟩,
    ⟨⟨h4, p4, q4, by rw [f4]; linarith, hp4, hq4, by rw [ea]; exact e4, by rw [f4]; try ring⟩,
      fun h p q hh hp hq e => ?_⟩,
    ⟨⟨h5, p5, hh5, by linarith, by rw [ea]; exact e5, by rw [f5]; try ring⟩,
      fun h p hh hp e => ?_⟩,
    ⟨⟨h6, q6, hh6, by linarith, e6, by rw [f6]; try ring⟩, fun h q hh hq e => ?_⟩,
    ⟨⟨h7, p7, q7, by rw [f7]; linarith, hp7, hq7, by rw [ea]; exact e7, by rw [f7]; try ring⟩,
      fun h p q hh hp hq e => ?_⟩,
    ⟨⟨h8, p8, hh8, by linarith, by rw [ea]; exact e8, by rw [f8]; try ring⟩,
      fun h p hh hp e => ?_⟩,
    ⟨⟨h9, q9, hh9, by linarith, e9, by rw [f9]; try ring⟩, fun h q hh hq e => ?_⟩⟩
  · have := g1 h p q hp hq (by rw [← ea]; exact e)
    rw [mul_comm (m * k)]; exact mono ha this
  · have := g2 h p hh (pos ha hb hh hp e) (by rw [← ea]; exact e)
    rw [mul_comm (m * k)]; exact mono ha this
  · have := g3 h q hh (pos ha hc hh hq e) (by rw [← ea]; exact e)
    exact mono ha this
  · have := g4 h p q hh hp hq (by rw [← ea]; exact e)
    exact mono hb this
  · have := g5 h p hh (pos hb ha hh hp e) (by rw [← ea]; exact e)
    rw [ea]; exact mono hb this
  · have := g6 h q hh (pos hb hc hh hq e) e
    rw [mul_comm (k ^ 2 - m ^ 2)]; exact mono hb this
  · have := g7 h p q hh hp hq (by rw [← ea]; exact e)
    rw [show k ^ 3 = k * k ^ 2 by ring]; exact mono hc this
  · have := g8 h p hh (pos hc ha hh hp e) (by rw [← ea]; exact e)
    exact mono hc this
  · have := g9 h q hh (pos hc hb hh hq e) e
    exact mono hc this

/-! ### Edge decompositions -/

/-- **Lemma `lemma:edgedecompositions`.** Let `(a, b, c) = (km, k² - m², k²)` with `0 < m < k` and
`gcd(m, k) = 1`. Let `1 ≤ n < k`. Then
(A) the only edge decomposition of `na` is `(n, 0, 0)`;
(B) the only edge decomposition of `nb` is `(0, n, 0)`;
(C) every edge decomposition `(p, q, r)` of `nc` has `q = 0`;
(D) the only edge decomposition `(p, q, r)` of `m(b + 2c)` with `r ≥ k` is `(0, m, 2m)`; there is
none if `2m < k`;
(E) no edge decomposition `(p, q, r)` of `m(b + c)` has `r ≥ k`.

An edge decomposition of `ℓ` is a triple `(p, q, r)` of nonnegative integers with
`pa + qb + rc = ℓ`; `a, b, c` are written out. -/
theorem edgedecompositions {m k : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∀ n p q r : ℤ, 1 ≤ n → n < k → 0 ≤ p → 0 ≤ q → 0 ≤ r →
      p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = n * (m * k) → p = n ∧ q = 0 ∧ r = 0) ∧
    (∀ n p q r : ℤ, 1 ≤ n → n < k → 0 ≤ p → 0 ≤ q → 0 ≤ r →
      p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = n * (k ^ 2 - m ^ 2) →
        p = 0 ∧ q = n ∧ r = 0) ∧
    (∀ n p q r : ℤ, 1 ≤ n → n < k → 0 ≤ p → 0 ≤ q → 0 ≤ r →
      p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = n * k ^ 2 → q = 0) ∧
    (∀ p q r : ℤ, 0 ≤ p → 0 ≤ q → 0 ≤ r →
      p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) →
        k ≤ r → p = 0 ∧ q = m ∧ r = 2 * m) ∧
    (2 * m < k → ∀ p q r : ℤ, 0 ≤ p → 0 ≤ q → 0 ≤ r →
      p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) →
        r < k) ∧
    (∀ p q r : ℤ, 0 ≤ p → 0 ≤ q → 0 ≤ r →
      p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = m * ((k ^ 2 - m ^ 2) + k ^ 2) → r < k) := by
  have hk : 0 < k := by linarith
  obtain ⟨⟨-, gabc⟩, ⟨-, gab⟩, ⟨-, gac⟩, ⟨-, gbac⟩, ⟨-, gba⟩, ⟨-, gbc⟩, ⟨-, gcab⟩, ⟨-, gca⟩,
    ⟨-, gcb⟩⟩ := minlengths hm hmk hcop
  have L := (lattice hm hmk hcop).2.1
  set a := m * k with ha_def
  set b := k ^ 2 - m ^ 2 with hb_def
  set c := k ^ 2 with hc_def
  have hb : k < b := by rw [hb_def]; nlinarith
  have ha : k ≤ a := by rw [ha_def]; nlinarith
  have hc : k < c := by rw [hc_def]; nlinarith
  have hpos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hcpos : 0 < c := by linarith
  -- `u X ≤ v X` with `X > 0` gives `u ≤ v`.
  have canc : ∀ {u v X : ℤ}, 0 < X → u * X ≤ v * X → u ≤ v := fun hX h =>
    le_of_mul_le_mul_right h hX
  -- a relation with `h ≥ 1` and a positive right side
  have pos1 : ∀ {h X R : ℤ}, 0 < X → 0 < R → h * X = R → 1 ≤ h := by
    intro h X R hX hR e
    by_contra h0; push Not at h0
    have : h * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hX.le
    linarith
  -- From the lattice: `q = m + ηk ≥ 0` gives `η ≥ 0`; for `η ≥ 1`, `p = ξk + ηm ≥ 0` gives
  -- `ξ ≥ 1 - η`; for `η = 0`, `p = ξk ≥ 0` gives `ξ ≥ 0`.
  have eta0 : ∀ {q η : ℤ}, 0 ≤ q → q - m = η * k → 0 ≤ η := by
    intro q η hq e2
    by_contra h0; push Not at h0
    have := mul_le_mul_of_nonneg_right (show η ≤ -1 by omega) hk.le
    linarith
  have xi1 : ∀ {p ξ η : ℤ}, 0 ≤ p → p = ξ * k + η * m → 1 ≤ η → 1 - η ≤ ξ := by
    intro p ξ η hp e1 hη
    by_contra h0; push Not at h0
    have h1 := mul_le_mul_of_nonneg_right (show ξ ≤ -η by omega) hk.le
    have h2 : 0 < η * (k - m) := mul_pos (by omega) (by linarith)
    linarith
  have xi0 : ∀ {p ξ : ℤ}, 0 ≤ p → p = ξ * k + 0 * m → 0 ≤ ξ := by
    intro p ξ hp e1
    by_contra h0; push Not at h0
    have := mul_neg_of_neg_of_pos h0 hk
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (A) an `a`-relation `ha = qb + rc` with `1 ≤ h < k`
    intro n p q r hn hnk hp hq hr e
    by_contra hne
    have hqr : 0 < q + r := by
      by_contra h0; push Not at h0
      have hq0 : q = 0 := by omega
      have hr0 : r = 0 := by omega
      subst hq0 hr0
      exact hne ⟨mul_right_cancel₀ hpos.ne' (by linarith), rfl, rfl⟩
    have hrel : (n - p) * a = q * b + r * c := by linarith
    have hR : 0 < q * b + r * c := by
      rcases (by omega : 0 < q ∨ 0 < r) with h | h
      · nlinarith
      · nlinarith
    have hh := pos1 hpos hR hrel
    rcases (by omega : (1 ≤ q ∧ 1 ≤ r) ∨ (1 ≤ q ∧ r = 0) ∨ (q = 0 ∧ 1 ≤ r)) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `h ≥ k⌊k/m⌋ + k - m > k`
      have g := gabc (n - p) q r hh h1 h2 hrel
      rw [mul_comm a] at g
      have := canc hpos g
      have hfl : 1 ≤ k / m := Int.le_ediv_of_mul_le hm (by linarith)
      nlinarith
    · subst h2
      have g := gab (n - p) q hh hq (by linarith)
      rw [mul_comm a] at g
      have := canc hpos g
      linarith
    · subst h1
      have := canc hpos (gac (n - p) r hh hr (by linarith))
      linarith
  · -- (B) a `b`-relation `hb = pa + rc` with `1 ≤ h < k`
    intro n p q r hn hnk hp hq hr e
    by_contra hne
    have hpr : 0 < p + r := by
      by_contra h0; push Not at h0
      have hp0 : p = 0 := by omega
      have hr0 : r = 0 := by omega
      subst hp0 hr0
      exact hne ⟨rfl, mul_right_cancel₀ hbpos.ne' (by linarith), rfl⟩
    have hrel : (n - q) * b = p * a + r * c := by linarith
    have hR : 0 < p * a + r * c := by
      rcases (by omega : 0 < p ∨ 0 < r) with h | h
      · nlinarith
      · nlinarith
    have hh := pos1 hbpos hR hrel
    rcases (by omega : (1 ≤ p ∧ 1 ≤ r) ∨ (1 ≤ p ∧ r = 0) ∨ (p = 0 ∧ 1 ≤ r)) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := canc hbpos (gbac (n - q) p r hh h1 h2 hrel)
      linarith
    · subst h2
      have := canc hbpos (gba (n - q) p hh hp (by linarith))
      linarith
    · subst h1
      have g := gbc (n - q) r hh hr (by linarith)
      rw [mul_comm b] at g
      have := canc hbpos g
      linarith
  · -- (C) a `c`-relation `hc = pa + qb` with `q > 0` and `1 ≤ h < k`
    intro n p q r hn hnk hp hq hr e
    by_contra hq0
    have hq1 : 1 ≤ q := by omega
    have hrel : (n - r) * c = p * a + q * b := by linarith
    have hR : 0 < p * a + q * b := by nlinarith
    have hh := pos1 hcpos hR hrel
    rcases (by omega : 1 ≤ p ∨ p = 0) with h1 | h1
    · have g := gcab (n - r) p q hh h1 hq1 hrel
      rw [show k ^ 3 = k * c by rw [hc_def]; ring] at g
      have := canc hcpos g
      linarith
    · subst h1
      have := canc hcpos (gcb (n - r) q hh hq (by linarith))
      linarith
  · -- (D) by the lattice: `p = ξk + ηm`, `q = m + ηk`, `r = 2m - ξm - ηk`
    intro p q r hp hq hr e hrk
    obtain ⟨ξ, η, e1, e2, e3⟩ := L p (q - m) (r - 2 * m) (by linear_combination e)
    have hη0 := eta0 hq e2
    rcases (by omega : η = 0 ∨ 1 ≤ η) with hη | hη
    · subst hη
      have hξ0 := xi0 hp e1
      have hξ1 : ξ ≤ 0 := by
        by_contra h0; push Not at h0
        have := mul_le_mul_of_nonneg_right (show 1 ≤ ξ by omega) hm.le
        linarith
      have : ξ = 0 := by omega
      subst this
      refine ⟨by linarith, by linarith, by linarith⟩
    · -- `ξ ≥ 1 - η`, so `r ≤ m - η(k - m) < m < k`
      have hξ := xi1 hp e1 hη
      have h1 := mul_le_mul_of_nonneg_right hξ hm.le
      have h2 : 0 ≤ η * (k - m) := mul_nonneg (by omega) (by linarith)
      linarith
  · -- (D), none if `2m < k`
    intro h2m p q r hp hq hr e
    by_contra hrk; push Not at hrk
    obtain ⟨ξ, η, e1, e2, e3⟩ := L p (q - m) (r - 2 * m) (by linear_combination e)
    have hη0 := eta0 hq e2
    rcases (by omega : η = 0 ∨ 1 ≤ η) with hη | hη
    · subst hη
      have hξ0 := xi0 hp e1
      have := mul_nonneg hξ0 hm.le
      linarith
    · have hξ := xi1 hp e1 hη
      have h1 := mul_le_mul_of_nonneg_right hξ hm.le
      have h2 : 0 ≤ η * (k - m) := mul_nonneg (by omega) (by linarith)
      linarith
  · -- (E) as in (D): `p = ξk + ηm`, `q = m + ηk`, `r = m - ξm - ηk`
    intro p q r hp hq hr e
    by_contra hrk; push Not at hrk
    obtain ⟨ξ, η, e1, e2, e3⟩ := L p (q - m) (r - m) (by linear_combination e)
    have hη0 := eta0 hq e2
    rcases (by omega : η = 0 ∨ 1 ≤ η) with hη | hη
    · subst hη
      have hξ0 := xi0 hp e1
      have := mul_nonneg hξ0 hm.le
      linarith
    · have hξ := xi1 hp e1 hη
      have h1 := mul_le_mul_of_nonneg_right hξ hm.le
      have h2 : 0 ≤ η * (k - m) := mul_nonneg (by omega) (by linarith)
      linarith

end TriangleTiling.Prime
