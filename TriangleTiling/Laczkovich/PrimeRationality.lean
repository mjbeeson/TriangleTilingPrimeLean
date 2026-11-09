/-
`theorem:rationality` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 1): Beeson–Zhang, *Rationality of certain triangle tilings*, Theorem 1.2.

The paper cites it. Here it is assembled, row by row, from Laczkovich's table of tilings by a tile
with incommensurable angles (`Laczkovich.table_incommensurable`): a tile not similar to `T` and not
a right triangle is one of
* `(α, 2π/3 - α, π/3)` tiling an equilateral `T`: Laczkovich 2012, Theorem 3.3, as used in the
  equilateral paper (`Equilateral.sixty_rational`);
* `(α, π - 3α, 2α)` tiling `(α, α, π - 2α)`: the isosceles paper's `theorem:rationaltile`
  (`TriangleTiling.rationaltile`);
* `(α, β, 2α + β)` with `3α + 2β = π`: `TriangleTiling3` `theorem:rationaltile`
  (`ThreeAlpha.rationaltile`);
* `(α, π/3 - α, 2π/3)`: Beeson–Zhang Theorem 1.1 (Bonfioli's `bz_thm11`).

"`R` is not similar to `T`" is Bonfioli's `NotSim D` (the angles of `T` are not those of `R` in any
order), as in `lemma:rationality3`. "`R` has incommensurable angles" is: some angle of `R` is not a
rational multiple of `π`. "`R` has commensurable sides" is: the ratio of any two sides of `R` is
rational.

Statement checked by Beeson.
-/
import TriangleTiling.Laczkovich.PrimeIsoPrime
import TriangleTiling.Laczkovich.PrimeGroup2
import TriangleTiling.Laczkovich.EquilateralSixty
import TriangleTiling.Isosceles.RationalTile

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.Laczkovich

variable {N : ℕ}

theorem fin3_all {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k, P k := by
  intro k; fin_cases k
  · exact h0
  · exact h1
  · exact h2

/-- If every side is a rational multiple of `C`, the sides are commensurable. -/
theorem commSides_of (T : Tri) (C : ℝ) (σ : Equiv.Perm (Fin 3))
    (h : ∀ k, ∃ u : ℚ, T.oppLen (σ k) = u * C) :
    ∀ i j : Fin 3, ∃ q : ℚ, T.oppLen i = q * T.oppLen j := by
  have key : ∀ i, ∃ u : ℚ, T.oppLen i = u * C := fun i => by
    obtain ⟨k, rfl⟩ := σ.surjective i; exact h k
  intro i j
  obtain ⟨u, hu⟩ := key i
  obtain ⟨v, hv⟩ := key j
  have hj := T.oppLen_pos j
  have hv0 : (v : ℝ) ≠ 0 := by rintro e; rw [hv, e, zero_mul] at hj; exact lt_irrefl _ hj
  refine ⟨u / v, ?_⟩
  rw [hu, hv]; push_cast; field_simp

/-- A ratio `x / C = q` with `C ≠ 0` writes `x` as `q C`. -/
theorem eq_mul_of_div {x C : ℝ} {q : ℚ} (hC : C ≠ 0) (h : x / C = q) : x = q * C := by
  rw [← h]; field_simp

/-- **Theorem `theorem:rationality`** (Beeson–Zhang, Theorem 1.2). Let triangle `T` be tiled by a
tile `R` such that `R` is not similar to `T`; `R` is not a right triangle; `R` has incommensurable
angles. Then `R` must have commensurable sides. -/
theorem rationality (D : CongruentDissection N) (hns : Erdos634.Draft.LaczFormal.RG.NotSim D)
    (hright : ∀ k, D.model.angleAt k ≠ Real.pi / 2) (hirr : ∃ k, IrrPi (D.model.angleAt k)) :
    ∀ i j : Fin 3, ∃ q : ℚ, D.model.oppLen i = q * D.model.oppLen j := by
  have hns' : ¬ SimilarTM D := by
    rintro ⟨μ, τ, hτ⟩
    exact hns ⟨τ, fun j => (hτ j).1⟩
  rcases table_incommensurable D hirr with h | ⟨α, β, ⟨σ, -, -, h2⟩, -⟩ | ⟨hE, α, hα, σ, h0, h1, h2⟩ |
      ⟨α, hα, ⟨τ, t0, t1, t2⟩, htgt⟩ | ⟨α, β, -, hrel, ⟨σ, h0, h1, h2⟩, -⟩ |
      ⟨α, hα, ⟨σ, h0, h1, h2⟩, -⟩
  · exact absurd h hns'
  · exact absurd h2 (hright _)
  · -- `γ = π/3`, `T` equilateral: Laczkovich 2012, Theorem 3.3.
    have hT : ThreeAlpha.TileSides D α (2 * Real.pi / 3 - α) (Real.pi / 3) (D.model.oppLen (σ 0))
        (D.model.oppLen (σ 1)) (D.model.oppLen (σ 2)) := ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩
    obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ea, eb⟩ := Equilateral.sixty_rational D hE hT hα
    have hc := (D.model.oppLen_pos (σ 2)).ne'
    refine commSides_of D.model (D.model.oppLen (σ 2)) σ (fin3_all ?_ ?_ ?_)
    · exact ⟨(q₂ : ℚ) / p₂, eq_mul_of_div hc (by rw [ea]; push_cast; rfl)⟩
    · exact ⟨(q₁ : ℚ) / p₁, eq_mul_of_div hc (by rw [eb]; push_cast; rfl)⟩
    · exact ⟨1, by simp⟩
  · -- `γ = 2α`, `T = (α, α, π - 2α)`: the isosceles paper's `theorem:rationaltile`.
    obtain ⟨σ, s0, s1, s2⟩ := tgt_swap12 htgt
    set D₁ := relabelTarget D σ
    set D₂ := relabelModel D₁ τ
    have e0 : tileα D₂ = α := by rw [← model_angleAt_0, relabel_angleAt]; exact t0
    have e2 : tileγ D₂ = 2 * α := by rw [← model_angleAt_2, relabel_angleAt]; exact t2
    have hA : ∠ (D₂.target.pts 1) (D₂.target.pts 0) (D₂.target.pts 2) = tileα D₂ := by
      rw [e0]; exact (ThreeAlpha.relabel_angleAt D σ 0).trans s0
    have hC : ∠ (D₂.target.pts 1) (D₂.target.pts 2) (D₂.target.pts 0) = tileα D₂ := by
      rw [e0, ← target_angleAt_2]; exact (ThreeAlpha.relabel_angleAt D σ 2).trans s2
    obtain ⟨r, s, hr, hs⟩ := TriangleTiling.rationaltile D₂ (by rw [e2, e0])
      (by rw [e0]; exact hα) hA hC
    -- the sides of `D₂.model` are those of `D.model`, relabelled by `τ`
    have hl : ∀ k, D₂.model.oppLen k = D.model.oppLen (τ k) := fun k =>
      (Row2.angleAt_comp D.model D₂.model τ (fun _ => rfl) k).2
    refine commSides_of D.model (D.model.oppLen (τ 0)) τ (fin3_all ⟨1, by simp⟩ ?_ ?_)
    · refine ⟨r, ?_⟩
      rw [← hl, ← hl]; exact hr
    · refine ⟨s, ?_⟩
      rw [← hl, ← hl]; exact hs
  · -- `3α + 2β = π`: `TriangleTiling3` `theorem:rationaltile`.
    have hT : ThreeAlpha.TileSides D α β (2 * α + β) (D.model.oppLen (σ 0))
        (D.model.oppLen (σ 1)) (D.model.oppLen (σ 2)) := ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩
    obtain ⟨⟨q, hq⟩, ⟨q', hq'⟩, -⟩ := ThreeAlpha.rationaltile D hrel hT hns'
    have hc := (D.model.oppLen_pos (σ 2)).ne'
    exact commSides_of D.model (D.model.oppLen (σ 2)) σ
      (fin3_all ⟨q, eq_mul_of_div hc hq⟩ ⟨q', eq_mul_of_div hc hq'⟩ ⟨1, by simp⟩)
  · -- `γ = 2π/3`: Beeson–Zhang Theorem 1.1.
    have hdata : D.model.TwoPiThreeData α (D.model.oppLen (σ 0)) (D.model.oppLen (σ 1))
        (D.model.oppLen (σ 2)) := ⟨σ, h0, rfl, h1, rfl, h2, rfl⟩
    obtain ⟨⟨p, q, hp, hq, hpq⟩, ⟨p', q', hp', hq', hpq'⟩⟩ :=
      Erdos634.Draft.LaczFormal.RG.bz_thm11 D hα hdata hns
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hq0' : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'.ne'
    refine commSides_of D.model (D.model.oppLen (σ 0)) σ (fin3_all ⟨1, by simp⟩ ?_ ?_)
    · refine ⟨(p : ℚ) / q, ?_⟩
      push_cast; field_simp; linarith
    · refine ⟨(p' : ℚ) / q', ?_⟩
      push_cast; field_simp; linarith

end TriangleTiling.Prime
