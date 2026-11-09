/-
`theorem:l1995-5.3` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 2), from Laczkovich 1995, Theorem 5.3.

Statement checked by Beeson. The proof is the paper's: Laczkovich's Theorem 5.3 (Bonfioli's
`thm53_c_classify`, UNAUDITED) says that a non-equilateral `T` with commensurable angles is tiled
only by a tile similar to `T`, or (if `T` is isosceles) by a right tile `(α, π/2 - α, π/2)` with `α`
the base angle of `T`; for the isosceles right triangle that tile is similar to `T` as well.

"The tiling is a reptiling" is `SimilarTM D`.
-/
import TriangleTiling.Prime.Group2Base
import TriangleTiling.Laczkovich.PrimeGroup2
import Erdos634.Draft.LaczFormal9i

namespace TriangleTiling.Prime

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Real
open Erdos634.Draft.LaczFormal (TileAngles CommAngles)

/-- A tile with the angles of `T` (in some order) is similar to `T`. -/
theorem similar_of_angles {N : ℕ} (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    (h : ∀ k, D.model.angleAt (σ k) = D.target.angleAt k) : SimilarTM D := by
  have hdm := ThreeAlpha.circumdiam_pos D.model
  refine ⟨ThreeAlpha.circumdiam D.target / ThreeAlpha.circumdiam D.model, σ, fun k => ⟨(h k).symm, ?_⟩⟩
  rw [ThreeAlpha.lawsin D.target k, ThreeAlpha.lawsin D.model (σ k), h k]
  field_simp

theorem fin3_rot (k : Fin 3) : k + (2 - k) = 2 ∧ k + 1 + (2 - k) = 0 ∧ k + 2 + (2 - k) = 1 := by
  revert k; decide

theorem fin3_cases (k j : Fin 3) : j = k ∨ j = k + 1 ∨ j = k + 2 := by revert k j; decide

/-- **Theorem `theorem:l1995-5.3`.** Suppose `T` has commensurable angles and is tiled by `R`. If
`T` is not an isosceles (or equilateral) triangle, or is an isosceles right triangle, then the tiling
is a reptiling. -/
theorem «l1995-5.3» {N : ℕ} (D : CongruentDissection N) (hcomm : CommAngles D.target)
    (hT : (∀ j₁ j₂ : Fin 3, j₁ ≠ j₂ → D.target.angleAt j₁ ≠ D.target.angleAt j₂) ∨
      ∃ k : Fin 3, D.target.angleAt k = π / 2 ∧ D.target.angleAt (k + 1) = D.target.angleAt (k + 2)) :
    SimilarTM D := by
  have hπ := Real.pi_pos
  have hsum := cornerAngle_sum D.target
  have hpos := fun j => Erdos634.MarchFlank.cornerAngle_pos D.target j
  -- `T` is not equilateral
  have hne : ¬ Equilateral D := by
    intro hE
    rcases hT with h | ⟨k, hk, -⟩
    · exact h 0 1 (by decide) (by rw [hE 0, hE 1])
    · rw [hE k] at hk; linarith
  rcases Erdos634.Laczkovich9.thm53_c_classify D hne hcomm with ⟨σ, hσ⟩ |
      ⟨α, j₁, j₂, hj, h1, h2, σ, m0, m1, m2⟩
  · exact similar_of_angles D σ hσ
  · rcases hT with h | ⟨k, hk, hk12⟩
    · exact absurd (h1.trans h2.symm) (h j₁ j₂ hj)
    · -- the two equal angles are the base angles, so `α = π/4`, and the tile is `(π/4, π/4, π/2)`
      have hsumk : D.target.angleAt k + D.target.angleAt (k + 1) + D.target.angleAt (k + 2) = π := by
        have := Equiv.sum_comp (Equiv.addRight k) (fun j => D.target.angleAt j)
        simp only [Fin.sum_univ_three, Equiv.coe_addRight] at this
        unfold Tri.angleAt at this ⊢
        have e : D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = π := hsum
        fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
          Fin.reduceAdd, zero_add] at this ⊢ <;> unfold Tri.angleAt at e <;> linarith
      have hbase : D.target.angleAt (k + 1) = π / 4 := by linarith
      have hb2 : D.target.angleAt (k + 2) = π / 4 := by rw [← hk12]; exact hbase
      have key : ∀ j, j ≠ k → D.target.angleAt j = π / 4 := by
        intro j hjk
        rcases fin3_cases k j with e | e | e
        · exact absurd e hjk
        · rw [e]; exact hbase
        · rw [e]; exact hb2
      have hα : α = π / 4 := by
        by_cases hk1 : j₁ = k
        · rw [← h2]; exact key j₂ (fun e => hj (hk1.trans e.symm))
        · rw [← h1]; exact key j₁ hk1
      refine similar_of_angles D (Equiv.trans (Equiv.addRight (2 - k)) σ) (fun j => ?_)
      obtain ⟨r0, r1, r2⟩ := fin3_rot k
      simp only [Equiv.trans_apply, Equiv.coe_addRight]
      rcases fin3_cases k j with rfl | rfl | rfl
      · rw [r0, m2, hk]
      · rw [r1, m0, hα, hbase]
      · rw [r2, m1, hα, ← hk12, hbase]; ring

end TriangleTiling.Prime
