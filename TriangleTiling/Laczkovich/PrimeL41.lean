/-
`theorem:l1995-4.1` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 2): the corollary of Laczkovich 1995, Theorem 4.1, for a non-isosceles `T`.

The paper's proof: Laczkovich's Theorem 4.1 has more cases, and the hypothesis that `T` is not
isosceles removes some of them. Here Laczkovich's theorem is our `Laczkovich.table_incommensurable`
(from Bonfioli's `LemmaCFinal.lemmaC_general` and `LemmaPProof.lemmaP_general`, NOTE/UNAUDITED in
his library), and the rows of its table with two equal angles of `T` are removed.

"`T` is not isosceles" is: the three angles of `T` are pairwise different. "`R` has incommensurable
angles" is: some angle of `R` is not a rational multiple of `π`. The renaming of `α` and `β` is
absorbed by the existential quantifier; `IrrPi α` is part of the conclusion.

Statement checked by Beeson.
-/
import TriangleTiling.Laczkovich.Tables

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)
open TriangleTiling.Laczkovich

variable {N : ℕ} (D : CongruentDissection N)

/-- A non-isosceles `T` has no two equal angles in any listing. -/
theorem not_iso_tgt (hniso : ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j)
    {x z : ℝ} (h : TgtAngles D x x z) : False := by
  obtain ⟨σ, h0, h1, -⟩ := h
  exact hniso (σ 0) (σ 1) (fun e => absurd (σ.injective e) (by decide)) (h0.trans h1.symm)

theorem irr_compl {α : ℝ} (h : IrrPi α) : IrrPi (Real.pi / 3 - α) := by
  rintro ⟨r, hr⟩
  exact h ⟨1 / 3 - r, by push_cast; linarith⟩

/-- **Theorem `theorem:l1995-4.1`** (Corollary of Laczkovich 1995, Theorem 4.1). Let a
non-isosceles triangle `T` be tiled by `R` where `R` has incommensurable angles `(α, β, γ)`.
Then one of the following must hold, after possibly interchanging the names `α` and `β` (and `a`
and `b`).
1. the tiling is a reptiling;
2. (Group 1): `3α + 2β = π` and `T` has angles `(α, 2α, 2β)` or `(2α, β, α + β)`; or
3. (Group 2): `3α + 3β = π` (equivalently, `γ = 2π/3`) and `T` has angles `(α, 2α, 3β)`,
   `(α, 2β, 2α + β)`, `(α, α + β, α + 2β)`, or `(2α, 2β, α + β)`. -/
theorem «l1995-4.1» (hirr : ∃ k, IrrPi (D.model.angleAt k))
    (hniso : ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j) :
    SimilarTM D ∨
    (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (TgtAngles D α (2 * α) (2 * β) ∨ TgtAngles D (2 * α) β (α + β))) ∨
    (∃ α β : ℝ, IrrPi α ∧ 3 * α + 3 * β = Real.pi ∧ TileAngles D α β (2 * Real.pi / 3) ∧
      (TgtAngles D α (2 * α) (3 * β) ∨ TgtAngles D α (2 * β) (2 * α + β) ∨
        TgtAngles D α (α + β) (α + 2 * β) ∨ TgtAngles D (2 * α) (2 * β) (α + β))) := by
  have heq : ¬ Equilateral D := fun h =>
    hniso 0 1 (by decide) ((h 0).trans (h 1).symm)
  rcases table_incommensurable D hirr with h | ⟨α, β, -, h⟩ | ⟨h, -⟩ | ⟨α, -, -, h⟩ |
      ⟨α, β, hα, hrel, hT, h⟩ | ⟨α, hα, hT, h⟩
  · exact Or.inl h
  · exact (not_iso_tgt D hniso h).elim
  · exact (heq h).elim
  · exact (not_iso_tgt D hniso h).elim
  · -- `3α + 2β = π`: Group 1.
    rcases h with h | h | h | h | h
    · exact (not_iso_tgt D hniso h).elim
    · exact (not_iso_tgt D hniso h).elim
    · exact Or.inr (Or.inl ⟨α, β, hα, hrel, hT, Or.inr h⟩)
    · obtain ⟨σ, h0, h1, h2⟩ := h
      refine Or.inr (Or.inl ⟨α, β, hα, hrel, hT, Or.inl ⟨(Equiv.swap (0 : Fin 3) 1).trans σ,
        ?_, ?_, ?_⟩⟩)
      · simpa using h1
      · simpa using h0
      · simp only [Equiv.trans_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h2
    · exact (not_iso_tgt D hniso h).elim
  · -- `γ = 2π/3`: Group 2, with `β = π/3 - α`.
    right; right
    have hrel : 3 * α + 3 * (Real.pi / 3 - α) = Real.pi := by ring
    have hrel' : 3 * (Real.pi / 3 - α) + 3 * α = Real.pi := by ring
    have hT' := TileAngles.swap hT
    have hα' := irr_compl hα
    rcases h with h | h | h | h
    · exact (heq h).elim
    · rcases h with h | h <;> exact (not_iso_tgt D hniso h).elim
    · rcases h with h | h
      · exact ⟨α, _, hα, hrel, hT, Or.inr (Or.inr (Or.inl h))⟩
      · refine ⟨_, α, hα', hrel', hT', Or.inr (Or.inr (Or.inl ?_))⟩
        exact tgtAngles_of_eq D h rfl (by ring) (by ring)
    · rcases h with h | h | h | h | h
      · exact ⟨α, _, hα, hrel, hT, Or.inr (Or.inr (Or.inr h))⟩
      · exact ⟨α, _, hα, hrel, hT, Or.inl h⟩
      · refine ⟨_, α, hα', hrel', hT', Or.inl ?_⟩
        exact tgtAngles_of_eq D h rfl rfl (by ring)
      · exact ⟨α, _, hα, hrel, hT, Or.inr (Or.inl h)⟩
      · refine ⟨_, α, hα', hrel', hT', Or.inr (Or.inl ?_)⟩
        exact tgtAngles_of_eq D h rfl rfl (by ring)

end TriangleTiling.Prime
