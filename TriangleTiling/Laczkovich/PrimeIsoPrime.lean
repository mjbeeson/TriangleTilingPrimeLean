/-
`cor:isoprime` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 2): an isosceles, non-equilateral triangle `N`-tiled with `N > 3` prime has
the shape `(β, β, 3α)` with `3α + 2β = π` and `α` not a rational multiple
of `π`.

The proof follows the paper: `theorem:isosceles` gives the seven lines of Table
`table:isosceles`, and the other six are excluded by
* line 1 (`T` similar to the tile): `theorem:reptile`, as printed (`isoreptile`);
* line 2 (`γ = π/2`): Corollary 7.9 of the isosceles paper, `TriangleTiling.notprime`;
* line 3 (`γ = 2α`): Theorem 11.7 of the isosceles paper, `TriangleTiling.notsquarefree`;
* line 4 (`γ = 2π/3`): Bonfioli's Theorem 42, `Erdos634.Draft.ThmIsoFull.thmIsoAll`
  (as in his paper, without `N ≡ 3 (mod 4)`);
* lines 5 and 7: `TriangleTiling3` Theorems 26 and 22, `ThreeAlpha.notprime5` and
  `ThreeAlpha.notprime3`.

Statement checked by Beeson.
-/
import TriangleTiling.Laczkovich.PrimeIsosceles
import TriangleTiling.Laczkovich.PrimeReptile
import TriangleTiling.Laczkovich.Extended
import TriangleTiling.Laczkovich.ThreeAlphaIsoAlpha
import TriangleTiling.Laczkovich.Bonfioli.ThmIsoFull
import TriangleTiling.Isosceles.Scaling

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.Laczkovich

variable {N : ℕ}

/-- The listing `(x, y, z)` of the angles of `T` can be reordered as `(x, z, y)`. -/
theorem tgt_swap12 {D : CongruentDissection N} {x y z : ℝ} (h : TgtAngles D x y z) :
    TgtAngles D x z y := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (1 : Fin 3) 2).trans σ, ?_, ?_, ?_⟩
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h0
  · simpa using h2
  · simpa using h1

/-- The proof of `cor:isoprime` for a tiling that is not a reptiling, for any prime `N > 3`
(lines 2–7 of Table `table:isosceles`; line 4 uses Bonfioli's Theorem 42 in the form `thmIsoAll`,
without `N ≡ 3 (mod 4)`). -/
theorem isoprimecore (D : CongruentDissection N) {θ : ℝ}
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ)
    (hne : θ ≠ Real.pi / 3) (hN : N.Prime) (h3 : 3 < N) (hs : ¬ SimilarTM D) :
    ∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      θ = β ∧ TgtAngles D β β (3 * α) := by
  have hiso : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) := hA.trans hC.symm
  rcases isosceles D hA hC hne with h | ⟨σ, h0, h1, h2⟩ | ⟨hirr, σ, h0, h1, h2⟩ |
      ⟨hirr, σ, h0, h1, h2⟩ | ⟨α, β, hirr, hrel, hT, hθ⟩
  · exact absurd h hs
  · -- Line 2: `γ = π/2`; Corollary 7.9 of the isosceles paper.
    exfalso
    have hright : tileγ (relabelModel D σ) = Real.pi / 2 := by
      rw [← model_angleAt_2, relabel_angleAt]; exact h2
    exact (TriangleTiling.notprime (relabelModel D σ) hright hiso (by omega)).1 hN
  · -- Line 3: `γ = 2α`; Theorem 11.7 of the isosceles paper.
    exfalso
    set D' := relabelModel D σ
    have e0 : tileα D' = θ := by rw [← model_angleAt_0, relabel_angleAt]; exact h0
    have e2 : tileγ D' = 2 * θ := by rw [← model_angleAt_2, relabel_angleAt]; exact h2
    refine TriangleTiling.notsquarefree D' (by rw [e2, e0]) (by rw [e0]; exact hirr)
      (by rw [e0]; exact hA) (by rw [e0]; exact hC) ?_
    exact Irreducible.squarefree hN
  · -- Line 4: `γ = 2π/3`; Bonfioli's Theorem 42.
    exfalso
    have hdata : D.model.TwoPiThreeData θ (D.model.oppLen (σ 0)) (D.model.oppLen (σ 1))
        (D.model.oppLen (σ 2)) := ⟨σ, h0, rfl, h1, rfl, h2, rfl⟩
    have hisoTP : IsoTP D θ :=
      Or.inl (tgtAngles_of_eq D (tgt_iso D hA hC) rfl rfl (by ring))
    exact Erdos634.Draft.ThmIsoFull.thmIsoAll N D hN h3 θ _ _ _ hirr hdata hisoTP
  · -- Lines 5–7: `3α + 2β = π`.
    obtain ⟨τ, g0, g1, g2⟩ := hT
    have hT' : ThreeAlpha.TileSides D α β (2 * α + β) (D.model.oppLen (τ 0))
        (D.model.oppLen (τ 1)) (D.model.oppLen (τ 2)) := ⟨τ, g0, g1, g2, rfl, rfl, rfl⟩
    have htgt := tgt_iso D hA hC
    rcases hθ with hθ | hθ | hθ
    · -- Line 5: `TriangleTiling3` Theorem 26.
      exact absurd hN (ThreeAlpha.notprime5 D hrel hT' hs
        (tgtAngles_of_eq D (tgt_swap12 htgt) hθ (by linarith) hθ))
    · -- Line 6.
      exact ⟨α, β, hirr, hrel, ⟨τ, g0, g1, g2⟩, hθ,
        tgtAngles_of_eq D htgt hθ hθ (by linarith)⟩
    · -- Line 7: `TriangleTiling3` Theorem 22.
      exact absurd hN (ThreeAlpha.notprime3 D hrel hT'
        (tgtAngles_of_eq D (tgt_swap12 htgt) hθ (by linarith) hθ))

/-- **Line 1 of `cor:isoprime`.** An isosceles, non-equilateral `T` reptiled by a prime number
`N > 3` of tiles is impossible. As printed: by `theorem:reptile`, `N` is a square (not prime), or
`3M²` with `T` the `(π/6, π/3, π/2)` triangle (not isosceles), or `M² + K²` with `T` a right triangle
whose legs have ratio `M/K`; being isosceles, `M = K` and `N = 2M²`, which is prime only for
`N = 2`. -/
theorem isoreptile (D : CongruentDissection N) {θ : ℝ}
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ)
    (hN : N.Prime) (h3 : 3 < N) (hs : SimilarTM D) : False := by
  obtain ⟨μ, τ, hτ⟩ := id hs
  have hmod : ∀ i, D.model.angleAt i = D.target.angleAt (τ.symm i) := fun i => by
    rw [(hτ (τ.symm i)).1, Equiv.apply_symm_apply]
  have t0 : D.target.angleAt 0 = θ := hA
  have t2 : D.target.angleAt 2 = θ := by rw [target_angleAt_2]; exact hC
  have tsum := D.target.angleAt_sum
  have tpos : ∀ x, 0 < D.target.angleAt x := fun x => Erdos634.MarchFlank.cornerAngle_pos _ x
  have tside : ∀ x : Fin 3, x ≠ 1 → D.target.angleAt x = θ := by
    intro x hx; fin_cases x
    · exact t0
    · exact absurd rfl hx
    · exact t2
  have hsq : ∀ r : ℕ, ¬ (r * r).Prime := fun r hr => by
    rcases Nat.prime_mul_iff.mp hr with ⟨hp, h1⟩ | ⟨hp, h1⟩
    · subst h1; exact Nat.not_prime_one hp
    · subst h1; exact Nat.not_prime_one hp
  rcases reptile D hs with ⟨r, hr⟩ | ⟨M, K, hMK, i, j, k, hij, hik, hjk, hk, hl⟩ | ⟨-, σ, h0, h1, h2⟩
  · exact hsq r (hr ▸ hN)
  · -- the right angle is at the apex of `T`, so the base angles are `π/4`
    have hc : τ.symm k = 1 := by
      by_contra hc
      have := tpos 1
      have e := tside _ hc
      rw [← hmod, hk] at e
      linarith
    have hθ : θ = Real.pi / 4 := by
      have e := hmod k
      rw [hk, hc] at e
      linarith
    have hi : D.model.angleAt i = θ := by
      rw [hmod]; exact tside _ (fun e => hik (τ.symm.injective (e.trans hc.symm)))
    have hj : D.model.angleAt j = θ := by
      rw [hmod]; exact tside _ (fun e => hjk (τ.symm.injective (e.trans hc.symm)))
    have hlen : D.model.oppLen i = D.model.oppLen j := by
      rw [ThreeAlpha.lawsin, ThreeAlpha.lawsin, hi, hj]
    rw [hlen] at hl
    have hKM : (K : ℝ) = M := mul_left_cancel₀ (D.model.oppLen_pos j).ne' hl
    have hKM' : K = M := by exact_mod_cast hKM
    subst hKM'
    rw [show K ^ 2 + K ^ 2 = 2 * (K * K) by ring] at hMK
    rw [hMK] at hN h3
    rcases Nat.prime_mul_iff.mp hN with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h] at h3; omega
    · omega
  · -- the `(π/6, π/3, π/2)` triangle has no two equal angles
    have e : D.model.angleAt (τ 0) = D.model.angleAt (τ 2) := by
      rw [← (hτ 0).1, ← (hτ 2).1, t0, t2]
    have hd : τ 0 ≠ τ 2 := fun h => absurd (τ.injective h) (by decide)
    obtain ⟨a, ha⟩ := σ.surjective (τ 0)
    obtain ⟨b, hb⟩ := σ.surjective (τ 2)
    rw [← ha, ← hb] at e
    have hab : a ≠ b := fun h => hd (by rw [← ha, ← hb, h])
    have hπ := Real.pi_pos
    have hv : ∀ x, D.model.angleAt (σ x) = ![Real.pi / 6, Real.pi / 3, Real.pi / 2] x := by
      intro x; fin_cases x
      · exact h0
      · exact h1
      · exact h2
    rw [hv a, hv b] at e
    fin_cases a <;> fin_cases b
    all_goals first | exact absurd rfl hab | (norm_num at e <;> linarith)

/-- **Corollary `cor:isoprime`.** Let `T` be isosceles but not equilateral, and `N`-tiled by a
tile `R` with angles `(α, β, γ)`, where `N` is prime and `N > 3`. Then `α` is
not a rational multiple of `π`, and `T` and `R` are given by the sixth line of Table
`table:isosceles`; that is, `3α + 2β = π` and `T` has angles `(β, β, 3α)`.

`T` has its base angles `θ` at its vertices `0` and `2`; non-equilateral is `θ ≠ π/3`. The tile's
third angle is `γ = π - α - β = 2α + β`. -/
theorem isoprime (D : CongruentDissection N) {θ : ℝ}
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ)
    (hne : θ ≠ Real.pi / 3) (hN : N.Prime) (h3 : 3 < N) :
    ∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      θ = β ∧ TgtAngles D β β (3 * α) := by
  -- Line 1: a reptiling.
  by_cases hs : SimilarTM D
  · exact (isoreptile D hA hC hN h3 hs).elim
  exact isoprimecore D hA hC hne hN h3 hs

end TriangleTiling.Prime
