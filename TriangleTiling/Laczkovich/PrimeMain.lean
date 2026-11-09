/-
`theorem:prime634` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 14): the prime case of Erdős problem 634.

`prime634` (as revised 2026-11-09): for `N > 3` prime, every `N`-tiling is a reptiling of a right
triangle with legs `e, f`, `N = e² + f²`, so `N ≡ 1 (mod 4)`. The proof follows the paper's case
analysis by the shape of `T` (`notreptile`, for a tiling that is not a reptiling):
* `T` equilateral: `theorem:equilateral` (here reached inside the isosceles case);
* `T` isosceles: `cor:isoprime` gives the shape `(β, β, 3α)`, excluded by `theorem:isoscelesbeta`
  (through its prime case `isobetaprime`);
* `T` not isosceles, commensurable angles: a reptiling by `theorem:l1995-5.3`;
* otherwise `theorem:l1995-4.1`: a reptiling, a Group 1 shape (`TriangleTiling3` `notprime2` for
  `(α, 2α, 2β)`; `theorem:triquadratic` through its prime case `triqprime`, for
  `(2α, β, α + β)`), or a Group 2 shape (`theorem:case2`–`theorem:case5`);
* a reptiling: `corollary:reptilenotprime` (the paper's last step, from `theorem:reptile`).

The case "a reptiling" is treated first, so the other cases may assume `T` is not similar to the
tile (`isoprimecore` is `cor:isoprime` without its line 1).

The converse (`primeexistence`, the right-to-left part of the proof of `corollary:prime634cor`) uses Bonfioli's constructions (`Erdos634.Draft.PrimeWitness2`,
`Erdos634.Draft.Equilateral3`, `Erdos634.Draft.SumTwoSquares`). For `N = 3` Bonfioli's
tiling is the equilateral triangle cut from its centre into three `(π/6, π/6, 2π/3)` tiles. For `N = e² + f²` his tiling is the paper's (the
right triangle with legs `e, f`, cut by the altitude and subdivided quadratically).

`prime634cor` (`corollary:prime634cor`) combines the two: for `N` prime, some triangle can be `N`-tiled
(`Nonempty (CongruentDissection N)`) iff `N = 2`, `N = 3`, or `N ≡ 1 (mod 4)`. The printed proof
gets `N = 3` from the equilateral triangle, as Bonfioli's construction does.

Statement checked by Beeson.
-/
import TriangleTiling.Laczkovich.PrimeIsoPrime
import TriangleTiling.Laczkovich.PrimeL41
import TriangleTiling.Laczkovich.PrimeJOne
import TriangleTiling.Laczkovich.PrimeEquilateral
import TriangleTiling.Laczkovich.PrimeL53
import TriangleTiling.Laczkovich.PrimeGroup2
import Erdos634.Draft.Equilateral3

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles CommAngles commAngles_iff RightLegs)

variable {N : ℕ}

/-- The listing `(x, y, z)` of the angles of `T` can be reordered as `(y, x, z)`. -/
theorem tgt_swap01 {D : CongruentDissection N} {x y z : ℝ} (h : TgtAngles D x y z) :
    TgtAngles D y x z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (0 : Fin 3) 1).trans σ, ?_, ?_, ?_⟩
  · simpa using h1
  · simpa using h0
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h2

theorem tileSides_of_angles {D : CongruentDissection N} {x y z : ℝ} (h : TileAngles D x y z) :
    ∃ a b c : ℝ, ThreeAlpha.TileSides D x y z a b c := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨_, _, _, σ, h0, h1, h2, rfl, rfl, rfl⟩

theorem exists_perm_02 : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 2 = j := by
  decide

theorem commAngles_of_relabel (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    (h : CommAngles (relabelTarget D σ).target) : CommAngles D.target := by
  rw [commAngles_iff] at h ⊢
  intro k
  obtain ⟨q, hq⟩ := h (σ.symm k)
  rw [ThreeAlpha.relabel_angleAt, Equiv.apply_symm_apply] at hq
  exact ⟨q, hq⟩

/-- The relabelled target with the listed angles at its vertices `0, 1, 2`. -/
theorem relabel_of_tgt (D : CongruentDissection N) {x y z : ℝ} (h : TgtAngles D x y z) :
    ∃ σ : Equiv.Perm (Fin 3), (relabelTarget D σ).target.angleAt 0 = x ∧
      (relabelTarget D σ).target.angleAt 1 = y ∧ (relabelTarget D σ).target.angleAt 2 = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨σ, by rw [ThreeAlpha.relabel_angleAt]; exact h0, by rw [ThreeAlpha.relabel_angleAt]; exact h1,
    by rw [ThreeAlpha.relabel_angleAt]; exact h2⟩

/-- **The main step.** For `N > 3` prime, every `N`-tiling is a reptiling. -/
theorem notreptile (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 < N)
    (hs : ¬ SimilarTM D) : False := by
  by_cases hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j
  · -- `T` isosceles (or equilateral).
    obtain ⟨i, j, hij, he⟩ := hiso
    obtain ⟨σ, hσ0, hσ2⟩ := exists_perm_02 i j hij
    set D₁ := relabelTarget D σ
    have hns₁ : ¬ SimilarTM D₁ := fun h => hs (ThreeAlpha.similar_of_relabel D σ h)
    have hA : ∠ (D₁.target.pts 1) (D₁.target.pts 0) (D₁.target.pts 2) = D.target.angleAt i := by
      rw [← target_angleAt_0, ThreeAlpha.relabel_angleAt, hσ0]
    have hC : ∠ (D₁.target.pts 1) (D₁.target.pts 2) (D₁.target.pts 0) = D.target.angleAt i := by
      rw [← target_angleAt_2, ThreeAlpha.relabel_angleAt, hσ2, he]
    by_cases hθ : D.target.angleAt i = Real.pi / 3
    · -- `T` equilateral.
      rw [hθ] at hA hC
      exact equilateral D₁ (equilateral_of_base D₁ hA hC) h3 hN
    obtain ⟨α, β, -, hrel, hTA, -, htgt⟩ := isoprimecore D₁ hA hC hθ hN h3 hns₁
    obtain ⟨a, b, c, hT⟩ := tileSides_of_angles hTA
    exact isobetaprime D₁ hrel hT hns₁ (tgt_swap12 htgt) hN
  push Not at hiso
  -- `T` not isosceles.
  by_cases hc : CommAngles D.target
  · exact hs («l1995-5.3» D hc (Or.inl hiso))
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra h
    push Not at h
    apply hc
    apply (RandT D).1
    rw [commAngles_iff]
    intro k
    exact not_not.mp (h k)
  rcases «l1995-4.1» D hirr hiso with h | ⟨α, β, -, hrel, hTA, h | h⟩ |
      ⟨α, β, -, hrel, hTA, h | h | h | h⟩
  · exact hs h
  · -- Group 1, `(α, 2α, 2β)`: `TriangleTiling3` Theorem 16.
    obtain ⟨a, b, c, hT⟩ := tileSides_of_angles hTA
    exact ThreeAlpha.notprime2 D hrel hT hs (tgt_swap01 h) hN
  · -- Group 1, the triquadratic shape.
    obtain ⟨a, b, c, hT⟩ := tileSides_of_angles hTA
    exact triqprime D hrel hT h hN
  -- Group 2.
  all_goals
    obtain ⟨a, b, c, hT⟩ := tileSides_of_angles hTA
    obtain ⟨σ, e0, e1, e2⟩ := relabel_of_tgt D h
    have hinc : ¬ CommAngles (relabelTarget D σ).target := fun h' =>
      hc (commAngles_of_relabel D σ h')
    have hT₁ : ThreeAlpha.TileSides (relabelTarget D σ) α β (2 * Real.pi / 3) a b c := hT
  · exact (case2 (relabelTarget D σ) hinc hT₁ e0 e1 e2).1 hN
  · exact (case3 (relabelTarget D σ) hinc hT₁ e0 e1 e2).1 hN
  · exact (case4 (relabelTarget D σ) hinc hT₁ e0 e1 e2).1 hN
  · exact (case5 (relabelTarget D σ) hinc hT₁ e0 e1 e2).1 hN

/-- **Theorem `theorem:prime634`.** Let `N` be prime and greater than 3. Suppose triangle `ABC`
can be `N`-tiled. Then
* `N ≡ 1 (mod 4)`;
* `ABC` is similar to the tile;
* both the tile and `ABC` are similar to a right triangle with legs `e` and `f`, where
  `N = e² + f²`.

The third item is Bonfioli's `RightLegs D e f`: the tile (similar to `ABC`) has a right angle and
its legs are in ratio `e : f`. -/
theorem prime634 (D : CongruentDissection N) (hN : N.Prime) (h3 : 3 < N) :
    N % 4 = 1 ∧ SimilarTM D ∧ ∃ e f : ℕ, N = e ^ 2 + f ^ 2 ∧ RightLegs D e f := by
  by_cases hs : SimilarTM D
  · obtain ⟨h1, e, f, hef, hR⟩ := reptilenotprime D hs hN (by omega) (by omega)
    exact ⟨h1, hs, e, f, hef, hR⟩
  · exact (notreptile D hN h3 hs).elim

/-- **The converse** (the right-to-left part of the proof of `corollary:prime634cor`): for
`N = 2`, `N = 3`, and every prime `N ≡ 1 (mod 4)`, some triangle can be `N`-tiled. -/
theorem primeexistence (hN : N.Prime) (h : N = 2 ∨ N = 3 ∨ N % 4 = 1) :
    Nonempty (CongruentDissection N) := by
  rcases h with rfl | rfl | h1
  · exact Erdos634.Draft.PrimeWitness2.exists_prime_dissection.1
  · exact Erdos634.Draft.Equilateral3.exists_dissection_3
  · haveI := Fact.mk hN
    obtain ⟨e, f, hef⟩ := Nat.Prime.sq_add_sq (p := N) (by omega)
    have key : ∀ x : ℕ, ¬ (x ^ 2).Prime := fun x hx => by
      rw [sq] at hx
      rcases Nat.prime_mul_iff.mp hx with ⟨hp, h1⟩ | ⟨hp, h1⟩
      · subst h1; exact Nat.not_prime_one hp
      · subst h1; exact Nat.not_prime_one hp
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; rw [zero_pow two_ne_zero, zero_add] at hef; exact absurd (hef ▸ hN) (key f)
      · exact h0
    have hf : 0 < f := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · subst h0; rw [zero_pow two_ne_zero, add_zero] at hef; exact absurd (hef ▸ hN) (key e)
      · exact h0
    have e2 : e * e + f * f = N := by rw [← hef]; ring
    exact e2 ▸ Erdos634.Draft.SumTwoSquares.sum_two_squares_tiling e f he hf

/-- **Corollary `corollary:prime634cor`.** Let `N` be prime. Then some triangle can be `N`-tiled if
and only if `N = 2`, `N = 3`, or `N ≡ 1 (mod 4)`. -/
theorem prime634cor (hN : N.Prime) :
    Nonempty (CongruentDissection N) ↔ N = 2 ∨ N = 3 ∨ N % 4 = 1 := by
  refine ⟨fun ⟨D⟩ => ?_, primeexistence hN⟩
  by_cases h2 : N = 2
  · exact Or.inl h2
  by_cases h3 : N = 3
  · exact Or.inr (Or.inl h3)
  have := hN.two_le
  exact Or.inr (Or.inr (prime634 D hN (by omega)).1)

end TriangleTiling.Prime
