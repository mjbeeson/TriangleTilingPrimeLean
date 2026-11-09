/-
Reptilings in M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 2): `theorem:reptile` (Snover–Waiveris–Williams) and
`corollary:reptilenotprime`.

Statements checked by Beeson. `theorem:reptile` is Bonfioli's `reptile_SWW` (UNAUDITED);
only the necessity of the conditions is formalized, not the existence of the tilings ("which is
possible for any triangle `T` and any natural number `M`"). `corollary:reptilenotprime` follows the
paper.

"`T` is reptiled" is `SimilarTM D`: `T` is similar to the tile. "`T` is a right triangle with legs
in ratio `M/K`" is Bonfioli's `RightLegs D M K`, about the tile (similar to `T`).
-/
import Erdos634.Draft.LaczFormalT6

namespace TriangleTiling.Prime

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles RightLegs)

/-- **Theorem `theorem:reptile`.** Suppose `T` can be reptiled by `N` tiles. Then `N` must be one
(or more) of: `N = M²`; `N = M² + K²`, in which case, if `N` is not a square, `T` must be a right
triangle with legs having ratio `M/K`; `N = 3M²`, in which case `T` must be the `(π/2, π/3, π/6)`
right triangle. -/
theorem reptile {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D) :
    IsSquare N ∨ (∃ M K : ℕ, N = M ^ 2 + K ^ 2 ∧ RightLegs D M K) ∨
      ((∃ M : ℕ, N = 3 * M ^ 2) ∧ TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2)) :=
  Erdos634.Draft.LaczFormal.reptile_SWW D hs

/-- **Corollary `corollary:reptilenotprime`.** Suppose `T` can be reptiled by `N` tiles and
`N ∉ {2, 3}` is prime. Then `N ≡ 1 (mod 4)`, and `T` is a right triangle with legs in ratio `M/K`,
where `N = M² + K²`. -/
theorem reptilenotprime {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D) (hN : N.Prime)
    (h2 : N ≠ 2) (h3 : N ≠ 3) :
    N % 4 = 1 ∧ ∃ M K : ℕ, N = M ^ 2 + K ^ 2 ∧ RightLegs D M K := by
  rcases reptile D hs with ⟨r, hr⟩ | ⟨M, K, hMK, hR⟩ | ⟨⟨M, hM⟩, -⟩
  · -- a square is not prime
    exfalso
    rw [hr] at hN
    rcases Nat.prime_mul_iff.mp hN with ⟨hp, h1⟩ | ⟨hp, h1⟩
    · subst h1; exact Nat.not_prime_one hp
    · subst h1; exact Nat.not_prime_one hp
  · -- a sum of two squares, odd, so `≡ 1 (mod 4)`
    refine ⟨?_, M, K, hMK, hR⟩
    have hodd : N % 2 = 1 := Nat.odd_iff.mp (hN.odd_of_ne_two h2)
    rw [hMK] at hodd ⊢
    have hM := Nat.mod_lt M (show 0 < 4 by norm_num)
    have hK := Nat.mod_lt K (show 0 < 4 by norm_num)
    have e : (M ^ 2 + K ^ 2) % 4 = ((M % 4) ^ 2 + (K % 4) ^ 2) % 4 := by
      simp [Nat.add_mod, Nat.pow_mod]
    have e2 : (M ^ 2 + K ^ 2) % 2 = ((M % 4) ^ 2 + (K % 4) ^ 2) % 2 := by
      rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 4 by norm_num), e, Nat.mod_mod_of_dvd _ (by norm_num)]
    rw [e]; rw [e2] at hodd
    interval_cases (M % 4) <;> interval_cases (K % 4) <;> simp_all
  · -- three times a square is prime only for `N = 3`
    exfalso
    rw [hM] at hN
    have hM1 : M ^ 2 = 1 := by
      rcases Nat.prime_mul_iff.mp hN with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h (by norm_num)
    exact h3 (by rw [hM, hM1])

end TriangleTiling.Prime
