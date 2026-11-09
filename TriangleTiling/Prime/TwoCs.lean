/-
`lemma:twocs` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 10, "Two `c` edges on every side"): the improved version of TriangleTiling3's
`lemma:twocs`, assuming only that no tile has its `γ` angle at a vertex of `ABC`.

Statement checked by Beeson. The proof is TriangleTiling3's (`ThreeAlpha.twocsGen`), which
uses hypothesis (iii) only in this weaker form, as the paper says.
-/
import TriangleTiling.TwoCs.TwoCs

namespace TriangleTiling.Prime

open Erdos634.Geometry

open Classical in
/-- **Lemma `lemma:twocs`** (Two `c` edges). Suppose triangle `ABC` is `N`-tiled by a tile with
angles `(α, β, γ)` (and sides `(a, b, c)` opposite them). Suppose (i) `γ > π/2`, (ii) `α/β` is not
rational, (iii) no tile has its `γ` angle at a vertex of triangle `ABC`, (iv) either neither of
`a, b` is an integer multiple of the other, or neither of the vertices `A, C` has two tiles with
equal angles there (two `α` angles or two `β` angles), and (v) the side `AC` is not a single tile
edge. Then there are at least two `c` edges of tiles on side `AC`. -/
theorem twocs {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hγ : Real.pi / 2 < γ)
    (hirr : ¬ ∃ q : ℚ, α / β = q)
    (hnoγ : ∀ (k : Fin 3) (i : Fin N) (l : Fin 3),
      (D.tile i).pts l = D.target.pts k → (D.tile i).angleAt l ≠ γ)
    (hiv : ((¬ ∃ n : ℕ, a = n * b) ∧ (¬ ∃ n : ℕ, b = n * a)) ∨
      (ThreeAlpha.anglesAt D 0 α ≤ 1 ∧ ThreeAlpha.anglesAt D 0 β ≤ 1 ∧
        ThreeAlpha.anglesAt D 2 α ≤ 1 ∧ ThreeAlpha.anglesAt D 2 β ≤ 1))
    (hv : ¬ ∃ e : Fin N × Fin 3,
      (D.tile e.1).edge e.2 = segment ℝ (D.target.pts 0) (D.target.pts 2)) :
    ∃ i j : Fin N, i ≠ j ∧
      (∃ m : Fin 3, (D.tile i).edge m ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) ∧
        dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) = c) ∧
      (∃ m : Fin 3, (D.tile j).edge m ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) ∧
        dist ((D.tile j).pts m) ((D.tile j).pts (m + 1)) = c) := by
  obtain ⟨hα, hβ, hγ0, hsum⟩ := ThreeAlpha.tileSides_angles D hT
  refine ThreeAlpha.twocsGen D hT hγ hirr (fun k i h => ?_) hiv
    (fun e he => absurd ⟨e, he⟩ hv)
  -- The local angle of tile `i` at the vertex `k` is one of its angles, or `0`, `π`, `2π`.
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
    ⟨l, hl, he⟩ | he | he | he
  · exact hnoγ k i l hl.symm (by rw [← h, he]; rfl)
  · rw [he] at h; linarith [Real.pi_pos]
  · rw [he] at h; linarith
  · rw [he] at h; linarith

end TriangleTiling.Prime
