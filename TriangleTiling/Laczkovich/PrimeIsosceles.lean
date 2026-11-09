/-
`theorem:isosceles` of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles* (Section 2): Theorem 3.1 of Beeson's *Tilings of an isosceles triangle*, assembled from
Laczkovich's results. It is the isosceles paper's `theorem:laczkovich-isosceles`
(`Laczkovich.laczkovich_isosceles`), whose table is the same as Table `table:isosceles`.

Statement checked by Beeson.
-/
import TriangleTiling.Laczkovich.Isosceles

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)

/-- **Theorem `theorem:isosceles`** (Beeson, *Tilings of an isosceles triangle*, Theorem 3.1). Let
`T` be an isosceles, non-equilateral triangle that is `N`-tiled by a tile with angles `(α, β, γ)`.
Then the possible shapes of `T` and the tile are given by Table `table:isosceles`: with `θ` the base
angle of `T`,
1. `T` is similar to the tile;
2. `T = (β, β, 2α)` and `γ = π/2`: the tile is `(θ, π/2 - θ, π/2)`;
3. `T = (α, α, π - 2α)` and `γ = 2α`: the tile is `(θ, π - 3θ, 2θ)`;
4. `T = (α, α, π - 2α)` and `γ = 2π/3`: the tile is `(θ, π/3 - θ, 2π/3)`;
5–7. `3α + 2β = π`, and `T` is `(α, α, α + 2β)`, `(β, β, 3α)` or `(α + β, α + β, α)`: `θ` is `α`,
`β` or `α + β`.
If the angles of the tile are commensurable, then one of the first two lines applies. Otherwise
`α` is not a rational multiple of `π` (here, in lines 3–7).

`T` has its base angles `θ` at its vertices `0` and `2`; non-equilateral is `θ ≠ π/3`. -/
theorem isosceles {N : ℕ} (D : CongruentDissection N) {θ : ℝ}
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ)
    (hne : θ ≠ Real.pi / 3) :
    SimilarTM D ∨ TileAngles D θ (Real.pi / 2 - θ) (Real.pi / 2) ∨
    (IrrPi θ ∧ TileAngles D θ (Real.pi - 3 * θ) (2 * θ)) ∨
    (IrrPi θ ∧ TileAngles D θ (Real.pi / 3 - θ) (2 * Real.pi / 3)) ∨
    (∃ α β, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (θ = α ∨ θ = β ∨ θ = α + β)) :=
  Laczkovich.laczkovich_isosceles D hA hC hne

end TriangleTiling.Prime
