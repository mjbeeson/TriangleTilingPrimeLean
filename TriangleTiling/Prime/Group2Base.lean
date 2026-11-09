/-
Common steps of Sections 4–7 of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of
congruent triangles* (the Group 2 shapes, tile `(α, β, 2π/3)`): the trigonometry of the tile
(`lemma:claude`, `lemma:beta`, `lemma:c120`, for a tile given by `TileSides`), the law of sines and
the area equation for the tiled triangle, and the integrality of `λ` (`lemma:claude3` after scaling
the tile to integer sides).

The tiled triangle `T` is `D.target`; its angles are at its vertices `0, 1, 2`, with opposite sides
`D.target.oppLen 0, 1, 2`.
-/
import TriangleTiling.Prime.TwoPiThree
import TriangleTiling.ThreeAlpha.Areas
import TriangleTiling.Tiling.Scale

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

theorem fin3_add_one_add_one (x : Fin 3) : x + 1 + 1 = x + 2 := by revert x; decide
theorem fin3_add_two_add_one (x : Fin 3) : x + 2 + 1 = x := by revert x; decide
theorem fin3_add_one_add_two (x : Fin 3) : x + 1 + 2 = x := by revert x; decide
theorem fin3_add_two_add_two (x : Fin 3) : x + 2 + 2 = x + 1 := by revert x; decide

/-- The vertices other than `σ 0` are `σ 0 + 1`, `σ 0 + 2`, in one order or the other. -/
theorem perm_cases (σ : Equiv.Perm (Fin 3)) :
    (σ 1 = σ 0 + 1 ∧ σ 2 = σ 0 + 2) ∨ (σ 1 = σ 0 + 2 ∧ σ 2 = σ 0 + 1) := by
  revert σ; decide

/-- A triangle `T` with angles `α, β, γ` at `σ 0, σ 1, σ 2` and opposite sides `a, b, c` is the
triangle `ABC` of the paper, with `A, B, C = T.pts (σ 0), T.pts (σ 1), T.pts (σ 2)`. -/
theorem tri_as_ABC (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    AffineIndependent ℝ ![T.pts (σ 0), T.pts (σ 1), T.pts (σ 2)] ∧
    ∠ (T.pts (σ 1)) (T.pts (σ 0)) (T.pts (σ 2)) = T.angleAt (σ 0) ∧
    ∠ (T.pts (σ 0)) (T.pts (σ 1)) (T.pts (σ 2)) = T.angleAt (σ 1) ∧
    ∠ (T.pts (σ 0)) (T.pts (σ 2)) (T.pts (σ 1)) = T.angleAt (σ 2) ∧
    dist (T.pts (σ 1)) (T.pts (σ 2)) = T.oppLen (σ 0) ∧
    dist (T.pts (σ 2)) (T.pts (σ 0)) = T.oppLen (σ 1) ∧
    dist (T.pts (σ 0)) (T.pts (σ 1)) = T.oppLen (σ 2) := by
  have hind : AffineIndependent ℝ ![T.pts (σ 0), T.pts (σ 1), T.pts (σ 2)] := by
    have : (![T.pts (σ 0), T.pts (σ 1), T.pts (σ 2)] : Fin 3 → Plane) = T.pts ∘ σ := by
      ext i; fin_cases i <;> rfl
    rw [this]; exact T.indep.comp_embedding σ.toEmbedding
  refine ⟨hind, ?_⟩
  simp only [Tri.angleAt, Tri.oppLen, cornerAngle]
  rcases perm_cases σ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [e1, e2, fin3_add_one_add_one, fin3_add_two_add_one, fin3_add_one_add_two,
      fin3_add_two_add_two] <;>
    first | rfl | exact angle_comm _ _ _ | rw [dist_comm]

/-- **The tile `(α, β, 2π/3)`** (`lemma:c120`, `lemma:claude`, `lemma:beta`): positive sides,
`c² = a² + ab + b²`, `α + β = π/3`, `sin α = a√3/(2c)`, `cos α = (a + 2b)/(2c)`,
`sin β = b√3/(2c)`, `cos β = (2a + b)/(2c)`. -/
theorem tile120 (T : Tri) {α β a b c : ℝ} (σ : Equiv.Perm (Fin 3))
    (h0 : T.angleAt (σ 0) = α) (h1 : T.angleAt (σ 1) = β) (h2 : T.angleAt (σ 2) = 2 * π / 3)
    (l0 : T.oppLen (σ 0) = a) (l1 : T.oppLen (σ 1) = b) (l2 : T.oppLen (σ 2) = c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ α + β = π / 3 ∧
    sin α = a * √3 / (2 * c) ∧ cos α = (a + 2 * b) / (2 * c) ∧
    sin β = b * √3 / (2 * c) ∧ cos β = (2 * a + b) / (2 * c) := by
  obtain ⟨hind, e0, e1, e2, d0, d1, d2⟩ := tri_as_ABC T σ
  rw [h0] at e0; rw [h1] at e1; rw [h2] at e2; rw [l0] at d0; rw [l1] at d1; rw [l2] at d2
  obtain ⟨hiff, himp⟩ := c120 hind
  have hc2 := hiff.mp e2
  obtain ⟨-, -, -, -⟩ := himp e2
  obtain ⟨cα, sα, -, -⟩ := claude hind e2
  obtain ⟨sβ, cβ, -, -, -⟩ := beta hind e2
  simp only [e0, e1, d0, d1, d2] at cα sα sβ cβ hc2
  have hsum : T.angleAt (σ 0) + T.angleAt (σ 1) + T.angleAt (σ 2) = π := by
    have := Equiv.sum_comp σ (fun j => T.angleAt j)
    simp only [Fin.sum_univ_three] at this
    rw [this]; exact cornerAngle_sum T
  rw [h0, h1, h2] at hsum
  refine ⟨?_, ?_, ?_, by linarith [hc2], by linarith, sα, cα, sβ, cβ⟩
  · rw [← l0]; exact T.oppLen_pos _
  · rw [← l1]; exact T.oppLen_pos _
  · rw [← l2]; exact T.oppLen_pos _

/-- The product of the sines of the angles of a triangle does not depend on their order. -/
theorem sin_prod_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    sin (T.angleAt 0) * sin (T.angleAt 1) * sin (T.angleAt 2) =
      sin (T.angleAt (σ 0)) * sin (T.angleAt (σ 1)) * sin (T.angleAt (σ 2)) := by
  have := Equiv.prod_comp σ (fun j => sin (T.angleAt j))
  simp only [Fin.prod_univ_three] at this
  linarith

/-- **The area equation**, with the angles of the tile in the order `σ`: the area of `T` is `N`
times that of the tile, written with the law of sines: `N d_R² sin α sin β sin γ =
d_T² sin A sin B sin C`, `d` the circumdiameters. -/
theorem area_sines' {N : ℕ} (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3)) :
    (N : ℝ) * (ThreeAlpha.circumdiam D.model ^ 2 * (sin (D.model.angleAt (σ 0)) *
        sin (D.model.angleAt (σ 1)) * sin (D.model.angleAt (σ 2))))
      = ThreeAlpha.circumdiam D.target ^ 2 * (sin (D.target.angleAt 0) *
        sin (D.target.angleAt 1) * sin (D.target.angleAt 2)) := by
  rw [← sin_prod_perm]; exact ThreeAlpha.area_sines D

/-- **`λ` is an integer** (`lemma:claude3`, after scaling the tile to integer sides). If the tile
has sides `μ a', μ b', μ c'` with `a', b', c'` integers, and the sides of `T` are
`μ λ (X₀, Y₀, Z₀)` with `X₀, Y₀, Z₀` coprime integers, then `λ` is an integer. -/
theorem lambda_int {N : ℕ} (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3)) {μ : ℝ}
    (hμ : 0 < μ) {a' b' c' : ℕ} (l0 : D.model.oppLen (σ 0) = μ * a')
    (l1 : D.model.oppLen (σ 1) = μ * b') (l2 : D.model.oppLen (σ 2) = μ * c')
    {X₀ Y₀ Z₀ : ℕ} (hg : Nat.gcd (Nat.gcd X₀ Y₀) Z₀ = 1) {l : ℝ}
    (hX : D.target.oppLen 0 = μ * (l * X₀)) (hY : D.target.oppLen 1 = μ * (l * Y₀))
    (hZ : D.target.oppLen 2 = μ * (l * Z₀)) :
    ∃ n : ℕ, l = n := by
  set D' := CongruentDissection.scale D μ⁻¹ (inv_ne_zero hμ.ne')
  have hs : ∀ (T : Tri) (k : Fin 3), (Tri.scale T μ⁻¹ (inv_ne_zero hμ.ne')).oppLen k =
      μ⁻¹ * T.oppLen k := by
    intro T k
    show dist (μ⁻¹ • T.pts (k + 1)) (μ⁻¹ • T.pts (k + 2)) = _
    rw [dist_smul_smul, abs_of_pos (inv_pos.mpr hμ)]; rfl
  have hm : ∀ k, D'.model.oppLen k = μ⁻¹ * D.model.oppLen k := hs D.model
  have ht : ∀ k, D'.target.oppLen k = μ⁻¹ * D.target.oppLen k := hs D.target
  refine claude3 D' (fun k => ?_) hg (l := l) ?_ ?_ ?_
  · obtain ⟨j, rfl⟩ := σ.surjective k
    rw [hm]
    fin_cases j
    · exact ⟨a', by rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, l0]; field_simp⟩
    · exact ⟨b', by rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, l1]; field_simp⟩
    · exact ⟨c', by rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, l2]; field_simp⟩
  · rw [ht, hX]; field_simp
  · rw [ht, hY]; field_simp
  · rw [ht, hZ]; field_simp

end TriangleTiling.Prime
