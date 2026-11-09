/-
`lemma:longrun`, Case 3: the angle between the `b` edges of `T_i` and `T_{i+1}` at `X_i` is
`π - 2α = α + 2β`.
-/
import TriangleTiling.Prime.RunsLongD

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric
open scoped RealInnerProductSpace

/-- **The angle between two unit vectors at angle `α` from `I` and from `-I`, on the same side
of `I`**, is `π - 2α`. -/
theorem angle_two_sides {I Jb Jf : Plane} {α : ℝ} (hI : ‖I‖ = 1) (hJb : ‖Jb‖ = 1) (hJf : ‖Jf‖ = 1)
    (hf : InnerProductGeometry.angle I Jf = α) (hb : InnerProductGeometry.angle (-I) Jb = α)
    (hside : 0 < cross I Jb * cross I Jf) (hα0 : 0 < α) (hα : α < π / 2) :
    InnerProductGeometry.angle Jb Jf = π - 2 * α ∧ cross Jb Jf ≠ 0 := by
  have cf : ⟪I, Jf⟫ = Real.cos α := by
    rw [← hf, InnerProductGeometry.cos_angle, hI, hJf]; simp
  have cb : ⟪I, Jb⟫ = -Real.cos α := by
    have : ⟪-I, Jb⟫ = Real.cos α := by
      rw [← hb, InnerProductGeometry.cos_angle, norm_neg, hI, hJb]; simp
    rw [inner_neg_left] at this; linarith
  have nI := norm_sq_coords I; have nb := norm_sq_coords Jb; have nf := norm_sq_coords Jf
  rw [hI] at nI; rw [hJb] at nb; rw [hJf] at nf
  rw [inner_coords] at cf cb
  set x := cross I Jb
  set y := cross I Jf
  have hx : x = I 0 * Jb 1 - I 1 * Jb 0 := rfl
  have hy : y = I 0 * Jf 1 - I 1 * Jf 0 := rfl
  clear_value x y
  -- Lagrange: `⟪I, J⟫² + cross(I, J)² = 1`.
  have lx : Real.cos α ^ 2 + x ^ 2 = 1 := by
    have : (-Real.cos α) ^ 2 + x ^ 2 = 1 := by rw [← cb, hx]; nlinarith
    linarith [sq_nonneg (Real.cos α)]
  have ly : Real.cos α ^ 2 + y ^ 2 = 1 := by rw [← cf, hy]; nlinarith
  have hs := Real.sin_sq_add_cos_sq α
  have hxy : x * y = Real.sin α ^ 2 := by
    have hx2 : x ^ 2 = Real.sin α ^ 2 := by linarith
    have hy2 : y ^ 2 = Real.sin α ^ 2 := by linarith
    have h1 : (x * y) ^ 2 = (Real.sin α ^ 2) ^ 2 := by rw [mul_pow, hx2, hy2]; ring
    exact (sq_eq_sq₀ hside.le (sq_nonneg _)).mp h1
  have hinner : ⟪Jb, Jf⟫ = Real.sin α ^ 2 - Real.cos α ^ 2 := by
    rw [inner_coords, ← hxy]
    have e : Jb 0 * Jf 0 + Jb 1 * Jf 1 =
        (I 0 * Jb 0 + I 1 * Jb 1) * (I 0 * Jf 0 + I 1 * Jf 1) + x * y := by
      rw [hx, hy]; linear_combination (Jb 0 * Jf 0 + Jb 1 * Jf 1) * nI
    rw [e, cb, cf]; ring
  have hcos : Real.cos α > 0 := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα⟩
  refine ⟨?_, ?_⟩
  · rw [InnerProductGeometry.angle, hinner, hJb, hJf, mul_one, div_one]
    have : Real.sin α ^ 2 - Real.cos α ^ 2 = Real.cos (π - 2 * α) := by
      rw [Real.cos_pi_sub, Real.cos_two_mul]; nlinarith [hs]
    rw [this, Real.arccos_cos (by linarith) (by linarith)]
  · intro h0
    have e : cross Jb Jf = (I 0 * Jb 0 + I 1 * Jb 1) * y - x * (I 0 * Jf 0 + I 1 * Jf 1) := by
      simp only [cross]; rw [hx, hy]; linear_combination (Jb 0 * Jf 1 - Jb 1 * Jf 0) * nI
    rw [e, cb, cf] at h0
    have : Real.cos α * (x + y) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · have hyx : y = -x := by linarith
      have : x * y = -(x ^ 2) := by rw [hyx]; ring
      have h2 := sq_nonneg x
      linarith

end TriangleTiling.Prime
