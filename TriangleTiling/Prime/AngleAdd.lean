/-
Angles in the plane, for Section 12 of Beeson–Roșu: the sine of the angle between two vectors is
`|cross| / (‖u‖ ‖v‖)`, and angles add up inside a cone: for `w` in the closed cone of `u` and `v`,
`∠(u, v) = ∠(u, w) + ∠(w, v)`.
-/
import TriangleTiling.Prime.IsoBetaNob

namespace TriangleTiling.Prime

open Erdos634.Geometry Real
open scoped RealInnerProductSpace

theorem lagrange (u v : Plane) : ⟪u, v⟫ ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_coords, norm_sq_coords, norm_sq_coords]; simp only [cross]; ring

theorem sin_angle_eq {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.sin (InnerProductGeometry.angle u v) = |cross u v| / (‖u‖ * ‖v‖) := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hs := InnerProductGeometry.sin_angle_nonneg u v
  have hc := InnerProductGeometry.cos_angle u v
  have h1 := Real.sin_sq_add_cos_sq (InnerProductGeometry.angle u v)
  have hl := lagrange u v
  have h2 : Real.sin (InnerProductGeometry.angle u v) ^ 2 = (|cross u v| / (‖u‖ * ‖v‖)) ^ 2 := by
    rw [div_pow, sq_abs, show Real.sin (InnerProductGeometry.angle u v) ^ 2 =
      1 - Real.cos (InnerProductGeometry.angle u v) ^ 2 by linarith, hc, div_pow,
      eq_div_iff (by positivity), sub_mul, div_mul_cancel₀ _ (by positivity)]
    rw [mul_pow]; linarith
  exact (sq_eq_sq₀ hs (by positivity)).mp h2

/-- **Angles add up inside a cone.** -/
theorem angle_add_cone {u v w : Plane} (hne : cross u v ≠ 0) (hw0 : w ≠ 0)
    (hw : 0 ≤ cross u w * cross u v ∧ 0 ≤ cross w v * cross u v) :
    InnerProductGeometry.angle u v =
      InnerProductGeometry.angle u w + InnerProductGeometry.angle w v := by
  have hu : u ≠ 0 := ne_zero_left_of_cross hne
  have hv : v ≠ 0 := ne_zero_right_of_cross hne
  have nu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have nv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have nw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set θ1 := InnerProductGeometry.angle u w
  set θ2 := InnerProductGeometry.angle w v
  have c1 := InnerProductGeometry.cos_angle u w
  have c2 := InnerProductGeometry.cos_angle w v
  have s1 := sin_angle_eq hu hw0
  have s2 := sin_angle_eq hw0 hv
  -- the signs of the crosses agree with `cross u v`
  have habs : |cross u w| * |cross w v| = cross u w * cross w v := by
    rw [← abs_mul]; apply abs_of_nonneg
    have := mul_nonneg hw.1 hw.2
    have hp : 0 < cross u v * cross u v := mul_self_pos.mpr hne
    nlinarith
  have hw2 : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := norm_sq_coords w
  have id1 : ⟪u, w⟫ * ⟪w, v⟫ - cross u w * cross w v = ‖w‖ ^ 2 * ⟪u, v⟫ := by
    rw [hw2]; simp only [inner_coords, cross]; ring
  have id2 : cross u w * ⟪w, v⟫ + ⟪u, w⟫ * cross w v = ‖w‖ ^ 2 * cross u v := by
    rw [hw2]; simp only [inner_coords, cross]; ring
  have hcos : Real.cos (θ1 + θ2) = ⟪u, v⟫ / (‖u‖ * ‖v‖) := by
    rw [Real.cos_add, c1, c2, s1, s2]
    have e : |cross u w| / (‖u‖ * ‖w‖) * (|cross w v| / (‖w‖ * ‖v‖)) =
        cross u w * cross w v / (‖u‖ * ‖w‖ * (‖w‖ * ‖v‖)) := by rw [div_mul_div_comm, habs]
    rw [e, div_mul_div_comm, ← sub_div, id1]
    field_simp
  have hsin_pos : 0 < Real.sin (θ1 + θ2) := by
    rw [Real.sin_add, c1, c2, s1, s2]
    -- `= |cross u v| / (‖u‖ ‖v‖)`
    have hsg : 0 ≤ cross u w * cross u v ∧ 0 ≤ cross w v * cross u v := hw
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have h1 : cross u w ≤ 0 := by nlinarith
      have h2 : cross w v ≤ 0 := by nlinarith
      rw [abs_of_nonpos h1, abs_of_nonpos h2]
      have : |cross u w| = -cross u w := abs_of_nonpos h1
      have e : -cross u w / (‖u‖ * ‖w‖) * (⟪w, v⟫ / (‖w‖ * ‖v‖)) +
          ⟪u, w⟫ / (‖u‖ * ‖w‖) * (-cross w v / (‖w‖ * ‖v‖)) =
          -(‖w‖ ^ 2 * cross u v) / (‖u‖ * ‖w‖ * (‖w‖ * ‖v‖)) := by
        rw [← id2]; field_simp; ring
      rw [e]; exact div_pos (by nlinarith [mul_pos (pow_pos nw 2) (neg_pos.mpr hneg)]) (by positivity)
    · have h1 : 0 ≤ cross u w := by nlinarith
      have h2 : 0 ≤ cross w v := by nlinarith
      rw [abs_of_nonneg h1, abs_of_nonneg h2]
      have e : cross u w / (‖u‖ * ‖w‖) * (⟪w, v⟫ / (‖w‖ * ‖v‖)) +
          ⟪u, w⟫ / (‖u‖ * ‖w‖) * (cross w v / (‖w‖ * ‖v‖)) =
          (‖w‖ ^ 2 * cross u v) / (‖u‖ * ‖w‖ * (‖w‖ * ‖v‖)) := by
        rw [← id2]; field_simp
      rw [e]; positivity
  have h0 : 0 ≤ θ1 + θ2 := add_nonneg (InnerProductGeometry.angle_nonneg _ _)
    (InnerProductGeometry.angle_nonneg _ _)
  have hπ : θ1 + θ2 ≤ π := by
    by_contra h; push Not at h
    have h2π : θ1 + θ2 ≤ 2 * π := by
      have := InnerProductGeometry.angle_le_pi u w
      have := InnerProductGeometry.angle_le_pi w v
      linarith
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := θ1 + θ2 - 2 * π) (by linarith)
      (by linarith)
    rw [Real.sin_sub_two_pi] at this
    linarith
  rw [InnerProductGeometry.angle, ← hcos, Real.arccos_cos h0 hπ]

end TriangleTiling.Prime
