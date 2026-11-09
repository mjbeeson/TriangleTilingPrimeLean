/-
The lattice of Section 11 of Beeson–Roșu ("Runs of `c` edges"): coordinates along two independent
vectors `I, J`, the lattice points `x(u, v) = U + uc I + vb J`, and its triangles `Δ_{i,j}`,
`∇_{i,j}` and trapezoids `𝒯(s, r)`.
-/
import TriangleTiling.Prime.RunsBasic

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set

/-! ### Coordinates along `I` and `J` -/

theorem cross_comb (p₁ q₁ p₂ q₂ : ℝ) (I J : Plane) :
    cross (p₁ • I + q₁ • J) (p₂ • I + q₂ • J) = (p₁ * q₂ - q₁ * p₂) * cross I J := by
  simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- The `I`-coordinate of `y` in the frame `(U, I, J)`. -/
noncomputable def crdI (U I J y : Plane) : ℝ := cross (y - U) J / cross I J

/-- The `J`-coordinate of `y` in the frame `(U, I, J)`. -/
noncomputable def crdJ (U I J y : Plane) : ℝ := cross I (y - U) / cross I J

section Frame

variable {U I J : Plane} (hIJ : cross I J ≠ 0)
include hIJ

theorem decomp (y : Plane) : y = U + crdI U I J y • I + crdJ U I J y • J := by
  have h : ∀ v : Plane, v = (cross v J / cross I J) • I + (cross I v / cross I J) • J := by
    intro v
    have e : cross I J • v = cross v J • I + cross I v • J := by
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      fin_cases i <;> simp [cross] <;> ring
    have : v = (cross I J)⁻¹ • (cross I J • v) := by rw [smul_smul, inv_mul_cancel₀ hIJ, one_smul]
    conv_lhs => rw [this, e, smul_add, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> field_simp
  have := h (y - U)
  unfold crdI crdJ
  calc y = U + (y - U) := by abel
    _ = _ := by rw [add_assoc, ← this]

theorem crdI_comb (p q : ℝ) : crdI U I J (U + p • I + q • J) = p := by
  unfold crdI
  rw [show U + p • I + q • J - U = p • I + q • J by abel]
  have : cross (p • I + q • J) J = p * cross I J := by
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this]; field_simp

theorem crdJ_comb (p q : ℝ) : crdJ U I J (U + p • I + q • J) = q := by
  unfold crdJ
  rw [show U + p • I + q • J - U = p • I + q • J by abel]
  have : cross I (p • I + q • J) = q * cross I J := by
    simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this]; field_simp

omit hIJ in
theorem crdI_affine (y z : Plane) (s : ℝ) :
    crdI U I J (AffineMap.lineMap y z s) = (1 - s) * crdI U I J y + s * crdI U I J z := by
  unfold crdI
  rw [AffineMap.lineMap_apply_module]
  simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

omit hIJ in
theorem crdJ_affine (y z : Plane) (s : ℝ) :
    crdJ U I J (AffineMap.lineMap y z s) = (1 - s) * crdJ U I J y + s * crdJ U I J z := by
  unfold crdJ
  rw [AffineMap.lineMap_apply_module]
  simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Two points with the same coordinates are equal. -/
theorem eq_of_crd {y z : Plane} (h1 : crdI U I J y = crdI U I J z)
    (h2 : crdJ U I J y = crdJ U I J z) : y = z := by
  rw [decomp hIJ y, decomp hIJ z, h1, h2]

end Frame

/-! ### The lattice -/

/-- The lattice point `x(u, v) = U + uc I + vb J`. -/
noncomputable def lat (U I J : Plane) (b c u v : ℝ) : Plane := U + (u * c) • I + (v * b) • J

section Lattice

variable {U I J : Plane} {b c : ℝ}

theorem crdI_lat (hIJ : cross I J ≠ 0) (u v : ℝ) : crdI U I J (lat U I J b c u v) = u * c :=
  crdI_comb hIJ _ _

theorem crdJ_lat (hIJ : cross I J ≠ 0) (u v : ℝ) : crdJ U I J (lat U I J b c u v) = v * b :=
  crdJ_comb hIJ _ _

theorem lat_sub (u v u' v' : ℝ) :
    lat U I J b c u v - lat U I J b c u' v' = ((u - u') * c) • I + ((v - v') * b) • J := by
  simp only [lat, sub_mul, sub_smul]; abel

theorem lat_add_I (u v t : ℝ) : lat U I J b c u v + (t * c) • I = lat U I J b c (u + t) v := by
  simp only [lat, add_mul, add_smul]; abel

theorem lat_add_J (u v t : ℝ) : lat U I J b c u v + (t * b) • J = lat U I J b c u (v + t) := by
  simp only [lat, add_mul, add_smul]; abel

theorem lat_inj (hIJ : cross I J ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) {u v u' v' : ℝ}
    (h : lat U I J b c u v = lat U I J b c u' v') : u = u' ∧ v = v' := by
  have h1 := congrArg (crdI U I J) h
  have h2 := congrArg (crdJ U I J) h
  rw [crdI_lat hIJ, crdI_lat hIJ] at h1
  rw [crdJ_lat hIJ, crdJ_lat hIJ] at h2
  exact ⟨mul_right_cancel₀ hc h1, mul_right_cancel₀ hb h2⟩

end Lattice

/-! ### Lattice triangles and trapezoids -/

variable {N : ℕ} (D : CongruentDissection N)

/-- `Δ_{i,j} = x(i,j) x(i+1,j) x(i,j+1)` is a tile. -/
def DeltaOcc (x : ℝ → ℝ → Plane) (i j : ℕ) : Prop :=
  Occurs D (x i j) (x (i + 1) j) (x i (j + 1))

/-- `∇_{i,j} = x(i+1,j) x(i,j+1) x(i+1,j+1)` is a tile. -/
def NablaOcc (x : ℝ → ℝ → Plane) (i j : ℕ) : Prop :=
  Occurs D (x (i + 1) j) (x i (j + 1)) (x (i + 1) (j + 1))

/-- `𝒯(s, r)` occurs: `Δ_{i,j}` for `j < r`, `i + j ≤ s - 1`, and `∇_{i,j}` for `j < r`,
`i + j ≤ s - 2`, are tiles. (The bounds are written `i + j + 1 ≤ s` and `i + j + 2 ≤ s`.) -/
def TOccurs (x : ℝ → ℝ → Plane) (s r : ℕ) : Prop :=
  (∀ i j : ℕ, j < r → i + j + 1 ≤ s → DeltaOcc D x i j) ∧
    (∀ i j : ℕ, j < r → i + j + 2 ≤ s → NablaOcc D x i j)

end TriangleTiling.Prime
