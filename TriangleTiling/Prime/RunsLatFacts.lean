/-
Facts about the lattice of a run frame, for Section 11 of Beeson–Roșu: distances between lattice
points, the angles of the lattice triangles `Δ_{i,j}`, `∇_{i,j}` when they are tiles, and angle
sums of distinct tiles.
-/
import TriangleTiling.Prime.RunsTools

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

/-! ### Sums over distinct tiles -/

section Distinct

variable (D)

theorem sum3_le {i j l : Fin N} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (X : Plane) :
    (D.tile i).localAngle X + (D.tile j).localAngle X + (D.tile l).localAngle X ≤
      D.target.localAngle X := by
  have := sum_ge_three D.toDissection hij hil hjl X
  rwa [D.sum_localAngle_eq] at this

theorem sum4_le {i j l o : Fin N} (hij : i ≠ j) (hil : i ≠ l) (hio : i ≠ o) (hjl : j ≠ l)
    (hjo : j ≠ o) (hlo : l ≠ o) (X : Plane) :
    (D.tile i).localAngle X + (D.tile j).localAngle X + (D.tile l).localAngle X +
      (D.tile o).localAngle X ≤ D.target.localAngle X := by
  classical
  have h : ({i, j, l, o} : Finset (Fin N)).sum (fun t => (D.tile t).localAngle X) =
      (D.tile i).localAngle X + (D.tile j).localAngle X + (D.tile l).localAngle X +
        (D.tile o).localAngle X := by
    rw [Finset.sum_insert (by simp [hij, hil, hio]), Finset.sum_insert (by simp [hjl, hjo]),
      Finset.sum_pair hlo]; ring
  rw [← h]
  exact sum_le_target D.toDissection _ X

theorem target_le_two_pi (X : Plane) : D.target.localAngle X ≤ 2 * π :=
  Tri.localAngle_le_two_pi _ _

theorem target_le_pi {X : Plane} (hX : X ∉ interior D.target.carrier) :
    D.target.localAngle X ≤ π := Tri.localAngle_le_pi _ hX

end Distinct

/-- Tiles with different vertex sets are different. -/
theorem tile_ne_of_pt {i j : Fin N} {P : Plane} (hi : P ∈ Set.range (D.tile i).pts)
    (hj : P ∉ Set.range (D.tile j).pts) : i ≠ j := by
  rintro rfl; exact hj hi

/-- Tiles with different angles at a point are different. -/
theorem tile_ne_of_angle {i j : Fin N} {X : Plane}
    (h : (D.tile i).localAngle X ≠ (D.tile j).localAngle X) : i ≠ j := by
  rintro rfl; exact h rfl

/-! ### The lattice of a frame -/

section Lattice

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

theorem norm_comb (p q : ℝ) :
    ‖(p * c) • I + (q * b) • J‖ ^ 2 =
      (p * c) ^ 2 + (q * b) ^ 2 + 2 * (p * c) * (q * b) * inner ℝ I J := by
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hF.nI, hF.nJ]
  simp only [Real.norm_eq_abs, mul_one, RCLike.conj_to_real]
  rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring

/-- `|c I - b J| = a` gives the inner product of `I` and `J`. -/
theorem inner_IJ : 2 * c * b * inner ℝ I J = c ^ 2 + b ^ 2 - a ^ 2 := by
  have h := norm_comb hS hF 1 (-1)
  have e : (1 * c) • I + (-1 * b) • J = c • I - b • J := by simp [sub_eq_add_neg, neg_smul]
  rw [e, hF.nw] at h
  linarith

theorem dist_lat (u v u' v' : ℝ) :
    dist (lat U I J b c u v) (lat U I J b c u' v') ^ 2 =
      ((u - u') * c) ^ 2 + ((v - v') * b) ^ 2 +
        (u - u') * (v - v') * (c ^ 2 + b ^ 2 - a ^ 2) := by
  rw [dist_eq_norm, lat_sub, norm_comb hS hF]
  have := inner_IJ hS hF
  have hb := hS.b_pos; have hc := hS.c_pos
  have : inner ℝ I J = (c ^ 2 + b ^ 2 - a ^ 2) / (2 * c * b) := by
    field_simp; linarith
  rw [this]; field_simp

theorem dist_lat_eq {u v u' v' : ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : ((u - u') * c) ^ 2 + ((v - v') * b) ^ 2 + (u - u') * (v - v') * (c ^ 2 + b ^ 2 - a ^ 2)
      = d ^ 2) : dist (lat U I J b c u v) (lat U I J b c u' v') = d := by
  have h2 := dist_lat hS hF u v u' v'
  rw [h] at h2
  exact (sq_eq_sq₀ dist_nonneg hd).mp h2

theorem dist_I (u v : ℝ) : dist (lat U I J b c u v) (lat U I J b c (u + 1) v) = c :=
  dist_lat_eq hS hF hS.c_pos.le (by ring)

theorem dist_J (u v : ℝ) : dist (lat U I J b c u v) (lat U I J b c u (v + 1)) = b :=
  dist_lat_eq hS hF hS.b_pos.le (by ring)

theorem dist_W (u v : ℝ) : dist (lat U I J b c (u + 1) v) (lat U I J b c u (v + 1)) = a :=
  dist_lat_eq hS hF hS.a_pos.le (by ring)

/-- **`Δ_{u,v}`, when it is a tile, has `α, β, γ` at `x(u,v), x(u+1,v), x(u,v+1)`.** -/
theorem delta_angles {t : Fin N} {u v : ℝ}
    (h : Set.range (D.tile t).pts =
      {lat U I J b c u v, lat U I J b c (u + 1) v, lat U I J b c u (v + 1)}) :
    HasAngle D t (lat U I J b c u v) α ∧ HasAngle D t (lat U I J b c (u + 1) v) β ∧
      HasAngle D t (lat U I J b c u (v + 1)) γ :=
  hS.occurs_angles h (dist_W hS hF u v) (dist_J hS hF u v) (dist_I hS hF u v)

/-- **`∇_{u,v}`, when it is a tile, has `γ, β, α` at `x(u+1,v), x(u,v+1), x(u+1,v+1)`.** -/
theorem nabla_angles {t : Fin N} {u v : ℝ}
    (h : Set.range (D.tile t).pts =
      {lat U I J b c (u + 1) v, lat U I J b c u (v + 1), lat U I J b c (u + 1) (v + 1)}) :
    HasAngle D t (lat U I J b c (u + 1) v) γ ∧ HasAngle D t (lat U I J b c u (v + 1)) β ∧
      HasAngle D t (lat U I J b c (u + 1) (v + 1)) α := by
  have h' : Set.range (D.tile t).pts = {lat U I J b c (u + 1) (v + 1), lat U I J b c u (v + 1),
      lat U I J b c (u + 1) v} := by
    rw [h]; ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  obtain ⟨h1, h2, h3⟩ := hS.occurs_angles h' (by rw [dist_comm]; exact dist_W hS hF u v)
    (by rw [dist_comm]; exact dist_J hS hF (u + 1) v)
    (by rw [dist_comm]; exact dist_I hS hF u (v + 1))
  exact ⟨h3, h2, h1⟩

omit hS in
theorem crdI_x (u v : ℝ) : crdI U I J (lat U I J b c u v) = u * c := crdI_lat hF.hIJ u v
omit hS in
theorem crdJ_x (u v : ℝ) : crdJ U I J (lat U I J b c u v) = v * b := crdJ_lat hF.hIJ u v

theorem x_inj {u v u' v' : ℝ} (h : lat U I J b c u v = lat U I J b c u' v') : u = u' ∧ v = v' :=
  lat_inj hF.hIJ hS.b_pos.ne' hS.c_pos.ne' h

omit hS in
/-- Points of the target with `crdJ = 0` are not interior. -/
theorem not_interior_of_crdJ {y : Plane} (hy : crdJ U I J y = 0) :
    y ∉ interior D.target.carrier := by
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hint
  have hJn : ‖J‖ = 1 := hF.nJ
  have hz : y - (ε / 2) • J ∈ ball y ε := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hJn, mul_one,
      Real.norm_of_nonneg (by positivity)]; linarith
  have := hF.north _ (interior_subset (hball hz))
  have e : crdJ U I J (y - (ε / 2) • J) = crdJ U I J y - ε / 2 := by
    unfold crdJ
    rw [show y - (ε / 2) • J - U = (y - U) - (ε / 2) • J by abel, cross_sub_right,
      cross_smul_right, sub_div, mul_div_assoc, div_self hF.hIJ]
    ring
  rw [e, hy] at this
  linarith

end Lattice

end TriangleTiling.Prime
