/-
Sectors at a point, for Section 11 of Beeson–Roșu, *Tiling a triangle into a prime number of
congruent triangles* ("Runs of `c` edges").

The paper says, many times, "the sector between these two rays has angle `θ`, so it is filled by
one tile with its `θ` angle there". This file proves the geometric half of that sentence. Let `X`
be a point and `u, v` independent vectors whose rays from `X` lie (near `X`) in no tile's interior
(for instance, along tile edges), and let the closed sector between them lie, near `X`, in the
tiled triangle. Call a tile *in the sector* if its interior meets the open sector arbitrarily close
to `X`. Then
* each tile in the sector lies, near `X`, inside the closed sector (it cannot cross the rays);
* the tiles in the sector cover the closed sector near `X`;
* their angles at `X` add up to the angle between `u` and `v`.
The last is the area argument of `Tiling/HalfPlaneAngle.half_angle_sum`: near `X` the sector has
area `θ r² / 2` (Bonfioli's vertex-sector area, applied to the triangle `X, X + u, X + v`), and a
tile meets a small disk about `X` in area `(local angle / 2) r²`.

`ray_edge`: a tile with a vertex at `X`, in the sector, containing points of the ray along `u`
near `X`, has an edge along that ray.
-/
import TriangleTiling.Tiling.Straight
import TriangleTiling.Tiling.Restrict
import Erdos634.VertexSector

namespace TriangleTiling.Prime

open Erdos634.Geometry MeasureTheory Set Metric

/-! ### Sectors -/

/-- The closed sector at `X` between the rays along `u` and `v` (Bonfioli's sign-free
`vertexCone`, translated to `X`). -/
def sectorC (X u v : Plane) : Set Plane := {y | y - X ∈ vertexCone u v}

/-- The open sector at `X` between the rays along `u` and `v`. -/
def sectorO (X u v : Plane) : Set Plane :=
  {y | 0 < cross u (y - X) * cross u v ∧ 0 < cross (y - X) v * cross u v}

theorem mem_sectorC {X u v y : Plane} :
    y ∈ sectorC X u v ↔ 0 ≤ cross u (y - X) * cross u v ∧ 0 ≤ cross (y - X) v * cross u v :=
  Iff.rfl

theorem sectorO_subset_sectorC (X u v : Plane) : sectorO X u v ⊆ sectorC X u v :=
  fun _ hy => ⟨hy.1.le, hy.2.le⟩

theorem cross_sub_left' (a b v : Plane) : cross (a - b) v = cross a v - cross b v := by
  simp only [cross, PiLp.sub_apply]; ring

theorem cross_add_left' (a b v : Plane) : cross (a + b) v = cross a v + cross b v := by
  simp only [cross, PiLp.add_apply]; ring

theorem continuous_cross_left (u : Plane) : Continuous fun y : Plane => cross u y :=
  (crossL u).continuous_of_finiteDimensional

theorem continuous_cross_right (v : Plane) : Continuous fun y : Plane => cross y v := by
  have : (fun y : Plane => cross y v) = fun y => -(crossL v y) := by
    funext y; rw [crossL_apply, cross_swap]
  rw [this]; exact ((crossL v).continuous_of_finiteDimensional).neg

theorem isOpen_sectorO (X u v : Plane) : IsOpen (sectorO X u v) := by
  have h1 : Continuous fun y : Plane => cross u (y - X) * cross u v :=
    ((continuous_cross_left u).comp (continuous_id.sub continuous_const)).mul continuous_const
  have h2 : Continuous fun y : Plane => cross (y - X) v * cross u v :=
    ((continuous_cross_right v).comp (continuous_id.sub continuous_const)).mul continuous_const
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2)

theorem isClosed_sectorC (X u v : Plane) : IsClosed (sectorC X u v) := by
  have h1 : Continuous fun y : Plane => cross u (y - X) * cross u v :=
    ((continuous_cross_left u).comp (continuous_id.sub continuous_const)).mul continuous_const
  have h2 : Continuous fun y : Plane => cross (y - X) v * cross u v :=
    ((continuous_cross_right v).comp (continuous_id.sub continuous_const)).mul continuous_const
  exact (isClosed_le continuous_const h1).inter (isClosed_le continuous_const h2)

theorem ne_zero_left_of_cross {u v : Plane} (h : cross u v ≠ 0) : u ≠ 0 := by
  rintro rfl; simp [cross] at h

theorem ne_zero_right_of_cross {u v : Plane} (h : cross u v ≠ 0) : v ≠ 0 := by
  rintro rfl; simp [cross] at h

/-- The boundary of a sector is null. -/
theorem volume_sectorC_diff {X u v : Plane} (hne : cross u v ≠ 0) :
    volume (sectorC X u v \ sectorO X u v) = 0 := by
  have hu := ne_zero_left_of_cross hne
  have hv := ne_zero_right_of_cross hne
  have hsub : sectorC X u v \ sectorO X u v ⊆
      {y | crossL u y = cross u X} ∪ {y | crossL v y = cross v X} := by
    rintro y ⟨⟨h1, h2⟩, hno⟩
    simp only [sectorO, Set.mem_setOf_eq, not_and_or, not_lt] at hno
    simp only [Set.mem_union, Set.mem_setOf_eq, crossL_apply]
    rcases hno with h | h
    · left
      have : cross u (y - X) * cross u v = 0 := le_antisymm h h1
      rcases mul_eq_zero.mp this with h0 | h0
      · rw [cross_sub_right] at h0; linarith
      · exact absurd h0 hne
    · right
      have : cross (y - X) v * cross u v = 0 := le_antisymm h h2
      rcases mul_eq_zero.mp this with h0 | h0
      · rw [cross_swap, cross_sub_right] at h0; linarith
      · exact absurd h0 hne
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · exact volume_level_zero (crossL_ne_zero hu) _
  · exact volume_level_zero (crossL_ne_zero hv) _

/-- Three points whose edge vectors have nonzero cross product are affinely independent. -/
theorem affineIndependent_of_cross' (a b c : Plane) (h : cross (b - a) (c - a) ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_of_ne (show (0 : Fin 3) ≠ 1 by decide)
    (show (0 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 2 by decide)]
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨q, v, hv⟩ := hc
  obtain ⟨ra, ha⟩ := hv a (by simp)
  obtain ⟨rb, hb⟩ := hv b (by simp)
  obtain ⟨rc, hc⟩ := hv c (by simp)
  apply h
  have e1 : b - a = (rb - ra) • v := by rw [hb, ha]; simp [sub_smul]
  have e2 : c - a = (rc - ra) • v := by rw [hc, ha]; simp [sub_smul]
  rw [e1, e2, cross_smul_left, cross_smul_right, cross_self]; ring

theorem affineIndependent_of_cross (X u v : Plane) (hne : cross u v ≠ 0) :
    AffineIndependent ℝ ![X, X + u, X + v] :=
  affineIndependent_of_cross' _ _ _ (by simpa using hne)

/-- The sector near `X` has area `θ r² / 2`. -/
theorem volume_sectorC_ball {X u v : Plane} (hne : cross u v ≠ 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (sectorC X u v ∩ ball X r') =
        ENNReal.ofReal (InnerProductGeometry.angle u v / 2 * r' ^ 2) := by
  let Θ : Tri := ⟨![X, X + u, X + v], affineIndependent_of_cross X u v hne⟩
  have h0 : Θ.pts 0 = X := rfl
  have e1 : Θ.edgeVec 0 = u := by simp [Tri.edgeVec, Θ]
  have e2 : Θ.edgeVec' 0 = v := by simp [Tri.edgeVec', Θ]
  obtain ⟨r0, hr0, hEq⟩ := Θ.inter_ball_eq_vertexCone 0
  obtain ⟨r1, hr1, hvol⟩ := Θ.volume_inter_ball_vertex 0
  refine ⟨min r0 r1, lt_min hr0 hr1, fun r' hr' hle => ?_⟩
  have hEq' := inter_ball_mono hEq (hle.trans (min_le_left _ _))
  rw [h0, e1, e2] at hEq'
  have hv := hvol r' hr' (hle.trans (min_le_right _ _))
  rw [Θ.cornerAngle_eq_angle, e1, e2, h0] at hv
  rw [← hv, hEq']
  rfl

/-! ### Rays and the tiles in a sector -/

variable {N : ℕ} (D : Dissection N)

/-- The ray from `X` along `u` lies, near `X`, in no tile's interior. -/
def RayWall (X u : Plane) : Prop :=
  ∃ t > (0 : ℝ), ∀ s : ℝ, 0 ≤ s → s ≤ t → ∀ i, X + s • u ∉ interior (D.tile i).carrier

open Classical in
/-- The tiles in the sector: those whose interior meets the open sector arbitrarily near `X`. -/
noncomputable def sectorTiles (X u v : Plane) : Finset (Fin N) :=
  Finset.univ.filter fun i => ∀ r > (0 : ℝ),
    (interior (D.tile i).carrier ∩ sectorO X u v ∩ ball X r).Nonempty

theorem mem_sectorTiles {X u v : Plane} {i : Fin N} :
    i ∈ sectorTiles D X u v ↔ ∀ r > (0 : ℝ),
      (interior (D.tile i).carrier ∩ sectorO X u v ∩ ball X r).Nonempty := by
  classical
  simp [sectorTiles]

/-- A ray along a tile edge from `X` is a wall. -/
theorem rayWall_of_edge {X u : Plane} {j : Fin N} {k : Fin 3} {t : ℝ} (ht : 0 < t)
    (hX : X ∈ (D.tile j).edge k) (hXt : X + t • u ∈ (D.tile j).edge k) : RayWall D X u := by
  refine ⟨t, ht, fun s hs hst i => ?_⟩
  suffices hm : X + s • u ∈ (D.tile j).edge k from D.edge_point_not_interior hm i
  have hc : Convex ℝ ((D.tile j).edge k) := convex_segment _ _
  have : X + s • u = AffineMap.lineMap X (X + t • u) (s / t) := by
    rw [AffineMap.lineMap_apply_module']
    simp only [add_sub_cancel_left, smul_smul]
    rw [div_mul_cancel₀ s ht.ne', add_comm]
  rw [this]
  exact hc.lineMap_mem hX hXt ⟨div_nonneg hs ht.le, (div_le_one ht).mpr hst⟩

/-- First root of two affine functions on `[0, 1]` that start positive. -/
theorem first_root {a1 a2 b1 b2 : ℝ} (ha1 : 0 < a1) (ha2 : 0 < a2) (hb : b1 < 0 ∨ b2 < 0) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ (((1 - s) * a1 + s * b1 = 0 ∧ 0 ≤ (1 - s) * a2 + s * b2) ∨
      ((1 - s) * a2 + s * b2 = 0 ∧ 0 ≤ (1 - s) * a1 + s * b1)) := by
  -- `s₁ = a₁ / (a₁ - b₁)` when `b₁ < 0`.
  have key : ∀ {a1 a2 b1 b2 : ℝ}, 0 < a1 → 0 < a2 → b1 < 0 →
      (0 ≤ b2 ∨ a1 * (a2 - b2) ≤ a2 * (a1 - b1)) →
      ∃ s : ℝ, 0 < s ∧ s < 1 ∧ (1 - s) * a1 + s * b1 = 0 ∧ 0 ≤ (1 - s) * a2 + s * b2 := by
    intro a1 a2 b1 b2 ha1 ha2 hb1 h
    have hd : 0 < a1 - b1 := by linarith
    refine ⟨a1 / (a1 - b1), div_pos ha1 hd, (div_lt_one hd).mpr (by linarith), ?_, ?_⟩
    · field_simp; ring
    · have e : (1 - a1 / (a1 - b1)) * a2 + a1 / (a1 - b1) * b2 =
          (a2 * (a1 - b1) - a1 * (a2 - b2)) / (a1 - b1) := by field_simp; ring
      rw [e]
      apply div_nonneg _ hd.le
      rcases h with h | h
      · nlinarith
      · linarith
  rcases hb with hb1 | hb2
  · by_cases h : 0 ≤ b2 ∨ a1 * (a2 - b2) ≤ a2 * (a1 - b1)
    · obtain ⟨s, h0, h1, h2, h3⟩ := key ha1 ha2 hb1 h
      exact ⟨s, h0, h1, Or.inl ⟨h2, h3⟩⟩
    · push Not at h
      obtain ⟨s, h0, h1, h2, h3⟩ := key ha2 ha1 h.1 (Or.inr h.2.le)
      exact ⟨s, h0, h1, Or.inr ⟨h2, h3⟩⟩
  · by_cases h : 0 ≤ b1 ∨ a2 * (a1 - b1) ≤ a1 * (a2 - b2)
    · obtain ⟨s, h0, h1, h2, h3⟩ := key ha2 ha1 hb2 h
      exact ⟨s, h0, h1, Or.inr ⟨h2, h3⟩⟩
    · push Not at h
      obtain ⟨s, h0, h1, h2, h3⟩ := key ha1 ha2 h.1 (Or.inr h.2.le)
      exact ⟨s, h0, h1, Or.inl ⟨h2, h3⟩⟩

theorem cross_lineMap_sub (u z y X : Plane) (s : ℝ) :
    cross u (AffineMap.lineMap z y s - X) = (1 - s) * cross u (z - X) + s * cross u (y - X) := by
  rw [AffineMap.lineMap_apply_module]
  simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem cross_lineMap_sub' (v z y X : Plane) (s : ℝ) :
    cross (AffineMap.lineMap z y s - X) v = (1 - s) * cross (z - X) v + s * cross (y - X) v := by
  rw [AffineMap.lineMap_apply_module]
  simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- A point of the closed sector's boundary near `X`: on one of the two rays. -/
theorem ray_of_boundary {X u v w : Plane} (hne : cross u v ≠ 0)
    (h : (cross u (w - X) * cross u v = 0 ∧ 0 ≤ cross (w - X) v * cross u v) ∨
      (cross (w - X) v * cross u v = 0 ∧ 0 ≤ cross u (w - X) * cross u v)) :
    (∃ l : ℝ, 0 ≤ l ∧ w = X + l • u) ∨ (∃ l : ℝ, 0 ≤ l ∧ w = X + l • v) := by
  have hu := ne_zero_left_of_cross hne
  have hv := ne_zero_right_of_cross hne
  have hsq : 0 < cross u v * cross u v := mul_self_pos.mpr hne
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h0 : cross u (w - X) = 0 := (mul_eq_zero.mp h1).resolve_right hne
    obtain ⟨l, hl⟩ := parallel_of_cross_eq_zero hu h0
    left
    refine ⟨l, ?_, by rw [← hl]; abel⟩
    rw [hl, cross_smul_left] at h2
    nlinarith
  · have h0 : cross (w - X) v = 0 := (mul_eq_zero.mp h1).resolve_right hne
    have h0' : cross v (w - X) = 0 := by rw [cross_swap, h0, neg_zero]
    obtain ⟨l, hl⟩ := parallel_of_cross_eq_zero hv h0'
    right
    refine ⟨l, ?_, by rw [← hl]; abel⟩
    rw [hl, cross_smul_right] at h2
    nlinarith

/-- **No tile crosses the rays.** A tile in the sector lies, near `X`, in the closed sector. -/
theorem sector_subset {X u v : Plane} (hne : cross u v ≠ 0) (hu : RayWall D X u)
    (hv : RayWall D X v) {i : Fin N} (hi : i ∈ sectorTiles D X u v) :
    ∃ r > (0 : ℝ), (D.tile i).carrier ∩ ball X r ⊆ sectorC X u v := by
  obtain ⟨tu, htu, hwu⟩ := hu
  obtain ⟨tv, htv, hwv⟩ := hv
  have hu0 := ne_zero_left_of_cross hne
  have hv0 := ne_zero_right_of_cross hne
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set r := min (tu * ‖u‖) (tv * ‖v‖)
  have hr : 0 < r := lt_min (mul_pos htu hnu) (mul_pos htv hnv)
  refine ⟨r, hr, ?_⟩
  rintro y ⟨hyT, hyB⟩
  by_contra hyS
  obtain ⟨z, ⟨hzT, hzO⟩, hzB⟩ := (mem_sectorTiles D).mp hi r hr
  rw [mem_sectorC, not_and_or, not_le, not_le] at hyS
  obtain ⟨s, hs0, hs1, hroot⟩ := first_root hzO.1 hzO.2 hyS
  set w := AffineMap.lineMap z y s
  have e1 : cross u (w - X) * cross u v = (1 - s) * (cross u (z - X) * cross u v) +
      s * (cross u (y - X) * cross u v) := by
    simp only [w]; rw [cross_lineMap_sub]; ring
  have e2 : cross (w - X) v * cross u v = (1 - s) * (cross (z - X) v * cross u v) +
      s * (cross (y - X) v * cross u v) := by
    simp only [w]; rw [cross_lineMap_sub']; ring
  have hw : (cross u (w - X) * cross u v = 0 ∧ 0 ≤ cross (w - X) v * cross u v) ∨
      (cross (w - X) v * cross u v = 0 ∧ 0 ≤ cross u (w - X) * cross u v) := by
    rw [e1, e2]; exact hroot
  -- `w` is interior to the tile, and near `X`.
  have hwint : w ∈ interior (D.tile i).carrier := by
    apply (D.tile i).convex.openSegment_interior_closure_subset_interior hzT
      (subset_closure hyT)
    rw [openSegment_eq_image_lineMap]
    exact ⟨s, ⟨hs0, hs1⟩, rfl⟩
  have hwB : w ∈ ball X r :=
    (convex_ball X r).lineMap_mem hzB hyB ⟨hs0.le, hs1.le⟩
  rw [mem_ball, dist_eq_norm] at hwB
  rcases ray_of_boundary hne hw with ⟨l, hl, hlw⟩ | ⟨l, hl, hlw⟩
  · have : l < tu := by
      rw [hlw, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hl] at hwB
      have := hwB.trans_le (min_le_left _ _)
      exact lt_of_mul_lt_mul_right this hnu.le
    exact hwu l hl this.le i (hlw ▸ hwint)
  · have : l < tv := by
      rw [hlw, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hl] at hwB
      have := hwB.trans_le (min_le_right _ _)
      exact lt_of_mul_lt_mul_right this hnv.le
    exact hwv l hl this.le i (hlw ▸ hwint)

/-- A tile in the sector contains `X`. -/
theorem mem_of_sectorTiles {X u v : Plane} {i : Fin N} (hi : i ∈ sectorTiles D X u v) :
    X ∈ (D.tile i).carrier := by
  rw [← (D.tile i).isCompact.isClosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, ⟨⟨hz, -⟩, hzB⟩⟩ := (mem_sectorTiles D).mp hi ε hε
  exact ⟨z, interior_subset hz, by rw [dist_comm]; exact hzB⟩

/-- A tile not in the sector misses the open sector near `X`. -/
theorem not_sectorTiles {X u v : Plane} {i : Fin N} (hi : i ∉ sectorTiles D X u v) :
    ∃ r > (0 : ℝ), (D.tile i).carrier ∩ sectorO X u v ∩ ball X r = ∅ := by
  rw [mem_sectorTiles] at hi
  push Not at hi
  obtain ⟨r, hr, he⟩ := hi
  refine ⟨r, hr, Set.eq_empty_iff_forall_notMem.mpr fun y ⟨⟨hyT, hyO⟩, hyB⟩ => ?_⟩
  have hO : IsOpen (sectorO X u v ∩ ball X r) := (isOpen_sectorO X u v).inter isOpen_ball
  rw [← tri_closure_interior] at hyT
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hyT _ hO ⟨hyO, hyB⟩
  exact (Set.eq_empty_iff_forall_notMem.mp he) z ⟨⟨hz2, hz1.1⟩, hz1.2⟩

/-- A radius below finitely many positive ones. -/
theorem exists_radius_le {N : ℕ} (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ r > (0 : ℝ), r ≤ r₀ ∧ ∀ i, r ≤ f i := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨r₀, hr₀, le_rfl, fun i => i.elim0⟩
  · obtain ⟨r, hr, hle⟩ := exists_common_radius hN f hf
    exact ⟨min r r₀, lt_min hr hr₀, min_le_right _ _, fun i => (min_le_left _ _).trans (hle i)⟩

/-- **The tiles in the sector cover it near `X`.** -/
theorem sector_cover {X u v : Plane} (hne : cross u v ≠ 0)
    (hin : ∃ r > (0 : ℝ), sectorC X u v ∩ ball X r ⊆ D.target.carrier) :
    ∃ r > (0 : ℝ), sectorC X u v ∩ ball X r ⊆ ⋃ i ∈ sectorTiles D X u v, (D.tile i).carrier := by
  classical
  obtain ⟨r₀, hr₀, hsub⟩ := hin
  have hfar : ∀ i, ∃ ρ > (0 : ℝ), i ∉ sectorTiles D X u v →
      (D.tile i).carrier ∩ sectorO X u v ∩ ball X ρ = ∅ := by
    intro i
    by_cases h : i ∈ sectorTiles D X u v
    · exact ⟨1, one_pos, fun h' => absurd h h'⟩
    · obtain ⟨ρ, hρ, he⟩ := not_sectorTiles D h
      exact ⟨ρ, hρ, fun _ => he⟩
  choose ρ hρ hρe using hfar
  obtain ⟨r, hr, hrr₀, hrρ⟩ := exists_radius_le ρ hρ r₀ hr₀
  refine ⟨r, hr, ?_⟩
  have hclosed : IsClosed (⋃ i ∈ sectorTiles D X u v, (D.tile i).carrier) :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun i _ => (D.tile i).isCompact.isClosed
  -- The open sector near `X`.
  have hopen : sectorO X u v ∩ ball X r ⊆ ⋃ i ∈ sectorTiles D X u v, (D.tile i).carrier := by
    rintro y ⟨hyO, hyB⟩
    have hyT : y ∈ D.target.carrier :=
      hsub ⟨sectorO_subset_sectorC X u v hyO, ball_subset_ball hrr₀ hyB⟩
    rw [← D.covers, Set.mem_iUnion] at hyT
    obtain ⟨i, hi⟩ := hyT
    by_cases h : i ∈ sectorTiles D X u v
    · exact Set.mem_biUnion h hi
    · exact absurd (hρe i h) (Set.nonempty_iff_ne_empty.mp
        ⟨y, ⟨hi, hyO⟩, ball_subset_ball (hrρ i) hyB⟩)
  -- Points of the closed sector are limits of points of the open sector.
  rintro y ⟨hyC, hyB⟩
  apply hclosed.mem_of_tendsto (f := fun ε : ℝ => y + ε • (u + v))
    (b := nhdsWithin 0 (Set.Ioi 0))
  · have : Filter.Tendsto (fun ε : ℝ => y + ε • (u + v)) (nhds 0) (nhds y) := by
      have h := ((continuous_const.add (continuous_id.smul continuous_const)) :
        Continuous fun ε : ℝ => y + ε • (u + v)).tendsto 0
      simpa using h
    exact this.mono_left nhdsWithin_le_nhds
  · have hB : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), y + ε • (u + v) ∈ ball X r := by
      have : Filter.Tendsto (fun ε : ℝ => y + ε • (u + v)) (nhds 0) (nhds y) := by
        have h := ((continuous_const.add (continuous_id.smul continuous_const)) :
          Continuous fun ε : ℝ => y + ε • (u + v)).tendsto 0
        simpa using h
      exact (this.mono_left nhdsWithin_le_nhds).eventually (isOpen_ball.mem_nhds hyB)
    filter_upwards [hB, self_mem_nhdsWithin] with ε hεB hε
    apply hopen
    refine ⟨⟨?_, ?_⟩, hεB⟩
    · have : cross u (y + ε • (u + v) - X) * cross u v =
          cross u (y - X) * cross u v + ε * (cross u v * cross u v) := by
        simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [this]
      have := mul_self_pos.mpr hne
      have h1 := hyC.1
      have : (0:ℝ) < ε := hε
      positivity
    · have : cross (y + ε • (u + v) - X) v * cross u v =
          cross (y - X) v * cross u v + ε * (cross u v * cross u v) := by
        simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [this]
      have := mul_self_pos.mpr hne
      have h1 := hyC.2
      have : (0:ℝ) < ε := hε
      positivity

/-- **The angles in a sector add up to its angle.** -/
theorem sector_sum {X u v : Plane} (hne : cross u v ≠ 0) (hu : RayWall D X u)
    (hv : RayWall D X v)
    (hin : ∃ r > (0 : ℝ), sectorC X u v ∩ ball X r ⊆ D.target.carrier) :
    ∑ i ∈ sectorTiles D X u v, (D.tile i).localAngle X = InnerProductGeometry.angle u v := by
  classical
  obtain ⟨r₀, hr₀, hsub⟩ := hin
  obtain ⟨rS, hrS, hvolS⟩ := volume_sectorC_ball (X := X) hne
  set F := sectorTiles D X u v
  -- A radius for each tile.
  have hrad : ∀ i, ∃ ρ > (0 : ℝ), (∀ r', 0 < r' → r' ≤ ρ →
      volume ((D.tile i).carrier ∩ ball X r') =
        ENNReal.ofReal ((D.tile i).localAngle X / 2 * r' ^ 2)) ∧
      (i ∈ F → (D.tile i).carrier ∩ ball X ρ ⊆ sectorC X u v) ∧
      (i ∉ F → (D.tile i).carrier ∩ sectorO X u v ∩ ball X ρ = ∅) := by
    intro i
    obtain ⟨ρ₁, hρ₁, h₁⟩ := (D.tile i).volume_inter_ball_localAngle X
    by_cases hi : i ∈ F
    · obtain ⟨ρ₂, hρ₂, h₂⟩ := sector_subset D hne hu hv hi
      refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun r' h1 h2 => h₁ r' h1 (h2.trans (min_le_left _ _)),
        fun _ => fun y hy => h₂ ⟨hy.1, ball_subset_ball (min_le_right _ _) hy.2⟩,
        fun h => absurd hi h⟩
    · obtain ⟨ρ₂, hρ₂, h₂⟩ := not_sectorTiles D hi
      refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun r' h1 h2 => h₁ r' h1 (h2.trans (min_le_left _ _)),
        fun h => absurd h hi, fun _ => ?_⟩
      exact Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
        (Set.eq_empty_iff_forall_notMem.mp h₂) y
          ⟨hy.1, ball_subset_ball (min_le_right _ _) hy.2⟩
  choose ρ hρ hρvol hρin hρout using hrad
  obtain ⟨r, hr, hrr, hrρ⟩ := exists_radius_le ρ hρ (min r₀ rS) (lt_min hr₀ hrS)
  have hr₀' : r ≤ r₀ := hrr.trans (min_le_left _ _)
  have hrS' : r ≤ rS := hrr.trans (min_le_right _ _)
  set B := ball X r
  have hCB : sectorC X u v ∩ B ⊆ D.target.carrier := fun y hy =>
    hsub ⟨hy.1, ball_subset_ball hr₀' hy.2⟩
  have hmeas : MeasurableSet (sectorC X u v ∩ B) :=
    (isClosed_sectorC X u v).measurableSet.inter isOpen_ball.measurableSet
  have hsum := volume_inter_eq_sum D hmeas
  rw [Set.inter_eq_right.mpr hCB, hvolS r hr hrS'] at hsum
  have hper : ∀ i, volume ((D.tile i).carrier ∩ (sectorC X u v ∩ B)) =
      ENNReal.ofReal (if i ∈ F then (D.tile i).localAngle X / 2 * r ^ 2 else 0) := by
    intro i
    split_ifs with hi
    · have heq : (D.tile i).carrier ∩ (sectorC X u v ∩ B) = (D.tile i).carrier ∩ B := by
        ext y
        simp only [Set.mem_inter_iff]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1,
          hρin i hi ⟨h.1, ball_subset_ball (hrρ i) h.2⟩, h.2⟩⟩
      rw [heq]
      exact hρvol i r hr (hrρ i)
    · rw [ENNReal.ofReal_zero]
      refine measure_mono_null ?_ (volume_sectorC_diff (X := X) hne)
      rintro y ⟨hyT, hyC, hyB⟩
      refine ⟨hyC, fun hyO => ?_⟩
      exact (Set.eq_empty_iff_forall_notMem.mp (hρout i hi)) y
        ⟨⟨hyT, hyO⟩, ball_subset_ball (hrρ i) hyB⟩
  rw [Finset.sum_congr rfl (fun i _ => hper i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      split_ifs
      · have := (D.tile i).localAngle_nonneg X; positivity
      · exact le_rfl)] at hsum
  have hA : 0 ≤ InnerProductGeometry.angle u v := InnerProductGeometry.angle_nonneg u v
  have hreal := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (Finset.sum_nonneg fun i _ => by
      split_ifs
      · have := (D.tile i).localAngle_nonneg X; positivity
      · exact le_rfl)).mp hsum
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_mul, ← Finset.sum_div,
    Finset.filter_mem_eq_inter, Finset.univ_inter] at hreal
  have hr2 : 0 < r ^ 2 := by positivity
  have : (∑ i ∈ F, (D.tile i).localAngle X) * r ^ 2 = InnerProductGeometry.angle u v * r ^ 2 := by
    linarith
  exact (mul_right_cancel₀ hr2.ne' this)

/-- **A wall ray lies along an edge.** A tile with a vertex at `X` containing points of a wall ray
from `X` along `u` arbitrarily near `X` has an edge along that ray. -/
theorem ray_edge {X u : Plane} (hu0 : u ≠ 0) (hu : RayWall D X u) {i : Fin N} {k : Fin 3}
    (hk : (D.tile i).pts k = X) (hray : ∀ ε > (0 : ℝ), ∃ s, 0 < s ∧ s < ε ∧
      X + s • u ∈ (D.tile i).carrier) :
    (∃ l > (0 : ℝ), (D.tile i).pts (k + 1) = X + l • u) ∨
      (∃ l > (0 : ℝ), (D.tile i).pts (k + 2) = X + l • u) := by
  set T := D.tile i
  obtain ⟨tu, htu, hwu⟩ := hu
  obtain ⟨r₁, hr₁, hEq⟩ := T.inter_ball_eq_vertexCone k
  rw [hk] at hEq
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  obtain ⟨s, hs0, hs1, hsT⟩ := hray (min tu (r₁ / ‖u‖)) (lt_min htu (div_pos hr₁ hnu))
  have hsB : X + s • u ∈ ball X r₁ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
    have := hs1.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hnu] at this
  have hcone : X + s • u ∈ {y : Plane | y - X ∈ vertexCone (T.edgeVec k) (T.edgeVec' k)} :=
    (hEq.subset ⟨hsT, hsB⟩).1
  simp only [Set.mem_setOf_eq, add_sub_cancel_left, vertexCone] at hcone
  set e := T.edgeVec k
  set e' := T.edgeVec' k
  have hd : cross e e' ≠ 0 := by rw [T.cross_edgeVec k]; exact T.det_ne_zero
  have hsq : 0 < cross e e' * cross e e' := mul_self_pos.mpr hd
  have he0 : e ≠ 0 := T.edgeVec_ne_zero k
  have he0' : e' ≠ 0 := T.edgeVec'_ne_zero k
  -- If both cross products were positive, `X + s u` would be interior to the tile.
  by_cases h1 : 0 < cross e (s • u) * cross e e'
  · by_cases h2 : 0 < cross (s • u) e' * cross e e'
    · exfalso
      apply hwu s hs0.le (hs1.trans_le (min_le_left _ _)).le i
      -- the open cone near the vertex lies in the tile
      have hO : IsOpen {y : Plane | 0 < cross e (y - X) * cross e e' ∧
          0 < cross (y - X) e' * cross e e'} := by
        have := isOpen_sectorO X e e'; exact this
      rw [mem_interior]
      refine ⟨{y : Plane | 0 < cross e (y - X) * cross e e' ∧
          0 < cross (y - X) e' * cross e e'} ∩ ball X r₁, ?_, hO.inter isOpen_ball, ?_, ?_⟩
      · rintro y ⟨hy, hyB⟩
        have : y ∈ {y : Plane | y - X ∈ vertexCone e e'} ∩ ball X r₁ :=
          ⟨⟨hy.1.le, hy.2.le⟩, hyB⟩
        rw [← hEq] at this
        exact this.1
      · simp only [Set.mem_setOf_eq, add_sub_cancel_left]; exact ⟨h1, h2⟩
      · exact hsB
    · -- `s u` is along `e'`
      have h0 : cross (s • u) e' * cross e e' = 0 := le_antisymm (not_lt.mp h2) hcone.2
      have h0' : cross e' (s • u) = 0 := by
        rw [cross_swap, (mul_eq_zero.mp h0).resolve_right hd, neg_zero]
      obtain ⟨l, hl⟩ := parallel_of_cross_eq_zero he0' h0'
      right
      have hl0 : 0 < l := by
        have : cross e (s • u) * cross e e' = l * (cross e e' * cross e e') := by
          rw [hl, cross_smul_right]; ring
        rw [this] at h1
        exact pos_of_mul_pos_left h1 hsq.le
      refine ⟨s / l, div_pos hs0 hl0, ?_⟩
      have : T.pts (k + 2) = X + e' := by simp [e', Tri.edgeVec', hk]
      rw [this]
      have hu' : u = (l / s) • e' := by
        rw [← smul_right_inj hs0.ne', hl, smul_smul]; congr 1; field_simp
      rw [hu', smul_smul, div_mul_div_comm, mul_comm s l, div_self (mul_pos hl0 hs0).ne',
        one_smul]
  · -- `s u` is along `e`
    have h0 : cross e (s • u) * cross e e' = 0 := le_antisymm (not_lt.mp h1) hcone.1
    have h0' : cross e (s • u) = 0 := (mul_eq_zero.mp h0).resolve_right hd
    obtain ⟨l, hl⟩ := parallel_of_cross_eq_zero he0 h0'
    left
    have hl0 : 0 < l := by
      have h2 := hcone.2
      have : cross (s • u) e' * cross e e' = l * (cross e e' * cross e e') := by
        rw [hl, cross_smul_left]; ring
      rw [this] at h2
      have hne' : cross (s • u) e' * cross e e' ≠ 0 := by
        intro hz
        have hz' : cross (s • u) e' = 0 := (mul_eq_zero.mp hz).resolve_right hd
        rw [hl, cross_smul_left] at hz'
        have : l = 0 := by
          rcases mul_eq_zero.mp hz' with h | h
          · exact h
          · exact absurd h hd
        rw [this, zero_smul] at hl
        exact (smul_ne_zero hs0.ne' hu0) hl
      rw [this] at hne'
      exact lt_of_le_of_ne (nonneg_of_mul_nonneg_left h2 hsq) (fun h => hne' (by rw [← h]; ring))
    refine ⟨s / l, div_pos hs0 hl0, ?_⟩
    have : T.pts (k + 1) = X + e := by simp [e, Tri.edgeVec, hk]
    rw [this]
    have hu' : u = (l / s) • e := by
      rw [← smul_right_inj hs0.ne', hl, smul_smul]; congr 1; field_simp
    rw [hu', smul_smul, div_mul_div_comm, mul_comm s l, div_self (mul_pos hl0 hs0).ne', one_smul]

end TriangleTiling.Prime
