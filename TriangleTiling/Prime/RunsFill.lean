/-
Filling a sector, for Section 11 of Beeson–Roșu ("Runs of `c` edges"): the paper's "the sector
between these two rays has angle `θ`, so by `lemma:angles` it is filled by one tile with its `θ`
angle there; its sides there lie on the two rays".

* `sector_one`: a sector of angle `α` or `β` is filled by one tile, whose edges at `X` lie along
  the two rays.
* `sector_minus`: a sector containing a known tile along one ray, the rest of angle `α` or `β`, has
  a second tile with that angle and an edge along the other ray.
* `sector_two`: a sector of angle `α + 2β` has tiles along both rays, one of them with angle `β`.
-/
import TriangleTiling.Prime.RunsAngles

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ}

/-- The vertices of a triangle, listed from any vertex. -/
theorem Tri.range_pts (T : Tri) (l : Fin 3) :
    Set.range T.pts = {T.pts l, T.pts (l + 1), T.pts (l + 2)} := by
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases l <;> fin_cases j <;> simp
  · rintro (h | h | h) <;> exact ⟨_, h.symm⟩

/-- The angle at a vertex whose two edges run along `u` and `v`. -/
theorem Tri.angleAt_of_edges (T : Tri) {l : Fin 3} {X u v : Plane} {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (h0 : T.pts l = X) (h1 : T.pts (l + 1) = X + s • u)
    (h2 : T.pts (l + 2) = X + t • v) : T.angleAt l = InnerProductGeometry.angle u v := by
  unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
  rw [h0, h1, h2]
  simp only [vsub_eq_sub, add_sub_cancel_left]
  rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
    InnerProductGeometry.angle_smul_right_of_pos _ _ ht]

/-! ### Sectors are cones -/

theorem sectorC_smul {X u v y : Plane} (hy : y ∈ sectorC X u v) {t : ℝ} (ht : 0 ≤ t) :
    X + t • (y - X) ∈ sectorC X u v := by
  rw [mem_sectorC] at hy ⊢
  rw [add_sub_cancel_left, cross_smul_right, cross_smul_left]
  constructor <;> nlinarith [hy.1, hy.2]

theorem convex_sectorC (X u v : Plane) : Convex ℝ (sectorC X u v) := by
  intro y hy z hz s t hs ht hst
  rw [mem_sectorC] at hy hz ⊢
  have e : s • y + t • z - X = s • (y - X) + t • (z - X) := by
    have hX : X = s • X + t • X := by rw [← add_smul, hst, one_smul]
    calc s • y + t • z - X = s • y + t • z - (s • X + t • X) := by rw [← hX]
      _ = _ := by rw [smul_sub, smul_sub]; abel
  rw [e, cross_add_right, cross_smul_right, cross_smul_right, cross_add_left', cross_smul_left,
    cross_smul_left]
  constructor <;> nlinarith [hy.1, hy.2, hz.1, hz.2, mul_nonneg hs (hy.1), mul_nonneg ht hz.1,
    mul_nonneg hs hy.2, mul_nonneg ht hz.2]

theorem ray_mem_sectorC {X u v : Plane} {s : ℝ} (hs : 0 ≤ s) : X + s • u ∈ sectorC X u v := by
  rw [mem_sectorC, add_sub_cancel_left, cross_smul_right, cross_smul_left, cross_self]
  constructor
  · simp
  · nlinarith [mul_self_nonneg (cross u v)]

theorem ray_mem_sectorC' {X u v : Plane} {s : ℝ} (hs : 0 ≤ s) : X + s • v ∈ sectorC X u v := by
  rw [mem_sectorC, add_sub_cancel_left, cross_smul_right, cross_smul_left, cross_self]
  constructor
  · nlinarith [mul_self_nonneg (cross u v)]
  · simp

variable (D : Dissection N)

/-- **A tile in the sector, with a vertex at `X`, lies in the closed sector.** -/
theorem tile_subset_sector {X u v : Plane} (hne : cross u v ≠ 0) (hu : RayWall D X u)
    (hv : RayWall D X v) {i : Fin N} (hi : i ∈ sectorTiles D X u v) {l : Fin 3}
    (hl : (D.tile i).pts l = X) : (D.tile i).carrier ⊆ sectorC X u v := by
  obtain ⟨r, hr, hsub⟩ := sector_subset D hne hu hv hi
  have hpts : ∀ j, (D.tile i).pts j ∈ sectorC X u v := by
    intro j
    set P := (D.tile i).pts j
    by_cases hP : P = X
    · rw [hP, mem_sectorC, sub_self]; simp [cross]
    have hd : 0 < dist P X := dist_pos.mpr hP
    set t := r / (2 * dist P X)
    have ht : 0 < t := by positivity
    have ht1 : t ≤ 1 ∨ 1 < t := le_or_gt t 1
    -- `X + t (P - X)` is in the tile and near `X`.
    set Y := X + (min t 1) • (P - X)
    have hYT : Y ∈ (D.tile i).carrier := by
      have : Y = AffineMap.lineMap X P (min t 1) := by
        rw [AffineMap.lineMap_apply_module']; simp only [Y]; abel
      rw [this]
      exact (D.tile i).convex.lineMap_mem (hl ▸ subset_convexHull ℝ _ ⟨l, rfl⟩)
        (subset_convexHull ℝ _ ⟨j, rfl⟩) ⟨(lt_min ht one_pos).le, min_le_right _ _⟩
    have hYB : Y ∈ ball X r := by
      rw [mem_ball, dist_eq_norm]
      simp only [Y, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (lt_min ht one_pos).le]
      rw [← dist_eq_norm]
      calc min t 1 * dist P X ≤ t * dist P X := by gcongr; exact min_le_left _ _
        _ = r / 2 := by simp only [t]; field_simp
        _ < r := by linarith
    have hY := hsub ⟨hYT, hYB⟩
    have := sectorC_smul hY (t := (min t 1)⁻¹) (inv_nonneg.mpr (lt_min ht one_pos).le)
    simp only [Y, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (lt_min ht one_pos).ne',
      one_smul, add_sub_cancel] at this
    exact this
  intro y hy
  exact (convexHull_min (by rintro _ ⟨j, rfl⟩; exact hpts j) (convex_sectorC X u v)) hy

/-- **A tile containing the ray near `X`.** If the tiles of a finite set cover the sector near
`X`, one of them contains points of the ray along `u` arbitrarily near `X`. -/
theorem ray_tile {X u v : Plane} (hu0 : u ≠ 0) {F : Finset (Fin N)} {r : ℝ} (hr : 0 < r)
    (hcov : sectorC X u v ∩ ball X r ⊆ ⋃ i ∈ F, (D.tile i).carrier) :
    ∃ i ∈ F, ∀ ε > (0 : ℝ), ∃ s, 0 < s ∧ s < ε ∧ X + s • u ∈ (D.tile i).carrier := by
  classical
  by_contra hno
  push Not at hno
  choose ε hε hfar using fun (i : F) => hno i i.2
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set f : Fin N → ℝ := fun i => if h : i ∈ F then ε ⟨i, h⟩ else 1
  have hf : ∀ i, 0 < f i := by
    intro i; simp only [f]; split_ifs with h
    · exact hε _
    · exact one_pos
  obtain ⟨ε₀, hε₀, hε₀r, hε₀f⟩ := exists_radius_le f hf (r / ‖u‖) (div_pos hr hnu)
  set s := ε₀ / 2
  have hs : 0 < s := by positivity
  have hmem : X + s • u ∈ sectorC X u v ∩ ball X r := by
    refine ⟨ray_mem_sectorC hs.le, ?_⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    have : s < r / ‖u‖ := by simp only [s]; linarith
    rwa [lt_div_iff₀ hnu] at this
  have := hcov hmem
  simp only [Set.mem_iUnion] at this
  obtain ⟨i, hi, hT⟩ := this
  have : s < ε ⟨i, hi⟩ := by
    have := hε₀f i
    simp only [f, dif_pos hi] at this
    simp only [s]; linarith
  exact absurd hT (hfar ⟨i, hi⟩ s hs this)

/-- Points of the open vertex cone of a tile near its vertex are interior to the tile. -/
theorem Tri.interior_of_openCone (T : Tri) (l : Fin 3) :
    ∃ r > (0 : ℝ), ∀ y ∈ ball (T.pts l) r,
      0 < cross (T.edgeVec l) (y - T.pts l) * cross (T.edgeVec l) (T.edgeVec' l) →
      0 < cross (y - T.pts l) (T.edgeVec' l) * cross (T.edgeVec l) (T.edgeVec' l) →
      y ∈ interior T.carrier := by
  obtain ⟨r₁, hr₁, hEq⟩ := T.inter_ball_eq_vertexCone l
  refine ⟨r₁, hr₁, fun y hyB h1 h2 => ?_⟩
  rw [mem_interior]
  refine ⟨sectorO (T.pts l) (T.edgeVec l) (T.edgeVec' l) ∩ ball (T.pts l) r₁, ?_,
    (isOpen_sectorO _ _ _).inter isOpen_ball, ⟨⟨h1, h2⟩, hyB⟩⟩
  rintro z ⟨hz, hzB⟩
  have : z ∈ {y : Plane | y - T.pts l ∈ vertexCone (T.edgeVec l) (T.edgeVec' l)} ∩
      ball (T.pts l) r₁ := ⟨⟨hz.1.le, hz.2.le⟩, hzB⟩
  rw [← hEq] at this
  exact this.1

theorem Tri.edgeVec_eq (T : Tri) (l : Fin 3) : T.edgeVec l = T.pts (l + 1) - T.pts l := rfl
theorem Tri.edgeVec'_eq (T : Tri) (l : Fin 3) : T.edgeVec' l = T.pts (l + 2) - T.pts l := rfl

/-- Two edges at a vertex along two independent rays: the angle there is the angle between the
rays, and the vertices are `X` and points on the two rays. -/
theorem Tri.two_rays (T : Tri) {l : Fin 3} {X u v : Plane} (hne : cross u v ≠ 0) (hl : T.pts l = X)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hu : T.pts (l + 1) = X + s • u ∨ T.pts (l + 2) = X + s • u)
    (hv : T.pts (l + 1) = X + t • v ∨ T.pts (l + 2) = X + t • v) :
    T.angleAt l = InnerProductGeometry.angle u v ∧
      Set.range T.pts = {X, X + s • u, X + t • v} := by
  have hsame : ∀ j : Fin 3, T.pts j = X + s • u → T.pts j = X + t • v → False := by
    intro j h1 h2
    have : s • u = t • v := by rw [← add_right_inj X, ← h1, ← h2]
    have h3 : cross u (s • u) = cross u (t • v) := by rw [this]
    rw [cross_smul_right, cross_smul_right, cross_self, mul_zero] at h3
    exact hne ((mul_eq_zero.mp h3.symm).resolve_left ht.ne')
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact absurd hv (fun h => hsame _ hu h)
  · refine ⟨Tri.angleAt_of_edges T hs ht hl hu hv, ?_⟩
    rw [Tri.range_pts T l, hl, hu, hv]
  · refine ⟨?_, ?_⟩
    · rw [Tri.angleAt_of_edges T ht hs hl hv hu, InnerProductGeometry.angle_comm]
    · rw [Tri.range_pts T l, hl, hu, hv, Set.pair_comm]
  · exact absurd hv (fun h => hsame _ hu h)

/-- **A tile along a ray of the sector**, on the sector's side of that ray, is in the sector. -/
theorem mem_sectorTiles_of_edge {X u v Z : Plane} {i : Fin N} {l : Fin 3}
    (hl : (D.tile i).pts l = X) {s : ℝ} (hs : 0 < s)
    (hpts : ((D.tile i).pts (l + 1) = X + s • u ∧ (D.tile i).pts (l + 2) = Z) ∨
      ((D.tile i).pts (l + 2) = X + s • u ∧ (D.tile i).pts (l + 1) = Z))
    (hZ : 0 < cross u (Z - X) * cross u v) : i ∈ sectorTiles D X u v := by
  set T := D.tile i
  set e2 := Z - X
  set C := cross u v
  have hC : C ≠ 0 := by intro h; rw [h, mul_zero] at hZ; exact lt_irrefl _ hZ
  have hK : cross u e2 ≠ 0 := by intro h; rw [h, zero_mul] at hZ; exact lt_irrefl _ hZ
  obtain ⟨r₁, hr₁, hint⟩ := Tri.interior_of_openCone T l
  rw [mem_sectorTiles]
  intro r hr
  -- `t` small, then `y = X + σ (s u + t e₂)` with `σ` small.
  set K := cross e2 v * C
  set t : ℝ := min 1 (s * (C * C) / (2 * (|K| + 1)))
  have hCC : 0 < C * C := mul_self_pos.mpr hC
  have ht : 0 < t := lt_min one_pos (by positivity)
  have htK : -(t * K) < s * (C * C) := by
    have h1 : t ≤ s * (C * C) / (2 * (|K| + 1)) := min_le_right _ _
    have h2 : -(t * K) ≤ t * |K| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs K) ht.le
    have h3 : t * |K| ≤ s * (C * C) / (2 * (|K| + 1)) * |K| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg K)
    have h4 : s * (C * C) / (2 * (|K| + 1)) * |K| < s * (C * C) := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      have : 0 < s * (C * C) := by positivity
      nlinarith [abs_nonneg K]
    linarith
  set w := s • u + t • e2
  set ρ := min r r₁
  have hρ : 0 < ρ := lt_min hr hr₁
  set σ : ℝ := ρ / (2 * (‖w‖ + 1))
  have hσ : 0 < σ := by positivity
  set y := X + σ • w
  have hyB : ∀ R, ρ ≤ R → y ∈ ball X R := by
    intro R hR
    rw [mem_ball, dist_eq_norm]
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hσ.le, σ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  refine ⟨y, ⟨?_, ?_⟩, hyB r (min_le_left _ _)⟩
  · -- interior: the open cone at the vertex `l`
    apply hint y (hl ▸ hyB r₁ (min_le_right _ _))
    · rw [hl]
      rcases hpts with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Tri.edgeVec_eq T, Tri.edgeVec'_eq T, h1, h2, hl]
        simp only [y, w, e2, add_sub_cancel_left, cross_smul_right, cross_add_right,
          cross_smul_left, cross_self]
        have : 0 < cross u (Z - X) * cross u (Z - X) := mul_self_pos.mpr hK
        nlinarith [mul_pos (mul_pos hσ ht) (mul_pos hs hs)]
      · rw [Tri.edgeVec_eq T, Tri.edgeVec'_eq T, h1, h2, hl]
        simp only [y, w, e2, add_sub_cancel_left, cross_smul_right, cross_add_right,
          cross_self]
        rw [cross_swap (Z - X) u]
        have : 0 < cross u (Z - X) * cross u (Z - X) := mul_self_pos.mpr hK
        nlinarith [mul_pos (mul_pos hσ hs) (mul_pos hs hs)]
    · rw [hl]
      rcases hpts with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Tri.edgeVec_eq T, Tri.edgeVec'_eq T, h1, h2, hl]
        simp only [y, w, e2, add_sub_cancel_left, cross_add_left',
          cross_smul_left, cross_self]
        have : 0 < cross u (Z - X) * cross u (Z - X) := mul_self_pos.mpr hK
        nlinarith [mul_pos (mul_pos hσ hs) (mul_pos hs hs)]
      · rw [Tri.edgeVec_eq T, Tri.edgeVec'_eq T, h1, h2, hl]
        simp only [y, w, e2, add_sub_cancel_left, cross_smul_right, cross_add_left',
          cross_smul_left, cross_self]
        rw [cross_swap (Z - X) u]
        have : 0 < cross u (Z - X) * cross u (Z - X) := mul_self_pos.mpr hK
        nlinarith [mul_pos (mul_pos hσ ht) (mul_pos hs hs)]
  · -- the open sector
    constructor
    · simp only [y, w, add_sub_cancel_left, cross_smul_right, cross_add_right, cross_self]
      have := mul_pos (mul_pos hσ ht) hZ
      nlinarith
    · simp only [y, w, add_sub_cancel_left, cross_smul_left, cross_add_left']
      have : σ * (s * cross u v + t * cross e2 v) * C = σ * (s * (C * C) + t * K) := by
        simp only [K, C]; ring
      rw [this]
      apply mul_pos hσ
      nlinarith

theorem sectorC_swap (X u v : Plane) : sectorC X v u = sectorC X u v := by
  ext y; simp only [sectorC, Set.mem_setOf_eq, vertexCone_swap]

/-- Ray points near `X` lie in the cover of the sector. -/
theorem ray_points {X u v : Plane} (hu0 : u ≠ 0) {S : Set Plane} {r : ℝ} (hr : 0 < r)
    (hcov : sectorC X u v ∩ ball X r ⊆ S) :
    ∀ ε > (0 : ℝ), ∃ s, 0 < s ∧ s < ε ∧ X + s • u ∈ S := by
  intro ε hε
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set s := min ε (r / ‖u‖) / 2
  have hs : 0 < s := by have := lt_min hε (div_pos hr hnu); simp only [s]; linarith
  refine ⟨s, hs, by have := min_le_left ε (r / ‖u‖); simp only [s]; linarith, hcov ⟨?_, ?_⟩⟩
  · exact ray_mem_sectorC hs.le
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    have : s < r / ‖u‖ := by
      have := min_le_right ε (r / ‖u‖); have := lt_min hε (div_pos hr hnu)
      simp only [s]; linarith
    rwa [lt_div_iff₀ hnu] at this

/-- `ray_edge`, with the scalar in front. -/
theorem ray_edge' {X u : Plane} (hu0 : u ≠ 0) (hu : RayWall D X u) {i : Fin N} {l : Fin 3}
    (hl : (D.tile i).pts l = X) (hray : ∀ ε > (0 : ℝ), ∃ s, 0 < s ∧ s < ε ∧
      X + s • u ∈ (D.tile i).carrier) :
    ∃ s > (0 : ℝ), (D.tile i).pts (l + 1) = X + s • u ∨ (D.tile i).pts (l + 2) = X + s • u := by
  rcases ray_edge D hu0 hu hl hray with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
  · exact ⟨s, hs, Or.inl h⟩
  · exact ⟨s, hs, Or.inr h⟩

/-! ### Sector fills in the setting of Section 11 -/

section Fill

variable {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
  (hS : RunSetting D α β γ a b c m k)
include hS

/-- **A sector of angle `α` or `β` is filled by one tile**, with that angle at `X` and its two
edges at `X` along the two rays. -/
theorem sector_one {X u v : Plane} (hne : cross u v ≠ 0) (hu : RayWall D.toDissection X u)
    (hv : RayWall D.toDissection X v)
    (hin : ∃ r > (0 : ℝ), sectorC X u v ∩ ball X r ⊆ D.target.carrier) {P Q : ℕ}
    (hPQ : P + Q = 1) (hang : InnerProductGeometry.angle u v = P * α + Q * β) :
    ∃ i, (∃ s > (0 : ℝ), ∃ t > (0 : ℝ), Set.range (D.tile i).pts = {X, X + s • u, X + t • v}) ∧
      HasAngle D i X (P * α + Q * β) ∧ (D.tile i).carrier ⊆ sectorC X u v := by
  classical
  have hsum := sector_sum D.toDissection hne hu hv hin
  have hF := fun i (hi : i ∈ sectorTiles D.toDissection X u v) =>
    mem_of_sectorTiles D.toDissection hi
  obtain ⟨i, hFi, hi⟩ := hS.sum_one hF hPQ (hsum.trans hang)
  obtain ⟨r, hr, hcov⟩ := sector_cover D.toDissection hne hin
  rw [hFi] at hcov
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left] at hcov
  obtain ⟨l, hl, -⟩ := id hi
  have hiF : i ∈ sectorTiles D.toDissection X u v := by rw [hFi]; exact Finset.mem_singleton_self i
  have hru := ray_points (ne_zero_left_of_cross hne) hr hcov
  have hrv := ray_points (ne_zero_right_of_cross hne) hr ((sectorC_swap X u v) ▸ hcov)
  obtain ⟨s, hs, hsu⟩ := ray_edge' D.toDissection (ne_zero_left_of_cross hne) hu hl hru
  obtain ⟨t, ht, htv⟩ := ray_edge' D.toDissection (ne_zero_right_of_cross hne) hv hl hrv
  obtain ⟨-, hrange⟩ := Tri.two_rays (D.tile i) hne hl hs ht hsu htv
  exact ⟨i, ⟨s, hs, t, ht, hrange⟩, hi, tile_subset_sector D.toDissection hne hu hv hiF hl⟩

omit hS in
theorem angleAt_eq_of_hasAngle {i : Fin N} {X : Plane} {θ : ℝ} (h : HasAngle D i X θ) {l : Fin 3}
    (hl : (D.tile i).pts l = X) : (D.tile i).angleAt l = θ := by
  obtain ⟨l', hl', ha⟩ := h
  rw [(D.tile i).indep.injective (hl.trans hl'.symm)]; exact ha

omit hS in
theorem localAngle_of_hasAngle {i : Fin N} {X : Plane} {θ : ℝ} (h : HasAngle D i X θ) :
    (D.tile i).localAngle X = θ := by
  obtain ⟨l, hl, ha⟩ := h
  rw [← hl, Tri.localAngle_vertex]; exact ha

/-- **A sector with a known tile along one ray**: if the rest of its angle is `α` or `β`, a
second tile has that angle at `X` and an edge along the other ray. -/
theorem sector_minus {X u v : Plane} (hne : cross u v ≠ 0) (hu : RayWall D.toDissection X u)
    (hv : RayWall D.toDissection X v)
    (hin : ∃ r > (0 : ℝ), sectorC X u v ∩ ball X r ⊆ D.target.carrier) {E : Fin N}
    (hE : E ∈ sectorTiles D.toDissection X u v) {θE : ℝ} (hEa : HasAngle D E X θE)
    (hEu : ∃ l, (D.tile E).pts l = X ∧ ∃ s > (0 : ℝ),
      (D.tile E).pts (l + 1) = X + s • u ∨ (D.tile E).pts (l + 2) = X + s • u)
    (hθ : θE ≠ InnerProductGeometry.angle u v) {P Q : ℕ} (hPQ : P + Q = 1)
    (hang : InnerProductGeometry.angle u v = θE + (P * α + Q * β)) :
    ∃ G, G ≠ E ∧ HasAngle D G X (P * α + Q * β) ∧
      (∃ l, (D.tile G).pts l = X ∧ ∃ t > (0 : ℝ),
        (D.tile G).pts (l + 1) = X + t • v ∨ (D.tile G).pts (l + 2) = X + t • v) ∧
      (D.tile G).carrier ⊆ sectorC X u v := by
  classical
  set F := sectorTiles D.toDissection X u v
  have hsum := sector_sum D.toDissection hne hu hv hin
  have hF := fun i (hi : i ∈ F) => mem_of_sectorTiles D.toDissection hi
  have hsum' : ∑ i ∈ F.erase E, (D.tile i).localAngle X = P * α + Q * β := by
    have := Finset.add_sum_erase F (fun i => (D.tile i).localAngle X) hE
    simp only at this
    rw [localAngle_of_hasAngle hEa] at this
    linarith
  obtain ⟨G, hFG, hG⟩ := hS.sum_one (fun i hi => hF i (Finset.mem_of_mem_erase hi)) hPQ hsum'
  have hGF : G ∈ F.erase E := by rw [hFG]; exact Finset.mem_singleton_self G
  have hGE : G ≠ E := Finset.ne_of_mem_erase hGF
  have hGF' : G ∈ F := Finset.mem_of_mem_erase hGF
  obtain ⟨r, hr, hcov⟩ := sector_cover D.toDissection hne hin
  rw [← sectorC_swap] at hcov
  obtain ⟨i, hi, hray⟩ := ray_tile D.toDissection (ne_zero_right_of_cross hne) hr hcov
  have hiEG : i = E ∨ i = G := by
    by_cases h : i = E
    · exact Or.inl h
    · right
      have : i ∈ F.erase E := Finset.mem_erase.mpr ⟨h, hi⟩
      rw [hFG] at this; exact Finset.mem_singleton.mp this
  rcases hiEG with rfl | rfl
  · exfalso
    obtain ⟨l, hl, s, hs, hsu⟩ := hEu
    obtain ⟨t, ht, htv⟩ := ray_edge' D.toDissection (ne_zero_right_of_cross hne) hv hl hray
    obtain ⟨hA, -⟩ := Tri.two_rays (D.tile i) hne hl hs ht hsu htv
    exact hθ ((angleAt_eq_of_hasAngle hEa hl).symm.trans hA)
  · obtain ⟨l, hl, -⟩ := id hG
    obtain ⟨t, ht, htv⟩ := ray_edge' D.toDissection (ne_zero_right_of_cross hne) hv hl hray
    exact ⟨i, hGE, hG, ⟨l, hl, t, ht, htv⟩,
      tile_subset_sector D.toDissection hne hu hv hGF' hl⟩

/-- **A sector of angle `α + 2β`** has a tile along each ray, these two tiles are different, each
has its angle `α` or `β` at `X`, and one of them has its `β` there. -/
theorem sector_two {X u v : Plane} (hne : cross u v ≠ 0) (hu : RayWall D.toDissection X u)
    (hv : RayWall D.toDissection X v)
    (hin : ∃ r > (0 : ℝ), sectorC X u v ∩ ball X r ⊆ D.target.carrier)
    (hang : InnerProductGeometry.angle u v = α + 2 * β) :
    ∃ Gu Gv, Gu ≠ Gv ∧
      (∃ l, (D.tile Gu).pts l = X ∧ ∃ s > (0 : ℝ),
        (D.tile Gu).pts (l + 1) = X + s • u ∨ (D.tile Gu).pts (l + 2) = X + s • u) ∧
      (∃ l, (D.tile Gv).pts l = X ∧ ∃ t > (0 : ℝ),
        (D.tile Gv).pts (l + 1) = X + t • v ∨ (D.tile Gv).pts (l + 2) = X + t • v) ∧
      (HasAngle D Gu X β ∨ HasAngle D Gv X β) ∧
      (HasAngle D Gu X α ∨ HasAngle D Gu X β) ∧ (HasAngle D Gv X α ∨ HasAngle D Gv X β) ∧
      (D.tile Gu).carrier ⊆ sectorC X u v ∧ (D.tile Gv).carrier ⊆ sectorC X u v := by
  classical
  set F := sectorTiles D.toDissection X u v
  have hsum := sector_sum D.toDissection hne hu hv hin
  have hF := fun i (hi : i ∈ F) => mem_of_sectorTiles D.toDissection hi
  obtain ⟨h1, h2⟩ := hS.sum_three hF (hsum.trans hang)
  obtain ⟨r, hr, hcov⟩ := sector_cover D.toDissection hne hin
  obtain ⟨Gu, hGu, hrayu⟩ := ray_tile D.toDissection (ne_zero_left_of_cross hne) hr hcov
  rw [← sectorC_swap] at hcov
  obtain ⟨Gv, hGv, hrayv⟩ := ray_tile D.toDissection (ne_zero_right_of_cross hne) hr hcov
  have hvert : ∀ i ∈ F, ∃ l, (D.tile i).pts l = X := by
    intro i hi
    rcases h1 i hi with ⟨l, hl, -⟩ | ⟨l, hl, -⟩ <;> exact ⟨l, hl⟩
  obtain ⟨lu, hlu⟩ := hvert Gu hGu
  obtain ⟨lv, hlv⟩ := hvert Gv hGv
  obtain ⟨s, hs, hsu⟩ := ray_edge' D.toDissection (ne_zero_left_of_cross hne) hu hlu hrayu
  obtain ⟨t, ht, htv⟩ := ray_edge' D.toDissection (ne_zero_right_of_cross hne) hv hlv hrayv
  have hne' : Gu ≠ Gv := by
    rintro rfl
    have : lv = lu := (D.tile Gu).indep.injective (hlv.trans hlu.symm)
    rw [this] at htv
    obtain ⟨hA, -⟩ := Tri.two_rays (D.tile Gu) hne hlu hs ht hsu htv
    rw [hang] at hA
    have hβ := hS.angles_pos.2.1
    have hα := hS.angles_pos.1
    rcases h1 Gu hGu with h | h
    · have := angleAt_eq_of_hasAngle h hlu; linarith
    · have := angleAt_eq_of_hasAngle h hlu; linarith
  exact ⟨Gu, Gv, hne', ⟨lu, hlu, s, hs, hsu⟩, ⟨lv, hlv, t, ht, htv⟩, h2 Gu hGu Gv hGv hne',
    h1 Gu hGu, h1 Gv hGv, tile_subset_sector D.toDissection hne hu hv hGu hlu,
    tile_subset_sector D.toDissection hne hu hv hGv hlv⟩

end Fill

end TriangleTiling.Prime
