/-
`theorem:isoscelesbeta`, the apex `B`, continued: the middle tile, and the hypothesis of
`lemma:longrun` for `AB` or `BC` (`apex_endHyp`).
-/
import TriangleTiling.Prime.IsoBetaApex

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

set_option maxHeartbeats 3200000 in
/-- **The apex.** If no tile has a `b` edge on `AB` or `BC`, the hypothesis of `lemma:longrun`
holds for `AB` or for `BC`. -/
theorem apex_endHyp
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    (hnob : ∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
      (segment ℝ P Q ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
        segment ℝ P Q ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) → dist P Q ≠ b) :
    EndHyp D 0 α γ a c ∨ EndHyp D 1 α γ a c := by
  classical
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  have hαβ := hS.alpha_ne_beta
  have hαγ : α ≠ γ := by intro h; linarith
  set A := D.target.pts 0
  set B := D.target.pts 1
  set C := D.target.pts 2
  set u := C - B
  set v := A - B
  have hne : cross u v ≠ 0 := by
    have := D.target.det_ne_zero
    rw [← D.target.cross_edgeVec 1, Tri.edgeVec_eq, Tri.edgeVec'_eq] at this; exact this
  have hu0 : u ≠ 0 := ne_zero_left_of_cross hne
  have hv0 : v ≠ 0 := ne_zero_right_of_cross hne
  have hang : InnerProductGeometry.angle u v = 3 * α := by
    rw [← hshape.2.1]; unfold Tri.angleAt; rw [Tri.cornerAngle_eq_angle]; rfl
  obtain ⟨hu, hv⟩ := vertex_rayWall D.toDissection 1
  change RayWall D.toDissection B u at hu
  change RayWall D.toDissection B v at hv
  obtain ⟨r₀, hr₀, hin⟩ := vertex_hin D.target 1
  change sectorC B u v ∩ ball B r₀ ⊆ D.target.carrier at hin
  set F := sectorTiles D.toDissection B u v
  have hsumF := sector_sum D.toDissection hne hu hv ⟨r₀, hr₀, hin⟩
  rw [hang] at hsumF
  have hF := fun i (hi : i ∈ F) => mem_of_sectorTiles D.toDissection hi
  obtain ⟨hFα, hF3⟩ := hS.three_alpha hF hsumF
  -- every tile at `B` is in `F`
  have hall : ∀ i, B ∈ (D.tile i).carrier → i ∈ F := by
    intro i hi
    by_contra hiF
    have htot := Finset.sum_add_sum_compl F (fun i => (D.tile i).localAngle B)
    rw [D.sum_localAngle_eq, Tri.localAngle_vertex] at htot
    change Finset.sum F _ + _ = D.target.angleAt 1 at htot
    rw [hsumF, hshape.2.1] at htot
    have h0 : ∑ i ∈ Fᶜ, (D.tile i).localAngle B = 0 := by linarith
    have hle := Finset.single_le_sum (f := fun i => (D.tile i).localAngle B)
      (fun i _ => (D.tile i).localAngle_nonneg B) (Finset.mem_compl.mpr hiF)
    obtain ⟨p, q, hpq, hcase, -⟩ := hS.combo hi
    simp only at hle
    rw [hpq] at hle
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rw [h1, h2] at hle <;> push_cast at hle <;> linarith
  obtain ⟨r, hr, hcov⟩ := sector_cover D.toDissection hne ⟨r₀, hr₀, hin⟩
  obtain ⟨G3, hG3F, hray3⟩ := ray_tile D.toDissection hu0 hr hcov
  rw [← sectorC_swap] at hcov
  obtain ⟨G1, hG1F, hray1⟩ := ray_tile D.toDissection hv0 hr hcov
  rw [sectorC_swap] at hcov
  have hG1α := hFα G1 hG1F
  have hG3α := hFα G3 hG3F
  obtain ⟨l1, hl1, -⟩ := id hG1α
  obtain ⟨l3, hl3, -⟩ := id hG3α
  obtain ⟨s1, hs1, hG1v⟩ := ray_edge' D.toDissection hv0 hv hl1 hray1
  obtain ⟨s3, hs3, hG3u⟩ := ray_edge' D.toDissection hu0 hu hl3 hray3
  have te1 : TileEdge D G1 B (B + s1 • v) := by
    rcases hG1v with h | h
    · exact ⟨l1, l1 + 1, fin3_ne_succ l1, hl1, h⟩
    · exact ⟨l1, l1 + 2, by fin_cases l1 <;> decide, hl1, h⟩
  have te3 : TileEdge D G3 B (B + s3 • u) := by
    rcases hG3u with h | h
    · exact ⟨l3, l3 + 1, fin3_ne_succ l3, hl3, h⟩
    · exact ⟨l3, l3 + 2, by fin_cases l3 <;> decide, hl3, h⟩
  obtain ⟨hc1, W1, hW1, te1W, hb1⟩ := hS.outer_tile (l' := 0) (by decide) hG1α hs1 te1
    (fun P Q h hs => hnob G1 P Q h (Or.inl (by rw [segment_symm ℝ A]; exact hs)))
  obtain ⟨hc3, W3, hW3, te3W, hb3⟩ := hS.outer_tile (l' := 2) (by decide) hG3α hs3 te3
    (fun P Q h hs => hnob G3 P Q h (Or.inr hs))
  set r1 := W1 - B
  set r2 := W3 - B
  have hW1r : W1 = B + (1 : ℝ) • r1 := by simp [r1]
  have hW3r : W3 = B + (1 : ℝ) • r2 := by simp [r2]
  have te1r : TileEdge D G1 B (B + (1 : ℝ) • r1) := hW1r ▸ te1W
  have te3r : TileEdge D G3 B (B + (1 : ℝ) • r2) := hW3r ▸ te3W
  have hb' : 0 < b := hS.b_pos
  have hc' : 0 < c := hS.c_pos
  have hbc : b ≠ c := hS.b_lt_c.ne
  -- the angles of the outer tiles at `B`
  have hne1v : B + s1 • v ≠ B + (1 : ℝ) • r1 := by
    intro h; rw [← hW1r] at h; rw [h, hb1] at hc1; exact hbc hc1
  have hne3u : B + s3 • u ≠ B + (1 : ℝ) • r2 := by
    intro h; rw [← hW3r] at h; rw [h, hb3] at hc3; exact hbc hc3
  have hcv1 := cross_ne_of_tileEdges hs1 one_pos te1 te1r hne1v
  have hcu3 := cross_ne_of_tileEdges hs3 one_pos te3 te3r hne3u
  have hidx : ∀ {t : Fin N} {l : Fin 3} {X P : Plane}, (D.tile t).pts l = X → TileEdge D t X P →
      (D.tile t).pts (l + 1) = P ∨ (D.tile t).pts (l + 2) = P := by
    intro t l X P hl hte
    obtain ⟨l', l'', hll, h1, h2⟩ := hte
    have : l' = l := (D.tile t).indep.injective (h1.trans hl.symm)
    subst this
    have : l'' = l' + 1 ∨ l'' = l' + 2 := by revert hll; fin_cases l' <;> fin_cases l'' <;> decide
    rcases this with rfl | rfl
    · exact Or.inl h2
    · exact Or.inr h2
  have ang1 : InnerProductGeometry.angle v r1 = α := by
    have := (Tri.two_rays (D.tile G1) hcv1 hl1 hs1 one_pos hG1v (hidx hl1 te1r)).1
    rw [← this]; exact angleAt_eq_of_hasAngle hG1α hl1
  have ang3 : InnerProductGeometry.angle u r2 = α := by
    have := (Tri.two_rays (D.tile G3) hcu3 hl3 hs3 one_pos hG3u (hidx hl3 te3r)).1
    rw [← this]; exact angleAt_eq_of_hasAngle hG3α hl3
  -- `r1, r2` lie in the cone of `u, v`
  have hcone : ∀ {t : Fin N}, t ∈ F → ∀ {Y : Plane}, Y ∈ Set.range (D.tile t).pts →
      0 ≤ cross u (Y - B) * cross u v ∧ 0 ≤ cross (Y - B) v * cross u v := by
    intro t ht Y hY
    obtain ⟨lt, hlt, -⟩ := hFα t ht
    exact tile_subset_sector D.toDissection hne hu hv ht hlt (subset_convexHull ℝ _ hY)
  have hr1c := hcone hG1F (mem_range_of_tileEdge te1W).2
  have hr2c := hcone hG3F (mem_range_of_tileEdge te3W).2
  have hr10 : r1 ≠ 0 := by
    intro h; have : W1 = B := by rw [hW1r, h, smul_zero, add_zero]
    rw [this, dist_self] at hb1; linarith
  have hr20 : r2 ≠ 0 := by
    intro h; have : W3 = B := by rw [hW3r, h, smul_zero, add_zero]
    rw [this, dist_self] at hb3; linarith
  have hπ3 : α < π / 3 := by linarith
  -- angles at `B`: `∠(u, r1) = 2α`, `∠(r2, v) = 2α`
  have aur1 : InnerProductGeometry.angle u r1 = 2 * α := by
    have := angle_add_cone hne hr10 hr1c
    rw [hang, InnerProductGeometry.angle_comm r1 v, ang1] at this; linarith
  have ar2v : InnerProductGeometry.angle r2 v = 2 * α := by
    have := angle_add_cone hne hr20 hr2c
    rw [hang, ang3] at this; linarith
  have hsin2 : 0 < Real.sin (2 * α) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcur1 : cross u r1 ≠ 0 := by
    intro h0; have := sin_angle_eq hu0 hr10; rw [aur1, h0, abs_zero, zero_div] at this; linarith
  have hcvr2 : cross v r2 ≠ 0 := by
    intro h0; have := sin_angle_eq hv0 hr20
    rw [InnerProductGeometry.angle_comm, ar2v, h0, abs_zero, zero_div] at this; linarith
  have hvr2 : InnerProductGeometry.angle v r2 = 2 * α := by
    rw [InnerProductGeometry.angle_comm]; exact ar2v
  have hu1 : RayWall D.toDissection B r1 := rayWall_of_tileEdge one_pos te1r
  have hu2 : RayWall D.toDissection B r2 := rayWall_of_tileEdge one_pos te3r
  have hCC : 0 < cross u v * cross u v := mul_self_pos.mpr hne
  -- the order of vertices at `B`
  have hord : ∀ {t : Fin N} {l : Fin 3} {P Z : Plane}, (D.tile t).pts l = B → P ≠ Z →
      ((D.tile t).pts (l + 1) = P ∨ (D.tile t).pts (l + 2) = P) →
      ((D.tile t).pts (l + 1) = Z ∨ (D.tile t).pts (l + 2) = Z) →
      ((D.tile t).pts (l + 1) = P ∧ (D.tile t).pts (l + 2) = Z) ∨
        ((D.tile t).pts (l + 2) = P ∧ (D.tile t).pts (l + 1) = Z) := by
    intro t l P Z _ hPZ h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.symm.trans h2) hPZ
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.symm.trans h2) hPZ
  -- first sector: `u, r1`, minus `G3`
  have hin1 : ∃ r > (0 : ℝ), sectorC B u r1 ∩ ball B r ⊆ D.target.carrier := by
    refine ⟨r₀, hr₀, fun y hy => hin ⟨sectorC_mono hne hcur1 ?_ hy.1, hy.2⟩⟩
    rw [mem_sectorC, add_sub_cancel_left]; exact hr1c
  have hE1 : G3 ∈ sectorTiles D.toDissection B u r1 := by
    have hp := hord hl3 hne3u.symm.symm hG3u (hidx hl3 te3r)
    refine mem_sectorTiles_of_edge D.toDissection hl3 hs3 hp ?_
    rw [add_sub_cancel_left, one_smul]
    have h1 : 0 < cross u r2 * cross u v := lt_of_le_of_ne hr2c.1
      (fun h => (mul_ne_zero hcu3 hne) h.symm)
    have h2 : 0 < cross u r1 * cross u v := lt_of_le_of_ne hr1c.1
      (fun h => (mul_ne_zero hcur1 hne) h.symm)
    have := mul_pos h1 h2
    have e : cross u r2 * cross u v * (cross u r1 * cross u v) =
        (cross u r2 * cross u r1) * (cross u v * cross u v) := by ring
    rw [e] at this
    exact pos_of_mul_pos_left this hCC.le
  obtain ⟨G, hGG3, hGα, ⟨lG, hlG, τ, hτ, hGr1⟩, hGsub⟩ := sector_minus hS hcur1 hu hu1 hin1 hE1
    hG3α ⟨l3, hl3, s3, hs3, hG3u⟩ (by rw [aur1]; intro h; linarith) (P := 1) (Q := 0)
    (by norm_num) (by rw [aur1]; push_cast; ring)
  have hGα' : HasAngle D G B α := by simpa using hGα
  have hGG1 : G ≠ G1 := by
    intro h
    rw [h] at hGsub
    have hv1 : B + s1 • v ∈ sectorC B u r1 :=
      hGsub (subset_convexHull ℝ _ (mem_range_of_tileEdge te1).2)
    have := sectorC_smul hv1 (t := s1⁻¹) (inv_nonneg.mpr hs1.le)
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs1.ne', one_smul, mem_sectorC,
      add_sub_cancel_left] at this
    have := angle_add_cone hcur1 hv0 this
    rw [aur1, hang, ang1] at this; linarith
  -- second sector: `v, r2`, minus `G1`
  have hne' : cross v u ≠ 0 := by rw [cross_swap]; exact neg_ne_zero.mpr hne
  have hr2c' : 0 ≤ cross v r2 * cross v u ∧ 0 ≤ cross r2 u * cross v u := by
    have e1 : cross v r2 * cross v u = cross r2 v * cross u v := by
      rw [cross_swap v r2, cross_swap v u]; ring
    have e2 : cross r2 u * cross v u = cross u r2 * cross u v := by
      rw [cross_swap r2 u, cross_swap v u]; ring
    rw [e1, e2]; exact ⟨hr2c.2, hr2c.1⟩
  have hr1c' : 0 ≤ cross v r1 * cross v u ∧ 0 ≤ cross r1 u * cross v u := by
    have e1 : cross v r1 * cross v u = cross r1 v * cross u v := by
      rw [cross_swap v r1, cross_swap v u]; ring
    have e2 : cross r1 u * cross v u = cross u r1 * cross u v := by
      rw [cross_swap r1 u, cross_swap v u]; ring
    rw [e1, e2]; exact ⟨hr1c.2, hr1c.1⟩
  have hin2 : ∃ r > (0 : ℝ), sectorC B v r2 ∩ ball B r ⊆ D.target.carrier := by
    refine ⟨r₀, hr₀, fun y hy => hin ⟨?_, hy.2⟩⟩
    rw [← sectorC_swap]
    refine sectorC_mono hne' hcvr2 ?_ hy.1
    rw [mem_sectorC, add_sub_cancel_left]; exact hr2c'
  have hcv1' : cross v r1 ≠ 0 := hcv1
  have hE2 : G1 ∈ sectorTiles D.toDissection B v r2 := by
    have hp := hord hl1 hne1v hG1v (hidx hl1 te1r)
    refine mem_sectorTiles_of_edge D.toDissection hl1 hs1 hp ?_
    rw [add_sub_cancel_left, one_smul]
    have h1 : 0 < cross v r1 * cross v u := lt_of_le_of_ne hr1c'.1
      (fun h => (mul_ne_zero hcv1' hne') h.symm)
    have h2 : 0 < cross v r2 * cross v u := lt_of_le_of_ne hr2c'.1
      (fun h => (mul_ne_zero hcvr2 hne') h.symm)
    have := mul_pos h1 h2
    have e : cross v r1 * cross v u * (cross v r2 * cross v u) =
        (cross v r1 * cross v r2) * (cross v u * cross v u) := by ring
    rw [e] at this
    exact pos_of_mul_pos_left this (mul_self_nonneg _)
  obtain ⟨G', hG'G1, hG'α, ⟨lG', hlG', τ', hτ', hG'r2⟩, hG'sub⟩ := sector_minus hS hcvr2 hv hu2
    hin2 hE2 hG1α ⟨l1, hl1, s1, hs1, hG1v⟩ (by rw [hvr2]; intro h; linarith) (P := 1) (Q := 0)
    (by norm_num) (by rw [hvr2]; push_cast; ring)
  have hG'G3 : G' ≠ G3 := by
    intro h
    rw [h] at hG'sub
    have hv3 : B + s3 • u ∈ sectorC B v r2 :=
      hG'sub (subset_convexHull ℝ _ (mem_range_of_tileEdge te3).2)
    have := sectorC_smul hv3 (t := s3⁻¹) (inv_nonneg.mpr hs3.le)
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs3.ne', one_smul, mem_sectorC,
      add_sub_cancel_left] at this
    have := angle_add_cone hcvr2 hu0 this
    rw [hvr2, InnerProductGeometry.angle_comm v u, hang, ang3] at this; linarith
  -- `G' = G`: the three tiles at `B`
  have hG'α' : HasAngle D G' B α := by simpa using hG'α
  have hGF : G ∈ F := by
    obtain ⟨l, hl, -⟩ := hGα'
    exact hall G (hl ▸ subset_convexHull ℝ _ ⟨l, rfl⟩)
  have hG'F : G' ∈ F := by
    obtain ⟨l, hl, -⟩ := hG'α'
    exact hall G' (hl ▸ subset_convexHull ℝ _ ⟨l, rfl⟩)
  have h13 : G1 ≠ G3 := by
    intro h
    rw [h] at hG1v hl1
    have : l1 = l3 := (D.tile G3).indep.injective (hl1.trans hl3.symm)
    rw [this] at hG1v
    have hcuv : cross v u ≠ 0 := hne'
    have := (Tri.two_rays (D.tile G3) hcuv hl3 hs1 hs3 hG1v hG3u).1
    rw [angleAt_eq_of_hasAngle hG3α hl3, InnerProductGeometry.angle_comm, hang] at this
    linarith
  have hsub3 : ({G1, G3, G} : Finset (Fin N)) ⊆ F := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard3 : ({G1, G3, G} : Finset (Fin N)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h13, hGG1.symm]),
      Finset.card_pair (Ne.symm hGG3)]
  have hFeq := Finset.eq_of_subset_of_card_le hsub3 (by rw [hF3, hcard3])
  have hG'G : G' = G := by
    have := hG'F; rw [← hFeq] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact absurd h hG'G1
    · exact absurd h hG'G3
    · exact h
  subst hG'G
  have hll : lG' = lG := (D.tile G').indep.injective (hlG'.trans hlG.symm)
  rw [hll] at hG'r2
  -- `r1, r2` are not parallel
  have hr12 : cross r1 r2 ≠ 0 := by
    intro h0
    obtain ⟨μ, hμ⟩ := parallel_of_cross_eq_zero hr10 h0
    rcases lt_trichotomy μ 0 with hμ0 | hμ0 | hμ0
    · have : InnerProductGeometry.angle u r2 = π - InnerProductGeometry.angle u r1 := by
        rw [hμ, InnerProductGeometry.angle_smul_right_of_neg _ _ hμ0,
          InnerProductGeometry.angle_neg_right]
      rw [ang3, aur1] at this; linarith
    · rw [hμ0, zero_smul] at hμ; exact hr20 hμ
    · have : InnerProductGeometry.angle u r2 = InnerProductGeometry.angle u r1 := by
        rw [hμ, InnerProductGeometry.angle_smul_right_of_pos _ _ hμ0]
      rw [ang3, aur1] at this; linarith
  obtain ⟨-, hGr⟩ := Tri.two_rays (D.tile G') hr12 hlG hτ hτ' hGr1 hG'r2
  have hd1 : dist B (B + τ • r1) = τ * ‖r1‖ := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.le]
  have hn1 : B ≠ B + τ • r1 := by
    intro h; have : τ • r1 = 0 := by rw [← add_right_inj B, ← h, add_zero]
    exact smul_ne_zero hτ.ne' hr10 this
  have hn2 : B ≠ B + τ' • r2 := by
    intro h; have : τ' • r2 = 0 := by rw [← add_right_inj B, ← h, add_zero]
    exact smul_ne_zero hτ'.ne' hr20 this
  have hn12 : B + τ • r1 ≠ B + τ' • r2 := by
    intro h
    have e : τ • r1 = τ' • r2 := by rw [← add_right_inj B, h]
    have := congrArg (cross r1) e
    rw [cross_smul_right, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero] at this
    exact (mul_ne_zero hτ'.ne' hr12) this.symm
  have hGe1 : TileEdge D G' B (B + τ • r1) := tileEdge_of_range hGr (by simp) (by simp) hn1
  have hGe2 : TileEdge D G' B (B + τ' • r2) := tileEdge_of_range hGr (by simp) (by simp) hn2
  -- the side `S` of `T` lies on one side of its line
  have hAB : ∀ y ∈ D.target.carrier, 0 ≤ -cross (B - A) (C - A) * cross v (y - B) := by
    intro y hy
    have := target_side D.target 0 y hy
    have e : cross v (y - B) = -cross (B - A) (y - A) := by
      simp only [v, cross, PiLp.sub_apply]; ring
    rw [e]; change 0 ≤ cross (B - A) (C - A) * cross (B - A) (y - A) at this; linarith
  have hBC : ∀ y ∈ D.target.carrier, 0 ≤ cross u (A - B) * cross u (y - B) := by
    intro y hy; exact target_side D.target 1 y hy
  have hκ1 : -cross (B - A) (C - A) ≠ 0 := by
    have := D.target.det_ne_zero; rw [← D.target.cross_edgeVec 0, Tri.edgeVec_eq,
      Tri.edgeVec'_eq] at this; exact neg_ne_zero.mpr this
  have hκ2 : cross u (A - B) ≠ 0 := hne
  have hseg : ∀ {X Y P : Plane}, P ∈ segment ℝ X Y → ∃ σ : ℝ, 0 ≤ σ ∧ P = X + σ • (Y - X) := by
    intro X Y P hP
    rw [segment_eq_image_lineMap] at hP
    obtain ⟨σ, ⟨h0, -⟩, rfl⟩ := hP
    exact ⟨σ, h0, by rw [AffineMap.lineMap_apply_module']; abel⟩
  have hGα'' : HasAngle D G' B α := hG'α'
  rcases hS.alpha_pair hGα'' hGr hn1 hn2 hn12 with ⟨-, hc''⟩ | ⟨hc'', -⟩
  · -- the middle tile's `c` edge is against the `b` edge of `G3`: side `BC`
    right
    intro R V P W hV hRα hRP hdc hsub hRW
    rcases hV with hV | hV
    · subst hV
      obtain ⟨σ, hσ0, hP⟩ := hseg (hsub (right_mem_segment ℝ _ _))
      have hσ : 0 < σ := by
        rcases hσ0.lt_or_eq with h | h
        · exact h
        · rw [← h, zero_smul, add_zero] at hP; rw [hP, dist_self] at hdc; linarith
      rw [hP] at hRP
      have hR := same_side_unique hκ2 hu0 hBC hσ hs3 hRP te3
      subst hR
      have hWW := hS.hasAngle_unique hRW hW3
      subst hWW
      exact ⟨G', hGG3, B + τ' • r2, ⟨τ', hτ', rfl⟩, hGe2, Or.inr hc''⟩
    · exfalso
      have hV' : V = D.target.pts 2 := hV
      subst hV'
      exact hS.no_alpha_at hshape.2.2 hRα
  · -- the middle tile's `c` edge is against the `b` edge of `G1`: side `AB`
    left
    intro R V P W hV hRα hRP hdc hsub hRW
    rcases hV with hV | hV
    · exfalso
      subst hV
      exact hS.no_alpha_at hshape.1 hRα
    · have hV' : V = B := hV
      subst hV'
      have hsub' : segment ℝ B P ⊆ segment ℝ B A := by rw [segment_symm ℝ B A]; exact hsub
      obtain ⟨σ, hσ0, hP⟩ := hseg (hsub' (right_mem_segment ℝ _ _))
      have hσ : 0 < σ := by
        rcases hσ0.lt_or_eq with h | h
        · exact h
        · rw [← h, zero_smul, add_zero] at hP; rw [hP, dist_self] at hdc; linarith
      rw [hP] at hRP
      have hR := same_side_unique hκ1 hv0 hAB hσ hs1 hRP te1
      subst hR
      have hWW := hS.hasAngle_unique hRW hW1
      subst hWW
      exact ⟨G', hGG1, B + τ • r1, ⟨τ, hτ, rfl⟩, hGe1, Or.inr hc''⟩

end RunSetting

end TriangleTiling.Prime
