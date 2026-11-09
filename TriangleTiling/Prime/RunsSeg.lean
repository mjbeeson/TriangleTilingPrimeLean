/-
Small facts about segments and tile edges, for Section 11 of Beeson–Roșu.
-/
import TriangleTiling.Prime.RunsLatFacts

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

/-- A segment along `w` through a point `P` strictly inside it contains `P + s w` for small
`s ≥ 0`. -/
theorem seg_ext {P A B w : Plane} (hw : w ≠ 0) (hAB : A ≠ B) {α β : ℝ} (hA : A = P + α • w)
    (hB : B = P + β • w) (hP : P ∈ openSegment ℝ A B) :
    ∃ ε > (0 : ℝ), ∀ s : ℝ, 0 ≤ s → s ≤ ε → P + s • w ∈ segment ℝ A B := by
  rw [openSegment_eq_image_lineMap] at hP
  obtain ⟨θ, ⟨h0, h1⟩, hθ⟩ := hP
  rw [AffineMap.lineMap_apply_module, hA, hB] at hθ
  have key : (α + θ * (β - α)) • w = 0 := by
    have : ((1 - θ) • (P + α • w) + θ • (P + β • w)) - P = (α + θ * (β - α)) • w := by
      simp only [smul_add, smul_smul]; module
    rw [← this, hθ, sub_self]
  have hk : α + θ * (β - α) = 0 := (smul_eq_zero.mp key).resolve_right hw
  have hne : α ≠ β := by
    rintro rfl; exact hAB (hA.trans hB.symm)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `α < 0 < β`
    have hβ : 0 < β := by nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hlt)]
    refine ⟨β, hβ, fun s hs hsβ => ?_⟩
    rw [segment_eq_image_lineMap]
    refine ⟨(s - α) / (β - α), ⟨div_nonneg (by nlinarith [mul_pos h0 (sub_pos.mpr hlt)]) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module, hA, hB]
    have hd : β - α ≠ 0 := by linarith
    have : (1 - (s - α) / (β - α)) • (P + α • w) + ((s - α) / (β - α)) • (P + β • w) =
        P + (α + (s - α) / (β - α) * (β - α)) • w := by
      simp only [smul_add, smul_smul]; module
    rw [this, div_mul_cancel₀ _ hd]; congr 2; ring
  · have hα : 0 < α := by nlinarith [mul_pos h0 (sub_pos.mpr hlt)]
    have hβ0 : β < 0 := by nlinarith [mul_pos hα (sub_pos.mpr h1)]
    refine ⟨α, hα, fun s hs hsα => ?_⟩
    rw [segment_eq_image_lineMap]
    refine ⟨(s - α) / (β - α), ⟨div_nonneg_of_nonpos (by linarith) (by linarith),
      (div_le_one_of_neg (by linarith)).mpr (by linarith)⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module, hA, hB]
    have hd : β - α ≠ 0 := by linarith
    have : (1 - (s - α) / (β - α)) • (P + α • w) + ((s - α) / (β - α)) • (P + β • w) =
        P + (α + (s - α) / (β - α) * (β - α)) • w := by
      simp only [smul_add, smul_smul]; module
    rw [this, div_mul_cancel₀ _ hd]; congr 2; ring

/-- Points `P + s w`, `0 ≤ s ≤ l`, lie on the segment from `P` to `P + l w`. -/
theorem mem_seg_smul {P w : Plane} {l s : ℝ} (hl : 0 < l) (hs : 0 ≤ s) (hsl : s ≤ l) :
    P + s • w ∈ segment ℝ P (P + l • w) := by
  rw [segment_eq_image_lineMap]
  refine ⟨s / l, ⟨div_nonneg hs hl.le, (div_le_one hl).mpr hsl⟩, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ s hl.ne']; abel

theorem mem_openSeg_smul {P w : Plane} {l s : ℝ} (hw : w ≠ 0) (hs : 0 < s) (hsl : s < l) :
    P + s • w ∈ openSegment ℝ P (P + l • w) := by
  have hl : 0 < l := hs.trans hsl
  rw [openSegment_eq_image_lineMap]
  refine ⟨s / l, ⟨div_pos hs hl, (div_lt_one hl).mpr hsl⟩, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  simp only [add_sub_cancel_left, smul_smul, div_mul_cancel₀ s hl.ne']; abel

/-- An edge between two vertices of a tile, as an indexed edge. -/
theorem edge_of_tileEdge {t : Fin N} {P Q : Plane} (h : TileEdge D t P Q) :
    ∃ e : Fin 3, (D.tile t).edge e = segment ℝ P Q ∧
      openSegment ℝ ((D.tile t).pts e) ((D.tile t).pts (e + 1)) = openSegment ℝ P Q ∧
      (((D.tile t).pts e = P ∧ (D.tile t).pts (e + 1) = Q) ∨
        ((D.tile t).pts e = Q ∧ (D.tile t).pts (e + 1) = P)) := by
  obtain ⟨e, he⟩ := tileEdge_edge h
  refine ⟨e, ?_, ?_, he⟩ <;> rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Tri.edge, h1, h2]
  · rw [Tri.edge, h1, h2, segment_symm]
  · rw [h1, h2]
  · rw [h1, h2, openSegment_symm]

/-- Two vertices of a tile given by its vertex set form an edge. -/
theorem tileEdge_of_range {t : Fin N} {P Q R : Plane} (h : Set.range (D.tile t).pts = {P, Q, R})
    {A B : Plane} (hA : A ∈ ({P, Q, R} : Set Plane)) (hB : B ∈ ({P, Q, R} : Set Plane))
    (hAB : A ≠ B) : TileEdge D t A B := by
  rw [← h] at hA hB
  obtain ⟨l, rfl⟩ := hA
  obtain ⟨l', rfl⟩ := hB
  exact ⟨l, l', fun e => hAB (by rw [e]), rfl, rfl⟩

/-- Points of an edge are in no tile's interior. -/
theorem not_interior_of_tileEdge {t : Fin N} {P Q y : Plane} (h : TileEdge D t P Q)
    (hy : y ∈ segment ℝ P Q) (i : Fin N) : y ∉ interior (D.tile i).carrier := by
  obtain ⟨e, he, -⟩ := edge_of_tileEdge h
  exact D.edge_point_not_interior (he ▸ hy) i

/-- A ray along an edge is a wall. -/
theorem rayWall_of_tileEdge {t : Fin N} {X w : Plane} {l : ℝ} (hl : 0 < l)
    (h : TileEdge D t X (X + l • w)) : RayWall D.toDissection X w := by
  obtain ⟨e, he, -⟩ := edge_of_tileEdge h
  exact rayWall_of_edge D.toDissection hl (he ▸ left_mem_segment ℝ _ _)
    (he ▸ right_mem_segment ℝ _ _)

theorem mem_range_of_tileEdge {t : Fin N} {P Q : Plane} (h : TileEdge D t P Q) :
    P ∈ Set.range (D.tile t).pts ∧ Q ∈ Set.range (D.tile t).pts := by
  obtain ⟨l, l', -, h1, h2⟩ := h; exact ⟨⟨l, h1⟩, ⟨l', h2⟩⟩

theorem mem_target_of_range {t : Fin N} {P : Plane} (h : P ∈ Set.range (D.tile t).pts) :
    P ∈ D.target.carrier := by
  obtain ⟨l, rfl⟩ := h; exact TwoCs.pts_mem_target D.toDissection _ _

end TriangleTiling.Prime
