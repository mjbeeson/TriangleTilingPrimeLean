/-
`theorem:isoscelesbeta` (Section 12 of Beeson–Roșu), the apex `B`: by `lemma:angles` there are
three tiles at `B`, each with its `α` there; the outer two have their `c` edges on `AB` and `BC`
(no `b` edges there, `lemma:isoscelesnob`) and their `b` edges against the middle tile; the
middle tile's `c` edge is against the `b` edge of one of them. So the hypothesis of
`lemma:longrun` holds for `AB` or for `BC` (`apex_endHyp`).
-/
import TriangleTiling.Prime.IsoBetaB

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

/-- Two tiles with an edge along the same ray from `X`, on the side of a line through `X` where
`T` lies, are the same tile. -/
theorem same_side_unique {t t' : Fin N} {X w : Plane} {κ : ℝ} (hκ : κ ≠ 0) (hw : w ≠ 0)
    (hall : ∀ y ∈ D.target.carrier, 0 ≤ κ * cross w (y - X)) {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') (h : TileEdge D t X (X + s • w)) (h' : TileEdge D t' X (X + s' • w)) :
    t = t' := by
  by_contra hne
  have hopp := opposite_of_ray hne hw hs hs' h h'
  have hline : ∀ (u : Fin N) (σ : ℝ), 0 < σ → TileEdge D u X (X + σ • w) →
      ∃ Z ∈ Set.range (D.tile u).pts, cross w (Z - X) ≠ 0 := by
    intro u σ hσ hu
    by_contra hno
    push Not at hno
    apply two_vertices_on_line (D.tile u) (crossL w) (cross w X) (crossL_ne_zero hw)
    intro i
    have := hno _ ⟨i, rfl⟩
    rw [crossL_apply]; rw [cross_sub_right] at this; linarith
  obtain ⟨Z, hZ, hZ0⟩ := hline t' s' hs' h'
  obtain ⟨Y, hY, hY0⟩ := hline t s hs h
  have h1 := hopp Y hY Z hZ
  have hYT := hall Y (by obtain ⟨l, rfl⟩ := hY; exact TwoCs.pts_mem_target D.toDissection _ _)
  have hZT := hall Z (by obtain ⟨l, rfl⟩ := hZ; exact TwoCs.pts_mem_target D.toDissection _ _)
  have h2 : 0 ≤ (κ * cross w (Y - X)) * (κ * cross w (Z - X)) := mul_nonneg hYT hZT
  have h3 : (κ * cross w (Y - X)) * (κ * cross w (Z - X)) =
      κ ^ 2 * (cross w (Y - X) * cross w (Z - X)) := by ring
  have hκ2 : 0 < κ ^ 2 := by positivity
  have h4 : cross w (Y - X) * cross w (Z - X) = 0 := by nlinarith
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact hY0 h5
  · exact hZ0 h5

/-- Edge vectors at a vertex of a tile are not parallel. -/
theorem cross_ne_of_tileEdges {t : Fin N} {X u w : Plane} {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ)
    (hu : TileEdge D t X (X + s • u)) (hw : TileEdge D t X (X + σ • w))
    (hne : X + s • u ≠ X + σ • w) : cross u w ≠ 0 := by
  intro h0
  have hu0 : u ≠ 0 := by
    rintro rfl
    obtain ⟨l, l', hll, h1, h2⟩ := hu
    simp only [smul_zero, add_zero] at h2
    exact hll ((D.tile t).indep.injective (h1.trans h2.symm))
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hu0 h0
  apply two_vertices_on_line (D.tile t) (crossL u) (cross u X) (crossL_ne_zero hu0)
  obtain ⟨l1, l2, h12, e1, e2⟩ := hu
  obtain ⟨l1', l3, h13, e1', e3⟩ := hw
  have hl : l1' = l1 := (D.tile t).indep.injective (e1'.trans e1.symm)
  subst hl
  have h23 : l2 ≠ l3 := by intro h; rw [h] at e2; exact hne (e2.symm.trans e3)
  intro i
  rw [crossL_apply]
  have : i = l1' ∨ i = l2 ∨ i = l3 := by
    revert h12 h13 h23; fin_cases i <;> fin_cases l1' <;> fin_cases l2 <;> fin_cases l3 <;> decide
  rcases this with rfl | rfl | rfl
  · rw [e1']
  · rw [e2, cross_add_right, cross_smul_right, Erdos634.Geometry.cross_self]; ring
  · rw [e3, cross_add_right, cross_smul_right, hτ, cross_smul_right,
      Erdos634.Geometry.cross_self]; ring

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- No tile has its `α` angle at a vertex of `T` with angle `β`. -/
theorem no_alpha_at {l : Fin 3} (hl : D.target.angleAt l = β) {t : Fin N}
    (h : HasAngle D t (D.target.pts l) α) : False := by
  have htot : D.target.localAngle (D.target.pts l) = ((0 : ℕ) : ℝ) * α + ((1 : ℕ) : ℝ) * β := by
    rw [Tri.localAngle_vertex]; simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add]
    exact hl
  have := hS.sum_le_count htot {t} (p := 1) (q := 0)
    (by rw [Finset.sum_singleton, localAngle_of_hasAngle h]; simp)
  omega

/-- At a vertex of `T` with angle `3α`, the tiles there are three, each with its `α` angle. -/
theorem three_alpha {X : Plane} {F : Finset (Fin N)} (hF : ∀ i ∈ F, X ∈ (D.tile i).carrier)
    (hsum : ∑ i ∈ F, (D.tile i).localAngle X = 3 * α) :
    (∀ i ∈ F, HasAngle D i X α) ∧ F.card = 3 := by
  classical
  choose p q hpq hcase hhas using fun (i : F) => hS.combo (hF i i.2)
  set p' : Fin N → ℕ := fun i => if h : i ∈ F then p ⟨i, h⟩ else 0
  set q' : Fin N → ℕ := fun i => if h : i ∈ F then q ⟨i, h⟩ else 0
  have hsum' : ∑ i ∈ F, (D.tile i).localAngle X =
      (∑ i ∈ F, p' i : ℕ) * α + (∑ i ∈ F, q' i : ℕ) * β := by
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [p', q', dif_pos hi]
    exact hpq ⟨i, hi⟩
  obtain ⟨e1, e2⟩ := hS.uniq (u := 3) (v := 0) (by rw [← hsum', hsum]; push_cast; ring)
  have hq0 : ∀ i ∈ F, q' i = 0 := fun i hi => by
    have := Finset.single_le_sum (f := q') (fun _ _ => Nat.zero_le _) hi; omega
  have h10 : ∀ i ∈ F, p' i = 1 := by
    intro i hi
    have := hq0 i hi
    simp only [p', q', dif_pos hi] at this ⊢
    rcases hcase ⟨i, hi⟩ with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> omega
  refine ⟨fun i hi => ?_, ?_⟩
  · have := hhas ⟨i, hi⟩
    have h1 := h10 i hi; have h2 := hq0 i hi
    simp only [p', q', dif_pos hi] at h1 h2
    rw [h1, h2] at this; simpa using this (by omega)
  · rw [Finset.sum_congr rfl h10] at e1; simpa using e1

/-- **An outer tile at the apex.** A tile at the apex `B` with its `α` there and an edge along the
side towards the vertex `pts l'`, where that side has no `b` edges, has its `c` edge on that side
and its `b` edge from `B` to its `γ` vertex `W`. -/
theorem outer_tile {G : Fin N} {l' : Fin 3} (hl' : l' ≠ 1) (hGα : HasAngle D G (D.target.pts 1) α)
    {s : ℝ} (hs : 0 < s)
    (hGe : TileEdge D G (D.target.pts 1)
      (D.target.pts 1 + s • (D.target.pts l' - D.target.pts 1)))
    (hnob : ∀ (P Q : Plane), TileEdge D G P Q →
      segment ℝ P Q ⊆ segment ℝ (D.target.pts 1) (D.target.pts l') → dist P Q ≠ b) :
    dist (D.target.pts 1) (D.target.pts 1 + s • (D.target.pts l' - D.target.pts 1)) = c ∧
      ∃ W, HasAngle D G W γ ∧ TileEdge D G (D.target.pts 1) W ∧ dist (D.target.pts 1) W = b := by
  set B := D.target.pts 1
  have hαβ := hS.alpha_ne_beta
  have hαγ : α ≠ γ := by have := hS.gamma; have := hS.angles_pos; intro h; linarith
  have hβγ : β ≠ γ := by have := hS.gamma; have := hS.angles_pos; intro h; linarith
  -- `s ≤ 1`: the edge lies on the side
  have hPT : B + s • (D.target.pts l' - B) ∈ D.target.carrier :=
    mem_target_of_range (mem_range_of_tileEdge hGe).2
  have hs1 := le_one_of_mem D.target (Ne.symm hl') hPT
  have hsub : segment ℝ B (B + s • (D.target.pts l' - B)) ⊆ segment ℝ B (D.target.pts l') := by
    apply (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨hs.le, hs1⟩, by rw [AffineMap.lineMap_apply_module']; abel⟩
  obtain ⟨ea, -, -⟩ := hS.edge_ends hGe
  have hc' : dist B (B + s • (D.target.pts l' - B)) = c := by
    rcases hS.tileEdge_len hGe with hd | hd | hd
    · rcases ea hd with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (angle_eq_of_two hGα h1) hαβ
      · exact absurd (angle_eq_of_two hGα h1) hαγ
    · exact absurd hd (hnob _ _ hGe hsub)
    · exact hd
  refine ⟨hc', ?_⟩
  obtain ⟨W, hW⟩ := hS.exists_gamma G
  have hBW : TileEdge D G B W := by
    obtain ⟨l, hl, ha⟩ := hGα
    obtain ⟨l2, hl2, ha2⟩ := hW
    exact ⟨l, l2, fun h => hαγ (by rw [← ha, ← ha2, h]), hl, hl2⟩
  refine ⟨W, hW, hBW, ?_⟩
  obtain ⟨ea', eb', ec'⟩ := hS.edge_ends hBW
  rcases hS.tileEdge_len hBW with hd | hd | hd
  · rcases ea' hd with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (angle_eq_of_two hGα h1) hαβ
    · exact absurd (angle_eq_of_two hGα h1) hαγ
  · exact hd
  · rcases ec' hd with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact absurd (angle_eq_of_two hW h2).symm hβγ
    · exact absurd (angle_eq_of_two hGα h1) hαβ

end RunSetting

end TriangleTiling.Prime
