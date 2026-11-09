/-
Tools for `theorem:isoscelesbeta` (Section 12 of Beeson–Roșu): rays along the sides of `T`, the
sector of `T` at a vertex, the tiles at a vertex, edge counts on a side including a run, and the
two sides at a `β` corner.
-/
import TriangleTiling.Prime.AngleAdd

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ}

/-- Points of a side of `T` are in no tile's interior. -/
theorem side_not_interior (D : Dissection N) (l : Fin 3) {y : Plane}
    (hy : y ∈ segment ℝ (D.target.pts l) (D.target.pts (l + 1))) (i : Fin N) :
    y ∉ interior (D.tile i).carrier := by
  intro hi
  have hT : y ∈ interior D.target.carrier := interior_mono (tile_subset_target D i) hi
  have h0 := D.target.coord_eq_zero_of_mem_edge l hy
  have := D.target.interior_coord_pos hT (l + 2)
  linarith

/-- The rays along the two sides at a vertex of `T` are walls. -/
theorem vertex_rayWall (D : Dissection N) (l : Fin 3) :
    RayWall D (D.target.pts l) (D.target.pts (l + 1) - D.target.pts l) ∧
      RayWall D (D.target.pts l) (D.target.pts (l + 2) - D.target.pts l) := by
  constructor
  · refine ⟨1, one_pos, fun s hs hs1 i => side_not_interior D l ?_ i⟩
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨hs, hs1⟩, by rw [AffineMap.lineMap_apply_module']; abel⟩
  · refine ⟨1, one_pos, fun s hs hs1 i => side_not_interior D (l + 2) ?_ i⟩
    rw [show l + 2 + 1 = l by fin_cases l <;> rfl, segment_symm, segment_eq_image_lineMap]
    exact ⟨s, ⟨hs, hs1⟩, by rw [AffineMap.lineMap_apply_module']; abel⟩

/-- Near a vertex of `T`, the sector of `T` there lies in `T`. -/
theorem vertex_hin (T : Tri) (l : Fin 3) :
    ∃ r > (0 : ℝ), sectorC (T.pts l) (T.pts (l + 1) - T.pts l) (T.pts (l + 2) - T.pts l) ∩
      ball (T.pts l) r ⊆ T.carrier := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_vertexCone l
  refine ⟨r, hr, fun y hy => ?_⟩
  have : y ∈ {y : Plane | y - T.pts l ∈ vertexCone (T.edgeVec l) (T.edgeVec' l)} ∩
      ball (T.pts l) r := hy
  rw [← hEq] at this; exact this.1

/-- A point `X + s (Y - X)` of `T`, for vertices `X, Y` of `T`, has `s ≤ 1`. -/
theorem le_one_of_mem (T : Tri) {l l' : Fin 3} (hll : l ≠ l') {s : ℝ}
    (h : T.pts l + s • (T.pts l' - T.pts l) ∈ T.carrier) : s ≤ 1 := by
  have hc := (Tri.mem_carrier_iff_coord T _).mp h l
  have e : T.pts l + s • (T.pts l' - T.pts l) = AffineMap.lineMap (T.pts l) (T.pts l') s := by
    rw [AffineMap.lineMap_apply_module']; abel
  rw [e, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, if_pos rfl,
    if_neg hll] at hc
  linarith

/-- A point of the cone of `u, v`, written `X + p u + q v`, `p, q ≥ 0`. -/
theorem mem_sectorC_comb {X u v : Plane} {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    X + p • u + q • v ∈ sectorC X u v := by
  rw [mem_sectorC, show X + p • u + q • v - X = p • u + q • v by abel, cross_add_right,
    cross_add_left', cross_smul_right, cross_smul_right, cross_smul_left, cross_smul_left,
    Erdos634.Geometry.cross_self, Erdos634.Geometry.cross_self]
  constructor <;> nlinarith [mul_self_nonneg (cross u v)]

/-- Cones within cones. -/
theorem sectorC_mono {X u v w : Plane} (hne : cross u v ≠ 0) (hne' : cross u w ≠ 0)
    (hw : X + w ∈ sectorC X u v) : sectorC X u w ⊆ sectorC X u v := by
  intro y hy
  obtain ⟨p, q, hp, hq, rfl⟩ := sectorC_decomp hne' hy
  obtain ⟨p', q', hp', hq', hw'⟩ := sectorC_decomp hne hw
  have hw'' : w = p' • u + q' • v := by
    have := congrArg (fun z => z - X) hw'; simp only [add_sub_cancel_left] at this
    rw [this]; abel
  rw [hw'', show X + p • u + q • (p' • u + q' • v) = X + (p + q * p') • u + (q * q') • v by
    simp only [smul_add, smul_smul, add_smul]; abel]
  exact mem_sectorC_comb (by positivity) (by positivity)

namespace RunSetting

variable {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- **At a `β` corner the two sides are `a` and `c`.** -/
theorem beta_pair {t : Fin N} {X Y Z : Plane} (hX : HasAngle D t X β)
    (h : Set.range (D.tile t).pts = {X, Y, Z}) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) :
    (dist X Y = a ∧ dist X Z = c) ∨ (dist X Y = c ∧ dist X Z = a) := by
  have eXY : TileEdge D t X Y := tileEdge_of_range h (by simp) (by simp) hXY
  have eXZ : TileEdge D t X Z := tileEdge_of_range h (by simp) (by simp) hXZ
  have hαβ := hS.alpha_ne_beta
  have hβγ : β ≠ γ := by have := hS.gamma; have := hS.angles_pos; intro h; linarith
  have key : ∀ W, TileEdge D t X W → (dist X W = a ∧ HasAngle D t W γ) ∨
      (dist X W = c ∧ HasAngle D t W α) := by
    intro W hW
    obtain ⟨ea, eb, ec⟩ := hS.edge_ends hW
    rcases hS.tileEdge_len hW with hd | hd | hd
    · rcases ea hd with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact Or.inl ⟨hd, h2⟩
      · exact absurd (angle_eq_of_two hX h1) hβγ
    · rcases eb hd with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (angle_eq_of_two h1 hX) hαβ
      · exact absurd (angle_eq_of_two hX h1) hβγ
    · rcases ec hd with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (angle_eq_of_two h1 hX) hαβ
      · exact Or.inr ⟨hd, h2⟩
  rcases key Y eXY with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases key Z eXZ with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact absurd (hS.hasAngle_unique h2 h4) hYZ
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inr ⟨h1, h3⟩
  · exact absurd (hS.hasAngle_unique h2 h4) hYZ

/-- **Edge counts on a side, with a run**: `|S| = pa + qb + rc`, an `a` (`b`) edge on `S` makes
`p` (`q`) positive, and a run of length `n` on `S` gives `r ≥ n`. -/
theorem side_counts_run (j : Fin 3) :
    ∃ p q r : ℕ, dist (D.target.pts j) (D.target.pts (j + 1)) = p * a + q * b + r * c ∧
      (∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
        segment ℝ P Q ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) →
        (dist P Q = a → 0 < p) ∧ (dist P Q = b → 0 < q)) ∧
      ∀ (n : ℕ) (U I : Plane) (t : ℕ → Fin N), run D j c n U I t → n ≤ r := by
  classical
  set s := sideSet D.toDissection j
  set len : Fin N × Fin 3 → ℝ := fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
  have hab := hS.a_ne_b
  have hac := hS.a_lt_c.ne
  have hbc := hS.b_lt_c.ne
  set p := (s.filter fun e => len e = a).card
  set q := (s.filter fun e => len e = b).card
  set r := (s.filter fun e => len e = c).card
  have hsum : ∑ e ∈ s, len e = p * a + q * b + r * c := by
    have h1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
    have h2 := Finset.sum_filter_add_sum_filter_not (s.filter fun e => ¬ len e = a)
      (fun e => len e = b) len
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    have e1 : s.filter (fun e => ¬ len e = a ∧ len e = b) = s.filter fun e => len e = b := by
      apply Finset.filter_congr; intro e _; constructor
      · exact fun h => h.2
      · exact fun h => ⟨fun h' => hab (h'.symm.trans h), h⟩
    have e2 : s.filter (fun e => ¬ len e = a ∧ ¬ len e = b) = s.filter fun e => len e = c := by
      apply Finset.filter_congr; intro e he; constructor
      · intro h; rcases hS.edge_len e.1 e.2 with h' | h' | h'
        · exact absurd h' h.1
        · exact absurd h' h.2
        · exact h'
      · exact fun h => ⟨fun h' => hac (h'.symm.trans h), fun h' => hbc (h'.symm.trans h)⟩
    rw [e1, e2] at h2
    have sa : ∑ e ∈ s.filter (fun e => len e = a), len e = p * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const,
        nsmul_eq_mul]
    have sb : ∑ e ∈ s.filter (fun e => len e = b), len e = q * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const,
        nsmul_eq_mul]
    have sc : ∑ e ∈ s.filter (fun e => len e = c), len e = r * c := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const,
        nsmul_eq_mul]
    linarith
  have hmem : ∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
      segment ℝ P Q ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) →
      ∃ e : Fin 3, (t, e) ∈ s ∧ len (t, e) = dist P Q ∧ (D.tile t).edge e = segment ℝ P Q := by
    intro t P Q hte hsub
    obtain ⟨e, he, -, hends⟩ := edge_of_tileEdge hte
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he]; exact hsub⟩, ?_, he⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [len]; rw [h1, h2]
    · simp only [len]; rw [h1, h2, dist_comm]
  refine ⟨p, q, r, (side_sum D.toDissection j).symm.trans hsum, fun t P Q hte hsub => ?_,
    fun n U I t hrun => ?_⟩
  · obtain ⟨e, hes, hlen, -⟩ := hmem t P Q hte hsub
    exact ⟨fun h => Finset.card_pos.mpr ⟨(t, e), Finset.mem_filter.mpr ⟨hes, hlen.trans h⟩⟩,
      fun h => Finset.card_pos.mpr ⟨(t, e), Finset.mem_filter.mpr ⟨hes, hlen.trans h⟩⟩⟩
  · -- the run's edges are `n` different `c` edges of the side
    have hc := hS.c_pos
    have hI0 : I ≠ 0 := fun h => by
      have := hrun.1; rw [h, norm_zero] at this; exact zero_ne_one this
    have hex : ∀ i : ℕ, ∃ e : Fin N × Fin 3, i < n → e ∈ s.filter (fun e => len e = c) ∧
        (D.tile e.1).edge e.2 = segment ℝ (U + ((i : ℝ) * c) • I) (U + (((i : ℝ) + 1) * c) • I) := by
      intro i
      by_cases hi : i < n
      · have hte := hrun.2.2 i hi
        have hsub : segment ℝ (U + ((i : ℝ) * c) • I) (U + (((i : ℝ) + 1) * c) • I) ⊆
            segment ℝ (D.target.pts j) (D.target.pts (j + 1)) :=
          Subset.trans ((convex_segment _ _).segment_subset (mem_seg_frac hi.le)
            (by have := mem_seg_frac (U := U) (I := I) (c := c) (show i + 1 ≤ n by omega)
                push_cast at this; exact this)) hrun.2.1
        obtain ⟨e, hes, hlen, hseg⟩ := hmem _ _ _ hte hsub
        refine ⟨(t (i + 1), e), fun _ => ⟨Finset.mem_filter.mpr ⟨hes, ?_⟩, hseg⟩⟩
        rw [hlen, dist_comm, dist_eq_norm, show U + (((i : ℝ) + 1) * c) • I -
          (U + ((i : ℝ) * c) • I) = c • I by module, norm_smul, hrun.1, mul_one,
          Real.norm_of_nonneg hc.le]
      · exact ⟨(t 1, 0), fun h => absurd h hi⟩
    choose E hE using hex
    have hinj : Set.InjOn E (Finset.range n) := by
      intro i hi i' hi' heq
      have h1 := (hE i (Finset.mem_range.mp hi)).2
      have h2 := (hE i' (Finset.mem_range.mp hi')).2
      rw [heq, h2] at h1
      -- equal segments have equal left ends
      have hL := congrArg (fun S : Set Plane => U + ((i' : ℝ) * c) • I ∈ S) h1
      simp only [eq_iff_iff] at hL
      have hm := hL.mp (left_mem_segment ℝ _ _)
      rw [segment_eq_image_lineMap] at hm
      obtain ⟨τ, ⟨h0, h1'⟩, hτ⟩ := hm
      rw [AffineMap.lineMap_apply_module'] at hτ
      have : ((τ * c - ((i' : ℝ) * c - (i : ℝ) * c)) • I) = 0 := by
        rw [← sub_eq_zero] at hτ
        rw [← hτ]; module
      rcases smul_eq_zero.mp this with h | h
      · -- `τ c = (i' - i) c` with `0 ≤ τ ≤ 1`: symmetrically `i ≤ i'` and `i' ≤ i`
        have hL' := congrArg (fun S : Set Plane => U + ((i : ℝ) * c) • I ∈ S) h1
        simp only [eq_iff_iff] at hL'
        have hm' := hL'.mpr (left_mem_segment ℝ _ _)
        rw [segment_eq_image_lineMap] at hm'
        obtain ⟨τ', ⟨h0', h1''⟩, hτ'⟩ := hm'
        rw [AffineMap.lineMap_apply_module'] at hτ'
        have : ((τ' * c - ((i : ℝ) * c - (i' : ℝ) * c)) • I) = 0 := by
          rw [← sub_eq_zero] at hτ'
          rw [← hτ']; module
        rcases smul_eq_zero.mp this with h' | h'
        · have e1 : (i' : ℝ) - i = τ := by
            have := mul_right_cancel₀ hc.ne' (show ((i' : ℝ) - i) * c = τ * c by linarith)
            exact this
          have e2 : (i : ℝ) - i' = τ' := by
            have := mul_right_cancel₀ hc.ne' (show ((i : ℝ) - i') * c = τ' * c by linarith)
            exact this
          have : (i : ℝ) = i' := by linarith
          exact_mod_cast this
        · exact absurd h' hI0
      · exact absurd h hI0
    have := Finset.card_le_card_of_injOn E (fun i hi => (hE i (Finset.mem_range.mp hi)).1) hinj
    simpa using this

end RunSetting

end TriangleTiling.Prime
