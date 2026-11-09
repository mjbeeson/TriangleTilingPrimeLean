/-
`lemma:notallsupported` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723): in an
`N`-tiling of a triangle with `N > 3`, no segment supports all `N` tiles.

Statement checked by Beeson. The proof follows the paper's. Every tile has an edge on the
line `L` of the segment, so lies on one side of `L`, and meets `L` only in that edge. Fix a side.
At a point `V` of `L` strictly between two points of the triangle, the tiles on that side at `V`
have angles adding up to `π` (Bonfioli's half-disk area argument, or, if `L` is a side line of
the triangle, the angle sum at a boundary point). So if `V` is an end of one of their edges, two of
them meet at `V`, with angles adding up to `π`, and as the tiles are congruent both angles are
right angles (`right_of_sum_pi`). A tile has at most one right angle, so each tile on that side
has an end of its edge at the leftmost or the rightmost end on that side, and at most one tile
does each: at most two tiles on each side. With four tiles, two on each side, each tile is
acute at its extreme end; then at an extreme end the angles add up to less than `π`, so it is a
vertex of the triangle, and the two extreme ends on one side are two vertices of the triangle on
`L`, so the triangle lies on one side of `L`: a contradiction.
-/
import TriangleTiling.Tiling.LineParams
import TriangleTiling.Tiling.HalfPlaneAngle
import TriangleTiling.Tiling.Links
import TriangleTiling.RightTile.Helper2

namespace TriangleTiling

open Erdos634.Geometry Set

namespace NotAllSupported

variable {N : ℕ}

/-! ### Angles -/

/-- The corner angle of `T` at vertex `j`. -/
noncomputable abbrev corner (T : Tri) (j : Fin 3) : ℝ :=
  cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))

theorem corner_pos (T : Tri) (j : Fin 3) : 0 < corner T j := Erdos634.MarchFlank.cornerAngle_pos T j

/-- Two different corner angles of a triangle add up to less than `π`. -/
theorem corner_add_lt (T : Tri) {a b : Fin 3} (hab : a ≠ b) : corner T a + corner T b < Real.pi := by
  have hs := cornerAngle_sum T
  have e0 : corner T 0 = cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) := rfl
  have e1 : corner T 1 = cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) := rfl
  have e2 : corner T 2 = cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) := rfl
  have p0 := corner_pos T 0
  have p1 := corner_pos T 1
  have p2 := corner_pos T 2
  have h3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases h3 a with rfl | rfl | rfl <;> rcases h3 b with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | linarith

/-- Angles of two congruent tiles adding up to `π` are right angles. -/
theorem right_of_sum_pi (D : CongruentDissection N) {i j : Fin N} {x y : Fin 3}
    (h : corner (D.tile i) x + corner (D.tile j) y = Real.pi) :
    corner (D.tile i) x = Real.pi / 2 := by
  obtain ⟨ρi, hρi, -⟩ := corner_perm_dist (D.tiles_congruent i)
  obtain ⟨ρj, hρj, -⟩ := corner_perm_dist (D.tiles_congruent j)
  have ei : corner (D.tile i) x = corner D.model (ρi x) := (hρi x).symm
  have ej : corner (D.tile j) y = corner D.model (ρj y) := (hρj y).symm
  rw [ei, ej] at h
  rw [ei]
  by_cases hxy : ρi x = ρj y
  · rw [hxy] at h ⊢; linarith
  · linarith [corner_add_lt D.model hxy]

theorem localAngle_zero_of_not_mem (T : Tri) {p : Plane} (hp : p ∉ T.carrier) :
    T.localAngle p = 0 := by
  classical
  rw [Tri.mem_carrier_iff_coord] at hp
  push Not at hp
  obtain ⟨j, hj⟩ := hp
  have hv : ¬ ∃ k, p = T.pts k := by
    rintro ⟨k, rfl⟩
    rw [Tri.coord_vertex] at hj
    split_ifs at hj <;> linarith
  unfold Tri.localAngle
  rw [dif_neg hv, if_neg (fun h => by linarith [h j]), if_neg]
  rintro ⟨k, hk0, hk⟩
  by_cases hjk : j = k
  · subst hjk; linarith
  · linarith [hk j hjk]

/-! ### A tile with an edge on a line -/

/-- A point of a tile on the line of one of its edges, on the side of the tile, lies on the
edge. -/
theorem mem_edge_of_level (T : Tri) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (k : Fin 3)
    (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) {y : Plane} (hy : y ∈ T.carrier)
    (hgy : g y = c) : y ∈ T.edge k := by
  have i1 : k + 2 + 1 = k := by fin_cases k <;> rfl
  have i2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  have hl := level_eq_coord T g c (k + 2) (by rw [i1]; exact h1) (by rw [i2]; exact h2) y
  have h3 := third_off_line T hg k h1 h2
  have hz : T.basis.coord (k + 2) y = 0 := by
    rw [hgy, sub_self] at hl
    rcases mul_eq_zero.mp hl.symm with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) h3
  have hc := (Tri.mem_carrier_iff_coord T y).mp hy
  have hs := Tri.coord_sum T y
  set s := T.basis.coord (k + 1) y with hsdef
  have hyl : y = AffineMap.lineMap (T.pts k) (T.pts (k + 1)) s := by
    apply T.basis.ext_elem
    intro j
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    have e3 : j = k ∨ j = k + 1 ∨ j = k + 2 := fin3_cases3 j k
    have n1 : k ≠ k + 1 := by fin_cases k <;> decide
    have n2 : k + 2 ≠ k := by fin_cases k <;> decide
    have n3 : k + 2 ≠ k + 1 := by fin_cases k <;> decide
    have hsum : T.basis.coord k y + s + T.basis.coord (k + 2) y = 1 := by
      rw [hsdef]
      rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) k with rfl | rfl | rfl <;>
        simp only [Fin.reduceAdd] <;> linarith
    rcases e3 with rfl | rfl | rfl
    · simp [n1]; linarith
    · simp [n1.symm, hsdef]
    · simp [n2, n3, hz]
  rw [Tri.edge, hyl, segment_eq_image_lineMap]
  refine ⟨s, ⟨hc _, ?_⟩, rfl⟩
  have hsum : T.basis.coord k y + s + T.basis.coord (k + 2) y = 1 := by
    rw [hsdef]
    rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) k with rfl | rfl | rfl <;>
      simp only [Fin.reduceAdd] <;> linarith
  linarith [hc k]

/-! ### A triangle not straddling a line -/

/-- If a barycentric coordinate of `T` vanishes at two points of a line, `T` lies on one side of
the line. -/
theorem not_straddle (T : Tri) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {a b : Plane}
    (hab : a ≠ b) (ha : g a = c) (hb : g b = c) {m : Fin 3} (hma : T.basis.coord m a = 0)
    (hmb : T.basis.coord m b = 0) {y z : Plane} (hy : y ∈ T.carrier) (hz : z ∈ T.carrier)
    (hgy : g y < c) (hgz : c < g z) : False := by
  set r := (c - g y) / (g z - g y) with hr
  have hd : 0 < g z - g y := by linarith
  have r0 : 0 < r := div_pos (by linarith) hd
  have r1 : r < 1 := (div_lt_one hd).mpr (by linarith)
  set x := AffineMap.lineMap y z r with hx
  have hgx : g x = c := by
    rw [hx, AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      hr]
    field_simp
    ring
  obtain ⟨s, hs⟩ := eq_lineMap_of_level hg hab ha hb hgx
  have hmx : T.basis.coord m x = 0 := by rw [hs, Tri.coord_lineMap, hma, hmb]; ring
  have hy0 := (Tri.mem_carrier_iff_coord T y).mp hy m
  have hz0 := (Tri.mem_carrier_iff_coord T z).mp hz m
  have hmx' := hmx
  rw [hx, Tri.coord_lineMap] at hmx'
  have hym : T.basis.coord m y = 0 := by nlinarith
  -- the coordinate `m` is a nonconstant affine function vanishing at `a`, `b`, `y`
  set f := (T.basis.coord m).linear with hf
  have hfv : ∀ p q : Plane, f p - f q = T.basis.coord m p - T.basis.coord m q := by
    intro p q
    rw [← map_sub, show p - q = p -ᵥ q from rfl, AffineMap.linearMap_vsub]
    rfl
  have hf0 : f ≠ 0 := by
    intro h0
    have := hfv (T.pts m) a
    rw [h0, Tri.coord_vertex, if_pos rfl, hma] at this
    simp at this
  obtain ⟨t, ht⟩ := eq_lineMap_of_level hf0 hab rfl (by linarith [hfv b a, hmb, hma])
    (show f y = f a by linarith [hfv y a])
  have := level_lineMap ha hb t
  rw [← ht] at this
  linarith

/-! ### One side of a line carrying an edge of every tile -/

section Side

open Classical

variable (D : CongruentDissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {X Y : Plane}
  (hXY : X ≠ Y) (hX : g X = c) (hY : g Y = c)

/-- The tiles on the side `g ≤ c`. -/
abbrev Low (i : Fin N) : Prop := ∀ y ∈ (D.tile i).carrier, g y ≤ c

/-- The sum of the angles at `p` of the tiles on the side `g ≤ c`. -/
noncomputable abbrev lowSum (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (p : Plane) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c), (D.tile i).localAngle p

/-- The lower and upper parameters of a chain edge. -/
noncomputable abbrev lo (X Y : Plane) (e : Fin N × Fin 3) : ℝ := edgeLo X Y (D.tile e.1) e.2
noncomputable abbrev hi (X Y : Plane) (e : Fin N × Fin 3) : ℝ := edgeHi X Y (D.tile e.1) e.2

variable (hsupp : ∀ i, ∃ k, g ((D.tile i).pts k) = c ∧ g ((D.tile i).pts (k + 1)) = c)

include hsupp in
theorem low_chain {i : Fin N} (hi : ∀ y ∈ (D.tile i).carrier, g y ≤ c) :
    ∃ k, (i, k) ∈ D.lineChain g c := by
  obtain ⟨k, h1, h2⟩ := hsupp i
  exact ⟨k, Dissection.mem_lineChain.mpr ⟨h1, h2, fun j => hi _ (subset_convexHull ℝ _ ⟨j, rfl⟩)⟩⟩

include hg in
/-- A tile on the side `g ≤ c` with an edge on the line has its third vertex strictly below. -/
theorem apex_lt {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    g ((D.tile e.1).pts (e.2 + 2)) < c := by
  obtain ⟨h1, h2, h3⟩ := Dissection.mem_lineChain.mp he
  exact lt_of_le_of_ne (h3 _) (third_off_line _ hg e.2 h1 h2)

include hsupp in
/-- Every tile lies on one side of the line. -/
theorem low_or_up (i : Fin N) :
    (∀ y ∈ (D.tile i).carrier, g y ≤ c) ∨ (∀ y ∈ (D.tile i).carrier, c ≤ g y) := by
  obtain ⟨k, h1, h2⟩ := hsupp i
  have e3 : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := fun j => fin3_cases3 j k
  rcases le_or_gt (g ((D.tile i).pts (k + 2))) c with h3 | h3
  · left
    refine (D.tile i).carrier_subset_halfplane g c fun j => ?_
    rcases e3 j with rfl | rfl | rfl
    · rw [h1]
    · rw [h2]
    · exact h3
  · right
    intro y hy
    have := (D.tile i).carrier_subset_halfplane (-g) (-c) (fun j => by
      rcases e3 j with rfl | rfl | rfl
      · simp [h1]
      · simp [h2]
      · simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact h3.le) y hy
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
    exact this

variable {D}

include hg hXY hX hY in
theorem mem_Icc_of_mem {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {t : ℝ}
    (ht : AffineMap.lineMap X Y t ∈ (D.tile e.1).carrier) : t ∈ Icc (lo D X Y e) (hi D X Y e) := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  rw [← chain_mem_edge_iff D.toDissection hg hXY hX hY he t]
  exact mem_edge_of_level _ hg e.2 h1 h2 ht (level_lineMap hX hY t)

include hg hXY hX hY in
theorem ang_out {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {t : ℝ}
    (ht : t ∉ Icc (lo D X Y e) (hi D X Y e)) :
    (D.tile e.1).localAngle (AffineMap.lineMap X Y t) = 0 :=
  localAngle_zero_of_not_mem _ fun hm => ht (mem_Icc_of_mem hg hXY hX hY he hm)

include hg hXY hX hY in
theorem ang_open {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {t : ℝ}
    (ht : t ∈ Ioo (lo D X Y e) (hi D X Y e)) :
    (D.tile e.1).localAngle (AffineMap.lineMap X Y t) = Real.pi := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  exact Tri.localAngle_openSegment _ e.2
    ((lineMap_mem_openSegment_iff hg hXY hX hY _ e.2 h1 h2 t).mpr ht)

include hg hXY hX hY in
theorem ang_end {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {t : ℝ}
    (ht : t = lo D X Y e ∨ t = hi D X Y e) :
    ∃ v, AffineMap.lineMap X Y t = (D.tile e.1).pts v ∧
      (D.tile e.1).localAngle (AffineMap.lineMap X Y t) = corner (D.tile e.1) v := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  have key : t = lineParam X Y ((D.tile e.1).pts e.2) ∨
      t = lineParam X Y ((D.tile e.1).pts (e.2 + 1)) := by
    rcases ht with rfl | rfl
    · exact min_choice _ _
    · exact max_choice _ _
  rcases key with rfl | rfl
  · refine ⟨e.2, eq_lineMap_lineParam hg hXY hX hY h1, ?_⟩
    rw [eq_lineMap_lineParam hg hXY hX hY h1, Tri.localAngle_vertex]
  · refine ⟨e.2 + 1, eq_lineMap_lineParam hg hXY hX hY h2, ?_⟩
    rw [eq_lineMap_lineParam hg hXY hX hY h2, Tri.localAngle_vertex]

include hg hXY hX hY in
theorem same_of_overlap {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (he' : e' ∈ D.lineChain g c)
    (h : max (lo D X Y e) (lo D X Y e') < min (hi D X Y e) (hi D X Y e')) : e.1 = e'.1 :=
  congrArg Prod.fst (lineChain_eq_of_overlap D.toDissection hg hXY hX hY he he' h)

include hg hXY hX hY in
theorem lo_lt_hi {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) : lo D X Y e < hi D X Y e :=
  chain_lo_lt_hi D.toDissection hg hXY hX hY he

include hg hXY hX hY in
/-- A tile with a nonzero angle at an end `t` of another tile's edge on the same side has `t` as
the other end of its own edge. -/
theorem opp_end {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (he' : e' ∈ D.lineChain g c)
    (hne : e.1 ≠ e'.1) {t : ℝ} (ht : t = lo D X Y e ∨ t = hi D X Y e)
    (h0 : (D.tile e'.1).localAngle (AffineMap.lineMap X Y t) ≠ 0) :
    (t = lo D X Y e ∧ t = hi D X Y e') ∨ (t = hi D X Y e ∧ t = lo D X Y e') := by
  have l1 := lo_lt_hi hg hXY hX hY he
  have l2 := lo_lt_hi hg hXY hX hY he'
  have hI : t ∈ Icc (lo D X Y e') (hi D X Y e') := by
    by_contra hn; exact h0 (ang_out hg hXY hX hY he' hn)
  have ov := fun h => hne (same_of_overlap hg hXY hX hY he he' h)
  rcases ht with rfl | rfl
  · rcases eq_or_lt_of_le hI.2 with h | h
    · exact Or.inl ⟨rfl, h⟩
    · exfalso; apply ov
      rw [max_eq_left hI.1, lt_min_iff]; exact ⟨l1, h⟩
  · rcases eq_or_lt_of_le hI.1 with h | h
    · exact Or.inr ⟨rfl, h.symm⟩
    · exfalso; apply ov
      rw [min_eq_left hI.2, max_lt_iff]; exact ⟨l1, h⟩

theorem corner_lt_pi (T : Tri) (v : Fin 3) : corner T v < Real.pi := by
  have := corner_add_lt T (show v ≠ v + 1 by fin_cases v <;> decide)
  linarith [corner_pos T (v + 1)]

include hg hXY hX hY hsupp in
/-- **At a junction the angles are right.** If the angles on the side `g ≤ c` at an end `t` of a
chain edge add up to `π`, the tile has a right angle there. -/
theorem right_at_flat {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {t : ℝ}
    (ht : t = lo D X Y e ∨ t = hi D X Y e)
    (hflat : lowSum D g c (AffineMap.lineMap X Y t) = Real.pi) :
    ∃ v, AffineMap.lineMap X Y t = (D.tile e.1).pts v ∧ corner (D.tile e.1) v = Real.pi / 2 := by
  obtain ⟨v, hv, hθ⟩ := ang_end hg hXY hX hY he ht
  refine ⟨v, hv, ?_⟩
  set S := Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c)
  set f := fun i => (D.tile i).localAngle (AffineMap.lineMap X Y t)
  have heS : e.1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lineChain_le D.toDissection he⟩
  -- another tile on the side has a nonzero angle there
  obtain ⟨j, hjS, hji, hj0⟩ : ∃ j ∈ S, j ≠ e.1 ∧ f j ≠ 0 := by
    by_contra hn
    push Not at hn
    have h1 : lowSum D g c (AffineMap.lineMap X Y t) = f e.1 :=
      Finset.sum_eq_single_of_mem _ heS fun j hj hji => hn j hj hji
    rw [hflat] at h1
    simp only [f] at h1
    rw [hθ] at h1
    linarith [corner_lt_pi (D.tile e.1) v]
  obtain ⟨k', hk'⟩ := low_chain D hsupp (Finset.mem_filter.mp hjS).2
  have hne : e.1 ≠ (j, k').1 := fun h => hji h.symm
  have hop := opp_end hg hXY hX hY he hk' hne ht hj0
  -- it is the only one
  have honly : ∀ j' ∈ S, j' ≠ e.1 → j' ≠ j → f j' = 0 := by
    intro j' hj'S hj'i hj'j
    by_contra hj'0
    obtain ⟨k'', hk''⟩ := low_chain D hsupp (Finset.mem_filter.mp hj'S).2
    have hop' := opp_end hg hXY hX hY he hk'' (fun h => hj'i h.symm) ht hj'0
    apply hj'j
    have l1 := lo_lt_hi hg hXY hX hY hk'
    have l2 := lo_lt_hi hg hXY hX hY hk''
    have := same_of_overlap hg hXY hX hY hk'' hk'
    have l0 := lo_lt_hi hg hXY hX hY he
    rcases hop with ⟨a1, h1⟩ | ⟨a1, h1⟩ <;> rcases hop' with ⟨a2, h2⟩ | ⟨a2, h2⟩
    · exact this (by simp only [lt_min_iff, max_lt_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
    · linarith
    · linarith
    · exact this (by simp only [lt_min_iff, max_lt_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  have hsum : lowSum D g c (AffineMap.lineMap X Y t) = f e.1 + f j :=
    Finset.sum_eq_add_of_mem _ _ heS hjS (Ne.symm hji) fun j' hj' h => honly j' hj' h.1 h.2
  obtain ⟨v', -, hθ'⟩ := ang_end hg hXY hX hY hk' (by rcases hop with ⟨-, h⟩ | ⟨-, h⟩; exacts [Or.inr h, Or.inl h])
  rw [hflat] at hsum
  simp only [f, hθ, hθ'] at hsum
  exact right_of_sum_pi D hsum.symm

end Side

theorem coord_le_one (T : Tri) {x : Plane} (hx : x ∈ T.carrier) (j : Fin 3) :
    T.basis.coord j x ≤ 1 := by
  have hs := Tri.coord_sum T x
  have hc := (Tri.mem_carrier_iff_coord T x).mp hx
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) j with rfl | rfl | rfl <;>
    linarith [hc 0, hc 1, hc 2]

/-- An affine function of `s` with a minimum at an inner point `t` is constant. -/
theorem slope_zero {A B t s₁ s₂ : ℝ} (h₁ : s₁ < t) (h₂ : t < s₂) (e₁ : A + t * B ≤ A + s₁ * B)
    (e₂ : A + t * B ≤ A + s₂ * B) : B = 0 := by
  rcases lt_trichotomy B 0 with hB | hB | hB
  · nlinarith
  · exact hB
  · nlinarith

section Side2

open Classical

variable {D : CongruentDissection N} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {X Y : Plane}
  (hXY : X ≠ Y) (hX : g X = c) (hY : g Y = c)
  (hsupp : ∀ i, ∃ k, g ((D.tile i).pts k) = c ∧ g ((D.tile i).pts (k + 1)) = c)

include hg hXY hX hY in
theorem end_mem {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {t : ℝ}
    (ht : t = lo D X Y e ∨ t = hi D X Y e) : AffineMap.lineMap X Y t ∈ D.target.carrier := by
  obtain ⟨v, hv, -⟩ := ang_end hg hXY hX hY he ht
  rw [hv]
  exact tile_subset_target D.toDissection e.1 (subset_convexHull ℝ _ ⟨v, rfl⟩)

include hg hXY hX hY hsupp in
/-- **Flatness strictly inside.** At an end `t` of a chain edge lying strictly between two points
of the triangle on the line, the angles on the side `g ≤ c` add up to `π`. -/
theorem flat_between {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) {t : ℝ}
    (ht : t = lo D X Y e ∨ t = hi D X Y e) {s₁ s₂ : ℝ}
    (h₁ : AffineMap.lineMap X Y s₁ ∈ D.target.carrier)
    (h₂ : AffineMap.lineMap X Y s₂ ∈ D.target.carrier) (hs₁ : s₁ < t) (hs₂ : t < s₂) :
    lowSum D g c (AffineMap.lineMap X Y t) = Real.pi := by
  have hpT := end_mem hg hXY hX hY he ht
  by_cases hint : AffineMap.lineMap X Y t ∈ interior D.target.carrier
  · exact half_angle_sum D.toDissection hint hg (level_lineMap hX hY t)
      (fun i _ => low_or_up D hsupp i)
  have hlin : ∀ j s, D.target.basis.coord j (AffineMap.lineMap X Y s) =
      D.target.basis.coord j X + s * (D.target.basis.coord j Y - D.target.basis.coord j X) :=
    fun j s => Tri.coord_lineMap _ j X Y s
  have hcoord := (Tri.mem_carrier_iff_coord _ _).mp hpT
  obtain ⟨m, hm⟩ : ∃ m, D.target.basis.coord m (AffineMap.lineMap X Y t) = 0 := by
    by_contra hn
    push Not at hn
    exact hint ((Tri.mem_interior_iff_coord_pos _ _).mpr fun j =>
      lt_of_le_of_ne (hcoord j) (hn j).symm)
  have c₁ := (Tri.mem_carrier_iff_coord _ _).mp h₁ m
  have c₂ := (Tri.mem_carrier_iff_coord _ _).mp h₂ m
  rw [hlin] at c₁ c₂ hm
  have hB := slope_zero (A := D.target.basis.coord m X)
    (B := D.target.basis.coord m Y - D.target.basis.coord m X) hs₁ hs₂ (by linarith) (by linarith)
  have hm' : D.target.basis.coord m X = 0 := by rw [hB, mul_zero, add_zero] at hm; exact hm
  have hm₁ : D.target.basis.coord m (AffineMap.lineMap X Y s₁) = 0 := by
    rw [hlin, hB, mul_zero, add_zero]; exact hm'
  have hm₂ : D.target.basis.coord m (AffineMap.lineMap X Y s₂) = 0 := by
    rw [hlin, hB, mul_zero, add_zero]; exact hm'
  have hne : AffineMap.lineMap X Y s₁ ≠ AffineMap.lineMap X Y s₂ := fun h => by
    have := AffineMap.lineMap_injective ℝ hXY h; linarith
  -- every tile is on the side `g ≤ c`
  have hall : ∀ i, ∀ y ∈ (D.tile i).carrier, g y ≤ c := by
    intro i
    by_contra hn
    push Not at hn
    obtain ⟨z, hz, hgz⟩ := hn
    exact not_straddle D.target hg hne (level_lineMap hX hY s₁) (level_lineMap hX hY s₂) hm₁ hm₂
      (tile_subset_target D.toDissection e.1 (subset_convexHull ℝ _ ⟨e.2 + 2, rfl⟩))
      (tile_subset_target D.toDissection i hz) (apex_lt D hg he) hgz
  -- the point is not a vertex of the triangle
  have hnv : AffineMap.lineMap X Y t ∉ Set.range D.target.pts := by
    rintro ⟨k, hk⟩
    have heq : AffineMap.lineMap X Y s₁ = AffineMap.lineMap X Y t := by
      apply D.target.basis.ext_elem
      intro j
      have a₁ := (Tri.mem_carrier_iff_coord _ _).mp h₁ j
      have a₂ := (Tri.mem_carrier_iff_coord _ _).mp h₂ j
      have b₁ := coord_le_one _ h₁ j
      have b₂ := coord_le_one _ h₂ j
      have pj : D.target.basis.coord j (AffineMap.lineMap X Y t) = 0 ∨
          D.target.basis.coord j (AffineMap.lineMap X Y t) = 1 := by
        rw [← hk, Tri.coord_vertex]; split_ifs <;> simp
      simp only [hlin] at a₁ a₂ b₁ b₂ pj ⊢
      rcases pj with h | h
      · have hB0 := slope_zero (A := D.target.basis.coord j X)
          (B := D.target.basis.coord j Y - D.target.basis.coord j X) hs₁ hs₂ (by linarith)
          (by linarith)
        rw [hB0]; ring
      · have := slope_zero (A := -D.target.basis.coord j X)
          (B := -(D.target.basis.coord j Y - D.target.basis.coord j X)) hs₁ hs₂
          (by linarith) (by linarith)
        have hB0 : D.target.basis.coord j Y - D.target.basis.coord j X = 0 := by linarith
        rw [hB0]; ring
    have := AffineMap.lineMap_injective ℝ hXY heq
    linarith
  have hsum := D.toDissection.sum_localAngle_eq (AffineMap.lineMap X Y t)
  rw [Tri.localAngle_frontier _ ⟨subset_closure hpT, hint⟩ hnv] at hsum
  rw [lowSum, Finset.filter_true_of_mem (fun i _ => hall i)]
  exact hsum

include hg hXY hX hY hsupp in
/-- Each tile on the side `g ≤ c` has the leftmost or the rightmost end on that side. -/
theorem ext_or {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    (∀ e' ∈ D.lineChain g c, lo D X Y e ≤ lo D X Y e') ∨
      (∀ e' ∈ D.lineChain g c, hi D X Y e' ≤ hi D X Y e) := by
  by_contra hn
  push Not at hn
  obtain ⟨⟨e₁, he₁, h₁⟩, ⟨e₂, he₂, h₂⟩⟩ := hn
  have l := lo_lt_hi hg hXY hX hY he
  have fl := flat_between hg hXY hX hY hsupp he (Or.inl rfl)
    (end_mem hg hXY hX hY he₁ (Or.inl rfl)) (end_mem hg hXY hX hY he (Or.inr rfl)) h₁ l
  have fh := flat_between hg hXY hX hY hsupp he (Or.inr rfl)
    (end_mem hg hXY hX hY he (Or.inl rfl)) (end_mem hg hXY hX hY he₂ (Or.inr rfl)) l h₂
  obtain ⟨v, hv, hv'⟩ := right_at_flat hg hXY hX hY hsupp he (Or.inl rfl) fl
  obtain ⟨w, hw, hw'⟩ := right_at_flat hg hXY hX hY hsupp he (Or.inr rfl) fh
  have hvw : v ≠ w := by
    rintro rfl
    have := AffineMap.lineMap_injective ℝ hXY (hv.trans hw.symm)
    linarith
  linarith [corner_add_lt (D.tile e.1) hvw]

include hg hXY hX hY in
theorem left_unique {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (he' : e' ∈ D.lineChain g c) (h : ∀ e'' ∈ D.lineChain g c, lo D X Y e ≤ lo D X Y e'')
    (h' : ∀ e'' ∈ D.lineChain g c, lo D X Y e' ≤ lo D X Y e'') : e.1 = e'.1 := by
  have a := h e' he'
  have b := h' e he
  have l := lo_lt_hi hg hXY hX hY he
  have l' := lo_lt_hi hg hXY hX hY he'
  exact same_of_overlap hg hXY hX hY he he' (by
    simp only [lt_min_iff, max_lt_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)

include hg hXY hX hY in
theorem right_unique {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (he' : e' ∈ D.lineChain g c) (h : ∀ e'' ∈ D.lineChain g c, hi D X Y e'' ≤ hi D X Y e)
    (h' : ∀ e'' ∈ D.lineChain g c, hi D X Y e'' ≤ hi D X Y e') : e.1 = e'.1 := by
  have a := h e' he'
  have b := h' e he
  have l := lo_lt_hi hg hXY hX hY he
  have l' := lo_lt_hi hg hXY hX hY he'
  exact same_of_overlap hg hXY hX hY he he' (by
    simp only [lt_min_iff, max_lt_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)

include hg hXY hX hY hsupp in
/-- **At most two tiles on a side.** -/
theorem card_le_two :
    (Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c)).card ≤ 2 := by
  by_contra h
  push Not at h
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := Finset.two_lt_card_iff.mp h
  obtain ⟨ka, hka⟩ := low_chain D hsupp (Finset.mem_filter.mp ha).2
  obtain ⟨kb, hkb⟩ := low_chain D hsupp (Finset.mem_filter.mp hb).2
  obtain ⟨kd, hkd⟩ := low_chain D hsupp (Finset.mem_filter.mp hd).2
  have L := fun {e e'} he he' h h' => left_unique (D := D) hg hXY hX hY (e := e) (e' := e') he he' h h'
  have R := fun {e e'} he he' h h' => right_unique (D := D) hg hXY hX hY (e := e) (e' := e') he he' h h'
  rcases ext_or hg hXY hX hY hsupp hka with la | ra <;>
    rcases ext_or hg hXY hX hY hsupp hkb with lb | rb <;>
    rcases ext_or hg hXY hX hY hsupp hkd with ld | rd
  all_goals first
    | exact hab (L hka hkb la lb) | exact had (L hka hkd la ld) | exact hbd (L hkb hkd lb ld)
    | exact hab (R hka hkb ra rb) | exact had (R hka hkd ra rd) | exact hbd (R hkb hkd rb rd)

include hg hXY hX hY hsupp in
/-- The structure with exactly two tiles on a side: the leftmost and rightmost ends `m < M`
carry one acute angle each, and at every point of the line the angles on that side add up to `π`
or to less than `π/2`. -/
theorem two_aux {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (he' : e' ∈ D.lineChain g c)
    (hne : e.1 ≠ e'.1)
    (hL : ∀ e'' ∈ D.lineChain g c, lo D X Y e ≤ lo D X Y e'')
    (hR : ∀ e'' ∈ D.lineChain g c, hi D X Y e'' ≤ hi D X Y e')
    (hS : Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c) = {e.1, e'.1}) :
    ∃ m M : ℝ, m < M ∧ AffineMap.lineMap X Y m ∈ D.target.carrier ∧
      AffineMap.lineMap X Y M ∈ D.target.carrier ∧
      0 < lowSum D g c (AffineMap.lineMap X Y m) ∧
      lowSum D g c (AffineMap.lineMap X Y m) < Real.pi / 2 ∧
      0 < lowSum D g c (AffineMap.lineMap X Y M) ∧
      lowSum D g c (AffineMap.lineMap X Y M) < Real.pi / 2 ∧
      ∀ t : ℝ, lowSum D g c (AffineMap.lineMap X Y t) = Real.pi ∨
        lowSum D g c (AffineMap.lineMap X Y t) < Real.pi / 2 := by
  set S := Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c)
  have l := lo_lt_hi hg hXY hX hY he
  have l' := lo_lt_hi hg hXY hX hY he'
  -- `e` is not rightmost, `e'` is not leftmost
  obtain ⟨e₂, he₂, h₂⟩ : ∃ e'' ∈ D.lineChain g c, hi D X Y e < hi D X Y e'' := by
    by_contra hn
    push Not at hn
    exact hne (right_unique hg hXY hX hY he he' hn hR)
  obtain ⟨e₁, he₁, h₁⟩ : ∃ e'' ∈ D.lineChain g c, lo D X Y e'' < lo D X Y e' := by
    by_contra hn
    push Not at hn
    exact hne (left_unique hg hXY hX hY he he' hL hn)
  have hmM : lo D X Y e < hi D X Y e' := lt_of_lt_of_le l (hR e he)
  have mem := fun {e''} (he'' : e'' ∈ D.lineChain g c) t ht => end_mem (D := D) hg hXY hX hY he'' (t := t) ht
  -- the angle at the leftmost end is acute
  have acute_m : ∃ v, (D.tile e.1).localAngle (AffineMap.lineMap X Y (lo D X Y e)) =
      corner (D.tile e.1) v ∧ corner (D.tile e.1) v < Real.pi / 2 := by
    obtain ⟨v, hv, hv'⟩ := ang_end hg hXY hX hY he (Or.inl rfl)
    obtain ⟨w, hw, hw'⟩ := right_at_flat hg hXY hX hY hsupp he (Or.inr rfl)
      (flat_between hg hXY hX hY hsupp he (Or.inr rfl) (mem he _ (Or.inl rfl))
        (mem he₂ _ (Or.inr rfl)) l h₂)
    have hvw : v ≠ w := by
      rintro rfl
      have := AffineMap.lineMap_injective ℝ hXY (hv.trans hw.symm)
      linarith
    exact ⟨v, hv', by linarith [corner_add_lt (D.tile e.1) hvw]⟩
  have acute_M : ∃ v, (D.tile e'.1).localAngle (AffineMap.lineMap X Y (hi D X Y e')) =
      corner (D.tile e'.1) v ∧ corner (D.tile e'.1) v < Real.pi / 2 := by
    obtain ⟨v, hv, hv'⟩ := ang_end hg hXY hX hY he' (Or.inr rfl)
    obtain ⟨w, hw, hw'⟩ := right_at_flat hg hXY hX hY hsupp he' (Or.inl rfl)
      (flat_between hg hXY hX hY hsupp he' (Or.inl rfl) (mem he₁ _ (Or.inl rfl))
        (mem he' _ (Or.inr rfl)) h₁ l')
    have hvw : v ≠ w := by
      rintro rfl
      have := AffineMap.lineMap_injective ℝ hXY (hv.trans hw.symm)
      linarith
    exact ⟨v, hv', by linarith [corner_add_lt (D.tile e'.1) hvw]⟩
  have heS : e.1 ∈ S := by rw [hS]; simp
  have he'S : e'.1 ∈ S := by rw [hS]; simp
  -- only one tile on the side at each extreme end
  have only_m : lowSum D g c (AffineMap.lineMap X Y (lo D X Y e)) =
      (D.tile e.1).localAngle (AffineMap.lineMap X Y (lo D X Y e)) := by
    refine Finset.sum_eq_single_of_mem _ heS fun j hj hji => ?_
    by_contra h0
    obtain ⟨k, hk⟩ := low_chain D hsupp (Finset.mem_filter.mp hj).2
    have hI : lo D X Y e ∈ Icc (lo D X Y (j, k)) (hi D X Y (j, k)) := by
      by_contra hn; exact h0 (ang_out hg hXY hX hY hk hn)
    have := hL _ hk
    have l₂ := lo_lt_hi hg hXY hX hY hk
    exact hji (same_of_overlap hg hXY hX hY hk he (by
      simp only [lt_min_iff, max_lt_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hI.1]))
  have only_M : lowSum D g c (AffineMap.lineMap X Y (hi D X Y e')) =
      (D.tile e'.1).localAngle (AffineMap.lineMap X Y (hi D X Y e')) := by
    refine Finset.sum_eq_single_of_mem _ he'S fun j hj hji => ?_
    by_contra h0
    obtain ⟨k, hk⟩ := low_chain D hsupp (Finset.mem_filter.mp hj).2
    have hI : hi D X Y e' ∈ Icc (lo D X Y (j, k)) (hi D X Y (j, k)) := by
      by_contra hn; exact h0 (ang_out hg hXY hX hY hk hn)
    have := hR _ hk
    have l₂ := lo_lt_hi hg hXY hX hY hk
    exact hji (same_of_overlap hg hXY hX hY hk he' (by
      simp only [lt_min_iff, max_lt_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hI.2]))
  obtain ⟨v, hv, hv'⟩ := acute_m
  obtain ⟨w, hw, hw'⟩ := acute_M
  refine ⟨lo D X Y e, hi D X Y e', hmM, mem he _ (Or.inl rfl), mem he' _ (Or.inr rfl),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [only_m, hv]; exact corner_pos _ _
  · rw [only_m, hv]; exact hv'
  · rw [only_M, hw]; exact corner_pos _ _
  · rw [only_M, hw]; exact hw'
  intro t
  by_cases hend : ∃ e₃ ∈ D.lineChain g c, t = lo D X Y e₃ ∨ t = hi D X Y e₃
  · obtain ⟨e₃, he₃, ht₃⟩ := hend
    have l₃ := lo_lt_hi hg hXY hX hY he₃
    have a₁ : lo D X Y e ≤ t := by rcases ht₃ with rfl | rfl <;> linarith [hL _ he₃]
    have a₂ : t ≤ hi D X Y e' := by rcases ht₃ with rfl | rfl <;> linarith [hR _ he₃]
    rcases eq_or_lt_of_le a₁ with rfl | b₁
    · right; rw [only_m, hv]; exact hv'
    rcases eq_or_lt_of_le a₂ with rfl | b₂
    · right; rw [only_M, hw]; exact hw'
    left
    exact flat_between hg hXY hX hY hsupp he₃ ht₃ (mem he _ (Or.inl rfl)) (mem he' _ (Or.inr rfl))
      b₁ b₂
  push Not at hend
  by_cases hin : ∃ j ∈ S, (D.tile j).localAngle (AffineMap.lineMap X Y t) ≠ 0
  · left
    obtain ⟨j, hjS, hj0⟩ := hin
    obtain ⟨k, hk⟩ := low_chain D hsupp (Finset.mem_filter.mp hjS).2
    have hopen : ∀ k' (j' : Fin N), (j', k') ∈ D.lineChain g c →
        (D.tile j').localAngle (AffineMap.lineMap X Y t) ≠ 0 →
        t ∈ Ioo (lo D X Y (j', k')) (hi D X Y (j', k')) := by
      intro k' j' hk' h0
      have hI : t ∈ Icc (lo D X Y (j', k')) (hi D X Y (j', k')) := by
        by_contra hn; exact h0 (ang_out hg hXY hX hY hk' hn)
      obtain ⟨n₁, n₂⟩ := hend _ hk'
      exact ⟨lt_of_le_of_ne hI.1 (Ne.symm n₁), lt_of_le_of_ne hI.2 n₂⟩
    have hjt := hopen k j hk hj0
    rw [lowSum, Finset.sum_eq_single_of_mem _ hjS]
    · exact ang_open hg hXY hX hY hk hjt
    · intro j' hj'S hj'j
      by_contra h0
      obtain ⟨k', hk'⟩ := low_chain D hsupp (Finset.mem_filter.mp hj'S).2
      have hj't := hopen k' j' hk' h0
      exact hj'j (same_of_overlap hg hXY hX hY hk' hk (by
        simp only [lt_min_iff, max_lt_iff]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hjt.1, hjt.2, hj't.1, hj't.2]))
  · right
    push Not at hin
    rw [lowSum, Finset.sum_eq_zero hin]
    positivity

include hg hXY hX hY hsupp in
theorem two_info
    (h2 : (Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c)).card = 2) :
    ∃ m M : ℝ, m < M ∧ AffineMap.lineMap X Y m ∈ D.target.carrier ∧
      AffineMap.lineMap X Y M ∈ D.target.carrier ∧
      0 < lowSum D g c (AffineMap.lineMap X Y m) ∧
      lowSum D g c (AffineMap.lineMap X Y m) < Real.pi / 2 ∧
      0 < lowSum D g c (AffineMap.lineMap X Y M) ∧
      lowSum D g c (AffineMap.lineMap X Y M) < Real.pi / 2 ∧
      ∀ t : ℝ, lowSum D g c (AffineMap.lineMap X Y t) = Real.pi ∨
        lowSum D g c (AffineMap.lineMap X Y t) < Real.pi / 2 := by
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp h2
  have ha : a ∈ Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c) := by
    rw [hS]; simp
  have hb : b ∈ Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c) := by
    rw [hS]; simp
  obtain ⟨ka, hka⟩ := low_chain D hsupp (Finset.mem_filter.mp ha).2
  obtain ⟨kb, hkb⟩ := low_chain D hsupp (Finset.mem_filter.mp hb).2
  rcases ext_or hg hXY hX hY hsupp hka with la | ra <;>
    rcases ext_or hg hXY hX hY hsupp hkb with lb | rb
  · exact absurd (left_unique hg hXY hX hY hka hkb la lb) hab
  · exact two_aux hg hXY hX hY hsupp hka hkb hab la rb hS
  · exact two_aux hg hXY hX hY hsupp hkb hka (Ne.symm hab) lb ra (by rw [hS, Finset.pair_comm])
  · exact absurd (right_unique hg hXY hX hY hka hkb ra rb) hab

end Side2

end NotAllSupported

open NotAllSupported Classical in
/-- **Lemma `lemma:notallsupported`.** In an `N`-tiling of any triangle `ABC` with `N > 3`, no
segment of the tiling can support all `N` tiles.

"A segment supports a tile" means that an edge of the tile lies on the segment. The statement is
for any segment `XY`, not only segments of the tiling. -/
theorem notallsupported {N : ℕ} (D : CongruentDissection N) (hN : 3 < N) (X Y : Plane) :
    ¬ ∀ i, ∃ k, (D.tile i).edge k ⊆ segment ℝ X Y := by
  intro hall
  have hXY : X ≠ Y := by
    rintro rfl
    obtain ⟨k, hk⟩ := hall ⟨0, by omega⟩
    rw [segment_same] at hk
    exact tri_pts_succ_ne _ k ((hk (left_mem_segment ℝ _ _)).trans (hk (right_mem_segment ℝ _ _)).symm)
  set g := crossL (Y - X) with hgdef
  set c := g X with hcdef
  have hg : g ≠ 0 := crossL_ne_zero (sub_ne_zero.mpr hXY.symm)
  have hX : g X = c := rfl
  have hY : g Y = c := by
    have h1 : g Y - g X = g (Y - X) := (map_sub g Y X).symm
    have h2 : g (Y - X) = 0 := by rw [hgdef, crossL_apply, cross_self]
    linarith
  have hsupp : ∀ i, ∃ k, g ((D.tile i).pts k) = c ∧ g ((D.tile i).pts (k + 1)) = c := by
    intro i
    obtain ⟨k, hk⟩ := hall i
    have lev : ∀ y ∈ segment ℝ X Y, g y = c := by
      intro y hy
      rw [segment_eq_image_lineMap] at hy
      obtain ⟨t, -, rfl⟩ := hy
      exact level_lineMap hX hY t
    exact ⟨k, lev _ (hk (left_mem_segment ℝ _ _)), lev _ (hk (right_mem_segment ℝ _ _))⟩
  -- the other side of the line
  have hg' : -g ≠ 0 := neg_ne_zero.mpr hg
  have hX' : (-g) X = -c := by simp [hX]
  have hY' : (-g) Y = -c := by simp [hY]
  have hsupp' : ∀ i, ∃ k, (-g) ((D.tile i).pts k) = -c ∧ (-g) ((D.tile i).pts (k + 1)) = -c := by
    intro i
    obtain ⟨k, h1, h2⟩ := hsupp i
    exact ⟨k, by simp [h1], by simp [h2]⟩
  set S := Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c) with hSdef
  set S' := Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, (-g) y ≤ -c) with hS'def
  have hpart : ∀ i, ¬ (∀ y ∈ (D.tile i).carrier, g y ≤ c) ↔
      (∀ y ∈ (D.tile i).carrier, (-g) y ≤ -c) := by
    intro i
    constructor
    · intro hn y hy
      rcases low_or_up D hsupp i with h | h
      · exact absurd h hn
      · simp only [LinearMap.neg_apply, neg_le_neg_iff]; exact h y hy
    · intro h' hl
      obtain ⟨k, hk⟩ := low_chain D hsupp hl
      have a := apex_lt D hg hk
      have b := h' _ (subset_convexHull ℝ _ ⟨k + 2, rfl⟩)
      simp only [LinearMap.neg_apply, neg_le_neg_iff] at b
      linarith
  have hfilt : Finset.univ.filter (fun i => ¬ ∀ y ∈ (D.tile i).carrier, g y ≤ c) = S' :=
    Finset.filter_congr fun i _ => hpart i
  have hcard : S.card + S'.card = N := by
    rw [← hfilt, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have c1 : S.card ≤ 2 := card_le_two hg hXY hX hY hsupp (D := D)
  have c2 : S'.card ≤ 2 := card_le_two hg' hXY hX' hY' hsupp' (D := D)
  have h2 : S.card = 2 := by omega
  have h2' : S'.card = 2 := by omega
  obtain ⟨m, M, hmM, hmT, hMT, pm, lm, pM, lM, -⟩ := two_info hg hXY hX hY hsupp h2
  obtain ⟨-, -, -, -, -, -, -, -, -, hup⟩ := two_info hg' hXY hX' hY' hsupp' h2'
  -- the extreme ends on the side `g ≤ c` are vertices of `ABC`
  have vert : ∀ t : ℝ, AffineMap.lineMap X Y t ∈ D.target.carrier →
      0 < lowSum D g c (AffineMap.lineMap X Y t) →
      lowSum D g c (AffineMap.lineMap X Y t) < Real.pi / 2 →
      AffineMap.lineMap X Y t ∈ Set.range D.target.pts := by
    intro t hT hpos hlt
    have hnint : AffineMap.lineMap X Y t ∉ interior D.target.carrier := fun hi => by
      have := half_angle_sum D.toDissection hi hg (level_lineMap hX hY t)
        (fun i _ => low_or_up D hsupp i)
      have : lowSum D g c (AffineMap.lineMap X Y t) = Real.pi := this
      linarith
    have hsum : ∑ i, (D.tile i).localAngle (AffineMap.lineMap X Y t) =
        lowSum D g c (AffineMap.lineMap X Y t) + lowSum D (-g) (-c) (AffineMap.lineMap X Y t) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c)]
      congr 1
      exact Finset.sum_congr (Finset.filter_congr fun i _ => hpart i) fun _ _ => rfl
    have hle := Tri.localAngle_le_pi _ hnint
    rw [← D.toDissection.sum_localAngle_eq, hsum] at hle
    rcases hup t with h | h
    · linarith
    · by_contra hnv
      have := Tri.localAngle_frontier _ ⟨subset_closure hT, hnint⟩ hnv
      rw [← D.toDissection.sum_localAngle_eq, hsum] at this
      linarith
  obtain ⟨k₁, hk₁⟩ := vert m hmT pm lm
  obtain ⟨k₂, hk₂⟩ := vert M hMT pM lM
  have hne : D.target.pts k₁ ≠ D.target.pts k₂ := by
    rw [hk₁, hk₂]
    intro h
    have := AffineMap.lineMap_injective ℝ hXY h
    linarith
  have hk : k₁ ≠ k₂ := fun h => hne (by rw [h])
  obtain ⟨k₃, h₃₁, h₃₂⟩ : ∃ w : Fin 3, w ≠ k₁ ∧ w ≠ k₂ :=
    (by decide : ∀ a b : Fin 3, ∃ w : Fin 3, w ≠ a ∧ w ≠ b) k₁ k₂
  -- a tile on each side
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨i', hi'⟩ := Finset.card_pos.mp (by omega : 0 < S'.card)
  obtain ⟨k, hkc⟩ := low_chain D hsupp (Finset.mem_filter.mp hi).2
  obtain ⟨k', hkc'⟩ := low_chain D hsupp' (Finset.mem_filter.mp hi').2
  have a₁ := apex_lt D hg hkc
  have a₂ := apex_lt D hg' hkc'
  simp only [LinearMap.neg_apply, neg_lt_neg_iff] at a₂
  refine NotAllSupported.not_straddle D.target hg hne (by rw [hk₁]; exact level_lineMap hX hY m)
    (by rw [hk₂]; exact level_lineMap hX hY M) (m := k₃)
    (by rw [Tri.coord_vertex, if_neg h₃₁]) (by rw [Tri.coord_vertex, if_neg h₃₂])
    (tile_subset_target D.toDissection i (subset_convexHull ℝ _ ⟨k + 2, rfl⟩))
    (tile_subset_target D.toDissection i' (subset_convexHull ℝ _ ⟨k' + 2, rfl⟩)) a₁ a₂

end TriangleTiling
