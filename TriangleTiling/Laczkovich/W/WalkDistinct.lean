/-
Facts about Bonfioli's chains of tiles along a segment (`WalkT`, `WalkR`), used for
`theorem:notprime120` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723):

* the tiles of a chain are distinct, and the tiles of the chains on the two sides of a segment are
  distinct from each other (a triangle has at most one edge on a line);
* each tile of a chain has an edge on the segment.
-/
import Erdos634.Draft.LaczFormalRGEnds
import Erdos634.Draft.LaczFormalRGGa

open scoped Classical

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.Graph (V2 neg2 toV2 TriStep crs dt Par)

namespace Walks

variable {N : ℕ}

theorem toV2_add (u v : Plane) : toV2 (u + v) = ((toV2 u).1 + (toV2 v).1, (toV2 u).2 + (toV2 v).2) := by
  unfold toV2; ext <;> simp

theorem toV2_split (Y X' X : Plane) :
    toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
  unfold toV2; ext <;> simp

theorem toV2_inj {u v : Plane} (h : toV2 u = toV2 v) : u = v := by
  have h0 : u 0 = v 0 := congrArg Prod.fst h
  have h1 : u 1 = v 1 := congrArg Prod.snd h
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem toV2_zero : toV2 (0 : Plane) = (0, 0) := by unfold toV2; simp

/-- The direction of a step is not zero. -/
theorem d_ne_zero {T : Tri} {d : V2} {U U' : Plane} (h : TriStep T d U U') : d ≠ (0, 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h
  intro hd
  have := hpar.2
  simp [dt, hd] at this

/-- A positive multiple of a nonzero vector is not zero. -/
theorem smul_ne_zero' {d : V2} (hd : d ≠ (0, 0)) {s : ℝ} (hs : s ≠ 0) : (s * d.1, s * d.2) ≠ (0, 0) := by
  intro h
  apply hd
  have h1 : s * d.1 = 0 := congrArg Prod.fst h
  have h2 : s * d.2 = 0 := congrArg Prod.snd h
  exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hs) ((mul_eq_zero.mp h2).resolve_left hs)

/-- The positions of the entries of a left chain along `d` from `X`. -/
theorem walkT_pos {R : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT R d X Y L) :
    ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧
      ∀ e ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ T ∧ toV2 (e.2.1 - X) = (s * d.1, s * d.2) ∧
        toV2 (e.2.2 - X) = (t * d.1, t * d.2) := by
  induction W with
  | nil X => exact ⟨0, le_rfl, by rw [sub_self, toV2_zero]; simp, fun e he => absurd he (by simp)⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, hL⟩ := ih
    refine ⟨c + T, by positivity, ?_, fun e he => ?_⟩
    · rw [toV2_split Y X' X, hTe, hcw]; ext <;> simp <;> ring
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨0, c, le_rfl, hc, by linarith, by rw [sub_self, toV2_zero]; simp, hcw⟩
      · obtain ⟨s, t, hs, hst, htT, e1, e2⟩ := hL e he
        refine ⟨c + s, c + t, by positivity, by linarith, by linarith, ?_, ?_⟩
        · rw [toV2_split e.2.1 X' X, e1, hcw]; ext <;> simp <;> ring
        · rw [toV2_split e.2.2 X' X, e2, hcw]; ext <;> simp <;> ring

/-- The positions of the entries of a right chain along `d` from `X`. -/
theorem walkR_pos {R : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR R d X Y L) :
    ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧
      ∀ e ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ T ∧ toV2 (e.2.1 - X) = (s * d.1, s * d.2) ∧
        toV2 (e.2.2 - X) = (t * d.1, t * d.2) := by
  induction W with
  | nil X => exact ⟨0, le_rfl, by rw [sub_self, toV2_zero]; simp, fun e he => absurd he (by simp)⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    have hcw' : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by unfold toV2; ext <;> simp
      rw [this, hcw]; simp [neg2]
    obtain ⟨T, hT, hTe, hL⟩ := ih
    refine ⟨c + T, by positivity, ?_, fun e he => ?_⟩
    · rw [toV2_split Y X' X, hTe, hcw']; ext <;> simp <;> ring
    · rcases List.mem_cons.mp he with rfl | he
      · exact ⟨0, c, le_rfl, hc, by linarith, by rw [sub_self, toV2_zero]; simp, hcw'⟩
      · obtain ⟨s, t, hs, hst, htT, e1, e2⟩ := hL e he
        refine ⟨c + s, c + t, by positivity, by linarith, by linarith, ?_, ?_⟩
        · rw [toV2_split e.2.1 X' X, e1, hcw']; ext <;> simp <;> ring
        · rw [toV2_split e.2.2 X' X, e2, hcw']; ext <;> simp <;> ring

theorem crs_smul_self (d : V2) (s : ℝ) : crs d (s * d.1, s * d.2) = 0 := by
  simp only [crs]; ring

theorem crs_neg2 (d w : V2) : crs (neg2 d) w = - crs d w := by
  simp only [crs, neg2]; ring

theorem fin3_two {x y z w : Fin 3} (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y) (hw : w ≠ z) :
    w = x ∨ w = y := by
  revert x y z w; decide

theorem fin3_third {x y z w : Fin 3} (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x)
    (hwy : w ≠ y) : w = z := by
  revert x y z w; decide

/-- **One edge on a line, same direction.** If a tile has steps `U → U'` and `V → V'` along `d`,
and `V, V'` lie on the line of the first step, then `V = U`. -/
theorem step_same {T : Tri} {d : V2} {U U' V V' : Plane} (h1 : TriStep T d U U') (h2 : TriStep T d V V')
    (hV : crs d (toV2 (V - U)) = 0) (hV' : crs d (toV2 (V' - U)) = 0) : V = U := by
  obtain ⟨kk, f, g, hkk, hf, hfk, hgk, hgf, hpar, hpos⟩ := h1
  obtain ⟨kk', f', g', hk', hf', hfk', -, -, hpar', -⟩ := h2
  have hk'g : kk' ≠ g := by rintro rfl; rw [hk'] at hpos; linarith
  have hf'g : f' ≠ g := by rintro rfl; rw [hf'] at hpos; linarith
  rcases fin3_two hfk hgk hgf hk'g with hA | hA
  · rw [← hk', hA, hkk]
  · rcases fin3_two hfk hgk hgf hf'g with hB | hB
    · exfalso
      have e1 : V = U' := hk'.symm.trans (hA ▸ hf)
      have e2 : V' = U := hf'.symm.trans (hB ▸ hkk)
      rw [e1, e2] at hpar'
      have e : dt (toV2 (U' - U)) d + dt (toV2 (U - U')) d = 0 := by
        simp only [dt, toV2, PiLp.sub_apply]; ring
      linarith [hpar.2, hpar'.2]
    · exact absurd (hB.trans hA.symm) hfk'

/-- **One edge on a line, opposite directions.** A tile cannot have a step `U → U'` along `d` and a
step `V → V'` along `-d` with `V, V'` on the line of the first. -/
theorem step_opp {T : Tri} {d : V2} {U U' V V' : Plane} (h1 : TriStep T d U U')
    (h2 : TriStep T (neg2 d) V V') (hV : crs d (toV2 (V - U)) = 0) (hV' : crs d (toV2 (V' - U)) = 0) :
    False := by
  obtain ⟨kk, f, g, hkk, hf, hfk, hgk, hgf, hpar, hpos⟩ := h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', -, hpos'⟩ := h2
  have hk'g : kk' ≠ g := by rintro rfl; rw [hk'] at hpos; linarith
  have hf'g : f' ≠ g := by rintro rfl; rw [hf'] at hpos; linarith
  have hg : g' = g := by
    rcases fin3_two hfk hgk hgf hk'g with hA | hA <;> rcases fin3_two hfk hgk hgf hf'g with hB | hB
    · exact absurd (hB.trans hA.symm) hfk'
    · exact fin3_third hfk hgk hgf (hA ▸ hgk') (hB ▸ hgf')
    · exact fin3_third hfk hgk hgf (hB ▸ hgf') (hA ▸ hgk')
    · exact absurd (hB.trans hA.symm) hfk'
  subst hg
  rw [crs_neg2] at hpos'
  have e : crs d (toV2 (T.pts g' - V)) = crs d (toV2 (T.pts g' - U)) - crs d (toV2 (V - U)) := by
    simp only [crs, toV2, PiLp.sub_apply]; ring
  linarith

/-- Two points on the line through `X` along `d`: their difference has `crs d _ = 0`. -/
theorem crs_line {d : V2} {X u v : Plane} {s t : ℝ} (hu : toV2 (u - X) = (s * d.1, s * d.2))
    (hv : toV2 (v - X) = (t * d.1, t * d.2)) : crs d (toV2 (u - v)) = 0 := by
  have : toV2 (u - v) = ((toV2 (u - X)).1 - (toV2 (v - X)).1, (toV2 (u - X)).2 - (toV2 (v - X)).2) := by
    unfold toV2; ext <;> simp
  rw [this, hu, hv]; simp only [crs]; ring

/-- The tiles of a left chain are distinct. -/
theorem walkT_nodup {R : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT R d X Y L) : (L.map Prod.fst).Nodup := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hei⟩ := List.mem_map.mp hmem
    obtain ⟨_, _, _, hL⟩ := walkT_pos W
    obtain ⟨s, t, hs, hst, -, e1, e2⟩ := hL e he
    have hS2 := walkT_mem_step W e he
    rw [hei] at hS2
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    have p1 : toV2 (e.2.1 - X) = ((c + s) * d.1, (c + s) * d.2) := by
      rw [toV2_split e.2.1 X' X, e1, hcw]; ext <;> simp <;> ring
    have p2 : toV2 (e.2.2 - X) = ((c + t) * d.1, (c + t) * d.2) := by
      rw [toV2_split e.2.2 X' X, e2, hcw]; ext <;> simp <;> ring
    have hX : toV2 (X - X) = ((0 : ℝ) * d.1, (0 : ℝ) * d.2) := by rw [sub_self, toV2_zero]; simp
    have heq := step_same hS hS2 (crs_line p1 hX) (crs_line p2 hX)
    rw [heq, sub_self, toV2_zero] at p1
    exact smul_ne_zero' (d_ne_zero hS) (by positivity : c + s ≠ 0) p1.symm

/-- The tiles of a right chain are distinct. -/
theorem walkR_nodup {R : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR R d X Y L) : (L.map Prod.fst).Nodup := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hei⟩ := List.mem_map.mp hmem
    obtain ⟨_, _, _, hL⟩ := walkR_pos W
    obtain ⟨s, t, hs, hst, -, e1, e2⟩ := hL e he
    have hS2 := walkR_mem_step W e he
    rw [hei] at hS2
    have hX : toV2 (X' - X') = ((0 : ℝ) * d.1, (0 : ℝ) * d.2) := by rw [sub_self, toV2_zero]; simp
    have l1 : crs (neg2 d) (toV2 (e.2.2 - X')) = 0 := by rw [crs_neg2, e2, crs_smul_self]; simp
    have l2 : crs (neg2 d) (toV2 (e.2.1 - X')) = 0 := by rw [crs_neg2, e1, crs_smul_self]; simp
    have heq := step_same hS hS2 l1 l2
    rw [heq, sub_self, toV2_zero] at e2
    have hd : neg2 d ≠ (0, 0) := d_ne_zero hS
    have hd' : d ≠ (0, 0) := by
      intro h; apply hd; rw [h]; simp [neg2]
    exact smul_ne_zero' hd' (by linarith : t ≠ 0) e2.symm

/-- The two chains on the sides of a segment have no tile in common. -/
theorem chains_disjoint {R : RegionDissection N} {d : V2} {X Y : Plane} {P Q : List (Fin N × Plane × Plane)}
    (W1 : WalkT R d X Y P) (W2 : WalkR R d X Y Q) {e e' : Fin N × Plane × Plane} (he : e ∈ P)
    (he' : e' ∈ Q) : e.1 ≠ e'.1 := by
  intro h
  obtain ⟨_, _, _, h1⟩ := walkT_pos W1
  obtain ⟨_, _, _, h2⟩ := walkR_pos W2
  obtain ⟨s, -, -, -, -, p1, -⟩ := h1 e he
  obtain ⟨s', t', -, -, -, q1, q2⟩ := h2 e' he'
  have hS1 := walkT_mem_step W1 e he
  have hS2 := walkR_mem_step W2 e' he'
  rw [← h] at hS2
  exact step_opp hS1 hS2 (crs_line q2 p1) (crs_line q1 p1)

theorem mem_seg {d : V2} {X Y U : Plane} {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hT : 0 < T)
    (hU : toV2 (U - X) = (s * d.1, s * d.2)) (hY : toV2 (Y - X) = (T * d.1, T * d.2)) :
    U ∈ segment ℝ X Y := by
  refine ⟨1 - s / T, s / T, by
    have : s / T ≤ 1 := (div_le_one hT).mpr hsT
    linarith, div_nonneg hs hT.le, by ring, ?_⟩
  have u0 : U 0 - X 0 = s * d.1 := congrArg Prod.fst hU
  have u1 : U 1 - X 1 = s * d.2 := congrArg Prod.snd hU
  have y0 : Y 0 - X 0 = T * d.1 := congrArg Prod.fst hY
  have y1 : Y 1 - X 1 = T * d.2 := congrArg Prod.snd hY
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (-T) * u0 + s * y0
  · simp only [Fin.mk_one, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    linear_combination (-T) * u1 + s * y1

theorem fin3_adj {kk f : Fin 3} (h : f ≠ kk) : f = kk + 1 ∨ kk = f + 1 := by
  revert kk f; decide

/-- A step whose ends lie on the segment `XY` gives an edge of the tile on `XY`. -/
theorem edge_of_step {T : Tri} {d : V2} {U U' X Y : Plane} (h : TriStep T d U U')
    (hU : U ∈ segment ℝ X Y) (hU' : U' ∈ segment ℝ X Y) : ∃ k, T.edge k ⊆ segment ℝ X Y := by
  obtain ⟨kk, f, -, hkk, hf, hfk, -⟩ := h
  have hsub : segment ℝ U U' ⊆ segment ℝ X Y := (convex_segment X Y).segment_subset hU hU'
  rcases fin3_adj hfk with e | e
  · refine ⟨kk, ?_⟩
    unfold Tri.edge; rw [← e, hkk, hf]; exact hsub
  · refine ⟨f, ?_⟩
    unfold Tri.edge; rw [← e, hkk, hf, segment_symm]; exact hsub

/-- **Counting the tiles on the two sides of a segment.** At most `N`; if `N`, every tile has an
edge on the segment. -/
theorem chains_card {R : RegionDissection N} {d : V2} {X Y : Plane} {P Q : List (Fin N × Plane × Plane)}
    (W1 : WalkT R d X Y P) (W2 : WalkR R d X Y Q) :
    P.length + Q.length ≤ N ∧
      (P.length + Q.length = N → ∀ i, ∃ k, (R.tile i).edge k ⊆ segment ℝ X Y) := by
  have hnd : (P.map Prod.fst ++ Q.map Prod.fst).Nodup := by
    refine List.nodup_append.mpr ⟨walkT_nodup W1, walkR_nodup W2, ?_⟩
    intro x hx y hy hxy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hy
    exact chains_disjoint W1 W2 he he' hxy
  have hlen : (P.map Prod.fst ++ Q.map Prod.fst).length = P.length + Q.length := by simp
  have hle := hnd.length_le_card
  rw [hlen, Fintype.card_fin] at hle
  refine ⟨hle, fun heq i => ?_⟩
  have hfin : (P.map Prod.fst ++ Q.map Prod.fst).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd, hlen, heq, Fintype.card_fin]
  have hi : i ∈ P.map Prod.fst ++ Q.map Prod.fst := by
    rw [← List.mem_toFinset, hfin]; exact Finset.mem_univ i
  obtain ⟨T1, -, hT1, h1⟩ := walkT_pos W1
  obtain ⟨T2, -, hT2, h2⟩ := walkR_pos W2
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨s, t, hs, hst, htT, e1, e2⟩ := h1 e he
    have hT : 0 < T1 := by linarith
    exact edge_of_step (walkT_mem_step W1 e he) (mem_seg hs (by linarith) hT e1 hT1)
      (mem_seg (by linarith) htT hT e2 hT1)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨s, t, hs, hst, htT, e1, e2⟩ := h2 e he
    have hT : 0 < T2 := by linarith
    exact edge_of_step (walkR_mem_step W2 e he) (mem_seg (by linarith) htT hT e2 hT2)
      (mem_seg hs (by linarith) hT e1 hT2)

/-- **Counting the tiles on one side of a segment.** At most `N`; if `N`, every tile has an edge
on the segment. -/
theorem chain_card {R : RegionDissection N} {d : V2} {X Y : Plane} {P : List (Fin N × Plane × Plane)}
    (W : WalkT R d X Y P) :
    P.length ≤ N ∧ (P.length = N → ∀ i, ∃ k, (R.tile i).edge k ⊆ segment ℝ X Y) := by
  have hnd := walkT_nodup W
  have hlen : (P.map Prod.fst).length = P.length := by simp
  have hle := hnd.length_le_card
  rw [hlen, Fintype.card_fin] at hle
  refine ⟨hle, fun heq i => ?_⟩
  have hfin : (P.map Prod.fst).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd, hlen, heq, Fintype.card_fin]
  have hi : i ∈ P.map Prod.fst := by
    rw [← List.mem_toFinset, hfin]; exact Finset.mem_univ i
  obtain ⟨T1, -, hT1, h1⟩ := walkT_pos W
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
  obtain ⟨s, t, hs, hst, htT, e1, e2⟩ := h1 e he
  have hT : 0 < T1 := by linarith
  exact edge_of_step (walkT_mem_step W e he) (mem_seg hs (by linarith) hT e1 hT1)
    (mem_seg (by linarith) htT hT e2 hT1)

end Walks

end TriangleTiling.Equilateral
