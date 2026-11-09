/-
`lemma:longrun`, second part: on every side `S` of `T` there is a run of `c` edges stopped at both
ends (`RunSetting.stopped_run`).
-/
import TriangleTiling.Prime.RunsLongA

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

set_option maxHeartbeats 1600000 in
open Classical in
/-- **A run stopped at both ends.** Every side `S` of `T` supports a run of `c` edges, of length
`n ≥ 1`, stopped at both ends. -/
theorem stopped_run (j : Fin 3) :
    ∃ (n : ℕ) (U I : Plane) (t : ℕ → Fin N), 1 ≤ n ∧ run D j c n U I t ∧
      StoppedAt D j γ (U + ((n : ℝ) * c) • I) I ∧ StoppedAt D j γ U (-I) := by
  have hc := hS.c_pos
  set A := D.target.pts j
  set B := D.target.pts (j + 1)
  have hAB : A ≠ B := tri_pts_succ_ne _ _
  have hdAB : 0 < dist A B := dist_pos.mpr hAB
  set L : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap A B with hLdef
  have hL : Function.Injective L := AffineMap.lineMap_injective ℝ hAB
  have hL0 : L 0 = A := AffineMap.lineMap_apply_zero A B
  have hL1 : L 1 = B := AffineMap.lineMap_apply_one A B
  have hseg : segment ℝ A B = L '' Icc 0 1 := by rw [segment_eq_image_lineMap]
  obtain ⟨part, hcov, hdisj, -⟩ := D.toDissection.side_walk j
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1)
  have hmem : ∀ e ∈ part, u e ∈ segment ℝ A B ∧ v e ∈ segment ℝ A B := by
    intro e he
    rw [← hcov]
    exact ⟨mem_biUnion he (left_mem_segment ℝ _ _), mem_biUnion he (right_mem_segment ℝ _ _)⟩
  have hpar : ∀ x ∈ segment ℝ A B, ∃ t ∈ Icc (0 : ℝ) 1, L t = x := by
    intro x hx; rw [hseg] at hx; exact hx
  let tu : Fin N × Fin 3 → ℝ := fun e =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = u e then h.choose else 0
  let tv : Fin N × Fin 3 → ℝ := fun e =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = v e then h.choose else 0
  have htu : ∀ e ∈ part, tu e ∈ Icc (0 : ℝ) 1 ∧ L (tu e) = u e := by
    intro e he
    have h := hpar _ (hmem e he).1
    simp only [tu, dif_pos h]
    exact h.choose_spec
  have htv : ∀ e ∈ part, tv e ∈ Icc (0 : ℝ) 1 ∧ L (tv e) = v e := by
    intro e he
    have h := hpar _ (hmem e he).2
    simp only [tv, dif_pos h]
    exact h.choose_spec
  let l : Fin N × Fin 3 → ℝ := fun e => min (tu e) (tv e)
  let r : Fin N × Fin 3 → ℝ := fun e => max (tu e) (tv e)
  have hsegk : ∀ e ∈ part, segment ℝ (u e) (v e) = L '' Icc (l e) (r e) := by
    intro e he
    rw [← (htu e he).2, ← (htv e he).2, ← image_segment, segment_eq_Icc']
  have hchain : IntervalChain part l r := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e he
      have hne : tu e ≠ tv e := fun h => tri_pts_succ_ne (D.tile e.1) e.2
        (by show u e = v e; rw [← (htu e he).2, ← (htv e he).2, h])
      exact min_lt_max.mpr hne
    · intro e he
      exact ⟨le_min (htu e he).1.1 (htv e he).1.1, max_le (htu e he).1.2 (htv e he).1.2⟩
    · intro x hx0 hx1
      have hLx : L x ∈ segment ℝ A B := by rw [hseg]; exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [← hcov] at hLx
      obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hLx
      rw [show (D.tile e.1).edge e.2 = segment ℝ (u e) (v e) from rfl, hsegk e he] at hxe
      obtain ⟨y, hy, hyx⟩ := hxe
      exact ⟨e, he, (hL hyx) ▸ hy.1, (hL hyx) ▸ hy.2⟩
    · intro e he e' he' hne x hx y hy
      have h := hdisj e he e' he' hne
      have hx' : L x ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 := by
        rw [show (D.tile e.1).edge e.2 = segment ℝ (u e) (v e) from rfl,
          show (D.tile e'.1).edge e'.2 = segment ℝ (u e') (v e') from rfl, hsegk e he, hsegk e' he']
        exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
      have hy' : L y ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 := by
        rw [show (D.tile e.1).edge e.2 = segment ℝ (u e) (v e) from rfl,
          show (D.tile e'.1).edge e'.2 = segment ℝ (u e') (v e') from rfl, hsegk e he, hsegk e' he']
        exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
      exact hL (h hx' hy')
  -- The two ends of each edge, as `L (l e)` and `L (r e)`.
  have hends : ∀ e ∈ part, TileEdge D e.1 (L (l e)) (L (r e)) := by
    intro e he
    simp only [l, r]
    rcases le_total (tu e) (tv e) with h | h
    · rw [min_eq_left h, max_eq_right h, (htu e he).2, (htv e he).2]
      exact ⟨e.2, e.2 + 1, fin3_ne_succ _, rfl, rfl⟩
    · rw [min_eq_right h, max_eq_left h, (htu e he).2, (htv e he).2]
      exact ⟨e.2 + 1, e.2, (fin3_ne_succ _).symm, rfl, rfl⟩
  have hdist : ∀ e ∈ part, dist (L (l e)) (L (r e)) = (r e - l e) * dist A B := by
    intro e he
    rw [hLdef, dist_lineMap_lineMap, Real.dist_eq, abs_of_nonpos (by linarith [hchain.lt e he])]
    ring
  -- The kinds of edges.
  let isC : Fin N × Fin 3 → Prop := fun e => dist (L (l e)) (L (r e)) = c
  let isE : Fin N × Fin 3 → Prop := fun e => ¬ isC e ∧ HasAngle D e.1 (L (r e)) γ
  let isW : Fin N × Fin 3 → Prop := fun e => ¬ isC e ∧ HasAngle D e.1 (L (l e)) γ
  have hkind : ∀ e ∈ part, isC e ∨ isE e ∨ isW e := by
    intro e he
    by_cases hC : isC e
    · exact Or.inl hC
    · right
      obtain ⟨ea, eb, -⟩ := hS.edge_ends (hends e he)
      rcases hS.tileEdge_len (hends e he) with hd | hd | hd
      · rcases ea hd with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inl ⟨hC, h⟩
        · exact Or.inr ⟨hC, h⟩
      · rcases eb hd with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inl ⟨hC, h⟩
        · exact Or.inr ⟨hC, h⟩
      · exact absurd hd hC
  have hnoγ : ∀ (t : Fin N) (P : Plane), P ∈ Set.range D.target.pts → ¬ HasAngle D t P γ := by
    rintro t P ⟨j', rfl⟩ ⟨l', hl', ha⟩
    exact hS.noγ j' t l' hl' ha
  have hW0 : ∀ e ∈ part, isW e → l e ≠ 0 := by
    intro e _ hW h0
    apply hnoγ e.1 A ⟨j, rfl⟩
    have := hW.2; rw [h0, hL0] at this; exact this
  have hE1 : ∀ e ∈ part, isE e → r e ≠ 1 := by
    intro e _ hE h1
    apply hnoγ e.1 B ⟨j + 1, rfl⟩
    have := hE.2; rw [h1, hL1] at this; exact this
  have hLS : ∀ x, 0 ≤ x → x ≤ 1 → L x ∈ segment ℝ A B := fun x h0 h1 => by
    rw [hseg]; exact ⟨x, ⟨h0, h1⟩, rfl⟩
  have hEW : ∀ e ∈ part, ∀ e' ∈ part, isE e → isW e' → r e ≠ l e' := by
    intro e he e' he' hE hW hre
    have h1 := hE.2
    have h2 := hW.2
    rw [← hre] at h2
    have hZ : L (r e) ∈ segment ℝ A B :=
      hLS _ ((hchain.sub e he).1.trans (hchain.lt e he).le) (hchain.sub e he).2
    have htt := hS.gamma_unique_side hZ h1 h2
    -- the same tile would have two edges on `S`, hence all its vertices on `S`
    by_cases hee : e.2 = e'.2
    · have : e = e' := Prod.ext htt hee
      subst this
      have := hS.hasAngle_unique hW.2 hE.2
      exact (hchain.lt e he).ne (hL this)
    · apply two_vertices_on_line (D.tile e.1) (crossL (B - A)) (cross (B - A) A)
        (crossL_ne_zero (sub_ne_zero.mpr hAB.symm))
      have honS : ∀ x ∈ segment ℝ A B, crossL (B - A) x = cross (B - A) A := by
        intro x hx
        rw [segment_eq_image_lineMap] at hx
        obtain ⟨s, -, rfl⟩ := hx
        rw [crossL_apply, AffineMap.lineMap_apply_module', cross_add_right, cross_smul_right,
          Erdos634.Geometry.cross_self, mul_zero, zero_add]
      intro i
      have hcases : i = e.2 ∨ i = e.2 + 1 ∨ i = e'.2 ∨ i = e'.2 + 1 := by
        revert hee; generalize e.2 = p; generalize e'.2 = q
        fin_cases i <;> fin_cases p <;> fin_cases q <;> decide
      rcases hcases with h | h | h | h <;> rw [h]
      · exact honS _ (hmem e he).1
      · exact honS _ (hmem e he).2
      · rw [htt]; exact honS _ (hmem e' he').1
      · rw [htt]; exact honS _ (hmem e' he').2
  -- The stretch.
  obtain ⟨X, Y, hX0, hXY, hY1, hX, hY, hin⟩ :=
    hchain.stopped_stretch isC isE isW hkind hW0 hE1 hEW
  set d := c / dist A B
  have hd : 0 < d := div_pos hc hdAB
  have hin' : ∀ e ∈ part, l e < Y → X < r e → X ≤ l e ∧ r e ≤ Y ∧ r e = l e + d := by
    intro e he h1 h2
    obtain ⟨hC, h3, h4⟩ := hin e he h1 h2
    refine ⟨h3, h4, ?_⟩
    have := hdist e he
    rw [show dist (L (l e)) (L (r e)) = c from hC] at this
    simp only [d]; field_simp; linarith
  obtain ⟨n, hn1, hn, hstart⟩ := hchain.uniform_stretch hd hXY hX0 hY1 hin'
  -- The run.
  set I : Plane := (dist A B)⁻¹ • (B - A)
  set U := L X
  have hLx : ∀ x, L x = U + ((x - X) * dist A B) • I := by
    intro x
    simp only [U, I, hLdef, AffineMap.lineMap_apply_module', smul_smul]
    rw [show (x - X) * dist A B * (dist A B)⁻¹ = x - X by field_simp]
    rw [sub_smul]; abel
  have hI : ‖I‖ = 1 := by
    simp only [I]; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hdAB.le), ← dist_eq_norm,
      dist_comm B A, inv_mul_cancel₀ hdAB.ne']
  have hLi : ∀ i : ℝ, L (X + i * d) = U + (i * c) • I := by
    intro i; rw [hLx]; congr 2; simp only [d]; field_simp; ring
  have hEx : ∀ i : ℕ, ∃ e, i < n → e ∈ part ∧ l e = X + i * d := by
    intro i
    by_cases hi : i < n
    · obtain ⟨e, he, hl⟩ := hstart i hi; exact ⟨e, fun _ => ⟨he, hl⟩⟩
    · exact ⟨(⟨0, by
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h; exact (D.toDissection.pos.ne' rfl).elim
        · exact h⟩, 0), fun h => absurd h hi⟩
  choose E hE using hEx
  refine ⟨n, U, I, fun i => (E (i - 1)).1, hn1, ⟨hI, ?_, ?_⟩, ?_, ?_⟩
  · -- the run lies on `S`
    have hV : U + ((n : ℝ) * c) • I = L Y := by
      rw [show Y = X + n * d by linarith, hLi]
    rw [hV]
    exact (convex_segment A B).segment_subset (hLS X hX0 (by linarith)) (hLS Y (by linarith) hY1)
  · -- the edges
    intro i hi
    obtain ⟨he, hl⟩ := hE i hi
    simp only [Nat.add_sub_cancel]
    obtain ⟨-, -, hr⟩ := hin' (E i) he (by
      rw [hl]; have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
      nlinarith) (by have := hchain.lt (E i) he; have : (0 : ℝ) ≤ i * d := by positivity
                     linarith)
    have := hends (E i) he
    rw [hr, hl, hLi, show X + i * d + d = X + ((i : ℝ) + 1) * d by ring, hLi] at this
    exact this
  · -- stopped at `V`
    have hV : U + ((n : ℝ) * c) • I = L Y := by
      rw [show Y = X + n * d by linarith, hLi]
    rw [hV]
    rcases hY with h1 | ⟨e, he, hW, hle⟩
    · left; rw [h1, hL1]; exact ⟨j + 1, rfl⟩
    · right
      refine ⟨e.1, (r e - Y) * dist A B, by
        have := hchain.lt e he; rw [hle] at this; nlinarith, ?_, ?_, ?_⟩
      · have : L Y + ((r e - Y) * dist A B) • I = L (r e) := by rw [hLx, hLx]; module
        rw [this]
        exact (convex_segment A B).segment_subset (hLS Y (by linarith) hY1)
          (hLS _ ((hchain.sub e he).1.trans (hchain.lt e he).le) (hchain.sub e he).2)
      · have : L Y + ((r e - Y) * dist A B) • I = L (r e) := by rw [hLx, hLx]; module
        rw [this, ← hle]; exact hends e he
      · rw [← hle]; exact hW.2
  · -- stopped at `U`
    rcases hX with h0 | ⟨e, he, hEe, hre⟩
    · left; simp only [U]; rw [h0, hL0]; exact ⟨j, rfl⟩
    · right
      refine ⟨e.1, (X - l e) * dist A B, by
        have := hchain.lt e he; rw [hre] at this; nlinarith, ?_, ?_, ?_⟩
      · have : U + ((X - l e) * dist A B) • (-I) = L (l e) := by rw [hLx]; module
        rw [this]
        exact (convex_segment A B).segment_subset (hLS X hX0 (by linarith))
          (hLS _ (hchain.sub e he).1 ((hchain.lt e he).le.trans (hchain.sub e he).2))
      · have : U + ((X - l e) * dist A B) • (-I) = L (l e) := by rw [hLx]; module
        rw [this]; simp only [U]; rw [← hre]; exact tileEdge_symm (hends e he)
      · simp only [U]; rw [← hre]; exact hEe.2

end RunSetting

end TriangleTiling.Prime
