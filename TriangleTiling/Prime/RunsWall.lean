/-
Edge decompositions along a segment, for Section 11 of Beeson–Roșu ("Runs of `c` edges").

* `tileEdge_edge`: an edge given by its two vertices is one of the tile's indexed edges.
* `RunSetting.edge_len`: every tile edge has length `a`, `b` or `c`.
* `RunSetting.wallA`, `wallB`, `wallC`: if tile edges of total length `na`, `nb` or `nc`
  (`1 ≤ n < k`) are given, then by `lemma:edgedecompositions` (A)–(C) they are all `a` edges
  (`n` of them), all `b` edges, or contain no `b` edge.
* `segment_chain_uniform`: `n` segments of length `|AB|/n` covering `AB` and meeting in at most a
  point are the `n` segments between consecutive points `A + (j/n)(B - A)`.
-/
import TriangleTiling.Prime.RunsFill
import TriangleTiling.Tiling.SegmentChain

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set

variable {N : ℕ}

theorem tileEdge_edge {D : CongruentDissection N} {t : Fin N} {P Q : Plane}
    (h : TileEdge D t P Q) : ∃ e : Fin 3,
      ((D.tile t).pts e = P ∧ (D.tile t).pts (e + 1) = Q) ∨
        ((D.tile t).pts e = Q ∧ (D.tile t).pts (e + 1) = P) := by
  obtain ⟨l, l', hll, hl, hl'⟩ := h
  have : l' = l + 1 ∨ l' = l + 2 := by
    revert hll; fin_cases l <;> fin_cases l' <;> decide
  rcases this with rfl | rfl
  · exact ⟨l, Or.inl ⟨hl, hl'⟩⟩
  · refine ⟨l + 2, Or.inr ⟨hl', ?_⟩⟩
    rw [show l + 2 + 1 = l by fin_cases l <;> rfl]; exact hl

theorem Tri.dist_edge_oppLen (T : Tri) (e : Fin 3) :
    dist (T.pts e) (T.pts (e + 1)) = T.oppLen (e + 2) := by
  unfold Tri.oppLen
  rw [show e + 2 + 1 = e by fin_cases e <;> rfl, show e + 2 + 2 = e + 1 by fin_cases e <;> rfl]

namespace RunSetting

variable {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
  (hS : RunSetting D α β γ a b c m k)
include hS

/-- Every tile edge has length `a`, `b` or `c`. -/
theorem edge_len (t : Fin N) (e : Fin 3) :
    dist ((D.tile t).pts e) ((D.tile t).pts (e + 1)) = a ∨
      dist ((D.tile t).pts e) ((D.tile t).pts (e + 1)) = b ∨
        dist ((D.tile t).pts e) ((D.tile t).pts (e + 1)) = c := by
  rw [Tri.dist_edge_oppLen]
  rcases hS.angleAt_combo t (e + 2) with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- Counting the edges of each length. -/
theorem count {ι : Type*} (S : Finset ι) (len : ι → ℝ)
    (hlen : ∀ e ∈ S, len e = a ∨ len e = b ∨ len e = c) :
    ∃ p q r : ℕ, ∑ e ∈ S, len e = p * a + q * b + r * c ∧ p + q + r = S.card ∧
      ((∃ e ∈ S, len e = b) → 0 < q) ∧ ((∃ e ∈ S, len e ≠ a) → 0 < q + r) := by
  classical
  have hab := hS.a_ne_b
  have hac := hS.a_lt_c.ne
  have hbc := hS.b_lt_c.ne
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp, by simp, by simp, by simp⟩
  | @insert x S hx ih =>
    obtain ⟨p, q, r, h1, h2, h3, h4⟩ := ih (fun e he => hlen e (Finset.mem_insert_of_mem he))
    rw [Finset.sum_insert hx, Finset.card_insert_of_notMem hx, h1]
    rcases hlen x (Finset.mem_insert_self x S) with hx' | hx' | hx'
    · refine ⟨p + 1, q, r, by rw [hx']; push_cast; ring, by omega, ?_, ?_⟩
      · rintro ⟨e, he, heb⟩
        rcases Finset.mem_insert.mp he with rfl | he
        · exact absurd (hx'.symm.trans heb) hab
        · exact h3 ⟨e, he, heb⟩
      · rintro ⟨e, he, hea⟩
        rcases Finset.mem_insert.mp he with rfl | he
        · exact absurd hx' hea
        · exact h4 ⟨e, he, hea⟩
    · exact ⟨p, q + 1, r, by rw [hx']; push_cast; ring, by omega, fun _ => by omega,
        fun _ => by omega⟩
    · refine ⟨p, q, r + 1, by rw [hx']; push_cast; ring, by omega, ?_, fun _ => by omega⟩
      rintro ⟨e, he, heb⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · exact absurd (hx'.symm.trans heb) hbc.symm
      · exact h3 ⟨e, he, heb⟩

/-- An edge decomposition in the reals is one in the integers. -/
theorem int_rel {p q r : ℕ} {L : ℝ} {L' : ℤ} (hL : L = L')
    (h : (p : ℝ) * a + q * b + r * c = L) :
    (p : ℤ) * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = L' := by
  rw [hS.ha, hS.hb, hS.hc, hL] at h
  exact_mod_cast h

/-- **Edges of total length `na` are `n` edges of length `a`** (`lemma:edgedecompositions` (A)). -/
theorem wallA {ι : Type*} {S : Finset ι} {len : ι → ℝ}
    (hlen : ∀ e ∈ S, len e = a ∨ len e = b ∨ len e = c) {n : ℕ} (hn1 : 1 ≤ n) (hnk : (n : ℤ) < k)
    (hsum : ∑ e ∈ S, len e = n * a) : (∀ e ∈ S, len e = a) ∧ S.card = n := by
  obtain ⟨p, q, r, h1, h2, -, h4⟩ := hS.count S len hlen
  have hrel := hS.int_rel (L' := (n : ℤ) * (m * k)) (by rw [hS.ha]; push_cast; ring) (h1.symm.trans hsum)
  obtain ⟨e1, e2, e3⟩ := (edgedecompositions hS.hm hS.hmk hS.cop).1 n p q r (by exact_mod_cast hn1)
    hnk (by positivity) (by positivity) (by positivity) hrel
  refine ⟨fun e he => ?_, by omega⟩
  by_contra hne
  have := h4 ⟨e, he, hne⟩
  omega

/-- **Edges of total length `nb` are `b` edges** (`lemma:edgedecompositions` (B)). -/
theorem wallB {ι : Type*} {S : Finset ι} {len : ι → ℝ}
    (hlen : ∀ e ∈ S, len e = a ∨ len e = b ∨ len e = c) {n : ℕ} (hn1 : 1 ≤ n) (hnk : (n : ℤ) < k)
    (hsum : ∑ e ∈ S, len e = n * b) : ∀ e ∈ S, len e ≠ a ∧ len e ≠ c := by
  classical
  obtain ⟨p, q, r, h1, h2, -, -⟩ := hS.count S len hlen
  have hrel := hS.int_rel (L' := (n : ℤ) * (k ^ 2 - m ^ 2)) (by rw [hS.hb]; push_cast; ring)
    (h1.symm.trans hsum)
  obtain ⟨e1, e2, e3⟩ := (edgedecompositions hS.hm hS.hmk hS.cop).2.1 n p q r
    (by exact_mod_cast hn1) hnk (by positivity) (by positivity) (by positivity) hrel
  -- `p = r = 0`: count the `a` and `c` edges separately.
  have hp : p = 0 := by exact_mod_cast e1
  have hr : r = 0 := by exact_mod_cast e3
  intro e he
  -- Recount with priorities `a` then `c`.
  have key : ∀ T : Finset ι, (∀ e ∈ T, len e = a ∨ len e = b ∨ len e = c) →
      ∀ e ∈ T, len e = a ∨ len e = c →
      ∃ p q r : ℕ, ∑ e ∈ T, len e = p * a + q * b + r * c ∧ 0 < p + r := by
    intro T hT
    induction T using Finset.induction_on with
    | empty => intro e he; simp at he
    | @insert x T hx ih =>
      intro e he hac
      rw [Finset.sum_insert hx]
      obtain ⟨p, q, r, h1', -, -, -⟩ := hS.count T len (fun e he => hT e (Finset.mem_insert_of_mem he))
      rcases Finset.mem_insert.mp he with rfl | he'
      · rcases hac with h | h
        · exact ⟨p + 1, q, r, by rw [h1', h]; push_cast; ring, by omega⟩
        · exact ⟨p, q, r + 1, by rw [h1', h]; push_cast; ring, by omega⟩
      · obtain ⟨p', q', r', h1'', h2''⟩ := ih (fun e he => hT e (Finset.mem_insert_of_mem he)) e he' hac
        rcases hT x (Finset.mem_insert_self x T) with h | h | h
        · exact ⟨p' + 1, q', r', by rw [h1'', h]; push_cast; ring, by omega⟩
        · exact ⟨p', q' + 1, r', by rw [h1'', h]; push_cast; ring, by omega⟩
        · exact ⟨p', q', r' + 1, by rw [h1'', h]; push_cast; ring, by omega⟩
  constructor
  · intro hea
    obtain ⟨p', q', r', h1', h2'⟩ := key S hlen e he (Or.inl hea)
    have hrel' := hS.int_rel (L' := (n : ℤ) * (k ^ 2 - m ^ 2)) (by rw [hS.hb]; push_cast; ring)
      (h1'.symm.trans hsum)
    obtain ⟨f1, -, f3⟩ := (edgedecompositions hS.hm hS.hmk hS.cop).2.1 n p' q' r'
      (by exact_mod_cast hn1) hnk (by positivity) (by positivity) (by positivity) hrel'
    omega
  · intro hec
    obtain ⟨p', q', r', h1', h2'⟩ := key S hlen e he (Or.inr hec)
    have hrel' := hS.int_rel (L' := (n : ℤ) * (k ^ 2 - m ^ 2)) (by rw [hS.hb]; push_cast; ring)
      (h1'.symm.trans hsum)
    obtain ⟨f1, -, f3⟩ := (edgedecompositions hS.hm hS.hmk hS.cop).2.1 n p' q' r'
      (by exact_mod_cast hn1) hnk (by positivity) (by positivity) (by positivity) hrel'
    omega

/-- **Edges of total length `nc` contain no `b` edge** (`lemma:edgedecompositions` (C)). -/
theorem wallC {ι : Type*} {S : Finset ι} {len : ι → ℝ}
    (hlen : ∀ e ∈ S, len e = a ∨ len e = b ∨ len e = c) {n : ℕ} (hn1 : 1 ≤ n) (hnk : (n : ℤ) < k)
    (hsum : ∑ e ∈ S, len e = n * c) : ∀ e ∈ S, len e ≠ b := by
  obtain ⟨p, q, r, h1, -, h3, -⟩ := hS.count S len hlen
  have hrel := hS.int_rel (L' := (n : ℤ) * k ^ 2) (by rw [hS.hc]; push_cast; ring)
    (h1.symm.trans hsum)
  have := (edgedecompositions hS.hm hS.hmk hS.cop).2.2.1 n p q r (by exact_mod_cast hn1) hnk
    (by positivity) (by positivity) (by positivity) hrel
  intro e he heb
  have := h3 ⟨e, he, heb⟩
  omega

end RunSetting

/-! ### Uniform chains of segments -/

open Classical in
/-- **A uniform chain.** If `n` nondegenerate segments, each of length `|AB|/n`, cover `AB` and
pairwise meet in at most one point, then for each `j < n` one of them joins
`A + (j/n)(B - A)` and `A + ((j+1)/n)(B - A)`. -/
theorem segment_chain_uniform {ι : Type*} (A B : Plane) (hAB : A ≠ B)
    (s : Finset ι) (u v : ι → Plane) (huv : ∀ k ∈ s, u k ≠ v k)
    (hcov : (⋃ k ∈ s, segment ℝ (u k) (v k)) = segment ℝ A B)
    (hdisj : ∀ k ∈ s, ∀ j ∈ s, k ≠ j →
      (segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j)).Subsingleton)
    {n : ℕ} (hn : 0 < n) (hlen : ∀ k ∈ s, dist (u k) (v k) * n = dist A B) :
    ∀ j < n, ∃ k ∈ s,
      (u k = AffineMap.lineMap A B ((j : ℝ) / n) ∧
        v k = AffineMap.lineMap A B (((j : ℝ) + 1) / n)) ∨
      (u k = AffineMap.lineMap A B (((j : ℝ) + 1) / n) ∧
        v k = AffineMap.lineMap A B ((j : ℝ) / n)) := by
  set L : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap A B with hLdef
  have hL : Function.Injective L := AffineMap.lineMap_injective ℝ hAB
  have hseg : segment ℝ A B = L '' Icc 0 1 := by
    rw [segment_eq_image_lineMap]
  have hmem : ∀ k ∈ s, u k ∈ segment ℝ A B ∧ v k ∈ segment ℝ A B := by
    intro k hk
    rw [← hcov]
    exact ⟨mem_biUnion hk (left_mem_segment ℝ _ _), mem_biUnion hk (right_mem_segment ℝ _ _)⟩
  have hpar : ∀ x ∈ segment ℝ A B, ∃ t ∈ Icc (0 : ℝ) 1, L t = x := by
    intro x hx; rw [hseg] at hx; exact hx
  let tu : ι → ℝ := fun k =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = u k then h.choose else 0
  let tv : ι → ℝ := fun k =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = v k then h.choose else 0
  have htu : ∀ k ∈ s, tu k ∈ Icc (0 : ℝ) 1 ∧ L (tu k) = u k := by
    intro k hk
    have h := hpar _ (hmem k hk).1
    simp only [tu, dif_pos h]
    exact h.choose_spec
  have htv : ∀ k ∈ s, tv k ∈ Icc (0 : ℝ) 1 ∧ L (tv k) = v k := by
    intro k hk
    have h := hpar _ (hmem k hk).2
    simp only [tv, dif_pos h]
    exact h.choose_spec
  let l : ι → ℝ := fun k => min (tu k) (tv k)
  let r : ι → ℝ := fun k => max (tu k) (tv k)
  have hsegk : ∀ k ∈ s, segment ℝ (u k) (v k) = L '' Icc (l k) (r k) := by
    intro k hk
    rw [← (htu k hk).2, ← (htv k hk).2, ← image_segment, segment_eq_Icc']
  have hchain : IntervalChain s l r := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      have hne : tu k ≠ tv k := fun h => huv k hk (by rw [← (htu k hk).2, ← (htv k hk).2, h])
      exact min_lt_max.mpr hne
    · intro k hk
      exact ⟨le_min (htu k hk).1.1 (htv k hk).1.1, max_le (htu k hk).1.2 (htv k hk).1.2⟩
    · intro x hx0 hx1
      have hLx : L x ∈ segment ℝ A B := by rw [hseg]; exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [← hcov] at hLx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hLx
      rw [hsegk k hk] at hxk
      obtain ⟨y, hy, hyx⟩ := hxk
      exact ⟨k, hk, (hL hyx) ▸ hy.1, (hL hyx) ▸ hy.2⟩
    · intro k hk j hj hkj x hx y hy
      have h := hdisj k hk j hj hkj
      have hx' : L x ∈ segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j) := by
        rw [hsegk k hk, hsegk j hj]
        exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
      have hy' : L y ∈ segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j) := by
        rw [hsegk k hk, hsegk j hj]
        exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
      exact hL (h hx' hy')
  have hdAB : 0 < dist A B := dist_pos.mpr hAB
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  -- Each interval has length `1/n`.
  have hlen' : ∀ k ∈ s, r k = l k + 1 / n := by
    intro k hk
    have h := hlen k hk
    rw [← (htu k hk).2, ← (htv k hk).2, hLdef, dist_lineMap_lineMap, Real.dist_eq] at h
    have habs : |tu k - tv k| = 1 / n := by
      have h2 := mul_right_cancel₀ hdAB.ne' (show |tu k - tv k| * n * dist A B = 1 * dist A B by
        rw [one_mul]; linarith [h])
      rw [eq_div_iff hnr.ne']; exact h2
    simp only [l, r]
    rcases le_total (tu k) (tv k) with h' | h'
    · rw [min_eq_left h', max_eq_right h']
      rw [abs_of_nonpos (by linarith)] at habs; linarith
    · rw [min_eq_right h', max_eq_left h']
      rw [abs_of_nonneg (by linarith)] at habs; linarith
  -- By induction, an interval starts at each `j/n`.
  have hstart : ∀ j < n, ∃ k ∈ s, l k = (j : ℝ) / n := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨k, hk, h1, -⟩ := hchain.cover 0 le_rfl zero_le_one
      exact ⟨k, hk, by simp only [Nat.cast_zero, zero_div]; exact le_antisymm h1 (hchain.sub k hk).1⟩
    | succ j ih =>
      intro hj
      obtain ⟨k, hk, hlk⟩ := ih (by omega)
      have hrk : r k = ((j : ℝ) + 1) / n := by rw [hlen' k hk, hlk]; ring
      have hr1 : r k ≠ 1 := by
        rw [hrk]; intro h
        rw [div_eq_one_iff_eq hnr.ne'] at h
        have : ((j : ℝ) + 1) < n := by exact_mod_cast hj
        linarith
      obtain ⟨k', hk', hl'⟩ := hchain.exists_left_eq_right hk hr1
      exact ⟨k', hk', by rw [hl', hrk]; push_cast; ring⟩
  intro j hj
  obtain ⟨k, hk, hlk⟩ := hstart j hj
  have hrk : r k = ((j : ℝ) + 1) / n := by rw [hlen' k hk, hlk]; ring
  refine ⟨k, hk, ?_⟩
  simp only [l, r] at hlk hrk
  rcases le_total (tu k) (tv k) with h' | h'
  · rw [min_eq_left h'] at hlk; rw [max_eq_right h'] at hrk
    left
    exact ⟨by rw [← (htu k hk).2, hlk], by rw [← (htv k hk).2, hrk]⟩
  · rw [min_eq_right h'] at hlk; rw [max_eq_left h'] at hrk
    right
    exact ⟨by rw [← (htu k hk).2, hrk], by rw [← (htv k hk).2, hlk]⟩

end TriangleTiling.Prime
