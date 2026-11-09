/-
A one-dimensional lemma for `lemma:longrun` of Beeson–Roșu, Section 11: on a chain of intervals
partitioning `[0, 1]`, each a `c` interval, or "pointing east" (its tile's `γ` at its right end), or
"pointing west" (at its left end), with no west-pointing interval at `0`, no east-pointing one at `1`,
and no east-pointing and west-pointing intervals meeting at a point, there is a stretch `[X, Y]`
made of `c` intervals, with `X = 0` or the right end of an east-pointing interval, and `Y = 1` or the
left end of a west-pointing interval: a run stopped at both ends.
-/
import TriangleTiling.Tiling.Intervals
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace TriangleTiling

open Set

variable {ι : Type*} {s : Finset ι} {l r : ι → ℝ}

/-- No interval of a chain straddles a right end of another, or `0`. -/
theorem IntervalChain.not_straddle (h : IntervalChain s l r) {k : ι} (hk : k ∈ s) {X : ℝ}
    (hX : X = 0 ∨ ∃ k' ∈ s, r k' = X) : ¬ (l k < X ∧ X < r k) := by
  rintro ⟨h1, h2⟩
  rcases hX with rfl | ⟨k', hk', rfl⟩
  · linarith [(h.sub k hk).1]
  · have hne : k ≠ k' := by rintro rfl; linarith
    set M := max (l k) (l k')
    have hM : M < r k' := max_lt h1 (h.lt k' hk')
    have hx : r k' ∈ Icc (l k) (r k) ∩ Icc (l k') (r k') := ⟨⟨h1.le, h2.le⟩, ⟨(h.lt k' hk').le, le_rfl⟩⟩
    have hy : (M + r k') / 2 ∈ Icc (l k) (r k) ∩ Icc (l k') (r k') := by
      refine ⟨⟨?_, by linarith⟩, ⟨?_, by linarith⟩⟩
      · have := le_max_left (l k) (l k'); linarith
      · have := le_max_right (l k) (l k'); linarith
    have := h.disj k hk k' hk' hne hx hy
    linarith

/-- No interval of a chain straddles a left end of another, or `1`. -/
theorem IntervalChain.not_straddle' (h : IntervalChain s l r) {k : ι} (hk : k ∈ s) {Y : ℝ}
    (hY : Y = 1 ∨ ∃ k' ∈ s, l k' = Y) : ¬ (l k < Y ∧ Y < r k) := by
  rintro ⟨h1, h2⟩
  rcases hY with rfl | ⟨k', hk', rfl⟩
  · linarith [(h.sub k hk).2]
  · have hne : k ≠ k' := by rintro rfl; linarith
    set M := min (r k) (r k')
    have hM : l k' < M := lt_min h2 (h.lt k' hk')
    have hx : l k' ∈ Icc (l k) (r k) ∩ Icc (l k') (r k') := ⟨⟨h1.le, h2.le⟩, ⟨le_rfl, (h.lt k' hk').le⟩⟩
    have hy : (M + l k') / 2 ∈ Icc (l k) (r k) ∩ Icc (l k') (r k') := by
      refine ⟨⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩⟩
      · have := min_le_left (r k) (r k'); linarith
      · have := min_le_right (r k) (r k'); linarith
    have := h.disj k hk k' hk' hne hx hy
    linarith

/-- **A run stopped at both ends.** -/
theorem IntervalChain.stopped_stretch [DecidableEq ι] (h : IntervalChain s l r)
    (isC isE isW : ι → Prop) [DecidablePred isE] [DecidablePred isW]
    (hkind : ∀ k ∈ s, isC k ∨ isE k ∨ isW k)
    (hW0 : ∀ k ∈ s, isW k → l k ≠ 0) (hE1 : ∀ k ∈ s, isE k → r k ≠ 1)
    (hEW : ∀ k ∈ s, ∀ k' ∈ s, isE k → isW k' → r k ≠ l k') :
    ∃ X Y : ℝ, 0 ≤ X ∧ X < Y ∧ Y ≤ 1 ∧ (X = 0 ∨ ∃ k ∈ s, isE k ∧ r k = X) ∧
      (Y = 1 ∨ ∃ k ∈ s, isW k ∧ l k = Y) ∧
      ∀ k ∈ s, l k < Y → X < r k → isC k ∧ X ≤ l k ∧ r k ≤ Y := by
  classical
  -- `Y`: the least left end of a west-pointing interval, or `1`.
  set Ws := (s.filter isW).image l
  set Y : ℝ := if hW : Ws.Nonempty then Ws.min' hW else 1
  have hY : Y = 1 ∨ ∃ k ∈ s, isW k ∧ l k = Y := by
    by_cases hW : Ws.Nonempty
    · right
      have := Ws.min'_mem hW
      obtain ⟨k, hk, hkl⟩ := Finset.mem_image.mp this
      exact ⟨k, (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2, by simp only [Y, dif_pos hW]; exact hkl⟩
    · left; simp only [Y, dif_neg hW]
  have hYle : ∀ k ∈ s, isW k → Y ≤ l k := by
    intro k hk hkW
    have hW : Ws.Nonempty := ⟨l k, Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hkW⟩, rfl⟩⟩
    simp only [Y, dif_pos hW]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hkW⟩, rfl⟩)
  have hY1 : Y ≤ 1 := by
    rcases hY with h1 | ⟨k, hk, -, hkl⟩
    · rw [h1]
    · rw [← hkl]; linarith [(h.sub k hk).2, h.lt k hk]
  -- `X`: the greatest right end `≤ Y` of an east-pointing interval, or `0`.
  set Es := ((s.filter isE).filter fun k => r k ≤ Y).image r
  set X : ℝ := if hE : Es.Nonempty then Es.max' hE else 0
  have hX : X = 0 ∨ ∃ k ∈ s, isE k ∧ r k = X := by
    by_cases hE : Es.Nonempty
    · right
      have := Es.max'_mem hE
      obtain ⟨k, hk, hkr⟩ := Finset.mem_image.mp this
      simp only [Finset.mem_filter] at hk
      exact ⟨k, hk.1.1, hk.1.2, by simp only [X, dif_pos hE]; exact hkr⟩
    · left; simp only [X, dif_neg hE]
  have hXge : ∀ k ∈ s, isE k → r k ≤ Y → r k ≤ X := by
    intro k hk hkE hkY
    have hE : Es.Nonempty := ⟨r k, Finset.mem_image.mpr ⟨k, by simp [hk, hkE, hkY], rfl⟩⟩
    simp only [X, dif_pos hE]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨k, by simp [hk, hkE, hkY], rfl⟩)
  have hX0 : 0 ≤ X := by
    rcases hX with h0 | ⟨k, hk, -, hkr⟩
    · rw [h0]
    · rw [← hkr]; linarith [(h.sub k hk).1, h.lt k hk]
  have hXY : X ≤ Y := by
    by_cases hE : Es.Nonempty
    · have := Es.max'_mem hE
      obtain ⟨k, hk, hkr⟩ := Finset.mem_image.mp this
      simp only [Finset.mem_filter] at hk
      simp only [X, dif_pos hE]; rw [← hkr]; exact hk.2
    · simp only [X, dif_neg hE]
      rcases hY with h1 | ⟨k, hk, -, hkl⟩
      · rw [h1]; norm_num
      · rw [← hkl]; exact (h.sub k hk).1
  -- The intervals meeting `(X, Y)` are `c` intervals inside `[X, Y]`.
  have hin : ∀ k ∈ s, l k < Y → X < r k → isC k ∧ X ≤ l k ∧ r k ≤ Y := by
    intro k hk h1 h2
    have hlX : X ≤ l k := by
      by_contra hlt; push Not at hlt
      exact h.not_straddle hk (hX.imp id fun ⟨k', hk', _, e⟩ => ⟨k', hk', e⟩) ⟨hlt, h2⟩
    have hrY : r k ≤ Y := by
      by_contra hlt; push Not at hlt
      exact h.not_straddle' hk (hY.imp id fun ⟨k', hk', _, e⟩ => ⟨k', hk', e⟩) ⟨h1, hlt⟩
    refine ⟨?_, hlX, hrY⟩
    rcases hkind k hk with hc | he | hw
    · exact hc
    · exfalso
      have := hXge k hk he hrY
      linarith [h.lt k hk]
    · exfalso
      have := hYle k hk hw
      linarith
  -- `X < Y`.
  have hXY' : X < Y := by
    refine lt_of_le_of_ne hXY fun hXY => ?_
    rcases hX with h0 | ⟨k, hk, hkE, hkr⟩ <;> rcases hY with h1 | ⟨k', hk', hkW, hkl⟩
    · rw [h0, h1] at hXY; norm_num at hXY
    · exact hW0 k' hk' hkW (hkl.trans (hXY.symm.trans h0))
    · exact hE1 k hk hkE (hkr.trans (hXY.trans h1))
    · exact hEW k hk k' hk' hkE hkW (hkr.trans (hXY.trans hkl.symm))
  exact ⟨X, Y, hX0, hXY', hY1, hX, hY, hin⟩

/-- **The stretch is a uniform chain.** If every interval meeting `(X, Y)` lies in `[X, Y]` and has
length `d > 0`, then `Y - X = n d` for some `n ≥ 1` and each `[X + i d, X + (i+1) d]`, `i < n`, is an
interval of the chain. -/
theorem IntervalChain.uniform_stretch (h : IntervalChain s l r) {X Y d : ℝ} (hd : 0 < d)
    (hXY : X < Y) (hX0 : 0 ≤ X) (hY1 : Y ≤ 1)
    (hin : ∀ k ∈ s, l k < Y → X < r k → X ≤ l k ∧ r k ≤ Y ∧ r k = l k + d) :
    ∃ n : ℕ, 1 ≤ n ∧ Y - X = n * d ∧ ∀ i < n, ∃ k ∈ s, l k = X + i * d := by
  classical
  -- An interval starts at `X`.
  have hstart : ∃ k ∈ s, l k = X := by
    set y := X + min d (Y - X) / 2
    have hy1 : X < y := by have := lt_min hd (sub_pos.mpr hXY); simp only [y]; linarith
    have hy2 : y < Y := by have := min_le_right d (Y - X); simp only [y]; linarith
    obtain ⟨k, hk, hlk, hrk⟩ := h.cover y (by linarith) (by linarith)
    obtain ⟨hX', hY', hd'⟩ := hin k hk (by linarith) (by linarith)
    refine ⟨k, hk, le_antisymm ?_ hX'⟩
    by_contra hgt; push Not at hgt
    -- the point midway between `X` and `l k` lies in another interval, which would start before `X`
    set z := (X + l k) / 2
    have hz1 : X < z := by simp only [z]; linarith
    have hz2 : z < l k := by simp only [z]; linarith
    obtain ⟨k', hk', hl', hr'⟩ := h.cover z (by linarith) (by linarith [(h.sub k hk).2])
    obtain ⟨hX'', -, hd''⟩ := hin k' hk' (by linarith) (by linarith)
    have hne : k' ≠ k := by rintro rfl; linarith
    -- `k'` cannot overlap `k`, so it ends by `l k`, and starts before `X`
    have hr'' : r k' ≤ l k := by
      by_contra hlt; push Not at hlt
      have hlk := h.lt k hk
      set M := min (r k') (r k)
      have h1 := min_le_left (r k') (r k)
      have h2 := min_le_right (r k') (r k)
      have h3 : l k < M := lt_min hlt hlk
      have hx : l k ∈ Icc (l k') (r k') ∩ Icc (l k) (r k) :=
        ⟨⟨by linarith, hlt.le⟩, ⟨le_rfl, hlk.le⟩⟩
      have hy : (l k + M) / 2 ∈ Icc (l k') (r k') ∩ Icc (l k) (r k) :=
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      have := h.disj k' hk' k hk hne hx hy
      linarith
    have : y < X + d := by have := min_le_left d (Y - X); simp only [y]; linarith
    linarith
  -- Successive intervals.
  have hstep : ∀ i : ℕ, X + i * d < Y → ∃ k ∈ s, l k = X + i * d := by
    intro i
    induction i with
    | zero => intro _; simpa using hstart
    | succ i ih =>
      intro hi
      have hi' : X + i * d < Y := by push_cast at hi; linarith
      obtain ⟨k, hk, hlk⟩ := ih hi'
      have hid : (0 : ℝ) ≤ i * d := by positivity
      obtain ⟨-, -, hrk⟩ := hin k hk (by linarith) (by linarith [h.lt k hk])
      have hr1 : r k ≠ 1 := by rw [hrk, hlk]; push_cast at hi; intro e; linarith
      obtain ⟨k', hk', hl'⟩ := h.exists_left_eq_right hk hr1
      have e : l k' = X + ((i + 1 : ℕ) : ℝ) * d := by rw [hl', hrk, hlk]; push_cast; ring
      exact ⟨k', hk', e⟩
  -- The last one.
  obtain ⟨N, hN⟩ := exists_nat_gt ((Y - X) / d)
  have hex : ∃ i : ℕ, Y ≤ X + (i + 1) * d := ⟨N, by
    rw [div_lt_iff₀ hd] at hN; linarith⟩
  set i₀ := Nat.find hex
  have hi₀ : Y ≤ X + (i₀ + 1) * d := Nat.find_spec hex
  have hlt : X + i₀ * d < Y := by
    by_cases h0 : i₀ = 0
    · rw [h0]; simpa using hXY
    · have := Nat.find_min hex (show i₀ - 1 < i₀ by omega)
      push Not at this
      have e : ((i₀ - 1 : ℕ) : ℝ) + 1 = i₀ := by rw [Nat.cast_sub (by omega)]; simp
      rw [e] at this; exact this
  obtain ⟨k, hk, hlk⟩ := hstep i₀ hlt
  have hid : (0 : ℝ) ≤ i₀ * d := by positivity
  obtain ⟨-, hrY, hrk⟩ := hin k hk (by linarith) (by linarith [h.lt k hk])
  refine ⟨i₀ + 1, by omega, ?_, fun i hi => hstep i ?_⟩
  · push_cast; rw [hrk, hlk] at hrY; linarith
  · have : (i : ℝ) + 1 ≤ i₀ + 1 := by exact_mod_cast hi
    have : (i : ℝ) * d ≤ i₀ * d := by nlinarith
    linarith

end TriangleTiling
