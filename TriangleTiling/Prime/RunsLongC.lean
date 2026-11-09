/-
`lemma:longrun`, third part: runs read backwards and parts of runs; two tiles with edges along a
common ray lie on opposite sides of it; and Case 1 of the printed proof (`case_start`): a run stopped
at both ends whose first tile has its `α` angle at its start contradicts `lemma:rootedblock`.
-/
import TriangleTiling.Prime.RunsLongB

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

/-- A run read backwards. -/
theorem run_reverse {j : Fin 3} {c : ℝ} {n : ℕ} {U I : Plane} {t : ℕ → Fin N}
    (h : run D j c n U I t) :
    run D j c n (U + ((n : ℝ) * c) • I) (-I) (fun i => t (n + 1 - i)) := by
  obtain ⟨hI, hseg, hedge⟩ := h
  refine ⟨by rw [norm_neg, hI], ?_, fun i hi => ?_⟩
  · have : U + ((n : ℝ) * c) • I + ((n : ℝ) * c) • -I = U := by rw [smul_neg]; abel
    rw [this, segment_symm]; exact hseg
  · have h1 := hedge (n - 1 - i) (by omega)
    have e1 : n - 1 - i + 1 = n + 1 - (i + 1) := by omega
    rw [e1] at h1
    have c1 : ((n - 1 - i : ℕ) : ℝ) = n - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [c1] at h1
    have p1 : U + (((n : ℝ) - 1 - i) * c) • I =
        U + ((n : ℝ) * c) • I + (((i : ℝ) + 1) * c) • -I := by
      rw [smul_neg, ← sub_eq_add_neg, add_sub_assoc, ← sub_smul]; ring_nf
    have p2 : U + (((n : ℝ) - 1 - i + 1) * c) • I = U + ((n : ℝ) * c) • I + ((i : ℝ) * c) • -I := by
      rw [smul_neg, ← sub_eq_add_neg, add_sub_assoc, ← sub_smul]; ring_nf
    rw [p1, p2] at h1
    exact tileEdge_symm h1

theorem mem_seg_frac {U I : Plane} {c : ℝ} {i n : ℕ} (hi : i ≤ n) :
    U + ((i : ℝ) * c) • I ∈ segment ℝ U (U + ((n : ℝ) * c) • I) := by
  rw [segment_eq_image_lineMap]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : i = 0 := by omega
    subst this
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨(i : ℝ) / n, ⟨by positivity, (div_le_one hn').mpr (by exact_mod_cast hi)⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul, add_comm]
    congr 2; field_simp

/-- The last part of a run. -/
theorem run_drop {j : Fin 3} {c : ℝ} {n : ℕ} {U I : Plane} {t : ℕ → Fin N}
    (h : run D j c n U I t) {i : ℕ} (hi : i ≤ n) :
    run D j c (n - i) (U + ((i : ℝ) * c) • I) I (fun m => t (i + m)) := by
  obtain ⟨hI, hseg, hedge⟩ := h
  refine ⟨hI, ?_, fun m hm => ?_⟩
  · have e : U + ((i : ℝ) * c) • I + (((n - i : ℕ) : ℝ) * c) • I = U + ((n : ℝ) * c) • I := by
      rw [Nat.cast_sub hi, add_assoc, ← add_smul]; ring_nf
    rw [e]
    exact Subset.trans ((convex_segment _ _).segment_subset (mem_seg_frac hi)
      (right_mem_segment ℝ _ _)) hseg
  · have h1 := hedge (i + m) (by omega)
    have e1 : U + (((i + m : ℕ) : ℝ) * c) • I = U + ((i : ℝ) * c) • I + ((m : ℝ) * c) • I := by
      push_cast; module
    have e2 : U + ((((i + m : ℕ) : ℝ) + 1) * c) • I =
        U + ((i : ℝ) * c) • I + (((m : ℝ) + 1) * c) • I := by
      push_cast; module
    rw [e1, e2] at h1
    simpa [add_assoc] using h1

/-- The first part of a run. -/
theorem run_take {j : Fin 3} {c : ℝ} {n : ℕ} {U I : Plane} {t : ℕ → Fin N}
    (h : run D j c n U I t) {i : ℕ} (hi : i ≤ n) : run D j c i U I t := by
  obtain ⟨hI, hseg, hedge⟩ := h
  refine ⟨hI, ?_, fun m hm => hedge m (by omega)⟩
  exact Subset.trans ((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
    (mem_seg_frac hi)) hseg

/-- **Two tiles with edges along a common ray lie on opposite sides of it.** -/
theorem opposite_of_ray {t₀ t₁ : Fin N} (hne : t₀ ≠ t₁) {X w : Plane} (hw : w ≠ 0) {s₀ s₁ : ℝ}
    (hs₀ : 0 < s₀) (hs₁ : 0 < s₁) (h₀ : TileEdge D t₀ X (X + s₀ • w))
    (h₁ : TileEdge D t₁ X (X + s₁ • w)) :
    ∀ y ∈ Set.range (D.tile t₀).pts, ∀ z ∈ Set.range (D.tile t₁).pts,
      cross w (y - X) * cross w (z - X) ≤ 0 := by
  intro y hy z hz
  by_contra hpos
  push Not at hpos
  set κ := cross w (z - X)
  set g : Plane →ₗ[ℝ] ℝ := (-κ) • crossL w
  have hκ : κ ≠ 0 := by intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hg : g ≠ 0 := smul_ne_zero (neg_ne_zero.mpr hκ) (crossL_ne_zero hw)
  have hgX : ∀ p, g p - g X = -κ * cross w (p - X) := by
    intro p; simp only [g, LinearMap.smul_apply, crossL_apply, smul_eq_mul, cross_sub_right]; ring
  -- each tile lies in `{g ≤ g X}`
  have hside : ∀ (t : Fin N) (s : ℝ), 0 < s → TileEdge D t X (X + s • w) →
      ∀ v ∈ Set.range (D.tile t).pts, 0 < cross w (v - X) * κ →
      ∀ i, g ((D.tile t).pts i) ≤ g X := by
    intro t s hs ht v hv hvκ i
    obtain ⟨l, l', hll, hl, hl'⟩ := ht
    obtain ⟨Z, hZr, -, -, -, -⟩ := third_vertex hl hl' (by
      intro h; have : s • w = 0 := by rw [← add_right_inj X, ← h, add_zero]
      exact smul_ne_zero hs.ne' hw this)
    have hv' := hZr ▸ hv
    have hcZ : ∀ p ∈ ({X, X + s • w, Z} : Set Plane), p = Z ∨ cross w (p - X) = 0 := by
      rintro p (rfl | rfl | rfl)
      · right; simp [cross]
      · right; rw [add_sub_cancel_left, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero]
      · left; rfl
    have hZκ : 0 < cross w (Z - X) * κ := by
      rcases hcZ v hv' with rfl | h0
      · exact hvκ
      · rw [h0, zero_mul] at hvκ; exact absurd hvκ (lt_irrefl _)
    have hi : (D.tile t).pts i ∈ ({X, X + s • w, Z} : Set Plane) := hZr ▸ ⟨i, rfl⟩
    have := hgX ((D.tile t).pts i)
    rcases hcZ _ hi with h | h
    · rw [h] at this ⊢; nlinarith
    · rw [h, mul_zero] at this; linarith
  have hz' : 0 < cross w (z - X) * κ := mul_self_pos.mpr hκ
  have hy' : 0 < cross w (y - X) * κ := hpos
  have hs₀' := hside t₀ s₀ hs₀ h₀ y hy hy'
  have hs₁' := hside t₁ s₁ hs₁ h₁ z hz hz'
  -- the two edges are in the same chain and share two points
  obtain ⟨e₀, he₀, -, hends₀⟩ := edge_of_tileEdge h₀
  obtain ⟨e₁, he₁, -, hends₁⟩ := edge_of_tileEdge h₁
  have hgline : ∀ s : ℝ, g (X + s • w) = g X := by
    intro s; have := hgX (X + s • w)
    rw [add_sub_cancel_left, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero,
      mul_zero] at this; linarith
  have hmem : ∀ (t : Fin N) (e : Fin 3) (s : ℝ), (∀ i, g ((D.tile t).pts i) ≤ g X) →
      (((D.tile t).pts e = X ∧ (D.tile t).pts (e + 1) = X + s • w) ∨
        ((D.tile t).pts e = X + s • w ∧ (D.tile t).pts (e + 1) = X)) →
      (t, e) ∈ D.lineChain g (g X) := by
    intro t e s hle hends
    rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, hle⟩
    · rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> first | rfl | exact hgline s
    · rcases hends with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> first | rfl | exact hgline s
  have hc₀ := hmem t₀ e₀ s₀ hs₀' hends₀
  have hc₁ := hmem t₁ e₁ s₁ hs₁' hends₁
  set σ := min s₀ s₁
  have hσ : 0 < σ := lt_min hs₀ hs₁
  have heq := lineChain_eq_of_two D.toDissection hg hc₀ hc₁ (y := X) (z := X + σ • w)
    (fun h => by
      have : σ • w = 0 := by rw [← add_right_inj X, ← h, add_zero]
      exact smul_ne_zero hσ.ne' hw this)
    ⟨by rw [he₀]; exact left_mem_segment ℝ _ _, by rw [he₁]; exact left_mem_segment ℝ _ _⟩
    ⟨by rw [he₀]; exact mem_seg_smul hs₀ hσ.le (min_le_left _ _),
      by rw [he₁]; exact mem_seg_smul hs₁ hσ.le (min_le_right _ _)⟩
  exact hne (congrArg Prod.fst heq)

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- Every tile has its `γ` angle somewhere. -/
theorem exists_gamma (t : Fin N) : ∃ W, HasAngle D t W γ := by
  have hγ := hS.gamma
  have d01 := hS.angles_ne (t := t) (show (0 : Fin 3) ≠ 1 by decide)
  have d02 := hS.angles_ne (t := t) (show (0 : Fin 3) ≠ 2 by decide)
  have d12 := hS.angles_ne (t := t) (show (1 : Fin 3) ≠ 2 by decide)
  have v := fun l => vertex_data hS.tile t l
  rcases v 0 with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rcases v 1 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (h0.trans h1.symm) d01
    · rcases v 2 with ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩
      · exact absurd (h0.trans h2.symm) d02
      · exact absurd (h1.trans h2.symm) d12
      · exact ⟨_, 2, rfl, h2⟩
    · exact ⟨_, 1, rfl, h1⟩
  · rcases v 1 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · rcases v 2 with ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩
      · exact absurd (h1.trans h2.symm) d12
      · exact absurd (h0.trans h2.symm) d02
      · exact ⟨_, 2, rfl, h2⟩
    · exact absurd (h0.trans h1.symm) d01
    · exact ⟨_, 1, rfl, h1⟩
  · exact ⟨_, 0, rfl, h0⟩

/-- An edge at a `β` corner is an `a` or `c` edge. -/
theorem beta_edge {t : Fin N} {X Y : Plane} (hX : HasAngle D t X β) (h : TileEdge D t X Y) :
    dist X Y = a ∨ dist X Y = c := by
  obtain ⟨-, eb, -⟩ := hS.edge_ends h
  have hαβ := hS.alpha_ne_beta
  have hβγ : β ≠ γ := by have := hS.gamma; have := hS.angles_pos; intro h; linarith
  rcases hS.tileEdge_len h with hd | hd | hd
  · exact Or.inl hd
  · rcases eb hd with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (angle_eq_of_two h1 hX) hαβ
    · exact absurd (angle_eq_of_two hX h1) hβγ
  · exact Or.inr hd

end RunSetting

end TriangleTiling.Prime
