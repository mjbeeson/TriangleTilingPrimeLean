/-
The edges on a side of `T`, for Sections 12–13 of Beeson–Roșu: the tile edges lying in a side
partition it, so their lengths add up to the side's length (`side_sum`), and the numbers `p, q, r`
of `a, b, c` edges on it give `|S| = pa + qb + rc` (`RunSetting.side_counts`).
-/
import TriangleTiling.Prime.IsoBeta

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set MeasureTheory

variable {N : ℕ}

open Classical in
/-- The tile edges lying in the side `j` of the target. -/
noncomputable def sideSet (D : Dissection N) (j : Fin 3) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e =>
    (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1))

/-- **The edges in a side add up to its length.** -/
theorem side_sum (D : Dissection N) (j : Fin 3) :
    ∑ e ∈ sideSet D j, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.target.pts j) (D.target.pts (j + 1)) := by
  classical
  set A := D.target.pts j
  set B := D.target.pts (j + 1)
  set w := B - A
  set σ := cross w (D.target.pts (j + 2) - A)
  have hw : w ≠ 0 := sub_ne_zero.mpr (tri_pts_succ_ne _ _).symm
  have hσ : σ ≠ 0 := by
    have := D.target.det_ne_zero
    rw [← D.target.cross_edgeVec j, Tri.edgeVec_eq, Tri.edgeVec'_eq] at this; exact this
  set g : Plane →ₗ[ℝ] ℝ := (-σ) • crossL w
  have hg : g ≠ 0 := smul_ne_zero (neg_ne_zero.mpr hσ) (crossL_ne_zero hw)
  set c₀ := -σ * cross w A
  have hgy : ∀ y, g y = -σ * cross w y := fun y => by simp [g]
  have hle : ∀ y ∈ D.target.carrier, g y ≤ c₀ := by
    intro y hy
    have := target_side D.target j y hy
    rw [hgy]; simp only [c₀]
    have e : cross w (y - A) = cross w y - cross w A := cross_sub_right _ _ _
    rw [e] at this; nlinarith
  have honS : ∀ y ∈ segment ℝ A B, g y = c₀ := by
    intro y hy
    rw [segment_eq_image_lineMap] at hy
    obtain ⟨s, -, rfl⟩ := hy
    rw [hgy, AffineMap.lineMap_apply_module', cross_add_right, cross_smul_right,
      Erdos634.Geometry.cross_self]; simp only [c₀]; ring
  have hmem : ∀ e ∈ sideSet D j, e ∈ D.lineChain g c₀ := by
    intro e he
    have hsub := (Finset.mem_filter.mp he).2
    rw [Dissection.mem_lineChain]
    exact ⟨honS _ (hsub (left_mem_segment ℝ _ _)), honS _ (hsub (right_mem_segment ℝ _ _)),
      fun i => hle _ (TwoCs.pts_mem_target D _ _)⟩
  obtain ⟨part, hcov, -, -⟩ := D.side_walk j
  have hsum := sum_hausdorff_of_partition (sideSet D j) (fun e => (D.tile e.1).edge e.2)
    (segment ℝ A B) ∅ Set.finite_empty
    (fun e _ => (D.tile e.1).isClosed_edge e.2 |>.measurableSet)
    (fun e₁ h₁ e₂ h₂ hne y hy z hz => by
      by_contra hyz
      exact hne (lineChain_eq_of_two D hg (hmem e₁ h₁) (hmem e₂ h₂) hyz hy hz))
    (fun e he => (Finset.mem_filter.mp he).2)
    (by
      rw [Set.diff_empty]
      intro y hy
      rw [← hcov] at hy
      obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
      have : e ∈ sideSet D j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        intro z hz; rw [← hcov]; exact Set.mem_biUnion he hz⟩
      exact Set.mem_biUnion this hye)
  simp only [Tri.hausdorff_edge] at hsum
  rw [MeasureTheory.hausdorffMeasure_segment] at hsum
  have h1 : ENNReal.ofReal (∑ e ∈ sideSet D j, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist A B) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)]
    simp only [← edist_dist]; exact hsum
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun e _ => dist_nonneg) dist_nonneg).mp h1

namespace RunSetting

variable {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- Counting with three distinct values. -/
theorem count3 {ι : Type*} (s : Finset ι) (len : ι → ℝ)
    (hlen : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ p q r : ℕ, ∑ e ∈ s, len e = p * a + q * b + r * c ∧
      ((∃ e ∈ s, len e = a) → 0 < p) ∧ ((∃ e ∈ s, len e = b) → 0 < q) ∧
      ((∃ e ∈ s, len e = c) → 0 < r) := by
  classical
  have hab := hS.a_ne_b
  have hac := hS.a_lt_c.ne
  have hbc := hS.b_lt_c.ne
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, by simp, by simp, by simp, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨p, q, r, h1, ha', hb', hc'⟩ := ih (fun e he => hlen e (Finset.mem_insert_of_mem he))
    rw [Finset.sum_insert hx, h1]
    have split : ∀ (P : ι → Prop), (∃ e ∈ insert x s, P e) → P x ∨ ∃ e ∈ s, P e := by
      rintro P ⟨e, he, hP⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Or.inl hP
      · exact Or.inr ⟨e, he, hP⟩
    rcases hlen x (Finset.mem_insert_self x s) with hx' | hx' | hx'
    · refine ⟨p + 1, q, r, by rw [hx']; push_cast; ring, fun _ => by omega, fun h => ?_, fun h => ?_⟩
      · rcases split _ h with h | h
        · exact absurd (hx'.symm.trans h) hab
        · exact hb' h
      · rcases split _ h with h | h
        · exact absurd (hx'.symm.trans h) hac
        · exact hc' h
    · refine ⟨p, q + 1, r, by rw [hx']; push_cast; ring, fun h => ?_, fun _ => by omega, fun h => ?_⟩
      · rcases split _ h with h | h
        · exact absurd (h.symm.trans hx') hab
        · exact ha' h
      · rcases split _ h with h | h
        · exact absurd (hx'.symm.trans h) hbc
        · exact hc' h
    · refine ⟨p, q, r + 1, by rw [hx']; push_cast; ring, fun h => ?_, fun h => ?_, fun _ => by omega⟩
      · rcases split _ h with h | h
        · exact absurd (h.symm.trans hx') hac
        · exact ha' h
      · rcases split _ h with h | h
        · exact absurd (h.symm.trans hx') hbc
        · exact hb' h

/-- **The edge counts on a side**: `|S| = pa + qb + rc`, where an `a`, `b` or `c` edge of a tile on
`S` forces `p`, `q` or `r` to be positive. -/
theorem side_counts (j : Fin 3) :
    ∃ p q r : ℕ, dist (D.target.pts j) (D.target.pts (j + 1)) = p * a + q * b + r * c ∧
      ∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
        segment ℝ P Q ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) →
        (dist P Q = a → 0 < p) ∧ (dist P Q = b → 0 < q) ∧ (dist P Q = c → 0 < r) := by
  obtain ⟨p, q, r, h1, ha', hb', hc'⟩ := hS.count3 (sideSet D.toDissection j)
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    (fun e _ => hS.edge_len e.1 e.2)
  refine ⟨p, q, r, (side_sum D.toDissection j).symm.trans h1, fun t P Q hte hsub => ?_⟩
  obtain ⟨e, he, -, hends⟩ := edge_of_tileEdge hte
  have hmem : (t, e) ∈ sideSet D.toDissection j := by
    classical
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he]; exact hsub⟩
  have hd : dist ((D.tile t).pts e) ((D.tile t).pts (e + 1)) = dist P Q := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, dist_comm]
  exact ⟨fun h => ha' ⟨(t, e), hmem, hd.trans h⟩, fun h => hb' ⟨(t, e), hmem, hd.trans h⟩,
    fun h => hc' ⟨(t, e), hmem, hd.trans h⟩⟩

end RunSetting

end TriangleTiling.Prime
