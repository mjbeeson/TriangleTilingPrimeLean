/-
`lemma:longrun`, Case 1 (and, read backwards, Case 2): a run stopped at both ends, of length
`n < k`, whose first tile has its `α` angle at its start `U`, contradicts `lemma:rootedblock`. If `U`
is a vertex of `T`, the hypothesis of `lemma:longrun` gives the tile on the ray along the `b` edge of
`T₁`; otherwise the tile on `S` west of `U` has its `γ` there, and the remaining sector, of angle
`β`, is filled by one tile with its `β` at `U`, whose edge on that ray is its `a` or `c` edge.
-/
import TriangleTiling.Prime.RunsLongC

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ}

/-- **The hypothesis of `lemma:longrun`** on the side `S = D.target.pts j D.target.pts (j+1)`:
whenever a tile `R` has its `α` angle at an end `V` of `S` and its `c` edge `VP` on `S`, some other
tile has a vertex at `V` and its `a` or `c` edge on the ray from `V` along the `b` edge `VW` of `R`
(`W` the vertex of `R` at its `γ` angle). -/
def EndHyp (D : CongruentDissection N) (j : Fin 3) (α γ a c : ℝ) : Prop :=
  ∀ (R : Fin N) (V P W : Plane), (V = D.target.pts j ∨ V = D.target.pts (j + 1)) →
    HasAngle D R V α → TileEdge D R V P → dist V P = c →
    segment ℝ V P ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) → HasAngle D R W γ →
    ∃ R' : Fin N, R' ≠ R ∧ ∃ P' : Plane, (∃ l > (0 : ℝ), P' = V + l • (W - V)) ∧
      TileEdge D R' V P' ∧ (dist V P' = a ∨ dist V P' = c)

theorem cross_neg_right (u v : Plane) : cross u (-v) = -cross u v := by
  simp only [cross, PiLp.neg_apply]; ring

variable {D : CongruentDissection N}

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- **Case 1 of `lemma:longrun`.** -/
theorem case_start {j : Fin 3} (hyp : EndHyp D j α γ a c) {n : ℕ} {U I : Plane} {t : ℕ → Fin N}
    (hrun : run D j c n U I t) (hn : 1 ≤ n) (hnk : (n : ℤ) < k)
    (hV : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I) (hU0 : StoppedAt D j γ U (-I))
    (hU : HasAngle D (t 1) U α) : False := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  obtain ⟨W, hW⟩ := hS.exists_gamma (t 1)
  obtain ⟨hF, hr1⟩ := hS.frame hrun hn hU hW
  set J := b⁻¹ • (W - U)
  have hWJ : W - U = b • J := by simp only [J]; rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  clear_value J
  have hJne : J ≠ 0 := fun h => by have := hF.nJ; rw [h, norm_zero] at this; exact zero_ne_one this
  have hIne : I ≠ 0 := fun h => by have := hF.nI; rw [h, norm_zero] at this; exact zero_ne_one this
  have hUS : U ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) :=
    hrun.2.1 (left_mem_segment ℝ _ _)
  have hU0' : crdJ U I J U = 0 := crdJ_U
  have he1 := hrun.2.2 0 (by omega)
  simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, zero_add, one_mul] at he1
  -- A tile `t₀ ≠ T₁` with its `a` or `c` edge on the ray along `J`.
  have key : ∃ t₀ : Fin N, t₀ ≠ t 1 ∧ ∃ τ > (0 : ℝ), TileEdge D t₀ U (U + τ • J) ∧
      (τ = a ∨ τ = c) := by
    by_cases hUv : U ∈ Set.range D.target.pts
    · have hUend : U = D.target.pts j ∨ U = D.target.pts (j + 1) := by
        obtain ⟨j', hj'⟩ := hUv
        rcases fin3_cases3 j' j with e | e | e
        · left; rw [← hj', e]
        · right; rw [← hj', e]
        · exfalso
          have := third_north hF
          rw [← e, hj', hU0'] at this; exact lt_irrefl _ this
      have hdc : dist U (U + c • I) = c := by
        rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nI, mul_one,
          Real.norm_of_nonneg hc.le]
      have hsegc : segment ℝ U (U + c • I) ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) := by
        refine Subset.trans ?_ hrun.2.1
        apply (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
        have := mem_seg_frac (U := U) (I := I) (c := c) (i := 1) (n := n) hn
        simpa using this
      obtain ⟨R', hR', P', ⟨l, hl, rfl⟩, hte, hd⟩ := hyp (t 1) U (U + c • I) W hUend hU he1 hdc
        hsegc hW
      refine ⟨R', hR', l * b, mul_pos hl hb, ?_, ?_⟩
      · rw [hWJ, smul_smul] at hte; exact hte
      · rw [hWJ, smul_smul, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ,
          mul_one, Real.norm_of_nonneg (mul_pos hl hb).le] at hd; exact hd
    · obtain ⟨E', lam, hlam, -, hte, hγE⟩ := hU0.resolve_left hUv
      have hne : cross (-I) J ≠ 0 := by rw [cross_neg_left, neg_ne_zero]; exact hF.hIJ
      have hUT : U ∈ D.target.carrier := mem_target_of_range (mem_range_of_tileEdge he1).1
      have hin := hin_side hF hUT hU0' hUv hne
        (by rw [cross_neg_right, Erdos634.Geometry.cross_self, neg_zero, zero_div])
        (by rw [div_self hF.hIJ]; norm_num)
      have hu : RayWall D.toDissection U (-I) := rayWall_of_tileEdge hlam hte
      have hv : RayWall D.toDissection U J := by
        refine rayWall_of_tileEdge (t := t 1) hb ?_
        rw [← hWJ, add_sub_cancel]
        exact tileEdge_of_range hr1 (by simp) (by simp) (by
          intro h; obtain ⟨lU, hlU, haU⟩ := hU; obtain ⟨lW, hlW, haW⟩ := hW
          have : lU = lW := (D.tile (t 1)).indep.injective (hlU.trans (h.trans hlW.symm))
          rw [this] at haU; rw [haU] at haW; linarith)
      -- the tile `E'` west of `U` is in the sector
      obtain ⟨lV, hlV, haV⟩ := id hγE
      obtain ⟨l1, l2, h12, h1, h2⟩ := hte
      have hl1 : l1 = lV := (D.tile E').indep.injective (h1.trans hlV.symm)
      subst hl1
      obtain ⟨l3, h31, h32, -⟩ := fin3_third l1 l2 h12
      set Z := (D.tile E').pts l3
      have hrange : Set.range (D.tile E').pts = {U, U + lam • -I, Z} := by
        rw [Tri.range_pts (D.tile E') l1, h1]
        rcases fin3_others h12 h31.symm (fun h => h32 h.symm) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [← e1, ← e2, h2]
        · rw [← e1, ← e2, h2, Set.pair_comm]
      have hZn := third_strict_north hF hrange hU0' (by
        rw [crdJ_addv, cross_smul_right, cross_neg_right, Erdos634.Geometry.cross_self, neg_zero,
          mul_zero, zero_div, hU0']; ring)
      have hpts : ((D.tile E').pts (l1 + 1) = U + lam • -I ∧ (D.tile E').pts (l1 + 2) = Z) ∨
          ((D.tile E').pts (l1 + 2) = U + lam • -I ∧ (D.tile E').pts (l1 + 1) = Z) := by
        rcases fin3_others h12 h31.symm (fun h => h32 h.symm) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · left; rw [← e1, ← e2, h2]; exact ⟨rfl, rfl⟩
        · right; rw [← e1, ← e2, h2]; exact ⟨rfl, rfl⟩
      have hZ : 0 < cross (-I) (Z - U) * cross (-I) J := by
        rw [cross_neg_left, cross_neg_left, crdJ_sub_of_zero hF hU0']
        have := mul_self_pos.mpr hF.hIJ
        nlinarith [mul_pos hZn this]
      have hE : E' ∈ sectorTiles D.toDissection U (-I) J :=
        mem_sectorTiles_of_edge D.toDissection hlV hlam hpts hZ
      have hang : InnerProductGeometry.angle (-I) J = π - α := by
        rw [InnerProductGeometry.angle_neg_left, hF.aIJ]
      have hEu : ∃ l, (D.tile E').pts l = U ∧ ∃ s > (0 : ℝ),
          (D.tile E').pts (l + 1) = U + s • -I ∨ (D.tile E').pts (l + 2) = U + s • -I :=
        ⟨l1, hlV, lam, hlam, hpts.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
      obtain ⟨G, -, hGβ, ⟨lG, hlG, τ, hτ, hGw⟩, -⟩ := sector_minus hS hne hu hv hin hE hγE hEu
        (by rw [hang]; intro h; linarith) (P := 0) (Q := 1) (by norm_num)
        (by rw [hang]; push_cast; linarith)
      have hGβ' : HasAngle D G U β := by simpa using hGβ
      have hGe : TileEdge D G U (U + τ • J) := by
        rcases hGw with h | h
        · exact ⟨lG, lG + 1, fin3_ne_succ lG, hlG, h⟩
        · exact ⟨lG, lG + 2, by fin_cases lG <;> decide, hlG, h⟩
      refine ⟨G, fun h => ?_, τ, hτ, hGe, ?_⟩
      · rw [h] at hGβ'; exact hS.alpha_ne_beta (angle_eq_of_two hU hGβ')
      · have := hS.beta_edge hGβ' hGe
        rwa [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ, mul_one,
          Real.norm_of_nonneg hτ.le] at this
  obtain ⟨t₀, hne, τ, hτ, hte, hτac⟩ := key
  have hWe : TileEdge D (t 1) U (U + b • J) := by
    rw [← hWJ, add_sub_cancel]
    exact tileEdge_of_range hr1 (by simp) (by simp) (by
      intro h; obtain ⟨lU, hlU, haU⟩ := hU; obtain ⟨lW, hlW, haW⟩ := hW
      have : lU = lW := (D.tile (t 1)).indep.injective (hlU.trans (h.trans hlW.symm))
      rw [this] at haU; rw [haU] at haW; linarith)
  have hopp := opposite_of_ray hne hJne hτ hb hte hWe
  apply rootedblock hS hrun hn hnk hV hU hW
  refine ⟨t₀, U + τ • J, ⟨τ / b, div_pos hτ hb, ?_⟩, hte, ?_, fun y hy z hz => ?_⟩
  · rw [hWJ, smul_smul, div_mul_cancel₀ _ hb.ne']
  · rwa [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ, mul_one,
      Real.norm_of_nonneg hτ.le]
  · rw [hWJ, cross_smul_left, cross_smul_left]
    have := hopp y hy z hz
    nlinarith [mul_self_nonneg b]

end RunSetting

end TriangleTiling.Prime
