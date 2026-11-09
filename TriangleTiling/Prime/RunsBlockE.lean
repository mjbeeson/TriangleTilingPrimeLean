/-
The trapezoid lemma (`lemma:block`), fifth step: the lower end of `σ`.

* `block_end`: `s = n` is impossible. If `V` is a vertex of `T`, `∇_{n-1,0}` has its `γ` angle at
  `V`, contrary to the standing assumption. Otherwise the run is stopped at `V` by a tile `E'` on
  `S` east of `V` with its `γ` angle at `V`; the sector at `V` between `S` (east) and `σ` has angle
  `π - β = γ + α`, so by `lemma:angles` a single tile `G` besides `E'` fills it, with its `α` angle
  at `V` and its `b` or `c` edge on `σ` — but the edges east of `σ` are `a` edges.
* `block_next`: if `s < n`, at `q₀` the tiles `T_s = Δ_{s-1,0}` and `∇_{s-1,0}` contribute
  `β + γ`, so `T_{s+1}` has its `α` angle at `q₀`, and `T_{s+1} = Δ_{s,0}`.
-/
import TriangleTiling.Prime.RunsBlockD

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

section BlockE

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

omit hS in
theorem crdJ_sub_of_zero {X Z : Plane} (hX : crdJ U I J X = 0) :
    cross I (Z - X) = crdJ U I J Z * cross I J := by
  have h1 : cross I (X - U) = 0 := by
    unfold crdJ at hX; rcases div_eq_zero_iff.mp hX with h | h
    · exact h
    · exact absurd h hF.hIJ
  unfold crdJ
  rw [show Z - X = (Z - U) - (X - U) by abel, cross_sub_right, h1, sub_zero,
    div_mul_cancel₀ _ hF.hIJ]

omit hS in
/-- A tile with two vertices on `S` has its third vertex strictly north of `S`. -/
theorem third_strict_north {t : Fin N} {P Q Z : Plane} (h : Set.range (D.tile t).pts = {P, Q, Z})
    (hP : crdJ U I J P = 0) (hQ : crdJ U I J Q = 0) : 0 < crdJ U I J Z := by
  have hZT : Z ∈ D.target.carrier := mem_target_of_range (t := t) (by rw [h]; simp)
  refine lt_of_le_of_ne (hF.north _ hZT) fun hZ => ?_
  apply two_vertices_on_line (D.tile t) (lineF I J 0 1) (lineF I J 0 1 U)
    (lineF_ne_zero hF.hIJ (Or.inr one_ne_zero))
  intro i
  rw [lineF_apply U I J _ 0 1]
  have : (D.tile t).pts i ∈ ({P, Q, Z} : Set Plane) := h ▸ ⟨i, rfl⟩
  rcases this with e | e | e <;> rw [e]
  · rw [hP]; ring
  · rw [hQ]; ring
  · rw [← hZ]; ring

/-- **`s = n` is impossible** (the lower end of `σ` when `s = n`). -/
theorem block_end {n r : ℕ} {t : ℕ → Fin N} (hrun : run D j c n U I t) (hr : 1 ≤ r) (hrn : r < n)
    (hstop : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I) (hT : TOccurs D (lat U I J b c) n r)
    (E : ℕ → Fin N)
    (hnab : ∀ i < r, Set.range (D.tile (E i)).pts = {lat U I J b c ((n : ℝ) - i) i,
        lat U I J b c ((n : ℝ) - i - 1) (i + 1), lat U I J b c ((n : ℝ) - i) (i + 1)} ∧
      HasAngle D (E i) (lat U I J b c ((n : ℝ) - i) i) γ)
    (hσa : ∀ (G : Fin N) (τ : ℝ), 0 < τ →
      (∀ l, (b * c) * n ≤ b * crdI U I J ((D.tile G).pts l) + c * crdJ U I J ((D.tile G).pts l)) →
      TileEdge D G (lat U I J b c n 0) (lat U I J b c n 0 + τ • (b • J - c • I)) → τ * a = a) :
    False := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  set x := lat U I J b c
  set V := x n 0
  have hVU : V = U + ((n : ℝ) * c) • I := by simp [V, x, lat]
  rw [← hVU] at hstop
  obtain ⟨-, hE0γ⟩ := hnab 0 (by omega)
  have e0 : x ((n : ℝ) - ((0 : ℕ) : ℝ)) ((0 : ℕ) : ℝ) = V := by simp [V]
  replace hE0γ : HasAngle D (E 0) V γ := e0 ▸ hE0γ
  by_cases hV : V ∈ Set.range D.target.pts
  · obtain ⟨j', hj'⟩ := hV
    obtain ⟨l, hl, ha'⟩ := hE0γ
    exact hS.noγ j' (E 0) l (hl.trans hj'.symm) ha'
  obtain ⟨t', lam, hlam, -, hte, hγt'⟩ := hstop.resolve_left hV
  set w := b • J - c • I
  have hne : cross I w ≠ 0 := by
    simp only [w]; rw [cross_sub_right, cross_smul_right, cross_smul_right,
      Erdos634.Geometry.cross_self, mul_zero, sub_zero]
    exact mul_ne_zero hb.ne' hF.hIJ
  have hV0 : crdJ U I J V = 0 := by simp only [V, x]; rw [crdJ_x hF]; ring
  have hVT : V ∈ D.target.carrier := D.target.convex.segment_subset
    (subset_convexHull ℝ _ ⟨j, rfl⟩) (subset_convexHull ℝ _ ⟨j + 1, rfl⟩)
    (hVU ▸ hrun.2.1 (right_mem_segment ℝ _ _))
  have hin := hin_side hF hVT hV0 hV hne
    (by rw [Erdos634.Geometry.cross_self, zero_div])
    (by simp only [w]; rw [cross_sub_right, cross_smul_right, cross_smul_right,
      Erdos634.Geometry.cross_self, mul_zero, sub_zero, mul_div_assoc, div_self hF.hIJ]; linarith)
  have hu : RayWall D.toDissection V I := rayWall_of_tileEdge hlam hte
  -- the `a` edge of `Δ_{n-1,0}` from `V` along `w`
  obtain ⟨tq, htq⟩ := hT.1 (n - 1) 0 (by omega) (by omega)
  have hn1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hVw : V + (1 : ℝ) • w = x ((n - 1 : ℕ) : ℝ) (((0 : ℕ) : ℝ) + 1) := by
    simp only [V, x, w]; rw [lat_add_w]; congr 1 <;> simp [hn1]
  have hVq : x (((n - 1 : ℕ) : ℝ) + 1) ((0 : ℕ) : ℝ) = V := by
    simp only [V, x]; congr 1 <;> simp [hn1]
  have hv : RayWall D.toDissection V w := by
    refine rayWall_of_tileEdge (t := tq) one_pos ?_
    rw [hVw]
    refine tileEdge_of_range htq (by right; left; exact hVq.symm) (by simp) ?_
    intro h; rw [← hVq] at h; have := (x_inj hS hF h).2; simp at this
  -- the stop tile `E'` is in the sector
  obtain ⟨lV, hlV, haV⟩ := id hγt'
  obtain ⟨l1, l2, h12, h1, h2⟩ := hte
  have hl1 : l1 = lV := (D.tile t').indep.injective (h1.trans hlV.symm)
  subst hl1
  obtain ⟨l3, h31, h32, -⟩ := RunSetting.fin3_third l1 l2 h12
  set Z := (D.tile t').pts l3
  have hZ : 0 < cross I (Z - V) * cross I w := by
    rw [crdJ_sub_of_zero hF hV0]
    have hrange : Set.range (D.tile t').pts = {V, V + lam • I, Z} := by
      rw [Tri.range_pts (D.tile t') l1, h1]
      rcases fin3_others h12 h31.symm (fun h => h32 h.symm) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2, h2]
      · rw [← e1, ← e2, h2, Set.pair_comm]
    have hZn := third_strict_north hF hrange hV0 (by
      rw [crdJ_addv, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero, zero_div, hV0]; ring)
    simp only [w]; rw [cross_sub_right, cross_smul_right, cross_smul_right,
      Erdos634.Geometry.cross_self, mul_zero, sub_zero]
    have := mul_self_pos.mpr hF.hIJ
    nlinarith [mul_pos (mul_pos hZn hb) this]
  have hpts : ((D.tile t').pts (l1 + 1) = V + lam • I ∧ (D.tile t').pts (l1 + 2) = Z) ∨
      ((D.tile t').pts (l1 + 2) = V + lam • I ∧ (D.tile t').pts (l1 + 1) = Z) := by
    rcases fin3_others h12 h31.symm (fun h => h32 h.symm) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left; rw [← e1, ← e2, h2]; exact ⟨rfl, rfl⟩
    · right; rw [← e1, ← e2, h2]; exact ⟨rfl, rfl⟩
  have hE : t' ∈ sectorTiles D.toDissection V I w :=
    mem_sectorTiles_of_edge D.toDissection hlV hlam hpts hZ
  have hang : InnerProductGeometry.angle I w = π - β := by
    have : w = -(c • I - b • J) := by simp only [w]; abel
    rw [this, InnerProductGeometry.angle_neg_right, hF.aIw]
  have hEu : ∃ l, (D.tile t').pts l = V ∧ ∃ s > (0 : ℝ),
      (D.tile t').pts (l + 1) = V + s • I ∨ (D.tile t').pts (l + 2) = V + s • I :=
    ⟨l1, hlV, lam, hlam, hpts.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  obtain ⟨G, -, hGα, ⟨lG, hlG, τ, hτ, hGw⟩, hGsub⟩ := sector_minus hS hne hu hv hin hE hγt' hEu
    (by rw [hang]; intro h; linarith) (P := 1) (Q := 0) (by norm_num)
    (by rw [hang]; push_cast; linarith)
  have hGα' : HasAngle D G V α := by simpa using hGα
  -- `G` is east of `σ`
  have heast : ∀ l, (b * c) * n ≤ b * crdI U I J ((D.tile G).pts l) +
      c * crdJ U I J ((D.tile G).pts l) := by
    intro l
    have hy := hGsub (subset_convexHull ℝ _ ⟨l, rfl⟩)
    obtain ⟨p, q, hp, hq, hpq⟩ := sectorC_decomp hne hy
    rw [hpq]
    have e : V + p • I + q • w = V + ((p - q * c) • I + (q * b) • J) := by
      simp only [w, smul_sub, smul_smul, sub_smul]; abel
    rw [e]
    obtain ⟨e1, e2⟩ := crd_addv_comb hF V (p - q * c) (q * b)
    rw [e1, e2]
    simp only [V, x]; rw [crdI_x hF, crdJ_x hF]
    nlinarith [mul_nonneg hb.le hp]
  have hGe : TileEdge D G V (V + τ • w) := by
    rcases hGw with h | h
    · exact ⟨lG, lG + 1, fin3_ne_succ lG, hlG, h⟩
    · exact ⟨lG, lG + 2, by fin_cases lG <;> decide, hlG, h⟩
  have hτa := hσa G τ hτ heast hGe
  have hτ1 : τ = 1 := by
    have := mul_right_cancel₀ ha.ne' (hτa.trans (one_mul a).symm); exact this
  have hdist : dist V (V + τ • w) = a := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hτ1, norm_one, one_mul]
    have : w = -(c • I - b • J) := by simp only [w]; abel
    rw [this, norm_neg, hF.nw]
  rcases (hS.edge_ends hGe).1 hdist with ⟨h, -⟩ | ⟨h, -⟩
  · exact hS.alpha_ne_beta (RunSetting.angle_eq_of_two hGα' h)
  · have := RunSetting.angle_eq_of_two hGα' h; linarith

/-- **`T_{s+1} = Δ_{s,0}`** (when `s < n`). -/
theorem block_next {n s : ℕ} {t : ℕ → Fin N} (hrun : run D j c n U I t) (hs1 : 1 ≤ s)
    (hsn : s < n) {tq : Fin N}
    (htq : Set.range (D.tile tq).pts = {lat U I J b c ((s : ℝ) - 1) 0, lat U I J b c s 0,
      lat U I J b c ((s : ℝ) - 1) 1})
    {E₀ : Fin N} (hE₀ : HasAngle D E₀ (lat U I J b c s 0) γ) :
    Set.range (D.tile (t (s + 1))).pts =
      {lat U I J b c s 0, lat U I J b c ((s : ℝ) + 1) 0, lat U I J b c s 1} := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  set x := lat U I J b c
  set q₀ := x s 0
  have hq₀U : q₀ = U + ((s : ℝ) * c) • I := by simp [q₀, x, lat]
  have hq₁U : x ((s : ℝ) + 1) 0 = U + (((s : ℝ) + 1) * c) • I := by simp [x, lat]
  have hte := hrun.2.2 s hsn
  rw [← hq₀U, ← hq₁U] at hte
  set T' := t (s + 1)
  have hdc : dist q₀ (x ((s : ℝ) + 1) 0) = c := dist_I hS hF _ _
  -- the angles at `q₀`
  have hβq : HasAngle D tq q₀ β := by
    have := (delta_angles hS hF (u := (s : ℝ) - 1) (v := 0)
      (by rw [htq, show (s : ℝ) - 1 + 1 = s by ring, zero_add])).2.1
    rwa [show (s : ℝ) - 1 + 1 = s by ring] at this
  have hq₀0 : crdJ U I J q₀ = 0 := by simp only [q₀, x]; rw [crdJ_x hF]; ring
  have hq₀T : q₀ ∈ D.target.carrier := mem_target_of_range (t := tq) (by rw [htq]; simp [q₀])
  have hUS := hrun.2.1 (left_mem_segment ℝ _ _)
  have hVS := hrun.2.1 (right_mem_segment ℝ _ _)
  have hIne : I ≠ 0 := fun h => by have := hF.nI; rw [h, norm_zero] at this; exact zero_ne_one this
  have hn0 : (0 : ℝ) < (n : ℝ) * c := mul_pos (by exact_mod_cast (show 0 < n by omega)) hc
  have hUV : U ≠ U + ((n : ℝ) * c) • I := by
    intro h
    have : ((n : ℝ) * c) • I = 0 := by rw [← add_right_inj U, ← h, add_zero]
    exact smul_ne_zero hn0.ne' hIne this
  have hq₀v : q₀ ∉ Set.range D.target.pts := by
    apply not_vertex_of_between hF hUS hVS hUV
    rw [hq₀U]
    exact mem_openSeg_smul hIne (mul_pos (by exact_mod_cast hs1) hc)
      (mul_lt_mul_of_pos_right (by exact_mod_cast hsn) hc)
  have hpi := target_pi_of_side hF hq₀T hq₀0 hq₀v
  rcases (hS.edge_ends hte).2.2 hdc with ⟨hα1, hβ1⟩ | ⟨hβ1, -⟩
  · -- the third vertex
    obtain ⟨lP, hlP, haP⟩ := hα1
    obtain ⟨lQ, hlQ, haQ⟩ := hβ1
    have hPQ : q₀ ≠ x ((s : ℝ) + 1) 0 := by
      intro h; rw [h, dist_self] at hdc; linarith
    obtain ⟨Z, hZr, hZP, hZQ, hdP, hdQ⟩ := third_vertex hlP hlQ hPQ
    rw [(hS.opp_of_angle lQ).2.1 haQ] at hdP
    rw [(hS.opp_of_angle lP).1 haP] at hdQ
    have hZZ : Z = x s 1 := by
      apply eq_of_dist_dist (A := q₀) (B := x ((s : ℝ) + 1) 0)
      · rw [dist_comm, hdP, dist_comm]
        have := dist_J hS hF (s : ℝ) 0; rw [zero_add] at this; exact this.symm
      · rw [dist_comm, hdQ, dist_comm]
        have := dist_W hS hF (s : ℝ) 0; rw [zero_add] at this; exact this.symm
      · have hZn := third_strict_north hF hZr hq₀0 (by simp only [x]; rw [crdJ_x hF]; ring)
        rw [cross_frame (U := U) hF.hIJ, cross_frame (U := U) hF.hIJ]
        simp only [q₀, x, crdI_x hF, crdJ_x hF]
        have hcIJ : 0 < cross I J * cross I J := mul_self_pos.mpr hF.hIJ
        have e1 : ((((s : ℝ) + 1) * c - s * c) * (crdJ U I J Z - 0 * b) -
            (0 * b - 0 * b) * (crdI U I J Z - s * c)) = c * crdJ U I J Z := by ring
        have e2 : ((((s : ℝ) + 1) * c - s * c) * (1 * b - 0 * b) -
            (0 * b - 0 * b) * ((s : ℝ) * c - s * c)) = c * b := by ring
        rw [e1, e2]
        nlinarith [mul_pos (mul_pos (mul_pos hc hZn) (mul_pos hc hb)) hcIJ]
    rw [hZr, hZZ]
  · -- `β` at `q₀` is too much: `β + γ + β > π`
    exfalso
    have l1 := localAngle_of_hasAngle hβq
    have l2 := localAngle_of_hasAngle hE₀
    have l3 := localAngle_of_hasAngle hβ1
    have hβγ : β ≠ γ := by intro h; linarith
    have n12 : tq ≠ E₀ := tile_ne_of_angle (by rw [l1, l2]; exact hβγ)
    have n23 : E₀ ≠ T' := tile_ne_of_angle (by rw [l2, l3]; exact hβγ.symm)
    have n13 : tq ≠ T' := by
      apply Ne.symm
      apply tile_ne_of_pt (P := x ((s : ℝ) + 1) 0) (mem_range_of_tileEdge hte).2
      rw [htq]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have := x_inj hS hF h <;>
        linarith [this.1, this.2]
    have hF3 : ∑ i ∈ ({tq, E₀, T'} : Finset (Fin N)), (D.tile i).localAngle q₀ =
        (2 : ℕ) * α + (3 : ℕ) * β := by
      rw [Finset.sum_insert (by simp [n12, n13]), Finset.sum_pair n23, l1, l2, l3, hγ]
      push_cast; ring
    have := hS.sum_le_count (P := 3) (Q := 2) (by rw [hpi]; push_cast; linarith) _ hF3
    omega

end BlockE

end TriangleTiling.Prime
