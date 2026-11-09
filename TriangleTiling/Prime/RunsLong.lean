/-
**`lemma:longrun`** of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*, Section 11.

The proof: a run `X₀ … X_h` on `S` stopped at both ends (`RunSetting.stopped_run`; see `RunsLongA`
for the difference from the printed counting argument). Suppose `h < k`. Case 1: `T₁` has its `α`
at `X₀` (`RunSetting.case_start`). Case 2: `T_h` has its `α` at `X_h` (Case 1 for the run read
backwards). Case 3: `T₁` has its `β` at `X₀` and `T_h` its `β` at `X_h`; with `i` the largest index
such that `T_i` has its `α` at `X_i`, the sector at `X_i` between the `b` edges of `T_i` and
`T_{i+1}` has angle `π - 2α = α + 2β` and is filled by three tiles with angles `α, β, β`; one of the
two outer ones has its `β` there and its `a` or `c` edge on the ray along the `b` edge of `T_i` or
`T_{i+1}`, contradicting `lemma:rootedblock` for the run `T_i, …, T₁` or `T_{i+1}, …, T_h`.

Statement checked by Beeson. The hypothesis on `S` is `EndHyp`; "`S` supports a run of at
least `k` consecutive `c` edges" is: there is a run (`definition:run`) on `S` of length `n ≥ k`.
-/
import TriangleTiling.Prime.RunsLongE

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- A run stopped at both ends at whose start `T₁` has its `α` angle, or at whose end `T_n` has its
`α` angle, is impossible if `n < k` (Cases 1 and 2). -/
theorem case_ends {j : Fin 3} (hyp : EndHyp D j α γ a c) {n : ℕ} {U I : Plane} {t : ℕ → Fin N}
    (hrun : run D j c n U I t) (hn : 1 ≤ n) (hnk : (n : ℤ) < k)
    (hV : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I) (hU0 : StoppedAt D j γ U (-I))
    (h : HasAngle D (t n) (U + ((n : ℝ) * c) • I) α) : False := by
  have hrev := run_reverse hrun
  refine hS.case_start hyp hrev hn hnk ?_ (by rw [neg_neg]; exact hV) (by simpa using h)
  have : U + ((n : ℝ) * c) • I + ((n : ℝ) * c) • -I = U := by rw [smul_neg]; abel
  rw [this]; exact hU0

/-- **Case 3 of `lemma:longrun`.** -/
theorem case_middle {j : Fin 3} {n : ℕ} {U I : Plane} {t : ℕ → Fin N}
    (hrun : run D j c n U I t) (hn : 1 ≤ n) (hnk : (n : ℤ) < k)
    (hV : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I) (hU0 : StoppedAt D j γ U (-I))
    (h1 : HasAngle D (t 1) (U + c • I) α)
    (hn' : ¬ HasAngle D (t n) (U + ((n : ℝ) * c) • I) α) : False := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  set X : ℕ → Plane := fun i => U + ((i : ℝ) * c) • I
  let P : ℕ → Prop := fun i => HasAngle D (t i) (X i) α
  have hP1 : P 1 := by simpa [P, X, smul_smul] using h1
  have hPn : ¬ P n := hn'
  set i := Nat.findGreatest P n
  have hPi : P i := Nat.findGreatest_spec (P := P) hn hP1
  have hi1 : 1 ≤ i := Nat.le_findGreatest hn hP1
  have hin : i < n := by
    have := Nat.findGreatest_le (P := P) n
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exact absurd (h ▸ hPi) hPn
  have hPi1 : ¬ P (i + 1) := Nat.findGreatest_is_greatest (P := P) (show i < i + 1 by omega)
    (show i + 1 ≤ n by omega)
  -- `T_{i+1}` has its `α` at `X_i`.
  have hte := hrun.2.2 i hin
  have hdc : dist (U + ((i : ℝ) * c) • I) (U + (((i : ℝ) + 1) * c) • I) = c := by
    rw [dist_comm, dist_eq_norm, show U + (((i : ℝ) + 1) * c) • I - (U + ((i : ℝ) * c) • I) =
      c • I by module, norm_smul, hrun.1, mul_one, Real.norm_of_nonneg hc.le]
  have hαf : HasAngle D (t (i + 1)) (X i) α := by
    rcases (hS.edge_ends hte).2.2 hdc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd (by simpa [P, X] using h) hPi1
  -- The two runs from `X_i`.
  have Rf := run_drop hrun hin.le
  have Rb := run_reverse (run_take hrun hin.le)
  have hVf : StoppedAt D j γ (U + ((i : ℝ) * c) • I + (((n - i : ℕ) : ℝ) * c) • I) I := by
    have : U + ((i : ℝ) * c) • I + (((n - i : ℕ) : ℝ) * c) • I = U + ((n : ℝ) * c) • I := by
      rw [Nat.cast_sub hin.le]; module
    rw [this]; exact hV
  have hVb : StoppedAt D j γ (U + ((i : ℝ) * c) • I + ((i : ℝ) * c) • -I) (-I) := by
    have : U + ((i : ℝ) * c) • I + ((i : ℝ) * c) • -I = U := by module
    rw [this]; exact hU0
  have hαf' : HasAngle D ((fun m => t (i + m)) 1) (U + ((i : ℝ) * c) • I) α := hαf
  have hαb' : HasAngle D ((fun m => t (i + 1 - m)) 1) (U + ((i : ℝ) * c) • I) α := by
    simpa using hPi
  obtain ⟨Wf, hWf⟩ := hS.exists_gamma (t (i + 1))
  obtain ⟨Wb, hWb⟩ := hS.exists_gamma (t i)
  have hWf' : HasAngle D ((fun m => t (i + m)) 1) Wf γ := hWf
  have hWb' : HasAngle D ((fun m => t (i + 1 - m)) 1) Wb γ := by simpa using hWb
  obtain ⟨Ff, hrf⟩ := hS.frame Rf (by omega) hαf' hWf'
  obtain ⟨Fb, hrb⟩ := hS.frame Rb hi1 hαb' hWb'
  set Xi := U + ((i : ℝ) * c) • I
  set Jf := b⁻¹ • (Wf - Xi)
  set Jb := b⁻¹ • (Wb - Xi)
  have hWJf : Wf - Xi = b • Jf := by simp only [Jf]; rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  have hWJb : Wb - Xi = b • Jb := by simp only [Jb]; rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  clear_value Jf Jb
  -- the two `b` edges are on the same side of `S`
  have hside : 0 < cross I Jb * cross I Jf := by
    have hWbT : Wb ∈ D.target.carrier := by
      obtain ⟨l, hl, -⟩ := hWb; rw [← hl]; exact TwoCs.pts_mem_target D.toDissection _ _
    have hn := Ff.north Wb hWbT
    unfold crdJ at hn
    rw [hWJb, cross_smul_right] at hn
    have hb0 : cross I Jb ≠ 0 := by
      have := Fb.hIJ; rw [cross_neg_left, neg_ne_zero] at this; exact this
    have hq : 0 < cross I Jb / cross I Jf := by
      rw [mul_div_assoc] at hn
      refine lt_of_le_of_ne (nonneg_of_mul_nonneg_right (by linarith) hb) ?_
      intro h0; exact hb0 ((div_eq_zero_iff.mp h0.symm).resolve_right Ff.hIJ)
    have : cross I Jb * cross I Jf = cross I Jb / cross I Jf * (cross I Jf * cross I Jf) := by
      field_simp [Ff.hIJ]
    rw [this]; exact mul_pos hq (mul_self_pos.mpr Ff.hIJ)
  obtain ⟨hang, hne⟩ := angle_two_sides Ff.nI Fb.nJ Ff.nJ Ff.aIJ Fb.aIJ hside hα (by linarith)
  have hang' : InnerProductGeometry.angle Jb Jf = α + 2 * β := by rw [hang]; linarith
  -- the rays and the sector
  have hedge : ∀ {t' : Fin N} {W J' : Plane}, HasAngle D t' Xi α → HasAngle D t' W γ →
      W - Xi = b • J' → TileEdge D t' Xi (Xi + b • J') := by
    intro t' W J' hA hG hW
    rw [← hW, add_sub_cancel]
    obtain ⟨l, hl, ha⟩ := hA
    obtain ⟨l', hl', ha'⟩ := hG
    refine ⟨l, l', fun h => ?_, hl, hl'⟩
    rw [h] at ha; rw [ha] at ha'; linarith
  have hbEb := hedge hPi hWb hWJb
  have hbEf := hedge hαf hWf hWJf
  have hu : RayWall D.toDissection Xi Jb := rayWall_of_tileEdge hb hbEb
  have hv : RayWall D.toDissection Xi Jf := rayWall_of_tileEdge hb hbEf
  have hXiT : Xi ∈ D.target.carrier :=
    mem_target_of_range (mem_range_of_tileEdge hbEb).1
  have hIne : I ≠ 0 := fun h => by have := Ff.nI; rw [h, norm_zero] at this; exact zero_ne_one this
  have hn0 : (0 : ℝ) < (n : ℝ) * c := mul_pos (by exact_mod_cast hn) hc
  have hUV : U ≠ U + ((n : ℝ) * c) • I := by
    intro h
    have : ((n : ℝ) * c) • I = 0 := by rw [← add_right_inj U, ← h, add_zero]
    exact smul_ne_zero hn0.ne' hIne this
  have hXiv : Xi ∉ Set.range D.target.pts :=
    not_vertex_of_between Ff (hrun.2.1 (left_mem_segment ℝ _ _))
      (hrun.2.1 (right_mem_segment ℝ _ _)) hUV
      (mem_openSeg_smul hIne (mul_pos (by exact_mod_cast hi1) hc)
        (mul_lt_mul_of_pos_right (by exact_mod_cast hin) hc))
  have hin' := hin_side Ff hXiT crdJ_U hXiv hne
    (by
      have : 0 < cross I Jb / cross I Jf := by
        have := mul_self_pos.mpr Ff.hIJ
        rw [div_pos_iff]
        rcases lt_or_gt_of_ne Ff.hIJ with h | h
        · right; exact ⟨by nlinarith, h⟩
        · left; exact ⟨by nlinarith, h⟩
      exact this.le)
    (by rw [div_self Ff.hIJ]; norm_num)
  obtain ⟨Gu, Gv, -, ⟨lu, hlu, su, hsu, hGu⟩, ⟨lv, hlv, sv, hsv, hGv⟩, hβ', hGuα, hGvα, -, -⟩ :=
    sector_two hS hne hu hv hin' hang'
  have hik : (i : ℤ) < k := lt_trans (by exact_mod_cast hin) hnk
  have hnik : ((n - i : ℕ) : ℤ) < k := lt_of_le_of_lt (by exact_mod_cast Nat.sub_le n i) hnk
  have hJb0 : Jb ≠ 0 := fun h => by have := Fb.nJ; rw [h, norm_zero] at this; exact zero_ne_one this
  have hJf0 : Jf ≠ 0 := fun h => by have := Ff.nJ; rw [h, norm_zero] at this; exact zero_ne_one this
  rcases hβ' with hβu | hβv
  · -- the run `T_i, …, T₁`
    have hGue : TileEdge D Gu Xi (Xi + su • Jb) := by
      rcases hGu with h | h
      · exact ⟨lu, lu + 1, fin3_ne_succ lu, hlu, h⟩
      · exact ⟨lu, lu + 2, by fin_cases lu <;> decide, hlu, h⟩
    have hne' : Gu ≠ t i := by
      intro h; rw [h] at hβu; exact hS.alpha_ne_beta (angle_eq_of_two hPi hβu)
    have hopp := opposite_of_ray hne' hJb0 hsu hb hGue hbEb
    apply rootedblock hS Rb hi1 hik hVb hαb' hWb'
    refine ⟨Gu, Xi + su • Jb, ⟨su / b, div_pos hsu hb, ?_⟩, hGue, ?_, fun y hy z hz => ?_⟩
    · rw [hWJb, smul_smul, div_mul_cancel₀ _ hb.ne']
    · have := hS.beta_edge hβu hGue
      rwa [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Fb.nJ, mul_one,
        Real.norm_of_nonneg hsu.le] at this ⊢
    · rw [hWJb, cross_smul_left, cross_smul_left]
      have := hopp y hy z (by simpa using hz)
      nlinarith [mul_self_nonneg b]
  · -- the run `T_{i+1}, …, T_n`
    have hGve : TileEdge D Gv Xi (Xi + sv • Jf) := by
      rcases hGv with h | h
      · exact ⟨lv, lv + 1, fin3_ne_succ lv, hlv, h⟩
      · exact ⟨lv, lv + 2, by fin_cases lv <;> decide, hlv, h⟩
    have hne' : Gv ≠ t (i + 1) := by
      intro h; rw [h] at hβv; exact hS.alpha_ne_beta (angle_eq_of_two hαf hβv)
    have hopp := opposite_of_ray hne' hJf0 hsv hb hGve hbEf
    apply rootedblock hS Rf (by omega) hnik hVf hαf' hWf'
    refine ⟨Gv, Xi + sv • Jf, ⟨sv / b, div_pos hsv hb, ?_⟩, hGve, ?_, fun y hy z hz => ?_⟩
    · rw [hWJf, smul_smul, div_mul_cancel₀ _ hb.ne']
    · have := hS.beta_edge hβv hGve
      rwa [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Ff.nJ, mul_one,
        Real.norm_of_nonneg hsv.le] at this ⊢
    · rw [hWJf, cross_smul_left, cross_smul_left]
      have := hopp y hy z hz
      nlinarith [mul_self_nonneg b]

end RunSetting

/-- **Lemma `lemma:longrun`.** Let `S = D.target.pts j D.target.pts (j+1)` be a side of `T` such
that whenever a tile `R` has its `α` angle at an end `V` of `S` and its `c` edge on `S`, some other
tile has a vertex at `V` and its `a` or `c` edge on the ray from `V` along the `b` edge of `R`. Then
`S` supports a run of at least `k` consecutive `c` edges. -/
theorem longrun {N : ℕ} {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hS : RunSetting D α β γ a b c m k) {j : Fin 3} (hyp : EndHyp D j α γ a c) :
    ∃ (n : ℕ) (U I : Plane) (t : ℕ → Fin N), k ≤ n ∧ run D j c n U I t := by
  obtain ⟨n, U, I, t, hn, hrun, hV, hU0⟩ := hS.stopped_run j
  refine ⟨n, U, I, t, ?_, hrun⟩
  by_contra hlt
  push Not at hlt
  have hc := hS.c_pos
  -- `T₁`: Case 1 or `β` at `X₀`
  have he1 := hrun.2.2 0 (by omega)
  simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, zero_add, one_mul] at he1
  have hd1 : dist U (U + c • I) = c := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hrun.1, mul_one,
      Real.norm_of_nonneg hc.le]
  rcases (hS.edge_ends he1).2.2 hd1 with ⟨hα0, -⟩ | ⟨-, hα1⟩
  · exact hS.case_start hyp hrun hn hlt hV hU0 hα0
  -- `T_n`: Case 2 or `β` at `X_n`
  by_cases hαn : HasAngle D (t n) (U + ((n : ℝ) * c) • I) α
  · exact hS.case_ends hyp hrun hn hlt hV hU0 hαn
  · exact hS.case_middle hrun hn hlt hV hU0 hα1 hαn

end TriangleTiling.Prime
