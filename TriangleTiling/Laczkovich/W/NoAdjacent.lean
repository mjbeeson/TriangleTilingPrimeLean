/-
Bonfioli's `no_adjacent_pi3` (Laczkovich, DCG 48 (2012), Sect. 8.3) with "no witnessed relation" in
place of `NotComb`: in a regular tiling of a convex polygon by a tile with `γ = π/3`, if no relation
`j c = ℓ a + m b` is witnessed, then no two consecutive corners of the polygon are `π/3`.

`edge_vertex_data_c`, `edge_step_c`, `walk_gamma` and `no_adjacent_pi3` are copied verbatim from
Bonfioli's `Draft/LaczFormalRG6IVcSmall.lean` with the suffix `_W`, `CaseC` replaced by `CaseCW`, and
`ga_edge_of_ray`, `gc_no_boundary` replaced by their `_W` versions (see `W/GammaC.lean`). Nothing else
changes.
-/
import Erdos634.Draft.LaczFormalRG6IVcSmall
import TriangleTiling.Laczkovich.W.GammaC

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]



/-- **The local data at a side vertex, `Γ_c` version.**  `V` in the relative interior of the edge `i` (`γ = π/3`, no edge of `Γ_c` starts at `V` because `V` is a boundary point):
a three-tile fan; either the three types at `V` are distinct, or all three corners at `V` are `γ` (the exceptional vertex `3γ = π`); the first sides on the two inner rays have the
same `c`-status. -/
theorem edge_vertex_data_c_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {V : Plane}
    (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) (hvert : ∃ j k, (D.tile j).pts k = V) :
    ∃ (pT : V2) (F : ExtFan D.toRegionDissection V Unit) (s1 s2 s3 : AtV D.toRegionDissection V),
      Par pT (toV2 (P.e i)) ∧ SideFan3 D.toRegionDissection V pT F.p F.q s1 s2 s3 ∧
      (∃ k, (D.tile s2.1).pts k = V) ∧
      ((∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        idx s1.1 k1 ≠ idx s2.1 k2 ∧ idx s1.1 k1 ≠ idx s3.1 k3 ∧ idx s2.1 k2 ≠ idx s3.1 k3) ∨
       (∀ k3, (D.tile s3.1).pts k3 = V → idx s3.1 k3 = 2)) ∧
      (nsq (F.q s1) = slen D 2 ^ 2 ↔ nsq (F.p s2) = slen D 2 ^ 2) ∧ (nsq (F.q s2) = slen D 2 ^ 2 ↔ nsq (F.p s3) = slen D 2 ^ 2) := by
  classical
  have hG := h.caseG
  have hs0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hbd : V ∉ interior D.region := by
    rw [hreg]; exact not_interior_of_c_zero P (i := i) (by rw [hV]; exact c_on_edge P i t)
  obtain ⟨pT, F, hpd, hpe, hqe, hcr, hcls, hcard⟩ := edge_fan_counts_c D P hreg idx h.hidxA hγ h.hregc i ht0 ht1 hV hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨s1, s2, s3, hF⟩ := unit_fan3 D.toRegionDissection pT F hpT hpe hqe hcard
  refine ⟨pT, F, s1, s2, s3, hpd, hF, ?_⟩
  have hcorner : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := fun x => ExtFan.corner_of_crs F x (hcr x)
  have c1 : 0 < crs pT (F.q s1) := by
    obtain ⟨a, ha, hap⟩ := hF.r1.smul
    have hh := hcr s1
    rw [hap] at hh; unfold crs at hh ⊢; try simp only at hh ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg ha.le (neg_nonneg.mpr hX)]
  have c2 : 0 < crs pT (F.p s2) := ExtFan.crs_pos_of_par hF.r2 c1
  have c3p : 0 < crs pT (F.p s3) := by
    obtain ⟨b, hb, hbq⟩ := hF.r4.symm.smul
    have hh := hcr s3
    rw [hbq] at hh; unfold crs at hh ⊢; try simp only at hh ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg hb.le (neg_nonneg.mpr hX)]
  have c3 : 0 < crs pT (F.q s2) := by
    obtain ⟨c, hc, hcp⟩ := hF.r3.smul
    rw [hcp] at c3p; unfold crs at c3p ⊢; try simp only at c3p ⊢
    by_contra hX; push Not at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have arm_nonneg : ∀ x : AtV D.toRegionDissection V, 0 ≤ crs pT (F.p x) ∧ 0 ≤ crs pT (F.q x) := by
    intro x
    rcases hF.all x with rfl | rfl | rfl
    · refine ⟨(ExtFan.crs_zero_of_par hF.r1 (by unfold crs; ring)).ge, c1.le⟩
    · exact ⟨c2.le, c3.le⟩
    · exact ⟨c3p.le, (ExtFan.crs_zero_of_par hF.r4.symm (by unfold crs; ring)).ge⟩
  have nbray : ∀ ρ : V2, 0 < crs pT ρ → NoBack D.toRegionDissection ρ V := by
    intro ρ hρ
    apply ExtFan.noBack_of_none F
    intro x
    obtain ⟨h1, h2⟩ := arm_nonneg x
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have := ExtFan.crs_neg_of_par h' hρ; linarith
    · have := ExtFan.crs_neg_of_par h' hρ; linarith
  have nb1 := nbray _ c1
  have nb2 := nbray _ c3
  have iff1 : (nsq (F.q s1) = slen D 2 ^ 2 ↔ nsq (F.p s2) = slen D 2 ^ 2) := by
    by_contra hn
    have hx : (nsq (F.q s1) = slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s2) ≠ slen (relabelC D) 0 ^ 2) ∨
        (nsq (F.q s1) ≠ slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s2) = slen (relabelC D) 0 ^ 2) := by rw [hs0]; tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray_W (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc F s1 s2 (hcr s1) (hcr s2) hF.r2 nb1 hx
    exact gc_no_boundary_W D idx h hbd ((gcEdge_iff D V H').mpr hH')
  have iff2 : (nsq (F.q s2) = slen D 2 ^ 2 ↔ nsq (F.p s3) = slen D 2 ^ 2) := by
    by_contra hn
    have hx : (nsq (F.q s2) = slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s3) ≠ slen (relabelC D) 0 ^ 2) ∨
        (nsq (F.q s2) ≠ slen (relabelC D) 0 ^ 2 ∧ nsq (F.p s3) = slen (relabelC D) 0 ^ 2) := by rw [hs0]; tauto
    obtain ⟨H', hH'⟩ := ga_edge_of_ray_W (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc F s2 s3 (hcr s2) (hcr s3) hF.r3 nb2 hx
    exact gc_no_boundary_W D idx h hbd ((gcEdge_iff D V H').mpr hH')
  refine ⟨hcorner s2, ?_, iff1, iff2⟩
  rcases hcls with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · right
    intro k3 hk3
    exact idx_two_of_cnt D idx e0 e1 hk3
  · left
    have hk : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k = V → ∀ l : Fin 3, idx t k = l → cnt D idx V l = 1 := by
      intro t k hk l hl
      have := cnt_one D idx l hk hl
      fin_cases l <;> simp_all
    refine fun k1 k2 k3 hk1 hk2 hk3 => ⟨?_, ?_, ?_⟩
    · intro e
      have := cnt_two D idx (idx s1.1 k1) (fun h' => hF.d12 (Subtype.ext h')) hk1 hk2 rfl e.symm
      have := hk _ _ hk1 _ rfl
      omega
    · intro e
      have := cnt_two D idx (idx s1.1 k1) (fun h' => hF.d13 (Subtype.ext h')) hk1 hk3 rfl e.symm
      have := hk _ _ hk1 _ rfl
      omega
    · intro e
      have := cnt_two D idx (idx s2.1 k2) (fun h' => hF.d23 (Subtype.ext h')) hk2 hk3 rfl e.symm
      have := hk _ _ hk2 _ rfl
      omega

set_option maxHeartbeats 3200000 in
/-- **The `γ` rule along a side** (Laczkovich Lemma 4.4, local content: the case check of Fig. 4, DCG 48 p. 348): two consecutive tiles `j1` (ending at `V`) and `j2` (starting at `V`) of the walk along the edge `i`, `V` in the relative
interior of the edge.  If `j1` has `γ` at its tail then `j2` has `γ` at its tail `V`. -/
theorem edge_step_c_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {V : Plane} (hV : V = (1 - t) • P.v i + t • P.v (i + 1)) {U U'' : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U V) (h2 : TriStep (D.tile j2) (toV2 (P.e i)) V U'')
    (kR fR kL fL : Fin 3) (hR1 : (D.tile j2).pts kR = V) (hR2 : (D.tile j2).pts fR = U'')
    (hL1 : (D.tile j1).pts kL = V) (hL2 : (D.tile j1).pts fL = U) :
    idx j1 fL = 2 → idx j2 kR = 2 := by
  classical
  intro hg
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hvert : ∃ j k, (D.tile j).pts k = V := ⟨j2, kR, hR1⟩
  obtain ⟨pT, F, s1, s2, s3, hpd, hF, hc2, hcls, hno1, hno2⟩ := edge_vertex_data_c_W D P hreg idx h hγ i ht0 ht1 hV hvert
  have hi : V ∈ (D.tile j1).carrier := hL1 ▸ subset_convexHull ℝ _ ⟨kL, rfl⟩
  have hi2 : V ∈ (D.tile j2).carrier := hR1 ▸ subset_convexHull ℝ _ ⟨kR, rfl⟩
  have e1 := fan_start_unique hF hpd h2 hi2
  have e3 := fan_end_unique hF hpd h1 hi
  have hj2 : s1.1 = j2 := by rw [← e1]
  have hj1 : s3.1 = j1 := by rw [← e3]
  have hR2' : Par (toV2 ((D.tile s1.1).pts fR - V)) pT := by
    rw [hj2, hR2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h2
    exact hpar.trans hpd.symm
  have hL2' : Par (toV2 ((D.tile s3.1).pts fL - V)) (-pT.1, -pT.2) := by
    rw [hj1, hL2]
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := h1
    have hneg : toV2 (U - V) = (-(toV2 (V - U)).1, -(toV2 (V - U)).2) := by
      unfold toV2; ext <;> simp
    rw [hneg]
    exact (par_neg hpar).trans (par_neg hpd).symm
  rcases hcls with hnorm | hall
  · have hnorm' : ∀ k1 k2 k3, (D.tile s1.1).pts k1 = V → (D.tile s2.1).pts k2 = V → (D.tile s3.1).pts k3 = V →
        relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s2.1 k2 ∧ relabelCIdx idx s1.1 k1 ≠ relabelCIdx idx s3.1 k3 ∧
        relabelCIdx idx s2.1 k2 ≠ relabelCIdx idx s3.1 k3 := by
      intro k1 k2 k3 a1 a2 a3
      obtain ⟨n1, n2, n3⟩ := hnorm k1 k2 k3 a1 a2 a3
      have inj : ∀ (a b : Fin N) (k k' : Fin 3), relabelCIdx idx a k = relabelCIdx idx b k' → idx a k = idx b k' := by
        intro a b k k' e
        unfold relabelCIdx at e
        rw [relabelIdx_apply, relabelIdx_apply] at e
        exact Equiv.injective _ e
      exact ⟨fun e => n1 (inj _ _ _ _ e), fun e => n2 (inj _ _ _ _ e), fun e => n3 (inj _ _ _ _ e)⟩
    have hs0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
    have := side_step_all (relabelC D) (relabelCIdx idx) hG.hidx V hF hc2 hG.hab hG.hac hnorm' (by rw [hs0]; exact hno1) (by rw [hs0]; exact hno2)
      kR fR kL fL (by rw [hj2]; exact hR1) hR2' (by rw [hj1]; exact hL1) hL2'
    rw [hj2, hj1] at this
    have h3 := this.2.1
    show idx j2 kR = 2
    unfold relabelCIdx at h3
    rw [relabelIdx_apply, relabelIdx_apply] at h3
    exact (swap02_symm_zero_iff _).mp (h3 ((swap02_symm_zero_iff _).mpr hg))
  · exfalso
    have hk := hall kL (by rw [hj1]; exact hL1)
    rw [hj1] at hk
    have hkf : kL = fL := (idx j1).injective (hk.trans hg.symm)
    have hne := hL2'.ne_left
    apply hne
    rw [hj1, ← hkf, hL1]
    unfold toV2; ext <;> simp


set_option maxHeartbeats 3200000 in
/-- **The `γ` rule along the whole edge** (Laczkovich Lemma 4.4 (i), proof, as used in Sect. 8.3, DCG 48 p. 370): `γ` at the tail of the first tile of the walk gives `γ` at the tail of the last tile. -/
theorem walk_gamma_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (i : Fin M) {L : List (Fin N × Plane × Plane)}
    (W : WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L) {e0 el : Fin N × Plane × Plane}
    (hf : L.head? = some e0) (hl : L.getLast? = some el) :
    TyAt D idx e0.1 e0.2.1 2 → TyAt D idx el.1 el.2.1 2 := by
  classical
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  have hL : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hf
    | cons x L0 => simp at hf; exact ⟨L0, by rw [hf]⟩
  obtain ⟨L0, hL0⟩ := hL
  have hel_mem : el ∈ L := List.mem_of_getLast? hl
  intro hR
  refine walk_prop_forward D.toRegionDissection P hreg i (fun e => TyAt D idx e.1 e.2.1 2) ?_ rfl W hU e0 L0 hL0 hR el hel_mem
  intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
  obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
  obtain ⟨kk2, f2, hk2, hf2⟩ := step_idx hS2
  have := edge_step_c_W D P hreg idx h hγ i ht0 ht1 hVt (U := e.2.1) (U'' := e2.2.2) (j1 := e.1) (j2 := e2.1) hS1 (by rw [← hX2]; exact hS2)
    kk2 f2 f1 kk1 (by rw [← hX2, ← hk2]) (by rw [hf2]) hf1 hk1 ((tyAt_iff hk1 2).mp hRe)
  exact (tyAt_iff hk2 2).mpr this

set_option maxHeartbeats 3200000 in
set_option maxHeartbeats 3200000 in
/-- **No two consecutive corners of the polygon equal `π/3`** (Subcase IVc with `N ≤ 4`: a triangle or a trapezoid is impossible).  `γ = π/3`, regular counts, no witnessed
relation `j c = ℓ a + m b` (`CaseCW`).  Proof: the first tile of the walk along the edge has `γ` at its tail (corner `π/3`), so by the `γ` rule (`walk_gamma_W`) the last tile has `γ` at its tail;
it also has `γ` at its head (corner `π/3`): two `γ` corners in one tile. -/
theorem no_adjacent_pi3_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx) (hγ : D.model.angleAt 2 = Real.pi / 3) (k : Fin M)
    (hk1 : P.angle (k + 1) = Real.pi / 3) (hk2 : P.angle (k + 1 + 1) = Real.pi / 3) : False := by
  classical
  have hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum D.model
    linarith
  obtain ⟨L, e0, el, hW, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data D P hreg (k + 1)
  have c1 := corner_pi3_types D P hreg idx h.hidxA hγ hαβ h.hregc k hk1
  have c2 := corner_pi3_types D P hreg idx h.hidxA hγ hαβ h.hregc (k + 1) hk2
  have t0 : TyAt D idx e0.1 e0.2.1 2 := by
    intro kk hkk
    exact c1 e0.1 kk (hkk.trans hs1)
  have t1 : TyAt D idx el.1 el.2.2 2 := by
    intro kk hkk
    exact c2 el.1 kk (hkk.trans hs2)
  have t2 := walk_gamma_W D P hreg idx h hγ (k + 1) hW hh hl t0
  obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := hT1
  have a1 := (tyAt_iff hk 2).mp t2
  have a2 := (tyAt_iff hf 2).mp t1
  exact hfk ((idx el.1).injective (a2.trans a1.symm))


end Erdos634.Draft.LaczFormal.RG
