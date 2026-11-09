/-
The trapezoid lemma (`lemma:block`) of Beeson–Roșu, Section 11, first step: "`R` is not a vertex
of a tile north of `ℓ_r`". With `𝒯(s, r)` occurring and a tile north of `ℓ_r` with its `b` edge on
`ℓ_r` running east from `x(i₀, r)`, the edges on `ℓ_r` of the tiles north of `ℓ_r`, between
`x(i₀, r)` and `R = x(s - r, r)`, would be an edge decomposition of `(s - r - i₀)c` with a `b` edge,
contrary to `lemma:edgedecompositions` (C). So `R` lies inside an edge, on `ℓ_r`, of a tile north
of `ℓ_r`.
-/
import TriangleTiling.Prime.RunsSeg

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

theorem cast_sub_one {s r : ℕ} (h : r ≤ s) : ((s - r : ℕ) : ℝ) = s - r := by
  rw [Nat.cast_sub h]

section BlockA

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

omit hS hF in
/-- The functional of the lines parallel to `I`: `g y = -crdJ y + const`. -/
theorem lineJ_apply (y : Plane) :
    lineF I J 0 (-1) y = -crdJ U I J y + lineF I J 0 (-1) U := by
  rw [lineF_apply U I J y 0 (-1)]; ring

omit hF in
/-- Points of the lattice line `ℓ_v` near a lattice point, as lattice points. -/
theorem lat_add_smul_I (u v s : ℝ) :
    lat U I J b c u v + s • I = lat U I J b c (u + s / c) v := by
  rw [← lat_add_I]; congr 2; field_simp [hS.c_pos.ne']

omit hS hF in
theorem crdI_addv (y w : Plane) : crdI U I J (y + w) = crdI U I J y + cross w J / cross I J := by
  unfold crdI; rw [show y + w - U = (y - U) + w by abel, cross_add_left', add_div]

omit hS hF in
theorem crdJ_addv (y w : Plane) : crdJ U I J (y + w) = crdJ U I J y + cross I w / cross I J := by
  unfold crdJ; rw [show y + w - U = (y - U) + w by abel, cross_add_right, add_div]

omit hS in
/-- A point of the line through `P` along `I`. -/
theorem eq_add_I {P y : Plane} (h : crdJ U I J y = crdJ U I J P) :
    y = P + (crdI U I J y - crdI U I J P) • I := by
  apply eq_of_crd hF.hIJ
  · rw [crdI_addv, cross_smul_left, mul_div_assoc, div_self hF.hIJ]; ring
  · rw [crdJ_addv, cross_smul_right, cross_self, mul_zero, zero_div, add_zero, h]

/-- **`R` lies inside an edge of a tile north of `ℓ_r`** (first step of `lemma:block`). -/
theorem block_north {r s i₀ : ℕ} (hr : 1 ≤ r) (hrs : r < s) (hsk : (s : ℤ) < k)
    (hT : TOccurs D (lat U I J b c) s r) (hi₀ : i₀ + r < s) {G₀ : Fin N}
    (hG₀ : ∀ l, (r : ℝ) * b ≤ crdJ U I J ((D.tile G₀).pts l))
    (hG₀e : TileEdge D G₀ (lat U I J b c i₀ r) (lat U I J b c i₀ r + b • I)) :
    ∃ e ∈ D.lineChain (lineF I J 0 (-1)) (-((r : ℝ) * b) + lineF I J 0 (-1) U),
      lat U I J b c ((s : ℝ) - r) r ∈
        openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
  classical
  have hb := hS.b_pos; have hc := hS.c_pos
  set x := lat U I J b c
  set g := lineF I J 0 (-1)
  set c₀ := -((r : ℝ) * b) + g U
  have hg : g ≠ 0 := lineF_ne_zero hF.hIJ (Or.inr (by norm_num))
  have hgx : ∀ u : ℝ, g (x u r) = c₀ := by
    intro u; rw [lineJ_apply, crdJ_x hF]
  set P := x i₀ r
  set R := x ((s : ℝ) - r) r
  have hIne : I ≠ 0 := fun h => by have := hF.nI; rw [h, norm_zero] at this; exact zero_ne_one this
  -- `R = P + (s - r - i₀) c I`
  set n' : ℕ := s - r - i₀
  have hn' : (n' : ℝ) = s - r - i₀ := by
    simp only [n']; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hn'1 : 1 ≤ n' := by omega
  have hn'k : (n' : ℤ) < k := by
    have : n' ≤ s := by omega
    calc (n' : ℤ) ≤ s := by exact_mod_cast this
      _ < k := hsk
  have hRP : R = P + ((n' : ℝ) * c) • I := by
    simp only [R, P, x]; rw [lat_add_I]; congr 1; rw [hn']; ring
  have hPR : P ≠ R := by
    intro h
    have := (x_inj hS hF h).1
    have : (n' : ℝ) = 0 := by rw [hn']; linarith
    have : (1 : ℝ) ≤ n' := by exact_mod_cast hn'1
    linarith
  -- The `b` edge of `G₀` is in the chain.
  obtain ⟨e₀, he₀, hoe₀, hends₀⟩ := edge_of_tileEdge hG₀e
  have hPb : g (P + b • I) = c₀ := by
    rw [lat_add_smul_I hS]; exact hgx _
  have he₀c : (G₀, e₀) ∈ D.lineChain g c₀ := by
    rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hends₀ with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [h1]; exacts [hgx _, hPb]
    · rcases hends₀ with ⟨-, h2⟩ | ⟨-, h2⟩ <;> simp only [h2]; exacts [hPb, hgx _]
    · show g ((D.tile G₀).pts i) ≤ c₀
      rw [lineJ_apply]; have := hG₀ i; simp only [c₀]; linarith
  -- The `c` edge of `∇_{i₀, r-1}` from `P` to `P + cI`.
  have hT2 := hT.2 i₀ (r - 1) (by omega) (by omega)
  obtain ⟨tN, htN⟩ := hT2
  have hr1 : ((r - 1 : ℕ) : ℝ) + 1 = r := by rw [Nat.cast_sub hr]; ring
  rw [hr1] at htN
  have hPc : x ((i₀ : ℝ) + 1) r = P + c • I := by
    simp only [P, x]; rw [← lat_add_I]; simp
  have hcN : TileEdge D tN P (P + c • I) := by
    rw [← hPc]
    exact tileEdge_of_range htN (by simp [P]) (by simp) (fun h => by
      have := (x_inj hS hF h).1; linarith)
  -- `G₀` and `∇_{i₀, r-1}` are different tiles.
  have hGN : G₀ ≠ tN := by
    have hv : x ((i₀ : ℝ) + 1) ((r - 1 : ℕ) : ℝ) ∈ Set.range (D.tile tN).pts := by rw [htN]; simp
    intro h; rw [← h] at hv
    obtain ⟨l, hl⟩ := hv
    have := hG₀ l
    rw [hl, crdJ_x hF, Nat.cast_sub hr] at this
    simp at this; linarith
  -- A point just east of `P` is interior.
  set ε := min b c / 2
  have hε : 0 < ε := by positivity
  have hεb : ε < b := by have := min_le_left b c; simp only [ε]; linarith
  have hεc : ε < c := by have := min_le_right b c; simp only [ε]; linarith
  have hZint : P + ε • I ∈ interior D.target.carrier := by
    obtain ⟨eN, -, hoN, -⟩ := edge_of_tileEdge hcN
    apply interior_of_two_openSegment D.toDissection hGN (m := e₀) (m' := eN)
    · rw [hoe₀]; exact mem_openSeg_smul hIne hε hεb
    · rw [hoN]; exact mem_openSeg_smul hIne hε hεc
  have hPT : P ∈ D.target.carrier := mem_target_of_range (mem_range_of_tileEdge hG₀e).1
  have hRT : R ∈ D.target.carrier := by
    have hT2' := hT.2 (s - r - 1) (r - 1) (by omega) (by omega)
    obtain ⟨tR, htR⟩ := hT2'
    apply mem_target_of_range (t := tR)
    rw [htR]
    have : x (((s - r - 1 : ℕ) : ℝ) + 1) (((r - 1 : ℕ) : ℝ) + 1) = R := by
      simp only [R, x]; rw [hr1, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; congr 1; ring
    rw [this]; simp
  have hint : openSegment ℝ P R ⊆ interior D.target.carrier := by
    apply openSegment_subset_interior_of D.target.convex hPT hRT (Z := P + ε • I) _ hZint
    rw [hRP]
    have : (1 : ℝ) ≤ n' := by exact_mod_cast hn'1
    exact mem_openSeg_smul hIne hε (by nlinarith)
  -- The wall: the `c` edges of `∇_{i, r-1}`.
  have hwall : ∀ y ∈ openSegment ℝ P R, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i
    have hy' := openSegment_subset_segment ℝ P R hy
    rw [hRP, show ((n' : ℝ) * c) • I = (n' : ℝ) • (c • I) by rw [smul_smul]] at hy'
    obtain ⟨q, hq, hyq⟩ := mem_unit_segment (by omega) hy'
    obtain ⟨tq, htq⟩ := hT.2 (i₀ + q) (r - 1) (by omega) (by omega)
    rw [hr1] at htq
    have e1 : x (((i₀ + q : ℕ) : ℝ)) r = P + (q : ℝ) • (c • I) := by
      simp only [P, x]; rw [smul_smul, lat_add_I]; push_cast; ring_nf
    have e2 : x (((i₀ + q : ℕ) : ℝ) + 1) r = P + ((q : ℝ) + 1) • (c • I) := by
      simp only [P, x]; rw [smul_smul, lat_add_I]; push_cast; ring_nf
    have hE : TileEdge D tq (x ((i₀ + q : ℕ) : ℝ) r) (x (((i₀ + q : ℕ) : ℝ) + 1) r) :=
      tileEdge_of_range htq (by simp) (by simp) (fun h => by
        have := (x_inj hS hF h).1; linarith)
    rw [e1, e2] at hE
    exact not_interior_of_tileEdge hE hyq i
  -- `P` is not inside an edge of the chain.
  have hendP : ∀ e ∈ D.lineChain g c₀,
      P ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he hPe
    obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
    have hA : crdJ U I J ((D.tile e.1).pts e.2) = crdJ U I J P := by
      have h3 : g ((D.tile e.1).pts e.2) = -crdJ U I J ((D.tile e.1).pts e.2) + g U :=
        lineJ_apply (U := U) _
      have h4 : g P = -crdJ U I J P + g U := lineJ_apply (U := U) _
      have h5 : g P = c₀ := hgx _
      linarith
    have hB : crdJ U I J ((D.tile e.1).pts (e.2 + 1)) = crdJ U I J P := by
      have h3 : g ((D.tile e.1).pts (e.2 + 1)) = -crdJ U I J ((D.tile e.1).pts (e.2 + 1)) + g U :=
        lineJ_apply (U := U) _
      have h4 : g P = -crdJ U I J P + g U := lineJ_apply (U := U) _
      have h5 : g P = c₀ := hgx _
      linarith
    obtain ⟨δ, hδ, hext⟩ := seg_ext hIne (tri_pts_succ_ne _ _) (eq_add_I hF hA)
      (eq_add_I hF hB) hPe
    set σ := min δ b / 2
    have hσ : 0 < σ := by positivity
    have hσδ : σ ≤ δ := by have := min_le_left δ b; simp only [σ]; linarith
    have hσb : σ ≤ b := by have := min_le_right δ b; simp only [σ]; linarith
    have heq : e = (G₀, e₀) := by
      refine lineChain_eq_of_two D.toDissection hg he he₀c (y := P) (z := P + σ • I) ?_ ⟨?_, ?_⟩
        ⟨?_, ?_⟩
      · intro h; have : σ • I = 0 := by rw [← add_right_inj P, ← h, add_zero]
        exact (smul_ne_zero hσ.ne' hIne) this
      · exact openSegment_subset_segment ℝ _ _ hPe
      · rw [he₀]; exact left_mem_segment ℝ _ _
      · exact hext σ hσ.le hσδ
      · rw [he₀]; exact mem_seg_smul hb hσ.le hσb
    rw [heq] at hPe
    simp only at hPe
    rw [hoe₀] at hPe
    have h := left_mem_openSegment_iff.mp hPe
    have : b • I = 0 := by rw [← add_right_inj P, ← h, add_zero]
    exact (smul_ne_zero hb.ne' hIne) this
  -- Otherwise the chain sum is an edge decomposition of `n' c` with a `b` edge.
  by_contra hno
  push Not at hno
  have hsum := TwoCs.chain_sum D.toDissection hg hPR (hgx _) (hgx _) hendP hno hint hwall
  set S := (D.lineChain g c₀).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P R)
  have he₀S : (G₀, e₀) ∈ S := by
    refine Finset.mem_filter.mpr ⟨he₀c, ?_⟩
    rcases TwoCs.chain_dich D.toDissection hg hPR (hgx _) (hgx _) hendP hno he₀c with h | h
    · exact h
    · exfalso
      have hm : (1 : ℝ) ≤ n' := by exact_mod_cast hn'1
      have h1 : P ∈ (D.tile G₀).edge e₀ ∩ segment ℝ P R :=
        ⟨by rw [he₀]; exact left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
      have h2 : P + ε • I ∈ (D.tile G₀).edge e₀ ∩ segment ℝ P R :=
        ⟨by rw [he₀]; exact mem_seg_smul hb hε.le hεb.le,
          by rw [hRP]; exact mem_seg_smul (by positivity) hε.le (by nlinarith)⟩
      have := h h1 h2
      have : ε • I = 0 := by rw [← add_right_inj P, ← this, add_zero]
      exact (smul_ne_zero hε.ne' hIne) this
  have hlen : ∀ e ∈ S, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c :=
    fun e _ => hS.edge_len e.1 e.2
  have hdPR : dist P R = (n' : ℝ) * c := by
    rw [hRP, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nI, mul_one,
      Real.norm_of_nonneg (by positivity)]
  rw [hdPR] at hsum
  have := hS.wallC hlen hn'1 hn'k hsum (G₀, e₀) he₀S
  apply this
  simp only
  rcases hends₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nI, mul_one,
      Real.norm_of_nonneg hb.le]
  · rw [h1, h2, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nI, mul_one,
      Real.norm_of_nonneg hb.le]

end BlockA

end TriangleTiling.Prime
