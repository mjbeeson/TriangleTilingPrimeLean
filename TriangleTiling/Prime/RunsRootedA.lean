/-
`lemma:rootedblock` of Beeson–Roșu, Section 11, first step: "the line `UP`". With
`𝒯(w, w)` occurring and a tile `T₀` west of `UP` with its `a` or `c` edge on the ray `UW`, the
edges on the line `UP` of the tiles west of it, from `U` to `P = x(0, w)`, would be an edge
decomposition of `wb` with an `a` or `c` edge, contrary to `lemma:edgedecompositions` (B). So `P`
lies inside an edge, on the line `UP`, of a tile west of `UP`.
-/
import TriangleTiling.Prime.RunsBlock

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

section RootedA

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

omit hS hF in
theorem lineI_apply (y : Plane) :
    lineF I J 1 0 y = crdI U I J y + lineF I J 1 0 U := by
  rw [lineF_apply U I J y 1 0]; ring

omit hS in
/-- A point of the line through `P` along `J`. -/
theorem eq_add_J {P y : Plane} (h : crdI U I J y = crdI U I J P) :
    y = P + (crdJ U I J y - crdJ U I J P) • J := by
  apply eq_of_crd hF.hIJ
  · rw [crdI_addv, cross_smul_left, Erdos634.Geometry.cross_self, mul_zero, zero_div, add_zero, h]
  · rw [crdJ_addv, cross_smul_right, mul_div_assoc, div_self hF.hIJ]; ring

/-- **`P` lies inside an edge of a tile west of `UP`** (first step of `lemma:rootedblock`). -/
theorem rooted_west {w : ℕ} (hw : 1 ≤ w) (hwk : (w : ℤ) < k) (hT : TOccurs D (lat U I J b c) w w)
    {t₀ : Fin N} (ht₀ : ∀ l, crdI U I J ((D.tile t₀).pts l) ≤ 0) {τ : ℝ} (hτ : 0 < τ)
    (hτac : τ = a ∨ τ = c) (ht₀e : TileEdge D t₀ U (U + τ • J)) :
    ∃ e ∈ D.lineChain (lineF I J 1 0) (lineF I J 1 0 U),
      lat U I J b c 0 w ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  set x := lat U I J b c
  set g := lineF I J 1 0
  set c₀ := g U
  have hg : g ≠ 0 := lineF_ne_zero hF.hIJ (Or.inl one_ne_zero)
  have hgx : ∀ v : ℝ, g (x 0 v) = c₀ := by
    intro v; rw [lineI_apply (U := U), crdI_x hF]; simp only [c₀, zero_mul, zero_add]; rfl
  have hJne : J ≠ 0 := fun h => by have := hF.nJ; rw [h, norm_zero] at this; exact zero_ne_one this
  have hU0 : x 0 0 = U := by simp [x, lat]
  set P := x 0 w
  have hPU : P = U + ((w : ℝ) * b) • J := by simp [P, x, lat]
  have hUP : U ≠ P := by
    intro h; rw [← hU0] at h; have := (x_inj hS hF h).2
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  -- The edge of `T₀` is in the chain.
  obtain ⟨e₀, he₀, hoe₀, hends₀⟩ := edge_of_tileEdge ht₀e
  have hUτ : g (U + τ • J) = c₀ := by
    rw [lineI_apply (U := U), crdI_addv, cross_smul_left, Erdos634.Geometry.cross_self, mul_zero,
      zero_div, add_zero]
    simp only [crdI, c₀, cross, sub_self]; simp; rfl
  have hgU : g U = c₀ := rfl
  have he₀c : (t₀, e₀) ∈ D.lineChain g c₀ := by
    rw [Dissection.mem_lineChain]
    refine ⟨?_, ?_, fun i => ?_⟩
    · rcases hends₀ with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [h1]; exacts [hgU, hUτ]
    · rcases hends₀ with ⟨-, h2⟩ | ⟨-, h2⟩ <;> simp only [h2]; exacts [hUτ, hgU]
    · show g ((D.tile t₀).pts i) ≤ c₀
      rw [lineI_apply (U := U)]; have := ht₀ i; simp only [c₀]; linarith
  -- The `b` edge of `T₁ = Δ_{0,0}` from `U` to `U + bJ`.
  obtain ⟨t1, ht1⟩ := hT.1 0 0 (by omega) (by omega)
  have hUb : x 0 ((0 : ℕ) + 1 : ℝ) = U + b • J := by simp [x, lat]
  have hbN : TileEdge D t1 U (U + b • J) := by
    rw [← hUb, ← hU0]
    exact tileEdge_of_range ht1 (by simp) (by simp) (fun h => by
      have := (x_inj hS hF h).2; simp at this)
  have ht01 : t₀ ≠ t1 := by
    have hv : x ((0 : ℕ) + 1 : ℝ) ((0 : ℕ) : ℝ) ∈ Set.range (D.tile t1).pts := by rw [ht1]; simp
    intro h; rw [← h] at hv
    obtain ⟨l, hl⟩ := hv
    have := ht₀ l
    rw [hl, crdI_x hF] at this
    simp at this; linarith
  -- A point just above `U` is interior.
  set ε := min τ b / 2
  have hε : 0 < ε := by positivity
  have hετ : ε < τ := by have := min_le_left τ b; simp only [ε]; linarith
  have hεb : ε < b := by have := min_le_right τ b; simp only [ε]; linarith
  have hZint : U + ε • J ∈ interior D.target.carrier := by
    obtain ⟨eN, -, hoN, -⟩ := edge_of_tileEdge hbN
    apply interior_of_two_openSegment D.toDissection ht01 (m := e₀) (m' := eN)
    · rw [hoe₀]; exact mem_openSeg_smul hJne hε hετ
    · rw [hoN]; exact mem_openSeg_smul hJne hε hεb
  have hUT : U ∈ D.target.carrier := mem_target_of_range (mem_range_of_tileEdge ht₀e).1
  obtain ⟨tP, htP⟩ := hT.1 0 (w - 1) (by omega) (by omega)
  have hw1 : ((w - 1 : ℕ) : ℝ) + 1 = w := by rw [Nat.cast_sub hw]; ring
  have hPv : P ∈ Set.range (D.tile tP).pts := by
    rw [htP]; right; right; simp only [Set.mem_singleton_iff, P, x]; rw [hw1]; simp
  have hPT : P ∈ D.target.carrier := mem_target_of_range hPv
  have hint : openSegment ℝ U P ⊆ interior D.target.carrier := by
    apply openSegment_subset_interior_of D.target.convex hUT hPT (Z := U + ε • J) _ hZint
    rw [hPU]
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    exact mem_openSeg_smul hJne hε (by nlinarith)
  -- The wall: the `b` edges of `Δ_{0,i}`.
  have hwall : ∀ y ∈ openSegment ℝ U P, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i
    have hy' := openSegment_subset_segment ℝ U P hy
    rw [hPU, show ((w : ℝ) * b) • J = (w : ℝ) • (b • J) by rw [smul_smul]] at hy'
    obtain ⟨q, hq, hyq⟩ := mem_unit_segment (by omega) hy'
    obtain ⟨tq, htq⟩ := hT.1 0 q (by omega) (by omega)
    have e1 : x ((0 : ℕ) : ℝ) (q : ℝ) = U + (q : ℝ) • (b • J) := by
      simp only [x, lat]; rw [smul_smul]; simp
    have e2 : x ((0 : ℕ) : ℝ) ((q : ℝ) + 1) = U + ((q : ℝ) + 1) • (b • J) := by
      simp only [x, lat]; rw [smul_smul]; simp
    have hE : TileEdge D tq (x ((0 : ℕ) : ℝ) (q : ℝ)) (x ((0 : ℕ) : ℝ) ((q : ℝ) + 1)) :=
      tileEdge_of_range htq (by simp) (by simp) (fun h => by
        have := (x_inj hS hF h).2; linarith)
    rw [e1, e2] at hE
    exact not_interior_of_tileEdge hE hyq i
  -- `U` is not inside an edge of the chain.
  have hendP : ∀ e ∈ D.lineChain g c₀,
      U ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he hUe
    obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
    have hA : crdI U I J ((D.tile e.1).pts e.2) = crdI U I J U := by
      have h3 : g ((D.tile e.1).pts e.2) = crdI U I J ((D.tile e.1).pts e.2) + g U :=
        lineI_apply (U := U) _
      have : crdI U I J U = 0 := by simp [crdI, cross]
      rw [this]; linarith
    have hB : crdI U I J ((D.tile e.1).pts (e.2 + 1)) = crdI U I J U := by
      have h3 : g ((D.tile e.1).pts (e.2 + 1)) = crdI U I J ((D.tile e.1).pts (e.2 + 1)) + g U :=
        lineI_apply (U := U) _
      have : crdI U I J U = 0 := by simp [crdI, cross]
      rw [this]; linarith
    obtain ⟨δ, hδ, hext⟩ := seg_ext hJne (tri_pts_succ_ne _ _) (eq_add_J hF hA)
      (eq_add_J hF hB) hUe
    set σ := min δ τ / 2
    have hσ : 0 < σ := by positivity
    have hσδ : σ ≤ δ := by have := min_le_left δ τ; simp only [σ]; linarith
    have hστ : σ ≤ τ := by have := min_le_right δ τ; simp only [σ]; linarith
    have heq : e = (t₀, e₀) := by
      refine lineChain_eq_of_two D.toDissection hg he he₀c (y := U) (z := U + σ • J) ?_ ⟨?_, ?_⟩
        ⟨?_, ?_⟩
      · intro h; have : σ • J = 0 := by rw [← add_right_inj U, ← h, add_zero]
        exact (smul_ne_zero hσ.ne' hJne) this
      · exact openSegment_subset_segment ℝ _ _ hUe
      · rw [he₀]; exact left_mem_segment ℝ _ _
      · exact hext σ hσ.le hσδ
      · rw [he₀]; exact mem_seg_smul hτ hσ.le hστ
    rw [heq] at hUe
    simp only at hUe
    rw [hoe₀] at hUe
    have h := left_mem_openSegment_iff.mp hUe
    have : τ • J = 0 := by rw [← add_right_inj U, ← h, add_zero]
    exact (smul_ne_zero hτ.ne' hJne) this
  -- Otherwise the chain sum is an edge decomposition of `wb` with an `a` or `c` edge.
  by_contra hno
  push Not at hno
  have hsum := TwoCs.chain_sum D.toDissection hg hUP hgU (hgx _) hendP hno hint hwall
  set S := (D.lineChain g c₀).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U P)
  have he₀S : (t₀, e₀) ∈ S := by
    refine Finset.mem_filter.mpr ⟨he₀c, ?_⟩
    rcases TwoCs.chain_dich D.toDissection hg hUP hgU (hgx _) hendP hno he₀c with h | h
    · exact h
    · exfalso
      have hm : (1 : ℝ) ≤ w := by exact_mod_cast hw
      have h1 : U ∈ (D.tile t₀).edge e₀ ∩ segment ℝ U P :=
        ⟨by rw [he₀]; exact left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
      have h2 : U + ε • J ∈ (D.tile t₀).edge e₀ ∩ segment ℝ U P :=
        ⟨by rw [he₀]; exact mem_seg_smul hτ hε.le hετ.le,
          by rw [hPU]; exact mem_seg_smul (by positivity) hε.le (by nlinarith)⟩
      have := h h1 h2
      have : ε • J = 0 := by rw [← add_right_inj U, ← this, add_zero]
      exact (smul_ne_zero hε.ne' hJne) this
  have hlen : ∀ e ∈ S, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c :=
    fun e _ => hS.edge_len e.1 e.2
  have hdUP : dist U P = (w : ℝ) * b := by
    rw [hPU, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ, mul_one,
      Real.norm_of_nonneg (by positivity)]
  rw [hdUP] at hsum
  have := hS.wallB hlen hw hwk hsum (t₀, e₀) he₀S
  have hlen₀ : dist ((D.tile t₀).pts e₀) ((D.tile t₀).pts (e₀ + 1)) = τ := by
    rcases hends₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ, mul_one,
        Real.norm_of_nonneg hτ.le]
    · rw [h1, h2, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ, mul_one,
        Real.norm_of_nonneg hτ.le]
  simp only [hlen₀] at this
  rcases hτac with h | h
  · exact this.1 h
  · exact this.2 h

end RootedA

end TriangleTiling.Prime
