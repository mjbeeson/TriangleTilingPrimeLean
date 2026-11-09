/-
The trapezoid lemma (`lemma:block`), second step: the segment `σ = q₀R`, `q_j = x(s - j, j)`.
`R` is interior; no tile edge on the line of `σ` runs past `R` (it would lie inside a tile north of
`ℓ_r`) or past `q₀` (it would leave `T`); so the edges of the tiles east of `σ` partition `σ`, and by
`lemma:edgedecompositions` (A) they are `r` edges of length `a`, with endpoints exactly
`q₀, …, q_r`.
-/
import TriangleTiling.Prime.RunsBlockA

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

theorem fin3_ne_succ (m : Fin 3) : m ≠ m + 1 := by fin_cases m <;> decide

section BlockB

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

omit hS hF in
/-- The functional of the lines parallel to `σ`: `g y = -(b crdI y + c crdJ y) + const`. -/
theorem lineS_apply (y : Plane) :
    lineF I J (-b) (-c) y = -(b * crdI U I J y + c * crdJ U I J y) + lineF I J (-b) (-c) U := by
  rw [lineF_apply U I J y (-b) (-c)]; ring

omit hS in
theorem crd_addv_comb (y : Plane) (p q : ℝ) :
    crdI U I J (y + (p • I + q • J)) = crdI U I J y + p ∧
      crdJ U I J (y + (p • I + q • J)) = crdJ U I J y + q := by
  rw [crdI_addv, crdJ_addv]
  have hIJ := hF.hIJ
  constructor
  · rw [cross_add_left', cross_smul_left, cross_smul_left, Erdos634.Geometry.cross_self]
    field_simp; ring
  · rw [cross_add_right, cross_smul_right, cross_smul_right, Erdos634.Geometry.cross_self]
    field_simp; ring

omit hS hF in
/-- The direction of `σ`, upward: `w = bJ - cI`. -/
theorem lat_add_w (u v t : ℝ) :
    lat U I J b c u v + t • (b • J - c • I) = lat U I J b c (u - t) (v + t) := by
  simp only [lat, smul_sub, smul_smul]; module

/-- A tile with `R` inside an edge on `ℓ_r` has a vertex west of `σ`. -/
theorem north_west {r s : ℕ} {N₀ : Fin N} {e₁ : Fin 3}
    (hN₀1 : crdJ U I J ((D.tile N₀).pts e₁) = r * b)
    (hN₀2 : crdJ U I J ((D.tile N₀).pts (e₁ + 1)) = r * b)
    (hRN : lat U I J b c ((s : ℝ) - r) r ∈
      openSegment ℝ ((D.tile N₀).pts e₁) ((D.tile N₀).pts (e₁ + 1))) :
    ∃ l, b * crdI U I J ((D.tile N₀).pts l) + c * crdJ U I J ((D.tile N₀).pts l) <
      (b * c) * s := by
  have hb := hS.b_pos
  rw [openSegment_eq_image_lineMap] at hRN
  obtain ⟨θ, ⟨h0, h1⟩, hθ⟩ := hRN
  have hcI := crdI_affine (U := U) (I := I) (J := J) ((D.tile N₀).pts e₁)
    ((D.tile N₀).pts (e₁ + 1)) θ
  rw [hθ, crdI_x hF] at hcI
  have hne : crdI U I J ((D.tile N₀).pts e₁) ≠ crdI U I J ((D.tile N₀).pts (e₁ + 1)) := by
    intro h; exact tri_pts_succ_ne _ _ (eq_of_crd hF.hIJ h (hN₀1.trans hN₀2.symm))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨e₁, ?_⟩; rw [hN₀1]
    have : crdI U I J ((D.tile N₀).pts e₁) < ((s : ℝ) - r) * c := by
      nlinarith [mul_pos h0 (sub_pos.mpr hlt)]
    nlinarith [mul_lt_mul_of_pos_left this hb]
  · refine ⟨e₁ + 1, ?_⟩; rw [hN₀2]
    have : crdI U I J ((D.tile N₀).pts (e₁ + 1)) < ((s : ℝ) - r) * c := by
      nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr hlt)]
    nlinarith [mul_lt_mul_of_pos_left this hb]

/-- `∇_{s-r-1, r-1}` has its `α` angle at `R`. -/
theorem nabla_at_R {r s : ℕ} (hr : 1 ≤ r) (hrs : r < s) (hT : TOccurs D (lat U I J b c) s r) :
    ∃ tR, HasAngle D tR (lat U I J b c ((s : ℝ) - r) r) α := by
  obtain ⟨tR, htR⟩ := hT.2 (s - r - 1) (r - 1) (by omega) (by omega)
  obtain ⟨-, -, hRα⟩ := nabla_angles hS hF htR
  have hx : lat U I J b c (((s - r - 1 : ℕ) : ℝ) + 1) (((r - 1 : ℕ) : ℝ) + 1) =
      lat U I J b c ((s : ℝ) - r) r := by
    rw [Nat.cast_sub hr, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; congr 1 <;> ring
  exact ⟨tR, hx ▸ hRα⟩

set_option maxHeartbeats 1600000 in
/-- **The chain on `σ`** (second step of `lemma:block`). -/
theorem block_east {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hsk : (s : ℤ) < k)
    (hT : TOccurs D (lat U I J b c) s r) {N₀ : Fin N} {e₁ : Fin 3}
    (hNw : ∃ l, b * crdI U I J ((D.tile N₀).pts l) + c * crdJ U I J ((D.tile N₀).pts l) <
        (b * c) * s)
    (hRN : lat U I J b c ((s : ℝ) - r) r ∈
      openSegment ℝ ((D.tile N₀).pts e₁) ((D.tile N₀).pts (e₁ + 1)))
    {tR : Fin N} {θ : ℝ} (hRθ : HasAngle D tR (lat U I J b c ((s : ℝ) - r) r) θ) (hθ0 : 0 < θ)
    (hθπ : θ < π) :
    lat U I J b c ((s : ℝ) - r) r ∈ interior D.target.carrier ∧
    (∀ i < r, ∃ E : Fin N,
      (∀ l, (b * c) * s ≤ b * crdI U I J ((D.tile E).pts l) + c * crdJ U I J ((D.tile E).pts l)) ∧
      TileEdge D E (lat U I J b c ((s : ℝ) - i) i) (lat U I J b c ((s : ℝ) - i - 1) (i + 1))) ∧
    (∀ (E : Fin N) (τ : ℝ), 0 < τ →
      (∀ l, (b * c) * s ≤ b * crdI U I J ((D.tile E).pts l) + c * crdJ U I J ((D.tile E).pts l)) →
      TileEdge D E (lat U I J b c s 0) (lat U I J b c s 0 + τ • (b • J - c • I)) → τ * a = a) := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  set x := lat U I J b c
  set w := b • J - c • I
  have hw0 : w ≠ 0 := by
    intro h
    have : crdJ U I J (U + w) = crdJ U I J U := by rw [h, add_zero]
    have e := (crd_addv_comb hF U (-c) b).2
    rw [show (-c) • I + b • J = w by simp only [w, neg_smul]; abel] at e
    rw [e, crdJ_U] at this; linarith
  have hnw : ‖w‖ = a := by
    have : w = -(c • I - b • J) := by simp only [w]; abel
    rw [this, norm_neg, hF.nw]
  set q₀ := x s 0
  set R := x ((s : ℝ) - r) r
  have hRq : R = q₀ + (r : ℝ) • w := by simp only [R, q₀, x, w]; rw [lat_add_w]; congr 1 <;> ring
  set g := lineF I J (-b) (-c)
  set c₀ := -(b * c * s) + g U
  have hg : g ≠ 0 := lineF_ne_zero hF.hIJ (Or.inl (by linarith))
  have hgx : ∀ u v : ℝ, u + v = s → g (x u v) = c₀ := by
    intro u v huv
    rw [lineS_apply, crdI_x hF, crdJ_x hF]; simp only [c₀]
    have : u = s - v := by linarith
    rw [this]; ring
  have hgE : ∀ y, g y ≤ c₀ ↔ (b * c) * s ≤ b * crdI U I J y + c * crdJ U I J y := by
    intro y; rw [lineS_apply]; simp only [c₀]; constructor <;> intro h <;> linarith
  -- `R` is interior: a vertex of `tR` inside an edge of `N₀`.
  obtain ⟨lR, hlR, -⟩ := id hRθ
  have hRint : R ∈ interior D.target.carrier :=
    interior_of_vertex_openSegment D.toDissection hlR hRN
  -- `q₀` is in `T`.
  obtain ⟨tq, htq⟩ := hT.1 (s - 1) 0 (by omega) (by omega)
  have hs1 : ((s - 1 : ℕ) : ℝ) + 1 = s := by rw [Nat.cast_sub (by omega)]; ring
  rw [hs1] at htq
  have hq₀T : q₀ ∈ D.target.carrier := by
    apply mem_target_of_range (t := tq); rw [htq]; simp [q₀]
  have hint : openSegment ℝ q₀ R ⊆ interior D.target.carrier := by
    rw [openSegment_symm]
    exact D.target.convex.openSegment_interior_closure_subset_interior hRint (subset_closure hq₀T)
  -- The wall: the `a` edges of `Δ_{s-1-i, i}`.
  have hwall : ∀ y ∈ openSegment ℝ q₀ R, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy i
    have hy' := openSegment_subset_segment ℝ q₀ R hy
    rw [hRq] at hy'
    obtain ⟨p, hp, hyp⟩ := mem_unit_segment (by omega) hy'
    obtain ⟨tp, htp⟩ := hT.1 (s - 1 - p) p (by omega) (by omega)
    have e1 : x (((s - 1 - p : ℕ) : ℝ) + 1) p = q₀ + (p : ℝ) • w := by
      simp only [q₀, x, w]; rw [lat_add_w, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      congr 1 <;> ring
    have e2 : x ((s - 1 - p : ℕ) : ℝ) ((p : ℝ) + 1) = q₀ + ((p : ℝ) + 1) • w := by
      simp only [q₀, x, w]; rw [lat_add_w, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      congr 1 <;> ring
    have hE : TileEdge D tp (x (((s - 1 - p : ℕ) : ℝ) + 1) p) (x ((s - 1 - p : ℕ) : ℝ) ((p : ℝ) + 1)) :=
      tileEdge_of_range htp (by simp) (by simp) (fun h => by
        have := (x_inj hS hF h).1; linarith)
    rw [e1, e2] at hE
    exact not_interior_of_tileEdge hE hyp i
  -- `q₀` is not inside a chain edge: it would leave `T`.
  have hendP : ∀ e ∈ D.lineChain g c₀,
      q₀ ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he hq
    obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
    set A := (D.tile e.1).pts e.2
    set B := (D.tile e.1).pts (e.2 + 1)
    have hAT := hF.north A (TwoCs.pts_mem_target D.toDissection _ _)
    have hBT := hF.north B (TwoCs.pts_mem_target D.toDissection _ _)
    rw [openSegment_eq_image_lineMap] at hq
    obtain ⟨θ, ⟨h0, h1'⟩, hθ⟩ := hq
    have hc0 : crdJ U I J q₀ = 0 := by simp only [q₀]; rw [crdJ_x hF]; ring
    have hcq := crdJ_affine (U := U) (I := I) (J := J) A B θ
    rw [hθ, hc0] at hcq
    have hA0 : crdJ U I J A = 0 := by
      nlinarith [mul_nonneg (sub_pos.mpr h1').le hAT, mul_nonneg h0.le hBT]
    have hB0 : crdJ U I J B = 0 := by
      nlinarith [mul_nonneg (sub_pos.mpr h1').le hAT, mul_nonneg h0.le hBT]
    have hgA : g A = g q₀ := by rw [h1, hgx s 0 (by ring)]
    have hgB : g B = g q₀ := by rw [h2, hgx s 0 (by ring)]
    rw [lineS_apply (U := U), lineS_apply (U := U) (y := q₀), hA0, hc0] at hgA
    rw [lineS_apply (U := U), lineS_apply (U := U) (y := q₀), hB0, hc0] at hgB
    have hAq : A = q₀ := eq_of_crd hF.hIJ (by
      have := mul_left_cancel₀ hb.ne' (show b * crdI U I J A = b * crdI U I J q₀ by linarith)
      exact this) (by rw [hA0, hc0])
    have hBq : B = q₀ := eq_of_crd hF.hIJ (by
      have := mul_left_cancel₀ hb.ne' (show b * crdI U I J B = b * crdI U I J q₀ by linarith)
      exact this) (by rw [hB0, hc0])
    exact tri_pts_succ_ne _ _ (hAq.trans hBq.symm)
  -- `R` is not inside a chain edge: with `N₀` and `∇` the angles at `R` would exceed `2π`.
  have hendR : ∀ e ∈ D.lineChain g c₀,
      R ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he hRe
    obtain ⟨-, -, h3⟩ := Dissection.mem_lineChain.mp he
    obtain ⟨l, hl⟩ := hNw
    have hEN : e.1 ≠ N₀ := by
      intro h
      have := (hgE _).mp (h3 l)
      rw [h] at this; linarith
    have hπ := Real.pi_pos
    have hα := hS.angles_pos.1
    have hαπ : α < π := by have := hS.angles_pos; linarith
    have hla1 := Tri.localAngle_openSegment (D.tile N₀) e₁ hRN
    have hla2 := Tri.localAngle_openSegment (D.tile e.1) e.2 hRe
    have hla3 := localAngle_of_hasAngle hRθ
    have h13 : N₀ ≠ tR := tile_ne_of_angle (by rw [hla1, hla3]; exact hθπ.ne')
    have h23 : e.1 ≠ tR := tile_ne_of_angle (by rw [hla2, hla3]; exact hθπ.ne')
    have := sum3_le D hEN.symm h13 h23 R
    have := target_le_two_pi D R
    linarith
  -- The chain sum: `r` edges of length `a`.
  have hsum := TwoCs.chain_sum D.toDissection hg
    (show q₀ ≠ R from fun h => by
      have := (x_inj hS hF h).2; have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith)
    (hgx s 0 (by ring)) (hgx _ _ (by ring)) hendP hendR hint hwall
  set S := (D.lineChain g c₀).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ q₀ R)
  have hdqR : dist q₀ R = (r : ℝ) * a := by
    rw [hRq, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hnw,
      Real.norm_of_nonneg (by positivity)]
  rw [hdqR] at hsum
  have hlen : ∀ e ∈ S, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = a ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = b ∨
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = c :=
    fun e _ => hS.edge_len e.1 e.2
  have hrk : (r : ℤ) < k := lt_of_le_of_lt (by exact_mod_cast hrs) hsk
  obtain ⟨hallA, -⟩ := hS.wallA hlen hr hrk hsum
  refine ⟨hRint, ?_, ?_⟩
  · -- The uniform chain.
    have hcov := TwoCs.chain_cover D.toDissection hg
      (show q₀ ≠ R from fun h => by
        have := (x_inj hS hF h).2; have : (1 : ℝ) ≤ r := by exact_mod_cast hr
        linarith)
      (hgx s 0 (by ring)) (hgx _ _ (by ring)) hendP hendR hint hwall
    have hq₀R : q₀ ≠ R := fun h => by
      have := (x_inj hS hF h).2; have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    have hunif := segment_chain_uniform q₀ R hq₀R S (fun e => (D.tile e.1).pts e.2)
      (fun e => (D.tile e.1).pts (e.2 + 1)) (fun e _ => tri_pts_succ_ne _ _) hcov
      (fun e he e' he' hne => TwoCs.chain_disj D.toDissection hg (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp he').1 hne) (n := r) (by omega)
      (fun e he => by rw [hallA e he, hdqR]; ring)
    intro i hi
    obtain ⟨e, he, hends⟩ := hunif i hi
    have hp1 : AffineMap.lineMap q₀ R ((i : ℝ) / r) = x ((s : ℝ) - i) i := by
      rw [AffineMap.lineMap_apply_module', hRq, add_sub_cancel_left, smul_smul,
        div_mul_cancel₀ _ (by positivity : (r : ℝ) ≠ 0), add_comm]
      simp only [q₀, x, w]; rw [lat_add_w]; congr 1 <;> ring
    have hp2 : AffineMap.lineMap q₀ R (((i : ℝ) + 1) / r) = x ((s : ℝ) - i - 1) (i + 1) := by
      rw [AffineMap.lineMap_apply_module', hRq, add_sub_cancel_left, smul_smul,
        div_mul_cancel₀ _ (by positivity : (r : ℝ) ≠ 0), add_comm]
      simp only [q₀, x, w]; rw [lat_add_w]; congr 1 <;> ring
    rw [hp1, hp2] at hends
    obtain ⟨-, -, h3⟩ := Dissection.mem_lineChain.mp (Finset.mem_filter.mp he).1
    refine ⟨e.1, fun l => (hgE _).mp (h3 l), ?_⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨e.2, e.2 + 1, (fin3_ne_succ e.2), h1, h2⟩
    · exact ⟨e.2 + 1, e.2, (fin3_ne_succ e.2).symm, h2, h1⟩
  · -- An edge on `σ` from `q₀`, of a tile east of `σ`, is an `a` edge.
    intro E τ hτ hE hEe
    obtain ⟨e', he', -, hends⟩ := edge_of_tileEdge hEe
    have hq₀g : g q₀ = c₀ := hgx s 0 (by ring)
    have hQg : g (q₀ + τ • w) = c₀ := by
      simp only [q₀, x, w]; rw [lat_add_w]; exact hgx _ _ (by ring)
    have hmem : (E, e') ∈ D.lineChain g c₀ := by
      rw [Dissection.mem_lineChain]
      refine ⟨?_, ?_, fun l => (hgE _).mpr (hE l)⟩
      · rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [h1]; exacts [hq₀g, hQg]
      · rcases hends with ⟨-, h2⟩ | ⟨-, h2⟩ <;> simp only [h2]; exacts [hQg, hq₀g]
    have hq₀R : q₀ ≠ R := fun h => by
      have := (x_inj hS hF h).2; have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    have hsub : (D.tile E).edge e' ⊆ segment ℝ q₀ R := by
      rcases TwoCs.chain_dich D.toDissection hg hq₀R hq₀g (hgx _ _ (by ring)) hendP hendR hmem
        with h | h
      · exact h
      · exfalso
        set σ' := min τ r / 2
        have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
        have hσ : 0 < σ' := by positivity
        have hστ : σ' ≤ τ := by have := min_le_left τ (r : ℝ); simp only [σ']; linarith
        have hσr : σ' ≤ r := by have := min_le_right τ (r : ℝ); simp only [σ']; linarith
        have h1 : q₀ ∈ (D.tile E).edge e' ∩ segment ℝ q₀ R :=
          ⟨by rw [he']; exact left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
        have h2 : q₀ + σ' • w ∈ (D.tile E).edge e' ∩ segment ℝ q₀ R :=
          ⟨by rw [he']; exact mem_seg_smul hτ hσ.le hστ,
            by rw [hRq]; exact mem_seg_smul (by exact_mod_cast hr) hσ.le hσr⟩
        have := h h1 h2
        have : σ' • w = 0 := by rw [← add_right_inj q₀, ← this, add_zero]
        exact (smul_ne_zero hσ.ne' hw0) this
    have := hallA (E, e') (Finset.mem_filter.mpr ⟨hmem, hsub⟩)
    simp only at this
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hnw,
        Real.norm_of_nonneg hτ.le] at this
      linarith
    · rw [h1, h2, dist_eq_norm, add_sub_cancel_left, norm_smul, hnw,
        Real.norm_of_nonneg hτ.le] at this
      linarith

end BlockB

end TriangleTiling.Prime
