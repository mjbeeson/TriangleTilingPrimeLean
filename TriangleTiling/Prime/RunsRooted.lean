/-
**`lemma:rootedblock`** ("How not to start a run") of M. Beeson and E. Roșu, *Tiling a triangle
into a prime number of congruent triangles*, Section 11.

The printed proof: `H(w)` says `𝒯(w, w)` occurs; `H(1)` holds since `T₁ = Δ_{0,0}`; and `H(w)`
implies `w < n` and `H(w + 1)` (`rooted_step`), so `H(n)` gives `n < n`. The step: `P = x(0, w)`
lies inside an edge, on the line `UP`, of a tile west of `UP` (`rooted_west`); the edges east of
`PQ` are `w` edges of length `a`, the tiles `∇_{i, w-1-i}` (`block_east`, `block_nablas`); `w < n`;
`T_{w+1} = Δ_{w,0}` (`block_next`); and the tiles `G_j`, `1 ≤ j ≤ w` (`block_G`, `G_core`), are
`Δ_{w-j,j}`, or the first one that is not contradicts `lemma:block`.

Statement checked by Beeson. Readings: "lying on the opposite side of the line `UW` from
`T₁`" is: for every vertex `y` of the tile and `z` of `T₁`, `y - U` and `z - U` are not strictly on
the same side of `W - U` (`cross (W - U) (y - U) * cross (W - U) (z - U) ≤ 0`); "its `a` edge or
its `c` edge on the ray `UW`" is: `U` and a point `U + l (W - U)`, `l > 0`, are vertices of the
tile at distance `a` or `c`.
-/
import TriangleTiling.Prime.RunsRootedA

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

section Rooted

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

/-- **The step of `lemma:rootedblock`**: `H(w)` implies `w < n` and `H(w + 1)`. -/
theorem rooted_step {n : ℕ} {t : ℕ → Fin N} (hrun : run D j c n U I t) (hnk : (n : ℤ) < k)
    (hstop : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I)
    {t₀ : Fin N} (ht₀ : ∀ l, crdI U I J ((D.tile t₀).pts l) ≤ 0) {τ : ℝ} (hτ : 0 < τ)
    (hτac : τ = a ∨ τ = c) (ht₀e : TileEdge D t₀ U (U + τ • J))
    (hblock : ∀ s r i₀ : ℕ, ∀ G : Fin N, 1 ≤ r → r < s → s ≤ n →
      TOccurs D (lat U I J b c) s r → i₀ + r < s →
      (∀ l, (r : ℝ) * b ≤ crdJ U I J ((D.tile G).pts l)) →
      TileEdge D G (lat U I J b c i₀ r) (lat U I J b c i₀ r + b • I) → False)
    {w : ℕ} (hw : 1 ≤ w) (hwn : w ≤ n) (hH : TOccurs D (lat U I J b c) w w) :
    w < n ∧ TOccurs D (lat U I J b c) (w + 1) (w + 1) := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  have hwk : (w : ℤ) < k := lt_of_le_of_lt (by exact_mod_cast hwn) hnk
  set x := lat U I J b c
  set P := x 0 w
  have hPw : x ((w : ℝ) - w) w = P := by simp [P]
  have hφ : ∀ u v : ℝ, b * crdI U I J (x u v) + c * crdJ U I J (x u v) = b * c * (u + v) := by
    intro u v; rw [crdI_x hF, crdJ_x hF]; ring
  -- `P` lies inside an edge of a tile `N_w` west of `UP`.
  obtain ⟨e, he, hPe⟩ := rooted_west hS hF hw hwk hH ht₀ hτ hτac ht₀e
  obtain ⟨h1, h2, h3⟩ := Dissection.mem_lineChain.mp he
  have hgI : ∀ y, lineF I J 1 0 y = crdI U I J y + lineF I J 1 0 U := lineI_apply
  have hA0 : crdI U I J ((D.tile e.1).pts e.2) = 0 := by rw [hgI] at h1; linarith
  have hB0 : crdI U I J ((D.tile e.1).pts (e.2 + 1)) = 0 := by rw [hgI] at h2; linarith
  -- `N_w` has a vertex west of `PQ`.
  have hNw : ∃ l, b * crdI U I J ((D.tile e.1).pts l) + c * crdJ U I J ((D.tile e.1).pts l) <
      (b * c) * w := by
    have hPe' := hPe
    rw [openSegment_eq_image_lineMap] at hPe'
    obtain ⟨θ, ⟨h0, h1'⟩, hθ⟩ := hPe'
    have hcJ := crdJ_affine (U := U) (I := I) (J := J) ((D.tile e.1).pts e.2)
      ((D.tile e.1).pts (e.2 + 1)) θ
    rw [hθ, crdJ_x hF] at hcJ
    have hne : crdJ U I J ((D.tile e.1).pts e.2) ≠ crdJ U I J ((D.tile e.1).pts (e.2 + 1)) := by
      intro h; exact tri_pts_succ_ne _ _ (eq_of_crd hF.hIJ (hA0.trans hB0.symm) h)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine ⟨e.2, ?_⟩; rw [hA0]
      have : crdJ U I J ((D.tile e.1).pts e.2) < (w : ℝ) * b := by
        nlinarith [mul_pos h0 (sub_pos.mpr hlt)]
      nlinarith [mul_lt_mul_of_pos_left this hc]
    · refine ⟨e.2 + 1, ?_⟩; rw [hB0]
      have : crdJ U I J ((D.tile e.1).pts (e.2 + 1)) < (w : ℝ) * b := by
        nlinarith [mul_pos (sub_pos.mpr h1') (sub_pos.mpr hlt)]
      nlinarith [mul_lt_mul_of_pos_left this hc]
  -- `Δ_{0,w-1}` has its `γ` angle at `P`.
  obtain ⟨tP, htP⟩ := hH.1 0 (w - 1) (by omega) (by omega)
  have hw1 : ((w - 1 : ℕ) : ℝ) + 1 = w := by rw [Nat.cast_sub hw]; ring
  obtain ⟨-, -, hPγ⟩ := delta_angles hS hF htP
  have eP : x ((0 : ℕ) : ℝ) (((w - 1 : ℕ) : ℝ) + 1) = P := by rw [hw1]; simp [P]
  replace hPγ : HasAngle D tP P γ := eP ▸ hPγ
  have hγπ : γ < π := by linarith
  have hPe' : x ((w : ℝ) - w) w ∈
      openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by rw [hPw]; exact hPe
  have hPγ' : HasAngle D tP (x ((w : ℝ) - w) w) γ := by rw [hPw]; exact hPγ
  -- The chain east of `PQ`, and the `∇`s.
  obtain ⟨hPint, hEast, hσa⟩ := block_east hS hF hw le_rfl hwk hH hNw hPe' hPγ' hγ0 hγπ
  replace hPint : P ∈ interior D.target.carrier := hPw ▸ hPint
  have hEast' : ∀ i : ℕ, ∃ E : Fin N, i < w →
      (∀ l, (b * c) * w ≤ b * crdI U I J ((D.tile E).pts l) + c * crdJ U I J ((D.tile E).pts l)) ∧
      TileEdge D E (x ((w : ℝ) - i) i) (x ((w : ℝ) - i - 1) (i + 1)) := by
    intro i
    by_cases hi : i < w
    · obtain ⟨E, h⟩ := hEast i hi; exact ⟨E, fun _ => h⟩
    · exact ⟨e.1, fun h => absurd h hi⟩
  choose E hE' using hEast'
  have hE := fun i hi => (hE' i hi).1
  have hEe := fun i hi => (hE' i hi).2
  have hlaN := Tri.localAngle_openSegment _ _ hPe
  -- No tile east of `PQ` has its `γ` angle at `P`.
  have htop : ¬ HasAngle D (E (w - 1)) (x ((w : ℝ) - w) w) γ := by
    intro h
    rw [hPw] at h
    have l2 := localAngle_of_hasAngle hPγ
    have l3 := localAngle_of_hasAngle h
    have n01 : e.1 ≠ tP := tile_ne_of_angle (by rw [hlaN, l2]; exact hγπ.ne')
    have n02 : e.1 ≠ E (w - 1) := tile_ne_of_angle (by rw [hlaN, l3]; exact hγπ.ne')
    have n12 : tP ≠ E (w - 1) := by
      apply tile_ne_of_pt (P := x ((0 : ℕ) : ℝ) ((w - 1 : ℕ) : ℝ)) (by rw [htP]; simp)
      rintro ⟨l, hl⟩
      have := hE (w - 1) (by omega) l
      rw [hl, hφ, Nat.cast_sub hw] at this
      have : (0 : ℝ) < b * c := by positivity
      push_cast at *; nlinarith
    have := sum3_le D n01 n02 n12 P
    rw [hlaN, l2, l3] at this
    have := target_le_two_pi D P
    linarith
  have hnab := block_nablas hS hF hw E (fun i hi l => hE i hi l) hEe htop
  -- `w < n`.
  have hE0 : HasAngle D (E 0) (x w 0) γ := by
    have := (hnab 0 (by omega)).2; simpa using this
  have hwn' : w < n := by
    by_contra hno
    have hwn'' : w = n := by omega
    set V := x n 0
    have hVU : V = U + ((n : ℝ) * c) • I := by simp [V, x, lat]
    rw [← hVU] at hstop
    rw [hwn''] at hE0
    by_cases hV : V ∈ Set.range D.target.pts
    · obtain ⟨j', hj'⟩ := hV
      obtain ⟨l, hl, ha'⟩ := hE0
      exact hS.noγ j' (E 0) l (hl.trans hj'.symm) ha'
    obtain ⟨t', lam, hlam, -, hte, hγt'⟩ := hstop.resolve_left hV
    have hne : E 0 ≠ t' := by
      apply Ne.symm
      apply tile_ne_of_pt (P := V + lam • I) (mem_range_of_tileEdge hte).2
      rw [(hnab 0 (by omega)).1]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      have hc0 : crdJ U I J (V + lam • I) = 0 := by
        rw [crdJ_addv, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero, zero_div,
          add_zero]
        simp only [V]; rw [crdJ_x hF]; ring
      have hIne : I ≠ 0 := fun h => by
        have := hF.nI; rw [h, norm_zero] at this; exact zero_ne_one this
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have : lam • I = 0 := by
          rw [← add_right_inj V, add_zero, h]; simp [V, hwn'']; rfl
        exact smul_ne_zero hlam.ne' hIne this
      · have := congrArg (crdJ U I J) h; rw [hc0, crdJ_x hF] at this; push_cast at this
        linarith
      · have := congrArg (crdJ U I J) h; rw [hc0, crdJ_x hF] at this; push_cast at this
        linarith
    have hgX : ∀ t ∈ ({E 0, t'} : Finset (Fin N)), ∀ y ∈ (D.tile t).carrier,
        lineF I J 0 1 V ≤ lineF I J 0 1 y := by
      intro t _ y hy
      rw [lineF_apply U I J V 0 1, lineF_apply U I J y 0 1]
      have := hF.north y (tile_subset_target D.toDissection t hy)
      simp only [V]; rw [crdJ_x hF]; linarith
    have := halfplane_sum_le D.toDissection (lineF_ne_zero hF.hIJ (Or.inr one_ne_zero)) _ hgX
    rw [Finset.sum_pair hne, localAngle_of_hasAngle hE0, localAngle_of_hasAngle hγt'] at this
    linarith
  refine ⟨hwn', ?_⟩
  -- `T_{w+1} = Δ_{w,0}`.
  obtain ⟨tq, htq⟩ := hH.1 (w - 1) 0 (by omega) (by omega)
  have hs1 : ((w - 1 : ℕ) : ℝ) = w - 1 := by rw [Nat.cast_sub hw]; simp
  rw [hs1, show (w : ℝ) - 1 + 1 = w by ring] at htq
  simp only [Nat.cast_zero, zero_add] at htq
  have hnext := block_next hS hF hrun hw hwn' htq hE0
  -- The dichotomy for `G_q`, `1 ≤ q ≤ w`.
  have hdich : ∀ q, 1 ≤ q → q < w + 1 →
      (∃ G, Set.range (D.tile G).pts = {x ((w : ℝ) - q) q, x ((w : ℝ) - q + 1) q,
        x ((w : ℝ) - q) (q + 1)}) ∨
      ∃ G, (∀ l, (q : ℝ) * b ≤ crdJ U I J ((D.tile G).pts l)) ∧
        TileEdge D G (x ((w : ℝ) - q) q) (x ((w : ℝ) - q) q + b • I) := by
    intro q hq1 hqw
    by_cases hqw' : q < w
    · exact block_G hS hF hw le_rfl hH E hnab hq1 hqw'
    · have hq : q = w := by omega
      subst hq
      rw [hPw]
      -- the ray `I`: the `c` edge of `∇_{0, q-1}`
      have hEq := (hnab (q - 1) (by omega)).1
      have hq1' : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub hq1]; simp
      have hPI : P + c • I = x 1 q := by
        simp only [P, x]; rw [show c • I = (1 * c) • I by rw [one_mul], lat_add_I]; simp
      have hu : RayWall D.toDissection P I := by
        refine rayWall_of_tileEdge (t := E (q - 1)) hc ?_
        rw [hPI]
        refine tileEdge_of_range hEq ?_ ?_ ?_
        · right; left; exact lat_eq (by rw [hq1']; ring) (by rw [hq1']; ring)
        · right; right; exact lat_eq (by rw [hq1']; ring) (by rw [hq1']; ring)
        · intro h; have := (x_inj hS hF h).1; linarith
      -- the ray `J`: the edge of `N_w` beyond `P`
      have hJne : J ≠ 0 := fun h => by
        have := hF.nJ; rw [h, norm_zero] at this; exact zero_ne_one this
      have hPI0 : crdI U I J P = 0 := by simp only [P]; rw [crdI_x hF]; ring
      obtain ⟨δ, hδ, hext⟩ := seg_ext hJne (tri_pts_succ_ne _ _)
        (eq_add_J hF (hA0.trans hPI0.symm)) (eq_add_J hF (hB0.trans hPI0.symm)) hPe
      have hv : RayWall D.toDissection P J :=
        ⟨δ, hδ, fun s hs hsδ i => D.edge_point_not_interior (j := e.1) (k := e.2)
          (hext s hs hsδ) i⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior P hPint
      have hin : ∃ r > (0 : ℝ), sectorC P I J ∩ ball P r ⊆ D.target.carrier :=
        ⟨ε, hε, fun y hy => interior_subset (hball hy.2)⟩
      rcases G_core hS hF hu hv hin (v₀ := q) (by simp only [P]; rw [crdJ_x hF]) with
        ⟨G, hG⟩ | ⟨G, hGn, hGe⟩
      · left; refine ⟨G, ?_⟩; rw [hG, hPI]
        have : P + b • J = x 0 ((q : ℝ) + 1) := by
          simp only [P, x]; rw [show b • J = (1 * b) • J by rw [one_mul], lat_add_J]
        rw [this]; simp
      · right; exact ⟨G, hGn, hGe⟩
  by_cases hall : ∀ q, 1 ≤ q → q < w + 1 → ∃ G, Set.range (D.tile G).pts =
      {x ((w : ℝ) - q) q, x ((w : ℝ) - q + 1) q, x ((w : ℝ) - q) (q + 1)}
  · exact extend_T hS hF (Or.inr ⟨rfl, rfl⟩) hH hnext E hnab hall
  · exfalso
    push Not at hall
    have hex : ∃ q, 1 ≤ q ∧ q < w + 1 ∧ ∀ G, Set.range (D.tile G).pts ≠
        {x ((w : ℝ) - q) q, x ((w : ℝ) - q + 1) q, x ((w : ℝ) - q) (q + 1)} := hall
    set q := Nat.find hex
    obtain ⟨hq1, hqw, hqG⟩ := Nat.find_spec hex
    have hmin : ∀ q', 1 ≤ q' → q' < q → ∃ G, Set.range (D.tile G).pts =
        {x ((w : ℝ) - q') q', x ((w : ℝ) - q' + 1) q', x ((w : ℝ) - q') (q' + 1)} := by
      intro q' h1 h2
      by_contra hno
      push Not at hno
      exact Nat.find_min hex h2 ⟨h1, by omega, hno⟩
    rcases hdich q hq1 hqw with ⟨G, hG⟩ | ⟨G, hGn, hGe⟩
    · exact hqG G hG
    · have hsq : (((w - q : ℕ) : ℝ)) = w - q := by rw [Nat.cast_sub (by omega)]
      refine hblock (w + 1) q (w - q) G hq1 (by omega) (by omega)
        (extend_T hS hF (Or.inl (by omega)) hH hnext E hnab hmin) (by omega) hGn ?_
      rw [hsq]; exact hGe

end Rooted

/-- **Lemma `lemma:rootedblock`** (How not to start a run). Let `T₁, …, T_n` be a run on a side `S`
of `T`, supported by `UV`, with `n < k`, stopped at `V`, and with `T₁` having its `α` angle at `U`
and its `b` side on `UW` (`W` the vertex of `T₁` at its `γ` angle). Then no tile with a vertex at
`U`, lying on the opposite side of the line `UW` from `T₁`, has its `a` edge or its `c` edge on the
ray `UW`. -/
theorem rootedblock {N : ℕ} {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hS : RunSetting D α β γ a b c m k) {j : Fin 3} {n : ℕ} {U I W : Plane} {t : ℕ → Fin N}
    (hrun : run D j c n U I t) (hn : 1 ≤ n) (hnk : (n : ℤ) < k)
    (hstop : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I)
    (hU : HasAngle D (t 1) U α) (hW : HasAngle D (t 1) W γ) :
    ¬ ∃ (t₀ : Fin N) (P : Plane), (∃ l > (0 : ℝ), P = U + l • (W - U)) ∧ TileEdge D t₀ U P ∧
      (dist U P = a ∨ dist U P = c) ∧
      ∀ y ∈ Set.range (D.tile t₀).pts, ∀ z ∈ Set.range (D.tile (t 1)).pts,
        cross (W - U) (y - U) * cross (W - U) (z - U) ≤ 0 := by
  rintro ⟨t₀, P, ⟨l, hl, rfl⟩, ht₀e, hd, hside⟩
  obtain ⟨hF, hr1⟩ := hS.frame hrun hn hU hW
  set J := b⁻¹ • (W - U)
  have hb := hS.b_pos; have hc := hS.c_pos
  have hWJ : W - U = b • J := by simp only [J]; rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  have hJne : J ≠ 0 := fun h => by have := hF.nJ; rw [h, norm_zero] at this; exact zero_ne_one this
  -- `T₀` is west of `UW`.
  have hU0 : lat U I J b c 0 0 = U := by simp [lat]
  have hW1 : lat U I J b c 0 1 = W := by
    simp only [lat, zero_mul, zero_smul, add_zero, one_mul, zero_add]
    rw [← hWJ]; abel
  have hcr : ∀ z, cross (W - U) (z - U) = -(b * crdI U I J z) * cross I J := by
    intro z
    have cU : crdI U I J U = 0 := by simp [crdI, cross]
    have cJU : crdJ U I J U = 0 := by simp [crdJ, cross]
    have cW : crdI U I J W = 0 := by rw [← hW1, crdI_x hF]; ring
    have cJW : crdJ U I J W = b := by rw [← hW1, crdJ_x hF]; ring
    rw [cross_frame (U := U) hF.hIJ, cU, cJU, cW, cJW]; ring
  have ht₀ : ∀ i, crdI U I J ((D.tile t₀).pts i) ≤ 0 := by
    intro i
    have h := hside _ ⟨i, rfl⟩ (U + c • I) (by rw [hr1]; simp)
    rw [hcr, hcr] at h
    have hcI : crdI U I J (U + c • I) = c := by
      have := crdI_comb (U := U) hF.hIJ c 0; simpa using this
    rw [hcI] at h
    have hsq := mul_self_pos.mpr hF.hIJ
    by_contra hpos
    push Not at hpos
    have : 0 < (b * crdI U I J ((D.tile t₀).pts i)) * (b * c) * (cross I J * cross I J) := by
      positivity
    nlinarith
  -- the edge of `T₀` on the ray `UW`
  have hτ : 0 < l * b := mul_pos hl hb
  have hPτ : U + l • (W - U) = U + (l * b) • J := by rw [hWJ, smul_smul]
  rw [hPτ] at ht₀e hd
  have hdτ : dist U (U + (l * b) • J) = l * b := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ, mul_one,
      Real.norm_of_nonneg hτ.le]
  rw [hdτ] at hd
  -- `lemma:block`, in the form used by the step.
  have hblock : ∀ s r i₀ : ℕ, ∀ G : Fin N, 1 ≤ r → r < s → s ≤ n →
      TOccurs D (lat U I J b c) s r → i₀ + r < s →
      (∀ l, (r : ℝ) * b ≤ crdJ U I J ((D.tile G).pts l)) →
      TileEdge D G (lat U I J b c i₀ r) (lat U I J b c i₀ r + b • I) → False := by
    intro s r i₀ G hr hrs hsn hT hi₀ hGn hGe
    refine block hS hrun hnk hstop hU hW hr hrs hsn ⟨hT, i₀, by omega, G, fun l => ?_, hGe⟩
    refine ⟨crdI U I J ((D.tile G).pts l) / c, crdJ U I J ((D.tile G).pts l) / b - r, ?_, ?_⟩
    · have := hGn l
      rw [sub_nonneg, le_div_iff₀ hb]; linarith
    · conv_lhs => rw [decomp (U := U) hF.hIJ ((D.tile G).pts l)]
      simp only [lat]
      congr 2 <;> field_simp <;> ring
  -- `H(w)` for all `w ≤ n`.
  have hH1 : TOccurs D (lat U I J b c) 1 1 := by
    constructor
    · intro i q hq hiq
      have hi : i = 0 := by omega
      have hq0 : q = 0 := by omega
      subst hi hq0
      refine ⟨t 1, ?_⟩
      rw [hr1]
      have e1 : lat U I J b c ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = U := by simp [lat]
      have e2 : lat U I J b c (((0 : ℕ) : ℝ) + 1) ((0 : ℕ) : ℝ) = U + c • I := by simp [lat]
      have e3 : lat U I J b c ((0 : ℕ) : ℝ) (((0 : ℕ) : ℝ) + 1) = W := by
        rw [← hW1]; simp
      rw [e1, e2, e3]
    · intro i q hq hiq; omega
  have hH : ∀ w, 1 ≤ w → w ≤ n → TOccurs D (lat U I J b c) w w := by
    intro w hw
    induction w, hw using Nat.le_induction with
    | base => intro _; exact hH1
    | succ w hw ih =>
      intro hwn
      exact (rooted_step hS hF hrun hnk hstop ht₀ hτ hd ht₀e hblock hw (by omega)
        (ih (by omega))).2
  have := (rooted_step hS hF hrun hnk hstop ht₀ hτ hd ht₀e hblock hn le_rfl (hH n hn le_rfl)).1
  omega


end TriangleTiling.Prime
