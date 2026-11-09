/-
`theorem:necessaryconditions` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723):
an `N`-tiling of an equilateral triangle `ABC` with side `X` by a tile with angles `(α, β, π/3)`, `α`
not a rational multiple of `π`, witnesses a relation `j c = ℓ a + m b` with `j c < X`.

Statement checked by Beeson. The rest of the theorem (the area and coloring equations) is
`theorem:coloring` and `lemma:equilateral3` (part (ii) has been removed from the paper).

The existence of a witnessed relation is not proved as in the paper. It is Laczkovich's argument in
DCG 48 (2012), Sect. 8.3 (Bonfioli's `no_adjacent_pi3`, here `no_adjacent_pi3_W` with "no witnessed
relation" in place of `NotComb`): if no relation is witnessed, then along a side of `ABC` the tile at
the first corner has `γ` at its tail, the propagation argument of
Laczkovich's Lemma 4.4 (i) as used in Sect. 8.3 (pp. 348 and 370; Bonfioli's "`γ` rule") propagates this to the last tile, which also has
`γ` at the second corner, so it has two `γ` angles. The bound `j c < X` is the paper's: the
witnessing segment has tiles on both sides, so it is not a side of `ABC`, and
`lemma:equilateralbound` applies.
-/
import TriangleTiling.Laczkovich.EquilateralGammaC
import TriangleTiling.Laczkovich.W.NoAdjacent
import TriangleTiling.Equilateral.EquilateralBound
import Erdos634.Draft.LaczFormalRG4IVa

open scoped Classical

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21
  Erdos634.Draft.LaczFormal.RG Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha
open Erdos634.Draft.LaczFormal.Graph (V2 neg2 toV2 TriStep crs Par)

variable {N : ℕ}

namespace Necessary

/-- If no relation `j c = ℓ a + m b` is witnessed, Laczkovich's Sect. 8.3 gives a contradiction. -/
theorem witnessed (D : CongruentDissection N) {α β a b c : ℝ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hT : TileSides D α β (Real.pi / 3) a b c)
    (hα : IrrPi α) : ∃ j ℓ m, Witnesses D.toDissection.toRegion a b c j ℓ m := by
  by_contra hne
  push Not at hne
  have hnw : ∀ j ℓ m, ¬ Witnesses D.toDissection.toRegion a b c j ℓ m := hne
  -- the tile is scalene (as in `noboundarylink`)
  have hsum : α + β + Real.pi / 3 = Real.pi := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [← h0, ← h1, ← h2, e, D.model.angleAt_sum]
  have hγα : Real.pi / 3 ≠ α := fun e => hα ⟨1 / 3, by rw [← e]; push_cast; ring⟩
  have hγβ : Real.pi / 3 ≠ β := fun e => hα ⟨1 / 3, by push_cast; linarith⟩
  have hαβ : α ≠ β := fun e => hα ⟨1 / 3, by push_cast; linarith⟩
  have hab : a ≠ b := sides_ne_of_angles_ne D hT hαβ
  have hcb : c ≠ b := by
    refine sides_ne_of_angles_ne D (α := Real.pi / 3) (β := β) (γ := α) (a := c) (b := b) (c := a) ?_ hγβ
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ * Equiv.swap 0 2, ?_⟩
    simp only [Equiv.Perm.mul_apply, swap02_0, swap02_1, swap02_2]
    exact ⟨h2, h1, h0, l2, l1, l0⟩
  have hca : c ≠ a := by
    refine sides_ne_of_angles_ne D (α := Real.pi / 3) (β := α) (γ := β) (a := c) (b := a) (c := b) ?_ hγα
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ * Equiv.swap 0 2 * Equiv.swap 1 2, ?_⟩
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp (config := { decide := true })
    exact ⟨h2, h0, h1, l2, l0, l1⟩
  -- the tiling as a polygon tiling, model relabeled so that `γ` is at vertex `2`
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have heq := equilateral_sides D.target hP
  set T := polyTilingOf D σ heq with hTdef
  obtain ⟨hang, hPang⟩ := polyTilingOf_angles D σ heq
  have hslen : ∀ k, slen D.toRegion k = D.model.oppLen k := by
    intro k; fin_cases k <;> rfl
  have hsl : ∀ j, slen T.C j = D.model.oppLen (σ j) := by
    intro j
    show slen (relabel D.toRegion σ) j = _
    rw [relabel_slen, hslen]
  have sa : slen T.C 0 = a := by rw [hsl, l0]
  have sb : slen T.C 1 = b := by rw [hsl, l1]
  have sc : slen T.C 2 = c := by rw [hsl, l2]
  have hαT : ¬ ∃ r : ℚ, Erdos634.TilePlacement.angleAt T.C.model 0 = (r : ℝ) * Real.pi := by
    rw [hang 0, h0]; exact hα
  have hγT : Erdos634.TilePlacement.angleAt T.C.model 2 = Real.pi / 3 := by rw [hang 2, h2]
  have hreg : RegularPQ T.C := regular_of_irr_pi3 T hγT hαT hPang
  have hnw' : ∀ j ℓ m, ¬ Witnesses T.C.toRegionDissection (slen T.C 0) (slen T.C 1) (slen T.C 2) j ℓ m := by
    rw [sa, sb, sc]; exact hnw
  obtain ⟨idx, h⟩ := caseCW_of_regular T hreg (by rwa [sa, sb]) (by rwa [sc, sa]) (by rwa [sc, sb]) hnw'
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hγ' : T.C.model.angleAt 2 = Real.pi / 3 := hγT
  exact no_adjacent_pi3_W T.C T.P T.region_eq idx h hγ' 0 (hPang _) (hPang _)

theorem sum_const {ι : Type*} (L : List ι) (f : ι → ℝ) (c : ℝ) (h : ∀ e ∈ L, f e = c) :
    (L.map f).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.sum_cons, h x List.mem_cons_self,
      ih fun e he => h e (List.mem_cons_of_mem _ he), List.length_cons]
    push_cast; ring

theorem crs_add (d : V2) (u v : Plane) : crs d (toV2 (u + v)) = crs d (toV2 u) + crs d (toV2 v) := by
  simp only [crs, toV2, PiLp.add_apply]; ring

theorem crs_smul (d : V2) (r : ℝ) (u : Plane) : crs d (toV2 (r • u)) = r * crs d (toV2 u) := by
  simp only [crs, toV2, PiLp.smul_apply, smul_eq_mul]; ring

theorem crs_sub (d : V2) (u v : Plane) : crs d (toV2 (u - v)) = crs d (toV2 u) - crs d (toV2 v) := by
  simp only [crs, toV2, PiLp.sub_apply]; ring

/-- A segment along `d` with tiles on both sides is not a side of the target triangle: if `X, Y` are
two different vertices of the target, there are no walks on both sides of `XY`. -/
theorem not_side (D : CongruentDissection N) {d : V2} {X Y : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toDissection.toRegion d X Y L1) (W2 : WalkR D.toDissection.toRegion d X Y L2)
    (h1 : L1 ≠ []) (h2 : L2 ≠ []) {i0 j0 : Fin 3} (hij : i0 ≠ j0)
    (hX : X = D.target.pts i0) (hY : Y = D.target.pts j0) : False := by
  obtain ⟨Tp, -, hTp, -⟩ := walkR_progress W2
  -- a point on the left of `XY` and a point on the right, both in the target
  obtain ⟨g, hg, hgpos⟩ : ∃ Z ∈ D.target.carrier, 0 < crs d (toV2 (Z - X)) := by
    cases W1 with
    | nil => exact absurd rfl h1
    | @cons i _ X' _ L hS _ =>
      obtain ⟨kk, f, g, hk, -, -, -, -, -, hpos⟩ := hS
      refine ⟨_, tile_subset_target D.toDissection i (subset_convexHull ℝ _ ⟨g, rfl⟩), ?_⟩
      exact hpos
  obtain ⟨g', hg', hgneg⟩ : ∃ Z ∈ D.target.carrier, crs d (toV2 (Z - X)) < 0 := by
    cases W2 with
    | nil => exact absurd rfl h2
    | @cons i _ X' _ L hS _ =>
      obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, hpos⟩ := hS
      refine ⟨_, tile_subset_target D.toDissection i (subset_convexHull ℝ _ ⟨g, rfl⟩), ?_⟩
      have hp := hpar.1
      change 0 < crs (neg2 d) (toV2 ((D.tile i).pts g - X')) at hpos
      simp only [crs, toV2, neg2, PiLp.sub_apply] at hp hpos ⊢
      linarith
  -- every point of the target is on one side of `XY`
  have s0 : crs d (toV2 (D.target.pts i0 - X)) = 0 := by
    rw [← hX, sub_self]; simp [crs, toV2]
  have s1 : crs d (toV2 (D.target.pts j0 - X)) = 0 := by
    rw [← hY]; simp only [crs] at *; rw [hTp]; ring
  have hcomb : ∀ Z, crs d (toV2 (Z - X)) =
      ∑ m, D.target.basis.coord m Z * crs d (toV2 (D.target.pts m - X)) := by
    intro Z
    rw [EquilateralBound.comb D.target Z X, Fin.sum_univ_three, Fin.sum_univ_three, crs_add, crs_add,
      crs_smul, crs_smul, crs_smul]
  have hc := fun Z (hZ : Z ∈ D.target.carrier) => (Tri.mem_carrier_iff_coord D.target Z).mp hZ
  by_cases hall : ∀ m, 0 ≤ crs d (toV2 (D.target.pts m - X))
  · have : 0 ≤ crs d (toV2 (g' - X)) := by
      rw [hcomb]; exact Finset.sum_nonneg fun m _ => mul_nonneg (hc g' hg' m) (hall m)
    linarith
  · push Not at hall
    obtain ⟨m, hm⟩ := hall
    have hmi : m ≠ i0 := by rintro rfl; linarith
    have hmj : m ≠ j0 := by rintro rfl; linarith
    have cover : ∀ x : Fin 3, x = i0 ∨ x = j0 ∨ x = m := by
      have key : ∀ a b c x : Fin 3, a ≠ b → c ≠ a → c ≠ b → x = a ∨ x = b ∨ x = c := by decide
      exact fun x => key _ _ _ x hij hmi hmj
    have hle : ∀ x, crs d (toV2 (D.target.pts x - X)) ≤ 0 := by
      intro x
      rcases cover x with rfl | rfl | rfl
      · exact s0.le
      · exact s1.le
      · exact hm.le
    have : crs d (toV2 (g - X)) ≤ 0 := by
      rw [hcomb]
      exact Finset.sum_nonpos fun x _ => mul_nonpos_of_nonneg_of_nonpos (hc g hg x) (hle x)
    linarith

end Necessary

open Necessary in
/-- **Theorem `theorem:necessaryconditions`.** Suppose an equilateral triangle `ABC` with side
`X` is `N`-tiled by a tile with angles `(α, β, π/3)` opposite its sides `(a, b, c)`, where `α` is not a
rational multiple of `π`. Then the tiling witnesses a relation `j c = ℓ a + m b` with `j > 0` and
`j c < X`. -/
theorem necessaryconditions (D : CongruentDissection N) {α β a b c : ℝ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hT : TileSides D α β (Real.pi / 3) a b c)
    (hα : IrrPi α) :
    ∃ j ℓ m, Witnesses D.toDissection.toRegion a b c j ℓ m ∧
      (j : ℝ) * c < dist (D.target.pts 0) (D.target.pts 1) := by
  obtain ⟨j, ℓ, m, hw⟩ := witnessed D hP hT hα
  refine ⟨j, ℓ, m, hw, ?_⟩
  have hc : 0 < c := by
    obtain ⟨σ, -, -, -, -, -, l2⟩ := hT
    rw [← l2]; exact ThreeAlpha.oppLen_pos _ _
  obtain ⟨d, X, Y, P, Q, hW, hj, hPc, -, -, hlen⟩ := hw
  have hsumP := sum_const P (fun e => dist e.2.1 e.2.2) c hPc
  have hjpos : 0 < (j : ℝ) * c := mul_pos (by exact_mod_cast hj) hc
  obtain ⟨L1, L2, W1, W2, hXY⟩ : ∃ L1 L2, WalkT D.toDissection.toRegion d X Y L1 ∧
      WalkR D.toDissection.toRegion d X Y L2 ∧ (P.map fun e => dist e.2.1 e.2.2).sum = dist X Y := by
    rcases hW with ⟨w1, w2⟩ | ⟨w1, w2⟩
    · exact ⟨P, Q, w1, w2, walkT_dist_sum w1⟩
    · exact ⟨Q, P, w2, w1, walkR_dist_sum w1⟩
  have hd : (j : ℝ) * c ≤ dist X Y := by
    rw [← hXY, hsumP, hlen]; push_cast
    nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((Q.map fun e => dist e.2.1 e.2.2).countP
      (fun x => decide (x = c)) : ℝ))]
  have h1 : L1 ≠ [] := by rintro rfl; cases W1; simp at hd; linarith
  have h2 : L2 ≠ [] := by rintro rfl; cases W2; simp at hd; linarith
  -- the sides of `ABC`
  have hs := equilateral_sides D.target hP
  have hX' : ∀ i k, i ≠ k → dist (D.target.pts i) (D.target.pts k) = dist (D.target.pts 0) (D.target.pts 1) := by
    intro i k hik
    have key : ∀ i k : Fin 3, i ≠ k → k = i + 1 ∨ i = k + 1 := by decide
    rcases key i k hik with rfl | rfl
    · exact hs i
    · rw [dist_comm]; exact hs k
  -- `X` and `Y` are tile vertices, so they lie in `ABC`
  have hXm : X ∈ D.target.carrier := by
    cases W1 with
    | nil => exact absurd rfl h1
    | @cons i _ X' _ L hS _ =>
      obtain ⟨kk, -, -, hk, -⟩ := hS
      exact tile_subset_target D.toDissection i (hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩)
  have hYm : Y ∈ D.target.carrier := by
    obtain ⟨el, -, hel, hS⟩ := walkT_getLast W1 h1
    obtain ⟨-, f, -, -, hf, -⟩ := hS
    rw [← hel, ← hf]
    exact tile_subset_target D.toDissection el.1 (subset_convexHull ℝ _ ⟨f, rfl⟩)
  obtain ⟨hle, heqc⟩ := equilateralbound D.target hX' (D.target.convex.segment_subset hXm hYm)
  rcases hle.lt_or_eq with hlt | heq'
  · linarith
  · obtain ⟨i0, j0, hij, hX, hY⟩ := heqc heq'
    exact (not_side D W1 W2 h1 h2 hij hX hY).elim

end TriangleTiling.Equilateral
