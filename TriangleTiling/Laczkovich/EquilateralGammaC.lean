/-
Laczkovich's graph `Γ_c` in M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723):
`lemma:propagation2` (Laczkovich's Lemma 4.5) and `lemma:noboundarylink`.

Statements checked by Beeson.

* A tiling is a `PolyTiling` (a congruent dissection of a convex polygon `P`); the model's sides
  `slen C 0, slen C 1, slen C 2` are `a, b, c`, opposite the model angles `α, β, γ`.
* The tiles supported by a segment `XY` (direction `d`) on its left are a chain `WalkT d X Y P` of
  tiles whose sides on `XY` are consecutive from `X` to `Y`; on its right, a chain `WalkR d X Y Q`.
  Each entry `(i, U, U')` of a chain is a tile `i` and its side `UU'` on `XY`. A chain from `X` to
  `Y` on each side says that `X` and `Y` are vertices of tiles on both sides of `XY`.
* `Γ_c` is Bonfioli's `GaEdge` for the length `c` (Laczkovich, DCG 48 (2012), p. 346), see
  `GammaC`.
-/
import TriangleTiling.Laczkovich.W.GammaC
import TriangleTiling.Laczkovich.EquilateralSixty
import Erdos634.Draft.LaczFormalThm33iii2
import Erdos634.Draft.LaczFormalBZ8

open scoped Classical

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21
  Erdos634.Draft.LaczFormal.RG Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha
open Erdos634.Draft.LaczFormal.Graph (V2 neg2 toV2 TriStep)

variable {N M : ℕ}

/-- **The relation `j c = ℓ a + m b` is witnessed** (the definition before `lemma:propagation2`):
there is a segment `XY` (direction `d`) such that `X` and `Y` are vertices of tiles on both sides of
`XY`, the tiles supported by `XY` on one side (the chain `P`) all have their `c` edge on `XY`, and
of the tiles supported by `XY` on the other side (the chain `Q`), `ℓ` have their `a` edge, `m` their
`b` edge and `n` their `c` edge on `XY`, where `P` has `j + n` tiles and `j > 0`. (Then
`j c = ℓ a + m b`, since both sides have length `XY`.) -/
def Witnesses (R : RegionDissection N) (a b c : ℝ) (j ℓ m : ℕ) : Prop :=
  ∃ (d : V2) (X Y : Plane) (P Q : List (Fin N × Plane × Plane)),
    (WalkT R d X Y P ∧ WalkR R d X Y Q ∨ WalkR R d X Y P ∧ WalkT R d X Y Q) ∧
    0 < j ∧ (∀ e ∈ P, dist e.2.1 e.2.2 = c) ∧
    (Q.map fun e => dist e.2.1 e.2.2).countP (fun x => decide (x = a)) = ℓ ∧
    (Q.map fun e => dist e.2.1 e.2.2).countP (fun x => decide (x = b)) = m ∧
    P.length = j + (Q.map fun e => dist e.2.1 e.2.2).countP (fun x => decide (x = c))

/-- **The graph `Γ_c`** (Laczkovich, DCG 48 (2012), p. 346): an edge `X → Y` when `X` is the start of
a maximal segment `XZ` (no tile side on that line, on either side, runs through `X`; the tiles on
both sides end together at `Z`); on one side the tiles from `X` have their `c` edges on `XZ` up to
`Y`, and the next tile on that side has a vertex at `Y` and not its `c` edge on `XZ`; and the first
tile on the other side at `X` does not have its `c` edge on `XZ` (Laczkovich's condition (iv)). -/
def GammaC (R : RegionDissection N) (c : ℝ) (X Y : Plane) : Prop := GaEdge R c X Y

/-- A sum of numbers from `{a, b, c}` (distinct), counted. -/
theorem sum_eq_countP {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ L : List ℝ, (∀ x ∈ L, x = a ∨ x = b ∨ x = c) →
      L.sum = (L.countP (fun x => decide (x = a)) : ℝ) * a + (L.countP (fun x => decide (x = b)) : ℝ) * b +
        (L.countP (fun x => decide (x = c)) : ℝ) * c
  | [], _ => by simp
  | x :: L, h => by
    have ih := sum_eq_countP hab hac hbc L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x List.mem_cons_self with rfl | rfl | rfl <;>
      simp [List.countP_cons, hab, hac, hbc, hab.symm, hac.symm, hbc.symm, ih] <;> ring

/-- One side all `c`, the other side not all `c`, equal lengths: the number of `c` sides on the first
side exceeds that on the second. -/
theorem witness_count {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (P Q : List ℝ) (hP : ∀ x ∈ P, x = c) (hQ : ∀ x ∈ Q, x = a ∨ x = b ∨ x = c) (hsum : P.sum = Q.sum)
    (hne : ∃ x ∈ Q, x ≠ c) : ∃ j, 0 < j ∧ P.length = j + Q.countP (fun x => decide (x = c)) := by
  have hPs : P.sum = P.length * c := by
    rw [List.eq_replicate_iff.mpr ⟨rfl, hP⟩]; simp
  have hQs := sum_eq_countP hab hca.symm hcb.symm Q hQ
  obtain ⟨x, hx, hxc⟩ := hne
  have hpos : (0 : ℝ) < (Q.countP (fun x => decide (x = a)) : ℝ) * a + (Q.countP (fun x => decide (x = b)) : ℝ) * b := by
    rcases hQ x hx with rfl | rfl | rfl
    · have : 0 < Q.countP (fun y => decide (y = x)) := List.countP_pos_iff.mpr ⟨x, hx, by simp⟩
      have : (1 : ℝ) ≤ Q.countP (fun y => decide (y = x)) := by exact_mod_cast this
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Q.countP (fun y => decide (y = b)))) hb.le]
    · have : 0 < Q.countP (fun y => decide (y = x)) := List.countP_pos_iff.mpr ⟨x, hx, by simp⟩
      have : (1 : ℝ) ≤ Q.countP (fun y => decide (y = x)) := by exact_mod_cast this
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Q.countP (fun y => decide (y = a)))) ha.le]
    · exact absurd rfl hxc
  have hlt : Q.countP (fun x => decide (x = c)) < P.length := by
    have : (Q.countP (fun x => decide (x = c)) : ℝ) * c < P.length * c := by linarith
    exact_mod_cast lt_of_mul_lt_mul_right this hc.le
  exact ⟨P.length - Q.countP (fun x => decide (x = c)), by omega, by omega⟩

/-- **No witnessed relation `j c = ℓ a + m b` gives `NoWit` for `c`**, the hypothesis of the
`Γ_c` lemmas in `W/GammaC.lean`. -/
theorem noWit_of_not_witnesses (C : CongruentRegionDissection N) (hab : slen C 0 ≠ slen C 1)
    (hca : slen C 2 ≠ slen C 0) (hcb : slen C 2 ≠ slen C 1)
    (h : ∀ j ℓ m, ¬ Witnesses C.toRegionDissection (slen C 0) (slen C 1) (slen C 2) j ℓ m) :
    NoWit C.toRegionDissection (slen C 2) := by
  obtain ⟨idx, hidx, -⟩ := exists_idx_both C
  have memT : ∀ {d X Y} {L : List (Fin N × Plane × Plane)}, WalkT C.toRegionDissection d X Y L →
      ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen C 0 ∨ x = slen C 1 ∨ x = slen C 2 := by
    intro d X Y L W x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem C idx hidx (walkT_mem_step W e he)
  have memR : ∀ {d X Y} {L : List (Fin N × Plane × Plane)}, WalkR C.toRegionDissection d X Y L →
      ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen C 0 ∨ x = slen C 1 ∨ x = slen C 2 := by
    intro d X Y L W x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have := side_len_mem C idx hidx (walkR_mem_step W e he)
    rwa [dist_comm] at this
  have key : ∀ (P Q : List (Fin N × Plane × Plane)), (∀ e ∈ P, dist e.2.1 e.2.2 = slen C 2) →
      (∀ x ∈ Q.map (fun e => dist e.2.1 e.2.2), x = slen C 0 ∨ x = slen C 1 ∨ x = slen C 2) →
      (P.map fun e => dist e.2.1 e.2.2).sum = (Q.map fun e => dist e.2.1 e.2.2).sum →
      (∃ e ∈ Q, dist e.2.1 e.2.2 ≠ slen C 2) →
      ∃ j, 0 < j ∧ P.length = j + (Q.map fun e => dist e.2.1 e.2.2).countP (fun x => decide (x = slen C 2)) := by
    intro P Q hP hQ hs hne
    obtain ⟨e, he, hec⟩ := hne
    have := witness_count (slen_pos C 0) (slen_pos C 1) (slen_pos C 2) hab hca hcb _ _
      (fun x hx => by obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx; exact hP e' he') hQ hs
      ⟨_, List.mem_map.mpr ⟨e, he, rfl⟩, hec⟩
    rwa [List.length_map] at this
  intro d X Y P1 P2 W1 W2
  have hs : (P1.map fun e => dist e.2.1 e.2.2).sum = (P2.map fun e => dist e.2.1 e.2.2).sum := by
    rw [walkT_dist_sum W1, walkR_dist_sum W2]
  refine ⟨fun ⟨hall, hne⟩ => ?_, fun ⟨hall, hne⟩ => ?_⟩
  · obtain ⟨j, hj, hl⟩ := key P1 P2 hall (memR W2) hs hne
    exact h j _ _ ⟨d, X, Y, P1, P2, Or.inl ⟨W1, W2⟩, hj, hall, rfl, rfl, hl⟩
  · obtain ⟨j, hj, hl⟩ := key P2 P1 hall (memT W1) hs.symm hne
    exact h j _ _ ⟨d, X, Y, P2, P1, Or.inr ⟨W2, W1⟩, hj, hall, rfl, rfl, hl⟩

/-- The standing hypotheses `CaseCW` from a regular tiling with no witnessed `c`-relation. -/
theorem caseCW_of_regular [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C)
    (hab : slen T.C 0 ≠ slen T.C 1) (hca : slen T.C 2 ≠ slen T.C 0) (hcb : slen T.C 2 ≠ slen T.C 1)
    (hnw : ∀ j ℓ m, ¬ Witnesses T.C.toRegionDissection (slen T.C 0) (slen T.C 1) (slen T.C 2) j ℓ m) :
    ∃ idx, CaseCW T.C idx := by
  obtain ⟨idx, hA, hcnt⟩ := hreg
  exact ⟨idx, idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X,
    noWit_of_not_witnesses T.C hab hca hcb hnw, hcb, hca⟩

/-- **Lemma `lemma:propagation2`** (Laczkovich's Lemma 4.5). In a regular tiling of a convex polygon
with no witnessed relation `j c = ℓ a + m b`, let `V` be a vertex of the tiling on a segment `XY`,
in its interior, and let two tiles supported by `XY` on the same side (the left of the direction
`d`) have a vertex at `V`, one with its side on `XY` ending at `V` and one with its side on `XY`
starting at `V`. Suppose exactly one of these two sides has length `c`. If either
* `V` is an inner point of a side `W'W` of a tile on the other side of `XY`, or
* `V` lies on the boundary of the polygon, in the interior of its side `i`,

then an edge of `Γ_c` starts from `V`. -/
theorem propagation2 [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C)
    (hab : slen T.C 0 ≠ slen T.C 1) (hca : slen T.C 2 ≠ slen T.C 0) (hcb : slen T.C 2 ≠ slen T.C 1)
    (hnw : ∀ j ℓ m, ¬ Witnesses T.C.toRegionDissection (slen T.C 0) (slen T.C 1) (slen T.C 2) j ℓ m) :
    (∀ {d : V2} {HA V HB W W' : Plane} {iA iB iS : Fin N} {σ : ℝ},
      TriStep (T.C.tile iA) d HA V → TriStep (T.C.tile iB) d V HB → TriStep (T.C.tile iS) (neg2 d) W' W →
      0 < σ → σ < 1 → V = W + σ • (W' - W) →
      (dist HA V = slen T.C 2 ∧ dist V HB ≠ slen T.C 2) ∨ (dist HA V ≠ slen T.C 2 ∧ dist V HB = slen T.C 2) →
      ∃ Y, GammaC T.C.toRegionDissection (slen T.C 2) V Y) ∧
    (∀ (i : Fin M) {t : ℝ} {HA HB : Plane} {iA iB : Fin N}, 0 < t → t < 1 →
      TriStep (T.C.tile iA) (toV2 (T.P.e i)) HA ((1 - t) • T.P.v i + t • T.P.v (i + 1)) →
      TriStep (T.C.tile iB) (toV2 (T.P.e i)) ((1 - t) • T.P.v i + t • T.P.v (i + 1)) HB →
      (dist HA ((1 - t) • T.P.v i + t • T.P.v (i + 1)) = slen T.C 2 ∧
          dist ((1 - t) • T.P.v i + t • T.P.v (i + 1)) HB ≠ slen T.C 2) ∨
        (dist HA ((1 - t) • T.P.v i + t • T.P.v (i + 1)) ≠ slen T.C 2 ∧
          dist ((1 - t) • T.P.v i + t • T.P.v (i + 1)) HB = slen T.C 2) →
      ∃ Y, GammaC T.C.toRegionDissection (slen T.C 2) ((1 - t) • T.P.v i + t • T.P.v (i + 1)) Y) := by
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨idx, h⟩ := caseCW_of_regular T hreg hab hca hcb hnw
  refine ⟨fun hSA hSB hSS hσ0 hσ1 hHV hord => gc_trans_left_W T.C idx h hSA hSB hSS hσ0 hσ1 hHV hord, ?_⟩
  intro i t HA HB iA iB ht0 ht1 hSA hSB hord
  have hG := h.caseG
  haveI : HasFansC (relabelC T.C).toRegionDissection := (inferInstance : HasFansC T.C.toRegionDissection)
  rw [← relabelC_slen0 T.C] at hord
  obtain ⟨Y, hY⟩ := bdy_edge_W (relabelC T.C) T.P T.region_eq (relabelCIdx idx) hG.hidx hG.hidxA hG.hnc hG.hab
    hG.hac hG.hhp i ht0 ht1 hSA hSB (by tauto)
  exact ⟨Y, (gcEdge_iff T.C _ Y).mpr hY⟩

/-- The out-edges of `v` in a relation on a finite set of points, as a fiber of the edge set. -/
theorem card_fiber_fst {S : Finset Plane} (r : Plane → Plane → Prop) (v : ↥S) :
    ((Finset.univ.filter (fun e : ↥S × ↥S => r e.1.1 e.2.1)).filter (fun e => e.1 = v)).card =
      (S.filter (r v.1)).card := by
  classical
  refine Finset.card_bij (fun e _ => e.2.1) (fun e he => ?_) (fun e1 he1 e2 he2 h12 => ?_) (fun Y hY => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Finset.mem_filter.mpr ⟨e.2.2, he.2 ▸ he.1⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
    exact Prod.ext (he1.2.trans he2.2.symm) (Subtype.ext h12)
  · obtain ⟨hYS, hY⟩ := Finset.mem_filter.mp hY
    exact ⟨(v, ⟨Y, hYS⟩), by simp [hY], rfl⟩

/-- The in-edges of `v`, as a fiber of the edge set. -/
theorem card_fiber_snd {S : Finset Plane} (r : Plane → Plane → Prop) (v : ↥S) :
    ((Finset.univ.filter (fun e : ↥S × ↥S => r e.1.1 e.2.1)).filter (fun e => e.2 = v)).card =
      (S.filter (fun X => r X v.1)).card := by
  classical
  refine Finset.card_bij (fun e _ => e.1.1) (fun e he => ?_) (fun e1 he1 e2 he2 h12 => ?_) (fun X hX => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Finset.mem_filter.mpr ⟨e.1.2, he.2 ▸ he.1⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
    exact Prod.ext (Subtype.ext h12) (he1.2.trans he2.2.symm)
  · obtain ⟨hXS, hX⟩ := Finset.mem_filter.mp hX
    exact ⟨(⟨X, hXS⟩, v), by simp [hX], rfl⟩

/-- A triangle with all angles `π/3` has equal sides. -/
theorem equilateral_sides (T : Tri) (hP : ∀ k, T.angleAt k = Real.pi / 3) :
    ∀ j : Fin 3, dist (T.pts j) (T.pts (j + 1)) = dist (T.pts 0) (T.pts 1) := by
  have hs : Real.sin (Real.pi / 3) ≠ 0 := by rw [Real.sin_pi_div_three]; positivity
  have e : ∀ i j, T.oppLen j = T.oppLen i := fun i j => by
    have := T.lawSin i j
    rw [hP i, hP j] at this
    exact mul_left_cancel₀ hs this
  intro j
  fin_cases j
  · rfl
  · exact e 2 0
  · exact e 2 1

/-- **Lemma `lemma:noboundarylink`.** Let an equilateral triangle `ABC` be tiled by the tile with angles
`α, β, γ` opposite its sides `a, b, c`, with `γ = π/3` or `γ = 2π/3` and `α` not a rational multiple of
`π`. If the tiling witnesses no relation `j c = ℓ a + m b`, then at every vertex of the tiling the
in-degree of `Γ_c` equals its out-degree, and no edge of `Γ_c` starts on the boundary of `ABC`. -/
theorem noboundarylink (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hT : TileSides D α β γ a b c)
    (hγ : γ = Real.pi / 3 ∨ γ = 2 * Real.pi / 3) (hα : IrrPi α)
    (hnw : ∀ j ℓ m, ¬ Witnesses D.toDissection.toRegion a b c j ℓ m) :
    (∀ V : Plane, ((vtxSet D.toDissection.toRegion).filter fun Y => GammaC D.toDissection.toRegion c V Y).card =
        ((vtxSet D.toDissection.toRegion).filter fun X => GammaC D.toDissection.toRegion c X V).card) ∧
      ∀ X Y, X ∈ frontier D.target.carrier → ¬ GammaC D.toDissection.toRegion c X Y := by
  -- the tile is scalene
  have hsum : α + β + γ = Real.pi := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [← h0, ← h1, ← h2, e, D.model.angleAt_sum]
  obtain ⟨q, hq⟩ : ∃ q : ℚ, γ = q * Real.pi := by
    rcases hγ with rfl | rfl
    · exact ⟨1 / 3, by push_cast; ring⟩
    · exact ⟨2 / 3, by push_cast; ring⟩
  have hγα : γ ≠ α := fun e => hα ⟨q, by rw [← e, hq]⟩
  have hγβ : γ ≠ β := fun e => hα ⟨1 - 2 * q, by push_cast; linarith⟩
  have hαβ : α ≠ β := fun e => hα ⟨(1 - q) / 2, by push_cast; linarith⟩
  have hab : a ≠ b := sides_ne_of_angles_ne D hT hαβ
  have hcb : c ≠ b := by
    refine sides_ne_of_angles_ne D (α := γ) (β := β) (γ := α) (a := c) (b := b) (c := a) ?_ hγβ
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ * Equiv.swap 0 2, ?_⟩
    simp only [Equiv.Perm.mul_apply, swap02_0, swap02_1, swap02_2]
    exact ⟨h2, h1, h0, l2, l1, l0⟩
  have hca : c ≠ a := by
    refine sides_ne_of_angles_ne D (α := γ) (β := α) (γ := β) (a := c) (b := a) (c := b) ?_ hγα
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
  have hreg : RegularPQ T.C := by
    rcases hγ with hγ | hγ
    · exact regular_of_irr_pi3 T (by rw [hang 2, h2, hγ]) hαT hPang
    · exact regular_of_irr T (by rw [hang 2, h2, hγ]) hαT hPang
  have hnw' : ∀ j ℓ m, ¬ Witnesses T.C.toRegionDissection (slen T.C 0) (slen T.C 1) (slen T.C 2) j ℓ m := by
    rw [sa, sb, sc]; exact hnw
  obtain ⟨idx, h⟩ := caseCW_of_regular T hreg (by rwa [sa, sb]) (by rwa [sc, sa]) (by rwa [sc, sb]) hnw'
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hc0 : slen (relabelC T.C) 0 = c := by rw [relabelC_slen0, sc]
  refine ⟨fun V => ?_, fun X Y hX hE => ?_⟩
  · by_cases hV : V ∈ vtxSet (relabelC T.C).toRegionDissection
    · have hbal := gc_balance_W T.C T.P T.region_eq idx h ⟨V, hV⟩
      unfold GAset at hbal
      rw [card_fiber_fst, card_fiber_snd, hc0] at hbal
      exact hbal
    · have e1 : ((vtxSet D.toDissection.toRegion).filter fun Y => GammaC D.toDissection.toRegion c V Y) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun Y _ hE => hV (mem_vtxSet.mpr (ga_edge_endpoints _ _ hE).1)
      have e2 : ((vtxSet D.toDissection.toRegion).filter fun X => GammaC D.toDissection.toRegion c X V) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun X _ hE => hV (mem_vtxSet.mpr (ga_edge_endpoints _ _ hE).2)
      rw [e1, e2]
  · refine gc_no_boundary_W T.C idx h (X := X) (H := Y) (fun hi => hX.2 hi) ?_
    show GaEdge T.C.toRegionDissection (slen T.C 2) X Y
    rw [sc]; exact hE

end TriangleTiling.Equilateral
