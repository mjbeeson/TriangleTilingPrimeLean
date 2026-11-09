/-
The coloring equation for M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723), for a
tile with angles `(α, 2π/3 - α, π/3)`, `α ∉ ℚπ`: `M(a + b + c) = 3X`, where `X` is the side of `ABC`
and `M` is the sum of any proper coloring of the tiles by `±1` with the tile at `A` (with an edge
on `AB`) colored `+1`.

Statements checked by Beeson. The proof is the paper's: the coloring is by the parity of
the number of crossings along a path from the tile at `A` (`pathColour`), and it is independent of
the path because each crossing changes the parity `(-1)^(j+k)` of the edge directions `jπ/3 + kα`
(`tpar`). Every tile is reached since the adjacency graph is connected (Bonfioli's
`Dissection.adjConnected`).
-/
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.BeesonColoringLemma12
import Erdos634.Draft.BeesonColoringConn
import Erdos634.Draft.FluxBoundary
import TriangleTiling.RightTile.Helper3

namespace TriangleTiling.Equilateral

open Erdos634.Geometry

variable {N : ℕ} (D : CongruentDissection N)

/-- Tile `i` has a vertex at `A` and another vertex on `AB`. -/
def AtAOnAB (i : Fin N) : Prop :=
  ∃ l l' : Fin 3, l ≠ l' ∧ (D.tile i).pts l = D.target.pts 0 ∧
    (D.tile i).pts l' ∈ segment ℝ (D.target.pts 0) (D.target.pts 1)

theorem edge_of_AtAOnAB {i : Fin N} (hi : AtAOnAB D i) :
    ∃ e : Fin 3, (D.tile i).edge e ⊆ D.target.edge 0 := by
  obtain ⟨l, l', hll', hl, hl'⟩ := hi
  have hAB : D.target.edge 0 = segment ℝ (D.target.pts 0) (D.target.pts 1) := rfl
  have hA : D.target.pts 0 ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) :=
    left_mem_segment ℝ _ _
  have hcases : ∀ l l' : Fin 3, l ≠ l' → l' = l + 1 ∨ l = l' + 1 := by decide
  rcases hcases l l' hll' with e | e
  · refine ⟨l, ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hA hl'
  · refine ⟨l', ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hl' hA

/-- Some tile has a vertex at `A` and an edge on `AB`. -/
theorem exists_atA_onAB : ∃ i, AtAOnAB D i := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1) := hcov
  obtain ⟨e, he, hV⟩ := TriangleTiling.side_edge_at_end D hcov' (V := D.target.pts 0) (Or.inl rfl)
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    rw [← hcov']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  refine ⟨e.1, ?_⟩
  rcases hV with h' | h'
  · exact ⟨e.2, e.2 + 1, fin3_ne_add_one e.2, h', hsub (right_mem_segment ℝ _ _)⟩
  · exact ⟨e.2 + 1, e.2, (fin3_ne_add_one e.2).symm, h', hsub (left_mem_segment ℝ _ _)⟩

variable {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)

/-- Every tile is a placement of the `π/3` tile. -/
theorem tile_sixty (h : D.model.SixtyData α a b c) (i : Fin N) : (D.tile i).SixtyData α a b c := by
  obtain ⟨σ, h0, h0', h1, h1', h2, h2'⟩ := h
  obtain ⟨τ, hτ⟩ := (D.tiles_congruent i).exists_perm
  refine ⟨σ.trans τ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Equiv.trans_apply, (hτ _).1, (hτ _).2, Equiv.apply_symm_apply] <;> assumption

include hα in
/-- `w₂` is `1` on the exterior angles of the `π/3` tile. -/
theorem sixty_hext (T : Tri) (h : T.SixtyData α a b c) (anc : Real.Angle) (k : Fin 3) :
    (wAt α hα 1 anc).chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) = 1 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  obtain ⟨x, rfl⟩ := σ.surjective k
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) x with rfl | rfl | rfl
  · rw [h0, show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / 3) + ((-1 : ℤ) : ℝ) * α by push_cast; ring,
      wAt_chi, if_pos (by decide)]
  · rw [h1, show Real.pi - (2 * Real.pi / 3 - α) = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring, wAt_chi, if_pos (by decide)]
  · rw [h2, show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, wAt_chi, if_pos (by decide)]

/-! ### The path coloring

The paper colors a tile black or white according as the number of tile boundaries crossed in
reaching it from `A`, without passing through a vertex, is even or odd. Crossing a boundary away
from a vertex is a step between two tiles sharing a segment of positive length (`Dissection.Adj`),
so a path is a `Chain` of adjacent tiles, and its length is the number of boundaries crossed. -/

/-- A path of `n` crossings from tile `i₀` to tile `j`: a chain of tiles, each sharing a segment of
positive length with the next. -/
inductive Chain (D : Dissection N) (i₀ : Fin N) : Fin N → ℕ → Prop
  | nil : Chain D i₀ i₀ 0
  | cons {j k : Fin N} {n : ℕ} : Chain D i₀ j n → D.Adj j k → Chain D i₀ k (n + 1)

/-- The paper's coloring: `1` (black) if the tile is reached from `i₀` by an even number of
crossings, `-1` (white) otherwise. -/
noncomputable def pathColour (D : Dissection N) (i₀ j : Fin N) : ℤ :=
  haveI := Classical.propDecidable
  if ∃ n, Chain D i₀ j n ∧ Even n then 1 else -1

/-- Every tile can be reached from `i₀` (the adjacency graph is connected, Bonfioli's
`Dissection.adjConnected`: `ABC` minus finitely many points is connected). -/
theorem exists_chain (D : Dissection N) (i₀ j : Fin N) : ∃ n, Chain D i₀ j n := by
  induction D.adjConnected i₀ j with
  | refl => exact ⟨0, .nil⟩
  | tail _ hab ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .cons hn hab⟩

/-- **The converse.** A coloring giving different colors to tiles sharing a segment changes color
at each crossing: along a chain of `n` crossings from `i₀`, the color is multiplied by `(-1)^n`. -/
theorem colour_chain {D : Dissection N} {ε : Fin N → ℤ} (hε : D.ProperColouring ε) {i₀ j : Fin N}
    {n : ℕ} (hc : Chain D i₀ j n) : ε j = ε i₀ * (-1) ^ n := by
  induction hc with
  | nil => ring
  | cons _ hadj ih =>
    rw [pow_succ, ← mul_assoc, ← ih]
    have := hε.2 _ _ hadj
    omega

/-- The parity of a tile: `(-1)^(j+k)` for the direction `jπ/3 + kα` of its edge `0`
(`G = wAt α hα 1 0`; Bonfioli's `GridChar.weight`). -/
noncomputable def tpar (i : Fin N) : ℝ := (wAt α hα 1 0).weight ((D.tile i).leftUnit 0)

include hα in
theorem tpar_sq (i : Fin N) : tpar D hα i * tpar D hα i = 1 := (wAt α hα 1 0).val_sq (wAt_sq α hα 1 0) _

include hα in
/-- All three edges of a tile have the parity of the tile: the exterior angles `π - α`,
`π/3 + α`, `2π/3` have even parity (`sixty_hext`). -/
theorem tpar_edge (h : D.model.SixtyData α a b c) (i : Fin N) (k : Fin 3) :
    (wAt α hα 1 0).weight ((D.tile i).leftUnit k) = tpar D hα i :=
  (D.tile i).weight_const _ ((D.tile i).sixty_angles_mem hα (tile_sixty D h i) 1 0)
    (sixty_hext hα (D.tile i) (tile_sixty D h i) 0) k

include hα in
/-- **Each crossing changes the parity.** Two tiles sharing a segment traverse it in opposite
directions, which differ by `π = 3·π/3`, of odd parity. -/
theorem tpar_adj (h : D.model.SixtyData α a b c) {i j : Fin N} (hij : D.toDissection.Adj i j) :
    tpar D hα j = - tpar D hα i := by
  obtain ⟨k, l, hkl⟩ := hij.leftUnit_neg
  rw [← tpar_edge D hα h j l, ← tpar_edge D hα h i k, hkl, (wAt α hα 1 0).weight_odd]

include hα in
/-- Along a chain of `n` crossings the parity is multiplied by `(-1)^n`. -/
theorem tpar_chain (h : D.model.SixtyData α a b c) {i₀ j : Fin N} {n : ℕ}
    (hc : Chain D.toDissection i₀ j n) : tpar D hα j = (-1) ^ n * tpar D hα i₀ := by
  induction hc with
  | nil => ring
  | cons _ hadj ih => rw [tpar_adj D hα h hadj, ih]; ring

include hα in
/-- **The color does not depend on the path**: the number of crossings along any path from `i₀`
to `j` is even or odd according as `j` has the parity of `i₀` or not. -/
theorem pathColour_of_chain (h : D.model.SixtyData α a b c) {i₀ j : Fin N} {n : ℕ}
    (hc : Chain D.toDissection i₀ j n) : pathColour D.toDissection i₀ j = (-1) ^ n := by
  unfold pathColour
  split_ifs with hE
  · obtain ⟨m, hm, hev⟩ := hE
    have h0 : tpar D hα i₀ ≠ 0 := fun e => by simpa [e] using tpar_sq D hα i₀
    have hmn : ((-1 : ℝ)) ^ m = (-1) ^ n :=
      mul_right_cancel₀ h0 ((tpar_chain D hα h hm).symm.trans (tpar_chain D hα h hc))
    rcases Nat.even_or_odd n with hn | hn
    · exact hn.neg_one_pow.symm
    · rw [hev.neg_one_pow, hn.neg_one_pow] at hmn; norm_num at hmn
  · rcases Nat.even_or_odd n with hn | hn
    · exact absurd ⟨n, hc, hn⟩ hE
    · exact hn.neg_one_pow.symm

include hα in
/-- The coloring so defined gives different colors to tiles sharing a segment, and the tile `i₀`
is black. -/
theorem pathColour_proper (h : D.model.SixtyData α a b c) (i₀ : Fin N) :
    D.toDissection.ProperColouring (pathColour D.toDissection i₀) ∧
      pathColour D.toDissection i₀ i₀ = 1 := by
  refine ⟨⟨fun j => ?_, fun i j hij => ?_⟩, by rw [pathColour_of_chain D hα h .nil]; rfl⟩
  · unfold pathColour; split_ifs <;> simp
  · obtain ⟨n, hn⟩ := exists_chain D.toDissection i₀ i
    rw [pathColour_of_chain D hα h hn, pathColour_of_chain D hα h (.cons hn hij), pow_succ]
    ring

/-- **Uniqueness.** A proper coloring is determined by the color of one tile. -/
theorem colouring_eq {D : Dissection N} {ε ε' : Fin N → ℤ} (hε : D.ProperColouring ε)
    (hε' : D.ProperColouring ε') {i : Fin N} (hi : ε i = ε' i) : ε = ε' := by
  funext j
  obtain ⟨n, hn⟩ := exists_chain D i j
  rw [colour_chain hε hn, colour_chain hε' hn, hi]

include hα in
/-- **The coloring equation.** For an equilateral `ABC` tiled by the `π/3` tile, `α ∉ ℚπ`, and any
proper coloring with the tile at `A` (on `AB`) black: `M(a + b + c) = 3X`.

As in the paper: such a coloring is the path coloring, so the color of a tile is its parity times
the parity of the tile at `A`. The black edge length minus the white edge length is
`M(a + b + c)`; in Lean this signed length is Laczkovich's sum `flux` of the edge parities over
directed edges, and interior edges cancel (`flux_cancel`) because the two sides of an interior
segment have opposite parities, that is, different colors. On the boundary, every side has the
parity of the tile at `A` (directions `0`, `2π/3`, `4π/3`), so the boundary gives `3X`. -/
theorem coloring_equation (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) = 3 * D.target.oppLen 0 := by
  set G := wAt α hα 1 0
  have hsq := wAt_sq α hα 1 0
  -- `ε` is the path coloring: `ε j = tpar j * tpar i₀`
  have hεj : ∀ j, (ε j : ℝ) = tpar D hα j * tpar D hα i₀ := by
    intro j
    obtain ⟨n, hn⟩ := exists_chain D.toDissection i₀ j
    have e1 : (ε j : ℝ) = (-1) ^ n := by
      have := colour_chain hε hn
      rw [h1, one_mul] at this
      exact_mod_cast this
    rw [e1, tpar_chain D hα h hn, mul_assoc, tpar_sq, mul_one]
  -- each tile: signed edge length `tpar i * (a + b + c)`
  have hflux : ∀ i, (D.tile i).flux G.weight = tpar D hα i * (a + b + c) := by
    intro i
    have hTi := tile_sixty D h i
    rw [(D.tile i).flux_eq_edgeSign G hsq ((D.tile i).sixty_angles_mem hα hTi 1 0) 0]
    unfold GridChar.edgeSign
    rw [sixty_hext hα (D.tile i) hTi 0, one_mul, sixty_tileValue_two (D.tile i) hα hTi]
    rfl
  -- the boundary of `ABC`: `w · 3X`, `w` the parity of direction `AB`
  have e3 : Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α := by push_cast; ring
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro k; rw [hP k, e3]; exact wAt_mem _ _ _ _ _ _
  have hchi2 : G.chi ((Real.pi - Real.pi / 3 : ℝ) : Real.Angle) = 1 := by
    rw [show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, wAt_chi, if_pos (by decide)]
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα 1
    (fun k => D.model.sixty_angles_mem hα h 1 _ k) hP
  set w := G.weight (D.target.leftUnit 0)
  have hT : D.target.flux G.weight = w * (3 * D.target.oppLen 0) := by
    rw [Tri.flux_eq_edgeSign G hsq D.target htarget 0]
    unfold GridChar.edgeSign GridChar.tileValue
    rw [Fin.sum_univ_three, hP, hP, hP, hP, hchi2, e1, e2]
    ring
  -- the tile at `A` has its edge on `AB`, of the direction of `AB`
  obtain ⟨e, he⟩ := edge_of_AtAOnAB D hi₀
  have hdir : (D.tile i₀).leftUnit e = D.target.leftUnit 0 :=
    D.toDissection.eDir_of_side (e := (i₀, e)) he
  have hw : w = tpar D hα i₀ := by rw [← tpar_edge D hα h i₀ e, hdir]
  have hsum : ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) = tpar D hα i₀ * ∑ i, (D.tile i).flux G.weight := by
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hflux j, hεj j]; ring
  rw [hsum, D.flux_cancel G.weight G.weight_odd, hT, hw]
  linear_combination (3 * D.target.oppLen 0) * tpar_sq D hα i₀

end TriangleTiling.Equilateral
