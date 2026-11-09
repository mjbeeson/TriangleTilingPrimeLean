/-
Bonfioli's `Γ_c` lemmas with "no witnessed relation" in place of `NotComb`.

Bonfioli's `Γ_a`/`Γ_c` theory (Erdos634, `Draft/LaczFormalRG*`) assumes `NotComb a b c`: `a` is not a
nonnegative rational combination of `b` and `c`. That is false for an integer tile. It is used only
in `abc_contra`, `abc_contra'` and `arun_end`, to rule out a segment `XY` covered on both sides by tile
sides, all of length `a` on one side and not all on the other. Here that configuration is ruled out by the
hypothesis `NoWit` instead (the paper's "no relation is witnessed"). Every declaration that depends on
`NotComb` is copied verbatim from Bonfioli's files with the suffix `_W` and `NotComb` replaced by
`NoWit`; nothing else changes, except that `bdy_edge_W` is the first half of `bdy_step_status`
(the edge of `Γ_a` that its proof constructs). The structures `CaseG`, `CaseC` become `CaseGW`, `CaseCW`, which also
carry `a ≠ b`, `a ≠ c` (formerly derived from `NotComb`).
-/
import Erdos634.Draft.LaczFormalRGGa
import Erdos634.Draft.LaczFormalRGHead
import Erdos634.Draft.LaczFormalRGHeadFan
import Erdos634.Draft.LaczFormalRGHead2
import Erdos634.Draft.LaczFormalRGHalf
import Erdos634.Draft.LaczFormalRGBal
import Erdos634.Draft.LaczFormalRGIn
import Erdos634.Draft.LaczFormalRGBdy4
import Erdos634.Draft.LaczFormalRGBdy5
import Erdos634.Draft.LaczFormalRG5GammaC
import Erdos634.Draft.LaczFormalRG7Trans
import Erdos634.Draft.LaczFormalRG8Deg

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21
  Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **No witnessed relation for the side length `a`.** There is no segment `XY` covered on its left by
the sides of a chain of tiles (`WalkT`) and on its right by the sides of another chain (`WalkR`), both
from `X` to `Y`, such that all the sides on one side have length `a` and some side on the other side
does not. -/
def NoWit (D : RegionDissection N) (a : ℝ) : Prop :=
  ∀ (d : V2) (X Y : Plane) (P1 P2 : List (Fin N × Plane × Plane)), WalkT D d X Y P1 → WalkR D d X Y P2 →
    ¬ ((∀ e ∈ P1, dist e.2.1 e.2.2 = a) ∧ ∃ e ∈ P2, dist e.2.1 e.2.2 ≠ a) ∧
    ¬ ((∀ e ∈ P2, dist e.2.1 e.2.2 = a) ∧ ∃ e ∈ P1, dist e.2.1 e.2.2 ≠ a)

/-- `abc_contra` from `NoWit`. -/
theorem abc_contra_W (D : CongruentRegionDissection N) (_idx : Fin N → Equiv.Perm (Fin 3))
    (_hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (_idx i k)) (D.model.pts (_idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} {X Y : Plane}
    {P1 : List (Fin N × Plane × Plane)} {P2 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toRegionDissection d X Y P1) (W2 : WalkR D.toRegionDissection d X Y P2)
    (hall : ∀ e ∈ P1, dist e.2.1 e.2.2 = slen D 0) {e2 : Fin N × Plane × Plane} {P2' : List (Fin N × Plane × Plane)}
    (h2 : P2 = e2 :: P2') (hf2 : dist e2.2.1 e2.2.2 ≠ slen D 0) : False :=
  (hnc d X Y P1 P2 W1 W2).1 ⟨hall, e2, by rw [h2]; exact List.mem_cons_self .., hf2⟩

/-- `abc_contra'` from `NoWit`. -/
theorem abc_contra_W' (D : CongruentRegionDissection N) (_idx : Fin N → Equiv.Perm (Fin 3))
    (_hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (_idx i k)) (D.model.pts (_idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} {X Y : Plane}
    {P1 : List (Fin N × Plane × Plane)} {P2 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toRegionDissection d X Y P1) (W2 : WalkR D.toRegionDissection d X Y P2)
    (hall : ∀ e ∈ P2, dist e.2.1 e.2.2 = slen D 0) {e1 : Fin N × Plane × Plane} {P1' : List (Fin N × Plane × Plane)}
    (h1 : P1 = e1 :: P1') (hf1 : dist e1.2.1 e1.2.2 ≠ slen D 0) : False :=
  (hnc d X Y P1 P2 W1 W2).2 ⟨hall, e1, by rw [h1]; exact List.mem_cons_self .., hf1⟩

/-- `CaseG` with `NoWit` in place of `NotComb`. -/
structure CaseGW (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))
  hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v
  hnc : NoWit D.toRegionDissection (slen D 0)
  hhp : HalfPar D idx
  hab : slen D 0 ≠ slen D 1
  hac : slen D 0 ≠ slen D 2

/-- `CaseC` with `NoWit` (for `c`) in place of `NotComb`. -/
structure CaseCW (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) : Prop where
  hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))
  hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v
  hregc : ∀ X, cnt D idx X 0 = cnt D idx X 1
  hnc : NoWit D.toRegionDissection (slen D 2)
  hcb : slen D 2 ≠ slen D 1
  hca : slen D 2 ≠ slen D 0

theorem CaseCW.halfPar {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseCW D idx) :
    HalfPar (relabelC D) (relabelCIdx idx) := by
  intro X _
  have e1 := relabel_cnt D idx (Equiv.swap 0 2) X 1
  have e2 := relabel_cnt D idx (Equiv.swap 0 2) X 2
  rw [swap02_1] at e1; rw [swap02_2] at e2
  show (cnt (relabelC D) (relabelCIdx idx) X 1 + cnt (relabelC D) (relabelCIdx idx) X 2) % 2 = 0
  unfold relabelC relabelCIdx
  rw [e1, e2, ← h.hregc X]
  omega

theorem CaseCW.caseG {D : CongruentRegionDissection N} {idx : Fin N → Equiv.Perm (Fin 3)} (h : CaseCW D idx) :
    CaseGW (relabelC D) (relabelCIdx idx) := by
  refine ⟨relabel_hidx D idx _ h.hidx, relabel_hidxA D idx _ h.hidxA, ?_, h.halfPar, ?_, ?_⟩
  · rw [relabelC_slen0]; exact h.hnc
  all_goals unfold relabelC; rw [relabel_slen, relabel_slen, swap02_0]
  · rw [swap02_1]; exact h.hcb
  · rw [swap02_2]; exact h.hca

/-- **The `A`-run of a division ends** (existence of the index `i_0` of Laczkovich's definition of `Γ_a`): if the first left side has length `a`, the first right side
does not, and the two divisions have the same total length, some left side is not `a`. -/
theorem arun_end_W (D : CongruentRegionDissection N) (_idx : Fin N → Equiv.Perm (Fin 3))
    (_hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (_idx i k)) (D.model.pts (_idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} {X Y : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    {e1 e2 : Fin N × Plane × Plane} {L1' L2' : List (Fin N × Plane × Plane)} (h1 : L1 = e1 :: L1') (h2 : L2 = e2 :: L2')
    (hf2 : dist e2.2.1 e2.2.2 ≠ slen D 0) : ∃ e ∈ L1, dist e.2.1 e.2.2 ≠ slen D 0 := by
  by_contra hall
  push_neg at hall
  exact (hnc d X Y L1 L2 W1 W2).1 ⟨hall, e2, by rw [h2]; exact List.mem_cons_self .., hf2⟩

/-- **An edge of `Γ_a` starts at `X` from local data**: `X` is the start of a maximal segment along `d`, a left tile starts at `X` along `d` with first side `a`, and the
right tile starting at `X` has first side different from `a` (and `a` is not a nonnegative rational combination of `b, c`).  Then `Γ_a` has an edge out of `X`. -/
theorem ga_edge_of_local_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} (hd : d ≠ 0) {X : Plane}
    (hX : ∃ j k, (D.tile j).pts k = X) (hnb : NoBack D.toRegionDissection d X)
    {i1 : Fin N} {U1 : Plane} (hl : TriStep (D.tile i1) d X U1) (hla : dist X U1 = slen D 0)
    {i2 : Fin N} {U2 : Plane} (hr : TriStep (D.tile i2) (neg2 d) U2 X) (hra : dist U2 X ≠ slen D 0) :
    ∃ H, GaEdge D.toRegionDissection (slen D 0) X H := by
  obtain ⟨Y, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toRegionDissection hd hX ⟨i1, U1, hl⟩ ⟨i2, U2, hr⟩
  -- first elements
  obtain ⟨e1, L1', hL1e, hS1, he1X⟩ : ∃ e1 L1', L1 = e1 :: L1' ∧ TriStep (D.tile e1.1) d e1.2.1 e1.2.2 ∧ e1.2.1 = X := by
    cases W1 with
    | nil => exact absurd rfl hL1
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  obtain ⟨e2, L2', hL2e, hS2, he2X⟩ : ∃ e2 L2', L2 = e2 :: L2' ∧ TriStep (D.tile e2.1) (neg2 d) e2.2.2 e2.2.1 ∧ e2.2.1 = X := by
    cases W2 with
    | nil => exact absurd rfl hL2
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  rw [he1X] at hS1
  rw [he2X] at hS2
  obtain ⟨hi1, hU1⟩ := left_step_unique D.toRegionDissection hS1 hl
  obtain ⟨hi2, hU2⟩ := right_step_unique D.toRegionDissection hS2 hr
  have hd1 : dist e1.2.1 e1.2.2 = slen D 0 := by rw [he1X, hU1]; exact hla
  have hd2 : dist e2.2.1 e2.2.2 ≠ slen D 0 := by
    rw [he2X, hU2, dist_comm]; exact hra
  obtain ⟨e, he, hne⟩ := arun_end_W D idx hidx hnc W1 W2 hL1e hL2e hd2
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot⟩ := list_first_not (fun x : Fin N × Plane × Plane => dist x.2.1 x.2.2 = slen D 0) L1
    (by rw [hL1e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hd1)
    hL1 ⟨e, he, hne⟩
  refine ⟨e0.2.1, d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, Or.inl ⟨⟨L', e0, L'', hdec, hL'ne, hall, hnot, rfl⟩, ?_⟩⟩
  intro x hx
  rw [hL2e] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  rw [← hx]; exact hd2

/-- **An edge of `Γ_a` starts at `X` from local data (right version)**: the right first side has length `a` and the left first side does not. -/
theorem ga_edge_of_local_W' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} (hd : d ≠ 0) {X : Plane}
    (hX : ∃ j k, (D.tile j).pts k = X) (hnb : NoBack D.toRegionDissection d X)
    {i1 : Fin N} {U1 : Plane} (hl : TriStep (D.tile i1) d X U1) (hla : dist X U1 ≠ slen D 0)
    {i2 : Fin N} {U2 : Plane} (hr : TriStep (D.tile i2) (neg2 d) U2 X) (hra : dist U2 X = slen D 0) :
    ∃ H, GaEdge D.toRegionDissection (slen D 0) X H := by
  obtain ⟨Y, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toRegionDissection hd hX ⟨i1, U1, hl⟩ ⟨i2, U2, hr⟩
  obtain ⟨e1, L1', hL1e, hS1, he1X⟩ : ∃ e1 L1', L1 = e1 :: L1' ∧ TriStep (D.tile e1.1) d e1.2.1 e1.2.2 ∧ e1.2.1 = X := by
    cases W1 with
    | nil => exact absurd rfl hL1
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  obtain ⟨e2, L2', hL2e, hS2, he2X⟩ : ∃ e2 L2', L2 = e2 :: L2' ∧ TriStep (D.tile e2.1) (neg2 d) e2.2.2 e2.2.1 ∧ e2.2.1 = X := by
    cases W2 with
    | nil => exact absurd rfl hL2
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  rw [he1X] at hS1
  rw [he2X] at hS2
  obtain ⟨hi1, hU1⟩ := left_step_unique D.toRegionDissection hS1 hl
  obtain ⟨hi2, hU2⟩ := right_step_unique D.toRegionDissection hS2 hr
  have hd1 : dist e1.2.1 e1.2.2 ≠ slen D 0 := by rw [he1X, hU1]; exact hla
  have hd2 : dist e2.2.1 e2.2.2 = slen D 0 := by
    rw [he2X, hU2, dist_comm]; exact hra
  have hex : ∃ e ∈ L2, dist e.2.1 e.2.2 ≠ slen D 0 := by
    by_contra hall
    push_neg at hall
    exact abc_contra_W' D idx hidx hnc W1 W2 hall hL1e hd1
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot⟩ := list_first_not (fun x : Fin N × Plane × Plane => dist x.2.1 x.2.2 = slen D 0) L2
    (by rw [hL2e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hd2)
    hL2 hex
  refine ⟨e0.2.1, d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, Or.inr ⟨⟨L', e0, L'', hdec, hL'ne, hall, hnot, rfl⟩, ?_⟩⟩
  intro x hx
  rw [hL1e] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  rw [← hx]; exact hd1

/-- **An edge of `Γ_a` along a ray of the fan** between two adjacent corner sectors `x` (clockwise) and `y` (counterclockwise): if `NoBack` holds and exactly one of the two first
sides has length `a`, `Γ_a` has an edge out of `H`. -/
theorem ga_edge_of_ray_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hcx : 0 < crs (F.p x) (F.q x)) (hcy : 0 < crs (F.p y) (F.q y))
    (hxy : Par (F.p y) (F.q x)) (hnb : NoBack D.toRegionDissection (F.q x) H)
    (hxor : (nsq (F.q x) = slen D 0 ^ 2 ∧ nsq (F.p y) ≠ slen D 0 ^ 2) ∨
            (nsq (F.q x) ≠ slen D 0 ^ 2 ∧ nsq (F.p y) = slen D 0 ^ 2)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  have hd : F.q x ≠ 0 := (F.hok x).ne_q
  have hcornx : ∃ k, (D.tile x.1).pts k = H := by
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcx; unfold crs at hcx; try simp only at hcx; nlinarith
  have horny : ∃ k, (D.tile y.1).pts k = H := by
    rcases F.hspec y with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcy; unfold crs at hcy; try simp only at hcy; nlinarith
  obtain ⟨kx, flx, hkx, hpx, hqx⟩ := spec_corner_data (F.hspec x) hcornx
  obtain ⟨ky, fly, hky, hpy, hqy⟩ := spec_corner_data (F.hspec y) horny
  have hstepR := triStep_of_end (T := D.tile x.1) (d := F.q x) kx flx hkx hpx hqx hcx (par_refl hd)
  have hstepL := triStep_of_start (T := D.tile y.1) (d := F.q x) ky fly hky hpy hqy hcy hxy
  have hX : ∃ j k, (D.tile j).pts k = H := ⟨y.1, ky, hky⟩
  have hdL : dist H ((D.tile y.1).pts (armP ky fly)) ^ 2 = nsq (F.p y) := by
    rw [hpy, nsq_toV2_sub, dist_comm]
  have hdR : dist ((D.tile x.1).pts (armQ kx flx)) H ^ 2 = nsq (F.q x) := by
    rw [hqx, nsq_toV2_sub]
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the right first side is `a`: right version
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H = slen D 0 := by
      have := hdR.trans h1
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hla : dist H ((D.tile y.1).pts (armP ky fly)) ≠ slen D 0 := by
      intro h; apply h2; rw [← hdL, h]
    exact ga_edge_of_local_W' D idx hidx hnc hd hX hnb hstepL hla hstepR hra
  · have hla : dist H ((D.tile y.1).pts (armP ky fly)) = slen D 0 := by
      have := hdL.trans h2
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H ≠ slen D 0 := by
      intro h; apply h1; rw [← hdR, h]
    exact ga_edge_of_local_W D idx hidx hnc hd hX hnb hstepL hla hstepR hra

set_option maxHeartbeats 1600000 in
/-- **The half-fan lemma.**  Let `F` be the fan at `H` and let the sector at position `j0` be straight; the other `L - 1` sectors are tile corners in order
`c 1, .., c (L-1)`.  The arms of `c 1` (start) and of `c (L-1)` (end) on the boundary line: exactly one has length `a`.  If the number of corners having a vertex of type
`β` or `γ` at `H` is even, then an edge of `Γ_a` starts at `H`. -/
theorem half_fan_edge_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) (j0 : ℕ)
    (hstr : sq' F (F.e j0) = (-(sp F (F.e j0)).1, -(sp F (F.e j0)).2))
    (hL : 3 ≤ Fintype.card (AtV D.toRegionDissection H ⊕ κ))
    (hcorn : ∀ m, 1 ≤ m → m < Fintype.card (AtV D.toRegionDissection H ⊕ κ) →
      ∃ x : AtV D.toRegionDissection H, F.e (j0 + m) = Sum.inl x ∧ 0 < crs (F.p x) (F.q x))
    (hxor : ∀ b a : AtV D.toRegionDissection H, F.e (j0 + 1) = Sum.inl b →
      F.e (j0 + (Fintype.card (AtV D.toRegionDissection H ⊕ κ) - 1)) = Sum.inl a →
      ¬ (nsq (F.p b) = slen D 0 ^ 2 ↔ nsq (F.q a) = slen D 0 ^ 2))
    (hpar : (Finset.univ.filter (fun x : AtV D.toRegionDissection H =>
        (Sum.inl x : AtV D.toRegionDissection H ⊕ κ) ≠ F.e j0 ∧ ∃ k : Fin 3, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0)).card % 2 = 0) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  set L := Fintype.card (AtV D.toRegionDissection H ⊕ κ) with hLdef
  haveI hne : Nonempty (AtV D.toRegionDissection H) := ⟨(hcorn 1 le_rfl (by omega)).choose⟩
  let c : ℕ → AtV D.toRegionDissection H := fun m =>
    if h : 1 ≤ m ∧ m < L then (hcorn m h.1 h.2).choose else Classical.arbitrary _
  have hc_e : ∀ m, 1 ≤ m → m < L → F.e (j0 + m) = Sum.inl (c m) := by
    intro m h1 h2
    simp only [c, dif_pos (And.intro h1 h2)]
    exact (hcorn m h1 h2).choose_spec.1
  have hc_pos : ∀ m, 1 ≤ m → m < L → 0 < crs (F.p (c m)) (F.q (c m)) := by
    intro m h1 h2
    simp only [c, dif_pos (And.intro h1 h2)]
    exact (hcorn m h1 h2).choose_spec.2
  have hc_inj : ∀ m m', 1 ≤ m → m < L → 1 ≤ m' → m' < L → c m = c m' → m = m' := by
    intro m m' h1 h2 h1' h2' h
    apply e_inj_shift F j0 h2 h2'
    rw [hc_e m h1 h2, hc_e m' h1' h2', h]
  have hdis := tiles_disjoint D.toRegionDissection H F.p F.q F.hloc
  set u := sp F (F.e j0) with hu
  have hu0 : u ≠ 0 := (sectorOK F _).ne_p
  have hadj : ∀ m, 1 ≤ m → m + 1 < L → Par (F.p (c (m + 1))) (F.q (c m)) := by
    intro m h1 h2
    have := F.hP (j0 + m)
    rw [show j0 + m + 1 = j0 + (m + 1) by ring, hc_e (m + 1) (by omega) h2, hc_e m h1 (by omega)] at this
    simpa using this
  have hfirst : Par (F.p (c 1)) (-u.1, -u.2) := by
    have := F.hP j0
    rw [hc_e 1 le_rfl (by omega)] at this
    simp only [Sum.elim_inl] at this
    have h2 : Sum.elim F.q F.qe (F.e j0) = (-u.1, -u.2) := hstr
    rw [h2] at this
    exact this
  have hlast : Par u (F.q (c (L - 1))) := by
    have := F.hP (j0 + (L - 1))
    rw [show j0 + (L - 1) + 1 = j0 + L by omega, F.hper j0, hc_e (L - 1) (by omega) (by omega)] at this
    simpa using this
  have hclosed : ∀ m, 1 ≤ m → m < L → crs u (F.p (c m)) ≤ 0 ∧ crs u (F.q (c m)) ≤ 0 := by
    intro m h1 h2
    refine rays_closed F hstr ?_ (hc_pos m h1 h2)
    intro h
    have h' : F.e (j0 + m) = F.e (j0 + 0) := by rw [hc_e m h1 h2, h]; rfl
    have := e_inj_shift F j0 h2 (by omega : 0 < L) h'
    omega
  have hinner : ∀ m, 1 ≤ m → m + 1 < L → crs u (F.q (c m)) < 0 := by
    intro m h1 h2
    rcases (hclosed m h1 (by omega)).2.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hw0 : F.q (c m) ≠ 0 := (F.hok (c m)).ne_q
      rcases par_or_par_neg_of_crs_zero hu0 hw0 heq with hp | hp
      · have hP1 : Par (F.q (c (L - 1))) (F.q (c m)) := hlast.symm.trans hp.symm
        have hne1 : c m ≠ c (L - 1) := fun h => by
          have := hc_inj m (L - 1) h1 (by omega) (by omega) (by omega) h
          omega
        exact end_inj' F.p F.q F.hok hdis hne1 hP1
      · have hP2 : Par (F.p (c (m + 1))) (F.p (c 1)) := (hadj m h1 h2).trans (hp.trans hfirst.symm)
        have hne1 : c 1 ≠ c (m + 1) := fun h => by
          have := hc_inj 1 (m + 1) le_rfl (by omega) (by omega) h2 h
          omega
        exact start_inj F.p F.q F.hok hdis hne1 hP2
  have hnb : ∀ m, 1 ≤ m → m + 1 < L → NoBack D.toRegionDissection (F.q (c m)) H := by
    intro m h1 h2
    apply ExtFan.noBack_of_none F
    intro s'
    have hneg : ∀ r : V2, crs u r ≤ 0 → ¬ Par r (neg2 (F.q (c m))) := by
      intro r hr hpar'
      have := crs_pos_of_par_neg (hinner m h1 h2) hpar'
      linarith
    obtain ⟨m', hm', hem'⟩ := e_surj_shift F j0 (Sum.inl s')
    by_cases h0 : m' = 0
    · subst h0
      have hs : F.e j0 = Sum.inl s' := by simpa using hem'
      have hp : u = F.p s' := by simp [hu, hs, sp]
      have hq : F.q s' = (-u.1, -u.2) := by
        have h3 : Sum.elim F.q F.qe (F.e j0) = (-u.1, -u.2) := hstr
        rw [hs] at h3; simpa using h3
      constructor
      · apply hneg; rw [← hp]; unfold crs; ring_nf; exact le_rfl
      · apply hneg; rw [hq]; unfold crs; simp only; ring_nf; exact le_rfl
    · have h1' : 1 ≤ m' := by omega
      have hs' : s' = c m' := by
        have := hc_e m' h1' hm'
        rw [hem'] at this
        exact Sum.inl_injective this
      rw [hs']
      exact ⟨hneg _ (hclosed m' h1' hm').1, hneg _ (hclosed m' h1' hm').2⟩
  have hcd : ∀ m, 1 ≤ m → m < L → ∃ (kk : Fin 3) (fl : Bool), (D.tile (c m).1).pts kk = H ∧
      F.p (c m) = toV2 ((D.tile (c m).1).pts (armP kk fl) - H) ∧ F.q (c m) = toV2 ((D.tile (c m).1).pts (armQ kk fl) - H) :=
    fun m h1 h2 => spec_corner_data (F.hspec (c m)) (corner_vertex F (c m) (hc_pos m h1 h2))
  let P : ℕ → Bool := fun m => decide (nsq (F.p (c m)) = slen D 0 ^ 2)
  let Q : ℕ → Bool := fun m => decide (nsq (F.q (c m)) = slen D 0 ^ 2)
  let f : ℕ → Bool := fun m => decide (∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0)
  have htile : ∀ m, 1 ≤ m → m ≤ L - 1 → ((f m = false → P m = false ∧ Q m = false) ∧ (f m = true → P m ≠ Q m)) := by
    intro m h1 h2
    obtain ⟨kk, fl, hk, hp, hq⟩ := hcd m h1 (by omega)
    have hb := corner_bits D idx hidx hab hac fl hk hp hq
    have hf : (∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0) ↔ idx (c m).1 kk ≠ 0 := by
      constructor
      · rintro ⟨k, hk', hne'⟩
        have : k = kk := (D.tile (c m).1).indep.injective (hk'.trans hk.symm)
        rw [← this]; exact hne'
      · intro h; exact ⟨kk, hk, h⟩
    constructor
    · intro hfm
      have hfm' : ¬ (∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0) := by simpa [f] using hfm
      have h0 : idx (c m).1 kk = 0 := by
        by_contra hh; exact hfm' (hf.mpr hh)
      have := hb.1 h0
      simp [P, Q, this.1, this.2]
    · intro hfm
      have hfm' : ∃ k, (D.tile (c m).1).pts k = H ∧ idx (c m).1 k ≠ 0 := by simpa [f] using hfm
      have h0 := hf.mp hfm'
      have := hb.2 h0
      simp only [P, Q, ne_eq, decide_eq_decide]
      tauto
  have hline : P 1 ≠ Q (L - 1) := by
    have := hxor (c 1) (c (L - 1)) (hc_e 1 le_rfl (by omega)) (hc_e (L - 1) (by omega) (by omega))
    simp only [P, Q, ne_eq, decide_eq_decide]
    exact this
  have hsumeq : (∑ j ∈ Finset.Icc 1 (L - 1), (if f j = true then 1 else 0)) =
      (Finset.univ.filter (fun x : AtV D.toRegionDissection H =>
        (Sum.inl x : AtV D.toRegionDissection H ⊕ κ) ≠ F.e j0 ∧ ∃ k : Fin 3, (D.tile x.1).pts k = H ∧ idx x.1 k ≠ 0)).card := by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    refine Finset.card_nbij' c (fun x => (e_surj_shift F j0 (Sum.inl x)).choose) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq, decide_eq_true_eq] at hj
      obtain ⟨⟨hj1, hj2⟩, hjf⟩ := hj
      have hjL : j < L := by omega
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      have hjf' : ∃ k, (D.tile (c j).1).pts k = H ∧ idx (c j).1 k ≠ 0 := by simpa [f] using hjf
      refine ⟨?_, hjf'⟩
      rw [← hc_e j hj1 hjL]
      intro h
      have h' : F.e (j0 + j) = F.e (j0 + 0) := h
      have := e_inj_shift F j0 hjL (by omega : 0 < L) h'
      omega
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      obtain ⟨hxs, hxf⟩ := hx
      have hsp := (e_surj_shift F j0 (Sum.inl x)).choose_spec
      set m := (e_surj_shift F j0 (Sum.inl x)).choose with hm
      have hmL : m < L := hsp.1
      have hm0 : m ≠ 0 := by
        intro h0; apply hxs; rw [← hsp.2, h0]; rfl
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have : c m = x := by
        have := hc_e m (by omega) hmL
        rw [hsp.2] at this; exact (Sum.inl_injective this).symm
      simp only [f, decide_eq_true_eq]
      rw [this]; exact hxf
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hj
      have hjL : j < L := by omega
      have hsp := (e_surj_shift F j0 (Sum.inl (c j))).choose_spec
      apply e_inj_shift F j0 hsp.1 hjL
      rw [hsp.2, hc_e j hj.1.1 hjL]
    · intro x hx
      have hsp := (e_surj_shift F j0 (Sum.inl x)).choose_spec
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      obtain ⟨hxs, hxf⟩ := hx
      have hm0 : (e_surj_shift F j0 (Sum.inl x)).choose ≠ 0 := by
        intro h0; apply hxs; rw [← hsp.2, h0]; rfl
      have := hc_e _ (by omega) hsp.1
      rw [hsp.2] at this
      exact (Sum.inl_injective this).symm
  have hpar' : (∑ j ∈ Finset.Icc 1 (L - 1), (if f j = true then 1 else 0)) % 2 = 0 := by
    rw [hsumeq]; exact hpar
  obtain ⟨m, hm1, hm2, hmne⟩ := parity_core (L - 1) (by omega) P Q f htile hline hpar'
  have hcx := hc_pos m hm1 (by omega)
  have hcy := hc_pos (m + 1) (by omega) (by omega)
  refine ga_edge_of_ray_W D idx hidx hnc F (c m) (c (m + 1)) hcx hcy (hadj m hm1 (by omega)) (hnb m hm1 (by omega)) ?_
  simp only [P, Q, ne_eq, decide_eq_decide] at hmne
  by_cases h1 : nsq (F.q (c m)) = slen D 0 ^ 2
  · left
    refine ⟨h1, fun h2 => hmne ⟨fun _ => h2, fun _ => h1⟩⟩
  · right
    refine ⟨h1, ?_⟩
    by_contra h2
    exact hmne ⟨fun h => absurd h h1, fun h => absurd h h2⟩

/-- **Head wrapper of the half-fan lemma.**  At a head configuration (`HeadCfg`: corner tiles `u` (end along `-e`), `v` (start along `e`), straight tile `s`),
an edge of `Γ_a` starts at `H` as soon as the number of non-`α` corners at `H` (`cnt 1 + cnt 2`) is even. -/
theorem head_cfg_edge_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {e : V2}
    {u v s : AtV D.toRegionDissection H} (hc : HeadCfg D F e u v s)
    (hev : (cnt D idx H 1 + cnt D idx H 2) % 2 = 0) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
  obtain ⟨hemp, hint, hus, hvs, huv, j0, hj0, hes, hev1, heu⟩ := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
  have hκ : Fintype.card κ = 0 := Fintype.card_eq_zero_iff.mpr hemp
  have hLcard : Fintype.card (AtV D.toRegionDissection H ⊕ κ) = Fintype.card (AtV D.toRegionDissection H) := by
    rw [Fintype.card_sum, hκ]; simp
  have hL3 : 3 ≤ Fintype.card (AtV D.toRegionDissection H ⊕ κ) := by
    rw [hLcard]
    have hsub : ({u, v, s} : Finset (AtV D.toRegionDissection H)) ⊆ Finset.univ := Finset.subset_univ _
    have h3 : ({u, v, s} : Finset (AtV D.toRegionDissection H)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [huv, hus]), Finset.card_pair hvs]
    have := Finset.card_le_card hsub
    rw [h3] at this
    simpa using this
  refine half_fan_edge_W D idx hidx hnc hab hac F j0 ?_ hL3 ?_ ?_ ?_
  · rw [hes]; exact hc6
  · intro m hm1 hm2
    have : ∃ x : AtV D.toRegionDissection H, F.e (j0 + m) = Sum.inl x := by
      rcases hx : F.e (j0 + m) with x | j
      · exact ⟨x, rfl⟩
      · exact (hemp.false j).elim
    obtain ⟨x, hx⟩ := this
    refine ⟨x, hx, ?_⟩
    have hxs : x ≠ s := by
      intro h
      subst h
      have h' : F.e (j0 + m) = F.e (j0 + 0) := by rw [hx]; exact hes.symm
      have := e_inj_shift F j0 hm2 (by omega) h'
      omega
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exact absurd (straight_unique F hq hc6 hc1) hxs
  · intro b a hb ha
    have hb' : b = v := by rw [hev1] at hb; exact (Sum.inl_injective hb).symm
    have ha' : a = u := by rw [heu] at ha; exact (Sum.inl_injective ha).symm
    subst hb'; subst ha'
    rcases hc7 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro h; exact h2 (h.mpr h1)
    · intro h; exact h1 (h.mp h2)
  · rw [hes]
    have hx := head_tile_count D idx F hc6 hc1
    simp only [ne_eq, Sum.inl.injEq]
    rw [hx]; exact hev

/-- **Structure at the head (left case).** -/
theorem ga_head_left_W (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L1 H) (hR2 : ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ slen D 0) :
    ∃ (iA : Fin N) (HA : Plane) (iB : Fin N) (HB : Plane) (iS : Fin N) (V V' : Plane) (σ : ℝ),
      TriStep (D.tile iA) d HA H ∧ dist HA H = slen D 0 ∧ TriStep (D.tile iB) d H HB ∧ dist H HB ≠ slen D 0 ∧
      TriStep (D.tile iS) (neg2 d) V' V ∧ 0 < σ ∧ σ < 1 ∧ H = V + σ • (V' - V) ∧ H ≠ X := by
  classical
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot, hH⟩ := hRun
  obtain ⟨hpre, hsuf⟩ := walkT_split W1 hdec
  subst hH
  -- (A): the last step of the prefix
  obtain ⟨iA, HA, hmemA, hSA⟩ := walkT_last hpre hL'ne
  have hdA : dist HA e0.2.1 = slen D 0 := hall (iA, HA, e0.2.1) hmemA
  -- (B): the step `e0`
  have hmem0 : e0 ∈ L1 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hSB := walkT_mem_step W1 e0 hmem0
  -- parameters
  obtain ⟨tH, htH, htHe, htHp⟩ := walkT_progress hpre
  have htHpos := htHp hL'ne
  obtain ⟨T', hT', hT'e, hT'p⟩ := walkT_progress hsuf
  have hT'pos := hT'p (by simp)
  have hXY : toV2 (Y - X) = ((tH + T') * d.1, (tH + T') * d.2) := by
    have : toV2 (Y - X) = ((toV2 (Y - e0.2.1)).1 + (toV2 (e0.2.1 - X)).1, (toV2 (Y - e0.2.1)).2 + (toV2 (e0.2.1 - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hT'e, htHe]; ext <;> simp <;> ring
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkR_cover W2 hXY hd tH htH (by linarith)
  have hSe := walkR_mem_step W2 e he
  have hHX : e0.2.1 ≠ X := by
    intro h
    rw [h] at htHe
    have h1' : tH * d.1 = 0 := by have := congrArg Prod.fst htHe; simpa [toV2] using this.symm
    have h2' : tH * d.2 = 0 := by have := congrArg Prod.snd htHe; simpa [toV2] using this.symm
    exact hd (Prod.ext ((mul_eq_zero.mp h1').resolve_left htHpos.ne') ((mul_eq_zero.mp h2').resolve_left htHpos.ne'))
  -- `H` is not the tail of the right step `e`
  have hne0 : t0 ≠ tH := by
    intro hteq
    have hc0 := coords_of_toV2 h0
    have hcH := coords_of_toV2 htHe
    have heH : e.2.1 = e0.2.1 := by
      apply pt_ext
      · rw [hc0.1, hcH.1, hteq]
      · rw [hc0.2, hcH.2, hteq]
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem he
    obtain ⟨hpreR, -⟩ := walkR_split W2 hPQ
    rw [heH] at hpreR
    have hPne : P ≠ [] := by
      rintro rfl
      cases hpreR
      exact hHX rfl
    obtain ⟨p1, P', hP1⟩ := List.exists_cons_of_ne_nil hPne
    have hhead : dist p1.2.1 p1.2.2 ≠ slen D 0 := by
      apply hR2 p1
      rw [hPQ, hP1]; simp
    exact abc_contra_W D idx hidx hnc hpre hpreR hall hP1 hhead
  have hlt0 : t0 < tH := lt_of_le_of_ne h2 hne0
  have hlt01 : t0 < t1 := lt_trans hlt0 h3
  set σ : ℝ := (tH - t0) / (t1 - t0) with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (by linarith)
  have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
  have hσm : σ * (t1 - t0) = tH - t0 := by
    have hne : t1 - t0 ≠ 0 := by linarith
    rw [hσ]; exact div_mul_cancel₀ _ hne
  refine ⟨iA, HA, e0.1, e0.2.2, e.1, e.2.1, e.2.2, σ, hSA, hdA, hSB, hnot, hSe, hσ0, hσ1, ?_, hHX⟩
  have d0 := coords_of_toV2 h0
  have d1 := coords_of_toV2 h1
  have cH := coords_of_toV2 htHe
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.2, d0.2, d1.2]; linear_combination (-d.2) * hσm

/-- **Head sectors (left case)**: the sectors of the fan `F` at the head `H` of a left-case edge. -/
theorem ga_head_sectors_left_W (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L1 H) (hR2 : ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ slen D 0)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ a b s : AtV D.toRegionDissection H,
      0 < crs (F.p a) (F.q a) ∧ Par (F.q a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.p b) d ∧
      Par (F.p s) (neg2 d) ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
      nsq (F.q a) = slen D 0 ^ 2 ∧ nsq (F.p b) ≠ slen D 0 ^ 2 ∧ H ≠ X := by
  classical
  obtain ⟨iA, HA, iB, HB, iS, V, V', σ, hSA, hdA, hSB, hdB, hSS, hσ0, hσ1, hHV, hHX⟩ :=
    ga_head_left_W D idx hidx hnc hd W1 W2 hRun hR2
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS (σ := 1 - σ) (by linarith) (by linarith)
  have hHS : V' + (1 - σ) • (V - V') = H := by rw [hHV]; ext i; simp; ring
  rw [hHS] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  refine ⟨a, b, s, ?_⟩
  -- A
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨fA, hfA⟩
  have hqa : Par (F.q a) (neg2 d) := triStep_end hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = fA := (D.tile iA).indep.injective (hk'.trans hfA.symm)
  have hnA : nsq (F.q a) = slen D 0 ^ 2 := by
    have hq' : Par (toV2 ((D.tile iA).pts (armQ kk' fl') - H)) (neg2 d) := hq ▸ hqa
    have hHA : Par (toV2 (HA - H)) (neg2 d) := par_neg_arm hparA
    have := qarm_eq (T := D.tile iA) fl' hk' (W := HA) (w := kkA) hkA (by rw [hkkA]; exact hfkA.symm) hq' hHA
    rw [hq, nsq_toV2_sub, this, hdA]
  -- B
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨kkB, hkB⟩
  have hpb : Par (F.p b) d := triStep_start hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = kkB := (D.tile iB).indep.injective (hk2.trans hkB.symm)
  have hnB : nsq (F.p b) ≠ slen D 0 ^ 2 := by
    have hp' : Par (toV2 ((D.tile iB).pts (armP kk2 fl2) - H)) d := hp2 ▸ hpb
    have := parm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := fB) hfB (by rw [hkkB]; exact hfkB) hp' hparB
    rw [hp2, nsq_toV2_sub, this, dist_comm]
    exact sq_ne_of_ne dist_nonneg (slen_pos D 0).le hdB
  -- S
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  exact ⟨hca, hqa, hcb, hpb, hpS, hqS, hnA, hnB, hHX⟩

/-- **Structure at the head (right case)**: mirror of `ga_head_left_W`. -/
theorem ga_head_right_W (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L2 H) (hL1 : ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ slen D 0) :
    ∃ (iA : Fin N) (HA : Plane) (iB : Fin N) (HB : Plane) (iS : Fin N) (V V' : Plane) (σ : ℝ),
      TriStep (D.tile iA) (neg2 d) H HA ∧ dist HA H = slen D 0 ∧ TriStep (D.tile iB) (neg2 d) HB H ∧ dist H HB ≠ slen D 0 ∧
      TriStep (D.tile iS) d V V' ∧ 0 < σ ∧ σ < 1 ∧ H = V + σ • (V' - V) ∧ H ≠ X := by
  classical
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot, hH⟩ := hRun
  obtain ⟨hpre, hsuf⟩ := walkR_split W2 hdec
  subst hH
  obtain ⟨iA, HA, hmemA, hSA⟩ := walkR_last hpre hL'ne
  have hdA : dist HA e0.2.1 = slen D 0 := hall (iA, HA, e0.2.1) hmemA
  have hmem0 : e0 ∈ L2 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hSB := walkR_mem_step W2 e0 hmem0
  obtain ⟨tH, htH, htHe, htHp⟩ := walkR_progress hpre
  have htHpos := htHp hL'ne
  obtain ⟨T', hT', hT'e, hT'p⟩ := walkR_progress hsuf
  have hT'pos := hT'p (by simp)
  have hXY : toV2 (Y - X) = ((tH + T') * d.1, (tH + T') * d.2) := by
    have : toV2 (Y - X) = ((toV2 (Y - e0.2.1)).1 + (toV2 (e0.2.1 - X)).1, (toV2 (Y - e0.2.1)).2 + (toV2 (e0.2.1 - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hT'e, htHe]; ext <;> simp <;> ring
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkT_cover W1 hXY hd tH htH (by linarith)
  have hSe := walkT_mem_step W1 e he
  have hHX : e0.2.1 ≠ X := by
    intro h
    rw [h] at htHe
    have h1' : tH * d.1 = 0 := by have := congrArg Prod.fst htHe; simpa [toV2] using this.symm
    have h2' : tH * d.2 = 0 := by have := congrArg Prod.snd htHe; simpa [toV2] using this.symm
    exact hd (Prod.ext ((mul_eq_zero.mp h1').resolve_left htHpos.ne') ((mul_eq_zero.mp h2').resolve_left htHpos.ne'))
  have hne0 : t0 ≠ tH := by
    intro hteq
    have hc0 := coords_of_toV2 h0
    have hcH := coords_of_toV2 htHe
    have heH : e.2.1 = e0.2.1 := by
      apply pt_ext
      · rw [hc0.1, hcH.1, hteq]
      · rw [hc0.2, hcH.2, hteq]
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem he
    obtain ⟨hpreT, -⟩ := walkT_split W1 hPQ
    rw [heH] at hpreT
    have hPne : P ≠ [] := by
      rintro rfl
      cases hpreT
      exact hHX rfl
    obtain ⟨p1, P', hP1⟩ := List.exists_cons_of_ne_nil hPne
    have hhead : dist p1.2.1 p1.2.2 ≠ slen D 0 := by
      apply hL1 p1
      rw [hPQ, hP1]; simp
    exact abc_contra_W' D idx hidx hnc hpreT hpre hall hP1 hhead
  have hlt0 : t0 < tH := lt_of_le_of_ne h2 hne0
  have hlt01 : t0 < t1 := lt_trans hlt0 h3
  set σ : ℝ := (tH - t0) / (t1 - t0) with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (by linarith)
  have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
  have hσm : σ * (t1 - t0) = tH - t0 := by
    have hne : t1 - t0 ≠ 0 := by linarith
    rw [hσ]; exact div_mul_cancel₀ _ hne
  refine ⟨iA, HA, e0.1, e0.2.2, e.1, e.2.1, e.2.2, σ, hSA, hdA, hSB, hnot, hSe, hσ0, hσ1, ?_, hHX⟩
  have d0 := coords_of_toV2 h0
  have d1 := coords_of_toV2 h1
  have cH := coords_of_toV2 htHe
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.2, d0.2, d1.2]; linear_combination (-d.2) * hσm

/-- **Head sectors (right case)**. -/
theorem ga_head_sectors_right_W (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L2 H) (hL1 : ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ slen D 0)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ a b s : AtV D.toRegionDissection H,
      0 < crs (F.p a) (F.q a) ∧ Par (F.p a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.q b) d ∧
      Par (F.p s) d ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
      nsq (F.p a) = slen D 0 ^ 2 ∧ nsq (F.q b) ≠ slen D 0 ^ 2 ∧ H ≠ X := by
  classical
  obtain ⟨iA, HA, iB, HB, iS, V, V', σ, hSA, hdA, hSB, hdB, hSS, hσ0, hσ1, hHV, hHX⟩ :=
    ga_head_right_W D idx hidx hnc hd W1 W2 hRun hL1
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS hσ0 hσ1
  rw [← hHV] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  refine ⟨a, b, s, ?_⟩
  -- A: tail H of a step along -d; its p-arm points to HA
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨kkA, hkA⟩
  have hpa : Par (F.p a) (neg2 d) := triStep_start hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = kkA := (D.tile iA).indep.injective (hk'.trans hkA.symm)
  have hnA : nsq (F.p a) = slen D 0 ^ 2 := by
    have hp' : Par (toV2 ((D.tile iA).pts (armP kk' fl') - H)) (neg2 d) := hp ▸ hpa
    -- hparA : Par (toV2 (HA - H)) (neg2 d)
    have := parm_eq (T := D.tile iA) fl' hk' (W := HA) (w := fA) hfA (by rw [hkkA]; exact hfkA) hp' hparA
    rw [hp, nsq_toV2_sub, this, hdA]
  -- B: head H of a step along -d; its q-arm points to HB along d
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨fB, hfB⟩
  have hqb0 : Par (F.q b) (-(neg2 d).1, -(neg2 d).2) := triStep_end hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hqb : Par (F.q b) d := by rw [neg2_neg2] at hqb0; exact hqb0
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = fB := (D.tile iB).indep.injective (hk2.trans hfB.symm)
  have hnB : nsq (F.q b) ≠ slen D 0 ^ 2 := by
    have hq' : Par (toV2 ((D.tile iB).pts (armQ kk2 fl2) - H)) d := hq2 ▸ hqb
    have hHB : Par (toV2 (HB - H)) d := par_arm_neg hparB
    have := qarm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := kkB) hkB (by rw [hkkB]; exact Ne.symm hfkB) hq' hHB
    rw [hq2, nsq_toV2_sub, this, dist_comm]
    exact sq_ne_of_ne dist_nonneg (slen_pos D 0).le hdB
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  exact ⟨hca, hpa, hcb, hqb, hpS, hqS, hnA, hnB, hHX⟩

theorem ga_edge_data_W (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {X H : Plane} (h : GaEdge D.toRegionDissection (slen D 0) X H)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ d : V2, d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧
      ((∃ P, WalkT D.toRegionDissection d X H P ∧ P ≠ [] ∧ ∃ a b s, LeftF D F d a b s) ∨
       (∃ P, WalkR D.toRegionDissection d X H P ∧ P ≠ [] ∧ ∃ a b s, RightF D F d a b s)) := by
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -, -, hcase⟩ := h
  refine ⟨d, hd, hnb, ?_⟩
  rcases hcase with ⟨hRun, hR2⟩ | ⟨hRun, hL1'⟩
  · left
    have hRun0 := hRun
    obtain ⟨L', e, L'', hdec, hL'ne, -, -, hH⟩ := hRun
    obtain ⟨hpre, -⟩ := walkT_split W1 hdec
    refine ⟨L', hH ▸ hpre, hL'ne, ?_⟩
    obtain ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
      ga_head_sectors_left_W D idx hidx hnc hd W1 W2 hRun0 hR2 F
    exact ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · right
    have hRun0 := hRun
    obtain ⟨L', e, L'', hdec, hL'ne, -, -, hH⟩ := hRun
    obtain ⟨hpre, -⟩ := walkR_split W2 hdec
    refine ⟨L', hH ▸ hpre, hL'ne, ?_⟩
    obtain ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
      ga_head_sectors_right_W D idx hidx hnc hd W1 W2 hRun0 hL1' F
    exact ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **Lemma 9.1 (i), head part**, with the parity hypothesis. -/
theorem ga_head_out_half_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NoWit D.toRegionDissection (slen D 0)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx) {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data_W D idx hidx hnc hE F
  have key : ∀ {e : V2} {u v s : AtV D.toRegionDissection H}, HeadCfg D F e u v s → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
    intro e u v s hc
    have hc' := hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
    have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
    obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hidxA F hcyc.1 hc6 hc1
    exact head_cfg_edge_W D idx hidx hnc hab hac F hc (hhp H hsum)
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact key (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
  · exact key (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8)

theorem ga_indegree_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {X X' H : Plane}
    (h1 : GaEdge D.toRegionDissection (slen D 0) X H) (h2 : GaEdge D.toRegionDissection (slen D 0) X' H) : X = X' := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ h1)
  obtain ⟨d1, hd1, nb1, c1⟩ := ga_edge_data_W D idx hidx hnc h1 F
  obtain ⟨d2, hd2, nb2, c2⟩ := ga_edge_data_W D idx hidx hnc h2 F
  rcases c1 with ⟨P, W, hP, a, b, s, hf⟩ | ⟨P, W, hP, a, b, s, hf⟩ <;>
  rcases c2 with ⟨P', W', hP', a', b', s', hf'⟩ | ⟨P', W', hP', a', b', s', hf'⟩
  · -- left, left
    have hss : s = s' := straight_unique F hf.2.2.2.2.2.1 hf'.2.2.2.2.2.1 hf.1
    subst hss
    have hpar : Par d2 d1 := par_neg2 (hf'.2.2.2.2.1.symm.trans hf.2.2.2.2.1)
    exact xuniq_T hd1 hpar W hP W' hP' nb1 nb2
  · exact (left_right_contra D F hf hf').elim
  · exact (left_right_contra D F hf' hf).elim
  · -- right, right
    have hss : s = s' := straight_unique F hf.2.2.2.2.2.1 hf'.2.2.2.2.2.1 hf.1
    subst hss
    have hpar : Par d2 d1 := hf'.2.2.2.2.1.symm.trans hf.2.2.2.2.1
    exact xuniq_R hd1 hpar W hP W' hP' nb1 nb2

/-- **Lemma 9.1 (i)** (`γ = π/2`): in `Γ_a`, out-degree = in-degree at every vertex. -/
theorem lemma91_i_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NoWit D.toRegionDissection (slen D 0)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx) :
    ∀ v : ↥(vtxSet D.toRegionDissection), ((GAset D).filter fun e => e.1 = v).card = ((GAset D).filter fun e => e.2 = v).card := by
  classical
  apply digraph_balance
  · intro v
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hb1 : GaEdge D.toRegionDissection (slen D 0) b.1.1 a.2.1 := by rw [show a.2 = b.2 from ha.2.trans hb.2.symm]; exact hb.1
    have := ga_indegree_W D idx hidx hnc ha.1 hb1
    exact Prod.ext (Subtype.ext this) (ha.2.trans hb.2.symm)
  · intro v hv
    obtain ⟨e, he⟩ := Finset.card_pos.mp hv
    simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hE, hev⟩ := he
    have hvv : v.1 = e.2.1 := by rw [hev]
    have hout : ∃ H', GaEdge D.toRegionDissection (slen D 0) v.1 H' := by
      rw [hvv]
      exact ga_head_out_half_W D idx hidx hidxA hnc hab hac hhp hE
    obtain ⟨H', hH'⟩ := hout
    apply Finset.card_pos.mpr
    have hv' : H' ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (ga_edge_endpoints _ _ hH').2
    exact ⟨(v, ⟨H', hv'⟩), by simp [GAset, hH']⟩

/-- **Balance**: at every vertex the out-degree of `Γ_c` equals the in-degree. -/
theorem gc_balance_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx) :
    ∀ v : ↥(vtxSet (relabelC D).toRegionDissection),
      ((GAset (relabelC D)).filter fun e => e.1 = v).card = ((GAset (relabelC D)).filter fun e => e.2 = v).card := by
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  exact lemma91_i_W (relabelC D) (relabelCIdx idx) hG.hidx hG.hidxA hG.hnc hG.hab hG.hac hG.hhp

/-- The head of a `Γ_a` edge is an interior point of the region. -/
theorem ga_head_interior_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NoWit D.toRegionDissection (slen D 0)) {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H) :
    H ∈ interior D.region := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data_W D idx hidx hnc hE F
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact (F.head_cyc a b s h1 h2 h3 h4 h5 h6).2.1
  · obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8
    exact (F.head_cyc b a s c1 c2 c3 c4 c5 c6).2.1

/-- **Lemma 9.1 (ii)**: no edge of `Γ_a` starts at a point that is not an interior point of the region. -/
theorem lemma91_ii_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NoWit D.toRegionDissection (slen D 0)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx)
    {X H : Plane} (hX : X ∉ interior D.region) : ¬ GaEdge D.toRegionDissection (slen D 0) X H := by
  classical
  intro hE
  have hXv : X ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (ga_edge_endpoints _ _ hE).1
  have hHv : H ∈ vtxSet D.toRegionDissection := mem_vtxSet.mpr (ga_edge_endpoints _ _ hE).2
  have hbal := lemma91_i_W D idx hidx hidxA hnc hab hac hhp ⟨X, hXv⟩
  have hout : 0 < ((GAset D).filter fun e => e.1 = (⟨X, hXv⟩ : ↥(vtxSet D.toRegionDissection))).card :=
    Finset.card_pos.mpr ⟨(⟨X, hXv⟩, ⟨H, hHv⟩), by simp [GAset, hE]⟩
  rw [hbal] at hout
  obtain ⟨e, he⟩ := Finset.card_pos.mp hout
  simp only [GAset, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨hE', hev⟩ := he
  have hvv : e.2.1 = X := by rw [hev]
  apply hX
  rw [← hvv]
  exact ga_head_interior_W D idx hidx hnc hE'

/-- **No edge of `Γ_c` starts at a point that is not an interior point of the polygon.** -/
theorem gc_no_boundary_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx)
    {X H : Plane} (hX : X ∉ interior D.region) : ¬ GcEdge D X H := by
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [gcEdge_iff]
  exact lemma91_ii_W (relabelC D) (relabelCIdx idx) hG.hidx hG.hidxA hG.hnc hG.hab hG.hac hG.hhp hX

/-- A head configuration at `H` with an even number of non-`alpha` corners gives an edge (the `key` of `ga_head_out_half_W`, for `CaseGW`). -/
theorem headcfg_edge_half_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (hG : CaseGW D idx)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {e : V2} {u v s : AtV D.toRegionDissection H}
    (hc : HeadCfg D F e u v s) : ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  have hc' := hc
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
  have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
  obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hG.hidxA F hcyc.1 hc6 hc1
  exact head_cfg_edge_W D idx hG.hidx hG.hnc hG.hab hG.hac F hc (hG.hhp H hsum)

/-- **Transition lemma, both tiles to the left of the line.**  Tiles `iA` (side `HA -> H`) and `iB` (side `H -> HB`) lie to the left of the direction `d` and have the common vertex `H` on the line;
`H` is an inner point of a side `V' -> V` of the tile `iS` on the other side.  If exactly one of the two sides has length `a`, an edge of `Γ_a` starts at `H`. -/
theorem trans_left_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (hG : CaseGW D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) d HA H) (hSB : TriStep (D.tile iB) d H HB) (hSS : TriStep (D.tile iS) (neg2 d) V' V)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 0 ∧ dist H HB ≠ slen D 0) ∨ (dist HA H ≠ slen D 0 ∧ dist H HB = slen D 0)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = H := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    exact ⟨iB, kk, hk⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H hvert
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS (σ := 1 - σ) (by linarith) (by linarith)
  have hHS : V' + (1 - σ) • (V - V') = H := by rw [hHV]; ext i; simp; ring
  rw [hHS] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨fA, hfA⟩
  have hqa : Par (F.q a) (neg2 d) := triStep_end hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = fA := (D.tile iA).indep.injective (hk'.trans hfA.symm)
  have hnA : nsq (F.q a) = dist HA H ^ 2 := by
    have hq' : Par (toV2 ((D.tile iA).pts (armQ kk' fl') - H)) (neg2 d) := hq ▸ hqa
    have hHA : Par (toV2 (HA - H)) (neg2 d) := par_neg_arm hparA
    have := qarm_eq (T := D.tile iA) fl' hk' (W := HA) (w := kkA) hkA (by rw [hkkA]; exact hfkA.symm) hq' hHA
    rw [hq, nsq_toV2_sub, this]
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨kkB, hkB⟩
  have hpb : Par (F.p b) d := triStep_start hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = kkB := (D.tile iB).indep.injective (hk2.trans hkB.symm)
  have hnB : nsq (F.p b) = dist H HB ^ 2 := by
    have hp' : Par (toV2 ((D.tile iB).pts (armP kk2 fl2) - H)) d := hp2 ▸ hpb
    have := parm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := fB) hfB (by rw [hkkB]; exact hfkB) hp' hparB
    rw [hp2, nsq_toV2_sub, this, dist_comm]
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  have ha2 : 0 ≤ slen D 0 := (slen_pos D 0).le
  have hcfg : HeadCfg D F d a b s := by
    refine ⟨hca, hqa, hcb, hpb, hpS, hqS, ?_⟩
    rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨by rw [hnA, h1], by rw [hnB]; exact sq_ne_of_ne dist_nonneg ha2 h2⟩
    · right; exact ⟨by rw [hnA]; exact sq_ne_of_ne dist_nonneg ha2 h1, by rw [hnB, h2]⟩
  exact headcfg_edge_half_W D idx hG F hcfg

/-- **Transition lemma for `Γ_c`, tiles to the left** (Laczkovich Lemma 4.5, polygon version, in the form used in Lemma 4.6). -/
theorem gc_trans_left_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) d HA H) (hSB : TriStep (D.tile iB) d H HB) (hSS : TriStep (D.tile iS) (neg2 d) V' V)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 2 ∧ dist H HB ≠ slen D 2) ∨ (dist HA H ≠ slen D 2 ∧ dist H HB = slen D 2)) :
    ∃ H', GcEdge D H H' := by
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [← relabelC_slen0 D] at hord
  obtain ⟨H', hH'⟩ := trans_left_W (relabelC D) (relabelCIdx idx) h.caseG hSA hSB hSS hσ0 hσ1 hHV hord
  exact ⟨H', (gcEdge_iff D H H').mpr hH'⟩

/-- **Transition lemma, both tiles to the right of the line** (steps along `-d`: `iA : H -> HA`, `iB : HB -> H`; `iS` on the left, `V -> V'` along `d`). -/
theorem trans_right_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (hG : CaseGW D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) (neg2 d) H HA) (hSB : TriStep (D.tile iB) (neg2 d) HB H) (hSS : TriStep (D.tile iS) d V V')
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 0 ∧ dist H HB ≠ slen D 0) ∨ (dist HA H ≠ slen D 0 ∧ dist H HB = slen D 0)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  have hvert : ∃ j k, (D.tile j).pts k = H := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    exact ⟨iA, kk, hk⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H hvert
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS hσ0 hσ1
  rw [← hHV] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨kkA, hkA⟩
  have hpa : Par (F.p a) (neg2 d) := triStep_start hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = kkA := (D.tile iA).indep.injective (hk'.trans hkA.symm)
  have hnA : nsq (F.p a) = dist HA H ^ 2 := by
    have hp' : Par (toV2 ((D.tile iA).pts (armP kk' fl') - H)) (neg2 d) := hp ▸ hpa
    have := parm_eq (T := D.tile iA) fl' hk' (W := HA) (w := fA) hfA (by rw [hkkA]; exact hfkA) hp' hparA
    rw [hp, nsq_toV2_sub, this, dist_comm]
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨fB, hfB⟩
  have hqb0 : Par (F.q b) (-(neg2 d).1, -(neg2 d).2) := triStep_end hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hqb : Par (F.q b) d := by rw [neg2_neg2] at hqb0; exact hqb0
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = fB := (D.tile iB).indep.injective (hk2.trans hfB.symm)
  have hnB : nsq (F.q b) = dist H HB ^ 2 := by
    have hq' : Par (toV2 ((D.tile iB).pts (armQ kk2 fl2) - H)) d := hq2 ▸ hqb
    have hHB : Par (toV2 (HB - H)) d := par_arm_neg hparB
    have := qarm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := kkB) hkB (by rw [hkkB]; exact Ne.symm hfkB) hq' hHB
    rw [hq2, nsq_toV2_sub, this, dist_comm]
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  have ha2 : 0 ≤ slen D 0 := (slen_pos D 0).le
  have hcfg : HeadCfg D F (neg2 d) b a s := by
    refine ⟨hcb, ?_, hca, hpa, ?_, hqS, ?_⟩
    · rw [neg2_neg2']; exact hqb
    · rw [neg2_neg2']; exact hpS
    · rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; exact ⟨by rw [hnB]; exact sq_ne_of_ne dist_nonneg ha2 h2, by rw [hnA, h1]⟩
      · left; exact ⟨by rw [hnB, h2], by rw [hnA]; exact sq_ne_of_ne dist_nonneg ha2 h1⟩
  exact headcfg_edge_half_W D idx hG F hcfg

/-- **Transition lemma for `Γ_c`, tiles to the right.** -/
theorem gc_trans_right_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx)
    {d : V2} {HA H HB V V' : Plane} {iA iB iS : Fin N} {σ : ℝ}
    (hSA : TriStep (D.tile iA) (neg2 d) H HA) (hSB : TriStep (D.tile iB) (neg2 d) HB H) (hSS : TriStep (D.tile iS) d V V')
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hHV : H = V + σ • (V' - V))
    (hord : (dist HA H = slen D 2 ∧ dist H HB ≠ slen D 2) ∨ (dist HA H ≠ slen D 2 ∧ dist H HB = slen D 2)) :
    ∃ H', GcEdge D H H' := by
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [← relabelC_slen0 D] at hord
  obtain ⟨H', hH'⟩ := trans_right_W (relabelC D) (relabelCIdx idx) h.caseG hSA hSB hSS hσ0 hσ1 hHV hord
  exact ⟨H', (gcEdge_iff D H H').mpr hH'⟩

theorem gc_indegree_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseCW D idx)
    {X X' H : Plane} (h1 : GcEdge D X H) (h2 : GcEdge D X' H) : X = X' := by
  have hG := h.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  rw [gcEdge_iff] at h1 h2
  exact ga_indegree_W (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc h1 h2

set_option maxHeartbeats 1600000 in
/-- **Lemma 9.1 (iii), the step argument.**  Let `U` be a vertex of the tiling in the relative interior of the edge `i` of the polygon, `j1` the tile of the walk arriving at `U`
and `j2` the tile of the walk leaving it.  Then their sides on the edge are both of length `a` or both not: otherwise an edge of `Γ_a` would start at the boundary point `U`. -/
theorem bdy_step_status_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NoWit D.toRegionDissection (slen D 0)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx)
    (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {U1 U2 : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U1 ((1 - t) • P.v i + t • P.v (i + 1)))
    (h2 : TriStep (D.tile j2) (toV2 (P.e i)) ((1 - t) • P.v i + t • P.v (i + 1)) U2) :
    (dist U1 ((1 - t) • P.v i + t • P.v (i + 1)) = slen D 0 ↔ dist ((1 - t) • P.v i + t • P.v (i + 1)) U2 = slen D 0) := by
  classical
  set U : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hU
  set d := toV2 (P.e i) with hd
  by_contra hxor
  obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := id h2
  obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := id h1
  have hvert : ∃ j k, (D.tile j).pts k = U := ⟨j2, kk2, hk2⟩
  obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  have hdis := tiles_disjoint D.toRegionDissection U F.p F.q F.hloc
  -- the sectors of the two walk tiles
  have hmem2 : U ∈ (D.tile j2).carrier := hk2 ▸ subset_convexHull ℝ _ ⟨kk2, rfl⟩
  have hmem1 : U ∈ (D.tile j1).carrier := hf1 ▸ subset_convexHull ℝ _ ⟨f1, rfl⟩
  set x2 : AtV D.toRegionDissection U := ⟨j2, hmem2⟩ with hx2
  set x1 : AtV D.toRegionDissection U := ⟨j1, hmem1⟩ with hx1
  have hc2 : ∃ k, (D.tile x2.1).pts k = U := ⟨kk2, hk2⟩
  have hc1 : ∃ k, (D.tile x1.1).pts k = U := ⟨f1, hf1⟩
  obtain ⟨kk2', fl2, hk2', hp2, hq2⟩ := spec_corner_data (F.hspec x2) hc2
  obtain ⟨kk1', fl1, hk1', hp1, hq1⟩ := spec_corner_data (F.hspec x1) hc1
  have hcr2 := crs_pos_of_corner (F.hok x2) (F.hspec x2) hc2
  have hcr1 := crs_pos_of_corner (F.hok x1) (F.hspec x1) hc1
  have hkk2 : kk2' = kk2 := (D.tile j2).indep.injective (hk2'.trans hk2.symm)
  have hkk1 : kk1' = f1 := (D.tile j1).indep.injective (hk1'.trans hf1.symm)
  have hP2 : Par (F.p x2) d := triStep_start h2 kk2' fl2 hk2' hp2 hq2 (F.hok x2)
  have hQ1 : Par (F.q x1) (neg2 d) := triStep_end h1 kk1' fl1 hk1' hp1 hq1 (F.hok x1)
  -- lengths
  have hn2 : nsq (F.p x2) = dist U U2 ^ 2 := by
    have hq' : Par (toV2 ((D.tile j2).pts (armP kk2' fl2) - U)) d := hp2 ▸ hP2
    have := parm_eq (T := D.tile j2) fl2 hk2' (W := U2) (w := f2) hf2 (by rw [hkk2]; exact hfk2) hq' hpar2
    rw [hp2, nsq_toV2_sub, this, dist_comm]
  have hn1 : nsq (F.q x1) = dist U1 U ^ 2 := by
    have hq' : Par (toV2 ((D.tile j1).pts (armQ kk1' fl1) - U)) (neg2 d) := hq1 ▸ hQ1
    have hW : Par (toV2 (U1 - U)) (neg2 d) := par_neg_arm hpar1
    have := qarm_eq (T := D.tile j1) fl1 hk1' (W := U1) (w := kk1) hk1 (by rw [hkk1]; exact hfk1.symm) hq' hW
    rw [hq1, nsq_toV2_sub, this]
  -- x1 ≠ x2
  have hx12 : x1 ≠ x2 := by
    intro h
    rw [h] at hQ1
    obtain ⟨c1, hc1', hcp⟩ := hP2.smul
    obtain ⟨c2, hc2', hcq⟩ := hQ1.smul
    have : crs (F.p x2) (F.q x2) = 0 := by
      rw [hcp, hcq]; unfold crs neg2; simp only; ring
    linarith
  -- sector sum
  have hsumT : ∑ x : AtV D.toRegionDissection U, wd (F.p x) (F.q x) ≤ Real.pi := by
    have hv : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
      rw [Fintype.sum_unique]
      show wd (F.pe ()) (F.qe ()) = Real.pi
      rw [hpe, hqe, wd_ext hpT]
    have := F.hsum
    linarith
  -- no straight tile
  have hnostr : ∀ x : AtV D.toRegionDissection U, ∃ k, (D.tile x.1).pts k = U := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hne : x ≠ x2 := by
        intro h; subst h; exact hnv kk2 hk2
      exact no_straight_of_sum F.p F.q F.hok hne hw hsumT
  have hcrall : ∀ x : AtV D.toRegionDissection U, 0 < crs (F.p x) (F.q x) := fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  -- counts
  have hStrn : Strn D.toRegionDissection U = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
    rw [Fintype.sum_unique]
    show wd (F.pe ()) (F.qe ()) = Real.pi
    rw [hpe, hqe, wd_ext hpT]
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ∑ l, (cnt D idx U l : ℝ) * D.model.angleAt l = Real.pi := by
    rw [Fin.sum_univ_three]
    linarith
  have h3 := hhp U hsum'
  -- the half-fan lemma
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr ())
  have hLcard : Fintype.card (AtV D.toRegionDissection U ⊕ Unit) = Fintype.card (AtV D.toRegionDissection U) + 1 := by
    rw [Fintype.card_sum]; simp
  have hAt2 : 2 ≤ Fintype.card (AtV D.toRegionDissection U) := by
    have : ({x1, x2} : Finset (AtV D.toRegionDissection U)).card = 2 := Finset.card_pair hx12
    have h := Finset.card_le_card (Finset.subset_univ ({x1, x2} : Finset (AtV D.toRegionDissection U)))
    rw [this] at h
    simpa using h
  have hedge : ∃ H', GaEdge D.toRegionDissection (slen D 0) U H' := by
    refine half_fan_edge_W D idx hidx hnc hab hac F j0 ?_ (by omega) ?_ ?_ ?_
    · rw [hej0]
      show F.qe () = (-(F.pe ()).1, -(F.pe ()).2)
      rw [hpe, hqe]; simp
    · intro m hm1 hm2
      have : ∃ x : AtV D.toRegionDissection U, F.e (j0 + m) = Sum.inl x := by
        rcases hx : F.e (j0 + m) with x | u
        · exact ⟨x, rfl⟩
        · exfalso
          have h' : F.e (j0 + m) = F.e (j0 + 0) := by
            show F.e (j0 + m) = F.e j0
            rw [hx, hej0]
          have := e_inj_shift F j0 hm2 (by omega) h'
          omega
      obtain ⟨x, hx⟩ := this
      exact ⟨x, hx, hcrall x⟩
    · intro b a hb ha
      have hPb : Par (F.p b) pT := by
        have := F.hP j0
        rw [hej0, hb] at this
        simpa [hqe] using this
      have hb2 : b = x2 := by
        by_contra hne
        have hpp : Par (F.p x2) (F.p b) := hP2.trans (hpd.symm.trans hPb.symm)
        exact start_inj F.p F.q F.hok hdis hne hpp
      have hQa : Par (-pT.1, -pT.2) (F.q a) := by
        have := F.hP (j0 + (Fintype.card (AtV D.toRegionDissection U ⊕ Unit) - 1))
        rw [show j0 + (Fintype.card (AtV D.toRegionDissection U ⊕ Unit) - 1) + 1 = j0 + Fintype.card (AtV D.toRegionDissection U ⊕ Unit) by omega,
          F.hper j0, hej0, ha] at this
        simpa [hpe] using this
      have ha1 : a = x1 := by
        by_contra hne
        have hdn : Par (F.q x1) (-pT.1, -pT.2) := hQ1.trans (by
          have := par_neg hpd
          exact this.symm)
        have hqq : Par (F.q x1) (F.q a) := hdn.trans hQa
        exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) hqq.symm
      rw [hb2, ha1, hn2, hn1]
      intro hiff
      apply hxor
      have e1 : dist U1 U = slen D 0 ↔ dist U1 U ^ 2 = slen D 0 ^ 2 :=
        (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).symm
      have e2 : dist U U2 = slen D 0 ↔ dist U U2 ^ 2 = slen D 0 ^ 2 :=
        (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).symm
      rw [e1, e2]
      exact hiff.symm
    · have hc := corner_tile_count D idx U x2
      refine Eq.trans (congrArg (· % 2) ?_) h3
      rw [← hc]
      apply congrArg Finset.card
      ext x
      simp [hej0]
  obtain ⟨H', hH'⟩ := hedge
  have hci : P.c i U = 0 := by
    rw [hU, ConvPoly.c_comb, P.c_self, P.c_next]; simp
  exact lemma91_ii_W D idx hidx hidxA hnc hab hac hhp (by rw [hreg]; exact not_interior_of_c_zero P hci) hH'


set_option maxHeartbeats 1600000 in
/-- **An edge of `Γ_a` starts at a boundary vertex** (the edge `hedge` in the proof of `bdy_step_status`): `U` is a vertex of the
tiling in the relative interior of the edge `i` of the polygon, and of the sides on that edge of the tiles `j1` (arriving at `U`) and
`j2` (leaving it) exactly one has length `a`. -/
theorem bdy_edge_W (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NoWit D.toRegionDissection (slen D 0)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hhp : HalfPar D idx)
    (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {U1 U2 : Plane} {j1 j2 : Fin N}
    (h1 : TriStep (D.tile j1) (toV2 (P.e i)) U1 ((1 - t) • P.v i + t • P.v (i + 1)))
    (h2 : TriStep (D.tile j2) (toV2 (P.e i)) ((1 - t) • P.v i + t • P.v (i + 1)) U2)
    (hxor : ¬ (dist U1 ((1 - t) • P.v i + t • P.v (i + 1)) = slen D 0 ↔ dist ((1 - t) • P.v i + t • P.v (i + 1)) U2 = slen D 0)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) ((1 - t) • P.v i + t • P.v (i + 1)) H' := by
  classical
  set U : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hU
  set d := toV2 (P.e i) with hd
  obtain ⟨kk2, f2, g2, hk2, hf2, hfk2, hgk2, hgf2, hpar2, hleft2⟩ := id h2
  obtain ⟨kk1, f1, g1, hk1, hf1, hfk1, hgk1, hgf1, hpar1, hleft1⟩ := id h1
  have hvert : ∃ j k, (D.tile j).pts k = U := ⟨j2, kk2, hk2⟩
  obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
  have hpT : pT ≠ 0 := hpd.ne_left
  have hdis := tiles_disjoint D.toRegionDissection U F.p F.q F.hloc
  -- the sectors of the two walk tiles
  have hmem2 : U ∈ (D.tile j2).carrier := hk2 ▸ subset_convexHull ℝ _ ⟨kk2, rfl⟩
  have hmem1 : U ∈ (D.tile j1).carrier := hf1 ▸ subset_convexHull ℝ _ ⟨f1, rfl⟩
  set x2 : AtV D.toRegionDissection U := ⟨j2, hmem2⟩ with hx2
  set x1 : AtV D.toRegionDissection U := ⟨j1, hmem1⟩ with hx1
  have hc2 : ∃ k, (D.tile x2.1).pts k = U := ⟨kk2, hk2⟩
  have hc1 : ∃ k, (D.tile x1.1).pts k = U := ⟨f1, hf1⟩
  obtain ⟨kk2', fl2, hk2', hp2, hq2⟩ := spec_corner_data (F.hspec x2) hc2
  obtain ⟨kk1', fl1, hk1', hp1, hq1⟩ := spec_corner_data (F.hspec x1) hc1
  have hcr2 := crs_pos_of_corner (F.hok x2) (F.hspec x2) hc2
  have hcr1 := crs_pos_of_corner (F.hok x1) (F.hspec x1) hc1
  have hkk2 : kk2' = kk2 := (D.tile j2).indep.injective (hk2'.trans hk2.symm)
  have hkk1 : kk1' = f1 := (D.tile j1).indep.injective (hk1'.trans hf1.symm)
  have hP2 : Par (F.p x2) d := triStep_start h2 kk2' fl2 hk2' hp2 hq2 (F.hok x2)
  have hQ1 : Par (F.q x1) (neg2 d) := triStep_end h1 kk1' fl1 hk1' hp1 hq1 (F.hok x1)
  -- lengths
  have hn2 : nsq (F.p x2) = dist U U2 ^ 2 := by
    have hq' : Par (toV2 ((D.tile j2).pts (armP kk2' fl2) - U)) d := hp2 ▸ hP2
    have := parm_eq (T := D.tile j2) fl2 hk2' (W := U2) (w := f2) hf2 (by rw [hkk2]; exact hfk2) hq' hpar2
    rw [hp2, nsq_toV2_sub, this, dist_comm]
  have hn1 : nsq (F.q x1) = dist U1 U ^ 2 := by
    have hq' : Par (toV2 ((D.tile j1).pts (armQ kk1' fl1) - U)) (neg2 d) := hq1 ▸ hQ1
    have hW : Par (toV2 (U1 - U)) (neg2 d) := par_neg_arm hpar1
    have := qarm_eq (T := D.tile j1) fl1 hk1' (W := U1) (w := kk1) hk1 (by rw [hkk1]; exact hfk1.symm) hq' hW
    rw [hq1, nsq_toV2_sub, this]
  -- x1 ≠ x2
  have hx12 : x1 ≠ x2 := by
    intro h
    rw [h] at hQ1
    obtain ⟨c1, hc1', hcp⟩ := hP2.smul
    obtain ⟨c2, hc2', hcq⟩ := hQ1.smul
    have : crs (F.p x2) (F.q x2) = 0 := by
      rw [hcp, hcq]; unfold crs neg2; simp only; ring
    linarith
  -- sector sum
  have hsumT : ∑ x : AtV D.toRegionDissection U, wd (F.p x) (F.q x) ≤ Real.pi := by
    have hv : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
      rw [Fintype.sum_unique]
      show wd (F.pe ()) (F.qe ()) = Real.pi
      rw [hpe, hqe, wd_ext hpT]
    have := F.hsum
    linarith
  -- no straight tile
  have hnostr : ∀ x : AtV D.toRegionDissection U, ∃ k, (D.tile x.1).pts k = U := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hne : x ≠ x2 := by
        intro h; subst h; exact hnv kk2 hk2
      exact no_straight_of_sum F.p F.q F.hok hne hw hsumT
  have hcrall : ∀ x : AtV D.toRegionDissection U, 0 < crs (F.p x) (F.q x) := fun x => crs_pos_of_corner (F.hok x) (F.hspec x) (hnostr x)
  -- counts
  have hStrn : Strn D.toRegionDissection U = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
    rw [Fintype.sum_unique]
    show wd (F.pe ()) (F.qe ()) = Real.pi
    rw [hpe, hqe, wd_ext hpT]
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  rw [Fin.sum_univ_three] at hang
  have hsum' : ∑ l, (cnt D idx U l : ℝ) * D.model.angleAt l = Real.pi := by
    rw [Fin.sum_univ_three]
    linarith
  have h3 := hhp U hsum'
  -- the half-fan lemma
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr ())
  have hLcard : Fintype.card (AtV D.toRegionDissection U ⊕ Unit) = Fintype.card (AtV D.toRegionDissection U) + 1 := by
    rw [Fintype.card_sum]; simp
  have hAt2 : 2 ≤ Fintype.card (AtV D.toRegionDissection U) := by
    have : ({x1, x2} : Finset (AtV D.toRegionDissection U)).card = 2 := Finset.card_pair hx12
    have h := Finset.card_le_card (Finset.subset_univ ({x1, x2} : Finset (AtV D.toRegionDissection U)))
    rw [this] at h
    simpa using h
  have hedge : ∃ H', GaEdge D.toRegionDissection (slen D 0) U H' := by
    refine half_fan_edge_W D idx hidx hnc hab hac F j0 ?_ (by omega) ?_ ?_ ?_
    · rw [hej0]
      show F.qe () = (-(F.pe ()).1, -(F.pe ()).2)
      rw [hpe, hqe]; simp
    · intro m hm1 hm2
      have : ∃ x : AtV D.toRegionDissection U, F.e (j0 + m) = Sum.inl x := by
        rcases hx : F.e (j0 + m) with x | u
        · exact ⟨x, rfl⟩
        · exfalso
          have h' : F.e (j0 + m) = F.e (j0 + 0) := by
            show F.e (j0 + m) = F.e j0
            rw [hx, hej0]
          have := e_inj_shift F j0 hm2 (by omega) h'
          omega
      obtain ⟨x, hx⟩ := this
      exact ⟨x, hx, hcrall x⟩
    · intro b a hb ha
      have hPb : Par (F.p b) pT := by
        have := F.hP j0
        rw [hej0, hb] at this
        simpa [hqe] using this
      have hb2 : b = x2 := by
        by_contra hne
        have hpp : Par (F.p x2) (F.p b) := hP2.trans (hpd.symm.trans hPb.symm)
        exact start_inj F.p F.q F.hok hdis hne hpp
      have hQa : Par (-pT.1, -pT.2) (F.q a) := by
        have := F.hP (j0 + (Fintype.card (AtV D.toRegionDissection U ⊕ Unit) - 1))
        rw [show j0 + (Fintype.card (AtV D.toRegionDissection U ⊕ Unit) - 1) + 1 = j0 + Fintype.card (AtV D.toRegionDissection U ⊕ Unit) by omega,
          F.hper j0, hej0, ha] at this
        simpa [hpe] using this
      have ha1 : a = x1 := by
        by_contra hne
        have hdn : Par (F.q x1) (-pT.1, -pT.2) := hQ1.trans (by
          have := par_neg hpd
          exact this.symm)
        have hqq : Par (F.q x1) (F.q a) := hdn.trans hQa
        exact end_inj' F.p F.q F.hok hdis (Ne.symm hne) hqq.symm
      rw [hb2, ha1, hn2, hn1]
      intro hiff
      apply hxor
      have e1 : dist U1 U = slen D 0 ↔ dist U1 U ^ 2 = slen D 0 ^ 2 :=
        (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).symm
      have e2 : dist U U2 = slen D 0 ↔ dist U U2 ^ 2 = slen D 0 ^ 2 :=
        (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).symm
      rw [e1, e2]
      exact hiff.symm
    · have hc := corner_tile_count D idx U x2
      refine Eq.trans (congrArg (· % 2) ?_) h3
      rw [← hc]
      apply congrArg Finset.card
      ext x
      simp [hej0]
  exact hedge

end Erdos634.Draft.LaczFormal.RG
