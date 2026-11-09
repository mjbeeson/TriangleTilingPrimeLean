/-
The last step of the proof of `theorem:notprime120` of M. Beeson, *Tiling an equilateral triangle*
(arXiv 1811.09723): a side of `ABC` cannot consist of `a` edges only, when `γ = 2π/3`.

Each tile with its `a` edge on the side has its `β` and `γ` at the ends of that edge. There is no
`γ` at a corner of `ABC` (`2π/3 > π/3`), and at most one `γ` at any point inside the side
(`2 · 2π/3 > π`). So the first tile has its `γ` at its head, hence the second tile has its `β` at
its tail and its `γ` at its head, and so on: the last tile has its `γ` at the next corner.
-/
import TriangleTiling.Laczkovich.W.WalkDistinct
import Erdos634.Draft.LaczFormalRG4IVa
import Erdos634.Draft.LaczFormalBZ1
import Erdos634.Draft.LaczFormalFluxPolyBdy

open scoped Classical

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.RG
  Erdos634.Draft.LaczFormal.Thm21
open Erdos634.Draft.LaczFormal.Graph (V2 neg2 toV2 TriStep crs dt Par)

namespace Gamma120

variable {N : ℕ}

/-- A step of length `a` has the types `β, γ` (in some order) at its ends. -/
theorem types_of_a (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') =
      dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
    (h01 : slen C 0 ≠ slen C 1) (h02 : slen C 0 ≠ slen C 2)
    {j : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (C.tile j) d U U') (hl : dist U U' = slen C 0) :
    ∃ kk f : Fin 3, (C.tile j).pts kk = U ∧ (C.tile j).pts f = U' ∧
      ((idx j kk = 1 ∧ idx j f = 2) ∨ (idx j kk = 2 ∧ idx j f = 1)) := by
  obtain ⟨kk, f, -, hk, hf, hfk, -⟩ := hS
  refine ⟨kk, f, hk, hf, ?_⟩
  have hd : dist (C.model.pts (idx j kk)) (C.model.pts (idx j f)) = slen C 0 := by
    rw [← hidx, hk, hf, hl]
  have hne : idx j kk ≠ idx j f := fun e => hfk ((idx j).injective e).symm
  have s1 : slen C 1 = dist (C.model.pts 2) (C.model.pts 0) := rfl
  have s2 : slen C 2 = dist (C.model.pts 0) (C.model.pts 1) := rfl
  generalize idx j kk = x at hd hne ⊢
  generalize idx j f = y at hd hne ⊢
  fin_cases x <;> fin_cases y
  · exact absurd rfl hne
  · exact absurd (hd.symm.trans s2.symm) h02
  · exact absurd (hd.symm.trans (by rw [s1, dist_comm]; rfl)) h01
  · exact absurd (hd.symm.trans (by rw [s2, dist_comm]; rfl)) h02
  · exact absurd rfl hne
  · left; exact ⟨rfl, rfl⟩
  · exact absurd (hd.symm.trans s1.symm) h01
  · right; exact ⟨rfl, rfl⟩
  · exact absurd rfl hne

theorem asum_ge (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X : Plane) (l : Fin 3) :
    (cnt C idx X l : ℝ) * C.model.angleAt l ≤ Asum C idx X := by
  unfold Asum
  exact Finset.single_le_sum (f := fun l => (cnt C idx X l : ℝ) * C.model.angleAt l)
    (fun l _ => mul_nonneg (Nat.cast_nonneg _) (model_angle_pos' C l).le) (Finset.mem_univ l)

theorem cnt_ge_one (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {j : Fin N}
    {k : Fin 3} {X : Plane} (hk : (C.tile j).pts k = X) : 1 ≤ cnt C idx X (idx j k) := by
  unfold cnt
  exact Finset.card_pos.mpr ⟨(j, k), by simp [hk]⟩

theorem cnt_ge_two (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {j1 j2 : Fin N}
    {k1 k2 : Fin 3} {X : Plane} {l : Fin 3} (hj : j1 ≠ j2) (hk1 : (C.tile j1).pts k1 = X)
    (hk2 : (C.tile j2).pts k2 = X) (h1 : idx j1 k1 = l) (h2 : idx j2 k2 = l) : 2 ≤ cnt C idx X l := by
  unfold cnt
  have hsub : ({(j1, k1), (j2, k2)} : Finset (Fin N × Fin 3)) ⊆
      Finset.univ.filter (fun p : Fin N × Fin 3 => (C.tile p.1).pts p.2 = X ∧ idx p.1 p.2 = l) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [hk1, hk2, h1, h2]
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair (fun e => hj (congrArg Prod.fst e))] at this

/-- **Forward propagation along a walk**, for steps of a given set (Bonfioli's `walk_prop_forward`
with membership). -/
theorem walk_prop_forward_mem {M : ℕ} [NeZero M] (D : RegionDissection N) (P : ConvPoly M)
    (hreg : D.region = P.carrier) (i : Fin M) (S : Fin N × Plane × Plane → Prop)
    (R : Fin N × Plane × Plane → Prop)
    (hstep : ∀ (e e2 : Fin N × Plane × Plane) (t : ℝ), S e → S e2 → 0 < t → t < 1 →
      e.2.2 = (1 - t) • P.v i + t • P.v (i + 1) → e2.2.1 = e.2.2 →
      TriStep (D.tile e.1) (toV2 (P.e i)) e.2.1 e.2.2 → TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 →
      R e → R e2)
    {U Y : Plane} (hY : Y = P.v (i + 1)) {L : List (Fin N × Plane × Plane)} (W : WalkT D (toV2 (P.e i)) U Y L)
    (hSL : ∀ e ∈ L, S e)
    (hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (U - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2)) :
    ∀ e0 L0, L = e0 :: L0 → R e0 → ∀ e ∈ L, R e := by
  induction W with
  | nil X => intro e0 L0 h; simp at h
  | @cons j X X' Y L' hS W' ih =>
    intro e0 L0 he0 hR e he
    simp only [List.cons.injEq] at he0
    obtain ⟨rfl, rfl⟩ := he0
    rcases List.mem_cons.mp he with h | h
    · subst h; exact hR
    · cases hL' : L' with
      | nil => rw [hL'] at h; simp at h
      | cons e2 L2 =>
        rw [hL'] at h W' ih hSL
        obtain ⟨t, ht0, ht1, hXt, hs'⟩ := junction_param D P hreg i hY hS W' (by simp) hU
        have hX2 : e2.2.1 = X' := by cases W' with | cons _ _ => rfl
        have hS2 : TriStep (D.tile e2.1) (toV2 (P.e i)) e2.2.1 e2.2.2 := by
          cases W' with | cons hS2 _ => exact hS2
        have hR2 := hstep (j, X, X') e2 t (hSL _ List.mem_cons_self)
          (hSL _ (List.mem_cons_of_mem _ List.mem_cons_self)) ht0 ht1 hXt hX2 hS hS2 hR
        exact ih hY (fun e he => hSL e (List.mem_cons_of_mem _ he)) hs' e2 L2 rfl hR2 e h

variable (C : CongruentRegionDissection N) [HasFansC C.toRegionDissection] (P : ConvPoly 3)
  (hreg : C.region = P.carrier) (idx : Fin N → Equiv.Perm (Fin 3))
  (hidx : ∀ i k k', dist ((C.tile i).pts k) ((C.tile i).pts k') =
    dist (C.model.pts (idx i k)) (C.model.pts (idx i k')))
  (hidxA : ∀ i v, C.model.angleAt (idx i v) = (C.tile i).angleAt v)
  (hγ : C.model.angleAt 2 = 2 * Real.pi / 3) (hPang : ∀ k, P.angle k = Real.pi / 3)

include hreg hidxA hγ hPang in
/-- No `γ` at a corner of the polygon. -/
theorem no_gamma_corner {j : Fin N} {kk : Fin 3} {k' : Fin 3} (hk : (C.tile j).pts kk = P.v k') :
    idx j kk ≠ 2 := by
  intro h2
  have hvert : ∃ j' k'', (C.tile j').pts k'' = P.v (k' - 1 + 1) := ⟨j, kk, by rw [sub_add_cancel]; exact hk⟩
  have hA := corner_A C P hreg idx hidxA (k' - 1) hvert
  rw [sub_add_cancel, hPang] at hA
  have h1 := cnt_ge_one C idx hk
  rw [h2] at h1
  have hle := asum_ge C idx (P.v k') 2
  rw [hγ] at hle
  have : (1 : ℝ) ≤ cnt C idx (P.v k') 2 := by exact_mod_cast h1
  nlinarith [Real.pi_pos]

include hreg hidxA hγ hPang in
/-- At most one `γ` at a point inside a side of the polygon. -/
theorem no_two_gamma (i : Fin 3) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {j1 j2 : Fin N} {k1 k2 : Fin 3}
    (hj : j1 ≠ j2) (hk1 : (C.tile j1).pts k1 = (1 - t) • P.v i + t • P.v (i + 1))
    (hk2 : (C.tile j2).pts k2 = (1 - t) • P.v i + t • P.v (i + 1)) (h1 : idx j1 k1 = 2)
    (h2 : idx j2 k2 = 2) : False := by
  set V := (1 - t) • P.v i + t • P.v (i + 1) with hV
  have hc := cnt_ge_two C idx hj hk1 hk2 h1 h2
  have hle := asum_ge C idx V 2
  rw [hγ] at hle
  have hc' : (2 : ℝ) ≤ cnt C idx V 2 := by exact_mod_cast hc
  have hint : V ∉ interior C.region := by
    rw [hreg]
    apply ConvPoly.not_interior_of_sideSet P (j := i)
    exact ⟨1 - t, t, by linarith, ht0.le, by ring, rfl⟩
  rcases vertex_A C P hreg idx hidxA ⟨j1, k1, hk1⟩ with ⟨h, -⟩ | ⟨-, h | ⟨k, -, h⟩⟩
  · exact hint h
  · nlinarith [Real.pi_pos]
  · rw [hPang] at h; nlinarith [Real.pi_pos]

omit [HasFansC C.toRegionDissection] in
/-- Two consecutive steps along a line are of different tiles. -/
theorem consec_ne {j1 j2 : Fin N} {d : V2} {U V W : Plane} (h1 : TriStep (C.tile j1) d U V)
    (h2 : TriStep (C.tile j2) d V W) : j1 ≠ j2 := by
  rintro rfl
  have p1 := h1
  obtain ⟨-, -, -, -, -, -, -, -, hpar1, -⟩ := p1
  have p2 := h2
  obtain ⟨-, -, -, -, -, -, -, -, hpar2, -⟩ := p2
  have l1 : crs d (toV2 (V - U)) = 0 := by
    have := hpar1.1; simp only [crs] at this ⊢; linarith
  have l2 : crs d (toV2 (W - U)) = 0 := by
    have := hpar2.1
    have e : crs d (toV2 (W - U)) = - crs (toV2 (W - V)) d + crs d (toV2 (V - U)) := by
      simp only [crs, toV2, PiLp.sub_apply]; ring
    rw [e, this, l1]; ring
  have heq := Walks.step_same h1 h2 l1 l2
  rw [heq, sub_self] at hpar1
  have := hpar1.2
  simp [dt, toV2] at this

include hreg hidx hidxA hγ hPang in
/-- **A side of the polygon is not made of `a` edges only.** -/
theorem not_all_a (h01 : slen C 0 ≠ slen C 1) (h02 : slen C 0 ≠ slen C 2) (i : Fin 3)
    (hall : ∀ L, WalkT C.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L →
      ∀ e ∈ L, dist e.2.1 e.2.2 = slen C 0) : False := by
  obtain ⟨L, e0, el, W, hh, hl, hs1, hs2, hT0, hT1⟩ := edge_data C P hreg i
  have hlen := hall L W
  obtain ⟨L0, hL0⟩ : ∃ L0, L = e0 :: L0 := by
    cases L with
    | nil => simp at hh
    | cons x L0 => simp at hh; exact ⟨L0, by rw [hh]⟩
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (P.v i - P.v i) = (s * (toV2 (P.e i)).1, s * (toV2 (P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  -- `γ` at the head of every tile
  have hR := walk_prop_forward_mem C.toRegionDissection P hreg i (fun e => e ∈ L)
      (fun e => TyAt C idx e.1 e.2.2 2) (by
      intro e e2 t he he2 ht0 ht1 hVt hX2 hS1 hS2 hRe
      obtain ⟨kk, f, hk, hf, hty⟩ := types_of_a C idx hidx h01 h02 hS2 (hlen e2 he2)
      have hne := consec_ne C hS1 (hX2 ▸ hS2)
      obtain ⟨kk1, f1, hk1, hf1⟩ := step_idx hS1
      have h1 : idx e.1 f1 = 2 := (tyAt_iff hf1 2).mp hRe
      have htail : idx e2.1 kk ≠ 2 := by
        intro h2
        exact no_two_gamma C P hreg idx hidxA hγ hPang i ht0 ht1 hne (hf1.trans hVt)
          (hk.trans (hX2.trans hVt)) h1 h2
      refine (tyAt_iff hf 2).mpr ?_
      rcases hty with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h htail) rfl W (fun e he => he) hU e0 L0 hL0 (by
      obtain ⟨kk, f, hk, hf, hty⟩ := types_of_a C idx hidx h01 h02 hT0 (hlen e0 (by rw [hL0]; simp))
      have htail : idx e0.1 kk ≠ 2 := no_gamma_corner C P hreg idx hidxA hγ hPang (hk.trans hs1)
      refine (tyAt_iff hf 2).mpr ?_
      rcases hty with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h htail)
  have hel : el ∈ L := List.mem_of_getLast? hl
  obtain ⟨kk, f, hk, hf⟩ := step_idx hT1
  exact no_gamma_corner C P hreg idx hidxA hγ hPang (hf.trans hs2) ((tyAt_iff hf 2).mp (hR el hel))

end Gamma120

end TriangleTiling.Equilateral
