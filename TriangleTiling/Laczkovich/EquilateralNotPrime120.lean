/-
`theorem:notprime120` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723): an
equilateral triangle tiled by a tile with a `2π/3` angle, `α ∉ ℚπ`, has a non-prime number of tiles.

Statement checked by Beeson. The proof is the paper's. Take the sides `a, b, c` integers
without a common factor (Laczkovich 2012, Theorem 3.3), and suppose `N` is prime.

* `N ≤ 3` is impossible, since `c² = a² + ab + b² > 3ab ≥ Nab = X²` while `c ≤ X`.
* The area equation `X² = Nab` gives `N ∣ ab`; by symmetry `N ∣ a`. Then `N ∤ b` and
  `c ≡ ±b (mod N)`.
* Each side of `ABC` is `X = pa + qb + rc`; `N ∣ X` gives `N ∣ (q ± r) b`. The tiles supported by
  the side are distinct, so `p + q + r ≤ N`, and `lemma:notallsupported` gives `q + r < N`.
* If `c ≡ -b`, no relation `jc = ℓa + mb` is witnessed: it would give `N ∣ m + j ≤ N`, so every
  tile would be supported by one segment (`lemma:notallsupported`). So by `lemma:noboundarylink`
  and `lemma:propagation2` each side of `ABC` is all `c` edges or has no `c` edge.
* Hence `AB` has no `c` edge: if `c ≡ b` then `N ∣ q + r < N`, so `q = r = 0`; if `c ≡ -b` then
  `q = r`, so `AB` is not all `c` edges, hence has none, and then `q = r = 0` too. So `AB` is all `a`
  edges. (`side_all_a` is stated for any side; `core` applies it to side `0`, which is `AB`.)
* A side of `a` edges only is impossible (the paper's last paragraph, `Gamma120.not_all_a`; the
  paper applies its pigeonhole to `a` and `b` edges, here only `a` edges are needed).
-/
import TriangleTiling.Laczkovich.EquilateralGammaC
import TriangleTiling.Laczkovich.W.Gamma120
import TriangleTiling.Equilateral.NotAllSupported
import TriangleTiling.Equilateral.EquilateralBound
import TriangleTiling.Equilateral.NotPrime60Core
import TriangleTiling.TwoCs.TwoCs
import Erdos634.Draft.LaczFormalThm33iii3
import Erdos634.Draft.LaczFormalBZL7d5b

open scoped Classical

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21
  Erdos634.Draft.LaczFormal.RG Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha
open Erdos634.Draft.LaczFormal.Graph (V2 neg2 toV2 TriStep crs dt Par)

variable {N : ℕ}

namespace NP120

/-- **Along a side, all `c` or no `c`.** With no witnessed relation, consecutive edges on a side of
the polygon are both `c` edges or both not (else a link of `Γ_c` starts on the boundary). -/
theorem c_uniform (T : PolyTiling N 3) (hreg : RegularPQ T.C)
    (hab : slen T.C 0 ≠ slen T.C 1) (hca : slen T.C 2 ≠ slen T.C 0) (hcb : slen T.C 2 ≠ slen T.C 1)
    (hnw : ∀ j ℓ m, ¬ Witnesses T.C.toRegionDissection (slen T.C 0) (slen T.C 1) (slen T.C 2) j ℓ m)
    (i : Fin 3) {L : List (Fin N × Plane × Plane)}
    (W : WalkT T.C.toRegionDissection (toV2 (T.P.e i)) (T.P.v i) (T.P.v (i + 1)) L)
    {e0 : Fin N × Plane × Plane} {L0 : List (Fin N × Plane × Plane)} (hL0 : L = e0 :: L0) :
    ∀ e ∈ L, (dist e.2.1 e.2.2 = slen T.C 2 ↔ dist e0.2.1 e0.2.2 = slen T.C 2) := by
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨idx, h⟩ := caseCW_of_regular T hreg hab hca hcb hnw
  have hprop := (propagation2 T hreg hab hca hcb hnw).2
  have hU : ∃ s : ℝ, 0 ≤ s ∧ toV2 (T.P.v i - T.P.v i) = (s * (toV2 (T.P.e i)).1, s * (toV2 (T.P.e i)).2) :=
    ⟨0, le_rfl, by unfold toV2; ext <;> simp⟩
  refine walk_prop_forward T.C.toRegionDissection T.P T.region_eq i
    (fun e => dist e.2.1 e.2.2 = slen T.C 2 ↔ dist e0.2.1 e0.2.2 = slen T.C 2) ?_ rfl W hU e0 L0 hL0 Iff.rfl
  intro e e2 t ht0 ht1 hVt hX2 hS1 hS2 hRe
  rw [← hRe]
  by_contra hne
  have hord : (dist e.2.1 ((1 - t) • T.P.v i + t • T.P.v (i + 1)) = slen T.C 2 ∧
        dist ((1 - t) • T.P.v i + t • T.P.v (i + 1)) e2.2.2 ≠ slen T.C 2) ∨
      (dist e.2.1 ((1 - t) • T.P.v i + t • T.P.v (i + 1)) ≠ slen T.C 2 ∧
        dist ((1 - t) • T.P.v i + t • T.P.v (i + 1)) e2.2.2 = slen T.C 2) := by
    rw [← hVt]
    have e2d : dist e.2.2 e2.2.2 = dist e2.2.1 e2.2.2 := by rw [hX2]
    rw [e2d]
    by_cases hA : dist e2.2.1 e2.2.2 = slen T.C 2 <;> by_cases hB : dist e.2.1 e.2.2 = slen T.C 2
    · exact absurd ⟨fun _ => hB, fun _ => hA⟩ hne
    · exact Or.inr ⟨hB, hA⟩
    · exact Or.inl ⟨hB, hA⟩
    · exact absurd ⟨fun h => absurd h hA, fun h => absurd h hB⟩ hne
  obtain ⟨Y, hY⟩ := hprop i ht0 ht1 (hVt ▸ hS1) (by rw [← hVt, ← hX2]; exact hS2) hord
  have hint : (1 - t) • T.P.v i + t • T.P.v (i + 1) ∉ interior T.C.region := by
    rw [T.region_eq]
    apply ConvPoly.not_interior_of_sideSet T.P (j := i)
    exact ⟨1 - t, t, by linarith, ht0.le, by ring, rfl⟩
  refine gc_no_boundary_W T.C idx h (H := Y) hint ?_
  show GaEdge T.C.toRegionDissection (slen T.C 2) _ Y
  exact hY

/-- A list of numbers from `{a, b, c}` (distinct): its length is the sum of the counts. -/
theorem length_eq_countP {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ L : List ℝ, (∀ x ∈ L, x = a ∨ x = b ∨ x = c) →
      L.length = L.countP (fun x => decide (x = a)) + L.countP (fun x => decide (x = b)) +
        L.countP (fun x => decide (x = c))
  | [], _ => by simp
  | x :: L, h => by
    have ih := length_eq_countP hab hac hbc L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x List.mem_cons_self with rfl | rfl | rfl <;>
      simp [List.countP_cons, hab, hac, hbc, hab.symm, hac.symm, hbc.symm] <;> omega

/-- **No witnessed relation when `c ≡ -b (mod N)`.** A witnessed `jc = ℓa + mb` gives
`j(b + c) = ℓa + (m + j)b`, so `N ∣ m + j`; but at most `N` tiles are supported by the segment,
so `m + j = N` and every tile is supported by it, which `lemma:notallsupported` forbids. -/
theorem no_witness (D : CongruentDissection N) (T : PolyTiling N 3)
    (htile : ∀ i, T.C.toRegionDissection.tile i = D.tile i) (hN : N.Prime) (hN3 : 3 < N)
    {A B C : ℕ} {μ : ℝ} (hμ : 0 < μ) (sa : slen T.C 0 = μ * A) (sb : slen T.C 1 = μ * B)
    (sc : slen T.C 2 = μ * C) (hab : slen T.C 0 ≠ slen T.C 1) (hca : slen T.C 2 ≠ slen T.C 0)
    (hcb : slen T.C 2 ≠ slen T.C 1) (hNA : (N : ℤ) ∣ A) (hNB : ¬ (N : ℤ) ∣ B)
    (hBC : (N : ℤ) ∣ C + B) :
    ∀ j ℓ m, ¬ Witnesses T.C.toRegionDissection (slen T.C 0) (slen T.C 1) (slen T.C 2) j ℓ m := by
  rintro j ℓ m ⟨d, X, Y, P, Q, hW, hj, hPc, hℓ, hm, hlen⟩
  obtain ⟨idx, hidx, -⟩ := exists_idx_both T.C
  have key : P.length + Q.length ≤ N ∧
      (P.length + Q.length = N → ∀ i, ∃ k, (T.C.toRegionDissection.tile i).edge k ⊆ segment ℝ X Y) ∧
      (P.map fun e => dist e.2.1 e.2.2).sum = (Q.map fun e => dist e.2.1 e.2.2).sum ∧
      ∀ x ∈ Q.map (fun e => dist e.2.1 e.2.2), x = slen T.C 0 ∨ x = slen T.C 1 ∨ x = slen T.C 2 := by
    rcases hW with ⟨W1, W2⟩ | ⟨W1, W2⟩
    · obtain ⟨h1, h2⟩ := Walks.chains_card W1 W2
      refine ⟨h1, h2, by rw [walkT_dist_sum W1, walkR_dist_sum W2], fun x hx => ?_⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have := side_len_mem T.C idx hidx (walkR_mem_step W2 e he)
      rwa [dist_comm] at this
    · obtain ⟨h1, h2⟩ := Walks.chains_card W2 W1
      refine ⟨by omega, fun h => h2 (by omega), by rw [walkR_dist_sum W1, walkT_dist_sum W2],
        fun x hx => ?_⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact side_len_mem T.C idx hidx (walkT_mem_step W2 e he)
  obtain ⟨htot, hall, hsum, hmem⟩ := key
  set n := (Q.map fun e => dist e.2.1 e.2.2).countP (fun x => decide (x = slen T.C 2)) with hn
  have hQlen : Q.length = ℓ + m + n := by
    have := length_eq_countP hab hca.symm hcb.symm _ hmem
    rw [List.length_map] at this
    rw [this, hℓ, hm]
  have hPs : (P.map fun e => dist e.2.1 e.2.2).sum = P.length * slen T.C 2 := by
    rw [List.sum_eq_card_nsmul _ (slen T.C 2) (fun x hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx; exact hPc e he), List.length_map, nsmul_eq_mul]
  have hQs := sum_eq_countP hab hca.symm hcb.symm _ hmem
  rw [hℓ, hm, ← hn] at hQs
  rw [hPs, hQs, hlen, sa, sb, sc] at hsum
  have hrel : ((j * C : ℕ) : ℝ) = ((ℓ * A + m * B : ℕ) : ℝ) := by
    push_cast
    apply mul_left_cancel₀ hμ.ne'
    push_cast at hsum
    linarith
  have hrelZ : (j : ℤ) * C = ℓ * A + m * B := by exact_mod_cast hrel
  -- `N ∣ m + j`
  have hpr : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hN
  have hdvd : (N : ℤ) ∣ ((m + j : ℕ) : ℤ) * B := by
    have : ((m + j : ℕ) : ℤ) * B = j * (C + B) - ℓ * A := by push_cast; linear_combination -hrelZ
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right hBC _) (dvd_mul_of_dvd_right hNA _)
  have hmj : N ∣ m + j := by
    rcases hpr.dvd_or_dvd hdvd with h | h
    · exact Int.natCast_dvd_natCast.mp h
    · exact absurd h hNB
  have hle : N ≤ m + j := Nat.le_of_dvd (by omega) hmj
  have heq : P.length + Q.length = N := by omega
  exact notallsupported D hN3 X Y (fun i => by
    obtain ⟨k, hk⟩ := hall heq i
    exact ⟨k, htile i ▸ hk⟩)

/-- Any two vertices of an equilateral triangle are at distance `X`. -/
theorem equi_dist (T : Tri) (heq : ∀ j : Fin 3, dist (T.pts j) (T.pts (j + 1)) = dist (T.pts 0) (T.pts 1))
    {u v : Fin 3} (h : u ≠ v) : dist (T.pts u) (T.pts v) = dist (T.pts 0) (T.pts 1) := by
  rcases Walks.fin3_adj (Ne.symm h) with e | e
  · rw [e]; exact heq u
  · rw [e, dist_comm]; exact heq v

/-- **Every side of `ABC` has only `a` edges** (the arithmetic and the `c`-propagation). -/
theorem side_all_a (D : CongruentDissection N) (T : PolyTiling N 3)
    (htile : ∀ i, T.C.toRegionDissection.tile i = D.tile i) (hreg : RegularPQ T.C)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((T.C.tile i).pts k) ((T.C.tile i).pts k') =
      dist (T.C.model.pts (idx i k)) (T.C.model.pts (idx i k')))
    (hN : N.Prime) (hN3 : 3 < N) {a b c : ℝ} {A B C : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (ha : a = μ * A) (hb : b = μ * B) (hc : c = μ * C)
    (sa : slen T.C 0 = a) (sb : slen T.C 1 = b) (sc : slen T.C 2 = c)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) {X : ℝ} (hside : ∀ i, T.P.side i = X)
    (harea : X ^ 2 = N * a * b)
    (hNAZ : (N : ℤ) ∣ A) (hNB : ¬ (N : ℤ) ∣ B) (hdiv : (N : ℤ) ∣ C - B ∨ (N : ℤ) ∣ C + B) :
    ∀ i : Fin 3, ∀ L, WalkT T.C.toRegionDissection (toV2 (T.P.e i)) (T.P.v i) (T.P.v (i + 1)) L →
      ∀ e ∈ L, dist e.2.1 e.2.2 = slen T.C 0 := by
  have hpr : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hN
  intro i L W
  by_contra hne
  push Not at hne
  obtain ⟨e1, he1, hne1⟩ := hne
  have hmem : ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen T.C 0 ∨ x = slen T.C 1 ∨ x = slen T.C 2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem T.C idx hidx (walkT_mem_step W e he)
  set ls := L.map (fun e => dist e.2.1 e.2.2) with hls
  set p := ls.countP (fun x => decide (x = slen T.C 0))
  set q := ls.countP (fun x => decide (x = slen T.C 1))
  set r := ls.countP (fun x => decide (x = slen T.C 2))
  have hsumL : X = p * a + q * b + r * c := by
    have hq := sum_eq_countP (by rwa [sa, sb]) (by rw [sa, sc]; exact hca.symm)
      (by rw [sb, sc]; exact hcb.symm) ls hmem
    calc X = T.P.side i := (hside i).symm
      _ = ls.sum := (walkT_dist_sum W).symm
      _ = _ := hq
      _ = p * a + q * b + r * c := by simp only [p, q, r, sa, sb, sc]
  -- `q + r > 0`
  have hqr0 : 0 < q + r := by
    have hx : dist e1.2.1 e1.2.2 ∈ ls := List.mem_map.mpr ⟨e1, he1, rfl⟩
    rcases hmem _ hx with h | h | h
    · exact absurd h hne1
    · have : 0 < q := List.countP_pos_iff.mpr ⟨_, hx, by simp [h]⟩
      omega
    · have : 0 < r := List.countP_pos_iff.mpr ⟨_, hx, by simp [h]⟩
      omega
  -- `q + r < N`: the tiles supported by the side are distinct, so `p + q + r ≤ N`, and
  -- `lemma:notallsupported` makes this strict
  have hqrN : q + r < N := by
    obtain ⟨h1, h2⟩ := Walks.chain_card W
    have hlen : L.length = p + q + r := by
      have := length_eq_countP (by rwa [sa, sb]) (by rw [sa, sc]; exact hca.symm)
        (by rw [sb, sc]; exact hcb.symm) ls hmem
      rw [hls, List.length_map] at this
      exact this
    rcases h1.lt_or_eq with h | h
    · omega
    · exact absurd (fun j => by
        obtain ⟨k, hk⟩ := h2 h j
        exact ⟨k, htile j ▸ hk⟩) (notallsupported D hN3 _ _)
  -- the integer side `Xn`
  obtain ⟨Xn, hXn⟩ : ∃ Xn : ℕ, Xn = p * A + q * B + r * C := ⟨_, rfl⟩
  have hXnR : X = μ * Xn := by rw [hsumL, ha, hb, hc, hXn]; push_cast; ring
  have hXn2 : (Xn : ℤ) ^ 2 = N * A * B := by
    have : ((Xn : ℝ)) ^ 2 = N * A * B := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hμ.ne')
      have := harea
      rw [hXnR, ha, hb] at this
      linear_combination this
    exact_mod_cast this
  have hNX : (N : ℤ) ∣ Xn := hpr.dvd_of_dvd_pow (n := 2) (by
    rw [hXn2]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  have hNqr : (N : ℤ) ∣ q * B + r * C := by
    have : ((q : ℤ) * B + r * C) = Xn - p * A := by rw [hXn]; push_cast; ring
    rw [this]; exact dvd_sub hNX (dvd_mul_of_dvd_right hNAZ _)
  rcases hdiv with hCB | hCB
  · -- `c ≡ b`: `N ∣ q + r`
    have : (N : ℤ) ∣ ((q + r : ℕ) : ℤ) * B := by
      have e : ((q + r : ℕ) : ℤ) * B = (q * B + r * C) - r * (C - B) := by push_cast; ring
      rw [e]; exact dvd_sub hNqr (dvd_mul_of_dvd_right hCB _)
    rcases hpr.dvd_or_dvd this with h | h
    · have := Nat.le_of_dvd hqr0 (Int.natCast_dvd_natCast.mp h)
      omega
    · exact hNB h
  · -- `c ≡ -b`: `q = r`, and the side has both `b` and `c` edges
    have hd : (N : ℤ) ∣ ((q : ℤ) - r) * B := by
      have e : ((q : ℤ) - r) * B = (q * B + r * C) - r * (C + B) := by ring
      rw [e]; exact dvd_sub hNqr (dvd_mul_of_dvd_right hCB _)
    have hqr : q = r := by
      rcases hpr.dvd_or_dvd hd with h | h
      · have h' := Int.eq_zero_of_abs_lt_dvd h (by
          rw [abs_lt]; constructor <;> push_cast <;> omega)
        omega
      · exact absurd h hNB
    have hq : 0 < q := by omega
    have hr : 0 < r := by omega
    obtain ⟨xb, hxb, hxbe⟩ := List.countP_pos_iff.mp hq
    obtain ⟨xc, hxc, hxce⟩ := List.countP_pos_iff.mp hr
    obtain ⟨eb, heb, rfl⟩ := List.mem_map.mp hxb
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp hxc
    simp only [decide_eq_true_eq] at hxbe hxce
    have hnw := no_witness D T htile hN hN3 hμ (by rw [sa, ha]) (by rw [sb, hb]) (by rw [sc, hc])
      (by rwa [sa, sb]) (by rw [sc, sa]; exact hca) (by rw [sc, sb]; exact hcb) hNAZ hNB hCB
    obtain ⟨e0, L0, hL0⟩ : ∃ e0 L0, L = e0 :: L0 := by
      cases L with
      | nil => simp at he1
      | cons x L0 => exact ⟨x, L0, rfl⟩
    have hu := c_uniform T hreg (by rwa [sa, sb]) (by rw [sc, sa]; exact hca)
      (by rw [sc, sb]; exact hcb) hnw i W hL0
    have h1 := (hu ec hec).mp hxce
    have h2 := (hu eb heb).mpr h1
    rw [hxbe, sb, sc] at h2
    exact hcb h2.symm

/-- The tile: positive sides, `a, b, c` distinct, `c² = a² + b² + ab`, and the area equation. -/
theorem facts (D : CongruentDissection N) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ c ^ 2 = a ^ 2 + b ^ 2 + a * b ∧
      D.target.oppLen 0 ^ 2 = N * a * b := by
  have hπ := Real.pi_pos
  -- the angles and sides of the tile
  have hsum : α + β + 2 * Real.pi / 3 = Real.pi := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [← h0, ← h1, ← h2, e, D.model.angleAt_sum]
  have hγα : 2 * Real.pi / 3 ≠ α := fun e => hα ⟨2 / 3, by rw [← e]; push_cast; ring⟩
  have hγβ : 2 * Real.pi / 3 ≠ β := fun e => hα ⟨-1 / 3, by push_cast; linarith⟩
  have hαβ : α ≠ β := fun e => hα ⟨1 / 6, by push_cast; linarith⟩
  have hab : a ≠ b := sides_ne_of_angles_ne D hT hαβ
  have hcb : c ≠ b := by
    refine sides_ne_of_angles_ne D (α := 2 * Real.pi / 3) (β := β) (γ := α) (a := c) (b := b) (c := a) ?_ hγβ
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ * Equiv.swap 0 2, ?_⟩
    simp only [Equiv.Perm.mul_apply, swap02_0, swap02_1, swap02_2]
    exact ⟨h2, h1, h0, l2, l1, l0⟩
  have hca : c ≠ a := by
    refine sides_ne_of_angles_ne D (α := 2 * Real.pi / 3) (β := α) (γ := β) (a := c) (b := a) (c := b) ?_ hγα
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ * Equiv.swap 0 2 * Equiv.swap 1 2, ?_⟩
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp (config := { decide := true })
    exact ⟨h2, h0, h1, l2, l0, l1⟩
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have pa : 0 < a := l0 ▸ D.model.oppLen_pos _
  have pb : 0 < b := l1 ▸ D.model.oppLen_pos _
  have pc : 0 < c := l2 ▸ D.model.oppLen_pos _
  -- law of cosines: `c² = a² + b² + ab`
  have hcos : c ^ 2 = a ^ 2 + b ^ 2 + a * b := by
    have hl := D.model.lawCos_perm σ
    rw [l0, l1, l2, h2, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hl
    linarith
  -- the area equation `X² = Nab`
  have harea : D.target.oppLen 0 ^ 2 = N * a * b := by
    have hs3 : 0 < Real.sin (Real.pi / 3) := by rw [Real.sin_pi_div_three]; positivity
    have hsγ : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi / 3) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
    have h := area_sines D
    have hprod : Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
        Real.sin (D.model.angleAt 2) = Real.sin α * Real.sin β * Real.sin (2 * Real.pi / 3) := by
      have e := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
      simp only [Fin.prod_univ_three] at e
      rw [← e, h0, h1, h2]
    rw [hprod, hP 0, hP 1, hP 2] at h
    have ha' := lawsin D.model (σ 0)
    have hb' := lawsin D.model (σ 1)
    rw [l0, h0] at ha'
    rw [l1, h1] at hb'
    have hX := lawsin D.target 0
    rw [hP 0] at hX
    rw [hsγ] at h
    have : ((N : ℝ) * a * b - D.target.oppLen 0 ^ 2) * Real.sin (Real.pi / 3) = 0 := by
      rw [ha', hb', hX]; linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  exact ⟨pa, pb, pc, hab, hca, hcb, hcos, harea⟩

/-- **The polygon tiling**, with the model relabeled so that `α, β, γ` are at `0, 1, 2`. -/
theorem setup (D : CongruentDissection N) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α) (hN0 : 0 < N) :
    ∃ (T : PolyTiling N 3) (idx : Fin N → Equiv.Perm (Fin 3)),
      (∀ i, T.C.toRegionDissection.tile i = D.tile i) ∧ RegularPQ T.C ∧
      (∀ i v, T.C.model.angleAt (idx i v) = (T.C.tile i).angleAt v) ∧
      (∀ i k k', dist ((T.C.tile i).pts k) ((T.C.tile i).pts k') =
        dist (T.C.model.pts (idx i k)) (T.C.model.pts (idx i k'))) ∧
      slen T.C 0 = a ∧ slen T.C 1 = b ∧ slen T.C 2 = c ∧
      T.C.model.angleAt 2 = 2 * Real.pi / 3 ∧ (∀ i, T.P.angle i = Real.pi / 3) ∧
      (∀ i, T.P.side i = D.target.oppLen 0) ∧ c ≤ D.target.oppLen 0 := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  set X := D.target.oppLen 0 with hXdef
  -- the polygon tiling, model relabeled so that `α, β, γ` are at `0, 1, 2`
  have heq := equilateral_sides D.target hP
  obtain ⟨P, hPc, τ, hPa, hPv⟩ := exists_convpoly_of_tri' D.target
  obtain ⟨T, hTC, hTP⟩ : ∃ T : PolyTiling N 3, T.C = relabel D.toRegion σ ∧ T.P = P :=
    ⟨⟨relabel D.toRegion σ, P, by rw [hPc]; rfl⟩, rfl, rfl⟩
  have hang : ∀ j, Erdos634.TilePlacement.angleAt T.C.model j = D.model.angleAt (σ j) := by
    intro j; rw [hTC, relabel_angleAt]; rfl
  have hslen : ∀ k, slen D.toRegion k = D.model.oppLen k := by
    intro k; fin_cases k <;> rfl
  have hsl : ∀ j, slen T.C j = D.model.oppLen (σ j) := by
    intro j; rw [hTC, relabel_slen, hslen]
  have sa : slen T.C 0 = a := by rw [hsl, l0]
  have sb : slen T.C 1 = b := by rw [hsl, l1]
  have sc : slen T.C 2 = c := by rw [hsl, l2]
  have hPang : ∀ i, T.P.angle i = Real.pi / 3 := fun i => by
    rw [hTP, hPa, hP]
  have hγT : Erdos634.TilePlacement.angleAt T.C.model 2 = 2 * Real.pi / 3 := by rw [hang 2, h2]
  have hαT : ¬ ∃ r : ℚ, Erdos634.TilePlacement.angleAt T.C.model 0 = (r : ℝ) * Real.pi := by rw [hang 0, h0]; exact hα
  have hreg : RegularPQ T.C := regular_of_irr T hγT hαT hPang
  obtain ⟨idx, hA, hcnt⟩ := id hreg
  have hidx := idx_dist_of_angle T.C idx hA
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have htile : ∀ i, T.C.toRegionDissection.tile i = D.tile i := fun i => by rw [hTC]; rfl
  have hX : ∀ u v : Fin 3, u ≠ v → dist (D.target.pts u) (D.target.pts v) = X := by
    intro u v huv
    rw [equi_dist D.target heq huv, hXdef]
    show _ = dist (D.target.pts (0 + 1)) (D.target.pts (0 + 2))
    exact (heq 1).symm
  have hside : ∀ i, T.P.side i = X := by
    intro i
    show dist (T.P.v i) (T.P.v (i + 1)) = X
    rw [hTP, hPv, hPv]
    exact hX _ _ (fun e => by
      have := τ.injective e
      revert this; generalize i = i'; revert i'; decide)
  -- `c ≤ X`: an edge of a tile lies in `ABC`
  have hcX : c ≤ X := by
    have i0 : Fin N := ⟨0, hN0⟩
    set k := (idx i0).symm 0
    set k' := (idx i0).symm 1
    have hd : dist ((D.tile i0).pts k) ((D.tile i0).pts k') = c := by
      have := hidx i0 k k'
      simp only [k, k', Equiv.apply_symm_apply] at this
      rw [← sc, ← htile]; exact this
    have hseg : segment ℝ ((D.tile i0).pts k) ((D.tile i0).pts k') ⊆ D.target.carrier :=
      ((convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (Set.mem_range_self k))
        (subset_convexHull ℝ _ (Set.mem_range_self k'))).trans (tile_subset_target D.toDissection i0)
    rw [← hd]
    exact (equilateralbound D.target hX hseg).1
  exact ⟨T, idx, htile, hreg, hA, hidx, sa, sb, sc, hγT, hPang, hside, hcX⟩

/-- `N` divides `ab` (the area equation, with `X` a sum of tile edges). -/
theorem dvd_ab (D : CongruentDissection N) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α)
    (hN : N.Prime) {A B C : ℕ} {μ : ℝ} (hμ : 0 < μ) (ha : a = μ * A) (hb : b = μ * B)
    (hc : c = μ * C) : N ∣ A * B := by
  obtain ⟨pa, pb, pc, hab, hca, hcb, hcos, harea⟩ := facts D hP hT hα
  obtain ⟨T, idx, htile, hreg, hA, hidx, sa, sb, sc, hγT, hPang, hside, -⟩ := setup D hP hT hα hN.pos
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨L, -, -, W, -⟩ := edge_data T.C T.P T.region_eq 0
  have hmem : ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen T.C 0 ∨ x = slen T.C 1 ∨ x = slen T.C 2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem T.C idx hidx (walkT_mem_step W e he)
  set ls := L.map (fun e => dist e.2.1 e.2.2) with hls
  set p := ls.countP (fun x => decide (x = slen T.C 0))
  set q := ls.countP (fun x => decide (x = slen T.C 1))
  set r := ls.countP (fun x => decide (x = slen T.C 2))
  have hsumL : D.target.oppLen 0 = p * a + q * b + r * c := by
    have hq := sum_eq_countP (by rwa [sa, sb]) (by rw [sa, sc]; exact hca.symm)
      (by rw [sb, sc]; exact hcb.symm) ls hmem
    calc D.target.oppLen 0 = T.P.side 0 := (hside 0).symm
      _ = ls.sum := (walkT_dist_sum W).symm
      _ = _ := hq
      _ = p * a + q * b + r * c := by simp only [p, q, r, sa, sb, sc]
  obtain ⟨Xn, hXn⟩ : ∃ Xn : ℕ, Xn = p * A + q * B + r * C := ⟨_, rfl⟩
  have hXnR : D.target.oppLen 0 = μ * Xn := by rw [hsumL, ha, hb, hc, hXn]; push_cast; ring
  have hXn2 : Xn ^ 2 = N * (A * B) := by
    have : ((Xn : ℝ)) ^ 2 = N * (A * B) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hμ.ne')
      have := harea
      rw [hXnR, ha, hb] at this
      linear_combination this
    exact_mod_cast this
  have hNX : N ∣ Xn := hN.dvd_of_dvd_pow (n := 2) (by rw [hXn2]; exact dvd_mul_right _ _)
  obtain ⟨k, hk⟩ := hNX
  have : N * (A * B) = N * (N * k ^ 2) := by rw [← hXn2, hk]; ring
  exact ⟨k ^ 2, Nat.eq_of_mul_eq_mul_left hN.pos this⟩

/-- **The core of the proof**, with integer sides `A, B, C` (`a = μA` etc.) and `N ∣ A`. -/
theorem core (D : CongruentDissection N) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α)
    (hN : N.Prime) (hN3 : 3 < N) {A B C : ℕ} {μ : ℝ} (hμ : 0 < μ) (ha : a = μ * A) (hb : b = μ * B)
    (hc : c = μ * C) (hgcd : Nat.gcd (Nat.gcd A B) C = 1) (hNA : N ∣ A) : False := by
  obtain ⟨pa, pb, pc, hab, hca, hcb, hcos, harea⟩ := facts D hP hT hα
  obtain ⟨T, idx, htile, hreg, hA, hidx, sa, sb, sc, hγT, hPang, hside, -⟩ := setup D hP hT hα hN.pos
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  -- integer facts
  have hcosZ : (C : ℤ) ^ 2 = A ^ 2 + B ^ 2 + A * B := by
    have : ((C : ℝ)) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hμ.ne')
      rw [ha, hb, hc] at hcos; linear_combination hcos
    exact_mod_cast this
  have hpr : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hN
  have hNAZ : (N : ℤ) ∣ A := Int.natCast_dvd_natCast.mpr hNA
  have hNB : ¬ (N : ℤ) ∣ B := by
    intro hB
    have hC2 : (N : ℤ) ∣ C ^ 2 := by
      rw [hcosZ]
      exact dvd_add (dvd_add (dvd_pow hNAZ two_ne_zero) (dvd_pow hB two_ne_zero)) (dvd_mul_of_dvd_left hNAZ _)
    have hC : (N : ℤ) ∣ C := hpr.dvd_of_dvd_pow hC2
    have := Nat.dvd_gcd (Nat.dvd_gcd hNA (Int.natCast_dvd_natCast.mp hB)) (Int.natCast_dvd_natCast.mp hC)
    rw [hgcd] at this
    exact hN.one_lt.ne' (Nat.dvd_one.mp this)
  have hdiv : (N : ℤ) ∣ C - B ∨ (N : ℤ) ∣ C + B := by
    apply hpr.dvd_or_dvd
    have : ((C : ℤ) - B) * (C + B) = A * (A + B) := by linear_combination hcosZ
    rw [this]; exact dvd_mul_of_dvd_left hNAZ _
  have hall := side_all_a D T htile hreg idx hidx hN hN3 hμ ha hb hc sa sb sc hab hca hcb
    hside harea hNAZ hNB hdiv
  exact Gamma120.not_all_a T.C T.P T.region_eq idx hidx hA hγT hPang (by rwa [sa, sb])
    (by rw [sa, sc]; exact hca.symm) 0 (hall 0)

end NP120

open NP120 in
/-- **Theorem `theorem:notprime120`.** Let equilateral triangle `ABC` be `N`-tiled by a tile with
angles `(α, β, γ)`, with `γ = 2π/3` and `α` not a rational multiple of `π`. Then `N` is not a prime
number. -/
theorem notprime120 (D : CongruentDissection N) {α β a b c : ℝ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α) : ¬ N.Prime := by
  intro hN
  obtain ⟨pa, pb, pc, hab, hca, hcb, hcos, harea⟩ := facts D hP hT hα
  have hβ : IrrPi β := by
    have hsum : α + β + 2 * Real.pi / 3 = Real.pi := by
      obtain ⟨σ, h0, h1, h2, -⟩ := hT
      have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
      simp only [Fin.sum_univ_three] at e
      rw [← h0, ← h1, ← h2, e, D.model.angleAt_sum]
    rintro ⟨r, hr⟩; apply hα
    exact ⟨1 / 3 - r, by push_cast; linarith⟩
  -- `N ≤ 3` is impossible: the tile would not fit
  by_cases hN3 : 3 < N
  swap
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcX⟩ := setup D hP hT hα hN.pos
    have hN' : (N : ℝ) ≤ 3 := by exact_mod_cast not_lt.mp hN3
    have hc2 : c ^ 2 ≤ D.target.oppLen 0 ^ 2 := pow_le_pow_left₀ pc.le hcX 2
    have hab' : 0 < (a - b) ^ 2 := by positivity
    nlinarith [mul_pos pa pb]
  -- integer sides without a common factor (Laczkovich 2012, Theorem 3.3)
  obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ha, hb⟩ :
      ∃ p₁ q₁ p₂ q₂ : ℕ, 0 < p₁ ∧ 0 < p₂ ∧ a / c = (q₂ : ℝ) / p₂ ∧ b / c = (q₁ : ℝ) / p₁ := by
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    have hsγ : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi / 3) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
    have sa : a * Real.sin (Real.pi / 3) = c * Real.sin α := by
      have := D.model.lawSin (σ 0) (σ 2)
      rw [h0, h2, l0, l2, hsγ] at this; linarith
    have sb : b * Real.sin (Real.pi / 3) = c * Real.sin β := by
      have := D.model.lawSin (σ 1) (σ 2)
      rw [h1, h2, l1, l2, hsγ] at this; linarith
    have hTA : Erdos634.Draft.LaczFormal.TileAngles D α β (2 * Real.pi / 3) := ⟨σ, h0, h1, h2⟩
    obtain ⟨-, ⟨p₁, q₁, hp₁, hq₁, e₁⟩, ⟨p₂, q₂, hp₂, hq₂, e₂⟩⟩ :=
      Erdos634.Draft.LaczFormal.RG.sincomm_irr_family D hP hα (Or.inr rfl) hTA
    rw [hsγ] at e₁ e₂
    have hs3 : 0 < Real.sin (Real.pi / 3) := by rw [Real.sin_pi_div_three]; positivity
    have ha : a / c = (q₂ : ℝ) / p₂ := by
      rw [div_eq_div_iff pc.ne' (by exact_mod_cast hp₂.ne')]
      have : Real.sin α = q₂ / p₂ * Real.sin (Real.pi / 3) := by
        field_simp; linarith [e₂]
      rw [this] at sa
      field_simp at sa
      nlinarith [sa, hs3]
    have hb : b / c = (q₁ : ℝ) / p₁ := by
      rw [div_eq_div_iff pc.ne' (by exact_mod_cast hp₁.ne')]
      have : Real.sin β = q₁ / p₁ * Real.sin (Real.pi / 3) := by
        field_simp; linarith [e₁]
      rw [this] at sb
      field_simp at sb
      nlinarith [sb, hs3]
    exact ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ha, hb⟩
  have hp₁R : (0 : ℝ) < p₁ := by exact_mod_cast hp₁
  have hp₂R : (0 : ℝ) < p₂ := by exact_mod_cast hp₂
  rw [div_eq_div_iff pc.ne' hp₂R.ne'] at ha
  rw [div_eq_div_iff pc.ne' hp₁R.ne'] at hb
  obtain ⟨A, B, C, hC0, hgcd, hA, hB⟩ := int_sides (a := a) (b := b) (c := c)
    (A' := q₂ * p₁) (B' := q₁ * p₂) (C' := p₁ * p₂) (Nat.mul_pos hp₁ hp₂)
    (by push_cast; linear_combination (p₁ : ℝ) * ha) (by push_cast; linear_combination (p₂ : ℝ) * hb)
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC0
  set μ := c / C with hμ
  have hμ0 : 0 < μ := div_pos pc hCR
  have eA : a = μ * A := by rw [hμ]; field_simp; linarith
  have eB : b = μ * B := by rw [hμ]; field_simp; linarith
  have eC : c = μ * C := by rw [hμ]; field_simp
  -- `N ∣ ab`, so `N ∣ a` or `N ∣ b`; the two cases are symmetric
  rcases (Nat.Prime.dvd_mul hN).mp (dvd_ab D hP hT hα hN hμ0 eA eB eC) with hNA | hNB
  · exact core D hP hT hα hN hN3 hμ0 eA eB eC hgcd hNA
  · exact core D hP (TriangleTiling.ThreeAlpha.tileSides_swap D hT) hβ hN hN3 hμ0 eB eA eC
      (by rwa [Nat.gcd_comm B A]) hNB

end TriangleTiling.Equilateral
