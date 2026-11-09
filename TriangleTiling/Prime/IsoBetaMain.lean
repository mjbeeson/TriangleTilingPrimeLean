/-
The `j = 1` part of **`theorem:isoscelesbeta`** of M. Beeson and E. Roșu, *Tiling a triangle into a
prime number of congruent triangles*, Section 12 (`isobetaone`): there is no `j = 1` tiling of the isosceles-`β` triangle
`(β, β, 3α)` when `3α + 2β = π` with `α` not a rational multiple of `π`.

The printed proof: by `lemma:longrun` (vacuous hypothesis at `A`, `C`) the base `AC` carries a run
of `k` `c` edges, so by `lemma:edgedecompositions` (D) it has no `a` edge; at the apex the hypothesis
of `lemma:longrun` holds for one leg (`apex_endHyp`), which then consists of `c` edges only; and the
tile at the corner of that leg on the base has its `β` there, so an `a` edge on the leg or on the
base.

"A `j = 1` tiling" is `N = 3k² - m²` (the paper's `N = j²(3k² - m²)` with `j = 1`). The theorem as
printed, with "in particular, `N` cannot be prime, or even squarefree" (by `TriangleTiling3`
Theorem 19, `ThreeAlpha.notprime4`), is `isoscelesbeta` in `TriangleTiling.Laczkovich.PrimeJOne`.
-/
import TriangleTiling.Prime.IsoBetaApex2

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ}

namespace RunSetting

variable {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- A side of length `kc` supporting a run of `k` `c` edges has no `a` edge. -/
theorem noA_of_long {j : Fin 3} (hyp : EndHyp D j α γ a c)
    (hlen : dist (D.target.pts j) (D.target.pts (j + 1)) = k * c) :
    ∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
      segment ℝ P Q ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) → dist P Q ≠ a := by
  obtain ⟨n, U, I, t, hkn, hrun⟩ := longrun hS hyp
  obtain ⟨p, q, r, hsum, hcount, hrc⟩ := hS.side_counts_run j
  have hnr := hrc n U I t hrun
  intro t' P Q hte hsub hd
  have hp := (hcount t' P Q hte hsub).1 hd
  have hkr : (k : ℝ) ≤ r := by
    have : (k : ℤ) ≤ r := le_trans hkn (by exact_mod_cast hnr)
    exact_mod_cast this
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  have : (p : ℝ) * a + q * b + (r - k) * c = 0 := by linarith
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  nlinarith [mul_pos hp' ha, mul_nonneg (Nat.cast_nonneg q) hb.le,
    mul_nonneg (sub_nonneg.mpr hkr) hc.le]

end RunSetting

/-- **The `j = 1` part of `theorem:isoscelesbeta`.** There is no `j = 1` tiling of the isosceles-`β` triangle
when `3α + 2β = π` with `α` not a rational multiple of `π`.

`ABC = D.target` has angles `(β, 3α, β)` at `A, B, C = pts 0, pts 1, pts 2`, and the tile has sides
`(a, b, c) = (mk, k² - m², k²)`, `0 < m < k`, `gcd(m, k) = 1`. -/
theorem isobetaone {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = π)
    (hirr : ¬ ∃ r : ℚ, α = r * π) (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) :
    (N : ℝ) ≠ 3 * k ^ 2 - m ^ 2 := by
  intro hN
  have hS := isobeta_setting hT hrel hirr hm hmk hcop ha hb hc hshape
  have hnob := isoscelesnob hT hrel hirr hm hmk hcop ha hb hc hshape hN
  obtain ⟨hBC, hX, hXc, -, hY, -, -⟩ := isobetasides hT hrel hm hmk ha hb hc hshape (j := 1) one_pos
    (by rw [hN]; push_cast; ring)
  push_cast at hXc hY
  rw [one_mul] at hXc
  -- the base `CA`: no `a` edge
  have hyp2 : EndHyp D 2 α γ a c := by
    intro R V P W hV hRα
    exfalso
    rcases hV with rfl | rfl
    · exact hS.no_alpha_at hshape.2.2 hRα
    · exact hS.no_alpha_at hshape.1 hRα
  have hnoAC : ∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
      segment ℝ P Q ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) → dist P Q ≠ a := by
    obtain ⟨n, U, I, t, hkn, hrun⟩ := longrun hS hyp2
    obtain ⟨p, q, r, hsum, hcount, hrc⟩ := hS.side_counts_run 2
    have hnr := hrc n U I t hrun
    intro t' P Q hte hsub hd
    have hp := (hcount t' P Q hte hsub).1 hd
    have hlen : dist (D.target.pts 2) (D.target.pts (2 + 1)) = m * (b + 2 * c) := by
      rw [show (2 : Fin 3) + 1 = 0 from rfl, dist_comm]; linarith
    rw [hlen, ha, hb, hc] at hsum
    have hZ : (p : ℤ) * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 =
        m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) := by
      have h' : ((p : ℤ) : ℝ) * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 =
          (m : ℝ) * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) := by push_cast; linarith
      exact_mod_cast h'
    have := ((edgedecompositions hm hmk hcop).2.2.2.1 p q r (by positivity) (by positivity)
      (by positivity) hZ (le_trans hkn (by exact_mod_cast hnr))).1
    have : p = 0 := by exact_mod_cast this
    omega
  -- the tile at a base corner `pts l` with angle `β` has an `a` edge on one of its sides
  have hfoot : ∀ l : Fin 3, D.target.angleAt l = β →
      ∃ (G : Fin N) (s t : ℝ), 0 < s ∧ s ≤ 1 ∧ 0 < t ∧ t ≤ 1 ∧
        ((TileEdge D G (D.target.pts l)
            (D.target.pts l + s • (D.target.pts (l + 1) - D.target.pts l)) ∧
          dist (D.target.pts l)
            (D.target.pts l + s • (D.target.pts (l + 1) - D.target.pts l)) = a) ∨
         (TileEdge D G (D.target.pts l)
            (D.target.pts l + t • (D.target.pts (l + 2) - D.target.pts l)) ∧
          dist (D.target.pts l)
            (D.target.pts l + t • (D.target.pts (l + 2) - D.target.pts l)) = a)) := by
    intro l hl
    obtain ⟨hu, hv⟩ := vertex_rayWall D.toDissection l
    have hne : cross (D.target.pts (l + 1) - D.target.pts l)
        (D.target.pts (l + 2) - D.target.pts l) ≠ 0 := by
      have := D.target.det_ne_zero; rw [← D.target.cross_edgeVec l] at this; exact this
    obtain ⟨G, ⟨s, hs, t, ht, hG⟩, hGβ, -⟩ := sector_one hS hne hu hv (vertex_hin D.target l)
      (P := 0) (Q := 1) (by norm_num) (by
        have h := (Tri.cornerAngle_eq_angle D.target l).symm.trans hl
        simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add]; exact h)
    have hGβ' : HasAngle D G (D.target.pts l) β := by simpa using hGβ
    set X := D.target.pts l
    set u := D.target.pts (l + 1) - X
    set w := D.target.pts (l + 2) - X
    have hu0 := ne_zero_left_of_cross hne
    have hw0 := ne_zero_right_of_cross hne
    have n1 : X ≠ X + s • u := by
      intro h; have : s • u = 0 := by rw [← add_right_inj X, ← h, add_zero]
      exact smul_ne_zero hs.ne' hu0 this
    have n2 : X ≠ X + t • w := by
      intro h; have : t • w = 0 := by rw [← add_right_inj X, ← h, add_zero]
      exact smul_ne_zero ht.ne' hw0 this
    have n12 : X + s • u ≠ X + t • w := by
      intro h
      have e : s • u = t • w := by rw [← add_right_inj X, h]
      have := congrArg (cross u) e
      rw [cross_smul_right, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero] at this
      exact (mul_ne_zero ht.ne' hne) this.symm
    have hs1 : s ≤ 1 := le_one_of_mem D.target (show l ≠ l + 1 by fin_cases l <;> decide)
      (mem_target_of_range (t := G) (P := X + s • u) (by rw [hG]; simp))
    have ht1 : t ≤ 1 := le_one_of_mem D.target (show l ≠ l + 2 by fin_cases l <;> decide)
      (mem_target_of_range (t := G) (P := X + t • w) (by rw [hG]; simp))
    refine ⟨G, s, t, hs, hs1, ht, ht1, ?_⟩
    rcases hS.beta_pair hGβ' hG n1 n2 n12 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl ⟨tileEdge_of_range hG (by simp) (by simp) n1, h1⟩
    · exact Or.inr ⟨tileEdge_of_range hG (by simp) (by simp) n2, h2⟩
  have hsegs : ∀ {X Y : Plane} {s : ℝ}, 0 ≤ s → s ≤ 1 →
      segment ℝ X (X + s • (Y - X)) ⊆ segment ℝ X Y := by
    intro X Y s h0 h1
    apply (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨h0, h1⟩, by rw [AffineMap.lineMap_apply_module']; abel⟩
  -- a leg made of `c` edges, and the tile at its foot on the base
  rcases hS.apex_endHyp hshape hnob with hyp0 | hyp1
  · have hnoAB := hS.noA_of_long hyp0 (by rw [show (0 : Fin 3) + 1 = 1 from rfl, hXc])
    obtain ⟨G, s, t, hs, hs1, ht, ht1, h | h⟩ := hfoot 0 hshape.1
    · exact hnoAB G _ _ h.1 (hsegs hs.le hs1) h.2
    · refine hnoAC G _ _ h.1 ?_ h.2
      rw [segment_symm ℝ (D.target.pts 2)]; exact hsegs ht.le ht1
  · have hnoBC := hS.noA_of_long hyp1
      (by rw [show (1 : Fin 3) + 1 = 2 from rfl, hBC, hXc])
    obtain ⟨G, s, t, hs, hs1, ht, ht1, h | h⟩ := hfoot 2 hshape.2.2
    · exact hnoAC G _ _ h.1 (hsegs hs.le hs1) h.2
    · refine hnoBC G _ _ h.1 ?_ h.2
      rw [segment_symm ℝ (D.target.pts 1)]; exact hsegs ht.le ht1

end TriangleTiling.Prime
