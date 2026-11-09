/-
Section 13 of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of congruent
triangles*: the triquadratic shape `(2α, β, α + β)`. `lemma:gammagreaterpiover2`,
`lemma:sidelengths`.

`ABC` is `D.target` with `A, B, C = pts 0, pts 1, pts 2`, angles `2α` at `A`, `β` at `B`, `α + β`
at `C`. The integer `j` is that of `N = j²(2k² - m²)` (`TriangleTiling3` Lemma 47), taken as a
hypothesis, as in `isobetasides`.

Statements checked by Beeson.
-/
import TriangleTiling.Prime.IsoBetaMain

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

variable {N : ℕ}

/-- **Lemma `lemma:gammagreaterpiover2`.** Suppose `3α + 2β = π`. Then `γ > π/2`. -/
theorem gammagreaterpiover2 {α β γ : ℝ} (hrel : 3 * α + 2 * β = π) (hsum : α + β + γ = π)
    (hα : 0 < α) : π / 2 < γ := by
  linarith

/-- The law of cosines at a corner of a triangle, in terms of `oppLen`. -/
theorem tri_cos (M : Tri) (v : Fin 3) :
    M.oppLen v ^ 2 = M.oppLen (v + 1) ^ 2 + M.oppLen (v + 2) ^ 2 -
      2 * M.oppLen (v + 1) * M.oppLen (v + 2) * Real.cos (M.angleAt v) := by
  have hlc := EuclideanGeometry.law_cos (M.pts (v + 1)) (M.pts v) (M.pts (v + 2))
  have hang : ∠ (M.pts (v + 1)) (M.pts v) (M.pts (v + 2)) = M.angleAt v := rfl
  have adj : dist (M.pts (v + 1)) (M.pts v) = M.oppLen (v + 2) ∧
      dist (M.pts (v + 2)) (M.pts v) = M.oppLen (v + 1) := by
    unfold Tri.oppLen
    fin_cases v <;> exact ⟨dist_comm _ _, rfl⟩
  rw [hang, adj.1, adj.2] at hlc
  have : M.oppLen v = dist (M.pts (v + 1)) (M.pts (v + 2)) := rfl
  rw [this]; linear_combination hlc

/-- The law of cosines in the tile, at its three corners. -/
theorem model_cos {D : CongruentDissection N} {α β γ a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) :
    a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α ∧
    b ^ 2 = a ^ 2 + c ^ 2 - 2 * a * c * Real.cos β ∧
    c ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * Real.cos γ := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have d01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have d02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have d12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have key : ∀ {x y z : Fin 3} {p q r θ : ℝ}, x ≠ y → x ≠ z → y ≠ z →
      D.model.angleAt x = θ → D.model.oppLen x = p → D.model.oppLen y = q →
      D.model.oppLen z = r → p ^ 2 = q ^ 2 + r ^ 2 - 2 * q * r * Real.cos θ := by
    intro x y z p q r θ hxy hxz hyz hθ hp hq hr
    have := tri_cos D.model x
    rw [hθ, hp] at this
    rcases fin3_others hxy hxz hyz with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2, hq, hr] at this; exact this
    · rw [← e1, ← e2, hq, hr] at this; linarith
  exact ⟨key d01 d02 d12 h0 l0 l1 l2, key d01.symm d12 d02 h1 l1 l0 l2,
    key d02.symm d12.symm d01 h2 l2 l0 l1⟩

/-- The tile's sides by its circumdiameter `d`: `a = d sin α`, `b = d sin β`, `c = d sin γ`, and
the product of the sines of its corner angles. -/
theorem model_sines {D : CongruentDissection N} {α β γ a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) :
    a = ThreeAlpha.circumdiam D.model * Real.sin α ∧
    b = ThreeAlpha.circumdiam D.model * Real.sin β ∧
    c = ThreeAlpha.circumdiam D.model * Real.sin γ ∧
    Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2) =
      Real.sin α * Real.sin β * Real.sin γ := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have la := ThreeAlpha.lawsin D.model (σ 0)
  have lb := ThreeAlpha.lawsin D.model (σ 1)
  have lc := ThreeAlpha.lawsin D.model (σ 2)
  rw [l0, h0] at la; rw [l1, h1] at lb; rw [l2, h2] at lc
  refine ⟨la, lb, lc, ?_⟩
  rw [← h0, ← h1, ← h2]
  have := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
  simp only [Fin.prod_univ_three] at this
  linarith

/-- The distances between the vertices of the tile. -/
theorem model_dists {D : CongruentDissection N} {α β γ a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) :
    ∃ σ : Equiv.Perm (Fin 3), dist (D.model.pts (σ 1)) (D.model.pts (σ 2)) = a ∧
      dist (D.model.pts (σ 0)) (D.model.pts (σ 2)) = b ∧
      dist (D.model.pts (σ 0)) (D.model.pts (σ 1)) = c := by
  obtain ⟨σ, -, -, -, l0, l1, l2⟩ := hT
  have d01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have d02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have d12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have key : ∀ {x y z : Fin 3} {p : ℝ}, x ≠ y → x ≠ z → y ≠ z → D.model.oppLen x = p →
      dist (D.model.pts y) (D.model.pts z) = p := by
    intro x y z p hxy hxz hyz hp
    rcases fin3_others hxy hxz hyz with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hp
    · rw [e1, e2, dist_comm]; exact hp
  exact ⟨σ, key d01 d02 d12 l0, key d01.symm d12 d02 l1, key d02.symm d12.symm d01 l2⟩

/-- **Lemma `lemma:sidelengths`** (Triquadratic side lengths). Let `ABC` have the shape
`(2α, β, α + β)`, with `2α` at `A`, `β` at `B` and `α + β` at `C`, and `α` not a rational multiple
of `π`. Let the tile have sides `(a, b, c) = (km, k² - m², k²)` with `gcd(k, m) = 1`. Let `ABC` be
`N`-tiled, and `N = 2K² - M²`, with `(M, K) = j(m, k)`. Then `|AB| = Kc`, `|AC| = Kb`,
`|BC| = M(b + c)`.

Here `K = jk`, `M = jm`, `0 < m < k`, and `j > 0` with `N = j²(2k² - m²)`. -/
theorem sidelengths {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hirr : ¬ ∃ r : ℚ, α = r * π) (hm : 0 < m)
    (hmk : m < k) (hcop : IsCoprime m k) (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2)
    (hc : c = k ^ 2)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧
      D.target.angleAt 2 = α + β)
    {j : ℤ} (hj : 0 < j) (hN : (N : ℝ) = j ^ 2 * (2 * k ^ 2 - m ^ 2)) :
    dist (D.target.pts 0) (D.target.pts 1) = j * k * c ∧
    dist (D.target.pts 0) (D.target.pts 2) = j * k * b ∧
    dist (D.target.pts 1) (D.target.pts 2) = j * m * (b + c) := by
  obtain ⟨hα, hβ, hγ, hsum⟩ := ThreeAlpha.tileSides_angles D hT
  obtain ⟨hA, hB, hC⟩ := hshape
  set T := D.target
  set dT := ThreeAlpha.circumdiam T
  set d := ThreeAlpha.circumdiam D.model
  have hd := ThreeAlpha.circumdiam_pos D.model
  have hdT := ThreeAlpha.circumdiam_pos T
  have sα := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have sβ := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have sγ := Real.sin_pos_of_pos_of_lt_pi hγ (by linarith)
  have hsab : Real.sin (α + β) = Real.sin γ := by
    rw [show α + β = π - γ by linarith, Real.sin_pi_sub]
  obtain ⟨ea, eb, ec, hprod⟩ := model_sines hT
  obtain ⟨ca, -, -⟩ := model_cos hT
  -- the triangle's sides by its circumdiameter
  have hBC : dist (T.pts 1) (T.pts 2) = dT * (2 * Real.sin α * Real.cos α) := by
    have := ThreeAlpha.lawsin T 0; rw [hA, Real.sin_two_mul] at this; rw [← this]; rfl
  have hAC : dist (T.pts 0) (T.pts 2) = dT * Real.sin β := by
    have := ThreeAlpha.lawsin T 1; rw [hB] at this; rw [← this]; unfold Tri.oppLen
    exact dist_comm _ _
  have hAB : dist (T.pts 0) (T.pts 1) = dT * Real.sin γ := by
    have := ThreeAlpha.lawsin T 2; rw [hC, hsab] at this; rw [← this]; rfl
  -- `cos α = (2k² - m²)/(2k²)`
  have hk : (0 : ℝ) < k := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (m : ℝ) < k := by exact_mod_cast hmk
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk' : (m : ℝ) < k := by exact_mod_cast hmk
  have hb0 : (0 : ℝ) < k ^ 2 - m ^ 2 := by nlinarith
  have hcos : 2 * Real.cos α * k ^ 2 = 2 * k ^ 2 - m ^ 2 := by
    rw [ha, hb, hc] at ca
    have : ((k : ℝ) ^ 2 - m ^ 2) * (2 * Real.cos α * k ^ 2 - (2 * k ^ 2 - m ^ 2)) = 0 := by
      linear_combination ca
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb0.ne')
  -- the area equation: `N d² = 2 dT² cos α`
  have harea := ThreeAlpha.area_sines D
  rw [hprod, hA, hB, hC, hsab, Real.sin_two_mul] at harea
  have hNd : (N : ℝ) * d ^ 2 = dT ^ 2 * (2 * Real.cos α) := by
    have hs : 0 < Real.sin α * Real.sin β * Real.sin γ := by positivity
    apply mul_right_cancel₀ hs.ne'
    linear_combination harea
  -- `dT = j k d`
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have h2 : (0 : ℝ) < 2 * k ^ 2 - m ^ 2 := by nlinarith
  have hdTv : dT = j * k * d := by
    have e : (dT ^ 2) * (2 * k ^ 2 - m ^ 2) = (j * k * d) ^ 2 * (2 * k ^ 2 - m ^ 2) := by
      rw [hN] at hNd
      linear_combination (-(k : ℝ) ^ 2) * hNd - dT ^ 2 * hcos
    exact (sq_eq_sq₀ hdT.le (by positivity)).mp (mul_right_cancel₀ h2.ne' e)
  refine ⟨?_, ?_, ?_⟩
  · rw [hAB, hdTv, ec]; ring
  · rw [hAC, hdTv, eb]; ring
  · rw [hBC, hdTv, hb, hc]
    have e : (j : ℝ) * k * d * (2 * Real.sin α * Real.cos α) * k ^ 2 =
        j * (d * Real.sin α) * k * (2 * Real.cos α * k ^ 2) := by ring
    rw [← ea, ha, hcos] at e
    have : (j : ℝ) * k * d * (2 * Real.sin α * Real.cos α) * k ^ 2 =
        (j * m * (k ^ 2 - m ^ 2 + k ^ 2)) * k ^ 2 := by rw [e]; ring
    exact mul_right_cancel₀ (by positivity) this

end TriangleTiling.Prime
