/-
The `j = 1` part of **`theorem:triquadratic`** (`triquadone`) of M. Beeson and E. Roșu, *Tiling a triangle into a prime number of
congruent triangles*, Section 13: there is no `j = 1` tiling of the triquadratic triangle
`(2α, β, α + β)` when `3α + 2β = π` with `α` not a rational multiple of `π`.

The printed proof: tacking a quadratic tiling onto the side `AC` (`lemma:trisector`) makes a `j = 1`
tiling of the isosceles-`β` triangle, which `theorem:isoscelesbeta` excludes. Here `ABC = D.target`
has `2α, β, α + β` at `A, B, C = pts 0, pts 1, pts 2`; `|BC| = m(b + c)`, `|AC| = kb`, `|AB| = kc`
(`sidelengths`). The point `Z` on the ray from `B` through `C` with `|CZ| = ka` makes `ZCA` the tile
scaled by `k` (sides `ka, kb, kc`, angle `γ` at `C`), cut into `k²` tiles by
`Erdos634.Subdivision.ladderDissection`; glued to `D` along `AC` it gives a tiling of `ZAB` by
`N + k² = 3k² - m²` tiles, and `ZAB` has angles `β, 3α, β`.

As in `isobetaone`, "a `j = 1` tiling" is `N = 2k² - m²`. The theorem as printed ("`N` is not prime,
indeed not squarefree; `N = j²(2k² - m²)` with `j > 1`", using `TriangleTiling3`
`corollary:tqparameters`) is `triquadratic` in `TriangleTiling.Laczkovich.PrimeJOne`.
-/
import TriangleTiling.Prime.TriquadGlue

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

variable {N : ℕ}

theorem angleAt_eq (T : Tri) (j : Fin 3) :
    T.angleAt j = InnerProductGeometry.angle (T.pts (j + 1) - T.pts j) (T.pts (j + 2) - T.pts j) :=
  Tri.cornerAngle_eq_angle T j

theorem range_pts (T : Tri) : Set.range T.pts = {T.pts 0, T.pts 1, T.pts 2} := by
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (h | h | h) <;> exact ⟨_, h.symm⟩

theorem cross_pts_ne (T : Tri) (j : Fin 3) :
    cross (T.pts (j + 1) - T.pts j) (T.pts (j + 2) - T.pts j) ≠ 0 := by
  have := T.det_ne_zero; rw [← T.cross_edgeVec j] at this; exact this

/-- The angle with cosine `cos θ` is `θ`. -/
theorem angle_of_cos {u v : Plane} {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π)
    (h : Real.cos (InnerProductGeometry.angle u v) = Real.cos θ) :
    InnerProductGeometry.angle u v = θ :=
  Real.injOn_cos ⟨InnerProductGeometry.angle_nonneg u v, InnerProductGeometry.angle_le_pi u v⟩
    ⟨h0, hπ⟩ h

/-- **The `j = 1` part of `theorem:triquadratic`.** With `(a, b, c) = (mk, k² - m², k²)`, `0 < m < k`, `gcd(m, k) = 1`, the case
`j = 1`, `N = 2k² - m²`, is impossible. -/
theorem triquadone {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = π)
    (hirr : ¬ ∃ r : ℚ, α = r * π) (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧
      D.target.angleAt 2 = α + β) :
    (N : ℝ) ≠ 2 * k ^ 2 - m ^ 2 := by
  intro hN
  obtain ⟨hα, hβ, hγ, hsum⟩ := ThreeAlpha.tileSides_angles D hT
  obtain ⟨hAB, hAC, hBC⟩ := sidelengths hT hirr hm hmk hcop ha hb hc hshape (j := 1) one_pos
    (by rw [hN]; ring)
  obtain ⟨ca, cb, cc⟩ := model_cos hT
  set T := D.target
  set A := T.pts 0
  set B := T.pts 1
  set C := T.pts 2
  have hk : (0 : ℝ) < k := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (m : ℝ) < k := by exact_mod_cast hmk
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmk' : (m : ℝ) < k := by exact_mod_cast hmk
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; nlinarith
  have hc0 : 0 < c := by rw [hc]; positivity
  push_cast at hAB hAC hBC
  rw [one_mul] at hAB hAC hBC
  -- the nondegeneracy of `ABC`
  have nA : cross (B - A) (C - A) ≠ 0 := cross_pts_ne T 0
  have nC : cross (A - C) (B - C) ≠ 0 := cross_pts_ne T 2
  -- the point `Z`
  set L := dist B C
  have hL : 0 < L := by rw [hBC]; have : 0 < b + c := by linarith
                        positivity
  set s := k * a / L
  have hs : 0 < s := by positivity
  set Z := C + s • (C - B)
  have hZC : dist Z C = k * a := by
    rw [dist_eq_norm, show Z - C = s • (C - B) by simp [Z], norm_smul, Real.norm_of_nonneg hs.le,
      ← dist_eq_norm, dist_comm]
    simp only [s, L]; field_simp; exact div_self (ne_of_gt hL)
  have hCA : dist A C = k * b := hAC
  -- `∠ZCA = γ`, so `|ZA| = kc`
  have hZCA : ∠ Z C A = γ := by
    have h1 : Z -ᵥ C = s • -(B - C) := by
      rw [vsub_eq_sub, show Z - C = s • (C - B) by simp [Z], neg_sub]
    have h2 : InnerProductGeometry.angle (B - C) (A - C) = α + β := by
      rw [InnerProductGeometry.angle_comm, ← hshape.2.2, angleAt_eq]; rfl
    rw [EuclideanGeometry.angle, h1, InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
      vsub_eq_sub, InnerProductGeometry.angle_neg_left, h2]
    linarith
  have hZA : dist Z A = k * c := by
    have hlc := EuclideanGeometry.law_cos Z C A
    rw [hZCA, hZC, hCA] at hlc
    have : dist Z A ^ 2 = (k * c) ^ 2 := by
      rw [sq, hlc]; linear_combination (-(k : ℝ) ^ 2) * cc
    exact (sq_eq_sq₀ dist_nonneg (by positivity)).mp this
  -- the angles of `ZCA` at `Z` and `A`
  have hAZC : InnerProductGeometry.angle (A - Z) (C - Z) = β := by
    have hlc := EuclideanGeometry.law_cos A Z C
    rw [dist_comm A Z, hZA, dist_comm C Z, hZC, hCA] at hlc
    apply angle_of_cos hβ.le (by linarith)
    have e : (2 * k ^ 2 * a * c) * (Real.cos (∠ A Z C) - Real.cos β) = 0 := by
      linear_combination hlc - (k : ℝ) ^ 2 * cb
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by positivity))
  have hCAZ : InnerProductGeometry.angle (C - A) (Z - A) = α := by
    have hlc := EuclideanGeometry.law_cos C A Z
    rw [dist_comm C A, hCA, hZA, dist_comm C Z, hZC] at hlc
    apply angle_of_cos hα.le (by linarith)
    have e : (2 * k ^ 2 * b * c) * (Real.cos (∠ C A Z) - Real.cos α) = 0 := by
      linear_combination hlc - (k : ℝ) ^ 2 * ca
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by positivity))
  -- the triangle `ZAB`
  have h0 : InnerProductGeometry.angle (B - A) (C - A) = 2 * α := by
    rw [← hshape.1, angleAt_eq]; rfl
  have hB' : InnerProductGeometry.angle (C - B) (A - B) = β := by
    rw [← hshape.2.1, angleAt_eq]; rfl
  obtain ⟨nZ, aZ, aA, aB, hCμ, hZnd, hsep⟩ :=
    zab_facts (Z := Z) hs rfl nA h0 hB' hAZC hCAZ
  obtain ⟨T', hT'p⟩ : ∃ T' : Tri, T'.pts = ![Z, A, B] :=
    ⟨⟨_, affineIndependent_of_cross' Z A B nZ⟩, rfl⟩
  -- the quadratic tiling of `ZCA`
  obtain ⟨K, hKk⟩ : ∃ K : ℕ, (K : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hK : 0 < K := by omega
  have hKr : (K : ℝ) = k := by exact_mod_cast hKk
  have hnd : cross (Z - C) (A - C) ≠ 0 := by
    rw [show Z - C = s • (C - B) by simp [Z], cross_smul_left, cross_swap,
      show C - B = -(B - C) by abel, cross_neg_right, neg_neg]
    exact mul_ne_zero hs.ne' nC
  obtain ⟨E, hE, hEt⟩ := ladder_tri hT hK (by rw [hKr]; exact hZC) (by rw [hKr]; exact hCA)
    (by rw [hKr]; exact hZA) hnd
  -- glued along `AC`
  have hD : T.carrier = convexHull ℝ {A, B, C} := by unfold Tri.carrier; rw [range_pts]
  have hT' : T'.carrier = convexHull ℝ {Z, A, B} := by unfold Tri.carrier; rw [hT'p, range_three]
  obtain ⟨D', htgt, hmod⟩ := glue_tri D E hE hD hEt (by positivity)
    (by rw [div_le_one (by linarith)]; linarith) hCμ hZnd hsep T' hT'
  have hTD' : ThreeAlpha.TileSides D' α β γ a b c := by
    unfold ThreeAlpha.TileSides; rw [hmod]; exact hT
  have hshape' : D'.target.angleAt 0 = β ∧ D'.target.angleAt 1 = 3 * α ∧
      D'.target.angleAt 2 = β := by
    rw [htgt, angleAt_eq, angleAt_eq, angleAt_eq, hT'p]
    exact ⟨aZ, aA, aB⟩
  apply isobetaone hTD' hrel hirr hm hmk hcop ha hb hc hshape'
  push_cast
  rw [hN, hKr]; ring

end TriangleTiling.Prime
