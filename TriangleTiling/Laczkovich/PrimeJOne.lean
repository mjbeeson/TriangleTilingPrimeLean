/-
The step "`N` prime forces `j = 1`" in the proof of `theorem:prime634` of M. Beeson and E. Roșu,
*Tiling a triangle into a prime number of congruent triangles* (Section 14), for the two Group 1
shapes left open by `TriangleTiling3`: the triquadratic shape `(2α, β, α + β)` and the
isosceles-`β` shape `(β, 3α, β)`.

The printed proof: "the remaining two are the triquadratic and isosceles-`β` shapes, where `N`
prime forces `j = 1`, excluded for the isosceles-`β` shape by `theorem:isoscelesbeta`, and hence for
the triquadratic shape by `theorem:triquadratic`." Here:
* the tile is rational (`TriangleTiling3` `theorem:rationaltile`), so with `a/c = m/k` in lowest
  terms it is `τ(mk, k² - m², k²)` (as in `lemma:gsquare`);
* `N = j²(2k² - m²)` (`TriangleTiling3` `corollary:tqparameters`), resp. `N = j²(3k² - m²)`
  (`TriangleTiling3` `theorem:notprime4`), so `N` prime gives `j = 1`;
* scaling the tiling by `1/τ` gives the tile `(mk, k² - m², k²)` of the `j = 1` parts
  (`triquadone`, `isobetaone`).

The theorems as printed are `isoscelesbeta` and `triquadratic` here: `N = j²(…)` with `j > 1`, so `N`
is neither prime nor squarefree. `triqprime` and `isobetaprime` are their prime cases, used in
`prime634`. Statements checked by Beeson.
-/
import TriangleTiling.Laczkovich.ThreeAlphaTilingEq
import TriangleTiling.Laczkovich.ThreeAlphaIsoBeta
import TriangleTiling.Laczkovich.ThreeAlphaScaling
import TriangleTiling.Prime.IsoBetaMain
import TriangleTiling.Prime.TriquadMain

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.ThreeAlpha

variable {N : ℕ}

/-- The tile of a tiling not similar to `ABC`, with `3α + 2β = π`, is `τ(mk, k² - m², k²)` with
`gcd(m, k) = 1` and `0 < m < k`. -/
theorem tile_params (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ m k : ℕ, Nat.Coprime m k ∧ 0 < m ∧ m < k ∧
      a = τ * (m * k) ∧ b = τ * (k ^ 2 - m ^ 2) ∧ c = τ * k ^ 2 := by
  obtain ⟨⟨q, hq⟩, -, -⟩ := TriangleTiling.ThreeAlpha.rationaltile D hrel hT hns
  obtain ⟨-, -, -, -, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  set t := 2 * Real.cos (α + β)
  have hqt : (q : ℝ) = t := by rw [← hq, ha]; field_simp
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (hqt ▸ ht0)
  have hn0 : 0 < q.num := Rat.num_pos.mpr hq0
  set m := q.num.toNat
  set k := q.den
  have hmn : (m : ℤ) = q.num := Int.toNat_of_nonneg hn0.le
  have hk0 : (0 : ℝ) < k := by exact_mod_cast q.den_pos
  have htmk : t = m / k := by
    rw [← hqt, Rat.cast_def]
    congr 1
    rw [← hmn]; push_cast; rfl
  have hm0 : 0 < m := by omega
  have hmk : m < k := by
    have : (m : ℝ) / k < 1 := htmk ▸ ht1
    rw [div_lt_one hk0] at this
    exact_mod_cast this
  have hcop : Nat.Coprime m k := by
    have h := q.reduced
    have : q.num.natAbs = m := by omega
    rwa [this] at h
  refine ⟨c / k ^ 2, by positivity, m, k, hcop, hm0, hmk, ?_, ?_, ?_⟩
  · rw [ha, htmk]; field_simp
  · rw [hb, htmk]; field_simp
  · field_simp

/-- The tile and the angles of `ABC` after scaling by `κ > 0`. -/
theorem tileSides_scale (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) :
    TileSides (scaleDissection D hκ) α β γ (κ * a) (κ * b) (κ * c) := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [scaleDissection, scale_angleAt, scale_oppLen _ hκ, *]

theorem scale_target_angleAt (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ) (j : Fin 3) :
    (scaleDissection D hκ).target.angleAt j = D.target.angleAt j :=
  scale_angleAt D.target hκ.ne' j

theorem similar_of_scale (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ)
    (h : SimilarTM (scaleDissection D hκ)) : SimilarTM D := by
  obtain ⟨μ, τ, hτ⟩ := h
  refine ⟨μ, τ, fun j => ?_⟩
  obtain ⟨e1, e2⟩ := hτ j
  change (scaleTri D.target κ hκ.ne').angleAt j = (scaleTri D.model κ hκ.ne').angleAt (τ j) at e1
  change (scaleTri D.target κ hκ.ne').oppLen j = μ * (scaleTri D.model κ hκ.ne').oppLen (τ j) at e2
  rw [scale_angleAt, scale_angleAt] at e1
  rw [scale_oppLen _ hκ, scale_oppLen _ hκ] at e2
  refine ⟨e1, ?_⟩
  have : κ * (D.target.oppLen j - μ * D.model.oppLen (τ j)) = 0 := by linear_combination e2
  linarith [(mul_eq_zero.mp this).resolve_left hκ.ne']

/-- The tile `τ(mk, k² - m², k²)` scaled by `1/τ`. -/
theorem tileSides_unscale (D : CongruentDissection N) {τ : ℝ} (hτ : 0 < τ) {α β γ a b c : ℝ}
    {m k : ℕ} (hT : TileSides D α β γ a b c) (ha : a = τ * (m * k))
    (hb : b = τ * (k ^ 2 - m ^ 2)) (hc : c = τ * k ^ 2) :
    TileSides (scaleDissection D (inv_pos.mpr hτ)) α β γ (m * k) (k ^ 2 - m ^ 2) (k ^ 2) := by
  have h := tileSides_scale D (inv_pos.mpr hτ) hT
  rw [ha, hb, hc, inv_mul_cancel_left₀ hτ.ne', inv_mul_cancel_left₀ hτ.ne',
    inv_mul_cancel_left₀ hτ.ne'] at h
  exact h

/-- If `N = j² f` is prime, then `j² = 1`. -/
theorem sq_eq_one_of_prime {j f : ℤ} (hN : N.Prime) (h : (N : ℤ) = j ^ 2 * f) : j ^ 2 = 1 := by
  have hd : (j.natAbs ^ 2 : ℤ) ∣ (N : ℤ) := ⟨f, by rw [h, Int.natAbs_sq]⟩
  have hd' : j.natAbs ^ 2 ∣ N := by exact_mod_cast hd
  have h1 : j.natAbs ∣ N := (dvd_pow_self _ two_ne_zero).trans hd'
  rcases (Nat.dvd_prime hN).mp h1 with e | e
  · rw [← Int.natAbs_sq, e]; norm_num
  · exfalso
    rw [e] at hd'
    have := Nat.le_of_dvd hN.pos hd'
    have h2 := hN.two_le
    nlinarith

/-- `gcd(mk, k² - m², k²) = 1` when `gcd(m, k) = 1` and `m < k`. -/
theorem gcd_params {m k : ℕ} (hmk : Nat.Coprime m k) (hlt : m < k) :
    Nat.gcd (Nat.gcd (m * k) (k ^ 2 - m ^ 2)) (k ^ 2) = 1 := by
  have hle : m ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hlt.le 2
  show Nat.Coprime _ _
  apply Nat.Coprime.pow_right
  apply Nat.coprime_of_dvd
  intro p hp hpd hpk
  have h2 : p ∣ k ^ 2 - m ^ 2 := hpd.trans (Nat.gcd_dvd_right _ _)
  have h3 : p ∣ k ^ 2 := dvd_pow hpk two_ne_zero
  have h4 : p ∣ m ^ 2 := by
    have := Nat.dvd_sub h3 h2
    rwa [Nat.sub_sub_self hle] at this
  have h5 := Nat.dvd_gcd (hp.dvd_of_dvd_pow h4) hpk
  rw [Nat.Coprime.gcd_eq_one hmk] at h5
  exact hp.not_dvd_one h5

/-- `N = j² f` with `|j| > 1` is not squarefree. -/
theorem not_squarefree_of {j f : ℤ} (h : (N : ℤ) = j ^ 2 * f) (hj : 1 < j.natAbs) :
    ¬ Squarefree N := by
  intro hsq
  have hd : ((j.natAbs * j.natAbs : ℕ) : ℤ) ∣ (N : ℤ) :=
    ⟨f, by rw [h]; push_cast; rw [abs_mul_abs_self, sq]⟩
  have := hsq _ (Int.natCast_dvd_natCast.mp hd)
  rw [Nat.isUnit_iff] at this
  omega

/-- The angles of the target are those of `T` in some order, so they sum to `π`. -/
theorem tgt_sum {x y z : ℝ} {D : CongruentDissection N} (h : TgtAngles D x y z) :
    x + y + z = Real.pi := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  have hs := Erdos634.Draft.LaczFormal.angleAt_sum D.target
  have e := Equiv.sum_comp σ (fun i => D.target.angleAt i)
  simp only [Fin.sum_univ_three] at e
  linarith

/-- **Theorem `theorem:isoscelesbeta`.** There is no `j = 1` tiling of the isosceles-`β` triangle
when `3α + 2β = π` with `α` not a rational multiple of `π`. In particular, the number of tiles `N`
cannot be prime, or even squarefree.

Here `T = D.target` has angles `(β, 3α, β)` and the tile has angles `(α, β, γ)` with opposite sides
`(a, b, c)`. "No `j = 1` tiling" is: `N = j²(3k² - m²)` with `j > 1`, where the tile is
`(a, b, c) = τ(mk, k² - m², k²)`, `gcd(m, k) = 1`, `0 < m < k` (`TriangleTiling3` Theorem 19). -/
theorem isoscelesbeta (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hshape : TgtAngles D β (3 * α) β) :
    ¬ N.Prime ∧ ¬ Squarefree N ∧ ∃ j m k : ℕ, 1 < j ∧ Nat.Coprime m k ∧ 0 < m ∧ m < k ∧
      (N : ℤ) = j ^ 2 * (3 * k ^ 2 - m ^ 2) ∧
      ∃ τ : ℝ, 0 < τ ∧ a = τ * (m * k) ∧ b = τ * (k ^ 2 - m ^ 2) ∧ c = τ * k ^ 2 := by
  have hns : ¬ SimilarTM D := by
    intro hs
    obtain ⟨hα, -, -, hsum⟩ := TriangleTiling.ThreeAlpha.tileSides_angles D hT
    obtain ⟨σ, -, h1, -⟩ := hshape
    rcases angles_of_similar D hT hs (σ 1) with e | e | e <;> rw [h1] at e
    · linarith
    · exact hirr ⟨1 / 9, by push_cast; linarith⟩
    · exact hirr ⟨1 / 5, by push_cast; linarith⟩
  obtain ⟨D', hm, hns', -, e0, e1, e2⟩ := normalize D hshape hns
  have hT' := tileSides_of_model D hm hT
  obtain ⟨τ, hτ, m, k, hmk, hm0, hlt, ha, hb, hc⟩ := tile_params D' hrel hT' hns'
  set D'' := scaleDissection D' (inv_pos.mpr hτ)
  have hT'' : TileSides D'' α β γ (m * k) (k ^ 2 - m ^ 2) (k ^ 2) :=
    tileSides_unscale D' hτ hT' ha hb hc
  have hns'' : ¬ SimilarTM D'' := fun h => hns' (similar_of_scale D' _ h)
  have hs := scale_target_angleAt D' (inv_pos.mpr hτ)
  have hshape'' : D''.target.angleAt 0 = β ∧ D''.target.angleAt 1 = 3 * α ∧
      D''.target.angleAt 2 = β := ⟨by rw [hs]; exact e0, by rw [hs]; exact e1, by rw [hs]; exact e2⟩
  have hTA : TileAngles D'' α β γ := by
    obtain ⟨σ, g0, g1, g2, -⟩ := hT''; exact ⟨σ, g0, g1, g2⟩
  have hle : m ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hlt.le 2
  have hbN : ((k ^ 2 - m ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
    rw [Nat.cast_sub hle]; push_cast; ring
  have hTn : TileSides D'' α β γ ((m * k : ℕ) : ℝ) ((k ^ 2 - m ^ 2 : ℕ) : ℝ) ((k ^ 2 : ℕ) : ℝ) := by
    rw [hbN]; push_cast; exact hT''
  obtain ⟨i₀, hAB⟩ := exists_atB_onAB D''
  have hi₀ : TileAt D'' 1 i₀ := by
    obtain ⟨l, -, -, hl, -⟩ := hAB
    exact ⟨l, hl⟩
  obtain ⟨ε, hε, hεi⟩ := signedtiles D'' hrel hTA hns'' hi₀
  have hk0 : 0 < k := by omega
  have te := notprime4 D'' hrel hTn hns'' hshape'' ⟨rfl, rfl, rfl⟩ (gcd_params hmk hlt) hε hAB
    hεi hmk hk0 (by push_cast; field_simp)
  dsimp only at te
  obtain ⟨-, j, hj0, -, hNj, -, hsq⟩ := te
  -- `j = 1` is excluded (the `j = 1` part, `isobetaone`)
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [one_pow, one_mul] at hNj
    refine isobetaone hT'' hrel hirr (m := m) (k := k) (by exact_mod_cast hm0)
      (by exact_mod_cast hlt) (Nat.isCoprime_iff_coprime.mpr hmk) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) hshape'' ?_
    have : ((N : ℤ) : ℝ) = ((3 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2 : ℤ) : ℝ) := by rw [hNj]
    push_cast at this ⊢
    exact this
  have hsq' : ¬ Squarefree N := fun h => hj1 (hsq h)
  have hjn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0.le
  refine ⟨fun hp => hsq' (Irreducible.squarefree hp), hsq', j.toNat, m, k, by omega, hmk, hm0,
    hlt, by rw [hjn]; exact hNj, τ, hτ, ha, hb, hc⟩

/-- **Theorem `theorem:triquadratic`** (`j > 1`). Let triangle `T` have angles `(2α, β, α + β)`,
and suppose `T` is `N`-tiled by a tile with `(α, β, γ)`, and `α` not a rational multiple of `π`.
Then `N` is not prime, indeed `N` is not even squarefree. In fact, `N = j²(2k² - m²)`, where
`j > 1` and `(a, b, c) = (mk, k² - m², k²)`.

Here `T = D.target`, the tile has angles `(α, β, γ)` with opposite sides `(a, b, c)`, and
`(a, b, c) = (mk, k² - m², k²)` is up to the scale `τ`, with `gcd(m, k) = 1`, `0 < m < k`. -/
theorem triquadratic (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β)) (hirr : IrrPi α) :
    ¬ N.Prime ∧ ¬ Squarefree N ∧ ∃ j m k : ℕ, 1 < j ∧ Nat.Coprime m k ∧ 0 < m ∧ m < k ∧
      (N : ℤ) = j ^ 2 * (2 * k ^ 2 - m ^ 2) ∧
      ∃ τ : ℝ, 0 < τ ∧ a = τ * (m * k) ∧ b = τ * (k ^ 2 - m ^ 2) ∧ c = τ * k ^ 2 := by
  have hrel : 3 * α + 2 * β = Real.pi := by have := tgt_sum hshape; linarith
  have hns : ¬ SimilarTM D := by
    obtain ⟨σ, -, -, h2⟩ := hshape
    exact not_similar_of_alpha_beta D hrel hT h2
  obtain ⟨D', hm, hns', hccw, e0, e1, e2⟩ := normalize D hshape hns
  have hT' := tileSides_of_model D hm hT
  obtain ⟨τ, hτ, m, k, hmk, hm0, hlt, ha, hb, hc⟩ := tile_params D' hrel hT' hns'
  obtain ⟨-, -, -, M₁, M₂, -, -, -, -, -, -, h₁, h₂⟩ := Mdef D' hrel hT' hns'
  obtain ⟨-, hNj, -⟩ := tqparameters D' hrel hT' hns' hccw h₁ h₂ ⟨e0, e1, e2⟩ hτ hmk hlt ha hb hc
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, (N : ℤ) = J ^ 2 * (2 * k ^ 2 - m ^ 2) := ⟨_, hNj⟩
  -- `j = ±1` is excluded (the `j = 1` part, `triquadone`)
  have hJ1 : J ^ 2 ≠ 1 := by
    intro hj
    rw [hj, one_mul] at hJ
    have hT'' := tileSides_unscale D' hτ hT' ha hb hc
    have hs := scale_target_angleAt D' (inv_pos.mpr hτ)
    refine triquadone hT'' hrel hirr (m := m) (k := k) (by exact_mod_cast hm0)
      (by exact_mod_cast hlt) (Nat.isCoprime_iff_coprime.mpr hmk) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) ⟨by rw [hs]; exact e0, by rw [hs]; exact e1,
        by rw [hs]; exact e2⟩ ?_
    have : ((N : ℤ) : ℝ) = ((2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2 : ℤ) : ℝ) := by rw [hJ]
    push_cast at this ⊢
    exact this
  have hJ0 : J ≠ 0 := by
    rintro rfl
    have := D.toDissection.pos
    simp at hJ
    omega
  have hj1 : 1 < J.natAbs := by
    have h0 : J.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hJ0
    have h1 : J.natAbs ≠ 1 := fun h => hJ1 (by rw [← Int.natAbs_sq, h]; norm_num)
    omega
  have hsq := not_squarefree_of hJ hj1
  refine ⟨fun hp => hsq (Irreducible.squarefree hp), hsq, J.natAbs, m, k, hj1, hmk, hm0, hlt,
    by rw [Int.natAbs_sq]; exact hJ, τ, hτ, ha, hb, hc⟩

/-- **`N` prime is excluded, the triquadratic shape** (`theorem:triquadratic`). If `ABC` with angles
`(2α, β, α + β)` (`3α + 2β = π`) is `N`-tiled by a tile with angles `(α, β, γ)`, then `N` is not
prime. -/
theorem triqprime (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c)
    (hshape : TgtAngles D (2 * α) β (α + β)) : ¬ N.Prime := by
  have hns : ¬ SimilarTM D := by
    obtain ⟨σ, -, -, h2⟩ := hshape
    exact not_similar_of_alpha_beta D hrel hT h2
  have hTA : TileAngles D α β γ := by obtain ⟨σ, g0, g1, g2, -⟩ := hT; exact ⟨σ, g0, g1, g2⟩
  exact (triquadratic D hT hshape (TriangleTiling.ThreeAlpha.angles D hrel hTA hns).1).1

/-- **`N` prime is excluded, the isosceles-`β` shape** (`theorem:isoscelesbeta`). If `ABC` with
angles `(β, 3α, β)` (`3α + 2β = π`) is `N`-tiled by a tile with angles `(α, β, γ)`, not similar to
`ABC`, then `N` is not prime. -/
theorem isobetaprime (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : TgtAngles D β (3 * α) β) : ¬ N.Prime := by
  have hTA : TileAngles D α β γ := by obtain ⟨σ, g0, g1, g2, -⟩ := hT; exact ⟨σ, g0, g1, g2⟩
  exact (isoscelesbeta D hT hrel (TriangleTiling.ThreeAlpha.angles D hrel hTA hns).1 hshape).1

end TriangleTiling.Prime
