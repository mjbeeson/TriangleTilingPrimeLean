/-
Section 12 of Beeson–Roșu: `lemma:isoscelesnob` (no `b` edges on the equal sides of `(β, β, 3α)`
when `j = 1`), and the section's setting as a `RunSetting`.
-/
import TriangleTiling.Prime.SideEdges

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Erdos634.BeesonColoring

variable {N : ℕ}

/-- **The setting of Section 12 is that of Section 11**: the shape `(β, 3α, β)` is not similar to
the tile, so by `lemma:nogammacorner` no tile has its `γ` angle at a vertex. -/
theorem isobeta_setting {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = π)
    (hirr : ¬ ∃ r : ℚ, α = r * π) (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) :
    RunSetting D α β γ a b c m k := by
  obtain ⟨hα, hβ, hγ, hsum⟩ := ThreeAlpha.tileSides_angles D hT
  have hγ' : γ = 2 * α + β := by linarith
  have hαβ : α ≠ β := by
    intro h; apply hirr; exact ⟨1 / 5, by rw [h] at hrel ⊢; push_cast; linarith⟩
  have hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β γ := by
    rw [hshape.1, hshape.2.1, hshape.2.2]
    unfold Triple3
    rintro (⟨h1, -, -⟩ | ⟨h1, -, h3⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩ | ⟨h1, -, -⟩ | ⟨h1, -, -⟩)
    · exact hαβ h1.symm
    · exact hαβ h1.symm
    · rw [hγ'] at h3; linarith
    · exact hαβ h3.symm
    · rw [hγ'] at h1; linarith
    · rw [hγ'] at h1; linarith
  exact ⟨hT, hrel, hm, hmk, hcop, ha, hb, hc, nogammacorner D hrel hirr hT hns⟩

/-- **Lemma `lemma:isoscelesnob`** (no `b` edges on sides). Suppose the isosceles triangle `ABC`
of shape `(β, β, 3α)` is `N`-tiled by `(a, b, c)` as above, with `j = 1`. Then no tiles with `b`
edges are supported on either of the two equal sides `AB` and `BC`.

"Supported on `AB`" is: the tile has an edge `PQ` (two of its vertices) contained in `AB`. -/
theorem isoscelesnob {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = π)
    (hirr : ¬ ∃ r : ℚ, α = r * π) (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    (hN : (N : ℝ) = 3 * k ^ 2 - m ^ 2) :
    ∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
      (segment ℝ P Q ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
        segment ℝ P Q ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) → dist P Q ≠ b := by
  have hS := isobeta_setting hT hrel hirr hm hmk hcop ha hb hc hshape
  obtain ⟨hBC, hX, -⟩ := isobetasides hT hrel hm hmk ha hb hc hshape (j := 1) one_pos
    (by rw [hN]; push_cast; ring)
  have hk := hS.k_pos
  -- On either equal side `S`: `kc = pa + qb + rc` with `r ≥ 1`, and `q = 0`.
  have key : ∀ j' : Fin 3, dist (D.target.pts j') (D.target.pts (j' + 1)) = (k : ℝ) ^ 3 →
      ∀ (t : Fin N) (P Q : Plane), TileEdge D t P Q →
        segment ℝ P Q ⊆ segment ℝ (D.target.pts j') (D.target.pts (j' + 1)) → dist P Q ≠ b := by
    intro j' hlen t P Q hte hsub hbq
    obtain ⟨p, q, r, hsum, hcount⟩ := hS.side_counts j'
    have hq := (hcount t P Q hte hsub).2.1 hbq
    -- a `c` edge on `S`
    obtain ⟨n, U, I, t', hn, hrun, -, -⟩ := hS.stopped_run j'
    have he0 := hrun.2.2 0 (by omega)
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, zero_add, one_mul] at he0
    have hsub0 : segment ℝ U (U + c • I) ⊆ segment ℝ (D.target.pts j') (D.target.pts (j' + 1)) :=
      Set.Subset.trans ((convex_segment _ _).segment_subset (left_mem_segment ℝ _ _)
        (by simpa using mem_seg_frac (U := U) (I := I) (c := c) (i := 1) (n := n) hn)) hrun.2.1
    have hr := (hcount _ _ _ he0 hsub0).2.2 (by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hrun.1, mul_one,
        Real.norm_of_nonneg hS.c_pos.le])
    -- the relation `(k - r) c = pa + qb`
    have hZ : (p : ℤ) * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = k * k ^ 2 := by
      have := hsum.symm.trans hlen
      rw [ha, hb, hc] at this
      have h' : (p : ℝ) * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = k * k ^ 2 := by
        linarith [this]
      exact_mod_cast h'
    have hmk2 : m ^ 2 < k ^ 2 := by nlinarith
    have hbpos : 0 < k ^ 2 - m ^ 2 := by linarith
    have hrk : (r : ℤ) < k := by
      by_contra hge; push Not at hge
      have : (q : ℤ) * (k ^ 2 - m ^ 2) > 0 := by
        have : (0 : ℤ) < q := by exact_mod_cast hq
        positivity
      have : (r : ℤ) * k ^ 2 ≥ k * k ^ 2 := by nlinarith
      nlinarith [Int.natCast_nonneg p, mul_nonneg (Int.natCast_nonneg p) (mul_pos hS.hm hk).le]
    have hh : (1 : ℤ) ≤ k - r := by omega
    have hrel' : (k - r) * k ^ 2 = p * (m * k) + q * (k ^ 2 - m ^ 2) := by linarith
    obtain ⟨-, -, -, -, -, -, ⟨-, hpq⟩, -, ⟨-, hqb⟩⟩ := minlengths hS.hm hS.hmk hS.cop
    have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
    rcases Nat.eq_zero_or_pos p with hp | hp
    · -- `hc = qb`: at least `bc > kc`
      rw [hp] at hrel'
      have := hqb (k - r) q hh (by positivity) (by rw [hrel']; ring)
      have hkb : k < k ^ 2 - m ^ 2 := by nlinarith
      nlinarith
    · -- `hc = pa + qb`: at least `kc`
      have := hpq (k - r) p q hh (by exact_mod_cast hp) (by exact_mod_cast hq) hrel'
      nlinarith
  intro t P Q hte hside
  rcases hside with hs | hs
  · exact key 0 (by rw [show (0 : Fin 3) + 1 = 1 from rfl, hX]; push_cast; ring) t P Q hte hs
  · exact key 1 (by rw [show (1 : Fin 3) + 1 = 2 from rfl, hBC, hX]; push_cast; ring) t P Q hte hs

end TriangleTiling.Prime
