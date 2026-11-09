/-
`theorem:decidable` of M. Beeson, *Tiling an equilateral triangle* (arXiv 1811.09723): given `N`,
the tiles `(α, β, π/3)`, `α ∉ ℚπ`, that can `N`-tile an equilateral triangle lie, up to scaling, in
an explicit finite set of at most `√N` integer tiles.

Statement checked by Beeson. The proof is the paper's (revised 2026-11-07): by
`theorem:equilateral3` the coloring number `M` satisfies `0 < M`, `M² < N`, and `(N, M)` determine
`a/c, b/c` up to order; they are rational by `lemma:square60`, so `(N, M)` determine the sides as
integers with no common factor (`tileInt`, computed as in the paper's appendix code). The
triangle `ABC` is scaled to fit: the tile is a positive multiple `μ` of a tile in `S`, with `a, b`
possibly swapped (swapping `α, β`).
-/
import TriangleTiling.Laczkovich.EquilateralSixty

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha

/-- The tile of coloring number `M` as integers with no common factor, as in the paper's appendix
code: `A = 3N + M² - r`, `B = 3N + M² + r`, `C = 2(3N - M²)` with `r = √((9N - M²)(N - M²))`, each
divided by `gcd(A, B, C)`. -/
def tileInt (N M : ℕ) : ℕ × ℕ × ℕ :=
  let r := Nat.sqrt ((9 * N - M ^ 2) * (N - M ^ 2))
  let A := 3 * N + M ^ 2 - r
  let B := 3 * N + M ^ 2 + r
  let C := 2 * (3 * N - M ^ 2)
  let g := Nat.gcd (Nat.gcd A B) C
  (A / g, B / g, C / g)

/-- Dividing by the gcd leaves no common factor. -/
theorem gcd_div3 (A B C : ℕ) (hC : 0 < C) :
    Nat.gcd (Nat.gcd (A / Nat.gcd (Nat.gcd A B) C) (B / Nat.gcd (Nat.gcd A B) C))
      (C / Nat.gcd (Nat.gcd A B) C) = 1 := by
  have hg : 0 < Nat.gcd (Nat.gcd A B) C := Nat.gcd_pos_of_pos_right _ hC
  have hgAB : Nat.gcd (Nat.gcd A B) C ∣ Nat.gcd A B := Nat.gcd_dvd_left _ _
  rw [Nat.gcd_div (hgAB.trans (Nat.gcd_dvd_left _ _)) (hgAB.trans (Nat.gcd_dvd_right _ _)),
    Nat.gcd_div hgAB (Nat.gcd_dvd_right _ _), Nat.div_self hg]

/-- **Theorem `theorem:decidable`.** Given `N`, there is a finite set `S` of not more than `√N`
tiles such that, if any tile with angles `(α, β, π/3)` and `α` not a rational multiple of `π` can
`N`-tile an equilateral triangle, then one of the tiles in `S` can do so.

The tiles of `S` are integer triples `(A, B, C)` with no common factor; "one of the tiles in `S`
can do so" is read as: the tile used is `μ (A, B, C)` for some `μ > 0` and some `(A, B, C) ∈ S`,
with `a, b` possibly swapped. -/
theorem decidable (N : ℕ) :
    ∃ S : Finset (ℕ × ℕ × ℕ), (S.card : ℝ) ≤ Real.sqrt N ∧
      (∀ t ∈ S, Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1) ∧
      ∀ (D : CongruentDissection N) {α β a b c : ℝ}, (∀ k, D.target.angleAt k = Real.pi / 3) →
        TileSides D α β (Real.pi / 3) a b c → IrrPi α →
        ∃ t ∈ S, ∃ μ : ℝ, 0 < μ ∧
          ((a = μ * t.1 ∧ b = μ * t.2.1 ∧ c = μ * t.2.2) ∨
            (b = μ * t.1 ∧ a = μ * t.2.1 ∧ c = μ * t.2.2)) := by
  refine ⟨(Finset.Icc 1 (Nat.sqrt N)).image (tileInt N), ?_, ?_, ?_⟩
  · calc (((Finset.Icc 1 (Nat.sqrt N)).image (tileInt N)).card : ℝ)
          ≤ ((Finset.Icc 1 (Nat.sqrt N)).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = Nat.sqrt N := by simp
      _ ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  · intro t ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    have hm' := Finset.mem_Icc.mp hm
    have hmN : m ^ 2 ≤ N := Nat.le_sqrt'.mp hm'.2
    have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm'.1
    have hC : 0 < 2 * (3 * N - m ^ 2) := by
      have : m ^ 2 < 3 * N := by linarith
      have := Nat.sub_pos_of_lt this
      omega
    exact gcd_div3 _ _ _ hC
  intro D α β a b c hP hT hα
  have hβ := irr_beta_of_alpha D hT hα
  obtain ⟨-, -, hS, -, -, -, -, pa, pb, pc, -⟩ := sixty_setup D hP hT hβ
  obtain ⟨i₀, hi₀⟩ := exists_atA_onAB D
  obtain ⟨ε, hε, h1⟩ := exists_colouring D hα hS i₀
  have hMpos := M_pos D hP hT hβ hε hi₀ h1
  obtain ⟨hMN, hd, -, -, hform⟩ := sixty_main D hP hT hβ hε hi₀ h1
  obtain ⟨-, -, hsq⟩ := square60 D hP hT hα hε hi₀ h1
  set Mi := ∑ i, ε i with hMi
  -- the coloring number as a natural number `m ∈ [1, ⌊√N⌋]`
  obtain ⟨m, hmM⟩ : ∃ m : ℕ, (m : ℤ) = Mi := ⟨Mi.toNat, Int.toNat_of_nonneg hMpos.le⟩
  have hmR : ((m : ℕ) : ℝ) = (Mi : ℝ) := by exact_mod_cast hmM
  have hm1 : 1 ≤ m := by omega
  have hmN2 : m ^ 2 < N := by
    have : ((m ^ 2 : ℕ) : ℝ) < N := by push_cast; rw [hmR]; exact hMN
    exact_mod_cast this
  have hmle : m ≤ Nat.sqrt N := Nat.le_sqrt'.mpr hmN2.le
  refine ⟨tileInt N m, Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hm1, hmle⟩), ?_⟩
  have hMr : (0 : ℝ) < Mi := by exact_mod_cast hMpos
  have hNr : (0 : ℝ) < N := by nlinarith
  -- the integer square root `r` (`lemma:square60`)
  have h9 : m ^ 2 ≤ 9 * N := by linarith
  have h3 : m ^ 2 ≤ 3 * N := by linarith
  obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (9 * N - m ^ 2) * (N - m ^ 2) := ⟨_, rfl⟩
  have hxR : (x : ℝ) = (9 * N - (Mi : ℝ) ^ 2) * (N - (Mi : ℝ) ^ 2) := by
    rw [hx, Nat.cast_mul, Nat.cast_sub h9, Nat.cast_sub hmN2.le]; push_cast; rw [hmR]
  obtain ⟨k, hk⟩ := hsq
  have hxk : x = k.natAbs * k.natAbs := by
    have e1 : ((x : ℕ) : ℤ) = k * k := by
      rw [← hk, hx, Nat.cast_mul, Nat.cast_sub h9, Nat.cast_sub hmN2.le]; push_cast; rw [hmM]
    have e2 : ((k.natAbs * k.natAbs : ℕ) : ℤ) = k * k := Int.natAbs_mul_self
    exact_mod_cast e1.trans e2.symm
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = Nat.sqrt ((9 * N - m ^ 2) * (N - m ^ 2)) := ⟨_, rfl⟩
  have hrr : r * r = x := by rw [hr, ← hx, hxk, Nat.sqrt_eq]
  have hr2 : (r : ℝ) * r = (9 * N - (Mi : ℝ) ^ 2) * (N - (Mi : ℝ) ^ 2) := by
    rw [← hxR, ← hrr]; push_cast; ring
  have hrR : Real.sqrt ((9 * N - (Mi : ℝ) ^ 2) * (N - (Mi : ℝ) ^ 2)) = r := by
    rw [← hr2]; exact Real.sqrt_mul_self (Nat.cast_nonneg _)
  rw [hrR] at hform
  -- `A, B, C` and their gcd `g`
  have hnumR : ((3 * N + m ^ 2 : ℕ) : ℝ) = 3 * N + (Mi : ℝ) ^ 2 := by push_cast; rw [hmR]
  have hdenR : ((3 * N - m ^ 2 : ℕ) : ℝ) = 3 * N - (Mi : ℝ) ^ 2 := by
    rw [Nat.cast_sub h3]; push_cast; rw [hmR]
  have hrnum : r ≤ 3 * N + m ^ 2 := by
    have : (r : ℝ) ≤ ((3 * N + m ^ 2 : ℕ) : ℝ) := by
      rw [hnumR]
      by_contra h
      push Not at h
      have h0 : (0 : ℝ) ≤ 3 * N + (Mi : ℝ) ^ 2 := by positivity
      nlinarith [mul_pos (mul_pos hMr hMr) hNr]
    exact_mod_cast this
  have hden0 : 0 < 3 * N - m ^ 2 := Nat.sub_pos_of_lt (by linarith)
  set g := Nat.gcd (Nat.gcd (3 * N + m ^ 2 - r) (3 * N + m ^ 2 + r)) (2 * (3 * N - m ^ 2)) with hg
  have ht : tileInt N m = ((3 * N + m ^ 2 - r) / g, (3 * N + m ^ 2 + r) / g,
      (2 * (3 * N - m ^ 2)) / g) := by
    simp only [tileInt, hg, hr]
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  have hgAB : g ∣ Nat.gcd (3 * N + m ^ 2 - r) (3 * N + m ^ 2 + r) := Nat.gcd_dvd_left _ _
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hAR : (((3 * N + m ^ 2 - r) / g : ℕ) : ℝ) = (3 * N + (Mi : ℝ) ^ 2 - r) / g := by
    rw [Nat.cast_div (hgAB.trans (Nat.gcd_dvd_left _ _)) hgR, Nat.cast_sub hrnum, hnumR]
  have hBR : (((3 * N + m ^ 2 + r) / g : ℕ) : ℝ) = (3 * N + (Mi : ℝ) ^ 2 + r) / g := by
    rw [Nat.cast_div (hgAB.trans (Nat.gcd_dvd_right _ _)) hgR, Nat.cast_add, hnumR]
  have hCR : (((2 * (3 * N - m ^ 2)) / g : ℕ) : ℝ) = 2 * (3 * N - (Mi : ℝ) ^ 2) / g := by
    rw [Nat.cast_div (Nat.gcd_dvd_right _ _) hgR, Nat.cast_mul, hdenR]; push_cast; ring
  -- the scale `μ = c g / (2(3N - M²))`
  have hd' : (3 * N - (Mi : ℝ) ^ 2) ≠ 0 := hd.ne'
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg0
  have e : ∀ v : ℝ, c * g / (2 * (3 * N - (Mi : ℝ) ^ 2)) * (v / g) =
      c * ((1 / 2) * (v / (3 * N - (Mi : ℝ) ^ 2))) := by
    intro v; field_simp
  have hcc : ∀ y : ℝ, y = c * (y / c) := fun y => by field_simp
  refine ⟨c * g / (2 * (3 * N - (Mi : ℝ) ^ 2)), by positivity, ?_⟩
  rw [ht]
  simp only
  rw [hAR, hBR, hCR, e, e, show 2 * (3 * N - (Mi : ℝ) ^ 2) / g = (2 * (3 * N - (Mi : ℝ) ^ 2)) / g
    from rfl, e, add_div, sub_div]
  have hc' : c = c * ((1 / 2) * (2 * (3 * N - (Mi : ℝ) ^ 2) / (3 * N - (Mi : ℝ) ^ 2))) := by
    field_simp
  rcases hform with ⟨u1, u2⟩ | ⟨u1, u2⟩
  · right
    exact ⟨by rw [← u2]; exact hcc b, by rw [← u1]; exact hcc a, hc'⟩
  · left
    exact ⟨by rw [← u1]; exact hcc a, by rw [← u2]; exact hcc b, hc'⟩

end TriangleTiling.Equilateral
