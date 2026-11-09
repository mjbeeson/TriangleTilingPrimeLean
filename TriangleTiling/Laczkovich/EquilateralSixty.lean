/-
A tile with an angle `γ = π/3` and `α/π` irrational (M. Beeson, *Tiling an equilateral triangle*,
arXiv 1811.09723): `theorem:equilateral3`, `lemma:ab`, `lemma:square60`, `theorem:notprime60`,
`theorem:comparison`.

Statements checked by Beeson. `M` is the coloring number: the sum of any proper coloring
of the tiles by `±1` with the tile at `A` (with an edge on `AB`) colored `+1` (`coloring_equation`;
such a coloring is the paper's path coloring `pathColour`).
The tile is given by `TileSides D α β (π/3) a b c` (angles `α, β, π/3` opposite `a, b, c`).
-/
import TriangleTiling.Laczkovich.EquilateralColoring
import TriangleTiling.Equilateral.SixtyAlg
import TriangleTiling.ThreeAlpha.Components
import Erdos634.Draft.LaczFormalThm33iii3
import TriangleTiling.Equilateral.NotPrime60Core

namespace TriangleTiling.Equilateral

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha

variable {N : ℕ} (D : CongruentDissection N)

/-- The facts used throughout: `β = 2π/3 - α`, `α ∉ ℚπ`, the tile is a `π/3` placement, the law of
cosines `c² = a² + b² - ab`, the area equation `X² = Nab`, the law of sines, and `a ≠ b`. -/
theorem sixty_setup {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hβ : IrrPi β) :
    β = 2 * Real.pi / 3 - α ∧ IrrPi α ∧ D.model.SixtyData α a b c ∧
      c ^ 2 = a ^ 2 + b ^ 2 - a * b ∧ D.target.oppLen 0 ^ 2 = N * a * b ∧
      D.target.oppLen 1 = D.target.oppLen 0 ∧ D.target.oppLen 2 = D.target.oppLen 0 ∧
      0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧
      a * Real.sin (Real.pi / 3) = c * Real.sin α ∧ b * Real.sin (Real.pi / 3) = c * Real.sin β := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  have hβα : β = 2 * Real.pi / 3 - α := by rw [h0, h1, h2] at hsum; linarith
  have hα : IrrPi α := by
    rintro ⟨r, hr⟩; apply hβ; exact ⟨2 / 3 - r, by rw [hβα, hr]; push_cast; ring⟩
  have hS : D.model.SixtyData α a b c := ⟨σ, h0, l0, hβα ▸ h1, l1, h2, l2⟩
  have hcos := D.model.lawCos_perm σ
  rw [l0, l1, l2, h2, Real.cos_pi_div_three] at hcos
  have hcos' : c ^ 2 = a ^ 2 + b ^ 2 - a * b := by linarith
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα 1
    (fun k => D.model.sixty_angles_mem hα hS 1 _ k) hP
  have harea := Row5.area D σ l0 l1 l2 (κ := -1) (by norm_num) (by linarith) e1 e2
  have pa : 0 < a := l0 ▸ D.model.oppLen_pos _
  have pb : 0 < b := l1 ▸ D.model.oppLen_pos _
  have pc : 0 < c := l2 ▸ D.model.oppLen_pos _
  have hαβ : α ≠ β := by
    intro e; apply hβ; exact ⟨1 / 3, by rw [hβα] at e ⊢; push_cast; linarith⟩
  have hab := sides_ne_of_angles_ne D ⟨σ, h0, h1, h2, l0, l1, l2⟩ hαβ
  have s0 := D.model.lawSin (σ 0) (σ 2)
  have s1 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, h2, l0, l2] at s0
  rw [h1, h2, l1, l2] at s1
  refine ⟨hβα, hα, hS, hcos', by rw [harea]; try ring, e1, e2, pa, pb, pc, hab, by linarith, by linarith⟩

/-- `sixty_alg` for a tiling, with `M` the coloring number. -/
theorem sixty_main {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hβ : IrrPi β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    let M : ℝ := ((∑ i, ε i : ℤ) : ℝ)
    M ^ 2 < N ∧ 0 < 3 * N - M ^ 2 ∧
      a / c + b / c = (3 * N + M ^ 2) / (3 * N - M ^ 2) ∧
      a / c * (b / c) = 4 * M ^ 2 * N / (3 * N - M ^ 2) ^ 2 ∧
      ((a / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        b / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2))) ∨
       (a / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        b / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)))) := by
  intro M
  obtain ⟨-, hα, hS, hcos, harea, -, -, pa, pb, pc, hab, -, -⟩ := sixty_setup D hP hT hβ
  have hcol := coloring_equation D hα hS hP hε hi₀ h1
  have hX := D.target.oppLen_pos 0
  have hN : (0 : ℝ) < N := by
    have : (0 : ℝ) < N * a * b := by rw [← harea]; positivity
    by_contra h; push Not at h
    nlinarith [mul_pos pa pb]
  exact sixty_alg (x := D.target.oppLen 0 / c) (div_pos pa pc) (div_pos pb pc)
    (fun e => hab (by field_simp at e; exact e)) (by field_simp; linarith) hN (div_pos hX pc)
    (by field_simp; linarith) (by field_simp; rw [harea]; try ring)

/-- A proper coloring with the tile at `A` black exists: the paper's path coloring. -/
theorem exists_colouring {α a b c : ℝ} (hα : IrrPi α) (hS : D.model.SixtyData α a b c) (i₀ : Fin N) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ε i₀ = 1 :=
  ⟨_, pathColour_proper D hα hS i₀⟩

/-- **Theorem `theorem:coloring`.** Let the equilateral triangle `ABC` be `N`-tiled by a tile with
angles `(α, β, π/3)` and sides `(a, b, c)`, where `α` is not a rational multiple of `π`, and let `X`
be the side of `ABC`. Then the tiles can be colored black (`1`) and white (`-1`) so that any two
tiles whose boundaries share a segment of positive length have different colors, and the tile at
`A` is black. For any such coloring, let `M` be the number of black tiles minus the number of white
tiles. Then `M(a + b + c) = 3X`, and the coloring is uniquely determined once the color of one
tile is fixed.

"The tile at `A`" is a tile with a vertex at `A` and another on `AB` (`AtAOnAB`); `X` is
`|BC|`. The coloring constructed is the paper's path coloring (`pathColour`). -/
theorem coloring {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α) :
    (∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ∃ i₀, AtAOnAB D i₀ ∧ ε i₀ = 1) ∧
    (∀ (ε : Fin N → ℤ) (i₀ : Fin N), D.toDissection.ProperColouring ε → AtAOnAB D i₀ →
      ε i₀ = 1 → ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) = 3 * D.target.oppLen 0) ∧
    ∀ (ε ε' : Fin N → ℤ) (i : Fin N), D.toDissection.ProperColouring ε →
      D.toDissection.ProperColouring ε' → ε i = ε' i → ε = ε' := by
  have hβ : IrrPi β := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    have hsum : α + β + Real.pi / 3 = Real.pi := by rw [← h0, ← h1, ← h2, e, D.model.angleAt_sum]
    rintro ⟨r, hr⟩; apply hα; exact ⟨2 / 3 - r, by rw [show α = 2 * Real.pi / 3 - β by linarith, hr]; push_cast; ring⟩
  obtain ⟨-, -, hS, -⟩ := sixty_setup D hP hT hβ
  obtain ⟨i₀, hi₀⟩ := exists_atA_onAB D
  obtain ⟨ε, hε, h1⟩ := exists_colouring D hα hS i₀
  exact ⟨⟨ε, hε, i₀, hi₀, h1⟩, fun ε i₀ hε hi₀ h1 => coloring_equation D hα hS hP hε hi₀ h1,
    fun ε ε' i hε hε' hi => colouring_eq hε hε' hi⟩

/-- **Theorem `theorem:equilateral3`.** Let triangle `ABC` be equilateral. Suppose it is `N`-tiled
using a tile with angles `(α, β, π/3)`, where `β` is not a rational multiple of `π`. Let `M` be the
coloring number of the tiling. Then `N` and `M` determine the shape of the tile: `a/c` and `b/c` are
`(1/2)((3N + M²)/(3N - M²) ± √((9N - M²)(N - M²))/(3N - M²))`; and `M² < N`.

The proof is the paper's (revised 2026-11-07): the law of cosines gives `3ab = (a + b)² - c²`, the
coloring and area equations give `s = (a + b)/c = (3N + M²)/(3N - M²)`, then
`((a - b)/c)² = (9N - M²)(N - M²)/(3N - M²)²`, which is positive as `a ≠ b` (`SixtyAlg.sixty_alg`). -/
theorem equilateral3 {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hβ : IrrPi β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    let M : ℝ := ((∑ i, ε i : ℤ) : ℝ)
    ((a / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        b / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2))) ∨
       (a / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        b / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)))) ∧
      M ^ 2 < N := by
  intro M
  obtain ⟨hMN, -, -, -, hform⟩ := sixty_main D hP hT hβ hε hi₀ h1
  exact ⟨hform, hMN⟩

/-- **Lemma `lemma:ab`.** Let triangle `ABC` be equilateral. Suppose it is `N`-tiled using a tile
with angles `(α, β, π/3)`, where `α` is not a rational multiple of `π`. Let `(a, b, c)` be the sides
of the tile. Then `ab/c² = 4M²N/(3N - M²)²`. -/
theorem ab {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    let M : ℝ := ((∑ i, ε i : ℤ) : ℝ)
    a * b / c ^ 2 = 4 * M ^ 2 * N / (3 * N - M ^ 2) ^ 2 := by
  intro M
  have hβ : IrrPi β := by
    obtain ⟨σ, h0, h1', h2, -⟩ := hT
    have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
      have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
      simp only [Fin.sum_univ_three] at e
      rw [e, D.model.angleAt_sum]
    rintro ⟨r, hr⟩; apply hα
    exact ⟨2 / 3 - r, by rw [h0, h1', h2] at hsum; push_cast; linarith⟩
  obtain ⟨-, -, -, hab, -⟩ := sixty_main D hP hT hβ hε hi₀ h1
  rw [← hab]; ring

theorem irr_beta_of_alpha {α β a b c : ℝ} (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α) :
    IrrPi β := by
  obtain ⟨σ, h0, h1', h2, -⟩ := hT
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  rintro ⟨r, hr⟩; apply hα
  exact ⟨2 / 3 - r, by rw [h0, h1', h2] at hsum; push_cast; linarith⟩

/-- The coloring number is positive. -/
theorem M_pos {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hβ : IrrPi β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) : 0 < ∑ i, ε i := by
  obtain ⟨-, hα, hS, -, -, -, -, pa, pb, pc, -⟩ := sixty_setup D hP hT hβ
  have hcol := coloring_equation D hα hS hP hε hi₀ h1
  have hX := D.target.oppLen_pos 0
  have : (0 : ℝ) < ((∑ i, ε i : ℤ) : ℝ) := by
    have : 0 < ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) := by rw [hcol]; positivity
    exact pos_of_mul_pos_left this (by positivity)
  exact_mod_cast this

/-- The tile is rational (Laczkovich 2012, Theorem 3.3): `a/c` and `b/c` are rational. -/
theorem sixty_rational {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α) :
    ∃ p₁ q₁ p₂ q₂ : ℕ, 0 < p₁ ∧ 0 < p₂ ∧ a / c = (q₂ : ℝ) / p₂ ∧ b / c = (q₁ : ℝ) / p₁ := by
  have hβ := irr_beta_of_alpha D hT hα
  obtain ⟨-, -, -, -, -, -, -, -, -, pc, -, sa, sb⟩ := sixty_setup D hP hT hβ
  -- the tile is rational (Laczkovich 2012, Theorem 3.3)
  have hTA : Erdos634.Draft.LaczFormal.TileAngles D α β (Real.pi / 3) := by
    obtain ⟨σ, h0, h1', h2, -⟩ := hT; exact ⟨σ, h0, h1', h2⟩
  obtain ⟨-, ⟨p₁, q₁, hp₁, hq₁, e₁⟩, ⟨p₂, q₂, hp₂, hq₂, e₂⟩⟩ :=
    Erdos634.Draft.LaczFormal.RG.sincomm_irr_family D hP hα (Or.inl rfl) hTA
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

/-- **Lemma `lemma:square60`.** Let triangle `ABC` be equilateral. Suppose it is `N`-tiled using a
tile with angles `(α, β, π/3)`, where `α` is not a rational multiple of `π`. Then for some integer
`M < √N` (the coloring number of the tiling), `(9N - M²)(N - M²)` is a square.

`M` is the sum of any proper coloring with the tile at `A` black; also `0 < M`. -/
theorem square60 {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    let M : ℤ := ∑ i, ε i
    0 < M ∧ (M : ℝ) < Real.sqrt N ∧ IsSquare ((9 * N - M ^ 2) * (N - M ^ 2)) := by
  intro M
  have hβ := irr_beta_of_alpha D hT hα
  obtain ⟨hMN, hT3, -, -, hform⟩ := sixty_main D hP hT hβ hε hi₀ h1
  have hM0 := M_pos D hP hT hβ hε hi₀ h1
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ha, hb⟩ := sixty_rational D hP hT hα
  -- `√((9N - M²)(N - M²)) = ±(3N - M²)(a/c - b/c)` is rational, so the integer is a square
  set D₀ : ℤ := (9 * N - M ^ 2) * (N - M ^ 2)
  have hD₀ : ((D₀ : ℤ) : ℝ) = (9 * N - (M : ℝ) ^ 2) * (N - (M : ℝ) ^ 2) := by
    simp only [D₀]; push_cast; ring
  have hsq : IsSquare D₀ := by
    have hD0 : 0 ≤ D₀ := by
      have : (0 : ℝ) ≤ ((D₀ : ℤ) : ℝ) := by rw [hD₀]; nlinarith
      exact_mod_cast this
    by_contra hns
    have hirr := (irrational_sqrt_intCast_iff_of_nonneg hD0).mpr hns
    rw [hD₀] at hirr
    apply hirr
    rcases hform with ⟨u1, u2⟩ | ⟨u1, u2⟩
    · refine ⟨(3 * N - M ^ 2) * ((q₂ : ℚ) / p₂ - (q₁ : ℚ) / p₁), ?_⟩
      push_cast
      rw [← ha, ← hb, u1, u2]; field_simp; ring
    · refine ⟨-((3 * N - M ^ 2) * ((q₂ : ℚ) / p₂ - (q₁ : ℚ) / p₁)), ?_⟩
      push_cast
      rw [← ha, ← hb, u1, u2]; field_simp; ring
  exact ⟨hM0, by rw [Real.lt_sqrt hMr.le]; exact hMN, hsq⟩

/-- **Theorem `theorem:notprime60`.** Let triangle `ABC` be equilateral. Suppose it is `N`-tiled
using a tile with angles `(α, β, π/3)`, where `α` is not a rational multiple of `π`. Then `N` is
not prime.

The proof is the paper's (revised 2026-11-06): the coloring equation and the area equation, for
integer sides without a common factor, give `t = 6N/(a + b + c)` with `t(a + b - c) = 2M²` and
`t²ab = 4M²N` (`notprime60_core`); `N = 2, 3` are excluded by `lemma:square60`. -/
theorem notprime60 {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α) : ¬ N.Prime := by
  intro hNp
  have hβ := irr_beta_of_alpha D hT hα
  obtain ⟨-, -, hS, hcos, harea, -, -, pa, pb, pc, hab, -⟩ := sixty_setup D hP hT hβ
  obtain ⟨i₀, hi₀⟩ := exists_atA_onAB D
  obtain ⟨ε, hε, h1⟩ := exists_colouring D hα hS i₀
  obtain ⟨hM0, -, hsq⟩ := square60 D hP hT hα hε hi₀ h1
  obtain ⟨hMN, -⟩ := sixty_main D hP hT hβ hε hi₀ h1
  have hcol := coloring_equation D hα hS hP hε hi₀ h1
  set M : ℤ := ∑ i, ε i with hMdef
  by_cases hN5 : 5 ≤ N
  swap
  · -- `N = 2, 3`: then `M = 1` and `17`, `52` are not squares
    set D₀ : ℤ := (9 * N - M ^ 2) * (N - M ^ 2) with hD₀
    have hN4 : N ≠ 4 := by rintro rfl; exact absurd hNp (by decide)
    have hN5' : (N : ℤ) < 5 := by exact_mod_cast not_le.mp hN5
    have hN2 := hNp.two_le
    have hMN' : M ^ 2 < N := by exact_mod_cast hMN
    have hM1 : M = 1 := by nlinarith
    obtain ⟨r, hr⟩ := hsq
    simp only [D₀, hM1] at hr
    have h' : ((r.natAbs : ℤ) * r.natAbs) = r * r := Int.natAbs_mul_self' r
    have hN23 : N = 2 ∨ N = 3 := by omega
    rcases hN23 with e | e <;> rw [e] at hr <;> norm_num at hr
    · have h17 : r.natAbs * r.natAbs = 17 := by
        have : ((r.natAbs * r.natAbs : ℕ) : ℤ) = 17 := by rw [Nat.cast_mul]; linarith
        exact_mod_cast this
      have hle : r.natAbs ≤ 17 := by nlinarith
      interval_cases h : r.natAbs <;> omega
    · have h52 : r.natAbs * r.natAbs = 52 := by
        have : ((r.natAbs * r.natAbs : ℕ) : ℤ) = 52 := by rw [Nat.cast_mul]; linarith
        exact_mod_cast this
      have hle : r.natAbs ≤ 52 := by nlinarith
      interval_cases h : r.natAbs <;> omega
  -- integer sides without a common factor
  obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ha, hb⟩ := sixty_rational D hP hT hα
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
  have hA0 : 0 < A := by
    have : (0 : ℝ) < μ * A := eA ▸ pa
    exact_mod_cast pos_of_mul_pos_right this hμ0.le
  have hB0 : 0 < B := by
    have : (0 : ℝ) < μ * B := eB ▸ pb
    exact_mod_cast pos_of_mul_pos_right this hμ0.le
  have hμ2 : μ ^ 2 ≠ 0 := by positivity
  -- the coloring number as a natural number
  have hMn : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hM0.le
  have hsqR : ((M.toNat : ℝ) * (A + B + C)) ^ 2 = 9 * N * A * B := by
    apply mul_left_cancel₀ hμ2
    rw [hMn]
    calc μ ^ 2 * ((M : ℝ) * (A + B + C)) ^ 2 = ((M : ℝ) * (a + b + c)) ^ 2 := by
          rw [eA, eB, eC]; ring
      _ = 9 * D.target.oppLen 0 ^ 2 := by rw [hcol]; ring
      _ = μ ^ 2 * (9 * N * A * B) := by rw [harea, eA, eB]; ring
  have hcosR : (C : ℝ) ^ 2 + A * B = A ^ 2 + B ^ 2 := by
    apply mul_left_cancel₀ hμ2
    have : (μ * C) ^ 2 = (μ * A) ^ 2 + (μ * B) ^ 2 - μ * A * (μ * B) := by
      rw [← eA, ← eB, ← eC]; exact hcos
    linear_combination this
  have hMNn : M.toNat ^ 2 < N := by
    have : ((M.toNat : ℕ) : ℝ) ^ 2 < N := by rw [hMn]; exact hMN
    exact_mod_cast this
  refine notprime60_core hNp hN5 hA0 hB0 hC0 hgcd (by exact_mod_cast hcosR) ?_ hMNn
    (by exact_mod_cast hsqR)
  intro e; apply hab; rw [eA, eB, e]

/-- **Theorem `theorem:comparison`.** Suppose `T` is a triangle with angles `(α, β, π/3)` with `β`
not a rational multiple of `π/3`. Suppose `T` can be used to `N`-tile an equilateral triangle, and
also to `K`-tile a (different) equilateral triangle. Then `N` and `K` have the same squarefree part.

"The same squarefree part" is stated as `N j² = K m²` for some positive integers `m, j` (here the
two coloring numbers); "`β` not a rational multiple of `π/3`" is `β ∉ ℚπ`. -/
theorem comparison {K : ℕ} (D₂ : CongruentDissection K) {α β a b c : ℝ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) (hP₂ : ∀ k, D₂.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hT₂ : TileSides D₂ α β (Real.pi / 3) a b c)
    (hβ : IrrPi β) :
    ∃ m j : ℕ, 0 < m ∧ 0 < j ∧ N * j ^ 2 = K * m ^ 2 := by
  obtain ⟨-, hα, hS, -⟩ := sixty_setup D hP hT hβ
  obtain ⟨-, -, hS₂, -⟩ := sixty_setup D₂ hP₂ hT₂ hβ
  obtain ⟨i₀, hi₀⟩ := exists_atA_onAB D
  obtain ⟨i₁, hi₁⟩ := exists_atA_onAB D₂
  obtain ⟨ε, hε, h1⟩ := exists_colouring D hα hS i₀
  obtain ⟨ε₂, hε₂, h2⟩ := exists_colouring D₂ hα hS₂ i₁
  obtain ⟨-, hd1, hs1, -⟩ := sixty_main D hP hT hβ hε hi₀ h1
  obtain ⟨-, hd2, hs2, -⟩ := sixty_main D₂ hP₂ hT₂ hβ hε₂ hi₁ h2
  have hM := M_pos D hP hT hβ hε hi₀ h1
  have hJ := M_pos D₂ hP₂ hT₂ hβ hε₂ hi₁ h2
  set M := ∑ i, ε i
  set J := ∑ i, ε₂ i
  have heq := hs1.symm.trans hs2
  rw [div_eq_div_iff hd1.ne' hd2.ne'] at heq
  refine ⟨M.toNat, J.toNat, by omega, by omega, ?_⟩
  have hMn : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hM.le
  have hJn : ((J.toNat : ℕ) : ℝ) = (J : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hJ.le
  have : ((N * J.toNat ^ 2 : ℕ) : ℝ) = ((K * M.toNat ^ 2 : ℕ) : ℝ) := by
    push_cast; rw [hMn, hJn]; linarith
  exact_mod_cast this

end TriangleTiling.Equilateral
