/-
The setting of Section 11 of Beeson–Roșu, *Tiling a triangle into a prime number of congruent
triangles* ("Runs of `c` edges"), and `definition:run`.

Throughout the section, triangle `T` is tiled by a tile with angles `(α, β, γ)`, where
`3α + 2β = π`, and integer sides `(a, b, c) = (mk, k² - m², k²)`, `0 < m < k`, `gcd(m, k) = 1`,
and no tile has its `γ` angle at a vertex of `T` (`RunSetting`). By `lemma:alphaoverpi`, `α` is
not a rational multiple of `π`, and `γ = 2α + β` (`RunSetting.irr`, `RunSetting.gamma`).

Tiles are handled through their vertices: `HasAngle D t P θ` (tile `t` has its angle `θ` at `P`),
`TileEdge D t P Q` (`P` and `Q` are two vertices of tile `t`, so `PQ` is an edge of it, of length
`dist P Q`), `Occurs D P Q R` (some tile has exactly the vertices `P, Q, R`: "the triangle `PQR` is
a tile of the given tiling").

Statements checked by Beeson.
-/
import TriangleTiling.Prime.ThreeAlpha
import TriangleTiling.Prime.TwoCs
import TriangleTiling.Prime.RunsSector

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set

variable {N : ℕ}

/-! ### The standing assumptions -/

/-- **The standing assumptions of Section 11.** Triangle `T = D.target` is tiled by a tile with
angles `(α, β, γ)` opposite sides `(a, b, c)`, where `3α + 2β = π`, `(a, b, c) = (mk, k² - m², k²)`,
`0 < m < k`, `gcd(m, k) = 1`, and no tile has its `γ` angle at a vertex of `T`. -/
structure RunSetting (D : CongruentDissection N) (α β γ a b c : ℝ) (m k : ℤ) : Prop where
  tile : ThreeAlpha.TileSides D α β γ a b c
  rel : 3 * α + 2 * β = π
  hm : 0 < m
  hmk : m < k
  cop : IsCoprime m k
  ha : a = m * k
  hb : b = k ^ 2 - m ^ 2
  hc : c = k ^ 2
  noγ : ∀ (j : Fin 3) (i : Fin N) (l : Fin 3),
    (D.tile i).pts l = D.target.pts j → (D.tile i).angleAt l ≠ γ

namespace RunSetting

variable {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
  (hS : RunSetting D α β γ a b c m k)
include hS

theorem angles_pos : 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = π :=
  ThreeAlpha.tileSides_angles D hS.tile

/-- `γ = 2α + β`. -/
theorem gamma : γ = 2 * α + β := by
  have := hS.angles_pos; have := hS.rel; linarith

theorem k_pos : 0 < k := lt_trans hS.hm hS.hmk

theorem a_pos : 0 < a := by
  rw [hS.ha]; exact_mod_cast mul_pos hS.hm hS.k_pos

theorem b_pos : 0 < b := by
  rw [hS.hb]; have := hS.hm; have := hS.hmk
  have : (m : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) < m := by exact_mod_cast hS.hm
    have h1 : (m : ℝ) < k := by exact_mod_cast hS.hmk
    nlinarith
  linarith

theorem c_pos : 0 < c := by
  rw [hS.hc]; have : (0 : ℝ) < k := by exact_mod_cast hS.k_pos
  positivity

theorem a_lt_c : a < c := by
  rw [hS.ha, hS.hc]
  have h0 : (0 : ℝ) < k := by exact_mod_cast hS.k_pos
  have h1 : (m : ℝ) < k := by exact_mod_cast hS.hmk
  nlinarith

theorem b_lt_c : b < c := by
  rw [hS.hb, hS.hc]
  have h0 : (0 : ℝ) < m := by exact_mod_cast hS.hm
  nlinarith

/-- `a ≠ b`: `mk = k² - m²` has no solution in positive integers (`5k²` is not a square). -/
theorem a_ne_b : a ≠ b := by
  intro h
  rw [hS.ha, hS.hb] at h
  have hz : m * k = k ^ 2 - m ^ 2 := by exact_mod_cast h
  -- `(2m + k)² = 5k²` is impossible with `k ≠ 0`, by the irrationality of `√5`: argue mod
  -- powers of `5` via descent on `k`.
  have h5 : (2 * m + k) ^ 2 = 5 * k ^ 2 := by linear_combination 4 * hz
  have hk := hS.k_pos
  -- `5 ∣ 2m + k`, then `5 ∣ k`, descend.
  have key : ∀ n : ℕ, ∀ x y : ℤ, y.natAbs = n → 0 < y → x ^ 2 = 5 * y ^ 2 → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hn hy hxy
      have h5x : (5 : ℤ) ∣ x := by
        have : (5 : ℤ) ∣ x ^ 2 := ⟨y ^ 2, hxy⟩
        exact Int.Prime.dvd_pow' (by norm_num) this
      obtain ⟨x', rfl⟩ := h5x
      have h5y : (5 : ℤ) ∣ y := by
        have : (5 : ℤ) ∣ y ^ 2 := ⟨x' ^ 2, by linarith⟩
        exact Int.Prime.dvd_pow' (by norm_num) this
      obtain ⟨y', rfl⟩ := h5y
      have hy' : 0 < y' := by linarith
      exact ih y'.natAbs (by rw [← hn]; rw [Int.natAbs_mul]; simp; omega) x' y' rfl hy'
        (by linarith)
  exact key _ _ _ rfl hk h5

omit hS in
theorem sides_gcd {m k : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    Nat.gcd (Nat.gcd (m * k).toNat (k ^ 2 - m ^ 2).toNat) (k ^ 2).toNat = 1 := by
  have hmk2 : m ^ 2 < k ^ 2 := by nlinarith
  have hbc : IsCoprime (k ^ 2 - m ^ 2) (k ^ 2) := by
    have h2 : IsCoprime (-(m ^ 2)) (k ^ 2) := (hcop.pow (m := 2) (n := 2)).neg_left
    have := h2.add_mul_right_left 1
    simpa [add_comm, sub_eq_add_neg] using this
  have h := Int.isCoprime_iff_gcd_eq_one.mp hbc
  rw [Int.gcd_eq_natAbs] at h
  have e1 : (k ^ 2 - m ^ 2).natAbs = (k ^ 2 - m ^ 2).toNat := by
    have h0 : (0 : ℤ) ≤ k ^ 2 - m ^ 2 := by linarith
    generalize k ^ 2 - m ^ 2 = z at h0 ⊢; omega
  have e2 : (k ^ 2).natAbs = (k ^ 2).toNat := by
    have h0 : (0 : ℤ) ≤ k ^ 2 := by positivity
    generalize k ^ 2 = z at h0 ⊢; omega
  rw [e1, e2] at h
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) h

omit hS in
theorem toNat_cast {z : ℤ} (h : 0 ≤ z) : (((z.toNat : ℕ) : ℤ) : ℝ) = (z : ℝ) := by
  rw [Int.toNat_of_nonneg h]

/-- **`lemma:alphaoverpi`** in this setting: `α` is not a rational multiple of `π`. -/
theorem irr : ¬ ∃ r : ℚ, α = r * π := by
  obtain ⟨τ, eα, eβ, -, ea, eb, ec⟩ := ThreeAlpha.relabel_sides D hS.tile
  have hk := hS.k_pos
  have hm := hS.hm
  have hmk := hS.hmk
  have hmk2 : m ^ 2 < k ^ 2 := by nlinarith
  have hA := toNat_cast (z := m * k) (by positivity)
  have hB := toNat_cast (z := k ^ 2 - m ^ 2) (by linarith)
  have hC := toNat_cast (z := k ^ 2) (by positivity)
  have hrel : 3 * ∠ ((ThreeAlpha.relabelModel D τ).model.pts 1)
      ((ThreeAlpha.relabelModel D τ).model.pts 0) ((ThreeAlpha.relabelModel D τ).model.pts 2) +
      2 * ∠ ((ThreeAlpha.relabelModel D τ).model.pts 0)
      ((ThreeAlpha.relabelModel D τ).model.pts 1) ((ThreeAlpha.relabelModel D τ).model.pts 2)
      = π := by
    have e2 : ∠ ((ThreeAlpha.relabelModel D τ).model.pts 0)
        ((ThreeAlpha.relabelModel D τ).model.pts 1) ((ThreeAlpha.relabelModel D τ).model.pts 2)
        = β := by
      rw [angle_comm]; exact eβ
    rw [e2]
    have e1 : tileα (ThreeAlpha.relabelModel D τ) = α := eα
    unfold tileα at e1
    rw [e1]; exact hS.rel
  have hind : AffineIndependent ℝ ![(ThreeAlpha.relabelModel D τ).model.pts 0,
      (ThreeAlpha.relabelModel D τ).model.pts 1, (ThreeAlpha.relabelModel D τ).model.pts 2] := by
    have e : ![(ThreeAlpha.relabelModel D τ).model.pts 0,
        (ThreeAlpha.relabelModel D τ).model.pts 1, (ThreeAlpha.relabelModel D τ).model.pts 2] =
        (ThreeAlpha.relabelModel D τ).model.pts := by
      funext i; fin_cases i <;> rfl
    rw [e]; exact (ThreeAlpha.relabelModel D τ).model.indep
  have h := (alphaoverpi hind hrel
    (a := (m * k).toNat) (b := (k ^ 2 - m ^ 2).toNat) (c := (k ^ 2).toNat)
    (by rw [ea, hS.ha]; push_cast at hA ⊢; rw [← hA])
    (by rw [eb, hS.hb]; push_cast at hB ⊢; rw [← hB])
    (by rw [ec, hS.hc]; push_cast at hC ⊢; rw [← hC])
    (sides_gcd hS.hm hS.hmk hS.cop)).1
  have e1 : tileα (ThreeAlpha.relabelModel D τ) = α := eα
  unfold tileα at e1
  rwa [e1] at h

theorem alpha_ne_beta : α ≠ β := by
  intro h
  apply hS.irr
  refine ⟨1 / 5, ?_⟩
  have := hS.rel; rw [h] at this ⊢; push_cast; linarith

/-- `γ > π/2`. -/
theorem gamma_gt : π / 2 < γ := by
  have := hS.angles_pos; have := hS.rel; have := hS.gamma; linarith

end RunSetting

/-! ### Tiles, through their vertices -/

variable (D : CongruentDissection N)

/-- Tile `t` has its angle `θ` at the point `P`. -/
def HasAngle (t : Fin N) (P : Plane) (θ : ℝ) : Prop :=
  ∃ l : Fin 3, (D.tile t).pts l = P ∧ (D.tile t).angleAt l = θ

/-- `P` and `Q` are two vertices of tile `t`, so the segment `PQ` is an edge of tile `t`. -/
def TileEdge (t : Fin N) (P Q : Plane) : Prop :=
  ∃ l l' : Fin 3, l ≠ l' ∧ (D.tile t).pts l = P ∧ (D.tile t).pts l' = Q

/-- The triangle `PQR` is a tile of the given tiling: some tile has exactly the vertices
`P, Q, R`. -/
def Occurs (P Q R : Plane) : Prop :=
  ∃ t : Fin N, Set.range (D.tile t).pts = {P, Q, R}

theorem fin3_others {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by
  revert hxy hxz hyz; fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

variable {D}

/-- **Each corner of a tile** has one of the angles `α, β, γ`, and the side opposite it has the
corresponding length `a, b, c`. -/
theorem vertex_data {α β γ a b c : ℝ} (hT : ThreeAlpha.TileSides D α β γ a b c) (i : Fin N)
    (l : Fin 3) :
    ((D.tile i).angleAt l = α ∧ (D.tile i).oppLen l = a) ∨
      ((D.tile i).angleAt l = β ∧ (D.tile i).oppLen l = b) ∨
        ((D.tile i).angleAt l = γ ∧ (D.tile i).oppLen l = c) := by
  obtain ⟨σ, hang, hdist⟩ := corner_perm_dist (D.tiles_congruent i)
  obtain ⟨σ', h0, h1, h2, l0, l1, l2⟩ := hT
  have hA : (D.tile i).angleAt l = D.model.angleAt (σ l) := (hang l).symm
  have hL : (D.tile i).oppLen l = D.model.oppLen (σ l) := by
    unfold Tri.oppLen
    rw [hdist]
    have d1 : σ l ≠ σ (l + 1) := σ.injective.ne (by fin_cases l <;> decide)
    have d2 : σ l ≠ σ (l + 2) := σ.injective.ne (by fin_cases l <;> decide)
    have d3 : σ (l + 1) ≠ σ (l + 2) := σ.injective.ne (by fin_cases l <;> decide)
    rcases fin3_others d1 d2 d3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2, dist_comm]
  rw [hA, hL]
  have : σ l = σ' 0 ∨ σ l = σ' 1 ∨ σ l = σ' 2 := by
    have : σ' (σ'.symm (σ l)) = σ l := σ'.apply_symm_apply _
    generalize σ'.symm (σ l) = p at this
    fin_cases p
    · exact Or.inl this.symm
    · exact Or.inr (Or.inl this.symm)
    · exact Or.inr (Or.inr this.symm)
  rcases this with e | e | e <;> rw [e]
  · exact Or.inl ⟨h0, l0⟩
  · exact Or.inr (Or.inl ⟨h1, l1⟩)
  · exact Or.inr (Or.inr ⟨h2, l2⟩)

end TriangleTiling.Prime
