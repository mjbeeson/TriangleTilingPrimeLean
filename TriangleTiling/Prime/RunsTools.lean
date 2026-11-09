/-
Tools for the proofs of Section 11 of Beeson–Roșu ("Runs of `c` edges"): angles and sides of a tile
given by its vertices, the third vertex of a tile from two distances, segments of the lattice, and
linear functionals for the lattice lines.
-/
import TriangleTiling.Prime.RunsRun

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

/-! ### A tile through its three vertices -/

/-- The three vertices of a tile given by its vertex set, as indices. -/
theorem range_indices {t : Fin N} {P Q R : Plane} (h : Set.range (D.tile t).pts = {P, Q, R})
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ∃ l : Fin 3, (D.tile t).pts l = P ∧
      (((D.tile t).pts (l + 1) = Q ∧ (D.tile t).pts (l + 2) = R) ∨
        ((D.tile t).pts (l + 1) = R ∧ (D.tile t).pts (l + 2) = Q)) := by
  have hP : P ∈ Set.range (D.tile t).pts := by rw [h]; simp
  obtain ⟨l, hl⟩ := hP
  have h1 : (D.tile t).pts (l + 1) ∈ ({P, Q, R} : Set Plane) := h ▸ ⟨_, rfl⟩
  have h2 : (D.tile t).pts (l + 2) ∈ ({P, Q, R} : Set Plane) := h ▸ ⟨_, rfl⟩
  have n1 : (D.tile t).pts (l + 1) ≠ P := by
    rw [← hl]; intro e; have := (D.tile t).indep.injective e; revert this; fin_cases l <;> decide
  have n2 : (D.tile t).pts (l + 2) ≠ P := by
    rw [← hl]; intro e; have := (D.tile t).indep.injective e; revert this; fin_cases l <;> decide
  have n12 : (D.tile t).pts (l + 1) ≠ (D.tile t).pts (l + 2) := by
    intro e; have := (D.tile t).indep.injective e; revert this; fin_cases l <;> decide
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  refine ⟨l, hl, ?_⟩
  rcases h1 with h1 | h1 | h1
  · exact absurd h1 n1
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 n2
    · exact absurd (h1.trans h2.symm) n12
    · exact Or.inl ⟨h1, h2⟩
  · rcases h2 with h2 | h2 | h2
    · exact absurd h2 n2
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) n12

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- The angle at a vertex is determined by the opposite side. -/
theorem angle_of_opp {t : Fin N} (l : Fin 3) :
    ((D.tile t).oppLen l = a → (D.tile t).angleAt l = α) ∧
      ((D.tile t).oppLen l = b → (D.tile t).angleAt l = β) ∧
        ((D.tile t).oppLen l = c → (D.tile t).angleAt l = γ) := by
  have hab := hS.a_ne_b
  have hac := hS.a_lt_c.ne
  have hbc := hS.b_lt_c.ne
  have hγ := hS.gamma
  rcases hS.angleAt_combo t l with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals first
    | exact absurd h hab | exact absurd h.symm hab | exact absurd h hac
    | exact absurd h.symm hac | exact absurd h hbc | exact absurd h.symm hbc
    | (rw [h1]; try linarith)

/-- The side opposite a vertex is determined by the angle there. -/
theorem opp_of_angle {t : Fin N} (l : Fin 3) :
    ((D.tile t).angleAt l = α → (D.tile t).oppLen l = a) ∧
      ((D.tile t).angleAt l = β → (D.tile t).oppLen l = b) ∧
        ((D.tile t).angleAt l = γ → (D.tile t).oppLen l = c) := by
  have hαβ := hS.alpha_ne_beta
  have hγ := hS.gamma
  obtain ⟨hα, hβ, -, -⟩ := hS.angles_pos
  rcases hS.angleAt_combo t l with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals first
    | exact h2 | exact absurd h hαβ | exact absurd h.symm hαβ | (exfalso; linarith)

/-- **A tile with vertices `P, Q, R`** whose sides `QR, PR, PQ` are `a, b, c` has its angles
`α, β, γ` at `P, Q, R`. -/
theorem occurs_angles {t : Fin N} {P Q R : Plane} (h : Set.range (D.tile t).pts = {P, Q, R})
    (hQR : dist Q R = a) (hPR : dist P R = b) (hPQ : dist P Q = c) :
    HasAngle D t P α ∧ HasAngle D t Q β ∧ HasAngle D t R γ := by
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  have nPQ : P ≠ Q := fun e => by rw [e, dist_self] at hPQ; linarith
  have nPR : P ≠ R := fun e => by rw [e, dist_self] at hPR; linarith
  have nQR : Q ≠ R := fun e => by rw [e, dist_self] at hQR; linarith
  obtain ⟨l, hl, hord⟩ := range_indices h nPQ nPR nQR
  have eP : (D.tile t).oppLen l = a := by
    unfold Tri.oppLen
    rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hQR]
    · rw [h1, h2, dist_comm, hQR]
  have s1 : l + 1 + 1 = l + 2 := by fin_cases l <;> rfl
  have s2 : l + 1 + 2 = l := by fin_cases l <;> rfl
  have s3 : l + 2 + 1 = l := by fin_cases l <;> rfl
  have s4 : l + 2 + 2 = l + 1 := by fin_cases l <;> rfl
  rcases hord with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨⟨l, hl, (hS.angle_of_opp l).1 eP⟩, ⟨l + 1, h1, (hS.angle_of_opp (l + 1)).2.1 ?_⟩,
      ⟨l + 2, h2, (hS.angle_of_opp (l + 2)).2.2 ?_⟩⟩
    · unfold Tri.oppLen; rw [s1, s2, h2, hl, dist_comm, hPR]
    · unfold Tri.oppLen; rw [s3, s4, hl, h1, hPQ]
  · refine ⟨⟨l, hl, (hS.angle_of_opp l).1 eP⟩, ⟨l + 2, h2, (hS.angle_of_opp (l + 2)).2.1 ?_⟩,
      ⟨l + 1, h1, (hS.angle_of_opp (l + 1)).2.2 ?_⟩⟩
    · unfold Tri.oppLen; rw [s3, s4, hl, h1, hPR]
    · unfold Tri.oppLen; rw [s1, s2, h2, hl, dist_comm, hPQ]

omit hS in
theorem fin3_third (l l' : Fin 3) (h : l ≠ l') : ∃ l'', l'' ≠ l ∧ l'' ≠ l' ∧
    ∀ f : Fin 3 → ℝ, f l + f l' + f l'' = f 0 + f 1 + f 2 := by
  fin_cases l <;> fin_cases l' <;> simp at h ⊢
  · exact ⟨2, by decide, by decide, fun f => by ring⟩
  · exact ⟨1, by decide, by decide, fun f => by ring⟩
  · exact ⟨2, by decide, by decide, fun f => by ring⟩
  · exact ⟨0, by decide, by decide, fun f => by ring⟩
  · exact ⟨1, by decide, by decide, fun f => by ring⟩
  · exact ⟨0, by decide, by decide, fun f => by ring⟩

/-- The three angles of a tile are different. -/
theorem angles_ne {t : Fin N} {l l' : Fin 3} (hll : l ≠ l') :
    (D.tile t).angleAt l ≠ (D.tile t).angleAt l' := by
  intro heq
  obtain ⟨l'', -, -, hf⟩ := fin3_third l l' hll
  have hall := hf (D.tile t).angleAt
  rw [(D.tile t).angleAt_sum, heq] at hall
  have hrel := hS.rel
  have hγ := hS.gamma
  obtain ⟨hα, hβ, -, -⟩ := hS.angles_pos
  rcases hS.angleAt_combo t l' with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨e1, -⟩ <;>
    rcases hS.angleAt_combo t l'' with ⟨e2, -⟩ | ⟨e2, -⟩ | ⟨e2, -⟩ <;> rw [e1, e2] at hall
  all_goals first
    | linarith
    | (have := hS.uniq (p := 3) (q := 0) (u := 3) (v := 2) (by push_cast; linarith); omega)
    | (have := hS.uniq (p := 2) (q := 1) (u := 3) (v := 2) (by push_cast; linarith); omega)
    | (have := hS.uniq (p := 1) (q := 2) (u := 3) (v := 2) (by push_cast; linarith); omega)
    | (have := hS.uniq (p := 0) (q := 3) (u := 3) (v := 2) (by push_cast; linarith); omega)
    | (have := hS.uniq (p := 4) (q := 1) (u := 3) (v := 2) (by push_cast; linarith); omega)
    | (have := hS.uniq (p := 2) (q := 3) (u := 3) (v := 2) (by push_cast; linarith); omega)
    | (have := hS.uniq (p := 5) (q := 2) (u := 3) (v := 2) (by push_cast; linarith); omega)
    | (have := hS.uniq (p := 4) (q := 3) (u := 3) (v := 2) (by push_cast; linarith); omega)

/-- **The sides at a vertex.** If tile `t` has its angle `θ` at `P = pts l`, the side from `P` to
`pts (l+1)` is opposite `pts (l+2)`, and its length is the side for the angle there. -/
theorem side_at {t : Fin N} (l : Fin 3) :
    dist ((D.tile t).pts l) ((D.tile t).pts (l + 1)) = (D.tile t).oppLen (l + 2) ∧
      dist ((D.tile t).pts l) ((D.tile t).pts (l + 2)) = (D.tile t).oppLen (l + 1) := by
  unfold Tri.oppLen
  have s1 : l + 1 + 1 = l + 2 := by fin_cases l <;> rfl
  have s2 : l + 1 + 2 = l := by fin_cases l <;> rfl
  have s3 : l + 2 + 1 = l := by fin_cases l <;> rfl
  have s4 : l + 2 + 2 = l + 1 := by fin_cases l <;> rfl
  rw [s1, s2, s3, s4, dist_comm ((D.tile t).pts (l + 2))]
  exact ⟨rfl, rfl⟩

/-- At a vertex with angle `α` the two sides are `b` and `c`; with `β`, `a` and `c`; with `γ`,
`a` and `b`. -/
theorem sides_at {t : Fin N} {l : Fin 3} :
    ((D.tile t).angleAt l = α →
      (dist ((D.tile t).pts l) ((D.tile t).pts (l + 1)) = b ∧
        dist ((D.tile t).pts l) ((D.tile t).pts (l + 2)) = c) ∨
      (dist ((D.tile t).pts l) ((D.tile t).pts (l + 1)) = c ∧
        dist ((D.tile t).pts l) ((D.tile t).pts (l + 2)) = b)) ∧
    ((D.tile t).angleAt l = β →
      (dist ((D.tile t).pts l) ((D.tile t).pts (l + 1)) = a ∧
        dist ((D.tile t).pts l) ((D.tile t).pts (l + 2)) = c) ∨
      (dist ((D.tile t).pts l) ((D.tile t).pts (l + 1)) = c ∧
        dist ((D.tile t).pts l) ((D.tile t).pts (l + 2)) = a)) ∧
    ((D.tile t).angleAt l = γ →
      (dist ((D.tile t).pts l) ((D.tile t).pts (l + 1)) = a ∧
        dist ((D.tile t).pts l) ((D.tile t).pts (l + 2)) = b) ∨
      (dist ((D.tile t).pts l) ((D.tile t).pts (l + 1)) = b ∧
        dist ((D.tile t).pts l) ((D.tile t).pts (l + 2)) = a)) := by
  obtain ⟨e1, e2⟩ := hS.side_at (t := t) l
  rw [e1, e2]
  have n12 : l + 1 ≠ l + 2 := by fin_cases l <;> decide
  have n01 : l ≠ l + 1 := by fin_cases l <;> decide
  have n02 : l ≠ l + 2 := by fin_cases l <;> decide
  have d1 := hS.angles_ne (t := t) n01
  have d2 := hS.angles_ne (t := t) n02
  have d3 := hS.angles_ne (t := t) n12
  have o1 := hS.opp_of_angle (t := t) (l + 1)
  have o2 := hS.opp_of_angle (t := t) (l + 2)
  have hγ := hS.gamma
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] at d1 d2 <;>
    rcases vertex_data hS.tile t (l + 1) with ⟨f1, -⟩ | ⟨f1, -⟩ | ⟨f1, -⟩ <;>
    rcases vertex_data hS.tile t (l + 2) with ⟨f2, -⟩ | ⟨f2, -⟩ | ⟨f2, -⟩ <;>
    first
    | exact absurd f1.symm d1 | exact absurd f2.symm d2 | exact absurd (f1.trans f2.symm) d3
    | exact Or.inl ⟨o2.1 f2, o1.2.1 f1⟩ | exact Or.inl ⟨o2.1 f2, o1.2.2 f1⟩
    | exact Or.inl ⟨o2.2.1 f2, o1.1 f1⟩ | exact Or.inl ⟨o2.2.1 f2, o1.2.2 f1⟩
    | exact Or.inl ⟨o2.2.2 f2, o1.1 f1⟩ | exact Or.inl ⟨o2.2.2 f2, o1.2.1 f1⟩
    | exact Or.inr ⟨o2.1 f2, o1.2.1 f1⟩ | exact Or.inr ⟨o2.1 f2, o1.2.2 f1⟩
    | exact Or.inr ⟨o2.2.1 f2, o1.1 f1⟩ | exact Or.inr ⟨o2.2.1 f2, o1.2.2 f1⟩
    | exact Or.inr ⟨o2.2.2 f2, o1.1 f1⟩ | exact Or.inr ⟨o2.2.2 f2, o1.2.1 f1⟩

end RunSetting

/-! ### The third vertex from two distances -/

theorem perp_both {p0 p1 q0 q1 w0 w1 : ℝ} (o1 : (p0 - q0) * w0 + (p1 - q1) * w1 = 0)
    (o2 : (p0 - q0) * (p0 + q0) + (p1 - q1) * (p1 + q1) = 0)
    (hs : 0 < (w0 * p1 - w1 * p0) * (w0 * q1 - w1 * q0)) : p0 = q0 ∧ p1 = q1 := by
  have e0 : (w0 * (p1 + q1) - w1 * (p0 + q0)) * (p0 - q0) = 0 := by
    linear_combination (p1 + q1) * o1 - w1 * o2
  have e1 : (w0 * (p1 + q1) - w1 * (p0 + q0)) * (p1 - q1) = 0 := by
    linear_combination (-(p0 + q0)) * o1 + w0 * o2
  by_contra hne
  have hc : w0 * (p1 + q1) - w1 * (p0 + q0) = 0 := by
    rcases not_and_or.mp hne with h | h
    · exact (mul_eq_zero.mp e0).resolve_right (sub_ne_zero.mpr h)
    · exact (mul_eq_zero.mp e1).resolve_right (sub_ne_zero.mpr h)
  have : w0 * p1 - w1 * p0 = -(w0 * q1 - w1 * q0) := by linear_combination hc
  rw [this] at hs
  nlinarith [sq_nonneg (w0 * q1 - w1 * q0)]

/-- Two points on the same strict side of the line `AB`, at the same distances from `A` and from
`B`, are equal. -/
theorem eq_of_dist_dist {A B Z Z' : Plane} (hZA : dist Z A = dist Z' A) (hZB : dist Z B = dist Z' B)
    (hside : 0 < cross (B - A) (Z - A) * cross (B - A) (Z' - A)) : Z = Z' := by
  have hsq : ∀ x y : Plane, dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
    intro x y
    rw [dist_eq_norm, norm_sq_coords]; simp
  have E1 : (Z 0 - A 0) ^ 2 + (Z 1 - A 1) ^ 2 = (Z' 0 - A 0) ^ 2 + (Z' 1 - A 1) ^ 2 := by
    rw [← hsq, ← hsq, hZA]
  have E2 : (Z 0 - B 0) ^ 2 + (Z 1 - B 1) ^ 2 = (Z' 0 - B 0) ^ 2 + (Z' 1 - B 1) ^ 2 := by
    rw [← hsq, ← hsq, hZB]
  simp only [cross, PiLp.sub_apply] at hside
  have o1 : ((Z 0 - A 0) - (Z' 0 - A 0)) * (B 0 - A 0) + ((Z 1 - A 1) - (Z' 1 - A 1)) * (B 1 - A 1)
      = 0 := by linear_combination (1 / 2 : ℝ) * (E1 - E2)
  have o2 : ((Z 0 - A 0) - (Z' 0 - A 0)) * ((Z 0 - A 0) + (Z' 0 - A 0)) +
      ((Z 1 - A 1) - (Z' 1 - A 1)) * ((Z 1 - A 1) + (Z' 1 - A 1)) = 0 := by
    linear_combination E1
  obtain ⟨h0, h1⟩ := perp_both o1 o2 hside
  ext i
  fin_cases i
  · show Z 0 = Z' 0; linarith
  · show Z 1 = Z' 1; linarith

/-! ### Segments -/

/-- An open segment between two points of a convex set, through an interior point, is
interior. -/
theorem openSegment_subset_interior_of {K : Set Plane} (hK : Convex ℝ K) {P R Z : Plane}
    (hP : P ∈ K) (hR : R ∈ K) (hZ : Z ∈ openSegment ℝ P R) (hZi : Z ∈ interior K) :
    openSegment ℝ P R ⊆ interior K := by
  rw [openSegment_eq_image_lineMap] at hZ
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hZ
  intro y hy
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨μ, ⟨m0, m1⟩, rfl⟩ := hy
  rcases lt_trichotomy μ θ with h | h | h
  · -- between `P` and `Z`
    apply hK.openSegment_interior_closure_subset_interior hZi (subset_closure hP)
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 - μ / θ, ⟨by rw [sub_pos, div_lt_one h0]; exact h, by
      have := div_pos m0 h0; linarith⟩, ?_⟩
    simp only [AffineMap.lineMap_apply_module]
    have hθ : θ ≠ 0 := h0.ne'
    ext i; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp; ring
  · rw [h]; exact hZi
  · apply hK.openSegment_interior_closure_subset_interior hZi (subset_closure hR)
    rw [openSegment_eq_image_lineMap]
    have h1θ : 0 < 1 - θ := by linarith
    refine ⟨(μ - θ) / (1 - θ), ⟨div_pos (by linarith) h1θ, by
      rw [div_lt_one h1θ]; linarith⟩, ?_⟩
    simp only [AffineMap.lineMap_apply_module]
    have hθ : 1 - θ ≠ 0 := h1θ.ne'
    ext i; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; field_simp; ring

/-- A point of the segment from `A` to `A + n w` lies in one of the `n` unit segments. -/
theorem mem_unit_segment {A w y : Plane} {n : ℕ} (hn : 0 < n)
    (hy : y ∈ segment ℝ A (A + (n : ℝ) • w)) :
    ∃ i : ℕ, i < n ∧ y ∈ segment ℝ (A + (i : ℝ) • w) (A + ((i : ℝ) + 1) • w) := by
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hy
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set τ := θ * n
  have hτ0 : 0 ≤ τ := by positivity
  have hτn : τ ≤ n := by simp only [τ]; nlinarith
  set i : ℕ := min (⌊τ⌋₊) (n - 1)
  have hi : i < n := by omega
  have hi1 : (i : ℝ) ≤ τ := by
    have := Nat.floor_le hτ0
    have : (i : ℝ) ≤ ⌊τ⌋₊ := by exact_mod_cast min_le_left _ _
    linarith
  have hi2 : τ ≤ (i : ℝ) + 1 := by
    by_cases hf : ⌊τ⌋₊ ≤ n - 1
    · have : i = ⌊τ⌋₊ := min_eq_left hf
      rw [this]; exact (Nat.lt_floor_add_one τ).le
    · push Not at hf
      have : i = n - 1 := min_eq_right hf.le
      rw [this]
      have : ((n - 1 : ℕ) : ℝ) = n - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]; linarith
  refine ⟨i, hi, ?_⟩
  rw [segment_eq_image_lineMap]
  refine ⟨τ - i, ⟨by linarith, by linarith⟩, ?_⟩
  simp only [AffineMap.lineMap_apply_module]
  simp only [τ]
  ext j; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-! ### Lattice lines as level sets -/

/-- The linear part of `crdI`. -/
noncomputable def fI (I J : Plane) : Plane →ₗ[ℝ] ℝ := (-(cross I J)⁻¹) • crossL J

/-- The linear part of `crdJ`. -/
noncomputable def fJ (I J : Plane) : Plane →ₗ[ℝ] ℝ := (cross I J)⁻¹ • crossL I

theorem crdI_eq (U I J y : Plane) : crdI U I J y = fI I J y - fI I J U := by
  simp only [crdI, fI, LinearMap.smul_apply, crossL_apply, smul_eq_mul, cross]
  simp only [PiLp.sub_apply]; ring

theorem crdJ_eq (U I J y : Plane) : crdJ U I J y = fJ I J y - fJ I J U := by
  simp only [crdJ, fJ, LinearMap.smul_apply, crossL_apply, smul_eq_mul, cross]
  simp only [PiLp.sub_apply]; ring

/-- The functional `p crdI + q crdJ` (up to a constant), for a lattice line. -/
noncomputable def lineF (I J : Plane) (p q : ℝ) : Plane →ₗ[ℝ] ℝ := p • fI I J + q • fJ I J

theorem lineF_apply (U I J y : Plane) (p q : ℝ) :
    lineF I J p q y = p * crdI U I J y + q * crdJ U I J y + lineF I J p q U := by
  simp only [lineF, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, crdI_eq, crdJ_eq]
  ring

theorem lineF_ne_zero {I J : Plane} (hIJ : cross I J ≠ 0) {p q : ℝ} (h : p ≠ 0 ∨ q ≠ 0) :
    lineF I J p q ≠ 0 := by
  intro h0
  have e1 := LinearMap.congr_fun h0 I
  have e2 := LinearMap.congr_fun h0 J
  simp only [lineF, fI, fJ, LinearMap.add_apply, LinearMap.smul_apply, crossL_apply,
    smul_eq_mul, LinearMap.zero_apply, cross_self] at e1 e2
  rw [cross_swap J I] at e1
  have hinv : (cross I J)⁻¹ ≠ 0 := inv_ne_zero hIJ
  rcases h with h | h
  · apply h
    have : p * ((cross I J)⁻¹ * cross I J) = 0 := by linarith
    rwa [inv_mul_cancel₀ hIJ, mul_one] at this
  · apply h
    have : q * ((cross I J)⁻¹ * cross I J) = 0 := by linarith
    rwa [inv_mul_cancel₀ hIJ, mul_one] at this

end TriangleTiling.Prime
