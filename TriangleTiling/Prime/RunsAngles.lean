/-
Angles at a point, for Section 11 of Beeson–Roșu ("Runs of `c` edges").

* `Tri.localAngle_mem`: at a point of a tile, its local angle is its angle at that vertex, `π`
  (inside an edge) or `2π` (inside the tile).
* `RunSetting.combo`: so it is `pα + qβ` with `(p, q)` one of `(1,0), (0,1), (2,1), (3,2), (6,4)`
  (`γ = 2α + β`, `π = 3α + 2β`).
* `RunSetting.sum_one`, `RunSetting.sum_three`: `lemma:angles` for a set of tiles at a point whose
  angles add up to `α`, `β` (one tile) or `α + 2β` (three tiles, angles `α, β, β`).
* `sum_le_target`, `halfplane_sum_le`: the angles of distinct tiles at a point add up to at most
  `2π`, `π` at a boundary point, and at most `π` for tiles on one side of a line through it.
-/
import TriangleTiling.Prime.RunsLattice
import TriangleTiling.TwoCs.Finish

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set MeasureTheory Metric

variable {N : ℕ}

/-- At a point of a triangle, its local angle is its angle at that vertex, `π` or `2π`. -/
theorem Tri.localAngle_mem (T : Tri) {X : Plane} (hX : X ∈ T.carrier) :
    (∃ l, T.pts l = X ∧ T.localAngle X = T.angleAt l) ∨ T.localAngle X = π ∨
      T.localAngle X = 2 * π := by
  classical
  by_cases hv : ∃ l, T.pts l = X
  · obtain ⟨l, hl⟩ := hv
    left; exact ⟨l, hl, by rw [← hl, Tri.localAngle_vertex]; rfl⟩
  · push Not at hv
    have hc : ∀ i, 0 ≤ T.basis.coord i X := (Tri.mem_carrier_iff_coord T X).mp hX
    rcases T.classify (fun k h => hv k h.symm) with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hneg⟩
    · right; right
      exact T.localAngle_interior ((T.mem_interior_iff_coord_pos X).mpr hpos)
    · right; left
      rw [Tri.localAngle, dif_neg (fun ⟨j, hj⟩ => hv j hj.symm),
        if_neg (fun h => (h k).ne' hk0), if_pos ⟨k, hk0, hkpos⟩]
    · exact absurd (hc k) (not_le.mpr hneg)

/-! ### Local angles as combinations of `α` and `β` -/

namespace RunSetting

variable {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
  (hS : RunSetting D α β γ a b c m k)
include hS

/-- The angles `α, β, γ` of a tile, as `pα + qβ`. -/
theorem angleAt_combo (i : Fin N) (l : Fin 3) :
    ((D.tile i).angleAt l = α ∧ (D.tile i).oppLen l = a) ∨
      ((D.tile i).angleAt l = β ∧ (D.tile i).oppLen l = b) ∨
        ((D.tile i).angleAt l = 2 * α + β ∧ (D.tile i).oppLen l = c) := by
  have := vertex_data hS.tile i l
  rwa [hS.gamma] at this

/-- **Local angles are combinations of `α` and `β`.** At a point `X` of a tile, its local angle
is `pα + qβ` with `(p, q)` one of `(1,0), (0,1), (2,1)` (and then `X` is a vertex with that
angle), `(3,2)` or `(6,4)`. -/
theorem combo {i : Fin N} {X : Plane} (hX : X ∈ (D.tile i).carrier) :
    ∃ p q : ℕ, (D.tile i).localAngle X = p * α + q * β ∧
      ((p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨ (p = 3 ∧ q = 2) ∨
        (p = 6 ∧ q = 4)) ∧
      (p + q ≤ 3 → HasAngle D i X (p * α + q * β)) := by
  have hrel := hS.rel
  rcases Tri.localAngle_mem (D.tile i) hX with ⟨l, hl, he⟩ | he | he
  · rcases hS.angleAt_combo i l with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · refine ⟨1, 0, by rw [he, h]; push_cast; ring, by omega, fun _ => ⟨l, hl, by rw [h]; push_cast; ring⟩⟩
    · refine ⟨0, 1, by rw [he, h]; push_cast; ring, by omega, fun _ => ⟨l, hl, by rw [h]; push_cast; ring⟩⟩
    · refine ⟨2, 1, by rw [he, h]; push_cast; ring, by omega, fun _ => ⟨l, hl, by rw [h]; push_cast; ring⟩⟩
  · exact ⟨3, 2, by rw [he]; push_cast; linarith, by omega, fun h => by omega⟩
  · exact ⟨6, 4, by rw [he]; push_cast; linarith, by omega, fun h => by omega⟩

/-- `lemma:angles` (uniqueness of `pα + qβ`). -/
theorem uniq {p q u v : ℕ} (h : (p : ℝ) * α + q * β = u * α + v * β) : p = u ∧ q = v :=
  (angles hS.irr hS.rel).1 p q u v h

/-- **A set of tiles at `X` whose angles add up to `α` or `β`** is a single tile, with that angle
at `X` (`lemma:angles`). -/
theorem sum_one {X : Plane} {F : Finset (Fin N)} (hF : ∀ i ∈ F, X ∈ (D.tile i).carrier)
    {P Q : ℕ} (hPQ : P + Q = 1) (hsum : ∑ i ∈ F, (D.tile i).localAngle X = P * α + Q * β) :
    ∃ i, F = {i} ∧ HasAngle D i X (P * α + Q * β) := by
  classical
  choose p q hpq hcase hhas using fun (i : F) => hS.combo (hF i i.2)
  set p' : Fin N → ℕ := fun i => if h : i ∈ F then p ⟨i, h⟩ else 0
  set q' : Fin N → ℕ := fun i => if h : i ∈ F then q ⟨i, h⟩ else 0
  have hsum' : ∑ i ∈ F, (D.tile i).localAngle X =
      (∑ i ∈ F, p' i : ℕ) * α + (∑ i ∈ F, q' i : ℕ) * β := by
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [p', q', dif_pos hi]
    exact hpq ⟨i, hi⟩
  obtain ⟨e1, e2⟩ := hS.uniq (hsum'.symm.trans hsum)
  have hpos : ∀ i ∈ F, 1 ≤ p' i + q' i := by
    intro i hi
    simp only [p', q', dif_pos hi]
    rcases hcase ⟨i, hi⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hcard : F.card ≤ 1 := by
    have : ∑ i ∈ F, 1 ≤ ∑ i ∈ F, (p' i + q' i) := Finset.sum_le_sum hpos
    rw [Finset.sum_add_distrib, e1, e2, Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  have hne : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at e1 e2
    omega
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hne))
  refine ⟨i, rfl, ?_⟩
  rw [Finset.sum_singleton] at e1 e2
  have hi : i ∈ ({i} : Finset (Fin N)) := Finset.mem_singleton_self i
  have := hhas ⟨i, hi⟩
  simp only [p', q', dif_pos hi] at e1 e2
  rw [← e1, ← e2]
  exact this (by omega)

/-- **A set of tiles at `X` whose angles add up to `α + 2β`** consists of tiles with angles `α` or
`β` at `X`, at most one of them `α` (`lemma:angles`: three tiles, angles `α, β, β`). -/
theorem sum_three {X : Plane} {F : Finset (Fin N)} (hF : ∀ i ∈ F, X ∈ (D.tile i).carrier)
    (hsum : ∑ i ∈ F, (D.tile i).localAngle X = α + 2 * β) :
    (∀ i ∈ F, HasAngle D i X α ∨ HasAngle D i X β) ∧
      ∀ i ∈ F, ∀ j ∈ F, i ≠ j → HasAngle D i X β ∨ HasAngle D j X β := by
  classical
  choose p q hpq hcase hhas using fun (i : F) => hS.combo (hF i i.2)
  set p' : Fin N → ℕ := fun i => if h : i ∈ F then p ⟨i, h⟩ else 0
  set q' : Fin N → ℕ := fun i => if h : i ∈ F then q ⟨i, h⟩ else 0
  have hsum' : ∑ i ∈ F, (D.tile i).localAngle X =
      (∑ i ∈ F, p' i : ℕ) * α + (∑ i ∈ F, q' i : ℕ) * β := by
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [p', q', dif_pos hi]
    exact hpq ⟨i, hi⟩
  obtain ⟨e1, e2⟩ := hS.uniq (u := 1) (v := 2) (by rw [← hsum', hsum]; push_cast; ring)
  have hle : ∀ i ∈ F, p' i ≤ 1 := fun i hi => e1 ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hle' : ∀ i ∈ F, q' i ≤ 2 := fun i hi => e2 ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hab : ∀ i ∈ F, (p' i = 1 ∧ q' i = 0) ∨ (p' i = 0 ∧ q' i = 1) := by
    intro i hi
    have h1 := hle i hi
    have h2 := hle' i hi
    simp only [p', q', dif_pos hi] at h1 h2 ⊢
    rcases hcase ⟨i, hi⟩ with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> omega
  have hhas' : ∀ i ∈ F, HasAngle D i X ((p' i : ℕ) * α + (q' i : ℕ) * β) := by
    intro i hi
    have := hhas ⟨i, hi⟩
    simp only [p', q', dif_pos hi] at this ⊢
    exact this (by
      have := hab i hi; simp only [p', q', dif_pos hi] at this; omega)
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · rcases hab i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; have := hhas' i hi; rw [h1, h2] at this; simpa using this
    · right; have := hhas' i hi; rw [h1, h2] at this; simpa using this
  · by_contra hno
    push Not at hno
    have hi1 : p' i = 1 := by
      rcases hab i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso; apply hno.1; have := hhas' i hi; rw [h1, h2] at this; simpa using this
    have hj1 : p' j = 1 := by
      rcases hab j hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso; apply hno.2; have := hhas' j hj; rw [h1, h2] at this; simpa using this
    have : p' i + p' j ≤ ∑ l ∈ F, p' l := by
      rw [← Finset.sum_pair hij]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by
        intro l hl; simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl <;> assumption) fun _ _ _ => Nat.zero_le _
    omega

end RunSetting

/-! ### Sums of angles at a point -/

section Sums

variable (D : Dissection N)

/-- The angles at `X` of a set of tiles add up to at most the target's local angle there. -/
theorem sum_le_target (F : Finset (Fin N)) (X : Plane) :
    ∑ i ∈ F, (D.tile i).localAngle X ≤ D.target.localAngle X := by
  rw [← D.sum_localAngle_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun i _ _ => (D.tile i).localAngle_nonneg X

theorem sum_le_two_pi (F : Finset (Fin N)) (X : Plane) :
    ∑ i ∈ F, (D.tile i).localAngle X ≤ 2 * π :=
  (sum_le_target D F X).trans (Tri.localAngle_le_two_pi _ _)

theorem sum_le_pi_of_not_interior (F : Finset (Fin N)) {X : Plane}
    (hX : X ∉ interior D.target.carrier) :
    ∑ i ∈ F, (D.tile i).localAngle X ≤ π :=
  (sum_le_target D F X).trans (Tri.localAngle_le_pi _ hX)

/-- If distinct tiles have angles at `X` adding up to more than `π`, `X` is interior. -/
theorem interior_of_sum_gt (F : Finset (Fin N)) {X : Plane}
    (h : π < ∑ i ∈ F, (D.tile i).localAngle X) : X ∈ interior D.target.carrier := by
  by_contra hX
  linarith [sum_le_pi_of_not_interior D F hX]

open Classical in
/-- **Angles on one side of a line.** The angles at `X` of tiles lying in a closed half-plane
bounded by a line through `X` add up to at most `π`. -/
theorem halfplane_sum_le {g : Plane →ₗ[ℝ] ℝ} (hg : g ≠ 0) {X : Plane} (F : Finset (Fin N))
    (hF : ∀ i ∈ F, ∀ y ∈ (D.tile i).carrier, g X ≤ g y) :
    ∑ i ∈ F, (D.tile i).localAngle X ≤ π := by
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle X
  obtain ⟨r, hr, -, hrle⟩ := exists_radius_le ri hri 1 one_pos
  set B := ball X r
  set H := {y : Plane | (-g) y ≤ -(g X)}
  have hHm : MeasurableSet H :=
    (isClosed_le (continuous_functional (-g)) continuous_const).measurableSet
  have hhalf := volume_ball_inter_half (neg_ne_zero.mpr hg) (Q := X) (c := -(g X)) (by simp) r
  have hsub : (⋃ i ∈ F, (D.tile i).carrier ∩ B) ⊆ B ∩ H := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨i, hi, hyT, hyB⟩ := hy
    refine ⟨hyB, ?_⟩
    simp only [H, Set.mem_setOf_eq, LinearMap.neg_apply, neg_le_neg_iff]
    exact hF i hi y hyT
  have hU := measure_biUnion_finset₀ (μ := volume) (s := F)
    (f := fun i => (D.tile i).carrier ∩ B)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter isOpen_ball.measurableSet.nullMeasurableSet)
  have hle := measure_mono (μ := volume) hsub
  rw [hU, Finset.sum_congr rfl (fun i _ => hcontrib i r hr (hrle i)),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (D.tile i).localAngle_nonneg X; positivity)] at hle
  have hB : volume B = ENNReal.ofReal (π * r ^ 2) := volume_ball_plane X hr.le
  have h2 : volume (B ∩ H) = ENNReal.ofReal (π / 2 * r ^ 2) := by
    rw [hB] at hhalf
    have : ENNReal.ofReal (π * r ^ 2) = 2 * ENNReal.ofReal (π / 2 * r ^ 2) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [this] at hhalf
    exact ((ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp hhalf).symm
  rw [h2, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  rw [← Finset.sum_mul, ← Finset.sum_div] at hle
  have hr2 : 0 < r ^ 2 := by positivity
  have : (∑ i ∈ F, (D.tile i).localAngle X) * r ^ 2 ≤ π * r ^ 2 := by linarith
  exact le_of_mul_le_mul_right this hr2

end Sums

end TriangleTiling.Prime
