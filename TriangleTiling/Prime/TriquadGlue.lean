/-
Tools for `theorem:triquadratic` (Section 13 of Beeson–Roșu): the carrier of a triangle split by a
cevian, and gluing two congruent dissections along a common side.
-/
import TriangleTiling.Prime.Triquad
import Erdos634.CellCoord
import Erdos634.Draft.GlueCut

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real

theorem range_three (x y z : Plane) : Set.range ![x, y, z] = {x, y, z} := by
  ext p
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_succ,
    Fin.exists_fin_zero]
  simp [eq_comm]

/-- A segment through an interior point splits into two. -/
theorem segment_split {B C Z : Plane} {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1)
    (hC : C = B + μ • (Z - B)) :
    segment ℝ B C ∪ segment ℝ C Z = segment ℝ B Z := by
  have hCm : C ∈ segment ℝ B Z := by
    rw [segment_eq_image_lineMap]
    exact ⟨μ, ⟨h0, h1⟩, by rw [AffineMap.lineMap_apply_module', hC]; module⟩
  apply Set.Subset.antisymm
  · exact Set.union_subset ((convex_segment B Z).segment_subset (left_mem_segment ℝ B Z) hCm)
      ((convex_segment B Z).segment_subset hCm (right_mem_segment ℝ B Z))
  · intro x hx
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨t, ⟨t0, t1⟩, rfl⟩ := hx
    rw [AffineMap.lineMap_apply_module']
    rcases le_or_gt t μ with htμ | htμ
    · left
      rcases eq_or_lt_of_le h0 with hμ | hμ
      · have : t = 0 := by linarith
        subst this; rw [zero_smul, zero_add]; exact left_mem_segment ℝ B C
      rw [segment_eq_image_lineMap]
      refine ⟨t / μ, ⟨div_nonneg t0 hμ.le, (div_le_one hμ).mpr htμ⟩, ?_⟩
      rw [AffineMap.lineMap_apply_module', hC, show B + μ • (Z - B) - B = μ • (Z - B) by abel,
        smul_smul, div_mul_cancel₀ _ hμ.ne']
    · right
      have hμ1 : μ < 1 := lt_of_lt_of_le htμ t1
      rw [segment_eq_image_lineMap]
      refine ⟨(t - μ) / (1 - μ), ⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith)).mpr (by linarith)⟩, ?_⟩
      rw [AffineMap.lineMap_apply_module', hC]
      have e : (1 - μ) ≠ 0 := by linarith
      have : ((t - μ) / (1 - μ)) • (Z - (B + μ • (Z - B))) = (t - μ) • (Z - B) := by
        rw [show Z - (B + μ • (Z - B)) = (1 - μ) • (Z - B) by module, smul_smul,
          div_mul_cancel₀ _ e]
      rw [this]; module

/-- **A triangle split by a cevian.** If `C` is on the segment `BZ`, the triangles `ABC` and `ZCA`
make up `ZAB`. -/
theorem hull_split {A B C Z : Plane} {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1)
    (hC : C = B + μ • (Z - B)) :
    convexHull ℝ {A, B, C} ∪ convexHull ℝ {Z, C, A} = convexHull ℝ {Z, A, B} := by
  have e1 : ({Z, C, A} : Set Plane) = insert A {C, Z} := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have e2 : ({Z, A, B} : Set Plane) = insert A {B, Z} := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [e1, e2, convexHull_insert (Set.insert_nonempty _ _), convexHull_insert
    (Set.insert_nonempty _ _), convexHull_insert (Set.insert_nonempty _ _), convexHull_pair,
    convexHull_pair, convexHull_pair, ← convexJoin_union_right, segment_split h0 h1 hC]

/-- The affine function `x ↦ κ · cross u (x - A)`. -/
noncomputable def crossAff (κ : ℝ) (u A : Plane) : Plane →ᵃ[ℝ] ℝ :=
  (κ • crossL u).toAffineMap + AffineMap.const ℝ Plane (-(κ * cross u A))

theorem crossAff_apply (κ : ℝ) (u A x : Plane) : crossAff κ u A x = κ * cross u (x - A) := by
  show (κ • crossL u) x + -(κ * cross u A) = _
  rw [LinearMap.smul_apply, crossL_apply, smul_eq_mul, cross_sub_right]
  ring

theorem crossAff_linear {κ : ℝ} {u : Plane} (hκ : κ ≠ 0) (hu : u ≠ 0) (A : Plane) :
    (crossAff κ u A).linear ≠ 0 := by
  intro h
  apply crossL_ne_zero hu
  ext v
  have := LinearMap.congr_fun h v
  have e : (crossAff κ u A).linear v = κ * cross u v := by
    show (κ • crossL u) v + (0 : Plane →ₗ[ℝ] ℝ) v = _
    rw [LinearMap.zero_apply, add_zero, LinearMap.smul_apply, crossL_apply, smul_eq_mul]
  rw [e, LinearMap.zero_apply] at this
  simpa using (mul_eq_zero.mp this).resolve_left hκ

/-- **Gluing along a common side.** A congruent dissection of `ABC` and a dissection of `ZCA` into
tiles congruent to the same model, with `C` on the segment `BZ` and `B`, `Z` on opposite sides of
the line `AC`, make a congruent dissection of `ZAB`. -/
theorem glue_tri {N M : ℕ} (D : CongruentDissection N) (E : Dissection M)
    (hE : ∀ i, (E.tile i).Congruent D.model) {A B C Z : Plane}
    (hD : D.target.carrier = convexHull ℝ {A, B, C}) (hEt : E.target.carrier = convexHull ℝ {Z, C, A})
    {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (hC : C = B + μ • (Z - B))
    (hZ : cross (C - A) (Z - A) ≠ 0) (hsep : cross (C - A) (B - A) * cross (C - A) (Z - A) ≤ 0)
    (T' : Tri) (hT' : T'.carrier = convexHull ℝ {Z, A, B}) :
    ∃ D' : CongruentDissection (N + M), D'.target = T' ∧ D'.model = D.model := by
  have hu : C - A ≠ 0 := by
    intro h; apply hZ; rw [h]; simp [cross]
  set f := crossAff (cross (C - A) (Z - A)) (C - A) A
  have hf := crossAff_linear hZ hu A
  have hhalf : ∀ (S : Set Plane) (s : ℝ), (∀ x ∈ S, s * f x ≤ 0) →
      ∀ x ∈ convexHull ℝ S, s * f x ≤ 0 := by
    intro S s h x hx
    have hconv : Convex ℝ ((fun y => s * f y) ⁻¹' Set.Iic 0) := by
      have : (fun y => s * f y) = (s • f : Plane →ᵃ[ℝ] ℝ) := by
        funext y; simp [smul_eq_mul]
      rw [this]; exact (convex_Iic (0 : ℝ)).affine_preimage _
    exact convexHull_min (fun y hy => h y hy) hconv hx
  have h1' : ∀ x ∈ D.target.carrier, f x ≤ 0 := by
    intro x hx
    rw [hD] at hx
    have := hhalf _ 1 (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [one_mul, crossAff_apply]
      rcases hy with h | h | h <;> rw [h]
      · simp [Erdos634.Geometry.cross_zero_right]
      · linarith [hsep]
      · rw [Erdos634.Geometry.cross_self, mul_zero]) x hx
    linarith
  have h2' : ∀ x ∈ E.target.carrier, 0 ≤ f x := by
    intro x hx
    rw [hEt] at hx
    have := hhalf _ (-1) (by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rw [crossAff_apply]
      rcases hy with h | h | h <;> rw [h]
      · nlinarith [sq_nonneg (cross (C - A) (Z - A))]
      · rw [Erdos634.Geometry.cross_self, mul_zero, mul_zero]
      · simp [Erdos634.Geometry.cross_zero_right]) x hx
    linarith
  let C2 : Erdos634.RegionDissection.CongruentRegionDissection M :=
    { toRegionDissection := E.toRegion, model := D.model, tiles_congruent := hE }
  have hdisj := Erdos634.GlueCut.interiors_disjoint_of_cut f hf h1' h2'
  let U := Erdos634.RegionDissection.unionCongruentRegion D.toRegion C2 rfl hdisj
  have hreg : U.region = T'.carrier := by
    show D.target.carrier ∪ E.target.carrier = T'.carrier
    rw [hD, hEt, hT', hull_split h0 h1 hC]
  exact ⟨U.toCongruentDissection T' hreg, rfl, rfl⟩

/-- **The triangle `ZAB`.** With `Z = C + s(C - B)`, `s > 0`, angles `2α` at `A` and `β` at `B`
in `ABC`, and `β` at `Z`, `α` at `A` in `ZCA`, the triangle `ZAB` is nondegenerate with angles
`β, 3α, β` at `Z, A, B`; `C` lies on `BZ`, and `B`, `Z` are on opposite sides of `AC`. -/
theorem zab_facts {A B C Z : Plane} {s α β : ℝ} (hs : 0 < s) (hZ : Z = C + s • (C - B))
    (nA : cross (B - A) (C - A) ≠ 0)
    (h0 : InnerProductGeometry.angle (B - A) (C - A) = 2 * α)
    (hB : InnerProductGeometry.angle (C - B) (A - B) = β)
    (hAZC : InnerProductGeometry.angle (A - Z) (C - Z) = β)
    (hCAZ : InnerProductGeometry.angle (C - A) (Z - A) = α) :
    cross (A - Z) (B - Z) ≠ 0 ∧
    InnerProductGeometry.angle (A - Z) (B - Z) = β ∧
    InnerProductGeometry.angle (B - A) (Z - A) = 3 * α ∧
    InnerProductGeometry.angle (Z - B) (A - B) = β ∧
    C = B + (1 / (1 + s)) • (Z - B) ∧
    cross (C - A) (Z - A) ≠ 0 ∧ cross (C - A) (B - A) * cross (C - A) (Z - A) ≤ 0 := by
  subst hZ
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have vZB : C + s • (C - B) - B = (1 + s) • (C - B) := by module
  have vBZ : B - (C + s • (C - B)) = (1 + s) • (B - C) := by module
  have vCZ : C - (C + s • (C - B)) = s • (B - C) := by module
  have vZA : C + s • (C - B) - A = (1 + s) • (C - A) - s • (B - A) := by module
  have e1 : cross (B - A) (C + s • (C - B) - A) = (1 + s) * cross (B - A) (C - A) := by
    rw [vZA, cross_sub_right, cross_smul_right, cross_smul_right,
      Erdos634.Geometry.cross_self, mul_zero, sub_zero]
  have e2 : cross (C - A) (C + s • (C - B) - A) = s * cross (B - A) (C - A) := by
    rw [vZA, cross_sub_right, cross_smul_right, cross_smul_right,
      Erdos634.Geometry.cross_self, mul_zero, zero_sub, cross_swap (C - A) (B - A)]; ring
  have e3 : cross (C - A) (B - A) = -cross (B - A) (C - A) := cross_swap _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : cross (A - (C + s • (C - B))) (B - (C + s • (C - B))) =
        (1 + s) * cross (B - A) (C - A) := by
      simp only [cross]; simp; ring
    rw [e]; exact mul_ne_zero h1s.ne' nA
  · rw [vBZ, InnerProductGeometry.angle_smul_right_of_pos _ _ h1s,
      ← InnerProductGeometry.angle_smul_right_of_pos _ (B - C) hs, ← vCZ, hAZC]
  · have hne : cross (B - A) (C + s • (C - B) - A) ≠ 0 := by
      rw [e1]; exact mul_ne_zero h1s.ne' nA
    have hw0 : C - A ≠ 0 := ne_zero_right_of_cross nA
    have hadd := angle_add_cone hne hw0
      ⟨by rw [e1]; nlinarith [sq_nonneg (cross (B - A) (C - A))],
        by rw [e1, e2]
           have := mul_nonneg (mul_nonneg hs.le h1s.le) (sq_nonneg (cross (B - A) (C - A)))
           linarith [show s * cross (B - A) (C - A) * ((1 + s) * cross (B - A) (C - A)) =
             s * (1 + s) * cross (B - A) (C - A) ^ 2 by ring]⟩
    rw [hadd, hCAZ, h0]; ring
  · rw [vZB, InnerProductGeometry.angle_smul_left_of_pos _ _ h1s, hB]
  · rw [vZB, smul_smul, one_div, inv_mul_cancel₀ h1s.ne', one_smul]; abel
  · rw [e2]; exact mul_ne_zero hs.ne' nA
  · rw [e2, e3]; nlinarith [sq_nonneg (cross (B - A) (C - A))]

/-- **The quadratic tiling.** A triangle `ZCA` with sides `|ZC| = Ka`, `|CA| = Kb`, `|ZA| = Kc` is
cut into `K²` tiles congruent to the tile (`Erdos634.Subdivision.ladderDissection`). -/
theorem ladder_tri {N : ℕ} {D : CongruentDissection N} {α β γ a b c : ℝ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) {C Z A : Plane} {K : ℕ} (hK : 0 < K)
    (hZC : dist Z C = K * a) (hCA : dist A C = K * b) (hZA : dist Z A = K * c)
    (hnd : cross (Z - C) (A - C) ≠ 0) :
    ∃ E : Dissection (K * K), (∀ i, (E.tile i).Congruent D.model) ∧
      E.target.carrier = convexHull ℝ {Z, C, A} := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set B0 := C + (1 / (K : ℝ)) • (Z - C)
  set C0 := C + (1 / (K : ℝ)) • (A - C)
  have vB : B0 - C = (1 / (K : ℝ)) • (Z - C) := by simp only [B0]; abel
  have vC : C0 - C = (1 / (K : ℝ)) • (A - C) := by simp only [C0]; abel
  have vBC : B0 - C0 = (1 / (K : ℝ)) • (Z - A) := by simp only [B0, C0]; module
  have hind : AffineIndependent ℝ ![C, B0, C0] := by
    apply affineIndependent_of_cross'
    rw [vB, vC, cross_smul_left, cross_smul_right]
    exact mul_ne_zero (by positivity) (mul_ne_zero (by positivity) hnd)
  have scale : ∀ {X Y U V : Plane} {r : ℝ}, X - Y = (1 / (K : ℝ)) • (U - V) →
      dist U V = K * r → dist X Y = r := by
    intro X Y U V r h hd
    rw [dist_eq_norm, h, norm_smul, ← dist_eq_norm, hd, Real.norm_of_nonneg (by positivity)]
    field_simp
  have d1 : dist B0 C = a := scale vB hZC
  have d2 : dist C0 C = b := scale vC hCA
  have d3 : dist B0 C0 = c := scale vBC hZA
  obtain ⟨σ, ma, mb, mc⟩ := model_dists hT
  have ht0 : (⟨![C, B0, C0], hind⟩ : Tri).Congruent D.model := by
    refine Erdos634.SssCongruent.congruent_of_dist_perm ((Equiv.swap 0 2).trans σ) ?_
    intro i j
    have d1' : dist C B0 = a := by rw [dist_comm]; exact d1
    have d2' : dist C C0 = b := by rw [dist_comm]; exact d2
    have d3' : dist C0 B0 = c := by rw [dist_comm]; exact d3
    have ma' : dist (D.model.pts (σ 2)) (D.model.pts (σ 1)) = a := by rw [dist_comm]; exact ma
    have mb' : dist (D.model.pts (σ 2)) (D.model.pts (σ 0)) = b := by rw [dist_comm]; exact mb
    have mc' : dist (D.model.pts (σ 1)) (D.model.pts (σ 0)) = c := by rw [dist_comm]; exact mc
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.swap_apply_def, d1, d2, d3, d1', d2', d3', ma, mb, mc, ma', mb', mc']
  refine ⟨Erdos634.Subdivision.ladderDissection C B0 C0 hind K hK, fun i =>
    (Erdos634.Subdivision.ladderDissection_congruent C B0 C0 hind K hK i).symm.trans ht0, ?_⟩
  show (Erdos634.Subdivision.bigTri C B0 C0 hind K hK).carrier = _
  have hP1 : Erdos634.Subdivision.P C B0 C0 K 0 = Z := by
    simp only [Erdos634.Subdivision.P, vB, vC, smul_smul, Nat.cast_zero, zero_mul, zero_smul,
      add_zero]
    rw [mul_one_div_cancel hK'.ne', one_smul]; abel
  have hP2 : Erdos634.Subdivision.P C B0 C0 0 K = A := by
    simp only [Erdos634.Subdivision.P, vB, vC, smul_smul, Nat.cast_zero, zero_mul, zero_smul,
      add_zero]
    rw [mul_one_div_cancel hK'.ne', one_smul]; abel
  unfold Tri.carrier
  rw [show (Erdos634.Subdivision.bigTri C B0 C0 hind K hK).pts = ![C, Z, A] by
    rw [← hP1, ← hP2]; rfl, range_three]
  congr 1
  ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

end TriangleTiling.Prime
