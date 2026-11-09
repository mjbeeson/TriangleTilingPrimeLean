/-
The trapezoid lemma (`lemma:block`), fourth step: at `x(s - j, j)`, `1 ≤ j ≤ r - 1`, the five tiles
`Δ_{s-j-1,j}`, `Δ_{s-j,j-1}`, `∇_{s-j-1,j-1}`, `∇_{s-j-1,j}`, `∇_{s-j,j-1}` leave a sector of angle
`α` between the `b` edge of `∇_{s-j-1,j}` and the `c` edge of `∇_{s-j,j-1}`; by `lemma:angles` it is
filled by one tile `G_j` with its `α` angle there, whose sides there are its `b` and `c` edges. So
`G_j = Δ_{s-j,j}`, or `G_j` has its `b` edge on `ℓ_j`, running east from `x(s - j, j)`.
-/
import TriangleTiling.Prime.RunsSide

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

omit hS in
theorem angle_eq_of_two {t : Fin N} {X : Plane} {θ θ' : ℝ} (h : HasAngle D t X θ)
    (h' : HasAngle D t X θ') : θ = θ' := by
  obtain ⟨l, hl, ha⟩ := h
  obtain ⟨l', hl', ha'⟩ := h'
  rw [← ha, ← ha', (D.tile t).indep.injective (hl.trans hl'.symm)]

theorem tileEdge_len {t : Fin N} {P Q : Plane} (h : TileEdge D t P Q) :
    dist P Q = a ∨ dist P Q = b ∨ dist P Q = c := by
  obtain ⟨e, he⟩ := tileEdge_edge h
  have := hS.edge_len t e
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rwa [h1, h2] at this
  · rwa [h1, h2, dist_comm] at this

/-- **At an `α` corner the two sides are `b` and `c`.** -/
theorem alpha_pair {t : Fin N} {X Y Z : Plane} (hX : HasAngle D t X α)
    (h : Set.range (D.tile t).pts = {X, Y, Z}) (hXY : X ≠ Y) (hXZ : X ≠ Z) (hYZ : Y ≠ Z) :
    (dist X Y = b ∧ dist X Z = c) ∨ (dist X Y = c ∧ dist X Z = b) := by
  have eXY : TileEdge D t X Y := tileEdge_of_range h (by simp) (by simp) hXY
  have eXZ : TileEdge D t X Z := tileEdge_of_range h (by simp) (by simp) hXZ
  have hαβ := hS.alpha_ne_beta
  have hαγ : α ≠ γ := by have := hS.gamma; have := hS.angles_pos; intro h; linarith
  have key : ∀ W, TileEdge D t X W → (dist X W = b ∧ HasAngle D t W γ) ∨
      (dist X W = c ∧ HasAngle D t W β) := by
    intro W hW
    obtain ⟨ea, eb, ec⟩ := hS.edge_ends hW
    rcases hS.tileEdge_len hW with hd | hd | hd
    · rcases ea hd with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (angle_eq_of_two hX h1) hαβ
      · exact absurd (angle_eq_of_two hX h1) hαγ
    · rcases eb hd with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact Or.inl ⟨hd, h2⟩
      · exact absurd (angle_eq_of_two hX h1) hαγ
    · rcases ec hd with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact Or.inr ⟨hd, h2⟩
      · exact absurd (angle_eq_of_two hX h1) hαβ
  rcases key Y eXY with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases key Z eXZ with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact absurd (hS.hasAngle_unique h2 h4) hYZ
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inr ⟨h1, h3⟩
  · exact absurd (hS.hasAngle_unique h2 h4) hYZ

end RunSetting

section BlockD

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

omit hS hF in
theorem lat_eq {u v u' v' : ℝ} (hu : u = u') (hv : v = v') :
    lat U I J b c u v = lat U I J b c u' v' := by rw [hu, hv]

/-- **A sector of angle `α` between `I` and `J`** at `X` is filled by `Δ` (its `c` edge along `I`,
its `b` edge along `J`), or by a tile north of the line of `X` with its `b` edge running east from
`X`. -/
theorem G_core {X : Plane} {v₀ : ℝ} (hu : RayWall D.toDissection X I)
    (hv : RayWall D.toDissection X J)
    (hin : ∃ r > (0 : ℝ), sectorC X I J ∩ ball X r ⊆ D.target.carrier)
    (hX0 : crdJ U I J X = v₀ * b) :
    (∃ G, Set.range (D.tile G).pts = {X, X + c • I, X + b • J}) ∨
      ∃ G, (∀ l, v₀ * b ≤ crdJ U I J ((D.tile G).pts l)) ∧ TileEdge D G X (X + b • I) := by
  have hb := hS.b_pos; have hc := hS.c_pos
  -- The sector of angle `α`.
  obtain ⟨G, ⟨σ, hσ, τ, hτ, hG⟩, hGα, -⟩ := sector_one hS hF.hIJ hu hv hin (P := 1) (Q := 0)
    (by norm_num) (by rw [hF.aIJ]; ring)
  have hGα' : HasAngle D G X α := by simpa using hGα
  have hIne : I ≠ 0 := fun h => by have := hF.nI; rw [h, norm_zero] at this; exact zero_ne_one this
  have hJne : J ≠ 0 := fun h => by have := hF.nJ; rw [h, norm_zero] at this; exact zero_ne_one this
  have hd1 : dist X (X + σ • I) = σ := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nI, mul_one,
      Real.norm_of_nonneg hσ.le]
  have hd2 : dist X (X + τ • J) = τ := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hF.nJ, mul_one,
      Real.norm_of_nonneg hτ.le]
  have n1 : X ≠ X + σ • I := fun h => by rw [← h, dist_self] at hd1; linarith
  have n2 : X ≠ X + τ • J := fun h => by rw [← h, dist_self] at hd2; linarith
  have n3 : X + σ • I ≠ X + τ • J := by
    intro h
    have := congrArg (crdJ U I J) h
    rw [crdJ_addv, crdJ_addv, cross_smul_right, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero, zero_div,
      mul_div_assoc, div_self hF.hIJ] at this
    linarith
  rcases hS.alpha_pair hGα' hG n1 n2 n3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `b` along `I`, `c` along `J`
    right
    rw [hd1] at h1
    refine ⟨G, fun l => ?_, ?_⟩
    · have : (D.tile G).pts l ∈ Set.range (D.tile G).pts := ⟨l, rfl⟩
      rw [hG] at this
      rcases this with h | h | h <;> rw [h]
      · rw [hX0]
      · rw [crdJ_addv, cross_smul_right, Erdos634.Geometry.cross_self, mul_zero, zero_div, add_zero,
          hX0]
      · rw [crdJ_addv, cross_smul_right, mul_div_assoc, div_self hF.hIJ, mul_one, hX0]; linarith
    · rw [← h1]; exact tileEdge_of_range hG (by simp) (by simp) n1
  · -- `c` along `I`, `b` along `J`: `G = Δ_{s-q, q}`
    left
    rw [hd1] at h1; rw [hd2] at h2
    refine ⟨G, ?_⟩
    rw [hG, h1, h2]


/-- **The tile `G_j`** (fourth step of `lemma:block`). -/
theorem block_G {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hT : TOccurs D (lat U I J b c) s r)
    (E : ℕ → Fin N)
    (hnab : ∀ i < r, Set.range (D.tile (E i)).pts = {lat U I J b c ((s : ℝ) - i) i,
        lat U I J b c ((s : ℝ) - i - 1) (i + 1), lat U I J b c ((s : ℝ) - i) (i + 1)} ∧
      HasAngle D (E i) (lat U I J b c ((s : ℝ) - i) i) γ)
    {q : ℕ} (hq1 : 1 ≤ q) (hqr : q < r) :
    ((∃ G, Set.range (D.tile G).pts = {lat U I J b c ((s : ℝ) - q) q,
        lat U I J b c ((s : ℝ) - q + 1) q, lat U I J b c ((s : ℝ) - q) (q + 1)}) ∨
      ∃ G, (∀ l, (q : ℝ) * b ≤ crdJ U I J ((D.tile G).pts l)) ∧
        TileEdge D G (lat U I J b c ((s : ℝ) - q) q) (lat U I J b c ((s : ℝ) - q) q + b • I)) := by
  classical
  have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  set x := lat U I J b c
  set X := x ((s : ℝ) - q) q
  have hq1' : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub hq1]; simp
  -- The two rays.
  have hXI : X + c • I = x ((s : ℝ) - q + 1) q := by
    simp only [X, x]; rw [show c • I = (1 * c) • I by rw [one_mul], lat_add_I]
  have hXJ : X + b • J = x ((s : ℝ) - q) (q + 1) := by
    simp only [X, x]; rw [show b • J = (1 * b) • J by rw [one_mul], lat_add_J]
  have hEq1 := (hnab (q - 1) (by omega)).1
  have hEq := (hnab q hqr).1
  have hu : RayWall D.toDissection X I := by
    refine rayWall_of_tileEdge (t := E (q - 1)) hc ?_
    rw [hXI]
    refine tileEdge_of_range hEq1 ?_ ?_ ?_
    · right; left; exact lat_eq (by rw [hq1']; ring) (by rw [hq1']; ring)
    · right; right; exact lat_eq (by rw [hq1']; ring) (by rw [hq1']; ring)
    · intro h; have := (x_inj hS hF h).1; linarith
  have hv : RayWall D.toDissection X J := by
    refine rayWall_of_tileEdge (t := E q) hb ?_
    rw [hXJ]
    refine tileEdge_of_range hEq (by simp [X]) (by simp) ?_
    intro h; have := (x_inj hS hF h).2; linarith
  -- `X` is interior.
  obtain ⟨t1, ht1⟩ := hT.2 (s - q - 1) (q - 1) (by omega) (by omega)
  obtain ⟨t2, ht2⟩ := hT.1 (s - q - 1) q (by omega) (by omega)
  obtain ⟨t3, ht3⟩ := hT.1 (s - q) (q - 1) (by omega) (by omega)
  have hsq1 : ((s - q - 1 : ℕ) : ℝ) = s - q - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  have hsq : ((s - q : ℕ) : ℝ) = s - q := by rw [Nat.cast_sub (by omega)]
  obtain ⟨-, -, a1⟩ := nabla_angles hS hF ht1
  obtain ⟨-, a2, -⟩ := delta_angles hS hF ht2
  obtain ⟨-, -, a3⟩ := delta_angles hS hF ht3
  have e1 : x (((s - q - 1 : ℕ) : ℝ) + 1) (((q - 1 : ℕ) : ℝ) + 1) = X :=
    lat_eq (by rw [hsq1]; ring) (by rw [hq1']; ring)
  have e2 : x (((s - q - 1 : ℕ) : ℝ) + 1) (q : ℝ) = X := lat_eq (by rw [hsq1]; ring) rfl
  have e3 : x ((s - q : ℕ) : ℝ) (((q - 1 : ℕ) : ℝ) + 1) = X :=
    lat_eq (by rw [hsq]) (by rw [hq1']; ring)
  replace a1 : HasAngle D t1 X α := e1 ▸ a1
  replace a2 : HasAngle D t2 X β := e2 ▸ a2
  replace a3 : HasAngle D t3 X γ := e3 ▸ a3
  have a4 := (hnab q hqr).2
  have l1 := localAngle_of_hasAngle a1
  have l2 := localAngle_of_hasAngle a2
  have l3 := localAngle_of_hasAngle a3
  have l4 := localAngle_of_hasAngle a4
  have hαβ := hS.alpha_ne_beta
  have hαγ : α ≠ γ := by intro h; linarith
  have hβγ : β ≠ γ := by intro h; linarith
  have n12 : t1 ≠ t2 := tile_ne_of_angle (by rw [l1, l2]; exact hαβ)
  have n13 : t1 ≠ t3 := tile_ne_of_angle (by rw [l1, l3]; exact hαγ)
  have n14 : t1 ≠ E q := tile_ne_of_angle (by rw [l1, l4]; exact hαγ)
  have n23 : t2 ≠ t3 := tile_ne_of_angle (by rw [l2, l3]; exact hβγ)
  have n24 : t2 ≠ E q := tile_ne_of_angle (by rw [l2, l4]; exact hβγ)
  have n34 : t3 ≠ E q := by
    apply Ne.symm
    apply tile_ne_of_pt (P := x ((s : ℝ) - q) (q + 1)) (by rw [hEq]; simp)
    rw [ht3]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have := (x_inj hS hF h) <;>
      rw [hsq, hq1'] at this <;> linarith [this.1, this.2]
  have hXint : X ∈ interior D.target.carrier := by
    by_contra hni
    have := sum4_le D n12 n13 n14 n23 n24 n34 X
    rw [l1, l2, l3, l4] at this
    have := target_le_pi D hni
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior X hXint
  have hin : ∃ r > (0 : ℝ), sectorC X I J ∩ ball X r ⊆ D.target.carrier :=
    ⟨ε, hε, fun y hy => interior_subset (hball hy.2)⟩
  rcases G_core hS hF hu hv hin (v₀ := q) (by simp only [X, x]; rw [crdJ_x hF]) with
    ⟨G, hG⟩ | ⟨G, hGn, hGe⟩
  · left; exact ⟨G, by rw [hG, hXI, hXJ]⟩
  · right; exact ⟨G, hGn, hGe⟩

end BlockD

end TriangleTiling.Prime
