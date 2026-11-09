/-
The trapezoid lemma (`lemma:block`), third step: the tiles east of `σ` are `∇_{s-1-j, j}`. The top
one has its `β` at `q_r = R` (with `γ` the angles at `R` would exceed `2π`), hence `γ` at `q_{r-1}`;
at a point `q_j` inside `σ` at most one tile east of `σ` has its `γ` angle (`γ > π/2`), so by
downward induction the tile on `q_j q_{j+1}` has `γ` at `q_j` and `β` at `q_{j+1}`; it is the
half-turn image of `Δ_{s-1-j, j}`, namely `∇_{s-1-j, j}`.
-/
import TriangleTiling.Prime.RunsEdgeEnds

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

section BlockC

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

/-- East of `σ`: `b crdI + c crdJ ≥ bcs`. -/
def EastOf (U I J : Plane) (b c s : ℝ) (y : Plane) : Prop :=
  (b * c) * s ≤ b * crdI U I J y + c * crdJ U I J y

omit hS hF in
theorem eastF_apply (y : Plane) :
    lineF I J b c y = b * crdI U I J y + c * crdJ U I J y + lineF I J b c U :=
  lineF_apply U I J y b c

omit hS hF in
theorem east_carrier {t : Fin N} {s : ℝ} (hE : ∀ l, EastOf U I J b c s ((D.tile t).pts l)) :
    ∀ y ∈ (D.tile t).carrier, EastOf U I J b c s y := by
  intro y hy
  refine (convexHull_min (t := {y | EastOf U I J b c s y}) ?_ ?_) hy
  · rintro _ ⟨l, rfl⟩; exact hE l
  · intro y1 hy1 y2 hy2 p q hp hq hpq
    simp only [Set.mem_setOf_eq, EastOf] at hy1 hy2 ⊢
    have e : p • y1 + q • y2 = AffineMap.lineMap y1 y2 q := by
      rw [AffineMap.lineMap_apply_module, show 1 - q = p by linarith]
    rw [e, crdI_affine, crdJ_affine, show 1 - q = p by linarith]
    have h1 := mul_le_mul_of_nonneg_left hy1 hp
    have h2 := mul_le_mul_of_nonneg_left hy2 hq
    have h3 : b * c * s = p * (b * c * s) + q * (b * c * s) := by rw [← add_mul, hpq, one_mul]
    nlinarith

/-- A tile east of the line `φ = bcs` has a vertex strictly east of it, if two of its vertices are
on it. -/
theorem strict_east {t : Fin N} {s : ℝ} (hE : ∀ l, EastOf U I J b c s ((D.tile t).pts l))
    {Z : Plane} (hZ : Z ∈ Set.range (D.tile t).pts) {P Q : Plane} (hP : P ∈ Set.range (D.tile t).pts)
    (hQ : Q ∈ Set.range (D.tile t).pts) (hPQ : P ≠ Q) (hZP : Z ≠ P) (hZQ : Z ≠ Q)
    (hPl : b * crdI U I J P + c * crdJ U I J P = (b * c) * s)
    (hQl : b * crdI U I J Q + c * crdJ U I J Q = (b * c) * s) :
    (b * c) * s < b * crdI U I J Z + c * crdJ U I J Z := by
  obtain ⟨lZ, rfl⟩ := hZ
  refine lt_of_le_of_ne (hE lZ) fun h => ?_
  have hb := hS.b_pos; have hc := hS.c_pos
  apply two_vertices_on_line (D.tile t) (lineF I J b c) ((b * c) * s + lineF I J b c U)
    (lineF_ne_zero hF.hIJ (Or.inl hb.ne'))
  intro i
  rw [eastF_apply (U := U)]
  obtain ⟨lP, rfl⟩ := hP
  obtain ⟨lQ, rfl⟩ := hQ
  have hlPQ : lP ≠ lQ := fun h => hPQ (by rw [h])
  have hlZP : lZ ≠ lP := fun h => hZP (by rw [h])
  have hlZQ : lZ ≠ lQ := fun h => hZQ (by rw [h])
  have : i = lZ ∨ i = lP ∨ i = lQ := by
    revert hlPQ hlZP hlZQ; fin_cases i <;> fin_cases lZ <;> fin_cases lP <;> fin_cases lQ <;>
      decide
  rcases this with rfl | rfl | rfl
  · rw [← h]
  · rw [hPl]
  · rw [hQl]


/-- **The top tile east of `σ` has its `β` angle at `R`**: with `γ` there, the angles at `R` of the
tile north of `ℓ_r`, `∇_{s-r-1,r-1}`, `Δ_{s-r,r-1}` and it would exceed `2π`. -/
theorem block_top {r s : ℕ} (hr : 1 ≤ r) (hrs : r < s) (hT : TOccurs D (lat U I J b c) s r)
    {N₀ : Fin N} (hN₀ : (D.tile N₀).localAngle (lat U I J b c ((s : ℝ) - r) r) = π)
    {E' : Fin N} (hE : ∀ l, EastOf U I J b c s ((D.tile E').pts l))
    (h2 : HasAngle D E' (lat U I J b c ((s : ℝ) - r) r) γ) : False := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  set x := lat U I J b c
  have hφ : ∀ u v : ℝ, b * crdI U I J (x u v) + c * crdJ U I J (x u v) = b * c * (u + v) := by
    intro u v; rw [crdI_x hF, crdJ_x hF]; ring
  -- the tiles at `R`
  obtain ⟨tR, htR⟩ := hT.2 (s - r - 1) (r - 1) (by omega) (by omega)
  obtain ⟨tD, htD⟩ := hT.1 (s - r) (r - 1) (by omega) (by omega)
  obtain ⟨-, -, hRα⟩ := nabla_angles hS hF htR
  obtain ⟨-, -, hDγ⟩ := delta_angles hS hF htD
  have e1 : x (((s - r - 1 : ℕ) : ℝ) + 1) (((r - 1 : ℕ) : ℝ) + 1) = x ((s : ℝ) - r) r := by
    rw [Nat.cast_sub hr, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; congr 1 <;> ring
  have e2 : x ((s - r : ℕ) : ℝ) (((r - 1 : ℕ) : ℝ) + 1) = x ((s : ℝ) - r) r := by
    rw [Nat.cast_sub hr, Nat.cast_sub (by omega)]; congr 1; ring
  replace hRα : HasAngle D tR (x ((s : ℝ) - r) r) α := e1 ▸ hRα
  replace hDγ : HasAngle D tD (x ((s : ℝ) - r) r) γ := e2 ▸ hDγ
  have l1 := localAngle_of_hasAngle hRα
  have l2 := localAngle_of_hasAngle hDγ
  have l3 := localAngle_of_hasAngle h2
  have hγπ : γ < π := by linarith
  have hαγ : α ≠ γ := by intro h; linarith
  have hαπ : α < π := by linarith
  have n01 : N₀ ≠ tR := tile_ne_of_angle (by rw [hN₀, l1]; exact hαπ.ne')
  have n02 : N₀ ≠ tD := tile_ne_of_angle (by rw [hN₀, l2]; exact hγπ.ne')
  have n03 : N₀ ≠ E' := tile_ne_of_angle (by rw [hN₀, l3]; exact hγπ.ne')
  have n12 : tR ≠ tD := tile_ne_of_angle (by rw [l1, l2]; exact hαγ)
  have n13 : tR ≠ E' := tile_ne_of_angle (by rw [l1, l3]; exact hαγ)
  have n23 : tD ≠ E' := by
    apply tile_ne_of_pt (P := x ((s - r : ℕ) : ℝ) ((r - 1 : ℕ) : ℝ)) (by rw [htD]; simp)
    rintro ⟨l, hl⟩
    have := hE l
    rw [hl] at this
    unfold EastOf at this
    rw [hφ, Nat.cast_sub hr, Nat.cast_sub (by omega), Nat.cast_one] at this
    have : (0 : ℝ) < b * c := by positivity
    nlinarith
  have := sum4_le D n01 n02 n03 n12 n13 n23 (x ((s : ℝ) - r) r)
  rw [hN₀, l1, l2, l3] at this
  have := target_le_two_pi D (x ((s : ℝ) - r) r)
  linarith

/-- **The tiles east of `σ` are the `∇_{s-1-i, i}`** (third step of `lemma:block`). -/
theorem block_nablas {r s : ℕ} (hr : 1 ≤ r) (E : ℕ → Fin N)
    (hE : ∀ i < r, ∀ l, EastOf U I J b c s ((D.tile (E i)).pts l))
    (hEe : ∀ i < r, TileEdge D (E i) (lat U I J b c ((s : ℝ) - i) i)
      (lat U I J b c ((s : ℝ) - i - 1) (i + 1)))
    (htop : ¬ HasAngle D (E (r - 1)) (lat U I J b c ((s : ℝ) - r) r) γ) :
    ∀ i < r, Set.range (D.tile (E i)).pts = {lat U I J b c ((s : ℝ) - i) i,
        lat U I J b c ((s : ℝ) - i - 1) (i + 1), lat U I J b c ((s : ℝ) - i) (i + 1)} ∧
      HasAngle D (E i) (lat U I J b c ((s : ℝ) - i) i) γ := by
  classical
  have ha := hS.a_pos; have hb := hS.b_pos; have hc := hS.c_pos
  obtain ⟨hα, hβ, hγ0, hsum⟩ := hS.angles_pos
  have hγ := hS.gamma
  have hrel := hS.rel
  set x := lat U I J b c
  have hda : ∀ i : ℕ, dist (x ((s : ℝ) - i) i) (x ((s : ℝ) - i - 1) (i + 1)) = a := by
    intro i
    have := dist_W hS hF ((s : ℝ) - i - 1) i
    rwa [show (s : ℝ) - i - 1 + 1 = s - i by ring] at this
  have hφ : ∀ u v : ℝ, b * crdI U I J (x u v) + c * crdJ U I J (x u v) = b * c * (u + v) := by
    intro u v; rw [crdI_x hF, crdJ_x hF]; ring
  -- Points of `σ` are distinct.
  have hqne : ∀ i i' : ℕ, i ≠ i' → x ((s : ℝ) - i) i ≠ x ((s : ℝ) - i') i' := by
    intro i i' h e
    have := (x_inj hS hF e).2; exact h (by exact_mod_cast this)
  -- The angle claim, by downward induction.
  have key : ∀ d i, i + d + 1 = r → HasAngle D (E i) (x ((s : ℝ) - i) i) γ ∧
      HasAngle D (E i) (x ((s : ℝ) - i - 1) (i + 1)) β := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hir : i < r := by omega
      have hiR : x ((s : ℝ) - i - 1) (i + 1) = x ((s : ℝ) - r) r := by
        have : (r : ℝ) = i + 1 := by exact_mod_cast hi.symm
        rw [this]; congr 1; ring
      rcases (hS.edge_ends (hEe i hir)).1 (hda i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso
        rw [hiR] at h2
        have : i = r - 1 := by omega
        subst this
        exact htop h2
      · exact ⟨h1, h2⟩
    | succ d ih =>
      intro i hi
      have hir : i < r := by omega
      obtain ⟨g1, g2⟩ := ih (i + 1) (by omega)
      have e3 : x ((s : ℝ) - ((i + 1 : ℕ) : ℝ)) ((i + 1 : ℕ) : ℝ) = x ((s : ℝ) - i - 1) (i + 1) := by
        push_cast; congr 1; ring
      rw [e3] at g1
      rcases (hS.edge_ends (hEe i hir)).1 (hda i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso
        -- two `γ` angles at `q_{i+1}` east of `σ`
        have hne : E i ≠ E (i + 1) := by
          intro h
          rw [h] at h1
          have := hS.hasAngle_unique h1 g2
          have h' := (x_inj hS hF this).2
          push_cast at h'; linarith
        have hgX : ∀ t ∈ ({E i, E (i + 1)} : Finset (Fin N)), ∀ y ∈ (D.tile t).carrier,
            lineF I J b c (x ((s : ℝ) - i - 1) (i + 1)) ≤ lineF I J b c y := by
          intro t ht y hy
          rw [eastF_apply (U := U), eastF_apply (U := U) (y := y), hφ]
          have hEt : ∀ l, EastOf U I J b c s ((D.tile t).pts l) := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with rfl | rfl
            · exact hE i hir
            · exact hE (i + 1) (by omega)
          have : EastOf U I J b c s y := east_carrier hEt y hy
          unfold EastOf at this
          linarith
        have hsum2 := halfplane_sum_le D.toDissection (lineF_ne_zero hF.hIJ (Or.inl hb.ne'))
          _ hgX
        rw [Finset.sum_pair hne, localAngle_of_hasAngle h2, localAngle_of_hasAngle g1] at hsum2
        linarith
      · exact ⟨h1, h2⟩
  intro i hi
  obtain ⟨hγi, hβi⟩ := key (r - 1 - i) i (by omega)
  refine ⟨?_, hγi⟩
  -- Identify the third vertex.
  obtain ⟨lP, hlP, haP⟩ := hγi
  obtain ⟨lQ, hlQ, haQ⟩ := hβi
  have hPQ : x ((s : ℝ) - i) i ≠ x ((s : ℝ) - i - 1) (i + 1) := by
    intro h; have := (x_inj hS hF h).2; linarith
  obtain ⟨Z, hZr, hZP, hZQ, hdP, hdQ⟩ := third_vertex hlP hlQ hPQ
  rw [(hS.opp_of_angle lQ).2.1 haQ] at hdP
  rw [(hS.opp_of_angle lP).2.2 haP] at hdQ
  set Z' := x ((s : ℝ) - i) (i + 1)
  have hdP' : dist (x ((s : ℝ) - i) i) Z' = b := dist_J hS hF _ _
  have hdQ' : dist (x ((s : ℝ) - i - 1) (i + 1)) Z' = c := by
    have := dist_I hS hF ((s : ℝ) - i - 1) (i + 1)
    rwa [show (s : ℝ) - i - 1 + 1 = s - i by ring] at this
  have hZeast := strict_east hS hF (hE i hi) (hZr ▸ (by simp)) (hZr ▸ (by simp))
    (hZr ▸ (by simp)) hPQ hZP hZQ (by rw [hφ]; ring) (by rw [hφ]; ring)
  have hZZ : Z = Z' := by
    apply eq_of_dist_dist (A := x ((s : ℝ) - i) i) (B := x ((s : ℝ) - i - 1) (i + 1))
    · rw [dist_comm, hdP, dist_comm, hdP']
    · rw [dist_comm, hdQ, dist_comm, hdQ']
    · rw [cross_frame (U := U) hF.hIJ, cross_frame (U := U) hF.hIJ]
      simp only [Z', x, crdI_x hF, crdJ_x hF]
      have hcIJ : 0 < cross I J * cross I J := mul_self_pos.mpr hF.hIJ
      have h' : 0 < b * crdI U I J Z + c * crdJ U I J Z - b * c * s := by linarith
      have e : ((((s : ℝ) - i - 1) * c - ((s : ℝ) - i) * c) * (crdJ U I J Z - i * b) -
          (((i : ℝ) + 1) * b - i * b) * (crdI U I J Z - ((s : ℝ) - i) * c)) =
          -(b * crdI U I J Z + c * crdJ U I J Z - b * c * s) := by ring
      rw [e]
      have e2 : ((((s : ℝ) - i - 1) * c - ((s : ℝ) - i) * c) * (((i : ℝ) + 1) * b - i * b) -
          (((i : ℝ) + 1) * b - i * b) * (((s : ℝ) - i) * c - ((s : ℝ) - i) * c)) = -(b * c) := by
        ring
      rw [e2]
      have : 0 < b * c := by positivity
      nlinarith [mul_pos (mul_pos h' this) hcIJ]
  rw [hZr, hZZ]

end BlockC

end TriangleTiling.Prime
