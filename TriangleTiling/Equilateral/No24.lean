/-
`lemma:threeangles` and the geometric part of `lemma:no24` of M. Beeson, *Tiling an equilateral
triangle* (arXiv 1811.09723). Statements checked by Beeson.

The tile has angles `(α, β, π/3)` with `α ∉ ℚπ`. `threeangles`: where the tiles with a vertex at `V`
have angles adding up to `π`, they are `α, β, π/3` (one each) or three `π/3`. The counts used below
(`counts60`) also cover tiles with `V` inside an edge, and corners.

`no24geom`: the tile `(3u, 8u, 7u)` cannot tile an equilateral triangle of side `24u`. The proof is
the paper's (as revised 2026-11-05). The tile `T₁` at `A` has its `a` and `b` edges on
`AB` and `AC`; say its `b` edge `AV` is on `AB` (else exchange `B` and `C`), so `T₁` has its `α` at
`V`, its `β` at `X` on `AC`, and its `c` edge `VX` runs through `ABC`. The tiles on the other side of
`VX` have edges summing to `7`, so there is just one, `T'`, with its `c` edge on `VX`; it has its
`β` at `V` (an `α` would be a second at `V`). So no tile on `AB` has its `β` at `V` (it would be
`T'`, with `β + α = π`). The pigeonhole on `AB` then gives at least one `a` edge and two `b` edges
there, while the edges on `AB` have lengths `3i + 8j + 7k = 24`: impossible.
-/
import TriangleTiling.TwoCs.TwoCs

namespace TriangleTiling.Equilateral

open Erdos634.Geometry EuclideanGeometry Set TriangleTiling.TwoCs

variable {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
  (hγ : tileγ D = Real.pi / 3) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)

open Classical in
/-- The number of tiles with a vertex at `V` and angle `θ` there. -/
noncomputable def vertexCount (V : Plane) (θ : ℝ) : ℕ :=
  ({i | ∃ l, (D.tile i).pts l = V ∧ (D.tile i).angleAt l = θ} : Finset (Fin N)).card

open TriangleTiling.ThreeAlpha in
/-- **Lemma `lemma:threeangles`.** Suppose the equilateral triangle `ABC` is tiled by a tile with
angles `(α, β, π/3)` with `β` not a rational multiple of `π`. Then every vertex `V` with angle sum
`π` has three tiles with vertices at `V`, either all `π/3` angles or one each of `α`, `β`, and
`π/3`.

"Angle sum `π` at `V`" is: the angles at `V` of the tiles with a vertex at `V` add up to `π`. The
hypothesis that `ABC` is equilateral is not used. -/
theorem threeangles {α β a b c : ℝ} (hT : TileSides D α β (Real.pi / 3) a b c)
    (hβ : ¬ ∃ r : ℚ, β = (r : ℝ) * Real.pi) (V : Plane)
    (hV : (vertexCount D V α : ℝ) * α + vertexCount D V β * β +
      vertexCount D V (Real.pi / 3) * (Real.pi / 3) = Real.pi) :
    (vertexCount D V α = 0 ∧ vertexCount D V β = 0 ∧ vertexCount D V (Real.pi / 3) = 3) ∨
      (vertexCount D V α = 1 ∧ vertexCount D V β = 1 ∧ vertexCount D V (Real.pi / 3) = 1) := by
  obtain ⟨-, -, -, hsum⟩ := tileSides_angles D hT
  set x := vertexCount D V α
  set y := vertexCount D V β
  set z := vertexCount D V (Real.pi / 3)
  have hα : α = 2 * Real.pi / 3 - β := by linarith
  rw [hα] at hV
  have key : ((y : ℝ) - x) * β = ((3 : ℝ) - 2 * x - z) / 3 * Real.pi := by linarith
  have hxy : x = y := by
    by_contra hne
    have hne' : (y : ℝ) - x ≠ 0 := by
      intro h; apply hne; exact_mod_cast (show (x : ℝ) = y by linarith)
    apply hβ
    refine ⟨((3 : ℚ) - 2 * x - z) / 3 / ((y : ℚ) - x), ?_⟩
    push_cast
    field_simp
    linear_combination 3 * key
  rw [hxy] at key
  have h3 : ((2 * y + z : ℕ) : ℝ) = 3 := by
    push_cast
    have : ((3 : ℝ) - 2 * y - z) / 3 * Real.pi = 0 := by rw [← key]; ring
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith [Real.pi_pos]
  have h3' : 2 * y + z = 3 := by exact_mod_cast h3
  omega

include hsep hγ hirr in
/-- The weighted counts at a point where the target's local angle is `k π / 3` (`k = 1` at a
corner, `k = 3` inside a side): as many `α` as `β`, and `2 y + z + 3 u + 6 w = k`. -/
theorem counts60 (P : Plane) {k : ℕ} (hk : D.target.localAngle P = k * (Real.pi / 3)) :
    angleCount D P (tileα D) = angleCount D P (tileβ D) ∧
      2 * angleCount D P (tileβ D) + angleCount D P (tileγ D) + 3 * angleCount D P Real.pi +
        6 * angleCount D P (2 * Real.pi) = k := by
  have hs := counts_sum D hsep P
  rw [hk, hγ] at hs
  have hsum := tile_angle_sum D
  rw [hγ] at hsum
  set x := angleCount D P (tileα D)
  set y := angleCount D P (tileβ D)
  set z := angleCount D P (Real.pi / 3)
  set u := angleCount D P Real.pi
  set w := angleCount D P (2 * Real.pi)
  have hπ := Real.pi_pos
  have hβ : tileβ D = 2 * Real.pi / 3 - tileα D := by linarith
  rw [hβ] at hs
  have key : ((x : ℝ) - y) * tileα D =
      ((k : ℝ) - 2 * y - z - 3 * u - 6 * w) / 3 * Real.pi := by linarith
  have hxy : x = y := by
    by_contra hne
    have hne' : (x : ℝ) - y ≠ 0 := by
      intro h; apply hne; exact_mod_cast (show (x : ℝ) = y by linarith)
    apply hirr
    refine ⟨((k : ℚ) - 2 * y - z - 3 * u - 6 * w) / 3 / ((x : ℚ) - y), ?_⟩
    push_cast
    field_simp
    linear_combination 3 * key
  refine ⟨hxy, ?_⟩
  rw [hγ]
  rw [hxy] at key
  have : ((2 * y + z + 3 * u + 6 * w : ℕ) : ℝ) = k := by
    push_cast
    have : ((k : ℝ) - 2 * y - z - 3 * u - 6 * w) / 3 * Real.pi = 0 := by rw [← key]; ring
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  exact_mod_cast this

include hsep hγ hirr in
/-- **Inside a side**: as many `α` as `β`, and `2 y + z + 3 u + 6 w = 3`. -/
theorem side60 {P : Plane} (hP : P ∈ frontier D.target.carrier) (hPc : P ∉ Set.range D.target.pts) :
    angleCount D P (tileα D) = angleCount D P (tileβ D) ∧
      2 * angleCount D P (tileβ D) + angleCount D P (tileγ D) + 3 * angleCount D P Real.pi +
        6 * angleCount D P (2 * Real.pi) = 3 :=
  counts60 D hsep hγ hirr P (k := 3) (by rw [D.target.localAngle_frontier hP hPc]; push_cast; ring)

include hsep hγ hirr in
/-- **At a corner** of angle `π/3`: one `γ`, nothing else. -/
theorem corner60 (k : Fin 3) (hk : D.target.angleAt k = Real.pi / 3) :
    angleCount D (D.target.pts k) (tileα D) = 0 ∧ angleCount D (D.target.pts k) (tileβ D) = 0 ∧
      angleCount D (D.target.pts k) (tileγ D) = 1 ∧ angleCount D (D.target.pts k) Real.pi = 0 := by
  obtain ⟨h1, h2⟩ := counts60 D hsep hγ hirr (D.target.pts k) (k := 1)
    (by rw [Tri.localAngle_vertex]; push_cast; rw [one_mul, ← hk]; rfl)
  omega

/-! ### Small facts -/

/-- A finite sum of `3`s, `7`s and `8`s, by the number of each. -/
theorem sum378 {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (h : ∀ x ∈ s, f x = 3 ∨ f x = 7 ∨ f x = 8) :
    ∑ x ∈ s, f x = 3 * (s.filter (f · = 3)).card + 7 * (s.filter (f · = 7)).card +
      8 * (s.filter (f · = 8)).card ∧
    s.card = (s.filter (f · = 3)).card + (s.filter (f · = 7)).card +
      (s.filter (f · = 8)).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    have hfa := h a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha, Finset.filter_insert, Finset.card_insert_of_notMem ha]
    rcases hfa with h3 | h7 | h8
    · simp only [h3, if_true, show (3 : ℕ) ≠ 7 by decide, show (3 : ℕ) ≠ 8 by decide, if_false,
        Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1)]
      omega
    · simp only [h7, if_true, show (7 : ℕ) ≠ 3 by decide, show (7 : ℕ) ≠ 8 by decide, if_false,
        Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1)]
      omega
    · simp only [h8, if_true, show (8 : ℕ) ≠ 3 by decide, show (8 : ℕ) ≠ 7 by decide, if_false,
        Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1)]
      omega

/-- Two points of a segment as far apart as its ends are its ends. -/
theorem seg_full {V X p q : Plane} (hVX : V ≠ X) (hp : p ∈ segment ℝ V X)
    (hq : q ∈ segment ℝ V X) (hd : dist p q = dist V X) :
    (p = V ∧ q = X) ∨ (p = X ∧ q = V) := by
  rw [segment_eq_image_lineMap] at hp hq
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hp
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  rw [dist_lineMap_lineMap, Real.dist_eq] at hd
  have hpos : 0 < dist V X := dist_pos.mpr hVX
  have h1 : |s - t| = 1 := by
    have := mul_right_cancel₀ hpos.ne' (hd.trans (one_mul _).symm)
    exact this
  rcases abs_eq (zero_le_one) |>.mp h1 with h | h
  · right
    have hs : s = 1 := by linarith
    have ht : t = 0 := by linarith
    rw [hs, ht, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]; exact ⟨rfl, rfl⟩
  · left
    have hs : s = 0 := by linarith
    have ht : t = 1 := by linarith
    rw [hs, ht, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero]; exact ⟨rfl, rfl⟩

include hsep in
/-- The side opposite a corner with angle `![α, β, γ] m` has the model's length opposite it. -/
theorem opp_len (i : Fin N) {j j' j'' : Fin 3} (h1 : j' ≠ j) (h2 : j'' ≠ j) (h3 : j' ≠ j'')
    {m : Fin 3} (h : (D.tile i).localAngle ((D.tile i).pts j) = ![tileα D, tileβ D, tileγ D] m) :
    dist ((D.tile i).pts j') ((D.tile i).pts j'') =
      dist (D.model.pts (m + 1)) (D.model.pts (m + 2)) := by
  have e := edge_length D hsep i (j + 1) m (by rwa [show j + 1 + 2 = j by fin_cases j <;> rfl])
  rw [show j + 1 + 1 = j + 2 by fin_cases j <;> rfl, dist_opp (D.tile i) h1 h2 h3] at e
  exact e

include hsep in
open Classical in
/-- **The pigeonhole on a segment.** The edges of `part` lie on `AB` and meet in at most a point.
Each edge whose opposite angle is not `θ` has its `θ` at an end; none at `A`, `B`, or a point of
`Z`, and at most one tile has its `θ` at any point of `AB`. So these edges are at most as many as
the inner ends of the edges, less those in `Z`. -/
theorem inj_count (part : Finset (Fin N × Fin 3)) {A B : Plane}
    (hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B)
    (θ : ℝ) (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D) (Z : Finset Plane)
    (hZ : Z ⊆ (part.image (fun e => (D.tile e.1).pts e.2) ∪
      part.image (fun e => (D.tile e.1).pts (e.2 + 1))).filter (fun x => x ≠ A ∧ x ≠ B))
    (hAθ : ∀ i, (D.tile i).localAngle A ≠ θ) (hBθ : ∀ i, (D.tile i).localAngle B ≠ θ)
    (hZθ : ∀ e ∈ part, ∀ z ∈ Z, ((D.tile e.1).pts e.2 = z ∨ (D.tile e.1).pts (e.2 + 1) = z) →
      (D.tile e.1).localAngle z ≠ θ)
    (htwo : ∀ P ∈ segment ℝ A B, P ≠ A → P ≠ B → angleCount D P θ ≤ 1) :
    (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) ≠ θ).card +
      Z.card ≤ ((part.image (fun e => (D.tile e.1).pts e.2) ∪
        part.image (fun e => (D.tile e.1).pts (e.2 + 1))).filter
          (fun x => x ≠ A ∧ x ≠ B)).card := by
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1)
  set Eint := (part.image u ∪ part.image v).filter (fun x => x ≠ A ∧ x ≠ B)
  set S := part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) ≠ θ
  have hend : ∀ e ∈ S, (D.tile e.1).localAngle (u e) = θ ∨ (D.tile e.1).localAngle (v e) = θ :=
    fun e he => TwoCs.corner_at_endpoint D hsep e.1 e.2 hθ (Finset.mem_filter.mp he).2
  let φ : Fin N × Fin 3 → Plane := fun e =>
    if (D.tile e.1).localAngle (u e) = θ then u e else v e
  have hφθ : ∀ e ∈ S, (D.tile e.1).localAngle (φ e) = θ := by
    intro e he
    simp only [φ]
    split_ifs with h
    · exact h
    · exact (hend e he).resolve_left h
  have hφuv : ∀ e, φ e = u e ∨ φ e = v e := by
    intro e; simp only [φ]; split_ifs <;> simp
  have hφseg : ∀ e ∈ S, φ e ∈ segment ℝ A B := by
    intro e he
    apply hsub e (Finset.mem_filter.mp he).1
    rcases hφuv e with h | h <;> rw [h]
    · exact left_mem_segment _ _ _
    · exact right_mem_segment _ _ _
  have hφE : ∀ e ∈ S, φ e ∈ Eint \ Z := by
    intro e he
    have hep := (Finset.mem_filter.mp he).1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · rcases hφuv e with h | h <;> rw [h]
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hep)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hep)
    · intro h; exact hAθ e.1 (h ▸ hφθ e he)
    · intro h; exact hBθ e.1 (h ▸ hφθ e he)
    · intro hz
      exact hZθ e hep _ hz ((hφuv e).imp Eq.symm Eq.symm) (hφθ e he)
  have hinj : Set.InjOn φ S := by
    intro e he e' he' heq
    by_contra hne
    by_cases h1 : e.1 = e'.1
    · have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact tri_two_edges_on_segment (D.tile e.1) h2 (hsub e (Finset.mem_filter.mp he).1)
        (h1 ▸ hsub e' (Finset.mem_filter.mp he').1)
    · have hE := Finset.mem_filter.mp (Finset.mem_sdiff.mp (hφE e he)).1
      have hle := htwo _ (hφseg e he) hE.2.1 hE.2.2
      exact h1 (eq_of_angleCount_le_one D hle (hφθ e he) (heq ▸ hφθ e' he'))
  have hcard : S.card ≤ (Eint \ Z).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card fun x hx => by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      exact hφE e he
  rw [Finset.card_sdiff_of_subset hZ] at hcard
  have := Finset.card_le_card hZ
  omega

/-! ### The tile `(3, 8, 7)` in a triangle of side `24` -/

section Main

variable {u : ℝ} (hu : 0 < u)
  (ha : dist (D.model.pts 1) (D.model.pts 2) = 3 * u)
  (hb : dist (D.model.pts 2) (D.model.pts 0) = 8 * u)
  (hc : dist (D.model.pts 0) (D.model.pts 1) = 7 * u)
  (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
  (hAB : dist (D.target.pts 0) (D.target.pts 1) = 24 * u)
  (hCA : dist (D.target.pts 2) (D.target.pts 0) = 24 * u)

/-- The length of an edge, in units `u`: `3, 8, 7` as the angle opposite it is `α, β, γ`. -/
noncomputable def len (e : Fin N × Fin 3) : ℕ :=
  if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D then 3
  else if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D then 8 else 7

include hsep ha hb hc in
theorem len_dist (e : Fin N × Fin 3) :
    dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = len D e * u := by
  rcases TwoCs.corner_mem D hsep e.1 (e.2 + 2) with h | h | h
  · have := edge_length D hsep e.1 e.2 0 (by simpa using h)
    rw [this, show (len D e : ℝ) = 3 by simp [len, h]]; simpa using ha
  · have hne : tileβ D ≠ tileα D := fun e => hsep.2.ne (by decide : (1 : Fin 5) ≠ 0) e
    have := edge_length D hsep e.1 e.2 1 (by simpa using h)
    rw [this, show (len D e : ℝ) = 8 by simp [len, h, hne]]; simpa using hb
  · have hne : tileγ D ≠ tileα D := fun e => hsep.2.ne (by decide : (2 : Fin 5) ≠ 0) e
    have hne' : tileγ D ≠ tileβ D := fun e => hsep.2.ne (by decide : (2 : Fin 5) ≠ 1) e
    have := edge_length D hsep e.1 e.2 2 (by simpa using h)
    rw [this, show (len D e : ℝ) = 7 by simp [len, h, hne, hne']]; simpa using hc

theorem len_mem (e : Fin N × Fin 3) : len D e = 3 ∨ len D e = 7 ∨ len D e = 8 := by
  unfold len; split_ifs <;> simp

include hsep hγ hirr hu ha hb hc hP hAB hCA in
open Classical in
/-- **The tile at `A`.** Let the tile `T₁` have its corners at `A`, at `V` on `AB` with its `α`, and
at `X` on `AC` with its `β`. Then `T₁` has its `b` edge `AV` on `AB` and its `c` edge `VX` inside
`ABC`. The `c` edge is matched by one `c` edge of a tile `T'` (no other sum of `3`, `7`, `8` is
`7`), which has its `β` at `V`, so no tile on `AB` has its `β` at `V`. The pigeonhole on `AB` then
gives two `b` edges and an `a` edge on `AB`, but `3i + 8j + 7k = 24` has no such solution. -/
theorem corner_contra {T₁ : Fin N} {jA jV jX : Fin 3} (hAV : jV ≠ jA) (hAX : jX ≠ jA)
    (hVX : jV ≠ jX) (hA : (D.tile T₁).pts jA = D.target.pts 0)
    (hV : (D.tile T₁).pts jV ∈ segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hX : (D.tile T₁).pts jX ∈ segment ℝ (D.target.pts 2) (D.target.pts 0))
    (hαV : (D.tile T₁).localAngle ((D.tile T₁).pts jV) = tileα D)
    (hβX : (D.tile T₁).localAngle ((D.tile T₁).pts jX) = tileβ D) : False := by
  set A := D.target.pts 0 with hAdef
  set B := D.target.pts 1 with hBdef
  set C := D.target.pts 2 with hCdef
  set V := (D.tile T₁).pts jV with hVdef
  set X := (D.tile T₁).pts jX with hXdef
  obtain ⟨hα0, hβ0, hγ0⟩ := angles_pos D hsep
  have hsum := tile_angle_sum D
  have hαβ : tileα D ≠ tileβ D := fun e => hsep.2.ne (by decide : (0 : Fin 5) ≠ 1) e
  have hαγ : tileα D ≠ tileγ D := fun e => hsep.2.ne (by decide : (0 : Fin 5) ≠ 2) e
  have hβγ : tileβ D ≠ tileγ D := fun e => hsep.2.ne (by decide : (1 : Fin 5) ≠ 2) e
  have hT1inj : ∀ {i j : Fin 3}, (D.tile T₁).pts i = (D.tile T₁).pts j → i = j :=
    fun h => (D.tile T₁).indep.injective h
  -- `γ` at `A`.
  have hγA : (D.tile T₁).localAngle A = tileγ D := by
    rw [← hA]
    rcases TwoCs.corner_mem D hsep T₁ jA with h | h | h
    · exact absurd (TwoCs.corner_unique D hsep T₁ (Or.inl rfl) h hαV) hAV.symm
    · exact absurd (TwoCs.corner_unique D hsep T₁ (Or.inr (Or.inl rfl)) h hβX) hAX.symm
    · exact h
  -- The lengths.
  have hlAV : dist A V = 8 * u := by
    rw [← hA, ← hb]
    exact opp_len D hsep T₁ (j := jX) (m := 1) hAX.symm hVX hAV.symm (by simpa using hβX)
  have hlAX : dist A X = 3 * u := by
    rw [← hA, ← ha]
    exact opp_len D hsep T₁ (j := jV) (m := 0) hAV.symm hVX.symm hAX.symm (by simpa using hαV)
  have hlVX : dist V X = 7 * u := by
    rw [← hc]
    exact opp_len D hsep T₁ (j := jA) (m := 2) hAV hAX hVX (by rw [hA]; simpa using hγA)
  have hVA : V ≠ A := fun h => hAV (hT1inj (h.trans hA.symm))
  have hXA : X ≠ A := fun h => hAX (hT1inj (h.trans hA.symm))
  have hVXne : V ≠ X := fun h => hVX (hT1inj h)
  have hVB : V ≠ B := by
    intro h; have := hlAV; rw [h, hAB] at this; linarith
  have hXC : X ≠ C := by
    intro h; have := hlAX; rw [h, dist_comm, hCA] at this; linarith
  have hABne : A ≠ B := D.target.indep.injective.ne (by decide)
  have hVo : V ∈ openSegment ℝ A B := mem_openSegment_of_ne_left_right hVA.symm hVB.symm hV
  have hXo : X ∈ openSegment ℝ C A := mem_openSegment_of_ne_left_right hXC.symm hXA.symm hX
  -- Points inside the sides `AB` and `CA`.
  have side0 : ∀ P ∈ openSegment ℝ A B, P ∈ frontier D.target.carrier ∧ P ∉ Set.range D.target.pts :=
    fun P hP' => ⟨tri_side_subset_frontier D.target 0 (openSegment_subset_segment _ _ _ hP'),
      by rintro ⟨k, rfl⟩; exact Tri.vertex_not_mem_openSegment D.target k 0 hP'⟩
  have side2 : ∀ P ∈ openSegment ℝ C A, P ∈ frontier D.target.carrier ∧ P ∉ Set.range D.target.pts :=
    fun P hP' => ⟨tri_side_subset_frontier D.target 2 (openSegment_subset_segment _ _ _ hP'),
      by rintro ⟨k, rfl⟩; exact Tri.vertex_not_mem_openSegment D.target k 2 hP'⟩
  have hcV := side60 D hsep hγ hirr (side0 V hVo).1 (side0 V hVo).2
  have hcX := side60 D hsep hγ hirr (side2 X hXo).1 (side2 X hXo).2
  have hV1 := angleCount_pos D hαV
  have hX1 := angleCount_pos D hβX
  have cVα : angleCount D V (tileα D) = 1 := by omega
  have cVβ : angleCount D V (tileβ D) = 1 := by omega
  have cVπ : angleCount D V Real.pi = 0 := by omega
  have cXπ : angleCount D X Real.pi = 0 := by omega
  obtain ⟨cAα, cAβ, cAγ, cAπ⟩ := corner60 D hsep hγ hirr 0 (hP 0)
  obtain ⟨cBα, cBβ, -, -⟩ := corner60 D hsep hγ hirr 1 (hP 1)
  rw [← hAdef] at cAα cAβ cAγ cAπ
  rw [← hBdef] at cBα cBβ
  -- `X` is not on `AB`.
  have hXnAB : ∀ Y ∈ segment ℝ A B, Y ≠ X := by
    intro Y hY h
    have h1 := coord_two_of_mem_side D.target hY
    have h2 := (Tri.coord_openSegment D.target 2 hXo).1
    rw [h] at h1; linarith
  -- **The wall `VX`.** `A` is on the side `g > cc`.
  obtain ⟨g, cc, hg, hgV, hgX, hgA⟩ := edge_level (D.tile T₁) hAV.symm hVX.symm hAX.symm
  rw [hA] at hgA
  have hne1 : ∀ e ∈ D.lineChain g cc, e.1 ≠ T₁ :=
    lineChain_tile_ne D.toDissection g cc (j := jA) (by rw [hA]; exact hgA)
  have hendV : ∀ e ∈ D.lineChain g cc,
      V ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e _ h
    have := angleCount_pos D (Tri.localAngle_openSegment _ e.2 h); omega
  have hendX : ∀ e ∈ D.lineChain g cc,
      X ∉ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e _ h
    have := angleCount_pos D (Tri.localAngle_openSegment _ e.2 h); omega
  have hint : openSegment ℝ V X ⊆ interior D.target.carrier := by
    obtain ⟨v0, v1, -⟩ := Tri.coord_openSegment D.target 0 hVo
    obtain ⟨x2, -, -⟩ := Tri.coord_openSegment D.target 2 hXo
    refine openSegment_subset_interior D.target (pts_mem_target D.toDissection T₁ jV)
      (pts_mem_target D.toDissection T₁ jX) fun k => ?_
    fin_cases k
    · exact Or.inl v0
    · exact Or.inl v1
    · exact Or.inr x2
  have hwall : ∀ y ∈ openSegment ℝ V X, ∀ i, y ∉ interior (D.tile i).carrier := by
    obtain ⟨m, hm⟩ : ∃ m : Fin 3, (m = jV ∧ m + 1 = jX) ∨ (m = jX ∧ m + 1 = jV) :=
      (by decide : ∀ q r : Fin 3, q ≠ r → ∃ m : Fin 3, (m = q ∧ m + 1 = r) ∨ (m = r ∧ m + 1 = q))
        jV jX hVX
    have h := openEdge_not_interior D.toDissection T₁ m
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, h1] at h; exact h
    · rw [h2, h1, openSegment_symm] at h; exact h
  have hS := chain_sum D.toDissection hg hVXne hgV hgX hendV hendX hint hwall
  set S := (D.lineChain g cc).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ V X)
  have hS7 : ∑ e ∈ S, len D e = 7 := by
    have : ((∑ e ∈ S, len D e : ℕ) : ℝ) * u = 7 * u := by
      rw [Nat.cast_sum, Finset.sum_mul, ← hlVX, ← hS]
      exact Finset.sum_congr rfl fun e _ => (len_dist D hsep ha hb hc e).symm
    exact_mod_cast mul_right_cancel₀ hu.ne' this
  obtain ⟨hS1, hS2⟩ := sum378 S (len D) (fun e _ => len_mem D e)
  obtain ⟨ep, hep⟩ : ∃ ep, S = {ep} := Finset.card_eq_one.mp (by
    revert hS1 hS2 hS7
    generalize (S.filter (len D · = 3)).card = p
    generalize (S.filter (len D · = 7)).card = q
    generalize (S.filter (len D · = 8)).card = r
    intro h1 h2 h3
    have := h2.symm.trans h1
    have hp : p ≤ 2 := by omega
    have hq : q ≤ 1 := by omega
    interval_cases p <;> interval_cases q <;> omega)
  have hepS : ep ∈ S := by rw [hep]; exact Finset.mem_singleton_self _
  have hep7 : len D ep = 7 := by rw [hep, Finset.sum_singleton] at hS7; exact hS7
  obtain ⟨hepC, hepsub⟩ := Finset.mem_filter.mp hepS
  set Tp := ep.1
  have hTp1 : Tp ≠ T₁ := hne1 ep hepC
  have hends := seg_full hVXne (hepsub (left_mem_segment _ _ _)) (hepsub (right_mem_segment _ _ _))
    (by rw [len_dist D hsep ha hb hc, hep7, hlVX]; norm_num)
  -- `T'` has its `γ` opposite the edge, so its `β` at `V`.
  have hopp : (D.tile Tp).localAngle ((D.tile Tp).pts (ep.2 + 2)) = tileγ D := by
    rcases TwoCs.corner_mem D hsep Tp (ep.2 + 2) with h | h | h
    · simp [len, Tp, h] at hep7
    · simp [len, Tp, h, hαβ.symm] at hep7
    · exact h
  obtain ⟨iV, iX, hiVX, hiV, hiX, hiV2, hiX2⟩ : ∃ iV iX : Fin 3, iV ≠ iX ∧ (D.tile Tp).pts iV = V ∧
      (D.tile Tp).pts iX = X ∧ iV ≠ ep.2 + 2 ∧ iX ≠ ep.2 + 2 := by
    have h02 : ep.2 ≠ ep.2 + 2 := (by decide : ∀ k : Fin 3, k ≠ k + 2) _
    have h12 : ep.2 + 1 ≠ ep.2 + 2 := (by decide : ∀ k : Fin 3, k + 1 ≠ k + 2) _
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨ep.2, ep.2 + 1, fin3_ne_add_one _, h1, h2, h02, h12⟩
    · exact ⟨ep.2 + 1, ep.2, (fin3_ne_add_one _).symm, h2, h1, h12, h02⟩
  have hβV : (D.tile Tp).localAngle V = tileβ D := by
    rw [← hiV]
    rcases TwoCs.corner_mem D hsep Tp iV with h | h | h
    · rw [hiV] at h
      exact absurd (eq_of_angleCount_le_one D cVα.le h hαV) hTp1
    · exact h
    · exact absurd (TwoCs.corner_unique D hsep Tp (Or.inr (Or.inr rfl)) h hopp) hiV2
  -- **The side `AB`.**
  obtain ⟨part, hcov, hdisj, hlen⟩ := D.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ A B := hcov
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B :=
    fun e he y hy => by rw [← hcov']; exact Set.mem_biUnion he hy
  -- The edge of `T₁` on `AB` is `AV`.
  obtain ⟨eA, heA, heA1, heAends⟩ : ∃ eA ∈ part, eA.1 = T₁ ∧
      (((D.tile eA.1).pts eA.2 = A ∧ (D.tile eA.1).pts (eA.2 + 1) = V) ∨
        ((D.tile eA.1).pts eA.2 = V ∧ (D.tile eA.1).pts (eA.2 + 1) = A)) := by
    have hAseg : A ∈ segment ℝ A B := left_mem_segment _ _ _
    rw [← hcov'] at hAseg
    obtain ⟨e, he, hAe⟩ := Set.mem_iUnion₂.mp hAseg
    rw [Tri.edge, ← insert_endpoints_openSegment] at hAe
    -- `A` is an end of the edge, and the tile is `T₁`.
    have hend : ∀ j : Fin 3, (D.tile e.1).pts j = A → e.1 = T₁ ∧ j = jA := by
      intro j hj
      have hγe : (D.tile e.1).localAngle A = tileγ D := by
        rw [← hj]
        rcases TwoCs.corner_mem D hsep e.1 j with h | h | h
        · rw [hj] at h; exact absurd h (ne_of_angleCount_zero D cAα e.1)
        · rw [hj] at h; exact absurd h (ne_of_angleCount_zero D cAβ e.1)
        · exact h
      have h1 : e.1 = T₁ := eq_of_angleCount_le_one D cAγ.le hγe hγA
      refine ⟨h1, ?_⟩
      rw [h1] at hj; exact hT1inj (hj.trans hA.symm)
    -- The other end is on `AB`, so it is `V`.
    have hother : ∀ j : Fin 3, j ≠ jA → (D.tile e.1).pts j ∈ segment ℝ A B → e.1 = T₁ →
        j = jV := by
      intro j hj hjs h1
      rw [h1] at hjs
      have : j = jA ∨ j = jV ∨ j = jX := by
        revert hAV hAX hVX hj; fin_cases j <;> fin_cases jA <;> fin_cases jV <;> fin_cases jX <;>
          simp
      rcases this with h | h | h
      · exact absurd h hj
      · exact h
      · exact absurd (by rw [h]) (hXnAB _ hjs)
    rcases hAe with h | h | h
    · obtain ⟨h1, h2⟩ := hend _ h.symm
      have h3 := hother (e.2 + 1) (fun h' => fin3_ne_add_one e.2 (h2.trans h'.symm))
        (hsub e he (right_mem_segment _ _ _)) h1
      exact ⟨e, he, h1, Or.inl ⟨h.symm, by rw [h1, h3]⟩⟩
    · obtain ⟨h1, h2⟩ := hend _ h.symm
      have h3 := hother e.2 (fun h' => fin3_ne_add_one e.2 (h'.trans h2.symm))
        (hsub e he (left_mem_segment _ _ _)) h1
      exact ⟨e, he, h1, Or.inr ⟨by rw [h1, h3], h.symm⟩⟩
    · exact absurd (angleCount_pos D (Tri.localAngle_openSegment _ e.2 h)) (by omega)
  have heAedge : (D.tile eA.1).edge eA.2 = segment ℝ V A := by
    rcases heAends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Tri.edge, h1, h2, segment_symm]
    · rw [Tri.edge, h1, h2]
  -- **No tile on `AB` has its `β` at `V`**: it would be `T'`, with an edge `VY` on `AB`; then
  -- `∠ Y V X + ∠ X V A = π`, that is `β + α = π`.
  have hnoβ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) →
      (D.tile e.1).localAngle V ≠ tileβ D := by
    intro e he hendV' hβe
    have h1 : e.1 = Tp := eq_of_angleCount_le_one D cVβ.le hβe hβV
    have hne : e ≠ eA := fun h => hTp1 (h1.symm.trans (h ▸ heA1))
    have hTpinj : ∀ {i j : Fin 3}, (D.tile Tp).pts i = (D.tile Tp).pts j → i = j :=
      fun h => (D.tile Tp).indep.injective h
    obtain ⟨iY, hiY, hYseg, hedge⟩ : ∃ iY : Fin 3, iY ≠ iV ∧
        (D.tile Tp).pts iY ∈ segment ℝ A B ∧
        (D.tile e.1).edge e.2 = segment ℝ V ((D.tile Tp).pts iY) := by
      rcases hendV' with h | h
      · rw [h1] at h
        refine ⟨e.2 + 1, fun h' => fin3_ne_add_one e.2 (hTpinj (h.trans (h' ▸ hiV).symm)), ?_, ?_⟩
        · have := hsub e he (right_mem_segment _ _ _); rwa [h1] at this
        · rw [Tri.edge, h1, h]
      · rw [h1] at h
        refine ⟨e.2, fun h' => fin3_ne_add_one e.2 (hTpinj ((h' ▸ hiV).trans h.symm)), ?_, ?_⟩
        · have := hsub e he (left_mem_segment _ _ _); rwa [h1] at this
        · rw [Tri.edge, h1, h, segment_symm]
    set Y := (D.tile Tp).pts iY
    have hYX : Y ≠ X := hXnAB _ hYseg
    have hiYX : iY ≠ iX := fun h => hYX (by rw [← hiX, ← h])
    have hVY : V ≠ Y := fun h => hiY (hTpinj (hiV.trans h)).symm
    have hsubs := hdisj e he eA heA hne
    rw [hedge, heAedge] at hsubs
    have hπ := opposite_of_subsingleton hABne hV hYseg (left_mem_segment _ _ _) hVY hVA hsubs
    have hsupp := angle_supp (Z := X) hπ
    have hT1V := corner_angle_eq (D.tile T₁) (j := jV) (j' := jX) (j'' := jA) hVX.symm hAV.symm hAX
    have hTpV := corner_angle_eq (D.tile Tp) (j := iV) (j' := iY) (j'' := iX) hiY hiVX.symm hiYX
    rw [hA, ← hVdef, ← hXdef, hαV] at hT1V
    rw [hiV, hiX, hβV] at hTpV
    linarith
  -- **The pigeonhole on `AB`.**
  have htwo : ∀ θ, (θ = tileα D ∨ θ = tileβ D) →
      ∀ P ∈ segment ℝ A B, P ≠ A → P ≠ B → angleCount D P θ ≤ 1 := by
    intro θ hθ P hP' hPA hPB
    have hPo := mem_openSegment_of_ne_left_right hPA.symm hPB.symm hP'
    have := side60 D hsep hγ hirr (side0 P hPo).1 (side0 P hPo).2
    rcases hθ with rfl | rfl <;> omega
  have hVE : V ∈ (part.image (fun e => (D.tile e.1).pts e.2) ∪
      part.image (fun e => (D.tile e.1).pts (e.2 + 1))).filter (fun x => x ≠ A ∧ x ≠ B) := by
    refine Finset.mem_filter.mpr ⟨?_, hVA, hVB⟩
    rcases heAends with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨eA, heA, h2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨eA, heA, h1⟩)
  have hIα := inj_count D hsep part hsub (tileα D) (Or.inl rfl) ∅ (Finset.empty_subset _)
    (fun i => ne_of_angleCount_zero D cAα i) (fun i => ne_of_angleCount_zero D cBα i)
    (fun _ _ _ hz => absurd hz (Finset.notMem_empty _)) (htwo _ (Or.inl rfl))
  have hIβ := inj_count D hsep part hsub (tileβ D) (Or.inr (Or.inl rfl)) {V}
    (Finset.singleton_subset_iff.mpr hVE)
    (fun i => ne_of_angleCount_zero D cAβ i) (fun i => ne_of_angleCount_zero D cBβ i)
    (fun e he z hz hend => by
      rw [Finset.mem_singleton] at hz; subst hz; exact hnoβ e he hend)
    (htwo _ (Or.inr rfl))
  have hchain := (segment_chain_endpoints A B hABne part (fun e => (D.tile e.1).pts e.2)
    (fun e => (D.tile e.1).pts (e.2 + 1)) (fun e _ => tri_pts_succ_ne _ _) hcov' hdisj).1
  -- The lengths: `3 p + 7 q + 8 r = 24`.
  have hL24 : ∑ e ∈ part, len D e = 24 := by
    have : ((∑ e ∈ part, len D e : ℕ) : ℝ) * u = 24 * u := by
      rw [Nat.cast_sum, Finset.sum_mul, ← hAB]
      rw [show (0 : Fin 3) + 1 = 1 from rfl] at hlen
      rw [← hlen]
      exact Finset.sum_congr rfl fun e _ => (len_dist D hsep ha hb hc e).symm
    exact_mod_cast mul_right_cancel₀ hu.ne' this
  obtain ⟨hP1, hP2⟩ := sum378 part (len D) (fun e _ => len_mem D e)
  have e3 : part.filter (len D · = 3) = part.filter
      (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D) := by
    apply Finset.filter_congr
    intro e _
    unfold len
    split_ifs with h1 h2 <;> simp [h1]
  have e8 : part.filter (len D · = 8) = part.filter
      (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D) := by
    apply Finset.filter_congr
    intro e _
    unfold len
    split_ifs with h1 h2
    · simp only [show (3 : ℕ) ≠ 8 by decide, false_iff]; rw [h1]; exact hαβ
    · simp [h2]
    · simp only [show (7 : ℕ) ≠ 8 by decide, false_iff]; exact h2
  have hfα := Finset.card_filter_add_card_filter_not (s := part)
    (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D)
  have hfβ := Finset.card_filter_add_card_filter_not (s := part)
    (fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D)
  rw [← e3] at hfα
  rw [← e8] at hfβ
  simp only [← ne_eq] at hfα hfβ
  rw [Finset.card_singleton] at hIβ
  rw [Finset.card_empty] at hIα
  revert hIα hIβ hchain hL24 hP1 hP2 hfα hfβ
  generalize (part.filter (len D · = 3)).card = p
  generalize (part.filter (len D · = 7)).card = q
  generalize (part.filter (len D · = 8)).card = r
  generalize (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) ≠
    tileα D).card = sα
  generalize (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) ≠
    tileβ D).card = sβ
  intro hIα hIβ hchain hL24 hP1 hP2 hfα hfβ
  have := hP1.symm.trans hL24
  have hr : r ≤ 3 := by omega
  have hq : q ≤ 3 := by omega
  interval_cases r <;> interval_cases q <;> omega

include hsep hγ hirr in
open Classical in
/-- An edge of a side partition with an end at the corner `A`, the other end on the side, and its
tile's `γ` at `A`. -/
theorem edge_at_corner (hP0 : D.target.angleAt 0 = Real.pi / 3) {S₁ S₂ : Plane}
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ S₁ S₂)
    (hA : D.target.pts 0 ∈ segment ℝ S₁ S₂) :
    ∃ (T : Fin N) (jA j : Fin 3), j ≠ jA ∧ (D.tile T).pts jA = D.target.pts 0 ∧
      (D.tile T).pts j ∈ segment ℝ S₁ S₂ ∧
      (D.tile T).localAngle (D.target.pts 0) = tileγ D := by
  obtain ⟨cAα, cAβ, -, cAπ⟩ := corner60 D hsep hγ hirr 0 hP0
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ S₁ S₂ :=
    fun e he y hy => by rw [← hcov]; exact Set.mem_biUnion he hy
  rw [← hcov] at hA
  obtain ⟨e, he, hAe⟩ := Set.mem_iUnion₂.mp hA
  rw [Tri.edge, ← insert_endpoints_openSegment] at hAe
  have hγe : ∀ j : Fin 3, (D.tile e.1).pts j = D.target.pts 0 →
      (D.tile e.1).localAngle (D.target.pts 0) = tileγ D := by
    intro j hj
    rw [← hj]
    rcases TwoCs.corner_mem D hsep e.1 j with h | h | h
    · rw [hj] at h; exact absurd h (ne_of_angleCount_zero D cAα e.1)
    · rw [hj] at h; exact absurd h (ne_of_angleCount_zero D cAβ e.1)
    · exact h
  rcases hAe with h | h | h
  · exact ⟨e.1, e.2, e.2 + 1, (fin3_ne_add_one _).symm, h.symm,
      hsub e he (right_mem_segment _ _ _), hγe _ h.symm⟩
  · exact ⟨e.1, e.2 + 1, e.2, fin3_ne_add_one _, h.symm,
      hsub e he (left_mem_segment _ _ _), hγe _ h.symm⟩
  · exact absurd (angleCount_pos D (Tri.localAngle_openSegment _ e.2 h)) (by omega)

include hsep hγ hirr in
open Classical in
/-- **The tile at `A`**: one tile, with its `γ` at `A` and its other corners on `AB` and `AC`. -/
theorem corner_tile (hP0 : D.target.angleAt 0 = Real.pi / 3) :
    ∃ (T : Fin N) (jA j₀ j₂ : Fin 3), j₀ ≠ jA ∧ j₂ ≠ jA ∧ j₀ ≠ j₂ ∧
      (D.tile T).pts jA = D.target.pts 0 ∧
      (D.tile T).pts j₀ ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) ∧
      (D.tile T).pts j₂ ∈ segment ℝ (D.target.pts 2) (D.target.pts 0) := by
  obtain ⟨-, -, cAγ, -⟩ := corner60 D hsep hγ hirr 0 hP0
  obtain ⟨part0, hcov0, -, -⟩ := D.toDissection.side_walk 0
  obtain ⟨part2, hcov2, -, -⟩ := D.toDissection.side_walk 2
  obtain ⟨T, jA, j₀, h0A, hA, h0, hγT⟩ := edge_at_corner D hsep hγ hirr hP0 part0 hcov0
    (left_mem_segment _ _ _)
  obtain ⟨T', jA', j₂, h2A, hA', h2, hγT'⟩ := edge_at_corner D hsep hγ hirr hP0 part2 hcov2
    (right_mem_segment _ _ _)
  have hTT : T' = T := eq_of_angleCount_le_one D cAγ.le hγT' hγT
  subst hTT
  have hjA : jA' = jA := (D.tile T').indep.injective (hA'.trans hA.symm)
  subst hjA
  refine ⟨T', jA', j₀, j₂, h0A, h2A, fun h => ?_, hA, h0, h2⟩
  subst h
  -- A point on both `AB` and `CA` is `A`.
  have c2 := coord_two_of_mem_side D.target h0
  have c1 : D.target.basis.coord 1 ((D.tile T').pts j₀) = 0 := by
    have h2' := h2
    rw [segment_eq_image_lineMap] at h2'
    obtain ⟨t, -, ht⟩ := h2'
    rw [← ht, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]; simp
  have := eq_vertex_of_two_coords D.target (i := 1) (j := 2) (l := 0) (by decide) (by decide)
    (by decide) c1 c2
  exact h0A ((D.tile T').indep.injective (this.trans hA.symm))

end Main

open TriangleTiling.ThreeAlpha in
/-- **The geometric part of `lemma:no24`.** An equilateral triangle of side `24u` cannot be tiled
by the tile `(α, β, π/3)` with sides `(3u, 8u, 7u)` and `α ∉ ℚπ`. -/
theorem no24geom {α β u : ℝ} (hu : 0 < u) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) (3 * u) (8 * u) (7 * u))
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hside : ∀ k, D.target.oppLen k = 24 * u) :
    False := by
  obtain ⟨hα0, hβ0, -, hsum⟩ := tileSides_angles D hT
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := by
    intro h; apply hα; exact ⟨1 / 3, by push_cast; linarith⟩
  have hα3 : α ≠ Real.pi / 3 := by
    intro h; apply hα; exact ⟨1 / 3, by push_cast; linarith⟩
  have hβ3 : β ≠ Real.pi / 3 := by
    intro h; apply hα; exact ⟨1 / 3, by push_cast; linarith⟩
  -- Normalize the model.
  obtain ⟨τ, eα, eβ, eγ, ea, eb, ec⟩ := relabel_sides D hT
  set D₁ := relabelModel D τ
  have hsep : AnglesSep D₁ := by
    rw [AnglesSep, eα, eβ, eγ]
    refine ⟨fun j => ?_, fun i j h => ?_⟩
    · fin_cases j <;> simp <;> linarith
    · fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
        first
        | rfl | linarith | exact absurd h hαβ | exact absurd h.symm hαβ
        | exact absurd h hα3 | exact absurd h.symm hα3 | exact absurd h hβ3 | exact absurd h.symm hβ3
  have hγ₁ : tileγ D₁ = Real.pi / 3 := eγ
  have hirr₁ : ¬ ∃ r : ℚ, tileα D₁ = (r : ℝ) * Real.pi := by rw [eα]; exact hα
  have hAB : dist (D.target.pts 0) (D.target.pts 1) = 24 * u := by
    have := hside 2; unfold Tri.oppLen at this; exact this
  have hCA : dist (D.target.pts 2) (D.target.pts 0) = 24 * u := by
    have := hside 1; unfold Tri.oppLen at this; exact this
  have hP₁ : ∀ k, D₁.target.angleAt k = Real.pi / 3 := hP
  -- The tile at `A`.
  obtain ⟨T, jA, j₀, j₂, h0A, h2A, h02, hA, h0, h2⟩ := corner_tile D₁ hsep hγ₁ hirr₁ (hP₁ 0)
  have hγA : (D₁.tile T).localAngle ((D₁.tile T).pts jA) = tileγ D₁ := by
    rcases TwoCs.corner_mem D₁ hsep T jA with h | h | h
    · rw [hA] at h
      obtain ⟨cAα, -⟩ := corner60 D₁ hsep hγ₁ hirr₁ 0 (hP₁ 0)
      exact absurd h (ne_of_angleCount_zero D₁ cAα T)
    · rw [hA] at h
      obtain ⟨-, cAβ, -⟩ := corner60 D₁ hsep hγ₁ hirr₁ 0 (hP₁ 0)
      exact absurd h (ne_of_angleCount_zero D₁ cAβ T)
    · exact h
  have hθ : ∀ j : Fin 3, j ≠ jA → (D₁.tile T).localAngle ((D₁.tile T).pts j) = tileα D₁ ∨
      (D₁.tile T).localAngle ((D₁.tile T).pts j) = tileβ D₁ := by
    intro j hj
    rcases TwoCs.corner_mem D₁ hsep T j with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (TwoCs.corner_unique D₁ hsep T (Or.inr (Or.inr rfl)) h hγA) hj
  have ha₁ : dist (D₁.model.pts 1) (D₁.model.pts 2) = 3 * u := ea
  have hb₁ : dist (D₁.model.pts 2) (D₁.model.pts 0) = 8 * u := eb
  have hc₁ : dist (D₁.model.pts 0) (D₁.model.pts 1) = 7 * u := ec
  rcases hθ j₀ h0A with hα₀ | hβ₀
  · -- `α` on `AB`.
    rcases hθ j₂ h2A with hα₂ | hβ₂
    · exact h02 (TwoCs.corner_unique D₁ hsep T (Or.inl rfl) hα₀ hα₂)
    · exact corner_contra D₁ hsep hγ₁ hirr₁ hu ha₁ hb₁ hc₁ hP₁ hAB hCA h0A h2A h02 hA h0 h2
        hα₀ hβ₂
  · -- `α` on `AC`: exchange `B` and `C`.
    rcases hθ j₂ h2A with hα₂ | hβ₂
    · set D₂ := relabelTarget D₁ (Equiv.swap 1 2)
      have p0 : D₂.target.pts 0 = D.target.pts 0 := by
        show D.target.pts (Equiv.swap 1 2 0) = _
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      have p1 : D₂.target.pts 1 = D.target.pts 2 := by
        show D.target.pts (Equiv.swap 1 2 1) = _
        rw [Equiv.swap_apply_left]
      have p2 : D₂.target.pts 2 = D.target.pts 1 := by
        show D.target.pts (Equiv.swap 1 2 2) = _
        rw [Equiv.swap_apply_right]
      have hP₂ : ∀ k, D₂.target.angleAt k = Real.pi / 3 := by
        have h0 := hP 0; have h1 := hP 1; have h2 := hP 2
        unfold Tri.angleAt cornerAngle at h0 h1 h2 ⊢
        intro k
        fin_cases k
        · show ∠ (D₂.target.pts 1) (D₂.target.pts 0) (D₂.target.pts 2) = _
          rw [p0, p1, p2, angle_comm]; exact h0
        · show ∠ (D₂.target.pts 2) (D₂.target.pts 1) (D₂.target.pts 0) = _
          rw [p0, p1, p2, angle_comm]; exact h2
        · show ∠ (D₂.target.pts 0) (D₂.target.pts 2) (D₂.target.pts 1) = _
          rw [p0, p1, p2, angle_comm]; exact h1
      exact corner_contra D₂ hsep hγ₁ hirr₁ hu ha₁ hb₁ hc₁ hP₂
        (by rw [p0, p1, dist_comm]; exact hCA) (by rw [p0, p2, dist_comm]; exact hAB)
        h2A h0A h02.symm (by rw [p0]; exact hA) (by rw [p0, p1, segment_symm]; exact h2)
        (by rw [p0, p2, segment_symm]; exact h0) hα₂ hβ₀
    · exact h02 (TwoCs.corner_unique D₁ hsep T (Or.inr (Or.inl rfl)) hβ₀ hβ₂)

end TriangleTiling.Equilateral
