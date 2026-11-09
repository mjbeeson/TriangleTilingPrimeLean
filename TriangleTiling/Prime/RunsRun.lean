/-
`definition:run` of Beeson–Roșu, Section 11 ("Runs of `c` edges"), and the lattice frame of a run
whose first tile has its `α` angle at `U`.

Reading of the definition (for Beeson's check). A run of length `n` on the side
`S = D.target.pts j D.target.pts (j+1)` is given by its first point `U`, a unit vector `I` along
`S`, and its tiles `t 1, …, t n`: the segment `UV`, `V = U + nc I`, lies in `S`, and the `c` edge
of `t i` is the segment from `U + (i-1)c I` to `U + ic I`. (The paper's "sequence of tiles each with
its `c` edge on `S`, consecutive `c` edges sharing an endpoint, partitioning `UV`" is this.) The
run is stopped at its end `V` (beyond which `S` continues in the direction `d`) if `V` is a vertex
of `T`, or some tile has an edge on `S` from `V` to `V + l d` (`l > 0`) and its `γ` angle at `V`.
-/
import TriangleTiling.Prime.RunsWall

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set

variable {N : ℕ} (D : CongruentDissection N)

/-- **`definition:run`** (run of `c` edges). A run of `c` edges of length `n` on the side
`S = D.target.pts j D.target.pts (j+1)`, supported by `UV` with `V = U + nc I` (`I` a unit vector
along `S`): the tiles `t 1, …, t n`, the `c` edge of `t (i+1)` being the segment from `U + ic I` to
`U + (i+1)c I`. -/
def run (j : Fin 3) (c : ℝ) (n : ℕ) (U I : Plane) (t : ℕ → Fin N) : Prop :=
  ‖I‖ = 1 ∧
    segment ℝ U (U + ((n : ℝ) * c) • I) ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) ∧
    ∀ i : ℕ, i < n → TileEdge D (t (i + 1)) (U + ((i : ℝ) * c) • I) (U + (((i : ℝ) + 1) * c) • I)

/-- The run is **stopped** at its end `V`, beyond which the side `S` continues in the direction
`d`: `V` is a vertex of `T`, or the tile whose edge on `S` lies beyond `V` and ends at `V` has its
`γ` angle at `V`. -/
def StoppedAt (j : Fin 3) (γ : ℝ) (V d : Plane) : Prop :=
  V ∈ Set.range D.target.pts ∨ ∃ (t : Fin N) (l : ℝ), 0 < l ∧
    segment ℝ V (V + l • d) ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) ∧
    TileEdge D t V (V + l • d) ∧ HasAngle D t V γ

/-- The run is **maximal** at its end `V` (beyond which `S` continues in the direction `d`): the
edge on `S` adjacent to `UV` at `V`, if any, is not a `c` edge. -/
def MaximalAt (j : Fin 3) (c : ℝ) (V d : Plane) : Prop :=
  ¬ ∃ t : Fin N, segment ℝ V (V + c • d) ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) ∧
    TileEdge D t V (V + c • d)

/-- **The lattice frame of a run** whose first tile has its `α` angle at `U` and its `γ` angle at
`W`: `I` along `S`, `J = (W - U)/b`. -/
structure Frame {α β γ a b c : ℝ} (j : Fin 3) (U I J : Plane) : Prop where
  nI : ‖I‖ = 1
  nJ : ‖J‖ = 1
  hIJ : cross I J ≠ 0
  aIJ : InnerProductGeometry.angle I J = α
  aIw : InnerProductGeometry.angle I (c • I - b • J) = β
  aJw : InnerProductGeometry.angle J (b • J - c • I) = γ
  nw : ‖c • I - b • J‖ = a
  north : ∀ y ∈ D.target.carrier, 0 ≤ crdJ U I J y
  side : ∀ y ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)), crdJ U I J y = 0

theorem crdJ_U {U I J : Plane} : crdJ U I J U = 0 := by simp [crdJ, cross]

variable {D}

theorem tileEdge_symm {t : Fin N} {P Q : Plane} (h : TileEdge D t P Q) : TileEdge D t Q P := by
  obtain ⟨l, l', h1, h2, h3⟩ := h; exact ⟨l', l, h1.symm, h3, h2⟩

theorem side_north {T : Tri} {j : Fin 3} {U I J V W : Plane}
    (hUS : U ∈ segment ℝ (T.pts j) (T.pts (j + 1))) (hVS : V ∈ segment ℝ (T.pts j) (T.pts (j + 1)))
    (hUV : U ≠ V) (hcU : crdJ U I J U = 0) (hcV : crdJ U I J V = 0) (hWT : W ∈ T.carrier)
    (hcW : 0 < crdJ U I J W) :
    (∀ y ∈ T.carrier, 0 ≤ crdJ U I J y) ∧
      ∀ y ∈ segment ℝ (T.pts j) (T.pts (j + 1)), crdJ U I J y = 0 := by
  rw [segment_eq_image_lineMap] at hUS hVS
  obtain ⟨t1, -, ht1⟩ := hUS
  obtain ⟨t2, -, ht2⟩ := hVS
  have e1 := crdJ_affine (U := U) (I := I) (J := J) (T.pts j) (T.pts (j + 1)) t1
  have e2 := crdJ_affine (U := U) (I := I) (J := J) (T.pts j) (T.pts (j + 1)) t2
  rw [ht1, hcU] at e1
  rw [ht2, hcV] at e2
  have ht12 : t1 ≠ t2 := by rintro rfl; exact hUV (ht1.symm.trans ht2)
  have hP0 : crdJ U I J (T.pts j) = 0 := by
    have : (t2 - t1) * crdJ U I J (T.pts j) = 0 := by
      linear_combination (-t2) * e1 + t1 * e2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht12.symm)
  have hP1 : crdJ U I J (T.pts (j + 1)) = 0 := by
    rw [hP0] at e1 e2
    have : (t2 - t1) * crdJ U I J (T.pts (j + 1)) = 0 := by
      linear_combination e1 - e2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ht12.symm)
  have hconv : ∀ σ : ℝ, Convex ℝ {y : Plane | 0 ≤ σ * crdJ U I J y} := by
    intro σ y hy z hz p q hp hq hpq
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    have : p • y + q • z = AffineMap.lineMap y z q := by
      rw [AffineMap.lineMap_apply_module, show 1 - q = p by linarith]
    rw [this, crdJ_affine, show 1 - q = p by linarith]
    nlinarith [mul_nonneg hp hy, mul_nonneg hq hz]
  have hthird : ∀ σ : ℝ, 0 ≤ σ * crdJ U I J (T.pts (j + 2)) →
      ∀ y ∈ T.carrier, 0 ≤ σ * crdJ U I J y := by
    intro σ h3 y hy
    refine (convexHull_min ?_ (hconv σ)) hy
    rintro _ ⟨i, rfl⟩
    show 0 ≤ σ * crdJ U I J (T.pts i)
    obtain h | h | h := fin3_cases3 i j
    · rw [h, hP0, mul_zero]
    · rw [h, hP1, mul_zero]
    · rw [h]; exact h3
  have h3 : 0 ≤ crdJ U I J (T.pts (j + 2)) := by
    by_contra h
    push Not at h
    have := hthird (-1) (by linarith) W hWT
    linarith
  refine ⟨fun y hy => by simpa using hthird 1 (by linarith) y hy, ?_⟩
  intro y hy
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨s, -, rfl⟩ := hy
  rw [crdJ_affine, hP0, hP1]; ring

theorem RunSetting.frame {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
    {j : Fin 3} {n : ℕ} {U I W : Plane} {t : ℕ → Fin N} (hrun : run D j c n U I t) (hn : 1 ≤ n)
    (hU : HasAngle D (t 1) U α) (hW : HasAngle D (t 1) W γ) :
    Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I (b⁻¹ • (W - U)) ∧
      Set.range (D.tile (t 1)).pts = {U, U + c • I, W} := by
  obtain ⟨hI, hseg, hedge⟩ := hrun
  have hb := hS.b_pos
  have hc := hS.c_pos
  obtain ⟨J, hJdef⟩ : ∃ J, b⁻¹ • (W - U) = J := ⟨_, rfl⟩
  have hJ : W = U + b • J := by rw [← hJdef, smul_smul, mul_inv_cancel₀ hb.ne', one_smul]; abel
  rw [hJdef]
  set T := D.tile (t 1)
  -- The first tile: `U` (α), `U + cI` (β), `W` (γ).
  have he0 := hedge 0 hn
  simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, zero_add, one_mul] at he0
  obtain ⟨lU, lP, hUP, hlU, hlP⟩ := he0
  obtain ⟨lW, hlW, haW⟩ := hW
  have haU : T.angleAt lU = α := angleAt_eq_of_hasAngle hU hlU
  have hsum := T.angleAt_sum
  obtain ⟨hα, hβ, hγ, hπ⟩ := hS.angles_pos
  have hαγ : α ≠ γ := by have := hS.gamma; intro h; linarith
  have hUW : lU ≠ lW := by intro h; rw [h] at haU; exact hαγ (haU.symm.trans haW)
  have hPW : lP ≠ lW := by
    intro h
    -- the side `UW` would be the `c` edge, but it is opposite the third vertex
    rw [h] at hlP
    have hd : dist U W = c := by
      rw [← hlW, hlP, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, hI, mul_one,
        Real.norm_of_nonneg hc.le]
    -- the third vertex `l₃`, with angle `β`
    obtain ⟨l3, h13, h23, hothers⟩ : ∃ l3 : Fin 3, l3 ≠ lU ∧ l3 ≠ lW ∧
        ((lU = l3 + 1 ∧ lW = l3 + 2) ∨ (lU = l3 + 2 ∧ lW = l3 + 1)) := by
      revert hUW; fin_cases lU <;> fin_cases lW <;> decide
    have hA : T.angleAt l3 = β := by
      have : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = T.angleAt l3 + T.angleAt lU + T.angleAt lW := by
        rcases hothers with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> fin_cases l3 <;> simp <;> ring
      linarith
    have hL : T.oppLen l3 = b := by
      rcases hS.angleAt_combo (t 1) l3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1.symm.trans hA) hS.alpha_ne_beta
      · exact h2
      · exfalso; rw [hA] at h1; linarith
    have : T.oppLen l3 = dist U W := by
      unfold Tri.oppLen
      rcases hothers with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2, hlU, hlW]
      · rw [← e1, ← e2, hlU, hlW, dist_comm]
    rw [this, hd] at hL
    exact hS.b_lt_c.ne' hL
  -- So the three vertices are `lU`, `lP`, `lW`.
  have hP3 : ∀ x : Fin 3, x = lU ∨ x = lP ∨ x = lW := by
    revert hUP hUW hPW; fin_cases lU <;> fin_cases lP <;> fin_cases lW <;> decide
  have hrange : Set.range T.pts = {U, U + c • I, W} := by
    ext y; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      rcases hP3 x with rfl | rfl | rfl
      · exact Or.inl hlU
      · exact Or.inr (Or.inl hlP)
      · exact Or.inr (Or.inr hlW)
    · rintro (rfl | rfl | rfl)
      exacts [⟨lU, hlU⟩, ⟨lP, hlP⟩, ⟨lW, hlW⟩]
  refine ⟨?_, hrange⟩
  -- the angles at the three vertices
  have hsum3 : T.angleAt lU + T.angleAt lP + T.angleAt lW = π := by
    rw [← hsum]
    revert hUP hUW hPW; fin_cases lU <;> fin_cases lP <;> fin_cases lW <;> simp <;> ring
  have haP : T.angleAt lP = β := by linarith
  have hnext : ∀ x y : Fin 3, x ≠ y → (y = x + 1 ∨ y = x + 2) := by decide
  -- at `U`: edges along `I` (length `c`) and `J` (length `b`)
  have hPu : T.pts (lU + 1) = U + c • I ∨ T.pts (lU + 2) = U + c • I := by
    rcases hnext lU lP hUP with h | h <;> [left; right] <;> rw [← h] <;> exact hlP
  have hWu : T.pts (lU + 1) = U + b • J ∨ T.pts (lU + 2) = U + b • J := by
    rcases hnext lU lW hUW with h | h <;> [left; right] <;> rw [← h, hlW] <;> exact hJ
  have hIJ : cross I J ≠ 0 := by
    have hdet := T.det_ne_zero
    rw [← T.cross_edgeVec lU, Tri.edgeVec_eq T, Tri.edgeVec'_eq T, hlU] at hdet
    intro h0
    apply hdet
    rcases fin3_others hUP hUW hPW with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2, hlP, hlW, hJ, add_sub_cancel_left, add_sub_cancel_left, cross_smul_left,
        cross_smul_right, h0]; ring
    · rw [← e1, ← e2, hlP, hlW, hJ, add_sub_cancel_left, add_sub_cancel_left, cross_smul_left,
        cross_smul_right, cross_swap, h0]; ring
  have aIJ : InnerProductGeometry.angle I J = α := by
    rw [← haU]
    exact ((Tri.two_rays T hIJ hlU hc hb hPu hWu).1).symm
  -- at `U + cI`: edges along `-I` and `bJ - cI`
  have hne2 : cross (-I) (b • J - c • I) ≠ 0 := by
    rw [cross_neg_left, cross_sub_right, cross_smul_right, cross_smul_right, cross_self]
    intro h; apply hIJ; nlinarith [hb]
  have hUv : T.pts (lP + 1) = (U + c • I) + c • (-I) ∨ T.pts (lP + 2) = (U + c • I) + c • (-I) := by
    have : (U + c • I) + c • (-I) = U := by rw [smul_neg]; abel
    rw [this]
    rcases hnext lP lU hUP.symm with h | h <;> [left; right] <;> rw [← h] <;> exact hlU
  have hWv : T.pts (lP + 1) = (U + c • I) + (1 : ℝ) • (b • J - c • I) ∨
      T.pts (lP + 2) = (U + c • I) + (1 : ℝ) • (b • J - c • I) := by
    have : (U + c • I) + (1 : ℝ) • (b • J - c • I) = W := by rw [one_smul, hJ]; abel
    rw [this]
    rcases hnext lP lW hPW with h | h <;> [left; right] <;> rw [← h] <;> exact hlW
  have aIw : InnerProductGeometry.angle I (c • I - b • J) = β := by
    rw [← haP, (Tri.two_rays T hne2 hlP hc one_pos hUv hWv).1, ← InnerProductGeometry.angle_neg_neg,
      neg_sub]
  -- at `W`: edges along `-J` and `cI - bJ`
  have hne3 : cross (-J) (c • I - b • J) ≠ 0 := by
    rw [cross_neg_left, cross_sub_right, cross_smul_right, cross_smul_right, cross_self,
      cross_swap]
    intro h; apply hIJ; nlinarith [hc]
  have hlW' : T.pts lW = W := hlW
  have hUw : T.pts (lW + 1) = W + b • (-J) ∨ T.pts (lW + 2) = W + b • (-J) := by
    have : W + b • (-J) = U := by rw [hJ, smul_neg]; abel
    rw [this]
    rcases hnext lW lU hUW.symm with h | h <;> [left; right] <;> rw [← h] <;> exact hlU
  have hPw : T.pts (lW + 1) = W + (1 : ℝ) • (c • I - b • J) ∨
      T.pts (lW + 2) = W + (1 : ℝ) • (c • I - b • J) := by
    have : W + (1 : ℝ) • (c • I - b • J) = U + c • I := by rw [one_smul, hJ]; abel
    rw [this]
    rcases hnext lW lP hPW.symm with h | h <;> [left; right] <;> rw [← h] <;> exact hlP
  have aJw : InnerProductGeometry.angle J (b • J - c • I) = γ := by
    rw [← haW, (Tri.two_rays T hne3 hlW' hb one_pos hUw hPw).1,
      ← InnerProductGeometry.angle_neg_neg, neg_sub]
  -- the `a` side
  have nw : ‖c • I - b • J‖ = a := by
    have hL : T.oppLen lU = a := by
      rcases hS.angleAt_combo (t 1) lU with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact absurd (h1.symm.trans haU) hS.alpha_ne_beta.symm
      · exfalso; have := hS.gamma; rw [haU] at h1; linarith
    rw [← hL]
    unfold Tri.oppLen
    have : dist (U + c • I) W = ‖c • I - b • J‖ := by
      rw [dist_eq_norm, hJ]; congr 1; abel
    rcases hnext lU lP hUP with h | h <;> rcases hnext lU lW hUW with h' | h'
    · exact absurd (h.trans h'.symm) hPW
    · rw [← h, ← h', hlP, hlW, this]
    · rw [← h, ← h', hlP, hlW, dist_comm, this]
    · exact absurd (h.trans h'.symm) hPW
  have hn0 : (0 : ℝ) < n * c := mul_pos (by exact_mod_cast hn) hc
  have hcrdV : crdJ U I J (U + ((n : ℝ) * c) • I) = 0 := by
    have := crdJ_comb (U := U) hIJ ((n : ℝ) * c) 0
    simpa using this
  have hUV : U ≠ U + ((n : ℝ) * c) • I := by
    intro h
    have : ((n : ℝ) * c) • I = 0 := by
      have := congrArg (fun y => y - U) h; simpa using this.symm
    rw [smul_eq_zero] at this
    rcases this with h | h
    · linarith
    · rw [h, norm_zero] at hI; exact zero_ne_one hI
  have hWT : W ∈ D.target.carrier := by
    rw [← hlW]; exact TwoCs.pts_mem_target D.toDissection _ _
  have hcW : crdJ U I J W = b := by
    rw [hJ]; have := crdJ_comb (U := U) hIJ 0 b; simpa using this
  obtain ⟨hnorth, hside⟩ := side_north (hseg (left_mem_segment ℝ _ _))
    (hseg (right_mem_segment ℝ _ _)) hUV crdJ_U hcrdV hWT (hcW ▸ hb)
  refine ⟨hI, ?_, hIJ, aIJ, aIw, aJw, nw, hnorth, hside⟩
  · rw [← hJdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hb.le), ← dist_eq_norm, dist_comm]
    rw [← hlW, ← hlU]
    have hL : T.oppLen lP = b := by
      rcases hS.angleAt_combo (t 1) lP with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd (h1.symm.trans haP) hS.alpha_ne_beta
      · exact h2
      · exfalso; have := hS.gamma; rw [haP] at h1; linarith
    have : dist (T.pts lU) (T.pts lW) = b := by
      rw [← hL]; unfold Tri.oppLen
      rcases hnext lP lU hUP.symm with h | h <;> rcases hnext lP lW hPW with h' | h'
      · exact absurd (h.trans h'.symm) hUW
      · rw [← h, ← h']
      · rw [← h, ← h', dist_comm]
      · exact absurd (h.trans h'.symm) hUW
    rw [this, inv_mul_cancel₀ hb.ne']


end TriangleTiling.Prime
