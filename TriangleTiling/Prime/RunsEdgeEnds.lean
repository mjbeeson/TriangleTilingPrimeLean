/-
The angles at the ends of a tile edge, and the third vertex of a tile from two of its corners,
for Section 11 of Beeson–Roșu.
-/
import TriangleTiling.Prime.RunsBlockB

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

namespace RunSetting

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k)
include hS

/-- A tile has each of its angles at one vertex only. -/
theorem hasAngle_unique {t : Fin N} {P Q : Plane} {θ : ℝ} (hP : HasAngle D t P θ)
    (hQ : HasAngle D t Q θ) : P = Q := by
  obtain ⟨l, hl, ha⟩ := hP
  obtain ⟨l', hl', ha'⟩ := hQ
  by_contra h
  have hll : l ≠ l' := by rintro rfl; exact h (hl.symm.trans hl')
  exact hS.angles_ne hll (ha.trans ha'.symm)

/-- **The angles at the ends of an edge**: the two ends carry the two angles other than the one
opposite. An `a` edge has `β` and `γ` at its ends, a `b` edge `α` and `γ`, a `c` edge `α` and `β`. -/
theorem edge_ends {t : Fin N} {P Q : Plane} (h : TileEdge D t P Q) :
    (dist P Q = a → (HasAngle D t P β ∧ HasAngle D t Q γ) ∨ (HasAngle D t P γ ∧ HasAngle D t Q β)) ∧
    (dist P Q = b → (HasAngle D t P α ∧ HasAngle D t Q γ) ∨ (HasAngle D t P γ ∧ HasAngle D t Q α)) ∧
    (dist P Q = c → (HasAngle D t P α ∧ HasAngle D t Q β) ∨
      (HasAngle D t P β ∧ HasAngle D t Q α)) := by
  obtain ⟨l, l', hll, hl, hl'⟩ := h
  obtain ⟨l'', h1, h2, -⟩ := fin3_third l l' hll
  have hopp : (D.tile t).oppLen l'' = dist P Q := by
    unfold Tri.oppLen
    rcases fin3_others h1 h2 hll with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2, hl, hl']
    · rw [← e1, ← e2, hl, hl', dist_comm]
  have d1 := hS.angles_ne (t := t) hll
  have d2 := hS.angles_ne (t := t) h1.symm
  have d3 := hS.angles_ne (t := t) h2.symm
  have hγ := hS.gamma
  have hA := hS.angle_of_opp (t := t) l''
  rw [hopp] at hA
  refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
  all_goals
    rcases vertex_data hS.tile t l with ⟨f1, -⟩ | ⟨f1, -⟩ | ⟨f1, -⟩ <;>
    rcases vertex_data hS.tile t l' with ⟨f2, -⟩ | ⟨f2, -⟩ | ⟨f2, -⟩
  all_goals first
    | exact absurd (f1.trans f2.symm) d1
    | exact absurd (f1.trans (hA.1 hd).symm) d2
    | exact absurd (f2.trans (hA.1 hd).symm) d3
    | exact absurd (f1.trans (hA.2.1 hd).symm) d2
    | exact absurd (f2.trans (hA.2.1 hd).symm) d3
    | exact absurd (f1.trans (hA.2.2 hd).symm) d2
    | exact absurd (f2.trans (hA.2.2 hd).symm) d3
    | exact Or.inl ⟨⟨l, hl, f1⟩, ⟨l', hl', f2⟩⟩
    | exact Or.inr ⟨⟨l, hl, f1⟩, ⟨l', hl', f2⟩⟩

omit hS in
/-- **The third vertex.** A tile with corners `P` (angle `θP`) and `Q` (angle `θQ`) has a third
vertex `Z`, at distance from `P` the side opposite `Q`, and from `Q` the side opposite `P`. -/
theorem third_vertex' {t : Fin N} {P Q : Plane} {lP lQ : Fin 3} (hP : (D.tile t).pts lP = P)
    (hQ : (D.tile t).pts lQ = Q) (hPQ : P ≠ Q) :
    ∃ Z : Plane, Set.range (D.tile t).pts = {P, Q, Z} ∧ Z ≠ P ∧ Z ≠ Q ∧
      dist P Z = (D.tile t).oppLen lQ ∧ dist Q Z = (D.tile t).oppLen lP := by
  have hll : lP ≠ lQ := by rintro rfl; exact hPQ (hP.symm.trans hQ)
  obtain ⟨l3, h1, h2, -⟩ := fin3_third lP lQ hll
  set Z := (D.tile t).pts l3
  have nP : Z ≠ P := fun h => h1 ((D.tile t).indep.injective (h.trans hP.symm))
  have nQ : Z ≠ Q := fun h => h2 ((D.tile t).indep.injective (h.trans hQ.symm))
  refine ⟨Z, ?_, nP, nQ, ?_, ?_⟩
  · ext y; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rcases fin3_cases3 i lP with h | h | h
      · left; rw [h, hP]
      · rcases fin3_others hll h1.symm h2.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · right; left; rw [h, ← e1, hQ]
        · right; right; rw [h, ← e2]
      · rcases fin3_others hll h1.symm h2.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · right; right; rw [h, ← e2]
        · right; left; rw [h, ← e1, hQ]
    · rintro (rfl | rfl | rfl)
      exacts [⟨lP, hP⟩, ⟨lQ, hQ⟩, ⟨l3, rfl⟩]
  · unfold Tri.oppLen
    rcases fin3_others hll.symm h2.symm h1.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2, hP]
    · rw [← e1, ← e2, hP, dist_comm]
  · unfold Tri.oppLen
    rcases fin3_others hll h1.symm h2.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [← e1, ← e2, hQ]
    · rw [← e1, ← e2, hQ, dist_comm]

end RunSetting

theorem third_vertex {t : Fin N} {P Q : Plane} {lP lQ : Fin 3} (hP : (D.tile t).pts lP = P)
    (hQ : (D.tile t).pts lQ = Q) (hPQ : P ≠ Q) :
    ∃ Z : Plane, Set.range (D.tile t).pts = {P, Q, Z} ∧ Z ≠ P ∧ Z ≠ Q ∧
      dist P Z = (D.tile t).oppLen lQ ∧ dist Q Z = (D.tile t).oppLen lP :=
  RunSetting.third_vertex' hP hQ hPQ

/-- The cross product of two differences, in frame coordinates. -/
theorem cross_frame {U I J : Plane} (hIJ : cross I J ≠ 0) (X y z : Plane) :
    cross (y - X) (z - X) =
      ((crdI U I J y - crdI U I J X) * (crdJ U I J z - crdJ U I J X) -
        (crdJ U I J y - crdJ U I J X) * (crdI U I J z - crdI U I J X)) * cross I J := by
  have hy := decomp (U := U) hIJ y
  have hz := decomp (U := U) hIJ z
  have hX := decomp (U := U) hIJ X
  have e1 : y - X = (crdI U I J y - crdI U I J X) • I + (crdJ U I J y - crdJ U I J X) • J := by
    conv_lhs => rw [hy, hX]
    simp only [sub_smul]; abel
  have e2 : z - X = (crdI U I J z - crdI U I J X) • I + (crdJ U I J z - crdJ U I J X) • J := by
    conv_lhs => rw [hz, hX]
    simp only [sub_smul]; abel
  rw [e1, e2, cross_comb]

end TriangleTiling.Prime
