/-
**`lemma:block`** (the trapezoid lemma) of M. Beeson and E. Roșu, *Tiling a triangle into a prime
number of congruent triangles*, Section 11.

The printed proof chooses a counterexample `(s, r, i₀)` with `s` as large as possible and produces
one for `s + 1`, either `(s + 1, r, i₀)` or `(s + 1, j*, s - j*)`. Here that step is `block_step`
(the steps of the proof are `block_north`, `block_east`, `block_nablas`, `block_end`,
`block_next`, `block_G`), and the maximality is an induction on `n - s`.

Statement checked by Beeson. Readings: the run is `run D j c n U I t` (`definition:run`);
`W` is the vertex of `T₁ = t 1` at its `γ` angle and `J = (W - U)/b`; "a tile north of `ℓ_r`" is a
tile all of whose vertices are `U + pc I + (r + q)b J` with `q ≥ 0`; "its `b` edge on `ℓ_r`,
running east from `x(i₀, r)`" is: `x(i₀, r)` and `x(i₀, r) + bI` are vertices of the tile.
-/
import TriangleTiling.Prime.RunsBlockE

namespace TriangleTiling.Prime

open Erdos634.Geometry EuclideanGeometry Real Set Metric

variable {N : ℕ} {D : CongruentDissection N}

section Block

variable {α β γ a b c : ℝ} {m k : ℤ} (hS : RunSetting D α β γ a b c m k) {j : Fin 3}
  {U I J : Plane} (hF : Frame D (α := α) (β := β) (γ := γ) (a := a) (b := b) (c := c) j U I J)
include hS hF

/-- `𝒯(s+1, r')` from `𝒯(s, r)`, `T_{s+1} = Δ_{s,0}`, the `∇_{s-1-i,i}` and the
`Δ_{s-q,q}`, `1 ≤ q < r'`. -/
theorem extend_T {r s r' : ℕ} (hr' : r' ≤ r ∨ (r = s ∧ r' = s + 1)) (hT : TOccurs D (lat U I J b c) s r)
    {T' : Fin N} (hT' : Set.range (D.tile T').pts =
      {lat U I J b c s 0, lat U I J b c ((s : ℝ) + 1) 0, lat U I J b c s 1})
    (E : ℕ → Fin N)
    (hnab : ∀ i < r, Set.range (D.tile (E i)).pts = {lat U I J b c ((s : ℝ) - i) i,
        lat U I J b c ((s : ℝ) - i - 1) (i + 1), lat U I J b c ((s : ℝ) - i) (i + 1)} ∧
      HasAngle D (E i) (lat U I J b c ((s : ℝ) - i) i) γ)
    (hG : ∀ q, 1 ≤ q → q < r' → ∃ G, Set.range (D.tile G).pts = {lat U I J b c ((s : ℝ) - q) q,
        lat U I J b c ((s : ℝ) - q + 1) q, lat U I J b c ((s : ℝ) - q) (q + 1)}) :
    TOccurs D (lat U I J b c) (s + 1) r' := by
  constructor
  · intro i q hq hiq
    by_cases h : i + q + 1 ≤ s
    · exact hT.1 i q (by omega) h
    · have hiq' : (i : ℝ) = s - q := by
        have : i + q = s := by omega
        have : ((i + q : ℕ) : ℝ) = s := by exact_mod_cast this
        push_cast at this; linarith
      by_cases hq0 : q = 0
      · subst hq0
        refine ⟨T', ?_⟩
        rw [hT', hiq']; simp
      · obtain ⟨G, hG'⟩ := hG q (by omega) hq
        refine ⟨G, ?_⟩
        rw [hG', hiq']
  · intro i q hq hiq
    by_cases h : i + q + 2 ≤ s
    · exact hT.2 i q (by omega) h
    · have hiq' : (i : ℝ) + 1 = s - q := by
        have : i + q + 1 = s := by omega
        have : ((i + q + 1 : ℕ) : ℝ) = s := by exact_mod_cast this
        push_cast at this; linarith
      refine ⟨E q, ?_⟩
      rw [(hnab q (by omega)).1, hiq', show (i : ℝ) = s - q - 1 by linarith]

/-- **The step of the trapezoid lemma**: a counterexample for `s` gives `s < n` and a
counterexample for `s + 1`. -/
theorem block_step {n : ℕ} {t : ℕ → Fin N} (hrun : run D j c n U I t) (hnk : (n : ℤ) < k)
    (hstop : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I) {r s i₀ : ℕ} (hr : 1 ≤ r) (hrs : r < s)
    (hsn : s ≤ n) (hT : TOccurs D (lat U I J b c) s r) (hi₀ : i₀ + r < s) {G₀ : Fin N}
    (hG₀ : ∀ l, (r : ℝ) * b ≤ crdJ U I J ((D.tile G₀).pts l))
    (hG₀e : TileEdge D G₀ (lat U I J b c i₀ r) (lat U I J b c i₀ r + b • I)) :
    s < n ∧ ∃ r' i₀' : ℕ, ∃ G' : Fin N, 1 ≤ r' ∧ r' < s + 1 ∧
      TOccurs D (lat U I J b c) (s + 1) r' ∧ i₀' + r' < s + 1 ∧
      (∀ l, (r' : ℝ) * b ≤ crdJ U I J ((D.tile G').pts l)) ∧
      TileEdge D G' (lat U I J b c i₀' r') (lat U I J b c i₀' r' + b • I) := by
  classical
  have hsk : (s : ℤ) < k := lt_of_le_of_lt (by exact_mod_cast hsn) hnk
  -- `R` lies inside an edge of a tile north of `ℓ_r`.
  obtain ⟨e, he, hRe⟩ := block_north hS hF hr hrs hsk hT hi₀ hG₀ hG₀e
  obtain ⟨h1, h2, h3⟩ := Dissection.mem_lineChain.mp he
  have hN : ∀ y, lineF I J 0 (-1) y = -crdJ U I J y + lineF I J 0 (-1) U := lineJ_apply
  have hN₀ : ∀ l, (r : ℝ) * b ≤ crdJ U I J ((D.tile e.1).pts l) := by
    intro l; have := h3 l; rw [hN] at this; linarith
  have hN₀1 : crdJ U I J ((D.tile e.1).pts e.2) = r * b := by rw [hN] at h1; linarith
  have hN₀2 : crdJ U I J ((D.tile e.1).pts (e.2 + 1)) = r * b := by rw [hN] at h2; linarith
  -- The chain on `σ`, and the `∇`s.
  obtain ⟨tR, htR⟩ := nabla_at_R hS hF hr hrs hT
  obtain ⟨-, hEast, hσa⟩ := block_east hS hF hr hrs.le hsk hT (north_west hS hF hN₀1 hN₀2 hRe) hRe
    htR hS.angles_pos.1 (by have := hS.angles_pos; linarith)
  have hEast' : ∀ i : ℕ, ∃ E : Fin N, i < r →
      (∀ l, (b * c) * s ≤ b * crdI U I J ((D.tile E).pts l) + c * crdJ U I J ((D.tile E).pts l)) ∧
      TileEdge D E (lat U I J b c ((s : ℝ) - i) i) (lat U I J b c ((s : ℝ) - i - 1) (i + 1)) := by
    intro i
    by_cases hi : i < r
    · obtain ⟨E, h⟩ := hEast i hi; exact ⟨E, fun _ => h⟩
    · exact ⟨e.1, fun h => absurd h hi⟩
  choose E hE' using hEast'
  have hE := fun i hi => (hE' i hi).1
  have hEe := fun i hi => (hE' i hi).2
  have hnab := block_nablas hS hF hr E (fun i hi l => hE i hi l) hEe
    (fun h => block_top hS hF hr hrs hT (Tri.localAngle_openSegment _ _ hRe)
      (fun l => hE (r - 1) (by omega) l) h)
  -- `s < n`.
  have hsn' : s < n := by
    by_contra h
    have : s = n := by omega
    subst this
    exact block_end hS hF hrun hr hrs hstop hT E hnab hσa
  refine ⟨hsn', ?_⟩
  -- `T_{s+1} = Δ_{s,0}`.
  obtain ⟨tq, htq⟩ := hT.1 (s - 1) 0 (by omega) (by omega)
  have hs1 : ((s - 1 : ℕ) : ℝ) = s - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hs1, show (s : ℝ) - 1 + 1 = s by ring] at htq
  simp only [Nat.cast_zero, zero_add] at htq
  have hE0 := (hnab 0 (by omega)).2
  simp only [Nat.cast_zero, sub_zero] at hE0
  have hnext := block_next hS hF hrun (by omega) hsn' htq hE0
  -- The tiles `G_q`.
  by_cases hall : ∀ q, 1 ≤ q → q < r → ∃ G, Set.range (D.tile G).pts =
      {lat U I J b c ((s : ℝ) - q) q, lat U I J b c ((s : ℝ) - q + 1) q,
        lat U I J b c ((s : ℝ) - q) (q + 1)}
  · exact ⟨r, i₀, G₀, hr, by omega, extend_T hS hF (Or.inl le_rfl) hT hnext E hnab hall, by omega, hG₀,
      hG₀e⟩
  · push Not at hall
    have hex : ∃ q, 1 ≤ q ∧ q < r ∧ ∀ G, Set.range (D.tile G).pts ≠
        {lat U I J b c ((s : ℝ) - q) q, lat U I J b c ((s : ℝ) - q + 1) q,
          lat U I J b c ((s : ℝ) - q) (q + 1)} := hall
    set q := Nat.find hex
    obtain ⟨hq1, hqr, hqG⟩ := Nat.find_spec hex
    have hmin : ∀ q', 1 ≤ q' → q' < q → ∃ G, Set.range (D.tile G).pts =
        {lat U I J b c ((s : ℝ) - q') q', lat U I J b c ((s : ℝ) - q' + 1) q',
          lat U I J b c ((s : ℝ) - q') (q' + 1)} := by
      intro q' h1 h2
      by_contra hno
      push Not at hno
      exact Nat.find_min hex h2 ⟨h1, by omega, hno⟩
    rcases block_G hS hF hr hrs.le hT E hnab hq1 hqr with ⟨G, hG⟩ | ⟨G, hGn, hGe⟩
    · exact absurd hG (hqG G)
    · have hsq : (((s - q : ℕ) : ℝ)) = s - q := by rw [Nat.cast_sub (by omega)]
      refine ⟨q, s - q, G, hq1, by omega, extend_T hS hF (Or.inl hqr.le) hT hnext E hnab hmin,
        by omega, hGn, ?_⟩
      rw [hsq]; exact hGe

end Block

/-- **Lemma `lemma:block`** (Trapezoid lemma). Let `T₁, …, T_n` be a run on a side `S` of `T`,
supported by `UV`, with `n < k`, stopped at `V`, and with `T₁` having its `α` angle at `U` (and its
`γ` angle at `W`; `J = (W - U)/b` and `x(u, v) = U + uc I + vb J`). Let `1 ≤ r < s ≤ n`. Then the
following cannot both hold:
(i) `𝒯(s, r)` occurs;
(ii) for some `i₀` with `0 ≤ i₀ < s - r`, a tile north of `ℓ_r` has a vertex at `x(i₀, r)` and its
`b` edge on `ℓ_r`, running east from `x(i₀, r)`. -/
theorem block {N : ℕ} {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hS : RunSetting D α β γ a b c m k) {j : Fin 3} {n : ℕ} {U I W : Plane} {t : ℕ → Fin N}
    (hrun : run D j c n U I t) (hnk : (n : ℤ) < k)
    (hstop : StoppedAt D j γ (U + ((n : ℝ) * c) • I) I)
    (hU : HasAngle D (t 1) U α) (hW : HasAngle D (t 1) W γ) {r s : ℕ} (hr : 1 ≤ r)
    (hrs : r < s) (hsn : s ≤ n) :
    ¬ (TOccurs D (lat U I (b⁻¹ • (W - U)) b c) s r ∧
      ∃ i₀ : ℕ, i₀ < s - r ∧ ∃ G : Fin N,
        (∀ l, ∃ p q : ℝ, 0 ≤ q ∧ (D.tile G).pts l = lat U I (b⁻¹ • (W - U)) b c p (r + q)) ∧
        TileEdge D G (lat U I (b⁻¹ • (W - U)) b c i₀ r)
          (lat U I (b⁻¹ • (W - U)) b c i₀ r + b • I)) := by
  rintro ⟨hT, i₀, hi₀, G, hGn, hGe⟩
  obtain ⟨hF, -⟩ := hS.frame hrun (by omega) hU hW
  set J := b⁻¹ • (W - U)
  have hGn' : ∀ l, (r : ℝ) * b ≤ crdJ U I J ((D.tile G).pts l) := by
    intro l
    obtain ⟨p, q, hq, hpq⟩ := hGn l
    rw [hpq, crdJ_x hF]
    nlinarith [hS.b_pos]
  -- Induction on `n - s`.
  have key : ∀ d s r i₀ : ℕ, n - s = d → ∀ G : Fin N, 1 ≤ r → r < s → s ≤ n →
      TOccurs D (lat U I J b c) s r → i₀ + r < s →
      (∀ l, (r : ℝ) * b ≤ crdJ U I J ((D.tile G).pts l)) →
      TileEdge D G (lat U I J b c i₀ r) (lat U I J b c i₀ r + b • I) → False := by
    intro d
    induction d with
    | zero =>
      intro s r i₀ hd G hr hrs hsn hT hi₀ hGn hGe
      have := (block_step hS hF hrun hnk hstop hr hrs hsn hT hi₀ hGn hGe).1
      omega
    | succ d ih =>
      intro s r i₀ hd G hr hrs hsn hT hi₀ hGn hGe
      obtain ⟨hsn', r', i₀', G', hr', hrs', hT', hi₀', hGn', hGe'⟩ :=
        block_step hS hF hrun hnk hstop hr hrs hsn hT hi₀ hGn hGe
      exact ih (s + 1) r' i₀' (by omega) G' hr' (by omega) (by omega) hT' hi₀' hGn' hGe'
  exact key (n - s) s r i₀ rfl G hr hrs hsn hT (by omega) hGn' hGe

end TriangleTiling.Prime
