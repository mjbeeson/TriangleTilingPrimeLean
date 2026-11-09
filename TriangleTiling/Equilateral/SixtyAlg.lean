/-
The algebra of `theorem:equilateral3` and `lemma:ab` (M. Beeson, *Tiling an equilateral triangle*,
arXiv 1811.09723): from the law of cosines `c² = a² + b² - ab`, the coloring equation
`M(a + b + c) = 3X` and the area equation `X² = Nab`, the ratios `u = a/c`, `v = b/c` are
`(1/2)((3N + M²)/(3N - M²) ± √((9N - M²)(N - M²))/(3N - M²))`, and `M² < N`.
-/
import Mathlib

namespace TriangleTiling.Equilateral

/-- The algebra, with `c = 1`: `u, v` the other two sides, `x` the side of `ABC`. -/
theorem sixty_alg {u v M N x : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v)
    (hcos : 1 = u ^ 2 + v ^ 2 - u * v) (hN : 0 < N) (hx : 0 < x)
    (hcol : M * (u + v + 1) = 3 * x) (harea : x ^ 2 = N * (u * v)) :
    M ^ 2 < N ∧ 0 < 3 * N - M ^ 2 ∧
      u + v = (3 * N + M ^ 2) / (3 * N - M ^ 2) ∧
      u * v = 4 * M ^ 2 * N / (3 * N - M ^ 2) ^ 2 ∧
      ((u = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        v = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2))) ∨
       (u = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        v = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)))) := by
  set s := u + v with hs
  -- `s > 1` (triangle inequality) and `M²(s + 1) = 3N(s - 1)`
  have hs1 : 1 < s := by nlinarith [mul_pos hu hv]
  have hp : u * v = (s ^ 2 - 1) / 3 := by rw [hs]; linarith
  have hMs : M ^ 2 * (s + 1) = 3 * N * (s - 1) := by
    have h1 : M ^ 2 * (s + 1) ^ 2 = 9 * (N * (u * v)) := by
      rw [← harea, show M ^ 2 * (s + 1) ^ 2 = (M * (u + v + 1)) ^ 2 by rw [hs]; ring, hcol]; ring
    rw [hp] at h1
    have h2 : (s + 1) * (M ^ 2 * (s + 1) - 3 * N * (s - 1)) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith
  have hD : 0 < 3 * N - M ^ 2 := by nlinarith [sq_nonneg M]
  have hsf : s = (3 * N + M ^ 2) / (3 * N - M ^ 2) := by
    rw [eq_div_iff hD.ne']; linarith
  -- `(u - v)² = (9N - M²)(N - M²)/(3N - M²)²`
  have hdiff : (u - v) ^ 2 = (9 * N - M ^ 2) * (N - M ^ 2) / (3 * N - M ^ 2) ^ 2 := by
    have : (u - v) ^ 2 = s ^ 2 - 4 * (u * v) := by rw [hs]; ring
    rw [this, hp, hsf]; field_simp; ring
  have hpos : 0 < (u - v) ^ 2 := by
    have : u - v ≠ 0 := sub_ne_zero.mpr huv
    positivity
  have hDpos : 0 < (9 * N - M ^ 2) * (N - M ^ 2) := by
    rw [hdiff] at hpos
    exact (div_pos_iff_of_pos_right (by positivity)).mp hpos
  have hMN : M ^ 2 < N := by
    have h9 : 0 < 9 * N - M ^ 2 := by linarith
    have := (pos_iff_pos_of_mul_pos hDpos).mp h9
    linarith
  have hab : u * v = 4 * M ^ 2 * N / (3 * N - M ^ 2) ^ 2 := by
    rw [hp, hsf]; field_simp; ring
  refine ⟨hMN, hD, hsf, hab, ?_⟩
  -- `u - v = ±√D/(3N - M²)`
  set R := Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2))
  have hR : (u - v) ^ 2 = (R / (3 * N - M ^ 2)) ^ 2 := by
    rw [hdiff, div_pow, Real.sq_sqrt hDpos.le]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hR with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

end TriangleTiling.Equilateral
