# TriangleTilingPrimeLean

A Lean 4 formalization of M. Beeson and G. Roșu, *Tiling a triangle into a prime number of
congruent triangles*.

An *N-tiling* of a triangle T cuts it into N triangles congruent to one tile (reflections
allowed). The paper proves that if T has an N-tiling with N > 3 prime, then T is a right triangle
tiled by copies of itself (a reptiling), with legs e, f and N = e² + f², so N ≡ 1 (mod 4)
(`prime634`). Hence some triangle can be cut into a prime number N of congruent triangles if and
only if N = 2, N = 3 or N ≡ 1 (mod 4) (`prime634cor`): the prime case of Erdős problem 634.

Every theorem, lemma and corollary of the paper, and the definition of a run, has a Lean
counterpart here, named after its label. Each states the result as printed, and its proof follows
the printed proof. The proofs are checked by the Lean kernel using only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), with no `sorry` and no `native_decide`.
The Lean statements have been checked against the paper by M. Beeson.

The docstring of each Lean theorem states the result in words and names the corresponding result
of the paper. In the table, † marks results in the separately built library
`TriangleTilingLaczkovich` (see below). All names are in the namespace `TriangleTiling.Prime`;
labels containing `-` or `.` are written with French quotes, as in `«l1995-5.3»`.

| Result of the paper (TeX label) | Lean name |
|---|---|
| Lemma `lemma:RandT` | `RandT` † |
| Theorem `theorem:rationality` | `rationality` † |
| Theorem `theorem:equilateral` | `equilateral` † |
| Theorem `theorem:l1995-5.3` | `«l1995-5.3»` † |
| Theorem `theorem:reptile` | `reptile` † |
| Corollary `corollary:reptilenotprime` | `reptilenotprime` † |
| Theorem `theorem:isosceles` | `isosceles` † |
| Corollary `cor:isoprime` | `isoprime` † |
| Theorem `theorem:l1995-4.1` | `«l1995-4.1»` † |
| Lemma `lemma:c120` | `c120` |
| Lemma `lemma:claude` | `claude` |
| Lemma `lemma:beta` | `beta` |
| Lemma `lemma:pairwisecoprimality` | `pairwisecoprimality` |
| Lemma `lemma:not3divc` | `not3divc` |
| Lemma `lemma:BLZ30` | `BLZ30` |
| Lemma `lemma:claude4` | `claude4` |
| Lemma `lemma:claude3` | `claude3` |
| Lemma `lemma:rationality3` | `rationality3` † |
| Theorem `theorem:case2` | `case2` † |
| Theorem `theorem:case3` | `case3` † |
| Theorem `theorem:case4` | `case4` † |
| Theorem `theorem:case5` | `case5` † |
| Lemma `lemma:angles` | `angles` |
| Lemma `lemma:nogammacorner` | `nogammacorner` |
| Lemma `lemma:anglesOK` | `anglesOK` |
| Lemma `lemma:gsquare` | `gsquare` |
| Lemma `lemma:alphaoverpi` | `alphaoverpi` |
| Lemma `lemma:lattice` | `lattice` |
| Theorem `theorem:minlengths` | `minlengths` |
| Lemma `lemma:edgedecompositions` | `edgedecompositions` |
| Lemma `lemma:twocs` | `twocs` |
| Definition `definition:run` | `run` |
| Lemma `lemma:block` | `block` |
| Lemma `lemma:rootedblock` | `rootedblock` |
| Lemma `lemma:longrun` | `longrun` |
| Lemma `lemma:isobetasides` | `isobetasides` |
| Lemma `lemma:isoscelesnob` | `isoscelesnob` |
| Theorem `theorem:isoscelesbeta` | `isoscelesbeta` † |
| Lemma `lemma:gammagreaterpiover2` | `gammagreaterpiover2` |
| Lemma `lemma:sidelengths` | `sidelengths` |
| Lemma `lemma:trisector` | `trisector` |
| Theorem `theorem:triquadratic` | `triquadratic` † |
| Theorem `theorem:prime634` | `prime634` † |
| Corollary `corollary:prime634cor` | `prime634cor` † |

The repository also contains the formalizations of M. Beeson, *Tilings of an isosceles triangle*
(namespace `TriangleTiling`; see
[IsoscelesTilingsLean](https://github.com/mjbeeson/IsoscelesTilingsLean)), *Triangle tiling: the
case 3α + 2β = π* (namespace `TriangleTiling.ThreeAlpha`; see
[TriangleTiling3Lean](https://github.com/mjbeeson/TriangleTiling3Lean)) and *Tiling an
equilateral triangle* (namespace `TriangleTiling.Equilateral`; see
[TriangleTilingEquilateralLean](https://github.com/mjbeeson/TriangleTilingEquilateralLean)),
whose results this paper cites.

## Dependencies

- Lean `v4.30.0` and Mathlib `v4.30.0`.
- V. Bonfioli, *Formalizing triangle tiling in Lean*
  ([ElVec1o/formalizing-triangle-tiling-in-lean](https://github.com/ElVec1o/formalizing-triangle-tiling-in-lean),
  pinned to commit `d728130`). It provides the definition of a congruent dissection and the
  results the paper takes from other work: Laczkovich's classification of the tilings of a
  triangle by congruent tiles (Laczkovich 1995, Theorems 4.1, 5.1 and 5.3; Laczkovich 2012,
  Theorem 3.3), Beeson–Zhang Theorem 1.1, the necessity part of the theorem of Snover et al. on
  reptiles (`reptile`), Theorem 42 of Bonfioli's paper on Erdős problem 634 (used in `isoprime`,
  and restated here without its unused hypothesis N ≡ 3 (mod 4)), and the tilings for N = 2,
  N = 3 and N = e² + f² used in `prime634cor`. These parts are marked unaudited in Bonfioli's
  library; the files here state the results as printed in the paper.

## Building

Install [elan](https://github.com/leanprover/elan), then:

```bash
lake exe cache get
lake build
```

This builds the library `TriangleTiling`, which is everything except the results marked †.
Continuous integration builds it on every push.

The results marked † use Laczkovich's classification from Bonfioli's library and are in the
separate library `TriangleTilingLaczkovich`. Its dependencies are about a thousand modules of
Bonfioli's library, which take several hours to build and need up to 9 GB of memory per Lean
process. To build it one module at a time on a machine with 16 GB:

```bash
LAKE_RSS_LIMIT_GB=13 python3 scripts/lakeserial.py . build TriangleTilingLaczkovich
```

To check the axioms of a theorem, for example:

```lean
import TriangleTilingLaczkovich
#print axioms TriangleTiling.Prime.prime634cor
```

## Authorship and license

The mathematics is M. Beeson's and G. Roșu's. The Lean code was written with Claude (Anthropic),
under Beeson's direction; its proofs are checked by the Lean kernel.

The Lean code is licensed under the Apache License 2.0 (see `LICENSE`).
`scripts/lakeserial.py` is copied from V. Bonfioli's repository
[erdos634_primes_and_N200](https://github.com/ElVec1o/erdos634_primes_and_N200) under the MIT
license.
