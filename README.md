# GTZ

**A Lean 4 formalization of the Goreinov–Tyrtyshnikov–Zamarashkin submatrix problem.**

> **Conjecture (GTZ, 1997).** Every real n×k matrix with orthonormal columns has
> a k×k row submatrix B with σ_min(B) ≥ 1/√n.

Known before this project: true for k ≤ 2 (Sengupta–Pautov); false over ℂ with
sharp constant α = 2 − 2/√3 (the SIC configuration is extremal). The first open
case is k = 3, and after the reductions formalized here it is exactly ONE
object — the weighted (7,3) instance — equivalently one polynomial covering
sentence over its all-heavy parameter space.

This repository is the campaign's **final proof artifact**: nothing enters
until it has survived adversarial audit or been re-derived during
mechanization, and the eventual paper will be a LaTeX rendition of exactly the
definitions and theorems in these modules. The repository is **sorry-free**;
every proved theorem's axiom set is printed on every build and must be exactly
`propext, Classical.choice, Quot.sound`.

---

## The working form

A **weighted design** is a family g₁, …, g_m ∈ ℝᵏ with weights t_c > 0,
Σ t_c = 1, and Σ t_c g_c g_cᵀ = I_k. A k-subset C **dominates** when
Σ_{c∈C} g_c g_cᵀ ⪰ I_k. The original statement for all n at rank k is
equivalent to: *every weighted design of every size has a dominating k-subset*
(`GtzWeightedAll k`). All structural work happens in this weighted form; the
bridge back to the 1997 statement is itself a theorem here.

## What is proven, end to end

**The solved boundary, unconditionally.** `GtzOriginal n k` holds for
k ∈ {1, 2, n−2, n−1, n} — every case humanity had ever solved — and for every
matrix with at most five rows. Rank two is the complete Sengupta–Pautov
theorem in its weighted generalization, formalized without spectral theory.

**The master reduction, as an equivalence.** Via sharp crystallization
(M(k) = k(k+1)/2 + 1), weighted Naimark duality, and the descent assembly:

```
GTZ for all (n, k)   ⟺   weighted (m, s) for  s ≥ 2,  2s ≤ m ≤ s(s+1)/2 + 1
GtzWeightedAll 3     ⟺   GtzWeighted 6 3  ∧  GtzWeighted 7 3
```

**The certificate machinery, at every rank.** The trace identity and
excess-balance pigeonhole (branch a), the de-spectralized cap criterion
(branch b), the determinant form that decides both branches by one sign, the
descent ladder, light-atom deflation, the corner fiber theorem B_k, and
Lemma F_k (Bhatia–Davis at mean zero) with its tie classification.

**The planar platform for (6,3).** The audited GAP-S layer: the master
identity R′ and its corollary R″, the Bloch dictionary, dust control, the
pinch quadratic, the per-pair level law, the compression bridge (Lemma G) that
puts this planar layer underneath a rank-3 design unconditionally, Theorem V
with its branch selection made algebraic, the Zero-Atom Pushoff theorem that
dissolved GAP-T, the tight-graph geometry, the corrected first-order law, the
collar floor, and the interface arithmetic — including a kernel-checked
**counterexample** settling a disputed numerical law inside the kernel.

**The complex refutations.** Weighted (4,2) — the canonical list's unique
rank-2 entry — and weighted (6,3) — the binding open object — are both FALSE
over ℂ, with explicit kernel-checked witnesses (the SIC and its padding). No
field-blind argument can prove GTZ; every proof must consume realness, and
that statement itself is now a theorem.

**The consumption pipeline.** A fully rational certificate layer: exact
ℚ-designs, LDL-congruence gate certificates, and cast lemmas so that a future
rational (6,3)/(7,3) certificate closes rank 3 by finite exact arithmetic.

## The formal frontier

Everything else about GTZ-for-all-(n,k) is a kernel-checked theorem. What
remains is a single strictly-ordered chain, one statement per rank:

> `GtzWeighted (M(s)) s` for every `s ≥ 3`, where `M(s) = s(s+1)/2 + 1`.

That is `gtz_iff_top_of_each_rank`, and it replaces the older "binding pair
plus a window" reading on both counts. The pair collapses: `(6,3)` follows
from `(7,3)` by splitting one atom (`gtzWeighted_six_three_of_seven_three`),
so the rank-3 frontier is the single object `(7,3)` and machinery specialized
to `m = 6` is redundant. And the window collapses: spike padding plus size
monotonicity reduce every object of the rank-`s` window to its top, so there
is nothing to sweep between `2s` and `M(s)`.

The chain descends — `(11,4)` implies all of rank 3
(`gtzWeightedAll_three_of_eleven_four`), and `(8,4)` already does — so the
lowest rung is the right thing to attack. It is not one-way, though: Naimark
duality at `m = 7` sends rank 3 to rank 4 at the same size, so `(7,3)` hands
over `(7,4)` (`gtzWeighted_seven_four_of_seven_three`). What no known
implication carries upward is a window TOP.

### Rank three, with the linear algebra removed

At rank three the single remaining object has a purely polynomial form, and it
is an equivalence:

> `DiscriminantCovering 7  ⟺  GtzWeightedAll 3`
> (`discriminantCovering_seven_iff_rank_three`)

Unfolded: *every all-heavy weighted `(7,3)` design has one of its 35 triples at
which `discriminantTrace ≥ 0` and `discriminantTie ≥ 0`.* Two polynomial
inequalities per triple — degrees 2 and 3 in the six Gram entries of the triple,
4 and 6 in the 21 atom coordinates — over a real semialgebraic parameter space
cut out by seven quadratic design equations and seven strict leverage
inequalities. No matrices, no test vectors, no deflation coisometry, no
analysis anywhere in the statement.

Three collapses stack to get there. Domination of a triple is `O(3)`-invariant
in the six inner products, so the (pivot, pair) bookkeeping is 35 triples read
three ways, not 105 combinations (`discriminantSystem_pivot_independent`). A
symmetric 3×3 form with a strictly positive corner — which `AllHeavy` supplies
at every atom — reduces division-free to its 2×2 Schur form, and a 2×2 form is
nonnegative iff its trace and determinant are; `discriminantTie` IS
`det(Gram − I)`. And atom splitting duplicates the atom vector while halving
only its weight, so it preserves all-heaviness: size monotonicity runs inside
the all-heavy statement (`gtzWeightedHeavy_of_le`) and the covering at the
crystallization cap carries every smaller size.

Being an equivalence, this is also the honest ceiling: the sentence is
first-order over a real closed field, hence decidable in principle by
Tarski–Seidenberg, and every wall the campaign has hit is a feasibility wall,
never an undecidability one.

### Rank four does the same thing

The collapse is not special to rank three. At a heavy pivot, domination of a
4-subset is exactly the nonnegativity of the **seven principal minors of
`Gram − I` containing the pivot** (degrees 2,2,2,3,3,3,4 in the ten Gram
entries), by the same division-free corner reduction. Hence

> `PivotMinorCoveringFour 11  ⟺  GtzWeightedAll 4`
> (`pivotMinorCoveringFour_eleven_iff_rank_four`)

330 quadruples × 7 inequalities. The gap scalars are defined rank-generically
and rank three is recovered from them by `rfl`, so there is one substrate at
both ranks rather than two parallel developments.

### The induction step is walled, and the wall is named

`GtzWeightedAll k → GtzWeighted (M(k+1)) (k+1)` would collapse the whole chain
to rank three. It does not close. `exists_all_certificates_but_discriminant`
transports six of the Lifting Lemma's seven certificates; the seventh is
`r rᵀ ⪯ A · (G′ − I)` in the Loewner order — a *quantitative* demand that the
projected domination have slack along the cross vector, where the rank-`k`
hypothesis supplies only the qualitative `G′ − I ⪰ 0`. Wherever the projected
domination is tight, the cross sum is forced to vanish and no amount of pivot
leverage substitutes. What survives is a pure *selection* problem: the
projected certificate is free at every pivot of a dominating subset with no
induction hypothesis at all (`dominates_pushforward_of_dominates_insert`).

## Module map

| Module | Content |
|---|---|
| `Basic` | designs, domination, `GtzWeighted` / `GtzOriginal`, pivots |
| `Sanity` | definition-pinning instances (must stay sorry-free forever) |
| `BhatiaDavis` | Lemma F_k: min-pair ≤ −1 on the zero-sum sphere, tie classification |
| `SchurRankOne` | rank-one Schur complement by polarization |
| `TraceIdentity` | trace identity, excess balance, the pigeonhole (branch a) |
| `CapCriterion` | the cap criterion, de-spectralized (branch b) |
| `CapSlack` | Theorem D: both branches as one determinant sign |
| `PsdKit` | Cauchy–Schwarz contraction flips, congruence, whitening |
| `Completion` | orthonormal completion |
| `Naimark` | Theorem N: weighted Naimark duality |
| `Crystallization` | sharp bounded support M(k) = k(k+1)/2 + 1 |
| `CornerFiber` | Theorem B_k: the exact (k+1)-cycle fiber closes at every rank |
| `TwoByTwo` | 2×2 PSD criterion; the one-surface identity |
| `Deflation` | light-atom deflation (m+1,k) → (m,k) |
| `RankTwo` | weighted Sengupta–Pautov, Case B, fully scalar |
| `Reductions` | rank ≤ 2, the bridge, Theorem L, duality descent, the all-heavy reduction |
| `DescentLadder` | Theorem Q: the full-base trace identity and its two ladder consequences |
| `Compression` | Lemma G: orthonormal compressions of designs are designs; the planar gate |
| `PlanarPlatform` | Theorem R′, trace form, abstract R″, the pinch quadratic |
| `BlochDictionary` | Bloch squares, the M-form identity, R″ end-to-end |
| `DustControl` | Proposition D: mixed positivity, dust deficit, cross rebate |
| `MomentCovector` | Theorem V: the tight-triangle covector, branch selected algebraically |
| `Pushoff` | the Zero-Atom Pushoff theorem and its corner saturation |
| `TightGraph` | the max-degree theorem: K₁,₃ is dead |
| `CertificateFrame` | stress-leaf, parabola poles, four-cycle collapse, dust exclusions |
| `FirstOrderLaw` | the corrected two-face first-order constant; the fire rate |
| `LocalLaw` | the LP vertex bound; weight-split invariance |
| `CollarFloor` | the R1 rescaled floor; Theorem OW's off-window fire |
| `Interface` | the statement-(2) interface arithmetic, both directions |
| `StressFrame` | the certificate frame's scalar layer; the Gordan kill, β ≠ 0 branch |
| `CollinearStratum` | the Gordan kill, β = 0 branch: no equality design is collinear |
| `QuantitativeCorner` | Lemma F-quant, Lemma T on the κ·I fiber, the z-mass floor |
| `MomentBound` | the antipode identity; the covector bound \|ξ\| < 1/2 |
| `PThreeStratum` | the P3 theorem: two tight pairs force the third |
| `Seam` | both halves of the τ-seam |
| `ComplexWitness` | weighted (4,2) is false over ℂ — the SIC, kernel-checked |
| `ComplexPadding` | weighted (6,3) is false over ℂ — the padded SIC |
| `LawCounterexample` | the kernel-checked cap-10 refutation of the displayed local law |
| `RatCertificate` | the computable ℚ-certificate consumption layer |
| `RankFourWindow` | atom splitting, spike padding, one-object-per-rank, all-heavy monotonicity |
| `RankInductionStep` | the rank-4 seven-minor system; the named induction-step wall |
| `OneObjectNarrowing` | the test-vector quantifier eliminated; the 2×2 trace/det criterion |
| `DiscriminantSystem` | the rank-3 frontier as one polynomial covering sentence |
| `CapArgmax` | H1b both sides of the threshold L = 4 + 2√2, by one Positivstellensatz identity |
| `RealnessEngine` | the icosahedron design; where realness is consumed |
| `SelectionObstruction` | no universal good pair; no symmetry-fixed dominating subset |
| `EigenvalueSubdifferential` | moment directions; the equal-leverage vacuity fence |
| `BranchTwoRational` | the one-negative-pivot congruence signature witness, every rank |
| `BranchTwoCompleteness` | branch (b) certifies every STRICT dominating triple |
| `BranchTwoMinimal` | the same, with the three redundant hypotheses deleted |
| `PsdCongruenceConsumer` | the PSD-boundary repair at every rank |
| `PrincipalMinorsThree` | the all-principal-minors repair at rank three, matrix-free |
| `GraphicInstance` | the edge/spanning-tree dictionary; the tie stratum is INSIDE it |
| `CollarExponent` | why the a-priori Łojasiewicz lever is dead (10⁹⁰ vs 10¹⁵) |
| `Audit` | `#print axioms` for every proved theorem, on every build |

## Rigor rules

- Nothing is called proven while it contains `sorry`. `Audit.lean` prints the
  axiom set of every proved theorem on every build; the expected set is
  `propext, Classical.choice, Quot.sound` — nothing else, ever.
- Definitions stay minimal and Mathlib-anchored (`Matrix.PosSemidef`, no
  bespoke orders). Junk-value footguns are fenced at every use: `Matrix.inv`
  of a singular matrix is 0, so every pivot theorem carries `PosDef`.
- `Sanity.lean` is the definition-drift alarm: if a refactor breaks it, the
  definitions have drifted from the mathematics.
- Mechanization is treated as audit: statement-hygiene findings (unnecessary
  hypotheses, hidden dependencies, silently consumed theorems) are recorded in
  the module docstrings where they were found.

## Build

```sh
lake exe cache get   # once — downloads Mathlib oleans
lake build           # builds everything and prints the axiom audit
```

Toolchain: Lean 4 with Mathlib, pinned in `lean-toolchain` / `lakefile`.

## Selected mechanization findings

Discoveries made *by* the formalization, not merely recorded in it:

- **Theorem V's hidden hypothesis.** The informal proof works in an angle
  parameterization that silently assumes the cyclic branch. The elimination
  actually factors as spread × co-spread, and the co-spread factor scaled by
  the leverage product equals ℓ_A + ℓ_B + ℓ_C − 2 > 0 — so the branch is
  *selected* by an inequality, not assumed.
- **The max-degree theorem consumes dust exclusion.** Its polar normal is
  nonzero only when ν|ξ| < ½, which needs ν ≥ 0 — quietly downstream of the
  Gordan covering theorem. The informal one-line proof states neither side
  condition.
- **The interface pair that composed to the empty set** is now a theorem in
  both directions: the recorded pair is vacuous, the repaired √τ₀ pair is
  nonvacuous, and the one-line nonvacuity test that would have caught it is
  kernel-checked.
- **Statement hygiene.** The bridge and crystallization need neither `1 ≤ k`
  nor `k < n`; Naimark duality genuinely needs `1 ≤ k`; the pigeonhole needs
  `1 ≤ k`; dust-ness is unnecessary for the dust-deficit bound.
- **No spectra anywhere.** Every informally-spectral step (Naimark's W^{−1/2},
  B_k's eigenvalue computation, the cap criterion's signature count) was
  replaced by polarization, Gram algebra, or a witness pair — the whole
  development is free of eigenvalue theory except one C*-factorization import.
