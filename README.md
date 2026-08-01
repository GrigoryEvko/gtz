# GTZ

A Lean 4 formalization of the Goreinov–Tyrtyshnikov–Zamarashkin submatrix
problem.

Paper: [paper/build/main.pdf](paper/build/main.pdf)

> **Conjecture (GTZ, 1997).** Every real n×k matrix with orthonormal columns
> has a k×k row submatrix B with σ_min(B) ≥ 1/√n.

287 modules, 8,379 declarations, sorry-free. `Gtz/Audit.lean` prints the
axiom set of every declaration on every build; each is a subset of
`propext, Classical.choice, Quot.sound`.

The conjecture holds for k ≤ 2 (Sengupta–Pautov) and for every size m ≤ 5 at
every rank (`gtzWeighted_of_le_five`). Over ℂ it fails, with exact threshold
m ≤ k+1 (`complexGtzWeighted_iff_size_le_rank_add_one`). For
m > N := k(k+1)/2 every design carries a stress and the walk reduces it
(`gtzWeighted_of_forall_smaller`), so each rank collapses to the single cell
(N, k) (`gtzWeightedAll_of_veroneseTop`). At rank 3 the cell is
`GtzWeighted 6 3`; the kernel proves it equivalent to (7,3), to (7,4), to all
of rank 3, and to the 1997 statement at rank 3 (`rank_three_iff_six_three`,
`gtzWeighted_six_three_iff_seven_three`, `gtzWeighted_six_three_iff_seven_four`,
`gtzWeightedAll_iff_forall_gtzOriginal`). The cell is open. Every mechanism
formalized so far runs unchanged over ℂ, where the statement is false.

## Notation

A ∈ ℝⁿˣᵏ with AᵀA = I_k. A design is (g_c, t_c), c = 1..m, with t_c > 0,
Σ t_c = 1, Σ t_c g_c g_cᵀ = I_k. Write G_c = g_c g_cᵀ, leverage l_c = |g_c|²,
share s_c = t_c l_c, S_C = Σ_{c∈C} G_c, N = k(k+1)/2 = dim Sym_k(ℝ). P is a
rank-k projection matrix, W = P − diag t.

Entry tags: [K] kernel theorem · [K≡] kernel equivalence at the stated
parameters · [K≡∀] kernel equivalence after quantifying over sizes ·
[M] measured (exact CAS or ≥ 60 digits, outside the kernel) ·
[lit] literature · [∗] derived from kernel facts, not yet formalized.

## The reformulations

### A. Matrix selection

1. **Row selection.** For every A there are k rows I with σ_min(A_I) ≥ 1/√n,
   i.e. A_IᵀA_I ⪰ (1/n)I. `GtzOriginal n k` [K]
2. **Principal submatrix.** Every rank-k projection matrix on ℝⁿ has a k×k
   principal submatrix with λ_min ≥ 1/n. `ProjectionCovering`,
   `FrameProjectionCovering`; both ⇔ 1 at fixed n. [K≡]
3. **Column subset selection.** Every k×n matrix with orthonormal rows has a
   k-column submatrix with σ_min ≥ 1/√n. The transpose reading (Hong–Pan,
   maximal volume, Xu). [K≡, lit]
4. **Volume selection.** The maximal-volume submatrix guarantees
   σ_min² ≥ 1/(k(n−k)+1), attained at (7,3): 1/13 against the conjectured
   1/7. Xu's interlacing bound (arXiv:2508.10452) gives 0.1127 at (6,3)
   against 1/6, and is tight at (4,3). [K wall, lit]
5. **Restricted invertibility at r = k.** The endpoint of the
   Bourgain–Tzafriri and MSS lines; the barrier factor vanishes identically
   there. [lit]

### B. Frames and measures

6. **Weighted design.** Every design has a k-subset with unweighted
   S_C ⪰ I. `GtzWeighted m k`. Domination does not mention the weights, so it
   is invariant along any weight motion. [K; implies 1 at m = n]
7. **Uniform slice.** Form 1 is form 6 restricted to uniform weights
   (`original_of_weighted_single`). A rational-weight design is a replication
   slice of a uniform one, and one archimedean step gives
   `GtzWeightedAll k ↔ ∀n, GtzOriginal n k`
   (`gtzWeightedAll_iff_forall_gtzOriginal`). No fixed-size arrow 1 → 6 is
   known. [K≡∀]
8. **Isotropic measures.** Every m-point isotropic decomposition of I_k
   contains k atoms whose squares dominate. Form 6 in the vocabulary of
   convex geometry. [∗]
9. **Heavy window.** The restriction to all-heavy designs (every l_c > 1) is
   equivalent to the full statement at the critical sizes
   (`gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three`,
   `rank_three_of_heavy_six_three`). [K≡]
10. **Stress-free stratum.** A stress is a dependence Σ α_c G_c = 0. Stressed
    designs reduce (`exists_dominating_sixThree_of_stress` at the cell,
    the walk above the top), so GTZ at rank k is equivalent to: every
    stress-free design is dominated. Stress-freeness forces m ≤ N. [K]
11. **Veronese position.** Stress-free designs are point sets on the Veronese
    variety v₂(ℙᵏ⁻¹) in linearly general position. At m = N the weights are
    determined by the points: t = (P∘P)⁻¹L (`SixThreeCrux.weight_unique`,
    `det_hadamardSquareGram_ne_zero`). [K]

### C. Variational

12. **Chart minimax.** Over Gr(k,m) × Δ_{m−1}, the minimum of
    max_{|C|=k} λ_min(W[C]) is 0, attained. `chartGtz_iff_gtzWeighted` at
    every (m,k). Threshold zero, not one. [K≡]
13. **Stationary points.** GTZ(m,k) ⇔ no admissible chart-stationary point
    has negative value. A negative global minimum produces an interior
    stationary admissible point (the crux, `SixThreeCrux`,
    `IsChartStationaryData`); boundary faces reduce to smaller m. [K]
14. **Value band.** A band ε with "every admissible stationary value is ≥ 0
    or ≤ −ε" closes the cell at ε = 4/27
    (`isEmpty_sixThreeCrux_of_chartValueTwoRegime`). The existential form is
    vacuous: all minimisers share one value
    (`SixThreeCrux.chartObjective_eq`). The usable range is (0, 4/27]. [K]
15. **Value spectrum.** The admissible stationary value set is finite.
    Measured at k = 3: the window [−4/27, 0) is empty over 45·10⁶ restarts;
    the |A| ≤ 5 classes take values in sixths; the two-block class is proved,
    by an integrality argument with assembly spectrum {½, ½}. GTZ ⇔ 0 is the
    least admissible stationary value. [M; one class K]

### D. Duality

16. **Covering value.** Per chart a scalar μ(P); GTZ(m,k) ⇔ μ(P) ≥ 1 for
    every real P. Ties sit at 1; the complex witness at 2 − 2/√3. [K≡ via 18;
    M constants]
17. **Balanced multipliers.** The stationarity assembly Ξ (diag Ξ = 𝟙/m,
    tr Ξ = 1, [P,Ξ] = 0, value + 1/m = tr(PΞ),
    `trace_projection_mul_multiplier_of_isChartStationaryData`) is the dual
    variable of 16, a balanced fractional cover in the sense of
    Bondareva–Shapley. For every balanced μ on k-subsets,
    Σ μ_C (S_C − I) = T − (n/k)I with T = Σ G_c ⪰ I. [K, ∗]

### E. Covering

18. **Simplex covering.** For every rank-k projection P on ℝᵐ the C(m,k)
    down-sets K_C = {t ∈ Δ : P[C] ⪰ diag t_C} cover the simplex
    (`gtzWeighted_iff_forall_coversSimplex`; sub-unit form
    `coversSimplex_iff_coversSubunit`). Abstract KKM with convexity,
    down-closure and face containment is false: K_C = {Σ_{c∈C} t_c ≤ 2/5}
    satisfies all three and misses the barycentre. The covering needs
    idempotence (`card_dead_add_rank_le`). [K≡]
19. **Spectraplex shadow.** K = conv{((g_c·x)²)_c : |x| = 1} is a linear
    image of the k×k spectraplex in the hyperplane ⟨t,·⟩ = 1. Failure at C
    means K meets the complementary-face neighborhood; GTZ ⇔ K misses one of
    the C(m,k) neighborhoods (`dominates_iff_forall_moment_ge`). Real shadow
    dimension ≤ N−1, complex ≤ k²−1. [K]

### F. Algebra and geometry

20. **Positive circuits.** H_c := G_c − (l_c/k)I satisfies Σ t_c H_c = 0 at
    every design; the relation space of {H_c} is the stress space plus ℝ·t.
    At the top with stress-freeness: N cone points positively spanning
    traceless Sym_k, unique circuit given by the weights. GTZ(top) ⇔ every
    such circuit admits a dominating k-subset. Ties are the degenerate
    circuits. [∗]
21. **Hypersimplex vertices.** In atom-square coordinates
    S_C − I = Σ_d (1_C − t)_d G_d, so GTZ ⇔ the spectrahedral cone
    𝒦 = {α : Σ α_d G_d ⪰ 0}, based at the interior point t, contains a
    vertex of Δ(m,k). [∗]
22. **Characteristic coefficients.** Dominates(C) ⇔ the k characteristic
    coefficients of the gap block are ≥ 0. All-heaviness makes the top one
    free; at k = 3 failure is e₂ < 0 or e₃ < 0, with e₂ a sum of three
    pair-minors and e₃ the discriminant
    (`dominates_triple_iff_symmetricLegs`). [K]
23. **Pencil.** charpoly(W[C]) = charpoly(diag t_C (Gram_C − I)): the chart
    is polynomial in the Gram entries and weights, no square roots, at every
    (m,k). [K]
24. **Averaged characteristic polynomials.**
    Σ_{|C|=k} charpoly(W[C]) = f⁽ᵐ⁻ᵏ⁾(x)/(m−k)! for f = charpoly(W). The
    ∏t-weighted average has all coefficients closed in (s,t)
    (`rungThreeAggregate_eq_sum_det_chartGapMinor`). Product-form weights
    keep mixtures real-rooted, and GTZ ⇔ at every real chart some v ∈ ℝ₊ᵐ
    puts the v-mixture's least root at ≥ 0. Uniform v reproduces Xu's
    constant. [∗, K pieces]
25. **Compounds and chirotopes.** Λʲ(Gram) has rank ≤ C(k,j); Λᵏ has rank 1
    with entries d_C·d_C′, d_C the determinant of the atom k-tuple. The signs
    d_C form the oriented matroid of the atoms, subject to
    Grassmann–Plücker. Finer than the sign layer of 28; unexamined. [∗]
26. **Dual basis.** At spanning configurations the dual basis Hᶜ has
    tr Hᶜ = t_c and Σ l_c Hᶜ = I; the stress space is ker(Gram∘Gram); every
    gap has coordinates 1_C − t. [K, M]

### G. Combinatorics

27. **Good k-subsets.** The compatibility structure of pair-minors and tie
    legs contains a good k-set (`elliptopeGoodTriangleCovering` at (7,3)).
    Turán counting on the compatible graph does not reach it: the
    icosahedron's compatible graph is complete K₆. [K]
28. **Sign sectors.** The sign pattern of the off-diagonal Gram entries; at
    k = 3 the two-graph layer. 842 of 1024 sectors survive three levers, in
    8 classes, each realized by an explicit rational all-heavy design, with
    pairwise non-isomorphism a theorem
    (`sectorClassWitness_pairwise_nonisomorphic`). No sign-only argument can
    close the cell. [K]
29. **Ties.** The equality manifold. At k = 2 a theorem (Nesterenko: three
    lines with multiplicities and forced leverages). At k = 3 the hinge
    `HingeHoldsAtSize`: every tie has a parallel pair; 4 of 9 pattern classes
    discharged, all sixteen stratum obligations narrowed by balanced stress.
    [lit k=2; open k≥3]
30. **Polygons (k = 2).** GTZ(n,2) ⇔ for closed planar polygons of fixed
    perimeter, max_{i≠j}(|w_i| + |w_j| − |w_i+w_j|) ≥ 2/n. The general-k
    analogue is 20 with the cone constraint of codimension (k−2)(k+1)/2,
    zero at k = 2. [lit]

### H. Logic and certificates

31. **One first-order sentence.** Rank k is a Π₁ sentence over the reals:
    `DiscriminantCovering 7 ↔ GtzWeightedAll 3`
    (`discriminantCovering_seven_iff_rank_three`; 35 triples, 2 inequalities
    each) and `PivotMinorCoveringFour 11 ↔ GtzWeightedAll 4` (330 quadruples,
    7 minors each). Decidable in principle by Tarski; quantifier elimination
    was measured to wall at 3 of 18 essential variables. [K≡∀; M]
32. **Positivstellensatz.** GTZ ⇔ emptiness of an explicit semialgebraic
    system, so if true some Stengle certificate exists. Low-degree SOS fails;
    the stationarity variety has Krull dimension 3–5 at the probed cells, so
    real-solving refuses. [K system; M]
33. **Failure normal form.** A counterexample is a chart point plus C(m,k)
    PSD probe certificates; with probes fixed, the failure region in weight
    space is an open union of convex polyhedral cones. A failing design at
    any (m,k) refutes the 1997 statement at some size
    (`exists_not_gtzOriginal_of_forall_not_dominates`). [K]

### I. Field contrasts

34. **Field gap.** Over ℂ the threshold is m ≤ k+1
    (`complexGtzWeighted_six_three_fails`); GTZ says over ℝ there is none.
    The top first exceeds the complex threshold at k = 3. A complex (7,3)
    design carrying no stress exists
    (`exists_complexWeightedDesign_sevenThree_stress_eq_zero`), so the walk's
    fuel is absent over ℂ, not merely unproved. [K]
35. **Realness quanta.** Six independent real Veronese images span Sym₃(ℝ)
    (`span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent`); six
    matrices never span Herm₃(ℂ)
    (`exists_mem_hermitianSubmodule_notMem_span_of_six`). Real fourth-moment
    floor 3k/(k+2) against Hermitian 2k/(k+1). Real triple products are
    extreme, ±2√(m_ab m_ac m_bc); complex phase is free. α₂ = 2 − 2/√3 is
    the sharp complex constant at rank 2 only
    (`trineMargin_lt_alphaRankTwo`). [K]

### J. Reduction lattice

```
GtzOriginal n k   ⇐ (uniform slice)  GtzWeighted n k            [fixed n]
∀n GtzOriginal n k  ⇔  GtzWeightedAll k  ⇔  GtzWeighted N k     [one cell per rank]
m > N : stress walk reduces          m ≤ 5 (any k) : theorem
m+1 ⇒ m (size monotone)             (m,k) ⇔ (m, m−k) (Naimark)
spike chains lift and descend ranks  failing design ⇒ ¬GtzOriginal at some size
rank 3:  (6,3) ⇔ (7,3) ⇔ (7,4) ⇔ GtzWeightedAll 3 ⇔ 1997@3     [RankThreeEquivalenceHub]
```

Forms 6–19 are pairwise kernel-equivalent at fixed (m,k). Forms 14, 15, 20,
21, 24, 25 and 29 are the ones not known to reduce to the covering scalar of
16. Form 4 is weaker than the conjecture. The all-floors coverings, the
deformation obligation at a crux, the heavy windows and the (7,3)/(7,4)
cells are each kernel-equivalent to the conjecture itself
(`forall_weightFlooredCovering_iff_gtzWeighted_six_three`,
`hasChartValueZeroLimitAtEveryCrux_iff_gtzWeighted_six_three`).

## Constraints on a proof

- The band of form 14 fails over ℂ: the complex witness has chart value
  −0.0137 inside the window, with no dominating triple. A proof of it uses
  the reals. No mechanism in the tree currently does; each runs verbatim
  with u u* over ℂ.
- The infimum is attained. The split tetrahedra and a ℚ(√5) design with
  uniform weights 1/6 are exact ties, so a strict inequality, a barrier
  function, or an SOS certificate with margin cannot close the cell. The
  k = 2 proof has the same shape: two bounds meet, and Perron simplicity
  supplies the contradiction.
- Per-subset arguments fail over ℂ subset by subset (form 34); the sign
  layer is sharp (form 28); the zero-pairing branch needs its own treatment;
  the computational routes wall at feasibility (forms 31, 32).
- The rank-induction step k → k+1 transports six of seven certificates and
  stops at the seventh (`exists_all_certificates_but_discriminant`). Ranks
  are attacked at their tops. A mechanism stated in N, the cone, and the
  rank-k value floor applies at every rank; one stated in the numerals of
  (6,3) applies once.

## Residuals

Mathematical:

- `GtzWeighted 6 3`, with fourteen kernel-equivalent forms.
- A band ε ∈ (0, 4/27] for `ChartValueBandExclusion`, equivalently a
  leverage cap 1/ε at every crux
  (`SixThreeCrux.leverageOf_le_inv_of_chartValueBandExclusion`); the partner
  covering ingredient is tight on that whole range.
- A realness consumer. Four invariant families are ruled out: the conic sign
  vector, the parity sum, the eigenvalue count ν, the Cauchy–Binet
  coefficients.
- Hinge, layer (a): 5 of 9 six-point pattern classes. Layer (b): 8
  tie-freeness obligations; 5 without a lever, 3 reduced to the
  balanced-stress sublocus.
- The support-two rung of the index floor (proved ladder |A| ≥ 2 + s, done
  at s = 3); whether a crux has at most one vanishing pairing; a Lipschitz
  constant on the collared class and the reach to the stress locus, both
  unmeasured; a production theorem for `SevenThreeCrux`;
  `EliminatesThreeMemberValue`, at two families.

Measured, not mechanized: emptiness of the five |A| = 5 orbits and the
index floor 8 (random restart, component bias); no (6,3) tie with |A| ≤ 7;
the heavy-arrow refutation, blocked by the walk's existential scale; the
spread law with exponent ½; the per-edge 840 at all fifteen edges and the
192 intersection; the window-witness values over ℚ(√5).

Operational: `Gtz/Audit.lean` does not import the root umbrella, so build
both (`lake build Gtz Gtz.Audit`) or `Gtz.olean` is missing after a purge.
Two docstrings are false as written and left in place by policy
(`Gtz/Quantitative/OrthogonalEdgeSectors.lean:119`,
`Gtz/Design/StratumEmptinessLedger.lean:317`; each is contradicted by a
tracked sibling). One audit pin is duplicated (`injective_four_of_ne`).

## Layout

```
Gtz/Core/           designs, domination, GtzWeighted/GtzOriginal, sanity pins
Gtz/LinAlg/         PSD kit, Schur complements, projections, 2×2 criteria
Gtz/Reduction/      walk, crystallization, Naimark, spikes, ConverseBridge,
                    CoveringForm, RankThreeEquivalenceHub
Gtz/Design/         collared classes, line patterns, stratum ledgers, frames
Gtz/Quantitative/   the (6,3)/(7,3) frontier: crux, chart, sectors, floors,
                    value lanes, index floor, minimality layer, dichotomies
Gtz/Ties/           tie and selection obstructions, relabelling action
Gtz/Complex/        the ℂ refutations: SIC, padded SIC
Gtz/Field/          field-generic designs (RCLike)
Gtz/Certificates/   rational certificate consumption
Gtz/Planar/ Corner/ the planar platform and corner fiber layers
Gtz/Audit.lean      #print axioms for every declaration, every build
```

## Build

```sh
lake exe cache get          # once; Mathlib oleans
lake build Gtz Gtz.Audit    # both umbrellas; prints every axiom set
```

Standalone files need
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>`;
the flags are not inherited. Audit pin records wrap across physical lines,
so line-based scans of the audit stream report false cleans; parse with a
whitespace-collapsing scanner.
