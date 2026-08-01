# GTZ

**A zero-sorry Lean 4 formalization of the Goreinov–Tyrtyshnikov–Zamarashkin submatrix problem.**

📄 **The paper: [paper/build/main.pdf](paper/build/main.pdf)**

> **Conjecture (GTZ, 1997).** Every real n×k matrix with orthonormal columns has
> a k×k row submatrix B with σ_min(B) ≥ 1/√n.

Trust base: ~290 modules, 8,379 audited declarations, every axiom set printed on
every build and required to be within `[propext, Classical.choice, Quot.sound]`
— no `sorry`, no `axiom`, no `native_decide`, anywhere, ever (`Gtz/Audit.lean`).

State of the problem, in one paragraph. True for k ≤ 2 (Sengupta–Pautov;
re-proved here twice, once by the walk alone) and for every case previously
solved by anyone (k ∈ {1, 2, n−2, n−1, n}, and every m ≤ 5 at every rank).
All the reduction plumbing is kernel-checked at every rank: the conjecture
collapses to **one cell per rank**, sitting at the Veronese dimension
N = k(k+1)/2 — the last size where the atom squares can be linearly
independent, hence the last size the dependence-driven induction cannot touch.
At rank 3 that cell is `GtzWeighted 6 3`, kernel-equivalent to (7,3), to (7,4),
to all of rank 3, and to the literal 1997 statement at rank 3
(`rank_three_iff_six_three`, `gtzWeighted_six_three_iff_seven_three`,
`gtzWeighted_six_three_iff_seven_four`, `gtzWeightedAll_iff_forall_gtzOriginal`).
The statement is **false over ℂ** at every top from rank 3 on
(`complexGtzWeighted_iff_size_le_rank_add_one`: the complex threshold is
m ≤ k+1), so any proof must consume realness — and every mechanism formalized
so far is proved to run verbatim over ℂ, which is the honest measure of what
is still missing.

---

## The reformulation atlas

Setup, fixed once. A ∈ ℝⁿˣᵏ with AᵀA = I_k. A *design* is (g_c, t_c)_{c=1..m},
t_c > 0, Σt_c = 1, Σ t_c g_c g_cᵀ = I_k. Write G_c = g_c g_cᵀ, leverage
l_c = |g_c|², share s_c = t_c·l_c (Σs = k), S_C = Σ_{c∈C} G_c,
N = dim Sym_k(ℝ) = k(k+1)/2, P a rank-k projection, W = P − diag t.

Tags: **[K≡]** kernel equivalence at the stated parameters · **[K≡∀]** kernel
equivalence after quantifying over sizes · **[K]** kernel fact/dictionary ·
**[M]** measured (exact CAS / ≥60-digit, outside the kernel) · **[lit]**
literature · **[∗]** derived packaging of kernel facts, not yet formalized.

### A. Matrix / selection language

1. **Original row selection** — ∀A: ∃ k rows I with σ_min(A_I) ≥ 1/√n, i.e.
   A_IᵀA_I ⪰ (1/n)I. `GtzOriginal` **[K]**
2. **Principal-submatrix form** — every rank-k projection matrix on ℝⁿ has a
   k×k principal submatrix with λ_min ≥ 1/n
   (`ProjectionCovering`/`FrameProjectionCovering`, ⇔ #1 at fixed n). **[K≡]**
3. **Column-subset / conditioning form** — every k×n matrix with orthonormal
   rows contains a k-column submatrix with σ_min ≥ 1/√n (the CSSP transpose
   reading; the Hong–Pan / maximal-volume / Xu line lives here). **[K≡, lit]**
4. **Volume-selection contrast** — the maximal-volume submatrix guarantees only
   1/(k(n−k)+1), sharp and *attained* at (7,3); Xu's interlacing variant
   (arXiv:2508.10452) reaches ≈ 0.68·(1/n) at the open cells. GTZ is strictly
   beyond every known selection rule. **[K wall + lit]**
5. **Restricted invertibility at r = k** — the extreme point of the
   Bourgain–Tzafriri / MSS line where the barrier method is identically zero;
   conjectured truth 1/n. **[lit]**

### B. Frame / measure language

6. **Weighted Parseval design form** — every design has a k-subset with
   *unweighted* S_C ⪰ I (`GtzWeighted`). The weight-free conclusion is the
   load-bearing choice: domination is invariant along weight motion, and every
   reduction rides that. **[K; ⇒ #1 at m = n]**
7. **Uniform-slice identity** — #1 is exactly #6 restricted to uniform weights
   (`original_of_weighted_single`); every rational-weight design is a
   replication slice of a uniform one, and one archimedean step closes the
   loop: `GtzWeightedAll k ↔ ∀n, GtzOriginal n k`
   (`gtzWeightedAll_iff_forall_gtzOriginal`). No fixed-size arrow #1 → #6 is
   known. **[K≡∀]**
8. **Isotropic-measure / John form** — every m-point isotropic decomposition of
   I_k contains k atoms whose squares dominate. Naming variant of #6 for the
   convex-geometry literature. **[∗]**
9. **Heavy-window form** — the statement restricted to all-heavy designs
   (every l_c > 1) is equivalent to the full statement at the critical sizes
   (`gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three`, `rank_three_of_heavy_six_three`). **[K≡]**
10. **Stress-free stratum form** — a *stress* is a dependence Σα_c G_c = 0;
    stressed designs reduce by the walk (`exists_dominating_sixThree_of_stress`
    at the cell; `gtzWeighted_of_forall_smaller` above the top), so GTZ(rank k)
    ⇔ every stress-free design is dominated — and stress-freeness forces
    m ≤ N. **[K-composable]**
11. **Veronese-position form** — stress-free designs are point sets on the
    Veronese variety v₂(ℙᵏ⁻¹) in linearly general position; at m = N the
    weights are *determined* by the points (t = (P∘P)⁻¹L,
    `SixThreeCrux.weight_unique`, `det_hadamardSquareGram_ne_zero`). GTZ is a
    statement about ≤ N points in general position on the Veronese. **[K pieces]**

### C. Variational / chart language

12. **Chart minimax form** — over the compact Gr(k,m) × Δ_{m−1}:
    min over (P,t) of max_{|C|=k} λ_min(W[C]) = 0, attained (threshold zero,
    never one). `chartGtz_iff_gtzWeighted` at every (m,k). **[K≡]**
13. **Stationary form** — GTZ(m,k) ⇔ no *admissible chart-stationary* point has
    negative value: a negative global minimum manufactures an interior
    stationary admissible point (the crux production), and boundary faces
    reduce to smaller m. `IsChartStationaryData` (13 fields),
    `SixThreeCrux`. **[K assembly]**
14. **Two-regime / band form** — an explicit band ε with "every admissible
    stationary value is ≥ 0 or ≤ −ε" closes the cell at ε = 4/27
    (`isEmpty_sixThreeCrux_of_chartValueTwoRegime`); existence-only is vacuous
    (all minimisers share one value, `SixThreeCrux.chartObjective_eq`); the
    useful range is exactly (0, 4/27]. **[K trichotomy; band open]**
15. **Finite-spectrum / quantization form** — the admissible stationary value
    set is finite; measured at k = 3: the window [−4/27, 0) is empty at 45M
    restarts, low-|A| classes quantized in sixths (= 1/m), one class proved by
    an integrality argument (spectrum {½,½} at the two-block). GTZ ⇔ 0 is the
    least admissible stationary value. **[M + one proved class]**

### D. Duality / game language

16. **Covering-LP scalar form** — per chart P a scalar μ(P) (optimal covering
    value); GTZ(m,k) ⇔ μ(P) ≥ 1 for every *real* P. Ties sit at exactly 1;
    the complex witness at 2 − 2/√3 ≈ 0.845. **[K≡ via #18; M constants]**
17. **Balanced-multiplier (Bondareva–Shapley) form** — the stationarity
    assembly Ξ (diag Ξ = 𝟙/m, tr Ξ = 1, [P,Ξ] = 0,
    value + 1/m = tr(PΞ), `trace_projection_mul_multiplier_of_isChartStationaryData`)
    is the LP dual variable = a balanced fractional cover; for every balanced
    μ on k-subsets, Σ μ_C (S_C − I) = T − (n/k)·I with T = ΣG_c ⪰ I. GTZ as
    anti-core nonemptiness of a chart game. **[K identities + ∗]**

### E. Covering / topological language

18. **Simplex-covering form** — for every rank-k projection P on ℝᵐ the
    C(m,k) down-sets K_C = {t ∈ Δ : P[C] ⪰ diag t_C} cover the simplex
    (`gtzWeighted_iff_forall_coversSimplex`; sub-unit relaxation
    `coversSimplex_iff_coversSubunit`). Abstract KKM (convex + down-closed +
    face containment) is *false* — explicit counterexample; the true statement
    needs idempotence (`card_dead_add_rank_le`). **[K≡]**
19. **Moment-image / spectraplex-shadow form** — K = conv{((g_c·x)²)_c : |x|=1}
    is a shadow of the k×k spectraplex in the hyperplane ⟨t,·⟩ = 1; failure at
    C ⇔ K enters the complementary-face neighborhood; GTZ ⇔ K always misses
    one of them (`dominates_iff_forall_moment_ge`). Real shadow dim ≤ N−1,
    complex ≤ k²−1. **[K dictionary]**

### F. Algebraic / geometric language

20. **Harmonic positive-circuit form** — H_c := G_c − (l_c/k)I satisfies
    Σ t_c H_c = 0 at *every* design (a closed polygon in traceless Sym_k);
    the relation space of {H_c} is (stresses) ⊕ ℝ·t. At the top with
    stress-freeness: N cone points positively spanning traceless Sym_k with
    unique circuit = the weights. GTZ(top) ⇔ every such positive circuit
    admits a dominating k-subset; ties = degenerate circuits. **[∗ from K]**
21. **Hypersimplex-vertex capture form** — in atom-square coordinates
    (spanning case) S_C − I = Σ_d (1_C − t)_d G_d, so GTZ ⇔ the spectrahedral
    cone 𝒦 = {α : Σα_d G_d ⪰ 0}, based at the interior point t, captures a
    vertex of the hypersimplex Δ(m,k). **[∗ from K]**
22. **Gram-only characteristic-coefficient form** — Dominates(C) ⇔ all k
    characteristic coefficients of the gap block are ≥ 0; at all-heavy the top
    coefficient is free, so failure is a (k−1)-way branch per subset (k = 3:
    e₂ < 0 ∨ e₃ < 0, with e₂ edge-additive over pair-minors and e₃ the
    discriminant, `dominates_triple_iff_symmetricLegs`). **[K]**
23. **Pencil form** — charpoly(W[C]) = charpoly(diag t_C (Gram_C − I)): the
    whole chart is square-root-free, polynomial in Gram entries and weights,
    at every (m,k). **[K]**
24. **Averaged-charpoly / derivative-mixture form** —
    Σ_{|C|=k} charpoly(W[C]) = f⁽ᵐ⁻ᵏ⁾(x)/(m−k)! for f = charpoly(W); the
    ∏t-weighted average is the aggregate ladder with all coefficients closed
    in (s,t) (`rungThreeAggregate_eq_sum_det_chartGapMinor`); product-form
    weights keep mixtures real-rooted, and GTZ ⇔ at every real chart some
    v ∈ ℝ₊ᵐ makes the v-mixture's least root ≥ 0. Uniform v reproduces Xu's
    constant exactly. **[∗ + K pieces]**
25. **Compound / chirotope form** — Λʲ(Gram) has rank ≤ C(k,j); Λᵏ has rank 1
    with entries d_C·d_C′, d_C = det of the atom k-tuple: the *oriented
    matroid* of the atoms, a realness layer strictly finer than the sign layer,
    currently unopened. **[∗]**
26. **Dual-basis / conic-coordinate form** — at spanning configurations the
    dual basis Hᶜ has tr Hᶜ = t_c and Σ l_c Hᶜ = I; the stress space is
    ker(Gram∘Gram); every gap has coordinates (1_C − t). **[K pieces + M]**

### G. Combinatorial language

27. **Good-k-subset hypergraph form** — the compatibility structure
    (pair-minors + tie legs) always contains a good k-set
    (`elliptopeGoodTriangleCovering` at (7,3)); graph-Turán provably
    insufficient (the icosahedron's compatible graph is complete). **[K]**
28. **Sign-sector form** — the sign pattern of the off-diagonal Gram entries
    (at k = 3 the two-graph / link-word layer: 842 of 1024 sectors survive, in
    8 classes, each realized by an explicit rational design with pairwise
    non-isomorphism a theorem, `sectorClassWitness_pairwise_nonisomorphic`).
    Proved **sharp**: a stratifier, not a route. **[K]**
29. **Tie-classification (equality) form** — the equality manifold of GTZ =
    degenerate (parallel-pair / multiplicity) configurations. *Theorem at
    k = 2* (Nesterenko: three lines with multiplicities); the hinge
    `HingeHoldsAtSize` at k = 3, 4 of 9 pattern classes discharged, all
    sixteen stratum obligations narrowed by balanced stress. **[lit k=2; open k≥3]**
30. **Isoperimetric polygon form (the k = 2 template)** — GTZ(n,2) ⇔ for
    closed planar polygons of fixed perimeter,
    max_{i≠j}(|w_i| + |w_j| − |w_i+w_j|) ≥ 2/n. The general-k analogue is #20
    with the cone constraint of codimension (k−2)(k+1)/2 — zero exactly at
    k = 2, which is why the literature stops there. **[lit + K census]**

### H. Logic / certificate language

31. **RCF-sentence form** — rank k is *one* explicit Π₁ first-order sentence
    over the reals: `DiscriminantCovering 7 ↔ GtzWeightedAll 3`
    (`discriminantCovering_seven_iff_rank_three`, 35 triples × 2 polynomial
    inequalities) and `PivotMinorCoveringFour 11 ↔ GtzWeightedAll 4`
    (330 quadruples × 7 minors). Tarski-decidable in principle; quantifier
    elimination measured infeasible; every wall hit is feasibility, never
    undecidability. **[K≡∀; M wall]**
32. **Positivstellensatz form** — GTZ ⇔ emptiness of the explicit
    semialgebraic failure system, hence (if true) *some* Stengle certificate
    exists; low-degree SOS measured dead, the stationarity variety measured
    positive-dimensional, so degree is unbounded a priori. **[K system; M wall]**
33. **Failure normal form** — a counterexample = a chart point plus C(m,k)
    PSD probe certificates; with probes fixed, the failure region in weight
    space is an open union of convex polyhedral cones
    (`exists_not_gtzOriginal_of_forall_not_dominates` transports it to a
    refutation of the literal 1997 statement). **[K]**

### I. Delimiting contrasts

34. **Field-gap form** — over ℂ the exact threshold is m ≤ k+1
    (`complexGtzWeighted_iff_size_le_rank_add_one`,
    `complexGtzWeighted_six_three_fails`); GTZ says over ℝ there is *no*
    threshold. Rank k's top first exceeds the complex threshold at k = 3 —
    the phase transition. A complex (7,3) design carrying **no stress** exists
    (`exists_complexWeightedDesign_sevenThree_stress_eq_zero`), so the real
    walk's fuel is genuinely absent over ℂ, not merely unproved. **[K]**
35. **Realness quanta** — six independent real Veronese images *span* Sym₃(ℝ)
    (`span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent`) while six
    can never span Herm₃(ℂ) (`exists_mem_hermitianSubmodule_notMem_span_of_six`);
    real fourth-moment floor 3k/(k+2) vs Hermitian 2k/(k+1); real triple
    products extreme (two-graph) vs free phase. Note α₂ = 2 − 2/√3 is the
    sharp complex constant **at rank 2 only** (Nesterenko;
    `trineMargin_lt_alphaRankTwo` shows rank 3 goes strictly below it). **[K]**

### J. The reduction lattice (proven, all ranks)

```
GtzOriginal n k   ⇐ (uniform slice)  GtzWeighted n k            [fixed n]
∀n GtzOriginal n k  ⇔  GtzWeightedAll k  ⇔  GtzWeighted N k     [one cell per rank]
m > N : stress walk reduces          m ≤ 5 (any k) : theorem
m+1 ⇒ m (size monotone)             (m,k) ⇔ (m, m−k) (Naimark)
spike chains lift/descend ranks      failing design ⇒ ¬GtzOriginal at some size
rank 3:  (6,3) ⇔ (7,3) ⇔ (7,4) ⇔ GtzWeightedAll 3 ⇔ 1997@3     [RankThreeEquivalenceHub]
```

Two footnotes. Forms #6–#19 are one statement wearing different clothes —
kernel-equivalent, all funnelling to the scalar of #16. The genuinely distinct
attack surfaces are #14/#15 (value spectrum), #20/#21 (circuit geometry),
#24 (stable mixtures), #25 (chirotope), #29 (equality set), and the walk-side
rigidity inside #10. The traps are catalogued too: #4 is strictly weaker than
GTZ, and the all-floors coverings, the deformation-at-the-crux obligation, the
heavy windows and the (7,3)/(7,4) forms are kernel-proved to *be* the
conjecture, not steps toward it.

## What a closing proof must satisfy

Each clause is a kernel theorem or an exact ≥60-digit measurement:

- **Consume realness** (#34): the two-regime target is itself real-only — the
  complex witness sits at chart value −0.0137 *inside* the band with no
  dominating triple. Every mechanism formalized so far runs verbatim over ℂ.
- **Be exact, with an inhabited equality set**: the infimum is *attained* at
  exact algebraic ties (rational split tetrahedra; a ℚ(√5) tie with uniform
  weights 1/6), so no strict inequality, barrier, or SOS margin survives. The
  only proof in existence (k = 2) is margin-free with the contradiction
  supplied by Perron simplicity alone.
- **Be global across k-subsets** (per-subset arguments are field-blind),
  **use magnitudes beyond signs** (the sign layer is proved sharp), **handle
  the zero-pairing branch**, and **not be a computation** (the stationarity
  variety is positive-dimensional; Gröbner/QE walls are measured).
- The rank-induction step k → k+1 is walled at exactly one of seven
  certificates (`exists_all_certificates_but_discriminant`), so ranks are
  attacked at their tops, one cell per rank, and only a mechanism stated
  cone-intrinsically (in N, the Veronese cone, and the rank-k value floor)
  generalizes across ranks.

## Residuals

**Mathematical (block the conjecture).**
- `GtzWeighted 6 3` — the one open statement; fourteen kernel-equivalent forms.
- The one number shared by three lanes: an explicit band ε ∈ (0, 4/27] for
  `ChartValueBandExclusion` — equivalently a leverage cap 1/ε at every crux
  (`SixThreeCrux.leverageOf_le_inv_of_chartValueBandExclusion`); the partner
  covering ingredient is tight on that whole range.
- A realness consumer: no wired mechanism distinguishes ℝ from ℂ; four
  invariant families exhausted with named counterexample shapes.
- Hinge layer (a): 5 of 9 six-point pattern classes (finite; recipe worked
  twice). Hinge layer (b): 8 tie-freeness obligations — 5 with no current
  lever, 3 narrowed to the balanced-stress sublocus.
- The support-two rung of the index floor (proved ladder |A| ≥ 2 + s, only
  s = 3 done); whether a crux has at most one vanishing pairing; a Lipschitz
  constant for the margin on the collared class plus the reach to the stress
  locus (the cheapest decisive unmeasured number); a production theorem for
  `SevenThreeCrux`; `EliminatesThreeMemberValue` (needs *two* families).

**Measured, not mechanized.** The |A| = 5 orbit emptiness and the index floor
8 (random-restart, known component bias); no (6,3) tie with |A| ≤ 7; the
heavy-arrow refutation (blocked by the walk's existential scale); the
quantitative laws (spread exponent ½, margin numerics); the uniform per-edge
840 and the 192 intersection of the sector ledger; the window-witness
bookkeeping over ℚ(√5).

**Operational.** `Gtz/Audit.lean` does not import the root umbrella — always
build both (`lake build Gtz Gtz.Audit`), else `Gtz.olean` goes missing after a
forced rebuild. Two prose sites are false-when-written and uncorrected by
policy (`Gtz/Quantitative/OrthogonalEdgeSectors.lean:119`,
`Gtz/Design/StratumEmptinessLedger.lean:317` — each contradicted by a tracked
sibling); five G8-era sites are merely superseded. One duplicated audit pin
(`injective_four_of_ne`).

## Layout

```
Gtz/Core/           designs, domination, GtzWeighted/GtzOriginal, sanity pins
Gtz/LinAlg/         PSD kit, Schur/rank-one, projections, 2×2 criteria
Gtz/Reduction/      the walk, crystallization, Naimark, spikes, ConverseBridge,
                    CoveringForm, RankThreeEquivalenceHub
Gtz/Design/         collared classes, line patterns, stratum ledgers, frames
Gtz/Quantitative/   the (6,3)/(7,3) frontier: crux, chart, sectors, floors,
                    value lanes, index floor, minimality layer, dichotomies
Gtz/Ties/           tie/selection obstructions, relabelling action
Gtz/Complex/        the ℂ refutations (SIC, padded SIC)
Gtz/Field/          field-generic designs (RCLike)
Gtz/Certificates/   rational certificate consumption layer
Gtz/Planar/ Corner/ the audited planar platform and corner fiber layers
Gtz/Audit.lean      #print axioms for every declaration, every build
```

## Build & audit

```sh
lake exe cache get          # once — Mathlib oleans
lake build Gtz Gtz.Audit    # both umbrellas; prints every axiom set
```

Standalone files must be checked with
`lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file>`
(the flags are not inherited). Audit pins wrap across lines: parse the audit
stream with a whitespace-collapsing scanner, never an `rg` one-liner.

## Rigor rules

- Nothing is called proven while it contains `sorry`; the expected axiom set
  is `propext, Classical.choice, Quot.sound` — nothing else, ever.
- Definitions stay minimal and Mathlib-anchored; junk-value footguns are
  fenced at every use. `Core/Sanity.lean` is the definition-drift alarm.
- Mechanization is treated as audit: statement-hygiene findings and every
  refuted claim are recorded where they were found; measured facts are never
  presented as theorems, and the tags above ([K]/[M]/[∗]) are load-bearing.
- Every quantitative claim at the frontier is exact-arithmetic or ≥60 digits;
  this campaign has recorded seven float artifacts, two of which briefly
  looked like refutations of the conjecture.
