import Gtz.Design.RigidityBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# K4 chart closure: contraction descent at the max-conductance edge

Everything of the K4 chart obligation's decided route EXCEPT the endgame.
The target is `Gtz.DirectionChartIsTieFree Gtz.kFourDirection` (consumed by
`Gtz.stressFreeStratumIsTieFree_graphicKFour_of_chart`); the route is
contraction descent at a maximum-conductance edge.  Vocabulary: at a chart
point write `conductance c = mass c / weight c` and
`alpha c = conductance c - mass c > 0`; in the graphic dictionary label
`c` is a K4 edge (`0=12, 1=13, 2=23, 3=14, 4=24, 5=34` on nodes `1..4`,
gauge `x4 = 0`), the four dependent triples are the four triangles, and the
sixteen basis triples are the spanning trees.

This module proves, in order:

* the rank-two Foster engine — the series-ratio identity, slack
  monotonicity, and the pair-gap determinant (the three scalar bricks
  driving the rank-two slack lemma);
* positive definiteness from leading minors for explicit `2x2` and `3x3`
  symmetric matrices by completed squares (`sylvesterLift`) — no eigenvalue
  API anywhere;
* the deletion-contraction determinant normal forms for the lifted trees
  through the contracted edge (star shape, gauge-node star shape, and the
  two path shapes);
* the **rank-two slack lemma** (Lemma A): three positive parallel classes
  in rank two with total slack below one always contain a strictly
  dominating pair;
* chart bookkeeping — the off-edge slack identity (where the chart
  constraint `sum weight = 1` is spent) and kappa positivity at a
  max-conductance edge;
* the entrywise closed forms of the chart gap for the eight spanning trees
  through edge `5` and the four triangles;
* the four dependent triples are never positive semidefinite at any chart
  point (so a weak triple is always a spanning tree);
* the contraction layer at edge `5`: restriction of a through-edge tree gap
  to the contracted plane is the leading `2x2` block, the class slack bound,
  and `kFourContractionHasWinner` — at EVERY chart point some spanning tree
  through edge `5` has positive definite contracted block;
* the endgame vocabulary (`KFourMaxEdgeHostsStrictTree`,
  `KFourMaxEdgeDetPigeonhole`) and the consumption bridge taking the host
  statement as a HYPOTHESIS down to
  `Gtz.DirectionChartIsTieFree Gtz.kFourDirection`;
* **the kernel REFUTATION of both endgame Props** at the exact witness
  `maxEdgeRefuterPoint`: masses `(36, 1/60, 1/60, 10, 20, 1/60)`, weights
  `(3/5, 1/60, 1/60, 1/10, 1/4, 1/60)`, conductances `(60, 1, 1, 100, 80, 1)`.
  Edge `3` is the STRICT argmax-conductance edge, yet all ten card-3
  selections through it fail positive definiteness and all eight
  through-trees have negative gap determinant — the dominant masses sit on
  edges `0` and `4` and `{0, 3, 4}` is a dependent triangle, so no spanning
  tree through `3` keeps both heavy edges.  The chart obligation itself is
  INTACT at the witness: `{0, 1, 4}` dominates strictly
  (`maxEdgeRefuterPoint_hasStrictTriple`).

So the max-conductance SELECTION mechanism is dead, not the route's parts:
every brick above the selection (Foster engine, Lemma A, contraction layer,
Sylvester lifts, det normal forms) survives, the bridge is retained as the
shape any repaired selection Prop must feed, and the witness's strictly
dominating triples all contain the dominant-MASS pair `{0, 4}` — pointing
any repaired selection at the masses, not the conductances.  Every consumer
takes the (refuted) host statement as an explicit binder, never as an axiom.
-/

namespace Gtz

open Matrix

/-! ## The rank-two Foster engine

Three scalar facts about positive `beta`s: the series-ratio identity (the
rank-two form of Foster's theorem, `#edges - rank = 3 - 2 = 1`), slack
monotonicity, and the pair-gap determinant in the normalized frame. -/

/-- **The Foster identity.**  With `seriesBC = betaB*betaC/(betaB+betaC)`
etc., the three series-over-total ratios sum to exactly one: the rank-two
form of Foster's theorem, the engine of the contraction lemma.  All-pairs
failure `M_V >= H_V` therefore forces unit slack. -/
theorem fosterIdentitySeries (betaA betaB betaC : ℝ)
    (hposA : 0 < betaA) (hposB : 0 < betaB) (hposC : 0 < betaC) :
    (betaB * betaC / (betaB + betaC))
        / (betaA + betaB * betaC / (betaB + betaC))
      + (betaA * betaC / (betaA + betaC))
        / (betaB + betaA * betaC / (betaA + betaC))
      + (betaA * betaB / (betaA + betaB))
        / (betaC + betaA * betaB / (betaA + betaB)) = 1 := by
  have hsumBC : (0 : ℝ) < betaB + betaC := by linarith
  have hsumAC : (0 : ℝ) < betaA + betaC := by linarith
  have hsumAB : (0 : ℝ) < betaA + betaB := by linarith
  have hdenA : (0 : ℝ) < betaA + betaB * betaC / (betaB + betaC) := by positivity
  have hdenB : (0 : ℝ) < betaB + betaA * betaC / (betaA + betaC) := by positivity
  have hdenC : (0 : ℝ) < betaC + betaA * betaB / (betaA + betaB) := by positivity
  field_simp
  ring

/-- **Slack monotonicity.**  Growing the mass past the series threshold
grows the spent slack: `H <= M` gives `H/(beta+H) <= M/(beta+M)`. -/
theorem slackRatio_mono (beta seriesValue massValue : ℝ) (hbeta : 0 < beta)
    (hseries : 0 ≤ seriesValue) (hle : seriesValue ≤ massValue) :
    seriesValue / (beta + seriesValue) ≤ massValue / (beta + massValue) := by
  have hdenH : (0 : ℝ) < beta + seriesValue := by linarith
  have hdenM : (0 : ℝ) < beta + massValue := by linarith
  rw [div_le_div_iff₀ hdenH hdenM]
  nlinarith

/-- **The pair determinant.**  In the normalized rank-two frame the gap of
the pair excluding the third class has determinant
`betaX*betaZ - massV*(betaX + betaZ)`: the pair dominates strictly iff the
excluded mass is below the series conductance of the kept pair. -/
theorem rankTwoPairGap_det (betaX betaZ massV : ℝ) :
    (!![betaX - massV, massV; massV, betaZ - massV] : Matrix (Fin 2) (Fin 2) ℝ).det
      = betaX * betaZ - massV * (betaX + betaZ) := by
  simp [Matrix.det_fin_two]
  ring

/-! ## Positive definiteness from leading minors

Sylvester's criterion for explicit symmetric `2x2` and `3x3` real matrices,
proved by completed squares in the house `posDef_iff_dotProduct_mulVec`
pattern — no eigenvalue or square-root API. -/

/-- A symmetric `2x2` matrix with positive corner and positive determinant
is positive definite: `diagOne * form = (diagOne*x0 + offDiag*x1)^2 +
det * x1^2`. -/
theorem posDef_of_leadingMinors_fin_two (diagOne offDiag diagTwo : ℝ)
    (hcorner : 0 < diagOne)
    (hminor : 0 < diagOne * diagTwo - offDiag ^ 2) :
    (!![diagOne, offDiag; offDiag, diagTwo] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hform : vecArg ⬝ᵥ ((!![diagOne, offDiag; offDiag, diagTwo]
          : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ vecArg)
        = diagOne * vecArg 0 ^ 2 + 2 * offDiag * (vecArg 0 * vecArg 1)
          + diagTwo * vecArg 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [hform]
    have hkey : diagOne * (diagOne * vecArg 0 ^ 2
          + 2 * offDiag * (vecArg 0 * vecArg 1) + diagTwo * vecArg 1 ^ 2)
        = (diagOne * vecArg 0 + offDiag * vecArg 1) ^ 2
          + (diagOne * diagTwo - offDiag ^ 2) * vecArg 1 ^ 2 := by ring
    by_cases hsecond : vecArg 1 = 0
    · have hfirst : vecArg 0 ≠ 0 := by
        intro hzero
        apply hne
        funext index
        fin_cases index
        · exact hzero
        · exact hsecond
      rw [hsecond]
      nlinarith [mul_pos hcorner (pow_two_pos_of_ne_zero hfirst)]
    · nlinarith [hkey, sq_nonneg (diagOne * vecArg 0 + offDiag * vecArg 1),
        mul_pos hminor (pow_two_pos_of_ne_zero hsecond)]

/-- The corner of a positive definite explicit `2x2` matrix is positive
(quadratic form at the first basis vector). -/
theorem posDef_fin_two_corner_pos {diagOne offDiag diagTwo : ℝ}
    (hposDef : (!![diagOne, offDiag; offDiag, diagTwo]
      : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    0 < diagOne := by
  have hbasis_ne : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hfirst := congrFun hzero 0
    simp at hfirst
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hbasis_ne
  rw [star_trivial] at hvalue
  have hform : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ((!![diagOne, offDiag; offDiag, diagTwo]
        : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0]) = diagOne := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  linarith [hform ▸ hvalue]

/-- The determinant minor of a positive definite explicit `2x2` matrix is
positive (quadratic form at the witness `(offDiag, -diagOne)`). -/
theorem posDef_fin_two_minor_pos {diagOne offDiag diagTwo : ℝ}
    (hposDef : (!![diagOne, offDiag; offDiag, diagTwo]
      : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    0 < diagOne * diagTwo - offDiag ^ 2 := by
  have hcorner : 0 < diagOne := posDef_fin_two_corner_pos hposDef
  have hwitness_ne : (![offDiag, -diagOne] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hsecond := congrFun hzero 1
    simp at hsecond
    exact absurd hsecond (ne_of_gt hcorner)
  have hvalue := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hwitness_ne
  rw [star_trivial] at hvalue
  have hform : (![offDiag, -diagOne] : Fin 2 → ℝ)
        ⬝ᵥ ((!![diagOne, offDiag; offDiag, diagTwo]
          : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![offDiag, -diagOne])
      = diagOne * (diagOne * diagTwo - offDiag ^ 2) := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    ring
  nlinarith [hform ▸ hvalue]

/-- A symmetric `3x3` matrix whose three leading principal minors are
positive is positive definite, by the completed-square identity

`corner * blockMinor * form = blockMinor * (corner*x0 + b*x1 + c*x2)^2
  + (blockMinor*x1 + (corner*e - b*c)*x2)^2 + corner * det * x2^2`. -/
theorem posDef_of_leadingMinors_fin_three
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ)
    (hcorner : 0 < entryOneOne)
    (hblockMinor : 0 < entryOneOne * entryTwoTwo - entryOneTwo ^ 2)
    (hdetMinor : 0 < entryOneOne * entryTwoTwo * entryThreeThree
      - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
      + 2 * entryOneTwo * entryOneThree * entryTwoThree
      - entryOneThree ^ 2 * entryTwoTwo) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hform : vecArg ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
            entryOneTwo, entryTwoTwo, entryTwoThree;
            entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = entryOneOne * vecArg 0 ^ 2 + 2 * entryOneTwo * (vecArg 0 * vecArg 1)
          + 2 * entryOneThree * (vecArg 0 * vecArg 2)
          + entryTwoTwo * vecArg 1 ^ 2
          + 2 * entryTwoThree * (vecArg 1 * vecArg 2)
          + entryThreeThree * vecArg 2 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    have hkey : entryOneOne * (entryOneOne * entryTwoTwo - entryOneTwo ^ 2)
          * (entryOneOne * vecArg 0 ^ 2 + 2 * entryOneTwo * (vecArg 0 * vecArg 1)
            + 2 * entryOneThree * (vecArg 0 * vecArg 2)
            + entryTwoTwo * vecArg 1 ^ 2
            + 2 * entryTwoThree * (vecArg 1 * vecArg 2)
            + entryThreeThree * vecArg 2 ^ 2)
        = (entryOneOne * entryTwoTwo - entryOneTwo ^ 2)
              * (entryOneOne * vecArg 0 + entryOneTwo * vecArg 1
                + entryOneThree * vecArg 2) ^ 2
          + ((entryOneOne * entryTwoTwo - entryOneTwo ^ 2) * vecArg 1
              + (entryOneOne * entryTwoThree - entryOneTwo * entryOneThree)
                * vecArg 2) ^ 2
          + entryOneOne * (entryOneOne * entryTwoTwo * entryThreeThree
              - entryOneOne * entryTwoThree ^ 2
              - entryOneTwo ^ 2 * entryThreeThree
              + 2 * entryOneTwo * entryOneThree * entryTwoThree
              - entryOneThree ^ 2 * entryTwoTwo) * vecArg 2 ^ 2 := by ring
    by_cases hthird : vecArg 2 = 0
    · by_cases hsecond : vecArg 1 = 0
      · have hfirst : vecArg 0 ≠ 0 := by
          intro hzero
          apply hne
          funext index
          fin_cases index
          · exact hzero
          · exact hsecond
          · exact hthird
        rw [hsecond, hthird]
        nlinarith [mul_pos hcorner (pow_two_pos_of_ne_zero hfirst)]
      · rw [hthird]
        have hkeyTwo : entryOneOne * (entryOneOne * vecArg 0 ^ 2
              + 2 * entryOneTwo * (vecArg 0 * vecArg 1)
              + 2 * entryOneThree * (vecArg 0 * 0)
              + entryTwoTwo * vecArg 1 ^ 2
              + 2 * entryTwoThree * (vecArg 1 * 0)
              + entryThreeThree * 0 ^ 2)
            = (entryOneOne * vecArg 0 + entryOneTwo * vecArg 1) ^ 2
              + (entryOneOne * entryTwoTwo - entryOneTwo ^ 2)
                * vecArg 1 ^ 2 := by ring
        nlinarith [hkeyTwo, sq_nonneg (entryOneOne * vecArg 0 + entryOneTwo * vecArg 1),
          mul_pos hblockMinor (pow_two_pos_of_ne_zero hsecond)]
    · nlinarith [hkey,
        mul_nonneg hblockMinor.le (sq_nonneg (entryOneOne * vecArg 0
          + entryOneTwo * vecArg 1 + entryOneThree * vecArg 2)),
        sq_nonneg ((entryOneOne * entryTwoTwo - entryOneTwo ^ 2) * vecArg 1
          + (entryOneOne * entryTwoThree - entryOneTwo * entryOneThree) * vecArg 2),
        mul_pos (mul_pos hcorner hdetMinor) (pow_two_pos_of_ne_zero hthird),
        mul_pos hcorner hblockMinor]

/-- **The Schur lift.**  Positive definite leading `2x2` block plus positive
determinant makes the symmetric `3x3` matrix positive definite (kappa
positivity is implied, not needed: the completed squares of
`posDef_of_leadingMinors_fin_three` consume only the three leading minors). -/
theorem sylvesterLift
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ)
    (hblock : (!![entryOneOne, entryOneTwo; entryOneTwo, entryTwoTwo]
      : Matrix (Fin 2) (Fin 2) ℝ).PosDef)
    (hdet : 0 < (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).det) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  have hdetExpanded : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).det
      = entryOneOne * entryTwoTwo * entryThreeThree
        - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
        + 2 * entryOneTwo * entryOneThree * entryTwoThree
        - entryOneThree ^ 2 * entryTwoTwo := by
    simp [Matrix.det_fin_three]
    ring
  rw [hdetExpanded] at hdet
  exact posDef_of_leadingMinors_fin_three entryOneOne entryOneTwo entryOneThree
    entryTwoTwo entryTwoThree entryThreeThree
    (posDef_fin_two_corner_pos hblock) (posDef_fin_two_minor_pos hblock) hdet

/-! ## Deletion-contraction determinant normal forms

The determinant of each lifted tree `{e*} u U` splits as
`alpha_{e*} * det(contracted U-gap) + R_U`, with `R_U` the deletion term
over the diamond `K4 - e*`.  Pure ring facts on the explicit `3x3` gap
matrices in the `alpha`/mass currency (`alpha_c = conductance_c - mass_c`),
at the normalized contracted edge `5`.  Sympy-verified exactly before
statement; `ring` re-proves them in the kernel. -/

/-- **The star lift determinant normal form.**  The explicit gap matrix of
the lifted tree `{1,2,5}` (star at node `3`) in potentials with the node-4
gauge; its determinant is EXACTLY the deletion-contraction normal form
`alpha5 * Delta + m0*(alpha1+alpha2)*(m3+m4)
 - m3*alpha1*(alpha2-m4) - m4*alpha2*(alpha1-m3)`,
with `Delta = (alpha1-m3)*(alpha2-m4) - m0*((alpha1-m3)+(alpha2-m4))` the
contracted (K4/34) gap determinant.  The whole Schur lift condition given
the contraction win is this single scalar. -/
theorem starLiftDet_normalForm (alphaOne alphaTwo alphaFive massZero massThree
    massFour : ℝ) :
    (!![alphaOne - massZero - massThree, massZero, -alphaOne;
        massZero, alphaTwo - massZero - massFour, -alphaTwo;
        -alphaOne, -alphaTwo, alphaFive + alphaOne + alphaTwo] :
      Matrix (Fin 3) (Fin 3) ℝ).det
      = alphaFive * ((alphaOne - massThree) * (alphaTwo - massFour)
            - massZero * ((alphaOne - massThree) + (alphaTwo - massFour)))
        + massZero * (alphaOne + alphaTwo) * (massThree + massFour)
        - massThree * alphaOne * (alphaTwo - massFour)
        - massFour * alphaTwo * (alphaOne - massThree) := by
  simp [Matrix.det_fin_three]
  ring

/-- The star lift at the gauge node: determinant normal form of the
`{3,4,5}` gap matrix (star at node `4`), deletion term
`(alpha3+alpha4)*(m0*(m1+m2) + m1*m2) - alpha3*alpha4*(m1+m2)`. -/
theorem starLiftDetGaugeNode_normalForm (alphaThree alphaFour alphaFive
    massZero massOne massTwo : ℝ) :
    (!![alphaThree - massZero - massOne, massZero, massOne;
        massZero, alphaFour - massZero - massTwo, massTwo;
        massOne, massTwo, alphaFive - massOne - massTwo] :
      Matrix (Fin 3) (Fin 3) ℝ).det
      = alphaFive * ((alphaThree - massOne) * (alphaFour - massTwo)
            - massZero * ((alphaThree - massOne) + (alphaFour - massTwo)))
        + (alphaThree + alphaFour) * (massZero * (massOne + massTwo)
            + massOne * massTwo)
        - alphaThree * alphaFour * (massOne + massTwo) := by
  simp [Matrix.det_fin_three]
  ring

/-- Path lift with representatives from both doubled classes: determinant
normal form of the `{1,4,5}` gap matrix (S4-orbit also covers `{2,3,5}`),
deletion term `alpha1*m3*(m0+m2) + alpha4*m2*(m0+m3)
- alpha1*alpha4*(m0+m2+m3) - m0*m2*m3`. -/
theorem pathLiftDetDoubledClasses_normalForm (alphaOne alphaFour alphaFive
    massZero massTwo massThree : ℝ) :
    (!![alphaOne - massZero - massThree, massZero, -alphaOne;
        massZero, alphaFour - massZero - massTwo, massTwo;
        -alphaOne, massTwo, alphaFive + alphaOne - massTwo] :
      Matrix (Fin 3) (Fin 3) ℝ).det
      = alphaFive * ((alphaOne - massThree) * (alphaFour - massTwo)
            - massZero * ((alphaOne - massThree) + (alphaFour - massTwo)))
        + alphaOne * massThree * (massZero + massTwo)
        + alphaFour * massTwo * (massZero + massThree)
        - alphaOne * alphaFour * (massZero + massTwo + massThree)
        - massZero * massTwo * massThree := by
  simp [Matrix.det_fin_three]
  ring

/-- Path lift through the singleton class (triangle edge `0`): determinant
normal form of the `{0,1,5}` gap matrix (S4-orbit also covers the other
three `{0,c,5}` lifts), deletion term
`(m3+m4)*(m2*(alpha0+alpha1) - alpha0*alpha1) + m3*m4*(alpha1-m2)`. -/
theorem pathLiftDetSingletonClass_normalForm (alphaZero alphaOne alphaFive
    massTwo massThree massFour : ℝ) :
    (!![alphaZero + alphaOne - massThree, -alphaZero, -alphaOne;
        -alphaZero, alphaZero - massTwo - massFour, massTwo;
        -alphaOne, massTwo, alphaFive + alphaOne - massTwo] :
      Matrix (Fin 3) (Fin 3) ℝ).det
      = alphaFive * ((alphaOne - massThree) * alphaZero
            - (massTwo + massFour) * ((alphaOne - massThree) + alphaZero))
        + (massThree + massFour) * (massTwo * (alphaZero + alphaOne)
            - alphaZero * alphaOne)
        + massThree * massFour * (alphaOne - massTwo) := by
  simp [Matrix.det_fin_three]
  ring

/-! ## The rank-two slack lemma (Lemma A)

Normalized frame `fA = (1,0)`, `fB = (0,1)`, `fC = (1,-1)`: three pairwise
independent classes with conductances `Y` and masses `M`, all positive.  The
pair gap excluding class `V` is
`Y_X fX fXᵀ + Y_Z fZ fZᵀ - (M_A fA fAᵀ + M_B fB fBᵀ + M_C fC fCᵀ)`; the
three matrices below are these gaps entry by entry (sympy-verified). -/

/-- **The rank-two slack lemma.**  If the total slack
`M_A/Y_A + M_B/Y_B + M_C/Y_C` is below one, some pair gap is positive
definite.  Proof: if all three pairs fail, the pair criterion forces every
excluded mass to reach its series conductance `H_V`; slack monotonicity and
the Foster identity then force slack `>= 1`. -/
theorem rankTwoSlackLemma (condA condB condC massA massB massC : ℝ)
    (hcondA : 0 < condA) (hcondB : 0 < condB) (hcondC : 0 < condC)
    (hmassA : 0 < massA) (hmassB : 0 < massB) (hmassC : 0 < massC)
    (hslack : massA / condA + massB / condB + massC / condC < 1) :
    (!![condA - massA - massC, massC;
        massC, condB - massB - massC] : Matrix (Fin 2) (Fin 2) ℝ).PosDef
    ∨ (!![condA + condC - massA - massC, massC - condC;
          massC - condC, condC - massB - massC]
        : Matrix (Fin 2) (Fin 2) ℝ).PosDef
    ∨ (!![condC - massA - massC, massC - condC;
          massC - condC, condB + condC - massB - massC]
        : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have hratioA : massA / condA < 1 := by
    have hposB : 0 < massB / condB := div_pos hmassB hcondB
    have hposC : 0 < massC / condC := div_pos hmassC hcondC
    linarith
  have hratioB : massB / condB < 1 := by
    have hposA : 0 < massA / condA := div_pos hmassA hcondA
    have hposC : 0 < massC / condC := div_pos hmassC hcondC
    linarith
  have hratioC : massC / condC < 1 := by
    have hposA : 0 < massA / condA := div_pos hmassA hcondA
    have hposB : 0 < massB / condB := div_pos hmassB hcondB
    linarith
  have hbetaA : 0 < condA - massA := by
    have hlt := (div_lt_one hcondA).mp hratioA
    linarith
  have hbetaB : 0 < condB - massB := by
    have hlt := (div_lt_one hcondB).mp hratioB
    linarith
  have hbetaC : 0 < condC - massC := by
    have hlt := (div_lt_one hcondC).mp hratioC
    linarith
  by_contra hallFail
  obtain ⟨hfailAB, hfailRest⟩ := not_or.mp hallFail
  obtain ⟨hfailAC, hfailBC⟩ := not_or.mp hfailRest
  -- pair criterion, contrapositive of failure: series conductance <= mass
  have hsumAB : 0 < condA - massA + (condB - massB) := by linarith
  have hsumAC : 0 < condA - massA + (condC - massC) := by linarith
  have hsumBC : 0 < condB - massB + (condC - massC) := by linarith
  have hseriesC_le : (condA - massA) * (condB - massB)
      / (condA - massA + (condB - massB)) ≤ massC := by
    by_contra hnot
    have hlt := not_le.mp hnot
    have hprod : massC * (condA - massA + (condB - massB))
        < (condA - massA) * (condB - massB) := (lt_div_iff₀ hsumAB).mp hlt
    refine hfailAB (posDef_of_leadingMinors_fin_two _ _ _ ?_ ?_)
    · have hHlt : (condA - massA) * (condB - massB)
          / (condA - massA + (condB - massB)) < condA - massA := by
        rw [div_lt_iff₀ hsumAB]
        nlinarith [mul_pos hbetaA hbetaA]
      linarith
    · nlinarith [hprod]
  have hseriesB_le : (condA - massA) * (condC - massC)
      / (condA - massA + (condC - massC)) ≤ massB := by
    by_contra hnot
    have hlt := not_le.mp hnot
    have hprod : massB * (condA - massA + (condC - massC))
        < (condA - massA) * (condC - massC) := (lt_div_iff₀ hsumAC).mp hlt
    refine hfailAC (posDef_of_leadingMinors_fin_two _ _ _ ?_ ?_)
    · linarith
    · nlinarith [hprod]
  have hseriesA_le : (condB - massB) * (condC - massC)
      / (condB - massB + (condC - massC)) ≤ massA := by
    by_contra hnot
    have hlt := not_le.mp hnot
    have hprod : massA * (condB - massB + (condC - massC))
        < (condB - massB) * (condC - massC) := (lt_div_iff₀ hsumBC).mp hlt
    refine hfailBC (posDef_of_leadingMinors_fin_two _ _ _ ?_ ?_)
    · have hHlt : (condB - massB) * (condC - massC)
          / (condB - massB + (condC - massC)) < condC - massC := by
        rw [div_lt_iff₀ hsumBC]
        nlinarith [mul_pos hbetaC hbetaC]
      linarith
    · nlinarith [hprod]
  -- slack monotonicity feeds the Foster identity: total slack must reach one
  have hfoster := fosterIdentitySeries (condA - massA) (condB - massB)
    (condC - massC) hbetaA hbetaB hbetaC
  have hmonoA := slackRatio_mono (condA - massA)
    ((condB - massB) * (condC - massC) / (condB - massB + (condC - massC)))
    massA hbetaA
    (div_nonneg (mul_nonneg hbetaB.le hbetaC.le) hsumBC.le) hseriesA_le
  have hmonoB := slackRatio_mono (condB - massB)
    ((condA - massA) * (condC - massC) / (condA - massA + (condC - massC)))
    massB hbetaB
    (div_nonneg (mul_nonneg hbetaA.le hbetaC.le) hsumAC.le) hseriesB_le
  have hmonoC := slackRatio_mono (condC - massC)
    ((condA - massA) * (condB - massB) / (condA - massA + (condB - massB)))
    massC hbetaC
    (div_nonneg (mul_nonneg hbetaA.le hbetaB.le) hsumAB.le) hseriesC_le
  rw [show condA - massA + massA = condA by ring] at hmonoA
  rw [show condB - massB + massB = condB by ring] at hmonoB
  rw [show condC - massC + massC = condC by ring] at hmonoC
  linarith [hfoster, hmonoA, hmonoB, hmonoC, hslack]

/-! ## Chart bookkeeping

Where the chart constraint `sum weight = 1` is spent, and kappa positivity
at a maximum-conductance edge. -/

/-- Mass divided by conductance is weight: `m_c / (m_c / w_c) = w_c`. -/
theorem massDivConductance_eq_weight (point : DirectionChartPoint 6)
    (label : Fin 6) :
    point.mass label / (point.mass label / point.weight label)
      = point.weight label := by
  rw [div_div_eq_mul_div,
    mul_div_cancel_left₀ _ (ne_of_gt (point.mass_pos label))]

/-- **The off-edge slack identity.**  Summing `m_c / y_c` over the labels
away from an edge spends the chart constraint:
`sum_{c != e} m_c / y_c = 1 - w_e`.  This is the strict sub-unit budget the
contracted problem lives on. -/
theorem offEdgeSlack_eq_one_sub_weight (point : DirectionChartPoint 6)
    (edge : Fin 6) :
    ∑ label ∈ Finset.univ.erase edge,
        point.mass label / (point.mass label / point.weight label)
      = 1 - point.weight edge := by
  calc ∑ label ∈ Finset.univ.erase edge,
        point.mass label / (point.mass label / point.weight label)
      = ∑ label ∈ Finset.univ.erase edge, point.weight label :=
        Finset.sum_congr rfl fun label _ => massDivConductance_eq_weight point label
    _ = 1 - point.weight edge := by
        have hadd := Finset.sum_erase_add Finset.univ point.weight
          (Finset.mem_univ edge)
        rw [point.weight_sum_one] at hadd
        linarith

/-- **Kappa positivity.**  At a max-conductance edge (here normalized to
label `5` = K4 edge `34`; labels `1, 2` are the other two edges at node `3`),
the dropped masses cannot reach the top conductance:
`m_5 + m_1 + m_2 < y_5`.  Only `weight_sum_one`, positivity, and
edge-maximality are used. -/
theorem kappaPositive_atMaxEdge (point : DirectionChartPoint 6)
    (hmax : ∀ label, point.mass label / point.weight label
      ≤ point.mass 5 / point.weight 5) :
    point.mass 5 + point.mass 1 + point.mass 2
      < point.mass 5 / point.weight 5 := by
  set topConductance := point.mass 5 / point.weight 5 with htopDef
  have htopPos : 0 < topConductance :=
    div_pos (point.mass_pos 5) (point.weight_pos 5)
  have hmassLe : ∀ label, point.mass label ≤ point.weight label * topConductance := by
    intro label
    have hstep := hmax label
    have hwPos := point.weight_pos label
    calc point.mass label
        = point.weight label * (point.mass label / point.weight label) := by
          field_simp
      _ ≤ point.weight label * topConductance := by
          exact mul_le_mul_of_nonneg_left hstep (le_of_lt hwPos)
  have hsumSix : point.weight 0 + point.weight 1 + point.weight 2
      + point.weight 3 + point.weight 4 + point.weight 5 = 1 := by
    have hsum := point.weight_sum_one
    rwa [Fin.sum_univ_six] at hsum
  have hw0 := point.weight_pos 0
  have hw3 := point.weight_pos 3
  have hw4 := point.weight_pos 4
  have hshare : point.weight 5 + point.weight 1 + point.weight 2 < 1 := by
    linarith
  have hbound1 := hmassLe 1
  have hbound2 := hmassLe 2
  have hbound5 := hmassLe 5
  nlinarith

/-! ## Tree lists in chart labels -/

/-- The sixteen spanning trees of K4 in chart labels (bases of `M(K4)`). -/
def kFourSpanningTreeList : List (Finset (Fin 6)) :=
  [{0, 1, 3}, {0, 2, 4}, {1, 2, 5}, {3, 4, 5},
   {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {0, 2, 5},
   {0, 3, 5}, {0, 4, 5}, {1, 2, 3}, {1, 2, 4},
   {1, 3, 4}, {1, 4, 5}, {2, 3, 4}, {2, 3, 5}]

/-- The eight spanning trees through edge `5`: the two stars at the edge's
endpoints and the six paths, i.e. `{5} u U` for `U` a spanning tree of the
contraction `K4/5` (classes `A = {1,3}`, `B = {2,4}`, `C = {0}`). -/
def kFourTreesThroughEdgeFive : List (Finset (Fin 6)) :=
  [{1, 2, 5}, {3, 4, 5}, {1, 4, 5}, {2, 3, 5},
   {0, 1, 5}, {0, 2, 5}, {0, 3, 5}, {0, 4, 5}]

/-- The four dependent triples of the K4 chart: the four triangles. -/
def kFourDependentTripleList : List (Finset (Fin 6)) :=
  [{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]

/-- Every through-edge-5 tree is a spanning tree containing label `5`. -/
theorem kFourTreesThroughEdgeFive_spanning :
    ∀ tree ∈ kFourTreesThroughEdgeFive,
      tree ∈ kFourSpanningTreeList ∧ (5 : Fin 6) ∈ tree := by decide

/-! ## Entrywise gap matrices

The chart gap `directionChartGap kFourDirection mass weight T` at SYMBOLIC
mass and weight, entry by entry, for the eight spanning trees through edge
`5` and the four triangles.  The leading `2x2` entries are arranged in the
rank-two-slack frame (`cond - classMass - m_0`) so the contraction layer
consumes them syntactically.  All twelve matrices sympy-verified against
the definition before statement. -/

/-- The `{1,2,5}` chart gap (star at node `3`), entry by entry. -/
theorem kFourGap_treeOneTwoFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {1, 2, 5}
      = Matrix.of
          ![![point.mass 1 / point.weight 1 - (point.mass 1 + point.mass 3)
                - point.mass 0,
              point.mass 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0,
              point.mass 2 / point.weight 2 - (point.mass 2 + point.mass 4)
                - point.mass 0,
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 5 / point.weight 5 + point.mass 1 / point.weight 1
                + point.mass 2 / point.weight 2
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{3,4,5}` chart gap (star at the gauge node `4`), entry by entry. -/
theorem kFourGap_treeThreeFourFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {3, 4, 5}
      = Matrix.of
          ![![point.mass 3 / point.weight 3 - (point.mass 1 + point.mass 3)
                - point.mass 0,
              point.mass 0, point.mass 1],
            ![point.mass 0,
              point.mass 4 / point.weight 4 - (point.mass 2 + point.mass 4)
                - point.mass 0,
              point.mass 2],
            ![point.mass 1, point.mass 2,
              point.mass 5 / point.weight 5
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{1,4,5}` chart gap (path, doubled-class representatives), entry by
entry. -/
theorem kFourGap_treeOneFourFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {1, 4, 5}
      = Matrix.of
          ![![point.mass 1 / point.weight 1 - (point.mass 1 + point.mass 3)
                - point.mass 0,
              point.mass 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0,
              point.mass 4 / point.weight 4 - (point.mass 2 + point.mass 4)
                - point.mass 0,
              point.mass 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2,
              point.mass 5 / point.weight 5 + point.mass 1 / point.weight 1
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{2,3,5}` chart gap (path, doubled-class representatives), entry by
entry. -/
theorem kFourGap_treeTwoThreeFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {2, 3, 5}
      = Matrix.of
          ![![point.mass 3 / point.weight 3 - (point.mass 1 + point.mass 3)
                - point.mass 0,
              point.mass 0, point.mass 1],
            ![point.mass 0,
              point.mass 2 / point.weight 2 - (point.mass 2 + point.mass 4)
                - point.mass 0,
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 5 / point.weight 5 + point.mass 2 / point.weight 2
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0,1,5}` chart gap (path through the singleton class), entry by
entry. -/
theorem kFourGap_treeZeroOneFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 1, 5}
      = Matrix.of
          ![![point.mass 1 / point.weight 1 + point.mass 0 / point.weight 0
                - (point.mass 1 + point.mass 3) - point.mass 0,
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 - (point.mass 2 + point.mass 4)
                - point.mass 0,
              point.mass 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2,
              point.mass 5 / point.weight 5 + point.mass 1 / point.weight 1
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0,2,5}` chart gap (path through the singleton class), entry by
entry. -/
theorem kFourGap_treeZeroTwoFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 2, 5}
      = Matrix.of
          ![![point.mass 0 / point.weight 0 - (point.mass 1 + point.mass 3)
                - point.mass 0,
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 2 / point.weight 2 + point.mass 0 / point.weight 0
                - (point.mass 2 + point.mass 4) - point.mass 0,
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 5 / point.weight 5 + point.mass 2 / point.weight 2
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0,3,5}` chart gap (path through the singleton class), entry by
entry. -/
theorem kFourGap_treeZeroThreeFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 3, 5}
      = Matrix.of
          ![![point.mass 3 / point.weight 3 + point.mass 0 / point.weight 0
                - (point.mass 1 + point.mass 3) - point.mass 0,
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 - (point.mass 2 + point.mass 4)
                - point.mass 0,
              point.mass 2],
            ![point.mass 1, point.mass 2,
              point.mass 5 / point.weight 5
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0,4,5}` chart gap (path through the singleton class), entry by
entry. -/
theorem kFourGap_treeZeroFourFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 4, 5}
      = Matrix.of
          ![![point.mass 0 / point.weight 0 - (point.mass 1 + point.mass 3)
                - point.mass 0,
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 4 / point.weight 4 + point.mass 0 / point.weight 0
                - (point.mass 2 + point.mass 4) - point.mass 0,
              point.mass 2],
            ![point.mass 1, point.mass 2,
              point.mass 5 / point.weight 5
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0,1,2}` chart gap (triangle `abc`), entry by entry. -/
theorem kFourGap_triangleZeroOneTwo_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 1, 2}
      = Matrix.of
          ![![point.mass 0 / point.weight 0 + point.mass 1 / point.weight 1
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 + point.mass 2 / point.weight 2
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 1 / point.weight 1 + point.mass 2 / point.weight 2
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0,3,4}` chart gap (triangle `abd`), entry by entry. -/
theorem kFourGap_triangleZeroThreeFour_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 3, 4}
      = Matrix.of
          ![![point.mass 0 / point.weight 0 + point.mass 3 / point.weight 3
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 + point.mass 4 / point.weight 4
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2],
            ![point.mass 1, point.mass 2,
              -(point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{1,3,5}` chart gap (triangle `acd`), entry by entry. -/
theorem kFourGap_triangleOneThreeFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {1, 3, 5}
      = Matrix.of
          ![![point.mass 1 / point.weight 1 + point.mass 3 / point.weight 3
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0,
              -(point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2,
              point.mass 1 / point.weight 1 + point.mass 5 / point.weight 5
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{2,4,5}` chart gap (triangle `bcd`), entry by entry. -/
theorem kFourGap_triangleTwoFourFive_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {2, 4, 5}
      = Matrix.of
          ![![-(point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0, point.mass 1],
            ![point.mass 0,
              point.mass 2 / point.weight 2 + point.mass 4 / point.weight 4
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 2 / point.weight 2 + point.mass 5 / point.weight 5
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-! ## The dependent triples are never weakly dominating

At every chart point each triangle gap has a strictly negative value at its
fixed rational plane normal, so it is never positive semidefinite: on the
K4 chart every weak triple is a spanning tree. -/

/-- The `{0,1,2}` gap is never positive semidefinite: the normal `(1,1,1)`
gives value `-(m_3 + m_4 + m_5) < 0`. -/
theorem kFourGap_triangleZeroOneTwo_not_posSemidef
    (point : DirectionChartPoint 6) :
    ¬ (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 2}).PosSemidef := by
  intro hpsd
  rw [kFourGap_triangleZeroOneTwo_eq] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 1, 1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  nlinarith [point.mass_pos 3, point.mass_pos 4, point.mass_pos 5, hvalue]

/-- The `{0,3,4}` gap is never positive semidefinite: the normal `(0,0,1)`
gives value `-(m_1 + m_2 + m_5) < 0`. -/
theorem kFourGap_triangleZeroThreeFour_not_posSemidef
    (point : DirectionChartPoint 6) :
    ¬ (directionChartGap kFourDirection point.mass point.weight
      {0, 3, 4}).PosSemidef := by
  intro hpsd
  rw [kFourGap_triangleZeroThreeFour_eq] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 0, 1]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  nlinarith [point.mass_pos 1, point.mass_pos 2, point.mass_pos 5, hvalue]

/-- The `{1,3,5}` gap is never positive semidefinite: the normal `(0,1,0)`
gives value `-(m_0 + m_2 + m_4) < 0`. -/
theorem kFourGap_triangleOneThreeFive_not_posSemidef
    (point : DirectionChartPoint 6) :
    ¬ (directionChartGap kFourDirection point.mass point.weight
      {1, 3, 5}).PosSemidef := by
  intro hpsd
  rw [kFourGap_triangleOneThreeFive_eq] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![0, 1, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  nlinarith [point.mass_pos 0, point.mass_pos 2, point.mass_pos 4, hvalue]

/-- The `{2,4,5}` gap is never positive semidefinite: the normal `(1,0,0)`
gives value `-(m_0 + m_1 + m_3) < 0`. -/
theorem kFourGap_triangleTwoFourFive_not_posSemidef
    (point : DirectionChartPoint 6) :
    ¬ (directionChartGap kFourDirection point.mass point.weight
      {2, 4, 5}).PosSemidef := by
  intro hpsd
  rw [kFourGap_triangleTwoFourFive_eq] at hpsd
  have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 ![1, 0, 0]
  rw [star_trivial] at hvalue
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
  nlinarith [point.mass_pos 0, point.mass_pos 1, point.mass_pos 3, hvalue]

/-- **No dependent triple ever weakly dominates.**  On the K4 chart the weak
antecedent always delivers a spanning tree. -/
theorem kFourDependentTriple_gap_not_posSemidef (point : DirectionChartPoint 6) :
    ∀ triple ∈ kFourDependentTripleList,
      ¬ (directionChartGap kFourDirection point.mass point.weight
        triple).PosSemidef := by
  intro triple hmem
  fin_cases hmem
  · exact kFourGap_triangleZeroOneTwo_not_posSemidef point
  · exact kFourGap_triangleZeroThreeFour_not_posSemidef point
  · exact kFourGap_triangleOneThreeFive_not_posSemidef point
  · exact kFourGap_triangleTwoFourFive_not_posSemidef point

/-! ## The contraction layer at edge 5

Contracting the edge `5` (`u_5 = e3`) restricts potentials to the plane
`x_2 = 0`: the restriction of a through-edge tree gap is its leading `2x2`
block, and the five remaining labels fall into the parallel classes
`A = {1,3}` (form `z_0^2`), `B = {2,4}` (form `z_1^2`), `C = {0}` (form
`(z_0 - z_1)^2`) of `K4/5` — exactly the normalized rank-two-slack frame. -/

/-- The leading `2x2` block of a `3x3` matrix: the restriction of its form
to the plane `x_2 = 0`. -/
def leadingTwoBlock (mat : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![mat 0 0, mat 0 1; mat 1 0, mat 1 1]

/-- Restriction = contraction for the `{1,2,5}` lift. -/
theorem kFourContraction_treeOneTwoFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {1, 2, 5})
      = !![point.mass 1 / point.weight 1 - (point.mass 1 + point.mass 3)
             - point.mass 0,
           point.mass 0;
           point.mass 0,
           point.mass 2 / point.weight 2 - (point.mass 2 + point.mass 4)
             - point.mass 0] := by
  rw [kFourGap_treeOneTwoFive_eq]
  simp [leadingTwoBlock]

/-- Restriction = contraction for the `{3,4,5}` lift. -/
theorem kFourContraction_treeThreeFourFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {3, 4, 5})
      = !![point.mass 3 / point.weight 3 - (point.mass 1 + point.mass 3)
             - point.mass 0,
           point.mass 0;
           point.mass 0,
           point.mass 4 / point.weight 4 - (point.mass 2 + point.mass 4)
             - point.mass 0] := by
  rw [kFourGap_treeThreeFourFive_eq]
  simp [leadingTwoBlock]

/-- Restriction = contraction for the `{1,4,5}` lift. -/
theorem kFourContraction_treeOneFourFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {1, 4, 5})
      = !![point.mass 1 / point.weight 1 - (point.mass 1 + point.mass 3)
             - point.mass 0,
           point.mass 0;
           point.mass 0,
           point.mass 4 / point.weight 4 - (point.mass 2 + point.mass 4)
             - point.mass 0] := by
  rw [kFourGap_treeOneFourFive_eq]
  simp [leadingTwoBlock]

/-- Restriction = contraction for the `{2,3,5}` lift. -/
theorem kFourContraction_treeTwoThreeFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {2, 3, 5})
      = !![point.mass 3 / point.weight 3 - (point.mass 1 + point.mass 3)
             - point.mass 0,
           point.mass 0;
           point.mass 0,
           point.mass 2 / point.weight 2 - (point.mass 2 + point.mass 4)
             - point.mass 0] := by
  rw [kFourGap_treeTwoThreeFive_eq]
  simp [leadingTwoBlock]

/-- Restriction = contraction for the `{0,1,5}` lift. -/
theorem kFourContraction_treeZeroOneFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {0, 1, 5})
      = !![point.mass 1 / point.weight 1 + point.mass 0 / point.weight 0
             - (point.mass 1 + point.mass 3) - point.mass 0,
           point.mass 0 - point.mass 0 / point.weight 0;
           point.mass 0 - point.mass 0 / point.weight 0,
           point.mass 0 / point.weight 0 - (point.mass 2 + point.mass 4)
             - point.mass 0] := by
  rw [kFourGap_treeZeroOneFive_eq]
  simp [leadingTwoBlock]

/-- Restriction = contraction for the `{0,2,5}` lift. -/
theorem kFourContraction_treeZeroTwoFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {0, 2, 5})
      = !![point.mass 0 / point.weight 0 - (point.mass 1 + point.mass 3)
             - point.mass 0,
           point.mass 0 - point.mass 0 / point.weight 0;
           point.mass 0 - point.mass 0 / point.weight 0,
           point.mass 2 / point.weight 2 + point.mass 0 / point.weight 0
             - (point.mass 2 + point.mass 4) - point.mass 0] := by
  rw [kFourGap_treeZeroTwoFive_eq]
  simp [leadingTwoBlock]

/-- Restriction = contraction for the `{0,3,5}` lift. -/
theorem kFourContraction_treeZeroThreeFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {0, 3, 5})
      = !![point.mass 3 / point.weight 3 + point.mass 0 / point.weight 0
             - (point.mass 1 + point.mass 3) - point.mass 0,
           point.mass 0 - point.mass 0 / point.weight 0;
           point.mass 0 - point.mass 0 / point.weight 0,
           point.mass 0 / point.weight 0 - (point.mass 2 + point.mass 4)
             - point.mass 0] := by
  rw [kFourGap_treeZeroThreeFive_eq]
  simp [leadingTwoBlock]

/-- Restriction = contraction for the `{0,4,5}` lift. -/
theorem kFourContraction_treeZeroFourFive_eq (point : DirectionChartPoint 6) :
    leadingTwoBlock (directionChartGap kFourDirection point.mass point.weight
        {0, 4, 5})
      = !![point.mass 0 / point.weight 0 - (point.mass 1 + point.mass 3)
             - point.mass 0,
           point.mass 0 - point.mass 0 / point.weight 0;
           point.mass 0 - point.mass 0 / point.weight 0,
           point.mass 4 / point.weight 4 + point.mass 0 / point.weight 0
             - (point.mass 2 + point.mass 4) - point.mass 0] := by
  rw [kFourGap_treeZeroFourFive_eq]
  simp [leadingTwoBlock]

/-- **The contracted class slack bound.**  Aggregating each doubled class at
its max-conductance representative keeps the slack below the off-edge
budget: `(m_1+m_3)/max(y_1,y_3) + (m_2+m_4)/max(y_2,y_4) + m_0/y_0
<= 1 - w_5`. -/
theorem kFourContractionSlack (point : DirectionChartPoint 6) :
    (point.mass 1 + point.mass 3)
        / max (point.mass 1 / point.weight 1) (point.mass 3 / point.weight 3)
      + (point.mass 2 + point.mass 4)
        / max (point.mass 2 / point.weight 2) (point.mass 4 / point.weight 4)
      + point.mass 0 / (point.mass 0 / point.weight 0)
      ≤ 1 - point.weight 5 := by
  have hcondOne : 0 < point.mass 1 / point.weight 1 :=
    div_pos (point.mass_pos 1) (point.weight_pos 1)
  have hcondTwo : 0 < point.mass 2 / point.weight 2 :=
    div_pos (point.mass_pos 2) (point.weight_pos 2)
  have hcondThree : 0 < point.mass 3 / point.weight 3 :=
    div_pos (point.mass_pos 3) (point.weight_pos 3)
  have hcondFour : 0 < point.mass 4 / point.weight 4 :=
    div_pos (point.mass_pos 4) (point.weight_pos 4)
  have hclassA : (point.mass 1 + point.mass 3)
      / max (point.mass 1 / point.weight 1) (point.mass 3 / point.weight 3)
      ≤ point.weight 1 + point.weight 3 := by
    rw [add_div]
    have hboundOne : point.mass 1
        / max (point.mass 1 / point.weight 1) (point.mass 3 / point.weight 3)
        ≤ point.mass 1 / (point.mass 1 / point.weight 1) :=
      div_le_div_of_nonneg_left (point.mass_pos 1).le hcondOne (le_max_left _ _)
    have hboundThree : point.mass 3
        / max (point.mass 1 / point.weight 1) (point.mass 3 / point.weight 3)
        ≤ point.mass 3 / (point.mass 3 / point.weight 3) :=
      div_le_div_of_nonneg_left (point.mass_pos 3).le hcondThree (le_max_right _ _)
    rw [massDivConductance_eq_weight point 1] at hboundOne
    rw [massDivConductance_eq_weight point 3] at hboundThree
    linarith
  have hclassB : (point.mass 2 + point.mass 4)
      / max (point.mass 2 / point.weight 2) (point.mass 4 / point.weight 4)
      ≤ point.weight 2 + point.weight 4 := by
    rw [add_div]
    have hboundTwo : point.mass 2
        / max (point.mass 2 / point.weight 2) (point.mass 4 / point.weight 4)
        ≤ point.mass 2 / (point.mass 2 / point.weight 2) :=
      div_le_div_of_nonneg_left (point.mass_pos 2).le hcondTwo (le_max_left _ _)
    have hboundFour : point.mass 4
        / max (point.mass 2 / point.weight 2) (point.mass 4 / point.weight 4)
        ≤ point.mass 4 / (point.mass 4 / point.weight 4) :=
      div_le_div_of_nonneg_left (point.mass_pos 4).le hcondFour (le_max_right _ _)
    rw [massDivConductance_eq_weight point 2] at hboundTwo
    rw [massDivConductance_eq_weight point 4] at hboundFour
    linarith
  have hclassC := massDivConductance_eq_weight point 0
  have hsumSix : point.weight 0 + point.weight 1 + point.weight 2
      + point.weight 3 + point.weight 4 + point.weight 5 = 1 := by
    have hsum := point.weight_sum_one
    rwa [Fin.sum_univ_six] at hsum
  linarith

/-- **The contraction always has a winner.**  At EVERY chart point (no
edge-maximality needed) some spanning tree through edge `5` has positive
definite contracted block: the class slack bound feeds the rank-two slack
lemma, and each disjunct is one of the eight restriction identities at the
max-conductance representative of the doubled classes. -/
theorem kFourContractionHasWinner (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourTreesThroughEdgeFive,
      (leadingTwoBlock (directionChartGap kFourDirection point.mass
        point.weight tree)).PosDef := by
  have hslackLt : (point.mass 1 + point.mass 3)
        / max (point.mass 1 / point.weight 1) (point.mass 3 / point.weight 3)
      + (point.mass 2 + point.mass 4)
        / max (point.mass 2 / point.weight 2) (point.mass 4 / point.weight 4)
      + point.mass 0 / (point.mass 0 / point.weight 0) < 1 :=
    lt_of_le_of_lt (kFourContractionSlack point)
      (by linarith [point.weight_pos 5])
  have hmaxAPos : 0 < max (point.mass 1 / point.weight 1)
      (point.mass 3 / point.weight 3) :=
    lt_of_lt_of_le (div_pos (point.mass_pos 1) (point.weight_pos 1))
      (le_max_left _ _)
  have hmaxBPos : 0 < max (point.mass 2 / point.weight 2)
      (point.mass 4 / point.weight 4) :=
    lt_of_lt_of_le (div_pos (point.mass_pos 2) (point.weight_pos 2))
      (le_max_left _ _)
  have hcondCPos : 0 < point.mass 0 / point.weight 0 :=
    div_pos (point.mass_pos 0) (point.weight_pos 0)
  have hwinner := rankTwoSlackLemma
    (max (point.mass 1 / point.weight 1) (point.mass 3 / point.weight 3))
    (max (point.mass 2 / point.weight 2) (point.mass 4 / point.weight 4))
    (point.mass 0 / point.weight 0)
    (point.mass 1 + point.mass 3) (point.mass 2 + point.mass 4) (point.mass 0)
    hmaxAPos hmaxBPos hcondCPos
    (by linarith [point.mass_pos 1, point.mass_pos 3])
    (by linarith [point.mass_pos 2, point.mass_pos 4])
    (point.mass_pos 0) hslackLt
  rcases hwinner with hpairAB | hpairAC | hpairBC
  · rcases max_choice (point.mass 1 / point.weight 1)
        (point.mass 3 / point.weight 3) with hmaxA | hmaxA <;>
      rcases max_choice (point.mass 2 / point.weight 2)
        (point.mass 4 / point.weight 4) with hmaxB | hmaxB <;>
      rw [hmaxA, hmaxB] at hpairAB
    · exact ⟨{1, 2, 5}, by decide,
        (kFourContraction_treeOneTwoFive_eq point) ▸ hpairAB⟩
    · exact ⟨{1, 4, 5}, by decide,
        (kFourContraction_treeOneFourFive_eq point) ▸ hpairAB⟩
    · exact ⟨{2, 3, 5}, by decide,
        (kFourContraction_treeTwoThreeFive_eq point) ▸ hpairAB⟩
    · exact ⟨{3, 4, 5}, by decide,
        (kFourContraction_treeThreeFourFive_eq point) ▸ hpairAB⟩
  · rcases max_choice (point.mass 1 / point.weight 1)
        (point.mass 3 / point.weight 3) with hmaxA | hmaxA <;>
      rw [hmaxA] at hpairAC
    · exact ⟨{0, 1, 5}, by decide,
        (kFourContraction_treeZeroOneFive_eq point) ▸ hpairAC⟩
    · exact ⟨{0, 3, 5}, by decide,
        (kFourContraction_treeZeroThreeFive_eq point) ▸ hpairAC⟩
  · rcases max_choice (point.mass 2 / point.weight 2)
        (point.mass 4 / point.weight 4) with hmaxB | hmaxB <;>
      rw [hmaxB] at hpairBC
    · exact ⟨{0, 2, 5}, by decide,
        (kFourContraction_treeZeroTwoFive_eq point) ▸ hpairBC⟩
    · exact ⟨{0, 4, 5}, by decide,
        (kFourContraction_treeZeroFourFive_eq point) ▸ hpairBC⟩

/-! ## The endgame vocabulary and the consumption bridge

The two named endgame claims and the bridge down to the chart obligation.
Both claims are REFUTED at `maxEdgeRefuterPoint` below; the bridge is
retained as the shape any repaired (mass-reading) selection Prop must
feed. -/

/-- `edge` attains the maximum conductance `mass/weight` at the chart point. -/
def IsMaxConductanceEdge (point : DirectionChartPoint 6) (edge : Fin 6) : Prop :=
  ∀ label, point.mass label / point.weight label
    ≤ point.mass edge / point.weight edge

/-- **E1, the det pigeonhole (named endgame claim) — FALSE.**  At a
max-conductance edge some spanning tree THROUGH the edge has positive gap
determinant.  Refuted below (`kFourMaxEdgeDetPigeonhole_refuted`) at
`maxEdgeRefuterPoint`, where every through-tree det is negative. -/
def KFourMaxEdgeDetPigeonhole : Prop :=
  ∀ (point : DirectionChartPoint 6) (edge : Fin 6),
    IsMaxConductanceEdge point edge →
      ∃ tree ∈ kFourSpanningTreeList, edge ∈ tree ∧
        0 < (directionChartGap kFourDirection point.mass point.weight tree).det

/-- **The max-edge host statement (E1 and E2 combined) — FALSE.**  At a
max-conductance edge some spanning tree through the edge is strictly
dominating.  Refuted below (`kFourMaxEdgeHostsStrictTree_refuted`) at
`maxEdgeRefuterPoint`, a strict-argmax point with dependent-triangle mass
concentration that no earlier scan regime covered. -/
def KFourMaxEdgeHostsStrictTree : Prop :=
  ∀ (point : DirectionChartPoint 6) (edge : Fin 6),
    IsMaxConductanceEdge point edge →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧ edge ∈ selected ∧
        (directionChartGap kFourDirection point.mass point.weight
          selected).PosDef

/-- Every chart point has a max-conductance edge (finiteness). -/
theorem exists_maxConductanceEdge (point : DirectionChartPoint 6) :
    ∃ edge, IsMaxConductanceEdge point edge := by
  obtain ⟨edge, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 6))
    (fun label => point.mass label / point.weight label) ⟨0, Finset.mem_univ 0⟩
  exact ⟨edge, fun label => hmax label (Finset.mem_univ label)⟩

/-- **The consumption bridge.**  A host-shaped selection statement closes
the chart obligation: every weak triple forces a strict one because a strict
one exists outright.  (On the OPEN chart this loses nothing: the guarded and
strict forms stand or fall together at the fixed spanning direction tuple;
the historical strict-form refutation lives at a degenerate DIRECTION, not
at any chart point.)  The hypothesis as stated is refuted below — the bridge
survives as the shape a repaired, mass-reading selection Prop must feed. -/
theorem directionChartIsTieFree_kFour_of_maxEdgeHosts
    (hhost : KFourMaxEdgeHostsStrictTree) :
    DirectionChartIsTieFree kFourDirection := by
  intro point _hweak
  obtain ⟨edge, hmax⟩ := exists_maxConductanceEdge point
  obtain ⟨selected, hcard, -, hposDef⟩ := hhost point edge hmax
  exact ⟨selected, hcard, hposDef⟩

/-! ## The refutation: the max-conductance edge does NOT always host

Kernel refutation of the two endgame Props above.  Witness
`maxEdgeRefuterPoint`: edge `3` is the strict argmax-conductance edge, yet
every card-3 selection through it fails positive definiteness and all eight
through-trees have negative determinant, because the dominant masses sit on
edges `0` and `4` and `{0, 3, 4}` is a dependent triangle.  The chart
obligation is intact at the witness: `{0, 1, 4}` dominates strictly. -/

/-- Masses of the refuting chart point: dominant masses on edges `0`, `4`. -/
noncomputable def maxEdgeRefuterMass : Fin 6 → ℝ
  | 0 => 36
  | 1 => 1/60
  | 2 => 1/60
  | 3 => 10
  | 4 => 20
  | 5 => 1/60

/-- Weights of the refuting chart point (positive, summing to one). -/
noncomputable def maxEdgeRefuterWeight : Fin 6 → ℝ
  | 0 => 3/5
  | 1 => 1/60
  | 2 => 1/60
  | 3 => 1/10
  | 4 => 1/4
  | 5 => 1/60

@[simp] theorem maxEdgeRefuterMass_zero : maxEdgeRefuterMass 0 = 36 := rfl
@[simp] theorem maxEdgeRefuterMass_one : maxEdgeRefuterMass 1 = 1/60 := rfl
@[simp] theorem maxEdgeRefuterMass_two : maxEdgeRefuterMass 2 = 1/60 := rfl
@[simp] theorem maxEdgeRefuterMass_three : maxEdgeRefuterMass 3 = 10 := rfl
@[simp] theorem maxEdgeRefuterMass_four : maxEdgeRefuterMass 4 = 20 := rfl
@[simp] theorem maxEdgeRefuterMass_five : maxEdgeRefuterMass 5 = 1/60 := rfl

@[simp] theorem maxEdgeRefuterWeight_zero : maxEdgeRefuterWeight 0 = 3/5 := rfl
@[simp] theorem maxEdgeRefuterWeight_one : maxEdgeRefuterWeight 1 = 1/60 := rfl
@[simp] theorem maxEdgeRefuterWeight_two : maxEdgeRefuterWeight 2 = 1/60 := rfl
@[simp] theorem maxEdgeRefuterWeight_three : maxEdgeRefuterWeight 3 = 1/10 := rfl
@[simp] theorem maxEdgeRefuterWeight_four : maxEdgeRefuterWeight 4 = 1/4 := rfl
@[simp] theorem maxEdgeRefuterWeight_five : maxEdgeRefuterWeight 5 = 1/60 := rfl

/-- The refuting chart point: conductances `(60, 1, 1, 100, 80, 1)`, so edge
`3` is the strict argmax; masses concentrate on the triangle `{0, 3, 4}`. -/
noncomputable def maxEdgeRefuterPoint : DirectionChartPoint 6 where
  mass := maxEdgeRefuterMass
  weight := maxEdgeRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [maxEdgeRefuterMass]
  weight_pos := by
    intro label; fin_cases label <;> norm_num [maxEdgeRefuterWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num

@[simp] theorem maxEdgeRefuterPoint_mass_eq :
    maxEdgeRefuterPoint.mass = maxEdgeRefuterMass := rfl

@[simp] theorem maxEdgeRefuterPoint_weight_eq :
    maxEdgeRefuterPoint.weight = maxEdgeRefuterWeight := rfl

/-- Edge `3` is the (strict) argmax-conductance edge at the witness. -/
theorem maxEdgeRefuter_isMaxConductanceEdge_three :
    IsMaxConductanceEdge maxEdgeRefuterPoint 3 := by
  intro label
  fin_cases label <;>
    norm_num [maxEdgeRefuterMass, maxEdgeRefuterWeight]

/-! ## Entrywise gap identities for the ten selections through edge `3`

Pattern: `tetrahedron_gap_eq` (KFourChartSample.lean). -/

theorem maxEdgeRefuter_gap_zeroOneThree_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 1, 3}
      = !![6899/60, -24, -59/60; -24, 239/60, 1/60; -59/60, 1/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_zeroTwoThree_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 2, 3}
      = !![6839/60, -24, 1/60; -24, 299/60, -59/60; 1/60, -59/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_zeroThreeFour_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 3, 4}
      = !![6839/60, -24, 1/60; -24, 5039/60, 1/60; 1/60, 1/60, -1/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_zeroThreeFive_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 3, 5}
      = !![6839/60, -24, 1/60; -24, 239/60, 1/60; 1/60, 1/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_oneTwoThree_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {1, 2, 3}
      = !![3299/60, 36, -59/60; 36, -3301/60, -59/60;
           -59/60, -59/60, 39/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_oneThreeFour_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {1, 3, 4}
      = !![3299/60, 36, -59/60; 36, 1439/60, 1/60; -59/60, 1/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_oneThreeFive_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {1, 3, 5}
      = !![3299/60, 36, -59/60; 36, -3361/60, 1/60; -59/60, 1/60, 39/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_twoThreeFour_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {2, 3, 4}
      = !![3239/60, 36, 1/60; 36, 1499/60, -59/60; 1/60, -59/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_twoThreeFive_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {2, 3, 5}
      = !![3239/60, 36, 1/60; 36, -3301/60, -59/60; 1/60, -59/60, 39/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_threeFourFive_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {3, 4, 5}
      = !![3239/60, 36, 1/60; 36, 1439/60, 1/60; 1/60, 1/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

/-! ## No selection through edge `3` is positive definite

Each refutation evaluates the quadratic form at an explicit rational
certificate vector; `Matrix.posDef_iff_dotProduct_mulVec` (the anchor API)
turns positive definiteness into pointwise positivity. -/

/-- Shared shape: an explicit `3 x 3` matrix with a vector of nonpositive
Rayleigh value is not positive definite. -/
theorem not_posDef_of_dotProduct_mulVec_nonpos
    (candidate : Matrix (Fin 3) (Fin 3) ℝ) (probe : Fin 3 → ℝ)
    (hprobe : probe ≠ 0)
    (hvalue : probe ⬝ᵥ (candidate *ᵥ probe) ≤ 0) :
    ¬ candidate.PosDef := by
  intro hpd
  obtain ⟨-, hquad⟩ := Matrix.posDef_iff_dotProduct_mulVec.mp hpd
  have hpos := hquad hprobe
  rw [star_trivial] at hpos
  linarith

theorem maxEdgeRefuter_gap_zeroOneThree_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 1, 3}).PosDef := by
  rw [maxEdgeRefuter_gap_zeroOneThree_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-1, -6, -6] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_zeroTwoThree_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 2, 3}).PosDef := by
  rw [maxEdgeRefuter_gap_zeroTwoThree_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-1, -6, -6] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_zeroThreeFour_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 3, 4}).PosDef := by
  rw [maxEdgeRefuter_gap_zeroThreeFour_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![1, 0, -60] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_zeroThreeFive_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 3, 5}).PosDef := by
  rw [maxEdgeRefuter_gap_zeroThreeFive_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-1, -6, -5] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_oneTwoThree_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {1, 2, 3}).PosDef := by
  rw [maxEdgeRefuter_gap_oneTwoThree_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-6, 4, -6] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_oneThreeFour_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {1, 3, 4}).PosDef := by
  rw [maxEdgeRefuter_gap_oneThreeFour_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-4, 6, -5] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_oneThreeFive_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {1, 3, 5}).PosDef := by
  rw [maxEdgeRefuter_gap_oneThreeFive_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-6, 4, -6] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_twoThreeFour_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {2, 3, 4}).PosDef := by
  rw [maxEdgeRefuter_gap_twoThreeFour_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-4, 6, 5] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_twoThreeFive_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {2, 3, 5}).PosDef := by
  rw [maxEdgeRefuter_gap_twoThreeFive_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-6, 4, -6] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem maxEdgeRefuter_gap_threeFourFive_not_posDef :
    ¬ (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {3, 4, 5}).PosDef := by
  rw [maxEdgeRefuter_gap_threeFourFive_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-4, 6, 0] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

/-! ## The eight through-trees all have negative gap determinant -/

theorem maxEdgeRefuter_gap_zeroOneThree_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {0, 1, 3}).det < 0 := by
  rw [maxEdgeRefuter_gap_zeroOneThree_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_zeroTwoThree_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {0, 2, 3}).det < 0 := by
  rw [maxEdgeRefuter_gap_zeroTwoThree_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_zeroThreeFive_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {0, 3, 5}).det < 0 := by
  rw [maxEdgeRefuter_gap_zeroThreeFive_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_oneTwoThree_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {1, 2, 3}).det < 0 := by
  rw [maxEdgeRefuter_gap_oneTwoThree_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_oneThreeFour_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {1, 3, 4}).det < 0 := by
  rw [maxEdgeRefuter_gap_oneThreeFour_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_oneThreeFive_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {1, 3, 5}).det < 0 := by
  rw [maxEdgeRefuter_gap_oneThreeFive_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_twoThreeFour_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {2, 3, 4}).det < 0 := by
  rw [maxEdgeRefuter_gap_twoThreeFour_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_twoThreeFive_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {2, 3, 5}).det < 0 := by
  rw [maxEdgeRefuter_gap_twoThreeFive_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem maxEdgeRefuter_gap_threeFourFive_det_neg :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {3, 4, 5}).det < 0 := by
  rw [maxEdgeRefuter_gap_threeFourFive_eq]
  norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

/-! ## The refutations -/

/-- Every card-3 selection containing label `3` is one of ten explicit
finsets — a kernel `decide` over the twenty card-3 subsets of `Fin 6`. -/
theorem finsetThroughThree_enumeration :
    ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (3 : Fin 6) ∈ selected →
      selected = {0, 1, 3} ∨ selected = {0, 2, 3} ∨ selected = {0, 3, 4} ∨
      selected = {0, 3, 5} ∨ selected = {1, 2, 3} ∨ selected = {1, 3, 4} ∨
      selected = {1, 3, 5} ∨ selected = {2, 3, 4} ∨ selected = {2, 3, 5} ∨
      selected = {3, 4, 5} := by decide

/-- **The max-edge host statement is FALSE.**  At `maxEdgeRefuterPoint` the
strict argmax-conductance edge `3` hosts no strictly dominating selection:
the two dominant masses sit on edges `0` and `4`, and `{0, 3, 4}` is a
dependent triangle. -/
theorem kFourMaxEdgeHostsStrictTree_refuted :
    ¬ KFourMaxEdgeHostsStrictTree := by
  intro hhost
  obtain ⟨selected, hcard, hmem, hpd⟩ :=
    hhost maxEdgeRefuterPoint 3 maxEdgeRefuter_isMaxConductanceEdge_three
  have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  rcases finsetThroughThree_enumeration selected hpow hmem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact maxEdgeRefuter_gap_zeroOneThree_not_posDef hpd
  · exact maxEdgeRefuter_gap_zeroTwoThree_not_posDef hpd
  · exact maxEdgeRefuter_gap_zeroThreeFour_not_posDef hpd
  · exact maxEdgeRefuter_gap_zeroThreeFive_not_posDef hpd
  · exact maxEdgeRefuter_gap_oneTwoThree_not_posDef hpd
  · exact maxEdgeRefuter_gap_oneThreeFour_not_posDef hpd
  · exact maxEdgeRefuter_gap_oneThreeFive_not_posDef hpd
  · exact maxEdgeRefuter_gap_twoThreeFour_not_posDef hpd
  · exact maxEdgeRefuter_gap_twoThreeFive_not_posDef hpd
  · exact maxEdgeRefuter_gap_threeFourFive_not_posDef hpd

/-- **E1's per-edge form is FALSE.**  At the same witness no spanning tree
through the argmax edge has positive gap determinant. -/
theorem kFourMaxEdgeDetPigeonhole_refuted :
    ¬ KFourMaxEdgeDetPigeonhole := by
  intro hpigeon
  obtain ⟨tree, htreeMem, hedgeMem, hdetPos⟩ :=
    hpigeon maxEdgeRefuterPoint 3 maxEdgeRefuter_isMaxConductanceEdge_three
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil,
    or_false] at htreeMem
  rcases htreeMem with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · linarith [maxEdgeRefuter_gap_zeroOneThree_det_neg]
  · exact absurd hedgeMem (by decide)
  · exact absurd hedgeMem (by decide)
  · linarith [maxEdgeRefuter_gap_threeFourFive_det_neg]
  · exact absurd hedgeMem (by decide)
  · exact absurd hedgeMem (by decide)
  · linarith [maxEdgeRefuter_gap_zeroTwoThree_det_neg]
  · exact absurd hedgeMem (by decide)
  · linarith [maxEdgeRefuter_gap_zeroThreeFive_det_neg]
  · exact absurd hedgeMem (by decide)
  · linarith [maxEdgeRefuter_gap_oneTwoThree_det_neg]
  · exact absurd hedgeMem (by decide)
  · linarith [maxEdgeRefuter_gap_oneThreeFour_det_neg]
  · exact absurd hedgeMem (by decide)
  · linarith [maxEdgeRefuter_gap_twoThreeFour_det_neg]
  · linarith [maxEdgeRefuter_gap_twoThreeFive_det_neg]

/-! ## The chart obligation itself is INTACT at the witness

The triple `{0, 1, 4}` (containing both dominant-mass edges) is strictly
dominating; positive semidefiniteness comes from the exact `L D L^T`
squares, definiteness from the nonzero determinant. -/

theorem maxEdgeRefuter_gap_zeroOneFour_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 1, 4}
      = !![899/60, -24, -59/60; -24, 5039/60, 1/60; -59/60, 1/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem maxEdgeRefuter_gap_zeroOneFour_posDef :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {0, 1, 4}).PosDef := by
  rw [maxEdgeRefuter_gap_zeroOneFour_eq]
  have hpsd : (!![899/60, -24, -59/60; -24, 5039/60, 1/60;
      -59/60, 1/60, 19/20] : Matrix (Fin 3) (Fin 3) ℝ).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
    · refine isHermitian_of_transpose_eq ?_
      ext rowIndex colIndex
      fin_cases rowIndex <;> fin_cases colIndex <;>
        simp [Matrix.transpose_apply]
    · rw [star_trivial]
      have hform : probe ⬝ᵥ ((!![899/60, -24, -59/60; -24, 5039/60, 1/60;
            -59/60, 1/60, 19/20] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probe)
          = 899/60 * probe 0 ^ 2 - 48 * probe 0 * probe 1
            - 59/30 * probe 0 * probe 2 + 5039/60 * probe 1 ^ 2
            + 1/30 * probe 1 * probe 2 + 19/20 * probe 2 ^ 2 := by
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
        ring
      rw [hform]
      nlinarith [sq_nonneg (899 * probe 0 - 1440 * probe 1 - 59 * probe 2),
        sq_nonneg (2456461 * probe 1 - 84061 * probe 2), sq_nonneg (probe 2)]
  have hdet : (!![899/60, -24, -59/60; -24, 5039/60, 1/60;
      -59/60, 1/60, 19/20] : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
    norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  exact hpsd.posDef_iff_det_ne_zero.mpr hdet

/-- The strict form holds at the witness: `{0, 1, 4}` dominates strictly, so
the refutation above kills ONLY the max-edge selection mechanism, not the
chart obligation. -/
theorem maxEdgeRefuterPoint_hasStrictTriple :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight selected).PosDef :=
  ⟨{0, 1, 4}, by decide, maxEdgeRefuter_gap_zeroOneFour_posDef⟩

end Gtz
