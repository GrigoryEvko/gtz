import Gtz.Design.RigidityBridge
import Gtz.Design.KFourChartSample

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


/-! ## The repaired-selection adjudication: every scalar-argmax selection dies

After the max-conductance refutation above, the repair campaign adjudicated
every remaining single-functional selection at exact rationals (four
mandatory points, seven named witnesses, 4340 fresh points across eleven
adversarial regimes including both refuter families, the sliver family, and
perturbation shells; lane record `/tmp/gtz-chain/wfk3/k8-repair/`):

* argmax-MASS edge hosting — FALSE (70 exact failures, multiscale regime);
* argmax-ALPHA edge hosting — FALSE, refuted in kernel below at the ALREADY
  LANDED `maxEdgeRefuterPoint` (the alpha argmax there is again edge `3`);
* dominant-mass-PAIR hosting — FALSE, refuted in kernel below at the dual
  witness `heavyPairRefuterPoint`;
* mass-product-argmax tree (the greedy max-mass basis) — FALSE (592
  failures, generic regime included; the kernel witness below kills it too,
  since its argmax trees all contain the dominant pair `{0, 4}`);
* alpha-product-argmax tree — FALSE (dies at five of the eight named
  witnesses, `P1` included);
* GLOBAL det-argmax tree PD when its det is positive — FALSE (371 exact
  failures; already at `maxEdgeRefuterPoint` the global det-argmax tree is
  `{1, 2, 5}` with positive determinant and indefinite gap).

The two kernel witnesses are DUAL: `maxEdgeRefuterPoint` kills every
conductance-side selection (dominant masses on a triangle THROUGH the argmax
edge), and `heavyPairRefuterPoint` — same weights, the triangle-closer mass
`18` pushed past the pair's series threshold
`alpha_0 * alpha_4 / (alpha_0 + alpha_4) = 120/7` — kills every mass-side
selection: once the closer crosses the threshold, EVERY selection keeping
both heavy edges fails on the triangle plane and the winners all keep the
closer instead.  Which side wins is a genuine polynomial threshold in the
triangle data, so no ordering of per-label scalars can decide it: a correct
selection must read the pairwise block tests themselves.

Representative-based winner rules die too: near the tetrahedron the strict
trees are exactly the four STARS, every contracted block of all 48
(edge, pair) candidates is positive definite (the contraction layer is
uninformative there), and picking a star requires a CORRELATED choice of
the two class representatives — per-class rules (max-conductance reps,
max-mass reps, or their disjunction, the argmax-edge lanes' R-TWOREP) are
steered by the perturbation into the anti-correlated mix at every edge
simultaneously (six exact witnesses, e.g. masses
`(124989/500000, 200019/800000, 999991/4000000, 249989/1000000,
500031/2000000, 499959/2000000)` with weights summing to one nearby
`1/6`).  Selection data must be JOINT over the kept pair.

What SURVIVES every exact point ever tested (~30,000 upstream + 4340 +
2900 + 2900 fresh this lane, zero failures): the strict form itself; the
global det pigeonhole (SOME of the sixteen tree gaps has positive
determinant); and — the repaired selection — the six-candidate per-edge
det-argmax host `KFourEdgeDetArgmaxHostsStrictTree` below: at SOME edge
the maximum-determinant spanning tree through that edge is strictly
dominating.  The determinant is a joint polynomial in the pair data, so
this rule is compatible with every impossibility above; it holds at both
kernel witnesses (via edges away from the broken argmax), at every
tetrahedron-shell two-rep killer, and across all regimes.  The Prop
`KFourSomeTreeLiftThreshold` below it is the selection-free scalar residue
either route discharges; both bridges to the chart obligation are
complete. -/

/-- `edge` attains the maximum alpha `mass/weight - mass` at the chart
point.  The alpha-argmax sibling of `IsMaxConductanceEdge`. -/
def IsMaxAlphaEdge (point : DirectionChartPoint 6) (edge : Fin 6) : Prop :=
  ∀ label, point.mass label / point.weight label - point.mass label
    ≤ point.mass edge / point.weight edge - point.mass edge

/-- **The max-alpha host statement — FALSE.**  At an argmax-alpha edge some
card-3 selection through the edge is strictly dominating.  Refuted below at
the landed `maxEdgeRefuterPoint`, whose alpha vector
`(24, 59/60, 59/60, 90, 60, 59/60)` puts the argmax on edge `3` again. -/
def KFourMaxAlphaEdgeHostsStrictTree : Prop :=
  ∀ (point : DirectionChartPoint 6) (edge : Fin 6),
    IsMaxAlphaEdge point edge →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧ edge ∈ selected ∧
        (directionChartGap kFourDirection point.mass point.weight
          selected).PosDef

/-- Edge `3` is also the (strict) argmax-ALPHA edge at the landed witness. -/
theorem maxEdgeRefuter_isMaxAlphaEdge_three :
    IsMaxAlphaEdge maxEdgeRefuterPoint 3 := by
  intro label
  fin_cases label <;>
    norm_num [maxEdgeRefuterMass, maxEdgeRefuterWeight]

/-- **The max-alpha selection is refuted** — by the SAME ten landed not-PD
certificates: at `maxEdgeRefuterPoint` the alpha argmax coincides with the
conductance argmax, and no selection through edge `3` dominates. -/
theorem kFourMaxAlphaEdgeHostsStrictTree_refuted :
    ¬ KFourMaxAlphaEdgeHostsStrictTree := by
  intro hhost
  obtain ⟨selected, hcard, hmem, hpd⟩ :=
    hhost maxEdgeRefuterPoint 3 maxEdgeRefuter_isMaxAlphaEdge_three
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

/-! ## The dual witness: the dominant-mass pair does NOT always host

Same weights as `maxEdgeRefuterPoint`; the mass of the triangle-closer edge
`3` is `18 > 120/7 = alpha_0 alpha_4 / (alpha_0 + alpha_4)`, so on the
triangle plane of `{0, 3, 4}` every selection keeping both dominant-mass
edges `0` and `4` fails.  All six strictly dominating trees at this point
keep the closer `3` instead. -/

/-- Masses of the dual refuting point: the dominant pair `(36, 20)` on edges
`0, 4` and the triangle-closer mass `18` past the series threshold. -/
noncomputable def heavyPairRefuterMass : Fin 6 → ℝ
  | 0 => 36
  | 1 => 1/60
  | 2 => 1/60
  | 3 => 18
  | 4 => 20
  | 5 => 1/60

@[simp] theorem heavyPairRefuterMass_zero : heavyPairRefuterMass 0 = 36 := rfl
@[simp] theorem heavyPairRefuterMass_one : heavyPairRefuterMass 1 = 1/60 := rfl
@[simp] theorem heavyPairRefuterMass_two : heavyPairRefuterMass 2 = 1/60 := rfl
@[simp] theorem heavyPairRefuterMass_three : heavyPairRefuterMass 3 = 18 := rfl
@[simp] theorem heavyPairRefuterMass_four : heavyPairRefuterMass 4 = 20 := rfl
@[simp] theorem heavyPairRefuterMass_five : heavyPairRefuterMass 5 = 1/60 := rfl

/-- The dual refuting chart point: weights verbatim those of
`maxEdgeRefuterPoint`, conductances `(60, 1, 1, 180, 80, 1)`. -/
noncomputable def heavyPairRefuterPoint : DirectionChartPoint 6 where
  mass := heavyPairRefuterMass
  weight := maxEdgeRefuterWeight
  mass_pos := by
    intro label; fin_cases label <;> norm_num [heavyPairRefuterMass]
  weight_pos := by
    intro label; fin_cases label <;> norm_num [maxEdgeRefuterWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num

@[simp] theorem heavyPairRefuterPoint_mass_eq :
    heavyPairRefuterPoint.mass = heavyPairRefuterMass := rfl

@[simp] theorem heavyPairRefuterPoint_weight_eq :
    heavyPairRefuterPoint.weight = maxEdgeRefuterWeight := rfl

/-- The pair `(edgeOne, edgeTwo)` carries the two dominant masses of the
chart point. -/
def IsDominantMassPair (point : DirectionChartPoint 6)
    (edgeOne edgeTwo : Fin 6) : Prop :=
  edgeOne ≠ edgeTwo ∧
    ∀ label, label ≠ edgeOne → label ≠ edgeTwo →
      point.mass label ≤ point.mass edgeOne ∧
        point.mass label ≤ point.mass edgeTwo

/-- **The dominant-mass-pair host statement — FALSE.**  Some card-3
selection containing both dominant-mass edges is strictly dominating.  This
was the surviving pointer of the max-edge refutation ("the witness's PD
triples all contain the dominant-MASS pair"); the dual witness below kills
it, and with it the mass-product-argmax (greedy max-mass basis) selection,
whose argmax trees always contain the dominant pair. -/
def KFourDominantMassPairHostsStrictTree : Prop :=
  ∀ (point : DirectionChartPoint 6) (edgeOne edgeTwo : Fin 6),
    IsDominantMassPair point edgeOne edgeTwo →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        edgeOne ∈ selected ∧ edgeTwo ∈ selected ∧
        (directionChartGap kFourDirection point.mass point.weight
          selected).PosDef

/-- `{0, 4}` is the (strict) dominant-mass pair at the dual witness:
`36 > 20 > 18 > 1/60`. -/
theorem heavyPairRefuter_isDominantMassPair_zeroFour :
    IsDominantMassPair heavyPairRefuterPoint 0 4 := by
  refine ⟨by decide, ?_⟩
  intro label hneZero hneFour
  fin_cases label
  · simp at hneZero
  · constructor <;> norm_num [heavyPairRefuterMass]
  · constructor <;> norm_num [heavyPairRefuterMass]
  · constructor <;> norm_num [heavyPairRefuterMass]
  · simp at hneFour
  · constructor <;> norm_num [heavyPairRefuterMass]

/-- Every card-3 selection containing labels `0` and `4` is one of four
explicit finsets. -/
theorem finsetContainingZeroAndFour_enumeration :
    ∀ selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3,
      (0 : Fin 6) ∈ selected → (4 : Fin 6) ∈ selected →
      selected = {0, 1, 4} ∨ selected = {0, 2, 4} ∨ selected = {0, 3, 4} ∨
      selected = {0, 4, 5} := by decide

/-! ### Entrywise gap identities for the four selections containing `{0, 4}` -/

theorem heavyPairRefuter_gap_zeroOneFour_eq :
    directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 1, 4}
      = !![419/60, -24, -59/60; -24, 5039/60, 1/60; -59/60, 1/60, 19/20] := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem heavyPairRefuter_gap_zeroTwoFour_eq :
    directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 2, 4}
      = !![359/60, -24, 1/60; -24, 5099/60, -59/60; 1/60, -59/60, 19/20] := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem heavyPairRefuter_gap_zeroThreeFour_eq :
    directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 3, 4}
      = !![11159/60, -24, 1/60; -24, 5039/60, 1/60; 1/60, 1/60, -1/20] := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

theorem heavyPairRefuter_gap_zeroFourFive_eq :
    directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 4, 5}
      = !![359/60, -24, 1/60; -24, 5039/60, 1/60; 1/60, 1/60, 19/20] := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

/-! ### None of the four is positive definite -/

theorem heavyPairRefuter_gap_zeroOneFour_not_posDef :
    ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 1, 4}).PosDef := by
  rw [heavyPairRefuter_gap_zeroOneFour_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-3, -1, -1] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem heavyPairRefuter_gap_zeroTwoFour_not_posDef :
    ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 2, 4}).PosDef := by
  rw [heavyPairRefuter_gap_zeroTwoFour_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-3, -1, 0] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem heavyPairRefuter_gap_zeroThreeFour_not_posDef :
    ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 3, 4}).PosDef := by
  rw [heavyPairRefuter_gap_zeroThreeFour_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![0, 0, -1] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 2
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

theorem heavyPairRefuter_gap_zeroFourFive_not_posDef :
    ¬ (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 4, 5}).PosDef := by
  rw [heavyPairRefuter_gap_zeroFourFive_eq]
  refine not_posDef_of_dotProduct_mulVec_nonpos _ ![-3, -1, 0] ?_ ?_
  · intro hzero
    have hentry := congrFun hzero 0
    norm_num at hentry
  · simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    norm_num

/-- **The dominant-mass-pair selection is FALSE.**  At the dual witness no
card-3 selection containing both dominant-mass edges dominates: the
triangle-closer mass has crossed the series threshold of the pair. -/
theorem kFourDominantMassPairHostsStrictTree_refuted :
    ¬ KFourDominantMassPairHostsStrictTree := by
  intro hhost
  obtain ⟨selected, hcard, hmemZero, hmemFour, hpd⟩ :=
    hhost heavyPairRefuterPoint 0 4
      heavyPairRefuter_isDominantMassPair_zeroFour
  have hpow : selected ∈ (Finset.univ : Finset (Fin 6)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
  rcases finsetContainingZeroAndFour_enumeration selected hpow hmemZero
      hmemFour with rfl | rfl | rfl | rfl
  · exact heavyPairRefuter_gap_zeroOneFour_not_posDef hpd
  · exact heavyPairRefuter_gap_zeroTwoFour_not_posDef hpd
  · exact heavyPairRefuter_gap_zeroThreeFour_not_posDef hpd
  · exact heavyPairRefuter_gap_zeroFourFive_not_posDef hpd

/-! ### The chart obligation is INTACT at the dual witness -/

theorem heavyPairRefuter_gap_threeFourFive_eq :
    directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {3, 4, 5}
      = !![7559/60, 36, 1/60; 36, 1439/60, 1/60; 1/60, 1/60, 19/20] := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

/-- The closer-keeping tree `{3, 4, 5}` dominates strictly at the dual
witness (leading minors `7559/60`, `6211801/3600`, `354067979/216000`). -/
theorem heavyPairRefuter_gap_threeFourFive_posDef :
    (directionChartGap kFourDirection heavyPairRefuterPoint.mass
      heavyPairRefuterPoint.weight {3, 4, 5}).PosDef := by
  rw [heavyPairRefuter_gap_threeFourFive_eq]
  refine posDef_of_leadingMinors_fin_three (7559/60) 36 (1/60) (1439/60)
    (1/60) (19/20) (by norm_num) (by norm_num) (by norm_num)

/-- The strict form holds at the dual witness: the refutation kills ONLY the
mass-side selection mechanisms, not the chart obligation. -/
theorem heavyPairRefuterPoint_hasStrictTriple :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight selected).PosDef :=
  ⟨{3, 4, 5}, by decide, heavyPairRefuter_gap_threeFourFive_posDef⟩

/-! ## The selection-free scalar residue and its bridge

With every per-label ordering dead on both sides and every per-class
representative rule dead at the tetrahedron shells, the surviving selection
reads JOINT pair data: the per-edge det-argmax host, and, below it, the
selector-free residue — SOME spanning tree has the three Sylvester minors
of its gap positive.  For the symmetric chart gap the latter is exactly
positive definiteness (via `posDef_of_leadingMinors_fin_two` +
`sylvesterLift` and the landed transpose identity): the pointwise strict
form in scalar clothing, three polynomial inequalities per point, the
exact shape either route (the det-argmax selection or the atlas)
discharges.  Neither statement was ever refuted: ~30,000 exact points
upstream and this lane's fresh adversarial corpus, zero failures. -/

/-- Positive leading minors make the (symmetric) chart gap positive
definite: the entry-level Sylvester wrapper. -/
theorem directionChartGap_posDef_of_leadingMinors {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (selected : Finset (Fin size))
    (hcorner : 0 < directionChartGap direction mass weight selected 0 0)
    (hblock : 0 < directionChartGap direction mass weight selected 0 0
        * directionChartGap direction mass weight selected 1 1
      - directionChartGap direction mass weight selected 0 1 ^ 2)
    (hdet : 0 < (directionChartGap direction mass weight selected).det) :
    (directionChartGap direction mass weight selected).PosDef := by
  set gap := directionChartGap direction mass weight selected with hgapDef
  have hsymm : gapᵀ = gap := directionChartGap_transpose direction mass
    weight selected
  have hOneZero : gap 1 0 = gap 0 1 := by
    have happly := congrFun (congrFun hsymm 0) 1
    simpa [Matrix.transpose_apply] using happly
  have hTwoZero : gap 2 0 = gap 0 2 := by
    have happly := congrFun (congrFun hsymm 0) 2
    simpa [Matrix.transpose_apply] using happly
  have hTwoOne : gap 2 1 = gap 1 2 := by
    have happly := congrFun (congrFun hsymm 1) 2
    simpa [Matrix.transpose_apply] using happly
  have hexplicit : gap = !![gap 0 0, gap 0 1, gap 0 2;
      gap 0 1, gap 1 1, gap 1 2;
      gap 0 2, gap 1 2, gap 2 2] := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [hOneZero, hTwoZero, hTwoOne]
  have hblockPd : (!![gap 0 0, gap 0 1; gap 0 1, gap 1 1]
      : Matrix (Fin 2) (Fin 2) ℝ).PosDef :=
    posDef_of_leadingMinors_fin_two _ _ _ hcorner hblock
  have hdetExplicit : 0 < (!![gap 0 0, gap 0 1, gap 0 2;
      gap 0 1, gap 1 1, gap 1 2;
      gap 0 2, gap 1 2, gap 2 2] : Matrix (Fin 3) (Fin 3) ℝ).det := by
    rw [← hexplicit]
    exact hdet
  have hfullPd := sylvesterLift (gap 0 0) (gap 0 1) (gap 0 2) (gap 1 1)
    (gap 1 2) (gap 2 2) hblockPd hdetExplicit
  rw [hexplicit]
  exact hfullPd

/-- **The repaired selection: the six-candidate per-edge det-argmax host.**
At every chart point some edge's maximum-determinant through-tree is
strictly dominating.  One designated candidate per edge, each a determinant
comparison (JOINT pair data — per-label scalar orderings are refuted
above); never refuted at ~30,000 upstream plus this lane's fresh exact
points, including both kernel witnesses and the tetrahedron shells that
kill every representative-based rule.  Proving this Prop (or the
selection-free residue below) is the residual K4 endgame. -/
def KFourEdgeDetArgmaxHostsStrictTree : Prop :=
  ∀ point : DirectionChartPoint 6,
    ∃ edge : Fin 6, ∃ tree ∈ kFourSpanningTreeList, edge ∈ tree ∧
      (∀ other ∈ kFourSpanningTreeList, edge ∈ other →
        (directionChartGap kFourDirection point.mass point.weight other).det
          ≤ (directionChartGap kFourDirection point.mass point.weight
            tree).det) ∧
      (directionChartGap kFourDirection point.mass point.weight
        tree).PosDef

/-- **The repaired selection's consumption bridge.**  The per-edge
det-argmax host closes the chart obligation (argmax data discarded; the
weak antecedent discarded pointwise per the forbidden-route law). -/
theorem directionChartIsTieFree_kFour_of_edgeDetArgmaxHosts
    (hhost : KFourEdgeDetArgmaxHostsStrictTree) :
    DirectionChartIsTieFree kFourDirection := by
  intro point _hweak
  obtain ⟨edge, tree, htreeMem, _hedgeMem, _hargmax, hposDef⟩ := hhost point
  have hcard : tree.card = 3 := by
    have hall : ∀ candidate ∈ kFourSpanningTreeList, candidate.card = 3 := by
      decide
    exact hall tree htreeMem
  exact ⟨tree, hcard, hposDef⟩

/-- **The selection-free lift threshold (the scalar residue).**  At every
chart point some spanning tree's gap has its three leading minors positive.
Equivalent to the pointwise strict form; the shape any certificate route —
the det-argmax selection above, or the atlas — discharges. -/
def KFourSomeTreeLiftThreshold : Prop :=
  ∀ point : DirectionChartPoint 6,
    ∃ tree ∈ kFourSpanningTreeList,
      0 < directionChartGap kFourDirection point.mass point.weight tree 0 0 ∧
      0 < directionChartGap kFourDirection point.mass point.weight tree 0 0
          * directionChartGap kFourDirection point.mass point.weight tree 1 1
        - directionChartGap kFourDirection point.mass point.weight tree 0 1
          ^ 2 ∧
      0 < (directionChartGap kFourDirection point.mass point.weight
        tree).det

/-- **The repaired consumption bridge.**  The selection-free lift threshold
closes the chart obligation: nothing but three polynomial inequalities per
point stands between a certificate route and
`DirectionChartIsTieFree kFourDirection`.  (The weak antecedent is discarded
pointwise, per the standing forbidden-route law.) -/
theorem directionChartIsTieFree_kFour_of_someTreeLiftThreshold
    (hlift : KFourSomeTreeLiftThreshold) :
    DirectionChartIsTieFree kFourDirection := by
  intro point _hweak
  obtain ⟨tree, htreeMem, hcorner, hblock, hdet⟩ := hlift point
  have hcard : tree.card = 3 := by
    have hall : ∀ candidate ∈ kFourSpanningTreeList, candidate.card = 3 := by
      decide
    exact hall tree htreeMem
  exact ⟨tree, hcard, directionChartGap_posDef_of_leadingMinors kFourDirection
    point.mass point.weight tree hcorner hblock hdet⟩


/-! ## The certificate atlas, Layer A: the diagonal-splitting engine and the
four star cells

Selection-rule-free covering certificates for the K4 chart obligation
(`DirectionChartIsTieFree kFourDirection`), the fallback route after the
kernel refutation of the max-edge selection above.  A Layer-A cell is a
finite list of strict rational inequalities in the raw chart fields; on the
cell ONE designated spanning tree has positive definite gap, certified by
completed squares (pair absorption), never by eigenvalue reasoning.

The engine is scalar: a symmetric quadratic form in three variables whose
three off-diagonal couplings are absorbed by Cauchy-Schwarz splits
(`offDiagonalAbsorption_nonneg`), leaving a strictly positive residual
diagonal (`splitQuadraticForm_pos`).  Each cell certificate rewrites the
tree's entrywise gap matrix, converts the raw cell inequalities through
`lt_div_iff₀`, and instantiates the engine at the tree's fundamental-cycle
coordinates.

The four star cells below (one per K4 node; designated tree = the star at
that node) are the bulk of the atlas: on exact-rational scans (2,968
adversarial points across six regimes plus the full S4 orbits of the named
hard points) they cover 66 percent of all points, including the ENTIRE
orbit of `maxEdgeRefuterPoint` (the max-edge selection's refutation witness
is caught by the node-2 star cell, re-proved below), the tetrahedron, and
the P1/genericD selection-killers.  The remaining cells of the atlas (the
sixteen scale-free harmonic cells and the knife-collar minor cells) are
enumerated in the campaign ledger; their engine is this same file's. -/

/-- **Pair absorption.**  A single off-diagonal coupling `2*p*zL*zR` is
absorbed by any positive Cauchy-Schwarz split `(sL, sR)` with
`p^2 <= sL*sR`: the key identity is
`sL * (sL*zL^2 + sR*zR^2 + 2*p*zL*zR) = (sL*zL + p*zR)^2 + (sL*sR - p^2)*zR^2`. -/
theorem offDiagonalAbsorption_nonneg (offDiag splitLeft splitRight
    zLeft zRight : ℝ) (hsplitLeftPos : 0 < splitLeft)
    (hsplitProduct : offDiag ^ 2 ≤ splitLeft * splitRight) :
    0 ≤ splitLeft * zLeft ^ 2 + splitRight * zRight ^ 2
      + 2 * offDiag * (zLeft * zRight) := by
  have hkey : splitLeft * (splitLeft * zLeft ^ 2 + splitRight * zRight ^ 2
        + 2 * offDiag * (zLeft * zRight))
      = (splitLeft * zLeft + offDiag * zRight) ^ 2
        + (splitLeft * splitRight - offDiag ^ 2) * zRight ^ 2 := by ring
  have hscaled : splitLeft * 0 ≤ splitLeft * (splitLeft * zLeft ^ 2
      + splitRight * zRight ^ 2 + 2 * offDiag * (zLeft * zRight)) := by
    rw [mul_zero, hkey]
    have hsquare := sq_nonneg (splitLeft * zLeft + offDiag * zRight)
    have hexcess : 0 ≤ (splitLeft * splitRight - offDiag ^ 2) * zRight ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  exact le_of_mul_le_mul_left hscaled hsplitLeftPos

/-- **The diagonal-splitting engine.**  A symmetric quadratic form in three
variables is strictly positive at any nonzero point once each off-diagonal
coupling has a positive split (`off^2 <= split*split'`) and the splits are
strictly diagonally dominated.  Subsumes unweighted, scaled, and banded
diagonal dominance at once; the split parameters may be arbitrary positive
expressions of the chart point, so scale-free cells fit too. -/
theorem splitQuadraticForm_pos (diagOne diagTwo diagThree offOneTwo
    offOneThree offTwoThree splitOneTwo splitTwoOne splitOneThree
    splitThreeOne splitTwoThree splitThreeTwo zOne zTwo zThree : ℝ)
    (hsplitOneTwoPos : 0 < splitOneTwo)
    (hsplitOneThreePos : 0 < splitOneThree)
    (hsplitTwoThreePos : 0 < splitTwoThree)
    (hproductOneTwo : offOneTwo ^ 2 ≤ splitOneTwo * splitTwoOne)
    (hproductOneThree : offOneThree ^ 2 ≤ splitOneThree * splitThreeOne)
    (hproductTwoThree : offTwoThree ^ 2 ≤ splitTwoThree * splitThreeTwo)
    (hdominanceOne : splitOneTwo + splitOneThree < diagOne)
    (hdominanceTwo : splitTwoOne + splitTwoThree < diagTwo)
    (hdominanceThree : splitThreeOne + splitThreeTwo < diagThree)
    (hsomeNonzero : zOne ≠ 0 ∨ zTwo ≠ 0 ∨ zThree ≠ 0) :
    0 < diagOne * zOne ^ 2 + diagTwo * zTwo ^ 2 + diagThree * zThree ^ 2
      + 2 * offOneTwo * (zOne * zTwo) + 2 * offOneThree * (zOne * zThree)
      + 2 * offTwoThree * (zTwo * zThree) := by
  have habsorbOneTwo := offDiagonalAbsorption_nonneg offOneTwo splitOneTwo
    splitTwoOne zOne zTwo hsplitOneTwoPos hproductOneTwo
  have habsorbOneThree := offDiagonalAbsorption_nonneg offOneThree
    splitOneThree splitThreeOne zOne zThree hsplitOneThreePos
    hproductOneThree
  have habsorbTwoThree := offDiagonalAbsorption_nonneg offTwoThree
    splitTwoThree splitThreeTwo zTwo zThree hsplitTwoThreePos
    hproductTwoThree
  have hdecompose : diagOne * zOne ^ 2 + diagTwo * zTwo ^ 2
        + diagThree * zThree ^ 2 + 2 * offOneTwo * (zOne * zTwo)
        + 2 * offOneThree * (zOne * zThree)
        + 2 * offTwoThree * (zTwo * zThree)
      = (splitOneTwo * zOne ^ 2 + splitTwoOne * zTwo ^ 2
          + 2 * offOneTwo * (zOne * zTwo))
        + (splitOneThree * zOne ^ 2 + splitThreeOne * zThree ^ 2
          + 2 * offOneThree * (zOne * zThree))
        + (splitTwoThree * zTwo ^ 2 + splitThreeTwo * zThree ^ 2
          + 2 * offTwoThree * (zTwo * zThree))
        + (diagOne - splitOneTwo - splitOneThree) * zOne ^ 2
        + (diagTwo - splitTwoOne - splitTwoThree) * zTwo ^ 2
        + (diagThree - splitThreeOne - splitThreeTwo) * zThree ^ 2 := by
    ring
  rcases hsomeNonzero with hnonzero | hnonzero | hnonzero
  · have hresidualOne : 0 < (diagOne - splitOneTwo - splitOneThree)
        * zOne ^ 2 :=
      mul_pos (by linarith) (pow_two_pos_of_ne_zero hnonzero)
    have hresidualTwo : 0 ≤ (diagTwo - splitTwoOne - splitTwoThree)
        * zTwo ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hresidualThree : 0 ≤ (diagThree - splitThreeOne - splitThreeTwo)
        * zThree ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  · have hresidualOne : 0 ≤ (diagOne - splitOneTwo - splitOneThree)
        * zOne ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hresidualTwo : 0 < (diagTwo - splitTwoOne - splitTwoThree)
        * zTwo ^ 2 :=
      mul_pos (by linarith) (pow_two_pos_of_ne_zero hnonzero)
    have hresidualThree : 0 ≤ (diagThree - splitThreeOne - splitThreeTwo)
        * zThree ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  · have hresidualOne : 0 ≤ (diagOne - splitOneTwo - splitOneThree)
        * zOne ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hresidualTwo : 0 ≤ (diagTwo - splitTwoOne - splitTwoThree)
        * zTwo ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hresidualThree : 0 < (diagThree - splitThreeOne - splitThreeTwo)
        * zThree ^ 2 :=
      mul_pos (by linarith) (pow_two_pos_of_ne_zero hnonzero)
    linarith

/-! ## Entrywise gap matrices for the two off-edge-5 star trees

`{0,1,3}` (star at node `1`) and `{0,2,4}` (star at node `2`); the other
two stars `{1,2,5}`, `{3,4,5}` are already stated above.  Sympy-verified
against the definition before statement, house template. -/

/-- The `{0,1,3}` chart gap (star at node `1`), entry by entry. -/
theorem kFourGap_treeZeroOneThree_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 1, 3}
      = Matrix.of
          ![![point.mass 0 / point.weight 0 + point.mass 1 / point.weight 1
                + point.mass 3 / point.weight 3
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2,
              point.mass 1 / point.weight 1
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0,2,4}` chart gap (star at node `2`), entry by entry. -/
theorem kFourGap_treeZeroTwoFour_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 2, 4}
      = Matrix.of
          ![![point.mass 0 / point.weight 0
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 + point.mass 2 / point.weight 2
                + point.mass 4 / point.weight 4
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 2 / point.weight 2
                - (point.mass 1 + point.mass 2 + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-! ## The four star cells

Cell of the star at node `n`: for each of the three edges `e` at `n`, the
raw quadratic inequality `w_e * (m_e + 2*m_a + 2*m_b) < m_e`, where
`a`, `b` are the two off-tree edges whose fundamental cycle uses `e`
(equivalently `alpha_e > 2*(m_a + m_b)` in conductance currency).  On the
cell the star's gap is positive definite via the engine at the star's
fundamental-cycle coordinates. -/

/-- **Star cell at node `1`** (tree `{0,1,3}`; off-tree cycles: edge `2`
over `{0,1}`, edge `4` over `{0,3}`, edge `5` over `{1,3}`). -/
theorem kFourAtlas_starNodeOne_posDef_of_cell (point : DirectionChartPoint 6)
    (hedgeZero : point.weight 0 * (point.mass 0 + 2 * point.mass 2
      + 2 * point.mass 4) < point.mass 0)
    (hedgeOne : point.weight 1 * (point.mass 1 + 2 * point.mass 2
      + 2 * point.mass 5) < point.mass 1)
    (hedgeThree : point.weight 3 * (point.mass 3 + 2 * point.mass 4
      + 2 * point.mass 5) < point.mass 3) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 3}).PosDef := by
  have hcoeffZero : point.mass 0 + 2 * point.mass 2 + 2 * point.mass 4
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + 2 * point.mass 2 + 2 * point.mass 4)
          * point.weight 0
        = point.weight 0 * (point.mass 0 + 2 * point.mass 2
            + 2 * point.mass 4) := by ring
      _ < point.mass 0 := hedgeZero
  have hcoeffOne : point.mass 1 + 2 * point.mass 2 + 2 * point.mass 5
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + 2 * point.mass 2 + 2 * point.mass 5)
          * point.weight 1
        = point.weight 1 * (point.mass 1 + 2 * point.mass 2
            + 2 * point.mass 5) := by ring
      _ < point.mass 1 := hedgeOne
  have hcoeffThree : point.mass 3 + 2 * point.mass 4 + 2 * point.mass 5
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + 2 * point.mass 4 + 2 * point.mass 5)
          * point.weight 3
        = point.weight 3 * (point.mass 3 + 2 * point.mass 4
            + 2 * point.mass 5) := by ring
      _ < point.mass 3 := hedgeThree
  rw [kFourGap_treeZeroOneThree_eq]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 0 - vecArg 2 ≠ 0
        ∨ vecArg 0 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvZero : vecArg 0 = 0 := hcycleThree
      have hvOne : vecArg 1 = 0 := by linarith
      have hvTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvZero
      · exact hbad hvOne
      · exact hbad hvTwo
    have hform : vecArg ⬝ᵥ ((Matrix.of
          ![![point.mass 0 / point.weight 0 + point.mass 1 / point.weight 1
                + point.mass 3 / point.weight 3
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2,
              point.mass 1 / point.weight 1
                - (point.mass 1 + point.mass 2 + point.mass 5)]]
            : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
              - point.mass 4) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
              - point.mass 5) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
              - point.mass 5) * (vecArg 0) ^ 2
          + 2 * point.mass 2 * ((vecArg 0 - vecArg 1) * (vecArg 0 - vecArg 2))
          + 2 * point.mass 4 * ((vecArg 0 - vecArg 1) * (vecArg 0))
          + 2 * point.mass 5 * ((vecArg 0 - vecArg 2) * (vecArg 0)) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact splitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
        - point.mass 4)
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
        - point.mass 5)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
        - point.mass 5)
      (point.mass 2) (point.mass 4) (point.mass 5)
      (point.mass 2) (point.mass 2) (point.mass 4) (point.mass 4)
      (point.mass 5) (point.mass 5)
      (vecArg 0 - vecArg 1) (vecArg 0 - vecArg 2) (vecArg 0)
      (point.mass_pos 2) (point.mass_pos 4) (point.mass_pos 5)
      (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
      (by linarith) (by linarith) (by linarith)
      hzNonzero

/-- **Star cell at node `2`** (tree `{0,2,4}`; off-tree cycles: edge `1`
over `{0,2}`, edge `3` over `{0,4}`, edge `5` over `{2,4}`). -/
theorem kFourAtlas_starNodeTwo_posDef_of_cell (point : DirectionChartPoint 6)
    (hedgeZero : point.weight 0 * (point.mass 0 + 2 * point.mass 1
      + 2 * point.mass 3) < point.mass 0)
    (hedgeTwo : point.weight 2 * (point.mass 2 + 2 * point.mass 1
      + 2 * point.mass 5) < point.mass 2)
    (hedgeFour : point.weight 4 * (point.mass 4 + 2 * point.mass 3
      + 2 * point.mass 5) < point.mass 4) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 4}).PosDef := by
  have hcoeffZero : point.mass 0 + 2 * point.mass 1 + 2 * point.mass 3
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + 2 * point.mass 1 + 2 * point.mass 3)
          * point.weight 0
        = point.weight 0 * (point.mass 0 + 2 * point.mass 1
            + 2 * point.mass 3) := by ring
      _ < point.mass 0 := hedgeZero
  have hcoeffTwo : point.mass 2 + 2 * point.mass 1 + 2 * point.mass 5
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + 2 * point.mass 1 + 2 * point.mass 5)
          * point.weight 2
        = point.weight 2 * (point.mass 2 + 2 * point.mass 1
            + 2 * point.mass 5) := by ring
      _ < point.mass 2 := hedgeTwo
  have hcoeffFour : point.mass 4 + 2 * point.mass 3 + 2 * point.mass 5
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + 2 * point.mass 3 + 2 * point.mass 5)
          * point.weight 4
        = point.weight 4 * (point.mass 4 + 2 * point.mass 3
            + 2 * point.mass 5) := by ring
      _ < point.mass 4 := hedgeFour
  rw [kFourGap_treeZeroTwoFour_eq]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 1 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvOne : vecArg 1 = 0 := hcycleThree
      have hvZero : vecArg 0 = 0 := by linarith
      have hvTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvZero
      · exact hbad hvOne
      · exact hbad hvTwo
    have hform : vecArg ⬝ᵥ ((Matrix.of
          ![![point.mass 0 / point.weight 0
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 + point.mass 2 / point.weight 2
                + point.mass 4 / point.weight 4
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 2 / point.weight 2
                - (point.mass 1 + point.mass 2 + point.mass 5)]]
            : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
              - point.mass 3) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
              - point.mass 5) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
              - point.mass 5) * (vecArg 1) ^ 2
          + 2 * (-point.mass 1)
              * ((vecArg 0 - vecArg 1) * (vecArg 1 - vecArg 2))
          + 2 * (-point.mass 3) * ((vecArg 0 - vecArg 1) * (vecArg 1))
          + 2 * point.mass 5 * ((vecArg 1 - vecArg 2) * (vecArg 1)) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact splitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
        - point.mass 3)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
        - point.mass 5)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
        - point.mass 5)
      (-point.mass 1) (-point.mass 3) (point.mass 5)
      (point.mass 1) (point.mass 1) (point.mass 3) (point.mass 3)
      (point.mass 5) (point.mass 5)
      (vecArg 0 - vecArg 1) (vecArg 1 - vecArg 2) (vecArg 1)
      (point.mass_pos 1) (point.mass_pos 3) (point.mass_pos 5)
      (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
      (by linarith) (by linarith) (by linarith)
      hzNonzero

/-- **Star cell at node `3`** (tree `{1,2,5}`; off-tree cycles: edge `0`
over `{1,2}`, edge `3` over `{1,5}`, edge `4` over `{2,5}`). -/
theorem kFourAtlas_starNodeThree_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hedgeOne : point.weight 1 * (point.mass 1 + 2 * point.mass 0
      + 2 * point.mass 3) < point.mass 1)
    (hedgeTwo : point.weight 2 * (point.mass 2 + 2 * point.mass 0
      + 2 * point.mass 4) < point.mass 2)
    (hedgeFive : point.weight 5 * (point.mass 5 + 2 * point.mass 3
      + 2 * point.mass 4) < point.mass 5) :
    (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 5}).PosDef := by
  have hcoeffOne : point.mass 1 + 2 * point.mass 0 + 2 * point.mass 3
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + 2 * point.mass 0 + 2 * point.mass 3)
          * point.weight 1
        = point.weight 1 * (point.mass 1 + 2 * point.mass 0
            + 2 * point.mass 3) := by ring
      _ < point.mass 1 := hedgeOne
  have hcoeffTwo : point.mass 2 + 2 * point.mass 0 + 2 * point.mass 4
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + 2 * point.mass 0 + 2 * point.mass 4)
          * point.weight 2
        = point.weight 2 * (point.mass 2 + 2 * point.mass 0
            + 2 * point.mass 4) := by ring
      _ < point.mass 2 := hedgeTwo
  have hcoeffFive : point.mass 5 + 2 * point.mass 3 + 2 * point.mass 4
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + 2 * point.mass 3 + 2 * point.mass 4)
          * point.weight 5
        = point.weight 5 * (point.mass 5 + 2 * point.mass 3
            + 2 * point.mass 4) := by ring
      _ < point.mass 5 := hedgeFive
  rw [kFourGap_treeOneTwoFive_eq]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 2 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 2 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvTwo : vecArg 2 = 0 := hcycleThree
      have hvZero : vecArg 0 = 0 := by linarith
      have hvOne : vecArg 1 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvZero
      · exact hbad hvOne
      · exact hbad hvTwo
    have hform : vecArg ⬝ᵥ ((Matrix.of
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
                - (point.mass 1 + point.mass 2 + point.mass 5)]]
            : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
              - point.mass 3) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
              - point.mass 4) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
              - point.mass 4) * (vecArg 2) ^ 2
          + 2 * point.mass 0
              * ((vecArg 0 - vecArg 2) * (vecArg 1 - vecArg 2))
          + 2 * (-point.mass 3) * ((vecArg 0 - vecArg 2) * (vecArg 2))
          + 2 * (-point.mass 4) * ((vecArg 1 - vecArg 2) * (vecArg 2)) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact splitQuadraticForm_pos
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
        - point.mass 3)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
        - point.mass 4)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
        - point.mass 4)
      (point.mass 0) (-point.mass 3) (-point.mass 4)
      (point.mass 0) (point.mass 0) (point.mass 3) (point.mass 3)
      (point.mass 4) (point.mass 4)
      (vecArg 0 - vecArg 2) (vecArg 1 - vecArg 2) (vecArg 2)
      (point.mass_pos 0) (point.mass_pos 3) (point.mass_pos 4)
      (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
      (by linarith) (by linarith) (by linarith)
      hzNonzero

/-- **Star cell at node `4`** (tree `{3,4,5}`, the gauge-node star;
off-tree cycles: edge `0` over `{3,4}`, edge `1` over `{3,5}`, edge `2`
over `{4,5}`).  The PoC region certificate, re-founded on the engine. -/
theorem kFourAtlas_starNodeFour_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hedgeThree : point.weight 3 * (point.mass 3 + 2 * point.mass 0
      + 2 * point.mass 1) < point.mass 3)
    (hedgeFour : point.weight 4 * (point.mass 4 + 2 * point.mass 0
      + 2 * point.mass 2) < point.mass 4)
    (hedgeFive : point.weight 5 * (point.mass 5 + 2 * point.mass 1
      + 2 * point.mass 2) < point.mass 5) :
    (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosDef := by
  have hcoeffThree : point.mass 3 + 2 * point.mass 0 + 2 * point.mass 1
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + 2 * point.mass 0 + 2 * point.mass 1)
          * point.weight 3
        = point.weight 3 * (point.mass 3 + 2 * point.mass 0
            + 2 * point.mass 1) := by ring
      _ < point.mass 3 := hedgeThree
  have hcoeffFour : point.mass 4 + 2 * point.mass 0 + 2 * point.mass 2
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + 2 * point.mass 0 + 2 * point.mass 2)
          * point.weight 4
        = point.weight 4 * (point.mass 4 + 2 * point.mass 0
            + 2 * point.mass 2) := by ring
      _ < point.mass 4 := hedgeFour
  have hcoeffFive : point.mass 5 + 2 * point.mass 1 + 2 * point.mass 2
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + 2 * point.mass 1 + 2 * point.mass 2)
          * point.weight 5
        = point.weight 5 * (point.mass 5 + 2 * point.mass 1
            + 2 * point.mass 2) := by ring
      _ < point.mass 5 := hedgeFive
  rw [kFourGap_treeThreeFourFive_eq]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [Matrix.transpose_apply]
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hform : vecArg ⬝ᵥ ((Matrix.of
          ![![point.mass 3 / point.weight 3 - (point.mass 1 + point.mass 3)
                - point.mass 0,
              point.mass 0, point.mass 1],
            ![point.mass 0,
              point.mass 4 / point.weight 4 - (point.mass 2 + point.mass 4)
                - point.mass 0,
              point.mass 2],
            ![point.mass 1, point.mass 2,
              point.mass 5 / point.weight 5
                - (point.mass 1 + point.mass 2 + point.mass 5)]]
            : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
        = (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
              - point.mass 1) * (vecArg 0) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
              - point.mass 2) * (vecArg 1) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
              - point.mass 2) * (vecArg 2) ^ 2
          + 2 * point.mass 0 * (vecArg 0 * vecArg 1)
          + 2 * point.mass 1 * (vecArg 0 * vecArg 2)
          + 2 * point.mass 2 * (vecArg 1 * vecArg 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact splitQuadraticForm_pos
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
        - point.mass 1)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
        - point.mass 2)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
        - point.mass 2)
      (point.mass 0) (point.mass 1) (point.mass 2)
      (point.mass 0) (point.mass 0) (point.mass 1) (point.mass 1)
      (point.mass 2) (point.mass 2)
      (vecArg 0) (vecArg 1) (vecArg 2)
      (point.mass_pos 0) (point.mass_pos 1) (point.mass_pos 2)
      (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
      (by linarith) (by linarith) (by linarith)
      hsomeCoordinateNonzero

/-! ## Layer-A star dispatch and the caught witnesses -/

/-- **The star dispatch.**  Any of the four star cells delivers the chart
obligation's conclusion outright — no weak antecedent, no selection rule.
This is the assembled bulk layer of the atlas; the remaining cells extend
this disjunction, never replace it. -/
theorem kFourAtlas_hasStrictTriple_of_anyStarCell
    (point : DirectionChartPoint 6)
    (hcell :
      (point.weight 0 * (point.mass 0 + 2 * point.mass 2 + 2 * point.mass 4)
          < point.mass 0
        ∧ point.weight 1 * (point.mass 1 + 2 * point.mass 2
            + 2 * point.mass 5) < point.mass 1
        ∧ point.weight 3 * (point.mass 3 + 2 * point.mass 4
            + 2 * point.mass 5) < point.mass 3)
      ∨ (point.weight 0 * (point.mass 0 + 2 * point.mass 1
            + 2 * point.mass 3) < point.mass 0
        ∧ point.weight 2 * (point.mass 2 + 2 * point.mass 1
            + 2 * point.mass 5) < point.mass 2
        ∧ point.weight 4 * (point.mass 4 + 2 * point.mass 3
            + 2 * point.mass 5) < point.mass 4)
      ∨ (point.weight 1 * (point.mass 1 + 2 * point.mass 0
            + 2 * point.mass 3) < point.mass 1
        ∧ point.weight 2 * (point.mass 2 + 2 * point.mass 0
            + 2 * point.mass 4) < point.mass 2
        ∧ point.weight 5 * (point.mass 5 + 2 * point.mass 3
            + 2 * point.mass 4) < point.mass 5)
      ∨ (point.weight 3 * (point.mass 3 + 2 * point.mass 0
            + 2 * point.mass 1) < point.mass 3
        ∧ point.weight 4 * (point.mass 4 + 2 * point.mass 0
            + 2 * point.mass 2) < point.mass 4
        ∧ point.weight 5 * (point.mass 5 + 2 * point.mass 1
            + 2 * point.mass 2) < point.mass 5)) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection point.mass point.weight
        selected).PosDef := by
  rcases hcell with ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩ | ⟨hA, hB, hC⟩
  · exact ⟨{0, 1, 3}, by decide,
      kFourAtlas_starNodeOne_posDef_of_cell point hA hB hC⟩
  · exact ⟨{0, 2, 4}, by decide,
      kFourAtlas_starNodeTwo_posDef_of_cell point hA hB hC⟩
  · exact ⟨{1, 2, 5}, by decide,
      kFourAtlas_starNodeThree_posDef_of_cell point hA hB hC⟩
  · exact ⟨{3, 4, 5}, by decide,
      kFourAtlas_starNodeFour_posDef_of_cell point hA hB hC⟩

/-- The max-edge refutation witness sits inside the node-`2` star cell
(margins `119/30`, `11/12`, `1199/30` in conductance currency): the atlas
catches TEST POINT ZERO with no selection rule. -/
theorem maxEdgeRefuterPoint_satisfiesStarNodeTwoCell :
    maxEdgeRefuterPoint.weight 0 * (maxEdgeRefuterPoint.mass 0
        + 2 * maxEdgeRefuterPoint.mass 1 + 2 * maxEdgeRefuterPoint.mass 3)
      < maxEdgeRefuterPoint.mass 0
    ∧ maxEdgeRefuterPoint.weight 2 * (maxEdgeRefuterPoint.mass 2
        + 2 * maxEdgeRefuterPoint.mass 1 + 2 * maxEdgeRefuterPoint.mass 5)
      < maxEdgeRefuterPoint.mass 2
    ∧ maxEdgeRefuterPoint.weight 4 * (maxEdgeRefuterPoint.mass 4
        + 2 * maxEdgeRefuterPoint.mass 3 + 2 * maxEdgeRefuterPoint.mass 5)
      < maxEdgeRefuterPoint.mass 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The atlas's independent re-derivation of the strict triple at the
refutation witness: the star dispatch applied at the node-`2` cell. -/
theorem maxEdgeRefuterPoint_hasStrictTriple_viaAtlas :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight selected).PosDef :=
  kFourAtlas_hasStrictTriple_of_anyStarCell maxEdgeRefuterPoint
    (Or.inr (Or.inl maxEdgeRefuterPoint_satisfiesStarNodeTwoCell))

/-- The tetrahedron sits inside ALL FOUR star cells (margin `1/24` per
inequality); the node-`4` membership re-derives the landed sample. -/
theorem tetrahedronChartPoint_satisfiesStarNodeFourCell :
    tetrahedronChartPoint.weight 3 * (tetrahedronChartPoint.mass 3
        + 2 * tetrahedronChartPoint.mass 0 + 2 * tetrahedronChartPoint.mass 1)
      < tetrahedronChartPoint.mass 3
    ∧ tetrahedronChartPoint.weight 4 * (tetrahedronChartPoint.mass 4
        + 2 * tetrahedronChartPoint.mass 0 + 2 * tetrahedronChartPoint.mass 2)
      < tetrahedronChartPoint.mass 4
    ∧ tetrahedronChartPoint.weight 5 * (tetrahedronChartPoint.mass 5
        + 2 * tetrahedronChartPoint.mass 1 + 2 * tetrahedronChartPoint.mass 2)
      < tetrahedronChartPoint.mass 5 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · show (1 / 6 : ℝ) * (1 / 4 + 2 * (1 / 4) + 2 * (1 / 4)) < 1 / 4
      norm_num


/-! ## The certificate atlas, Layer A completed: the sixteen scale-free
harmonic cells

The scale-free complement of the four star cells above.  Cell
HARMONIC(T) asserts, at the designated spanning tree `T`, a positive
Z-form diagonal (three raw degree-2 inequalities, one per tree edge) plus
Jacobi-scaled strict diagonal dominance in cleared form --
`A*d3 + B*d2 < d2*d3`, `A*d3 + C*d1 < d1*d3`, `B*d2 + C*d1 < d1*d2`,
where `d1, d2, d3` are the tree-form diagonal entries and `A`, `B`, `C`
the off-diagonal mass sums.  No off-diagonal of any of the sixteen tree
forms mixes signs, so the absolute values are polynomial GLOBALLY and no
sign sub-cells are needed.  The certificate is the same splitting engine
at the scale-free splits `(d1*A/d2, d2*A/d1)` etc., packaged once as
`harmonicSplitQuadraticForm_pos`; being scale-free, the cells survive the
weight-floor collar where every bounded-menu splitting family provably
blows up (campaign ledger, step-4/6 refutations).  Six new entrywise gap
matrices (the off-edge-5 path trees) complete the sixteen per-tree closed
forms; `kFourAtlas_hasStrictTriple_of_anyCell` extends the star dispatch
to the full twenty-cell Layer A. -/

/-! ### Entrywise gap matrices for the six off-edge-5 path trees

`{0,1,4}`, `{0,2,3}`, `{1,2,3}`, `{1,2,4}`, `{1,3,4}`, `{2,3,4}` -- the
sixteen spanning trees now all have entrywise closed forms in the module.
Sympy-verified against the definition before statement, house rule. -/

/-- The `{0, 1, 4}` chart gap (off-edge-5 path), entry by entry (atlas frame). -/
theorem kFourGap_treeZeroOneFour_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 1, 4}
      = Matrix.of
          ![![point.mass 0 / point.weight 0 + point.mass 1 / point.weight 1
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 + point.mass 4 / point.weight 4
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2,
              point.mass 1 / point.weight 1 - (point.mass 1 + point.mass 2
                + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{0, 2, 3}` chart gap (off-edge-5 path), entry by entry (atlas frame). -/
theorem kFourGap_treeZeroTwoThree_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {0, 2, 3}
      = Matrix.of
          ![![point.mass 0 / point.weight 0 + point.mass 3 / point.weight 3
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 1],
            ![point.mass 0 - point.mass 0 / point.weight 0,
              point.mass 0 / point.weight 0 + point.mass 2 / point.weight 2
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 2 / point.weight 2 - (point.mass 1 + point.mass 2
                + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{1, 2, 3}` chart gap (off-edge-5 path), entry by entry (atlas frame). -/
theorem kFourGap_treeOneTwoThree_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {1, 2, 3}
      = Matrix.of
          ![![point.mass 1 / point.weight 1 + point.mass 3 / point.weight 3
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0,
              point.mass 2 / point.weight 2 - (point.mass 0 + point.mass 2
                + point.mass 4),
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

/-- The `{1, 2, 4}` chart gap (off-edge-5 path), entry by entry (atlas frame). -/
theorem kFourGap_treeOneTwoFour_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {1, 2, 4}
      = Matrix.of
          ![![point.mass 1 / point.weight 1 - (point.mass 0 + point.mass 1
                + point.mass 3),
              point.mass 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0,
              point.mass 2 / point.weight 2 + point.mass 4 / point.weight 4
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

/-- The `{1, 3, 4}` chart gap (off-edge-5 path), entry by entry (atlas frame). -/
theorem kFourGap_treeOneThreeFour_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {1, 3, 4}
      = Matrix.of
          ![![point.mass 1 / point.weight 1 + point.mass 3 / point.weight 3
                - (point.mass 0 + point.mass 1 + point.mass 3),
              point.mass 0,
              point.mass 1 - point.mass 1 / point.weight 1],
            ![point.mass 0,
              point.mass 4 / point.weight 4 - (point.mass 0 + point.mass 2
                + point.mass 4),
              point.mass 2],
            ![point.mass 1 - point.mass 1 / point.weight 1,
              point.mass 2,
              point.mass 1 / point.weight 1 - (point.mass 1 + point.mass 2
                + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- The `{2, 3, 4}` chart gap (off-edge-5 path), entry by entry (atlas frame). -/
theorem kFourGap_treeTwoThreeFour_eq (point : DirectionChartPoint 6) :
    directionChartGap kFourDirection point.mass point.weight {2, 3, 4}
      = Matrix.of
          ![![point.mass 3 / point.weight 3 - (point.mass 0 + point.mass 1
                + point.mass 3),
              point.mass 0,
              point.mass 1],
            ![point.mass 0,
              point.mass 2 / point.weight 2 + point.mass 4 / point.weight 4
                - (point.mass 0 + point.mass 2 + point.mass 4),
              point.mass 2 - point.mass 2 / point.weight 2],
            ![point.mass 1,
              point.mass 2 - point.mass 2 / point.weight 2,
              point.mass 2 / point.weight 2 - (point.mass 1 + point.mass 2
                + point.mass 5)]] := by
  simp only [directionChartGap]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;> ring

/-- **The harmonic engine: Jacobi-scaled strict diagonal dominance.**
The diagonal-splitting engine at the scale-free splits
`(d1*A/d2, d2*A/d1)`, `(d1*B/d3, d3*B/d1)`, `(d2*C/d3, d3*C/d2)`:
a symmetric quadratic form with positive diagonal `d1, d2, d3` whose
off-diagonals match positive absolute values `A, B, C` (as squares) is
strictly positive at any nonzero point once the three cleared Jacobi
inequalities `A*d3 + B*d2 < d2*d3`, `A*d3 + C*d1 < d1*d3`,
`B*d2 + C*d1 < d1*d2` hold.  No menu constants: weight-floor collars
cannot escape by ratio blowup. -/
theorem harmonicSplitQuadraticForm_pos (diagOne diagTwo diagThree offOneTwo
    offOneThree offTwoThree absOneTwo absOneThree absTwoThree
    zOne zTwo zThree : ℝ)
    (hdiagOnePos : 0 < diagOne) (hdiagTwoPos : 0 < diagTwo)
    (hdiagThreePos : 0 < diagThree)
    (habsOneTwoPos : 0 < absOneTwo)
    (habsOneThreePos : 0 < absOneThree)
    (habsTwoThreePos : 0 < absTwoThree)
    (hsquareOneTwo : offOneTwo ^ 2 = absOneTwo ^ 2)
    (hsquareOneThree : offOneThree ^ 2 = absOneThree ^ 2)
    (hsquareTwoThree : offTwoThree ^ 2 = absTwoThree ^ 2)
    (hdominanceOne : absOneTwo * diagThree + absOneThree * diagTwo
      < diagTwo * diagThree)
    (hdominanceTwo : absOneTwo * diagThree + absTwoThree * diagOne
      < diagOne * diagThree)
    (hdominanceThree : absOneThree * diagTwo + absTwoThree * diagOne
      < diagOne * diagTwo)
    (hsomeNonzero : zOne ≠ 0 ∨ zTwo ≠ 0 ∨ zThree ≠ 0) :
    0 < diagOne * zOne ^ 2 + diagTwo * zTwo ^ 2 + diagThree * zThree ^ 2
      + 2 * offOneTwo * (zOne * zTwo) + 2 * offOneThree * (zOne * zThree)
      + 2 * offTwoThree * (zTwo * zThree) := by
  have hproductOneTwo : diagOne * absOneTwo / diagTwo
      * (diagTwo * absOneTwo / diagOne) = absOneTwo ^ 2 := by
    field_simp [ne_of_gt hdiagOnePos, ne_of_gt hdiagTwoPos]
  have hproductOneThree : diagOne * absOneThree / diagThree
      * (diagThree * absOneThree / diagOne) = absOneThree ^ 2 := by
    field_simp [ne_of_gt hdiagOnePos, ne_of_gt hdiagThreePos]
  have hproductTwoThree : diagTwo * absTwoThree / diagThree
      * (diagThree * absTwoThree / diagTwo) = absTwoThree ^ 2 := by
    field_simp [ne_of_gt hdiagTwoPos, ne_of_gt hdiagThreePos]
  have hsplitDomOne : diagOne * absOneTwo / diagTwo
      + diagOne * absOneThree / diagThree < diagOne := by
    have hcombine : diagOne * absOneTwo / diagTwo
        + diagOne * absOneThree / diagThree
        = diagOne * (absOneTwo * diagThree + absOneThree * diagTwo)
          / (diagTwo * diagThree) := by
      field_simp [ne_of_gt hdiagTwoPos, ne_of_gt hdiagThreePos]
    rw [hcombine, div_lt_iff₀ (mul_pos hdiagTwoPos hdiagThreePos)]
    exact mul_lt_mul_of_pos_left hdominanceOne hdiagOnePos
  have hsplitDomTwo : diagTwo * absOneTwo / diagOne
      + diagTwo * absTwoThree / diagThree < diagTwo := by
    have hcombine : diagTwo * absOneTwo / diagOne
        + diagTwo * absTwoThree / diagThree
        = diagTwo * (absOneTwo * diagThree + absTwoThree * diagOne)
          / (diagOne * diagThree) := by
      field_simp [ne_of_gt hdiagOnePos, ne_of_gt hdiagThreePos]
    rw [hcombine, div_lt_iff₀ (mul_pos hdiagOnePos hdiagThreePos)]
    exact mul_lt_mul_of_pos_left hdominanceTwo hdiagTwoPos
  have hsplitDomThree : diagThree * absOneThree / diagOne
      + diagThree * absTwoThree / diagTwo < diagThree := by
    have hcombine : diagThree * absOneThree / diagOne
        + diagThree * absTwoThree / diagTwo
        = diagThree * (absOneThree * diagTwo + absTwoThree * diagOne)
          / (diagOne * diagTwo) := by
      field_simp [ne_of_gt hdiagOnePos, ne_of_gt hdiagTwoPos]
    rw [hcombine, div_lt_iff₀ (mul_pos hdiagOnePos hdiagTwoPos)]
    exact mul_lt_mul_of_pos_left hdominanceThree hdiagThreePos
  refine splitQuadraticForm_pos diagOne diagTwo diagThree offOneTwo
    offOneThree offTwoThree
    (diagOne * absOneTwo / diagTwo) (diagTwo * absOneTwo / diagOne)
    (diagOne * absOneThree / diagThree) (diagThree * absOneThree / diagOne)
    (diagTwo * absTwoThree / diagThree) (diagThree * absTwoThree / diagTwo)
    zOne zTwo zThree
    (div_pos (mul_pos hdiagOnePos habsOneTwoPos) hdiagTwoPos)
    (div_pos (mul_pos hdiagOnePos habsOneThreePos) hdiagThreePos)
    (div_pos (mul_pos hdiagTwoPos habsTwoThreePos) hdiagThreePos)
    ?_ ?_ ?_ hsplitDomOne hsplitDomTwo hsplitDomThree hsomeNonzero
  · rw [hproductOneTwo]
    exact le_of_eq hsquareOneTwo
  · rw [hproductOneThree]
    exact le_of_eq hsquareOneThree
  · rw [hproductTwoThree]
    exact le_of_eq hsquareTwoThree

/-! ### The sixteen harmonic cells

One cell per spanning tree, hypotheses in the raw chart fields (diagonal
positivity) and cleared Jacobi currency (dominance); each certificate is
the harmonic engine at the tree's fundamental-cycle coordinates, with the
nonzero-coordinate transfer supplied by the explicit basis solve. -/

/-- **Harmonic cell on tree `{0, 1, 3}`** (scale-free Jacobi dominance;
off-tree cycles: edge `2` over `{0,1}`, edge `4` over `{0,3}`, edge `5` over `{1,3}`). -/
theorem kFourAtlas_harmonicZeroOneThree_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 2
      + point.mass 4) < point.mass 0)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 2
      + point.mass 5) < point.mass 1)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 4
      + point.mass 5) < point.mass 3)
    (hdomRowOne : point.mass 2 * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5) + point.mass 4
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
      - point.mass 5) < (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 5) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5))
    (hdomRowTwo : point.mass 2 * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5) + point.mass 5
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 4) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 4) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5))
    (hdomRowThree : point.mass 4 * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 2 - point.mass 5) + point.mass 5
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 4) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 4) * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 2 - point.mass 5)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 3}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 2 + point.mass 4
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 2 + point.mass 4) * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 4)
            := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffOne : point.mass 1 + point.mass 2 + point.mass 5
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 2 + point.mass 5) * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 5)
            := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffThree : point.mass 3 + point.mass 4 + point.mass 5
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 4 + point.mass 5) * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 4 + point.mass 5)
            := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 4 := by linarith
  have hdiagTwoPos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 5 := by linarith
  have hdiagThreePos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 4 - point.mass 5 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 1, 3})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 0 - vecArg 2 ≠ 0
        ∨ vecArg 0 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 1, 3} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
          - point.mass 4) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
          - point.mass 5) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
          - point.mass 5) * (vecArg 0) ^ 2 + 2 * point.mass 2 * ((vecArg 0
          - vecArg 1) * (vecArg 0 - vecArg 2)) + 2 * point.mass 4
          * ((vecArg 0 - vecArg 1) * (vecArg 0)) + 2 * point.mass 5
          * ((vecArg 0 - vecArg 2) * (vecArg 0)) := by
      rw [kFourGap_treeZeroOneThree_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
        - point.mass 4)
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
        - point.mass 5)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
        - point.mass 5)
      (point.mass 2) (point.mass 4) (point.mass 5)
      (point.mass 2) (point.mass 4) (point.mass 5)
      (vecArg 0 - vecArg 1) (vecArg 0 - vecArg 2) (vecArg 0)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (point.mass_pos 2) (point.mass_pos 4) (point.mass_pos 5)
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{0, 1, 4}`** (scale-free Jacobi dominance;
off-tree cycles: edge `2` over `{0,1}`, edge `3` over `{0,4}`, edge `5` over `{0,1,4}`). -/
theorem kFourAtlas_harmonicZeroOneFour_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 2
      + point.mass 3 + point.mass 5) < point.mass 0)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 2
      + point.mass 5) < point.mass 1)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 3
      + point.mass 5) < point.mass 4)
    (hdomRowOne : (point.mass 2 + point.mass 5)
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
      - point.mass 5) + (point.mass 3 + point.mass 5)
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
      - point.mass 5) < (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 5) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5))
    (hdomRowTwo : (point.mass 2 + point.mass 5)
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
      - point.mass 5) + point.mass 5 * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 2 - point.mass 3 - point.mass 5)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 3 - point.mass 5) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5))
    (hdomRowThree : (point.mass 3 + point.mass 5)
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
      - point.mass 5) + point.mass 5 * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 2 - point.mass 3 - point.mass 5)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 3 - point.mass 5) * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 2 - point.mass 5)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 4}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 2 + point.mass 3
      + point.mass 5 < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 2 + point.mass 3 + point.mass 5)
          * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 3
            + point.mass 5) := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffOne : point.mass 1 + point.mass 2 + point.mass 5
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 2 + point.mass 5) * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 5)
            := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffFour : point.mass 4 + point.mass 3 + point.mass 5
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 3 + point.mass 5) * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 3 + point.mass 5)
            := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 3 - point.mass 5 := by linarith
  have hdiagTwoPos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 5 := by linarith
  have hdiagThreePos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 3 - point.mass 5 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 1, 4})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 0 - vecArg 2 ≠ 0
        ∨ vecArg 1 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 1, 4} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
          - point.mass 3 - point.mass 5) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
          - point.mass 5) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
          - point.mass 5) * (vecArg 1) ^ 2 + 2 * (point.mass 2
          + point.mass 5) * ((vecArg 0 - vecArg 1) * (vecArg 0 - vecArg 2))
          + 2 * (-(point.mass 3 + point.mass 5)) * ((vecArg 0 - vecArg 1)
          * (vecArg 1)) + 2 * point.mass 5 * ((vecArg 0 - vecArg 2)
          * (vecArg 1)) := by
      rw [kFourGap_treeZeroOneFour_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
        - point.mass 3 - point.mass 5)
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
        - point.mass 5)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
        - point.mass 5)
      (point.mass 2 + point.mass 5) (-(point.mass 3 + point.mass 5))
        (point.mass 5)
      (point.mass 2 + point.mass 5) (point.mass 3 + point.mass 5)
        (point.mass 5)
      (vecArg 0 - vecArg 1) (vecArg 0 - vecArg 2) (vecArg 1)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 2) (point.mass_pos 5)) (add_pos
        (point.mass_pos 3) (point.mass_pos 5)) (point.mass_pos 5)
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{0, 1, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `2` over `{0,1}`, edge `3` over `{1,5}`, edge `4` over `{0,1,5}`). -/
theorem kFourAtlas_harmonicZeroOneFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 2
      + point.mass 4) < point.mass 0)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 2
      + point.mass 3 + point.mass 4) < point.mass 1)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 3
      + point.mass 4) < point.mass 5)
    (hdomRowOne : (point.mass 2 + point.mass 4)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
      - point.mass 4) + point.mass 4 * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 2 - point.mass 3 - point.mass 4)
      < (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
      - point.mass 3 - point.mass 4) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4))
    (hdomRowTwo : (point.mass 2 + point.mass 4)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
      - point.mass 4) + (point.mass 3 + point.mass 4)
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 4) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 4) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4))
    (hdomRowThree : point.mass 4 * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 2 - point.mass 3 - point.mass 4)
      + (point.mass 3 + point.mass 4) * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 2 - point.mass 4)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 4) * (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 3 - point.mass 4)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 1, 5}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 2 + point.mass 4
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 2 + point.mass 4) * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 4)
            := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffOne : point.mass 1 + point.mass 2 + point.mass 3 + point.mass 4
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 2 + point.mass 3 + point.mass 4)
          * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 3
            + point.mass 4) := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffFive : point.mass 5 + point.mass 3 + point.mass 4
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 3 + point.mass 4) * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 3 + point.mass 4)
            := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 4 := by linarith
  have hdiagTwoPos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 3 - point.mass 4 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 3 - point.mass 4 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 1, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 0 - vecArg 2 ≠ 0
        ∨ vecArg 2 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 1, 5} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
          - point.mass 4) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
          - point.mass 3 - point.mass 4) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
          - point.mass 4) * (vecArg 2) ^ 2 + 2 * (point.mass 2
          + point.mass 4) * ((vecArg 0 - vecArg 1) * (vecArg 0 - vecArg 2))
          + 2 * point.mass 4 * ((vecArg 0 - vecArg 1) * (vecArg 2)) + 2
          * (-(point.mass 3 + point.mass 4)) * ((vecArg 0 - vecArg 2)
          * (vecArg 2)) := by
      rw [kFourGap_treeZeroOneFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
        - point.mass 4)
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
        - point.mass 3 - point.mass 4)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
        - point.mass 4)
      (point.mass 2 + point.mass 4) (point.mass 4) (-(point.mass 3
        + point.mass 4))
      (point.mass 2 + point.mass 4) (point.mass 4) (point.mass 3
        + point.mass 4)
      (vecArg 0 - vecArg 1) (vecArg 0 - vecArg 2) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 2) (point.mass_pos 4)) (point.mass_pos 4)
        (add_pos (point.mass_pos 3) (point.mass_pos 4))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{0, 2, 3}`** (scale-free Jacobi dominance;
off-tree cycles: edge `1` over `{0,2}`, edge `4` over `{0,3}`, edge `5` over `{0,2,3}`). -/
theorem kFourAtlas_harmonicZeroTwoThree_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 1
      + point.mass 4 + point.mass 5) < point.mass 0)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 1
      + point.mass 5) < point.mass 2)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 4
      + point.mass 5) < point.mass 3)
    (hdomRowOne : (point.mass 1 + point.mass 5)
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
      - point.mass 5) + (point.mass 4 + point.mass 5)
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
      - point.mass 5) < (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 5) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5))
    (hdomRowTwo : (point.mass 1 + point.mass 5)
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
      - point.mass 5) + point.mass 5 * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 1 - point.mass 4 - point.mass 5)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 4 - point.mass 5) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5))
    (hdomRowThree : (point.mass 4 + point.mass 5)
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
      - point.mass 5) + point.mass 5 * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 1 - point.mass 4 - point.mass 5)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 4 - point.mass 5) * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 1 - point.mass 5)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 3}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 1 + point.mass 4
      + point.mass 5 < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 1 + point.mass 4 + point.mass 5)
          * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 4
            + point.mass 5) := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffTwo : point.mass 2 + point.mass 1 + point.mass 5
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 1 + point.mass 5) * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 5)
            := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffThree : point.mass 3 + point.mass 4 + point.mass 5
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 4 + point.mass 5) * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 4 + point.mass 5)
            := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 4 - point.mass 5 := by linarith
  have hdiagTwoPos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 5 := by linarith
  have hdiagThreePos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 4 - point.mass 5 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 2, 3})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 0 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 2, 3} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
          - point.mass 4 - point.mass 5) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
          - point.mass 5) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
          - point.mass 5) * (vecArg 0) ^ 2 + 2 * (-(point.mass 1
          + point.mass 5)) * ((vecArg 0 - vecArg 1) * (vecArg 1 - vecArg 2))
          + 2 * (point.mass 4 + point.mass 5) * ((vecArg 0 - vecArg 1)
          * (vecArg 0)) + 2 * point.mass 5 * ((vecArg 1 - vecArg 2)
          * (vecArg 0)) := by
      rw [kFourGap_treeZeroTwoThree_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
        - point.mass 4 - point.mass 5)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
        - point.mass 5)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
        - point.mass 5)
      (-(point.mass 1 + point.mass 5)) (point.mass 4 + point.mass 5)
        (point.mass 5)
      (point.mass 1 + point.mass 5) (point.mass 4 + point.mass 5)
        (point.mass 5)
      (vecArg 0 - vecArg 1) (vecArg 1 - vecArg 2) (vecArg 0)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 1) (point.mass_pos 5)) (add_pos
        (point.mass_pos 4) (point.mass_pos 5)) (point.mass_pos 5)
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{0, 2, 4}`** (scale-free Jacobi dominance;
off-tree cycles: edge `1` over `{0,2}`, edge `3` over `{0,4}`, edge `5` over `{2,4}`). -/
theorem kFourAtlas_harmonicZeroTwoFour_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 1
      + point.mass 3) < point.mass 0)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 1
      + point.mass 5) < point.mass 2)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 3
      + point.mass 5) < point.mass 4)
    (hdomRowOne : point.mass 1 * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5) + point.mass 3
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
      - point.mass 5) < (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 5) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5))
    (hdomRowTwo : point.mass 1 * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5) + point.mass 5
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 3) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 3) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5))
    (hdomRowThree : point.mass 3 * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 1 - point.mass 5) + point.mass 5
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 3) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 3) * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 1 - point.mass 5)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 4}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 1 + point.mass 3
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 1 + point.mass 3) * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 3)
            := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffTwo : point.mass 2 + point.mass 1 + point.mass 5
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 1 + point.mass 5) * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 5)
            := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffFour : point.mass 4 + point.mass 3 + point.mass 5
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 3 + point.mass 5) * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 3 + point.mass 5)
            := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 3 := by linarith
  have hdiagTwoPos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 5 := by linarith
  have hdiagThreePos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 3 - point.mass 5 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 2, 4})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 1 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 2, 4} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
          - point.mass 3) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
          - point.mass 5) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
          - point.mass 5) * (vecArg 1) ^ 2 + 2 * (-point.mass 1)
          * ((vecArg 0 - vecArg 1) * (vecArg 1 - vecArg 2)) + 2
          * (-point.mass 3) * ((vecArg 0 - vecArg 1) * (vecArg 1)) + 2
          * point.mass 5 * ((vecArg 1 - vecArg 2) * (vecArg 1)) := by
      rw [kFourGap_treeZeroTwoFour_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
        - point.mass 3)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
        - point.mass 5)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
        - point.mass 5)
      (-point.mass 1) (-point.mass 3) (point.mass 5)
      (point.mass 1) (point.mass 3) (point.mass 5)
      (vecArg 0 - vecArg 1) (vecArg 1 - vecArg 2) (vecArg 1)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (point.mass_pos 1) (point.mass_pos 3) (point.mass_pos 5)
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{0, 2, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `1` over `{0,2}`, edge `3` over `{0,2,5}`, edge `4` over `{2,5}`). -/
theorem kFourAtlas_harmonicZeroTwoFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 1
      + point.mass 3) < point.mass 0)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 1
      + point.mass 3 + point.mass 4) < point.mass 2)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 3
      + point.mass 4) < point.mass 5)
    (hdomRowOne : (point.mass 1 + point.mass 3)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
      - point.mass 4) + point.mass 3 * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 1 - point.mass 3 - point.mass 4)
      < (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
      - point.mass 3 - point.mass 4) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4))
    (hdomRowTwo : (point.mass 1 + point.mass 3)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
      - point.mass 4) + (point.mass 3 + point.mass 4)
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 3) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 3) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4))
    (hdomRowThree : point.mass 3 * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 1 - point.mass 3 - point.mass 4)
      + (point.mass 3 + point.mass 4) * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 1 - point.mass 3)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 3) * (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 3 - point.mass 4)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 2, 5}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 1 + point.mass 3
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 1 + point.mass 3) * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 3)
            := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffTwo : point.mass 2 + point.mass 1 + point.mass 3 + point.mass 4
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 1 + point.mass 3 + point.mass 4)
          * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 3
            + point.mass 4) := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffFive : point.mass 5 + point.mass 3 + point.mass 4
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 3 + point.mass 4) * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 3 + point.mass 4)
            := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 3 := by linarith
  have hdiagTwoPos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 3 - point.mass 4 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 3 - point.mass 4 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 2, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 2 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 2, 5} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
          - point.mass 3) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
          - point.mass 3 - point.mass 4) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
          - point.mass 4) * (vecArg 2) ^ 2 + 2 * (-(point.mass 1
          + point.mass 3)) * ((vecArg 0 - vecArg 1) * (vecArg 1 - vecArg 2))
          + 2 * (-point.mass 3) * ((vecArg 0 - vecArg 1) * (vecArg 2)) + 2
          * (-(point.mass 3 + point.mass 4)) * ((vecArg 1 - vecArg 2)
          * (vecArg 2)) := by
      rw [kFourGap_treeZeroTwoFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
        - point.mass 3)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
        - point.mass 3 - point.mass 4)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
        - point.mass 4)
      (-(point.mass 1 + point.mass 3)) (-point.mass 3) (-(point.mass 3
        + point.mass 4))
      (point.mass 1 + point.mass 3) (point.mass 3) (point.mass 3
        + point.mass 4)
      (vecArg 0 - vecArg 1) (vecArg 1 - vecArg 2) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 1) (point.mass_pos 3)) (point.mass_pos 3)
        (add_pos (point.mass_pos 3) (point.mass_pos 4))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{0, 3, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `1` over `{3,5}`, edge `2` over `{0,3,5}`, edge `4` over `{0,3}`). -/
theorem kFourAtlas_harmonicZeroThreeFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 2
      + point.mass 4) < point.mass 0)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 1
      + point.mass 2 + point.mass 4) < point.mass 3)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 1
      + point.mass 2) < point.mass 5)
    (hdomRowOne : (point.mass 2 + point.mass 4)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
      - point.mass 2) + point.mass 2 * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 1 - point.mass 2 - point.mass 4)
      < (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 1
      - point.mass 2 - point.mass 4) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2))
    (hdomRowTwo : (point.mass 2 + point.mass 4)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
      - point.mass 2) + (point.mass 1 + point.mass 2)
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 4) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 4) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2))
    (hdomRowThree : point.mass 2 * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 1 - point.mass 2 - point.mass 4)
      + (point.mass 1 + point.mass 2) * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 2 - point.mass 4)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
      - point.mass 4) * (point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 1 - point.mass 2 - point.mass 4)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 3, 5}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 2 + point.mass 4
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 2 + point.mass 4) * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 4)
            := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffThree : point.mass 3 + point.mass 1 + point.mass 2
      + point.mass 4 < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 1 + point.mass 2 + point.mass 4)
          * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 1 + point.mass 2
            + point.mass 4) := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hcoeffFive : point.mass 5 + point.mass 1 + point.mass 2
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 1 + point.mass 2) * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 1 + point.mass 2)
            := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 2 - point.mass 4 := by linarith
  have hdiagTwoPos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 1 - point.mass 2 - point.mass 4 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 1 - point.mass 2 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 3, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 0 ≠ 0 ∨ vecArg 2 ≠ 0
        := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 3, 5} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
          - point.mass 4) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 1
          - point.mass 2 - point.mass 4) * (vecArg 0) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
          - point.mass 2) * (vecArg 2) ^ 2 + 2 * (point.mass 2
          + point.mass 4) * ((vecArg 0 - vecArg 1) * (vecArg 0)) + 2
          * (-point.mass 2) * ((vecArg 0 - vecArg 1) * (vecArg 2)) + 2
          * (point.mass 1 + point.mass 2) * ((vecArg 0) * (vecArg 2)) := by
      rw [kFourGap_treeZeroThreeFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
        - point.mass 4)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 1
        - point.mass 2 - point.mass 4)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
        - point.mass 2)
      (point.mass 2 + point.mass 4) (-point.mass 2) (point.mass 1
        + point.mass 2)
      (point.mass 2 + point.mass 4) (point.mass 2) (point.mass 1
        + point.mass 2)
      (vecArg 0 - vecArg 1) (vecArg 0) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 2) (point.mass_pos 4)) (point.mass_pos 2)
        (add_pos (point.mass_pos 1) (point.mass_pos 2))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{0, 4, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `1` over `{0,4,5}`, edge `2` over `{4,5}`, edge `3` over `{0,4}`). -/
theorem kFourAtlas_harmonicZeroFourFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeZero : point.weight 0 * (point.mass 0 + point.mass 1
      + point.mass 3) < point.mass 0)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 1
      + point.mass 2 + point.mass 3) < point.mass 4)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 1
      + point.mass 2) < point.mass 5)
    (hdomRowOne : (point.mass 1 + point.mass 3)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
      - point.mass 2) + point.mass 1 * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 1 - point.mass 2 - point.mass 3)
      < (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 1
      - point.mass 2 - point.mass 3) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2))
    (hdomRowTwo : (point.mass 1 + point.mass 3)
      * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
      - point.mass 2) + (point.mass 1 + point.mass 2)
      * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 3) < (point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 3) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2))
    (hdomRowThree : point.mass 1 * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 1 - point.mass 2 - point.mass 3)
      + (point.mass 1 + point.mass 2) * (point.mass 0 / point.weight 0
      - point.mass 0 - point.mass 1 - point.mass 3)
      < (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
      - point.mass 3) * (point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 1 - point.mass 2 - point.mass 3)) :
    (directionChartGap kFourDirection point.mass point.weight
      {0, 4, 5}).PosDef := by
  have hcoeffZero : point.mass 0 + point.mass 1 + point.mass 3
      < point.mass 0 / point.weight 0 := by
    rw [lt_div_iff₀ (point.weight_pos 0)]
    calc (point.mass 0 + point.mass 1 + point.mass 3) * point.weight 0
        = point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 3)
            := by ring
      _ < point.mass 0 := hdiagEdgeZero
  have hcoeffFour : point.mass 4 + point.mass 1 + point.mass 2
      + point.mass 3 < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 1 + point.mass 2 + point.mass 3)
          * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 1 + point.mass 2
            + point.mass 3) := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hcoeffFive : point.mass 5 + point.mass 1 + point.mass 2
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 1 + point.mass 2) * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 1 + point.mass 2)
            := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 0 / point.weight 0 - point.mass 0
      - point.mass 1 - point.mass 3 := by linarith
  have hdiagTwoPos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 1 - point.mass 2 - point.mass 3 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 1 - point.mass 2 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {0, 4, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 1 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0
        := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {0, 4, 5} *ᵥ vecArg)
        = (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
          - point.mass 3) * (vecArg 0 - vecArg 1) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 1
          - point.mass 2 - point.mass 3) * (vecArg 1) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
          - point.mass 2) * (vecArg 2) ^ 2 + 2 * (-(point.mass 1
          + point.mass 3)) * ((vecArg 0 - vecArg 1) * (vecArg 1)) + 2
          * point.mass 1 * ((vecArg 0 - vecArg 1) * (vecArg 2)) + 2
          * (point.mass 1 + point.mass 2) * ((vecArg 1) * (vecArg 2)) := by
      rw [kFourGap_treeZeroFourFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
        - point.mass 3)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 1
        - point.mass 2 - point.mass 3)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
        - point.mass 2)
      (-(point.mass 1 + point.mass 3)) (point.mass 1) (point.mass 1
        + point.mass 2)
      (point.mass 1 + point.mass 3) (point.mass 1) (point.mass 1
        + point.mass 2)
      (vecArg 0 - vecArg 1) (vecArg 1) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 1) (point.mass_pos 3)) (point.mass_pos 1)
        (add_pos (point.mass_pos 1) (point.mass_pos 2))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{1, 2, 3}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{1,2}`, edge `4` over `{1,2,3}`, edge `5` over `{1,3}`). -/
theorem kFourAtlas_harmonicOneTwoThree_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 0
      + point.mass 4 + point.mass 5) < point.mass 1)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 0
      + point.mass 4) < point.mass 2)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 4
      + point.mass 5) < point.mass 3)
    (hdomRowOne : (point.mass 0 + point.mass 4)
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
      - point.mass 5) + (point.mass 4 + point.mass 5)
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
      - point.mass 4) < (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 4) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5))
    (hdomRowTwo : (point.mass 0 + point.mass 4)
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
      - point.mass 5) + point.mass 4 * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 0 - point.mass 4 - point.mass 5)
      < (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 4 - point.mass 5) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 4 - point.mass 5))
    (hdomRowThree : (point.mass 4 + point.mass 5)
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
      - point.mass 4) + point.mass 4 * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 0 - point.mass 4 - point.mass 5)
      < (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 4 - point.mass 5) * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 0 - point.mass 4)) :
    (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 3}).PosDef := by
  have hcoeffOne : point.mass 1 + point.mass 0 + point.mass 4 + point.mass 5
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 0 + point.mass 4 + point.mass 5)
          * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 4
            + point.mass 5) := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffTwo : point.mass 2 + point.mass 0 + point.mass 4
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 0 + point.mass 4) * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 4)
            := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffThree : point.mass 3 + point.mass 4 + point.mass 5
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 4 + point.mass 5) * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 4 + point.mass 5)
            := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hdiagOnePos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 4 - point.mass 5 := by linarith
  have hdiagTwoPos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 4 := by linarith
  have hdiagThreePos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 4 - point.mass 5 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {1, 2, 3})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 2 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 0 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {1, 2, 3} *ᵥ vecArg)
        = (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
          - point.mass 4 - point.mass 5) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
          - point.mass 4) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
          - point.mass 5) * (vecArg 0) ^ 2 + 2 * (point.mass 0
          + point.mass 4) * ((vecArg 0 - vecArg 2) * (vecArg 1 - vecArg 2))
          + 2 * (point.mass 4 + point.mass 5) * ((vecArg 0 - vecArg 2)
          * (vecArg 0)) + 2 * (-point.mass 4) * ((vecArg 1 - vecArg 2)
          * (vecArg 0)) := by
      rw [kFourGap_treeOneTwoThree_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
        - point.mass 4 - point.mass 5)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
        - point.mass 4)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
        - point.mass 5)
      (point.mass 0 + point.mass 4) (point.mass 4 + point.mass 5)
        (-point.mass 4)
      (point.mass 0 + point.mass 4) (point.mass 4 + point.mass 5)
        (point.mass 4)
      (vecArg 0 - vecArg 2) (vecArg 1 - vecArg 2) (vecArg 0)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 0) (point.mass_pos 4)) (add_pos
        (point.mass_pos 4) (point.mass_pos 5)) (point.mass_pos 4)
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{1, 2, 4}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{1,2}`, edge `3` over `{1,2,4}`, edge `5` over `{2,4}`). -/
theorem kFourAtlas_harmonicOneTwoFour_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 0
      + point.mass 3) < point.mass 1)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 0
      + point.mass 3 + point.mass 5) < point.mass 2)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 3
      + point.mass 5) < point.mass 4)
    (hdomRowOne : (point.mass 0 + point.mass 3)
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
      - point.mass 5) + point.mass 3 * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 0 - point.mass 3 - point.mass 5)
      < (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
      - point.mass 3 - point.mass 5) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5))
    (hdomRowTwo : (point.mass 0 + point.mass 3)
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
      - point.mass 5) + (point.mass 3 + point.mass 5)
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 3) < (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 3) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 3 - point.mass 5))
    (hdomRowThree : point.mass 3 * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 0 - point.mass 3 - point.mass 5)
      + (point.mass 3 + point.mass 5) * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 0 - point.mass 3)
      < (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 3) * (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 3 - point.mass 5)) :
    (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 4}).PosDef := by
  have hcoeffOne : point.mass 1 + point.mass 0 + point.mass 3
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 0 + point.mass 3) * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 3)
            := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffTwo : point.mass 2 + point.mass 0 + point.mass 3 + point.mass 5
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 0 + point.mass 3 + point.mass 5)
          * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 3
            + point.mass 5) := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffFour : point.mass 4 + point.mass 3 + point.mass 5
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 3 + point.mass 5) * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 3 + point.mass 5)
            := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hdiagOnePos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 3 := by linarith
  have hdiagTwoPos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 3 - point.mass 5 := by linarith
  have hdiagThreePos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 3 - point.mass 5 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {1, 2, 4})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 2 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 1 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {1, 2, 4} *ᵥ vecArg)
        = (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
          - point.mass 3) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
          - point.mass 3 - point.mass 5) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
          - point.mass 5) * (vecArg 1) ^ 2 + 2 * (point.mass 0
          + point.mass 3) * ((vecArg 0 - vecArg 2) * (vecArg 1 - vecArg 2))
          + 2 * (-point.mass 3) * ((vecArg 0 - vecArg 2) * (vecArg 1)) + 2
          * (point.mass 3 + point.mass 5) * ((vecArg 1 - vecArg 2)
          * (vecArg 1)) := by
      rw [kFourGap_treeOneTwoFour_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
        - point.mass 3)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
        - point.mass 3 - point.mass 5)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
        - point.mass 5)
      (point.mass 0 + point.mass 3) (-point.mass 3) (point.mass 3
        + point.mass 5)
      (point.mass 0 + point.mass 3) (point.mass 3) (point.mass 3
        + point.mass 5)
      (vecArg 0 - vecArg 2) (vecArg 1 - vecArg 2) (vecArg 1)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 0) (point.mass_pos 3)) (point.mass_pos 3)
        (add_pos (point.mass_pos 3) (point.mass_pos 5))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{1, 2, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{1,2}`, edge `3` over `{1,5}`, edge `4` over `{2,5}`). -/
theorem kFourAtlas_harmonicOneTwoFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 0
      + point.mass 3) < point.mass 1)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 0
      + point.mass 4) < point.mass 2)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 3
      + point.mass 4) < point.mass 5)
    (hdomRowOne : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4) + point.mass 3
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
      - point.mass 4) < (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 4) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4))
    (hdomRowTwo : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4) + point.mass 4
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 3) < (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 3) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 3 - point.mass 4))
    (hdomRowThree : point.mass 3 * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 0 - point.mass 4) + point.mass 4
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 3) < (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 3) * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 0 - point.mass 4)) :
    (directionChartGap kFourDirection point.mass point.weight
      {1, 2, 5}).PosDef := by
  have hcoeffOne : point.mass 1 + point.mass 0 + point.mass 3
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 0 + point.mass 3) * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 3)
            := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffTwo : point.mass 2 + point.mass 0 + point.mass 4
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 0 + point.mass 4) * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 4)
            := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffFive : point.mass 5 + point.mass 3 + point.mass 4
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 3 + point.mass 4) * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 3 + point.mass 4)
            := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 3 := by linarith
  have hdiagTwoPos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 4 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 3 - point.mass 4 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {1, 2, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 2 ≠ 0 ∨ vecArg 1 - vecArg 2 ≠ 0
        ∨ vecArg 2 ≠ 0 := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {1, 2, 5} *ᵥ vecArg)
        = (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
          - point.mass 3) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
          - point.mass 4) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
          - point.mass 4) * (vecArg 2) ^ 2 + 2 * point.mass 0 * ((vecArg 0
          - vecArg 2) * (vecArg 1 - vecArg 2)) + 2 * (-point.mass 3)
          * ((vecArg 0 - vecArg 2) * (vecArg 2)) + 2 * (-point.mass 4)
          * ((vecArg 1 - vecArg 2) * (vecArg 2)) := by
      rw [kFourGap_treeOneTwoFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
        - point.mass 3)
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
        - point.mass 4)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
        - point.mass 4)
      (point.mass 0) (-point.mass 3) (-point.mass 4)
      (point.mass 0) (point.mass 3) (point.mass 4)
      (vecArg 0 - vecArg 2) (vecArg 1 - vecArg 2) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (point.mass_pos 0) (point.mass_pos 3) (point.mass_pos 4)
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{1, 3, 4}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{3,4}`, edge `2` over `{1,3,4}`, edge `5` over `{1,3}`). -/
theorem kFourAtlas_harmonicOneThreeFour_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 2
      + point.mass 5) < point.mass 1)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 0
      + point.mass 2 + point.mass 5) < point.mass 3)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 0
      + point.mass 2) < point.mass 4)
    (hdomRowOne : (point.mass 2 + point.mass 5)
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
      - point.mass 2) + point.mass 2 * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 0 - point.mass 2 - point.mass 5)
      < (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
      - point.mass 2 - point.mass 5) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 2))
    (hdomRowTwo : (point.mass 2 + point.mass 5)
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
      - point.mass 2) + (point.mass 0 + point.mass 2)
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
      - point.mass 5) < (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 5) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 2))
    (hdomRowThree : point.mass 2 * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 0 - point.mass 2 - point.mass 5)
      + (point.mass 0 + point.mass 2) * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 2 - point.mass 5)
      < (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
      - point.mass 5) * (point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 0 - point.mass 2 - point.mass 5)) :
    (directionChartGap kFourDirection point.mass point.weight
      {1, 3, 4}).PosDef := by
  have hcoeffOne : point.mass 1 + point.mass 2 + point.mass 5
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 2 + point.mass 5) * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 5)
            := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffThree : point.mass 3 + point.mass 0 + point.mass 2
      + point.mass 5 < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 0 + point.mass 2 + point.mass 5)
          * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 2
            + point.mass 5) := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hcoeffFour : point.mass 4 + point.mass 0 + point.mass 2
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 0 + point.mass 2) * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 2)
            := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hdiagOnePos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 2 - point.mass 5 := by linarith
  have hdiagTwoPos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 0 - point.mass 2 - point.mass 5 := by linarith
  have hdiagThreePos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 0 - point.mass 2 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {1, 3, 4})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 2 ≠ 0 ∨ vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0
        := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {1, 3, 4} *ᵥ vecArg)
        = (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
          - point.mass 5) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
          - point.mass 2 - point.mass 5) * (vecArg 0) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
          - point.mass 2) * (vecArg 1) ^ 2 + 2 * (point.mass 2
          + point.mass 5) * ((vecArg 0 - vecArg 2) * (vecArg 0)) + 2
          * (-point.mass 2) * ((vecArg 0 - vecArg 2) * (vecArg 1)) + 2
          * (point.mass 0 + point.mass 2) * ((vecArg 0) * (vecArg 1)) := by
      rw [kFourGap_treeOneThreeFour_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
        - point.mass 5)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
        - point.mass 2 - point.mass 5)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
        - point.mass 2)
      (point.mass 2 + point.mass 5) (-point.mass 2) (point.mass 0
        + point.mass 2)
      (point.mass 2 + point.mass 5) (point.mass 2) (point.mass 0
        + point.mass 2)
      (vecArg 0 - vecArg 2) (vecArg 0) (vecArg 1)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (add_pos (point.mass_pos 2) (point.mass_pos 5)) (point.mass_pos 2)
        (add_pos (point.mass_pos 0) (point.mass_pos 2))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{1, 4, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{1,4,5}`, edge `2` over `{4,5}`, edge `3` over `{1,5}`). -/
theorem kFourAtlas_harmonicOneFourFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeOne : point.weight 1 * (point.mass 1 + point.mass 0
      + point.mass 3) < point.mass 1)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 0
      + point.mass 2) < point.mass 4)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 0
      + point.mass 2 + point.mass 3) < point.mass 5)
    (hdomRowOne : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 0 - point.mass 2 - point.mass 3)
      + (point.mass 0 + point.mass 3) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 2)
      < (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
      - point.mass 2) * (point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 0 - point.mass 2 - point.mass 3))
    (hdomRowTwo : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 0 - point.mass 2 - point.mass 3)
      + (point.mass 0 + point.mass 2) * (point.mass 1 / point.weight 1
      - point.mass 1 - point.mass 0 - point.mass 3)
      < (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 3) * (point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 0 - point.mass 2 - point.mass 3))
    (hdomRowThree : (point.mass 0 + point.mass 3)
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
      - point.mass 2) + (point.mass 0 + point.mass 2)
      * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
      - point.mass 3) < (point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 3) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 2)) :
    (directionChartGap kFourDirection point.mass point.weight
      {1, 4, 5}).PosDef := by
  have hcoeffOne : point.mass 1 + point.mass 0 + point.mass 3
      < point.mass 1 / point.weight 1 := by
    rw [lt_div_iff₀ (point.weight_pos 1)]
    calc (point.mass 1 + point.mass 0 + point.mass 3) * point.weight 1
        = point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 3)
            := by ring
      _ < point.mass 1 := hdiagEdgeOne
  have hcoeffFour : point.mass 4 + point.mass 0 + point.mass 2
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 0 + point.mass 2) * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 2)
            := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hcoeffFive : point.mass 5 + point.mass 0 + point.mass 2
      + point.mass 3 < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 0 + point.mass 2 + point.mass 3)
          * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 0 + point.mass 2
            + point.mass 3) := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 1 / point.weight 1 - point.mass 1
      - point.mass 0 - point.mass 3 := by linarith
  have hdiagTwoPos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 0 - point.mass 2 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 0 - point.mass 2 - point.mass 3 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {1, 4, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 0 - vecArg 2 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0
        := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueZero : vecArg 0 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {1, 4, 5} *ᵥ vecArg)
        = (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
          - point.mass 3) * (vecArg 0 - vecArg 2) ^ 2
          + (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
          - point.mass 2) * (vecArg 1) ^ 2 + (point.mass 5 / point.weight 5
          - point.mass 5 - point.mass 0 - point.mass 2 - point.mass 3)
          * (vecArg 2) ^ 2 + 2 * point.mass 0 * ((vecArg 0 - vecArg 2)
          * (vecArg 1)) + 2 * (-(point.mass 0 + point.mass 3)) * ((vecArg 0
          - vecArg 2) * (vecArg 2)) + 2 * (point.mass 0 + point.mass 2)
          * ((vecArg 1) * (vecArg 2)) := by
      rw [kFourGap_treeOneFourFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
        - point.mass 3)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
        - point.mass 2)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 0
        - point.mass 2 - point.mass 3)
      (point.mass 0) (-(point.mass 0 + point.mass 3)) (point.mass 0
        + point.mass 2)
      (point.mass 0) (point.mass 0 + point.mass 3) (point.mass 0
        + point.mass 2)
      (vecArg 0 - vecArg 2) (vecArg 1) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (point.mass_pos 0) (add_pos (point.mass_pos 0) (point.mass_pos 3))
        (add_pos (point.mass_pos 0) (point.mass_pos 2))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{2, 3, 4}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{3,4}`, edge `1` over `{2,3,4}`, edge `5` over `{2,4}`). -/
theorem kFourAtlas_harmonicTwoThreeFour_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 1
      + point.mass 5) < point.mass 2)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 0
      + point.mass 1) < point.mass 3)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 0
      + point.mass 1 + point.mass 5) < point.mass 4)
    (hdomRowOne : point.mass 1 * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 1 - point.mass 5)
      + (point.mass 1 + point.mass 5) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 0 - point.mass 1)
      < (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
      - point.mass 1) * (point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 0 - point.mass 1 - point.mass 5))
    (hdomRowTwo : point.mass 1 * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 1 - point.mass 5)
      + (point.mass 0 + point.mass 1) * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 1 - point.mass 5)
      < (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
      - point.mass 5) * (point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 0 - point.mass 1 - point.mass 5))
    (hdomRowThree : (point.mass 1 + point.mass 5)
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
      - point.mass 1) + (point.mass 0 + point.mass 1)
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
      - point.mass 5) < (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 5) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 0 - point.mass 1)) :
    (directionChartGap kFourDirection point.mass point.weight
      {2, 3, 4}).PosDef := by
  have hcoeffTwo : point.mass 2 + point.mass 1 + point.mass 5
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 1 + point.mass 5) * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 5)
            := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffThree : point.mass 3 + point.mass 0 + point.mass 1
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 0 + point.mass 1) * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 1)
            := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hcoeffFour : point.mass 4 + point.mass 0 + point.mass 1
      + point.mass 5 < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 0 + point.mass 1 + point.mass 5)
          * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 1
            + point.mass 5) := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hdiagOnePos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 1 - point.mass 5 := by linarith
  have hdiagTwoPos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 0 - point.mass 1 := by linarith
  have hdiagThreePos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 0 - point.mass 1 - point.mass 5 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {2, 3, 4})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 1 - vecArg 2 ≠ 0 ∨ vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0
        := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {2, 3, 4} *ᵥ vecArg)
        = (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
          - point.mass 5) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
          - point.mass 1) * (vecArg 0) ^ 2 + (point.mass 4 / point.weight 4
          - point.mass 4 - point.mass 0 - point.mass 1 - point.mass 5)
          * (vecArg 1) ^ 2 + 2 * (-point.mass 1) * ((vecArg 1 - vecArg 2)
          * (vecArg 0)) + 2 * (point.mass 1 + point.mass 5) * ((vecArg 1
          - vecArg 2) * (vecArg 1)) + 2 * (point.mass 0 + point.mass 1)
          * ((vecArg 0) * (vecArg 1)) := by
      rw [kFourGap_treeTwoThreeFour_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
        - point.mass 5)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
        - point.mass 1)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
        - point.mass 1 - point.mass 5)
      (-point.mass 1) (point.mass 1 + point.mass 5) (point.mass 0
        + point.mass 1)
      (point.mass 1) (point.mass 1 + point.mass 5) (point.mass 0
        + point.mass 1)
      (vecArg 1 - vecArg 2) (vecArg 0) (vecArg 1)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (point.mass_pos 1) (add_pos (point.mass_pos 1) (point.mass_pos 5))
        (add_pos (point.mass_pos 0) (point.mass_pos 1))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{2, 3, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{2,3,5}`, edge `1` over `{3,5}`, edge `4` over `{2,5}`). -/
theorem kFourAtlas_harmonicTwoThreeFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeTwo : point.weight 2 * (point.mass 2 + point.mass 0
      + point.mass 4) < point.mass 2)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 0
      + point.mass 1) < point.mass 3)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 0
      + point.mass 1 + point.mass 4) < point.mass 5)
    (hdomRowOne : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 0 - point.mass 1 - point.mass 4)
      + (point.mass 0 + point.mass 4) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 0 - point.mass 1)
      < (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
      - point.mass 1) * (point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 0 - point.mass 1 - point.mass 4))
    (hdomRowTwo : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 0 - point.mass 1 - point.mass 4)
      + (point.mass 0 + point.mass 1) * (point.mass 2 / point.weight 2
      - point.mass 2 - point.mass 0 - point.mass 4)
      < (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
      - point.mass 4) * (point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 0 - point.mass 1 - point.mass 4))
    (hdomRowThree : (point.mass 0 + point.mass 4)
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
      - point.mass 1) + (point.mass 0 + point.mass 1)
      * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
      - point.mass 4) < (point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 4) * (point.mass 3 / point.weight 3
      - point.mass 3 - point.mass 0 - point.mass 1)) :
    (directionChartGap kFourDirection point.mass point.weight
      {2, 3, 5}).PosDef := by
  have hcoeffTwo : point.mass 2 + point.mass 0 + point.mass 4
      < point.mass 2 / point.weight 2 := by
    rw [lt_div_iff₀ (point.weight_pos 2)]
    calc (point.mass 2 + point.mass 0 + point.mass 4) * point.weight 2
        = point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 4)
            := by ring
      _ < point.mass 2 := hdiagEdgeTwo
  have hcoeffThree : point.mass 3 + point.mass 0 + point.mass 1
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 0 + point.mass 1) * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 1)
            := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hcoeffFive : point.mass 5 + point.mass 0 + point.mass 1
      + point.mass 4 < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 0 + point.mass 1 + point.mass 4)
          * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 0 + point.mass 1
            + point.mass 4) := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 2 / point.weight 2 - point.mass 2
      - point.mass 0 - point.mass 4 := by linarith
  have hdiagTwoPos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 0 - point.mass 1 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 0 - point.mass 1 - point.mass 4 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {2, 3, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hzNonzero : vecArg 1 - vecArg 2 ≠ 0 ∨ vecArg 0 ≠ 0 ∨ vecArg 2 ≠ 0
        := by
      by_contra hallCycleZero
      push Not at hallCycleZero
      obtain ⟨hcycleOne, hcycleTwo, hcycleThree⟩ := hallCycleZero
      have hvalueZero : vecArg 0 = 0 := by linarith
      have hvalueTwo : vecArg 2 = 0 := by linarith
      have hvalueOne : vecArg 1 = 0 := by linarith
      rcases hsomeCoordinateNonzero with hbad | hbad | hbad
      · exact hbad hvalueZero
      · exact hbad hvalueOne
      · exact hbad hvalueTwo
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {2, 3, 5} *ᵥ vecArg)
        = (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
          - point.mass 4) * (vecArg 1 - vecArg 2) ^ 2
          + (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
          - point.mass 1) * (vecArg 0) ^ 2 + (point.mass 5 / point.weight 5
          - point.mass 5 - point.mass 0 - point.mass 1 - point.mass 4)
          * (vecArg 2) ^ 2 + 2 * point.mass 0 * ((vecArg 1 - vecArg 2)
          * (vecArg 0)) + 2 * (-(point.mass 0 + point.mass 4)) * ((vecArg 1
          - vecArg 2) * (vecArg 2)) + 2 * (point.mass 0 + point.mass 1)
          * ((vecArg 0) * (vecArg 2)) := by
      rw [kFourGap_treeTwoThreeFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
        - point.mass 4)
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
        - point.mass 1)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 0
        - point.mass 1 - point.mass 4)
      (point.mass 0) (-(point.mass 0 + point.mass 4)) (point.mass 0
        + point.mass 1)
      (point.mass 0) (point.mass 0 + point.mass 4) (point.mass 0
        + point.mass 1)
      (vecArg 1 - vecArg 2) (vecArg 0) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (point.mass_pos 0) (add_pos (point.mass_pos 0) (point.mass_pos 4))
        (add_pos (point.mass_pos 0) (point.mass_pos 1))
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hzNonzero

/-- **Harmonic cell on tree `{3, 4, 5}`** (scale-free Jacobi dominance;
off-tree cycles: edge `0` over `{3,4}`, edge `1` over `{3,5}`, edge `2` over `{4,5}`). -/
theorem kFourAtlas_harmonicThreeFourFive_posDef_of_cell
    (point : DirectionChartPoint 6)
    (hdiagEdgeThree : point.weight 3 * (point.mass 3 + point.mass 0
      + point.mass 1) < point.mass 3)
    (hdiagEdgeFour : point.weight 4 * (point.mass 4 + point.mass 0
      + point.mass 2) < point.mass 4)
    (hdiagEdgeFive : point.weight 5 * (point.mass 5 + point.mass 1
      + point.mass 2) < point.mass 5)
    (hdomRowOne : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2) + point.mass 1
      * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
      - point.mass 2) < (point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 0 - point.mass 2) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2))
    (hdomRowTwo : point.mass 0 * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2) + point.mass 2
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
      - point.mass 1) < (point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 0 - point.mass 1) * (point.mass 5 / point.weight 5
      - point.mass 5 - point.mass 1 - point.mass 2))
    (hdomRowThree : point.mass 1 * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 2) + point.mass 2
      * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
      - point.mass 1) < (point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 0 - point.mass 1) * (point.mass 4 / point.weight 4
      - point.mass 4 - point.mass 0 - point.mass 2)) :
    (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).PosDef := by
  have hcoeffThree : point.mass 3 + point.mass 0 + point.mass 1
      < point.mass 3 / point.weight 3 := by
    rw [lt_div_iff₀ (point.weight_pos 3)]
    calc (point.mass 3 + point.mass 0 + point.mass 1) * point.weight 3
        = point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 1)
            := by ring
      _ < point.mass 3 := hdiagEdgeThree
  have hcoeffFour : point.mass 4 + point.mass 0 + point.mass 2
      < point.mass 4 / point.weight 4 := by
    rw [lt_div_iff₀ (point.weight_pos 4)]
    calc (point.mass 4 + point.mass 0 + point.mass 2) * point.weight 4
        = point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 2)
            := by ring
      _ < point.mass 4 := hdiagEdgeFour
  have hcoeffFive : point.mass 5 + point.mass 1 + point.mass 2
      < point.mass 5 / point.weight 5 := by
    rw [lt_div_iff₀ (point.weight_pos 5)]
    calc (point.mass 5 + point.mass 1 + point.mass 2) * point.weight 5
        = point.weight 5 * (point.mass 5 + point.mass 1 + point.mass 2)
            := by ring
      _ < point.mass 5 := hdiagEdgeFive
  have hdiagOnePos : 0 < point.mass 3 / point.weight 3 - point.mass 3
      - point.mass 0 - point.mass 1 := by linarith
  have hdiagTwoPos : 0 < point.mass 4 / point.weight 4 - point.mass 4
      - point.mass 0 - point.mass 2 := by linarith
  have hdiagThreePos : 0 < point.mass 5 / point.weight 5 - point.mass 5
      - point.mass 1 - point.mass 2 := by linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose kFourDirection point.mass point.weight
        {3, 4, 5})
  · rw [star_trivial]
    have hsomeCoordinateNonzero :
        vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hallZero
      push Not at hallZero
      obtain ⟨hzeroFirst, hzeroSecond, hzeroThird⟩ := hallZero
      apply hne
      funext index
      fin_cases index
      · exact hzeroFirst
      · exact hzeroSecond
      · exact hzeroThird
    have hform : vecArg ⬝ᵥ (directionChartGap kFourDirection point.mass
          point.weight {3, 4, 5} *ᵥ vecArg)
        = (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
          - point.mass 1) * (vecArg 0) ^ 2 + (point.mass 4 / point.weight 4
          - point.mass 4 - point.mass 0 - point.mass 2) * (vecArg 1) ^ 2
          + (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
          - point.mass 2) * (vecArg 2) ^ 2 + 2 * point.mass 0 * ((vecArg 0)
          * (vecArg 1)) + 2 * point.mass 1 * ((vecArg 0) * (vecArg 2)) + 2
          * point.mass 2 * ((vecArg 1) * (vecArg 2)) := by
      rw [kFourGap_treeThreeFourFive_eq]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hform]
    exact harmonicSplitQuadraticForm_pos
      (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
        - point.mass 1)
      (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
        - point.mass 2)
      (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
        - point.mass 2)
      (point.mass 0) (point.mass 1) (point.mass 2)
      (point.mass 0) (point.mass 1) (point.mass 2)
      (vecArg 0) (vecArg 1) (vecArg 2)
      hdiagOnePos hdiagTwoPos hdiagThreePos
      (point.mass_pos 0) (point.mass_pos 1) (point.mass_pos 2)
      (by ring) (by ring) (by ring)
      hdomRowOne hdomRowTwo hdomRowThree
      hsomeCoordinateNonzero

/-- **The twenty-cell Layer-A dispatch.**  Any of the four star cells or
the sixteen harmonic cells delivers the chart obligation's conclusion
outright -- no weak antecedent, no selection rule.  Extends
`kFourAtlas_hasStrictTriple_of_anyStarCell`; the knife-band cells extend
this disjunction in turn, never replace it. -/
theorem kFourAtlas_hasStrictTriple_of_anyCell
    (point : DirectionChartPoint 6)
    (hcell :
      (point.weight 0 * (point.mass 0 + 2 * point.mass 2 + 2 * point.mass 4)
            < point.mass 0
        ∧ point.weight 1 * (point.mass 1 + 2 * point.mass 2 + 2
            * point.mass 5) < point.mass 1
        ∧ point.weight 3 * (point.mass 3 + 2 * point.mass 4 + 2
            * point.mass 5) < point.mass 3)
      ∨ (point.weight 0 * (point.mass 0 + 2 * point.mass 1 + 2
            * point.mass 3) < point.mass 0
        ∧ point.weight 2 * (point.mass 2 + 2 * point.mass 1 + 2
            * point.mass 5) < point.mass 2
        ∧ point.weight 4 * (point.mass 4 + 2 * point.mass 3 + 2
            * point.mass 5) < point.mass 4)
      ∨ (point.weight 1 * (point.mass 1 + 2 * point.mass 0 + 2
            * point.mass 3) < point.mass 1
        ∧ point.weight 2 * (point.mass 2 + 2 * point.mass 0 + 2
            * point.mass 4) < point.mass 2
        ∧ point.weight 5 * (point.mass 5 + 2 * point.mass 3 + 2
            * point.mass 4) < point.mass 5)
      ∨ (point.weight 3 * (point.mass 3 + 2 * point.mass 0 + 2
            * point.mass 1) < point.mass 3
        ∧ point.weight 4 * (point.mass 4 + 2 * point.mass 0 + 2
            * point.mass 2) < point.mass 4
        ∧ point.weight 5 * (point.mass 5 + 2 * point.mass 1 + 2
            * point.mass 2) < point.mass 5)
      ∨ (point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 4)
            < point.mass 0
        ∧ point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 5)
            < point.mass 1
        ∧ point.weight 3 * (point.mass 3 + point.mass 4 + point.mass 5)
            < point.mass 3
        ∧ point.mass 2 * (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 4 - point.mass 5) + point.mass 4
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
            - point.mass 5) < (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 2 - point.mass 5) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 4 - point.mass 5)
        ∧ point.mass 2 * (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 4 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
            - point.mass 4) < (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 2 - point.mass 4) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 4 - point.mass 5)
        ∧ point.mass 4 * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 2 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
            - point.mass 4) < (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 2 - point.mass 4) * (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 2 - point.mass 5))
      ∨ (point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 3
            + point.mass 5) < point.mass 0
        ∧ point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 5)
            < point.mass 1
        ∧ point.weight 4 * (point.mass 4 + point.mass 3 + point.mass 5)
            < point.mass 4
        ∧ (point.mass 2 + point.mass 5) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 3 - point.mass 5) + (point.mass 3
            + point.mass 5) * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 2 - point.mass 5) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 2 - point.mass 5)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
            - point.mass 5)
        ∧ (point.mass 2 + point.mass 5) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 3 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
            - point.mass 3 - point.mass 5) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 2 - point.mass 3 - point.mass 5)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
            - point.mass 5)
        ∧ (point.mass 3 + point.mass 5) * (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 2 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 2
            - point.mass 3 - point.mass 5) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 2 - point.mass 3 - point.mass 5)
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
            - point.mass 5))
      ∨ (point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 4)
            < point.mass 0
        ∧ point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 3
            + point.mass 4) < point.mass 1
        ∧ point.weight 5 * (point.mass 5 + point.mass 3 + point.mass 4)
            < point.mass 5
        ∧ (point.mass 2 + point.mass 4) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 3 - point.mass 4) + point.mass 4
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
            - point.mass 3 - point.mass 4) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 2 - point.mass 3 - point.mass 4)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
            - point.mass 4)
        ∧ (point.mass 2 + point.mass 4) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 3 - point.mass 4) + (point.mass 3
            + point.mass 4) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 2 - point.mass 4) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 2 - point.mass 4)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
            - point.mass 4)
        ∧ point.mass 4 * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 2 - point.mass 3 - point.mass 4) + (point.mass 3
            + point.mass 4) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 2 - point.mass 4) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 2 - point.mass 4)
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 2
            - point.mass 3 - point.mass 4))
      ∨ (point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 4
            + point.mass 5) < point.mass 0
        ∧ point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 5)
            < point.mass 2
        ∧ point.weight 3 * (point.mass 3 + point.mass 4 + point.mass 5)
            < point.mass 3
        ∧ (point.mass 1 + point.mass 5) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 4 - point.mass 5) + (point.mass 4
            + point.mass 5) * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 1 - point.mass 5) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 1 - point.mass 5)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
            - point.mass 5)
        ∧ (point.mass 1 + point.mass 5) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 4 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
            - point.mass 4 - point.mass 5) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 1 - point.mass 4 - point.mass 5)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
            - point.mass 5)
        ∧ (point.mass 4 + point.mass 5) * (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 1 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
            - point.mass 4 - point.mass 5) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 1 - point.mass 4 - point.mass 5)
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
            - point.mass 5))
      ∨ (point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 3)
            < point.mass 0
        ∧ point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 5)
            < point.mass 2
        ∧ point.weight 4 * (point.mass 4 + point.mass 3 + point.mass 5)
            < point.mass 4
        ∧ point.mass 1 * (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 3 - point.mass 5) + point.mass 3
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
            - point.mass 5) < (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 1 - point.mass 5) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 3 - point.mass 5)
        ∧ point.mass 1 * (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 3 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
            - point.mass 3) < (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 1 - point.mass 3) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 3 - point.mass 5)
        ∧ point.mass 3 * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 1 - point.mass 5) + point.mass 5
            * (point.mass 0 / point.weight 0 - point.mass 0 - point.mass 1
            - point.mass 3) < (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 1 - point.mass 3) * (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 1 - point.mass 5))
      ∨ (point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 3)
            < point.mass 0
        ∧ point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 3
            + point.mass 4) < point.mass 2
        ∧ point.weight 5 * (point.mass 5 + point.mass 3 + point.mass 4)
            < point.mass 5
        ∧ (point.mass 1 + point.mass 3) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 3 - point.mass 4) + point.mass 3
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
            - point.mass 3 - point.mass 4) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 1 - point.mass 3 - point.mass 4)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
            - point.mass 4)
        ∧ (point.mass 1 + point.mass 3) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 3 - point.mass 4) + (point.mass 3
            + point.mass 4) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 1 - point.mass 3) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 1 - point.mass 3)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 3
            - point.mass 4)
        ∧ point.mass 3 * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 1 - point.mass 3 - point.mass 4) + (point.mass 3
            + point.mass 4) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 1 - point.mass 3) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 1 - point.mass 3)
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 1
            - point.mass 3 - point.mass 4))
      ∨ (point.weight 0 * (point.mass 0 + point.mass 2 + point.mass 4)
            < point.mass 0
        ∧ point.weight 3 * (point.mass 3 + point.mass 1 + point.mass 2
            + point.mass 4) < point.mass 3
        ∧ point.weight 5 * (point.mass 5 + point.mass 1 + point.mass 2)
            < point.mass 5
        ∧ (point.mass 2 + point.mass 4) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 1 - point.mass 2) + point.mass 2
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 1
            - point.mass 2 - point.mass 4) < (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 1 - point.mass 2 - point.mass 4)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
            - point.mass 2)
        ∧ (point.mass 2 + point.mass 4) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 1 - point.mass 2) + (point.mass 1
            + point.mass 2) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 2 - point.mass 4) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 2 - point.mass 4)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
            - point.mass 2)
        ∧ point.mass 2 * (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 1 - point.mass 2 - point.mass 4) + (point.mass 1
            + point.mass 2) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 2 - point.mass 4) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 2 - point.mass 4)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 1
            - point.mass 2 - point.mass 4))
      ∨ (point.weight 0 * (point.mass 0 + point.mass 1 + point.mass 3)
            < point.mass 0
        ∧ point.weight 4 * (point.mass 4 + point.mass 1 + point.mass 2
            + point.mass 3) < point.mass 4
        ∧ point.weight 5 * (point.mass 5 + point.mass 1 + point.mass 2)
            < point.mass 5
        ∧ (point.mass 1 + point.mass 3) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 1 - point.mass 2) + point.mass 1
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 1
            - point.mass 2 - point.mass 3) < (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 1 - point.mass 2 - point.mass 3)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
            - point.mass 2)
        ∧ (point.mass 1 + point.mass 3) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 1 - point.mass 2) + (point.mass 1
            + point.mass 2) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 1 - point.mass 3) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 1 - point.mass 3)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 1
            - point.mass 2)
        ∧ point.mass 1 * (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 1 - point.mass 2 - point.mass 3) + (point.mass 1
            + point.mass 2) * (point.mass 0 / point.weight 0 - point.mass 0
            - point.mass 1 - point.mass 3) < (point.mass 0 / point.weight 0
            - point.mass 0 - point.mass 1 - point.mass 3)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 1
            - point.mass 2 - point.mass 3))
      ∨ (point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 4
            + point.mass 5) < point.mass 1
        ∧ point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 4)
            < point.mass 2
        ∧ point.weight 3 * (point.mass 3 + point.mass 4 + point.mass 5)
            < point.mass 3
        ∧ (point.mass 0 + point.mass 4) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 4 - point.mass 5) + (point.mass 4
            + point.mass 5) * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 0 - point.mass 4) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 0 - point.mass 4)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
            - point.mass 5)
        ∧ (point.mass 0 + point.mass 4) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 4 - point.mass 5) + point.mass 4
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
            - point.mass 4 - point.mass 5) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 0 - point.mass 4 - point.mass 5)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 4
            - point.mass 5)
        ∧ (point.mass 4 + point.mass 5) * (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 0 - point.mass 4) + point.mass 4
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
            - point.mass 4 - point.mass 5) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 0 - point.mass 4 - point.mass 5)
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
            - point.mass 4))
      ∨ (point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 3)
            < point.mass 1
        ∧ point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 3
            + point.mass 5) < point.mass 2
        ∧ point.weight 4 * (point.mass 4 + point.mass 3 + point.mass 5)
            < point.mass 4
        ∧ (point.mass 0 + point.mass 3) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 3 - point.mass 5) + point.mass 3
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
            - point.mass 3 - point.mass 5) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 0 - point.mass 3 - point.mass 5)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
            - point.mass 5)
        ∧ (point.mass 0 + point.mass 3) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 3 - point.mass 5) + (point.mass 3
            + point.mass 5) * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 0 - point.mass 3) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 0 - point.mass 3)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 3
            - point.mass 5)
        ∧ point.mass 3 * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 0 - point.mass 3 - point.mass 5) + (point.mass 3
            + point.mass 5) * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 0 - point.mass 3) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 0 - point.mass 3)
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
            - point.mass 3 - point.mass 5))
      ∨ (point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 3)
            < point.mass 1
        ∧ point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 4)
            < point.mass 2
        ∧ point.weight 5 * (point.mass 5 + point.mass 3 + point.mass 4)
            < point.mass 5
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 3 - point.mass 4) + point.mass 3
            * (point.mass 2 / point.weight 2 - point.mass 2 - point.mass 0
            - point.mass 4) < (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 0 - point.mass 4) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 3 - point.mass 4)
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 3 - point.mass 4) + point.mass 4
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
            - point.mass 3) < (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 0 - point.mass 3) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 3 - point.mass 4)
        ∧ point.mass 3 * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 0 - point.mass 4) + point.mass 4
            * (point.mass 1 / point.weight 1 - point.mass 1 - point.mass 0
            - point.mass 3) < (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 0 - point.mass 3) * (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 0 - point.mass 4))
      ∨ (point.weight 1 * (point.mass 1 + point.mass 2 + point.mass 5)
            < point.mass 1
        ∧ point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 2
            + point.mass 5) < point.mass 3
        ∧ point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 2)
            < point.mass 4
        ∧ (point.mass 2 + point.mass 5) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 0 - point.mass 2) + point.mass 2
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
            - point.mass 2 - point.mass 5) < (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 0 - point.mass 2 - point.mass 5)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
            - point.mass 2)
        ∧ (point.mass 2 + point.mass 5) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 0 - point.mass 2) + (point.mass 0
            + point.mass 2) * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 2 - point.mass 5) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 2 - point.mass 5)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
            - point.mass 2)
        ∧ point.mass 2 * (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 0 - point.mass 2 - point.mass 5) + (point.mass 0
            + point.mass 2) * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 2 - point.mass 5) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 2 - point.mass 5)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
            - point.mass 2 - point.mass 5))
      ∨ (point.weight 1 * (point.mass 1 + point.mass 0 + point.mass 3)
            < point.mass 1
        ∧ point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 2)
            < point.mass 4
        ∧ point.weight 5 * (point.mass 5 + point.mass 0 + point.mass 2
            + point.mass 3) < point.mass 5
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 0 - point.mass 2 - point.mass 3) + (point.mass 0
            + point.mass 3) * (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 0 - point.mass 2) < (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 0 - point.mass 2)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 0
            - point.mass 2 - point.mass 3)
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 0 - point.mass 2 - point.mass 3) + (point.mass 0
            + point.mass 2) * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 0 - point.mass 3) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 0 - point.mass 3)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 0
            - point.mass 2 - point.mass 3)
        ∧ (point.mass 0 + point.mass 3) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 0 - point.mass 2) + (point.mass 0
            + point.mass 2) * (point.mass 1 / point.weight 1 - point.mass 1
            - point.mass 0 - point.mass 3) < (point.mass 1 / point.weight 1
            - point.mass 1 - point.mass 0 - point.mass 3)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
            - point.mass 2))
      ∨ (point.weight 2 * (point.mass 2 + point.mass 1 + point.mass 5)
            < point.mass 2
        ∧ point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 1)
            < point.mass 3
        ∧ point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 1
            + point.mass 5) < point.mass 4
        ∧ point.mass 1 * (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 0 - point.mass 1 - point.mass 5) + (point.mass 1
            + point.mass 5) * (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 0 - point.mass 1) < (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 0 - point.mass 1)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
            - point.mass 1 - point.mass 5)
        ∧ point.mass 1 * (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 0 - point.mass 1 - point.mass 5) + (point.mass 0
            + point.mass 1) * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 1 - point.mass 5) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 1 - point.mass 5)
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
            - point.mass 1 - point.mass 5)
        ∧ (point.mass 1 + point.mass 5) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 0 - point.mass 1) + (point.mass 0
            + point.mass 1) * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 1 - point.mass 5) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 1 - point.mass 5)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
            - point.mass 1))
      ∨ (point.weight 2 * (point.mass 2 + point.mass 0 + point.mass 4)
            < point.mass 2
        ∧ point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 1)
            < point.mass 3
        ∧ point.weight 5 * (point.mass 5 + point.mass 0 + point.mass 1
            + point.mass 4) < point.mass 5
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 0 - point.mass 1 - point.mass 4) + (point.mass 0
            + point.mass 4) * (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 0 - point.mass 1) < (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 0 - point.mass 1)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 0
            - point.mass 1 - point.mass 4)
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 0 - point.mass 1 - point.mass 4) + (point.mass 0
            + point.mass 1) * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 0 - point.mass 4) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 0 - point.mass 4)
            * (point.mass 5 / point.weight 5 - point.mass 5 - point.mass 0
            - point.mass 1 - point.mass 4)
        ∧ (point.mass 0 + point.mass 4) * (point.mass 3 / point.weight 3
            - point.mass 3 - point.mass 0 - point.mass 1) + (point.mass 0
            + point.mass 1) * (point.mass 2 / point.weight 2 - point.mass 2
            - point.mass 0 - point.mass 4) < (point.mass 2 / point.weight 2
            - point.mass 2 - point.mass 0 - point.mass 4)
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
            - point.mass 1))
      ∨ (point.weight 3 * (point.mass 3 + point.mass 0 + point.mass 1)
            < point.mass 3
        ∧ point.weight 4 * (point.mass 4 + point.mass 0 + point.mass 2)
            < point.mass 4
        ∧ point.weight 5 * (point.mass 5 + point.mass 1 + point.mass 2)
            < point.mass 5
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 1 - point.mass 2) + point.mass 1
            * (point.mass 4 / point.weight 4 - point.mass 4 - point.mass 0
            - point.mass 2) < (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 0 - point.mass 2) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 1 - point.mass 2)
        ∧ point.mass 0 * (point.mass 5 / point.weight 5 - point.mass 5
            - point.mass 1 - point.mass 2) + point.mass 2
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
            - point.mass 1) < (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 0 - point.mass 1) * (point.mass 5 / point.weight 5
            - point.mass 5 - point.mass 1 - point.mass 2)
        ∧ point.mass 1 * (point.mass 4 / point.weight 4 - point.mass 4
            - point.mass 0 - point.mass 2) + point.mass 2
            * (point.mass 3 / point.weight 3 - point.mass 3 - point.mass 0
            - point.mass 1) < (point.mass 3 / point.weight 3 - point.mass 3
            - point.mass 0 - point.mass 1) * (point.mass 4 / point.weight 4
            - point.mass 4 - point.mass 0 - point.mass 2))) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection point.mass point.weight
        selected).PosDef := by
  rcases hcell with ⟨hFirst, hSecond, hThird⟩ | ⟨hFirst, hSecond, hThird⟩ |
    ⟨hFirst, hSecond, hThird⟩ | ⟨hFirst, hSecond, hThird⟩ | ⟨hFirst,
    hSecond, hThird, hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird,
    hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth,
    hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth, hSixth⟩ | ⟨hFirst,
    hSecond, hThird, hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird,
    hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth,
    hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth, hSixth⟩ | ⟨hFirst,
    hSecond, hThird, hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird,
    hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth,
    hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth, hSixth⟩ | ⟨hFirst,
    hSecond, hThird, hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird,
    hFourth, hFifth, hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth,
    hSixth⟩ | ⟨hFirst, hSecond, hThird, hFourth, hFifth, hSixth⟩
  · exact ⟨{0, 1, 3}, by decide,
      kFourAtlas_starNodeOne_posDef_of_cell point hFirst hSecond hThird⟩
  · exact ⟨{0, 2, 4}, by decide,
      kFourAtlas_starNodeTwo_posDef_of_cell point hFirst hSecond hThird⟩
  · exact ⟨{1, 2, 5}, by decide,
      kFourAtlas_starNodeThree_posDef_of_cell point hFirst hSecond hThird⟩
  · exact ⟨{3, 4, 5}, by decide,
      kFourAtlas_starNodeFour_posDef_of_cell point hFirst hSecond hThird⟩
  · exact ⟨{0, 1, 3}, by decide,
      kFourAtlas_harmonicZeroOneThree_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{0, 1, 4}, by decide,
      kFourAtlas_harmonicZeroOneFour_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{0, 1, 5}, by decide,
      kFourAtlas_harmonicZeroOneFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{0, 2, 3}, by decide,
      kFourAtlas_harmonicZeroTwoThree_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{0, 2, 4}, by decide,
      kFourAtlas_harmonicZeroTwoFour_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{0, 2, 5}, by decide,
      kFourAtlas_harmonicZeroTwoFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{0, 3, 5}, by decide,
      kFourAtlas_harmonicZeroThreeFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{0, 4, 5}, by decide,
      kFourAtlas_harmonicZeroFourFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{1, 2, 3}, by decide,
      kFourAtlas_harmonicOneTwoThree_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{1, 2, 4}, by decide,
      kFourAtlas_harmonicOneTwoFour_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{1, 2, 5}, by decide,
      kFourAtlas_harmonicOneTwoFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{1, 3, 4}, by decide,
      kFourAtlas_harmonicOneThreeFour_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{1, 4, 5}, by decide,
      kFourAtlas_harmonicOneFourFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{2, 3, 4}, by decide,
      kFourAtlas_harmonicTwoThreeFour_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{2, 3, 5}, by decide,
      kFourAtlas_harmonicTwoThreeFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩
  · exact ⟨{3, 4, 5}, by decide,
      kFourAtlas_harmonicThreeFourFive_posDef_of_cell point hFirst hSecond hThird hFourth hFifth
        hSixth⟩


/-! ## The leverage layer: the contraction tree polynomial, the designated
leverage edge, and the surviving leverage-hosted selection

The determinant currency of the chart gap factors through the weights only:
with `y_c = mass c / weight c` Cauchy-Binet over the totally unimodular K4
tree basis gives `det G_T = sum over trees S of y_S * c(S, T)` where
`c(S, T) = prod_{c in S cap T} (1 - w_c) * prod_{c in S \ T} (-w_c)`.  The
round-four campaign proved this route CLOSED in its linear form: at every
mandatory point and every knife-corpus point there is an exact rational
dual `z >= 0` with `sum_S z_S c(S, T) < 0` for all sixteen trees, so no
nonnegative tree aggregate with y-free coefficients can certify even the
det-positivity half of the endgame; the toric product structure
`y_S = prod y_c` is load-bearing (lane record `/tmp/gtz-chain/wfk4/detmax/`).

What survives is a POLYNOMIAL leverage structure.  For the mass Laplacian
`M = sum_c mass_c A_c` the matrix-determinant lemma and Cauchy-Binet give,
with no inverse anywhere,

* `det M = kFourMassTreeSum mass` (the sixteen tree mass-products),
* `u_c^T adj(M) u_c = kFourContractionTreePolynomial mass c` (the weighted
  spanning-tree polynomial of the contraction `K4/c`: eight two-edge
  products), and
* `mass_c * kFourContractionTreePolynomial mass c` = the tree mass-sum
  THROUGH `c`, so the statistical leverage score of atom `c` is exactly
  `mass_c * Q_c / kFourMassTreeSum mass` and the scores sum to `3`
  (`kFourLeverage_sumIdentity`, a ring fact).

The designated LEVERAGE EDGE maximizes `mass_c * Q_c / weight_c`
(`IsMaxLeverageEdge`, stated cross-multiplied; an argmax always exists).
The pigeonhole `isMaxLeverageEdge_leverageFloor` gives
`3 * w_e * treeSum <= mass_e * Q_e` there: every tree through the leverage
edge clears the floor `2 * det M` in its leverage term.  This designation
is a JOINT polynomial functional of all six masses, so it is compatible
with the kernel refutations of every per-label scalar ordering above; and
unlike all of them it SURVIVES both landed refuter points in kernel below
(edge `5` is the leverage edge at both, hosting `{0, 4, 5}` at
`maxEdgeRefuterPoint` and the landed `{3, 4, 5}` at
`heavyPairRefuterPoint`).  Adjudication record: the hosting statement
`KFourLeverageEdgeHostsStrictTree` holds at all fifteen mandatory points,
all 467 knife-corpus leftovers, and 2900 fresh exact adversarial points
(tetraShell, sliver, triangleCloser, twoHeavyMass, knifeEdge, multiscale,
generic) with zero failures -- the first surviving selection with a
designated edge.  It is UNPROVED vocabulary with the consumption bridge
`directionChartIsTieFree_kFour_of_leverageEdgeHosts` proved below.

The det normal form `kFourGapDet_treeThreeFourFive_leverageForm` displays
the leverage reduction at the gauge star: the gap determinant splits into
the through-tree leverage terms minus the tree sum minus three exchange
terms (each an adjacent-tree mass-product), and the corollary
`kFourGapDet_treeThreeFourFive_pos_of_exchangeBound` states the reduced
residual obligation in kernel: past the leverage floor, det-positivity at
the gauge star is exactly an exchange bound. -/

/-- The spanning-tree mass polynomial of the K4 chart: the sum of the
sixteen tree mass-products.  Equals `det (sum_c mass_c A_c)` by
Cauchy-Binet (sympy-verified; the kernel consumes only the polynomial). -/
noncomputable def kFourMassTreeSum (massVec : Fin 6 → ℝ) : ℝ :=
  massVec 0 * massVec 1 * massVec 3 + massVec 0 * massVec 2 * massVec 4
    + massVec 1 * massVec 2 * massVec 5 + massVec 3 * massVec 4 * massVec 5
    + massVec 0 * massVec 1 * massVec 4 + massVec 0 * massVec 1 * massVec 5
    + massVec 0 * massVec 2 * massVec 3 + massVec 0 * massVec 2 * massVec 5
    + massVec 0 * massVec 3 * massVec 5 + massVec 0 * massVec 4 * massVec 5
    + massVec 1 * massVec 2 * massVec 3 + massVec 1 * massVec 2 * massVec 4
    + massVec 1 * massVec 3 * massVec 4 + massVec 1 * massVec 4 * massVec 5
    + massVec 2 * massVec 3 * massVec 4 + massVec 2 * massVec 3 * massVec 5

/-- The weighted spanning-tree polynomial of the contraction `K4/c`: the
two parallel classes of `K4/c` multiply and the opposite edge couples to
their union.  Equals `u_c^T adj(M) u_c` for the mass Laplacian `M`
(matrix-determinant lemma, sympy-verified), and
`massVec c * kFourContractionTreePolynomial massVec c` is the sum of the
eight tree mass-products through `c`. -/
noncomputable def kFourContractionTreePolynomial (massVec : Fin 6 → ℝ) :
    Fin 6 → ℝ
  | 0 => (massVec 1 + massVec 2) * (massVec 3 + massVec 4)
      + massVec 5 * (massVec 1 + massVec 2 + massVec 3 + massVec 4)
  | 1 => (massVec 0 + massVec 2) * (massVec 3 + massVec 5)
      + massVec 4 * (massVec 0 + massVec 2 + massVec 3 + massVec 5)
  | 2 => (massVec 0 + massVec 1) * (massVec 4 + massVec 5)
      + massVec 3 * (massVec 0 + massVec 1 + massVec 4 + massVec 5)
  | 3 => (massVec 0 + massVec 4) * (massVec 1 + massVec 5)
      + massVec 2 * (massVec 0 + massVec 4 + massVec 1 + massVec 5)
  | 4 => (massVec 0 + massVec 3) * (massVec 2 + massVec 5)
      + massVec 1 * (massVec 0 + massVec 3 + massVec 2 + massVec 5)
  | 5 => (massVec 1 + massVec 3) * (massVec 2 + massVec 4)
      + massVec 0 * (massVec 1 + massVec 3 + massVec 2 + massVec 4)

theorem kFourContractionTreePolynomial_zero (massVec : Fin 6 → ℝ) :
    kFourContractionTreePolynomial massVec 0
      = (massVec 1 + massVec 2) * (massVec 3 + massVec 4)
        + massVec 5 * (massVec 1 + massVec 2 + massVec 3 + massVec 4) := rfl

theorem kFourContractionTreePolynomial_one (massVec : Fin 6 → ℝ) :
    kFourContractionTreePolynomial massVec 1
      = (massVec 0 + massVec 2) * (massVec 3 + massVec 5)
        + massVec 4 * (massVec 0 + massVec 2 + massVec 3 + massVec 5) := rfl

theorem kFourContractionTreePolynomial_two (massVec : Fin 6 → ℝ) :
    kFourContractionTreePolynomial massVec 2
      = (massVec 0 + massVec 1) * (massVec 4 + massVec 5)
        + massVec 3 * (massVec 0 + massVec 1 + massVec 4 + massVec 5) := rfl

theorem kFourContractionTreePolynomial_three (massVec : Fin 6 → ℝ) :
    kFourContractionTreePolynomial massVec 3
      = (massVec 0 + massVec 4) * (massVec 1 + massVec 5)
        + massVec 2 * (massVec 0 + massVec 4 + massVec 1 + massVec 5) := rfl

theorem kFourContractionTreePolynomial_four (massVec : Fin 6 → ℝ) :
    kFourContractionTreePolynomial massVec 4
      = (massVec 0 + massVec 3) * (massVec 2 + massVec 5)
        + massVec 1 * (massVec 0 + massVec 3 + massVec 2 + massVec 5) := rfl

theorem kFourContractionTreePolynomial_five (massVec : Fin 6 → ℝ) :
    kFourContractionTreePolynomial massVec 5
      = (massVec 1 + massVec 3) * (massVec 2 + massVec 4)
        + massVec 0 * (massVec 1 + massVec 3 + massVec 2 + massVec 4) := rfl

/-- The tree mass-sum is positive at positive masses: the floor of the
leverage pigeonhole is never vacuous. -/
theorem kFourMassTreeSum_pos (massVec : Fin 6 → ℝ)
    (hmassPos : ∀ label, 0 < massVec label) :
    0 < kFourMassTreeSum massVec := by
  have hzero := hmassPos 0
  have hone := hmassPos 1
  have htwo := hmassPos 2
  have hthree := hmassPos 3
  have hfour := hmassPos 4
  have hfive := hmassPos 5
  unfold kFourMassTreeSum
  positivity

/-- **The leverage trace identity.**  The six leverage numerators sum to
three times the tree sum: each tree is counted once per edge.  This is the
polynomial face of `tr(M^{-1} M) = 3` for the mass Laplacian. -/
theorem kFourLeverage_sumIdentity (massVec : Fin 6 → ℝ) :
    massVec 0 * kFourContractionTreePolynomial massVec 0
      + massVec 1 * kFourContractionTreePolynomial massVec 1
      + massVec 2 * kFourContractionTreePolynomial massVec 2
      + massVec 3 * kFourContractionTreePolynomial massVec 3
      + massVec 4 * kFourContractionTreePolynomial massVec 4
      + massVec 5 * kFourContractionTreePolynomial massVec 5
    = 3 * kFourMassTreeSum massVec := by
  simp only [kFourContractionTreePolynomial_zero,
    kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
    kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
    kFourContractionTreePolynomial_five, kFourMassTreeSum]
  ring

/-- `edge` attains the maximum leverage ratio
`mass * kFourContractionTreePolynomial / weight` at the chart point, stated
cross-multiplied (weights are positive).  Unlike the refuted conductance,
alpha, and mass designations, this reads a JOINT polynomial of all six
masses. -/
def IsMaxLeverageEdge (point : DirectionChartPoint 6) (edge : Fin 6) : Prop :=
  ∀ label,
    point.mass label * kFourContractionTreePolynomial point.mass label
        * point.weight edge
      ≤ point.mass edge * kFourContractionTreePolynomial point.mass edge
        * point.weight label

/-- A leverage edge always exists: finite argmax of the ratio. -/
theorem exists_isMaxLeverageEdge (point : DirectionChartPoint 6) :
    ∃ edge, IsMaxLeverageEdge point edge := by
  obtain ⟨edge, -, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin 6))
    (fun label => point.mass label
      * kFourContractionTreePolynomial point.mass label
      / point.weight label) Finset.univ_nonempty
  refine ⟨edge, fun label => ?_⟩
  have hratio := hmax label (Finset.mem_univ label)
  rw [div_le_div_iff₀ (point.weight_pos label) (point.weight_pos edge)]
    at hratio
  exact hratio

/-- **The leverage pigeonhole.**  The scores sum to `3` while the weights
sum to `1`, so the leverage edge clears three times its weight share:
`3 * w_e * treeSum <= mass_e * Q_e`.  Consequently every spanning tree
through the leverage edge has its leverage term at least `3 * det M`, a
floor of `2 * det M` past the tree-sum subtraction. -/
theorem isMaxLeverageEdge_leverageFloor (point : DirectionChartPoint 6)
    {edge : Fin 6} (hmax : IsMaxLeverageEdge point edge) :
    3 * point.weight edge * kFourMassTreeSum point.mass
      ≤ point.mass edge * kFourContractionTreePolynomial point.mass edge := by
  have hsum := kFourLeverage_sumIdentity point.mass
  have hweight := point.weight_sum_one
  rw [Fin.sum_univ_six] at hweight
  have hscaled : (point.mass 0 * kFourContractionTreePolynomial point.mass 0
        + point.mass 1 * kFourContractionTreePolynomial point.mass 1
        + point.mass 2 * kFourContractionTreePolynomial point.mass 2
        + point.mass 3 * kFourContractionTreePolynomial point.mass 3
        + point.mass 4 * kFourContractionTreePolynomial point.mass 4
        + point.mass 5 * kFourContractionTreePolynomial point.mass 5)
          * point.weight edge
      ≤ point.mass edge * kFourContractionTreePolynomial point.mass edge
          * (point.weight 0 + point.weight 1 + point.weight 2
            + point.weight 3 + point.weight 4 + point.weight 5) := by
    have hzero := hmax 0
    have hone := hmax 1
    have htwo := hmax 2
    have hthree := hmax 3
    have hfour := hmax 4
    have hfive := hmax 5
    ring_nf
    ring_nf at hzero hone htwo hthree hfour hfive
    linarith
  rw [hsum, hweight] at hscaled
  linarith

/-- **The surviving leverage-hosted selection.**  At every chart point the
leverage edge hosts a strictly dominating spanning tree.  The designation
is a joint polynomial comparison, so it is compatible with every kernel
refutation of per-label orderings; it survives both refuter points (in
kernel below), the full mandatory battery, the 467-point knife corpus, and
2900 fresh adversarial points with zero failures.  UNPROVED vocabulary;
proving it (or `KFourEdgeDetArgmaxHostsStrictTree`, or the selection-free
`KFourSomeTreeLiftThreshold`) is the residual K4 endgame. -/
def KFourLeverageEdgeHostsStrictTree : Prop :=
  ∀ (point : DirectionChartPoint 6) (edge : Fin 6),
    IsMaxLeverageEdge point edge →
      ∃ tree ∈ kFourSpanningTreeList, edge ∈ tree ∧
        (directionChartGap kFourDirection point.mass point.weight
          tree).PosDef

/-- **The leverage selection's consumption bridge.**  The leverage-hosted
selection closes the chart obligation (the argmax data and the weak
antecedent are discarded pointwise, per the standing forbidden-route law). -/
theorem directionChartIsTieFree_kFour_of_leverageEdgeHosts
    (hhost : KFourLeverageEdgeHostsStrictTree) :
    DirectionChartIsTieFree kFourDirection := by
  intro point _hweak
  obtain ⟨edge, hmax⟩ := exists_isMaxLeverageEdge point
  obtain ⟨tree, htreeMem, _hedgeMem, hposDef⟩ := hhost point edge hmax
  have hcard : tree.card = 3 := by
    have hall : ∀ candidate ∈ kFourSpanningTreeList, candidate.card = 3 := by
      decide
    exact hall tree htreeMem
  exact ⟨tree, hcard, hposDef⟩

/-! ### The leverage selection is ALIVE at both landed refuter points

At `maxEdgeRefuterPoint` (which kernel-kills the conductance and alpha
designations) and at `heavyPairRefuterPoint` (which kernel-kills the
dominant-mass-pair designation) the leverage edge is `5`, away from the
broken argmax edge `3` in both cases, and it hosts: `{0, 4, 5}` dominates
strictly at the first, the landed `{3, 4, 5}` at the second. -/

/-- Edge `5` is the leverage edge at the landed max-edge refuter. -/
theorem maxEdgeRefuter_isMaxLeverageEdge_five :
    IsMaxLeverageEdge maxEdgeRefuterPoint 5 := by
  intro label
  fin_cases label <;>
    norm_num [kFourContractionTreePolynomial, maxEdgeRefuterMass,
      maxEdgeRefuterWeight]

/-- The `{0,4,5}` chart gap at `maxEdgeRefuterPoint`, entry by entry. -/
theorem maxEdgeRefuter_gap_zeroFourFive_eq :
    directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight {0, 4, 5}
      = !![839/60, -24, 1/60; -24, 5039/60, 1/60; 1/60, 1/60, 19/20] := by
  simp only [directionChartGap, maxEdgeRefuterPoint_mass_eq,
    maxEdgeRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

/-- The through-leverage-edge tree `{0, 4, 5}` dominates strictly at the
max-edge refuter (leading minors `839/60`, `2154121/3600`,
`122776139/216000`). -/
theorem maxEdgeRefuter_gap_zeroFourFive_posDef :
    (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
      maxEdgeRefuterPoint.weight {0, 4, 5}).PosDef := by
  rw [maxEdgeRefuter_gap_zeroFourFive_eq]
  refine posDef_of_leadingMinors_fin_three (839/60) (-24) (1/60) (5039/60)
    (1/60) (19/20) (by norm_num) (by norm_num) (by norm_num)

/-- The leverage edge HOSTS at the point that kernel-killed the
conductance and alpha designations. -/
theorem maxEdgeRefuterPoint_leverageEdge_hostsStrictTree :
    ∃ tree ∈ kFourSpanningTreeList, (5 : Fin 6) ∈ tree ∧
      (directionChartGap kFourDirection maxEdgeRefuterPoint.mass
        maxEdgeRefuterPoint.weight tree).PosDef :=
  ⟨{0, 4, 5}, by decide, by decide, maxEdgeRefuter_gap_zeroFourFive_posDef⟩

/-- Edge `5` is the leverage edge at the dual (heavy-pair) refuter too. -/
theorem heavyPairRefuter_isMaxLeverageEdge_five :
    IsMaxLeverageEdge heavyPairRefuterPoint 5 := by
  intro label
  fin_cases label <;>
    norm_num [kFourContractionTreePolynomial, heavyPairRefuterMass,
      maxEdgeRefuterWeight]

/-- The leverage edge HOSTS at the point that kernel-killed the
dominant-mass-pair designation: the landed `{3, 4, 5}` certificate is a
through-`5` tree. -/
theorem heavyPairRefuterPoint_leverageEdge_hostsStrictTree :
    ∃ tree ∈ kFourSpanningTreeList, (5 : Fin 6) ∈ tree ∧
      (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight tree).PosDef :=
  ⟨{3, 4, 5}, by decide, by decide, heavyPairRefuter_gap_threeFourFive_posDef⟩

/-! ### The det leverage normal form at the gauge star

The gap determinant of `{3, 4, 5}` splits into the three through-tree
leverage terms minus the tree sum, minus three exchange terms (each pairing
a chord mass with the adjacent-tree product), all times the tree's weight
product.  At a chart point the closer factor `1 - w3 - w4 - w5` equals
`w0 + w1 + w2`.  With the leverage floor at edge `5` the tree-sum
subtraction is over-paid, and det-positivity at the gauge star reduces to
one exchange bound -- the kernel-precise residual obligation of the
leverage program. -/

/-- The `{3,4,5}` gap determinant in leverage normal form (free identity,
no chart constraint: the closer factor appears as `1 - w3 - w4 - w5`). -/
theorem kFourGapDet_treeThreeFourFive_leverageForm
    (point : DirectionChartPoint 6) :
    (directionChartGap kFourDirection point.mass point.weight {3, 4, 5}).det
        * (point.weight 3 * point.weight 4 * point.weight 5)
      = point.mass 3 * point.mass 4 * point.mass 5
            * (1 - point.weight 3 - point.weight 4 - point.weight 5)
        - (point.mass 0 + point.mass 1) * point.mass 4 * point.mass 5
            * point.weight 3
        - (point.mass 0 + point.mass 2) * point.mass 3 * point.mass 5
            * point.weight 4
        - (point.mass 1 + point.mass 2) * point.mass 3 * point.mass 4
            * point.weight 5
        + point.mass 3 * kFourContractionTreePolynomial point.mass 3
            * (point.weight 4 * point.weight 5)
        + point.mass 4 * kFourContractionTreePolynomial point.mass 4
            * (point.weight 3 * point.weight 5)
        + point.mass 5 * kFourContractionTreePolynomial point.mass 5
            * (point.weight 3 * point.weight 4)
        - point.weight 3 * point.weight 4 * point.weight 5
            * kFourMassTreeSum point.mass := by
  have hthreeNe : point.weight 3 ≠ 0 := ne_of_gt (point.weight_pos 3)
  have hfourNe : point.weight 4 ≠ 0 := ne_of_gt (point.weight_pos 4)
  have hfiveNe : point.weight 5 ≠ 0 := ne_of_gt (point.weight_pos 5)
  rw [kFourGap_treeThreeFourFive_eq]
  simp only [kFourContractionTreePolynomial_three,
    kFourContractionTreePolynomial_four, kFourContractionTreePolynomial_five,
    kFourMassTreeSum]
  simp [Matrix.det_fin_three]
  field_simp
  ring

/-- **The reduced residual obligation at the gauge star.**  Given the
leverage floor at edge `5` and the exchange bound (the three exchange
terms below the retained leverage terms plus twice the weighted tree sum),
the `{3,4,5}` gap determinant is positive.  This is the exact shape the
K-term round must prove for the leverage program to close its
det-positivity half at star-designated points. -/
theorem kFourGapDet_treeThreeFourFive_pos_of_exchangeBound
    (point : DirectionChartPoint 6)
    (hfloor : 3 * point.weight 5 * kFourMassTreeSum point.mass
      ≤ point.mass 5 * kFourContractionTreePolynomial point.mass 5)
    (hexchange : (point.mass 0 + point.mass 1) * point.mass 4 * point.mass 5
          * point.weight 3
        + (point.mass 0 + point.mass 2) * point.mass 3 * point.mass 5
          * point.weight 4
        + (point.mass 1 + point.mass 2) * point.mass 3 * point.mass 4
          * point.weight 5
      < point.mass 3 * point.mass 4 * point.mass 5
            * (1 - point.weight 3 - point.weight 4 - point.weight 5)
        + point.mass 3 * kFourContractionTreePolynomial point.mass 3
            * (point.weight 4 * point.weight 5)
        + point.mass 4 * kFourContractionTreePolynomial point.mass 4
            * (point.weight 3 * point.weight 5)
        + 2 * (point.weight 3 * point.weight 4 * point.weight 5)
            * kFourMassTreeSum point.mass) :
    0 < (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).det := by
  have hform := kFourGapDet_treeThreeFourFive_leverageForm point
  have hpairPos : 0 < point.weight 3 * point.weight 4 :=
    mul_pos (point.weight_pos 3) (point.weight_pos 4)
  have hproductPos : 0 < point.weight 3 * point.weight 4 * point.weight 5 :=
    mul_pos hpairPos (point.weight_pos 5)
  have hboost := mul_le_mul_of_nonneg_right hfloor hpairPos.le
  by_contra hnot
  have hnonpos : (directionChartGap kFourDirection point.mass point.weight
      {3, 4, 5}).det ≤ 0 := not_lt.mp hnot
  have hdetTimesWeights : (directionChartGap kFourDirection point.mass
        point.weight {3, 4, 5}).det
        * (point.weight 3 * point.weight 4 * point.weight 5) ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inr ⟨hnonpos, hproductPos.le⟩)
  nlinarith [hform, hboost, hexchange, hdetTimesWeights]

/-! ## The invariant-Sylvester pencil engine

The knife-round certificate basis.  For the reduced K4 Laplacian
`L1 = sum_c A_c = !![3,-1,-1; -1,3,-1; -1,-1,3]` (determinant `16`), the
pencil determinant of a symmetric matrix `N` against `L1` expands as

    det (N + t * L1) = 16 t^3 + 8 * D1 t^2 + D2 t + D3,

where `D1` is the sum of the six entries (diagonal plus upper triangle),
`D2` the fixed invariant quadratic below, and `D3 = det N`.  Under the
kFour chart dictionary (gap = `sum_c s_c A_c` with `s = alpha` on the
selected tree and `-mass` off it) these are the three S4-invariant
polynomials of the selection vector: `D1 = sum_c s_c`,
`D2 = 4 * (opposite-pair products) + 3 * (adjacent-pair products)`,
`D3` the spanning-tree polynomial.  `posDef_of_invariantPencilTriple`
proves positive definiteness FROM the three coefficient positivities —
eigenvalue-free: the set of pencil parameters where the three Sylvester
minors are positive is nonempty far out and (when the target is not yet
certified) bounded below by zero; at its infimum the form is positive
semidefinite by a squeeze, a kernel vector is forbidden because the
pencil determinant has all coefficients positive on the half-line, and
the landed completed-square bricks re-enter the set strictly below the
infimum through an explicit polynomial openness bound — contradiction.
The three converses extract the coefficient positivities from positive
definiteness by explicit test vectors; `D2` is realized as the sum of
the six plane-restriction block determinants (the adjugate compound
identity, one block per K4 edge direction).  Exact adjudication before
statement: the equivalence holds at 52,064 fresh exact tree-instances
(mandatory battery, the 464-point and 467-point knife corpora, and
2,307 adversarial points) on top of the stage-4 7,712. -/

/-- Positive energy of the reduced K4 Laplacian quadratic form:
`3x0^2 + 3x1^2 + 3x2^2 - 2x0x1 - 2x0x2 - 2x1x2` is the square sum
`x0^2 + x1^2 + x2^2 + (x0-x1)^2 + (x0-x2)^2 + (x1-x2)^2`, positive at
every nonzero vector. -/
theorem kFourPencilLaplacianForm_pos (vecArg : Fin 3 → ℝ) (hne : vecArg ≠ 0) :
    0 < 3 * vecArg 0 ^ 2 + 3 * vecArg 1 ^ 2 + 3 * vecArg 2 ^ 2
      - 2 * (vecArg 0 * vecArg 1) - 2 * (vecArg 0 * vecArg 2)
      - 2 * (vecArg 1 * vecArg 2) := by
  have hcases : vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
    rcases eq_or_ne (vecArg 0) 0 with hzero | hnonzero
    · rcases eq_or_ne (vecArg 1) 0 with hone | hnonone
      · rcases eq_or_ne (vecArg 2) 0 with htwo | hnontwo
        · exfalso
          apply hne
          funext index
          fin_cases index
          · exact hzero
          · exact hone
          · exact htwo
        · exact Or.inr (Or.inr hnontwo)
      · exact Or.inr (Or.inl hnonone)
    · exact Or.inl hnonzero
  rcases hcases with hcoord | hcoord | hcoord
  · linarith [pow_two_pos_of_ne_zero hcoord, sq_nonneg (vecArg 0 - vecArg 1),
      sq_nonneg (vecArg 0 - vecArg 2), sq_nonneg (vecArg 1 - vecArg 2),
      sq_nonneg (vecArg 1), sq_nonneg (vecArg 2)]
  · linarith [pow_two_pos_of_ne_zero hcoord, sq_nonneg (vecArg 0 - vecArg 1),
      sq_nonneg (vecArg 0 - vecArg 2), sq_nonneg (vecArg 1 - vecArg 2),
      sq_nonneg (vecArg 0), sq_nonneg (vecArg 2)]
  · linarith [pow_two_pos_of_ne_zero hcoord, sq_nonneg (vecArg 0 - vecArg 1),
      sq_nonneg (vecArg 0 - vecArg 2), sq_nonneg (vecArg 1 - vecArg 2),
      sq_nonneg (vecArg 0), sq_nonneg (vecArg 1)]

set_option maxHeartbeats 1600000 in
/-- **The invariant-Sylvester pencil engine.**  A symmetric `3x3` matrix
whose three invariant pencil coefficients are positive — the entry sum,
the invariant quadratic, and the determinant — is positive definite.
The three hypotheses are exactly the `t^2`, `t^1`, `t^0` coefficients
(the first divided by its content `8`) of `det (N + t * L1)` for the
reduced K4 Laplacian `L1`; positive definiteness at every knife-band
point is certified by evaluating three fixed polynomials, no per-tree
frame. -/
theorem posDef_of_invariantPencilTriple
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ)
    (hlinear : 0 < entryOneOne + entryTwoTwo + entryThreeThree
      + entryOneTwo + entryOneThree + entryTwoThree)
    (hquadratic : 0 < 3 * entryOneOne * entryTwoTwo
      + 3 * entryOneOne * entryThreeThree + 3 * entryTwoTwo * entryThreeThree
      + 2 * entryOneOne * entryTwoThree + 2 * entryTwoTwo * entryOneThree
      + 2 * entryThreeThree * entryOneTwo
      - 3 * entryOneTwo ^ 2 - 3 * entryOneThree ^ 2 - 3 * entryTwoThree ^ 2
      - 2 * entryOneTwo * entryOneThree - 2 * entryOneTwo * entryTwoThree
      - 2 * entryOneThree * entryTwoThree)
    (hcubic : 0 < entryOneOne * entryTwoTwo * entryThreeThree
      - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
      + 2 * entryOneTwo * entryOneThree * entryTwoThree
      - entryOneThree ^ 2 * entryTwoTwo) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  set linearCoefficient : ℝ := entryOneOne + entryTwoTwo + entryThreeThree
    + entryOneTwo + entryOneThree + entryTwoThree with hlinearDef
  set quadraticCoefficient : ℝ := 3 * entryOneOne * entryTwoTwo
    + 3 * entryOneOne * entryThreeThree + 3 * entryTwoTwo * entryThreeThree
    + 2 * entryOneOne * entryTwoThree + 2 * entryTwoTwo * entryOneThree
    + 2 * entryThreeThree * entryOneTwo
    - 3 * entryOneTwo ^ 2 - 3 * entryOneThree ^ 2 - 3 * entryTwoThree ^ 2
    - 2 * entryOneTwo * entryOneThree - 2 * entryOneTwo * entryTwoThree
    - 2 * entryOneThree * entryTwoThree with hquadraticDef
  set cubicCoefficient : ℝ := entryOneOne * entryTwoTwo * entryThreeThree
    - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
    + 2 * entryOneTwo * entryOneThree * entryTwoThree
    - entryOneThree ^ 2 * entryTwoTwo with hcubicDef
  set blockCoefficient : ℝ := 3 * entryOneOne + 3 * entryTwoTwo
    + 2 * entryOneTwo with hblockCoefficientDef
  set blockConstant : ℝ := entryOneOne * entryTwoTwo - entryOneTwo ^ 2
    with hblockConstantDef
  set pencilMemberSet : Set ℝ := {timeVal : ℝ |
    0 < entryOneOne + 3 * timeVal ∧
    0 < 8 * timeVal ^ 2 + blockCoefficient * timeVal + blockConstant ∧
    0 < 16 * timeVal ^ 3 + 8 * linearCoefficient * timeVal ^ 2
      + quadraticCoefficient * timeVal + cubicCoefficient} with hsetDef
  clear_value linearCoefficient quadraticCoefficient cubicCoefficient
    blockCoefficient blockConstant pencilMemberSet
  have hformEval : ∀ (timeVal : ℝ) (vecArg : Fin 3 → ℝ),
      vecArg ⬝ᵥ ((!![entryOneOne + 3 * timeVal, entryOneTwo - timeVal,
          entryOneThree - timeVal;
          entryOneTwo - timeVal, entryTwoTwo + 3 * timeVal,
          entryTwoThree - timeVal;
          entryOneThree - timeVal, entryTwoThree - timeVal,
          entryThreeThree + 3 * timeVal] : Matrix (Fin 3) (Fin 3) ℝ)
        *ᵥ vecArg)
      = (entryOneOne * vecArg 0 ^ 2 + entryTwoTwo * vecArg 1 ^ 2
          + entryThreeThree * vecArg 2 ^ 2
          + 2 * entryOneTwo * (vecArg 0 * vecArg 1)
          + 2 * entryOneThree * (vecArg 0 * vecArg 2)
          + 2 * entryTwoThree * (vecArg 1 * vecArg 2))
        + timeVal * (3 * vecArg 0 ^ 2 + 3 * vecArg 1 ^ 2 + 3 * vecArg 2 ^ 2
          - 2 * (vecArg 0 * vecArg 1) - 2 * (vecArg 0 * vecArg 2)
          - 2 * (vecArg 1 * vecArg 2)) := by
    intro timeVal vecArg
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  have hmemberPosDef : ∀ timeVal ∈ pencilMemberSet,
      (!![entryOneOne + 3 * timeVal, entryOneTwo - timeVal,
          entryOneThree - timeVal;
          entryOneTwo - timeVal, entryTwoTwo + 3 * timeVal,
          entryTwoThree - timeVal;
          entryOneThree - timeVal, entryTwoThree - timeVal,
          entryThreeThree + 3 * timeVal] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
    intro timeVal htime
    rw [hsetDef] at htime
    obtain ⟨honeMinor, htwoMinor, hthreeMinor⟩ := htime
    refine posDef_of_leadingMinors_fin_three (entryOneOne + 3 * timeVal)
      (entryOneTwo - timeVal) (entryOneThree - timeVal)
      (entryTwoTwo + 3 * timeVal) (entryTwoThree - timeVal)
      (entryThreeThree + 3 * timeVal) honeMinor ?_ ?_
    · have hidentity : (entryOneOne + 3 * timeVal) * (entryTwoTwo + 3 * timeVal)
          - (entryOneTwo - timeVal) ^ 2
          = 8 * timeVal ^ 2 + blockCoefficient * timeVal + blockConstant := by
        rw [hblockCoefficientDef, hblockConstantDef]
        ring
      rw [hidentity]
      exact htwoMinor
    · have hidentity : (entryOneOne + 3 * timeVal) * (entryTwoTwo + 3 * timeVal)
            * (entryThreeThree + 3 * timeVal)
          - (entryOneOne + 3 * timeVal) * (entryTwoThree - timeVal) ^ 2
          - (entryOneTwo - timeVal) ^ 2 * (entryThreeThree + 3 * timeVal)
          + 2 * (entryOneTwo - timeVal) * (entryOneThree - timeVal)
            * (entryTwoThree - timeVal)
          - (entryOneThree - timeVal) ^ 2 * (entryTwoTwo + 3 * timeVal)
          = 16 * timeVal ^ 3 + 8 * linearCoefficient * timeVal ^ 2
            + quadraticCoefficient * timeVal + cubicCoefficient := by
        rw [hlinearDef, hquadraticDef, hcubicDef]
        ring
      rw [hidentity]
      exact hthreeMinor
  have hmemberFormPos : ∀ timeVal ∈ pencilMemberSet, ∀ vecArg : Fin 3 → ℝ,
      vecArg ≠ 0 →
      0 < vecArg ⬝ᵥ ((!![entryOneOne + 3 * timeVal, entryOneTwo - timeVal,
          entryOneThree - timeVal;
          entryOneTwo - timeVal, entryTwoTwo + 3 * timeVal,
          entryTwoThree - timeVal;
          entryOneThree - timeVal, entryTwoThree - timeVal,
          entryThreeThree + 3 * timeVal] : Matrix (Fin 3) (Fin 3) ℝ)
        *ᵥ vecArg) := by
    intro timeVal htime vecArg hne
    have hvalue := (hmemberPosDef timeVal htime).dotProduct_mulVec_pos hne
    rwa [star_trivial] at hvalue
  have hformGivesMinors : ∀ timeVal : ℝ,
      (∀ vecArg : Fin 3 → ℝ, vecArg ≠ 0 →
        0 < vecArg ⬝ᵥ ((!![entryOneOne + 3 * timeVal, entryOneTwo - timeVal,
            entryOneThree - timeVal;
            entryOneTwo - timeVal, entryTwoTwo + 3 * timeVal,
            entryTwoThree - timeVal;
            entryOneThree - timeVal, entryTwoThree - timeVal,
            entryThreeThree + 3 * timeVal] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ vecArg)) →
      0 < entryOneOne + 3 * timeVal ∧
        0 < 8 * timeVal ^ 2 + blockCoefficient * timeVal + blockConstant := by
    intro timeVal hform
    have hbasisNe : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 0
      norm_num at hcomp
    have hcornerValue : (![1, 0, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne + 3 * timeVal, entryOneTwo - timeVal,
            entryOneThree - timeVal;
            entryOneTwo - timeVal, entryTwoTwo + 3 * timeVal,
            entryTwoThree - timeVal;
            entryOneThree - timeVal, entryTwoThree - timeVal,
            entryThreeThree + 3 * timeVal] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![1, 0, 0])
        = entryOneOne + 3 * timeVal := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    have hcorner : 0 < entryOneOne + 3 * timeVal := by
      have hvalue := hform ![1, 0, 0] hbasisNe
      rw [hcornerValue] at hvalue
      exact hvalue
    have hwitnessNe : (![entryOneTwo - timeVal, -(entryOneOne + 3 * timeVal), 0]
        : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 1
      norm_num at hcomp
      linarith [hcomp, hcorner]
    have hwitnessValue : (![entryOneTwo - timeVal, -(entryOneOne + 3 * timeVal),
          0] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne + 3 * timeVal, entryOneTwo - timeVal,
            entryOneThree - timeVal;
            entryOneTwo - timeVal, entryTwoTwo + 3 * timeVal,
            entryTwoThree - timeVal;
            entryOneThree - timeVal, entryTwoThree - timeVal,
            entryThreeThree + 3 * timeVal] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![entryOneTwo - timeVal, -(entryOneOne + 3 * timeVal), 0])
        = (entryOneOne + 3 * timeVal)
          * (8 * timeVal ^ 2 + blockCoefficient * timeVal + blockConstant) := by
      rw [hblockCoefficientDef, hblockConstantDef]
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    have hproduct := hform _ hwitnessNe
    rw [hwitnessValue] at hproduct
    refine ⟨hcorner, ?_⟩
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hproduct, mul_nonneg hcorner.le (neg_nonneg.mpr hblockNonpos)]
  by_cases hzeroMember : (0 : ℝ) ∈ pencilMemberSet
  · rw [hsetDef] at hzeroMember
    obtain ⟨honeMinor, htwoMinor, hthreeMinor⟩ := hzeroMember
    rw [hblockConstantDef] at htwoMinor
    rw [hcubicDef] at hthreeMinor
    refine posDef_of_leadingMinors_fin_three entryOneOne entryOneTwo
      entryOneThree entryTwoTwo entryTwoThree entryThreeThree ?_ ?_ ?_
    · linarith [honeMinor]
    · linarith [htwoMinor]
    · linarith [hthreeMinor]
  · exfalso
    set bigTime : ℝ := 1 + entryOneOne ^ 2 + blockCoefficient ^ 2
      + blockConstant ^ 2 with hbigDef
    clear_value bigTime
    have hbigOne : 1 ≤ bigTime := by
      rw [hbigDef]
      linarith [sq_nonneg entryOneOne, sq_nonneg blockCoefficient,
        sq_nonneg blockConstant]
    have hbigPos : 0 < bigTime := by linarith
    have hbigCorner : 1 + entryOneOne ^ 2 ≤ bigTime := by
      rw [hbigDef]
      linarith [sq_nonneg blockCoefficient, sq_nonneg blockConstant]
    have hbigBlockCoef : 1 + blockCoefficient ^ 2 ≤ bigTime := by
      rw [hbigDef]
      linarith [sq_nonneg entryOneOne, sq_nonneg blockConstant]
    have hbigBlockConst : 1 + blockConstant ^ 2 ≤ bigTime := by
      rw [hbigDef]
      linarith [sq_nonneg entryOneOne, sq_nonneg blockCoefficient]
    have hbigMember : bigTime ∈ pencilMemberSet := by
      rw [hsetDef]
      refine ⟨?_, ?_, ?_⟩
      · linarith [sq_nonneg (6 * entryOneOne + 1), hbigCorner]
      · have hcoefLower : -((1 + blockCoefficient ^ 2) / 2) ≤ blockCoefficient := by
          linarith [sq_nonneg (1 + blockCoefficient)]
        have hcoefProduct := mul_le_mul_of_nonneg_right hcoefLower hbigPos.le
        have hcoefSquare := mul_le_mul_of_nonneg_right hbigBlockCoef hbigPos.le
        have hconstLower : -((1 + blockConstant ^ 2) / 2) ≤ blockConstant := by
          linarith [sq_nonneg (1 + blockConstant)]
        have hbigSelf : bigTime ≤ bigTime ^ 2 := by
          linarith [mul_nonneg hbigPos.le (by linarith : (0:ℝ) ≤ bigTime - 1)]
        linarith [hcoefProduct, hcoefSquare, hconstLower, hbigBlockConst,
          hbigSelf, hbigOne]
      · have hcubeTerm : (0:ℝ) < bigTime ^ 3 := pow_pos hbigPos 3
        have hsquareTerm : (0:ℝ) < linearCoefficient * bigTime ^ 2 :=
          mul_pos hlinear (pow_pos hbigPos 2)
        have hlinearTerm : (0:ℝ) < quadraticCoefficient * bigTime :=
          mul_pos hquadratic hbigPos
        linarith [hcubeTerm, hsquareTerm, hlinearTerm, hcubic]
    have hSetNonempty : pencilMemberSet.Nonempty := ⟨bigTime, hbigMember⟩
    have hlowerBound : ∀ member ∈ pencilMemberSet, (0 : ℝ) ≤ member := by
      intro member hmember
      by_contra hnotNonneg
      have hmemberNeg : member < 0 := not_le.mp hnotNonneg
      apply hzeroMember
      have hformZero : ∀ vecArg : Fin 3 → ℝ, vecArg ≠ 0 →
          0 < vecArg ⬝ᵥ ((!![entryOneOne + 3 * (0:ℝ), entryOneTwo - (0:ℝ),
              entryOneThree - (0:ℝ);
              entryOneTwo - (0:ℝ), entryTwoTwo + 3 * (0:ℝ),
              entryTwoThree - (0:ℝ);
              entryOneThree - (0:ℝ), entryTwoThree - (0:ℝ),
              entryThreeThree + 3 * (0:ℝ)] : Matrix (Fin 3) (Fin 3) ℝ)
            *ᵥ vecArg) := by
        intro vecArg hne
        have hmemberForm := hmemberFormPos member hmember vecArg hne
        rw [hformEval member vecArg] at hmemberForm
        rw [hformEval (0:ℝ) vecArg]
        have hlapPos := kFourPencilLaplacianForm_pos vecArg hne
        linarith [hmemberForm, mul_pos (by linarith : (0:ℝ) < -member) hlapPos]
      obtain ⟨hcornerZero, hblockZero⟩ := hformGivesMinors (0:ℝ) hformZero
      rw [hsetDef]
      refine ⟨hcornerZero, hblockZero, ?_⟩
      linarith [hcubic]
    have hbddBelow : BddBelow pencilMemberSet :=
      ⟨0, fun member hmember => hlowerBound member hmember⟩
    set criticalTime : ℝ := sInf pencilMemberSet with hcriticalDef
    clear_value criticalTime
    have hcriticalNonneg : 0 ≤ criticalTime := by
      rw [hcriticalDef]
      exact le_csInf hSetNonempty hlowerBound
    have hdetCritical : 0 < 16 * criticalTime ^ 3
        + 8 * linearCoefficient * criticalTime ^ 2
        + quadraticCoefficient * criticalTime + cubicCoefficient := by
      have hcubeTerm : (0:ℝ) ≤ criticalTime ^ 3 := pow_nonneg hcriticalNonneg 3
      have hsquareTerm : (0:ℝ) ≤ linearCoefficient * criticalTime ^ 2 :=
        mul_nonneg hlinear.le (sq_nonneg criticalTime)
      have hlinearTerm : (0:ℝ) ≤ quadraticCoefficient * criticalTime :=
        mul_nonneg hquadratic.le hcriticalNonneg
      linarith [hcubeTerm, hsquareTerm, hlinearTerm, hcubic]
    have hpsdCritical : ∀ vecArg : Fin 3 → ℝ,
        0 ≤ vecArg ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
            entryOneTwo - criticalTime, entryOneThree - criticalTime;
            entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
            entryTwoThree - criticalTime;
            entryOneThree - criticalTime, entryTwoThree - criticalTime,
            entryThreeThree + 3 * criticalTime] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ vecArg) := by
      intro vecArg
      rcases eq_or_ne vecArg 0 with rfl | hne
      · simp
      · rw [hformEval criticalTime vecArg]
        set baseValue : ℝ := entryOneOne * vecArg 0 ^ 2
          + entryTwoTwo * vecArg 1 ^ 2 + entryThreeThree * vecArg 2 ^ 2
          + 2 * entryOneTwo * (vecArg 0 * vecArg 1)
          + 2 * entryOneThree * (vecArg 0 * vecArg 2)
          + 2 * entryTwoThree * (vecArg 1 * vecArg 2) with hbaseDef
        set laplacianValue : ℝ := 3 * vecArg 0 ^ 2 + 3 * vecArg 1 ^ 2
          + 3 * vecArg 2 ^ 2 - 2 * (vecArg 0 * vecArg 1)
          - 2 * (vecArg 0 * vecArg 2) - 2 * (vecArg 1 * vecArg 2)
          with hlaplacianDef
        clear_value baseValue laplacianValue
        have hlapPos : 0 < laplacianValue := by
          rw [hlaplacianDef]
          exact kFourPencilLaplacianForm_pos vecArg hne
        by_contra hnotNonneg
        have hformNeg : baseValue + criticalTime * laplacianValue < 0 :=
          not_le.mp hnotNonneg
        set epsilonValue : ℝ :=
          -(baseValue + criticalTime * laplacianValue) / (2 * laplacianValue)
          with hepsilonDef
        clear_value epsilonValue
        have hepsilonPos : 0 < epsilonValue := by
          rw [hepsilonDef]
          exact div_pos (by linarith) (by linarith)
        obtain ⟨member, hmember, hmemberLt⟩ :=
          exists_lt_of_csInf_lt hSetNonempty
            (show sInf pencilMemberSet < criticalTime + epsilonValue by
              rw [← hcriticalDef]; linarith)
        have hcriticalLe : criticalTime ≤ member := by
          rw [hcriticalDef]
          exact csInf_le hbddBelow hmember
        have hmemberForm := hmemberFormPos member hmember vecArg hne
        rw [hformEval member vecArg] at hmemberForm
        rw [← hbaseDef, ← hlaplacianDef] at hmemberForm
        have hlaplacianNe : laplacianValue ≠ 0 := ne_of_gt hlapPos
        have hepsilonLap : epsilonValue * laplacianValue
            = -(baseValue + criticalTime * laplacianValue) / 2 := by
          rw [hepsilonDef]
          field_simp
        have hshiftLt : member - criticalTime < epsilonValue := by linarith
        have hproductLt : (member - criticalTime) * laplacianValue
            < epsilonValue * laplacianValue :=
          mul_lt_mul_of_pos_right hshiftLt hlapPos
        linarith [hmemberForm, hproductLt, hepsilonLap, hformNeg]
    have hstrictCritical : ∀ vecArg : Fin 3 → ℝ, vecArg ≠ 0 →
        0 < vecArg ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
            entryOneTwo - criticalTime, entryOneThree - criticalTime;
            entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
            entryTwoThree - criticalTime;
            entryOneThree - criticalTime, entryTwoThree - criticalTime,
            entryThreeThree + 3 * criticalTime] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ vecArg) := by
      intro vecArg hne
      rcases (hpsdCritical vecArg).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hqZero : vecArg ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
            entryOneTwo - criticalTime, entryOneThree - criticalTime;
            entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
            entryTwoThree - criticalTime;
            entryOneThree - criticalTime, entryTwoThree - criticalTime,
            entryThreeThree + 3 * criticalTime] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ vecArg) = 0 := heq.symm
        have hexpandQuadratic : ∀ (scaleVal : ℝ) (otherVec : Fin 3 → ℝ),
            (vecArg + scaleVal • otherVec)
              ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
                entryOneTwo - criticalTime, entryOneThree - criticalTime;
                entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
                entryTwoThree - criticalTime;
                entryOneThree - criticalTime, entryTwoThree - criticalTime,
                entryThreeThree + 3 * criticalTime]
                : Matrix (Fin 3) (Fin 3) ℝ)
              *ᵥ (vecArg + scaleVal • otherVec))
            = vecArg ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
                entryOneTwo - criticalTime, entryOneThree - criticalTime;
                entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
                entryTwoThree - criticalTime;
                entryOneThree - criticalTime, entryTwoThree - criticalTime,
                entryThreeThree + 3 * criticalTime]
                : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ vecArg)
              + 2 * scaleVal * (vecArg
                ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
                  entryOneTwo - criticalTime, entryOneThree - criticalTime;
                  entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
                  entryTwoThree - criticalTime;
                  entryOneThree - criticalTime, entryTwoThree - criticalTime,
                  entryThreeThree + 3 * criticalTime]
                  : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ otherVec))
              + scaleVal ^ 2 * (otherVec
                ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
                  entryOneTwo - criticalTime, entryOneThree - criticalTime;
                  entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
                  entryTwoThree - criticalTime;
                  entryOneThree - criticalTime, entryTwoThree - criticalTime,
                  entryThreeThree + 3 * criticalTime]
                  : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ otherVec)) := by
          intro scaleVal otherVec
          simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul]
          ring
        have hpairingZero : ∀ otherVec : Fin 3 → ℝ,
            vecArg ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
              entryOneTwo - criticalTime, entryOneThree - criticalTime;
              entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
              entryTwoThree - criticalTime;
              entryOneThree - criticalTime, entryTwoThree - criticalTime,
              entryThreeThree + 3 * criticalTime]
              : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ otherVec) = 0 := by
          intro otherVec
          set pairingValue : ℝ := vecArg
            ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
              entryOneTwo - criticalTime, entryOneThree - criticalTime;
              entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
              entryTwoThree - criticalTime;
              entryOneThree - criticalTime, entryTwoThree - criticalTime,
              entryThreeThree + 3 * criticalTime]
              : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ otherVec) with hpairingDef
          set diagonalValue : ℝ := otherVec
            ⬝ᵥ ((!![entryOneOne + 3 * criticalTime,
              entryOneTwo - criticalTime, entryOneThree - criticalTime;
              entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
              entryTwoThree - criticalTime;
              entryOneThree - criticalTime, entryTwoThree - criticalTime,
              entryThreeThree + 3 * criticalTime]
              : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ otherVec) with hdiagonalDef
          clear_value pairingValue diagonalValue
          have hdiagonalNonneg : 0 ≤ diagonalValue := by
            rw [hdiagonalDef]
            exact hpsdCritical otherVec
          have hdiagonalShiftNe : diagonalValue + 1 ≠ 0 :=
            ne_of_gt (by linarith : (0:ℝ) < diagonalValue + 1)
          set scaleChoice : ℝ := -pairingValue / (diagonalValue + 1)
            with hscaleDef
          clear_value scaleChoice
          have hscaleEq : scaleChoice * (diagonalValue + 1) = -pairingValue := by
            rw [hscaleDef]
            field_simp
          have hquadNonneg := hpsdCritical (vecArg + scaleChoice • otherVec)
          rw [hexpandQuadratic scaleChoice otherVec, hqZero] at hquadNonneg
          rw [← hpairingDef, ← hdiagonalDef] at hquadNonneg
          have hproductNonneg : 0 ≤ (2 * scaleChoice * pairingValue
              + scaleChoice ^ 2 * diagonalValue) * (diagonalValue + 1) ^ 2 := by
            have hquadClean : 0 ≤ 2 * scaleChoice * pairingValue
                + scaleChoice ^ 2 * diagonalValue := by linarith [hquadNonneg]
            exact mul_nonneg hquadClean (sq_nonneg _)
          have hrewriteProduct : (2 * scaleChoice * pairingValue
              + scaleChoice ^ 2 * diagonalValue) * (diagonalValue + 1) ^ 2
              = 2 * (scaleChoice * (diagonalValue + 1)) * pairingValue
                  * (diagonalValue + 1)
                + (scaleChoice * (diagonalValue + 1)) ^ 2 * diagonalValue := by
            ring
          rw [hrewriteProduct, hscaleEq] at hproductNonneg
          have hsquareZero : pairingValue ^ 2 = 0 := by
            refine le_antisymm ?_ (sq_nonneg _)
            nlinarith [hproductNonneg, hdiagonalNonneg, sq_nonneg pairingValue]
          exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hsquareZero
        have hkernel : (!![entryOneOne + 3 * criticalTime,
            entryOneTwo - criticalTime, entryOneThree - criticalTime;
            entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
            entryTwoThree - criticalTime;
            entryOneThree - criticalTime, entryTwoThree - criticalTime,
            entryThreeThree + 3 * criticalTime] : Matrix (Fin 3) (Fin 3) ℝ)
            *ᵥ vecArg = 0 := by
          have hpairZero := hpairingZero ![1, 0, 0]
          have hpairOne := hpairingZero ![0, 1, 0]
          have hpairTwo := hpairingZero ![0, 0, 1]
          simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
            at hpairZero hpairOne hpairTwo
          funext index
          fin_cases index <;>
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
            linarith [hpairZero, hpairOne, hpairTwo]
        have hdetZero : (!![entryOneOne + 3 * criticalTime,
            entryOneTwo - criticalTime, entryOneThree - criticalTime;
            entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
            entryTwoThree - criticalTime;
            entryOneThree - criticalTime, entryTwoThree - criticalTime,
            entryThreeThree + 3 * criticalTime]
            : Matrix (Fin 3) (Fin 3) ℝ).det = 0 :=
          Matrix.exists_mulVec_eq_zero_iff.mp ⟨vecArg, hne, hkernel⟩
        have hdetEval : (!![entryOneOne + 3 * criticalTime,
            entryOneTwo - criticalTime, entryOneThree - criticalTime;
            entryOneTwo - criticalTime, entryTwoTwo + 3 * criticalTime,
            entryTwoThree - criticalTime;
            entryOneThree - criticalTime, entryTwoThree - criticalTime,
            entryThreeThree + 3 * criticalTime]
            : Matrix (Fin 3) (Fin 3) ℝ).det
            = 16 * criticalTime ^ 3
              + 8 * linearCoefficient * criticalTime ^ 2
              + quadraticCoefficient * criticalTime + cubicCoefficient := by
          rw [hlinearDef, hquadraticDef, hcubicDef]
          simp [Matrix.det_fin_three]
          ring
        rw [hdetEval] at hdetZero
        linarith [hdetCritical]
    obtain ⟨hcornerCritical, hblockCritical⟩ :=
      hformGivesMinors criticalTime hstrictCritical
    have hcriticalMember : criticalTime ∈ pencilMemberSet := by
      rw [hsetDef]
      exact ⟨hcornerCritical, hblockCritical, hdetCritical⟩
    set cornerCritical : ℝ := entryOneOne + 3 * criticalTime
      with hcornerCriticalDef
    set blockValueCritical : ℝ := 8 * criticalTime ^ 2
      + blockCoefficient * criticalTime + blockConstant
      with hblockValueCriticalDef
    set cubicValueCritical : ℝ := 16 * criticalTime ^ 3
      + 8 * linearCoefficient * criticalTime ^ 2
      + quadraticCoefficient * criticalTime + cubicCoefficient
      with hcubicValueCriticalDef
    set blockSlope : ℝ := 16 * criticalTime + blockCoefficient
      with hblockSlopeDef
    set cubicSlope : ℝ := 48 * criticalTime ^ 2
      + 16 * linearCoefficient * criticalTime + quadraticCoefficient
      with hcubicSlopeDef
    set cubicCurve : ℝ := 48 * criticalTime + 8 * linearCoefficient
      with hcubicCurveDef
    clear_value cornerCritical blockValueCritical cubicValueCritical
      blockSlope cubicSlope cubicCurve
    set shiftAmount : ℝ := min 1 (min (cornerCritical / 6)
      (min (blockValueCritical / (1 + blockSlope ^ 2))
        (cubicValueCritical / (2 * (17 + cubicSlope ^ 2 + cubicCurve ^ 2)))))
      with hshiftDef
    clear_value shiftAmount
    have hblockDenPos : (0:ℝ) < 1 + blockSlope ^ 2 := by positivity
    have hcubicDenPos : (0:ℝ) < 2 * (17 + cubicSlope ^ 2 + cubicCurve ^ 2) := by
      positivity
    have hshiftPos : 0 < shiftAmount := by
      rw [hshiftDef]
      refine lt_min (by norm_num) (lt_min ?_ (lt_min ?_ ?_))
      · exact div_pos hcornerCritical (by norm_num)
      · exact div_pos hblockCritical hblockDenPos
      · exact div_pos hdetCritical hcubicDenPos
    have hshiftLeOne : shiftAmount ≤ 1 := by
      rw [hshiftDef]
      exact min_le_left _ _
    have hshiftLeCorner : shiftAmount ≤ cornerCritical / 6 := by
      rw [hshiftDef]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hshiftLeBlock : shiftAmount
        ≤ blockValueCritical / (1 + blockSlope ^ 2) := by
      rw [hshiftDef]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have hshiftLeCubic : shiftAmount
        ≤ cubicValueCritical / (2 * (17 + cubicSlope ^ 2 + cubicCurve ^ 2)) := by
      rw [hshiftDef]
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))
    have hshiftBlockProduct : shiftAmount * (1 + blockSlope ^ 2)
        ≤ blockValueCritical := (le_div_iff₀ hblockDenPos).mp hshiftLeBlock
    have hshiftCubicProduct : shiftAmount
        * (2 * (17 + cubicSlope ^ 2 + cubicCurve ^ 2))
        ≤ cubicValueCritical := (le_div_iff₀ hcubicDenPos).mp hshiftLeCubic
    have hshiftMember : criticalTime - shiftAmount ∈ pencilMemberSet := by
      rw [hsetDef]
      refine ⟨?_, ?_, ?_⟩
      · have hexpand : entryOneOne + 3 * (criticalTime - shiftAmount)
            = cornerCritical - 3 * shiftAmount := by
          rw [hcornerCriticalDef]
          ring
        rw [hexpand]
        linarith [hshiftLeCorner, hcornerCritical]
      · have hexpand : 8 * (criticalTime - shiftAmount) ^ 2
            + blockCoefficient * (criticalTime - shiftAmount) + blockConstant
            = blockValueCritical - shiftAmount * blockSlope
              + 8 * shiftAmount ^ 2 := by
          rw [hblockValueCriticalDef, hblockSlopeDef]
          ring
        rw [hexpand]
        have hslopeUpper : blockSlope ≤ (1 + blockSlope ^ 2) / 2 := by
          linarith [sq_nonneg (1 - blockSlope)]
        have hslopeProduct : shiftAmount * blockSlope
            ≤ shiftAmount * ((1 + blockSlope ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hslopeUpper hshiftPos.le
        linarith [hslopeProduct, hshiftBlockProduct, sq_nonneg shiftAmount,
          hblockCritical]
      · have hexpand : 16 * (criticalTime - shiftAmount) ^ 3
            + 8 * linearCoefficient * (criticalTime - shiftAmount) ^ 2
            + quadraticCoefficient * (criticalTime - shiftAmount)
            + cubicCoefficient
            = cubicValueCritical - shiftAmount * cubicSlope
              + shiftAmount ^ 2 * cubicCurve - 16 * shiftAmount ^ 3 := by
          rw [hcubicValueCriticalDef, hcubicSlopeDef, hcubicCurveDef]
          ring
        rw [hexpand]
        have hslopeUpper : cubicSlope ≤ (1 + cubicSlope ^ 2) / 2 := by
          linarith [sq_nonneg (1 - cubicSlope)]
        have hcurveLower : -((1 + cubicCurve ^ 2) / 2) ≤ cubicCurve := by
          linarith [sq_nonneg (1 + cubicCurve)]
        have hsquareLe : shiftAmount ^ 2 ≤ shiftAmount := by
          linarith [mul_nonneg hshiftPos.le
            (by linarith : (0:ℝ) ≤ 1 - shiftAmount)]
        have hcubeLe : shiftAmount ^ 3 ≤ shiftAmount := by
          linarith [mul_nonneg (mul_nonneg hshiftPos.le hshiftPos.le)
            (by linarith : (0:ℝ) ≤ 1 - shiftAmount), hsquareLe]
        have hslopeProduct : shiftAmount * cubicSlope
            ≤ shiftAmount * ((1 + cubicSlope ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hslopeUpper hshiftPos.le
        have hcurveProduct : shiftAmount ^ 2 * (-((1 + cubicCurve ^ 2) / 2))
            ≤ shiftAmount ^ 2 * cubicCurve :=
          mul_le_mul_of_nonneg_left hcurveLower (sq_nonneg _)
        have hcurveSquare : shiftAmount ^ 2 * ((1 + cubicCurve ^ 2) / 2)
            ≤ shiftAmount * ((1 + cubicCurve ^ 2) / 2) :=
          mul_le_mul_of_nonneg_right hsquareLe (by positivity)
        have hslopeSquareNonneg : (0:ℝ) ≤ shiftAmount * cubicSlope ^ 2 :=
          mul_nonneg hshiftPos.le (sq_nonneg _)
        have hcurveSquareNonneg : (0:ℝ) ≤ shiftAmount * cubicCurve ^ 2 :=
          mul_nonneg hshiftPos.le (sq_nonneg _)
        linarith [hslopeProduct, hcurveProduct, hcurveSquare, hcubeLe,
          hshiftCubicProduct, hslopeSquareNonneg, hcurveSquareNonneg,
          hdetCritical]
    have hcontradiction : criticalTime ≤ criticalTime - shiftAmount := by
      have hinfLe := csInf_le hbddBelow hshiftMember
      rw [← hcriticalDef] at hinfLe
      exact hinfLe
    linarith [hshiftPos, hcontradiction]

/-- Positive definiteness forces the linear pencil coefficient: the entry
sum is one half of `q(e0) + q(e1) + q(e2) + q(ones)`. -/
theorem invariantPencilLinear_pos_of_posDef
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ)
    (hposDef : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef) :
    0 < entryOneOne + entryTwoTwo + entryThreeThree
      + entryOneTwo + entryOneThree + entryTwoThree := by
  have hbasisZeroNe : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcomp := congrFun hzero 0
    norm_num at hcomp
  have hbasisOneNe : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcomp := congrFun hzero 1
    norm_num at hcomp
  have hbasisTwoNe : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcomp := congrFun hzero 2
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcomp
  have honesNe : (![1, 1, 1] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcomp := congrFun hzero 0
    norm_num at hcomp
  have hvalueZero := hposDef.dotProduct_mulVec_pos hbasisZeroNe
  have hvalueOne := hposDef.dotProduct_mulVec_pos hbasisOneNe
  have hvalueTwo := hposDef.dotProduct_mulVec_pos hbasisTwoNe
  have hvalueOnes := hposDef.dotProduct_mulVec_pos honesNe
  rw [star_trivial] at hvalueZero hvalueOne hvalueTwo hvalueOnes
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    at hvalueZero hvalueOne hvalueTwo hvalueOnes
  linarith [hvalueZero, hvalueOne, hvalueTwo, hvalueOnes]

set_option maxHeartbeats 800000 in
/-- Positive definiteness forces the quadratic pencil coefficient: the
invariant quadratic is the sum of the six plane-restriction block
determinants (the adjugate compound identity), one per K4 edge
direction, each positive by a completed-square witness. -/
theorem invariantPencilQuadratic_pos_of_posDef
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ)
    (hposDef : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef) :
    0 < 3 * entryOneOne * entryTwoTwo + 3 * entryOneOne * entryThreeThree
      + 3 * entryTwoTwo * entryThreeThree + 2 * entryOneOne * entryTwoThree
      + 2 * entryTwoTwo * entryOneThree + 2 * entryThreeThree * entryOneTwo
      - 3 * entryOneTwo ^ 2 - 3 * entryOneThree ^ 2 - 3 * entryTwoThree ^ 2
      - 2 * entryOneTwo * entryOneThree - 2 * entryOneTwo * entryTwoThree
      - 2 * entryOneThree * entryTwoThree := by
  have hformPos : ∀ probeVec : Fin 3 → ℝ, probeVec ≠ 0 →
      0 < probeVec ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
        : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probeVec) := by
    intro probeVec hne
    have hvalue := hposDef.dotProduct_mulVec_pos hne
    rwa [star_trivial] at hvalue
  have hcornerPos : 0 < entryOneOne := by
    have hne : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 0
      norm_num at hcomp
    have hvalue := hformPos _ hne
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
    linarith [hvalue]
  have hdiagTwoPos : 0 < entryTwoTwo := by
    have hne : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 1
      norm_num at hcomp
    have hvalue := hformPos _ hne
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
    linarith [hvalue]
  have hblockFive : 0 < entryOneOne * entryTwoTwo - entryOneTwo ^ 2 := by
    have hne : (![entryOneTwo, -entryOneOne, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 1
      norm_num at hcomp
      exact absurd hcomp (ne_of_gt hcornerPos)
    have hvalue := hformPos _ hne
    have hrewrite : (![entryOneTwo, -entryOneOne, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
          entryOneTwo, entryTwoTwo, entryTwoThree;
          entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![entryOneTwo, -entryOneOne, 0])
        = entryOneOne * (entryOneOne * entryTwoTwo - entryOneTwo ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hrewrite] at hvalue
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hvalue, mul_nonneg hcornerPos.le (neg_nonneg.mpr hblockNonpos)]
  have hblockFour : 0 < entryOneOne * entryThreeThree - entryOneThree ^ 2 := by
    have hne : (![entryOneThree, 0, -entryOneOne] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 2
      norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        at hcomp
      exact absurd hcomp (ne_of_gt hcornerPos)
    have hvalue := hformPos _ hne
    have hrewrite : (![entryOneThree, 0, -entryOneOne] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
          entryOneTwo, entryTwoTwo, entryTwoThree;
          entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![entryOneThree, 0, -entryOneOne])
        = entryOneOne * (entryOneOne * entryThreeThree - entryOneThree ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hrewrite] at hvalue
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hvalue, mul_nonneg hcornerPos.le (neg_nonneg.mpr hblockNonpos)]
  have hblockThree : 0 < entryTwoTwo * entryThreeThree - entryTwoThree ^ 2 := by
    have hne : (![0, entryTwoThree, -entryTwoTwo] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 2
      norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        at hcomp
      exact absurd hcomp (ne_of_gt hdiagTwoPos)
    have hvalue := hformPos _ hne
    have hrewrite : (![0, entryTwoThree, -entryTwoTwo] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
          entryOneTwo, entryTwoTwo, entryTwoThree;
          entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![0, entryTwoThree, -entryTwoTwo])
        = entryTwoTwo * (entryTwoTwo * entryThreeThree - entryTwoThree ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hrewrite] at hvalue
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hvalue, mul_nonneg hdiagTwoPos.le (neg_nonneg.mpr hblockNonpos)]
  have hplaneZeroPos : 0 < entryOneOne + entryTwoTwo + 2 * entryOneTwo := by
    have hne : (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 0
      norm_num at hcomp
    have hvalue := hformPos _ hne
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
    linarith [hvalue]
  have hblockZero : 0 < (entryOneOne + entryTwoTwo + 2 * entryOneTwo)
      * entryThreeThree - (entryOneThree + entryTwoThree) ^ 2 := by
    have hne : (![entryOneThree + entryTwoThree, entryOneThree + entryTwoThree,
        -(entryOneOne + entryTwoTwo + 2 * entryOneTwo)] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 2
      norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        at hcomp
      linarith [hcomp, hplaneZeroPos]
    have hvalue := hformPos _ hne
    have hrewrite : (![entryOneThree + entryTwoThree,
          entryOneThree + entryTwoThree,
          -(entryOneOne + entryTwoTwo + 2 * entryOneTwo)] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
          entryOneTwo, entryTwoTwo, entryTwoThree;
          entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![entryOneThree + entryTwoThree, entryOneThree + entryTwoThree,
            -(entryOneOne + entryTwoTwo + 2 * entryOneTwo)])
        = (entryOneOne + entryTwoTwo + 2 * entryOneTwo)
          * ((entryOneOne + entryTwoTwo + 2 * entryOneTwo) * entryThreeThree
            - (entryOneThree + entryTwoThree) ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hrewrite] at hvalue
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hvalue, mul_nonneg hplaneZeroPos.le (neg_nonneg.mpr hblockNonpos)]
  have hplaneOnePos : 0 < entryOneOne + entryThreeThree + 2 * entryOneThree := by
    have hne : (![1, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 0
      norm_num at hcomp
    have hvalue := hformPos _ hne
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
    linarith [hvalue]
  have hblockOne : 0 < (entryOneOne + entryThreeThree + 2 * entryOneThree)
      * entryTwoTwo - (entryOneTwo + entryTwoThree) ^ 2 := by
    have hne : (![entryOneTwo + entryTwoThree,
        -(entryOneOne + entryThreeThree + 2 * entryOneThree),
        entryOneTwo + entryTwoThree] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 1
      norm_num at hcomp
      linarith [hcomp, hplaneOnePos]
    have hvalue := hformPos _ hne
    have hrewrite : (![entryOneTwo + entryTwoThree,
          -(entryOneOne + entryThreeThree + 2 * entryOneThree),
          entryOneTwo + entryTwoThree] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
          entryOneTwo, entryTwoTwo, entryTwoThree;
          entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![entryOneTwo + entryTwoThree,
            -(entryOneOne + entryThreeThree + 2 * entryOneThree),
            entryOneTwo + entryTwoThree])
        = (entryOneOne + entryThreeThree + 2 * entryOneThree)
          * ((entryOneOne + entryThreeThree + 2 * entryOneThree) * entryTwoTwo
            - (entryOneTwo + entryTwoThree) ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hrewrite] at hvalue
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hvalue, mul_nonneg hplaneOnePos.le (neg_nonneg.mpr hblockNonpos)]
  have hplaneTwoPos : 0 < entryTwoTwo + entryThreeThree + 2 * entryTwoThree := by
    have hne : (![0, 1, 1] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 1
      norm_num at hcomp
    have hvalue := hformPos _ hne
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
    linarith [hvalue]
  have hblockTwo : 0 < (entryTwoTwo + entryThreeThree + 2 * entryTwoThree)
      * entryOneOne - (entryOneTwo + entryOneThree) ^ 2 := by
    have hne : (![-(entryTwoTwo + entryThreeThree + 2 * entryTwoThree),
        entryOneTwo + entryOneThree, entryOneTwo + entryOneThree]
        : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 0
      norm_num at hcomp
      linarith [hcomp, hplaneTwoPos]
    have hvalue := hformPos _ hne
    have hrewrite : (![-(entryTwoTwo + entryThreeThree + 2 * entryTwoThree),
          entryOneTwo + entryOneThree, entryOneTwo + entryOneThree]
          : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
          entryOneTwo, entryTwoTwo, entryTwoThree;
          entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![-(entryTwoTwo + entryThreeThree + 2 * entryTwoThree),
            entryOneTwo + entryOneThree, entryOneTwo + entryOneThree])
        = (entryTwoTwo + entryThreeThree + 2 * entryTwoThree)
          * ((entryTwoTwo + entryThreeThree + 2 * entryTwoThree) * entryOneOne
            - (entryOneTwo + entryOneThree) ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hrewrite] at hvalue
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hvalue, mul_nonneg hplaneTwoPos.le (neg_nonneg.mpr hblockNonpos)]
  linarith [hblockZero, hblockOne, hblockTwo, hblockThree, hblockFour,
    hblockFive]

/-- Positive definiteness forces the cubic pencil coefficient (the
determinant), by the adjugate-column witness against the leading `2x2`
minor. -/
theorem invariantPencilCubic_pos_of_posDef
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ)
    (hposDef : (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef) :
    0 < entryOneOne * entryTwoTwo * entryThreeThree
      - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
      + 2 * entryOneTwo * entryOneThree * entryTwoThree
      - entryOneThree ^ 2 * entryTwoTwo := by
  have hformPos : ∀ probeVec : Fin 3 → ℝ, probeVec ≠ 0 →
      0 < probeVec ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
        : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probeVec) := by
    intro probeVec hne
    have hvalue := hposDef.dotProduct_mulVec_pos hne
    rwa [star_trivial] at hvalue
  have hcornerPos : 0 < entryOneOne := by
    have hne : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 0
      norm_num at hcomp
    have hvalue := hformPos _ hne
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three] at hvalue
    linarith [hvalue]
  have hblockPos : 0 < entryOneOne * entryTwoTwo - entryOneTwo ^ 2 := by
    have hne : (![entryOneTwo, -entryOneOne, 0] : Fin 3 → ℝ) ≠ 0 := by
      intro hzero
      have hcomp := congrFun hzero 1
      norm_num at hcomp
      exact absurd hcomp (ne_of_gt hcornerPos)
    have hvalue := hformPos _ hne
    have hrewrite : (![entryOneTwo, -entryOneOne, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
          entryOneTwo, entryTwoTwo, entryTwoThree;
          entryOneThree, entryTwoThree, entryThreeThree]
          : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ ![entryOneTwo, -entryOneOne, 0])
        = entryOneOne * (entryOneOne * entryTwoTwo - entryOneTwo ^ 2) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      ring
    rw [hrewrite] at hvalue
    by_contra hnotBlock
    have hblockNonpos := not_lt.mp hnotBlock
    linarith [hvalue, mul_nonneg hcornerPos.le (neg_nonneg.mpr hblockNonpos)]
  have hwitnessNe : (![entryOneTwo * entryTwoThree - entryOneThree * entryTwoTwo,
      entryOneThree * entryOneTwo - entryOneOne * entryTwoThree,
      entryOneOne * entryTwoTwo - entryOneTwo ^ 2] : Fin 3 → ℝ) ≠ 0 := by
    intro hzero
    have hcomp := congrFun hzero 2
    norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hcomp
    exact absurd hcomp (ne_of_gt hblockPos)
  have hvalue := hformPos _ hwitnessNe
  have hrewrite : (![entryOneTwo * entryTwoThree - entryOneThree * entryTwoTwo,
        entryOneThree * entryOneTwo - entryOneOne * entryTwoThree,
        entryOneOne * entryTwoTwo - entryOneTwo ^ 2] : Fin 3 → ℝ)
      ⬝ᵥ ((!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
        : Matrix (Fin 3) (Fin 3) ℝ)
        *ᵥ ![entryOneTwo * entryTwoThree - entryOneThree * entryTwoTwo,
          entryOneThree * entryOneTwo - entryOneOne * entryTwoThree,
          entryOneOne * entryTwoTwo - entryOneTwo ^ 2])
      = (entryOneOne * entryTwoTwo * entryThreeThree
          - entryOneOne * entryTwoThree ^ 2
          - entryOneTwo ^ 2 * entryThreeThree
          + 2 * entryOneTwo * entryOneThree * entryTwoThree
          - entryOneThree ^ 2 * entryTwoTwo)
        * (entryOneOne * entryTwoTwo - entryOneTwo ^ 2) := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  rw [hrewrite] at hvalue
  by_contra hnotCubic
  have hcubicNonpos := not_lt.mp hnotCubic
  linarith [hvalue, mul_nonneg (neg_nonneg.mpr hcubicNonpos) hblockPos.le]

/-- **The kernel equivalence of the invariant-Sylvester triple.**
Positive definiteness of a symmetric `3x3` matrix is EQUIVALENT to
positivity of the three invariant pencil coefficients — the frame-free
restatement of Sylvester's criterion the knife band certifies against. -/
theorem posDef_iff_invariantPencilTriple
    (entryOneOne entryOneTwo entryOneThree entryTwoTwo entryTwoThree
      entryThreeThree : ℝ) :
    (!![entryOneOne, entryOneTwo, entryOneThree;
        entryOneTwo, entryTwoTwo, entryTwoThree;
        entryOneThree, entryTwoThree, entryThreeThree]
      : Matrix (Fin 3) (Fin 3) ℝ).PosDef
    ↔ (0 < entryOneOne + entryTwoTwo + entryThreeThree
          + entryOneTwo + entryOneThree + entryTwoThree
        ∧ 0 < 3 * entryOneOne * entryTwoTwo
          + 3 * entryOneOne * entryThreeThree
          + 3 * entryTwoTwo * entryThreeThree
          + 2 * entryOneOne * entryTwoThree + 2 * entryTwoTwo * entryOneThree
          + 2 * entryThreeThree * entryOneTwo
          - 3 * entryOneTwo ^ 2 - 3 * entryOneThree ^ 2
          - 3 * entryTwoThree ^ 2
          - 2 * entryOneTwo * entryOneThree - 2 * entryOneTwo * entryTwoThree
          - 2 * entryOneThree * entryTwoThree
        ∧ 0 < entryOneOne * entryTwoTwo * entryThreeThree
          - entryOneOne * entryTwoThree ^ 2 - entryOneTwo ^ 2 * entryThreeThree
          + 2 * entryOneTwo * entryOneThree * entryTwoThree
          - entryOneThree ^ 2 * entryTwoTwo) := by
  constructor
  · intro hposDef
    exact ⟨invariantPencilLinear_pos_of_posDef _ _ _ _ _ _ hposDef,
      invariantPencilQuadratic_pos_of_posDef _ _ _ _ _ _ hposDef,
      invariantPencilCubic_pos_of_posDef _ _ _ _ _ _ hposDef⟩
  · intro htriple
    exact posDef_of_invariantPencilTriple _ _ _ _ _ _ htriple.1 htriple.2.1
      htriple.2.2

/-! ### The engine firing on the knife band

`heavyPairRefuterPoint` is the one mandatory point outside atlas
Layer A (no star cell, no harmonic cell fires there).  The invariant
triple certifies its through-edge-3 tree `{0, 1, 3}` from three
polynomial evaluations: `D1 = 3339/20`, `D2 = 1145083/1200`,
`D3 = 33967979/216000`. -/

/-- Entrywise chart gap at the dual refuter for the through-edge-3 tree
`{0, 1, 3}`. -/
theorem heavyPairRefuter_gap_zeroOneThree_eq :
    directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 1, 3}
      = !![11219/60, -24, -59/60; -24, 239/60, 1/60; -59/60, 1/60, 19/20] := by
  simp only [directionChartGap, heavyPairRefuterPoint_mass_eq,
    heavyPairRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [kFourDirection, atomMatrix, Matrix.sub_apply] <;>
    norm_num

/-- The knife-band demonstration: the invariant-Sylvester engine
certifies the strictly dominating tree `{0, 1, 3}` at
`heavyPairRefuterPoint` by evaluating the three fixed polynomials —
no Layer-A cell fires at this point. -/
theorem heavyPairRefuter_gap_zeroOneThree_posDef :
    (directionChartGap kFourDirection heavyPairRefuterPoint.mass
        heavyPairRefuterPoint.weight {0, 1, 3}).PosDef := by
  rw [heavyPairRefuter_gap_zeroOneThree_eq]
  refine posDef_of_invariantPencilTriple (11219/60) (-24) (-59/60) (239/60)
    (1/60) (19/20) ?_ ?_ ?_ <;> norm_num

end Gtz
