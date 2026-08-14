import Gtz.Wave.AtomDeepCutRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The coherent triangle: the oriented sign as a domination certificate

Every certificate of the atom lane up to this module reads the SQUARE of a
Gram entry.  A square carries no sign, thus every such certificate is
field-agnostic and the complex two-trine survives it.  This module supplies
the first family of atom-lane certificates that read the ORIENTED SIGN of a
triangle, and the sign is the one ingredient the complex obstruction cannot
carry.

The object is the TRIANGLE CYCLE of three slots, the product of the three
Gram entries around the triangle.  Two facts drive the module.

The cycle is a gauge invariant.  Negating an atom flips two of the three
entries of every triangle through it, thus it fixes the cycle, and it fixes
the shifted diagonal, the pair minor and the triple determinant as well.
This is Seidel switching, and layer zero states it slot by slot.

The cycle splits the triple determinant.  With the TRIANGLE GAP of a vertex,
the shifted diagonal of that vertex against the square of the opposite edge
minus the cycle, the determinant obeys

  `cycle ^ 2 * det = gapOne * gapTwo * gapThree
      + cycle * (gapOne * gapTwo + gapOne * gapThree + gapTwo * gapThree)`

which is a polynomial identity.  A triangle of positive cycle and three
positive gaps therefore has a positive determinant, and the pair minors and
the shifted diagonals come from two companion identities of the same shape.
The result is the COHERENT PRODUCT CELL, and it is sharp along the balanced
direction: three equal correlations of any modulus below one pass it, while
the half-box cell of `Gtz/LinAlg/SignForcing.lean` stops at `1/√2`.

Three more cells come from the same algebra: the half-box cell in raw
scalars, the energy cell, and the orthogonal-apex cell.

Layer three consumes the landed sign forcing.  Six real atoms of rank three
carry a triangle of nonnegative cycle, because `3 + 2 = 5` is the threshold
of `Gtz.exists_pos_triangleProduct_of_card_ge` and six exceeds it.  Over the
complex field the same threshold is `2 * 3 + 2 = 8`, thus six atoms sit
strictly inside the window where the real argument forces and the complex one
does not.  Layer four turns the cells around: at a datum with no dominating
triple, every coherent triangle carries a nonpositive gap and a strong edge.

## MEASURED, and recorded here so that no successor repeats it

The cells do NOT cover the blocked stratum.  An adversarial search over the
doubly blocked stratum reaches a datum whose best triple dominates by `0.143`
while every one of the twenty triples fails all three cells by at least
`0.69`.  A second search reaches a blocked datum at which NO coherent triple
dominates at all.  Coherence is therefore a certificate, not a selection
rule, and a residue must never be narrowed to the coherent triples.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.atomSwitch` and its eight invariance laws — **SEIDEL SWITCHING AT THE
  ATOM INTERFACE**: signs are free, and the frame law survives them.
* `Gtz.atomTriangleCycle`, `Gtz.atomTriangleGap`, `Gtz.atomTriangleSlack`,
  `Gtz.atomTripleVolume`, `Gtz.atomTripleReading` — the triangle calculus.
* `Gtz.atomTripleDet_mul_cycle_sq`, `Gtz.atomShiftedDiag_mul_edge_sq`,
  `Gtz.atomPairMinor_mul_edge_sq`, `Gtz.atomTripleDet_eq_energy`,
  `Gtz.atomTripleVolume_sq_sub_cycle_sq`, `Gtz.atomTriangleHalfBox_split` —
  **THE SIX EXACT IDENTITIES**, all verified at zero residual before
  transcription.
* `Gtz.atomTripleDet_pos_of_coherentGaps`,
  `Gtz.exists_deflated_pair_of_coherentGaps` — **THE COHERENT PRODUCT CELL.**
* `Gtz.atomTripleDet_pos_of_coherentHalfBox`,
  `Gtz.exists_deflated_pair_of_coherentHalfBox` — the half-box cell in raw
  scalars, with no normalisation and no square root.
* `Gtz.atomTripleDet_pos_of_coherentEnergy`,
  `Gtz.exists_deflated_pair_of_orthogonalApex` — the two cheap cells.
* `Gtz.exists_coherent_atomTriple`, `Gtz.exists_pos_coherent_atomTriple` —
  **THE PARITY SUPPLY** at six real atoms of rank three.
* `Gtz.six_lt_complexSignForcing_threshold` — the field door as a number.
* `Gtz.exists_flat_coherent_triangle_of_no_dominating_triple`,
  `Gtz.exists_strong_edge_of_no_dominating_triple` — **THE COUNTEREXAMPLE
  CONSTRAINTS**: a datum with no dominating triple carries a coherent
  triangle with a nonpositive gap, and, when every slot is live, a pair whose
  shifted diagonals fail the half-box against their Gram entry.
* `Gtz.atomPairMinor_neg_of_parallel` — a parallel pair kills every triple
  through it.

## Vacuity

Layers zero, one and two are unconditional statements about a family of
vectors, a family of scales and three slots.  Layer three consumes only the
cardinality `5 ≤ 6`.  Layer four is the contrapositive of layers two and
three together, thus it is as nonvacuous as they are.
-/

namespace Gtz

/-! ## Layer 0 — Seidel switching at the atom interface -/

/-- The SWITCHED FAMILY: each atom rescaled by its own sign.  When every sign
squares to one this is Seidel switching, the gauge freedom of the oriented
sign pattern. -/
def atomSwitch {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (sign : Fin slotCount → ℝ) : Fin slotCount → (Fin rank → ℝ) :=
  fun slot => sign slot • atom slot

/-- The Gram of the switched family carries the two signs of its slots. -/
theorem atomGram_atomSwitch {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (sign : Fin slotCount → ℝ) (rowSlot colSlot : Fin slotCount) :
    atomGram (atomSwitch atom sign) rowSlot colSlot
      = sign rowSlot * sign colSlot * atomGram atom rowSlot colSlot := by
  simp only [atomGram, atomSwitch, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- A sign that squares to one multiplies to one against itself. -/
theorem sign_mul_self_of_sq_eq_one {value : ℝ} (hsq : value ^ 2 = 1) :
    value * value = 1 := by linear_combination hsq

/-- **THE GAUGE CANCELS IN A SQUARE.**  Two signs of square one leave the
square of a scalar untouched. -/
theorem sign_pair_mul_sq {signOne signTwo entry : ℝ} (hone : signOne ^ 2 = 1)
    (htwo : signTwo ^ 2 = 1) : (signOne * signTwo * entry) ^ 2 = entry ^ 2 := by
  linear_combination (entry ^ 2 * signTwo ^ 2) * hone + entry ^ 2 * htwo

/-- **THE GAUGE CANCELS AROUND A TRIANGLE.**  Each of the three signs occurs
in exactly two of the three edges, thus no odd power survives. -/
theorem sign_cycle_mul {signOne signTwo signThree entryOne entryTwo entryThree : ℝ}
    (hone : signOne ^ 2 = 1) (htwo : signTwo ^ 2 = 1) (hthree : signThree ^ 2 = 1) :
    (signOne * signTwo * entryOne) * (signOne * signThree * entryTwo)
        * (signTwo * signThree * entryThree)
      = entryOne * entryTwo * entryThree := by
  linear_combination (signTwo ^ 2 * signThree ^ 2 * entryOne * entryTwo * entryThree) * hone
    + (signThree ^ 2 * entryOne * entryTwo * entryThree) * htwo
    + (entryOne * entryTwo * entryThree) * hthree

/-- **THE SHIFTED DIAGONAL IS GAUGE INVARIANT.** -/
theorem atomShiftedDiag_atomSwitch {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {sign : Fin slotCount → ℝ} {slot : Fin slotCount} (hsq : sign slot ^ 2 = 1) :
    atomShiftedDiag (atomSwitch atom sign) scale slot
      = atomShiftedDiag atom scale slot := by
  simp only [atomShiftedDiag, atomGram_atomSwitch, sign_mul_self_of_sq_eq_one hsq, one_mul]

/-- **THE PAIR MINOR IS GAUGE INVARIANT.** -/
theorem atomPairMinor_atomSwitch {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {sign : Fin slotCount → ℝ} {rowSlot colSlot : Fin slotCount}
    (hrow : sign rowSlot ^ 2 = 1) (hcol : sign colSlot ^ 2 = 1) :
    atomPairMinor (atomSwitch atom sign) scale rowSlot colSlot
      = atomPairMinor atom scale rowSlot colSlot := by
  simp only [atomPairMinor, atomShiftedDiag_atomSwitch atom scale hrow,
    atomShiftedDiag_atomSwitch atom scale hcol, atomGram_atomSwitch,
    sign_pair_mul_sq hrow hcol]

/-- **THE DEFLATED CROSS ENTRY CARRIES THE TWO OFF-PIVOT SIGNS.**  The pivot
sign cancels against itself, which is exactly why the deflated pair test is a
statement about the two-graph. -/
theorem atomPivotCross_atomSwitch {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {sign : Fin slotCount → ℝ} {pivot slotOne slotTwo : Fin slotCount}
    (hpivot : sign pivot ^ 2 = 1) :
    atomPivotCross (atomSwitch atom sign) scale pivot slotOne slotTwo
      = sign slotOne * sign slotTwo
        * atomPivotCross atom scale pivot slotOne slotTwo := by
  simp only [atomPivotCross, atomGram_atomSwitch,
    atomShiftedDiag_atomSwitch atom scale hpivot]
  linear_combination (-(sign slotOne * sign slotTwo * atomGram atom pivot slotOne
    * atomGram atom pivot slotTwo)) * hpivot

/-- **THE TRIPLE DETERMINANT IS GAUGE INVARIANT.** -/
theorem atomTripleDet_atomSwitch {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {sign : Fin slotCount → ℝ} {slotOne slotTwo slotThree : Fin slotCount}
    (hone : sign slotOne ^ 2 = 1) (htwo : sign slotTwo ^ 2 = 1)
    (hthree : sign slotThree ^ 2 = 1) :
    atomTripleDet (atomSwitch atom sign) scale slotOne slotTwo slotThree
      = atomTripleDet atom scale slotOne slotTwo slotThree := by
  simp only [atomTripleDet, atomGram_atomSwitch,
    atomShiftedDiag_atomSwitch atom scale hone,
    atomShiftedDiag_atomSwitch atom scale htwo,
    atomShiftedDiag_atomSwitch atom scale hthree, sign_pair_mul_sq hone htwo,
    sign_pair_mul_sq hone hthree, sign_pair_mul_sq htwo hthree]
  linear_combination (2 * sign slotTwo ^ 2 * sign slotThree ^ 2
      * atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
      * atomGram atom slotTwo slotThree) * hone
    + (2 * sign slotThree ^ 2 * atomGram atom slotOne slotTwo
      * atomGram atom slotOne slotThree * atomGram atom slotTwo slotThree) * htwo
    + (2 * atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
      * atomGram atom slotTwo slotThree) * hthree

/-- **THE TIGHT FRAME LAW SURVIVES SWITCHING.**  Thus a switched datum is
again a datum of every residue of the lane, and the gauge may be chosen
freely before any certificate is applied. -/
theorem frame_atomSwitch {slotCount rank : ℕ} {atom : Fin slotCount → (Fin rank → ℝ)}
    {sign : Fin slotCount → ℝ} (hsq : ∀ slot, sign slot ^ 2 = 1)
    (hframe : ∀ probe direction : Fin rank → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (probe direction : Fin rank → ℝ) :
    (∑ slot, (atomSwitch atom sign slot ⬝ᵥ probe)
        * (atomSwitch atom sign slot ⬝ᵥ direction)) = probe ⬝ᵥ direction := by
  rw [← hframe probe direction]
  refine Finset.sum_congr rfl fun slot _ => ?_
  simp only [atomSwitch, smul_dotProduct, smul_eq_mul]
  have hmul := sign_mul_self_of_sq_eq_one (hsq slot)
  calc sign slot * (atom slot ⬝ᵥ probe) * (sign slot * (atom slot ⬝ᵥ direction))
      = (sign slot * sign slot)
        * ((atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) := by ring
    _ = (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction) := by rw [hmul, one_mul]

/-! ## Layer 1 — the triangle calculus and its six exact identities -/

/-- The TRIANGLE CYCLE of three slots: the product of the three Gram entries
around the triangle.  It is the oriented invariant of the two-graph, and it
is the only reading of the lane that a square cannot reproduce. -/
def atomTriangleCycle {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomGram atom slotOne slotTwo * atomGram atom slotOne slotThree
    * atomGram atom slotTwo slotThree

/-- The TRIANGLE GAP at a vertex: the shifted diagonal of that vertex against
the square of the opposite edge, minus the cycle.  A positive gap says the
vertex beats the product of its two incident edges divided by the opposite
one, in division-free form. -/
def atomTriangleGap {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (apex slotOne slotTwo : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale apex * atomGram atom slotOne slotTwo ^ 2
    - atomTriangleCycle atom apex slotOne slotTwo

/-- The TRIANGLE SLACK of an edge: the half-box reading of the pair. -/
def atomTriangleSlack {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (rowSlot colSlot : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale rowSlot * atomShiftedDiag atom scale colSlot
    - 2 * atomGram atom rowSlot colSlot ^ 2

/-- The TRIPLE VOLUME: the product of the three shifted diagonals. -/
def atomTripleVolume {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale slotOne * atomShiftedDiag atom scale slotTwo
    * atomShiftedDiag atom scale slotThree

/-- The TRIPLE READING: each shifted diagonal against the square of its
opposite edge. -/
def atomTripleReading {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (slotOne slotTwo slotThree : Fin slotCount) : ℝ :=
  atomShiftedDiag atom scale slotOne * atomGram atom slotTwo slotThree ^ 2
    + atomShiftedDiag atom scale slotTwo * atomGram atom slotOne slotThree ^ 2
    + atomShiftedDiag atom scale slotThree * atomGram atom slotOne slotTwo ^ 2

/-- The cycle does not read the order of its first two slots. -/
theorem atomTriangleCycle_swap_left {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (slotOne slotTwo slotThree : Fin slotCount) :
    atomTriangleCycle atom slotTwo slotOne slotThree
      = atomTriangleCycle atom slotOne slotTwo slotThree := by
  simp only [atomTriangleCycle, atomGram_comm atom slotTwo slotOne]
  ring

/-- The cycle does not read the order of its last two slots. -/
theorem atomTriangleCycle_swap_right {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (slotOne slotTwo slotThree : Fin slotCount) :
    atomTriangleCycle atom slotOne slotThree slotTwo
      = atomTriangleCycle atom slotOne slotTwo slotThree := by
  simp only [atomTriangleCycle, atomGram_comm atom slotThree slotTwo]
  ring

/-- The cycle sends its first slot to the back without change. -/
theorem atomTriangleCycle_rotate {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (slotOne slotTwo slotThree : Fin slotCount) :
    atomTriangleCycle atom slotTwo slotThree slotOne
      = atomTriangleCycle atom slotOne slotTwo slotThree := by
  simp only [atomTriangleCycle, atomGram_comm atom slotTwo slotOne,
    atomGram_comm atom slotThree slotOne]
  ring

/-- **THE CYCLE IS GAUGE INVARIANT.**  Each sign occurs in exactly two of the
three edges, thus no odd power survives.  This is the atom-interface form of
`Gtz.triangleProduct_smul_of_sq_eq_one`. -/
theorem atomTriangleCycle_atomSwitch {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ))
    {sign : Fin slotCount → ℝ} {slotOne slotTwo slotThree : Fin slotCount}
    (hone : sign slotOne ^ 2 = 1) (htwo : sign slotTwo ^ 2 = 1)
    (hthree : sign slotThree ^ 2 = 1) :
    atomTriangleCycle (atomSwitch atom sign) slotOne slotTwo slotThree
      = atomTriangleCycle atom slotOne slotTwo slotThree := by
  simp only [atomTriangleCycle, atomGram_atomSwitch, sign_cycle_mul hone htwo hthree]

/-- **THE TRIANGLE GAP IS GAUGE INVARIANT.** -/
theorem atomTriangleGap_atomSwitch {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {sign : Fin slotCount → ℝ} {apex slotOne slotTwo : Fin slotCount}
    (hapex : sign apex ^ 2 = 1) (hone : sign slotOne ^ 2 = 1)
    (htwo : sign slotTwo ^ 2 = 1) :
    atomTriangleGap (atomSwitch atom sign) scale apex slotOne slotTwo
      = atomTriangleGap atom scale apex slotOne slotTwo := by
  simp only [atomTriangleGap, atomTriangleCycle_atomSwitch atom hapex hone htwo,
    atomShiftedDiag_atomSwitch atom scale hapex, atomGram_atomSwitch,
    sign_pair_mul_sq hone htwo]

/-- **IDENTITY ONE — THE SHIFTED DIAGONAL AGAINST THE OPPOSITE EDGE.**  The
square of the opposite edge times the shifted diagonal of a vertex is the gap
of that vertex plus the cycle. -/
theorem atomShiftedDiag_mul_edge_sq {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomGram atom slotTwo slotThree ^ 2 * atomShiftedDiag atom scale slotOne
      = atomTriangleGap atom scale slotOne slotTwo slotThree
        + atomTriangleCycle atom slotOne slotTwo slotThree := by
  simp only [atomTriangleGap]
  ring

/-- **IDENTITY TWO — THE PAIR MINOR FROM TWO GAPS.**  The pair minor of two
vertices, scaled by the squares of the two edges that leave the third vertex,
is the product of the two gaps plus the cycle against their sum. -/
theorem atomPairMinor_mul_edge_sq {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomGram atom slotOne slotThree ^ 2 * atomGram atom slotTwo slotThree ^ 2
        * atomPairMinor atom scale slotOne slotTwo
      = atomTriangleGap atom scale slotOne slotTwo slotThree
          * atomTriangleGap atom scale slotTwo slotOne slotThree
        + atomTriangleCycle atom slotOne slotTwo slotThree
          * (atomTriangleGap atom scale slotOne slotTwo slotThree
            + atomTriangleGap atom scale slotTwo slotOne slotThree) := by
  have hswapLeft := atomTriangleCycle_swap_left atom slotOne slotTwo slotThree
  simp only [atomTriangleGap, atomPairMinor, atomTriangleCycle,
    atomGram_comm atom slotTwo slotOne] at hswapLeft ⊢
  ring

/-- **IDENTITY THREE — THE MASTER IDENTITY.**  The square of the cycle times
the triple determinant is the product of the three gaps plus the cycle
against the three pairwise products of gaps.  Verified at zero residual
before transcription. -/
theorem atomTripleDet_mul_cycle_sq {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTriangleCycle atom slotOne slotTwo slotThree ^ 2
        * atomTripleDet atom scale slotOne slotTwo slotThree
      = atomTriangleGap atom scale slotOne slotTwo slotThree
          * atomTriangleGap atom scale slotTwo slotOne slotThree
          * atomTriangleGap atom scale slotThree slotOne slotTwo
        + atomTriangleCycle atom slotOne slotTwo slotThree
          * (atomTriangleGap atom scale slotOne slotTwo slotThree
                * atomTriangleGap atom scale slotTwo slotOne slotThree
              + atomTriangleGap atom scale slotOne slotTwo slotThree
                * atomTriangleGap atom scale slotThree slotOne slotTwo
              + atomTriangleGap atom scale slotTwo slotOne slotThree
                * atomTriangleGap atom scale slotThree slotOne slotTwo) := by
  simp only [atomTriangleGap, atomTriangleCycle, atomTripleDet,
    atomGram_comm atom slotTwo slotOne, atomGram_comm atom slotThree slotOne,
    atomGram_comm atom slotThree slotTwo]
  ring

/-- **IDENTITY FOUR — THE ENERGY FORM.**  The triple determinant is the
volume, plus twice the cycle, minus the reading. -/
theorem atomTripleDet_eq_energy {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      = atomTripleVolume atom scale slotOne slotTwo slotThree
        + 2 * atomTriangleCycle atom slotOne slotTwo slotThree
        - atomTripleReading atom scale slotOne slotTwo slotThree := by
  simp only [atomTripleDet, atomTripleVolume, atomTriangleCycle, atomTripleReading]
  ring

/-- **IDENTITY FIVE — THE VOLUME AGAINST THE CYCLE.**  The square of the
volume, minus eight times the square of the cycle, is a positive combination
of the three edge slacks.  Every coefficient is a square, thus three positive
slacks force the volume to beat twice the cycle. -/
theorem atomTripleVolume_sq_sub_cycle_sq {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    atomTripleVolume atom scale slotOne slotTwo slotThree ^ 2
        - 8 * atomTriangleCycle atom slotOne slotTwo slotThree ^ 2
      = atomTriangleSlack atom scale slotOne slotTwo
            * atomTriangleSlack atom scale slotOne slotThree
            * atomTriangleSlack atom scale slotTwo slotThree
        + 2 * (atomTriangleSlack atom scale slotOne slotTwo
            * atomTriangleSlack atom scale slotOne slotThree
            * atomGram atom slotTwo slotThree ^ 2)
        + 2 * (atomTriangleSlack atom scale slotOne slotTwo
            * atomTriangleSlack atom scale slotTwo slotThree
            * atomGram atom slotOne slotThree ^ 2)
        + 2 * (atomTriangleSlack atom scale slotOne slotThree
            * atomTriangleSlack atom scale slotTwo slotThree
            * atomGram atom slotOne slotTwo ^ 2)
        + 4 * (atomTriangleSlack atom scale slotOne slotTwo
            * (atomGram atom slotOne slotThree ^ 2
              * atomGram atom slotTwo slotThree ^ 2))
        + 4 * (atomTriangleSlack atom scale slotOne slotThree
            * (atomGram atom slotOne slotTwo ^ 2
              * atomGram atom slotTwo slotThree ^ 2))
        + 4 * (atomTriangleSlack atom scale slotTwo slotThree
            * (atomGram atom slotOne slotTwo ^ 2
              * atomGram atom slotOne slotThree ^ 2)) := by
  simp only [atomTripleVolume, atomTriangleCycle, atomTriangleSlack]
  ring

/-- **IDENTITY SIX — THE HALF-BOX SPLIT.**  Four times the square of the
cycle, plus the square of the volume, minus the volume against the reading,
is a positive combination of the three edge slacks.  This is the multilinear
certificate of the half-box cell, written in raw scalars with no
normalisation and no square root. -/
theorem atomTriangleHalfBox_split {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    (slotOne slotTwo slotThree : Fin slotCount) :
    4 * atomTriangleCycle atom slotOne slotTwo slotThree ^ 2
        + atomTripleVolume atom scale slotOne slotTwo slotThree ^ 2
        - atomTripleVolume atom scale slotOne slotTwo slotThree
          * atomTripleReading atom scale slotOne slotTwo slotThree
      = atomTriangleSlack atom scale slotOne slotTwo
            * atomTriangleSlack atom scale slotOne slotThree
            * atomTriangleSlack atom scale slotTwo slotThree
        + atomGram atom slotOne slotTwo ^ 2
            * (atomTriangleSlack atom scale slotOne slotThree
              * atomTriangleSlack atom scale slotTwo slotThree)
        + atomGram atom slotOne slotThree ^ 2
            * (atomTriangleSlack atom scale slotOne slotTwo
              * atomTriangleSlack atom scale slotTwo slotThree)
        + atomGram atom slotTwo slotThree ^ 2
            * (atomTriangleSlack atom scale slotOne slotTwo
              * atomTriangleSlack atom scale slotOne slotThree) := by
  simp only [atomTriangleCycle, atomTripleVolume, atomTripleReading, atomTriangleSlack]
  ring

/-! ## Layer 2 — the four coherent cells -/

/-- A positive cycle forces every edge of the triangle to be nonzero. -/
theorem atomGram_ne_zero_of_cycle_pos {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : 0 < atomTriangleCycle atom slotOne slotTwo slotThree) :
    atomGram atom slotOne slotTwo ≠ 0 ∧ atomGram atom slotOne slotThree ≠ 0
      ∧ atomGram atom slotTwo slotThree ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro hzero <;>
    · rw [atomTriangleCycle, hzero] at hcycle
      simp at hcycle

/-- **THE COHERENT PRODUCT CELL, DETERMINANT FORM.**  A triangle of positive
cycle whose three gaps are positive has a positive triple determinant.  The
proof is the master identity divided by the square of the cycle. -/
theorem atomTripleDet_pos_of_coherentGaps {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : 0 < atomTriangleCycle atom slotOne slotTwo slotThree)
    (hone : 0 < atomTriangleGap atom scale slotOne slotTwo slotThree)
    (htwo : 0 < atomTriangleGap atom scale slotTwo slotOne slotThree)
    (hthree : 0 < atomTriangleGap atom scale slotThree slotOne slotTwo) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  have hmaster := atomTripleDet_mul_cycle_sq atom scale slotOne slotTwo slotThree
  have hsq : 0 < atomTriangleCycle atom slotOne slotTwo slotThree ^ 2 := by positivity
  have hright : 0 < atomTriangleCycle atom slotOne slotTwo slotThree ^ 2
      * atomTripleDet atom scale slotOne slotTwo slotThree := by
    rw [hmaster]
    have hprod : 0 < atomTriangleGap atom scale slotOne slotTwo slotThree
        * atomTriangleGap atom scale slotTwo slotOne slotThree
        * atomTriangleGap atom scale slotThree slotOne slotTwo :=
      mul_pos (mul_pos hone htwo) hthree
    have hpairs : 0 < atomTriangleGap atom scale slotOne slotTwo slotThree
          * atomTriangleGap atom scale slotTwo slotOne slotThree
        + atomTriangleGap atom scale slotOne slotTwo slotThree
          * atomTriangleGap atom scale slotThree slotOne slotTwo
        + atomTriangleGap atom scale slotTwo slotOne slotThree
          * atomTriangleGap atom scale slotThree slotOne slotTwo := by
      have := mul_pos hone htwo
      have := mul_pos hone hthree
      have := mul_pos htwo hthree
      linarith
    nlinarith [hprod, hpairs, hcycle]
  nlinarith [hright, hsq]

/-- The shifted diagonal of a vertex of a coherent triangle with a positive
gap is positive. -/
theorem atomShiftedDiag_pos_of_coherentGap {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : 0 < atomTriangleCycle atom slotOne slotTwo slotThree)
    (hone : 0 < atomTriangleGap atom scale slotOne slotTwo slotThree) :
    0 < atomShiftedDiag atom scale slotOne := by
  have hidentity := atomShiftedDiag_mul_edge_sq atom scale slotOne slotTwo slotThree
  have hedge := (atomGram_ne_zero_of_cycle_pos hcycle).2.2
  have hedgeSq : 0 < atomGram atom slotTwo slotThree ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hedge))
  nlinarith [hidentity, hedgeSq, hone, hcycle]

/-- The pair minor of two vertices of a coherent triangle with positive gaps
is positive. -/
theorem atomPairMinor_pos_of_coherentGaps {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : 0 < atomTriangleCycle atom slotOne slotTwo slotThree)
    (hone : 0 < atomTriangleGap atom scale slotOne slotTwo slotThree)
    (htwo : 0 < atomTriangleGap atom scale slotTwo slotOne slotThree) :
    0 < atomPairMinor atom scale slotOne slotTwo := by
  have hidentity := atomPairMinor_mul_edge_sq atom scale slotOne slotTwo slotThree
  have hedges := atomGram_ne_zero_of_cycle_pos hcycle
  have hfactor : 0 < atomGram atom slotOne slotThree ^ 2
      * atomGram atom slotTwo slotThree ^ 2 := by
    have hleft : 0 < atomGram atom slotOne slotThree ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hedges.2.1))
    have hright : 0 < atomGram atom slotTwo slotThree ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hedges.2.2))
    exact mul_pos hleft hright
  nlinarith [hidentity, hfactor, hone, htwo, hcycle, mul_pos hone htwo]

/-- **THE DEFLATED PAIR FROM A POSITIVE TRIPLE DETERMINANT.**  The Dodgson
identity read backwards: a live pivot and a positive determinant give the
deflated pair test of the residue. -/
theorem deflated_pair_of_tripleDet_pos {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {pivot slotOne slotTwo : Fin slotCount}
    (hpivot : 0 < atomShiftedDiag atom scale pivot)
    (hdet : 0 < atomTripleDet atom scale pivot slotOne slotTwo) :
    atomPivotCross atom scale pivot slotOne slotTwo ^ 2
      < atomPairMinor atom scale pivot slotOne
        * atomPairMinor atom scale pivot slotTwo := by
  have hdeflate := atomTripleDet_deflate atom scale pivot slotOne slotTwo
  nlinarith [hdeflate, mul_pos hpivot hdet]

/-- **THE COHERENT PRODUCT CELL, IN THE FORM THE RESIDUE CONSUMES.**  Three
distinct slots of positive cycle and positive gaps supply the deflated pair
of the blocked residue, at the first slot as pivot. -/
theorem exists_deflated_pair_of_coherentGaps {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hcycle : 0 < atomTriangleCycle atom slotOne slotTwo slotThree)
    (hone : 0 < atomTriangleGap atom scale slotOne slotTwo slotThree)
    (htwo : 0 < atomTriangleGap atom scale slotTwo slotOne slotThree)
    (hthree : 0 < atomTriangleGap atom scale slotThree slotOne slotTwo) :
    ∃ pivot firstSlot secondSlot : Fin 6,
      pivot ≠ firstSlot ∧ pivot ≠ secondSlot ∧ firstSlot ≠ secondSlot
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot firstSlot
        ∧ atomPivotCross atom scale pivot firstSlot secondSlot ^ 2
            < atomPairMinor atom scale pivot firstSlot
              * atomPairMinor atom scale pivot secondSlot := by
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree,
    atomShiftedDiag_pos_of_coherentGap hcycle hone,
    atomPairMinor_pos_of_coherentGaps hcycle hone htwo, ?_⟩
  exact deflated_pair_of_tripleDet_pos (atomShiftedDiag_pos_of_coherentGap hcycle hone)
    (atomTripleDet_pos_of_coherentGaps hcycle hone htwo hthree)

/-- **THE VOLUME BEATS TWICE THE CYCLE UNDER THE HALF-BOX.**  Three positive
edge slacks force the square of the volume past eight times the square of the
cycle, hence the volume past twice the cycle. -/
theorem two_mul_cycle_lt_volume_of_halfBox {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hvolume : 0 < atomTripleVolume atom scale slotOne slotTwo slotThree)
    (hslackOneTwo : 0 < atomTriangleSlack atom scale slotOne slotTwo)
    (hslackOneThree : 0 < atomTriangleSlack atom scale slotOne slotThree)
    (hslackTwoThree : 0 < atomTriangleSlack atom scale slotTwo slotThree) :
    2 * |atomTriangleCycle atom slotOne slotTwo slotThree|
      < atomTripleVolume atom scale slotOne slotTwo slotThree := by
  have hsplit := atomTripleVolume_sq_sub_cycle_sq atom scale slotOne slotTwo slotThree
  have hpositive : 0 < atomTripleVolume atom scale slotOne slotTwo slotThree ^ 2
      - 8 * atomTriangleCycle atom slotOne slotTwo slotThree ^ 2 := by
    rw [hsplit]
    have hone : 0 < atomTriangleSlack atom scale slotOne slotTwo
        * atomTriangleSlack atom scale slotOne slotThree
        * atomTriangleSlack atom scale slotTwo slotThree :=
      mul_pos (mul_pos hslackOneTwo hslackOneThree) hslackTwoThree
    have htwo : 0 ≤ atomTriangleSlack atom scale slotOne slotTwo
        * atomTriangleSlack atom scale slotOne slotThree
        * atomGram atom slotTwo slotThree ^ 2 :=
      mul_nonneg (mul_pos hslackOneTwo hslackOneThree).le (sq_nonneg _)
    have hthree : 0 ≤ atomTriangleSlack atom scale slotOne slotTwo
        * atomTriangleSlack atom scale slotTwo slotThree
        * atomGram atom slotOne slotThree ^ 2 :=
      mul_nonneg (mul_pos hslackOneTwo hslackTwoThree).le (sq_nonneg _)
    have hfour : 0 ≤ atomTriangleSlack atom scale slotOne slotThree
        * atomTriangleSlack atom scale slotTwo slotThree
        * atomGram atom slotOne slotTwo ^ 2 :=
      mul_nonneg (mul_pos hslackOneThree hslackTwoThree).le (sq_nonneg _)
    have hfive : 0 ≤ atomTriangleSlack atom scale slotOne slotTwo
        * (atomGram atom slotOne slotThree ^ 2 * atomGram atom slotTwo slotThree ^ 2) :=
      mul_nonneg hslackOneTwo.le (by positivity)
    have hsix : 0 ≤ atomTriangleSlack atom scale slotOne slotThree
        * (atomGram atom slotOne slotTwo ^ 2 * atomGram atom slotTwo slotThree ^ 2) :=
      mul_nonneg hslackOneThree.le (by positivity)
    have hseven : 0 ≤ atomTriangleSlack atom scale slotTwo slotThree
        * (atomGram atom slotOne slotTwo ^ 2 * atomGram atom slotOne slotThree ^ 2) :=
      mul_nonneg hslackTwoThree.le (by positivity)
    linarith
  have habs : |atomTriangleCycle atom slotOne slotTwo slotThree| ^ 2
      = atomTriangleCycle atom slotOne slotTwo slotThree ^ 2 := sq_abs _
  nlinarith [hpositive, hvolume, habs,
    abs_nonneg (atomTriangleCycle atom slotOne slotTwo slotThree)]

/-- **THE COHERENT HALF-BOX CELL, DETERMINANT FORM.**  A triangle of
nonnegative cycle whose three edge slacks are positive has a positive triple
determinant.  Compare `Gtz.dominates_of_coherentHalfBoxTriangle`, which
states the same cell at the design interface through the normalised
correlations: here the reading is raw and no atom needs to be heavy. -/
theorem atomTripleDet_pos_of_coherentHalfBox {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree)
    (hvolume : 0 < atomTripleVolume atom scale slotOne slotTwo slotThree)
    (hslackOneTwo : 0 < atomTriangleSlack atom scale slotOne slotTwo)
    (hslackOneThree : 0 < atomTriangleSlack atom scale slotOne slotThree)
    (hslackTwoThree : 0 < atomTriangleSlack atom scale slotTwo slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  have hsplit := atomTriangleHalfBox_split atom scale slotOne slotTwo slotThree
  have hrightPos : 0 < atomTriangleSlack atom scale slotOne slotTwo
        * atomTriangleSlack atom scale slotOne slotThree
        * atomTriangleSlack atom scale slotTwo slotThree
      + atomGram atom slotOne slotTwo ^ 2
          * (atomTriangleSlack atom scale slotOne slotThree
            * atomTriangleSlack atom scale slotTwo slotThree)
      + atomGram atom slotOne slotThree ^ 2
          * (atomTriangleSlack atom scale slotOne slotTwo
            * atomTriangleSlack atom scale slotTwo slotThree)
      + atomGram atom slotTwo slotThree ^ 2
          * (atomTriangleSlack atom scale slotOne slotTwo
            * atomTriangleSlack atom scale slotOne slotThree) := by
    have hbase : 0 < atomTriangleSlack atom scale slotOne slotTwo
        * atomTriangleSlack atom scale slotOne slotThree
        * atomTriangleSlack atom scale slotTwo slotThree :=
      mul_pos (mul_pos hslackOneTwo hslackOneThree) hslackTwoThree
    have hone : 0 ≤ atomGram atom slotOne slotTwo ^ 2
        * (atomTriangleSlack atom scale slotOne slotThree
          * atomTriangleSlack atom scale slotTwo slotThree) :=
      mul_nonneg (sq_nonneg _) (mul_pos hslackOneThree hslackTwoThree).le
    have htwo : 0 ≤ atomGram atom slotOne slotThree ^ 2
        * (atomTriangleSlack atom scale slotOne slotTwo
          * atomTriangleSlack atom scale slotTwo slotThree) :=
      mul_nonneg (sq_nonneg _) (mul_pos hslackOneTwo hslackTwoThree).le
    have hthree : 0 ≤ atomGram atom slotTwo slotThree ^ 2
        * (atomTriangleSlack atom scale slotOne slotTwo
          * atomTriangleSlack atom scale slotOne slotThree) :=
      mul_nonneg (sq_nonneg _) (mul_pos hslackOneTwo hslackOneThree).le
    linarith
  have hreading : atomTripleVolume atom scale slotOne slotTwo slotThree
      * atomTripleReading atom scale slotOne slotTwo slotThree
      < atomTripleVolume atom scale slotOne slotTwo slotThree ^ 2
        + 4 * atomTriangleCycle atom slotOne slotTwo slotThree ^ 2 := by
    linarith [hsplit, hrightPos]
  have hgap := two_mul_cycle_lt_volume_of_halfBox hvolume hslackOneTwo hslackOneThree
    hslackTwoThree
  have habs : atomTriangleCycle atom slotOne slotTwo slotThree
      ≤ |atomTriangleCycle atom slotOne slotTwo slotThree| := le_abs_self _
  have hscaled : 0 < atomTripleVolume atom scale slotOne slotTwo slotThree
      * atomTripleDet atom scale slotOne slotTwo slotThree := by
    rw [atomTripleDet_eq_energy atom scale slotOne slotTwo slotThree]
    nlinarith [hreading, hgap, habs, hcycle, hvolume]
  nlinarith [hscaled, hvolume]

/-- A positive edge slack forces the pair minor of that edge to be positive. -/
theorem atomPairMinor_pos_of_slack_pos {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {rowSlot colSlot : Fin slotCount}
    (hslack : 0 < atomTriangleSlack atom scale rowSlot colSlot) :
    0 < atomPairMinor atom scale rowSlot colSlot := by
  simp only [atomTriangleSlack] at hslack
  simp only [atomPairMinor]
  nlinarith [hslack, sq_nonneg (atomGram atom rowSlot colSlot)]

/-- **THE COHERENT HALF-BOX CELL, IN THE FORM THE RESIDUE CONSUMES.** -/
theorem exists_deflated_pair_of_coherentHalfBox {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hcycle : 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree)
    (hdiagOne : 0 < atomShiftedDiag atom scale slotOne)
    (hdiagTwo : 0 < atomShiftedDiag atom scale slotTwo)
    (hdiagThree : 0 < atomShiftedDiag atom scale slotThree)
    (hslackOneTwo : 0 < atomTriangleSlack atom scale slotOne slotTwo)
    (hslackOneThree : 0 < atomTriangleSlack atom scale slotOne slotThree)
    (hslackTwoThree : 0 < atomTriangleSlack atom scale slotTwo slotThree) :
    ∃ pivot firstSlot secondSlot : Fin 6,
      pivot ≠ firstSlot ∧ pivot ≠ secondSlot ∧ firstSlot ≠ secondSlot
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot firstSlot
        ∧ atomPivotCross atom scale pivot firstSlot secondSlot ^ 2
            < atomPairMinor atom scale pivot firstSlot
              * atomPairMinor atom scale pivot secondSlot := by
  have hvolume : 0 < atomTripleVolume atom scale slotOne slotTwo slotThree := by
    simp only [atomTripleVolume]
    exact mul_pos (mul_pos hdiagOne hdiagTwo) hdiagThree
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdiagOne,
    atomPairMinor_pos_of_slack_pos hslackOneTwo, ?_⟩
  exact deflated_pair_of_tripleDet_pos hdiagOne
    (atomTripleDet_pos_of_coherentHalfBox hcycle hvolume hslackOneTwo hslackOneThree
      hslackTwoThree)

/-- **THE COHERENT ENERGY CELL.**  A triangle of nonnegative cycle whose
reading stays below its volume has a positive triple determinant.  This is
the cheapest cell of the four and it needs no square. -/
theorem atomTripleDet_pos_of_coherentEnergy {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {slotOne slotTwo slotThree : Fin slotCount}
    (hcycle : 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree)
    (henergy : atomTripleReading atom scale slotOne slotTwo slotThree
      < atomTripleVolume atom scale slotOne slotTwo slotThree) :
    0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
  rw [atomTripleDet_eq_energy atom scale slotOne slotTwo slotThree]
  linarith

/-- **THE ORTHOGONAL APEX CELL.**  When one vertex is orthogonal to the other
two the determinant factors as its shifted diagonal against the pair minor of
the opposite edge.  No sign is read at all. -/
theorem atomTripleDet_eq_of_orthogonalApex {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {slotOne slotTwo slotThree : Fin slotCount}
    (hone : atomGram atom slotOne slotTwo = 0)
    (htwo : atomGram atom slotOne slotThree = 0) :
    atomTripleDet atom scale slotOne slotTwo slotThree
      = atomShiftedDiag atom scale slotOne
        * atomPairMinor atom scale slotTwo slotThree := by
  simp only [atomTripleDet, atomPairMinor, hone, htwo]
  ring

/-- **THE ORTHOGONAL APEX CELL, IN THE FORM THE RESIDUE CONSUMES.** -/
theorem exists_deflated_pair_of_orthogonalApex {atom : Fin 6 → (Fin 3 → ℝ)}
    {scale : Fin 6 → ℝ} {slotOne slotTwo slotThree : Fin 6}
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (htwoThree : slotTwo ≠ slotThree)
    (hone : atomGram atom slotOne slotTwo = 0)
    (htwo : atomGram atom slotOne slotThree = 0)
    (hdiagOne : 0 < atomShiftedDiag atom scale slotOne)
    (hdiagTwo : 0 < atomShiftedDiag atom scale slotTwo)
    (hminor : 0 < atomPairMinor atom scale slotTwo slotThree) :
    ∃ pivot firstSlot secondSlot : Fin 6,
      pivot ≠ firstSlot ∧ pivot ≠ secondSlot ∧ firstSlot ≠ secondSlot
        ∧ 0 < atomShiftedDiag atom scale pivot
        ∧ 0 < atomPairMinor atom scale pivot firstSlot
        ∧ atomPivotCross atom scale pivot firstSlot secondSlot ^ 2
            < atomPairMinor atom scale pivot firstSlot
              * atomPairMinor atom scale pivot secondSlot := by
  have hdet : 0 < atomTripleDet atom scale slotOne slotTwo slotThree := by
    rw [atomTripleDet_eq_of_orthogonalApex atom scale hone htwo]
    exact mul_pos hdiagOne hminor
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hdiagOne, ?_, ?_⟩
  · simp only [atomPairMinor, hone]
    nlinarith [mul_pos hdiagOne hdiagTwo]
  · exact deflated_pair_of_tripleDet_pos hdiagOne hdet

/-! ## Layer 3 — the parity supply, and the field door -/

/-- The triangle cycle IS the triangle product of the three atoms. -/
theorem atomTriangleCycle_eq_triangleProduct {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (slotOne slotTwo slotThree : Fin slotCount) :
    atomTriangleCycle atom slotOne slotTwo slotThree
      = triangleProduct (atom slotOne) (atom slotTwo) (atom slotThree) := by
  simp only [atomTriangleCycle, triangleProduct, atomGram]

/-- **THE PARITY SUPPLY.**  Six real atoms of rank three carry a triangle of
nonnegative cycle.  The threshold of the landed sign forcing is
`rank + 2 = 5`, and six exceeds it.  This is the real-only ingredient of the
module: the argument runs on the fact that a real vector has a sign. -/
theorem exists_coherent_atomTriple (atom : Fin 6 → (Fin 3 → ℝ)) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree := by
  have hcard : Fintype.card (Fin 3) + 2 ≤ Fintype.card (Fin 6) := by simp
  have hthree : 3 ≤ Fintype.card (Fin 6) := by simp
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hproduct⟩ :=
    exists_nonneg_triangleProduct_of_card_ge atom hcard hthree
  exact ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, by
    rw [atomTriangleCycle_eq_triangleProduct]; exact hproduct⟩

/-- **THE PARITY SUPPLY, STRICT FORM.**  When every pairwise Gram entry is
nonzero the supplied triangle has a strictly positive cycle, which is what
the coherent product cell consumes. -/
theorem exists_pos_coherent_atomTriple (atom : Fin 6 → (Fin 3 → ℝ))
    (hnonzero : ∀ first second : Fin 6, first ≠ second → atomGram atom first second ≠ 0) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 < atomTriangleCycle atom slotOne slotTwo slotThree := by
  have hcard : Fintype.card (Fin 3) + 2 ≤ Fintype.card (Fin 6) := by simp
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hproduct⟩ :=
    exists_pos_triangleProduct_of_card_ge atom
      (fun first second hne => hnonzero first second hne) hcard
  exact ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, by
    rw [atomTriangleCycle_eq_triangleProduct]; exact hproduct⟩

/-- **THE PARITY SUPPLY AT FIVE SLOTS.**  Any five of the six slots already
carry a coherent triangle, thus one slot may be dropped before the selection
runs.  The extra freedom is six choices of the dropped slot. -/
theorem exists_coherent_atomTriple_of_pick (atom : Fin 6 → (Fin 3 → ℝ))
    (pick : Fin 5 → Fin 6) (hinjective : Function.Injective pick) :
    ∃ slotOne slotTwo slotThree : Fin 5,
      pick slotOne ≠ pick slotTwo ∧ pick slotOne ≠ pick slotThree
        ∧ pick slotTwo ≠ pick slotThree
        ∧ 0 ≤ atomTriangleCycle atom (pick slotOne) (pick slotTwo) (pick slotThree) := by
  have hcard : Fintype.card (Fin 3) + 2 ≤ Fintype.card (Fin 5) := by simp
  have hthree : 3 ≤ Fintype.card (Fin 5) := by simp
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hproduct⟩ :=
    exists_nonneg_triangleProduct_of_card_ge (fun index : Fin 5 => atom (pick index))
      hcard hthree
  refine ⟨slotOne, slotTwo, slotThree, fun heq => honeTwo (hinjective heq),
    fun heq => honeThree (hinjective heq), fun heq => htwoThree (hinjective heq), ?_⟩
  rw [atomTriangleCycle_eq_triangleProduct]
  exact hproduct

/-- **THE PARITY SUPPLY AT A PRESCRIBED SLOT.**  Every slot of six real atoms
of rank three lies on a coherent triangle.  This is strictly stronger than
`Gtz.exists_coherent_atomTriple`, because the residue names its pivot first
and the triangle is then supplied around that pivot.

The argument switches at the prescribed slot, which makes every edge to it
negative, and then reads the obtuse bound on the five remaining atoms: at
most `3 + 1` vectors of rank three pair strictly negatively in pairs, thus
some pair of the five does not, and the triangle through the prescribed slot
carries a nonnegative cycle.  A vanishing edge at the prescribed slot
short-circuits the argument, because it makes every cycle through that slot
vanish, thus the degenerate branch is routed and not excluded. -/
theorem exists_coherent_atomTriple_at (atom : Fin 6 → (Fin 3 → ℝ)) (base : Fin 6) :
    ∃ slotOne slotTwo : Fin 6,
      base ≠ slotOne ∧ base ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 ≤ atomTriangleCycle atom base slotOne slotTwo := by
  classical
  by_cases hzero : ∃ other : Fin 6, other ≠ base ∧ atomGram atom base other = 0
  · obtain ⟨other, hother, hgram⟩ := hzero
    have hroom : (({base, other} : Finset (Fin 6))ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      have hpair : ({base, other} : Finset (Fin 6)).card ≤ 2 :=
        (Finset.card_insert_le _ _).trans (by simp)
      omega
    obtain ⟨third, hthirdMem⟩ := hroom
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
      not_or] at hthirdMem
    refine ⟨other, third, Ne.symm hother, Ne.symm hthirdMem.1,
      fun heq => hthirdMem.2 heq.symm, ?_⟩
    simp only [atomTriangleCycle, hgram, zero_mul, le_refl]
  · push Not at hzero
    have hsq : ∀ slot : Fin 6, switchSign atom base slot ^ 2 = 1 :=
      switchSign_sq_eq_one atom base
    have hcard : Fintype.card {y : Fin 6 // y ≠ base} = 5 := by
      have hcompl := Fintype.card_subtype_compl (fun y : Fin 6 => y = base)
      rw [Fintype.card_subtype_eq base, Fintype.card_fin] at hcompl
      exact hcompl
    have hnotObtuse : ¬ IsPairwiseObtuse
        (fun index : {y : Fin 6 // y ≠ base} =>
          atomSwitch atom (switchSign atom base) index.val) := by
      intro hobtuse
      have hbound := card_le_succ_of_isPairwiseObtuse hobtuse
      rw [hcard, Fintype.card_fin] at hbound
      omega
    simp only [IsPairwiseObtuse] at hnotObtuse
    push Not at hnotObtuse
    obtain ⟨first, second, hne, hdot⟩ := hnotObtuse
    have hfirstNe : first.val ≠ base := first.property
    have hsecondNe : second.val ≠ base := second.property
    have hvalNe : first.val ≠ second.val := fun heq => hne (Subtype.ext heq)
    have hbaseFirst : atomGram (atomSwitch atom (switchSign atom base)) base first.val
        < 0 := by
      rw [atomGram_atomSwitch, switchSign_base, one_mul]
      exact switchSign_mul_basePairing_neg (hzero first.val hfirstNe) hfirstNe
    have hbaseSecond : atomGram (atomSwitch atom (switchSign atom base)) base second.val
        < 0 := by
      rw [atomGram_atomSwitch, switchSign_base, one_mul]
      exact switchSign_mul_basePairing_neg (hzero second.val hsecondNe) hsecondNe
    have hcross : 0 ≤ atomGram (atomSwitch atom (switchSign atom base))
        first.val second.val := hdot
    have hswitched : 0 ≤ atomTriangleCycle (atomSwitch atom (switchSign atom base))
        base first.val second.val := by
      simp only [atomTriangleCycle]
      exact mul_nonneg (mul_pos_of_neg_of_neg hbaseFirst hbaseSecond).le hcross
    rw [atomTriangleCycle_atomSwitch atom (hsq base) (hsq first.val) (hsq second.val)]
      at hswitched
    exact ⟨first.val, second.val, Ne.symm hfirstNe, Ne.symm hsecondNe, hvalNe, hswitched⟩

/-- **THE FIELD DOOR, AS A NUMBER.**  Six atoms sit strictly below the
complex sign-forcing threshold `2 * rank + 2 = 8` of
`Gtz.exists_pos_realTriangleProduct_of_complex_card_ge`, while they sit above
the real threshold `rank + 2 = 5`.  The parity supply of this module is
therefore unavailable over the complex field at the size that matters, which
is exactly why every certificate here is real-only. -/
theorem six_lt_complexSignForcing_threshold :
    Fintype.card (Fin 3) + 2 ≤ Fintype.card (Fin 6)
      ∧ Fintype.card (Fin 6) < 2 * Fintype.card (Fin 3) + 2 := by
  constructor <;> simp

/-! ## Layer 4 — the constraints a counterexample must satisfy -/

/-- The statement that three slots supply the deflated pair of the residue at
the first slot as pivot. -/
def AtomTripleDeflates {slotCount rank : ℕ} (atom : Fin slotCount → (Fin rank → ℝ))
    (scale : Fin slotCount → ℝ) (pivot slotOne slotTwo : Fin slotCount) : Prop :=
  0 < atomShiftedDiag atom scale pivot
    ∧ 0 < atomPairMinor atom scale pivot slotOne
    ∧ atomPivotCross atom scale pivot slotOne slotTwo ^ 2
        < atomPairMinor atom scale pivot slotOne
          * atomPairMinor atom scale pivot slotTwo

/-- **THE COUNTEREXAMPLE CARRIES A FLAT COHERENT TRIANGLE.**  At a datum
whose triples never deflate, the coherent triangle that sign forcing supplies
has a nonpositive gap at one of its three vertices, or a vanishing cycle.
This is the exact contrapositive of the coherent product cell against the
parity supply, and it holds with no hypothesis on the scales at all. -/
theorem exists_flat_coherent_triangle_of_no_dominating_triple
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hfail : ∀ pivot slotOne slotTwo : Fin 6, pivot ≠ slotOne → pivot ≠ slotTwo →
      slotOne ≠ slotTwo → ¬ AtomTripleDeflates atom scale pivot slotOne slotTwo) :
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 ≤ atomTriangleCycle atom slotOne slotTwo slotThree
        ∧ (atomTriangleCycle atom slotOne slotTwo slotThree = 0
            ∨ atomTriangleGap atom scale slotOne slotTwo slotThree ≤ 0
            ∨ atomTriangleGap atom scale slotTwo slotOne slotThree ≤ 0
            ∨ atomTriangleGap atom scale slotThree slotOne slotTwo ≤ 0) := by
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcycle⟩ :=
    exists_coherent_atomTriple atom
  refine ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcycle, ?_⟩
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hcycleNe, hone, htwo, hthree⟩ := hcontra
  have hcyclePos : 0 < atomTriangleCycle atom slotOne slotTwo slotThree :=
    lt_of_le_of_ne hcycle (Ne.symm hcycleNe)
  obtain ⟨pivot, firstSlot, secondSlot, hpivotFirst, hpivotSecond, hfirstSecond,
    hdiag, hminor, hcross⟩ :=
    exists_deflated_pair_of_coherentGaps honeTwo honeThree htwoThree hcyclePos
      hone htwo hthree
  exact hfail pivot firstSlot secondSlot hpivotFirst hpivotSecond hfirstSecond
    ⟨hdiag, hminor, hcross⟩

/-- **THE COUNTEREXAMPLE CARRIES A STRONG EDGE.**  At a datum whose triples
never deflate and whose every slot is live, some pair of slots fails the
half-box: its two shifted diagonals do not beat twice the square of its Gram
entry.  This is the atom-interface analogue of
`Gtz.exists_normalizedPairing_sq_gt_half_of_five_atoms`, and it consumes no
heaviness and no injectivity. -/
theorem exists_strong_edge_of_no_dominating_triple
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)
    (hlive : ∀ slot : Fin 6, 0 < atomShiftedDiag atom scale slot)
    (hfail : ∀ pivot slotOne slotTwo : Fin 6, pivot ≠ slotOne → pivot ≠ slotTwo →
      slotOne ≠ slotTwo → ¬ AtomTripleDeflates atom scale pivot slotOne slotTwo) :
    ∃ rowSlot colSlot : Fin 6, rowSlot ≠ colSlot
      ∧ atomTriangleSlack atom scale rowSlot colSlot ≤ 0 := by
  obtain ⟨slotOne, slotTwo, slotThree, honeTwo, honeThree, htwoThree, hcycle⟩ :=
    exists_coherent_atomTriple atom
  by_contra hcontra
  push Not at hcontra
  obtain ⟨pivot, firstSlot, secondSlot, hpivotFirst, hpivotSecond, hfirstSecond,
    hdiag, hminor, hcross⟩ :=
    exists_deflated_pair_of_coherentHalfBox honeTwo honeThree htwoThree hcycle
      (hlive slotOne) (hlive slotTwo) (hlive slotThree)
      (hcontra slotOne slotTwo honeTwo) (hcontra slotOne slotThree honeThree)
      (hcontra slotTwo slotThree htwoThree)
  exact hfail pivot firstSlot secondSlot hpivotFirst hpivotSecond hfirstSecond
    ⟨hdiag, hminor, hcross⟩

/-- **THE COUNTEREXAMPLE CARRIES A FLAT COHERENT TRIANGLE AT EVERY SLOT.**  The
prescribed-slot supply upgrades the single constraint of
`Gtz.exists_flat_coherent_triangle_of_no_dominating_triple` to six of them, one
through each slot, and each one is available with no hypothesis on the
scales. -/
theorem exists_flat_coherent_triangle_at_of_no_dominating_triple
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (base : Fin 6)
    (hfail : ∀ pivot slotOne slotTwo : Fin 6, pivot ≠ slotOne → pivot ≠ slotTwo →
      slotOne ≠ slotTwo → ¬ AtomTripleDeflates atom scale pivot slotOne slotTwo) :
    ∃ slotOne slotTwo : Fin 6,
      base ≠ slotOne ∧ base ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 ≤ atomTriangleCycle atom base slotOne slotTwo
        ∧ (atomTriangleCycle atom base slotOne slotTwo = 0
            ∨ atomTriangleGap atom scale base slotOne slotTwo ≤ 0
            ∨ atomTriangleGap atom scale slotOne base slotTwo ≤ 0
            ∨ atomTriangleGap atom scale slotTwo base slotOne ≤ 0) := by
  obtain ⟨slotOne, slotTwo, honeBase, htwoBase, honeTwo, hcycle⟩ :=
    exists_coherent_atomTriple_at atom base
  refine ⟨slotOne, slotTwo, honeBase, htwoBase, honeTwo, hcycle, ?_⟩
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hcycleNe, hone, htwo, hthree⟩ := hcontra
  have hcyclePos : 0 < atomTriangleCycle atom base slotOne slotTwo :=
    lt_of_le_of_ne hcycle (Ne.symm hcycleNe)
  obtain ⟨pivot, firstSlot, secondSlot, hpivotFirst, hpivotSecond, hfirstSecond,
    hdiag, hminor, hcross⟩ :=
    exists_deflated_pair_of_coherentGaps honeBase htwoBase honeTwo hcyclePos
      hone htwo hthree
  exact hfail pivot firstSlot secondSlot hpivotFirst hpivotSecond hfirstSecond
    ⟨hdiag, hminor, hcross⟩

/-- **THE COUNTEREXAMPLE CARRIES A STRONG EDGE IN EVERY COHERENT TRIANGLE.**
At a datum whose triples never deflate and whose every slot is live, the
coherent triangle supplied at EACH slot carries an edge that fails the
half-box.  Six such triangles are available, one through each slot, so the
strong edges cannot all hide in one corner of the configuration. -/
theorem exists_strong_edge_in_coherent_triangle_of_no_dominating_triple
    (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ) (base : Fin 6)
    (hlive : ∀ slot : Fin 6, 0 < atomShiftedDiag atom scale slot)
    (hfail : ∀ pivot slotOne slotTwo : Fin 6, pivot ≠ slotOne → pivot ≠ slotTwo →
      slotOne ≠ slotTwo → ¬ AtomTripleDeflates atom scale pivot slotOne slotTwo) :
    ∃ slotOne slotTwo : Fin 6,
      base ≠ slotOne ∧ base ≠ slotTwo ∧ slotOne ≠ slotTwo
        ∧ 0 ≤ atomTriangleCycle atom base slotOne slotTwo
        ∧ (atomTriangleSlack atom scale base slotOne ≤ 0
            ∨ atomTriangleSlack atom scale base slotTwo ≤ 0
            ∨ atomTriangleSlack atom scale slotOne slotTwo ≤ 0) := by
  obtain ⟨slotOne, slotTwo, honeBase, htwoBase, honeTwo, hcycle⟩ :=
    exists_coherent_atomTriple_at atom base
  refine ⟨slotOne, slotTwo, honeBase, htwoBase, honeTwo, hcycle, ?_⟩
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hbaseOne, hbaseTwo, hfar⟩ := hcontra
  obtain ⟨pivot, firstSlot, secondSlot, hpivotFirst, hpivotSecond, hfirstSecond,
    hdiag, hminor, hcross⟩ :=
    exists_deflated_pair_of_coherentHalfBox honeBase htwoBase honeTwo hcycle
      (hlive base) (hlive slotOne) (hlive slotTwo) hbaseOne hbaseTwo hfar
  exact hfail pivot firstSlot secondSlot hpivotFirst hpivotSecond hfirstSecond
    ⟨hdiag, hminor, hcross⟩

/-- **A PARALLEL PAIR KILLS EVERY TRIPLE THROUGH IT.**  When the Gram entry
of two slots saturates the Cauchy-Schwarz bound, their pair minor is strictly
negative as soon as one of them is live and both scales are positive, thus no
pivot chain of the residue can use both.  This is the atom-interface form of
`Gtz.not_dominates_of_repeated_atom`, and it explains why the adversarial
floor of the lane is attained at a configuration with an antiparallel pair. -/
theorem atomPairMinor_neg_of_parallel {slotCount rank : ℕ}
    {atom : Fin slotCount → (Fin rank → ℝ)} {scale : Fin slotCount → ℝ}
    {rowSlot colSlot : Fin slotCount}
    (hparallel : atomGram atom rowSlot colSlot ^ 2
      = atomGram atom rowSlot rowSlot * atomGram atom colSlot colSlot)
    (hrowScale : 0 < scale rowSlot) (hcolScale : 0 < scale colSlot)
    (hrowLive : 0 < atomShiftedDiag atom scale rowSlot) :
    atomPairMinor atom scale rowSlot colSlot < 0 := by
  have hcolDiag : 0 ≤ atomGram atom colSlot colSlot := atomGram_diag_nonneg atom colSlot
  have hrowDiag : scale rowSlot < atomGram atom rowSlot rowSlot := by
    simp only [atomShiftedDiag] at hrowLive
    linarith
  simp only [atomPairMinor, atomShiftedDiag, hparallel]
  nlinarith [hcolDiag, hrowDiag, hrowScale, hcolScale]

/-- The coherent product cell fires at a triple exactly when the gauge can be
chosen to make all three edges positive: the cycle and the three gaps are
gauge invariant, thus the cell is a statement about the two-graph of the
configuration and never about a choice of representative vectors. -/
theorem coherentGaps_atomSwitch_iff {slotCount rank : ℕ}
    (atom : Fin slotCount → (Fin rank → ℝ)) (scale : Fin slotCount → ℝ)
    {sign : Fin slotCount → ℝ} {slotOne slotTwo slotThree : Fin slotCount}
    (hone : sign slotOne ^ 2 = 1) (htwo : sign slotTwo ^ 2 = 1)
    (hthree : sign slotThree ^ 2 = 1) :
    (0 < atomTriangleCycle (atomSwitch atom sign) slotOne slotTwo slotThree
        ∧ 0 < atomTriangleGap (atomSwitch atom sign) scale slotOne slotTwo slotThree
        ∧ 0 < atomTriangleGap (atomSwitch atom sign) scale slotTwo slotOne slotThree
        ∧ 0 < atomTriangleGap (atomSwitch atom sign) scale slotThree slotOne slotTwo)
      ↔ (0 < atomTriangleCycle atom slotOne slotTwo slotThree
        ∧ 0 < atomTriangleGap atom scale slotOne slotTwo slotThree
        ∧ 0 < atomTriangleGap atom scale slotTwo slotOne slotThree
        ∧ 0 < atomTriangleGap atom scale slotThree slotOne slotTwo) := by
  rw [atomTriangleCycle_atomSwitch atom hone htwo hthree,
    atomTriangleGap_atomSwitch atom scale hone htwo hthree,
    atomTriangleGap_atomSwitch atom scale htwo hone hthree,
    atomTriangleGap_atomSwitch atom scale hthree hone htwo]

end Gtz
