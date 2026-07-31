/-
# Private-atom localisation of the Clarke pairing

`Gtz/Quantitative/IsolatedBlockExclusion.lean` localises the Clarke pairing at an
active block on the hypothesis that the block is ISOLATED -- no active subset meets it
without equalling it.  That hypothesis is global to the block.  This file weakens it to
a per-atom condition: an atom is PRIVATE to a block when every active subset containing
THAT ATOM equals the block, with nothing assumed about the block's other atoms.  The
shipped localisation only ever consults the membership dichotomy at the one atom it is
contracted at, so it survives the weakening intact.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `clarkePairing_sum_right` and `clarkePairing_subsetSum_mulVec_left` -- right-linearity
  of the unrestricted Clarke pairing.  The tree ships only the block-restricted
  `Gtz.blockClarkePairing_sum_right`; the unrestricted sibling was a genuine gap.
* `blockClarkePairing_atom_eq_of_privateAtom` -- the localisation.  Strictly generalises
  the shipped `Gtz.blockClarkePairing_atom_eq`, which is its `IsIsolatedActiveBlock`
  instance.
* `blockOverlapSum_eq_value_of_privateAtom` -- the weight-free bridge.  Strictly
  generalises the shipped `Gtz.clarkePairing_subsetSum_atom_eq_value`, which is its
  all-atoms-private instance.
* `multiplierTotal_subsetSum_normSq_eq_sum` -- the second moment of an ARBITRARY subset
  sum, with no stationarity hypothesis and no isolation.  The shipped
  `Gtz.multiplierTotal_subsetSum_normSq_eq_card_mul_value` is this identity followed by
  the isolated-block evaluation of each summand.
* `crossMass_le_of_privatePart` and its geometric reading `overlapAbsSum_ge_of_privatePart`
  -- the private atoms of an active subset must carry a large total overlap with the
  subset's shared atoms.  Strictly generalise the shipped
  `Gtz.card_le_value_of_isIsolatedActiveBlock`, which is the empty-cross-term instance.
* `sq_clarkePairing_le_mul` and `abs_clarkePairing_atom_le_one` -- the Clarke pairing is a
  nonnegative combination of rank-one projectors, hence obeys Cauchy-Schwarz; every atom
  sits at Clarke level one, so the atom correlations form a correlation matrix.  This is
  the most reusable pair in the file: both are value-agnostic in `(m, k)`.
* `exists_pos_activeWeight_of_privateAtom` -- a block with a private atom is carried by a
  strictly positive Clarke multiplier.
* `exists_dependence_tightDir_of_value_lt_one` -- the positive witness form of the shipped
  negation `Gtz.not_hasIndependentTightSupport_of_value_lt_one`, in the shape a rank
  argument can consume.
* `three_le_card_activeSubsetImage_sevenThree` -- the `(7,3)` image floor, with NO
  below-one hypothesis, unlike the shipped `(6,3)` sibling.

## NOT PROVED here -- and why two advertised consequences are DEAD

The cross-mass inequalities were built to attack the below-one regime, and that
application does not exist.  A single private atom already forces `1 ≤ value`: the sharp
form of the localisation bounds the sum of squared Clarke correlations over the block by
`value`, and the diagonal term is the quadric law, which is exactly one.  So
"private part nonempty" together with "`value < 1`" is CONTRADICTORY, and the surviving
non-trivial band of `crossMass_le_of_privatePart` is `2 ≤ |P|` with `1 ≤ value < |P|`.

Consequently two results of the source scratch are NOT landed, both because their
hypotheses are contradictory rather than because they are hard:

* the `(7,3)` two-private-atom overlap bound `2 < sum |<g_d, g_c>|`, which assumes both
  `value < 1` and a private part of size two; and
* the `(7,3)` three-triple PATH classification, which additionally assumes the active
  image is a three-element literal, while below one that image has at least five members.

Both vacuities were machine-checked against the workflow scratch
`/tmp/gtz-wf/deepen-bundle/private_atom.lean`, which is NOT landed in this repository --
so `1 ≤ value` from a private atom, and the below-one image bound `2m ≤ k * p`, are at
present verified-but-unlanded facts, not citable repository theorems.  A later agent
landing that file should re-derive the two dropped statements' vacuity as Lean theorems
if it wants them on the record, and should note that its own `sq_clarkePairing_le_mul` is
already landed here and must be consumed rather than duplicated.

Provenance: workflow scratch `/tmp/gtz-wf/covseven/coverage_seven_three.lean` (report 03).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Quantitative.CriticalQuadric
import Gtz.Quantitative.InteriorExclusion
import Gtz.Quantitative.IsolatedBlockExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ} {activeIndex : Type*}
variable {D : WeightedDesign m k} {value : ℝ} {multiplierMatrix : Matrix (Fin k) (Fin k) ℝ}
  {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin m)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin k → ℝ)}

/-! ## Linearity of the unrestricted Clarke pairing -/

/-- The Clarke pairing is linear in its right argument along a finite combination.
The unrestricted sibling of the shipped `Gtz.blockClarkePairing_sum_right`. -/
theorem clarkePairing_sum_right (indexSet : Finset (Fin m)) (left : Fin k → ℝ)
    (coefficient : Fin m → ℝ) (piece : Fin m → (Fin k → ℝ)) :
    clarkePairing activeSet activeWeight tightDir left
        (∑ pieceIndex ∈ indexSet, coefficient pieceIndex • piece pieceIndex)
      = ∑ pieceIndex ∈ indexSet, coefficient pieceIndex
        * clarkePairing activeSet activeWeight tightDir left (piece pieceIndex) := by
  classical
  calc clarkePairing activeSet activeWeight tightDir left
        (∑ pieceIndex ∈ indexSet, coefficient pieceIndex • piece pieceIndex)
      = ∑ activeLabel ∈ activeSet, ∑ pieceIndex ∈ indexSet, coefficient pieceIndex
          * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ left)
            * (tightDir activeLabel ⬝ᵥ piece pieceIndex)) := by
        rw [clarkePairing]
        refine Finset.sum_congr rfl fun activeLabel _ => ?_
        rw [dotProduct_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun pieceIndex _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
        ring
    _ = ∑ pieceIndex ∈ indexSet, ∑ activeLabel ∈ activeSet, coefficient pieceIndex
          * (activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ left)
            * (tightDir activeLabel ⬝ᵥ piece pieceIndex)) := Finset.sum_comm
    _ = ∑ pieceIndex ∈ indexSet, coefficient pieceIndex
          * clarkePairing activeSet activeWeight tightDir left (piece pieceIndex) := by
        refine Finset.sum_congr rfl fun pieceIndex _ => ?_
        rw [clarkePairing, Finset.mul_sum]

/-- Reading a subset sum through the Clarke pairing collects weight-free double
products over the subset. -/
theorem clarkePairing_subsetSum_mulVec_left (block : Finset (Fin m)) (probe target : Fin k → ℝ) :
    clarkePairing activeSet activeWeight tightDir (subsetSum D block *ᵥ probe) target
      = ∑ otherAtom ∈ block, (D.atom otherAtom ⬝ᵥ probe)
          * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom) target := by
  rw [clarkePairing_comm, subsetSum_mulVec_eq_sum, clarkePairing_sum_right]
  exact Finset.sum_congr rfl fun otherAtom _ => by rw [clarkePairing_comm]

/-! ## The localisation, weakened from an isolated BLOCK to a private ATOM -/

/-- **THE LOCALISATION AT A PRIVATE ATOM.**  The shipped
`Gtz.blockClarkePairing_atom_eq` asks that the WHOLE block be isolated.  Its proof
only ever consults the block-membership dichotomy AT THE ONE ATOM it is contracted
at, so the hypothesis weakens to: every active subset containing this atom IS the
block.  Nothing is assumed about the other atoms of the block.

The shipped theorem is exactly the `IsIsolatedActiveBlock` instance of this one: that
hypothesis yields the private condition at every atom of the block in one step, through
`Gtz.mem_activeSubset_iff_eq_block_of_isIsolatedActiveBlock`.  The derivation is carried
out below in `card_le_value_of_isIsolatedActiveBlock_viaCrossMass`. -/
theorem blockClarkePairing_atom_eq_of_privateAtom
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) {block : Finset (Fin m)} {atomLabel : Fin m}
    (hatom : atomLabel ∈ block)
    (hprivate : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel →
      activeSubset activeLabel = block) (probe : Fin k → ℝ) :
    blockClarkePairing activeSet activeSubset activeWeight tightDir block probe
        (D.atom atomLabel)
      = (D.weight atomLabel * value)
        * clarkePairing activeSet activeWeight tightDir probe (D.atom atomLabel) := by
  classical
  have hpaired := congrArg (fun vec => vec ⬝ᵥ probe) (hdata.atomStationarity atomLabel)
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul] at hpaired
  have hleft : blockClarkePairing activeSet activeSubset activeWeight tightDir block probe
      (D.atom atomLabel)
      = ∑ activeLabel ∈ activeSet,
        (if atomLabel ∈ activeSubset activeLabel
          then activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) else 0)
        * (tightDir activeLabel ⬝ᵥ probe) := by
    rw [blockClarkePairing]
    refine Finset.sum_congr rfl fun activeLabel hactive => ?_
    by_cases hmem : atomLabel ∈ activeSubset activeLabel
    · rw [if_pos hmem, if_pos (hprivate activeLabel hactive hmem)]
      ring
    · have hne : activeSubset activeLabel ≠ block := by
        intro heq
        exact hmem (by rw [heq]; exact hatom)
      rw [if_neg hmem, if_neg hne]
      ring
  rw [hleft, hpaired, dotProduct_comm (multiplierMatrix *ᵥ D.atom atomLabel) probe,
    multiplierPairing_eq_value_mul_clarkePairing hdata probe (D.atom atomLabel)]
  ring

/-- **THE WEIGHT-FREE BRIDGE AT A PRIVATE ATOM.**  Contract `M_B S_B = value * M_B`
at a private atom of the block, reading the localisation in BOTH slots.  The scalar
`t_c * value` cancels and what survives carries no weights and no isolation:

    `sum_{d in block} <g_d, g_c> * (g_d^T M g_c) = value`   for every atom `c`
    private to `block`.

The shipped `Gtz.clarkePairing_subsetSum_atom_eq_value` is this identity under the
strictly stronger hypothesis that every atom of the block is private. -/
theorem blockOverlapSum_eq_value_of_privateAtom
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    {atomLabel : Fin m} (hatom : atomLabel ∈ block)
    (hprivate : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel →
      activeSubset activeLabel = block) :
    ∑ otherAtom ∈ block, (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
        * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom) (D.atom atomLabel)
      = value := by
  classical
  have hscaleNe : D.weight atomLabel * value ≠ 0 :=
    mul_ne_zero (ne_of_gt (D.weight_pos atomLabel)) hvalueNe
  have heigenSide : blockClarkePairing activeSet activeSubset activeWeight tightDir block
      (D.atom atomLabel) (subsetSum D block *ᵥ D.atom atomLabel)
      = value * ((D.weight atomLabel * value) * 1) := by
    rw [blockClarkePairing_subsetSum_eq hdata block,
      blockClarkePairing_atom_eq_of_privateAtom hdata hatom hprivate (D.atom atomLabel),
      clarkePairing_atom_self_eq_one hdata hvalueNe atomLabel]
  have hexpandSide : blockClarkePairing activeSet activeSubset activeWeight tightDir block
      (D.atom atomLabel) (subsetSum D block *ᵥ D.atom atomLabel)
      = (D.weight atomLabel * value)
        * ∑ otherAtom ∈ block, (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
            * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom)
                (D.atom atomLabel) := by
    rw [subsetSum_mulVec_eq_sum, blockClarkePairing_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun otherAtom _ => ?_
    rw [blockClarkePairing_comm,
      blockClarkePairing_atom_eq_of_privateAtom hdata hatom hprivate (D.atom otherAtom)]
    ring
  have hjoin := hexpandSide.symm.trans heigenSide
  have hcancellable : (D.weight atomLabel * value)
      * (∑ otherAtom ∈ block, (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
          * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom) (D.atom atomLabel))
      = (D.weight atomLabel * value) * value := by
    rw [hjoin]
    ring
  exact mul_left_cancel₀ hscaleNe hcancellable

/-! ## The second moment of an arbitrary subset sum -/

/-- **THE SECOND MOMENT, UNEVALUATED.**  For ANY subset the multiplier-weighted
squared norm of the subset-sum image collects one Clarke pairing per atom.  No
stationarity datum and no isolation appear in the hypotheses -- this is pure bilinear
algebra.  The shipped `Gtz.multiplierTotal_subsetSum_normSq_eq_card_mul_value` is this
identity followed by the isolated-block evaluation of each summand. -/
theorem multiplierTotal_subsetSum_normSq_eq_sum (block : Finset (Fin m)) :
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * ((subsetSum D block *ᵥ tightDir activeLabel)
            ⬝ᵥ (subsetSum D block *ᵥ tightDir activeLabel))
      = ∑ atomLabel ∈ block,
          clarkePairing activeSet activeWeight tightDir
            (subsetSum D block *ᵥ D.atom atomLabel) (D.atom atomLabel) := by
  classical
  have hperActive : ∀ activeLabel ∈ activeSet,
      activeWeight activeLabel
          * ((subsetSum D block *ᵥ tightDir activeLabel)
              ⬝ᵥ (subsetSum D block *ᵥ tightDir activeLabel))
        = ∑ atomLabel ∈ block,
            activeWeight activeLabel
              * (tightDir activeLabel ⬝ᵥ (subsetSum D block *ᵥ D.atom atomLabel))
              * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) := by
    intro activeLabel _
    rw [subsetSum_mulVec_dotProduct_eq_sum D block (tightDir activeLabel)
      (subsetSum D block *ᵥ tightDir activeLabel), Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomLabel _ => ?_
    rw [← subsetSum_mulVec_dotProduct_comm D block (D.atom atomLabel) (tightDir activeLabel),
      dotProduct_comm (subsetSum D block *ᵥ D.atom atomLabel) (tightDir activeLabel),
      dotProduct_comm (D.atom atomLabel) (tightDir activeLabel)]
    ring
  rw [Finset.sum_congr rfl hperActive, Finset.sum_comm]
  rfl

/-! ## The cross-mass inequality -/

/-- **THE CROSS-MASS INEQUALITY.**  Let `P` be a set of atoms all private to a
common active subset `block`.  Then the Clarke-weighted overlap between `P` and the
REST of the block obeys

    `sum_{c in P} sum_{d in block \ P} <g_d, g_c> * (g_d^T M g_c)  <=  |P| * value - |P|^2` .

Proof: the private bridge evaluates the second moment of `S_P` atom by atom as
`value` minus the cross term; the first moment of `S_P` is `|P|` by the quadric law;
and the shipped multiplier-weighted Cauchy-Schwarz compares them.

When `P` is the WHOLE block -- the case where the block is isolated -- the cross term
is an empty sum and the inequality reads `|P|^2 <= |P| * value`, which is the shipped
`Gtz.card_le_value_of_isIsolatedActiveBlock`.  So this strictly generalises it, and
the generalisation is exactly the residue a block with SHARED atoms leaves behind.

BAND OF USE: nonempty `P` already forces `1 ≤ value` (see this file's header), so the
below-one regime this was built for is empty.  What survives is `2 ≤ |P|` with
`1 ≤ value < |P|`. -/
theorem crossMass_le_of_privatePart
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block privatePart : Finset (Fin m)}
    (hsubset : privatePart ⊆ block)
    (hprivate : ∀ atomLabel ∈ privatePart, ∀ activeLabel ∈ activeSet,
      atomLabel ∈ activeSubset activeLabel → activeSubset activeLabel = block) :
    ∑ atomLabel ∈ privatePart, ∑ otherAtom ∈ block \ privatePart,
        (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
          * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom) (D.atom atomLabel)
      ≤ (privatePart.card : ℝ) * value - (privatePart.card : ℝ) ^ 2 := by
  classical
  have hcauchy := sq_multiplierPairingTotal_le_multiplierNormTotal hdata
    (fun activeLabel => subsetSum D privatePart *ᵥ tightDir activeLabel)
  rw [multiplierTotal_subsetSum_form_eq_card hdata hvalueNe privatePart,
    multiplierTotal_subsetSum_normSq_eq_sum (D := D) privatePart] at hcauchy
  have hperAtom : ∀ atomLabel ∈ privatePart,
      clarkePairing activeSet activeWeight tightDir
          (subsetSum D privatePart *ᵥ D.atom atomLabel) (D.atom atomLabel)
        = value - ∑ otherAtom ∈ block \ privatePart,
            (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
              * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom)
                  (D.atom atomLabel) := by
    intro atomLabel hatomPriv
    have hwhole := blockOverlapSum_eq_value_of_privateAtom hdata hvalueNe (hsubset hatomPriv)
      (hprivate atomLabel hatomPriv)
    have hsplit := Finset.sum_sdiff (f := fun otherAtom => (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
      * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom) (D.atom atomLabel))
      hsubset
    rw [hwhole] at hsplit
    rw [clarkePairing_subsetSum_mulVec_left]
    linarith [hsplit]
  rw [Finset.sum_congr rfl hperAtom, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul] at hcauchy
  linarith [hcauchy]

/-- **DEGENERACY CHECK ON THE CROSS-MASS INEQUALITY.**  This is not an independent proof
of the shipped `Gtz.card_le_value_of_isIsolatedActiveBlock` -- it is the regression test
that the NEW inequality above degenerates correctly.  Every atom of an isolated block is
its own private atom, `block \ block` is empty, and dividing by the positive card returns
the shipped statement exactly.  A generalisation that failed to recover its own special case
would be wrong, and this pins that it does not. -/
theorem card_le_value_of_isIsolatedActiveBlock_viaCrossMass
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    (hblockNonempty : block.Nonempty)
    (hisolated : IsIsolatedActiveBlock activeSet activeSubset block) :
    (block.card : ℝ) ≤ value := by
  classical
  have hprivate : ∀ atomLabel ∈ block, ∀ activeLabel ∈ activeSet,
      atomLabel ∈ activeSubset activeLabel → activeSubset activeLabel = block :=
    fun atomLabel hatom activeLabel hactive hmem =>
      (mem_activeSubset_iff_eq_block_of_isIsolatedActiveBlock hisolated hactive hatom).mp hmem
  have hbound := crossMass_le_of_privatePart hdata hvalueNe (Finset.Subset.refl block) hprivate
  rw [Finset.sdiff_self] at hbound
  simp only [Finset.sum_empty, Finset.sum_const_zero] at hbound
  have hcardPos : (0 : ℝ) < (block.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hblockNonempty
  have hmul : (block.card : ℝ) * (block.card : ℝ) ≤ (block.card : ℝ) * value := by
    have hsq := hbound
    rw [pow_two] at hsq
    linarith
  exact le_of_mul_le_mul_left hmul hcardPos

/-! ## The Clarke correlation of two atoms is a correlation -/

/-- **CAUCHY-SCHWARZ FOR THE CLARKE PAIRING.**  It is the quadratic form of a
nonnegative combination of rank-one projectors, so it obeys the Cauchy-Schwarz
inequality.  Proved through the explicit decomposition, with `sqrt` of the
multipliers, exactly as the shipped multiplier-weighted Cauchy-Schwarz is.

Deliberately NOT routed through `Gtz.quadForm_sq_le_mul_of_posSemidef`: that is PSD
Cauchy-Schwarz for a MATRIX form, whereas the Clarke pairing is a scalar-sum definition
whose underlying psd matrix is never shipped as a declaration.  The direct proof is also
stronger -- it needs no `value ≠ 0`. -/
theorem sq_clarkePairing_le_mul
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (left right : Fin k → ℝ) :
    clarkePairing activeSet activeWeight tightDir left right ^ 2
      ≤ clarkePairing activeSet activeWeight tightDir left left
        * clarkePairing activeSet activeWeight tightDir right right := by
  classical
  have hsplit := Finset.sum_mul_sq_le_sq_mul_sq activeSet
    (fun activeLabel => Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ left))
    (fun activeLabel => Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ right))
  have hcross : ∑ activeLabel ∈ activeSet,
      (Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ left))
        * (Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ right))
      = clarkePairing activeSet activeWeight tightDir left right := by
    rw [clarkePairing]
    refine Finset.sum_congr rfl fun activeLabel hactive => ?_
    have hroot := Real.mul_self_sqrt (hdata.activeWeight_nonneg activeLabel hactive)
    calc (Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ left))
          * (Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ right))
        = (Real.sqrt (activeWeight activeLabel) * Real.sqrt (activeWeight activeLabel))
          * ((tightDir activeLabel ⬝ᵥ left) * (tightDir activeLabel ⬝ᵥ right)) := by ring
      _ = activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ left)
          * (tightDir activeLabel ⬝ᵥ right) := by rw [hroot]; ring
  have hleftSq : ∑ activeLabel ∈ activeSet,
      (Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ left)) ^ 2
      = clarkePairing activeSet activeWeight tightDir left left := by
    rw [clarkePairing]
    refine Finset.sum_congr rfl fun activeLabel hactive => ?_
    rw [mul_pow, Real.sq_sqrt (hdata.activeWeight_nonneg activeLabel hactive)]
    ring
  have hrightSq : ∑ activeLabel ∈ activeSet,
      (Real.sqrt (activeWeight activeLabel) * (tightDir activeLabel ⬝ᵥ right)) ^ 2
      = clarkePairing activeSet activeWeight tightDir right right := by
    rw [clarkePairing]
    refine Finset.sum_congr rfl fun activeLabel hactive => ?_
    rw [mul_pow, Real.sq_sqrt (hdata.activeWeight_nonneg activeLabel hactive)]
    ring
  rw [hcross, hleftSq, hrightSq] at hsplit
  exact hsplit

/-- **THE ATOM CORRELATIONS ARE CORRELATIONS.**  Every atom sits at Clarke level one
(the quadric law), so Cauchy-Schwarz bounds the Clarke pairing of any two atoms by
one in absolute value.  In matrix language: `K = (g_c^T M g_d)` is positive
semidefinite with unit diagonal, hence a correlation matrix, and this is its
off-diagonal bound. -/
theorem abs_clarkePairing_atom_le_one
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (atomFirst atomSecond : Fin m) :
    |clarkePairing activeSet activeWeight tightDir (D.atom atomFirst) (D.atom atomSecond)| ≤ 1 := by
  have hcauchy := sq_clarkePairing_le_mul hdata (D.atom atomFirst) (D.atom atomSecond)
  rw [clarkePairing_atom_self_eq_one hdata hvalueNe atomFirst,
    clarkePairing_atom_self_eq_one hdata hvalueNe atomSecond, one_mul] at hcauchy
  have habsSq : |clarkePairing activeSet activeWeight tightDir (D.atom atomFirst)
      (D.atom atomSecond)| ^ 2 ≤ 1 := by
    rw [sq_abs]
    exact hcauchy
  nlinarith [abs_nonneg (clarkePairing activeSet activeWeight tightDir (D.atom atomFirst)
    (D.atom atomSecond)), habsSq]

/-- **THE GEOMETRIC READING OF THE CROSS-MASS INEQUALITY.**  Since the Clarke
correlations are bounded by one, the cross-mass inequality becomes a statement about
the atoms alone:

    `|P| * (|P| - value)  <=  sum_{c in P} sum_{d in block \ P} |<g_d, g_c>|` .

The private atoms of an active subset must carry a LARGE total overlap with the
subset's shared atoms -- with no multiplier, no tight direction and no Clarke datum
left in the conclusion.  At `P = block` the right side is an empty sum, and the
inequality degenerates to the isolated-block exclusion `card block <= value`.

Same band of use as `crossMass_le_of_privatePart`: non-trivial only for `2 ≤ |P|` with
`1 ≤ value < |P|`, because a nonempty private part already forces `1 ≤ value`. -/
theorem overlapAbsSum_ge_of_privatePart
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block privatePart : Finset (Fin m)}
    (hsubset : privatePart ⊆ block)
    (hprivate : ∀ atomLabel ∈ privatePart, ∀ activeLabel ∈ activeSet,
      atomLabel ∈ activeSubset activeLabel → activeSubset activeLabel = block) :
    (privatePart.card : ℝ) * ((privatePart.card : ℝ) - value)
      ≤ ∑ atomLabel ∈ privatePart, ∑ otherAtom ∈ block \ privatePart,
          |D.atom otherAtom ⬝ᵥ D.atom atomLabel| := by
  classical
  have hcross := crossMass_le_of_privatePart hdata hvalueNe hsubset hprivate
  have hpointwise : ∀ atomLabel ∈ privatePart, ∀ otherAtom ∈ block \ privatePart,
      -|D.atom otherAtom ⬝ᵥ D.atom atomLabel|
        ≤ (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
            * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom)
                (D.atom atomLabel) := by
    intro atomLabel _ otherAtom _
    have habs := abs_clarkePairing_atom_le_one hdata hvalueNe otherAtom atomLabel
    have hproduct : |(D.atom otherAtom ⬝ᵥ D.atom atomLabel)
        * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom) (D.atom atomLabel)|
        ≤ |D.atom otherAtom ⬝ᵥ D.atom atomLabel| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) habs
    have hneg := neg_abs_le ((D.atom otherAtom ⬝ᵥ D.atom atomLabel)
      * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom) (D.atom atomLabel))
    linarith
  have hsumLower : ∑ atomLabel ∈ privatePart, ∑ otherAtom ∈ block \ privatePart,
        (-|D.atom otherAtom ⬝ᵥ D.atom atomLabel|)
      ≤ ∑ atomLabel ∈ privatePart, ∑ otherAtom ∈ block \ privatePart,
          (D.atom otherAtom ⬝ᵥ D.atom atomLabel)
            * clarkePairing activeSet activeWeight tightDir (D.atom otherAtom)
                (D.atom atomLabel) :=
    Finset.sum_le_sum fun atomLabel hatom =>
      Finset.sum_le_sum fun otherAtom hother => hpointwise atomLabel hatom otherAtom hother
  have hnegSum : ∑ atomLabel ∈ privatePart, ∑ otherAtom ∈ block \ privatePart,
        (-|D.atom otherAtom ⬝ᵥ D.atom atomLabel|)
      = - ∑ atomLabel ∈ privatePart, ∑ otherAtom ∈ block \ privatePart,
          |D.atom otherAtom ⬝ᵥ D.atom atomLabel| := by
    simp
  rw [hnegSum] at hsumLower
  nlinarith [hcross, hsumLower]

/-! ## Two structural consequences of privacy -/

/-- **A BLOCK WITH A PRIVATE ATOM IS CARRIED BY A POSITIVE MULTIPLIER.**  The
localisation evaluates the block's own Clarke mass at its private atom as
`t_c * value`, which is nonzero; a vanishing sum cannot have a nonzero value, so some
active index carries the block with a strictly positive Clarke multiplier.

Its originally intended consumer was a below-one path-pattern classification at `(7,3)`,
which does not exist (see this file's header).  It is landed anyway because the statement
is non-vacuous, carries no below-one hypothesis, and is the natural existence companion
to `blockClarkePairing_atom_eq_of_privateAtom`. -/
theorem exists_pos_activeWeight_of_privateAtom
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    {atomLabel : Fin m} (hatom : atomLabel ∈ block)
    (hprivate : ∀ activeLabel ∈ activeSet, atomLabel ∈ activeSubset activeLabel →
      activeSubset activeLabel = block) :
    ∃ activeLabel ∈ activeSet, activeSubset activeLabel = block
      ∧ 0 < activeWeight activeLabel := by
  classical
  have hmass : blockClarkePairing activeSet activeSubset activeWeight tightDir block
      (D.atom atomLabel) (D.atom atomLabel) ≠ 0 := by
    rw [blockClarkePairing_atom_eq_of_privateAtom hdata hatom hprivate (D.atom atomLabel),
      clarkePairing_atom_self_eq_one hdata hvalueNe atomLabel, mul_one]
    exact mul_ne_zero (ne_of_gt (D.weight_pos atomLabel)) hvalueNe
  rw [blockClarkePairing] at hmass
  obtain ⟨witnessLabel, hwitness, htermNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmass
  have hblockEq : activeSubset witnessLabel = block := by
    by_contra hblockNe
    rw [if_neg hblockNe, zero_mul, zero_mul] at htermNe
    exact htermNe rfl
  refine ⟨witnessLabel, hwitness, hblockEq, ?_⟩
  rw [if_pos hblockEq] at htermNe
  have hweightNe : activeWeight witnessLabel ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, zero_mul] at htermNe
    exact htermNe rfl
  exact lt_of_le_of_ne (hdata.activeWeight_nonneg witnessLabel hwitness) (Ne.symm hweightNe)

/-- **BELOW ONE THE TIGHT DIRECTIONS ARE LINEARLY DEPENDENT, EXPLICITLY.**  The
shipped `Gtz.not_hasIndependentTightSupport_of_value_lt_one` is a negation of a
product-form predicate, which a rank argument cannot consume directly; this is the
witness it asserts, in the shape a rank argument does consume -- a vanishing
combination with a coefficient that does not vanish. -/
theorem exists_dependence_tightDir_of_value_lt_one
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hbelowOne : value < 1) :
    ∃ coefficient : activeIndex → ℝ,
      (∑ activeLabel ∈ activeSet, coefficient activeLabel • tightDir activeLabel = 0)
        ∧ ∃ witnessLabel ∈ activeSet, coefficient witnessLabel ≠ 0 := by
  by_contra hnone
  refine absurd ?_ (not_hasIndependentTightSupport_of_value_lt_one hdata hvalueNe hbelowOne)
  intro rawCoefficient hvanish activeLabel hactive
  by_contra hne
  exact hnone ⟨fun label => activeWeight label * rawCoefficient label, hvanish,
    activeLabel, hactive, hne⟩

/-! ## The image floor at the frontier cell -/

section SevenThree

variable {activeIndex : Type*} {D : WeightedDesign 7 3} {value : ℝ}
  {multiplierMatrix : Matrix (Fin 3) (Fin 3) ℝ} {activeSet : Finset activeIndex}
  {activeSubset : activeIndex → Finset (Fin 7)} {activeWeight : activeIndex → ℝ}
  {tightDir : activeIndex → (Fin 3 → ℝ)}

/-- **THE `(7,3)` IMAGE FLOOR.**  Three atoms per active triple cannot cover seven
atoms with two triples, so a stationarity datum with a nonzero value at the frontier
cell has at least THREE distinct active triples -- with no below-one hypothesis at
all, unlike the shipped `(6,3)` statement `Gtz.three_le_card_activeSubsetImage_sixThree`,
which needed one to kill the two-block partition. -/
theorem three_le_card_activeSubsetImage_sevenThree
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) :
    3 ≤ (activeSet.image activeSubset).card := by
  have hbound := size_le_rank_mul_card_activeSubsetImage hdata hvalueNe
  omega

end SevenThree

end Gtz
