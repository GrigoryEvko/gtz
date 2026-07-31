/-
# `PARTITION-BELOW-ONE`, PROVED — an isolated active block forces the value to the rank

`Gtz/Quantitative/InteriorExclusion.lean` names its open leaf in capitals:

> **PARTITION-BELOW-ONE.**  No stationarity datum whose distinct active subsets
> partition the atoms has `0 < value < 1`.  NOT PROVED, and NOT assumed anywhere.

This file proves it, unconditionally, from a weaker hypothesis, and with a
conclusion far stronger than `1 <= value`.

## The statement

`IsIsolatedActiveBlock` asks LESS than a partition: ONE active subset disjoint from
every OTHER active subset.  Distinct blocks of a partition are pairwise disjoint, so
a partition block is the special case; nothing here constrains the atoms outside the
block and no covering hypothesis appears.  Under it, at nonzero value,

    card block <= value        (`card_le_value_of_isIsolatedActiveBlock`)

and when the block is an active subset its card IS the rank, so

    rank <= value              (`rank_le_value_of_isIsolatedActiveBlock_mem_image`)

which for `rank >= 1` gives the leaf (`not_value_lt_one_of_isIsolatedActiveBlock`).
The named leaf in its own words — the distinct active subsets pairwise disjoint — is
`rank_le_value_of_pairwiseDisjoint_activeSubset`.

The bound is SHARP, not merely sufficient: `Gtz.value_eq_rank_of_constant_activeSubset`
forces `value = rank` when every active subset is the same, which is the one-block
instance of the hypothesis, and the Cauchy-Schwarz step below is an equality exactly
there.

## The proof

Write `M` for the Clarke multiplier `sum_i lambda_i u_i u_i^T`, which
`Gtz.multiplierMatrix_eq_of_isQuadricStationaryData` identifies with
`multiplierMatrix / value`; `M_B` for the same sum restricted to the indices
carrying the block; `S_B = sum_{c in B} g_c g_c^T`; `theta_c = t_c * value`.
Three facts and one inequality.

1. **The quadric** — `Gtz.tightOverlap_sum_eq_one_of_isQuadricStationaryData`:
   `g_c^T M g_c = 1` at EVERY atom, no isolation needed.  Summing over the block,
   `trace (M S_B) = card block`; that is the first moment
   (`multiplierTotal_subsetSum_form_eq_card`).
2. **The localisation** — isolation makes atom stationarity read
   `M_B g_c = theta_c * M g_c` for `c` in the block, because the only active subsets
   meeting such an atom are copies of the block itself
   (`blockClarkePairing_atom_eq`).
3. **The weight-free bridge** (`clarkePairing_subsetSum_atom_eq_value`) — contract
   `M_B S_B = value * M_B` at one atom of the block, reading the left factor through
   the localisation IN THE OTHER SLOT.  The scalar `theta_c` cancels off both sides
   and what survives carries no weights at all:

       g_c^T M S_B g_c = value        for every c in the block.

   Summing over the block, `trace (M S_B ^ 2) = card block * value`; that is the
   second moment (`multiplierTotal_subsetSum_normSq_eq_card_mul_value`).
4. **Cauchy-Schwarz**, twice (`sq_multiplierPairingTotal_le_multiplierNormTotal`):
   the vector form at each unit tight direction, then the multiplier-weighted form
   across the active set.  It says `trace (M S_B) ^ 2 <= trace M * trace (M S_B ^ 2)`,
   and `trace M = 1`.

Substituting 1 and 3 into 4 gives `(card block) ^ 2 <= card block * value`.

Everything is done with scalar sums and bilinear pairings.  No eigenvalues, no
spectral theorem, no matrix square root, no subdifferential calculus.  The
decomposition `M = sum_i lambda_i u_i u_i^T` is what replaces the square root the
trace form of Cauchy-Schwarz would otherwise need.

## Three wrong turns, recorded so they are not retried

WHY THE PREVIOUSLY REPORTED ROUTE FAILED.  The route recorded in
`InteriorExclusion`'s header contracted through Parseval,
`M_B = M_B * (sum_c t_c g_c g_c^T)`, and landed on `M_B = M A` with
`A = sum_{c in B} t_c theta_c g_c g_c^T + sum_{c not in B} t_c (1 - theta_c) g_c g_c^T`
— not `M P_B`, exactly as that header says.  Contracting against the block's own
subset sum instead is what lets the eigenvector field bite.

WHY THE TRACE AGAINST THE SUBSET SUM IS NOT ENOUGH BY ITSELF.  The quadric gives
`trace (M S_B) = card block` and hence `trace (M (value - S_B)) = value - card block`
IDENTICALLY, so that inequality is the conclusion restated and no manipulation of it
closes anything.  The second moment is where the eigenvector field enters and the
information appears.

WHY THE WEIGHTED BRIDGE IS THE WEAKER READING.  Reading the localisation in the
FIRST slot instead of the second keeps the weights and yields
`sum_{c' in B} t_c' (g_c'.g_c) (g_c^T M g_c') = t_c * value`, whose Cauchy-Schwarz
consequence is `value >= (sum_{c in B} t_c) ^ 2 / sum_{c in B} t_c ^ 2` — the block's
inverse participation ratio.  That is a true bound and it was the first proof here,
but `(sum t) ^ 2 <= card block * sum t ^ 2` is Cauchy-Schwarz again, so it is
strictly weaker than `card block <= value` and it has been dropped rather than kept
alongside.

## What this closes, and what it does not

CLOSED: the named leaf, unconditionally and in the strong form `rank <= value`; the
`(7,3)` partition branch twice over, since three does not divide seven (the vacuity
section below); and the `(6,3)` dichotomy's partition branch, so that dichotomy
collapses to its first alternative
(`three_le_card_activeSubsetImage_sixThree`).

ISOLATION IS LOAD-BEARING, NOT DECORATION.  `InteriorExclusion` ships
`Gtz.not_forall_one_le_value_of_isQuadricStationaryData`: the bundle ALONE does not
force `1 <= value`, witnessed at `(4,2)` by a design whose four active pairs all
overlap and whose common value is `2 - sqrt 2`.  So no strengthening of the argument
below can drop the hypothesis, and the witness is the proof of that.

NOT CLOSED, stated so it cannot be misread: this does NOT prove
`Gtz.GtzWeighted 6 3` or `Gtz.GtzWeighted 7 3`.  It kills one branch of the `(6,3)`
dichotomy and leaves the three-or-more-distinct-subsets branch untouched.
`InteriorExclusion`'s firewall note records that the argmax-complete form of that
remaining branch is the interior case of GTZ itself, so none of the residue is
claimed here.

Calibrated against the shipped inhabitants before anything was written:
`Gtz.splitSevenDesign_isQuadricStationaryData` has `value = 1` with twenty
OVERLAPPING active triples, and `Gtz.belowOneDesign_isQuadricStationaryData` has
`value = 2 - sqrt 2` with four OVERLAPPING active pairs.  Neither carries an isolated
block, so neither is a counterexample and neither is an inhabitant: the repository
owns NO stationarity datum satisfying the hypothesis, and the theorem's force is
entirely as a branch-killer, not as a statement about a datum in hand.  What pins it
as non-vacuous instead is the machine-checked agreement
`multiplierTotal_subsetSum_moments_eq_of_constant_activeSubset` below, which shows
the Cauchy-Schwarz is an equality wherever the shipped
`Gtz.value_eq_rank_of_constant_activeSubset` applies.  A `(2,1)` two-block datum was
hand-checked against both moment identities and sits at `value = rank = 1` exactly.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Quantitative.CriticalQuadric
import Gtz.Quantitative.InteriorExclusion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ} {activeIndex : Type*}

/-! ## The partition branch is vacuous at the frontier cell -/

/-- **No partition of seven atoms into triples.**  A partition into blocks of card
three carries `3 * blockCount` atoms, and seven is not a multiple of three, so the
`(7,3)` partition branch is empty before any stationarity input. -/
theorem not_exists_tripleBlockCount_seven : ¬ ∃ blockCount : ℕ, 3 * blockCount = 7 := by
  rintro ⟨blockCount, hcount⟩
  omega

/-- A partition into blocks of card `rank` forces `rank` to divide the atom count. -/
theorem rank_dvd_size_of_blockCount {rank size blockCount : ℕ}
    (hpartition : rank * blockCount = size) : rank ∣ size :=
  ⟨blockCount, hpartition.symm⟩

/-- **The frontier cell has no partition of its atoms into subsets of the rank.** -/
theorem not_rank_dvd_size_sevenThree : ¬ (3 ∣ 7) := by decide

/-! ## Isolated blocks and the localisation -/

/-- **An isolated active block**: an active subset disjoint from every other active
subset.  Strictly weaker than being a block of a partition. -/
def IsIsolatedActiveBlock (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin m)) (block : Finset (Fin m)) : Prop :=
  ∀ activeLabel ∈ activeSet, activeSubset activeLabel ≠ block →
    Disjoint (activeSubset activeLabel) block

/-- **THE LOCALISATION.**  An atom of an isolated block is met by an active subset
exactly when that subset IS the block.  This is the entire force of isolation. -/
theorem mem_activeSubset_iff_eq_block_of_isIsolatedActiveBlock
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin m)}
    {block : Finset (Fin m)} (hisolated : IsIsolatedActiveBlock activeSet activeSubset block)
    {activeLabel : activeIndex} (hactive : activeLabel ∈ activeSet) {atomLabel : Fin m}
    (hatom : atomLabel ∈ block) :
    atomLabel ∈ activeSubset activeLabel ↔ activeSubset activeLabel = block := by
  refine ⟨fun hmem => ?_, fun heq => heq ▸ hatom⟩
  by_contra hne
  exact Finset.disjoint_left.mp (hisolated activeLabel hactive hne) hmem hatom

/-! ## The subset sum as an operator on probes -/

/-- The subset sum acts on a probe as the unweighted combination of its atoms. -/
theorem subsetSum_mulVec_eq_sum (D : WeightedDesign m k) (block : Finset (Fin m))
    (probe : Fin k → ℝ) :
    subsetSum D block *ᵥ probe
      = ∑ atomLabel ∈ block, (D.atom atomLabel ⬝ᵥ probe) • D.atom atomLabel := by
  rw [subsetSum, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun atomLabel _ => ?_
  rw [atomMatrix, vecMulVec_mulVec_eq]

/-- Pairing the subset-sum image of a probe against a target collects weight-free
double products over the block. -/
theorem subsetSum_mulVec_dotProduct_eq_sum (D : WeightedDesign m k) (block : Finset (Fin m))
    (probe target : Fin k → ℝ) :
    (subsetSum D block *ᵥ probe) ⬝ᵥ target
      = ∑ atomLabel ∈ block, (D.atom atomLabel ⬝ᵥ probe) * (D.atom atomLabel ⬝ᵥ target) := by
  rw [subsetSum_mulVec_eq_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun atomLabel _ => ?_
  rw [smul_dotProduct, smul_eq_mul]

/-- **The subset sum is self-adjoint.**  Both readings collect the same weight-free
double product over the block. -/
theorem subsetSum_mulVec_dotProduct_comm (D : WeightedDesign m k) (block : Finset (Fin m))
    (left right : Fin k → ℝ) :
    (subsetSum D block *ᵥ left) ⬝ᵥ right = left ⬝ᵥ (subsetSum D block *ᵥ right) := by
  rw [subsetSum_mulVec_dotProduct_eq_sum, dotProduct_comm left (subsetSum D block *ᵥ right),
    subsetSum_mulVec_dotProduct_eq_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## The two Clarke pairings -/

variable {D : WeightedDesign m k} {value : ℝ} {multiplierMatrix : Matrix (Fin k) (Fin k) ℝ}
  {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin m)}
  {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin k → ℝ)}

/-- **The Clarke pairing** `left^T M right`, where `M = sum_i lambda_i u_i u_i^T` is
the multiplier divided by the value. -/
noncomputable def clarkePairing (activeSet : Finset activeIndex) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin k → ℝ)) (left right : Fin k → ℝ) : ℝ :=
  ∑ activeLabel ∈ activeSet,
    activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ left) * (tightDir activeLabel ⬝ᵥ right)

/-- **The block Clarke pairing** `left^T M_B right`: the same sum restricted to the
indices whose active subset IS the block. -/
noncomputable def blockClarkePairing (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin m)) (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin k → ℝ)) (block : Finset (Fin m))
    (left right : Fin k → ℝ) : ℝ :=
  ∑ activeLabel ∈ activeSet,
    (if activeSubset activeLabel = block then activeWeight activeLabel else 0)
      * (tightDir activeLabel ⬝ᵥ left) * (tightDir activeLabel ⬝ᵥ right)

/-- Both pairings are symmetric — they are quadratic forms of symmetric matrices. -/
theorem clarkePairing_comm (left right : Fin k → ℝ) :
    clarkePairing activeSet activeWeight tightDir left right
      = clarkePairing activeSet activeWeight tightDir right left := by
  rw [clarkePairing, clarkePairing]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The block pairing is symmetric for the same reason. -/
theorem blockClarkePairing_comm (block : Finset (Fin m)) (left right : Fin k → ℝ) :
    blockClarkePairing activeSet activeSubset activeWeight tightDir block left right
      = blockClarkePairing activeSet activeSubset activeWeight tightDir block right left := by
  rw [blockClarkePairing, blockClarkePairing]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The block Clarke pairing is linear in its right argument along a finite
combination of atoms. -/
theorem blockClarkePairing_sum_right (block indexSet : Finset (Fin m)) (left : Fin k → ℝ)
    (coefficient : Fin m → ℝ) (piece : Fin m → (Fin k → ℝ)) :
    blockClarkePairing activeSet activeSubset activeWeight tightDir block left
        (∑ pieceIndex ∈ indexSet, coefficient pieceIndex • piece pieceIndex)
      = ∑ pieceIndex ∈ indexSet, coefficient pieceIndex
        * blockClarkePairing activeSet activeSubset activeWeight tightDir block left
            (piece pieceIndex) := by
  classical
  calc blockClarkePairing activeSet activeSubset activeWeight tightDir block left
        (∑ pieceIndex ∈ indexSet, coefficient pieceIndex • piece pieceIndex)
      = ∑ activeLabel ∈ activeSet, ∑ pieceIndex ∈ indexSet, coefficient pieceIndex
          * ((if activeSubset activeLabel = block then activeWeight activeLabel else 0)
            * (tightDir activeLabel ⬝ᵥ left) * (tightDir activeLabel ⬝ᵥ piece pieceIndex)) := by
        rw [blockClarkePairing]
        refine Finset.sum_congr rfl fun activeLabel _ => ?_
        rw [dotProduct_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun pieceIndex _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
        ring
    _ = ∑ pieceIndex ∈ indexSet, ∑ activeLabel ∈ activeSet, coefficient pieceIndex
          * ((if activeSubset activeLabel = block then activeWeight activeLabel else 0)
            * (tightDir activeLabel ⬝ᵥ left) * (tightDir activeLabel ⬝ᵥ piece pieceIndex)) :=
        Finset.sum_comm
    _ = ∑ pieceIndex ∈ indexSet, coefficient pieceIndex
          * blockClarkePairing activeSet activeSubset activeWeight tightDir block left
              (piece pieceIndex) := by
        refine Finset.sum_congr rfl fun pieceIndex _ => ?_
        rw [blockClarkePairing, Finset.mul_sum]

/-- **The quadric, as a pairing.**  Every atom sits at level one for the Clarke
pairing — the shipped quadric law in the pairing this file uses. -/
theorem clarkePairing_atom_self_eq_one
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (atomLabel : Fin m) :
    clarkePairing activeSet activeWeight tightDir (D.atom atomLabel) (D.atom atomLabel) = 1 := by
  rw [clarkePairing, ← tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe atomLabel]
  refine Finset.sum_congr rfl fun activeLabel _ => by ring

/-- Pairing the shipped multiplier identity against two probes: the multiplier's
bilinear form is `value` times the Clarke pairing. -/
theorem multiplierPairing_eq_value_mul_clarkePairing
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (left right : Fin k → ℝ) :
    left ⬝ᵥ (multiplierMatrix *ᵥ right)
      = value * clarkePairing activeSet activeWeight tightDir left right := by
  rw [multiplierMatrix_eq_of_isQuadricStationaryData hdata, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  congr 1
  rw [Matrix.sum_mulVec, dotProduct_sum, clarkePairing]
  refine Finset.sum_congr rfl fun activeLabel _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atomMatrix, vecMulVec_mulVec_eq,
    dotProduct_smul, smul_eq_mul, dotProduct_comm left (tightDir activeLabel)]
  ring

/-- **THE LOCALISED STATIONARITY EQUATION.**  At an atom of an isolated block, atom
stationarity reads `M_B g_c = theta_c * M g_c`, contracted against any probe. -/
theorem blockClarkePairing_atom_eq
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) {block : Finset (Fin m)}
    (hisolated : IsIsolatedActiveBlock activeSet activeSubset block) {atomLabel : Fin m}
    (hatom : atomLabel ∈ block) (probe : Fin k → ℝ) :
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
    · rw [if_pos hmem, if_pos ((mem_activeSubset_iff_eq_block_of_isIsolatedActiveBlock
        hisolated hactive hatom).mp hmem)]
      ring
    · rw [if_neg hmem, if_neg (fun heq => hmem
        ((mem_activeSubset_iff_eq_block_of_isIsolatedActiveBlock hisolated hactive
          hatom).mpr heq))]
      ring
  rw [hleft, hpaired, dotProduct_comm (multiplierMatrix *ᵥ D.atom atomLabel) probe,
    multiplierPairing_eq_value_mul_clarkePairing hdata probe (D.atom atomLabel)]
  ring

/-- The eigenvector field, read through the block pairing: every index carrying the
block contributes `value` times its own pairing. -/
theorem blockClarkePairing_subsetSum_eq
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (block : Finset (Fin m)) (left right : Fin k → ℝ) :
    blockClarkePairing activeSet activeSubset activeWeight tightDir block left
        (subsetSum D block *ᵥ right)
      = value
        * blockClarkePairing activeSet activeSubset activeWeight tightDir block left right := by
  classical
  rw [blockClarkePairing, blockClarkePairing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun activeLabel hactive => ?_
  by_cases heq : activeSubset activeLabel = block
  · have heigen : tightDir activeLabel ⬝ᵥ (subsetSum D block *ᵥ right)
        = value * (tightDir activeLabel ⬝ᵥ right) := by
      rw [← heq]
      exact tightDirection_bilinearForm_eq_smul D (activeSubset activeLabel)
        (hdata.tightDir_isEigenvector activeLabel hactive) right
    rw [if_pos heq, heigen]
    ring
  · rw [if_neg heq]
    ring

/-- **THE WEIGHT-FREE BRIDGE.**  Contract `M_B S_B = value * M_B` at one atom of an
isolated block, reading the localisation in the OTHER slot.  The scalar `theta_c`
divides out of both sides and the surviving identity carries no weights:

    g_c^T M S_B g_c = value.

This is the step the participation-ratio route missed by reading the localisation in
the first slot instead; see the third wrong turn in the header. -/
theorem clarkePairing_subsetSum_atom_eq_value
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    (hisolated : IsIsolatedActiveBlock activeSet activeSubset block) {atomLabel : Fin m}
    (hatom : atomLabel ∈ block) :
    clarkePairing activeSet activeWeight tightDir
        (subsetSum D block *ᵥ D.atom atomLabel) (D.atom atomLabel) = value := by
  classical
  have hscaleNe : D.weight atomLabel * value ≠ 0 :=
    mul_ne_zero (ne_of_gt (D.weight_pos atomLabel)) hvalueNe
  have heigenSide : blockClarkePairing activeSet activeSubset activeWeight tightDir block
      (D.atom atomLabel) (subsetSum D block *ᵥ D.atom atomLabel)
      = value * ((D.weight atomLabel * value) * 1) := by
    rw [blockClarkePairing_subsetSum_eq hdata block,
      blockClarkePairing_atom_eq hdata hisolated hatom (D.atom atomLabel),
      clarkePairing_atom_self_eq_one hdata hvalueNe atomLabel]
  have hlocalSide : blockClarkePairing activeSet activeSubset activeWeight tightDir block
      (D.atom atomLabel) (subsetSum D block *ᵥ D.atom atomLabel)
      = (D.weight atomLabel * value)
        * clarkePairing activeSet activeWeight tightDir
            (subsetSum D block *ᵥ D.atom atomLabel) (D.atom atomLabel) := by
    rw [blockClarkePairing_comm, blockClarkePairing_atom_eq hdata hisolated hatom
      (subsetSum D block *ᵥ D.atom atomLabel)]
  have hjoin := hlocalSide.symm.trans heigenSide
  have hcancellable : (D.weight atomLabel * value)
      * clarkePairing activeSet activeWeight tightDir
          (subsetSum D block *ᵥ D.atom atomLabel) (D.atom atomLabel)
      = (D.weight atomLabel * value) * value := by
    rw [hjoin]
    ring
  exact mul_left_cancel₀ hscaleNe hcancellable

/-! ## The two moments of the subset sum over the whole active set -/

/-- **THE FIRST MOMENT IS THE BLOCK SIZE.**  Straight from the quadric, with no
isolation: each atom of the block contributes exactly one. -/
theorem multiplierTotal_subsetSum_form_eq_card
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (block : Finset (Fin m)) :
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * (tightDir activeLabel ⬝ᵥ (subsetSum D block *ᵥ tightDir activeLabel))
      = (block.card : ℝ) := by
  classical
  have hperActive : ∀ activeLabel ∈ activeSet,
      activeWeight activeLabel
          * (tightDir activeLabel ⬝ᵥ (subsetSum D block *ᵥ tightDir activeLabel))
        = ∑ atomLabel ∈ block,
            activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ D.atom atomLabel) ^ 2 := by
    intro activeLabel _
    rw [subsetSum_form_eq_sum_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomLabel _ => ?_
    rw [dotProduct_comm (D.atom atomLabel) (tightDir activeLabel)]
  rw [Finset.sum_congr rfl hperActive, Finset.sum_comm,
    Finset.sum_congr rfl (fun atomLabel _ =>
      tightOverlap_sum_eq_one_of_isQuadricStationaryData hdata hvalueNe atomLabel),
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **THE SECOND MOMENT IS THE BLOCK SIZE TIMES THE VALUE.**  The weight-free bridge
at each atom of the block, summed. -/
theorem multiplierTotal_subsetSum_normSq_eq_card_mul_value
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    (hisolated : IsIsolatedActiveBlock activeSet activeSubset block) :
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * ((subsetSum D block *ᵥ tightDir activeLabel)
            ⬝ᵥ (subsetSum D block *ᵥ tightDir activeLabel))
      = (block.card : ℝ) * value := by
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
  have hperAtom : ∀ atomLabel ∈ block,
      (∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * (tightDir activeLabel ⬝ᵥ (subsetSum D block *ᵥ D.atom atomLabel))
          * (tightDir activeLabel ⬝ᵥ D.atom atomLabel)) = value := by
    intro atomLabel hatom
    rw [← clarkePairing]
    exact clarkePairing_subsetSum_atom_eq_value hdata hvalueNe hisolated hatom
  rw [Finset.sum_congr rfl hperAtom, Finset.sum_const, nsmul_eq_mul]

/-! ## Cauchy-Schwarz, and the exclusion -/

/-- **THE MULTIPLIER-WEIGHTED CAUCHY-SCHWARZ.**  For any vector attached to each
active index, the square of the multiplier-weighted total of `u_i . w_i` is at most
the multiplier-weighted total of `|w_i| ^ 2`.

Two steps: the vector form at each unit tight direction, then the weighted form
across the active set, whose multipliers are nonnegative and sum to one.  In trace
language this is `trace (M S) ^ 2 <= trace M * trace (M S ^ 2)` with `trace M = 1`,
proved through the explicit decomposition of `M` rather than a matrix square root. -/
theorem sq_multiplierPairingTotal_le_multiplierNormTotal
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (probeImage : activeIndex → (Fin k → ℝ)) :
    (∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probeImage activeLabel)) ^ 2
      ≤ ∑ activeLabel ∈ activeSet,
          activeWeight activeLabel * (probeImage activeLabel ⬝ᵥ probeImage activeLabel) := by
  classical
  have hperIndex : ∀ activeLabel ∈ activeSet,
      activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probeImage activeLabel) ^ 2
        ≤ activeWeight activeLabel * (probeImage activeLabel ⬝ᵥ probeImage activeLabel) := by
    intro activeLabel hactive
    refine mul_le_mul_of_nonneg_left ?_ (hdata.activeWeight_nonneg activeLabel hactive)
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
      (tightDir activeLabel) (probeImage activeLabel)
    rw [← dotProduct, ← dotProduct_self_eq_sum_sq, ← dotProduct_self_eq_sum_sq,
      hdata.tightDir_unit activeLabel hactive, one_mul] at hcauchy
    exact hcauchy
  have hweighted : (∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probeImage activeLabel)) ^ 2
      ≤ ∑ activeLabel ∈ activeSet,
          activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probeImage activeLabel) ^ 2 := by
    have hsplit := Finset.sum_mul_sq_le_sq_mul_sq activeSet
      (fun activeLabel => Real.sqrt (activeWeight activeLabel))
      (fun activeLabel => Real.sqrt (activeWeight activeLabel)
        * (tightDir activeLabel ⬝ᵥ probeImage activeLabel))
    have hleftSum : ∑ activeLabel ∈ activeSet,
        Real.sqrt (activeWeight activeLabel)
          * (Real.sqrt (activeWeight activeLabel)
            * (tightDir activeLabel ⬝ᵥ probeImage activeLabel))
        = ∑ activeLabel ∈ activeSet,
            activeWeight activeLabel * (tightDir activeLabel ⬝ᵥ probeImage activeLabel) := by
      refine Finset.sum_congr rfl fun activeLabel hactive => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (hdata.activeWeight_nonneg activeLabel hactive)]
    have hfirstSq : ∑ activeLabel ∈ activeSet, Real.sqrt (activeWeight activeLabel) ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun activeLabel hactive =>
        Real.sq_sqrt (hdata.activeWeight_nonneg activeLabel hactive)]
      exact hdata.activeWeight_sum_one
    have hsecondSq : ∑ activeLabel ∈ activeSet,
        (Real.sqrt (activeWeight activeLabel)
          * (tightDir activeLabel ⬝ᵥ probeImage activeLabel)) ^ 2
        = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * (tightDir activeLabel ⬝ᵥ probeImage activeLabel) ^ 2 := by
      refine Finset.sum_congr rfl fun activeLabel hactive => ?_
      rw [mul_pow, Real.sq_sqrt (hdata.activeWeight_nonneg activeLabel hactive)]
    rw [hleftSum, hfirstSq, hsecondSq, one_mul] at hsplit
    exact hsplit
  exact hweighted.trans (Finset.sum_le_sum hperIndex)

/-- **THE EXCLUSION, QUANTITATIVE.**  At an isolated active block the value is at
least the block's size.  Substituting the two moment identities into the weighted
Cauchy-Schwarz gives `card block ^ 2 <= card block * value`. -/
theorem card_le_value_of_isIsolatedActiveBlock
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    (hblockNonempty : block.Nonempty)
    (hisolated : IsIsolatedActiveBlock activeSet activeSubset block) :
    (block.card : ℝ) ≤ value := by
  have hcauchy := sq_multiplierPairingTotal_le_multiplierNormTotal hdata
    (fun activeLabel => subsetSum D block *ᵥ tightDir activeLabel)
  rw [multiplierTotal_subsetSum_form_eq_card hdata hvalueNe block,
    multiplierTotal_subsetSum_normSq_eq_card_mul_value hdata hvalueNe hisolated, pow_two] at hcauchy
  have hcardPos : (0 : ℝ) < (block.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hblockNonempty
  exact le_of_mul_le_mul_left hcauchy hcardPos

/-- **THE RANK BOUND.**  When the isolated block is itself an active subset its size
is the rank, so the value is at least the rank.  Sharp: it is an equality on the
constant-active-subset locus, where `Gtz.value_eq_rank_of_constant_activeSubset`
gives `value = rank`. -/
theorem rank_le_value_of_isIsolatedActiveBlock_mem_image
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hrankPos : 0 < k)
    {block : Finset (Fin m)} (hinImage : block ∈ activeSet.image activeSubset)
    (hisolated : IsIsolatedActiveBlock activeSet activeSubset block) :
    (k : ℝ) ≤ value := by
  classical
  obtain ⟨activeLabel, hactive, heq⟩ := Finset.mem_image.mp hinImage
  have hcard : block.card = k := by
    rw [← heq]
    exact hdata.activeSubset_card activeLabel hactive
  have hblockNonempty : block.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hrankPos)
  have hbound := card_le_value_of_isIsolatedActiveBlock hdata hvalueNe hblockNonempty hisolated
  rwa [hcard] at hbound

/-- **`PARTITION-BELOW-ONE`, PROVED, IN ITS OWN WORDS.**  If the distinct active
subsets are pairwise disjoint — in particular if they partition the atoms — then the
value is at least the rank.  No covering hypothesis, no size, no rank fixed. -/
theorem rank_le_value_of_pairwiseDisjoint_activeSubset
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hrankPos : 0 < k)
    (hpairwiseDisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet,
      activeSubset firstLabel ≠ activeSubset secondLabel →
        Disjoint (activeSubset firstLabel) (activeSubset secondLabel)) :
    (k : ℝ) ≤ value := by
  classical
  obtain ⟨witnessLabel, hwitness⟩ := activeSet_nonempty_of_isQuadricStationaryData hdata
  have hisolated : IsIsolatedActiveBlock activeSet activeSubset (activeSubset witnessLabel) :=
    fun activeLabel hactive hne => hpairwiseDisjoint activeLabel hactive witnessLabel hwitness hne
  exact rank_le_value_of_isIsolatedActiveBlock_mem_image hdata hvalueNe hrankPos
    (Finset.mem_image_of_mem activeSubset hwitness) hisolated

/-- The leaf in the shape `InteriorExclusion` asks for, from a pairwise-disjoint
active family. -/
theorem not_value_lt_one_of_pairwiseDisjoint_activeSubset
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hrankPos : 0 < k)
    (hpairwiseDisjoint : ∀ firstLabel ∈ activeSet, ∀ secondLabel ∈ activeSet,
      activeSubset firstLabel ≠ activeSubset secondLabel →
        Disjoint (activeSubset firstLabel) (activeSubset secondLabel)) :
    ¬ value < 1 := by
  have hbound := rank_le_value_of_pairwiseDisjoint_activeSubset hdata hvalueNe hrankPos
    hpairwiseDisjoint
  have hrankOne : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrankPos
  exact not_lt.mpr (hrankOne.trans hbound)

/-- The leaf in the shape `InteriorExclusion` asks for, from a single isolated
block. -/
theorem not_value_lt_one_of_isIsolatedActiveBlock
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) {block : Finset (Fin m)}
    (hblockNonempty : block.Nonempty)
    (hisolated : IsIsolatedActiveBlock activeSet activeSubset block) :
    ¬ value < 1 := by
  have hbound := card_le_value_of_isIsolatedActiveBlock hdata hvalueNe hblockNonempty hisolated
  have hcardOne : (1 : ℝ) ≤ (block.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hblockNonempty
  exact not_lt.mpr (hcardOne.trans hbound)

/-- **A DOUBLY-COVERED ATOM DEFEATS ISOLATION.**  If an atom of the block lies in two
DISTINCT active subsets then the block is not isolated, because the localisation would
force both of them to equal the block.  This is the exact obstruction the shipped
`(4,2)` witness realises. -/
theorem not_isIsolatedActiveBlock_of_two_distinct_activeSubset
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin m)}
    {block : Finset (Fin m)} {atomLabel : Fin m} (hatom : atomLabel ∈ block)
    {firstLabel secondLabel : activeIndex} (hfirst : firstLabel ∈ activeSet)
    (hsecond : secondLabel ∈ activeSet) (hfirstMem : atomLabel ∈ activeSubset firstLabel)
    (hsecondMem : atomLabel ∈ activeSubset secondLabel)
    (hdistinct : activeSubset firstLabel ≠ activeSubset secondLabel) :
    ¬ IsIsolatedActiveBlock activeSet activeSubset block := by
  intro hisolated
  have hfirstEq : activeSubset firstLabel = block :=
    (mem_activeSubset_iff_eq_block_of_isIsolatedActiveBlock hisolated hfirst hatom).mp hfirstMem
  have hsecondEq : activeSubset secondLabel = block :=
    (mem_activeSubset_iff_eq_block_of_isIsolatedActiveBlock hisolated hsecond hatom).mp hsecondMem
  exact hdistinct (hfirstEq.trans hsecondEq.symm)

/-! ## Cross-check against the shipped one-block theorem -/

/-- A constant active subset satisfies pairwise disjointness vacuously, so the route
of this file reaches `rank <= value` on the locus where
`Gtz.value_eq_rank_of_constant_activeSubset` independently gives `value = rank`. -/
theorem rank_le_value_of_constant_activeSubset {commonSubset : Finset (Fin m)}
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hrankPos : 0 < k)
    (hconstant : ∀ activeLabel ∈ activeSet, activeSubset activeLabel = commonSubset) :
    (k : ℝ) ≤ value :=
  rank_le_value_of_pairwiseDisjoint_activeSubset hdata hvalueNe hrankPos
    fun firstLabel hfirst secondLabel hsecond hne =>
      absurd ((hconstant firstLabel hfirst).trans (hconstant secondLabel hsecond).symm) hne

/-- **THE CAUCHY-SCHWARZ IS TIGHT ON THE ONE-BLOCK LOCUS, AND THE TWO ROUTES AGREE.**
There the first moment is `rank` and the second is `rank * value`, so the inequality
of `sq_multiplierPairingTotal_le_multiplierNormTotal` holds with EQUALITY exactly
when `value = rank` — which is what `Gtz.value_eq_rank_of_constant_activeSubset`
proves by a route that never touches the weight-free bridge.

So this is a genuine cross-lane agreement test, not a restatement: the second moment
here rides the bridge and the localisation, the shipped theorem rides neither, and
the two numbers must coincide for this to close.  It also shows `card block <= value`
cannot be improved. -/
theorem multiplierTotal_subsetSum_moments_eq_of_constant_activeSubset
    {commonSubset : Finset (Fin m)}
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0)
    (hconstant : ∀ activeLabel ∈ activeSet, activeSubset activeLabel = commonSubset) :
    (∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * (tightDir activeLabel ⬝ᵥ (subsetSum D commonSubset *ᵥ tightDir activeLabel))) ^ 2
      = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * ((subsetSum D commonSubset *ᵥ tightDir activeLabel)
              ⬝ᵥ (subsetSum D commonSubset *ᵥ tightDir activeLabel)) := by
  obtain ⟨someActive, hsomeMem⟩ := activeSet_nonempty_of_isQuadricStationaryData hdata
  have hcard : commonSubset.card = k := by
    rw [← hconstant someActive hsomeMem]
    exact hdata.activeSubset_card someActive hsomeMem
  have hisolated : IsIsolatedActiveBlock activeSet activeSubset commonSubset :=
    fun activeLabel hactive hne => absurd (hconstant activeLabel hactive) hne
  rw [multiplierTotal_subsetSum_form_eq_card hdata hvalueNe commonSubset,
    multiplierTotal_subsetSum_normSq_eq_card_mul_value hdata hvalueNe hisolated,
    value_eq_rank_of_constant_activeSubset hdata hvalueNe hconstant, hcard, pow_two]

/-! ## The two-block image, and the `(6,3)` collapse -/

/-- **A two-element active image with disjoint members forces the rank bound.**  This
is the exact shape of the partition branch of the `(6,3)` dichotomy. -/
theorem rank_le_value_of_disjointPair_activeSubsetImage
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hrankPos : 0 < k)
    {firstSubset secondSubset : Finset (Fin m)}
    (himage : activeSet.image activeSubset = {firstSubset, secondSubset})
    (hdisjoint : Disjoint firstSubset secondSubset) :
    (k : ℝ) ≤ value := by
  classical
  have hisolated : IsIsolatedActiveBlock activeSet activeSubset firstSubset := by
    intro activeLabel hactive hne
    have hmem : activeSubset activeLabel
        ∈ ({firstSubset, secondSubset} : Finset (Finset (Fin m))) := by
      rw [← himage]
      exact Finset.mem_image_of_mem activeSubset hactive
    rcases Finset.mem_insert.mp hmem with hfirst | hsecond
    · exact absurd hfirst hne
    · rw [Finset.mem_singleton.mp hsecond]
      exact hdisjoint.symm
  refine rank_le_value_of_isIsolatedActiveBlock_mem_image hdata hvalueNe hrankPos ?_ hisolated
  rw [himage]
  exact Finset.mem_insert_self firstSubset {secondSubset}

/-- **THE `(6,3)` DICHOTOMY COLLAPSES.**  Its partition branch would force
`3 <= value`, so a stationarity datum with a nonzero value strictly below one at
`(6,3)` has at least THREE distinct active triples — unconditionally.

`Gtz.three_le_card_activeSubsetImage_or_dependentPartition_sixThree` is the
disjunction this strengthens; the second alternative is now dead. -/
theorem three_le_card_activeSubsetImage_sixThree {D : WeightedDesign 6 3} {value : ℝ}
    {multiplierMatrix : Matrix (Fin 3) (Fin 3) ℝ} {activeSet : Finset activeIndex}
    {activeSubset : activeIndex → Finset (Fin 6)} {activeWeight : activeIndex → ℝ}
    {tightDir : activeIndex → (Fin 3 → ℝ)}
    (hdata : IsQuadricStationaryData D value multiplierMatrix activeSet activeSubset
      activeWeight tightDir) (hvalueNe : value ≠ 0) (hbelowOne : value < 1) :
    3 ≤ (activeSet.image activeSubset).card := by
  rcases three_le_card_activeSubsetImage_or_dependentPartition_sixThree hdata hvalueNe hbelowOne
    with hthree | ⟨_, firstSubset, secondSubset, himage, hdisjoint, _⟩
  · exact hthree
  · exfalso
    have hbound := rank_le_value_of_disjointPair_activeSubsetImage hdata hvalueNe (by norm_num)
      himage hdisjoint
    have hthreeLe : (3 : ℝ) ≤ value := by exact_mod_cast hbound
    linarith

/-! ## The surviving branch is a certified wall, not an unfinished step -/

/-- **THE SHIPPED `(4,2)` WITNESS HAS NO NONEMPTY ISOLATED BLOCK.**  Its four active
pairs form a four-cycle, so every atom sits in two of them, and
`not_isIsolatedActiveBlock_of_two_distinct_activeSubset` applies at every atom.  The
theorems of this file therefore do not apply to it, which is exactly why they do not
contradict `Gtz.belowOneValue_lt_one`. -/
theorem not_isIsolatedActiveBlock_belowOneSubset_of_nonempty {block : Finset (Fin 4)}
    (hblockNonempty : block.Nonempty) :
    ¬ IsIsolatedActiveBlock (Finset.univ : Finset (Fin 4)) belowOneSubset block := by
  obtain ⟨atomLabel, hatom⟩ := hblockNonempty
  fin_cases atomLabel
  · exact not_isIsolatedActiveBlock_of_two_distinct_activeSubset hatom (Finset.mem_univ 0)
      (Finset.mem_univ 1) (by decide) (by decide) (by decide)
  · exact not_isIsolatedActiveBlock_of_two_distinct_activeSubset hatom (Finset.mem_univ 0)
      (Finset.mem_univ 2) (by decide) (by decide) (by decide)
  · exact not_isIsolatedActiveBlock_of_two_distinct_activeSubset hatom (Finset.mem_univ 1)
      (Finset.mem_univ 3) (by decide) (by decide) (by decide)
  · exact not_isIsolatedActiveBlock_of_two_distinct_activeSubset hatom (Finset.mem_univ 2)
      (Finset.mem_univ 3) (by decide) (by decide) (by decide)

/-- The witness's four active pairs are distinct, so its active image has card four. -/
theorem card_activeSubsetImage_belowOneSubset :
    ((Finset.univ : Finset (Fin 4)).image belowOneSubset).card = 4 := by decide

/-- **THE WALL, CERTIFIED.**  The shape left over after the `(6,3)` collapse — a
stationarity datum with `0 < value < 1` and at least THREE distinct active subsets —
is REALIZABLE inside the bundle, at `(4,2)`, by the shipped witness.

So the surviving alternative of `three_le_card_activeSubsetImage_sixThree` is not an
unfinished step of the argument above: no strengthening of this file, and no argument
that sees only the bundle together with that combinatorial invariant, can close it.
`Gtz.not_isArgmaxDominated_belowOneDesign` says what the witness DOES violate — the
argmax field — and `Gtz.one_le_value_of_isArgmaxDominated` says that once the argmax
field is attached the obligation is the interior case of GTZ itself.  That is where the
route ends, and it ends by obstruction rather than by exhaustion. -/
theorem exists_isQuadricStationaryData_three_le_card_activeSubsetImage_value_lt_one :
    ∃ (D : WeightedDesign 4 2) (value : ℝ) (multiplier : Matrix (Fin 2) (Fin 2) ℝ)
      (activeSubset : Fin 4 → Finset (Fin 4)) (activeWeight : Fin 4 → ℝ)
      (tightDir : Fin 4 → (Fin 2 → ℝ)),
      IsQuadricStationaryData D value multiplier (Finset.univ : Finset (Fin 4)) activeSubset
          activeWeight tightDir
        ∧ 0 < value ∧ value < 1
        ∧ 3 ≤ ((Finset.univ : Finset (Fin 4)).image activeSubset).card :=
  ⟨belowOneDesign, belowOneValue, belowOneMultiplierMatrix, belowOneSubset, belowOneMultiplier,
    belowOneTightDir, belowOneDesign_isQuadricStationaryData, belowOneValue_pos,
    belowOneValue_lt_one, by rw [card_activeSubsetImage_belowOneSubset]; norm_num⟩

end Gtz
