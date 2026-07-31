/-
# The Veronese barrier survives the dimension bound

`Gtz/Quantitative/SevenThreeMetricBound.lean` section 5 states the metric
frontier of the `(7,3)` equal-share stratum with the rank-one structure
forgotten.  `Gtz.AbstractMetricTripleBoundSevenThree` asks: must every `7 x 7`
positive semidefinite matrix with constant diagonal `2/3` and vanishing row sums
carry a triple of block mass at most `2/3`?  It really does imply the metric
bound (`Gtz.metricTripleBoundSevenThree_of_abstract`), and it is FALSE
(`Gtz.not_abstractMetricTripleBound_sevenThree`): the witness `(7/9) I - (1/9) J`
puts every triple at `4/3`, exactly twice the target.

That refutation leaves one escape open, and it is the obvious one.  The witness
`(7/9) I - (1/9) J` is `(7/9)` times the projection onto the all-ones complement,
so it has RANK SIX — while the object it is standing in for, the Gram of the
seven traceless parts `Y_c = u_c u_c^T - I/3`, lives in the FIVE-dimensional space
of traceless symmetric `3 x 3` matrices (`Gtz.finrank_symmetricTracelessSubmodule_atRankThree`)
and therefore has rank at most five.  A reader could reasonably hope that adding
`rank <= 5` — a constraint every real `Y`-Gram satisfies for free — rescues the
relaxation.

It does not.  This file closes that escape.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `AbstractMetricTripleBoundSevenThreeRankFive` — the shipped relaxation with the
  rank bound added, and
  `abstractMetricTripleBoundSevenThreeRankFive_of_abstract`, the one-line
  implication that makes it visibly the SHARPER statement.
* `rankFiveSpreadWitnessVector` and `rankFiveSpreadWitnessTable` — seven vectors
  of `R^5` and their exact integer Gram: one coordinate direction taken TWICE at
  height `20`, and five further vectors tilted against it to `-8` carrying a
  regular four-simplex in the remaining four coordinates.  The Gram is `400` on
  the diagonal and on the doubled pair, `-160` between the doubled direction and
  the simplex, `-20` inside the simplex; every row sums to zero.
* `not_abstractMetricTripleBoundSevenThreeRankFive` — normalised by `600` the
  witness has diagonal `2/3`, vanishing row sums, rank at most five and positive
  semidefiniteness by construction, and every triple carries block mass at least
  `13/15`, never the `2/3` the relaxation demands.

So the barrier is not an artefact of allowing rank six.  Any proof that some
triple of the uniform `(7,3)` stratum achieves the metric bound must consume the
rank-one (Veronese) structure of the atoms `u_c u_c^T` itself — positive
semidefiniteness, the constant diagonal, the vanishing row sums and the exact
dimension of the traceless chart together are not enough.

## NOT PROVED here

This is a NEGATIVE result about how the residue may be proved.  It advances
`Gtz.GtzWeightedHeavy 7 3` not at all; it forecloses a class of routes to it.
The ratio is weaker than the shipped barrier's (`13/10` of the target rather than
exactly `2`) and the hypothesis set is strictly stronger, which is the whole
point: the increment is the hypothesis, not the ratio.

Nothing here shows the rank-five witness is REALIZABLE as a `Y`-Gram — it is not,
and the shipped `Gtz.rank_hadamardSquareDirectionGram_le_six` plus
`Gtz.not_exists_design_with_uniform_edgeWeight_two_ninths` are the file that
handles realizability.

Provenance: scratch report 09 (`/tmp/gtz-wf/deepen-special/probe.lean`, namespace
`GtzSpecialFamilies`).  That file's Frobenius/traceless chart and its
`not_unboundedSpreadGate` are shipped already —
`Gtz.frobeniusInner`, `Gtz.veroneseTracelessPart`,
`Gtz.frobeniusNormSq_veroneseTracelessPart`,
`Gtz.frobeniusNormSq_tripleTracelessSum_eq_two_mul_tripleSigma` and
`Gtz.not_abstractMetricTripleBound_sevenThree` — and are not restated.  Its
rank-five witness, stated there over vectors rather than over Gram matrices, is
what survives; here it is transported into the shipped Gram vocabulary so the
strengthening is legible as one.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.SevenThreeMetricBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## The relaxation, with the dimension bound the traceless chart supplies -/

/-- **THE RANK-BOUNDED RELAXATION.**  `Gtz.AbstractMetricTripleBoundSevenThree`
with the one extra hypothesis every real `Y`-Gram satisfies: rank at most five,
the dimension of the traceless symmetric `3 x 3` matrices. -/
def AbstractMetricTripleBoundSevenThreeRankFive : Prop :=
  ∀ gramCandidate : Matrix (Fin 7) (Fin 7) ℝ, gramCandidate.PosSemidef →
    gramCandidate.rank ≤ 5 →
    (∀ atomIndex, gramCandidate atomIndex atomIndex = 2 / 3) →
    (∀ atomIndex, ∑ otherIndex, gramCandidate atomIndex otherIndex = 0) →
      ∃ tripleFirst tripleSecond tripleThird : Fin 7,
        tripleFirst ≠ tripleSecond ∧ tripleFirst ≠ tripleThird ∧ tripleSecond ≠ tripleThird ∧
          gramCandidate tripleFirst tripleFirst + gramCandidate tripleSecond tripleSecond
              + gramCandidate tripleThird tripleThird
            + 2 * gramCandidate tripleFirst tripleSecond
            + 2 * gramCandidate tripleFirst tripleThird
            + 2 * gramCandidate tripleSecond tripleThird ≤ 2 / 3

/-- The rank-bounded relaxation is WEAKER as a hypothesis, hence sharper to
refute: dropping the rank bound is all that separates it from the shipped one.
Refuting it therefore refutes `Gtz.AbstractMetricTripleBoundSevenThree` as
well. -/
theorem abstractMetricTripleBoundSevenThreeRankFive_of_abstract
    (habstract : AbstractMetricTripleBoundSevenThree) :
    AbstractMetricTripleBoundSevenThreeRankFive :=
  fun gramCandidate hposSemidef _hrank hdiagonal hrowSum =>
    habstract gramCandidate hposSemidef hdiagonal hrowSum

/-! ## The rank-five witness -/

private noncomputable def rankFiveWitnessTilt : ℝ := Real.sqrt 105

private noncomputable def rankFiveWitnessHeight : ℝ := Real.sqrt 21

private theorem rankFiveWitnessTilt_sq : rankFiveWitnessTilt ^ 2 = 105 := by
  rw [rankFiveWitnessTilt, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 105)]

private theorem rankFiveWitnessHeight_sq : rankFiveWitnessHeight ^ 2 = 21 := by
  rw [rankFiveWitnessHeight, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]

/-- **THE WITNESS.**  Seven vectors of `R^5` of common squared length `400`: the
first coordinate direction taken TWICE at height `20`, and five further vectors
tilted against it to `-8` carrying a regular four-simplex in the remaining four
coordinates.  Seven vectors in five dimensions, so their Gram has rank at most
five by construction. -/
noncomputable def rankFiveSpreadWitnessVector : Fin 7 → (Fin 5 → ℝ)
  | 0 => ![20, 0, 0, 0, 0]
  | 1 => ![20, 0, 0, 0, 0]
  | 2 => ![-8, rankFiveWitnessTilt, rankFiveWitnessTilt, rankFiveWitnessTilt,
      -rankFiveWitnessHeight]
  | 3 => ![-8, rankFiveWitnessTilt, -rankFiveWitnessTilt, -rankFiveWitnessTilt,
      -rankFiveWitnessHeight]
  | 4 => ![-8, -rankFiveWitnessTilt, rankFiveWitnessTilt, -rankFiveWitnessTilt,
      -rankFiveWitnessHeight]
  | 5 => ![-8, -rankFiveWitnessTilt, -rankFiveWitnessTilt, rankFiveWitnessTilt,
      -rankFiveWitnessHeight]
  | 6 => ![-8, 0, 0, 0, 4 * rankFiveWitnessHeight]

/-- The witness's Gram, exactly: `400` on the diagonal and on the doubled pair,
`-160` between the doubled direction and the simplex, `-20` inside the simplex.
Every row sums to zero, so the normalised Gram meets the shipped relaxation's
vanishing-row-sum hypothesis on the nose. -/
def rankFiveSpreadWitnessTable : Fin 7 → Fin 7 → ℤ :=
  ![![400, 400, -160, -160, -160, -160, -160],
    ![400, 400, -160, -160, -160, -160, -160],
    ![-160, -160, 400, -20, -20, -20, -20],
    ![-160, -160, -20, 400, -20, -20, -20],
    ![-160, -160, -20, -20, 400, -20, -20],
    ![-160, -160, -20, -20, -20, 400, -20],
    ![-160, -160, -20, -20, -20, -20, 400]]

private theorem dotProduct_fiveEntries (firstZero firstOne firstTwo firstThree firstFour
    secondZero secondOne secondTwo secondThree secondFour : ℝ) :
    (![firstZero, firstOne, firstTwo, firstThree, firstFour] : Fin 5 → ℝ) ⬝ᵥ
        ![secondZero, secondOne, secondTwo, secondThree, secondFour]
      = firstZero * secondZero + firstOne * secondOne + firstTwo * secondTwo
        + firstThree * secondThree + firstFour * secondFour := by
  simp [dotProduct, Fin.sum_univ_five]

set_option maxHeartbeats 1000000 in
/-- The witness realises the table. -/
theorem rankFiveSpreadWitnessVector_dotProduct (firstIndex secondIndex : Fin 7) :
    rankFiveSpreadWitnessVector firstIndex ⬝ᵥ rankFiveSpreadWitnessVector secondIndex
      = (rankFiveSpreadWitnessTable firstIndex secondIndex : ℝ) := by
  fin_cases firstIndex <;> fin_cases secondIndex <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      rankFiveSpreadWitnessVector, rankFiveSpreadWitnessTable, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, dotProduct_fiveEntries] <;>
    push_cast <;> ring_nf <;>
    simp only [rankFiveWitnessTilt_sq, rankFiveWitnessHeight_sq] <;> norm_num

theorem rankFiveSpreadWitnessTable_diagonal (atomIndex : Fin 7) :
    rankFiveSpreadWitnessTable atomIndex atomIndex = 400 := by
  revert atomIndex
  decide

theorem rankFiveSpreadWitnessTable_rowSum (atomIndex : Fin 7) :
    ∑ otherIndex : Fin 7, rankFiveSpreadWitnessTable atomIndex otherIndex = 0 := by
  rw [Fin.sum_univ_seven]
  revert atomIndex
  decide

/-- Every triple of the witness overshoots: the block mass of the unnormalised
Gram is at least `520`, never the `400` the relaxation demands. -/
theorem rankFiveSpreadWitnessTable_triple_lower (tripleFirst tripleSecond tripleThird : Fin 7)
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird) :
    520 ≤ 1200 + 2 * (rankFiveSpreadWitnessTable tripleFirst tripleSecond
      + rankFiveSpreadWitnessTable tripleFirst tripleThird
      + rankFiveSpreadWitnessTable tripleSecond tripleThird) := by
  revert tripleFirst tripleSecond tripleThird
  decide

/-! ## The normalised Gram -/

/-- The witness's rows, scaled so the Gram carries the diagonal `2/3` the shipped
relaxation demands.  Five rows and seven columns: the shape is what bounds the
rank. -/
noncomputable def rankFiveSpreadWitnessRows : Matrix (Fin 5) (Fin 7) ℝ :=
  Matrix.of fun coordIndex atomIndex =>
    rankFiveSpreadWitnessVector atomIndex coordIndex / Real.sqrt 600

/-- The normalised Gram of the rank-five witness. -/
noncomputable def rankFiveSpreadWitnessGram : Matrix (Fin 7) (Fin 7) ℝ :=
  rankFiveSpreadWitnessRowsᴴ * rankFiveSpreadWitnessRows

theorem rankFiveSpreadWitnessGram_apply (firstIndex secondIndex : Fin 7) :
    rankFiveSpreadWitnessGram firstIndex secondIndex
      = (rankFiveSpreadWitnessTable firstIndex secondIndex : ℝ) / 600 := by
  have hrootSquare : Real.sqrt 600 * Real.sqrt 600 = 600 :=
    Real.mul_self_sqrt (by norm_num)
  have hexpand : rankFiveSpreadWitnessGram firstIndex secondIndex
      = (∑ coordIndex : Fin 5, rankFiveSpreadWitnessVector firstIndex coordIndex
          * rankFiveSpreadWitnessVector secondIndex coordIndex) / 600 := by
    simp only [rankFiveSpreadWitnessGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
      rankFiveSpreadWitnessRows, Matrix.of_apply, star_trivial]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun coordIndex _ => ?_
    rw [div_mul_div_comm, hrootSquare]
  rw [hexpand, show (∑ coordIndex : Fin 5, rankFiveSpreadWitnessVector firstIndex coordIndex
      * rankFiveSpreadWitnessVector secondIndex coordIndex)
      = rankFiveSpreadWitnessVector firstIndex ⬝ᵥ rankFiveSpreadWitnessVector secondIndex from rfl,
    rankFiveSpreadWitnessVector_dotProduct]

theorem posSemidef_rankFiveSpreadWitnessGram : rankFiveSpreadWitnessGram.PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self rankFiveSpreadWitnessRows

/-- **THE RANK BOUND, BY CONSTRUCTION.**  Seven vectors in five dimensions. -/
theorem rank_rankFiveSpreadWitnessGram_le_five : rankFiveSpreadWitnessGram.rank ≤ 5 := by
  show (rankFiveSpreadWitnessRowsᴴ * rankFiveSpreadWitnessRows).rank ≤ 5
  refine le_trans (Matrix.rank_mul_le_left rankFiveSpreadWitnessRowsᴴ
    rankFiveSpreadWitnessRows) ?_
  simpa using Matrix.rank_le_card_width (rankFiveSpreadWitnessRowsᴴ)

theorem rankFiveSpreadWitnessGram_diagonal (atomIndex : Fin 7) :
    rankFiveSpreadWitnessGram atomIndex atomIndex = 2 / 3 := by
  rw [rankFiveSpreadWitnessGram_apply, rankFiveSpreadWitnessTable_diagonal atomIndex]
  norm_num

theorem sum_rankFiveSpreadWitnessGram_row (atomIndex : Fin 7) :
    ∑ otherIndex, rankFiveSpreadWitnessGram atomIndex otherIndex = 0 := by
  have hrowSum : ∑ otherIndex : Fin 7,
      ((rankFiveSpreadWitnessTable atomIndex otherIndex : ℤ) : ℝ) = 0 := by
    exact_mod_cast rankFiveSpreadWitnessTable_rowSum atomIndex
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) =>
      rankFiveSpreadWitnessGram_apply atomIndex otherIndex,
    ← Finset.sum_div, hrowSum]
  norm_num

/-- Every triple of the normalised witness carries block mass at least `13/15`,
comfortably above the `2/3` the relaxation demands. -/
theorem rankFiveSpreadWitnessGram_triple_lower {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird) :
    13 / 15 ≤ rankFiveSpreadWitnessGram tripleFirst tripleFirst
        + rankFiveSpreadWitnessGram tripleSecond tripleSecond
        + rankFiveSpreadWitnessGram tripleThird tripleThird
      + 2 * rankFiveSpreadWitnessGram tripleFirst tripleSecond
      + 2 * rankFiveSpreadWitnessGram tripleFirst tripleThird
      + 2 * rankFiveSpreadWitnessGram tripleSecond tripleThird := by
  have hcast : (520 : ℝ) ≤ 1200
      + 2 * (((rankFiveSpreadWitnessTable tripleFirst tripleSecond : ℤ) : ℝ)
        + ((rankFiveSpreadWitnessTable tripleFirst tripleThird : ℤ) : ℝ)
        + ((rankFiveSpreadWitnessTable tripleSecond tripleThird : ℤ) : ℝ)) := by
    exact_mod_cast rankFiveSpreadWitnessTable_triple_lower tripleFirst tripleSecond tripleThird
      hfirstSecond hfirstThird hsecondThird
  rw [rankFiveSpreadWitnessGram_diagonal tripleFirst, rankFiveSpreadWitnessGram_diagonal
    tripleSecond, rankFiveSpreadWitnessGram_diagonal tripleThird,
    rankFiveSpreadWitnessGram_apply, rankFiveSpreadWitnessGram_apply,
    rankFiveSpreadWitnessGram_apply]
  linarith

/-- **THE SHARP NO-GO.**  Even WITH the five-dimensional bound the relaxed metric
statement is false.  The shipped `Gtz.not_abstractMetricTripleBound_sevenThree`
refutes the unbounded version with a rank-SIX witness, leaving open whether the
dimension of the traceless chart rescues it; it does not.  Any proof of the
metric bound on the uniform `(7,3)` stratum must consume the rank-one structure
of the atoms and not merely the metric data of their traceless parts. -/
theorem not_abstractMetricTripleBoundSevenThreeRankFive :
    ¬ AbstractMetricTripleBoundSevenThreeRankFive := by
  intro hgate
  obtain ⟨tripleFirst, tripleSecond, tripleThird, hfirstSecond, hfirstThird, hsecondThird,
    hblock⟩ := hgate rankFiveSpreadWitnessGram posSemidef_rankFiveSpreadWitnessGram
      rank_rankFiveSpreadWitnessGram_le_five rankFiveSpreadWitnessGram_diagonal
      sum_rankFiveSpreadWitnessGram_row
  have hlarge := rankFiveSpreadWitnessGram_triple_lower hfirstSecond hfirstThird hsecondThird
  linarith

end Gtz
