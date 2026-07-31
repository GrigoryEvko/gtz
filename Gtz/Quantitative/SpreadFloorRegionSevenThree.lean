/-
# The floored spread region at `(7,3)`: the spread ceiling is the Welch bound, the
# ceiling forces equiangularity, and the light gate is OBSTRUCTED — not forced — by
# spread

`Gtz.Quantitative.FlooredSpreadRegion` fixes the floored spread region at size
six and names the qualitative hypothesis `Gtz.FlooredSpreadCovering`.  Its region
predicates `Gtz.HasSpreadAtLeast`, `Gtz.HasWeightFloor`,
`Gtz.IsFlooredSpreadDesign` are ALREADY size-generic (they take
`WeightedDesign m 3`); only the covering sentence is pinned to size six.  This
file therefore re-defines nothing from that layer.  It adds the size-generic
covering, the quantitative boundary of the region at EVERY size, the `(7,3)`
non-vacuity witness, and the exact reason the route this lane was asked to try
does not exist.

THERE IS NO CERTIFICATE HERE.  Rank three is not proved and nothing below claims
it is.  Every constant below is an exact rational; no floating-point computation
enters any statement or any proof.

## PROVED here

**The spread parameter IS an edge-weight cap.**
`hasSpreadAtLeast_iff_edgeWeight_le` — on a design with all leverages positive,
`HasSpreadAtLeast D spread` holds exactly when every off-diagonal edge weight
`w_cd = gamma_cd^2` is at most `1 - spread`.  So the region's spread generator and
the `(7,3)` gate layer of `Gtz.Quantitative.SevenThreeCapsGates`, which is written
entirely in `Gtz.edgeWeight`, speak the same language, with no loss.

**THE SPREAD CEILING IS THE WELCH BOUND, at every size, with no share
hypothesis.**  `size_sub_three_le_three_mul_size_sub_one_mul_one_sub_spread` —
any `(m,3)` design with positive leverages in the region satisfies
`m - 3 <= 3 (m - 1) (1 - spread)`, i.e. `1 - spread >= (m - 3)/(3(m-1))`, the
Welch/Levenshtein coherence bound `(m-k)/(k(m-1))` at `k = 3`.  The proof is the
row law `Gtz.atomShare_add_sum_erase_atomShare_mul_sq_directionGram` evaluated at
an atom of minimum share, which `Gtz.exists_atomShare_le_rank_div_size` supplies;
uniform share is NOT assumed and neither are uniform weights or leverages.

Three specialisations, two of them attained:

  `spread_le_eight_ninths_of_hasSpreadAtLeast_fourThree` — at size four the ceiling
    is `8/9`, ATTAINED by the regular tetrahedron
    (`tetraDesign_hasSpreadAtLeast_eight_ninths`: squared pairing `1` against
    leverage `3`, so squared cosine exactly `1/9`).  This is a calibration anchor at
    a size and against a design built for an unrelated purpose, and it is the
    strongest available check that the general constant is not off by a factor.
  `spread_le_four_fifths_of_hasSpreadAtLeast_sixThree` — at size six the ceiling
    is `4/5`, ATTAINED by `Gtz.icosaDesign` (`Gtz.icosaDesign_hasSpreadAtLeast`), and
    `not_forall_spread_le_of_lt_four_fifths_sixThree` turns that attainment into the
    statement that the constant cannot be improved.
    This CLOSES a gap the size-six layer flagged as open: the header of
    `Gtz.Quantitative.SpreadCertificateSixThree` records "The window `(4/5, 1]` is
    guarded by NEITHER: the region is measured empty well before `1`, since six
    real lines in three-space cannot beat the icosahedron's `4/5`, but nothing here
    proves that."  `flooredSpreadCoveringAtSize_six_of_four_fifths_lt_spread` now
    proves it — the whole window is empty and the covering there is vacuous.
  `spread_le_seven_ninths_of_hasSpreadAtLeast_sevenThree` — at size seven the
    ceiling is `7/9`.  Whether it is ATTAINED is NOT settled here.  What IS proved
    is that attainment ON THE UNIFORM-SHARE STRATUM forces every off-diagonal edge
    weight to be exactly `2/9`, i.e. a real `(7,3)` equiangular tight frame; this
    repository constructs no such frame and proves no non-existence.  The step from
    general attainment down to the uniform-share case — the minimum share must sit
    at `3/7`, which forces every share there — is a one-line consequence of the
    proof of the general ceiling but is NOT formalised here.

**THE CEILING FORCES EQUIANGULARITY.**
`edgeWeight_eq_two_ninths_of_hasSpreadAtLeast_seven_ninths` — a `(7,3)`
uniform-share design at the extreme spread `7/9` has EVERY off-diagonal edge
weight exactly `2/9`.  Each vertex must spend exactly `4/3` across its six edges
(`Gtz.sum_erase_edgeWeight_eq_of_atomShare_eq`) and no edge may exceed
`6 * (2/9) = 4/3` worth of cap, so the budget is saturated termwise.  The region
at the ceiling is therefore rigid — but whether it is INHABITED is open, and the
rigidity is what makes that doubtful: it demands seven EQUIANGULAR real lines in
three-space at squared cosine `2/9`.  If no such configuration exists then this
theorem and `not_hasLightTripleSevenThree_of_hasSpreadAtLeast_seven_ninths` both
have an unsatisfiable hypothesis on the uniform-share stratum.  Read "rigid" as a
statement about the shape of the constraint, never as a claim that the stratum at
the ceiling is nonempty.

**THE LANE'S PIGEONHOLE ROUTE IS REFUTED, with the exact inversion constant.**
The brief that produced this file proposed: "A spread hypothesis is exactly a cap
on squared cosine, i.e. on edge weight — so a sufficiently strong spread should
force the light gate to fire on SOME triple by pigeonhole."  That is BACKWARDS.
At `(7,3)` uniform share the vertex budget is a fixed `4/3`, so capping every
edge does not make edges small, it makes them UNIFORM — and the light gate of
`Gtz.dominates_triple_of_lightEdges_sevenThree` needs three edges at most `1/9`,
strictly below the forced average `2/9`.  Quantitatively:

  `spread_le_thirteen_eighteenths_of_two_lightEdges_sevenThree` — if a single atom
    carries TWO incident edges of weight at most `1/9`, then `spread <= 13/18`.
    (Its four remaining edges must carry `4/3 - 2/9 = 10/9`, so one of them
    reaches `5/18` and the cap `1 - spread` cannot be below `5/18`.)
  `not_hasLightTripleSevenThree_of_thirteen_eighteenths_lt_spread` — hence for
    `spread > 13/18` NO triple is light: the gate fires nowhere.
  `not_hasLightTripleSevenThree_of_hasSpreadAtLeast_seven_ninths` — at the ceiling
    itself the reason is exact rather than asymptotic: every edge is `2/9 > 1/9`.
  `edgeWeight_lt_four_ninths_of_five_ninths_lt_spread` — and the HEAVY gate dies
    first, at `5/9`, for the same reason read the other way: a cap below `4/9`
    forbids a heavy edge outright.
  `gateLayerFenced_of_thirteen_eighteenths_lt_spread` — so on the strip
    `(13/18, 7/9]` BOTH exact per-triple gates fire nowhere and every edge is
    confined to the middle band `(1/9, 4/9)`.  THIS IS THE WALL, NAMED: it is the
    exact strip of the feasible spread window on which raising the spread buys
    nothing from the gate layer of `Gtz.Quantitative.SevenThreeCapsGates`.

So the answer to "find the exact spread threshold at which the light gate is
guaranteed on some triple" is: THERE IS NO SUCH THRESHOLD.  The feasible spread
window at `(7,3)` is `[0, 7/9]` (with no share hypothesis at all), on the
uniform-share stratum the light gate is available only on `[0, 13/18]`, and raising
the spread monotonically destroys it.  By the witness below at
`spread = 2/3 < 13/18` the surviving window is not empty.  `13/18` is exactly what
the vertex budget yields; whether some design ATTAINS it — two light edges at one
atom with every other edge at exactly `5/18` — is NOT settled here, and the theorem
does not need it.

The structural reason is one line, and
`sum_sum_erase_edgeWeight_eq_twentyEight_thirds_of_uniformShare_sevenThree` records
it: at `(7,3)` uniform share the forty-two ordered off-diagonal edge weights total
exactly `28/3`, so their MEAN is exactly `2/9` — the Welch bound is the mean, the
ceiling asks no edge to exceed the mean (hence forces equality everywhere), and the
light gate asks three edges to sit at `1/9`, HALF the mean.  A cap cannot produce
values below the mean.

**WHAT THE LIGHT GATE DOES BUY, unconditionally.**
`symmetricLegs_nonneg_of_hasLightTripleSevenThree` — on the `(7,3)` equal-share
stratum (`atomShare = 3/7` and every leverage `3`), owning a light triple gives
both `S_3`-invariant legs of `Gtz.Quantitative.PositivstellensatzRankThree`
nonnegative at that triple, which is exactly the covering conclusion.  This is a
genuine unconditional covering theorem on a region that is NOT empty:
`sevenThreeBasisTetrapodDesign_hasLightTripleSevenThree` puts the verified `(7,3)`
witness in it.

**NON-VACUITY AT SEVEN POINTS, at exact parameters.**
`Gtz.sevenThreeBasisTetrapodDesign` (three axis atoms at `sqrt 3` times the
standard basis, four even-sign tetrapod atoms, weight `1/7`) has exactly three
distinct edge weights — `0` on the three basis pairs, `1/3` on the twelve mixed
pairs, `1/9` on the six tetrapod pairs — so:

  `sevenThreeBasisTetrapodDesign_hasSpreadAtLeast_two_thirds` — its spread is at
    least `2/3`, and
    `sevenThreeBasisTetrapodDesign_not_hasSpreadAtLeast_of_two_thirds_lt`
    shows `2/3` is EXACT (the mixed pair `(0,3)` has squared pairing exactly `3`).
  `sevenThreeBasisTetrapodDesign_hasWeightFloor_one_seventh` — its floor is `1/7`,
    the extreme, and by `weight_eq_inv_size_of_hasWeightFloor_inv_size` the
    extreme floor PINS the weights: `HasWeightFloor D (1/m)` forces
    `D.weight = 1/m` at every atom.  The floor parameter is rigid at its top end
    exactly as the spread parameter is.
  `sevenThreeBasisTetrapodDesign_isFlooredSpreadDesign` — the `(7,3)` region is
    inhabited at `(spread, floor) = (2/3, 1/7)`, and `2/3 < 13/18 < 7/9`, so the
    witness sits strictly inside the light-gate-available window.
  `sevenThreeBasisTetrapodDesign_hasLightTripleSevenThree` — the tetrapod triple
    `{3,4,5}` has all three edge weights exactly `1/9`, the gate boundary, so the
    covering conclusion is discharged AT the witness.  (The domination itself was
    already landed as `Gtz.dominates_tetrapodTriple_sevenThreeBasisTetrapodDesign`
    through the seven-clause slack criterion; what is new here is that the LANE'S
    gate reaches the same conclusion, so the route is not merely nonvacuous but
    exercised.)

**THE REGION EXCISES THE `(7,3)` TIE.**
`splitSevenDesign_not_hasSpreadAtLeast` — `Gtz.splitSevenDesign` carries duplicated
atoms (`Gtz.splitSevenDirection` is `![0,1,2,3,0,1,2]`, so atoms `0` and `4` are
the same vector), and a duplicated pair has squared cosine exactly `1`, so no
positive spread tolerates it.  This is the seven-point twin of
`Gtz.splitTetraDesign_not_hasSpreadAtLeast`.

DO NOT STRENGTHEN ANY OF THIS TO "ties carry parallel pairs".  That sentence is
`Gtz.HingeHoldsAtSize`, OPEN at sizes six and seven and PROVED FALSE at `(5,3)` by
`Gtz.not_hingeHoldsAtSize_five_three`.  What is shipped here is one witness on each
side, never the universal claim.

## HYPOTHESIS (stated, NOT proved)

`FlooredSpreadCoveringAtSize size spread floor` — the size-generic covering, tied
to the existing size-six sentence by `flooredSpreadCovering_iff_flooredSpreadCoveringAtSize_six`
(which is `Iff.rfl`: the two are the same proposition at size six, so nothing is
duplicated and nothing is lost).  It is proved here only where the region is
EMPTY, i.e. above the Welch ceiling, and those instances are labelled vacuous in
their own docstrings.

## NOT PROVED here

* `FlooredSpreadCoveringAtSize 7 spread floor` at any spread below `7/9`.  The
  light-gate route covers only designs owning a light triple; nothing here shows
  every region design owns one, and nothing here should be read as suggesting the
  spread parameter could deliver it — see the refutation above.
* Whether the `(7,3)` spread ceiling `7/9` is attained.  Attainment ON THE
  UNIFORM-SHARE STRATUM forces every one of the twenty-one edge weights to equal
  `2/9` exactly (the rigidity theorem above), i.e. a real `(7,3)` equiangular tight
  frame.  No such frame is built here and no non-existence proof is given here
  either.  Nor is the reduction of general attainment to the uniform-share case
  formalised, though it follows from the ceiling proof: equality throughout forces
  the minimum share to `3/7`, and shares summing to `3` over seven atoms then leave
  no other value.
* Whether the window `(13/18, 7/9]` — spread feasible but light gate dead — is
  inhabited.  If it is empty the refutation is a statement about a vacuous strip;
  if it is not, it is a live obstruction.  Either way the inequality
  `spread_le_thirteen_eighteenths_of_two_lightEdges_sevenThree` is unconditional
  and needs no such information: it says a light triple COSTS spread, and that is
  the content.

## CITED (proved elsewhere in this repository, used below)

`WeightedDesign`, `leverageOf`, `Dominates` (`Gtz.Core.Basic`);
`atomShare`, `sum_atomShare_eq_rank`, `exists_atomShare_le_rank_div_size`
(`Gtz.Reduction.BranchTransferConstants`); `directionGram`,
`directionGram_eq_scaled_atomPairing`,
`atomShare_add_sum_erase_atomShare_mul_sq_directionGram`
(`Gtz.Design.FrameConservation`); `edgeWeight`, `edgeWeight_comm`,
`sum_erase_edgeWeight_eq_of_atomShare_eq` (`Gtz.Quantitative.WeightProductFloor`);
`leverageOf_pos_of_atomShare_pos` (`Gtz.Quantitative.MirrorLaw`); `AllHeavy`
(`Gtz.Reduction.Reductions`); `heavyExcess`, `atomPairing`,
`discriminantMinorSum`, `discriminantTie` (`Gtz.Quantitative.DiscriminantSystem`);
`dominates_triple_iff_symmetricLegs`, `SymmetricCovering`
(`Gtz.Quantitative.PositivstellensatzRankThree`); `tetraAtom`, `tetraDesign`,
`tetraAtom_dot_sq_of_ne` (`Gtz.Design.StressCertificate`); `tetraDesign_leverage`
(`Gtz.Quantitative.DiscriminantSystem`); `icosaDesign`, `icosaDesign_allHeavy`,
`icosaDesign_hasSpreadAtLeast` (`Gtz.Quantitative.RealnessEngine` and
`Gtz.Quantitative.FlooredSpreadRegion`); `HasSpreadAtLeast`,
`HasWeightFloor`, `IsFlooredSpreadDesign`, `isFlooredSpreadDesign_mono`,
`FlooredSpreadCovering`, `leverageOf_nonneg`
(`Gtz.Quantitative.FlooredSpreadRegion`);
`dominates_triple_of_lightEdges_sevenThree`
(`Gtz.Quantitative.SevenThreeCapsGates`); `sevenThreeBasisTetrapodDesign` and its
Gram pattern, `leverageOf_sevenThreeBasisTetrapodDesign`,
`atomShare_sevenThreeBasisTetrapodDesign`, `allHeavy_sevenThreeBasisTetrapodDesign`,
`edgeWeight_sevenThreeBasisTetrapodDesign_zero_three`,
`dominates_tetrapodTriple_sevenThreeBasisTetrapodDesign`
(`Gtz.Quantitative.SevenThreeInvolution`); `splitSevenDesign`,
`splitSevenDirection`, `splitSevenDesign_leverage`,
`splitSevenDesign_atomPairing_of_sameDirection`
(`Gtz.Quantitative.DecisionAtlasSevenThree`).
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.Reduction.BranchTransferConstants
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.SevenThreeCapsGates
import Gtz.Quantitative.SevenThreeInvolution
import Gtz.Quantitative.DecisionAtlasSevenThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The bridge: the spread parameter IS an edge-weight cap

`HasSpreadAtLeast` is written in the RAW coordinates — squared `atomPairing`
against the product of the two leverages — precisely so that it carries no
division.  The gate layer at `(7,3)` is written in `edgeWeight`, the squared
DIRECTION correlation.  The two are the same constraint. -/

/-- The edge weight times the leverage product is the squared raw pairing.  Stated
multiplicatively, so no division appears and the identity is a ring fact once the
two square roots are discharged. -/
theorem edgeWeight_mul_leverageProduct_eq_atomPairing_sq (design : WeightedDesign m 3)
    {atomFirst atomSecond : Fin m} (hfirst : 0 < leverageOf (design.atom atomFirst))
    (hsecond : 0 < leverageOf (design.atom atomSecond)) :
    edgeWeight design atomFirst atomSecond
        * (leverageOf (design.atom atomFirst) * leverageOf (design.atom atomSecond))
      = atomPairing design atomFirst atomSecond ^ 2 := by
  have hfirstNe : leverageOf (design.atom atomFirst) ≠ 0 := hfirst.ne'
  have hsecondNe : leverageOf (design.atom atomSecond) ≠ 0 := hsecond.ne'
  rw [edgeWeight, directionGram_eq_scaled_atomPairing, atomPairing, mul_pow, mul_pow,
    inv_pow, inv_pow, Real.sq_sqrt hfirst.le, Real.sq_sqrt hsecond.le]
  field_simp

/-- **The spread bound is an edge cap.**  Every off-diagonal edge weight of a
design in the region is at most `1 - spread`. -/
theorem edgeWeight_le_of_hasSpreadAtLeast (design : WeightedDesign m 3) {spread : ℝ}
    (hspread : HasSpreadAtLeast design spread)
    (hleveragePos : ∀ atomIndex : Fin m, 0 < leverageOf (design.atom atomIndex))
    {atomFirst atomSecond : Fin m} (hne : atomFirst ≠ atomSecond) :
    edgeWeight design atomFirst atomSecond ≤ 1 - spread := by
  have hproductPos : 0 < leverageOf (design.atom atomFirst) * leverageOf (design.atom atomSecond) :=
    mul_pos (hleveragePos atomFirst) (hleveragePos atomSecond)
  have hraw := hspread atomFirst atomSecond hne
  have hidentity := edgeWeight_mul_leverageProduct_eq_atomPairing_sq design
    (hleveragePos atomFirst) (hleveragePos atomSecond)
  refine le_of_mul_le_mul_right ?_ hproductPos
  rw [hidentity]
  exact hraw

/-- The converse of `edgeWeight_le_of_hasSpreadAtLeast`: an edge cap is a spread
bound. -/
theorem hasSpreadAtLeast_of_edgeWeight_le (design : WeightedDesign m 3) {spread : ℝ}
    (hleveragePos : ∀ atomIndex : Fin m, 0 < leverageOf (design.atom atomIndex))
    (hedgeCap : ∀ atomFirst atomSecond : Fin m, atomFirst ≠ atomSecond →
      edgeWeight design atomFirst atomSecond ≤ 1 - spread) :
    HasSpreadAtLeast design spread := by
  intro atomFirst atomSecond hne
  have hproductNonneg :
      0 ≤ leverageOf (design.atom atomFirst) * leverageOf (design.atom atomSecond) :=
    (mul_pos (hleveragePos atomFirst) (hleveragePos atomSecond)).le
  have hidentity := edgeWeight_mul_leverageProduct_eq_atomPairing_sq design
    (hleveragePos atomFirst) (hleveragePos atomSecond)
  rw [← hidentity]
  exact mul_le_mul_of_nonneg_right (hedgeCap atomFirst atomSecond hne) hproductNonneg

/-- **The two spellings of the spread generator agree.** -/
theorem hasSpreadAtLeast_iff_edgeWeight_le (design : WeightedDesign m 3) {spread : ℝ}
    (hleveragePos : ∀ atomIndex : Fin m, 0 < leverageOf (design.atom atomIndex)) :
    HasSpreadAtLeast design spread ↔ ∀ atomFirst atomSecond : Fin m, atomFirst ≠ atomSecond →
      edgeWeight design atomFirst atomSecond ≤ 1 - spread :=
  ⟨fun hspread _ _ hne => edgeWeight_le_of_hasSpreadAtLeast design hspread hleveragePos hne,
    fun hedgeCap => hasSpreadAtLeast_of_edgeWeight_le design hleveragePos hedgeCap⟩

/-! ## 2. The spread ceiling is the Welch bound

The row law `s_a + sum_{d /= a} s_d gamma_ad^2 = 1` says an atom's share plus its
weighted squared correlations to everything else is exactly one.  Capping every
squared correlation at `cap` and evaluating at an atom of MINIMUM share — whose
share is at most `k/m` — gives the Welch coherence bound.  No uniformity of any
kind is assumed. -/

/-- Every atom share is nonnegative: a positive weight times a sum of squares. -/
theorem atomShare_nonneg (design : WeightedDesign m 3) (atomIndex : Fin m) :
    0 ≤ atomShare design atomIndex :=
  mul_nonneg (design.weight_pos atomIndex).le (leverageOf_nonneg _)

/-- The shares off one atom total `3 - s_a`, because all shares total the rank. -/
theorem sum_erase_atomShare_eq (design : WeightedDesign m 3) (atomIndex : Fin m) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare design otherIndex
      = 3 - atomShare design atomIndex := by
  have htotal := sum_atomShare_eq_rank design
  have hsplit := Finset.sum_erase_add Finset.univ (atomShare design) (Finset.mem_univ atomIndex)
  have hcast : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [hcast] at htotal
  linarith [hsplit, htotal]

/-- **The row law under an edge cap.**  At every atom, `1 - s_a <= cap (3 - s_a)`. -/
theorem one_sub_atomShare_le_edgeCap_mul_three_sub_atomShare (design : WeightedDesign m 3)
    {edgeCap : ℝ} (hleveragePos : ∀ atomIndex : Fin m, 0 < leverageOf (design.atom atomIndex))
    (hedgeCap : ∀ atomFirst atomSecond : Fin m, atomFirst ≠ atomSecond →
      edgeWeight design atomFirst atomSecond ≤ edgeCap)
    (atomIndex : Fin m) :
    1 - atomShare design atomIndex ≤ edgeCap * (3 - atomShare design atomIndex) := by
  have hrow := atomShare_add_sum_erase_atomShare_mul_sq_directionGram design
    (hleveragePos atomIndex)
  have hbound : ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        atomShare design otherIndex * directionGram design atomIndex otherIndex ^ 2
      ≤ ∑ otherIndex ∈ Finset.univ.erase atomIndex, atomShare design otherIndex * edgeCap := by
    refine Finset.sum_le_sum fun otherIndex hmem => ?_
    refine mul_le_mul_of_nonneg_left ?_ (atomShare_nonneg design otherIndex)
    exact hedgeCap atomIndex otherIndex (Finset.ne_of_mem_erase hmem).symm
  rw [← Finset.sum_mul, sum_erase_atomShare_eq design atomIndex] at hbound
  linarith [hrow, hbound]

/-- **THE SPREAD CEILING IS THE WELCH BOUND.**  Any `(m,3)` design with positive
leverages whose pairwise squared sines are at least `spread` satisfies
`m - 3 <= 3 (m - 1) (1 - spread)`, i.e. `1 - spread >= (m - 3)/(3(m-1))` — the
Welch/Levenshtein coherence bound `(m - k)/(k(m-1))` at `k = 3`.  Stated
division-free.

Neither uniform share nor uniform weights nor uniform leverages are assumed: the
argument evaluates the row law at an atom of MINIMUM share, which
`Gtz.exists_atomShare_le_rank_div_size` produces at every design. -/
theorem size_sub_three_le_three_mul_size_sub_one_mul_one_sub_spread
    (design : WeightedDesign m 3) {spread : ℝ} (hsize : 2 ≤ m)
    (hleveragePos : ∀ atomIndex : Fin m, 0 < leverageOf (design.atom atomIndex))
    (hspread : HasSpreadAtLeast design spread) :
    (m : ℝ) - 3 ≤ 3 * ((m : ℝ) - 1) * (1 - spread) := by
  obtain ⟨minimalAtom, hshareLe⟩ := exists_atomShare_le_rank_div_size design (by omega)
  have hsizeReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hsize
  have hsizePos : (0 : ℝ) < (m : ℝ) := by linarith
  have hshareNonneg : 0 ≤ atomShare design minimalAtom := atomShare_nonneg design minimalAtom
  have hsizeMulShare : (m : ℝ) * atomShare design minimalAtom ≤ 3 := by
    have hcast : ((3 : ℕ) : ℝ) / (m : ℝ) = 3 / (m : ℝ) := by norm_num
    rw [hcast] at hshareLe
    have hstep := mul_le_mul_of_nonneg_left hshareLe hsizePos.le
    have hcancel : (m : ℝ) * (3 / (m : ℝ)) = 3 := by field_simp
    linarith [hstep, hcancel]
  have hrow := one_sub_atomShare_le_edgeCap_mul_three_sub_atomShare design hleveragePos
    (fun atomFirst atomSecond hne =>
      edgeWeight_le_of_hasSpreadAtLeast design hspread hleveragePos hne) minimalAtom
  have hthreeSubShare : (0 : ℝ) < 3 - atomShare design minimalAtom := by
    nlinarith [hsizeMulShare, hsizeReal, hshareNonneg,
      mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2) hshareNonneg]
  have hfactorPos : (0 : ℝ) < 3 * ((m : ℝ) - 1) := by linarith
  have hscaled : 3 * ((m : ℝ) - 1) * (1 - atomShare design minimalAtom)
      ≤ 3 * ((m : ℝ) - 1) * ((1 - spread) * (3 - atomShare design minimalAtom)) :=
    mul_le_mul_of_nonneg_left hrow hfactorPos.le
  have hshift : ((m : ℝ) - 3) * (3 - atomShare design minimalAtom)
      ≤ 3 * ((m : ℝ) - 1) * (1 - atomShare design minimalAtom) := by
    nlinarith [hsizeMulShare]
  refine le_of_mul_le_mul_right ?_ hthreeSubShare
  nlinarith [hscaled, hshift]

/-- **At `(6,3)` the spread ceiling is exactly `4/5`**, and `Gtz.icosaDesign`
attains it (`Gtz.icosaDesign_hasSpreadAtLeast`).  Together those two statements
close the window `(4/5, 1]` that the header of
`Gtz.Quantitative.SpreadCertificateSixThree` records as guarded by neither of its
two boundary theorems. -/
theorem spread_le_four_fifths_of_hasSpreadAtLeast_sixThree (design : WeightedDesign 6 3)
    {spread : ℝ} (hleveragePos : ∀ atomIndex : Fin 6, 0 < leverageOf (design.atom atomIndex))
    (hspread : HasSpreadAtLeast design spread) :
    spread ≤ 4 / 5 := by
  have hceiling := size_sub_three_le_three_mul_size_sub_one_mul_one_sub_spread design
    (by norm_num) hleveragePos hspread
  norm_num at hceiling
  linarith

/-- **At `(7,3)` the spread ceiling is `7/9`.**  Whether it is attained is not
settled here.  Attainment on the uniform-share stratum forces every off-diagonal
edge weight to be exactly `2/9`
(`edgeWeight_eq_two_ninths_of_hasSpreadAtLeast_seven_ninths`), i.e. a real `(7,3)`
equiangular tight frame, and this repository constructs none and refutes none. -/
theorem spread_le_seven_ninths_of_hasSpreadAtLeast_sevenThree (design : WeightedDesign 7 3)
    {spread : ℝ} (hleveragePos : ∀ atomIndex : Fin 7, 0 < leverageOf (design.atom atomIndex))
    (hspread : HasSpreadAtLeast design spread) :
    spread ≤ 7 / 9 := by
  have hceiling := size_sub_three_le_three_mul_size_sub_one_mul_one_sub_spread design
    (by norm_num) hleveragePos hspread
  norm_num at hceiling
  linarith

/-- All-heaviness supplies the positivity the ceiling needs. -/
theorem leveragePos_of_allHeavy {design : WeightedDesign m 3} (hheavy : AllHeavy design)
    (atomIndex : Fin m) : 0 < leverageOf (design.atom atomIndex) :=
  lt_trans zero_lt_one (hheavy atomIndex)

/-- **CALIBRATION AT `(4,3)`.**  The general ceiling reads `spread <= 8/9` at size
four, and the Welch bound `(m-k)/(k(m-1)) = 1/9` there is the regular tetrahedron's
exact squared cosine, so the tetrahedron attains it
(`tetraDesign_hasSpreadAtLeast_eight_ninths`).  A second attained instance of the
same constant, at a different size and against a design built for an unrelated
purpose — the strongest available check that the bound is not off by a factor. -/
theorem spread_le_eight_ninths_of_hasSpreadAtLeast_fourThree (design : WeightedDesign 4 3)
    {spread : ℝ} (hleveragePos : ∀ atomIndex : Fin 4, 0 < leverageOf (design.atom atomIndex))
    (hspread : HasSpreadAtLeast design spread) :
    spread ≤ 8 / 9 := by
  have hceiling := size_sub_three_le_three_mul_size_sub_one_mul_one_sub_spread design
    (by norm_num) hleveragePos hspread
  norm_num at hceiling
  linarith

/-- The regular tetrahedron sits at exactly the `(4,3)` ceiling: distinct vertices
have squared pairing `1` against leverage `3` each, so squared cosine `1/9` and
squared sine `8/9`. -/
theorem tetraDesign_hasSpreadAtLeast_eight_ninths : HasSpreadAtLeast tetraDesign (8 / 9) := by
  intro atomFirst atomSecond hne
  rw [atomPairing, tetraDesign_leverage, tetraDesign_leverage,
    show tetraDesign.atom atomFirst ⬝ᵥ tetraDesign.atom atomSecond
      = tetraAtom atomFirst ⬝ᵥ tetraAtom atomSecond from rfl, tetraAtom_dot_sq_of_ne hne]
  norm_num

/-- **THE `(6,3)` CEILING CONSTANT CANNOT BE IMPROVED.**  No bound strictly below
`4/5` holds for every `(6,3)` region design, because `Gtz.icosaDesign` sits at
exactly `4/5`.  So `spread_le_four_fifths_of_hasSpreadAtLeast_sixThree` is sharp,
and the size-six Welch ceiling is attained.

The `(7,3)` analogue is NOT available: this repository constructs no real `(7,3)`
equiangular tight frame, so `7/9` is proved as a ceiling and left unproved as an
attained value. -/
theorem not_forall_spread_le_of_lt_four_fifths_sixThree {bound : ℝ} (hbound : bound < 4 / 5) :
    ¬ ∀ design : WeightedDesign 6 3, ∀ spread : ℝ,
        (∀ atomIndex : Fin 6, 0 < leverageOf (design.atom atomIndex)) →
        HasSpreadAtLeast design spread → spread ≤ bound := by
  intro hforall
  have hicosa := hforall icosaDesign (4 / 5) (leveragePos_of_allHeavy icosaDesign_allHeavy)
    icosaDesign_hasSpreadAtLeast
  linarith

/-- Above the `(6,3)` Welch ceiling the region is EMPTY. -/
theorem not_isFlooredSpreadDesign_sixThree_of_four_fifths_lt_spread
    (design : WeightedDesign 6 3) {spread weightFloor : ℝ} (hspreadGt : 4 / 5 < spread) :
    ¬ IsFlooredSpreadDesign design spread weightFloor := by
  intro hregion
  have hceiling := spread_le_four_fifths_of_hasSpreadAtLeast_sixThree design
    (leveragePos_of_allHeavy hregion.1) hregion.2.1
  linarith

/-- Above the `(7,3)` Welch ceiling the region is EMPTY. -/
theorem not_isFlooredSpreadDesign_sevenThree_of_seven_ninths_lt_spread
    (design : WeightedDesign 7 3) {spread weightFloor : ℝ} (hspreadGt : 7 / 9 < spread) :
    ¬ IsFlooredSpreadDesign design spread weightFloor := by
  intro hregion
  have hceiling := spread_le_seven_ninths_of_hasSpreadAtLeast_sevenThree design
    (leveragePos_of_allHeavy hregion.1) hregion.2.1
  linarith

/-! ## 3. The floor is rigid at its extreme

The complementary boundary.  `Gtz.Reduction.SplitTransfer` already records that
the region is empty above floor `1/size`; what is new here is that AT `1/size` the
weights are PINNED, so the extreme-floor slice is a rigid stratum rather than a
small one. -/

/-- **THE EXTREME FLOOR PINS THE WEIGHTS.**  `HasWeightFloor D (1/m)` forces every
weight to equal `1/m` exactly: `m` numbers each at least `1/m` summing to one
leave no slack.  So the extreme-floor slice of the region is the uniform-weight
stratum, which is where `Gtz.sevenThreeBasisTetrapodDesign` lives. -/
theorem weight_eq_inv_size_of_hasWeightFloor_inv_size (design : WeightedDesign m 3)
    (hfloor : HasWeightFloor design ((m : ℝ)⁻¹)) (atomIndex : Fin m) :
    design.weight atomIndex = ((m : ℝ))⁻¹ := by
  have hsizePos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Fin.pos atomIndex
  have hgapSum : ∑ otherIndex : Fin m, (design.weight otherIndex - ((m : ℝ))⁻¹) = 0 := by
    rw [Finset.sum_sub_distrib design.weight fun _ => ((m : ℝ))⁻¹, design.weight_sum_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hsizePos.ne']
    ring
  have hgapNonneg : ∀ otherIndex ∈ (Finset.univ : Finset (Fin m)),
      (0 : ℝ) ≤ design.weight otherIndex - ((m : ℝ))⁻¹ := fun otherIndex _ => by
    linarith [hfloor otherIndex]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hgapNonneg).mp hgapSum atomIndex
    (Finset.mem_univ atomIndex)
  linarith

/-! ## 4. Rigidity at the `(7,3)` ceiling

At uniform share `3/7` each vertex spends exactly `4/3` of edge weight across its
six edges.  A cap of `2/9` leaves exactly no slack, so the ceiling forces
equiangularity. -/

/-- The `(7,3)` uniform-share vertex budget: every atom spends exactly `4/3`. -/
theorem sum_erase_edgeWeight_eq_four_thirds_of_uniformShare_sevenThree
    (design : WeightedDesign 7 3) (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7)
    (atomIndex : Fin 7) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, edgeWeight design atomIndex otherIndex = 4 / 3 := by
  have hleveragePos : 0 < leverageOf (design.atom atomIndex) :=
    leverageOf_pos_of_atomShare_pos design (by rw [hshare atomIndex]; norm_num)
  rw [sum_erase_edgeWeight_eq_of_atomShare_eq design hshare hleveragePos]
  norm_num

/-- **THE WELCH BOUND IS THE MEAN EDGE WEIGHT.**  Summing the vertex budget over the
seven atoms, the forty-two ordered off-diagonal edge weights of a `(7,3)`
uniform-share design total exactly `28/3`, so their mean is exactly
`(28/3)/42 = 2/9` — the Welch bound of
`spread_le_seven_ninths_of_hasSpreadAtLeast_sevenThree`.

This is the structural reason the spread parameter cannot deliver the light gate.
A cap asks every edge to sit at or below a value; the mean is fixed at `2/9`; so a
cap at `2/9` forces equality everywhere
(`edgeWeight_eq_two_ninths_of_hasSpreadAtLeast_seven_ninths`) and no cap whatsoever
can push edges below the mean.  The light gate needs three edges at `1/9`, HALF the
mean. -/
theorem sum_sum_erase_edgeWeight_eq_twentyEight_thirds_of_uniformShare_sevenThree
    (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7) :
    ∑ atomIndex : Fin 7, ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        edgeWeight design atomIndex otherIndex = 28 / 3 := by
  rw [Finset.sum_congr rfl fun atomIndex _ =>
    sum_erase_edgeWeight_eq_four_thirds_of_uniformShare_sevenThree design hshare atomIndex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- Positivity of every leverage on the `(7,3)` uniform-share stratum. -/
theorem leveragePos_of_uniformShare_sevenThree (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7) (atomIndex : Fin 7) :
    0 < leverageOf (design.atom atomIndex) :=
  leverageOf_pos_of_atomShare_pos design (by rw [hshare atomIndex]; norm_num)

/-- Every atom of a `(7,3)` uniform-share design has an incident edge of weight at
least `2/9` — the Welch bound read as a per-vertex pigeonhole on the fixed budget
`4/3` spread over six edges.  This is the direct obstruction to any spread above
`7/9`. -/
theorem exists_two_ninths_le_edgeWeight_of_uniformShare_sevenThree (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7) (atomIndex : Fin 7) :
    ∃ otherIndex : Fin 7, otherIndex ≠ atomIndex ∧ 2 / 9 ≤ edgeWeight design atomIndex otherIndex := by
  by_contra hcontra
  push Not at hcontra
  have hcard : (Finset.univ.erase atomIndex).card = 6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hnonempty : (Finset.univ.erase atomIndex).Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  have hstrict : ∑ otherIndex ∈ Finset.univ.erase atomIndex,
        edgeWeight design atomIndex otherIndex
      < ∑ _otherIndex ∈ Finset.univ.erase atomIndex, (2 : ℝ) / 9 :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun otherIndex hmem =>
      hcontra otherIndex (Finset.ne_of_mem_erase hmem)
  rw [Finset.sum_const, hcard, nsmul_eq_mul,
    sum_erase_edgeWeight_eq_four_thirds_of_uniformShare_sevenThree design hshare atomIndex]
    at hstrict
  norm_num at hstrict

/-- **THE `(7,3)` CEILING FORCES EQUIANGULARITY.**  A uniform-share design at the
extreme spread `7/9` has EVERY off-diagonal edge weight exactly `2/9`.  The vertex
budget `4/3` equals `6 * (2/9)`, so a cap of `2/9` is saturated termwise and no
edge can fall below it either. -/
theorem edgeWeight_eq_two_ninths_of_hasSpreadAtLeast_seven_ninths (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7)
    (hspread : HasSpreadAtLeast design (7 / 9)) {atomFirst atomSecond : Fin 7}
    (hne : atomFirst ≠ atomSecond) :
    edgeWeight design atomFirst atomSecond = 2 / 9 := by
  have hleveragePos := leveragePos_of_uniformShare_sevenThree design hshare
  have hcap : ∀ first second : Fin 7, first ≠ second →
      edgeWeight design first second ≤ 2 / 9 := fun first second hpair => by
    have hbound := edgeWeight_le_of_hasSpreadAtLeast design hspread hleveragePos hpair
    linarith
  have hcard : (Finset.univ.erase atomFirst).card = 6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hgapSum : ∑ otherIndex ∈ Finset.univ.erase atomFirst,
      ((2 : ℝ) / 9 - edgeWeight design atomFirst otherIndex) = 0 := by
    rw [Finset.sum_sub_distrib (fun _ => (2 : ℝ) / 9)
        fun otherIndex => edgeWeight design atomFirst otherIndex,
      Finset.sum_const, hcard, nsmul_eq_mul,
      sum_erase_edgeWeight_eq_four_thirds_of_uniformShare_sevenThree design hshare atomFirst]
    norm_num
  have hgapNonneg : ∀ otherIndex ∈ Finset.univ.erase atomFirst,
      (0 : ℝ) ≤ (2 : ℝ) / 9 - edgeWeight design atomFirst otherIndex :=
    fun otherIndex hmem => by
      linarith [hcap atomFirst otherIndex (Finset.ne_of_mem_erase hmem).symm]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hgapNonneg).mp hgapSum atomSecond
    (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩)
  linarith

/-! ## 5. The light gate is obstructed by spread, with the exact constant `13/18`

This is the refutation.  The lane brief expected a large spread to FORCE the light
gate of `Gtz.dominates_triple_of_lightEdges_sevenThree` by pigeonhole.  The
implication runs the other way: the vertex budget is fixed, so capping every edge
makes the edges uniform at `2/9`, and the gate needs `1/9`. -/

/-- **A light triple at `(7,3)`**: three distinct atoms whose three edge weights are
all at most `1/9`, the threshold of `Gtz.dominates_triple_of_lightEdges_sevenThree`. -/
def HasLightTripleSevenThree (design : WeightedDesign 7 3) : Prop :=
  ∃ first second third : Fin 7,
    first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ edgeWeight design first second ≤ 1 / 9
      ∧ edgeWeight design first third ≤ 1 / 9
      ∧ edgeWeight design second third ≤ 1 / 9

/-- **A LIGHT PAIR AT ONE ATOM COSTS SPREAD.**  If a single atom of a `(7,3)`
uniform-share design carries two incident edges of weight at most `1/9`, then
`spread <= 13/18`.  Its four other edges must carry `4/3 - 2/9 = 10/9`, so one of
them reaches `5/18` and the cap `1 - spread` cannot be smaller than `5/18`.

This is unconditional: it needs no information about whether the strip
`(13/18, 7/9]` is inhabited, nor whether `13/18` is attained. -/
theorem spread_le_thirteen_eighteenths_of_two_lightEdges_sevenThree (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7) {spread : ℝ}
    (hspread : HasSpreadAtLeast design spread) {pivotAtom lightFirst lightSecond : Fin 7}
    (hpivotFirst : pivotAtom ≠ lightFirst) (hpivotSecond : pivotAtom ≠ lightSecond)
    (hlightPair : lightFirst ≠ lightSecond)
    (hlightEdgeFirst : edgeWeight design pivotAtom lightFirst ≤ 1 / 9)
    (hlightEdgeSecond : edgeWeight design pivotAtom lightSecond ≤ 1 / 9) :
    spread ≤ 13 / 18 := by
  have hleveragePos := leveragePos_of_uniformShare_sevenThree design hshare
  have hedgeCap : ∀ first second : Fin 7, first ≠ second →
      edgeWeight design first second ≤ 1 - spread := fun first second hpair =>
    edgeWeight_le_of_hasSpreadAtLeast design hspread hleveragePos hpair
  have hsubset : ({lightFirst, lightSecond} : Finset (Fin 7)) ⊆ Finset.univ.erase pivotAtom := by
    intro candidate hcandidate
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · subst hcandidate
      exact Finset.mem_erase.mpr ⟨hpivotFirst.symm, Finset.mem_univ _⟩
    · subst hcandidate
      exact Finset.mem_erase.mpr ⟨hpivotSecond.symm, Finset.mem_univ _⟩
  have hcardOuter :
      (Finset.univ.erase pivotAtom \ ({lightFirst, lightSecond} : Finset (Fin 7))).card = 4 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset,
      Finset.card_insert_of_notMem (by simpa using hlightPair), Finset.card_singleton,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have houterBound : ∑ otherIndex ∈
        Finset.univ.erase pivotAtom \ ({lightFirst, lightSecond} : Finset (Fin 7)),
        edgeWeight design pivotAtom otherIndex ≤ 4 * (1 - spread) := by
    have hstep : ∑ otherIndex ∈
          Finset.univ.erase pivotAtom \ ({lightFirst, lightSecond} : Finset (Fin 7)),
          edgeWeight design pivotAtom otherIndex
        ≤ ∑ _otherIndex ∈
          Finset.univ.erase pivotAtom \ ({lightFirst, lightSecond} : Finset (Fin 7)),
          (1 - spread) :=
      Finset.sum_le_sum fun otherIndex hmem =>
        hedgeCap pivotAtom otherIndex
          (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hmem).1).symm
    rw [Finset.sum_const, hcardOuter, nsmul_eq_mul] at hstep
    norm_num at hstep
    linarith
  have hsplit := Finset.sum_sdiff (f := fun otherIndex => edgeWeight design pivotAtom otherIndex)
    hsubset
  rw [Finset.sum_pair hlightPair,
    sum_erase_edgeWeight_eq_four_thirds_of_uniformShare_sevenThree design hshare pivotAtom]
    at hsplit
  linarith

/-- **THE REFUTATION.**  Above spread `13/18` no `(7,3)` uniform-share design owns a
light triple, so the light gate of `Gtz.dominates_triple_of_lightEdges_sevenThree`
fires NOWHERE.  Spread OBSTRUCTS the gate; it does not force it.  Read together
with `spread_le_seven_ninths_of_hasSpreadAtLeast_sevenThree`, the feasible spread
window is `[0, 7/9]` and the gate-available part of it is exactly `[0, 13/18]`. -/
theorem not_hasLightTripleSevenThree_of_thirteen_eighteenths_lt_spread
    (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7) {spread : ℝ}
    (hspreadGt : 13 / 18 < spread) (hspread : HasSpreadAtLeast design spread) :
    ¬ HasLightTripleSevenThree design := by
  intro hlight
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hedgeOne, hedgeTwo, _⟩ :=
    hlight
  have hceiling := spread_le_thirteen_eighteenths_of_two_lightEdges_sevenThree design hshare
    hspread hfirstSecond hfirstThird hsecondThird hedgeOne hedgeTwo
  linarith

/-- The same conclusion at the ceiling, for an exact rather than an inequality
reason: at spread `7/9` every edge weight is exactly `2/9`, and `2/9 > 1/9`. -/
theorem not_hasLightTripleSevenThree_of_hasSpreadAtLeast_seven_ninths
    (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7)
    (hspread : HasSpreadAtLeast design (7 / 9)) :
    ¬ HasLightTripleSevenThree design := by
  intro hlight
  obtain ⟨first, second, _, hfirstSecond, _, _, hedgeOne, _, _⟩ := hlight
  have hexact := edgeWeight_eq_two_ninths_of_hasSpreadAtLeast_seven_ninths design hshare hspread
    hfirstSecond
  rw [hexact] at hedgeOne
  norm_num at hedgeOne

/-- **THE HEAVY GATE DIES FIRST.**  `Gtz.dominates_triple_of_heavyEdges_sevenThree`
and `Gtz.heavyEdges_rigid_of_uniformShare_sevenThree` need three edges of weight at
least `4/9`.  A spread above `5/9` caps every edge strictly below `4/9`, so no edge
— let alone a triple of them — can be heavy.  No share hypothesis: this is the edge
cap alone. -/
theorem edgeWeight_lt_four_ninths_of_five_ninths_lt_spread (design : WeightedDesign m 3)
    {spread : ℝ} (hspreadGt : 5 / 9 < spread)
    (hleveragePos : ∀ atomIndex : Fin m, 0 < leverageOf (design.atom atomIndex))
    (hspread : HasSpreadAtLeast design spread) {atomFirst atomSecond : Fin m}
    (hne : atomFirst ≠ atomSecond) :
    edgeWeight design atomFirst atomSecond < 4 / 9 := by
  have hcap := edgeWeight_le_of_hasSpreadAtLeast design hspread hleveragePos hne
  linarith

/-- **THE WHOLE PER-TRIPLE GATE LAYER IS FENCED ON THE STRIP `(13/18, 7/9]`.**  Above
spread `13/18` the light gate of `Gtz.dominates_triple_of_lightEdges_sevenThree`
fires nowhere AND the heavy gate of `Gtz.dominates_triple_of_heavyEdges_sevenThree`
fires nowhere, because `13/18 > 5/9`.  Every edge is confined to the MIDDLE BAND
`(1/9, 4/9)` at which neither exact gate applies — the territory of
`Gtz.Quantitative.SevenThreeMiddleBand`.  Read with
`spread_le_seven_ninths_of_hasSpreadAtLeast_sevenThree`, which caps the feasible
spread at `7/9`, this is the exact strip on which raising the spread buys nothing
from the gate layer.

This is the wall, named.  It says where a `(7,3)` certificate must NOT be sought,
not that one cannot exist: whether the strip is inhabited is open (see the header). -/
theorem gateLayerFenced_of_thirteen_eighteenths_lt_spread (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7) {spread : ℝ}
    (hspreadGt : 13 / 18 < spread) (hspread : HasSpreadAtLeast design spread) :
    ¬ HasLightTripleSevenThree design
      ∧ ∀ atomFirst atomSecond : Fin 7, atomFirst ≠ atomSecond →
          edgeWeight design atomFirst atomSecond < 4 / 9 :=
  ⟨not_hasLightTripleSevenThree_of_thirteen_eighteenths_lt_spread design hshare hspreadGt hspread,
    fun atomFirst atomSecond hne =>
      edgeWeight_lt_four_ninths_of_five_ninths_lt_spread design (by linarith)
        (leveragePos_of_uniformShare_sevenThree design hshare) hspread hne⟩

/-! ## 6. What the light gate does buy, unconditionally

The positive half.  On the `(7,3)` equal-share stratum a light triple discharges
the covering conclusion outright, through the landed gate and the symmetric-leg
translation. -/

/-- **A LIGHT TRIPLE DOMINATES.**  On the `(7,3)` equal-share stratum — uniform
share `3/7` and every leverage `3` — a light triple is a dominating triple, by
`Gtz.dominates_triple_of_lightEdges_sevenThree`. -/
theorem exists_dominates_of_hasLightTripleSevenThree (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex : Fin 7, leverageOf (design.atom atomIndex) = 3)
    (hlight : HasLightTripleSevenThree design) :
    ∃ first second third : Fin 7, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ Dominates design {first, second, third} := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    hedgeOne, hedgeTwo, hedgeThree⟩ := hlight
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    dominates_triple_of_lightEdges_sevenThree design hshare (hleverage first) (hleverage second)
      (hleverage third) hfirstSecond hfirstThird hsecondThird hedgeOne hedgeTwo hedgeThree⟩

/-- **A LIGHT TRIPLE DISCHARGES THE COVERING CONCLUSION.**  Both `S_3`-invariant
legs of `Gtz.Quantitative.PositivstellensatzRankThree` are nonnegative at the light
triple.  This is an unconditional covering theorem on a region that is NOT empty —
`sevenThreeBasisTetrapodDesign_hasLightTripleSevenThree` inhabits it. -/
theorem symmetricLegs_nonneg_of_hasLightTripleSevenThree (design : WeightedDesign 7 3)
    (hshare : ∀ atomIndex : Fin 7, atomShare design atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex : Fin 7, leverageOf (design.atom atomIndex) = 3)
    (hlight : HasLightTripleSevenThree design) :
    ∃ first second third : Fin 7, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ discriminantMinorSum design first second third
      ∧ 0 ≤ discriminantTie design first second third := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hdominates⟩ :=
    exists_dominates_of_hasLightTripleSevenThree design hshare hleverage hlight
  have hheavy : ∀ atomIndex : Fin 7, 1 < leverageOf (design.atom atomIndex) := fun atomIndex => by
    rw [hleverage atomIndex]; norm_num
  obtain ⟨hminorSum, htie⟩ :=
    (dominates_triple_iff_symmetricLegs design hfirstSecond hfirstThird hsecondThird
      (hheavy first) (hheavy second) (hheavy third)).mp hdominates
  exact ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminorSum, htie⟩

/-! ## 7. The size-generic covering, and the two vacuous windows

`Gtz.FlooredSpreadCovering` is the size-six sentence.  The region predicates it
uses are already size-generic, so only the covering itself needs lifting, and the
lift is LOSSLESS: at size six the two propositions are literally equal. -/

/-- **The floored spread covering at an arbitrary size.**  Every all-heavy design of
the given size whose pairwise squared sines are at least `spread` and whose weights
are at least `weightFloor` has a triple at which both `S_3`-invariant legs are
nonnegative.  NOT PROVED at any size below the Welch ceiling. -/
def FlooredSpreadCoveringAtSize (size : ℕ) (spread weightFloor : ℝ) : Prop :=
  ∀ design : WeightedDesign size 3, IsFlooredSpreadDesign design spread weightFloor →
    ∃ first second third : Fin size,
      first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ 0 ≤ discriminantMinorSum design first second third
        ∧ 0 ≤ discriminantTie design first second third

/-- The size-generic covering IS the size-six one at size six — same proposition,
so no duplication and no loss. -/
theorem flooredSpreadCovering_iff_flooredSpreadCoveringAtSize_six (spread weightFloor : ℝ) :
    FlooredSpreadCovering spread weightFloor ↔ FlooredSpreadCoveringAtSize 6 spread weightFloor :=
  Iff.rfl

/-- Shrinking either parameter enlarges the region, so the covering at the smaller
parameters is the stronger statement. -/
theorem flooredSpreadCoveringAtSize_mono {size : ℕ}
    {spread weightFloor smallerSpread smallerFloor : ℝ} (hspreadLe : smallerSpread ≤ spread)
    (hfloorLe : smallerFloor ≤ weightFloor)
    (hcovering : FlooredSpreadCoveringAtSize size smallerSpread smallerFloor) :
    FlooredSpreadCoveringAtSize size spread weightFloor :=
  fun design hregion => hcovering design (isFlooredSpreadDesign_mono hspreadLe hfloorLe hregion)

/-- The trivial direction: the unrestricted covering implies its restriction. -/
theorem flooredSpreadCoveringAtSize_of_symmetricCovering (size : ℕ) (spread weightFloor : ℝ)
    (hcovering : SymmetricCovering size) : FlooredSpreadCoveringAtSize size spread weightFloor :=
  fun design hregion => hcovering design hregion.1

/-- **VACUOUS, and that is the point.**  Above the `(6,3)` Welch ceiling `4/5` the
region is empty, so the covering holds for the emptiest of reasons.  This closes
the window `(4/5, 1]` that `Gtz.Quantitative.SpreadCertificateSixThree` records as
guarded by neither of its boundary theorems, and it says that no certificate found
at a spread above `4/5` proves anything. -/
theorem flooredSpreadCoveringAtSize_six_of_four_fifths_lt_spread {spread weightFloor : ℝ}
    (hspreadGt : 4 / 5 < spread) : FlooredSpreadCoveringAtSize 6 spread weightFloor :=
  fun design hregion =>
    absurd hregion (not_isFlooredSpreadDesign_sixThree_of_four_fifths_lt_spread design hspreadGt)

/-- **VACUOUS.**  Above the `(7,3)` Welch ceiling `7/9` the region is empty.  The
seven-point twin of the previous theorem, and the reason no `(7,3)` certificate
should be sought above `7/9`. -/
theorem flooredSpreadCoveringAtSize_seven_of_seven_ninths_lt_spread {spread weightFloor : ℝ}
    (hspreadGt : 7 / 9 < spread) : FlooredSpreadCoveringAtSize 7 spread weightFloor :=
  fun design hregion =>
    absurd hregion
      (not_isFlooredSpreadDesign_sevenThree_of_seven_ninths_lt_spread design hspreadGt)

/-! ## 8. Non-vacuity at seven points

`Gtz.sevenThreeBasisTetrapodDesign` carries exactly three distinct edge weights:
`0` on the three basis pairs, `1/3` on the twelve mixed pairs, `1/9` on the six
tetrapod pairs.  Its spread is therefore exactly `2/3` and its floor exactly `1/7`,
the extreme. -/

/-- Every off-diagonal squared pairing of the witness is at most `3`, with equality
on the twelve mixed pairs.  Since every leverage is `3`, this is the spread bound
`2/3` in raw coordinates. -/
theorem atomPairing_sq_le_three_sevenThreeBasisTetrapodDesign {atomFirst atomSecond : Fin 7}
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sevenThreeBasisTetrapodDesign atomFirst atomSecond ^ 2 ≤ 3 := by
  have hrootSq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [atomPairing]
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    simp_all [sevenThreeBasisTetrapodDesign_atom, sevenThreeBasisTetrapodAtom, tetraAtom,
      dotProduct, Fin.sum_univ_three]

/-- **THE `(7,3)` WITNESS HAS SPREAD `2/3`.** -/
theorem sevenThreeBasisTetrapodDesign_hasSpreadAtLeast_two_thirds :
    HasSpreadAtLeast sevenThreeBasisTetrapodDesign (2 / 3) := by
  intro atomFirst atomSecond hne
  rw [leverageOf_sevenThreeBasisTetrapodDesign, leverageOf_sevenThreeBasisTetrapodDesign]
  have hbound := atomPairing_sq_le_three_sevenThreeBasisTetrapodDesign hne
  linarith

/-- The mixed pair `(0,3)` has squared pairing exactly `3`. -/
theorem atomPairing_sq_zero_three_sevenThreeBasisTetrapodDesign :
    atomPairing sevenThreeBasisTetrapodDesign 0 3 ^ 2 = 3 := by
  have hrootSq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [atomPairing, sevenThreeBasisTetrapodDesign_atom]
  simp only [sevenThreeBasisTetrapodAtom_zero, sevenThreeBasisTetrapodAtom_three, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [hrootSq]

/-- **`2/3` IS EXACT for the witness**: the mixed pair `(0,3)` saturates it, so no
larger spread holds. -/
theorem sevenThreeBasisTetrapodDesign_not_hasSpreadAtLeast_of_two_thirds_lt {spread : ℝ}
    (hspreadGt : 2 / 3 < spread) : ¬ HasSpreadAtLeast sevenThreeBasisTetrapodDesign spread := by
  intro hspread
  have hbound := hspread 0 3 (by decide)
  rw [atomPairing_sq_zero_three_sevenThreeBasisTetrapodDesign,
    leverageOf_sevenThreeBasisTetrapodDesign, leverageOf_sevenThreeBasisTetrapodDesign] at hbound
  linarith

/-- The witness carries the extreme weight floor `1/7`; by
`weight_eq_inv_size_of_hasWeightFloor_inv_size` that floor pins the weights, and
indeed all seven are `1/7`. -/
theorem sevenThreeBasisTetrapodDesign_hasWeightFloor_one_seventh :
    HasWeightFloor sevenThreeBasisTetrapodDesign (1 / 7) := by
  intro atomIndex
  rw [sevenThreeBasisTetrapodDesign_weight]
  norm_num

/-- **THE `(7,3)` FLOORED SPREAD REGION IS INHABITED**, at `spread = 2/3` and
`weightFloor = 1/7`.  Both parameters are exact and `2/3 < 13/18 < 7/9`, so the
witness sits strictly inside the part of the feasible spread window where the light
gate is still available. -/
theorem sevenThreeBasisTetrapodDesign_isFlooredSpreadDesign :
    IsFlooredSpreadDesign sevenThreeBasisTetrapodDesign (2 / 3) (1 / 7) :=
  ⟨allHeavy_sevenThreeBasisTetrapodDesign,
    sevenThreeBasisTetrapodDesign_hasSpreadAtLeast_two_thirds,
    sevenThreeBasisTetrapodDesign_hasWeightFloor_one_seventh⟩

/-- The tetrapod pair `(3,4)` has edge weight exactly `1/9`. -/
theorem edgeWeight_three_four_sevenThreeBasisTetrapodDesign :
    edgeWeight sevenThreeBasisTetrapodDesign 3 4 = 1 / 9 := by
  rw [edgeWeight, directionGram_sevenThreeBasisTetrapodDesign_three_four]
  norm_num

/-- The tetrapod pair `(3,5)` has edge weight exactly `1/9`. -/
theorem edgeWeight_three_five_sevenThreeBasisTetrapodDesign :
    edgeWeight sevenThreeBasisTetrapodDesign 3 5 = 1 / 9 := by
  rw [edgeWeight, directionGram_sevenThreeBasisTetrapodDesign_three_five]
  norm_num

/-- The tetrapod pair `(4,5)` has edge weight exactly `1/9`. -/
theorem edgeWeight_four_five_sevenThreeBasisTetrapodDesign :
    edgeWeight sevenThreeBasisTetrapodDesign 4 5 = 1 / 9 := by
  rw [edgeWeight, directionGram_sevenThreeBasisTetrapodDesign_four_five]
  norm_num

/-- **THE WITNESS OWNS A LIGHT TRIPLE**, the tetrapod triple `{3,4,5}`, sitting
exactly ON the gate boundary `1/9`.  So the light-gate covering theorem
`symmetricLegs_nonneg_of_hasLightTripleSevenThree` is not vacuous. -/
theorem sevenThreeBasisTetrapodDesign_hasLightTripleSevenThree :
    HasLightTripleSevenThree sevenThreeBasisTetrapodDesign :=
  ⟨3, 4, 5, by decide, by decide, by decide,
    le_of_eq edgeWeight_three_four_sevenThreeBasisTetrapodDesign,
    le_of_eq edgeWeight_three_five_sevenThreeBasisTetrapodDesign,
    le_of_eq edgeWeight_four_five_sevenThreeBasisTetrapodDesign⟩

/-- **THE COVERING CONCLUSION, DISCHARGED AT THE WITNESS.**  The route this file
builds — region membership, light triple, landed gate, symmetric-leg translation —
runs end to end on `Gtz.sevenThreeBasisTetrapodDesign`.  (The domination itself was
already landed independently as
`Gtz.dominates_tetrapodTriple_sevenThreeBasisTetrapodDesign` through the
seven-clause slack criterion; what is new is that the LANE'S gate reaches it, so
the route is exercised and not merely stated.) -/
theorem symmetricLegs_nonneg_sevenThreeBasisTetrapodDesign :
    ∃ first second third : Fin 7, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 0 ≤ discriminantMinorSum sevenThreeBasisTetrapodDesign first second third
      ∧ 0 ≤ discriminantTie sevenThreeBasisTetrapodDesign first second third :=
  symmetricLegs_nonneg_of_hasLightTripleSevenThree sevenThreeBasisTetrapodDesign
    atomShare_sevenThreeBasisTetrapodDesign leverageOf_sevenThreeBasisTetrapodDesign
    sevenThreeBasisTetrapodDesign_hasLightTripleSevenThree

/-! ## 9. The region excises the `(7,3)` split-tetrahedron tie

`Gtz.splitSevenDesign` is the seven-point split tetrahedron: `Gtz.splitSevenDirection`
is `![0,1,2,3,0,1,2]`, so atoms `0` and `4` are the SAME vector and their squared
cosine is exactly `1`.  Any positive spread removes it — the seven-point twin of
`Gtz.splitTetraDesign_not_hasSpreadAtLeast`.

This is one witness, not the universal claim.  See the header's warning about
`Gtz.HingeHoldsAtSize`. -/

/-- **THE SPREAD PARAMETER REMOVES THE `(7,3)` TIE.**  Atoms `0` and `4` of
`Gtz.splitSevenDesign` carry the same tetrahedron direction, so they pair at exactly
their common leverage `3`, giving squared cosine `1`. -/
theorem splitSevenDesign_not_hasSpreadAtLeast {spread : ℝ} (hspreadPos : 0 < spread) :
    ¬ HasSpreadAtLeast splitSevenDesign spread := by
  intro hspread
  have hpairing : atomPairing splitSevenDesign 0 4 = 3 :=
    splitSevenDesign_atomPairing_of_sameDirection (by decide)
  have hbound := hspread 0 4 (by decide)
  rw [hpairing, splitSevenDesign_leverage, splitSevenDesign_leverage] at hbound
  linarith

/-- The `(7,3)` tie is outside the region at every positive spread and every
floor. -/
theorem splitSevenDesign_not_isFlooredSpreadDesign {spread weightFloor : ℝ}
    (hspreadPos : 0 < spread) :
    ¬ IsFlooredSpreadDesign splitSevenDesign spread weightFloor := by
  intro hregion
  exact splitSevenDesign_not_hasSpreadAtLeast hspreadPos hregion.2.1

end Gtz
