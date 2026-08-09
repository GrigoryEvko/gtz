/-
# The depth-cap normal form and the cross-axis Parseval

Two readings of the rank-three residual that the endgame consumes, plus the
two-by-two algebra that connects them.

## The cross-axis Parseval (Part 2 below)

Fix two labels and let `w = a_i x a_j` be their cross axis (`Gtz.bracketNormal`
of the two atoms).  Both `a_i` and `a_j` are orthogonal to `w`, so Parseval
evaluated at `w` is carried ENTIRELY by the other atoms:

    sum over c NOT in {i,j} of  t_c * [a_i, a_j, a_c]^2
      =  leverage_i * leverage_j - <a_i, a_j>^2

the right side being the Lagrange identity for `|w|^2`.  Nothing is assumed:
not heaviness, not distinctness of the two labels, not primitivity.  At size six
that is four atoms carrying the whole axis budget, one exact identity per pair,
fifteen in all, each touching only four atoms.

## The depth cap (Part 3 below)

The tie polynomial `Gtz.discriminantTie` at pivot `k` over the pair `(i,j)`
splits as

    discriminantTie D k i j  =  E_ij * heavyExcess k  -  depthForm D i j k

where `E_ij = Gtz.pairGapExcessOf` is the two-by-two leading minor of `Gram - I`
at the pair and `depthForm` is the ADJUGATE form of that minor evaluated at the
pair of pairings `(<a_i,a_k>, <a_j,a_k>)`.  The split is a reading, not a new
polynomial: the lump `depthForm - E * heavyExcess` is the landed
`Gtz.tripleGapForm`, and `Gtz.tripleGapForm_eq_neg_discriminantTie` already
records its sign.  What is new here is that the first summand alone is a
positive semidefinite quadratic in the third atom, nonnegative whenever the pair
is nonnegative-definite and vanishing exactly on the cross axis when the pair is
LIVE.  Domination of a triple at a heavy pivot is therefore, on the tie leg
exactly, the DEPTH CAP `depthForm <= E_ij * heavyExcess k`, and the tie side
`discriminantTie <= 0` is the reverse floor.

## Live pairs (Part 4 below)

A pair is live when both excesses and the pair minor are strictly positive.  A
live pair strictly dominates on the plane orthogonal to its cross axis: for
every nonzero planar probe `x`,

    x . x  <  (a_i . x)^2 + (a_j . x)^2.

This is the compression of the pair gap to the plane, whose matrix is congruent
to the two-by-two Gram gap `[[h_i, p], [p, h_j]]`; positive definiteness of that
is Sylvester, which is exactly liveness.  The proof here is frame-free -- no
orthonormal basis of the plane is chosen, and the conclusion quantifies over
every planar probe -- carried by one nine-variable polynomial resolution of a
probe against the pair and its axis.
-/
import Gtz.Design.GeneralRankAveraging
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.PairDifferenceCover
import Gtz.Ties.TotalTieCorankOne
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Reduction.RealVolumeFloor
import Gtz.LinAlg.PsdKit
import Gtz.Design.LeverageBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1: the two-by-two algebra, design-free

Three scalar facts about the symmetric two-by-two form `[[a, p], [p, b]]` and its
adjugate `[[b, -p], [-p, a]]`.  Keeping them design-free is what lets the same
statements serve the depth form (where the form is the adjugate and the
coordinates are pairings) and the planar strictness (where the form is the
compressed gap and the coordinates are probe projections). -/

/-- **The adjugate form is nonnegative** as soon as the form it is adjugate to
is nonnegative-definite.  This is the semidefinite half of Sylvester at size two,
stated on the adjugate so that no division and no matrix appears. -/
theorem adjugateForm_nonneg (headFirst headSecond pairing firstCoord secondCoord : ℝ)
    (hfirstNonneg : 0 ≤ headFirst) (hsecondNonneg : 0 ≤ headSecond)
    (hdetNonneg : 0 ≤ headFirst * headSecond - pairing ^ 2) :
    0 ≤ headSecond * firstCoord ^ 2 - 2 * pairing * firstCoord * secondCoord
      + headFirst * secondCoord ^ 2 := by
  rcases eq_or_lt_of_le hsecondNonneg with hheadZero | hheadPos
  · have hpairingZero : pairing = 0 := by nlinarith [sq_nonneg pairing]
    rw [hpairingZero]
    nlinarith [sq_nonneg secondCoord]
  · nlinarith [sq_nonneg (headSecond * firstCoord - pairing * secondCoord),
      mul_nonneg hdetNonneg (sq_nonneg secondCoord)]

/-- **The kernel of the adjugate form** is exactly the common zero of the two
coordinates, once the form it is adjugate to is positive definite.  Only the
second head and the determinant are needed; the first head comes along free. -/
theorem adjugateForm_eq_zero_iff (headFirst headSecond pairing firstCoord secondCoord : ℝ)
    (hsecondPos : 0 < headSecond)
    (hdetPos : 0 < headFirst * headSecond - pairing ^ 2) :
    headSecond * firstCoord ^ 2 - 2 * pairing * firstCoord * secondCoord
        + headFirst * secondCoord ^ 2 = 0
      ↔ (firstCoord = 0 ∧ secondCoord = 0) := by
  constructor
  · intro hvanish
    have hcomplete : (headSecond * firstCoord - pairing * secondCoord) ^ 2
        + (headFirst * headSecond - pairing ^ 2) * secondCoord ^ 2 = 0 := by
      linear_combination headSecond * hvanish
    have hsecondZero : secondCoord = 0 := by
      by_contra hsecondNe
      have hsecondSqPos : 0 < secondCoord ^ 2 :=
        lt_of_le_of_ne (sq_nonneg secondCoord) (Ne.symm (pow_ne_zero 2 hsecondNe))
      have hsquareNonneg := sq_nonneg (headSecond * firstCoord - pairing * secondCoord)
      have hdetTermPos := mul_pos hdetPos hsecondSqPos
      linarith
    have hfirstZero : firstCoord = 0 := by
      rw [hsecondZero] at hcomplete
      have hheadSq : (headSecond * firstCoord) ^ 2 = 0 := by linear_combination hcomplete
      have hheadProd : headSecond * firstCoord = 0 := pow_eq_zero_iff two_ne_zero |>.mp hheadSq
      rcases mul_eq_zero.mp hheadProd with hheadZero | hcoordZero
      · exact absurd hheadZero (ne_of_gt hsecondPos)
      · exact hcoordZero
    exact ⟨hfirstZero, hsecondZero⟩
  · rintro ⟨hfirstZero, hsecondZero⟩
    rw [hfirstZero, hsecondZero]
    ring

/-- **Sylvester at size two, strict**, in scalar form: a positive leading entry
and a positive determinant make the form strictly positive away from the
origin. -/
theorem twoByTwoForm_pos_of_leadingPos_of_detPos
    (headFirst headSecond pairing firstCoord secondCoord : ℝ)
    (hfirstPos : 0 < headFirst)
    (hdetPos : 0 < headFirst * headSecond - pairing ^ 2)
    (hnotBothZero : ¬ (firstCoord = 0 ∧ secondCoord = 0)) :
    0 < headFirst * firstCoord ^ 2 + 2 * pairing * firstCoord * secondCoord
      + headSecond * secondCoord ^ 2 := by
  rcases eq_or_ne secondCoord 0 with hsecondZero | hsecondNe
  · have hfirstNe : firstCoord ≠ 0 := fun hzero => hnotBothZero ⟨hzero, hsecondZero⟩
    have hfirstSqPos : 0 < firstCoord ^ 2 :=
      lt_of_le_of_ne (sq_nonneg firstCoord) (Ne.symm (pow_ne_zero 2 hfirstNe))
    rw [hsecondZero]
    nlinarith [mul_pos hfirstPos hfirstSqPos]
  · have hsecondSqPos : 0 < secondCoord ^ 2 :=
      lt_of_le_of_ne (sq_nonneg secondCoord) (Ne.symm (pow_ne_zero 2 hsecondNe))
    nlinarith [sq_nonneg (headFirst * firstCoord + pairing * secondCoord),
      mul_pos hdetPos hsecondSqPos]

/-! ## Part 2: the cross axis and the cross-axis Parseval

`Gtz.bracketNormal` is the cross product: `Gtz.tripleBracket l r x` is
`bracketNormal l r` paired with `x`, and
`Gtz.bracketNormal_self_dotProduct` is the Lagrange identity.  Naming the
design-level cross product makes the Parseval statement readable and gives the
axis budget a name of its own. -/

/-- The **cross axis** of an ordered pair of atoms: the direction both atoms of
the pair are orthogonal to. -/
def crossAxis (D : WeightedDesign m 3) (firstLabel secondLabel : Fin m) : Fin 3 → ℝ :=
  bracketNormal (D.atom firstLabel) (D.atom secondLabel)

/-- The **cross-axis budget** of a pair: the Gram determinant
`|a_i|^2 |a_j|^2 - <a_i, a_j>^2`, which the Lagrange identity makes the squared
length of the cross axis. -/
def crossAxisBudget (D : WeightedDesign m 3) (firstLabel secondLabel : Fin m) : ℝ :=
  leverageOf (D.atom firstLabel) * leverageOf (D.atom secondLabel)
    - atomPairing D firstLabel secondLabel ^ 2

/-- **The Lagrange identity, at a design pair.** -/
theorem crossAxis_dotProduct_self (D : WeightedDesign m 3) (firstLabel secondLabel : Fin m) :
    crossAxis D firstLabel secondLabel ⬝ᵥ crossAxis D firstLabel secondLabel
      = crossAxisBudget D firstLabel secondLabel := by
  rw [crossAxis, bracketNormal_self_dotProduct, crossAxisBudget, atomPairing,
    leverageOf_eq_dotProduct, leverageOf_eq_dotProduct]

/-- **The bracket is the pairing against the cross axis.** -/
theorem atom_dotProduct_crossAxis (D : WeightedDesign m 3)
    (firstLabel secondLabel probeLabel : Fin m) :
    D.atom probeLabel ⬝ᵥ crossAxis D firstLabel secondLabel
      = atomBracket D firstLabel secondLabel probeLabel := by
  rw [crossAxis, atomBracket, tripleBracket_eq_bracketNormal_dotProduct]
  exact dotProduct_comm _ _

/-- The pair's FIRST atom is orthogonal to the cross axis. -/
theorem atomBracket_self_left (D : WeightedDesign m 3) (firstLabel secondLabel : Fin m) :
    atomBracket D firstLabel secondLabel firstLabel = 0 := by
  simp only [atomBracket, tripleBracket_eq]
  ring

/-- The pair's SECOND atom is orthogonal to the cross axis. -/
theorem atomBracket_self_right (D : WeightedDesign m 3) (firstLabel secondLabel : Fin m) :
    atomBracket D firstLabel secondLabel secondLabel = 0 := by
  simp only [atomBracket, tripleBracket_eq]
  ring

theorem crossAxisBudget_nonneg (D : WeightedDesign m 3) (firstLabel secondLabel : Fin m) :
    0 ≤ crossAxisBudget D firstLabel secondLabel := by
  rw [← crossAxis_dotProduct_self]
  exact dotProduct_self_nonneg _

/-- **The axis budget in the gap scalars.**  `|a_i x a_j|^2` is the pair minor
plus the two excesses plus one: the two readings of a pair -- its Gram
determinant and its gap minor -- differ by exactly the excess budget plus one.
`Gtz.one_lt_crossAxisBudget_of_isLivePair` reads off the consequence at a live
pair. -/
theorem crossAxisBudget_eq_pairGapExcessOf_add (D : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    crossAxisBudget D firstLabel secondLabel
      = pairGapExcessOf D firstLabel secondLabel
        + gapExcessOf D firstLabel + gapExcessOf D secondLabel + 1 := by
  simp only [crossAxisBudget, pairGapExcessOf, gapExcessOf, gapPairingOf, atomPairing]
  ring

/-- **THE CROSS-AXIS PARSEVAL, FULL SUM.**  Parseval evaluated at the cross axis
of a pair, read through the bracket dictionary.  Hypothesis-free. -/
theorem sum_weight_mul_atomBracket_sq (D : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    ∑ probeLabel, D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2
      = crossAxisBudget D firstLabel secondLabel := by
  have hparseval := dotProduct_self_eq_sum_weight_mul_sq D (crossAxis D firstLabel secondLabel)
  rw [crossAxis_dotProduct_self] at hparseval
  rw [hparseval]
  exact Finset.sum_congr rfl fun probeLabel _ => by
    rw [atom_dotProduct_crossAxis]

/-- **THE CROSS-AXIS PARSEVAL.**  The two atoms of the pair contribute nothing at
their own cross axis, so the whole axis budget is carried by the atoms OUTSIDE
the pair:

    sum over c not in {i,j} of  t_c * [a_i, a_j, a_c]^2
      =  leverage_i * leverage_j - <a_i, a_j>^2.

No heaviness, no distinctness, no primitivity: one exact identity per ordered
pair of labels, at every rank-three design.  At size six the left side runs over
four atoms, so the fifteen unordered pairs give fifteen exact identities each
touching only four atoms. -/
theorem sum_offPair_weight_mul_atomBracket_sq (D : WeightedDesign m 3)
    (firstLabel secondLabel : Fin m) :
    ∑ probeLabel ∈ ({firstLabel, secondLabel} : Finset (Fin m))ᶜ,
        D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2
      = crossAxisBudget D firstLabel secondLabel := by
  classical
  have hpairVanishes : ∑ probeLabel ∈ ({firstLabel, secondLabel} : Finset (Fin m)),
      D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun probeLabel hmember => ?_
    rcases Finset.mem_insert.mp hmember with rfl | hsingleton
    · rw [atomBracket_self_left]; ring
    · rw [Finset.mem_singleton.mp hsingleton, atomBracket_self_right]; ring
  have hsplit := Finset.sum_add_sum_compl ({firstLabel, secondLabel} : Finset (Fin m))
    (fun probeLabel =>
      D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2)
  rw [hpairVanishes, zero_add] at hsplit
  rw [hsplit, sum_weight_mul_atomBracket_sq]

/-- **The per-atom cap.**  Every single weighted squared bracket is capped by the
axis budget of the pair it is taken against. -/
theorem weight_mul_atomBracket_sq_le_crossAxisBudget (D : WeightedDesign m 3)
    (firstLabel secondLabel probeLabel : Fin m) :
    D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2
      ≤ crossAxisBudget D firstLabel secondLabel := by
  have htermNonneg : ∀ otherLabel ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ D.weight otherLabel * atomBracket D firstLabel secondLabel otherLabel ^ 2 :=
    fun otherLabel _ => mul_nonneg (D.weight_pos otherLabel).le (sq_nonneg _)
  calc D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2
      ≤ ∑ otherLabel, D.weight otherLabel
          * atomBracket D firstLabel secondLabel otherLabel ^ 2 :=
        Finset.single_le_sum htermNonneg (Finset.mem_univ probeLabel)
    _ = crossAxisBudget D firstLabel secondLabel :=
        sum_weight_mul_atomBracket_sq D firstLabel secondLabel

/-- **No rank-three design is coplanar with a nondegenerate pair.**  If the pair's
axis budget is positive -- equivalently the two atoms are not parallel -- then
some atom outside the pair has a nonvanishing bracket against it.  A positive
right side cannot be carried by an empty left side. -/
theorem exists_offPair_atomBracket_ne_zero_of_crossAxisBudget_pos (D : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m}
    (hbudgetPos : 0 < crossAxisBudget D firstLabel secondLabel) :
    ∃ probeLabel ∈ ({firstLabel, secondLabel} : Finset (Fin m))ᶜ,
      atomBracket D firstLabel secondLabel probeLabel ≠ 0 := by
  classical
  by_contra hallVanish
  push Not at hallVanish
  have hsumZero : ∑ probeLabel ∈ ({firstLabel, secondLabel} : Finset (Fin m))ᶜ,
      D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2 = 0 :=
    Finset.sum_eq_zero fun probeLabel hmember => by
      rw [hallVanish probeLabel hmember]; ring
  rw [sum_offPair_weight_mul_atomBracket_sq] at hsumZero
  exact absurd hsumZero (ne_of_gt hbudgetPos)

/-- **The support of the cross-axis Parseval has size `m - 2`.**  Stated added
rather than subtracted so no natural subtraction appears: at size six the axis
budget of a distinct pair is carried by exactly four atoms. -/
theorem card_offPair_add_two {firstLabel secondLabel : Fin m}
    (hdistinct : firstLabel ≠ secondLabel) :
    (({firstLabel, secondLabel} : Finset (Fin m))ᶜ).card + 2 = m := by
  classical
  have hpairCard : ({firstLabel, secondLabel} : Finset (Fin m)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hdistinct), Finset.card_singleton]
  have hcomplement := Finset.card_add_card_compl ({firstLabel, secondLabel} : Finset (Fin m))
  rw [hpairCard, Fintype.card_fin] at hcomplement
  omega

/-- **The pigeonhole at the cross axis.**  The axis budget is spread over `m - 2`
atoms, so some atom outside the pair carries at least the average share.  Stated
multiplied by the support size so no division appears: at size six this reads
`budget <= 4 * (t_c * bracket_c^2)` for some `c` outside the pair. -/
theorem exists_offPair_weight_mul_atomBracket_sq_ge (D : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hdistinct : firstLabel ≠ secondLabel)
    (hsizeThree : 2 < m) :
    ∃ probeLabel ∈ ({firstLabel, secondLabel} : Finset (Fin m))ᶜ,
      crossAxisBudget D firstLabel secondLabel
        ≤ ((({firstLabel, secondLabel} : Finset (Fin m))ᶜ).card : ℝ)
          * (D.weight probeLabel * atomBracket D firstLabel secondLabel probeLabel ^ 2) := by
  classical
  have hsupportCard := card_offPair_add_two (m := m) hdistinct
  have hsupportNonempty : (({firstLabel, secondLabel} : Finset (Fin m))ᶜ).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨topLabel, htopMember, htopMax⟩ := Finset.exists_max_image
    (({firstLabel, secondLabel} : Finset (Fin m))ᶜ)
    (fun probeLabel => D.weight probeLabel
      * atomBracket D firstLabel secondLabel probeLabel ^ 2) hsupportNonempty
  refine ⟨topLabel, htopMember, ?_⟩
  have hsumBound := Finset.sum_le_card_nsmul
    (({firstLabel, secondLabel} : Finset (Fin m))ᶜ)
    (fun probeLabel => D.weight probeLabel
      * atomBracket D firstLabel secondLabel probeLabel ^ 2)
    (D.weight topLabel * atomBracket D firstLabel secondLabel topLabel ^ 2) htopMax
  rw [sum_offPair_weight_mul_atomBracket_sq, nsmul_eq_mul] at hsumBound
  exact hsumBound

/-! ## Part 3: the depth form and the depth cap

`Gtz.tripleGapForm` is the landed lump `depthForm - pairMinor * pivotExcess`, and
`Gtz.tripleGapForm_eq_neg_discriminantTie` already fixes its sign.  What follows
splits the lump and reads each piece. -/

/-- The **depth form** of a third atom against an ordered pair: the ADJUGATE of
the pair's two-by-two gap minor, evaluated at the two pairings of the third atom
against the pair.  As a function of the third atom this is a quadratic form; it
is the piece of the tie polynomial that the third atom controls. -/
def depthForm (D : WeightedDesign m k) (firstLabel secondLabel probeLabel : Fin m) : ℝ :=
  gapExcessOf D secondLabel * gapPairingOf D firstLabel probeLabel ^ 2
    - 2 * gapPairingOf D firstLabel secondLabel * gapPairingOf D firstLabel probeLabel
        * gapPairingOf D secondLabel probeLabel
    + gapExcessOf D firstLabel * gapPairingOf D secondLabel probeLabel ^ 2

/-- The rank-three spelling of the depth form, in `Gtz.heavyExcess` and
`Gtz.atomPairing`. -/
theorem depthForm_eq_heavyExcess_expansion (D : WeightedDesign m 3)
    (firstLabel secondLabel probeLabel : Fin m) :
    depthForm D firstLabel secondLabel probeLabel
      = heavyExcess D secondLabel * atomPairing D firstLabel probeLabel ^ 2
        - 2 * atomPairing D firstLabel secondLabel * atomPairing D firstLabel probeLabel
            * atomPairing D secondLabel probeLabel
        + heavyExcess D firstLabel * atomPairing D secondLabel probeLabel ^ 2 := rfl

/-- **The split, at any rank.**  Subtracting the pair minor scaled by the pivot's
excess from the depth form is exactly the landed `Gtz.tripleGapForm` -- the only
content is the symmetry of the pairing. -/
theorem depthForm_sub_pairGapExcessOf_mul_gapExcessOf (D : WeightedDesign m k)
    (firstLabel secondLabel probeLabel : Fin m) :
    depthForm D firstLabel secondLabel probeLabel
        - pairGapExcessOf D firstLabel secondLabel * gapExcessOf D probeLabel
      = tripleGapForm D probeLabel firstLabel secondLabel := by
  rw [depthForm, tripleGapForm, gapPairingOf_comm D firstLabel probeLabel,
    gapPairingOf_comm D secondLabel probeLabel]

/-- **THE DEPTH-CAP NORMAL FORM.**  At rank three the split reads the tie
polynomial: `depthForm - pairMinor * pivotExcess` is MINUS
`Gtz.discriminantTie` at the pivot.  The sign is inherited from the landed
`Gtz.tripleGapForm_eq_neg_discriminantTie`, not guessed. -/
theorem depthForm_sub_pairGapExcessOf_mul_heavyExcess_eq_neg_discriminantTie
    (D : WeightedDesign m 3) (firstLabel secondLabel probeLabel : Fin m) :
    depthForm D firstLabel secondLabel probeLabel
        - pairGapExcessOf D firstLabel secondLabel * heavyExcess D probeLabel
      = - discriminantTie D probeLabel firstLabel secondLabel := by
  rw [← gapExcessOf_eq_heavyExcess, depthForm_sub_pairGapExcessOf_mul_gapExcessOf,
    tripleGapForm_eq_neg_discriminantTie]

/-- The same identity solved for the tie polynomial: the tie is the pair's
capacity `pairMinor * pivotExcess` minus the depth the pivot occupies. -/
theorem discriminantTie_eq_pairGapExcessOf_mul_heavyExcess_sub_depthForm
    (D : WeightedDesign m 3) (firstLabel secondLabel probeLabel : Fin m) :
    discriminantTie D probeLabel firstLabel secondLabel
      = pairGapExcessOf D firstLabel secondLabel * heavyExcess D probeLabel
        - depthForm D firstLabel secondLabel probeLabel := by
  have hsplit := depthForm_sub_pairGapExcessOf_mul_heavyExcess_eq_neg_discriminantTie
    D firstLabel secondLabel probeLabel
  linarith

/-- **The depth form is positive semidefinite** in the third atom whenever the
pair it is taken against is nonnegative-definite.  This is what makes "depth" a
meaningful word: the quantity is never negative, so the cap below is a genuine
one-sided constraint. -/
theorem depthForm_nonneg (D : WeightedDesign m k) (firstLabel secondLabel probeLabel : Fin m)
    (hfirstNonneg : 0 ≤ gapExcessOf D firstLabel)
    (hsecondNonneg : 0 ≤ gapExcessOf D secondLabel)
    (hpairNonneg : 0 ≤ pairGapExcessOf D firstLabel secondLabel) :
    0 ≤ depthForm D firstLabel secondLabel probeLabel := by
  rw [pairGapExcessOf] at hpairNonneg
  rw [depthForm]
  exact adjugateForm_nonneg _ _ _ _ _ hfirstNonneg hsecondNonneg hpairNonneg

/-- A pair is **live** when both its atoms are heavy and its two-by-two gap minor
is strictly positive -- exactly Sylvester's criterion for the two-by-two gap Gram
`[[h_i, p], [p, h_j]]` to be positive definite. -/
def IsLivePair (D : WeightedDesign m k) (firstLabel secondLabel : Fin m) : Prop :=
  0 < gapExcessOf D firstLabel ∧ 0 < gapExcessOf D secondLabel
    ∧ 0 < pairGapExcessOf D firstLabel secondLabel

/-- **The kernel of the depth form at a live pair** is exactly the common
orthogonal of the pair.  So the depth form is a positive definite reading of the
third atom modulo the cross axis, and "depth zero" means "sits on the axis". -/
theorem depthForm_eq_zero_iff_of_isLivePair (D : WeightedDesign m k)
    {firstLabel secondLabel : Fin m} (hlive : IsLivePair D firstLabel secondLabel)
    (probeLabel : Fin m) :
    depthForm D firstLabel secondLabel probeLabel = 0
      ↔ (gapPairingOf D firstLabel probeLabel = 0
          ∧ gapPairingOf D secondLabel probeLabel = 0) := by
  obtain ⟨-, hsecondPos, hpairPos⟩ := hlive
  rw [pairGapExcessOf] at hpairPos
  rw [depthForm]
  exact adjugateForm_eq_zero_iff _ _ _ _ _ hsecondPos hpairPos

/-- **The depth cap.**  The tie leg is nonnegative exactly when the pivot's depth
inside the pair is at most the pair's capacity. -/
theorem discriminantTie_nonneg_iff_depthForm_le (D : WeightedDesign m 3)
    (firstLabel secondLabel probeLabel : Fin m) :
    0 ≤ discriminantTie D probeLabel firstLabel secondLabel
      ↔ depthForm D firstLabel secondLabel probeLabel
          ≤ pairGapExcessOf D firstLabel secondLabel * heavyExcess D probeLabel := by
  rw [discriminantTie_eq_pairGapExcessOf_mul_heavyExcess_sub_depthForm]
  constructor <;> intro hbound <;> linarith

/-- **The depth floor**, the tie side of the same identity: the tie leg is
nonpositive exactly when the pivot sits at depth AT LEAST the pair's capacity.
On a tie every triple satisfies this at every reading. -/
theorem discriminantTie_nonpos_iff_le_depthForm (D : WeightedDesign m 3)
    (firstLabel secondLabel probeLabel : Fin m) :
    discriminantTie D probeLabel firstLabel secondLabel ≤ 0
      ↔ pairGapExcessOf D firstLabel secondLabel * heavyExcess D probeLabel
          ≤ depthForm D firstLabel secondLabel probeLabel := by
  rw [discriminantTie_eq_pairGapExcessOf_mul_heavyExcess_sub_depthForm]
  constructor <;> intro hbound <;> linarith

/-- **Domination, read as a depth cap.**  The landed narrowing
`Gtz.dominates_triple_iff_discriminantSystem` says domination at a heavy pivot is
the trace leg plus the tie leg; the tie leg IS the depth cap. -/
theorem dominates_triple_iff_depthCap (D : WeightedDesign m 3)
    {pivotLabel pairFirst pairSecond : Fin m} (hpivotFirst : pivotLabel ≠ pairFirst)
    (hpivotSecond : pivotLabel ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivotLabel)) :
    Dominates D {pivotLabel, pairFirst, pairSecond}
      ↔ (0 ≤ discriminantTrace D pivotLabel pairFirst pairSecond
          ∧ depthForm D pairFirst pairSecond pivotLabel
              ≤ pairGapExcessOf D pairFirst pairSecond * heavyExcess D pivotLabel) := by
  rw [dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
    hpivotHeavy, discriminantTie_nonneg_iff_depthForm_le]

/-! ## Part 4: live pairs strictly dominate on their cross-axis plane -/

/-- **The plane resolution**, nine variables, no hypotheses: the squared axis
length times the squared probe length splits into the axis component and the
adjugate form of the pair's Gram at the two projections.  With the probe planar
the first term drops and the identity computes the probe's length from its two
projections alone. -/
theorem crossAxisNorm_mul_dotProduct_self (leftVec rightVec probeVec : Fin 3 → ℝ) :
    (bracketNormal leftVec rightVec ⬝ᵥ bracketNormal leftVec rightVec) * (probeVec ⬝ᵥ probeVec)
      = (probeVec ⬝ᵥ bracketNormal leftVec rightVec) ^ 2
        + (rightVec ⬝ᵥ rightVec) * (leftVec ⬝ᵥ probeVec) ^ 2
        - 2 * (leftVec ⬝ᵥ rightVec) * (leftVec ⬝ᵥ probeVec) * (rightVec ⬝ᵥ probeVec)
        + (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ probeVec) ^ 2 := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **The plane expansion**, the vector form: every probe resolves along the axis
and the two atoms of the pair.  In particular a probe orthogonal to both atoms
lies ON the axis whenever the axis is nonzero. -/
theorem crossAxisNorm_smul_eq_planeResolution (leftVec rightVec probeVec : Fin 3 → ℝ) :
    (bracketNormal leftVec rightVec ⬝ᵥ bracketNormal leftVec rightVec) • probeVec
      = (probeVec ⬝ᵥ bracketNormal leftVec rightVec) • bracketNormal leftVec rightVec
        + ((rightVec ⬝ᵥ rightVec) * (leftVec ⬝ᵥ probeVec)
            - (leftVec ⬝ᵥ rightVec) * (rightVec ⬝ᵥ probeVec)) • leftVec
        + ((leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ probeVec)
            - (leftVec ⬝ᵥ rightVec) * (leftVec ⬝ᵥ probeVec)) • rightVec := by
  have hcoordSplit : ∀ coordIndex : Fin 3,
      coordIndex = 0 ∨ coordIndex = 1 ∨ coordIndex = 2 := by decide
  funext coordIndex
  rcases hcoordSplit coordIndex with rfl | rfl | rfl <;>
    · simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring

/-- **The common orthogonal of a nondegenerate pair is the axis.**  Together with
`Gtz.depthForm_eq_zero_iff_of_isLivePair` this identifies the kernel of the depth
form with the span of the cross axis. -/
theorem smul_eq_smul_crossAxis_of_orthogonal_pair (leftVec rightVec probeVec : Fin 3 → ℝ)
    (hleftOrth : leftVec ⬝ᵥ probeVec = 0) (hrightOrth : rightVec ⬝ᵥ probeVec = 0) :
    (bracketNormal leftVec rightVec ⬝ᵥ bracketNormal leftVec rightVec) • probeVec
      = (probeVec ⬝ᵥ bracketNormal leftVec rightVec) • bracketNormal leftVec rightVec := by
  rw [crossAxisNorm_smul_eq_planeResolution, hleftOrth, hrightOrth]
  simp

/-- **The kernel of the depth form IS the axis line, forward half.**  At a live
pair an atom of depth zero is pinned onto the cross axis.  Stated scaled by the
axis budget so no division appears; the budget is positive at a live pair
(`Gtz.one_lt_crossAxisBudget_of_isLivePair`). -/
theorem crossAxisBudget_smul_atom_eq_of_depthForm_eq_zero (D : WeightedDesign m 3)
    {firstLabel secondLabel probeLabel : Fin m}
    (hlive : IsLivePair D firstLabel secondLabel)
    (hdepthZero : depthForm D firstLabel secondLabel probeLabel = 0) :
    crossAxisBudget D firstLabel secondLabel • D.atom probeLabel
      = atomBracket D firstLabel secondLabel probeLabel
        • crossAxis D firstLabel secondLabel := by
  obtain ⟨hfirstOrth, hsecondOrth⟩ :=
    (depthForm_eq_zero_iff_of_isLivePair D hlive probeLabel).mp hdepthZero
  rw [gapPairingOf] at hfirstOrth hsecondOrth
  have hbudgetRead : crossAxisBudget D firstLabel secondLabel
      = bracketNormal (D.atom firstLabel) (D.atom secondLabel)
        ⬝ᵥ bracketNormal (D.atom firstLabel) (D.atom secondLabel) := by
    rw [← crossAxis_dotProduct_self, crossAxis]
  have hbracketRead : atomBracket D firstLabel secondLabel probeLabel
      = D.atom probeLabel ⬝ᵥ bracketNormal (D.atom firstLabel) (D.atom secondLabel) := by
    rw [← atom_dotProduct_crossAxis, crossAxis]
  rw [hbudgetRead, hbracketRead, crossAxis]
  exact smul_eq_smul_crossAxis_of_orthogonal_pair _ _ _ hfirstOrth hsecondOrth

/-- **The kernel of the depth form IS the axis line, backward half.**  Any atom
parallel to the cross axis has depth zero -- and this half needs no liveness. -/
theorem depthForm_eq_zero_of_atom_eq_smul_crossAxis (D : WeightedDesign m 3)
    (firstLabel secondLabel probeLabel : Fin m) (scale : ℝ)
    (hparallel : D.atom probeLabel = scale • crossAxis D firstLabel secondLabel) :
    depthForm D firstLabel secondLabel probeLabel = 0 := by
  have haxisFirst : D.atom firstLabel ⬝ᵥ crossAxis D firstLabel secondLabel = 0 := by
    rw [atom_dotProduct_crossAxis, atomBracket_self_left]
  have haxisSecond : D.atom secondLabel ⬝ᵥ crossAxis D firstLabel secondLabel = 0 := by
    rw [atom_dotProduct_crossAxis, atomBracket_self_right]
  have hfirstOrth : gapPairingOf D firstLabel probeLabel = 0 := by
    rw [gapPairingOf, hparallel, dotProduct_smul, haxisFirst, smul_zero]
  have hsecondOrth : gapPairingOf D secondLabel probeLabel = 0 := by
    rw [gapPairingOf, hparallel, dotProduct_smul, haxisSecond, smul_zero]
  rw [depthForm, hfirstOrth, hsecondOrth]
  ring

/-- **THE PLANAR STRICTNESS CORE, design-free.**  Two heavy vectors whose gap
minor is positive strictly dominate on the plane orthogonal to their cross
product.  No orthonormal frame of the plane is chosen and the conclusion covers
every nonzero planar probe. -/
theorem dotProduct_self_lt_pair_of_planar (leftVec rightVec probeVec : Fin 3 → ℝ)
    (hleftHeavy : 1 < leftVec ⬝ᵥ leftVec) (hrightHeavy : 1 < rightVec ⬝ᵥ rightVec)
    (hminorPos : 0 < ((leftVec ⬝ᵥ leftVec) - 1) * ((rightVec ⬝ᵥ rightVec) - 1)
      - (leftVec ⬝ᵥ rightVec) ^ 2)
    (hplanar : probeVec ⬝ᵥ bracketNormal leftVec rightVec = 0)
    (hprobeNe : probeVec ≠ 0) :
    probeVec ⬝ᵥ probeVec < (leftVec ⬝ᵥ probeVec) ^ 2 + (rightVec ⬝ᵥ probeVec) ^ 2 := by
  have hbudgetExpand : (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2
      = (((leftVec ⬝ᵥ leftVec) - 1) * ((rightVec ⬝ᵥ rightVec) - 1)
            - (leftVec ⬝ᵥ rightVec) ^ 2)
        + ((leftVec ⬝ᵥ leftVec) - 1) + ((rightVec ⬝ᵥ rightVec) - 1) + 1 := by ring
  have hbudgetPos : 0 < (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec)
      - (leftVec ⬝ᵥ rightVec) ^ 2 := by
    rw [hbudgetExpand]; linarith
  have hresolve := crossAxisNorm_mul_dotProduct_self leftVec rightVec probeVec
  rw [hplanar, bracketNormal_self_dotProduct] at hresolve
  have hnotBothZero : ¬ ((leftVec ⬝ᵥ probeVec) = 0 ∧ (rightVec ⬝ᵥ probeVec) = 0) := by
    rintro ⟨hleftZero, hrightZero⟩
    rw [hleftZero, hrightZero] at hresolve
    have hbudgetTimesSelf : ((leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec)
        - (leftVec ⬝ᵥ rightVec) ^ 2) * (probeVec ⬝ᵥ probeVec) = 0 := by
      rw [hresolve]; ring
    rcases mul_eq_zero.mp hbudgetTimesSelf with hbudgetZero | hselfZero
    · exact absurd hbudgetZero (ne_of_gt hbudgetPos)
    · exact hprobeNe (eq_zero_of_dotProduct_self_eq_zero hselfZero)
  have hcompressed : 0 < ((((leftVec ⬝ᵥ leftVec) - 1) * ((rightVec ⬝ᵥ rightVec) - 1)
          - (leftVec ⬝ᵥ rightVec) ^ 2) + ((leftVec ⬝ᵥ leftVec) - 1)) * (leftVec ⬝ᵥ probeVec) ^ 2
      + 2 * (leftVec ⬝ᵥ rightVec) * (leftVec ⬝ᵥ probeVec) * (rightVec ⬝ᵥ probeVec)
      + ((((leftVec ⬝ᵥ leftVec) - 1) * ((rightVec ⬝ᵥ rightVec) - 1)
          - (leftVec ⬝ᵥ rightVec) ^ 2) + ((rightVec ⬝ᵥ rightVec) - 1))
        * (rightVec ⬝ᵥ probeVec) ^ 2 := by
    refine twoByTwoForm_pos_of_leadingPos_of_detPos _ _ _ _ _ (by linarith) ?_ hnotBothZero
    have hdetIdentity : ((((leftVec ⬝ᵥ leftVec) - 1) * ((rightVec ⬝ᵥ rightVec) - 1)
            - (leftVec ⬝ᵥ rightVec) ^ 2) + ((leftVec ⬝ᵥ leftVec) - 1))
          * ((((leftVec ⬝ᵥ leftVec) - 1) * ((rightVec ⬝ᵥ rightVec) - 1)
            - (leftVec ⬝ᵥ rightVec) ^ 2) + ((rightVec ⬝ᵥ rightVec) - 1))
          - (leftVec ⬝ᵥ rightVec) ^ 2
        = (((leftVec ⬝ᵥ leftVec) - 1) * ((rightVec ⬝ᵥ rightVec) - 1)
            - (leftVec ⬝ᵥ rightVec) ^ 2)
          * ((leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2) := by
      ring
    rw [hdetIdentity]
    exact mul_pos hminorPos hbudgetPos
  have hscaled : ((leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2)
        * (probeVec ⬝ᵥ probeVec)
      < ((leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec) - (leftVec ⬝ᵥ rightVec) ^ 2)
        * ((leftVec ⬝ᵥ probeVec) ^ 2 + (rightVec ⬝ᵥ probeVec) ^ 2) := by
    rw [hresolve]
    nlinarith [hcompressed]
  exact lt_of_mul_lt_mul_left hscaled hbudgetPos.le

/-- **TARGET: LIVE PAIRS DOMINATE THEIR PLANE.**  A live pair of a rank-three
design strictly dominates on the plane orthogonal to its cross axis.  Frame-free:
the statement mentions only the design's own cross axis, and quantifies over
every nonzero planar probe. -/
theorem dotProduct_self_lt_pair_of_isLivePair (D : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hlive : IsLivePair D firstLabel secondLabel)
    {probeVec : Fin 3 → ℝ}
    (hplanar : probeVec ⬝ᵥ crossAxis D firstLabel secondLabel = 0)
    (hprobeNe : probeVec ≠ 0) :
    probeVec ⬝ᵥ probeVec
      < (D.atom firstLabel ⬝ᵥ probeVec) ^ 2 + (D.atom secondLabel ⬝ᵥ probeVec) ^ 2 := by
  obtain ⟨hfirstPos, hsecondPos, hpairPos⟩ := hlive
  rw [gapExcessOf, leverageOf_eq_dotProduct] at hfirstPos hsecondPos
  rw [pairGapExcessOf, gapExcessOf, gapExcessOf, gapPairingOf, leverageOf_eq_dotProduct,
    leverageOf_eq_dotProduct] at hpairPos
  rw [crossAxis] at hplanar
  exact dotProduct_self_lt_pair_of_planar _ _ _ (by linarith) (by linarith) hpairPos
    hplanar hprobeNe

/-- The same statement as a strict quadratic-form inequality for the pair's atom
sum: the gap `S_{i,j} - I` is strictly positive on the cross-axis plane. -/
theorem pos_gapForm_pair_of_isLivePair (D : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hlive : IsLivePair D firstLabel secondLabel)
    (hdistinct : firstLabel ≠ secondLabel) {probeVec : Fin 3 → ℝ}
    (hplanar : probeVec ⬝ᵥ crossAxis D firstLabel secondLabel = 0)
    (hprobeNe : probeVec ≠ 0) :
    0 < probeVec ⬝ᵥ ((subsetSum D {firstLabel, secondLabel} - 1) *ᵥ probeVec) := by
  have hpairForm := dotProduct_subsetSum_mulVec_of_finset D
    ({firstLabel, secondLabel} : Finset (Fin m)) probeVec
  rw [Finset.sum_pair hdistinct] at hpairForm
  have hstrict := dotProduct_self_lt_pair_of_isLivePair D hlive hplanar hprobeNe
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hpairForm]
  linarith

/-- A live pair has axis budget strictly above one, so its cross axis is a
genuine direction. -/
theorem one_lt_crossAxisBudget_of_isLivePair (D : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hlive : IsLivePair D firstLabel secondLabel) :
    1 < crossAxisBudget D firstLabel secondLabel := by
  obtain ⟨hfirstPos, hsecondPos, hpairPos⟩ := hlive
  rw [crossAxisBudget_eq_pairGapExcessOf_add]
  linarith

theorem crossAxis_ne_zero_of_isLivePair (D : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hlive : IsLivePair D firstLabel secondLabel) :
    crossAxis D firstLabel secondLabel ≠ 0 := by
  intro haxisZero
  have hbudget := one_lt_crossAxisBudget_of_isLivePair D hlive
  rw [← crossAxis_dotProduct_self, haxisZero, dotProduct_zero] at hbudget
  linarith

/-- **A live pair is never coplanar with the rest of the design.**  Combining the
axis budget bound with the cross-axis Parseval: some atom outside a live pair has
a nonvanishing bracket against it. -/
theorem exists_offPair_atomBracket_ne_zero_of_isLivePair (D : WeightedDesign m 3)
    {firstLabel secondLabel : Fin m} (hlive : IsLivePair D firstLabel secondLabel) :
    ∃ probeLabel ∈ ({firstLabel, secondLabel} : Finset (Fin m))ᶜ,
      atomBracket D firstLabel secondLabel probeLabel ≠ 0 :=
  exists_offPair_atomBracket_ne_zero_of_crossAxisBudget_pos D
    (by linarith [one_lt_crossAxisBudget_of_isLivePair D hlive])

/-! ## Part 5: the statements are not vacuous

The regular tetrahedron is the campaign's hardest small fixture -- it IS a tie --
and every one of its pairs is live.  So liveness is not an empty predicate, the
depth cap is attained with equality there, and the planar strictness above says
that a design which ties in three dimensions still dominates strictly in every
cross-axis plane. -/

/-- Every distinct pair of tetrahedron atoms pairs to `-1`. -/
theorem tetraDesign_atomPairing_of_distinct {firstLabel secondLabel : Fin 4}
    (hdistinct : firstLabel ≠ secondLabel) :
    atomPairing tetraDesign firstLabel secondLabel = -1 := by
  fin_cases firstLabel <;> fin_cases secondLabel <;>
    simp_all [atomPairing, tetraDesign, tetraAtom, dotProduct, Fin.sum_univ_three]

/-- The tetrahedron's pair minor is `3` at every distinct pair. -/
theorem tetraDesign_pairGapExcessOf {firstLabel secondLabel : Fin 4}
    (hdistinct : firstLabel ≠ secondLabel) :
    pairGapExcessOf tetraDesign firstLabel secondLabel = 3 := by
  rw [pairGapExcessOf, gapExcessOf_eq_heavyExcess, gapExcessOf_eq_heavyExcess,
    gapPairingOf_eq_atomPairing, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_atomPairing_of_distinct hdistinct]
  norm_num

/-- **Every tetrahedron pair is live.** -/
theorem tetraDesign_isLivePair {firstLabel secondLabel : Fin 4}
    (hdistinct : firstLabel ≠ secondLabel) :
    IsLivePair tetraDesign firstLabel secondLabel := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gapExcessOf_eq_heavyExcess, tetraDesign_heavyExcess]; norm_num
  · rw [gapExcessOf_eq_heavyExcess, tetraDesign_heavyExcess]; norm_num
  · rw [tetraDesign_pairGapExcessOf hdistinct]; norm_num

/-- **The tetrahedron's axis budget is `8`.**  By the cross-axis Parseval the two
atoms outside any pair carry all of it. -/
theorem tetraDesign_crossAxisBudget {firstLabel secondLabel : Fin 4}
    (hdistinct : firstLabel ≠ secondLabel) :
    crossAxisBudget tetraDesign firstLabel secondLabel = 8 := by
  rw [crossAxisBudget, tetraDesign_leverage, tetraDesign_leverage,
    tetraDesign_atomPairing_of_distinct hdistinct]
  norm_num

/-- The cross-axis Parseval, instantiated: at the tetrahedron the two off-pair
atoms carry a budget of `8`. -/
theorem tetraDesign_sum_offPair_weight_mul_atomBracket_sq {firstLabel secondLabel : Fin 4}
    (hdistinct : firstLabel ≠ secondLabel) :
    ∑ probeLabel ∈ ({firstLabel, secondLabel} : Finset (Fin 4))ᶜ,
        tetraDesign.weight probeLabel
          * atomBracket tetraDesign firstLabel secondLabel probeLabel ^ 2 = 8 := by
  rw [sum_offPair_weight_mul_atomBracket_sq, tetraDesign_crossAxisBudget hdistinct]

/-- **The depth cap is ATTAINED at the tetrahedron**: depth `6` against capacity
`pairMinor * pivotExcess = 3 * 2 = 6`, which is `Gtz.tetraDesign_discriminantTie`
read through the split. -/
theorem tetraDesign_depthForm_eq_capacity :
    depthForm tetraDesign 1 2 0
      = pairGapExcessOf tetraDesign 1 2 * heavyExcess tetraDesign 0 := by
  have hsplit := discriminantTie_eq_pairGapExcessOf_mul_heavyExcess_sub_depthForm
    tetraDesign 1 2 0
  rw [tetraDesign_discriminantTie] at hsplit
  linarith

/-- **A tie in space that is strict in a cross-axis plane.**  The tetrahedron is
a tie, yet by liveness its pair `{0,1}` strictly dominates on the plane
orthogonal to that pair's cross axis.  The pair is chosen only for concreteness:
`Gtz.tetraDesign_isLivePair` covers every distinct pair, so the same conclusion
follows at each of the six. -/
theorem tetraDesign_isTie_and_pos_gapForm_pair {probeVec : Fin 3 → ℝ}
    (hplanar : probeVec ⬝ᵥ crossAxis tetraDesign 0 1 = 0) (hprobeNe : probeVec ≠ 0) :
    IsTie tetraDesign
      ∧ 0 < probeVec ⬝ᵥ ((subsetSum tetraDesign {0, 1} - 1) *ᵥ probeVec) :=
  ⟨tetraDesign_isTie,
    pos_gapForm_pair_of_isLivePair tetraDesign (tetraDesign_isLivePair (by decide))
      (by decide) hplanar hprobeNe⟩

end Gtz
