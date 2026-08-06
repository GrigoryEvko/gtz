/-!
# The M(K4) collar atlas kernel-replay checker (GTZ p29 pilot lane)

Self-contained Lean 4 module -- no imports.  The verified-checker half of
the kernel-replay architecture for the rung-15 barycentric atlas: a chart
certificate (an adaptive dyadic cover tree with per-leaf window witnesses,
emitted by `adaptive_emitter.c`) is replayed entirely inside the kernel,
and the ONE generic soundness theorem `checkChart_sound` turns
`checkChart data = true` (a single `decide`) into the pointwise window
sign package at EVERY rational point of the half-open chart cube
`(0,1]^4`.

Design (the homogenizer-variable trick): every emitted polynomial is
HOMOGENEOUS in five variables `(h, r2, r3, r4, r5)` -- the chart cores of
`chart_bary_build.py`, homogenized by the denominator variable `h`.  The
sign of a chart core at the rational point `(n1/d, .., n4/d)` is then the
sign of the plain integer evaluation `polyEval p d n1 n2 n3 n4`, and
- the engine's interval corner bound,
- the grouped (graded) bound at zero-touching faces, and
- the upper-face shift variants `r -> 1 - q`
all become ordinary polynomial-evaluation lemmas with no degree
bookkeeping: reflection is the homogeneous substitution `r_v -> h - r_v`,
and the reflected point is `n_v -> d - n_v`.

Strictness discipline (sharper than `chart_bary_engine3.c`, whose grouped
bound at an upper face is only limit-sound at tie points `r_v = 1`):
- the plain corner bound and a grouped bound WITH a zero-key group are
  strict at every rational point of the closed box;
- a grouped bound whose zero-touching variables are all lower (unshifted)
  coordinates is strict on the `(0,1]^4` domain;
- a grouped bound with no zero-key group touching a shifted variable is
  only WEAK evidence (a certified direction, `>= 0` or `<= 0`), accepted
  in beta slots only, where the boundary-ray semantics needs direction,
  not strictness.

Nothing outside this file is trusted: the certificate data (cores,
variants, thresholds, candidates, cover tree) is untrusted input -- wrong
data makes `checkChart` return `false`, never an unsound theorem.  The
shift variants are DATA but are verified inside `checkChart` against a
Lean-computed reflection via the canonical-form bridge.
-/

namespace Gtz.CollarReplay

set_option autoImplicit false
set_option maxRecDepth 65536

/-! ## The five-variable sparse polynomial layer -/

/-- Exponent vector of a monomial in (h, r2, r3, r4, r5); `expDen` is the
homogenizer (denominator) variable. -/
structure Monomial where
  expDen : Nat
  expOne : Nat
  expTwo : Nat
  expThree : Nat
  expFour : Nat
deriving DecidableEq

/-- One signed term of a sparse polynomial. -/
structure Term where
  monomial : Monomial
  coeff : Int
deriving DecidableEq

abbrev Poly := List Term

/-- Term literal helper. -/
def tm (expDen expOne expTwo expThree expFour : Nat) (coeff : Int) : Term :=
  ⟨⟨expDen, expOne, expTwo, expThree, expFour⟩, coeff⟩

/-- Structural power, kept local for zero dependencies. -/
def intPow (base : Int) : Nat → Int
  | 0 => 1
  | n + 1 => intPow base n * base

theorem intPow_add (base : Int) (m n : Nat) :
    intPow base (m + n) = intPow base m * intPow base n := by
  induction n with
  | zero => simp [intPow]
  | succ n ih =>
      show intPow base (m + n + 1) = _
      rw [intPow, ih, intPow, Int.mul_assoc]

theorem intPow_nonneg {base : Int} (baseNonneg : 0 ≤ base) (n : Nat) :
    0 ≤ intPow base n := by
  induction n with
  | zero => exact Int.le_of_lt Int.zero_lt_one
  | succ n ih => exact Int.mul_nonneg ih baseNonneg

theorem intPow_pos {base : Int} (basePos : 0 < base) (n : Nat) :
    0 < intPow base n := by
  induction n with
  | zero => exact Int.zero_lt_one
  | succ n ih => exact Int.mul_pos ih basePos

theorem intPow_le_intPow {small large : Int} (smallNonneg : 0 ≤ small)
    (smallLe : small ≤ large) (n : Nat) :
    intPow small n ≤ intPow large n := by
  induction n with
  | zero => exact Int.le_refl 1
  | succ n ih =>
      have largeNonneg : 0 ≤ large := Int.le_trans smallNonneg smallLe
      have powSmallNonneg : 0 ≤ intPow small n := intPow_nonneg smallNonneg n
      calc intPow small n * small ≤ intPow small n * large :=
            Int.mul_le_mul_of_nonneg_left smallLe powSmallNonneg
        _ ≤ intPow large n * large :=
            Int.mul_le_mul_of_nonneg_right ih largeNonneg

theorem intPow_mul (baseA baseB : Int) (n : Nat) :
    intPow (baseA * baseB) n = intPow baseA n * intPow baseB n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show intPow (baseA * baseB) n * (baseA * baseB) = _
      rw [ih]
      show intPow baseA n * intPow baseB n * (baseA * baseB)
        = intPow baseA n * baseA * (intPow baseB n * baseB)
      rw [Int.mul_assoc, Int.mul_assoc]
      rw [Int.mul_left_comm (intPow baseB n) baseA baseB]

theorem square_nonneg (base : Int) : 0 ≤ base * base := by
  cases Int.le_total 0 base with
  | inl baseNonneg => exact Int.mul_nonneg baseNonneg baseNonneg
  | inr baseNonpos =>
      have negNonneg : 0 ≤ -base := Int.neg_nonneg.mpr baseNonpos
      have product : (0 : Int) ≤ -base * -base :=
        Int.mul_nonneg negNonneg negNonneg
      rw [Int.neg_mul_neg] at product
      exact product

/-- Even powers are nonnegative (used for even-multiplicity beta cores). -/
theorem intPow_even_nonneg (base : Int) (halfExp : Nat) :
    0 ≤ intPow base (halfExp * 2) := by
  induction halfExp with
  | zero => exact Int.le_of_lt Int.zero_lt_one
  | succ halfExp ih =>
      have expandExp : (halfExp + 1) * 2 = halfExp * 2 + 2 :=
        Nat.succ_mul halfExp 2
      have squareForm : intPow base 2 = base * base := by
        show intPow base 0 * base * base = base * base
        show (1 : Int) * base * base = base * base
        rw [Int.one_mul]
      rw [expandExp, intPow_add, squareForm]
      exact Int.mul_nonneg ih (square_nonneg base)

/-- Evaluation of one term at an integer point (den, one..four). -/
def termEval (t : Term) (den one two three four : Int) : Int :=
  t.coeff * intPow den t.monomial.expDen * intPow one t.monomial.expOne
    * intPow two t.monomial.expTwo * intPow three t.monomial.expThree
    * intPow four t.monomial.expFour

/-- Evaluation of a sparse polynomial. -/
def polyEval : Poly → Int → Int → Int → Int → Int → Int
  | [], _, _, _, _, _ => 0
  | t :: rest, den, one, two, three, four =>
      termEval t den one two three four
        + polyEval rest den one two three four

def polyAdd (p q : Poly) : Poly := p ++ q

def polyNeg (p : Poly) : Poly :=
  p.map fun t => ⟨t.monomial, -t.coeff⟩

def monomialMul (m n : Monomial) : Monomial :=
  ⟨m.expDen + n.expDen, m.expOne + n.expOne, m.expTwo + n.expTwo,
   m.expThree + n.expThree, m.expFour + n.expFour⟩

def termMul (s t : Term) : Term :=
  ⟨monomialMul s.monomial t.monomial, s.coeff * t.coeff⟩

def polyMulTerm (s : Term) (q : Poly) : Poly := q.map (termMul s)

def polyMul : Poly → Poly → Poly
  | [], _ => []
  | t :: rest, q => polyMulTerm t q ++ polyMul rest q

/-! ## Evaluation semantics (the payload lemmas, ported to five slots) -/

theorem polyEval_append (p q : Poly) (den one two three four : Int) :
    polyEval (p ++ q) den one two three four
      = polyEval p den one two three four
        + polyEval q den one two three four := by
  induction p with
  | nil => simp [polyEval]
  | cons head rest ih =>
      show termEval head den one two three four
            + polyEval (rest ++ q) den one two three four = _
      rw [ih, polyEval, Int.add_assoc]

theorem polyEval_neg (p : Poly) (den one two three four : Int) :
    polyEval (polyNeg p) den one two three four
      = -(polyEval p den one two three four) := by
  induction p with
  | nil => simp [polyEval, polyNeg]
  | cons head rest ih =>
      show termEval ⟨head.monomial, -head.coeff⟩ den one two three four
             + polyEval (polyNeg rest) den one two three four = _
      rw [ih, polyEval]
      show -head.coeff * intPow den head.monomial.expDen
             * intPow one head.monomial.expOne
             * intPow two head.monomial.expTwo
             * intPow three head.monomial.expThree
             * intPow four head.monomial.expFour
             + -(polyEval rest den one two three four) = _
      rw [termEval, Int.neg_add]
      simp [Int.neg_mul]

theorem termEval_termMul (s t : Term) (den one two three four : Int) :
    termEval (termMul s t) den one two three four
      = termEval s den one two three four
        * termEval t den one two three four := by
  unfold termEval termMul monomialMul
  simp only [intPow_add]
  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem polyEval_mulTerm (s : Term) (q : Poly)
    (den one two three four : Int) :
    polyEval (polyMulTerm s q) den one two three four
      = termEval s den one two three four
        * polyEval q den one two three four := by
  induction q with
  | nil => simp [polyEval, polyMulTerm]
  | cons head rest ih =>
      show termEval (termMul s head) den one two three four
             + polyEval (polyMulTerm s rest) den one two three four = _
      rw [ih, termEval_termMul, polyEval, Int.mul_add]

theorem polyEval_mul (p q : Poly) (den one two three four : Int) :
    polyEval (polyMul p q) den one two three four
      = polyEval p den one two three four
        * polyEval q den one two three four := by
  induction p with
  | nil => simp [polyEval, polyMul]
  | cons head rest ih =>
      show polyEval (polyMulTerm head q ++ polyMul rest q)
              den one two three four = _
      rw [polyEval_append, polyEval_mulTerm, ih, polyEval, Int.add_mul]

/-! ## Canonical form and the bridge -/

def monomialLtB (m n : Monomial) : Bool :=
  if m.expDen ≠ n.expDen then m.expDen < n.expDen
  else if m.expOne ≠ n.expOne then m.expOne < n.expOne
  else if m.expTwo ≠ n.expTwo then m.expTwo < n.expTwo
  else if m.expThree ≠ n.expThree then m.expThree < n.expThree
  else m.expFour < n.expFour

def insertTerm (t : Term) : Poly → Poly
  | [] => [t]
  | head :: rest =>
      if t.monomial = head.monomial then
        ⟨t.monomial, t.coeff + head.coeff⟩ :: rest
      else if monomialLtB t.monomial head.monomial then
        t :: head :: rest
      else
        head :: insertTerm t rest

def sortMerge : Poly → Poly
  | [] => []
  | t :: rest => insertTerm t (sortMerge rest)

def canon (p : Poly) : Poly :=
  (sortMerge p).filter fun t => t.coeff ≠ 0

theorem termEval_mergeCoeff (m : Monomial) (c d : Int)
    (den one two three four : Int) :
    termEval ⟨m, c + d⟩ den one two three four
      = termEval ⟨m, c⟩ den one two three four
        + termEval ⟨m, d⟩ den one two three four := by
  unfold termEval
  simp [Int.add_mul]

theorem polyEval_insertTerm (t : Term) (p : Poly)
    (den one two three four : Int) :
    polyEval (insertTerm t p) den one two three four
      = termEval t den one two three four
        + polyEval p den one two three four := by
  induction p with
  | nil => simp [insertTerm, polyEval]
  | cons head rest ih =>
      unfold insertTerm
      split
      · next monEq =>
          rw [polyEval, polyEval]
          rw [show t.monomial = head.monomial from monEq]
          rw [← Int.add_assoc]
          rw [termEval_mergeCoeff head.monomial t.coeff head.coeff]
          have coeffCast :
              termEval ⟨head.monomial, t.coeff⟩ den one two three four
                = termEval t den one two three four := by
            rw [← monEq]
          rw [coeffCast]
      · split
        · rw [polyEval, polyEval]
        · rw [polyEval, polyEval, ih, ← Int.add_assoc,
              Int.add_comm (termEval head den one two three four)
                (termEval t den one two three four), Int.add_assoc]

theorem polyEval_sortMerge (p : Poly) (den one two three four : Int) :
    polyEval (sortMerge p) den one two three four
      = polyEval p den one two three four := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
      show polyEval (insertTerm head (sortMerge rest)) den one two three four
        = _
      rw [polyEval_insertTerm, ih, polyEval]

theorem polyEval_filterZero (p : Poly) (den one two three four : Int) :
    polyEval (p.filter fun t => t.coeff ≠ 0) den one two three four
      = polyEval p den one two three four := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
      by_cases isZero : head.coeff = 0
      · have dropped :
            (head :: rest).filter (fun t => t.coeff ≠ 0)
              = rest.filter fun t => t.coeff ≠ 0 := by
          simp [List.filter, isZero]
        rw [dropped, ih, polyEval]
        have killed : termEval head den one two three four = 0 := by
          unfold termEval
          rw [isZero]
          simp
        rw [killed, Int.zero_add]
      · have kept :
            (head :: rest).filter (fun t => t.coeff ≠ 0)
              = head :: rest.filter fun t => t.coeff ≠ 0 := by
          simp [List.filter, isZero]
        rw [kept, polyEval, ih, polyEval]

theorem polyEval_canon (p : Poly) (den one two three four : Int) :
    polyEval (canon p) den one two three four
      = polyEval p den one two three four := by
  unfold canon
  rw [polyEval_filterZero, polyEval_sortMerge]

/-- THE BRIDGE: equal canonical forms give equal values everywhere. -/
theorem polyEval_eq_of_canon_eq (p q : Poly) (canonEq : canon p = canon q)
    (den one two three four : Int) :
    polyEval p den one two three four = polyEval q den one two three four := by
  rw [← polyEval_canon p, canonEq, polyEval_canon]

/-! ## Sign-algebra helpers -/

theorem mul_le_mul_of_nonpos_left {scaleFactor left right : Int}
    (compare : left ≤ right) (scaleNonpos : scaleFactor ≤ 0) :
    scaleFactor * right ≤ scaleFactor * left := by
  have negNonneg : 0 ≤ -scaleFactor := Int.neg_nonneg.mpr scaleNonpos
  have scaled : -scaleFactor * left ≤ -scaleFactor * right :=
    Int.mul_le_mul_of_nonneg_left compare negNonneg
  rw [Int.neg_mul, Int.neg_mul] at scaled
  omega

theorem pos_of_mul_pos_of_pos_right {left right : Int}
    (productPos : 0 < left * right) (rightPos : 0 < right) : 0 < left := by
  by_cases leftPos : 0 < left
  · exact leftPos
  · have leftNonpos : left ≤ 0 := by omega
    have productNonpos : left * right ≤ 0 * right :=
      Int.mul_le_mul_of_nonneg_right leftNonpos (Int.le_of_lt rightPos)
    rw [Int.zero_mul] at productNonpos
    omega

theorem mul_self_pos_of_ne_zero {value : Int} (valueNe : value ≠ 0) :
    0 < value * value := by
  cases Int.lt_or_lt_of_ne valueNe with
  | inl valueNeg =>
      have negPos : 0 < -value := by omega
      have product : 0 < -value * -value := Int.mul_pos negPos negPos
      rw [Int.neg_mul_neg] at product
      exact product
  | inr valuePos => exact Int.mul_pos valuePos valuePos

theorem intPow_two_mul (base : Int) (halfExp : Nat) :
    intPow base (halfExp * 2) = intPow (base * base) halfExp := by
  induction halfExp with
  | zero => rfl
  | succ halfExp ih =>
      have expandExp : (halfExp + 1) * 2 = halfExp * 2 + 2 :=
        Nat.succ_mul halfExp 2
      have squareForm : intPow base 2 = base * base := by
        show intPow base 0 * base * base = base * base
        show (1 : Int) * base * base = base * base
        rw [Int.one_mul]
      rw [expandExp, intPow_add, squareForm, ih]
      rfl

theorem intPow_even_pos {base : Int} (baseNe : base ≠ 0) (halfExp : Nat) :
    0 < intPow base (halfExp * 2) := by
  rw [intPow_two_mul]
  exact intPow_pos (mul_self_pos_of_ne_zero baseNe) halfExp

/-! ## Dyadic boxes and rational points

A point of the chart cube is a rational tuple `(n1/den, .., n4/den)`
given by integers with `1 <= den` and `1 <= n_v <= den` -- exactly the
rational points of the half-open cube `(0,1]^4`, the chart image of the
open weight simplex.  A box at scale exponent `k` has integer corner
coordinates over the grid `1/2^k`; membership is expressed by cleared
denominators. -/

structure Box where
  scaleExp : Nat
  lowOne : Int
  lowTwo : Int
  lowThree : Int
  lowFour : Int
  highOne : Int
  highTwo : Int
  highThree : Int
  highFour : Int
deriving DecidableEq

def boxScale (box : Box) : Int := intPow 2 box.scaleExp

def rootBox : Box := ⟨0, 0, 0, 0, 0, 1, 1, 1, 1⟩

/-- Membership of the rational point in the box, denominators cleared. -/
def PointLiesInBox (box : Box) (den one two three four : Int) : Prop :=
  box.lowOne * den ≤ one * boxScale box
    ∧ one * boxScale box ≤ box.highOne * den
    ∧ box.lowTwo * den ≤ two * boxScale box
    ∧ two * boxScale box ≤ box.highTwo * den
    ∧ box.lowThree * den ≤ three * boxScale box
    ∧ three * boxScale box ≤ box.highThree * den
    ∧ box.lowFour * den ≤ four * boxScale box
    ∧ four * boxScale box ≤ box.highFour * den

/-- The point domain: rational points of the half-open cube (0,1]^4. -/
def PointLiesInDomain (den one two three four : Int) : Prop :=
  1 ≤ den ∧ 1 ≤ one ∧ one ≤ den ∧ 1 ≤ two ∧ two ≤ den
    ∧ 1 ≤ three ∧ three ≤ den ∧ 1 ≤ four ∧ four ≤ den

theorem rootBox_covers {den one two three four : Int}
    (domain : PointLiesInDomain den one two three four) :
    PointLiesInBox rootBox den one two three four := by
  obtain ⟨denGe, oneGe, oneLe, twoGe, twoLe, threeGe, threeLe, fourGe,
    fourLe⟩ := domain
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rootBox, boxScale, intPow, Int.mul_one, Int.zero_mul] <;>
    omega

/-- Coordinate sanity checked at every leaf: nonnegative lows, highs
within the scale (so the reflected box has nonnegative lows). -/
def boxIsSane (box : Box) : Bool :=
  decide (0 ≤ box.lowOne) && decide (0 ≤ box.lowTwo)
    && decide (0 ≤ box.lowThree) && decide (0 ≤ box.lowFour)
    && decide (box.highOne ≤ boxScale box)
    && decide (box.highTwo ≤ boxScale box)
    && decide (box.highThree ≤ boxScale box)
    && decide (box.highFour ≤ boxScale box)

/-! ## The split rule (mirrors the emitter's; soundness needs only the
covering property, which holds for any midpoint) -/

def boxDouble (box : Box) : Box :=
  ⟨box.scaleExp + 1, box.lowOne * 2, box.lowTwo * 2, box.lowThree * 2,
   box.lowFour * 2, box.highOne * 2, box.highTwo * 2, box.highThree * 2,
   box.highFour * 2⟩

def boxSetLow (box : Box) (dim : Nat) (value : Int) : Box :=
  match dim with
  | 0 => { box with lowOne := value }
  | 1 => { box with lowTwo := value }
  | 2 => { box with lowThree := value }
  | _ => { box with lowFour := value }

def boxSetHigh (box : Box) (dim : Nat) (value : Int) : Box :=
  match dim with
  | 0 => { box with highOne := value }
  | 1 => { box with highTwo := value }
  | 2 => { box with highThree := value }
  | _ => { box with highFour := value }

def boxLowAt (box : Box) (dim : Nat) : Int :=
  match dim with
  | 0 => box.lowOne
  | 1 => box.lowTwo
  | 2 => box.lowThree
  | _ => box.lowFour

def boxHighAt (box : Box) (dim : Nat) : Int :=
  match dim with
  | 0 => box.highOne
  | 1 => box.highTwo
  | 2 => box.highThree
  | _ => box.highFour

def boxMidpoint (box : Box) (dim : Nat) : Int :=
  boxLowAt box dim + (boxHighAt box dim - boxLowAt box dim) / 2

def splitBox (box : Box) (dim : Nat) : Box × Box :=
  if (boxHighAt box dim - boxLowAt box dim) % 2 == 0 then
    (boxSetHigh box dim (boxMidpoint box dim),
     boxSetLow box dim (boxMidpoint box dim))
  else
    (boxSetHigh (boxDouble box) dim (boxMidpoint (boxDouble box) dim),
     boxSetLow (boxDouble box) dim (boxMidpoint (boxDouble box) dim))

theorem double_side_low {lowValue scale den coord : Int}
    (side : lowValue * den ≤ coord * scale) :
    lowValue * 2 * den ≤ coord * (scale * 2) := by
  have leftForm : lowValue * 2 * den = lowValue * den * 2 := by
    rw [Int.mul_assoc, Int.mul_comm 2 den, ← Int.mul_assoc]
  have rightForm : coord * (scale * 2) = coord * scale * 2 :=
    (Int.mul_assoc coord scale 2).symm
  omega

theorem double_side_high {highValue scale den coord : Int}
    (side : coord * scale ≤ highValue * den) :
    coord * (scale * 2) ≤ highValue * 2 * den := by
  have leftForm : highValue * 2 * den = highValue * den * 2 := by
    rw [Int.mul_assoc, Int.mul_comm 2 den, ← Int.mul_assoc]
  have rightForm : coord * (scale * 2) = coord * scale * 2 :=
    (Int.mul_assoc coord scale 2).symm
  omega

theorem pointLiesInBox_double {box : Box} {den one two three four : Int}
    (membership : PointLiesInBox box den one two three four) :
    PointLiesInBox (boxDouble box) den one two three four := by
  obtain ⟨lowOne, highOne, lowTwo, highTwo, lowThree, highThree, lowFour,
    highFour⟩ := membership
  exact ⟨double_side_low lowOne, double_side_high highOne,
    double_side_low lowTwo, double_side_high highTwo,
    double_side_low lowThree, double_side_high highThree,
    double_side_low lowFour, double_side_high highFour⟩

theorem pointLiesInBox_setMid {box : Box} {dim : Nat} {mid : Int}
    {den one two three four : Int}
    (membership : PointLiesInBox box den one two three four) :
    PointLiesInBox (boxSetHigh box dim mid) den one two three four
      ∨ PointLiesInBox (boxSetLow box dim mid) den one two three four := by
  obtain ⟨lowOne, highOne, lowTwo, highTwo, lowThree, highThree, lowFour,
    highFour⟩ := membership
  match dim with
  | 0 =>
      cases Int.le_total (one * boxScale box) (mid * den) with
      | inl leftSide =>
          exact Or.inl ⟨lowOne, leftSide, lowTwo, highTwo, lowThree,
            highThree, lowFour, highFour⟩
      | inr rightSide =>
          exact Or.inr ⟨rightSide, highOne, lowTwo, highTwo, lowThree,
            highThree, lowFour, highFour⟩
  | 1 =>
      cases Int.le_total (two * boxScale box) (mid * den) with
      | inl leftSide =>
          exact Or.inl ⟨lowOne, highOne, lowTwo, leftSide, lowThree,
            highThree, lowFour, highFour⟩
      | inr rightSide =>
          exact Or.inr ⟨lowOne, highOne, rightSide, highTwo, lowThree,
            highThree, lowFour, highFour⟩
  | 2 =>
      cases Int.le_total (three * boxScale box) (mid * den) with
      | inl leftSide =>
          exact Or.inl ⟨lowOne, highOne, lowTwo, highTwo, lowThree,
            leftSide, lowFour, highFour⟩
      | inr rightSide =>
          exact Or.inr ⟨lowOne, highOne, lowTwo, highTwo, rightSide,
            highThree, lowFour, highFour⟩
  | (n + 3) =>
      cases Int.le_total (four * boxScale box) (mid * den) with
      | inl leftSide =>
          exact Or.inl ⟨lowOne, highOne, lowTwo, highTwo, lowThree,
            highThree, lowFour, leftSide⟩
      | inr rightSide =>
          exact Or.inr ⟨lowOne, highOne, lowTwo, highTwo, lowThree,
            highThree, rightSide, highFour⟩

theorem splitBox_covers {box : Box} {dim : Nat} {den one two three four : Int}
    (membership : PointLiesInBox box den one two three four) :
    PointLiesInBox (splitBox box dim).fst den one two three four
      ∨ PointLiesInBox (splitBox box dim).snd den one two three four := by
  unfold splitBox
  split
  · exact pointLiesInBox_setMid membership
  · exact pointLiesInBox_setMid (pointLiesInBox_double membership)

/-! ## The corner bound (the engine's `boundSign` low side, verified)

For a HOMOGENEOUS five-variable polynomial and a rational point of the
box, the term-wise corner sum bounds the (denominator-cleared) value:
`lowBound p box * den^deg <= polyEval p den n * scale^deg`.  Strict
positivity of `lowBound` therefore forces strict positivity of the value
at every rational point of the box.  The high side is obtained through
`polyNeg`, exactly matching the engine's decision arithmetic. -/

def termDegree (t : Term) : Nat :=
  t.monomial.expDen + t.monomial.expOne + t.monomial.expTwo
    + t.monomial.expThree + t.monomial.expFour

def isHomogeneousOfDegree (p : Poly) (deg : Nat) : Bool :=
  p.all fun t => termDegree t == deg

def polyLeadDegree : Poly → Nat
  | [] => 0
  | t :: _ => termDegree t

def cornerOne (t : Term) (box : Box) : Int :=
  if 0 ≤ t.coeff then box.lowOne else box.highOne
def cornerTwo (t : Term) (box : Box) : Int :=
  if 0 ≤ t.coeff then box.lowTwo else box.highTwo
def cornerThree (t : Term) (box : Box) : Int :=
  if 0 ≤ t.coeff then box.lowThree else box.highThree
def cornerFour (t : Term) (box : Box) : Int :=
  if 0 ≤ t.coeff then box.lowFour else box.highFour

def termLowCorner (t : Term) (box : Box) : Int :=
  t.coeff * intPow (boxScale box) t.monomial.expDen
    * intPow (cornerOne t box) t.monomial.expOne
    * intPow (cornerTwo t box) t.monomial.expTwo
    * intPow (cornerThree t box) t.monomial.expThree
    * intPow (cornerFour t box) t.monomial.expFour

def lowBound : Poly → Box → Int
  | [], _ => 0
  | t :: rest, box => termLowCorner t box + lowBound rest box

theorem mul_le_mul_of_nonneg_pair {leftLow leftHigh rightLow rightHigh : Int}
    (leftNonneg : 0 ≤ leftLow) (leftLe : leftLow ≤ leftHigh)
    (rightNonneg : 0 ≤ rightLow) (rightLe : rightLow ≤ rightHigh) :
    leftLow * rightLow ≤ leftHigh * rightHigh := by
  have firstStep : leftLow * rightLow ≤ leftHigh * rightLow :=
    Int.mul_le_mul_of_nonneg_right leftLe rightNonneg
  have secondStep : leftHigh * rightLow ≤ leftHigh * rightHigh :=
    Int.mul_le_mul_of_nonneg_left rightLe (Int.le_trans leftNonneg leftLe)
  omega

/-- Product of four power factors, monotone from per-slot bounds. -/
theorem prodFour_le {lowA lowB lowC lowD highA highB highC highD : Int}
    {expA expB expC expD : Nat}
    (nonnegA : 0 ≤ lowA) (leA : lowA ≤ highA)
    (nonnegB : 0 ≤ lowB) (leB : lowB ≤ highB)
    (nonnegC : 0 ≤ lowC) (leC : lowC ≤ highC)
    (nonnegD : 0 ≤ lowD) (leD : lowD ≤ highD) :
    intPow lowA expA * intPow lowB expB * intPow lowC expC * intPow lowD expD
      ≤ intPow highA expA * intPow highB expB * intPow highC expC
        * intPow highD expD := by
  have powA := intPow_le_intPow nonnegA leA expA
  have powB := intPow_le_intPow nonnegB leB expB
  have powC := intPow_le_intPow nonnegC leC expC
  have powD := intPow_le_intPow nonnegD leD expD
  have nnA := intPow_nonneg nonnegA expA
  have nnB := intPow_nonneg nonnegB expB
  have nnC := intPow_nonneg nonnegC expC
  have nnD := intPow_nonneg nonnegD expD
  have stepAB := mul_le_mul_of_nonneg_pair nnA powA nnB powB
  have nnAB := Int.mul_nonneg nnA nnB
  have stepABC := mul_le_mul_of_nonneg_pair nnAB stepAB nnC powC
  have nnABC := Int.mul_nonneg nnAB nnC
  exact mul_le_mul_of_nonneg_pair nnABC stepABC nnD powD

/-- Nonnegativity of the four-fold power product. -/
theorem prodFour_nonneg {baseA baseB baseC baseD : Int}
    {expA expB expC expD : Nat}
    (nonnegA : 0 ≤ baseA) (nonnegB : 0 ≤ baseB) (nonnegC : 0 ≤ baseC)
    (nonnegD : 0 ≤ baseD) :
    0 ≤ intPow baseA expA * intPow baseB expB * intPow baseC expC
      * intPow baseD expD :=
  Int.mul_nonneg (Int.mul_nonneg (Int.mul_nonneg
    (intPow_nonneg nonnegA expA) (intPow_nonneg nonnegB expB))
    (intPow_nonneg nonnegC expC)) (intPow_nonneg nonnegD expD)

/-- The crux per-term inequality of the corner bound. -/
theorem termLowCorner_scaled_le (t : Term) (box : Box)
    (den one two three four : Int)
    (denNonneg : 0 ≤ den)
    (lowsNonneg : 0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree
      ∧ 0 ≤ box.lowFour)
    (pointNonneg : 0 ≤ one ∧ 0 ≤ two ∧ 0 ≤ three ∧ 0 ≤ four)
    (membership : PointLiesInBox box den one two three four) :
    termLowCorner t box * intPow den (termDegree t)
      ≤ termEval t den one two three four
        * intPow (boxScale box) (termDegree t) := by
  obtain ⟨lowOneSide, highOneSide, lowTwoSide, highTwoSide, lowThreeSide,
    highThreeSide, lowFourSide, highFourSide⟩ := membership
  obtain ⟨lowOneNN, lowTwoNN, lowThreeNN, lowFourNN⟩ := lowsNonneg
  obtain ⟨oneNN, twoNN, threeNN, fourNN⟩ := pointNonneg
  have scaleNonneg : 0 ≤ boxScale box :=
    intPow_nonneg (by omega) box.scaleExp
  have commonNonneg : 0 ≤ intPow (boxScale box) t.monomial.expDen
      * intPow den t.monomial.expDen :=
    Int.mul_nonneg (intPow_nonneg scaleNonneg t.monomial.expDen)
      (intPow_nonneg denNonneg t.monomial.expDen)
  have leftForm : termLowCorner t box * intPow den (termDegree t)
      = (intPow (boxScale box) t.monomial.expDen
          * intPow den t.monomial.expDen)
        * (t.coeff
          * (intPow (cornerOne t box * den) t.monomial.expOne
            * intPow (cornerTwo t box * den) t.monomial.expTwo
            * intPow (cornerThree t box * den) t.monomial.expThree
            * intPow (cornerFour t box * den) t.monomial.expFour)) := by
    unfold termLowCorner termDegree
    simp only [intPow_add, intPow_mul]
    simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have rightForm : termEval t den one two three four
      * intPow (boxScale box) (termDegree t)
      = (intPow (boxScale box) t.monomial.expDen
          * intPow den t.monomial.expDen)
        * (t.coeff
          * (intPow (one * boxScale box) t.monomial.expOne
            * intPow (two * boxScale box) t.monomial.expTwo
            * intPow (three * boxScale box) t.monomial.expThree
            * intPow (four * boxScale box) t.monomial.expFour)) := by
    unfold termEval termDegree
    simp only [intPow_add, intPow_mul]
    simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [leftForm, rightForm]
  apply Int.mul_le_mul_of_nonneg_left _ commonNonneg
  by_cases coeffNonneg : 0 ≤ t.coeff
  · have cornersLow : cornerOne t box = box.lowOne ∧ cornerTwo t box
        = box.lowTwo ∧ cornerThree t box = box.lowThree
        ∧ cornerFour t box = box.lowFour := by
      unfold cornerOne cornerTwo cornerThree cornerFour
      simp [coeffNonneg]
    obtain ⟨eqOne, eqTwo, eqThree, eqFour⟩ := cornersLow
    rw [eqOne, eqTwo, eqThree, eqFour]
    apply Int.mul_le_mul_of_nonneg_left _ coeffNonneg
    exact prodFour_le (Int.mul_nonneg lowOneNN denNonneg) lowOneSide
      (Int.mul_nonneg lowTwoNN denNonneg) lowTwoSide
      (Int.mul_nonneg lowThreeNN denNonneg) lowThreeSide
      (Int.mul_nonneg lowFourNN denNonneg) lowFourSide
  · have cornersHigh : cornerOne t box = box.highOne ∧ cornerTwo t box
        = box.highTwo ∧ cornerThree t box = box.highThree
        ∧ cornerFour t box = box.highFour := by
      unfold cornerOne cornerTwo cornerThree cornerFour
      simp [coeffNonneg]
    obtain ⟨eqOne, eqTwo, eqThree, eqFour⟩ := cornersHigh
    rw [eqOne, eqTwo, eqThree, eqFour]
    have pointProdLe : intPow (one * boxScale box) t.monomial.expOne
        * intPow (two * boxScale box) t.monomial.expTwo
        * intPow (three * boxScale box) t.monomial.expThree
        * intPow (four * boxScale box) t.monomial.expFour
        ≤ intPow (box.highOne * den) t.monomial.expOne
          * intPow (box.highTwo * den) t.monomial.expTwo
          * intPow (box.highThree * den) t.monomial.expThree
          * intPow (box.highFour * den) t.monomial.expFour :=
      prodFour_le (Int.mul_nonneg oneNN scaleNonneg) highOneSide
        (Int.mul_nonneg twoNN scaleNonneg) highTwoSide
        (Int.mul_nonneg threeNN scaleNonneg) highThreeSide
        (Int.mul_nonneg fourNN scaleNonneg) highFourSide
    exact mul_le_mul_of_nonpos_left pointProdLe (by omega)

/-- Bool homogeneity check read back as a membership statement. -/
theorem isHomog_spec {p : Poly} {deg : Nat}
    (homogTrue : isHomogeneousOfDegree p deg = true) :
    ∀ t, t ∈ p → termDegree t = deg := by
  intro t tMem
  have allTrue : (termDegree t == deg) = true :=
    List.all_eq_true.mp homogTrue t tMem
  simpa using allTrue

/-- The summed corner bound against the denominator-cleared value. -/
theorem lowBound_scaled_le (p : Poly) (deg : Nat) (box : Box)
    (den one two three four : Int)
    (homogAll : ∀ t, t ∈ p → termDegree t = deg)
    (denNonneg : 0 ≤ den)
    (lowsNonneg : 0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree
      ∧ 0 ≤ box.lowFour)
    (pointNonneg : 0 ≤ one ∧ 0 ≤ two ∧ 0 ≤ three ∧ 0 ≤ four)
    (membership : PointLiesInBox box den one two three four) :
    lowBound p box * intPow den deg
      ≤ polyEval p den one two three four * intPow (boxScale box) deg := by
  induction p with
  | nil =>
      show (0 : Int) * intPow den deg ≤ 0 * intPow (boxScale box) deg
      rw [Int.zero_mul, Int.zero_mul]
      omega
  | cons head rest ih =>
      have headHomog : termDegree head = deg :=
        homogAll head (List.mem_cons_self ..)
      have headBound := termLowCorner_scaled_le head box den one two three
        four denNonneg lowsNonneg pointNonneg membership
      rw [headHomog] at headBound
      have restBound := ih fun t tMem =>
        homogAll t (List.mem_cons_of_mem head tMem)
      show (termLowCorner head box + lowBound rest box) * intPow den deg
        ≤ (termEval head den one two three four
            + polyEval rest den one two three four)
          * intPow (boxScale box) deg
      rw [Int.add_mul, Int.add_mul]
      omega

/-- Strict positivity transfer: the engine's `lowSum > 0` verdict. -/
theorem evalPos_of_lowBound_pos {p : Poly} {deg : Nat} {box : Box}
    {den one two three four : Int}
    (boundPos : 0 < lowBound p box)
    (homog : isHomogeneousOfDegree p deg = true)
    (denPos : 0 < den)
    (lowsNonneg : 0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree
      ∧ 0 ≤ box.lowFour)
    (pointNonneg : 0 ≤ one ∧ 0 ≤ two ∧ 0 ≤ three ∧ 0 ≤ four)
    (membership : PointLiesInBox box den one two three four) :
    0 < polyEval p den one two three four := by
  have scaledLe := lowBound_scaled_le p deg box den one two three four
    (isHomog_spec homog) (Int.le_of_lt denPos) lowsNonneg pointNonneg
    membership
  have leftPos : 0 < lowBound p box * intPow den deg :=
    Int.mul_pos boundPos (intPow_pos denPos deg)
  have scalePowPos : 0 < intPow (boxScale box) deg :=
    intPow_pos (intPow_pos (by omega) box.scaleExp) deg
  exact pos_of_mul_pos_of_pos_right (by omega) scalePowPos

/-! ## The grouped (graded) bound at zero-touching faces

The engine's grouped rule: partition the terms by their exponent key on
the zero-touching coordinates; if the stripped residual of every group
passes the corner bound strictly positive, the value is a sum of
(monomial >= 0) * (positive) pieces.  Three soundness grades:
- WEAK: value >= 0 at every box point;
- STRICT via a zero-key group (its monomial is identically 1);
- STRICT via positive masked coordinates (every group monomial > 0). -/

structure VarMask where
  onOne : Bool
  onTwo : Bool
  onThree : Bool
  onFour : Bool
deriving DecidableEq

abbrev ExponentKey := Nat × Nat × Nat × Nat

def maskedKeyOf (mask : VarMask) (t : Term) : ExponentKey :=
  (if mask.onOne then t.monomial.expOne else 0,
   if mask.onTwo then t.monomial.expTwo else 0,
   if mask.onThree then t.monomial.expThree else 0,
   if mask.onFour then t.monomial.expFour else 0)

def stripMasked (mask : VarMask) (t : Term) : Term :=
  ⟨⟨t.monomial.expDen,
    if mask.onOne then 0 else t.monomial.expOne,
    if mask.onTwo then 0 else t.monomial.expTwo,
    if mask.onThree then 0 else t.monomial.expThree,
    if mask.onFour then 0 else t.monomial.expFour⟩, t.coeff⟩

def keyMonomialValue (key : ExponentKey) (one two three four : Int) : Int :=
  intPow one key.1 * intPow two key.2.1 * intPow three key.2.2.1
    * intPow four key.2.2.2

theorem intPow_zero (base : Int) : intPow base 0 = 1 := rfl

/-- A power factors through any flag-partition of its exponent: the slot
either goes entirely to the masked monomial or entirely to the residual. -/
theorem intPow_split_by_flag (base : Int) (flag : Bool) (exponent : Nat) :
    intPow base exponent
      = intPow base (if flag then exponent else 0)
        * intPow base (if flag then 0 else exponent) := by
  cases flag with
  | true => rw [if_pos rfl, if_pos rfl, intPow_zero, Int.mul_one]
  | false => rw [if_neg (by simp), if_neg (by simp), intPow_zero,
      Int.one_mul]

/-- Splitting one term into its masked monomial times its stripped rest:
a monomial factors through the partition of its exponent vector. -/
theorem termEval_masked_split (mask : VarMask) (t : Term)
    (den one two three four : Int) :
    termEval t den one two three four
      = keyMonomialValue (maskedKeyOf mask t) one two three four
        * termEval (stripMasked mask t) den one two three four := by
  unfold termEval keyMonomialValue maskedKeyOf stripMasked
  rw [intPow_split_by_flag one mask.onOne t.monomial.expOne,
      intPow_split_by_flag two mask.onTwo t.monomial.expTwo,
      intPow_split_by_flag three mask.onThree t.monomial.expThree,
      intPow_split_by_flag four mask.onFour t.monomial.expFour]
  simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- Evaluation of a list of terms sharing one masked key. -/
theorem polyEval_of_sharedKey (mask : VarMask) (key : ExponentKey)
    (q : Poly) (den one two three four : Int)
    (allShare : ∀ t, t ∈ q → maskedKeyOf mask t = key) :
    polyEval q den one two three four
      = keyMonomialValue key one two three four
        * polyEval (q.map (stripMasked mask)) den one two three four := by
  induction q with
  | nil => simp [polyEval]
  | cons head rest ih =>
      have headKey : maskedKeyOf mask head = key :=
        allShare head (List.mem_cons_self ..)
      have restShare : ∀ t, t ∈ rest → maskedKeyOf mask t = key :=
        fun t tMem => allShare t (List.mem_cons_of_mem head tMem)
      have headSplit := termEval_masked_split mask head den one two three four
      rw [headKey] at headSplit
      show termEval head den one two three four
          + polyEval rest den one two three four
        = keyMonomialValue key one two three four
          * (termEval (stripMasked mask head) den one two three four
            + polyEval (rest.map (stripMasked mask)) den one two three four)
      rw [Int.mul_add, headSplit, ih restShare]

/-- The head-key group of a term list: the terms sharing the head's
masked exponent key, stripped of the masked exponents. -/
def headKeyGroup (mask : VarMask) (p : Poly) : Poly :=
  match p with
  | [] => []
  | head :: _ =>
      (p.filter fun t =>
        decide (maskedKeyOf mask t = maskedKeyOf mask head)).map
        (stripMasked mask)

/-- The remainder after removing the head-key group. -/
def headKeyRemainder (mask : VarMask) (p : Poly) : Poly :=
  match p with
  | [] => []
  | head :: _ =>
      p.filter fun t => !decide (maskedKeyOf mask t = maskedKeyOf mask head)

def groupedScanHolds (mask : VarMask) (box : Box) : Nat → Poly → Bool
  | 0, remaining => remaining.isEmpty
  | _ + 1, [] => true
  | fuel + 1, head :: rest =>
      decide (0 < lowBound (headKeyGroup mask (head :: rest)) box)
        && isHomogeneousOfDegree (headKeyGroup mask (head :: rest))
          (polyLeadDegree (headKeyGroup mask (head :: rest)))
        && groupedScanHolds mask box fuel
          (headKeyRemainder mask (head :: rest))

/-- Is there a group with the all-zero key (nonvanishing at the face)? -/
def hasZeroKeyTerm (mask : VarMask) (p : Poly) : Bool :=
  p.any fun t => decide (maskedKeyOf mask t = ((0, 0, 0, 0) : ExponentKey))

/-- The masked coordinates are at least one (the strict-GL side condition:
those coordinates of the point are strictly positive rationals). -/
def MaskedCoordsAtLeastOne (mask : VarMask) (one two three four : Int) :
    Prop :=
  (mask.onOne = true → 1 ≤ one) ∧ (mask.onTwo = true → 1 ≤ two)
    ∧ (mask.onThree = true → 1 ≤ three) ∧ (mask.onFour = true → 1 ≤ four)

theorem polyEval_filter_split (p : Poly) (predicate : Term → Bool)
    (den one two three four : Int) :
    polyEval p den one two three four
      = polyEval (p.filter predicate) den one two three four
        + polyEval (p.filter fun t => !predicate t) den one two three four := by
  induction p with
  | nil => simp [polyEval]
  | cons head rest ih =>
      by_cases headPasses : predicate head = true
      · rw [List.filter_cons_of_pos headPasses,
            List.filter_cons_of_neg (by simp [headPasses])]
        show termEval head den one two three four
            + polyEval rest den one two three four = _
        rw [ih, polyEval]
        omega
      · have headFails : predicate head = false :=
          Bool.eq_false_iff.mpr headPasses
        rw [List.filter_cons_of_neg (by simp [headFails]),
            List.filter_cons_of_pos (by simp [headFails])]
        show termEval head den one two three four
            + polyEval rest den one two three four = _
        rw [ih, polyEval]
        omega

theorem keyMonomialValue_nonneg (key : ExponentKey)
    {one two three four : Int} (oneNN : 0 ≤ one) (twoNN : 0 ≤ two)
    (threeNN : 0 ≤ three) (fourNN : 0 ≤ four) :
    0 ≤ keyMonomialValue key one two three four :=
  prodFour_nonneg oneNN twoNN threeNN fourNN

theorem keyMonomialValue_zero_key (one two three four : Int) :
    keyMonomialValue ((0, 0, 0, 0) : ExponentKey) one two three four = 1 := by
  unfold keyMonomialValue
  simp [intPow_zero]

theorem keyMonomialValue_pos_of_masked {mask : VarMask} {t : Term}
    {one two three four : Int}
    (maskedGe : MaskedCoordsAtLeastOne mask one two three four)
    (oneNN : 0 ≤ one) (twoNN : 0 ≤ two) (threeNN : 0 ≤ three)
    (fourNN : 0 ≤ four) :
    0 < keyMonomialValue (maskedKeyOf mask t) one two three four := by
  obtain ⟨geOne, geTwo, geThree, geFour⟩ := maskedGe
  unfold keyMonomialValue maskedKeyOf
  apply Int.mul_pos
  apply Int.mul_pos
  apply Int.mul_pos
  · cases maskOne : mask.onOne with
    | true => exact intPow_pos (by have := geOne maskOne; omega) _
    | false => simp [intPow_zero]
  · cases maskTwo : mask.onTwo with
    | true => exact intPow_pos (by have := geTwo maskTwo; omega) _
    | false => simp [intPow_zero]
  · cases maskThree : mask.onThree with
    | true => exact intPow_pos (by have := geThree maskThree; omega) _
    | false => simp [intPow_zero]
  · cases maskFour : mask.onFour with
    | true => exact intPow_pos (by have := geFour maskFour; omega) _
    | false => simp [intPow_zero]

/-- WEAK soundness of the group peel: the value is nonnegative at every
rational point of the box (coordinates only need nonnegativity). -/
theorem groupedScanHolds_nonneg (mask : VarMask) (box : Box) (fuel : Nat)
    (p : Poly) {den one two three four : Int}
    (scanTrue : groupedScanHolds mask box fuel p = true)
    (denPos : 0 < den)
    (lowsNonneg : 0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree
      ∧ 0 ≤ box.lowFour)
    (pointNonneg : 0 ≤ one ∧ 0 ≤ two ∧ 0 ≤ three ∧ 0 ≤ four)
    (membership : PointLiesInBox box den one two three four) :
    0 ≤ polyEval p den one two three four := by
  induction fuel generalizing p with
  | zero =>
      have isEmpty : p.isEmpty = true := scanTrue
      have pNil : p = [] := List.isEmpty_iff.mp isEmpty
      rw [pNil]
      exact Int.le_refl 0
  | succ fuel ih =>
      cases p with
      | nil => exact Int.le_refl 0
      | cons head rest =>
          have parts : ((0 < lowBound (headKeyGroup mask (head :: rest)) box)
              ∧ isHomogeneousOfDegree (headKeyGroup mask (head :: rest))
                (polyLeadDegree (headKeyGroup mask (head :: rest))) = true)
              ∧ groupedScanHolds mask box fuel
                (headKeyRemainder mask (head :: rest)) = true := by
            simpa [groupedScanHolds] using scanTrue
          have allShare : ∀ t, t ∈ ((head :: rest).filter fun t =>
              decide (maskedKeyOf mask t = maskedKeyOf mask head)) →
              maskedKeyOf mask t = maskedKeyOf mask head :=
            fun t tMem => of_decide_eq_true (List.mem_filter.mp tMem).2
          have matchingValue := polyEval_of_sharedKey mask
            (maskedKeyOf mask head)
            ((head :: rest).filter fun t =>
              decide (maskedKeyOf mask t = maskedKeyOf mask head))
            den one two three four allShare
          have strippedPos : 0 < polyEval (headKeyGroup mask (head :: rest))
              den one two three four :=
            evalPos_of_lowBound_pos parts.1.1 parts.1.2 denPos
              lowsNonneg pointNonneg membership
          have monomialNN : 0 ≤ keyMonomialValue (maskedKeyOf mask head)
              one two three four :=
            keyMonomialValue_nonneg (maskedKeyOf mask head) pointNonneg.1
              pointNonneg.2.1 pointNonneg.2.2.1 pointNonneg.2.2.2
          have matchingNN : 0 ≤ polyEval
              ((head :: rest).filter fun t =>
                decide (maskedKeyOf mask t = maskedKeyOf mask head))
              den one two three four := by
            rw [matchingValue]
            exact Int.mul_nonneg monomialNN (Int.le_of_lt strippedPos)
          have remainingNN : 0 ≤ polyEval
              (headKeyRemainder mask (head :: rest)) den one two three four :=
            ih (headKeyRemainder mask (head :: rest)) parts.2
          have splitValue := polyEval_filter_split (head :: rest)
            (fun t => decide (maskedKeyOf mask t = maskedKeyOf mask head))
            den one two three four
          have remainderForm : polyEval
              (headKeyRemainder mask (head :: rest)) den one two three four
              = polyEval ((head :: rest).filter fun t =>
                  !decide (maskedKeyOf mask t = maskedKeyOf mask head))
                den one two three four := rfl
          omega

/-- STRICT soundness via a zero-key group: some group's monomial is
identically one, so the sum of nonnegative group contributions is
strictly positive wherever that group's residual is. -/
theorem groupedScanHolds_pos_of_zeroKey (mask : VarMask) (box : Box)
    (fuel : Nat) (p : Poly) {den one two three four : Int}
    (scanTrue : groupedScanHolds mask box fuel p = true)
    (zeroKeyPresent : hasZeroKeyTerm mask p = true)
    (denPos : 0 < den)
    (lowsNonneg : 0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree
      ∧ 0 ≤ box.lowFour)
    (pointNonneg : 0 ≤ one ∧ 0 ≤ two ∧ 0 ≤ three ∧ 0 ≤ four)
    (membership : PointLiesInBox box den one two three four) :
    0 < polyEval p den one two three four := by
  induction fuel generalizing p with
  | zero =>
      have pNil : p = [] := List.isEmpty_iff.mp scanTrue
      rw [pNil] at zeroKeyPresent
      exact absurd zeroKeyPresent (by simp [hasZeroKeyTerm])
  | succ fuel ih =>
      cases p with
      | nil => exact absurd zeroKeyPresent (by simp [hasZeroKeyTerm])
      | cons head rest =>
          have parts : ((0 < lowBound (headKeyGroup mask (head :: rest)) box)
              ∧ isHomogeneousOfDegree (headKeyGroup mask (head :: rest))
                (polyLeadDegree (headKeyGroup mask (head :: rest))) = true)
              ∧ groupedScanHolds mask box fuel
                (headKeyRemainder mask (head :: rest)) = true := by
            simpa [groupedScanHolds] using scanTrue
          have allShare : ∀ t, t ∈ ((head :: rest).filter fun t =>
              decide (maskedKeyOf mask t = maskedKeyOf mask head)) →
              maskedKeyOf mask t = maskedKeyOf mask head :=
            fun t tMem => of_decide_eq_true (List.mem_filter.mp tMem).2
          have matchingValue := polyEval_of_sharedKey mask
            (maskedKeyOf mask head)
            ((head :: rest).filter fun t =>
              decide (maskedKeyOf mask t = maskedKeyOf mask head))
            den one two three four allShare
          have strippedPos : 0 < polyEval (headKeyGroup mask (head :: rest))
              den one two three four :=
            evalPos_of_lowBound_pos parts.1.1 parts.1.2 denPos
              lowsNonneg pointNonneg membership
          have remainderNN : 0 ≤ polyEval
              (headKeyRemainder mask (head :: rest)) den one two three four :=
            groupedScanHolds_nonneg mask box fuel _ parts.2 denPos
              lowsNonneg pointNonneg membership
          have splitValue := polyEval_filter_split (head :: rest)
            (fun t => decide (maskedKeyOf mask t = maskedKeyOf mask head))
            den one two three four
          have remainderForm : polyEval
              (headKeyRemainder mask (head :: rest)) den one two three four
              = polyEval ((head :: rest).filter fun t =>
                  !decide (maskedKeyOf mask t = maskedKeyOf mask head))
                den one two three four := rfl
          by_cases headIsZeroKey :
              maskedKeyOf mask head = ((0, 0, 0, 0) : ExponentKey)
          · have monomialOne : keyMonomialValue (maskedKeyOf mask head)
                one two three four = 1 := by
              rw [headIsZeroKey, keyMonomialValue_zero_key]
            have matchingPos : 0 < polyEval
                ((head :: rest).filter fun t =>
                  decide (maskedKeyOf mask t = maskedKeyOf mask head))
                den one two three four := by
              rw [matchingValue, monomialOne, Int.one_mul]
              exact strippedPos
            omega
          · obtain ⟨witness, witnessMem, witnessKey⟩ :=
              List.any_eq_true.mp zeroKeyPresent
            have witnessZero : maskedKeyOf mask witness
                = ((0, 0, 0, 0) : ExponentKey) := of_decide_eq_true witnessKey
            have witnessSurvives : hasZeroKeyTerm mask
                (headKeyRemainder mask (head :: rest)) = true := by
              apply List.any_eq_true.mpr
              refine ⟨witness, List.mem_filter.mpr ⟨witnessMem, ?_⟩,
                witnessKey⟩
              have keysDiffer : maskedKeyOf mask witness
                  ≠ maskedKeyOf mask head := by
                rw [witnessZero]
                exact fun keyEq => headIsZeroKey keyEq.symm
              simpa using keysDiffer
            have remainderPos := ih (headKeyRemainder mask (head :: rest))
              parts.2 witnessSurvives
            have matchingNN : 0 ≤ polyEval
                ((head :: rest).filter fun t =>
                  decide (maskedKeyOf mask t = maskedKeyOf mask head))
                den one two three four := by
              rw [matchingValue]
              exact Int.mul_nonneg
                (keyMonomialValue_nonneg _ pointNonneg.1 pointNonneg.2.1
                  pointNonneg.2.2.1 pointNonneg.2.2.2)
                (Int.le_of_lt strippedPos)
            omega

/-- STRICT soundness via strictly positive masked coordinates: every
group monomial is positive, and the head group is present. -/
theorem groupedScanHolds_pos_of_maskedPositive (mask : VarMask) (box : Box)
    (fuel : Nat) (p : Poly) {den one two three four : Int}
    (scanTrue : groupedScanHolds mask box fuel p = true)
    (pNonempty : p ≠ [])
    (maskedGe : MaskedCoordsAtLeastOne mask one two three four)
    (denPos : 0 < den)
    (lowsNonneg : 0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree
      ∧ 0 ≤ box.lowFour)
    (pointNonneg : 0 ≤ one ∧ 0 ≤ two ∧ 0 ≤ three ∧ 0 ≤ four)
    (membership : PointLiesInBox box den one two three four) :
    0 < polyEval p den one two three four := by
  cases fuel with
  | zero =>
      have pNil : p = [] := List.isEmpty_iff.mp scanTrue
      exact absurd pNil pNonempty
  | succ fuel =>
      cases p with
      | nil => exact absurd rfl pNonempty
      | cons head rest =>
          have parts : ((0 < lowBound (headKeyGroup mask (head :: rest)) box)
              ∧ isHomogeneousOfDegree (headKeyGroup mask (head :: rest))
                (polyLeadDegree (headKeyGroup mask (head :: rest))) = true)
              ∧ groupedScanHolds mask box fuel
                (headKeyRemainder mask (head :: rest)) = true := by
            simpa [groupedScanHolds] using scanTrue
          have allShare : ∀ t, t ∈ ((head :: rest).filter fun t =>
              decide (maskedKeyOf mask t = maskedKeyOf mask head)) →
              maskedKeyOf mask t = maskedKeyOf mask head :=
            fun t tMem => of_decide_eq_true (List.mem_filter.mp tMem).2
          have matchingValue := polyEval_of_sharedKey mask
            (maskedKeyOf mask head)
            ((head :: rest).filter fun t =>
              decide (maskedKeyOf mask t = maskedKeyOf mask head))
            den one two three four allShare
          have strippedPos : 0 < polyEval (headKeyGroup mask (head :: rest))
              den one two three four :=
            evalPos_of_lowBound_pos parts.1.1 parts.1.2 denPos
              lowsNonneg pointNonneg membership
          have monomialPos : 0 < keyMonomialValue (maskedKeyOf mask head)
              one two three four :=
            keyMonomialValue_pos_of_masked maskedGe pointNonneg.1
              pointNonneg.2.1 pointNonneg.2.2.1 pointNonneg.2.2.2
          have matchingPos : 0 < polyEval
              ((head :: rest).filter fun t =>
                decide (maskedKeyOf mask t = maskedKeyOf mask head))
              den one two three four := by
            rw [matchingValue]
            exact Int.mul_pos monomialPos strippedPos
          have remainderNN : 0 ≤ polyEval
              (headKeyRemainder mask (head :: rest)) den one two three four :=
            groupedScanHolds_nonneg mask box fuel _ parts.2 denPos
              lowsNonneg pointNonneg membership
          have splitValue := polyEval_filter_split (head :: rest)
            (fun t => decide (maskedKeyOf mask t = maskedKeyOf mask head))
            den one two three four
          have remainderForm : polyEval
              (headKeyRemainder mask (head :: rest)) den one two three four
              = polyEval ((head :: rest).filter fun t =>
                  !decide (maskedKeyOf mask t = maskedKeyOf mask head))
                den one two three four := rfl
          omega

/-! ## The upper-face reflection: `r_v -> h - r_v` as a homogeneous
substitution.  Reflection is an affine involution; its evaluation law
turns a bound on the reflected polynomial over the reflected box into a
sign claim for the base polynomial at the original point. -/

def unitPoly : Poly := [tm 0 0 0 0 0 1]

def denMinusOnePoly : Poly := [tm 1 0 0 0 0 1, tm 0 1 0 0 0 (-1)]
def denMinusTwoPoly : Poly := [tm 1 0 0 0 0 1, tm 0 0 1 0 0 (-1)]
def denMinusThreePoly : Poly := [tm 1 0 0 0 0 1, tm 0 0 0 1 0 (-1)]
def denMinusFourPoly : Poly := [tm 1 0 0 0 0 1, tm 0 0 0 0 1 (-1)]

def powPoly (base : Poly) : Nat → Poly
  | 0 => unitPoly
  | exponent + 1 => polyMul (powPoly base exponent) base

theorem polyEval_unitPoly (den one two three four : Int) :
    polyEval unitPoly den one two three four = 1 := by
  show termEval (tm 0 0 0 0 0 1) den one two three four + 0 = 1
  unfold termEval tm
  simp [intPow_zero]

theorem polyEval_powPoly (base : Poly) (exponent : Nat)
    (den one two three four : Int) :
    polyEval (powPoly base exponent) den one two three four
      = intPow (polyEval base den one two three four) exponent := by
  induction exponent with
  | zero => exact polyEval_unitPoly den one two three four
  | succ exponent ih =>
      show polyEval (polyMul (powPoly base exponent) base) den one two
        three four = _
      rw [polyEval_mul, ih]
      rfl

theorem polyEval_denMinusOne (den one two three four : Int) :
    polyEval denMinusOnePoly den one two three four = den - one := by
  show termEval (tm 1 0 0 0 0 1) den one two three four
    + (termEval (tm 0 1 0 0 0 (-1)) den one two three four + 0) = den - one
  unfold termEval tm
  simp [intPow_zero, intPow]
  omega

theorem polyEval_denMinusTwo (den one two three four : Int) :
    polyEval denMinusTwoPoly den one two three four = den - two := by
  show termEval (tm 1 0 0 0 0 1) den one two three four
    + (termEval (tm 0 0 1 0 0 (-1)) den one two three four + 0) = den - two
  unfold termEval tm
  simp [intPow_zero, intPow]
  omega

theorem polyEval_denMinusThree (den one two three four : Int) :
    polyEval denMinusThreePoly den one two three four = den - three := by
  show termEval (tm 1 0 0 0 0 1) den one two three four
    + (termEval (tm 0 0 0 1 0 (-1)) den one two three four + 0)
      = den - three
  unfold termEval tm
  simp [intPow_zero, intPow]
  omega

theorem polyEval_denMinusFour (den one two three four : Int) :
    polyEval denMinusFourPoly den one two three four = den - four := by
  show termEval (tm 1 0 0 0 0 1) den one two three four
    + (termEval (tm 0 0 0 0 1 (-1)) den one two three four + 0)
      = den - four
  unfold termEval tm
  simp [intPow_zero, intPow]
  omega

def slotFactorOne (isReflected : Bool) (exponent : Nat) : Poly :=
  if isReflected then powPoly denMinusOnePoly exponent
  else [tm 0 exponent 0 0 0 1]
def slotFactorTwo (isReflected : Bool) (exponent : Nat) : Poly :=
  if isReflected then powPoly denMinusTwoPoly exponent
  else [tm 0 0 exponent 0 0 1]
def slotFactorThree (isReflected : Bool) (exponent : Nat) : Poly :=
  if isReflected then powPoly denMinusThreePoly exponent
  else [tm 0 0 0 exponent 0 1]
def slotFactorFour (isReflected : Bool) (exponent : Nat) : Poly :=
  if isReflected then powPoly denMinusFourPoly exponent
  else [tm 0 0 0 0 exponent 1]

/-- The reflected image of one term. -/
def reflectTerm (mask : VarMask) (t : Term) : Poly :=
  polyMul (polyMul (polyMul (polyMul
    [⟨⟨t.monomial.expDen, 0, 0, 0, 0⟩, t.coeff⟩]
    (slotFactorOne mask.onOne t.monomial.expOne))
    (slotFactorTwo mask.onTwo t.monomial.expTwo))
    (slotFactorThree mask.onThree t.monomial.expThree))
    (slotFactorFour mask.onFour t.monomial.expFour)

def reflectPoly (mask : VarMask) : Poly → Poly
  | [] => []
  | t :: rest => reflectTerm mask t ++ reflectPoly mask rest

/-- The reflected coordinate: `n_v -> den - n_v` on masked slots. -/
def reflectCoord (isReflected : Bool) (den value : Int) : Int :=
  if isReflected then den - value else value

theorem polyEval_slotFactorOne (flag : Bool) (exponent : Nat)
    (den one two three four : Int) :
    polyEval (slotFactorOne flag exponent) den one two three four
      = intPow (reflectCoord flag den one) exponent := by
  cases flag with
  | true =>
      show polyEval (powPoly denMinusOnePoly exponent) den one two three
        four = _
      rw [polyEval_powPoly, polyEval_denMinusOne]
      rfl
  | false =>
      show termEval (tm 0 exponent 0 0 0 1) den one two three four + 0 = _
      unfold termEval tm reflectCoord
      simp [intPow_zero]

theorem polyEval_slotFactorTwo (flag : Bool) (exponent : Nat)
    (den one two three four : Int) :
    polyEval (slotFactorTwo flag exponent) den one two three four
      = intPow (reflectCoord flag den two) exponent := by
  cases flag with
  | true =>
      show polyEval (powPoly denMinusTwoPoly exponent) den one two three
        four = _
      rw [polyEval_powPoly, polyEval_denMinusTwo]
      rfl
  | false =>
      show termEval (tm 0 0 exponent 0 0 1) den one two three four + 0 = _
      unfold termEval tm reflectCoord
      simp [intPow_zero]

theorem polyEval_slotFactorThree (flag : Bool) (exponent : Nat)
    (den one two three four : Int) :
    polyEval (slotFactorThree flag exponent) den one two three four
      = intPow (reflectCoord flag den three) exponent := by
  cases flag with
  | true =>
      show polyEval (powPoly denMinusThreePoly exponent) den one two three
        four = _
      rw [polyEval_powPoly, polyEval_denMinusThree]
      rfl
  | false =>
      show termEval (tm 0 0 0 exponent 0 1) den one two three four + 0 = _
      unfold termEval tm reflectCoord
      simp [intPow_zero]

theorem polyEval_slotFactorFour (flag : Bool) (exponent : Nat)
    (den one two three four : Int) :
    polyEval (slotFactorFour flag exponent) den one two three four
      = intPow (reflectCoord flag den four) exponent := by
  cases flag with
  | true =>
      show polyEval (powPoly denMinusFourPoly exponent) den one two three
        four = _
      rw [polyEval_powPoly, polyEval_denMinusFour]
      rfl
  | false =>
      show termEval (tm 0 0 0 0 exponent 1) den one two three four + 0 = _
      unfold termEval tm reflectCoord
      simp [intPow_zero]

/-- Reflection is an involution on coordinates. -/
theorem reflectCoord_involution (flag : Bool) (den value : Int) :
    reflectCoord flag den (reflectCoord flag den value) = value := by
  cases flag <;> simp [reflectCoord] <;> omega

/-- THE REFLECTION LAW: evaluating the reflected polynomial at the
reflected point recovers the original value. -/
theorem polyEval_reflectPoly (mask : VarMask) (p : Poly)
    (den one two three four : Int) :
    polyEval (reflectPoly mask p) den
      (reflectCoord mask.onOne den one) (reflectCoord mask.onTwo den two)
      (reflectCoord mask.onThree den three)
      (reflectCoord mask.onFour den four)
      = polyEval p den one two three four := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
      show polyEval (reflectTerm mask head ++ reflectPoly mask rest) _ _ _ _ _
        = _
      rw [polyEval_append, ih]
      have headValue : polyEval (reflectTerm mask head) den
          (reflectCoord mask.onOne den one) (reflectCoord mask.onTwo den two)
          (reflectCoord mask.onThree den three)
          (reflectCoord mask.onFour den four)
          = termEval head den one two three four := by
        unfold reflectTerm
        rw [polyEval_mul, polyEval_mul, polyEval_mul, polyEval_mul,
          polyEval_slotFactorOne, polyEval_slotFactorTwo,
          polyEval_slotFactorThree, polyEval_slotFactorFour,
          reflectCoord_involution, reflectCoord_involution,
          reflectCoord_involution, reflectCoord_involution]
        show (termEval ⟨⟨head.monomial.expDen, 0, 0, 0, 0⟩, head.coeff⟩ den
            (reflectCoord mask.onOne den one)
            (reflectCoord mask.onTwo den two)
            (reflectCoord mask.onThree den three)
            (reflectCoord mask.onFour den four) + 0)
            * intPow one head.monomial.expOne
            * intPow two head.monomial.expTwo
            * intPow three head.monomial.expThree
            * intPow four head.monomial.expFour
          = termEval head den one two three four
        unfold termEval
        simp [intPow_zero]
      rw [headValue]
      rfl

/-! ## Certificate data -/

structure FactorRef where
  coreIndex : Nat
  multiplicity : Nat
deriving DecidableEq

structure TripleData where
  sign : Int
  factors : List FactorRef
deriving DecidableEq

structure ThresholdData where
  spanNum : TripleData
  spanDen : TripleData
  massNum : TripleData
  massDen : TripleData
  thrNum : TripleData
  thrDen : TripleData

structure CandidateData where
  betas : List TripleData
  ratioNum : TripleData
  margins : List TripleData

inductive LeafWitness where
  | windowWin (candIndex thrIndex : Nat)
  | freeWin (thrIndex : Nat)
  | guardPair (candP thrP candQ thrQ guardCoreIndex : Nat)

inductive CoverTree where
  | leaf (witness : LeafWitness)
  | node (splitDim : Nat) (left right : CoverTree)

structure VariantEntry where
  coreIndex : Nat
  maskCode : Nat
  variantPoly : Poly

structure ChartData where
  cores : List Poly
  variants : List VariantEntry
  thresholds : List ThresholdData
  candidates : List CandidateData
  cover : CoverTree

def coreAt (cores : List Poly) (index : Nat) : Poly := cores.getD index []

def degenerateTriple : TripleData := ⟨0, []⟩

def degenerateThreshold : ThresholdData :=
  ⟨degenerateTriple, degenerateTriple, degenerateTriple, degenerateTriple,
   degenerateTriple, degenerateTriple⟩

def degenerateCandidate : CandidateData := ⟨[], degenerateTriple, []⟩

def thresholdAt (data : ChartData) (index : Nat) : ThresholdData :=
  data.thresholds.getD index degenerateThreshold

def candidateAt (data : ChartData) (index : Nat) : CandidateData :=
  data.candidates.getD index degenerateCandidate

def marginAt (data : ChartData) (candIndex thrIndex : Nat) : TripleData :=
  (candidateAt data candIndex).margins.getD thrIndex degenerateTriple

/-! ## Masks, the upper-face variant lookup, and its verification -/

def maskOfCode (code : Nat) : VarMask :=
  ⟨code.testBit 0, code.testBit 1, code.testBit 2, code.testBit 3⟩

def maskCodeOfBox (box : Box) : Nat :=
  (if box.highOne = boxScale box then 1 else 0)
    + (if box.highTwo = boxScale box then 2 else 0)
    + (if box.highThree = boxScale box then 4 else 0)
    + (if box.highFour = boxScale box then 8 else 0)

/-- One variant entry is verified against the Lean-computed reflection of
its base core through the canonical-form bridge. -/
def isVariantEntryVerified (cores : List Poly) (entry : VariantEntry) :
    Bool :=
  decide (canon (reflectPoly (maskOfCode entry.maskCode)
      (coreAt cores entry.coreIndex)) = canon entry.variantPoly)

def allVariantsVerified (data : ChartData) : Bool :=
  data.variants.all (isVariantEntryVerified data.cores)

def findVariantPoly (entries : List VariantEntry)
    (coreIndex maskCode : Nat) : Option Poly :=
  match entries with
  | [] => none
  | entry :: rest =>
      if entry.coreIndex = coreIndex ∧ entry.maskCode = maskCode then
        some entry.variantPoly
      else findVariantPoly rest coreIndex maskCode

theorem findVariantPoly_verified {entries : List VariantEntry}
    {cores : List Poly} {coreIndex maskCode : Nat} {variantPoly : Poly}
    (allVerified : entries.all (isVariantEntryVerified cores) = true)
    (found : findVariantPoly entries coreIndex maskCode
      = some variantPoly) :
    isVariantEntryVerified cores ⟨coreIndex, maskCode, variantPoly⟩
      = true := by
  induction entries with
  | nil => exact absurd found (by simp [findVariantPoly])
  | cons entry rest ih =>
      have entryVerified : isVariantEntryVerified cores entry = true :=
        List.all_eq_true.mp allVerified entry (List.mem_cons_self ..)
      have restVerified : rest.all (isVariantEntryVerified cores) = true :=
        List.all_eq_true.mpr fun other otherMem =>
          List.all_eq_true.mp allVerified other
            (List.mem_cons_of_mem entry otherMem)
      unfold findVariantPoly at found
      split at found
      · next fieldsEq =>
          obtain ⟨coreEq, maskEq⟩ := fieldsEq
          have polyEq : entry.variantPoly = variantPoly :=
            Option.some.inj found
          have entryForm : entry
              = (⟨coreIndex, maskCode, variantPoly⟩ : VariantEntry) := by
            cases entry
            simp_all
          rw [← entryForm]
          exact entryVerified
      · exact ih restVerified found

/-- The looked-up variant for a box: variant of the box's upper-touch
mask; the mask-zero variant entries carry the base polynomial itself. -/
def variantPolyForBox (data : ChartData) (box : Box) (coreIndex : Nat) :
    Option Poly :=
  findVariantPoly data.variants coreIndex (maskCodeOfBox box)

/-- The verified transfer: the variant's value at the reflected point IS
the base core's value at the point. -/
theorem variantValue_eq_baseValue {data : ChartData} {box : Box}
    {coreIndex : Nat} {variantPoly : Poly}
    (variantsOk : allVariantsVerified data = true)
    (found : variantPolyForBox data box coreIndex = some variantPoly)
    (den one two three four : Int) :
    polyEval variantPoly den
      (reflectCoord (maskOfCode (maskCodeOfBox box)).onOne den one)
      (reflectCoord (maskOfCode (maskCodeOfBox box)).onTwo den two)
      (reflectCoord (maskOfCode (maskCodeOfBox box)).onThree den three)
      (reflectCoord (maskOfCode (maskCodeOfBox box)).onFour den four)
      = polyEval (coreAt data.cores coreIndex) den one two three four := by
  have entryVerified := findVariantPoly_verified variantsOk found
  have canonEq : canon (reflectPoly (maskOfCode (maskCodeOfBox box))
      (coreAt data.cores coreIndex)) = canon variantPoly :=
    of_decide_eq_true entryVerified
  have valueEq := polyEval_eq_of_canon_eq _ _ canonEq den
    (reflectCoord (maskOfCode (maskCodeOfBox box)).onOne den one)
    (reflectCoord (maskOfCode (maskCodeOfBox box)).onTwo den two)
    (reflectCoord (maskOfCode (maskCodeOfBox box)).onThree den three)
    (reflectCoord (maskOfCode (maskCodeOfBox box)).onFour den four)
  rw [← valueEq, polyEval_reflectPoly]

/-! ## The reflected box and the geometric transfer -/

def reflectBox (mask : VarMask) (box : Box) : Box :=
  ⟨box.scaleExp,
   if mask.onOne then boxScale box - box.highOne else box.lowOne,
   if mask.onTwo then boxScale box - box.highTwo else box.lowTwo,
   if mask.onThree then boxScale box - box.highThree else box.lowThree,
   if mask.onFour then boxScale box - box.highFour else box.lowFour,
   if mask.onOne then boxScale box - box.lowOne else box.highOne,
   if mask.onTwo then boxScale box - box.lowTwo else box.highTwo,
   if mask.onThree then boxScale box - box.lowThree else box.highThree,
   if mask.onFour then boxScale box - box.lowFour else box.highFour⟩

theorem reflect_side_low {scale low high den coord : Int}
    (lowSide : low * den ≤ coord * scale)
    (highSide : coord * scale ≤ high * den) :
    (scale - high) * den ≤ (den - coord) * scale := by
  have expandLeft : (scale - high) * den = scale * den - high * den :=
    Int.sub_mul scale high den
  have expandRight : (den - coord) * scale = den * scale - coord * scale :=
    Int.sub_mul den coord scale
  have commuteScale : scale * den = den * scale := Int.mul_comm scale den
  omega

theorem reflect_side_high {scale low high den coord : Int}
    (lowSide : low * den ≤ coord * scale)
    (highSide : coord * scale ≤ high * den) :
    (den - coord) * scale ≤ (scale - low) * den := by
  have expandLeft : (den - coord) * scale = den * scale - coord * scale :=
    Int.sub_mul den coord scale
  have expandRight : (scale - low) * den = scale * den - low * den :=
    Int.sub_mul scale low den
  have commuteScale : scale * den = den * scale := Int.mul_comm scale den
  omega

theorem pointLiesInBox_reflectBox {mask : VarMask} {box : Box}
    {den one two three four : Int}
    (membership : PointLiesInBox box den one two three four) :
    PointLiesInBox (reflectBox mask box) den
      (reflectCoord mask.onOne den one) (reflectCoord mask.onTwo den two)
      (reflectCoord mask.onThree den three)
      (reflectCoord mask.onFour den four) := by
  obtain ⟨lowOneSide, highOneSide, lowTwoSide, highTwoSide, lowThreeSide,
    highThreeSide, lowFourSide, highFourSide⟩ := membership
  have scaleSame : boxScale (reflectBox mask box) = boxScale box := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [reflectBox, reflectCoord, scaleSame]
  · cases mask.onOne <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact lowOneSide
    · exact reflect_side_low lowOneSide highOneSide
  · cases mask.onOne <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact highOneSide
    · exact reflect_side_high lowOneSide highOneSide
  · cases mask.onTwo <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact lowTwoSide
    · exact reflect_side_low lowTwoSide highTwoSide
  · cases mask.onTwo <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact highTwoSide
    · exact reflect_side_high lowTwoSide highTwoSide
  · cases mask.onThree <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact lowThreeSide
    · exact reflect_side_low lowThreeSide highThreeSide
  · cases mask.onThree <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact highThreeSide
    · exact reflect_side_high lowThreeSide highThreeSide
  · cases mask.onFour <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact lowFourSide
    · exact reflect_side_low lowFourSide highFourSide
  · cases mask.onFour <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false]
    · exact highFourSide
    · exact reflect_side_high lowFourSide highFourSide

theorem boxIsSane_spec {box : Box} (sane : boxIsSane box = true) :
    (0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree ∧ 0 ≤ box.lowFour)
      ∧ box.highOne ≤ boxScale box ∧ box.highTwo ≤ boxScale box
      ∧ box.highThree ≤ boxScale box ∧ box.highFour ≤ boxScale box := by
  have parts : (0 ≤ box.lowOne ∧ 0 ≤ box.lowTwo ∧ 0 ≤ box.lowThree
      ∧ 0 ≤ box.lowFour) ∧ box.highOne ≤ boxScale box
      ∧ box.highTwo ≤ boxScale box ∧ box.highThree ≤ boxScale box
      ∧ box.highFour ≤ boxScale box := by
    simpa [boxIsSane, and_assoc] using sane
  exact parts

theorem reflectBox_lowsNonneg {mask : VarMask} {box : Box}
    (sane : boxIsSane box = true) :
    0 ≤ (reflectBox mask box).lowOne ∧ 0 ≤ (reflectBox mask box).lowTwo
      ∧ 0 ≤ (reflectBox mask box).lowThree
      ∧ 0 ≤ (reflectBox mask box).lowFour := by
  obtain ⟨lows, highOneLe, highTwoLe, highThreeLe, highFourLe⟩ :=
    boxIsSane_spec sane
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [reflectBox]
  · cases mask.onOne <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false] <;> omega
  · cases mask.onTwo <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false] <;> omega
  · cases mask.onThree <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false] <;> omega
  · cases mask.onFour <;> simp only [if_true, if_false, Bool.false_eq_true,
      ite_true, ite_false] <;> omega

theorem reflectCoord_nonneg {flag : Bool} {den value : Int}
    (valueNonneg : 0 ≤ value) (valueLe : value ≤ den) :
    0 ≤ reflectCoord flag den value := by
  cases flag <;> simp [reflectCoord] <;> omega

/-! ## Core sign evidence

Per core, per box, the checker derives one of five verdicts.  The strict
verdicts assert the sign of the base core's value at EVERY rational
point of `box ^ (0,1]^4`; the weak verdicts assert the direction
(`>= 0` / `<= 0`) there -- the boundary-ray grade for beta slots. -/

inductive SignEvidence where
  | strictPositive
  | strictNegative
  | weakPositive
  | weakNegative
  | undecided
deriving DecidableEq

def zeroTouchMask (box : Box) : VarMask :=
  ⟨decide (box.lowOne = 0), decide (box.lowTwo = 0),
   decide (box.lowThree = 0), decide (box.lowFour = 0)⟩

def maskHasAnyVar (mask : VarMask) : Bool :=
  mask.onOne || mask.onTwo || mask.onThree || mask.onFour

def masksAreDisjoint (left right : VarMask) : Bool :=
  !(left.onOne && right.onOne) && !(left.onTwo && right.onTwo)
    && !(left.onThree && right.onThree) && !(left.onFour && right.onFour)

/-- Positivity grade of one polynomial over one (reflected-side) box:
2 = strict at every domain point, 1 = weak (nonnegative), 0 = none. -/
def directedPositiveGrade (candidate : Poly) (reflBox : Box)
    (upperMask : VarMask) : Nat :=
  if isHomogeneousOfDegree candidate (polyLeadDegree candidate)
      && decide (0 < lowBound candidate reflBox) then 2
  else if !maskHasAnyVar (zeroTouchMask reflBox) then 0
  else if groupedScanHolds (zeroTouchMask reflBox) reflBox
      (candidate.length + 1) candidate && !candidate.isEmpty then
    if hasZeroKeyTerm (zeroTouchMask reflBox) candidate
        || masksAreDisjoint (zeroTouchMask reflBox) upperMask then 2
    else 1
  else 0

/-- Soundness of the grade over the reflected side.  The `maskedGe`
hypothesis feeds the disjoint-mask strict rule: whenever the zero-touch
mask avoids the reflected coordinates, those coordinates are original
ones, hence at least `1/den`. -/
theorem directedPositiveGrade_sound (candidate : Poly) (reflBox : Box)
    (upperMask : VarMask) {den one two three four : Int}
    (denPos : 0 < den)
    (lowsNonneg : 0 ≤ reflBox.lowOne ∧ 0 ≤ reflBox.lowTwo
      ∧ 0 ≤ reflBox.lowThree ∧ 0 ≤ reflBox.lowFour)
    (pointNonneg : 0 ≤ one ∧ 0 ≤ two ∧ 0 ≤ three ∧ 0 ≤ four)
    (unmaskedGe : (upperMask.onOne = false → 1 ≤ one)
      ∧ (upperMask.onTwo = false → 1 ≤ two)
      ∧ (upperMask.onThree = false → 1 ≤ three)
      ∧ (upperMask.onFour = false → 1 ≤ four))
    (membership : PointLiesInBox reflBox den one two three four) :
    (directedPositiveGrade candidate reflBox upperMask = 2
      → 0 < polyEval candidate den one two three four)
    ∧ (directedPositiveGrade candidate reflBox upperMask = 1
      → 0 ≤ polyEval candidate den one two three four) := by
  unfold directedPositiveGrade
  split
  · next plainFired =>
      have plainParts := Bool.and_eq_true_iff.mp plainFired
      have boundPos : 0 < lowBound candidate reflBox :=
        of_decide_eq_true plainParts.2
      have valuePos : 0 < polyEval candidate den one two three four :=
        evalPos_of_lowBound_pos boundPos plainParts.1 denPos lowsNonneg
          pointNonneg membership
      exact ⟨fun _ => valuePos, fun _ => Int.le_of_lt valuePos⟩
  · split
    · exact ⟨fun contra => absurd contra (by omega),
        fun contra => absurd contra (by omega)⟩
    · next hasZeroVar =>
        split
        · next scanFired =>
            have scanParts := Bool.and_eq_true_iff.mp scanFired
            have scanTrue := scanParts.1
            have nonempty : candidate ≠ [] := by
              intro contra
              subst contra
              simp [List.isEmpty] at scanFired
            have weakClaim : 0 ≤ polyEval candidate den one two three four :=
              groupedScanHolds_nonneg (zeroTouchMask reflBox) reflBox
                (candidate.length + 1) candidate scanTrue denPos lowsNonneg
                pointNonneg membership
            split
            · next strictRule =>
                refine ⟨fun _ => ?_, fun _ => weakClaim⟩
                cases Bool.or_eq_true_iff.mp strictRule with
                | inl zeroKeyRule =>
                    exact groupedScanHolds_pos_of_zeroKey
                      (zeroTouchMask reflBox) reflBox
                      (candidate.length + 1) candidate scanTrue zeroKeyRule
                      denPos lowsNonneg pointNonneg membership
                | inr disjointRule =>
                    have disjointParts :
                        (!(( zeroTouchMask reflBox).onOne && upperMask.onOne)) = true
                        ∧ (!((zeroTouchMask reflBox).onTwo && upperMask.onTwo)) = true
                        ∧ (!((zeroTouchMask reflBox).onThree && upperMask.onThree)) = true
                        ∧ (!((zeroTouchMask reflBox).onFour && upperMask.onFour)) = true := by
                      simpa [masksAreDisjoint, and_assoc] using disjointRule
                    have maskedGe : MaskedCoordsAtLeastOne
                        (zeroTouchMask reflBox) one two three four := by
                      refine ⟨?_, ?_, ?_, ?_⟩
                      · intro flagOn
                        apply unmaskedGe.1
                        have := disjointParts.1
                        rw [flagOn] at this
                        simpa using this
                      · intro flagOn
                        apply unmaskedGe.2.1
                        have := disjointParts.2.1
                        rw [flagOn] at this
                        simpa using this
                      · intro flagOn
                        apply unmaskedGe.2.2.1
                        have := disjointParts.2.2.1
                        rw [flagOn] at this
                        simpa using this
                      · intro flagOn
                        apply unmaskedGe.2.2.2
                        have := disjointParts.2.2.2
                        rw [flagOn] at this
                        simpa using this
                    exact groupedScanHolds_pos_of_maskedPositive
                      (zeroTouchMask reflBox) reflBox
                      (candidate.length + 1) candidate scanTrue nonempty
                      maskedGe denPos lowsNonneg pointNonneg membership
            · exact ⟨fun contra => absurd contra (by omega),
                fun _ => weakClaim⟩
        · exact ⟨fun contra => absurd contra (by omega),
            fun contra => absurd contra (by omega)⟩

/-- The five-way core sign verdict on a box. -/
def signEvidenceOfGrades (posGrade negGrade : Nat) : SignEvidence :=
  if posGrade = 2 then .strictPositive
  else if negGrade = 2 then .strictNegative
  else if posGrade = 1 then .weakPositive
  else if negGrade = 1 then .weakNegative
  else .undecided

def coreSignEvidence (data : ChartData) (box : Box) (coreIndex : Nat) :
    SignEvidence :=
  match variantPolyForBox data box coreIndex with
  | none => .undecided
  | some variantPoly =>
      signEvidenceOfGrades
        (directedPositiveGrade variantPoly
          (reflectBox (maskOfCode (maskCodeOfBox box)) box)
          (maskOfCode (maskCodeOfBox box)))
        (directedPositiveGrade (polyNeg variantPoly)
          (reflectBox (maskOfCode (maskCodeOfBox box)) box)
          (maskOfCode (maskCodeOfBox box)))

/-- MASTER LEMMA: what each verdict of `coreSignEvidence` asserts about
the base core's value at every rational point of `box ^ (0,1]^4`. -/
theorem coreSignEvidence_sound (data : ChartData) (box : Box)
    (coreIndex : Nat) {den one two three four : Int}
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    (coreSignEvidence data box coreIndex = .strictPositive
      → 0 < polyEval (coreAt data.cores coreIndex) den one two three four)
    ∧ (coreSignEvidence data box coreIndex = .strictNegative
      → polyEval (coreAt data.cores coreIndex) den one two three four < 0)
    ∧ (coreSignEvidence data box coreIndex = .weakPositive
      → 0 ≤ polyEval (coreAt data.cores coreIndex) den one two three four)
    ∧ (coreSignEvidence data box coreIndex = .weakNegative
      → polyEval (coreAt data.cores coreIndex) den one two three four
        ≤ 0) := by
  obtain ⟨denGe, oneGe, oneLe, twoGe, twoLe, threeGe, threeLe, fourGe,
    fourLe⟩ := domain
  cases lookupResult : variantPolyForBox data box coreIndex with
  | none =>
      have evidenceForm : coreSignEvidence data box coreIndex
          = .undecided := by
        unfold coreSignEvidence
        rw [lookupResult]
      rw [evidenceForm]
      exact ⟨fun contra => absurd contra (by decide), fun contra => absurd contra (by decide),
        fun contra => absurd contra (by decide), fun contra => absurd contra (by decide)⟩
  | some variantPoly =>
      have evidenceForm : coreSignEvidence data box coreIndex
          = signEvidenceOfGrades
            (directedPositiveGrade variantPoly
              (reflectBox (maskOfCode (maskCodeOfBox box)) box)
              (maskOfCode (maskCodeOfBox box)))
            (directedPositiveGrade (polyNeg variantPoly)
              (reflectBox (maskOfCode (maskCodeOfBox box)) box)
              (maskOfCode (maskCodeOfBox box))) := by
        unfold coreSignEvidence
        rw [lookupResult]
      rw [evidenceForm]
      have transferEq := variantValue_eq_baseValue variantsOk lookupResult
        den one two three four
      have reflMembership := pointLiesInBox_reflectBox
        (mask := maskOfCode (maskCodeOfBox box)) membership
      have reflLows := reflectBox_lowsNonneg
        (mask := maskOfCode (maskCodeOfBox box)) sane
      have reflPointNonneg :
          0 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onOne den one
          ∧ 0 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onTwo den two
          ∧ 0 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onThree den three
          ∧ 0 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onFour den four :=
        ⟨reflectCoord_nonneg (by omega) oneLe,
         reflectCoord_nonneg (by omega) twoLe,
         reflectCoord_nonneg (by omega) threeLe,
         reflectCoord_nonneg (by omega) fourLe⟩
      have unmaskedGe :
          ((maskOfCode (maskCodeOfBox box)).onOne = false
            → 1 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onOne den one)
          ∧ ((maskOfCode (maskCodeOfBox box)).onTwo = false
            → 1 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onTwo den two)
          ∧ ((maskOfCode (maskCodeOfBox box)).onThree = false
            → 1 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onThree den
                three)
          ∧ ((maskOfCode (maskCodeOfBox box)).onFour = false
            → 1 ≤ reflectCoord (maskOfCode (maskCodeOfBox box)).onFour den
                four) := by
        refine ⟨fun flagOff => ?_, fun flagOff => ?_, fun flagOff => ?_,
          fun flagOff => ?_⟩ <;> rw [flagOff] <;>
          simp [reflectCoord] <;> omega
      have posGradeSound := directedPositiveGrade_sound variantPoly
        (reflectBox (maskOfCode (maskCodeOfBox box)) box)
        (maskOfCode (maskCodeOfBox box)) (by omega) reflLows
        reflPointNonneg unmaskedGe reflMembership
      have negGradeSound := directedPositiveGrade_sound (polyNeg variantPoly)
        (reflectBox (maskOfCode (maskCodeOfBox box)) box)
        (maskOfCode (maskCodeOfBox box)) (by omega) reflLows
        reflPointNonneg unmaskedGe reflMembership
      have negValueEq := polyEval_neg variantPoly den
        (reflectCoord (maskOfCode (maskCodeOfBox box)).onOne den one)
        (reflectCoord (maskOfCode (maskCodeOfBox box)).onTwo den two)
        (reflectCoord (maskOfCode (maskCodeOfBox box)).onThree den three)
        (reflectCoord (maskOfCode (maskCodeOfBox box)).onFour den four)
      rw [transferEq] at negValueEq
      rw [transferEq] at posGradeSound
      rw [negValueEq] at negGradeSound
      by_cases posTwo : directedPositiveGrade variantPoly
          (reflectBox (maskOfCode (maskCodeOfBox box)) box)
          (maskOfCode (maskCodeOfBox box)) = 2
      · rw [signEvidenceOfGrades, if_pos posTwo]
        exact ⟨fun _ => posGradeSound.1 posTwo,
          fun contra => absurd contra (by decide), fun contra => absurd contra (by decide),
          fun contra => absurd contra (by decide)⟩
      by_cases negTwo : directedPositiveGrade (polyNeg variantPoly)
          (reflectBox (maskOfCode (maskCodeOfBox box)) box)
          (maskOfCode (maskCodeOfBox box)) = 2
      · rw [signEvidenceOfGrades, if_neg posTwo, if_pos negTwo]
        refine ⟨fun contra => absurd contra (by decide), fun _ => ?_,
          fun contra => absurd contra (by decide), fun contra => absurd contra (by decide)⟩
        have := negGradeSound.1 negTwo
        omega
      by_cases posOne : directedPositiveGrade variantPoly
          (reflectBox (maskOfCode (maskCodeOfBox box)) box)
          (maskOfCode (maskCodeOfBox box)) = 1
      · rw [signEvidenceOfGrades, if_neg posTwo, if_neg negTwo,
          if_pos posOne]
        exact ⟨fun contra => absurd contra (by decide), fun contra => absurd contra (by decide),
          fun _ => posGradeSound.2 posOne, fun contra => absurd contra (by decide)⟩
      by_cases negOne : directedPositiveGrade (polyNeg variantPoly)
          (reflectBox (maskOfCode (maskCodeOfBox box)) box)
          (maskOfCode (maskCodeOfBox box)) = 1
      · rw [signEvidenceOfGrades, if_neg posTwo, if_neg negTwo,
          if_neg posOne, if_pos negOne]
        refine ⟨fun contra => absurd contra (by decide), fun contra => absurd contra (by decide),
          fun contra => absurd contra (by decide), fun _ => ?_⟩
        have := negGradeSound.2 negOne
        omega
      · rw [signEvidenceOfGrades, if_neg posTwo, if_neg negTwo,
          if_neg posOne, if_neg negOne]
        exact ⟨fun contra => absurd contra (by decide), fun contra => absurd contra (by decide),
          fun contra => absurd contra (by decide), fun contra => absurd contra (by decide)⟩

/-! ## Power parity helpers -/

theorem mul_nonpos_of_nonneg_of_nonpos {left right : Int}
    (leftNonneg : 0 ≤ left) (rightNonpos : right ≤ 0) : left * right ≤ 0 := by
  have scaled : left * right ≤ left * 0 :=
    Int.mul_le_mul_of_nonneg_left rightNonpos leftNonneg
  simpa using scaled

theorem mul_neg_of_pos_of_neg {left right : Int} (leftPos : 0 < left)
    (rightNeg : right < 0) : left * right < 0 := by
  have negPos : 0 < left * -right := Int.mul_pos leftPos (by omega)
  have expand : left * -right = -(left * right) := Int.mul_neg left right
  omega

theorem intPow_pos_of_even {value : Int} (valueNe : value ≠ 0) {mult : Nat}
    (multEven : mult % 2 = 0) : 0 < intPow value mult := by
  have decompose : mult = mult / 2 * 2 := by omega
  rw [decompose]
  exact intPow_even_pos valueNe (mult / 2)

theorem intPow_nonneg_of_even (value : Int) {mult : Nat}
    (multEven : mult % 2 = 0) : 0 ≤ intPow value mult := by
  have decompose : mult = mult / 2 * 2 := by omega
  rw [decompose]
  exact intPow_even_nonneg value (mult / 2)

theorem intPow_neg_of_odd {value : Int} (valueNeg : value < 0) {mult : Nat}
    (multOdd : mult % 2 = 1) : intPow value mult < 0 := by
  have decompose : mult = mult / 2 * 2 + 1 := by omega
  rw [decompose, intPow_add]
  have evenPos : 0 < intPow value (mult / 2 * 2) :=
    intPow_even_pos (by omega) (mult / 2)
  have oneForm : intPow value 1 = value := by
    show intPow value 0 * value = value
    rw [intPow_zero, Int.one_mul]
  rw [oneForm]
  exact mul_neg_of_pos_of_neg evenPos valueNeg

theorem intPow_nonpos_of_odd {value : Int} (valueNonpos : value ≤ 0)
    {mult : Nat} (multOdd : mult % 2 = 1) : intPow value mult ≤ 0 := by
  have decompose : mult = mult / 2 * 2 + 1 := by omega
  rw [decompose, intPow_add]
  have evenNonneg : 0 ≤ intPow value (mult / 2 * 2) :=
    intPow_even_nonneg value (mult / 2)
  have oneForm : intPow value 1 = value := by
    show intPow value 0 * value = value
    rw [intPow_zero, Int.one_mul]
  rw [oneForm]
  exact mul_nonpos_of_nonneg_of_nonpos evenNonneg valueNonpos

/-! ## Triple values: the objects the window package speaks about -/

def tripleFactorsValue (cores : List Poly) (factors : List FactorRef)
    (den one two three four : Int) : Int :=
  match factors with
  | [] => 1
  | ref :: rest =>
      intPow (polyEval (coreAt cores ref.coreIndex) den one two three four)
        ref.multiplicity
      * tripleFactorsValue cores rest den one two three four

def tripleValueAt (data : ChartData) (t : TripleData)
    (den one two three four : Int) : Int :=
  t.sign * tripleFactorsValue data.cores t.factors den one two three four

/-! ## Strict triple signs -/

def strictFactorsSign (data : ChartData) (box : Box) :
    List FactorRef → Option Int
  | [] => some 1
  | ref :: rest =>
      match strictFactorsSign data box rest with
      | none => none
      | some restSign =>
          match coreSignEvidence data box ref.coreIndex with
          | .strictPositive => some restSign
          | .strictNegative =>
              some (if ref.multiplicity % 2 = 1 then -restSign else restSign)
          | _ => none

def strictTripleSign (data : ChartData) (box : Box) (t : TripleData) :
    Option Int :=
  if t.sign = 0 then none
  else (strictFactorsSign data box t.factors).map (t.sign * ·)

theorem strictFactorsSign_sound (data : ChartData) (box : Box)
    (factors : List FactorRef) {factorSign : Int}
    {den one two three four : Int}
    (scan : strictFactorsSign data box factors = some factorSign)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    0 < factorSign
      * tripleFactorsValue data.cores factors den one two three four := by
  induction factors generalizing factorSign with
  | nil =>
      have signOne : factorSign = 1 := by
        have := Option.some.inj scan
        omega
      rw [signOne]
      show (0 : Int) < 1 * 1
      omega
  | cons ref rest ih =>
      unfold strictFactorsSign at scan
      cases restScan : strictFactorsSign data box rest with
      | none => rw [restScan] at scan; exact absurd scan (by simp)
      | some restSign =>
          rw [restScan] at scan
          have restClaim := ih restScan
          have coreClaims := coreSignEvidence_sound data box ref.coreIndex
            variantsOk sane domain membership
          cases evidence : coreSignEvidence data box ref.coreIndex with
          | strictPositive =>
              rw [evidence] at scan
              have signForm : factorSign = restSign := (Option.some.inj scan).symm
              have corePos := coreClaims.1 evidence
              have powPos : 0 < intPow (polyEval
                  (coreAt data.cores ref.coreIndex) den one two three four)
                  ref.multiplicity := intPow_pos corePos ref.multiplicity
              rw [signForm]
              show 0 < restSign * (intPow _ ref.multiplicity
                * tripleFactorsValue data.cores rest den one two three four)
              have rearranged : restSign * (intPow (polyEval
                    (coreAt data.cores ref.coreIndex) den one two three four)
                    ref.multiplicity
                  * tripleFactorsValue data.cores rest den one two three four)
                  = intPow (polyEval (coreAt data.cores ref.coreIndex)
                      den one two three four) ref.multiplicity
                    * (restSign * tripleFactorsValue data.cores rest
                        den one two three four) := by
                simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
              rw [rearranged]
              exact Int.mul_pos powPos restClaim
          | strictNegative =>
              rw [evidence] at scan
              have coreNeg := coreClaims.2.1 evidence
              have signForm : factorSign
                  = if ref.multiplicity % 2 = 1 then -restSign
                    else restSign := (Option.some.inj scan).symm
              by_cases multOdd : ref.multiplicity % 2 = 1
              · have powNeg := intPow_neg_of_odd coreNeg multOdd
                rw [signForm, if_pos multOdd]
                show 0 < -restSign * (intPow _ ref.multiplicity
                  * tripleFactorsValue data.cores rest den one two three four)
                have rearranged : -restSign * (intPow (polyEval
                      (coreAt data.cores ref.coreIndex) den one two three
                      four) ref.multiplicity
                    * tripleFactorsValue data.cores rest den one two three
                        four)
                    = -(intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity)
                      * (restSign * tripleFactorsValue data.cores rest
                          den one two three four) := by
                  simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
                rw [rearranged]
                exact Int.mul_pos (Int.neg_pos.mpr powNeg) restClaim
              · have multEven : ref.multiplicity % 2 = 0 := by omega
                have powPos := intPow_pos_of_even (Int.ne_of_lt coreNeg)
                  multEven
                rw [signForm, if_neg multOdd]
                show 0 < restSign * (intPow _ ref.multiplicity
                  * tripleFactorsValue data.cores rest den one two three four)
                have rearranged : restSign * (intPow (polyEval
                      (coreAt data.cores ref.coreIndex) den one two three
                      four) ref.multiplicity
                    * tripleFactorsValue data.cores rest den one two three
                        four)
                    = intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity
                      * (restSign * tripleFactorsValue data.cores rest
                          den one two three four) := by
                  simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
                rw [rearranged]
                exact Int.mul_pos powPos restClaim
          | weakPositive => rw [evidence] at scan; exact absurd scan (by simp)
          | weakNegative => rw [evidence] at scan; exact absurd scan (by simp)
          | undecided => rw [evidence] at scan; exact absurd scan (by simp)

/-- Strict triple sign soundness: the claimed sign times the triple's
value is positive (the sign square makes garbage magnitudes harmless). -/
theorem strictTripleSign_sound (data : ChartData) (box : Box)
    (t : TripleData) {tripleSign : Int} {den one two three four : Int}
    (scan : strictTripleSign data box t = some tripleSign)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    0 < tripleSign * tripleValueAt data t den one two three four := by
  unfold strictTripleSign at scan
  split at scan
  · exact absurd scan (by simp)
  · next signNonzero =>
      cases factorScan : strictFactorsSign data box t.factors with
      | none => rw [factorScan] at scan; exact absurd scan (by simp)
      | some factorSign =>
          rw [factorScan] at scan
          have signForm : tripleSign = t.sign * factorSign :=
            (Option.some.inj (by simpa using scan)).symm
          have factorClaim := strictFactorsSign_sound data box t.factors
            factorScan variantsOk sane domain membership
          have signSquarePos : 0 < t.sign * t.sign :=
            mul_self_pos_of_ne_zero signNonzero
          unfold tripleValueAt
          rw [signForm]
          have rearranged : t.sign * factorSign
              * (t.sign * tripleFactorsValue data.cores t.factors den one
                  two three four)
              = (t.sign * t.sign) * (factorSign
                * tripleFactorsValue data.cores t.factors den one two three
                    four) := by
            simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
          rw [rearranged]
          exact Int.mul_pos signSquarePos factorClaim

/-! ## Weak and guarded slot directions (the boundary-ray grade)

A beta slot only needs a certified DIRECTION: even-multiplicity cores are
skipped (squares), odd-multiplicity cores contribute weak or strict sign
evidence, and in the guarded form exactly one odd-multiplicity core -- the
pivot -- may stay undecided.  The soundness statements are uniform over a
pivot orientation `sigma`: `0 <= sigma * pivotValue` resolves every
guarded slot in direction `condSign used sigma * dir`. -/

def condSign (usedGuard : Bool) (sigma : Int) : Int :=
  if usedGuard then sigma else 1

/-- Factor scan with one permitted undecided odd core (the pivot). -/
def guardFactorsScan (data : ChartData) (box : Box) (guardCoreIndex : Nat) :
    List FactorRef → Option (Int × Bool)
  | [] => some (1, false)
  | ref :: rest =>
      match guardFactorsScan data box guardCoreIndex rest with
      | none => none
      | some (restDir, restUsed) =>
          if ref.multiplicity % 2 = 0 then some (restDir, restUsed)
          else match coreSignEvidence data box ref.coreIndex with
            | .strictPositive => some (restDir, restUsed)
            | .weakPositive => some (restDir, restUsed)
            | .strictNegative => some (-restDir, restUsed)
            | .weakNegative => some (-restDir, restUsed)
            | .undecided =>
                if ref.coreIndex = guardCoreIndex ∧ restUsed = false then
                  some (restDir, true)
                else none

/-- Slot scan: neutral slots report direction zero; live slots must carry
a unit sign. -/
def guardSlotScan (data : ChartData) (box : Box) (guardCoreIndex : Nat)
    (t : TripleData) : Option (Int × Bool) :=
  if t.sign = 0 then some (0, false)
  else if t.sign = 1 ∨ t.sign = -1 then
    match guardFactorsScan data box guardCoreIndex t.factors with
    | none => none
    | some (factorDir, usedGuard) => some (t.sign * factorDir, usedGuard)
  else none

/-- The pivot value the guarded scans are conditioned on. -/
def guardValueAt (data : ChartData) (guardCoreIndex : Nat)
    (den one two three four : Int) : Int :=
  polyEval (coreAt data.cores guardCoreIndex) den one two three four

theorem guardFactorsScan_sound (data : ChartData) (box : Box)
    (guardCoreIndex : Nat) (factors : List FactorRef)
    {factorDir : Int} {usedGuard : Bool} {sigma : Int}
    {den one two three four : Int}
    (scan : guardFactorsScan data box guardCoreIndex factors
      = some (factorDir, usedGuard))
    (sigmaUnit : sigma = 1 ∨ sigma = -1)
    (pivotDirected : 0 ≤ sigma
      * guardValueAt data guardCoreIndex den one two three four)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    (factorDir = 1 ∨ factorDir = -1)
      ∧ 0 ≤ condSign usedGuard sigma * factorDir
        * tripleFactorsValue data.cores factors den one two three four := by
  induction factors generalizing factorDir usedGuard with
  | nil =>
      obtain ⟨dirEq, usedEq⟩ : 1 = factorDir ∧ false = usedGuard := by
        have pairEq := Option.some.inj scan
        exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
      subst dirEq
      subst usedEq
      exact ⟨Or.inl rfl, by simp [condSign, tripleFactorsValue]⟩
  | cons ref rest ih =>
      unfold guardFactorsScan at scan
      cases restScan : guardFactorsScan data box guardCoreIndex rest with
      | none => rw [restScan] at scan; exact absurd scan (by simp)
      | some restPair =>
          obtain ⟨restDir, restUsed⟩ := restPair
          rw [restScan] at scan
          dsimp only [] at scan
          have restClaim := ih restScan
          obtain ⟨restUnit, restDirected⟩ := restClaim
          have coreClaims := coreSignEvidence_sound data box ref.coreIndex
            variantsOk sane domain membership
          have factorsValueForm : tripleFactorsValue data.cores
              (ref :: rest) den one two three four
              = intPow (polyEval (coreAt data.cores ref.coreIndex)
                  den one two three four) ref.multiplicity
                * tripleFactorsValue data.cores rest den one two three
                    four := rfl
          by_cases multEven : ref.multiplicity % 2 = 0
          · rw [if_pos multEven] at scan
            obtain ⟨dirEq, usedEq⟩ : restDir = factorDir
                ∧ restUsed = usedGuard := by
              have pairEq := Option.some.inj scan
              exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
            subst dirEq
            subst usedEq
            rw [factorsValueForm]
            refine ⟨restUnit, ?_⟩
            have powNonneg : 0 ≤ intPow (polyEval
                (coreAt data.cores ref.coreIndex) den one two three four)
                ref.multiplicity :=
              intPow_nonneg_of_even _ multEven
            have rearranged : condSign restUsed sigma * restDir
                * (intPow (polyEval (coreAt data.cores ref.coreIndex)
                    den one two three four) ref.multiplicity
                  * tripleFactorsValue data.cores rest den one two three
                      four)
                = intPow (polyEval (coreAt data.cores ref.coreIndex)
                    den one two three four) ref.multiplicity
                  * (condSign restUsed sigma * restDir
                    * tripleFactorsValue data.cores rest den one two three
                        four) := by
              simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
            rw [rearranged]
            exact Int.mul_nonneg powNonneg restDirected
          · rw [if_neg multEven] at scan
            have multOdd : ref.multiplicity % 2 = 1 := by omega
            cases evidence : coreSignEvidence data box ref.coreIndex with
            | strictPositive =>
                rw [evidence] at scan
                obtain ⟨dirEq, usedEq⟩ : restDir = factorDir ∧ restUsed = usedGuard := by
                  have pairEq := Option.some.inj scan
                  exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
                subst dirEq
                subst usedEq
                rw [factorsValueForm]
                refine ⟨restUnit, ?_⟩
                have powNonneg : 0 ≤ intPow (polyEval
                    (coreAt data.cores ref.coreIndex) den one two three
                    four) ref.multiplicity :=
                  intPow_nonneg (Int.le_of_lt (coreClaims.1 evidence)) _
                have rearranged : condSign restUsed sigma * restDir
                    * (intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity
                      * tripleFactorsValue data.cores rest den one two
                          three four)
                    = intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity
                      * (condSign restUsed sigma * restDir
                        * tripleFactorsValue data.cores rest den one two
                            three four) := by
                  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
                rw [rearranged]
                exact Int.mul_nonneg powNonneg restDirected
            | weakPositive =>
                rw [evidence] at scan
                obtain ⟨dirEq, usedEq⟩ : restDir = factorDir ∧ restUsed = usedGuard := by
                  have pairEq := Option.some.inj scan
                  exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
                subst dirEq
                subst usedEq
                rw [factorsValueForm]
                refine ⟨restUnit, ?_⟩
                have powNonneg : 0 ≤ intPow (polyEval
                    (coreAt data.cores ref.coreIndex) den one two three
                    four) ref.multiplicity :=
                  intPow_nonneg (coreClaims.2.2.1 evidence) _
                have rearranged : condSign restUsed sigma * restDir
                    * (intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity
                      * tripleFactorsValue data.cores rest den one two
                          three four)
                    = intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity
                      * (condSign restUsed sigma * restDir
                        * tripleFactorsValue data.cores rest den one two
                            three four) := by
                  simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
                rw [rearranged]
                exact Int.mul_nonneg powNonneg restDirected
            | strictNegative =>
                rw [evidence] at scan
                obtain ⟨dirEq, usedEq⟩ : -restDir = factorDir ∧ restUsed = usedGuard := by
                  have pairEq := Option.some.inj scan
                  exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
                subst dirEq
                subst usedEq
                rw [factorsValueForm]
                refine ⟨by omega, ?_⟩
                have powNonpos : intPow (polyEval
                    (coreAt data.cores ref.coreIndex) den one two three
                    four) ref.multiplicity ≤ 0 :=
                  intPow_nonpos_of_odd
                    (Int.le_of_lt (coreClaims.2.1 evidence)) multOdd
                have rearranged : condSign restUsed sigma * -restDir
                    * (intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity
                      * tripleFactorsValue data.cores rest den one two
                          three four)
                    = -(intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity)
                      * (condSign restUsed sigma * restDir
                        * tripleFactorsValue data.cores rest den one two
                            three four) := by
                  simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc,
                    Int.mul_comm, Int.mul_left_comm]
                rw [rearranged]
                exact Int.mul_nonneg (by omega) restDirected
            | weakNegative =>
                rw [evidence] at scan
                obtain ⟨dirEq, usedEq⟩ : -restDir = factorDir ∧ restUsed = usedGuard := by
                  have pairEq := Option.some.inj scan
                  exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
                subst dirEq
                subst usedEq
                rw [factorsValueForm]
                refine ⟨by omega, ?_⟩
                have powNonpos : intPow (polyEval
                    (coreAt data.cores ref.coreIndex) den one two three
                    four) ref.multiplicity ≤ 0 :=
                  intPow_nonpos_of_odd (coreClaims.2.2.2 evidence) multOdd
                have rearranged : condSign restUsed sigma * -restDir
                    * (intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity
                      * tripleFactorsValue data.cores rest den one two
                          three four)
                    = -(intPow (polyEval (coreAt data.cores ref.coreIndex)
                        den one two three four) ref.multiplicity)
                      * (condSign restUsed sigma * restDir
                        * tripleFactorsValue data.cores rest den one two
                            three four) := by
                  simp [Int.neg_mul, Int.mul_neg, Int.mul_assoc,
                    Int.mul_comm, Int.mul_left_comm]
                rw [rearranged]
                exact Int.mul_nonneg (by omega) restDirected
            | undecided =>
                rw [evidence] at scan
                dsimp only [] at scan
                split at scan
                · next guardHit =>
                    obtain ⟨coreIsGuard, notUsedYet⟩ := guardHit
                    obtain ⟨dirEq, usedEq⟩ : restDir
                        = factorDir ∧ true = usedGuard := by
                      have pairEq := Option.some.inj scan
                      exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
                    subst dirEq
                    subst usedEq
                    rw [factorsValueForm, coreIsGuard]
                    have guardValueForm : polyEval
                        (coreAt data.cores guardCoreIndex) den one two three
                        four
                        = guardValueAt data guardCoreIndex den one two three
                            four := rfl
                    rw [guardValueForm]
                    refine ⟨restUnit, ?_⟩
                    rw [notUsedYet] at restDirected
                    have sigmaPowNonneg : 0 ≤ sigma * intPow
                        (guardValueAt data guardCoreIndex den one two three
                          four) ref.multiplicity := by
                      have decompose : ref.multiplicity
                          = ref.multiplicity / 2 * 2 + 1 := by omega
                      rw [decompose, intPow_add]
                      have evenNonneg : 0 ≤ intPow (guardValueAt data
                          guardCoreIndex den one two three four)
                          (ref.multiplicity / 2 * 2) :=
                        intPow_even_nonneg _ _
                      have oneForm : intPow (guardValueAt data
                          guardCoreIndex den one two three four) 1
                          = guardValueAt data guardCoreIndex den one two
                              three four := by
                        show intPow _ 0 * _ = _
                        rw [intPow_zero, Int.one_mul]
                      rw [oneForm]
                      have rearranged : sigma * (intPow (guardValueAt data
                          guardCoreIndex den one two three four)
                          (ref.multiplicity / 2 * 2)
                          * guardValueAt data guardCoreIndex den one two
                              three four)
                          = intPow (guardValueAt data guardCoreIndex den
                              one two three four)
                              (ref.multiplicity / 2 * 2)
                            * (sigma * guardValueAt data guardCoreIndex
                                den one two three four) := by
                        simp [Int.mul_assoc, Int.mul_comm,
                          Int.mul_left_comm]
                      rw [rearranged]
                      exact Int.mul_nonneg evenNonneg pivotDirected
                    have rearranged : condSign true sigma * restDir
                        * (intPow (guardValueAt data guardCoreIndex den one
                            two three four) ref.multiplicity
                          * tripleFactorsValue data.cores rest den one two
                              three four)
                        = (sigma * intPow (guardValueAt data guardCoreIndex
                            den one two three four) ref.multiplicity)
                          * (condSign false sigma * restDir
                            * tripleFactorsValue data.cores rest den one
                                two three four) := by
                      simp [condSign, Int.mul_assoc, Int.mul_comm,
                        Int.mul_left_comm]
                    rw [rearranged]
                    exact Int.mul_nonneg sigmaPowNonneg restDirected
                · exact absurd scan (by simp)

/-- Slot-level guarded direction soundness. -/
theorem guardSlotScan_sound (data : ChartData) (box : Box)
    (guardCoreIndex : Nat) (t : TripleData) {slotDir : Int}
    {usedGuard : Bool} {sigma den one two three four : Int}
    (scan : guardSlotScan data box guardCoreIndex t
      = some (slotDir, usedGuard))
    (sigmaUnit : sigma = 1 ∨ sigma = -1)
    (pivotDirected : 0 ≤ sigma
      * guardValueAt data guardCoreIndex den one two three four)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    (slotDir = 0 → tripleValueAt data t den one two three four = 0)
      ∧ (slotDir = 0 ∨ slotDir = 1 ∨ slotDir = -1)
      ∧ 0 ≤ condSign usedGuard sigma * slotDir
        * tripleValueAt data t den one two three four := by
  unfold guardSlotScan at scan
  split at scan
  · next signZero =>
      obtain ⟨dirEq, usedEq⟩ : (0 : Int) = slotDir ∧ false = usedGuard := by
        have pairEq := Option.some.inj scan
        exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
      subst dirEq
      subst usedEq
      have valueZero : tripleValueAt data t den one two three four = 0 := by
        unfold tripleValueAt
        rw [signZero, Int.zero_mul]
      refine ⟨fun _ => valueZero, Or.inl rfl, ?_⟩
      rw [valueZero]
      simp
  · split at scan
    · next signUnit =>
        cases factorScan : guardFactorsScan data box guardCoreIndex
            t.factors with
        | none => rw [factorScan] at scan; exact absurd scan (by simp)
        | some factorPair =>
            obtain ⟨factorDir, factorUsed⟩ := factorPair
            rw [factorScan] at scan
            dsimp only [] at scan
            obtain ⟨dirEq, usedEq⟩ : t.sign * factorDir = slotDir
                ∧ factorUsed = usedGuard := by
              have pairEq := Option.some.inj scan
              exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
            subst dirEq
            subst usedEq
            obtain ⟨factorUnit, factorDirected⟩ := guardFactorsScan_sound
              data box guardCoreIndex t.factors factorScan sigmaUnit
              pivotDirected variantsOk sane domain membership
            refine ⟨?_, ?_, ?_⟩
            · intro contra
              rcases signUnit with signIs | signIs <;>
                rcases factorUnit with dirIs | dirIs <;>
                rw [signIs, dirIs] at contra <;>
                exact absurd contra (by decide)
            · rcases signUnit with signIs | signIs <;>
                rcases factorUnit with dirIs | dirIs <;>
                rw [signIs, dirIs] <;> decide
            · unfold tripleValueAt
              have rearranged : condSign factorUsed sigma
                  * (t.sign * factorDir)
                  * (t.sign * tripleFactorsValue data.cores t.factors den
                      one two three four)
                  = (t.sign * t.sign) * (condSign factorUsed sigma
                    * factorDir * tripleFactorsValue data.cores t.factors
                        den one two three four) := by
                simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
              rw [rearranged]
              have signSquareOne : t.sign * t.sign = 1 := by
                rcases signUnit with signIs | signIs <;>
                  rw [signIs] <;> decide
              rw [signSquareOne, Int.one_mul]
              exact factorDirected
    · exact absurd scan (by simp)

/-! ## The candidate-level slot fold -/

def foldBetaSlotsGuarded (data : ChartData) (box : Box)
    (guardCoreIndex : Nat) : List TripleData → Option (Int × Int)
  | [] => some (2, 2)
  | slot :: rest =>
      match foldBetaSlotsGuarded data box guardCoreIndex rest with
      | none => none
      | some (restCommon, restPending) =>
          match guardSlotScan data box guardCoreIndex slot with
          | none => none
          | some (slotDir, usedGuard) =>
              if slotDir = 0 then
                if usedGuard then none else some (restCommon, restPending)
              else if slotDir = 1 ∨ slotDir = -1 then
                if usedGuard then
                  if restPending = 2 ∨ restPending = slotDir then
                    some (restCommon, slotDir)
                  else none
                else
                  if restCommon = 2 ∨ restCommon = slotDir then
                    some (slotDir, restPending)
                  else none
              else none

/-- Bookkeeping classification of a successful fold: every slot scans to
a direction that is neutral, the common sign, or the shared pending
guard direction, and the accumulated signs are sentinels or units. -/
theorem foldBetaSlotsGuarded_classify (data : ChartData) (box : Box)
    (guardCoreIndex : Nat) (slots : List TripleData)
    {common pending : Int}
    (fold : foldBetaSlotsGuarded data box guardCoreIndex slots
      = some (common, pending)) :
    (common = 2 ∨ common = 1 ∨ common = -1)
      ∧ (pending = 2 ∨ pending = 1 ∨ pending = -1)
      ∧ ∀ slot, slot ∈ slots → ∃ slotDir usedGuard,
        guardSlotScan data box guardCoreIndex slot
            = some (slotDir, usedGuard)
          ∧ (usedGuard = true → slotDir = pending
              ∧ (pending = 1 ∨ pending = -1))
          ∧ (usedGuard = false → slotDir = 0
              ∨ (slotDir = common ∧ (common = 1 ∨ common = -1))) := by
  induction slots generalizing common pending with
  | nil =>
      obtain ⟨commonEq, pendingEq⟩ : (2 : Int) = common
          ∧ (2 : Int) = pending := by
        have pairEq := Option.some.inj fold
        exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq⟩
      subst commonEq
      subst pendingEq
      exact ⟨Or.inl rfl, Or.inl rfl, fun slot slotMem => absurd slotMem
        (by simp)⟩
  | cons headSlot restSlots ih =>
      unfold foldBetaSlotsGuarded at fold
      cases restFold : foldBetaSlotsGuarded data box guardCoreIndex
          restSlots with
      | none => rw [restFold] at fold; exact absurd fold (by simp)
      | some restPair =>
          obtain ⟨restCommon, restPending⟩ := restPair
          rw [restFold] at fold
          dsimp only [] at fold
          obtain ⟨restCommonUnit, restPendingUnit, restClassify⟩ :=
            ih restFold
          cases headScan : guardSlotScan data box guardCoreIndex
              headSlot with
          | none => rw [headScan] at fold; exact absurd fold (by simp)
          | some headPair =>
              obtain ⟨slotDir, usedGuard⟩ := headPair
              rw [headScan] at fold
              dsimp only [] at fold
              split at fold
              · next dirZero =>
                  cases usedGuard with
                  | true => rw [if_pos rfl] at fold
                            exact absurd fold (by simp)
                  | false =>
                      rw [if_neg (by simp)] at fold
                      obtain ⟨commonEq, pendingEq⟩ :
                          restCommon = common ∧ restPending = pending := by
                        have pairEq := Option.some.inj fold
                        exact ⟨congrArg Prod.fst pairEq,
                          congrArg Prod.snd pairEq⟩
                      subst commonEq
                      subst pendingEq
                      refine ⟨restCommonUnit, restPendingUnit,
                        fun slot slotMem => ?_⟩
                      cases List.mem_cons.mp slotMem with
                      | inl isHead =>
                          rw [isHead]
                          exact ⟨slotDir, false, headScan,
                            fun contra => absurd contra (by simp),
                            fun _ => Or.inl dirZero⟩
                      | inr inRest => exact restClassify slot inRest
              · next dirNonzero =>
                  split at fold
                  · next dirUnit =>
                      cases usedGuard with
                      | true =>
                          rw [if_pos rfl] at fold
                          split at fold
                          · next pendingMatch =>
                              obtain ⟨commonEq, pendingEq⟩ :
                                  restCommon = common
                                  ∧ slotDir = pending := by
                                have pairEq := Option.some.inj fold
                                exact ⟨congrArg Prod.fst pairEq,
                                  congrArg Prod.snd pairEq⟩
                              subst commonEq
                              subst pendingEq
                              refine ⟨restCommonUnit,
                                Or.inr dirUnit,
                                fun slot slotMem => ?_⟩
                              cases List.mem_cons.mp slotMem with
                              | inl isHead =>
                                  rw [isHead]
                                  exact ⟨slotDir, true, headScan,
                                    fun _ => ⟨rfl, dirUnit⟩,
                                    fun contra => absurd contra (by simp)⟩
                              | inr inRest =>
                                  obtain ⟨otherDir, otherUsed, otherScan,
                                    otherGuard, otherPlain⟩ :=
                                    restClassify slot inRest
                                  refine ⟨otherDir, otherUsed, otherScan,
                                    fun isUsed => ?_, otherPlain⟩
                                  obtain ⟨otherPendingEq, otherPendingUnit⟩
                                    := otherGuard isUsed
                                  cases pendingMatch with
                                  | inl pendingWasTwo =>
                                      rw [pendingWasTwo] at otherPendingUnit
                                      rcases otherPendingUnit with contra
                                        | contra <;>
                                        exact absurd contra (by decide)
                                  | inr pendingWasDir =>
                                      rw [pendingWasDir] at otherPendingEq
                                      exact ⟨otherPendingEq, dirUnit⟩
                          · exact absurd fold (by simp)
                      | false =>
                          rw [if_neg (by simp)] at fold
                          split at fold
                          · next commonMatch =>
                              obtain ⟨commonEq, pendingEq⟩ :
                                  slotDir = common
                                  ∧ restPending = pending := by
                                have pairEq := Option.some.inj fold
                                exact ⟨congrArg Prod.fst pairEq,
                                  congrArg Prod.snd pairEq⟩
                              subst commonEq
                              subst pendingEq
                              refine ⟨Or.inr dirUnit, restPendingUnit,
                                fun slot slotMem => ?_⟩
                              cases List.mem_cons.mp slotMem with
                              | inl isHead =>
                                  rw [isHead]
                                  exact ⟨slotDir, false, headScan,
                                    fun contra => absurd contra (by simp),
                                    fun _ => Or.inr ⟨rfl, dirUnit⟩⟩
                              | inr inRest =>
                                  obtain ⟨otherDir, otherUsed, otherScan,
                                    otherGuard, otherPlain⟩ :=
                                    restClassify slot inRest
                                  refine ⟨otherDir, otherUsed, otherScan,
                                    otherGuard, fun notUsed => ?_⟩
                                  cases otherPlain notUsed with
                                  | inl isZero => exact Or.inl isZero
                                  | inr isRestCommon =>
                                      obtain ⟨dirWasCommon, commonUnit⟩ :=
                                        isRestCommon
                                      cases commonMatch with
                                      | inl commonWasTwo =>
                                          rw [commonWasTwo] at commonUnit
                                          rcases commonUnit with contra
                                            | contra <;>
                                            exact absurd contra (by decide)
                                      | inr commonWasDir =>
                                          rw [commonWasDir] at dirWasCommon
                                          exact Or.inr ⟨dirWasCommon,
                                            dirUnit⟩
                          · exact absurd fold (by simp)
                  · exact absurd fold (by simp)

/-! ## Strict checks for validity, thresholds, and margins -/

def checkStrictProductPositive (data : ChartData) (box : Box)
    (tripleA tripleB : TripleData) : Bool :=
  match strictTripleSign data box tripleA,
      strictTripleSign data box tripleB with
  | some signA, some signB => decide (0 < signA * signB)
  | _, _ => false

def checkValidity (data : ChartData) (box : Box) (th : ThresholdData) :
    Bool :=
  checkStrictProductPositive data box th.spanNum th.spanDen
    && checkStrictProductPositive data box th.massNum th.massDen

def checkMarginCondition (data : ChartData) (box : Box)
    (candIndex thrIndex : Nat) : Bool :=
  match strictTripleSign data box (candidateAt data candIndex).ratioNum,
      strictTripleSign data box (thresholdAt data thrIndex).thrDen,
      strictTripleSign data box (marginAt data candIndex thrIndex) with
  | some ratioSign, some denSign, some marginSign =>
      decide (0 < ratioSign * denSign * marginSign)
  | _, _, _ => false

def checkFreeWin (data : ChartData) (box : Box) (thrIndex : Nat) : Bool :=
  checkValidity data box (thresholdAt data thrIndex)
    && (match strictTripleSign data box (thresholdAt data thrIndex).thrNum,
          strictTripleSign data box (thresholdAt data thrIndex).thrDen with
        | some numSign, some denSign => decide (numSign * denSign < 0)
        | _, _ => false)

def checkWindowWin (data : ChartData) (box : Box)
    (candIndex thrIndex : Nat) : Bool :=
  checkValidity data box (thresholdAt data thrIndex)
    && checkMarginCondition data box candIndex thrIndex
    && (match foldBetaSlotsGuarded data box 0
          (candidateAt data candIndex).betas with
        | some (common, pending) =>
            !decide (common = 2) && decide (pending = 2)
        | none => false)

/-- Guard member check: returns the required pivot orientation. -/
def checkGuardMemberSigma (data : ChartData) (box : Box)
    (candIndex thrIndex guardCoreIndex : Nat) : Option Int :=
  if checkValidity data box (thresholdAt data thrIndex)
      && checkMarginCondition data box candIndex thrIndex then
    match foldBetaSlotsGuarded data box guardCoreIndex
        (candidateAt data candIndex).betas with
    | some (common, pending) =>
        if decide (common = 2) || decide (pending = 2) then none
        else some (pending * common)
    | none => none
  else none

def checkLeaf (data : ChartData) (box : Box) : LeafWitness → Bool
  | .windowWin candIndex thrIndex =>
      checkWindowWin data box candIndex thrIndex
  | .freeWin thrIndex => checkFreeWin data box thrIndex
  | .guardPair candP thrP candQ thrQ guardCoreIndex =>
      (match checkGuardMemberSigma data box candP thrP guardCoreIndex with
       | some sigmaP => decide (sigmaP = 1)
       | none => false)
      && (match checkGuardMemberSigma data box candQ thrQ guardCoreIndex with
       | some sigmaQ => decide (sigmaQ = -1)
       | none => false)

def checkCoverTree (data : ChartData) : Box → CoverTree → Bool
  | box, .leaf witness => boxIsSane box && checkLeaf data box witness
  | box, .node splitDim left right =>
      checkCoverTree data (splitBox box splitDim).fst left
        && checkCoverTree data (splitBox box splitDim).snd right

/-- THE CHECKER. -/
def checkChart (data : ChartData) : Bool :=
  allVariantsVerified data && checkCoverTree data rootBox data.cover

/-! ## The exported window sign package -/

/-- Validity of a through-tree threshold at a point: both defining
ratios have strictly positive numerator-denominator products. -/
def ThresholdIsValidAt (data : ChartData) (thrIndex : Nat)
    (den one two three four : Int) : Prop :=
  0 < tripleValueAt data (thresholdAt data thrIndex).spanNum den one two
        three four
      * tripleValueAt data (thresholdAt data thrIndex).spanDen den one two
        three four
    ∧ 0 < tripleValueAt data (thresholdAt data thrIndex).massNum den one
        two three four
      * tripleValueAt data (thresholdAt data thrIndex).massDen den one two
        three four

/-- A free win: the threshold itself is negative. -/
def FreeWinHoldsAt (data : ChartData) (thrIndex : Nat)
    (den one two three four : Int) : Prop :=
  tripleValueAt data (thresholdAt data thrIndex).thrNum den one two three
      four
    * tripleValueAt data (thresholdAt data thrIndex).thrDen den one two
      three four < 0

/-- A window win by a candidate against a threshold: the kernel vector is
directed (boundary-ray semantics) and the margin chain is strict. -/
def CandidateWinsAt (data : ChartData) (candIndex thrIndex : Nat)
    (den one two three four : Int) : Prop :=
  (∃ commonDir : Int, (commonDir = 1 ∨ commonDir = -1)
    ∧ ∀ slot, slot ∈ (candidateAt data candIndex).betas →
        0 ≤ commonDir * tripleValueAt data slot den one two three four)
  ∧ 0 < tripleValueAt data (candidateAt data candIndex).ratioNum den one
        two three four
      * tripleValueAt data (thresholdAt data thrIndex).thrDen den one two
        three four
      * tripleValueAt data (marginAt data candIndex thrIndex) den one two
        three four

/-- THE WINDOW SIGN PACKAGE: what a certified chart asserts at every
rational point of its half-open cube. -/
def WindowWitnessAt (data : ChartData) (den one two three four : Int) :
    Prop :=
  ∃ thrIndex, ThresholdIsValidAt data thrIndex den one two three four
    ∧ (FreeWinHoldsAt data thrIndex den one two three four
       ∨ ∃ candIndex,
          CandidateWinsAt data candIndex thrIndex den one two three four)

/-! ## Soundness of the strict checks -/

theorem product_positive_transfer {signA signB valueA valueB : Int}
    (dirA : 0 < signA * valueA) (dirB : 0 < signB * valueB)
    (signsAgree : 0 < signA * signB) : 0 < valueA * valueB := by
  have productPos : 0 < (signA * valueA) * (signB * valueB) :=
    Int.mul_pos dirA dirB
  have rearranged : (signA * valueA) * (signB * valueB)
      = (valueA * valueB) * (signA * signB) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [rearranged] at productPos
  exact pos_of_mul_pos_of_pos_right productPos signsAgree

theorem product_negative_transfer {signA signB valueA valueB : Int}
    (dirA : 0 < signA * valueA) (dirB : 0 < signB * valueB)
    (signsFlip : signA * signB < 0) : valueA * valueB < 0 := by
  have productPos : 0 < (signA * valueA) * (signB * valueB) :=
    Int.mul_pos dirA dirB
  have rearranged : (signA * valueA) * (signB * valueB)
      = (signA * signB) * (valueA * valueB) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [rearranged] at productPos
  by_cases valueNeg : valueA * valueB < 0
  · exact valueNeg
  · have valueNonneg : 0 ≤ valueA * valueB := by omega
    have nonpos : (signA * signB) * (valueA * valueB) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos valueNonneg
        (Int.le_of_lt signsFlip)
      have commuted : (signA * signB) * (valueA * valueB)
          = (valueA * valueB) * (signA * signB) := Int.mul_comm ..
      omega
    omega

theorem triple_product_positive_transfer
    {signA signB signC valueA valueB valueC : Int}
    (dirA : 0 < signA * valueA) (dirB : 0 < signB * valueB)
    (dirC : 0 < signC * valueC) (signsAgree : 0 < signA * signB * signC) :
    0 < valueA * valueB * valueC := by
  have productPos : 0 < (signA * valueA) * (signB * valueB)
      * (signC * valueC) :=
    Int.mul_pos (Int.mul_pos dirA dirB) dirC
  have rearranged : (signA * valueA) * (signB * valueB) * (signC * valueC)
      = (valueA * valueB * valueC) * (signA * signB * signC) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [rearranged] at productPos
  exact pos_of_mul_pos_of_pos_right productPos signsAgree

theorem checkValidity_sound {data : ChartData} {box : Box} {thrIndex : Nat}
    {den one two three four : Int}
    (check : checkValidity data box (thresholdAt data thrIndex) = true)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    ThresholdIsValidAt data thrIndex den one two three four := by
  have parts := Bool.and_eq_true_iff.mp check
  constructor
  · unfold checkStrictProductPositive at parts
    have spanPart := parts.1
    cases scanNum : strictTripleSign data box
        (thresholdAt data thrIndex).spanNum with
    | none => rw [scanNum] at spanPart; exact absurd spanPart (by simp)
    | some numSign =>
        cases scanDen : strictTripleSign data box
            (thresholdAt data thrIndex).spanDen with
        | none =>
            rw [scanNum, scanDen] at spanPart
            exact absurd spanPart (by simp)
        | some denSign =>
            rw [scanNum, scanDen] at spanPart
            have signsAgree : 0 < numSign * denSign :=
              of_decide_eq_true spanPart
            exact product_positive_transfer
              (strictTripleSign_sound data box _ scanNum variantsOk sane
                domain membership)
              (strictTripleSign_sound data box _ scanDen variantsOk sane
                domain membership)
              signsAgree
  · unfold checkStrictProductPositive at parts
    have massPart := parts.2
    cases scanNum : strictTripleSign data box
        (thresholdAt data thrIndex).massNum with
    | none => rw [scanNum] at massPart; exact absurd massPart (by simp)
    | some numSign =>
        cases scanDen : strictTripleSign data box
            (thresholdAt data thrIndex).massDen with
        | none =>
            rw [scanNum, scanDen] at massPart
            exact absurd massPart (by simp)
        | some denSign =>
            rw [scanNum, scanDen] at massPart
            have signsAgree : 0 < numSign * denSign :=
              of_decide_eq_true massPart
            exact product_positive_transfer
              (strictTripleSign_sound data box _ scanNum variantsOk sane
                domain membership)
              (strictTripleSign_sound data box _ scanDen variantsOk sane
                domain membership)
              signsAgree

theorem checkMarginCondition_sound {data : ChartData} {box : Box}
    {candIndex thrIndex : Nat} {den one two three four : Int}
    (check : checkMarginCondition data box candIndex thrIndex = true)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    0 < tripleValueAt data (candidateAt data candIndex).ratioNum den one
          two three four
        * tripleValueAt data (thresholdAt data thrIndex).thrDen den one two
          three four
        * tripleValueAt data (marginAt data candIndex thrIndex) den one two
          three four := by
  unfold checkMarginCondition at check
  cases scanRatio : strictTripleSign data box
      (candidateAt data candIndex).ratioNum with
  | none => rw [scanRatio] at check; exact absurd check (by simp)
  | some ratioSign =>
      cases scanDen : strictTripleSign data box
          (thresholdAt data thrIndex).thrDen with
      | none =>
          rw [scanRatio, scanDen] at check
          exact absurd check (by simp)
      | some denSign =>
          cases scanMargin : strictTripleSign data box
              (marginAt data candIndex thrIndex) with
          | none =>
              rw [scanRatio, scanDen, scanMargin] at check
              exact absurd check (by simp)
          | some marginSign =>
              rw [scanRatio, scanDen, scanMargin] at check
              have signsAgree : 0 < ratioSign * denSign * marginSign :=
                of_decide_eq_true check
              exact triple_product_positive_transfer
                (strictTripleSign_sound data box _ scanRatio variantsOk
                  sane domain membership)
                (strictTripleSign_sound data box _ scanDen variantsOk sane
                  domain membership)
                (strictTripleSign_sound data box _ scanMargin variantsOk
                  sane domain membership)
                signsAgree

/-! ## Soundness of the beta-slot folds at a point -/

/-- The directed-slots consumer: a successful fold with established
common sign directs every slot at any point where the pivot carries the
matching orientation. -/
theorem foldedSlots_directed {data : ChartData} {box : Box}
    {guardCoreIndex : Nat} {slots : List TripleData}
    {common pending sigma den one two three four : Int}
    (fold : foldBetaSlotsGuarded data box guardCoreIndex slots
      = some (common, pending))
    (commonUnit : common = 1 ∨ common = -1)
    (orientation : pending = 2 ∨ sigma = pending * common)
    (sigmaUnit : sigma = 1 ∨ sigma = -1)
    (pivotDirected : 0 ≤ sigma
      * guardValueAt data guardCoreIndex den one two three four)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    ∀ slot, slot ∈ slots →
      0 ≤ common * tripleValueAt data slot den one two three four := by
  obtain ⟨_, _, classify⟩ := foldBetaSlotsGuarded_classify data box
    guardCoreIndex slots fold
  intro slot slotMem
  obtain ⟨slotDir, usedGuard, slotScan, guardCase, plainCase⟩ :=
    classify slot slotMem
  obtain ⟨slotNeutral, _, slotDirected⟩ := guardSlotScan_sound data box
    guardCoreIndex slot slotScan sigmaUnit pivotDirected variantsOk sane
    domain membership
  cases usedGuard with
  | false =>
      cases plainCase rfl with
      | inl dirZero =>
          rw [slotNeutral dirZero]
          simp
      | inr dirCommon =>
          have slotClaim := slotDirected
          rw [dirCommon.1] at slotClaim
          have condOne : condSign false sigma = 1 := rfl
          rw [condOne, Int.one_mul] at slotClaim
          exact slotClaim
  | true =>
      obtain ⟨dirPending, pendingUnit⟩ := guardCase rfl
      have pendingReal : pending = 1 ∨ pending = -1 := pendingUnit
      have sigmaForm : sigma = pending * common := by
        cases orientation with
        | inl pendingTwo => rcases pendingReal with p | p <;> omega
        | inr oriented => exact oriented
      have slotClaim := slotDirected
      rw [dirPending] at slotClaim
      have condForm : condSign true sigma = sigma := rfl
      rw [condForm] at slotClaim
      have commonForm : sigma * pending = common := by
        rcases pendingReal with p | p <;> rcases commonUnit with c | c <;>
          rw [p, c] at sigmaForm ⊢ <;> omega
      rw [← commonForm]
      exact slotClaim

/-! ## Leaf soundness -/

theorem sigma_exists_for_point (data : ChartData) (guardCoreIndex : Nat)
    (den one two three four : Int) :
    ∃ sigma : Int, (sigma = 1 ∨ sigma = -1) ∧ 0 ≤ sigma
      * guardValueAt data guardCoreIndex den one two three four := by
  cases Int.le_total 0
      (guardValueAt data guardCoreIndex den one two three four) with
  | inl nonneg =>
      exact ⟨1, Or.inl rfl, by rw [Int.one_mul]; exact nonneg⟩
  | inr nonpos =>
      refine ⟨-1, Or.inr rfl, ?_⟩
      have : (-1 : Int) * guardValueAt data guardCoreIndex den one two
          three four
          = -(guardValueAt data guardCoreIndex den one two three four) := by
        omega
      omega

theorem checkWindowWin_sound {data : ChartData} {box : Box}
    {candIndex thrIndex : Nat} {den one two three four : Int}
    (check : checkWindowWin data box candIndex thrIndex = true)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    WindowWitnessAt data den one two three four := by
  have parts := Bool.and_eq_true_iff.mp check
  have leftParts := Bool.and_eq_true_iff.mp parts.1
  refine ⟨thrIndex, checkValidity_sound leftParts.1 variantsOk sane domain
    membership, Or.inr ⟨candIndex, ?_, checkMarginCondition_sound
      leftParts.2 variantsOk sane domain membership⟩⟩
  have betaPart := parts.2
  cases betaFold : foldBetaSlotsGuarded data box 0
      (candidateAt data candIndex).betas with
  | none => rw [betaFold] at betaPart; exact absurd betaPart (by simp)
  | some foldPair =>
      obtain ⟨common, pending⟩ := foldPair
      rw [betaFold] at betaPart
      dsimp only [] at betaPart
      have foldParts := Bool.and_eq_true_iff.mp betaPart
      have commonNotTwo : common ≠ 2 := by
        have := foldParts.1
        simp at this
        exact this
      have pendingTwo : pending = 2 := of_decide_eq_true foldParts.2
      obtain ⟨commonUnit3, _, _⟩ := foldBetaSlotsGuarded_classify data box
        0 (candidateAt data candIndex).betas betaFold
      have commonUnit : common = 1 ∨ common = -1 := by
        rcases commonUnit3 with two | rest
        · exact absurd two commonNotTwo
        · exact rest
      obtain ⟨sigma, sigmaUnit, pivotDirected⟩ :=
        sigma_exists_for_point data 0 den one two three four
      exact ⟨common, commonUnit, foldedSlots_directed betaFold commonUnit
        (Or.inl pendingTwo) sigmaUnit pivotDirected variantsOk sane domain
        membership⟩

theorem checkFreeWin_sound {data : ChartData} {box : Box} {thrIndex : Nat}
    {den one two three four : Int}
    (check : checkFreeWin data box thrIndex = true)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    WindowWitnessAt data den one two three four := by
  have parts := Bool.and_eq_true_iff.mp check
  refine ⟨thrIndex, checkValidity_sound parts.1 variantsOk sane domain
    membership, Or.inl ?_⟩
  have freePart := parts.2
  cases scanNum : strictTripleSign data box
      (thresholdAt data thrIndex).thrNum with
  | none => rw [scanNum] at freePart; exact absurd freePart (by simp)
  | some numSign =>
      cases scanDen : strictTripleSign data box
          (thresholdAt data thrIndex).thrDen with
      | none =>
          rw [scanNum, scanDen] at freePart
          exact absurd freePart (by simp)
      | some denSign =>
          rw [scanNum, scanDen] at freePart
          have signsFlip : numSign * denSign < 0 :=
            of_decide_eq_true freePart
          exact product_negative_transfer
            (strictTripleSign_sound data box _ scanNum variantsOk sane
              domain membership)
            (strictTripleSign_sound data box _ scanDen variantsOk sane
              domain membership)
            signsFlip

theorem checkGuardMemberSigma_sound {data : ChartData} {box : Box}
    {candIndex thrIndex guardCoreIndex : Nat}
    {sigmaRequired den one two three four : Int}
    (check : checkGuardMemberSigma data box candIndex thrIndex
      guardCoreIndex = some sigmaRequired)
    (sigmaUnit : sigmaRequired = 1 ∨ sigmaRequired = -1)
    (pivotDirected : 0 ≤ sigmaRequired
      * guardValueAt data guardCoreIndex den one two three four)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    ThresholdIsValidAt data thrIndex den one two three four
      ∧ CandidateWinsAt data candIndex thrIndex den one two three four := by
  unfold checkGuardMemberSigma at check
  split at check
  · next bothChecks =>
      have checkParts := Bool.and_eq_true_iff.mp bothChecks
      cases betaFold : foldBetaSlotsGuarded data box guardCoreIndex
          (candidateAt data candIndex).betas with
      | none => rw [betaFold] at check; exact absurd check (by simp)
      | some foldPair =>
          obtain ⟨common, pending⟩ := foldPair
          rw [betaFold] at check
          dsimp only [] at check
          split at check
          · exact absurd check (by simp)
          · next notSentinel =>
              have sigmaForm : pending * common = sigmaRequired :=
                Option.some.inj check
              have sentinelParts : ¬(common = 2) ∧ ¬(pending = 2) := by
                constructor <;> intro contra <;> apply notSentinel <;>
                  simp [contra]
              obtain ⟨commonUnit3, pendingUnit3, _⟩ :=
                foldBetaSlotsGuarded_classify data box guardCoreIndex
                  (candidateAt data candIndex).betas betaFold
              have commonUnit : common = 1 ∨ common = -1 := by
                rcases commonUnit3 with two | rest
                · exact absurd two sentinelParts.1
                · exact rest
              refine ⟨checkValidity_sound checkParts.1 variantsOk sane
                domain membership, ⟨common, commonUnit,
                foldedSlots_directed betaFold commonUnit
                  (Or.inr sigmaForm.symm) sigmaUnit pivotDirected
                  variantsOk sane domain membership⟩,
                checkMarginCondition_sound checkParts.2 variantsOk sane
                  domain membership⟩
  · exact absurd check (by simp)

theorem checkLeaf_sound {data : ChartData} {box : Box}
    {witness : LeafWitness} {den one two three four : Int}
    (check : checkLeaf data box witness = true)
    (variantsOk : allVariantsVerified data = true)
    (sane : boxIsSane box = true)
    (domain : PointLiesInDomain den one two three four)
    (membership : PointLiesInBox box den one two three four) :
    WindowWitnessAt data den one two three four := by
  cases witness with
  | windowWin candIndex thrIndex =>
      exact checkWindowWin_sound check variantsOk sane domain membership
  | freeWin thrIndex =>
      exact checkFreeWin_sound check variantsOk sane domain membership
  | guardPair candP thrP candQ thrQ guardCoreIndex =>
      have parts := Bool.and_eq_true_iff.mp check
      have memberP : checkGuardMemberSigma data box candP thrP
          guardCoreIndex = some 1 := by
        have partP := parts.1
        cases scanP : checkGuardMemberSigma data box candP thrP
            guardCoreIndex with
        | none => rw [scanP] at partP; exact absurd partP (by simp)
        | some sigmaP =>
            rw [scanP] at partP
            have sigmaIsOne : sigmaP = 1 := of_decide_eq_true partP
            rw [sigmaIsOne]
      have memberQ : checkGuardMemberSigma data box candQ thrQ
          guardCoreIndex = some (-1) := by
        have partQ := parts.2
        cases scanQ : checkGuardMemberSigma data box candQ thrQ
            guardCoreIndex with
        | none => rw [scanQ] at partQ; exact absurd partQ (by simp)
        | some sigmaQ =>
            rw [scanQ] at partQ
            have sigmaIsNegOne : sigmaQ = -1 := of_decide_eq_true partQ
            rw [sigmaIsNegOne]
      cases Int.le_total 0
          (guardValueAt data guardCoreIndex den one two three four) with
      | inl pivotNonneg =>
          have pivotDirected : 0 ≤ (1 : Int)
              * guardValueAt data guardCoreIndex den one two three four := by
            rw [Int.one_mul]
            exact pivotNonneg
          obtain ⟨valid, wins⟩ := checkGuardMemberSigma_sound memberP
            (Or.inl rfl) pivotDirected variantsOk sane domain membership
          exact ⟨thrP, valid, Or.inr ⟨candP, wins⟩⟩
      | inr pivotNonpos =>
          have pivotDirected : 0 ≤ (-1 : Int)
              * guardValueAt data guardCoreIndex den one two three four := by
            have negForm : (-1 : Int) * guardValueAt data guardCoreIndex
                den one two three four
                = -(guardValueAt data guardCoreIndex den one two three
                    four) := by omega
            omega
          obtain ⟨valid, wins⟩ := checkGuardMemberSigma_sound memberQ
            (Or.inr rfl) pivotDirected variantsOk sane domain membership
          exact ⟨thrQ, valid, Or.inr ⟨candQ, wins⟩⟩

/-! ## The tree walk and THE SOUNDNESS THEOREM -/

theorem checkCoverTree_sound (data : ChartData)
    (variantsOk : allVariantsVerified data = true) :
    ∀ (tree : CoverTree) (box : Box),
      checkCoverTree data box tree = true →
      ∀ {den one two three four : Int},
        PointLiesInDomain den one two three four →
        PointLiesInBox box den one two three four →
        WindowWitnessAt data den one two three four := by
  intro tree
  induction tree with
  | leaf witness =>
      intro box check den one two three four domain membership
      have parts := Bool.and_eq_true_iff.mp check
      exact checkLeaf_sound parts.2 variantsOk parts.1 domain membership
  | node splitDim left right leftSound rightSound =>
      intro box check den one two three four domain membership
      have parts := Bool.and_eq_true_iff.mp check
      cases splitBox_covers (dim := splitDim) membership with
      | inl inLeft => exact leftSound _ parts.1 domain inLeft
      | inr inRight => exact rightSound _ parts.2 domain inRight

/-- THE KERNEL-REPLAY SOUNDNESS THEOREM.  One successful `decide` on
`checkChart data` certifies the window sign package at EVERY rational
point of the half-open chart cube `(0,1]^4` -- the polynomial-semantics
form of the collar window inequality on the chart, resting on nothing
but this file's definitions and the Lean kernel. -/
theorem checkChart_sound (data : ChartData)
    (check : checkChart data = true)
    (den one two three four : Int)
    (domain : PointLiesInDomain den one two three four) :
    WindowWitnessAt data den one two three four := by
  have parts := Bool.and_eq_true_iff.mp check
  exact checkCoverTree_sound data parts.1 data.cover rootBox parts.2
    domain (rootBox_covers domain)

end Gtz.CollarReplay

