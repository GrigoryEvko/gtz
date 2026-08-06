/-!
# The M(K4) collar margin identities (GTZ rung 14, obligation (7c))

Self-contained Lean 4 payload -- no imports.  MEASURED AXIOM AUDIT (pinned in Gtz/Audit.lean): every theorem depends on exactly
[propext, Quot.sound], inherited from the Lean-core Int/List lemma layer
(core `Int.add_comm`-family proofs carry propext in this toolchain); the
file is sorry-free and Classical.choice-free.  A port onto the FX1Poly
zero-axiom number layer would remove both.

A sparse integer-polynomial calculus over four variables (the rim weights
`w1 w2 w3 w4`; the spine weight is the polynomial `w0 = 1 - w1-w2-w3-w4`),
with a PROVED evaluation semantics: `polyEval` commutes with append,
negation, multiplication, and canonicalization.  Two polynomials with
equal canonical forms therefore agree at every integer point -- and since
the canonical forms are computed by `decide`, every identity below is
kernel-checked.

Payload (all data exact, produced by the rung-14 flint pipeline and
INDEPENDENTLY re-verified in sympy):
  * the four spine-survivor denominators `eDen0 .. eDen3` (E_k = -RD_k,
    Gordan ratio = 10 a b (1-a)(1-b) / E_k);
  * the two star threshold denominators `eDenA, eDenB`;
  * THE EIGHT MARGIN IDENTITIES, e.g.
      E_A - a * E_0  =  2 * w0 * w1 * (w1 w2 + w3 (1 - w4)),
    whose right-hand factors are manifestly positive on the open weight
    simplex for the S0/S3 rows (the window/collar margins), and carry the
    explicit `w0` factor (the rung-13 face law and reopening rate);
  * the two Gordan-sum laws `G1 + G3 = 2 a b`, `G2 + G4 = 2 a b` for the
    pair-sum candidates U03/U12 (ray-merge loci).

Downstream (ordered-field positivity, the window criterion, the box
certificates) consumes these through the FX number tower; this file is the
ring-identity core.
-/

namespace GtzCollarMargins

/- The rung-15 sheet identities multiply six-factor chains; their decide
canonicalizations recurse past the default elaborator cap. -/
set_option maxRecDepth 65536

/-- Exponent vector of a monomial in (w1, w2, w3, w4). -/
structure Monomial where
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

/-- Sparse polynomial: a bag of terms (order and zero-terms immaterial to
the evaluation semantics; `canon` fixes a normal form). -/
abbrev Poly := List Term

/-- Term literal helper. -/
def tm (expOne expTwo expThree expFour : Nat) (coeff : Int) : Term :=
  ⟨⟨expOne, expTwo, expThree, expFour⟩, coeff⟩

/-- Structural power (kept local so the file has zero dependencies). -/
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

/-- Evaluation of one term at an integer point. -/
def termEval (t : Term) (w1 w2 w3 w4 : Int) : Int :=
  t.coeff * intPow w1 t.monomial.expOne * intPow w2 t.monomial.expTwo
    * intPow w3 t.monomial.expThree * intPow w4 t.monomial.expFour

/-- Evaluation of a sparse polynomial. -/
def polyEval : Poly → Int → Int → Int → Int → Int
  | [], _, _, _, _ => 0
  | t :: rest, w1, w2, w3, w4 =>
      termEval t w1 w2 w3 w4 + polyEval rest w1 w2 w3 w4

/-- Sum = list append. -/
def polyAdd (p q : Poly) : Poly := p ++ q

def polyNeg (p : Poly) : Poly :=
  p.map fun t => ⟨t.monomial, -t.coeff⟩

def monomialMul (m n : Monomial) : Monomial :=
  ⟨m.expOne + n.expOne, m.expTwo + n.expTwo,
   m.expThree + n.expThree, m.expFour + n.expFour⟩

def termMul (s t : Term) : Term :=
  ⟨monomialMul s.monomial t.monomial, s.coeff * t.coeff⟩

def polyMulTerm (s : Term) (q : Poly) : Poly := q.map (termMul s)

def polyMul : Poly → Poly → Poly
  | [], _ => []
  | t :: rest, q => polyMulTerm t q ++ polyMul rest q

/-- Lexicographic strict order on exponent vectors (Bool-valued). -/
def monomialLtB (m n : Monomial) : Bool :=
  if m.expOne ≠ n.expOne then m.expOne < n.expOne
  else if m.expTwo ≠ n.expTwo then m.expTwo < n.expTwo
  else if m.expThree ≠ n.expThree then m.expThree < n.expThree
  else m.expFour < n.expFour

/-- Sorted insertion with coefficient merge. -/
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

/-- Canonical form: sorted, merged, zero coefficients pruned. -/
def canon (p : Poly) : Poly :=
  (sortMerge p).filter fun t => t.coeff ≠ 0

/-! ## Evaluation semantics -/

theorem polyEval_append (p q : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (p ++ q) w1 w2 w3 w4
      = polyEval p w1 w2 w3 w4 + polyEval q w1 w2 w3 w4 := by
  induction p with
  | nil => simp [polyEval]
  | cons head rest ih =>
      show termEval head w1 w2 w3 w4 + polyEval (rest ++ q) w1 w2 w3 w4 = _
      rw [ih, polyEval, Int.add_assoc]

theorem polyEval_neg (p : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (polyNeg p) w1 w2 w3 w4 = -(polyEval p w1 w2 w3 w4) := by
  induction p with
  | nil => simp [polyEval, polyNeg]
  | cons head rest ih =>
      show termEval ⟨head.monomial, -head.coeff⟩ w1 w2 w3 w4
             + polyEval (polyNeg rest) w1 w2 w3 w4 = _
      rw [ih, polyEval]
      show -head.coeff * intPow w1 head.monomial.expOne
             * intPow w2 head.monomial.expTwo
             * intPow w3 head.monomial.expThree
             * intPow w4 head.monomial.expFour
             + -(polyEval rest w1 w2 w3 w4) = _
      rw [termEval, Int.neg_add]
      simp [Int.neg_mul]

theorem termEval_termMul (s t : Term) (w1 w2 w3 w4 : Int) :
    termEval (termMul s t) w1 w2 w3 w4
      = termEval s w1 w2 w3 w4 * termEval t w1 w2 w3 w4 := by
  unfold termEval termMul monomialMul
  simp only [intPow_add]
  simp [Int.mul_comm, Int.mul_left_comm]

theorem polyEval_mulTerm (s : Term) (q : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (polyMulTerm s q) w1 w2 w3 w4
      = termEval s w1 w2 w3 w4 * polyEval q w1 w2 w3 w4 := by
  induction q with
  | nil => simp [polyEval, polyMulTerm]
  | cons head rest ih =>
      show termEval (termMul s head) w1 w2 w3 w4
             + polyEval (polyMulTerm s rest) w1 w2 w3 w4 = _
      rw [ih, termEval_termMul, polyEval, Int.mul_add]

theorem polyEval_mul (p q : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (polyMul p q) w1 w2 w3 w4
      = polyEval p w1 w2 w3 w4 * polyEval q w1 w2 w3 w4 := by
  induction p with
  | nil => simp [polyEval, polyMul]
  | cons head rest ih =>
      show polyEval (polyMulTerm head q ++ polyMul rest q) w1 w2 w3 w4 = _
      rw [polyEval_append, polyEval_mulTerm, ih, polyEval, Int.add_mul]

theorem termEval_mergeCoeff (m : Monomial) (c d : Int)
    (w1 w2 w3 w4 : Int) :
    termEval ⟨m, c + d⟩ w1 w2 w3 w4
      = termEval ⟨m, c⟩ w1 w2 w3 w4 + termEval ⟨m, d⟩ w1 w2 w3 w4 := by
  unfold termEval
  simp [Int.add_mul]

theorem polyEval_insertTerm (t : Term) (p : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (insertTerm t p) w1 w2 w3 w4
      = termEval t w1 w2 w3 w4 + polyEval p w1 w2 w3 w4 := by
  induction p with
  | nil => simp [insertTerm, polyEval]
  | cons head rest ih =>
      unfold insertTerm
      split
      · next monEq =>
          rw [polyEval, polyEval]
          rw [show t.monomial = head.monomial from monEq]
          rw [← Int.add_assoc]
          rw [show (⟨head.monomial, t.coeff + head.coeff⟩ : Term)
                = ⟨head.monomial, t.coeff + head.coeff⟩ from rfl]
          rw [termEval_mergeCoeff head.monomial t.coeff head.coeff]
          have coeffCast :
              termEval ⟨head.monomial, t.coeff⟩ w1 w2 w3 w4
                = termEval t w1 w2 w3 w4 := by
            rw [← monEq]
          rw [coeffCast]
      · split
        · rw [polyEval, polyEval]
        · rw [polyEval, polyEval, ih, ← Int.add_assoc,
              Int.add_comm (termEval head w1 w2 w3 w4)
                (termEval t w1 w2 w3 w4), Int.add_assoc]

theorem polyEval_sortMerge (p : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (sortMerge p) w1 w2 w3 w4 = polyEval p w1 w2 w3 w4 := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
      show polyEval (insertTerm head (sortMerge rest)) w1 w2 w3 w4 = _
      rw [polyEval_insertTerm, ih, polyEval]

theorem polyEval_filterZero (p : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (p.filter fun t => t.coeff ≠ 0) w1 w2 w3 w4
      = polyEval p w1 w2 w3 w4 := by
  induction p with
  | nil => rfl
  | cons head rest ih =>
      by_cases isZero : head.coeff = 0
      · have dropped :
            (head :: rest).filter (fun t => t.coeff ≠ 0)
              = rest.filter fun t => t.coeff ≠ 0 := by
          simp [List.filter, isZero]
        rw [dropped, ih, polyEval]
        have killed : termEval head w1 w2 w3 w4 = 0 := by
          unfold termEval
          rw [isZero]
          simp
        rw [killed, Int.zero_add]
      · have kept :
            (head :: rest).filter (fun t => t.coeff ≠ 0)
              = head :: rest.filter fun t => t.coeff ≠ 0 := by
          simp [List.filter, isZero]
        rw [kept, polyEval, ih, polyEval]

theorem polyEval_canon (p : Poly) (w1 w2 w3 w4 : Int) :
    polyEval (canon p) w1 w2 w3 w4 = polyEval p w1 w2 w3 w4 := by
  unfold canon
  rw [polyEval_filterZero, polyEval_sortMerge]

/-- THE BRIDGE: equal canonical forms give equal values everywhere. -/
theorem polyEval_eq_of_canon_eq (p q : Poly) (canonEq : canon p = canon q)
    (w1 w2 w3 w4 : Int) :
    polyEval p w1 w2 w3 w4 = polyEval q w1 w2 w3 w4 := by
  rw [← polyEval_canon p, canonEq, polyEval_canon]

/-! ## The exact rung-14 data -/

/-- a := w1 + w3 (branch B sum). -/
def branchSumA : Poly := [tm 1 0 0 0 1, tm 0 0 1 0 1]

/-- b := w2 + w4 (branch C sum). -/
def branchSumB : Poly := [tm 0 1 0 0 1, tm 0 0 0 1 1]

/-- w0 := 1 - w1 - w2 - w3 - w4 (spine weight). -/
def spineWeight : Poly :=
  [tm 0 0 0 0 1, tm 1 0 0 0 (-1), tm 0 1 0 0 (-1),
   tm 0 0 1 0 (-1), tm 0 0 0 1 (-1)]

/-- E_0 := -RD of the stripped spine-survivor family S0 (rung 14, exact). -/
def eDen0 : Poly :=
  [tm 0 1 1 0 (1),
    tm 0 1 2 0 (-1),
    tm 0 2 1 0 (-1),
    tm 0 2 2 0 (1),
    tm 1 0 0 1 (1),
    tm 1 0 0 2 (-1),
    tm 1 1 0 0 (-2),
    tm 1 1 0 1 (2),
    tm 1 1 1 0 (2),
    tm 1 1 1 1 (-2),
    tm 1 2 0 0 (2),
    tm 2 0 0 1 (-1),
    tm 2 0 0 2 (1),
    tm 2 1 0 0 (2)]

/-- E_1 := -RD of the stripped spine-survivor family S1 (rung 14, exact). -/
def eDen1 : Poly :=
  [tm 0 1 1 0 (1),
    tm 0 1 2 0 (-1),
    tm 0 2 1 0 (-1),
    tm 0 2 2 0 (1),
    tm 1 0 0 1 (3),
    tm 1 0 0 2 (-3),
    tm 1 0 1 1 (-2),
    tm 1 1 0 1 (-2),
    tm 1 1 1 1 (-2),
    tm 2 0 0 1 (-3),
    tm 2 0 0 2 (1)]

/-- E_2 := -RD of the stripped spine-survivor family S2 (rung 14, exact). -/
def eDen2 : Poly :=
  [tm 0 1 1 0 (3),
    tm 0 1 1 1 (-2),
    tm 0 1 2 0 (-3),
    tm 0 2 1 0 (-3),
    tm 0 2 2 0 (1),
    tm 1 0 0 1 (1),
    tm 1 0 0 2 (-1),
    tm 1 1 1 0 (-2),
    tm 1 1 1 1 (-2),
    tm 2 0 0 1 (-1),
    tm 2 0 0 2 (1)]

/-- E_3 := -RD of the stripped spine-survivor family S3 (rung 14, exact). -/
def eDen3 : Poly :=
  [tm 0 0 1 1 (-2),
    tm 0 0 1 2 (2),
    tm 0 0 2 1 (2),
    tm 0 1 1 0 (1),
    tm 0 1 1 1 (2),
    tm 0 1 2 0 (-1),
    tm 0 2 1 0 (-1),
    tm 0 2 2 0 (1),
    tm 1 0 0 1 (1),
    tm 1 0 0 2 (-1),
    tm 1 0 1 1 (2),
    tm 1 1 1 1 (-2),
    tm 2 0 0 1 (-1),
    tm 2 0 0 2 (1)]

/-- E_A: the star-(1,3,5) threshold denominator, normalized so thrA = 10 a^2 b (1-a)(1-b) / E_A (rung 13, exact). -/
def eDenA : Poly :=
  [tm 0 1 2 0 (1),
    tm 0 1 3 0 (-1),
    tm 0 2 2 0 (-1),
    tm 0 2 3 0 (1),
    tm 1 0 1 0 (2),
    tm 1 0 1 1 (-3),
    tm 1 0 1 2 (1),
    tm 1 0 2 0 (-2),
    tm 1 0 2 1 (2),
    tm 1 1 1 0 (-3),
    tm 1 1 1 1 (4),
    tm 1 1 2 0 (1),
    tm 1 1 2 1 (-2),
    tm 1 2 1 0 (1),
    tm 1 2 2 0 (1),
    tm 2 0 0 1 (1),
    tm 2 0 0 2 (-1),
    tm 2 0 1 0 (-2),
    tm 2 0 1 1 (1),
    tm 2 0 1 2 (1),
    tm 2 1 1 0 (2),
    tm 2 1 1 1 (-2),
    tm 3 0 0 1 (-1),
    tm 3 0 0 2 (1)]

/-- E_B: the star-(2,4,5) threshold denominator, normalized so thrB = 10 a^2 b (1-a)(1-b) / E_B (b^2 a for B) (rung 13, exact). -/
def eDenB : Poly :=
  [tm 0 1 0 1 (2),
    tm 0 1 0 2 (-2),
    tm 0 1 1 1 (-3),
    tm 0 1 1 2 (2),
    tm 0 1 2 1 (1),
    tm 0 2 0 1 (-2),
    tm 0 2 1 0 (1),
    tm 0 2 1 1 (1),
    tm 0 2 2 0 (-1),
    tm 0 2 2 1 (1),
    tm 0 3 1 0 (-1),
    tm 0 3 2 0 (1),
    tm 1 0 0 2 (1),
    tm 1 0 0 3 (-1),
    tm 1 1 0 1 (-3),
    tm 1 1 0 2 (1),
    tm 1 1 1 1 (4),
    tm 1 1 1 2 (-2),
    tm 1 2 0 1 (2),
    tm 1 2 1 1 (-2),
    tm 2 0 0 2 (-1),
    tm 2 0 0 3 (1),
    tm 2 1 0 1 (1),
    tm 2 1 0 2 (1)]

/-! ## The eight margin identities -/

/-- Margin factor of (S0, thrA): E_A - a E_0 = 2 w0 * (outer weight) * (w1 w2 + w3 (1 - w4)). -/
def marginS0AInner : Poly :=
  [tm 1 1 0 0 1, tm 0 0 1 0 1, tm 0 0 1 1 (-1)]

def marginS0ALhs : Poly :=
  polyAdd eDenA (polyNeg (polyMul branchSumA eDen0))

def marginS0ARhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 1 0 0 0 1]) marginS0AInner

/-- KERNEL-CHECKED: the (S0, A) margin identity as a forall-statement over Int. -/
theorem marginS0AIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS0ALhs w1 w2 w3 w4
      = polyEval marginS0ARhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Margin factor of (S0, thrB): E_B - b E_0 = 2 w0 * (outer weight) * (w1 w2 + w4 (1 - w3)). -/
def marginS0BInner : Poly :=
  [tm 1 1 0 0 1, tm 0 0 0 1 1, tm 0 0 1 1 (-1)]

def marginS0BLhs : Poly :=
  polyAdd eDenB (polyNeg (polyMul branchSumB eDen0))

def marginS0BRhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 0 1 0 0 1]) marginS0BInner

/-- KERNEL-CHECKED: the (S0, B) margin identity as a forall-statement over Int. -/
theorem marginS0BIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS0BLhs w1 w2 w3 w4
      = polyEval marginS0BRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Margin factor of (S1, thrA): E_A - a E_1 = 2 w0 * (outer weight) * (w3 (1 - w2 - 2 w4) - w1 w4). -/
def marginS1AInner : Poly :=
  [tm 0 0 1 0 1, tm 0 1 1 0 (-1), tm 0 0 1 1 (-2), tm 1 0 0 1 (-1)]

def marginS1ALhs : Poly :=
  polyAdd eDenA (polyNeg (polyMul branchSumA eDen1))

def marginS1ARhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 1 0 0 0 1]) marginS1AInner

/-- KERNEL-CHECKED: the (S1, A) margin identity as a forall-statement over Int. -/
theorem marginS1AIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS1ALhs w1 w2 w3 w4
      = polyEval marginS1ARhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Margin factor of (S1, thrB): E_B - b E_1 = 2 w0 * (outer weight) * (w2 (1 - 2 w1 - w3) - w1 w4). -/
def marginS1BInner : Poly :=
  [tm 0 1 0 0 1, tm 1 1 0 0 (-2), tm 0 1 1 0 (-1), tm 1 0 0 1 (-1)]

def marginS1BLhs : Poly :=
  polyAdd eDenB (polyNeg (polyMul branchSumB eDen1))

def marginS1BRhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 0 0 0 1 1]) marginS1BInner

/-- KERNEL-CHECKED: the (S1, B) margin identity as a forall-statement over Int. -/
theorem marginS1BIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS1BLhs w1 w2 w3 w4
      = polyEval marginS1BRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Margin factor of (S2, thrA): E_A - a E_2 = 2 w0 * (outer weight) * (w1 (1 - 2 w2 - w4) - w2 w3). -/
def marginS2AInner : Poly :=
  [tm 1 0 0 0 1, tm 1 1 0 0 (-2), tm 1 0 0 1 (-1), tm 0 1 1 0 (-1)]

def marginS2ALhs : Poly :=
  polyAdd eDenA (polyNeg (polyMul branchSumA eDen2))

def marginS2ARhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 0 0 1 0 1]) marginS2AInner

/-- KERNEL-CHECKED: the (S2, A) margin identity as a forall-statement over Int. -/
theorem marginS2AIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS2ALhs w1 w2 w3 w4
      = polyEval marginS2ARhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Margin factor of (S2, thrB): E_B - b E_2 = 2 w0 * (outer weight) * (w4 (1 - w1 - 2 w3) - w2 w3). -/
def marginS2BInner : Poly :=
  [tm 0 0 0 1 1, tm 1 0 0 1 (-1), tm 0 0 1 1 (-2), tm 0 1 1 0 (-1)]

def marginS2BLhs : Poly :=
  polyAdd eDenB (polyNeg (polyMul branchSumB eDen2))

def marginS2BRhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 0 1 0 0 1]) marginS2BInner

/-- KERNEL-CHECKED: the (S2, B) margin identity as a forall-statement over Int. -/
theorem marginS2BIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS2BLhs w1 w2 w3 w4
      = polyEval marginS2BRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Margin factor of (S3, thrA): E_A - a E_3 = 2 w0 * (outer weight) * (w1 (1 - w2) + w3 w4). -/
def marginS3AInner : Poly :=
  [tm 1 0 0 0 1, tm 1 1 0 0 (-1), tm 0 0 1 1 1]

def marginS3ALhs : Poly :=
  polyAdd eDenA (polyNeg (polyMul branchSumA eDen3))

def marginS3ARhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 0 0 1 0 1]) marginS3AInner

/-- KERNEL-CHECKED: the (S3, A) margin identity as a forall-statement over Int. -/
theorem marginS3AIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS3ALhs w1 w2 w3 w4
      = polyEval marginS3ARhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Margin factor of (S3, thrB): E_B - b E_3 = 2 w0 * (outer weight) * (w2 (1 - w1) + w3 w4). -/
def marginS3BInner : Poly :=
  [tm 0 1 0 0 1, tm 1 1 0 0 (-1), tm 0 0 1 1 1]

def marginS3BLhs : Poly :=
  polyAdd eDenB (polyNeg (polyMul branchSumB eDen3))

def marginS3BRhs : Poly :=
  polyMul (polyMul (polyMul [tm 0 0 0 0 2] spineWeight)
    [tm 0 0 0 1 1]) marginS3BInner

/-- KERNEL-CHECKED: the (S3, B) margin identity as a forall-statement over Int. -/
theorem marginS3BIdentity (w1 w2 w3 w4 : Int) :
    polyEval marginS3BLhs w1 w2 w3 w4
      = polyEval marginS3BRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-! ## The Gordan-sum laws for the pair-sum candidates U03 / U12 -/

/-- G1 := 2 w4 a + w0 (w4 - w2). -/
def gordanOne : Poly :=
  polyAdd (polyMul [tm 0 0 0 1 2] branchSumA)
    (polyMul spineWeight [tm 0 0 0 1 1, tm 0 1 0 0 (-1)])

/-- G3 := 2 w2 a + w0 (w2 - w4). -/
def gordanThree : Poly :=
  polyAdd (polyMul [tm 0 1 0 0 2] branchSumA)
    (polyMul spineWeight [tm 0 1 0 0 1, tm 0 0 0 1 (-1)])

/-- G2 := 2 w3 b + w0 (w3 - w1). -/
def gordanTwo : Poly :=
  polyAdd (polyMul [tm 0 0 1 0 2] branchSumB)
    (polyMul spineWeight [tm 0 0 1 0 1, tm 1 0 0 0 (-1)])

/-- G4 := 2 w1 b + w0 (w1 - w3). -/
def gordanFour : Poly :=
  polyAdd (polyMul [tm 1 0 0 0 2] branchSumB)
    (polyMul spineWeight [tm 1 0 0 0 1, tm 0 0 1 0 (-1)])

/-- KERNEL-CHECKED: G1 + G3 = 2 a b -- the C-branch pair of U03/U12 cone
conditions can never both be negative on the open simplex. -/
theorem gordanSumLawC (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd gordanOne gordanThree) w1 w2 w3 w4
      = polyEval (polyMul (polyMul [tm 0 0 0 0 2] branchSumA) branchSumB)
          w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- KERNEL-CHECKED: G2 + G4 = 2 a b (the B-branch pair). -/
theorem gordanSumLawB (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd gordanTwo gordanFour) w1 w2 w3 w4
      = polyEval (polyMul (polyMul [tm 0 0 0 0 2] branchSumA) branchSumB)
          w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-! ## RUNG 15: the composite-tie fiber closure identities -/

/-- mu := w1 w2 - w3 w4, the diamond pivot invariant (the
bilinear invariant of the branch pairing; vanishes on double
ties). -/
def muInvariant : Poly := [tm 1 1 0 0 1, tm 0 0 1 1 (-1)]

/-- K_A := mu + a b (w3 + w4): the T01245/T12345 pivot core. -/
def pivotCoreA : Poly :=
  polyAdd muInvariant
    (polyMul (polyMul branchSumA branchSumB)
      [tm 0 0 1 0 1, tm 0 0 0 1 1])

/-- K_B := a b (w1 - w4) - mu: the T01256/T12356 pivot core. -/
def pivotCoreB : Poly :=
  polyAdd (polyMul (polyMul branchSumA branchSumB)
      [tm 1 0 0 0 1, tm 0 0 0 1 (-1)])
    (polyNeg muInvariant)

/-- K_C := a b (w2 - w3) - mu: the T01247/T12347 pivot core. -/
def pivotCoreC : Poly :=
  polyAdd (polyMul (polyMul branchSumA branchSumB)
      [tm 0 1 0 0 1, tm 0 0 1 0 (-1)])
    (polyNeg muInvariant)

/-- KERNEL-CHECKED pivot-sum law: K_A + K_B = a^2 b -- on the
open simplex the two pivots can never both be nonpositive
(coverage of the guarded pair regions). -/
theorem pivotSumLawAB (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd pivotCoreA pivotCoreB) w1 w2 w3 w4
      = polyEval (polyMul (polyMul branchSumA branchSumA) branchSumB) w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- KERNEL-CHECKED pivot-sum law: K_A + K_C = a b^2 -- on the
open simplex the two pivots can never both be nonpositive
(coverage of the guarded pair regions). -/
theorem pivotSumLawAC (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd pivotCoreA pivotCoreC) w1 w2 w3 w4
      = polyEval (polyMul (polyMul branchSumA branchSumB) branchSumB) w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-! The six pivot-exchange identities: the boundary beta of each
guard-pair member equals an explicit simplex-signed unit times
the pair's pivot core -- adjacent supports pivot across the SAME
surface, the ring-identity core of the guarded-pair box rule. -/

/-- beta[tree 0] of support T01245. -/
def pivotExchangeT01245Tree0Lhs : Poly :=
  [tm 0 0 3 3 (1),
    tm 0 0 3 4 (-2),
    tm 0 0 3 5 (1),
    tm 0 0 4 3 (-2),
    tm 0 0 4 4 (3),
    tm 0 0 4 5 (-1),
    tm 0 0 5 3 (1),
    tm 0 0 5 4 (-1),
    tm 0 1 3 3 (-1),
    tm 0 1 3 4 (1),
    tm 0 1 4 2 (-1),
    tm 0 1 4 3 (2),
    tm 0 1 4 4 (-1),
    tm 0 1 5 2 (1),
    tm 0 1 5 3 (-1),
    tm 1 0 2 4 (-1),
    tm 1 0 2 5 (1),
    tm 1 0 3 3 (-1),
    tm 1 0 3 4 (2),
    tm 1 0 3 5 (-1),
    tm 1 0 4 3 (1),
    tm 1 0 4 4 (-1),
    tm 1 1 2 2 (-1),
    tm 1 1 2 4 (1),
    tm 1 1 3 3 (1),
    tm 1 1 3 4 (-1),
    tm 1 1 4 2 (1),
    tm 1 1 4 3 (-1)]

def pivotExchangeT01245Tree0Rhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 0 0 1 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    (pivotCoreA)

/-- KERNEL-CHECKED pivot-exchange identity for T01245[0]. -/
theorem pivotExchangeT01245Tree0 (w1 w2 w3 w4 : Int) :
    polyEval pivotExchangeT01245Tree0Lhs w1 w2 w3 w4
      = polyEval pivotExchangeT01245Tree0Rhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- beta[tree 3] of support T12345. -/
def pivotExchangeT12345Tree3Lhs : Poly :=
  [tm 2 2 1 1 (1),
    tm 2 2 1 2 (-1),
    tm 2 2 2 1 (-1),
    tm 2 3 1 1 (-2),
    tm 2 3 1 2 (1),
    tm 2 3 2 0 (-1),
    tm 2 3 2 1 (1),
    tm 2 4 1 1 (1),
    tm 2 4 2 0 (1),
    tm 3 2 0 2 (-1),
    tm 3 2 1 1 (-2),
    tm 3 2 1 2 (1),
    tm 3 2 2 1 (1),
    tm 3 3 0 0 (-1),
    tm 3 3 0 1 (-1),
    tm 3 3 0 2 (1),
    tm 3 3 1 0 (-1),
    tm 3 3 1 1 (3),
    tm 3 3 1 2 (-1),
    tm 3 3 2 0 (1),
    tm 3 3 2 1 (-1),
    tm 3 4 0 0 (1),
    tm 3 4 0 1 (1),
    tm 3 4 1 0 (1),
    tm 3 4 1 1 (-1),
    tm 3 4 2 0 (-1),
    tm 4 2 0 2 (1),
    tm 4 2 1 1 (1),
    tm 4 3 0 0 (1),
    tm 4 3 0 1 (1),
    tm 4 3 0 2 (-1),
    tm 4 3 1 0 (1),
    tm 4 3 1 1 (-1),
    tm 4 4 0 0 (-1),
    tm 4 4 0 1 (-1),
    tm 4 4 1 0 (-1)]

def pivotExchangeT12345Tree3Rhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
    tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    (pivotCoreA)

/-- KERNEL-CHECKED pivot-exchange identity for T12345[3]. -/
theorem pivotExchangeT12345Tree3 (w1 w2 w3 w4 : Int) :
    polyEval pivotExchangeT12345Tree3Lhs w1 w2 w3 w4
      = polyEval pivotExchangeT12345Tree3Rhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- beta[tree 0] of support T01256. -/
def pivotExchangeT01256Tree0Lhs : Poly :=
  [tm 0 0 3 3 (-1),
    tm 0 0 3 4 (2),
    tm 0 0 3 5 (-1),
    tm 0 0 4 3 (1),
    tm 0 0 4 4 (-2),
    tm 0 0 4 5 (1),
    tm 0 1 3 3 (1),
    tm 0 1 3 4 (-1),
    tm 0 1 4 3 (-1),
    tm 0 1 4 4 (1),
    tm 1 0 2 4 (1),
    tm 1 0 2 5 (-1),
    tm 1 0 3 3 (-1),
    tm 1 0 3 5 (1),
    tm 1 0 4 3 (1),
    tm 1 0 4 4 (-1),
    tm 1 1 2 2 (1),
    tm 1 1 2 4 (-1),
    tm 1 1 3 2 (-2),
    tm 1 1 3 3 (1),
    tm 1 1 3 4 (1),
    tm 1 1 4 2 (1),
    tm 1 1 4 3 (-1),
    tm 2 0 2 3 (-1),
    tm 2 0 2 4 (1),
    tm 2 0 3 3 (1),
    tm 2 0 3 4 (-1),
    tm 2 1 2 2 (-1),
    tm 2 1 2 3 (1),
    tm 2 1 3 2 (1),
    tm 2 1 3 3 (-1)]

def pivotExchangeT01256Tree0Rhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 0 0 1 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    (pivotCoreB)

/-- KERNEL-CHECKED pivot-exchange identity for T01256[0]. -/
theorem pivotExchangeT01256Tree0 (w1 w2 w3 w4 : Int) :
    polyEval pivotExchangeT01256Tree0Lhs w1 w2 w3 w4
      = polyEval pivotExchangeT01256Tree0Rhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- beta[tree 3] of support T12356. -/
def pivotExchangeT12356Tree3Lhs : Poly :=
  [tm 2 2 1 1 (-1),
    tm 2 2 1 2 (1),
    tm 2 3 1 1 (2),
    tm 2 3 1 2 (-1),
    tm 2 4 1 1 (-1),
    tm 3 2 0 2 (1),
    tm 3 2 1 2 (-1),
    tm 3 3 0 0 (1),
    tm 3 3 0 1 (1),
    tm 3 3 0 2 (-1),
    tm 3 3 1 0 (-1),
    tm 3 3 1 1 (-1),
    tm 3 3 1 2 (1),
    tm 3 4 0 0 (-1),
    tm 3 4 0 1 (-1),
    tm 3 4 1 0 (1),
    tm 3 4 1 1 (1),
    tm 4 2 0 1 (-1),
    tm 4 2 0 2 (-1),
    tm 4 2 1 1 (1),
    tm 4 3 0 0 (-2),
    tm 4 3 0 2 (1),
    tm 4 3 1 0 (1),
    tm 4 3 1 1 (-1),
    tm 4 4 0 0 (2),
    tm 4 4 0 1 (1),
    tm 4 4 1 0 (-1),
    tm 5 2 0 1 (1),
    tm 5 3 0 0 (1),
    tm 5 3 0 1 (-1),
    tm 5 4 0 0 (-1)]

def pivotExchangeT12356Tree3Rhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
    tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    (pivotCoreB)

/-- KERNEL-CHECKED pivot-exchange identity for T12356[3]. -/
theorem pivotExchangeT12356Tree3 (w1 w2 w3 w4 : Int) :
    polyEval pivotExchangeT12356Tree3Lhs w1 w2 w3 w4
      = polyEval pivotExchangeT12356Tree3Rhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- beta[tree 0] of support T01247. -/
def pivotExchangeT01247Tree0Lhs : Poly :=
  [tm 0 0 3 3 (1),
    tm 0 0 3 4 (-1),
    tm 0 0 4 3 (-2),
    tm 0 0 4 4 (2),
    tm 0 0 5 3 (1),
    tm 0 0 5 4 (-1),
    tm 0 1 3 3 (1),
    tm 0 1 3 4 (-1),
    tm 0 1 4 2 (-1),
    tm 0 1 4 4 (1),
    tm 0 1 5 2 (1),
    tm 0 1 5 3 (-1),
    tm 0 2 3 2 (1),
    tm 0 2 3 3 (-1),
    tm 0 2 4 2 (-1),
    tm 0 2 4 3 (1),
    tm 1 0 3 3 (-1),
    tm 1 0 3 4 (1),
    tm 1 0 4 3 (1),
    tm 1 0 4 4 (-1),
    tm 1 1 2 2 (-1),
    tm 1 1 2 3 (2),
    tm 1 1 2 4 (-1),
    tm 1 1 3 3 (-1),
    tm 1 1 3 4 (1),
    tm 1 1 4 2 (1),
    tm 1 1 4 3 (-1),
    tm 1 2 2 2 (1),
    tm 1 2 2 3 (-1),
    tm 1 2 3 2 (-1),
    tm 1 2 3 3 (1)]

def pivotExchangeT01247Tree0Rhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 0 0 1 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    (pivotCoreC)

/-- KERNEL-CHECKED pivot-exchange identity for T01247[0]. -/
theorem pivotExchangeT01247Tree0 (w1 w2 w3 w4 : Int) :
    polyEval pivotExchangeT01247Tree0Lhs w1 w2 w3 w4
      = polyEval pivotExchangeT01247Tree0Rhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- beta[tree 3] of support T12347. -/
def pivotExchangeT12347Tree3Lhs : Poly :=
  [tm 2 2 1 1 (1),
    tm 2 2 2 1 (-1),
    tm 2 3 2 0 (-1),
    tm 2 3 2 1 (1),
    tm 2 4 1 0 (1),
    tm 2 4 1 1 (-1),
    tm 2 4 2 0 (1),
    tm 2 5 1 0 (-1),
    tm 3 2 1 1 (-2),
    tm 3 2 2 1 (1),
    tm 3 3 0 0 (-1),
    tm 3 3 0 1 (1),
    tm 3 3 1 0 (-1),
    tm 3 3 1 1 (1),
    tm 3 3 2 0 (1),
    tm 3 3 2 1 (-1),
    tm 3 4 0 0 (2),
    tm 3 4 0 1 (-1),
    tm 3 4 1 1 (1),
    tm 3 4 2 0 (-1),
    tm 3 5 0 0 (-1),
    tm 3 5 1 0 (1),
    tm 4 2 1 1 (1),
    tm 4 3 0 0 (1),
    tm 4 3 0 1 (-1),
    tm 4 3 1 0 (1),
    tm 4 3 1 1 (-1),
    tm 4 4 0 0 (-2),
    tm 4 4 0 1 (1),
    tm 4 4 1 0 (-1),
    tm 4 5 0 0 (1)]

def pivotExchangeT12347Tree3Rhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
    tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    (pivotCoreC)

/-- KERNEL-CHECKED pivot-exchange identity for T12347[3]. -/
theorem pivotExchangeT12347Tree3 (w1 w2 w3 w4 : Int) :
    polyEval pivotExchangeT12347Tree3Lhs w1 w2 w3 w4
      = polyEval pivotExchangeT12347Tree3Rhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-! The double-tie line lemma identities: fiber w = (s, cs, s,
cs) -- variables (s, c) occupy exponent slots 1-2, slots 3-4
unused.  Support (0,2,3,5,6); threshold = through-star (1,3). -/

def lineRatioNum : Poly :=
  [tm 2 1 0 0 (-40),
    tm 3 1 0 0 (80),
    tm 3 2 0 0 (80),
    tm 4 2 0 0 (-160)]

def lineRatioDen : Poly :=
  [tm 3 1 0 0 (-6),
    tm 3 2 0 0 (-6)]

def lineThrNum : Poly :=
  [tm 1 1 0 0 (40),
    tm 2 1 0 0 (-80),
    tm 2 2 0 0 (-80),
    tm 3 2 0 0 (160)]

def lineThrDen : Poly :=
  [tm 0 0 0 0 (1),
    tm 1 0 0 0 (-2),
    tm 1 1 0 0 (-2),
    tm 2 1 0 0 (2),
    tm 2 2 0 0 (2)]

def lineBetaTree0FactorizationLhs : Poly :=
  [tm 6 3 0 0 (2),
    tm 7 3 0 0 (-6),
    tm 7 4 0 0 (-10),
    tm 8 3 0 0 (4),
    tm 8 4 0 0 (14),
    tm 8 5 0 0 (8),
    tm 9 4 0 0 (-4),
    tm 9 5 0 0 (-8)]

def lineBetaTree0FactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-2)])
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2),
    tm 1 1 0 0 (4)])

/-- KERNEL-CHECKED: line restriction of beta[tree 0], complete factorization. -/
theorem lineBetaTree0Factorization (w1 w2 w3 w4 : Int) :
    polyEval lineBetaTree0FactorizationLhs w1 w2 w3 w4
      = polyEval lineBetaTree0FactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def lineBetaTree2FactorizationLhs : Poly :=
  [tm 7 3 0 0 (4),
    tm 7 4 0 0 (4),
    tm 8 3 0 0 (-4),
    tm 8 4 0 0 (-8),
    tm 8 5 0 0 (-4),
    tm 9 4 0 0 (4),
    tm 9 5 0 0 (4)]

def lineBetaTree2FactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (4)])
    ([tm 0 0 0 0 (1),
    tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 1 0 0 (1)])

/-- KERNEL-CHECKED: line restriction of beta[tree 2], complete factorization. -/
theorem lineBetaTree2Factorization (w1 w2 w3 w4 : Int) :
    polyEval lineBetaTree2FactorizationLhs w1 w2 w3 w4
      = polyEval lineBetaTree2FactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def lineBetaTree3FactorizationLhs : Poly :=
  [tm 6 3 0 0 (2),
    tm 7 3 0 0 (-10),
    tm 7 4 0 0 (-6),
    tm 8 3 0 0 (8),
    tm 8 4 0 0 (14),
    tm 8 5 0 0 (4),
    tm 9 4 0 0 (-8),
    tm 9 5 0 0 (-4)]

def lineBetaTree3FactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-2)])
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (4),
    tm 1 1 0 0 (2)])

/-- KERNEL-CHECKED: line restriction of beta[tree 3], complete factorization. -/
theorem lineBetaTree3Factorization (w1 w2 w3 w4 : Int) :
    polyEval lineBetaTree3FactorizationLhs w1 w2 w3 w4
      = polyEval lineBetaTree3FactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def lineBetaTree5FactorizationLhs : Poly :=
  [tm 3 0 0 0 (2),
    tm 4 0 0 0 (-6),
    tm 4 1 0 0 (-12),
    tm 5 0 0 0 (4),
    tm 5 1 0 0 (28),
    tm 5 2 0 0 (24),
    tm 6 1 0 0 (-16),
    tm 6 2 0 0 (-40),
    tm 6 3 0 0 (-16),
    tm 7 2 0 0 (16),
    tm 7 3 0 0 (16)]

def lineBetaTree5FactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (2)])
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2),
    tm 1 1 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 1 1 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 1 1 0 0 (2)])

/-- KERNEL-CHECKED: line restriction of beta[tree 5], complete factorization. -/
theorem lineBetaTree5Factorization (w1 w2 w3 w4 : Int) :
    polyEval lineBetaTree5FactorizationLhs w1 w2 w3 w4
      = polyEval lineBetaTree5FactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def lineBetaTree6FactorizationLhs : Poly :=
  [tm 3 3 0 0 (2),
    tm 4 3 0 0 (-12),
    tm 4 4 0 0 (-6),
    tm 5 3 0 0 (24),
    tm 5 4 0 0 (28),
    tm 5 5 0 0 (4),
    tm 6 3 0 0 (-16),
    tm 6 4 0 0 (-40),
    tm 6 5 0 0 (-16),
    tm 7 4 0 0 (16),
    tm 7 5 0 0 (16)]

def lineBetaTree6FactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (2)])
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2),
    tm 1 1 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)])

/-- KERNEL-CHECKED: line restriction of beta[tree 6], complete factorization. -/
theorem lineBetaTree6Factorization (w1 w2 w3 w4 : Int) :
    polyEval lineBetaTree6FactorizationLhs w1 w2 w3 w4
      = polyEval lineBetaTree6FactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def lineWindowMarginLhs : Poly :=
  polyAdd (polyMul lineRatioNum lineThrDen)
    (polyNeg (polyMul lineThrNum lineRatioDen))

def lineWindowMarginRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (40)])
    ([tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 1 1 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2),
    tm 1 1 0 0 (2),
    tm 2 1 0 0 (4),
    tm 2 2 0 0 (4)])

/-- KERNEL-CHECKED: the line window margin RN thrDen - thrNum RD
factors completely -- every factor is explicitly signed on the
line tube 0 < s <= 1/8, 0 < c <= 1 (rung-15 line lemma). -/
theorem lineWindowMarginFactorization (w1 w2 w3 w4 : Int) :
    polyEval lineWindowMarginLhs w1 w2 w3 w4
      = polyEval lineWindowMarginRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-! The composite-tie sheet lemma identities: fiber w = (t, bu,
t, b(1-u)) -- variables (t, u, b) occupy exponent slots 1-3.
Bands: {W2 >= 0} (support (0,2,4,5,6)), {W1 >= 0 >= W2} (support
(0,2,3,5,6)), {W1 <= 0} (support (0,1,3,5,6)). -/

/-- W1 := 2bu + 2t - 2u + 1, the inner switch wall. -/
def sheetWallOne : Poly :=
  [tm 0 0 0 0 (1),
    tm 0 1 0 0 (-2),
    tm 0 1 1 0 (2),
    tm 1 0 0 0 (2)]

/-- W2 := bu + 2t - u, the outer switch wall. -/
def sheetWallTwo : Poly :=
  [tm 0 1 0 0 (-1),
    tm 0 1 1 0 (1),
    tm 1 0 0 0 (2)]

def sheetWallOrderRhs : Poly :=
  [tm 0 0 0 0 (1),
    tm 0 1 0 0 (-1),
    tm 0 1 1 0 (1)]

/-- KERNEL-CHECKED wall-order law: W1 - W2 = (1 - u) + u b, a
sum of tube-nonnegative terms, so W1 >= W2 on the sheet tube --
the three bands cover everything. -/
theorem sheetWallOrderLaw (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd sheetWallOne (polyNeg sheetWallTwo))
        w1 w2 w3 w4
      = polyEval sheetWallOrderRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def sheetThrNum : Poly :=
  [tm 0 0 1 0 (20),
    tm 0 0 2 0 (-20),
    tm 1 0 1 0 (-40),
    tm 1 0 2 0 (40)]

def sheetThrDen : Poly :=
  [tm 0 0 0 0 (1),
    tm 0 0 1 0 (-1),
    tm 0 1 2 0 (2),
    tm 0 2 2 0 (-2),
    tm 1 0 0 0 (-2),
    tm 1 0 1 0 (1),
    tm 1 0 2 0 (1),
    tm 1 1 2 0 (-4),
    tm 1 2 2 0 (4)]

def sheetMiddleWallBetaFactorizationLhs : Poly :=
  [tm 3 0 3 0 (1),
    tm 3 0 4 0 (-1),
    tm 3 1 3 0 (-4),
    tm 3 1 4 0 (7),
    tm 3 1 5 0 (-2),
    tm 3 2 3 0 (5),
    tm 3 2 4 0 (-13),
    tm 3 2 5 0 (6),
    tm 3 3 3 0 (-2),
    tm 3 3 4 0 (9),
    tm 3 3 5 0 (-6),
    tm 3 4 4 0 (-2),
    tm 3 4 5 0 (2),
    tm 4 0 3 0 (1),
    tm 4 0 4 0 (-1),
    tm 4 1 4 0 (-1),
    tm 4 1 5 0 (2),
    tm 4 2 3 0 (-3),
    tm 4 2 4 0 (7),
    tm 4 2 5 0 (-6),
    tm 4 3 3 0 (2),
    tm 4 3 4 0 (-7),
    tm 4 3 5 0 (6),
    tm 4 4 4 0 (2),
    tm 4 4 5 0 (-2),
    tm 5 0 3 0 (-2),
    tm 5 0 4 0 (2),
    tm 5 1 3 0 (4),
    tm 5 1 4 0 (-6),
    tm 5 2 3 0 (-2),
    tm 5 2 4 0 (6),
    tm 5 3 4 0 (-2)]

def sheetMiddleWallBetaFactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (1),
    tm 0 0 1 0 (-1),
    tm 0 1 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    (sheetWallOne)

/-- KERNEL-CHECKED: the wall-carrying beta of the middle-band support (0, 2, 3, 5, 6) -- the switch
wall appears as a literal factor. -/
theorem sheetMiddleWallBetaFactorization (w1 w2 w3 w4 : Int) :
    polyEval sheetMiddleWallBetaFactorizationLhs w1 w2 w3 w4
      = polyEval sheetMiddleWallBetaFactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def sheetMiddleWindowMarginFactorizationRatioNum : Poly :=
  [tm 1 0 1 0 (-20),
    tm 1 0 2 0 (20),
    tm 2 0 1 0 (40),
    tm 2 0 2 0 (-40)]

def sheetMiddleWindowMarginFactorizationRatioDen : Poly :=
  [tm 1 0 1 0 (-1),
    tm 1 0 2 0 (1),
    tm 1 1 1 0 (2),
    tm 1 1 2 0 (-6),
    tm 1 2 2 0 (2),
    tm 2 0 1 0 (-3),
    tm 2 0 2 0 (-1),
    tm 2 1 2 0 (4),
    tm 2 2 2 0 (-4)]

def sheetMiddleWindowMarginFactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (20)])
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (2),
    tm 0 0 2 0 (-1),
    tm 0 1 1 0 (-2),
    tm 0 1 2 0 (4),
    tm 1 0 0 0 (2),
    tm 1 0 1 0 (2)])

/-- KERNEL-CHECKED: the middle-band window margin factors completely
(rung-15 sheet lemma). -/
theorem sheetMiddleWindowMarginFactorization (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd (polyMul sheetMiddleWindowMarginFactorizationRatioNum sheetThrDen)
        (polyNeg (polyMul sheetThrNum sheetMiddleWindowMarginFactorizationRatioDen))) w1 w2 w3 w4
      = polyEval sheetMiddleWindowMarginFactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def sheetLowWallBetaFactorizationLhs : Poly :=
  [tm 3 2 3 0 (1),
    tm 3 3 3 0 (-2),
    tm 3 3 4 0 (1),
    tm 3 4 4 0 (2),
    tm 3 4 5 0 (-2),
    tm 4 2 3 0 (1),
    tm 4 3 3 0 (2),
    tm 4 3 4 0 (-3),
    tm 4 4 4 0 (-2),
    tm 4 4 5 0 (2),
    tm 5 2 3 0 (-2),
    tm 5 3 4 0 (2)]

def sheetLowWallBetaFactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
    tm 0 1 1 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (1)]))
    (sheetWallOne)

/-- KERNEL-CHECKED: the wall-carrying beta of the low-band support (0, 1, 3, 5, 6) -- the switch
wall appears as a literal factor. -/
theorem sheetLowWallBetaFactorization (w1 w2 w3 w4 : Int) :
    polyEval sheetLowWallBetaFactorizationLhs w1 w2 w3 w4
      = polyEval sheetLowWallBetaFactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def sheetLowWindowMarginFactorizationRatioNum : Poly :=
  [tm 1 0 1 0 (20),
    tm 1 0 2 0 (-20),
    tm 2 0 1 0 (-40),
    tm 2 0 2 0 (40)]

def sheetLowWindowMarginFactorizationRatioDen : Poly :=
  [tm 1 0 1 0 (-1),
    tm 1 0 2 0 (-1),
    tm 1 1 1 0 (2),
    tm 1 1 2 0 (2),
    tm 1 2 2 0 (-2),
    tm 2 0 1 0 (-1),
    tm 2 0 2 0 (1),
    tm 2 1 2 0 (-4),
    tm 2 2 2 0 (4)]

def sheetLowWindowMarginFactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (20)])
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)]))
    ([tm 0 0 0 0 (1),
    tm 0 0 2 0 (1),
    tm 0 1 1 0 (-2),
    tm 1 0 0 0 (-2),
    tm 1 0 1 0 (2)])

/-- KERNEL-CHECKED: the low-band window margin factors completely
(rung-15 sheet lemma). -/
theorem sheetLowWindowMarginFactorization (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd (polyMul sheetLowWindowMarginFactorizationRatioNum sheetThrDen)
        (polyNeg (polyMul sheetThrNum sheetLowWindowMarginFactorizationRatioDen))) w1 w2 w3 w4
      = polyEval sheetLowWindowMarginFactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def sheetTopWallBetaFactorizationLhs : Poly :=
  [tm 0 1 3 0 (1),
    tm 0 1 4 0 (-3),
    tm 0 1 5 0 (3),
    tm 0 1 6 0 (-1),
    tm 0 2 3 0 (-2),
    tm 0 2 4 0 (7),
    tm 0 2 5 0 (-8),
    tm 0 2 6 0 (3),
    tm 0 3 3 0 (1),
    tm 0 3 4 0 (-5),
    tm 0 3 5 0 (7),
    tm 0 3 6 0 (-3),
    tm 0 4 4 0 (1),
    tm 0 4 5 0 (-2),
    tm 0 4 6 0 (1),
    tm 1 0 3 0 (-2),
    tm 1 0 4 0 (4),
    tm 1 0 5 0 (-2),
    tm 1 1 3 0 (-2),
    tm 1 1 4 0 (6),
    tm 1 1 5 0 (-8),
    tm 1 1 6 0 (4),
    tm 1 2 3 0 (10),
    tm 1 2 4 0 (-30),
    tm 1 2 5 0 (32),
    tm 1 2 6 0 (-12),
    tm 1 3 3 0 (-6),
    tm 1 3 4 0 (26),
    tm 1 3 5 0 (-32),
    tm 1 3 6 0 (12),
    tm 1 4 4 0 (-6),
    tm 1 4 5 0 (10),
    tm 1 4 6 0 (-4),
    tm 2 0 3 0 (12),
    tm 2 0 4 0 (-20),
    tm 2 0 5 0 (8),
    tm 2 1 3 0 (-12),
    tm 2 1 4 0 (24),
    tm 2 1 5 0 (-4),
    tm 2 1 6 0 (-4),
    tm 2 2 3 0 (-12),
    tm 2 2 4 0 (24),
    tm 2 2 5 0 (-32),
    tm 2 2 6 0 (12),
    tm 2 3 3 0 (12),
    tm 2 3 4 0 (-40),
    tm 2 3 5 0 (44),
    tm 2 3 6 0 (-12),
    tm 2 4 4 0 (12),
    tm 2 4 5 0 (-16),
    tm 2 4 6 0 (4),
    tm 3 0 3 0 (-24),
    tm 3 0 4 0 (32),
    tm 3 0 5 0 (-8),
    tm 3 1 3 0 (40),
    tm 3 1 4 0 (-72),
    tm 3 1 5 0 (16),
    tm 3 2 3 0 (-8),
    tm 3 2 4 0 (40),
    tm 3 3 3 0 (-8),
    tm 3 3 4 0 (8),
    tm 3 3 5 0 (-16),
    tm 3 4 4 0 (-8),
    tm 3 4 5 0 (8),
    tm 4 0 3 0 (16),
    tm 4 0 4 0 (-16),
    tm 4 1 3 0 (-32),
    tm 4 1 4 0 (48),
    tm 4 2 3 0 (16),
    tm 4 2 4 0 (-48),
    tm 4 3 4 0 (16)]

def sheetTopWallBetaFactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (1),
    tm 0 0 1 0 (-1),
    tm 0 1 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (1),
    tm 1 0 0 0 (2)]))
    (sheetWallTwo))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)])

/-- KERNEL-CHECKED: the wall-carrying beta of the top-band support (0, 2, 4, 5, 6) -- the switch
wall appears as a literal factor. -/
theorem sheetTopWallBetaFactorization (w1 w2 w3 w4 : Int) :
    polyEval sheetTopWallBetaFactorizationLhs w1 w2 w3 w4
      = polyEval sheetTopWallBetaFactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

def sheetTopWindowMarginFactorizationRatioNum : Poly :=
  [tm 1 0 1 0 (20),
    tm 1 0 2 0 (-20),
    tm 2 0 1 0 (-40),
    tm 2 0 2 0 (40)]

def sheetTopWindowMarginFactorizationRatioDen : Poly :=
  [tm 1 0 1 0 (1),
    tm 1 0 2 0 (-1),
    tm 1 1 2 0 (4),
    tm 1 2 2 0 (-2),
    tm 2 0 1 0 (-1),
    tm 2 0 2 0 (1),
    tm 2 1 2 0 (-4),
    tm 2 2 2 0 (4)]

def sheetTopWindowMarginFactorizationRhs : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (20)])
    ([tm 0 0 0 0 (-1),
    tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
    tm 1 0 0 0 (2)]))
    ([tm 0 0 0 0 (1),
    tm 0 0 1 0 (-2),
    tm 0 0 2 0 (1),
    tm 0 1 2 0 (-2),
    tm 1 0 0 0 (-2),
    tm 1 0 1 0 (2)])

/-- KERNEL-CHECKED: the top-band window margin factors completely
(rung-15 sheet lemma). -/
theorem sheetTopWindowMarginFactorization (w1 w2 w3 w4 : Int) :
    polyEval (polyAdd (polyMul sheetTopWindowMarginFactorizationRatioNum sheetThrDen)
        (polyNeg (polyMul sheetThrNum sheetTopWindowMarginFactorizationRatioDen))) w1 w2 w3 w4
      = polyEval sheetTopWindowMarginFactorizationRhs w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-! ## Axiom audit -- measured: [propext, Quot.sound] from core Int/List;
sorry-free, Classical.choice-free -/

end GtzCollarMargins
