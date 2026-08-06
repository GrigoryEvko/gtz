/-!
# Bridge (iii): the collar dictionary ring identities

Self-contained Lean 4 payload -- no imports, same species and same proved
evaluation semantics as the landed `CollarMarginIdentities.lean`.  Where that
file carried the rung-14 MARGIN identities, this one carries the layer
underneath them: the CRAMER DICTIONARY itself.

The diamond-tie crossing system is an 8 x 9 polynomial matrix over
`Q(w1, w2, w3, w4)` (one row per marginal diamond tree, nine tangent
columns).  A spine-survivor family `S_k` picks the spine row `k` and the four
non-spine rows, and solves for the left-kernel ray by Cramer: the five beta
slots ARE the signed 4x4 minors

    beta_0 = det(nonSpine rows, columns 0..3),
    beta_{j+1} = det(same, column j replaced by -spineRow),

and the ray annihilates all NINE columns, not just the four it was solved on
-- that overdetermined agreement is the arithmetic content of "the crossing
system has rank four", i.e. the rung-13 degeneracy law.  Dividing the vector
by its polynomial content (degree 39) leaves the small stripped slots whose
signs the box engine decides.

Payload:
  * `sharedRatioNumFactorization` -- the Cramer numerator core is
    `-10 a b (1-a)(1-b)`, an explicitly-signed product, hence strictly
    negative on the open weight simplex (the sign the window criterion of
    bridge (i) consumes as `ratioNum != 0` with a known direction);
  * `ratioDenCoreIsNegatedMarginDenominatorS{k}` -- the flint Cramer
    denominator of each family is exactly minus the `E_k` of the landed
    margin payload, welding this file to `CollarMarginIdentities.lean`;
  * `betaSlotFactorizationS{k}Position{i}` -- each stripped slot as an
    explicit product of simplex atoms times at most one cone-boundary core,
    so in-cone sign reading is pure inspection;
  * `cramerColumnIdentityS{k}Column{c}` -- the Cramer/left-kernel identities.

Every identity is proved through the canonical-form bridge
`polyEval_eq_of_canon_eq` with the canonical forms compared by `decide`;
the generator additionally asserted each one in exact flint arithmetic
before emitting it.
-/

namespace GtzCollarDictionary

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

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

/-- Sparse polynomial: a bag of terms; `canon` fixes a normal form. -/
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

theorem termEval_mergeCoeff (m : Monomial) (c d : Int) (w1 w2 w3 w4 : Int) :
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

/-! ## The rung-14 flint Cramer dictionary -/

/-- The Cramer numerator core, shared by all four spine-survivor families: RN = -10 a b (1-a) (1-b). -/
def sharedRatioNumCore : Poly :=
  [tm 0 0 1 1 (-10),
    tm 0 0 1 2 (10),
    tm 0 0 2 1 (10),
    tm 0 0 2 2 (-10),
    tm 0 1 1 0 (-10),
    tm 0 1 1 1 (20),
    tm 0 1 2 0 (10),
    tm 0 1 2 1 (-20),
    tm 0 2 1 0 (10),
    tm 0 2 2 0 (-10),
    tm 1 0 0 1 (-10),
    tm 1 0 0 2 (10),
    tm 1 0 1 1 (20),
    tm 1 0 1 2 (-20),
    tm 1 1 0 0 (-10),
    tm 1 1 0 1 (20),
    tm 1 1 1 0 (20),
    tm 1 1 1 1 (-40),
    tm 1 2 0 0 (10),
    tm 1 2 1 0 (-20),
    tm 2 0 0 1 (10),
    tm 2 0 0 2 (-10),
    tm 2 1 0 0 (10),
    tm 2 1 0 1 (-20),
    tm 2 2 0 0 (-10)]

/-- The same numerator as an explicitly-signed product: strictly negative on the open weight simplex. -/
def sharedRatioNumFactored : Poly :=
  polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-10)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: the shared Cramer numerator factors into
manifestly simplex-signed atoms, so `RN < 0` throughout. -/
theorem sharedRatioNumFactorization (w1 w2 w3 w4 : Int) :
    polyEval sharedRatioNumCore w1 w2 w3 w4
      = polyEval sharedRatioNumFactored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- The Cramer denominator core RD of the spine-survivor family S0, straight from the flint solve. -/
def ratioDenCoreS0 : Poly :=
  [tm 0 1 1 0 (-1),
    tm 0 1 2 0 (1),
    tm 0 2 1 0 (1),
    tm 0 2 2 0 (-1),
    tm 1 0 0 1 (-1),
    tm 1 0 0 2 (1),
    tm 1 1 0 0 (2),
    tm 1 1 0 1 (-2),
    tm 1 1 1 0 (-2),
    tm 1 1 1 1 (2),
    tm 1 2 0 0 (-2),
    tm 2 0 0 1 (1),
    tm 2 0 0 2 (-1),
    tm 2 1 0 0 (-2)]

/-- E_0 = -RD_0: the margin denominator of the landed CollarMarginIdentities payload. -/
def marginDenominatorS0 : Poly :=
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

/-- KERNEL-CHECKED: the flint Cramer denominator of S0 is
exactly minus the landed margin denominator `E_0`. -/
theorem ratioDenCoreIsNegatedMarginDenominatorS0
    (w1 w2 w3 w4 : Int) :
    polyEval ratioDenCoreS0 w1 w2 w3 w4
      = polyEval (polyNeg marginDenominatorS0) w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- The Cramer denominator core RD of the spine-survivor family S1, straight from the flint solve. -/
def ratioDenCoreS1 : Poly :=
  [tm 0 1 1 0 (-1),
    tm 0 1 2 0 (1),
    tm 0 2 1 0 (1),
    tm 0 2 2 0 (-1),
    tm 1 0 0 1 (-3),
    tm 1 0 0 2 (3),
    tm 1 0 1 1 (2),
    tm 1 1 0 1 (2),
    tm 1 1 1 1 (2),
    tm 2 0 0 1 (3),
    tm 2 0 0 2 (-1)]

/-- E_1 = -RD_1: the margin denominator of the landed CollarMarginIdentities payload. -/
def marginDenominatorS1 : Poly :=
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

/-- KERNEL-CHECKED: the flint Cramer denominator of S1 is
exactly minus the landed margin denominator `E_1`. -/
theorem ratioDenCoreIsNegatedMarginDenominatorS1
    (w1 w2 w3 w4 : Int) :
    polyEval ratioDenCoreS1 w1 w2 w3 w4
      = polyEval (polyNeg marginDenominatorS1) w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- The Cramer denominator core RD of the spine-survivor family S2, straight from the flint solve. -/
def ratioDenCoreS2 : Poly :=
  [tm 0 1 1 0 (-3),
    tm 0 1 1 1 (2),
    tm 0 1 2 0 (3),
    tm 0 2 1 0 (3),
    tm 0 2 2 0 (-1),
    tm 1 0 0 1 (-1),
    tm 1 0 0 2 (1),
    tm 1 1 1 0 (2),
    tm 1 1 1 1 (2),
    tm 2 0 0 1 (1),
    tm 2 0 0 2 (-1)]

/-- E_2 = -RD_2: the margin denominator of the landed CollarMarginIdentities payload. -/
def marginDenominatorS2 : Poly :=
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

/-- KERNEL-CHECKED: the flint Cramer denominator of S2 is
exactly minus the landed margin denominator `E_2`. -/
theorem ratioDenCoreIsNegatedMarginDenominatorS2
    (w1 w2 w3 w4 : Int) :
    polyEval ratioDenCoreS2 w1 w2 w3 w4
      = polyEval (polyNeg marginDenominatorS2) w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- The Cramer denominator core RD of the spine-survivor family S3, straight from the flint solve. -/
def ratioDenCoreS3 : Poly :=
  [tm 0 0 1 1 (2),
    tm 0 0 1 2 (-2),
    tm 0 0 2 1 (-2),
    tm 0 1 1 0 (-1),
    tm 0 1 1 1 (-2),
    tm 0 1 2 0 (1),
    tm 0 2 1 0 (1),
    tm 0 2 2 0 (-1),
    tm 1 0 0 1 (-1),
    tm 1 0 0 2 (1),
    tm 1 0 1 1 (-2),
    tm 1 1 1 1 (2),
    tm 2 0 0 1 (1),
    tm 2 0 0 2 (-1)]

/-- E_3 = -RD_3: the margin denominator of the landed CollarMarginIdentities payload. -/
def marginDenominatorS3 : Poly :=
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

/-- KERNEL-CHECKED: the flint Cramer denominator of S3 is
exactly minus the landed margin denominator `E_3`. -/
theorem ratioDenCoreIsNegatedMarginDenominatorS3
    (w1 w2 w3 w4 : Int) :
    polyEval ratioDenCoreS3 w1 w2 w3 w4
      = polyEval (polyNeg marginDenominatorS3) w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 0 of family S0: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS0Position0 : Poly :=
  [tm 0 0 4 4 (-1),
    tm 0 0 4 5 (1),
    tm 0 0 5 4 (1),
    tm 0 0 5 5 (-1),
    tm 0 1 4 3 (-2),
    tm 0 1 4 4 (2),
    tm 0 1 5 3 (2),
    tm 0 1 5 4 (-2),
    tm 0 2 4 2 (-1),
    tm 0 2 4 3 (1),
    tm 0 2 5 2 (1),
    tm 0 2 5 3 (-1),
    tm 1 0 3 4 (-2),
    tm 1 0 3 5 (2),
    tm 1 0 4 4 (2),
    tm 1 0 4 5 (-2),
    tm 1 1 3 3 (-4),
    tm 1 1 3 4 (4),
    tm 1 1 4 3 (4),
    tm 1 1 4 4 (-4),
    tm 1 2 3 2 (-2),
    tm 1 2 3 3 (2),
    tm 1 2 4 2 (2),
    tm 1 2 4 3 (-2),
    tm 2 0 2 4 (-1),
    tm 2 0 2 5 (1),
    tm 2 0 3 4 (1),
    tm 2 0 3 5 (-1),
    tm 2 1 2 3 (-2),
    tm 2 1 2 4 (2),
    tm 2 1 3 3 (2),
    tm 2 1 3 4 (-2),
    tm 2 2 2 2 (-1),
    tm 2 2 2 3 (1),
    tm 2 2 3 2 (1),
    tm 2 2 3 3 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS0Position0Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 0 of S0 factors, exposing its cone core. -/
theorem betaSlotFactorizationS0Position0
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS0Position0 w1 w2 w3 w4
      = polyEval betaSlotS0Position0Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 1 of family S0: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS0Position1 : Poly :=
  [tm 0 0 1 4 (-1),
    tm 0 0 1 5 (1),
    tm 0 0 2 4 (2),
    tm 0 0 2 5 (-2),
    tm 0 0 3 4 (-1),
    tm 0 0 3 5 (1),
    tm 0 1 0 3 (1),
    tm 0 1 0 4 (-2),
    tm 0 1 0 5 (1),
    tm 0 1 1 3 (-4),
    tm 0 1 1 4 (6),
    tm 0 1 1 5 (-2),
    tm 0 1 2 3 (5),
    tm 0 1 2 4 (-6),
    tm 0 1 2 5 (1),
    tm 0 1 3 3 (-2),
    tm 0 1 3 4 (2),
    tm 0 2 0 2 (1),
    tm 0 2 0 3 (-3),
    tm 0 2 0 4 (2),
    tm 0 2 1 2 (-3),
    tm 0 2 1 3 (7),
    tm 0 2 1 4 (-4),
    tm 0 2 2 2 (3),
    tm 0 2 2 3 (-5),
    tm 0 2 2 4 (2),
    tm 0 2 3 2 (-1),
    tm 0 2 3 3 (1),
    tm 0 3 0 2 (-1),
    tm 0 3 0 3 (1),
    tm 0 3 1 2 (2),
    tm 0 3 1 3 (-2),
    tm 0 3 2 2 (-1),
    tm 0 3 2 3 (1),
    tm 1 0 0 4 (-1),
    tm 1 0 0 5 (1),
    tm 1 0 1 4 (4),
    tm 1 0 1 5 (-4),
    tm 1 0 2 4 (-3),
    tm 1 0 2 5 (3),
    tm 1 1 0 3 (-4),
    tm 1 1 0 4 (6),
    tm 1 1 0 5 (-2),
    tm 1 1 1 3 (10),
    tm 1 1 1 4 (-12),
    tm 1 1 1 5 (2),
    tm 1 1 2 3 (-6),
    tm 1 1 2 4 (6),
    tm 1 2 0 2 (-3),
    tm 1 2 0 3 (7),
    tm 1 2 0 4 (-4),
    tm 1 2 1 2 (6),
    tm 1 2 1 3 (-10),
    tm 1 2 1 4 (4),
    tm 1 2 2 2 (-3),
    tm 1 2 2 3 (3),
    tm 1 3 0 2 (2),
    tm 1 3 0 3 (-2),
    tm 1 3 1 2 (-2),
    tm 1 3 1 3 (2),
    tm 2 0 0 4 (2),
    tm 2 0 0 5 (-2),
    tm 2 0 1 4 (-3),
    tm 2 0 1 5 (3),
    tm 2 1 0 3 (5),
    tm 2 1 0 4 (-6),
    tm 2 1 0 5 (1),
    tm 2 1 1 3 (-6),
    tm 2 1 1 4 (6),
    tm 2 2 0 2 (3),
    tm 2 2 0 3 (-5),
    tm 2 2 0 4 (2),
    tm 2 2 1 2 (-3),
    tm 2 2 1 3 (3),
    tm 2 3 0 2 (-1),
    tm 2 3 0 3 (1),
    tm 3 0 0 4 (-1),
    tm 3 0 0 5 (1),
    tm 3 1 0 3 (-2),
    tm 3 1 0 4 (2),
    tm 3 2 0 2 (-1),
    tm 3 2 0 3 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS0Position1Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 1 1 (1),
      tm 0 1 0 0 (-1),
      tm 0 1 0 1 (1),
      tm 0 1 1 0 (1),
      tm 0 2 0 0 (1),
      tm 1 0 0 1 (1),
      tm 1 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 1 of S0 factors, exposing its cone core. -/
theorem betaSlotFactorizationS0Position1
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS0Position1 w1 w2 w3 w4
      = polyEval betaSlotS0Position1Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 2 of family S0: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS0Position2 : Poly :=
  [tm 0 0 4 1 (-1),
    tm 0 0 4 2 (2),
    tm 0 0 4 3 (-1),
    tm 0 0 5 1 (1),
    tm 0 0 5 2 (-2),
    tm 0 0 5 3 (1),
    tm 0 1 4 0 (-1),
    tm 0 1 4 1 (4),
    tm 0 1 4 2 (-3),
    tm 0 1 5 0 (1),
    tm 0 1 5 1 (-4),
    tm 0 1 5 2 (3),
    tm 0 2 4 0 (2),
    tm 0 2 4 1 (-3),
    tm 0 2 5 0 (-2),
    tm 0 2 5 1 (3),
    tm 0 3 4 0 (-1),
    tm 0 3 5 0 (1),
    tm 1 0 3 0 (1),
    tm 1 0 3 1 (-4),
    tm 1 0 3 2 (5),
    tm 1 0 3 3 (-2),
    tm 1 0 4 0 (-2),
    tm 1 0 4 1 (6),
    tm 1 0 4 2 (-6),
    tm 1 0 4 3 (2),
    tm 1 0 5 0 (1),
    tm 1 0 5 1 (-2),
    tm 1 0 5 2 (1),
    tm 1 1 3 0 (-4),
    tm 1 1 3 1 (10),
    tm 1 1 3 2 (-6),
    tm 1 1 4 0 (6),
    tm 1 1 4 1 (-12),
    tm 1 1 4 2 (6),
    tm 1 1 5 0 (-2),
    tm 1 1 5 1 (2),
    tm 1 2 3 0 (5),
    tm 1 2 3 1 (-6),
    tm 1 2 4 0 (-6),
    tm 1 2 4 1 (6),
    tm 1 2 5 0 (1),
    tm 1 3 3 0 (-2),
    tm 1 3 4 0 (2),
    tm 2 0 2 0 (1),
    tm 2 0 2 1 (-3),
    tm 2 0 2 2 (3),
    tm 2 0 2 3 (-1),
    tm 2 0 3 0 (-3),
    tm 2 0 3 1 (7),
    tm 2 0 3 2 (-5),
    tm 2 0 3 3 (1),
    tm 2 0 4 0 (2),
    tm 2 0 4 1 (-4),
    tm 2 0 4 2 (2),
    tm 2 1 2 0 (-3),
    tm 2 1 2 1 (6),
    tm 2 1 2 2 (-3),
    tm 2 1 3 0 (7),
    tm 2 1 3 1 (-10),
    tm 2 1 3 2 (3),
    tm 2 1 4 0 (-4),
    tm 2 1 4 1 (4),
    tm 2 2 2 0 (3),
    tm 2 2 2 1 (-3),
    tm 2 2 3 0 (-5),
    tm 2 2 3 1 (3),
    tm 2 2 4 0 (2),
    tm 2 3 2 0 (-1),
    tm 2 3 3 0 (1),
    tm 3 0 2 0 (-1),
    tm 3 0 2 1 (2),
    tm 3 0 2 2 (-1),
    tm 3 0 3 0 (1),
    tm 3 0 3 1 (-2),
    tm 3 0 3 2 (1),
    tm 3 1 2 0 (2),
    tm 3 1 2 1 (-2),
    tm 3 1 3 0 (-2),
    tm 3 1 3 1 (2),
    tm 3 2 2 0 (-1),
    tm 3 2 3 0 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS0Position2Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 1 (1),
      tm 0 1 1 0 (1),
      tm 1 0 0 0 (-1),
      tm 1 0 0 1 (1),
      tm 1 0 1 0 (1),
      tm 1 1 0 0 (1),
      tm 2 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 2 of S0 factors, exposing its cone core. -/
theorem betaSlotFactorizationS0Position2
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS0Position2 w1 w2 w3 w4
      = polyEval betaSlotS0Position2Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 3 of family S0: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS0Position3 : Poly :=
  [tm 0 3 0 1 (-1),
    tm 0 3 0 2 (1),
    tm 0 3 1 1 (2),
    tm 0 3 1 2 (-2),
    tm 0 3 2 1 (-1),
    tm 0 3 2 2 (1),
    tm 0 4 0 0 (-1),
    tm 0 4 0 1 (3),
    tm 0 4 0 2 (-1),
    tm 0 4 1 0 (2),
    tm 0 4 1 1 (-6),
    tm 0 4 1 2 (2),
    tm 0 4 2 0 (-1),
    tm 0 4 2 1 (3),
    tm 0 4 2 2 (-1),
    tm 0 5 0 0 (2),
    tm 0 5 0 1 (-2),
    tm 0 5 1 0 (-4),
    tm 0 5 1 1 (4),
    tm 0 5 2 0 (2),
    tm 0 5 2 1 (-2),
    tm 0 6 0 0 (-1),
    tm 0 6 1 0 (2),
    tm 0 6 2 0 (-1),
    tm 1 3 0 1 (2),
    tm 1 3 0 2 (-2),
    tm 1 3 1 1 (-2),
    tm 1 3 1 2 (2),
    tm 1 4 0 0 (2),
    tm 1 4 0 1 (-6),
    tm 1 4 0 2 (2),
    tm 1 4 1 0 (-2),
    tm 1 4 1 1 (6),
    tm 1 4 1 2 (-2),
    tm 1 5 0 0 (-4),
    tm 1 5 0 1 (4),
    tm 1 5 1 0 (4),
    tm 1 5 1 1 (-4),
    tm 1 6 0 0 (2),
    tm 1 6 1 0 (-2),
    tm 2 3 0 1 (-1),
    tm 2 3 0 2 (1),
    tm 2 4 0 0 (-1),
    tm 2 4 0 1 (3),
    tm 2 4 0 2 (-1),
    tm 2 5 0 0 (2),
    tm 2 5 0 1 (-2),
    tm 2 6 0 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS0Position3Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 3 of S0 factors, exposing its cone core. -/
theorem betaSlotFactorizationS0Position3
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS0Position3 w1 w2 w3 w4
      = polyEval betaSlotS0Position3Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 4 of family S0: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS0Position4 : Poly :=
  [tm 3 0 1 0 (-1),
    tm 3 0 1 1 (2),
    tm 3 0 1 2 (-1),
    tm 3 0 2 0 (1),
    tm 3 0 2 1 (-2),
    tm 3 0 2 2 (1),
    tm 3 1 1 0 (2),
    tm 3 1 1 1 (-2),
    tm 3 1 2 0 (-2),
    tm 3 1 2 1 (2),
    tm 3 2 1 0 (-1),
    tm 3 2 2 0 (1),
    tm 4 0 0 0 (-1),
    tm 4 0 0 1 (2),
    tm 4 0 0 2 (-1),
    tm 4 0 1 0 (3),
    tm 4 0 1 1 (-6),
    tm 4 0 1 2 (3),
    tm 4 0 2 0 (-1),
    tm 4 0 2 1 (2),
    tm 4 0 2 2 (-1),
    tm 4 1 0 0 (2),
    tm 4 1 0 1 (-2),
    tm 4 1 1 0 (-6),
    tm 4 1 1 1 (6),
    tm 4 1 2 0 (2),
    tm 4 1 2 1 (-2),
    tm 4 2 0 0 (-1),
    tm 4 2 1 0 (3),
    tm 4 2 2 0 (-1),
    tm 5 0 0 0 (2),
    tm 5 0 0 1 (-4),
    tm 5 0 0 2 (2),
    tm 5 0 1 0 (-2),
    tm 5 0 1 1 (4),
    tm 5 0 1 2 (-2),
    tm 5 1 0 0 (-4),
    tm 5 1 0 1 (4),
    tm 5 1 1 0 (4),
    tm 5 1 1 1 (-4),
    tm 5 2 0 0 (2),
    tm 5 2 1 0 (-2),
    tm 6 0 0 0 (-1),
    tm 6 0 0 1 (2),
    tm 6 0 0 2 (-1),
    tm 6 1 0 0 (2),
    tm 6 1 0 1 (-2),
    tm 6 2 0 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS0Position4Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 4 of S0 factors, exposing its cone core. -/
theorem betaSlotFactorizationS0Position4
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS0Position4 w1 w2 w3 w4
      = polyEval betaSlotS0Position4Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 0 of family S1: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS1Position0 : Poly :=
  [tm 0 2 4 2 (-1),
    tm 0 2 5 2 (1),
    tm 0 3 4 1 (-2),
    tm 0 3 4 2 (1),
    tm 0 3 5 1 (2),
    tm 0 3 5 2 (-1),
    tm 0 4 4 0 (-1),
    tm 0 4 4 1 (2),
    tm 0 4 5 0 (1),
    tm 0 4 5 1 (-2),
    tm 0 5 4 0 (1),
    tm 0 5 5 0 (-1),
    tm 1 2 3 2 (-2),
    tm 1 2 4 2 (2),
    tm 1 3 3 1 (-4),
    tm 1 3 3 2 (2),
    tm 1 3 4 1 (4),
    tm 1 3 4 2 (-2),
    tm 1 4 3 0 (-2),
    tm 1 4 3 1 (4),
    tm 1 4 4 0 (2),
    tm 1 4 4 1 (-4),
    tm 1 5 3 0 (2),
    tm 1 5 4 0 (-2),
    tm 2 2 2 2 (-1),
    tm 2 2 3 2 (1),
    tm 2 3 2 1 (-2),
    tm 2 3 2 2 (1),
    tm 2 3 3 1 (2),
    tm 2 3 3 2 (-1),
    tm 2 4 2 0 (-1),
    tm 2 4 2 1 (2),
    tm 2 4 3 0 (1),
    tm 2 4 3 1 (-2),
    tm 2 5 2 0 (1),
    tm 2 5 3 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS1Position0Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 0 of S1 factors, exposing its cone core. -/
theorem betaSlotFactorizationS1Position0
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS1Position0 w1 w2 w3 w4
      = polyEval betaSlotS1Position0Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 1 of family S1: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS1Position1 : Poly :=
  [tm 0 0 0 4 (-1),
    tm 0 0 0 5 (2),
    tm 0 0 0 6 (-1),
    tm 0 0 1 4 (2),
    tm 0 0 1 5 (-4),
    tm 0 0 1 6 (2),
    tm 0 0 2 4 (-1),
    tm 0 0 2 5 (2),
    tm 0 0 2 6 (-1),
    tm 0 1 0 3 (-1),
    tm 0 1 0 4 (3),
    tm 0 1 0 5 (-2),
    tm 0 1 1 3 (2),
    tm 0 1 1 4 (-6),
    tm 0 1 1 5 (4),
    tm 0 1 2 3 (-1),
    tm 0 1 2 4 (3),
    tm 0 1 2 5 (-2),
    tm 0 2 0 3 (1),
    tm 0 2 0 4 (-1),
    tm 0 2 1 3 (-2),
    tm 0 2 1 4 (2),
    tm 0 2 2 3 (1),
    tm 0 2 2 4 (-1),
    tm 1 0 0 4 (2),
    tm 1 0 0 5 (-4),
    tm 1 0 0 6 (2),
    tm 1 0 1 4 (-2),
    tm 1 0 1 5 (4),
    tm 1 0 1 6 (-2),
    tm 1 1 0 3 (2),
    tm 1 1 0 4 (-6),
    tm 1 1 0 5 (4),
    tm 1 1 1 3 (-2),
    tm 1 1 1 4 (6),
    tm 1 1 1 5 (-4),
    tm 1 2 0 3 (-2),
    tm 1 2 0 4 (2),
    tm 1 2 1 3 (2),
    tm 1 2 1 4 (-2),
    tm 2 0 0 4 (-1),
    tm 2 0 0 5 (2),
    tm 2 0 0 6 (-1),
    tm 2 1 0 3 (-1),
    tm 2 1 0 4 (3),
    tm 2 1 0 5 (-2),
    tm 2 2 0 3 (1),
    tm 2 2 0 4 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS1Position1Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 1 of S1 factors, exposing its cone core. -/
theorem betaSlotFactorizationS1Position1
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS1Position1 w1 w2 w3 w4
      = polyEval betaSlotS1Position1Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 2 of family S1: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS1Position2 : Poly :=
  [tm 0 0 4 1 (-1),
    tm 0 0 4 2 (2),
    tm 0 0 4 3 (-1),
    tm 0 0 5 1 (1),
    tm 0 0 5 2 (-2),
    tm 0 0 5 3 (1),
    tm 0 1 4 0 (-1),
    tm 0 1 4 1 (4),
    tm 0 1 4 2 (-3),
    tm 0 1 5 0 (1),
    tm 0 1 5 1 (-4),
    tm 0 1 5 2 (3),
    tm 0 2 4 0 (2),
    tm 0 2 4 1 (-3),
    tm 0 2 5 0 (-2),
    tm 0 2 5 1 (3),
    tm 0 3 4 0 (-1),
    tm 0 3 5 0 (1),
    tm 1 0 3 0 (1),
    tm 1 0 3 1 (-4),
    tm 1 0 3 2 (5),
    tm 1 0 3 3 (-2),
    tm 1 0 4 0 (-2),
    tm 1 0 4 1 (6),
    tm 1 0 4 2 (-6),
    tm 1 0 4 3 (2),
    tm 1 0 5 0 (1),
    tm 1 0 5 1 (-2),
    tm 1 0 5 2 (1),
    tm 1 1 3 0 (-4),
    tm 1 1 3 1 (10),
    tm 1 1 3 2 (-6),
    tm 1 1 4 0 (6),
    tm 1 1 4 1 (-12),
    tm 1 1 4 2 (6),
    tm 1 1 5 0 (-2),
    tm 1 1 5 1 (2),
    tm 1 2 3 0 (5),
    tm 1 2 3 1 (-6),
    tm 1 2 4 0 (-6),
    tm 1 2 4 1 (6),
    tm 1 2 5 0 (1),
    tm 1 3 3 0 (-2),
    tm 1 3 4 0 (2),
    tm 2 0 2 0 (1),
    tm 2 0 2 1 (-3),
    tm 2 0 2 2 (3),
    tm 2 0 2 3 (-1),
    tm 2 0 3 0 (-3),
    tm 2 0 3 1 (7),
    tm 2 0 3 2 (-5),
    tm 2 0 3 3 (1),
    tm 2 0 4 0 (2),
    tm 2 0 4 1 (-4),
    tm 2 0 4 2 (2),
    tm 2 1 2 0 (-3),
    tm 2 1 2 1 (6),
    tm 2 1 2 2 (-3),
    tm 2 1 3 0 (7),
    tm 2 1 3 1 (-10),
    tm 2 1 3 2 (3),
    tm 2 1 4 0 (-4),
    tm 2 1 4 1 (4),
    tm 2 2 2 0 (3),
    tm 2 2 2 1 (-3),
    tm 2 2 3 0 (-5),
    tm 2 2 3 1 (3),
    tm 2 2 4 0 (2),
    tm 2 3 2 0 (-1),
    tm 2 3 3 0 (1),
    tm 3 0 2 0 (-1),
    tm 3 0 2 1 (2),
    tm 3 0 2 2 (-1),
    tm 3 0 3 0 (1),
    tm 3 0 3 1 (-2),
    tm 3 0 3 2 (1),
    tm 3 1 2 0 (2),
    tm 3 1 2 1 (-2),
    tm 3 1 3 0 (-2),
    tm 3 1 3 1 (2),
    tm 3 2 2 0 (-1),
    tm 3 2 3 0 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS1Position2Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 1 (1),
      tm 0 1 1 0 (1),
      tm 1 0 0 0 (-1),
      tm 1 0 0 1 (1),
      tm 1 0 1 0 (1),
      tm 1 1 0 0 (1),
      tm 2 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 2 of S1 factors, exposing its cone core. -/
theorem betaSlotFactorizationS1Position2
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS1Position2 w1 w2 w3 w4
      = polyEval betaSlotS1Position2Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 3 of family S1: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS1Position3 : Poly :=
  [tm 0 2 0 2 (1),
    tm 0 2 0 3 (-1),
    tm 0 2 1 2 (-3),
    tm 0 2 1 3 (2),
    tm 0 2 2 2 (3),
    tm 0 2 2 3 (-1),
    tm 0 2 3 2 (-1),
    tm 0 3 0 1 (1),
    tm 0 3 0 2 (-3),
    tm 0 3 0 3 (1),
    tm 0 3 1 1 (-4),
    tm 0 3 1 2 (7),
    tm 0 3 1 3 (-2),
    tm 0 3 2 1 (5),
    tm 0 3 2 2 (-5),
    tm 0 3 2 3 (1),
    tm 0 3 3 1 (-2),
    tm 0 3 3 2 (1),
    tm 0 4 0 1 (-2),
    tm 0 4 0 2 (2),
    tm 0 4 1 0 (-1),
    tm 0 4 1 1 (6),
    tm 0 4 1 2 (-4),
    tm 0 4 2 0 (2),
    tm 0 4 2 1 (-6),
    tm 0 4 2 2 (2),
    tm 0 4 3 0 (-1),
    tm 0 4 3 1 (2),
    tm 0 5 0 1 (1),
    tm 0 5 1 0 (1),
    tm 0 5 1 1 (-2),
    tm 0 5 2 0 (-2),
    tm 0 5 2 1 (1),
    tm 0 5 3 0 (1),
    tm 1 2 0 2 (-3),
    tm 1 2 0 3 (2),
    tm 1 2 1 2 (6),
    tm 1 2 1 3 (-2),
    tm 1 2 2 2 (-3),
    tm 1 3 0 1 (-4),
    tm 1 3 0 2 (7),
    tm 1 3 0 3 (-2),
    tm 1 3 1 1 (10),
    tm 1 3 1 2 (-10),
    tm 1 3 1 3 (2),
    tm 1 3 2 1 (-6),
    tm 1 3 2 2 (3),
    tm 1 4 0 0 (-1),
    tm 1 4 0 1 (6),
    tm 1 4 0 2 (-4),
    tm 1 4 1 0 (4),
    tm 1 4 1 1 (-12),
    tm 1 4 1 2 (4),
    tm 1 4 2 0 (-3),
    tm 1 4 2 1 (6),
    tm 1 5 0 0 (1),
    tm 1 5 0 1 (-2),
    tm 1 5 1 0 (-4),
    tm 1 5 1 1 (2),
    tm 1 5 2 0 (3),
    tm 2 2 0 2 (3),
    tm 2 2 0 3 (-1),
    tm 2 2 1 2 (-3),
    tm 2 3 0 1 (5),
    tm 2 3 0 2 (-5),
    tm 2 3 0 3 (1),
    tm 2 3 1 1 (-6),
    tm 2 3 1 2 (3),
    tm 2 4 0 0 (2),
    tm 2 4 0 1 (-6),
    tm 2 4 0 2 (2),
    tm 2 4 1 0 (-3),
    tm 2 4 1 1 (6),
    tm 2 5 0 0 (-2),
    tm 2 5 0 1 (1),
    tm 2 5 1 0 (3),
    tm 3 2 0 2 (-1),
    tm 3 3 0 1 (-2),
    tm 3 3 0 2 (1),
    tm 3 4 0 0 (-1),
    tm 3 4 0 1 (2),
    tm 3 5 0 0 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS1Position3Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (-1),
      tm 0 0 0 2 (1),
      tm 0 0 1 1 (1),
      tm 0 1 0 1 (1),
      tm 0 1 1 0 (1),
      tm 1 0 0 1 (1),
      tm 1 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 3 of S1 factors, exposing its cone core. -/
theorem betaSlotFactorizationS1Position3
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS1Position3 w1 w2 w3 w4
      = polyEval betaSlotS1Position3Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 4 of family S1: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS1Position4 : Poly :=
  [tm 3 0 1 0 (-1),
    tm 3 0 1 1 (2),
    tm 3 0 1 2 (-1),
    tm 3 0 2 0 (1),
    tm 3 0 2 1 (-2),
    tm 3 0 2 2 (1),
    tm 3 1 1 0 (2),
    tm 3 1 1 1 (-2),
    tm 3 1 2 0 (-2),
    tm 3 1 2 1 (2),
    tm 3 2 1 0 (-1),
    tm 3 2 2 0 (1),
    tm 4 0 0 0 (-1),
    tm 4 0 0 1 (2),
    tm 4 0 0 2 (-1),
    tm 4 0 1 0 (3),
    tm 4 0 1 1 (-6),
    tm 4 0 1 2 (3),
    tm 4 0 2 0 (-1),
    tm 4 0 2 1 (2),
    tm 4 0 2 2 (-1),
    tm 4 1 0 0 (2),
    tm 4 1 0 1 (-2),
    tm 4 1 1 0 (-6),
    tm 4 1 1 1 (6),
    tm 4 1 2 0 (2),
    tm 4 1 2 1 (-2),
    tm 4 2 0 0 (-1),
    tm 4 2 1 0 (3),
    tm 4 2 2 0 (-1),
    tm 5 0 0 0 (2),
    tm 5 0 0 1 (-4),
    tm 5 0 0 2 (2),
    tm 5 0 1 0 (-2),
    tm 5 0 1 1 (4),
    tm 5 0 1 2 (-2),
    tm 5 1 0 0 (-4),
    tm 5 1 0 1 (4),
    tm 5 1 1 0 (4),
    tm 5 1 1 1 (-4),
    tm 5 2 0 0 (2),
    tm 5 2 1 0 (-2),
    tm 6 0 0 0 (-1),
    tm 6 0 0 1 (2),
    tm 6 0 0 2 (-1),
    tm 6 1 0 0 (2),
    tm 6 1 0 1 (-2),
    tm 6 2 0 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS1Position4Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 4 of S1 factors, exposing its cone core. -/
theorem betaSlotFactorizationS1Position4
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS1Position4 w1 w2 w3 w4
      = polyEval betaSlotS1Position4Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 0 of family S2: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS2Position0 : Poly :=
  [tm 2 0 2 4 (-1),
    tm 2 0 2 5 (1),
    tm 2 1 2 3 (-2),
    tm 2 1 2 4 (2),
    tm 2 2 2 2 (-1),
    tm 2 2 2 3 (1),
    tm 3 0 1 4 (-2),
    tm 3 0 1 5 (2),
    tm 3 0 2 4 (1),
    tm 3 0 2 5 (-1),
    tm 3 1 1 3 (-4),
    tm 3 1 1 4 (4),
    tm 3 1 2 3 (2),
    tm 3 1 2 4 (-2),
    tm 3 2 1 2 (-2),
    tm 3 2 1 3 (2),
    tm 3 2 2 2 (1),
    tm 3 2 2 3 (-1),
    tm 4 0 0 4 (-1),
    tm 4 0 0 5 (1),
    tm 4 0 1 4 (2),
    tm 4 0 1 5 (-2),
    tm 4 1 0 3 (-2),
    tm 4 1 0 4 (2),
    tm 4 1 1 3 (4),
    tm 4 1 1 4 (-4),
    tm 4 2 0 2 (-1),
    tm 4 2 0 3 (1),
    tm 4 2 1 2 (2),
    tm 4 2 1 3 (-2),
    tm 5 0 0 4 (1),
    tm 5 0 0 5 (-1),
    tm 5 1 0 3 (2),
    tm 5 1 0 4 (-2),
    tm 5 2 0 2 (1),
    tm 5 2 0 3 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS2Position0Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 0 of S2 factors, exposing its cone core. -/
theorem betaSlotFactorizationS2Position0
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS2Position0 w1 w2 w3 w4
      = polyEval betaSlotS2Position0Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 1 of family S2: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS2Position1 : Poly :=
  [tm 0 0 1 4 (-1),
    tm 0 0 1 5 (1),
    tm 0 0 2 4 (2),
    tm 0 0 2 5 (-2),
    tm 0 0 3 4 (-1),
    tm 0 0 3 5 (1),
    tm 0 1 0 3 (1),
    tm 0 1 0 4 (-2),
    tm 0 1 0 5 (1),
    tm 0 1 1 3 (-4),
    tm 0 1 1 4 (6),
    tm 0 1 1 5 (-2),
    tm 0 1 2 3 (5),
    tm 0 1 2 4 (-6),
    tm 0 1 2 5 (1),
    tm 0 1 3 3 (-2),
    tm 0 1 3 4 (2),
    tm 0 2 0 2 (1),
    tm 0 2 0 3 (-3),
    tm 0 2 0 4 (2),
    tm 0 2 1 2 (-3),
    tm 0 2 1 3 (7),
    tm 0 2 1 4 (-4),
    tm 0 2 2 2 (3),
    tm 0 2 2 3 (-5),
    tm 0 2 2 4 (2),
    tm 0 2 3 2 (-1),
    tm 0 2 3 3 (1),
    tm 0 3 0 2 (-1),
    tm 0 3 0 3 (1),
    tm 0 3 1 2 (2),
    tm 0 3 1 3 (-2),
    tm 0 3 2 2 (-1),
    tm 0 3 2 3 (1),
    tm 1 0 0 4 (-1),
    tm 1 0 0 5 (1),
    tm 1 0 1 4 (4),
    tm 1 0 1 5 (-4),
    tm 1 0 2 4 (-3),
    tm 1 0 2 5 (3),
    tm 1 1 0 3 (-4),
    tm 1 1 0 4 (6),
    tm 1 1 0 5 (-2),
    tm 1 1 1 3 (10),
    tm 1 1 1 4 (-12),
    tm 1 1 1 5 (2),
    tm 1 1 2 3 (-6),
    tm 1 1 2 4 (6),
    tm 1 2 0 2 (-3),
    tm 1 2 0 3 (7),
    tm 1 2 0 4 (-4),
    tm 1 2 1 2 (6),
    tm 1 2 1 3 (-10),
    tm 1 2 1 4 (4),
    tm 1 2 2 2 (-3),
    tm 1 2 2 3 (3),
    tm 1 3 0 2 (2),
    tm 1 3 0 3 (-2),
    tm 1 3 1 2 (-2),
    tm 1 3 1 3 (2),
    tm 2 0 0 4 (2),
    tm 2 0 0 5 (-2),
    tm 2 0 1 4 (-3),
    tm 2 0 1 5 (3),
    tm 2 1 0 3 (5),
    tm 2 1 0 4 (-6),
    tm 2 1 0 5 (1),
    tm 2 1 1 3 (-6),
    tm 2 1 1 4 (6),
    tm 2 2 0 2 (3),
    tm 2 2 0 3 (-5),
    tm 2 2 0 4 (2),
    tm 2 2 1 2 (-3),
    tm 2 2 1 3 (3),
    tm 2 3 0 2 (-1),
    tm 2 3 0 3 (1),
    tm 3 0 0 4 (-1),
    tm 3 0 0 5 (1),
    tm 3 1 0 3 (-2),
    tm 3 1 0 4 (2),
    tm 3 2 0 2 (-1),
    tm 3 2 0 3 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS2Position1Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 1 1 (1),
      tm 0 1 0 0 (-1),
      tm 0 1 0 1 (1),
      tm 0 1 1 0 (1),
      tm 0 2 0 0 (1),
      tm 1 0 0 1 (1),
      tm 1 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 1 of S2 factors, exposing its cone core. -/
theorem betaSlotFactorizationS2Position1
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS2Position1 w1 w2 w3 w4
      = polyEval betaSlotS2Position1Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 2 of family S2: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS2Position2 : Poly :=
  [tm 0 0 4 0 (-1),
    tm 0 0 4 1 (2),
    tm 0 0 4 2 (-1),
    tm 0 0 5 0 (2),
    tm 0 0 5 1 (-4),
    tm 0 0 5 2 (2),
    tm 0 0 6 0 (-1),
    tm 0 0 6 1 (2),
    tm 0 0 6 2 (-1),
    tm 0 1 4 0 (2),
    tm 0 1 4 1 (-2),
    tm 0 1 5 0 (-4),
    tm 0 1 5 1 (4),
    tm 0 1 6 0 (2),
    tm 0 1 6 1 (-2),
    tm 0 2 4 0 (-1),
    tm 0 2 5 0 (2),
    tm 0 2 6 0 (-1),
    tm 1 0 3 0 (-1),
    tm 1 0 3 1 (2),
    tm 1 0 3 2 (-1),
    tm 1 0 4 0 (3),
    tm 1 0 4 1 (-6),
    tm 1 0 4 2 (3),
    tm 1 0 5 0 (-2),
    tm 1 0 5 1 (4),
    tm 1 0 5 2 (-2),
    tm 1 1 3 0 (2),
    tm 1 1 3 1 (-2),
    tm 1 1 4 0 (-6),
    tm 1 1 4 1 (6),
    tm 1 1 5 0 (4),
    tm 1 1 5 1 (-4),
    tm 1 2 3 0 (-1),
    tm 1 2 4 0 (3),
    tm 1 2 5 0 (-2),
    tm 2 0 3 0 (1),
    tm 2 0 3 1 (-2),
    tm 2 0 3 2 (1),
    tm 2 0 4 0 (-1),
    tm 2 0 4 1 (2),
    tm 2 0 4 2 (-1),
    tm 2 1 3 0 (-2),
    tm 2 1 3 1 (2),
    tm 2 1 4 0 (2),
    tm 2 1 4 1 (-2),
    tm 2 2 3 0 (1),
    tm 2 2 4 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS2Position2Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 2 of S2 factors, exposing its cone core. -/
theorem betaSlotFactorizationS2Position2
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS2Position2 w1 w2 w3 w4
      = polyEval betaSlotS2Position2Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 3 of family S2: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS2Position3 : Poly :=
  [tm 0 3 0 1 (-1),
    tm 0 3 0 2 (1),
    tm 0 3 1 1 (2),
    tm 0 3 1 2 (-2),
    tm 0 3 2 1 (-1),
    tm 0 3 2 2 (1),
    tm 0 4 0 0 (-1),
    tm 0 4 0 1 (3),
    tm 0 4 0 2 (-1),
    tm 0 4 1 0 (2),
    tm 0 4 1 1 (-6),
    tm 0 4 1 2 (2),
    tm 0 4 2 0 (-1),
    tm 0 4 2 1 (3),
    tm 0 4 2 2 (-1),
    tm 0 5 0 0 (2),
    tm 0 5 0 1 (-2),
    tm 0 5 1 0 (-4),
    tm 0 5 1 1 (4),
    tm 0 5 2 0 (2),
    tm 0 5 2 1 (-2),
    tm 0 6 0 0 (-1),
    tm 0 6 1 0 (2),
    tm 0 6 2 0 (-1),
    tm 1 3 0 1 (2),
    tm 1 3 0 2 (-2),
    tm 1 3 1 1 (-2),
    tm 1 3 1 2 (2),
    tm 1 4 0 0 (2),
    tm 1 4 0 1 (-6),
    tm 1 4 0 2 (2),
    tm 1 4 1 0 (-2),
    tm 1 4 1 1 (6),
    tm 1 4 1 2 (-2),
    tm 1 5 0 0 (-4),
    tm 1 5 0 1 (4),
    tm 1 5 1 0 (4),
    tm 1 5 1 1 (-4),
    tm 1 6 0 0 (2),
    tm 1 6 1 0 (-2),
    tm 2 3 0 1 (-1),
    tm 2 3 0 2 (1),
    tm 2 4 0 0 (-1),
    tm 2 4 0 1 (3),
    tm 2 4 0 2 (-1),
    tm 2 5 0 0 (2),
    tm 2 5 0 1 (-2),
    tm 2 6 0 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS2Position3Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 3 of S2 factors, exposing its cone core. -/
theorem betaSlotFactorizationS2Position3
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS2Position3 w1 w2 w3 w4
      = polyEval betaSlotS2Position3Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 4 of family S2: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS2Position4 : Poly :=
  [tm 2 0 2 0 (1),
    tm 2 0 2 1 (-3),
    tm 2 0 2 2 (3),
    tm 2 0 2 3 (-1),
    tm 2 0 3 0 (-1),
    tm 2 0 3 1 (2),
    tm 2 0 3 2 (-1),
    tm 2 1 2 0 (-3),
    tm 2 1 2 1 (6),
    tm 2 1 2 2 (-3),
    tm 2 1 3 0 (2),
    tm 2 1 3 1 (-2),
    tm 2 2 2 0 (3),
    tm 2 2 2 1 (-3),
    tm 2 2 3 0 (-1),
    tm 2 3 2 0 (-1),
    tm 3 0 1 0 (1),
    tm 3 0 1 1 (-4),
    tm 3 0 1 2 (5),
    tm 3 0 1 3 (-2),
    tm 3 0 2 0 (-3),
    tm 3 0 2 1 (7),
    tm 3 0 2 2 (-5),
    tm 3 0 2 3 (1),
    tm 3 0 3 0 (1),
    tm 3 0 3 1 (-2),
    tm 3 0 3 2 (1),
    tm 3 1 1 0 (-4),
    tm 3 1 1 1 (10),
    tm 3 1 1 2 (-6),
    tm 3 1 2 0 (7),
    tm 3 1 2 1 (-10),
    tm 3 1 2 2 (3),
    tm 3 1 3 0 (-2),
    tm 3 1 3 1 (2),
    tm 3 2 1 0 (5),
    tm 3 2 1 1 (-6),
    tm 3 2 2 0 (-5),
    tm 3 2 2 1 (3),
    tm 3 2 3 0 (1),
    tm 3 3 1 0 (-2),
    tm 3 3 2 0 (1),
    tm 4 0 0 1 (-1),
    tm 4 0 0 2 (2),
    tm 4 0 0 3 (-1),
    tm 4 0 1 0 (-2),
    tm 4 0 1 1 (6),
    tm 4 0 1 2 (-6),
    tm 4 0 1 3 (2),
    tm 4 0 2 0 (2),
    tm 4 0 2 1 (-4),
    tm 4 0 2 2 (2),
    tm 4 1 0 0 (-1),
    tm 4 1 0 1 (4),
    tm 4 1 0 2 (-3),
    tm 4 1 1 0 (6),
    tm 4 1 1 1 (-12),
    tm 4 1 1 2 (6),
    tm 4 1 2 0 (-4),
    tm 4 1 2 1 (4),
    tm 4 2 0 0 (2),
    tm 4 2 0 1 (-3),
    tm 4 2 1 0 (-6),
    tm 4 2 1 1 (6),
    tm 4 2 2 0 (2),
    tm 4 3 0 0 (-1),
    tm 4 3 1 0 (2),
    tm 5 0 0 1 (1),
    tm 5 0 0 2 (-2),
    tm 5 0 0 3 (1),
    tm 5 0 1 0 (1),
    tm 5 0 1 1 (-2),
    tm 5 0 1 2 (1),
    tm 5 1 0 0 (1),
    tm 5 1 0 1 (-4),
    tm 5 1 0 2 (3),
    tm 5 1 1 0 (-2),
    tm 5 1 1 1 (2),
    tm 5 2 0 0 (-2),
    tm 5 2 0 1 (3),
    tm 5 2 1 0 (1),
    tm 5 3 0 0 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS2Position4Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (-1),
      tm 0 0 1 1 (1),
      tm 0 0 2 0 (1),
      tm 0 1 1 0 (1),
      tm 1 0 0 1 (1),
      tm 1 0 1 0 (1),
      tm 1 1 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 4 of S2 factors, exposing its cone core. -/
theorem betaSlotFactorizationS2Position4
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS2Position4 w1 w2 w3 w4
      = polyEval betaSlotS2Position4Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 0 of family S3: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS3Position0 : Poly :=
  [tm 2 2 2 2 (-1),
    tm 2 3 2 1 (-2),
    tm 2 3 2 2 (1),
    tm 2 4 2 0 (-1),
    tm 2 4 2 1 (2),
    tm 2 5 2 0 (1),
    tm 3 2 1 2 (-2),
    tm 3 2 2 2 (1),
    tm 3 3 1 1 (-4),
    tm 3 3 1 2 (2),
    tm 3 3 2 1 (2),
    tm 3 3 2 2 (-1),
    tm 3 4 1 0 (-2),
    tm 3 4 1 1 (4),
    tm 3 4 2 0 (1),
    tm 3 4 2 1 (-2),
    tm 3 5 1 0 (2),
    tm 3 5 2 0 (-1),
    tm 4 2 0 2 (-1),
    tm 4 2 1 2 (2),
    tm 4 3 0 1 (-2),
    tm 4 3 0 2 (1),
    tm 4 3 1 1 (4),
    tm 4 3 1 2 (-2),
    tm 4 4 0 0 (-1),
    tm 4 4 0 1 (2),
    tm 4 4 1 0 (2),
    tm 4 4 1 1 (-4),
    tm 4 5 0 0 (1),
    tm 4 5 1 0 (-2),
    tm 5 2 0 2 (1),
    tm 5 3 0 1 (2),
    tm 5 3 0 2 (-1),
    tm 5 4 0 0 (1),
    tm 5 4 0 1 (-2),
    tm 5 5 0 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS3Position0Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 0 of S3 factors, exposing its cone core. -/
theorem betaSlotFactorizationS3Position0
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS3Position0 w1 w2 w3 w4
      = polyEval betaSlotS3Position0Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 1 of family S3: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS3Position1 : Poly :=
  [tm 0 0 0 4 (-1),
    tm 0 0 0 5 (2),
    tm 0 0 0 6 (-1),
    tm 0 0 1 4 (2),
    tm 0 0 1 5 (-4),
    tm 0 0 1 6 (2),
    tm 0 0 2 4 (-1),
    tm 0 0 2 5 (2),
    tm 0 0 2 6 (-1),
    tm 0 1 0 3 (-1),
    tm 0 1 0 4 (3),
    tm 0 1 0 5 (-2),
    tm 0 1 1 3 (2),
    tm 0 1 1 4 (-6),
    tm 0 1 1 5 (4),
    tm 0 1 2 3 (-1),
    tm 0 1 2 4 (3),
    tm 0 1 2 5 (-2),
    tm 0 2 0 3 (1),
    tm 0 2 0 4 (-1),
    tm 0 2 1 3 (-2),
    tm 0 2 1 4 (2),
    tm 0 2 2 3 (1),
    tm 0 2 2 4 (-1),
    tm 1 0 0 4 (2),
    tm 1 0 0 5 (-4),
    tm 1 0 0 6 (2),
    tm 1 0 1 4 (-2),
    tm 1 0 1 5 (4),
    tm 1 0 1 6 (-2),
    tm 1 1 0 3 (2),
    tm 1 1 0 4 (-6),
    tm 1 1 0 5 (4),
    tm 1 1 1 3 (-2),
    tm 1 1 1 4 (6),
    tm 1 1 1 5 (-4),
    tm 1 2 0 3 (-2),
    tm 1 2 0 4 (2),
    tm 1 2 1 3 (2),
    tm 1 2 1 4 (-2),
    tm 2 0 0 4 (-1),
    tm 2 0 0 5 (2),
    tm 2 0 0 6 (-1),
    tm 2 1 0 3 (-1),
    tm 2 1 0 4 (3),
    tm 2 1 0 5 (-2),
    tm 2 2 0 3 (1),
    tm 2 2 0 4 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS3Position1Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 1 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 1 of S3 factors, exposing its cone core. -/
theorem betaSlotFactorizationS3Position1
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS3Position1 w1 w2 w3 w4
      = polyEval betaSlotS3Position1Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 2 of family S3: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS3Position2 : Poly :=
  [tm 0 0 4 0 (-1),
    tm 0 0 4 1 (2),
    tm 0 0 4 2 (-1),
    tm 0 0 5 0 (2),
    tm 0 0 5 1 (-4),
    tm 0 0 5 2 (2),
    tm 0 0 6 0 (-1),
    tm 0 0 6 1 (2),
    tm 0 0 6 2 (-1),
    tm 0 1 4 0 (2),
    tm 0 1 4 1 (-2),
    tm 0 1 5 0 (-4),
    tm 0 1 5 1 (4),
    tm 0 1 6 0 (2),
    tm 0 1 6 1 (-2),
    tm 0 2 4 0 (-1),
    tm 0 2 5 0 (2),
    tm 0 2 6 0 (-1),
    tm 1 0 3 0 (-1),
    tm 1 0 3 1 (2),
    tm 1 0 3 2 (-1),
    tm 1 0 4 0 (3),
    tm 1 0 4 1 (-6),
    tm 1 0 4 2 (3),
    tm 1 0 5 0 (-2),
    tm 1 0 5 1 (4),
    tm 1 0 5 2 (-2),
    tm 1 1 3 0 (2),
    tm 1 1 3 1 (-2),
    tm 1 1 4 0 (-6),
    tm 1 1 4 1 (6),
    tm 1 1 5 0 (4),
    tm 1 1 5 1 (-4),
    tm 1 2 3 0 (-1),
    tm 1 2 4 0 (3),
    tm 1 2 5 0 (-2),
    tm 2 0 3 0 (1),
    tm 2 0 3 1 (-2),
    tm 2 0 3 2 (1),
    tm 2 0 4 0 (-1),
    tm 2 0 4 1 (2),
    tm 2 0 4 2 (-1),
    tm 2 1 3 0 (-2),
    tm 2 1 3 1 (2),
    tm 2 1 4 0 (2),
    tm 2 1 4 1 (-2),
    tm 2 2 3 0 (1),
    tm 2 2 4 0 (-1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS3Position2Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (-1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 2 of S3 factors, exposing its cone core. -/
theorem betaSlotFactorizationS3Position2
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS3Position2 w1 w2 w3 w4
      = polyEval betaSlotS3Position2Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 3 of family S3: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS3Position3 : Poly :=
  [tm 0 2 0 2 (1),
    tm 0 2 0 3 (-1),
    tm 0 2 1 2 (-3),
    tm 0 2 1 3 (2),
    tm 0 2 2 2 (3),
    tm 0 2 2 3 (-1),
    tm 0 2 3 2 (-1),
    tm 0 3 0 1 (1),
    tm 0 3 0 2 (-3),
    tm 0 3 0 3 (1),
    tm 0 3 1 1 (-4),
    tm 0 3 1 2 (7),
    tm 0 3 1 3 (-2),
    tm 0 3 2 1 (5),
    tm 0 3 2 2 (-5),
    tm 0 3 2 3 (1),
    tm 0 3 3 1 (-2),
    tm 0 3 3 2 (1),
    tm 0 4 0 1 (-2),
    tm 0 4 0 2 (2),
    tm 0 4 1 0 (-1),
    tm 0 4 1 1 (6),
    tm 0 4 1 2 (-4),
    tm 0 4 2 0 (2),
    tm 0 4 2 1 (-6),
    tm 0 4 2 2 (2),
    tm 0 4 3 0 (-1),
    tm 0 4 3 1 (2),
    tm 0 5 0 1 (1),
    tm 0 5 1 0 (1),
    tm 0 5 1 1 (-2),
    tm 0 5 2 0 (-2),
    tm 0 5 2 1 (1),
    tm 0 5 3 0 (1),
    tm 1 2 0 2 (-3),
    tm 1 2 0 3 (2),
    tm 1 2 1 2 (6),
    tm 1 2 1 3 (-2),
    tm 1 2 2 2 (-3),
    tm 1 3 0 1 (-4),
    tm 1 3 0 2 (7),
    tm 1 3 0 3 (-2),
    tm 1 3 1 1 (10),
    tm 1 3 1 2 (-10),
    tm 1 3 1 3 (2),
    tm 1 3 2 1 (-6),
    tm 1 3 2 2 (3),
    tm 1 4 0 0 (-1),
    tm 1 4 0 1 (6),
    tm 1 4 0 2 (-4),
    tm 1 4 1 0 (4),
    tm 1 4 1 1 (-12),
    tm 1 4 1 2 (4),
    tm 1 4 2 0 (-3),
    tm 1 4 2 1 (6),
    tm 1 5 0 0 (1),
    tm 1 5 0 1 (-2),
    tm 1 5 1 0 (-4),
    tm 1 5 1 1 (2),
    tm 1 5 2 0 (3),
    tm 2 2 0 2 (3),
    tm 2 2 0 3 (-1),
    tm 2 2 1 2 (-3),
    tm 2 3 0 1 (5),
    tm 2 3 0 2 (-5),
    tm 2 3 0 3 (1),
    tm 2 3 1 1 (-6),
    tm 2 3 1 2 (3),
    tm 2 4 0 0 (2),
    tm 2 4 0 1 (-6),
    tm 2 4 0 2 (2),
    tm 2 4 1 0 (-3),
    tm 2 4 1 1 (6),
    tm 2 5 0 0 (-2),
    tm 2 5 0 1 (1),
    tm 2 5 1 0 (3),
    tm 3 2 0 2 (-1),
    tm 3 3 0 1 (-2),
    tm 3 3 0 2 (1),
    tm 3 4 0 0 (-1),
    tm 3 4 0 1 (2),
    tm 3 5 0 0 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS3Position3Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 1 0 0 (1)]))
    ([tm 0 0 0 1 (-1),
      tm 0 0 0 2 (1),
      tm 0 0 1 1 (1),
      tm 0 1 0 1 (1),
      tm 0 1 1 0 (1),
      tm 1 0 0 1 (1),
      tm 1 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 3 of S3 factors, exposing its cone core. -/
theorem betaSlotFactorizationS3Position3
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS3Position3 w1 w2 w3 w4
      = polyEval betaSlotS3Position3Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Beta slot 4 of family S3: the signed 4x4 Cramer minor, content stripped. -/
def betaSlotS3Position4 : Poly :=
  [tm 2 0 2 0 (1),
    tm 2 0 2 1 (-3),
    tm 2 0 2 2 (3),
    tm 2 0 2 3 (-1),
    tm 2 0 3 0 (-1),
    tm 2 0 3 1 (2),
    tm 2 0 3 2 (-1),
    tm 2 1 2 0 (-3),
    tm 2 1 2 1 (6),
    tm 2 1 2 2 (-3),
    tm 2 1 3 0 (2),
    tm 2 1 3 1 (-2),
    tm 2 2 2 0 (3),
    tm 2 2 2 1 (-3),
    tm 2 2 3 0 (-1),
    tm 2 3 2 0 (-1),
    tm 3 0 1 0 (1),
    tm 3 0 1 1 (-4),
    tm 3 0 1 2 (5),
    tm 3 0 1 3 (-2),
    tm 3 0 2 0 (-3),
    tm 3 0 2 1 (7),
    tm 3 0 2 2 (-5),
    tm 3 0 2 3 (1),
    tm 3 0 3 0 (1),
    tm 3 0 3 1 (-2),
    tm 3 0 3 2 (1),
    tm 3 1 1 0 (-4),
    tm 3 1 1 1 (10),
    tm 3 1 1 2 (-6),
    tm 3 1 2 0 (7),
    tm 3 1 2 1 (-10),
    tm 3 1 2 2 (3),
    tm 3 1 3 0 (-2),
    tm 3 1 3 1 (2),
    tm 3 2 1 0 (5),
    tm 3 2 1 1 (-6),
    tm 3 2 2 0 (-5),
    tm 3 2 2 1 (3),
    tm 3 2 3 0 (1),
    tm 3 3 1 0 (-2),
    tm 3 3 2 0 (1),
    tm 4 0 0 1 (-1),
    tm 4 0 0 2 (2),
    tm 4 0 0 3 (-1),
    tm 4 0 1 0 (-2),
    tm 4 0 1 1 (6),
    tm 4 0 1 2 (-6),
    tm 4 0 1 3 (2),
    tm 4 0 2 0 (2),
    tm 4 0 2 1 (-4),
    tm 4 0 2 2 (2),
    tm 4 1 0 0 (-1),
    tm 4 1 0 1 (4),
    tm 4 1 0 2 (-3),
    tm 4 1 1 0 (6),
    tm 4 1 1 1 (-12),
    tm 4 1 1 2 (6),
    tm 4 1 2 0 (-4),
    tm 4 1 2 1 (4),
    tm 4 2 0 0 (2),
    tm 4 2 0 1 (-3),
    tm 4 2 1 0 (-6),
    tm 4 2 1 1 (6),
    tm 4 2 2 0 (2),
    tm 4 3 0 0 (-1),
    tm 4 3 1 0 (2),
    tm 5 0 0 1 (1),
    tm 5 0 0 2 (-2),
    tm 5 0 0 3 (1),
    tm 5 0 1 0 (1),
    tm 5 0 1 1 (-2),
    tm 5 0 1 2 (1),
    tm 5 1 0 0 (1),
    tm 5 1 0 1 (-4),
    tm 5 1 0 2 (3),
    tm 5 1 1 0 (-2),
    tm 5 1 1 1 (2),
    tm 5 2 0 0 (-2),
    tm 5 2 0 1 (3),
    tm 5 2 1 0 (1),
    tm 5 3 0 0 (1)]

/-- The same slot as an explicit product: every factor is a simplex atom except the single cone-boundary core. -/
def betaSlotS3Position4Factored : Poly :=
  polyMul (polyMul (polyMul (polyMul (polyMul (polyMul (polyMul ([tm 0 0 0 0 (1)])
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 0 0 0 1 (1),
      tm 0 1 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 1 0 0 0 (1)]))
    ([tm 0 0 0 0 (-1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (1),
      tm 1 0 0 0 (1)]))
    ([tm 0 0 1 0 (-1),
      tm 0 0 1 1 (1),
      tm 0 0 2 0 (1),
      tm 0 1 1 0 (1),
      tm 1 0 0 1 (1),
      tm 1 0 1 0 (1),
      tm 1 1 0 0 (1)])

/-- KERNEL-CHECKED: beta slot 4 of S3 factors, exposing its cone core. -/
theorem betaSlotFactorizationS3Position4
    (w1 w2 w3 w4 : Int) :
    polyEval betaSlotS3Position4 w1 w2 w3 w4
      = polyEval betaSlotS3Position4Factored w1 w2 w3 w4 :=
  polyEval_eq_of_canon_eq _ _ (by decide) w1 w2 w3 w4

/-- Column 0 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column0 : Poly :=
  [tm 2 2 4 0 (-1),
    tm 2 2 4 1 (2),
    tm 2 2 4 2 (-1),
    tm 2 2 5 0 (1),
    tm 2 2 5 1 (-2),
    tm 2 2 5 2 (1),
    tm 2 3 4 0 (3),
    tm 2 3 4 1 (-4),
    tm 2 3 4 2 (1),
    tm 2 3 5 0 (-3),
    tm 2 3 5 1 (4),
    tm 2 3 5 2 (-1),
    tm 2 4 4 0 (-3),
    tm 2 4 4 1 (2),
    tm 2 4 5 0 (3),
    tm 2 4 5 1 (-2),
    tm 2 5 4 0 (1),
    tm 2 5 5 0 (-1),
    tm 3 2 3 0 (-2),
    tm 3 2 3 1 (4),
    tm 3 2 3 2 (-2),
    tm 3 2 4 0 (3),
    tm 3 2 4 1 (-6),
    tm 3 2 4 2 (3),
    tm 3 2 5 0 (-1),
    tm 3 2 5 1 (2),
    tm 3 2 5 2 (-1),
    tm 3 3 3 0 (6),
    tm 3 3 3 1 (-8),
    tm 3 3 3 2 (2),
    tm 3 3 4 0 (-9),
    tm 3 3 4 1 (12),
    tm 3 3 4 2 (-3),
    tm 3 3 5 0 (3),
    tm 3 3 5 1 (-4),
    tm 3 3 5 2 (1),
    tm 3 4 3 0 (-6),
    tm 3 4 3 1 (4),
    tm 3 4 4 0 (9),
    tm 3 4 4 1 (-6),
    tm 3 4 5 0 (-3),
    tm 3 4 5 1 (2),
    tm 3 5 3 0 (2),
    tm 3 5 4 0 (-3),
    tm 3 5 5 0 (1),
    tm 4 2 2 0 (-1),
    tm 4 2 2 1 (2),
    tm 4 2 2 2 (-1),
    tm 4 2 3 0 (3),
    tm 4 2 3 1 (-6),
    tm 4 2 3 2 (3),
    tm 4 2 4 0 (-2),
    tm 4 2 4 1 (4),
    tm 4 2 4 2 (-2),
    tm 4 3 2 0 (3),
    tm 4 3 2 1 (-4),
    tm 4 3 2 2 (1),
    tm 4 3 3 0 (-9),
    tm 4 3 3 1 (12),
    tm 4 3 3 2 (-3),
    tm 4 3 4 0 (6),
    tm 4 3 4 1 (-8),
    tm 4 3 4 2 (2),
    tm 4 4 2 0 (-3),
    tm 4 4 2 1 (2),
    tm 4 4 3 0 (9),
    tm 4 4 3 1 (-6),
    tm 4 4 4 0 (-6),
    tm 4 4 4 1 (4),
    tm 4 5 2 0 (1),
    tm 4 5 3 0 (-3),
    tm 4 5 4 0 (2),
    tm 5 2 2 0 (1),
    tm 5 2 2 1 (-2),
    tm 5 2 2 2 (1),
    tm 5 2 3 0 (-1),
    tm 5 2 3 1 (2),
    tm 5 2 3 2 (-1),
    tm 5 3 2 0 (-3),
    tm 5 3 2 1 (4),
    tm 5 3 2 2 (-1),
    tm 5 3 3 0 (3),
    tm 5 3 3 1 (-4),
    tm 5 3 3 2 (1),
    tm 5 4 2 0 (3),
    tm 5 4 2 1 (-2),
    tm 5 4 3 0 (-3),
    tm 5 4 3 1 (2),
    tm 5 5 2 0 (-1),
    tm 5 5 3 0 (1)]

/-- Column 0 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column0 : Poly :=
  [tm 2 2 0 4 (-1),
    tm 2 2 0 5 (1),
    tm 2 2 1 4 (2),
    tm 2 2 1 5 (-2),
    tm 2 2 2 4 (-1),
    tm 2 2 2 5 (1),
    tm 2 3 0 3 (-2),
    tm 2 3 0 4 (3),
    tm 2 3 0 5 (-1),
    tm 2 3 1 3 (4),
    tm 2 3 1 4 (-6),
    tm 2 3 1 5 (2),
    tm 2 3 2 3 (-2),
    tm 2 3 2 4 (3),
    tm 2 3 2 5 (-1),
    tm 2 4 0 2 (-1),
    tm 2 4 0 3 (3),
    tm 2 4 0 4 (-2),
    tm 2 4 1 2 (2),
    tm 2 4 1 3 (-6),
    tm 2 4 1 4 (4),
    tm 2 4 2 2 (-1),
    tm 2 4 2 3 (3),
    tm 2 4 2 4 (-2),
    tm 2 5 0 2 (1),
    tm 2 5 0 3 (-1),
    tm 2 5 1 2 (-2),
    tm 2 5 1 3 (2),
    tm 2 5 2 2 (1),
    tm 2 5 2 3 (-1),
    tm 3 2 0 4 (3),
    tm 3 2 0 5 (-3),
    tm 3 2 1 4 (-4),
    tm 3 2 1 5 (4),
    tm 3 2 2 4 (1),
    tm 3 2 2 5 (-1),
    tm 3 3 0 3 (6),
    tm 3 3 0 4 (-9),
    tm 3 3 0 5 (3),
    tm 3 3 1 3 (-8),
    tm 3 3 1 4 (12),
    tm 3 3 1 5 (-4),
    tm 3 3 2 3 (2),
    tm 3 3 2 4 (-3),
    tm 3 3 2 5 (1),
    tm 3 4 0 2 (3),
    tm 3 4 0 3 (-9),
    tm 3 4 0 4 (6),
    tm 3 4 1 2 (-4),
    tm 3 4 1 3 (12),
    tm 3 4 1 4 (-8),
    tm 3 4 2 2 (1),
    tm 3 4 2 3 (-3),
    tm 3 4 2 4 (2),
    tm 3 5 0 2 (-3),
    tm 3 5 0 3 (3),
    tm 3 5 1 2 (4),
    tm 3 5 1 3 (-4),
    tm 3 5 2 2 (-1),
    tm 3 5 2 3 (1),
    tm 4 2 0 4 (-3),
    tm 4 2 0 5 (3),
    tm 4 2 1 4 (2),
    tm 4 2 1 5 (-2),
    tm 4 3 0 3 (-6),
    tm 4 3 0 4 (9),
    tm 4 3 0 5 (-3),
    tm 4 3 1 3 (4),
    tm 4 3 1 4 (-6),
    tm 4 3 1 5 (2),
    tm 4 4 0 2 (-3),
    tm 4 4 0 3 (9),
    tm 4 4 0 4 (-6),
    tm 4 4 1 2 (2),
    tm 4 4 1 3 (-6),
    tm 4 4 1 4 (4),
    tm 4 5 0 2 (3),
    tm 4 5 0 3 (-3),
    tm 4 5 1 2 (-2),
    tm 4 5 1 3 (2),
    tm 5 2 0 4 (1),
    tm 5 2 0 5 (-1),
    tm 5 3 0 3 (2),
    tm 5 3 0 4 (-3),
    tm 5 3 0 5 (1),
    tm 5 4 0 2 (1),
    tm 5 4 0 3 (-3),
    tm 5 4 0 4 (2),
    tm 5 5 0 2 (-1),
    tm 5 5 0 3 (1)]

/-- Column 0 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column0 : Poly :=
  [tm 2 0 4 2 (-1),
    tm 2 0 4 3 (3),
    tm 2 0 4 4 (-3),
    tm 2 0 4 5 (1),
    tm 2 0 5 2 (1),
    tm 2 0 5 3 (-3),
    tm 2 0 5 4 (3),
    tm 2 0 5 5 (-1),
    tm 2 1 4 2 (2),
    tm 2 1 4 3 (-4),
    tm 2 1 4 4 (2),
    tm 2 1 5 2 (-2),
    tm 2 1 5 3 (4),
    tm 2 1 5 4 (-2),
    tm 2 2 4 2 (-1),
    tm 2 2 4 3 (1),
    tm 2 2 5 2 (1),
    tm 2 2 5 3 (-1),
    tm 3 0 3 2 (-2),
    tm 3 0 3 3 (6),
    tm 3 0 3 4 (-6),
    tm 3 0 3 5 (2),
    tm 3 0 4 2 (3),
    tm 3 0 4 3 (-9),
    tm 3 0 4 4 (9),
    tm 3 0 4 5 (-3),
    tm 3 0 5 2 (-1),
    tm 3 0 5 3 (3),
    tm 3 0 5 4 (-3),
    tm 3 0 5 5 (1),
    tm 3 1 3 2 (4),
    tm 3 1 3 3 (-8),
    tm 3 1 3 4 (4),
    tm 3 1 4 2 (-6),
    tm 3 1 4 3 (12),
    tm 3 1 4 4 (-6),
    tm 3 1 5 2 (2),
    tm 3 1 5 3 (-4),
    tm 3 1 5 4 (2),
    tm 3 2 3 2 (-2),
    tm 3 2 3 3 (2),
    tm 3 2 4 2 (3),
    tm 3 2 4 3 (-3),
    tm 3 2 5 2 (-1),
    tm 3 2 5 3 (1),
    tm 4 0 2 2 (-1),
    tm 4 0 2 3 (3),
    tm 4 0 2 4 (-3),
    tm 4 0 2 5 (1),
    tm 4 0 3 2 (3),
    tm 4 0 3 3 (-9),
    tm 4 0 3 4 (9),
    tm 4 0 3 5 (-3),
    tm 4 0 4 2 (-2),
    tm 4 0 4 3 (6),
    tm 4 0 4 4 (-6),
    tm 4 0 4 5 (2),
    tm 4 1 2 2 (2),
    tm 4 1 2 3 (-4),
    tm 4 1 2 4 (2),
    tm 4 1 3 2 (-6),
    tm 4 1 3 3 (12),
    tm 4 1 3 4 (-6),
    tm 4 1 4 2 (4),
    tm 4 1 4 3 (-8),
    tm 4 1 4 4 (4),
    tm 4 2 2 2 (-1),
    tm 4 2 2 3 (1),
    tm 4 2 3 2 (3),
    tm 4 2 3 3 (-3),
    tm 4 2 4 2 (-2),
    tm 4 2 4 3 (2),
    tm 5 0 2 2 (1),
    tm 5 0 2 3 (-3),
    tm 5 0 2 4 (3),
    tm 5 0 2 5 (-1),
    tm 5 0 3 2 (-1),
    tm 5 0 3 3 (3),
    tm 5 0 3 4 (-3),
    tm 5 0 3 5 (1),
    tm 5 1 2 2 (-2),
    tm 5 1 2 3 (4),
    tm 5 1 2 4 (-2),
    tm 5 1 3 2 (2),
    tm 5 1 3 3 (-4),
    tm 5 1 3 4 (2),
    tm 5 2 2 2 (1),
    tm 5 2 2 3 (-1),
    tm 5 2 3 2 (-1),
    tm 5 2 3 3 (1)]

/-- Column 0 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column0 : Poly :=
  [tm 0 2 2 4 (-1),
    tm 0 2 2 5 (1),
    tm 0 2 3 4 (3),
    tm 0 2 3 5 (-3),
    tm 0 2 4 4 (-3),
    tm 0 2 4 5 (3),
    tm 0 2 5 4 (1),
    tm 0 2 5 5 (-1),
    tm 0 3 2 3 (-2),
    tm 0 3 2 4 (3),
    tm 0 3 2 5 (-1),
    tm 0 3 3 3 (6),
    tm 0 3 3 4 (-9),
    tm 0 3 3 5 (3),
    tm 0 3 4 3 (-6),
    tm 0 3 4 4 (9),
    tm 0 3 4 5 (-3),
    tm 0 3 5 3 (2),
    tm 0 3 5 4 (-3),
    tm 0 3 5 5 (1),
    tm 0 4 2 2 (-1),
    tm 0 4 2 3 (3),
    tm 0 4 2 4 (-2),
    tm 0 4 3 2 (3),
    tm 0 4 3 3 (-9),
    tm 0 4 3 4 (6),
    tm 0 4 4 2 (-3),
    tm 0 4 4 3 (9),
    tm 0 4 4 4 (-6),
    tm 0 4 5 2 (1),
    tm 0 4 5 3 (-3),
    tm 0 4 5 4 (2),
    tm 0 5 2 2 (1),
    tm 0 5 2 3 (-1),
    tm 0 5 3 2 (-3),
    tm 0 5 3 3 (3),
    tm 0 5 4 2 (3),
    tm 0 5 4 3 (-3),
    tm 0 5 5 2 (-1),
    tm 0 5 5 3 (1),
    tm 1 2 2 4 (2),
    tm 1 2 2 5 (-2),
    tm 1 2 3 4 (-4),
    tm 1 2 3 5 (4),
    tm 1 2 4 4 (2),
    tm 1 2 4 5 (-2),
    tm 1 3 2 3 (4),
    tm 1 3 2 4 (-6),
    tm 1 3 2 5 (2),
    tm 1 3 3 3 (-8),
    tm 1 3 3 4 (12),
    tm 1 3 3 5 (-4),
    tm 1 3 4 3 (4),
    tm 1 3 4 4 (-6),
    tm 1 3 4 5 (2),
    tm 1 4 2 2 (2),
    tm 1 4 2 3 (-6),
    tm 1 4 2 4 (4),
    tm 1 4 3 2 (-4),
    tm 1 4 3 3 (12),
    tm 1 4 3 4 (-8),
    tm 1 4 4 2 (2),
    tm 1 4 4 3 (-6),
    tm 1 4 4 4 (4),
    tm 1 5 2 2 (-2),
    tm 1 5 2 3 (2),
    tm 1 5 3 2 (4),
    tm 1 5 3 3 (-4),
    tm 1 5 4 2 (-2),
    tm 1 5 4 3 (2),
    tm 2 2 2 4 (-1),
    tm 2 2 2 5 (1),
    tm 2 2 3 4 (1),
    tm 2 2 3 5 (-1),
    tm 2 3 2 3 (-2),
    tm 2 3 2 4 (3),
    tm 2 3 2 5 (-1),
    tm 2 3 3 3 (2),
    tm 2 3 3 4 (-3),
    tm 2 3 3 5 (1),
    tm 2 4 2 2 (-1),
    tm 2 4 2 3 (3),
    tm 2 4 2 4 (-2),
    tm 2 4 3 2 (1),
    tm 2 4 3 3 (-3),
    tm 2 4 3 4 (2),
    tm 2 5 2 2 (1),
    tm 2 5 2 3 (-1),
    tm 2 5 3 2 (-1),
    tm 2 5 3 3 (1)]

/-- Column 1 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column1 : Poly :=
  [tm 3 2 2 0 (1),
    tm 3 2 2 1 (-2),
    tm 3 2 2 2 (1),
    tm 3 2 3 0 (-1),
    tm 3 2 3 1 (2),
    tm 3 2 3 2 (-1),
    tm 3 3 2 0 (-3),
    tm 3 3 2 1 (4),
    tm 3 3 2 2 (-1),
    tm 3 3 3 0 (3),
    tm 3 3 3 1 (-4),
    tm 3 3 3 2 (1),
    tm 3 4 2 0 (3),
    tm 3 4 2 1 (-2),
    tm 3 4 3 0 (-3),
    tm 3 4 3 1 (2),
    tm 3 5 2 0 (-1),
    tm 3 5 3 0 (1),
    tm 4 2 2 0 (-2),
    tm 4 2 2 1 (4),
    tm 4 2 2 2 (-2),
    tm 4 2 3 0 (2),
    tm 4 2 3 1 (-4),
    tm 4 2 3 2 (2),
    tm 4 3 2 0 (6),
    tm 4 3 2 1 (-8),
    tm 4 3 2 2 (2),
    tm 4 3 3 0 (-6),
    tm 4 3 3 1 (8),
    tm 4 3 3 2 (-2),
    tm 4 4 2 0 (-6),
    tm 4 4 2 1 (4),
    tm 4 4 3 0 (6),
    tm 4 4 3 1 (-4),
    tm 4 5 2 0 (2),
    tm 4 5 3 0 (-2),
    tm 5 2 2 0 (1),
    tm 5 2 2 1 (-2),
    tm 5 2 2 2 (1),
    tm 5 2 3 0 (-1),
    tm 5 2 3 1 (2),
    tm 5 2 3 2 (-1),
    tm 5 3 2 0 (-3),
    tm 5 3 2 1 (4),
    tm 5 3 2 2 (-1),
    tm 5 3 3 0 (3),
    tm 5 3 3 1 (-4),
    tm 5 3 3 2 (1),
    tm 5 4 2 0 (3),
    tm 5 4 2 1 (-2),
    tm 5 4 3 0 (-3),
    tm 5 4 3 1 (2),
    tm 5 5 2 0 (-1),
    tm 5 5 3 0 (1)]

/-- Column 1 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column1 : Poly :=
  [tm 3 2 0 4 (1),
    tm 3 2 0 5 (-1),
    tm 3 3 0 3 (2),
    tm 3 3 0 4 (-3),
    tm 3 3 0 5 (1),
    tm 3 4 0 2 (1),
    tm 3 4 0 3 (-3),
    tm 3 4 0 4 (2),
    tm 3 5 0 2 (-1),
    tm 3 5 0 3 (1),
    tm 4 2 0 4 (-2),
    tm 4 2 0 5 (2),
    tm 4 3 0 3 (-4),
    tm 4 3 0 4 (6),
    tm 4 3 0 5 (-2),
    tm 4 4 0 2 (-2),
    tm 4 4 0 3 (6),
    tm 4 4 0 4 (-4),
    tm 4 5 0 2 (2),
    tm 4 5 0 3 (-2),
    tm 5 2 0 4 (1),
    tm 5 2 0 5 (-1),
    tm 5 3 0 3 (2),
    tm 5 3 0 4 (-3),
    tm 5 3 0 5 (1),
    tm 5 4 0 2 (1),
    tm 5 4 0 3 (-3),
    tm 5 4 0 4 (2),
    tm 5 5 0 2 (-1),
    tm 5 5 0 3 (1)]

/-- Column 1 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column1 : Poly :=
  [tm 3 0 2 2 (1),
    tm 3 0 2 3 (-3),
    tm 3 0 2 4 (3),
    tm 3 0 2 5 (-1),
    tm 3 0 3 2 (-1),
    tm 3 0 3 3 (3),
    tm 3 0 3 4 (-3),
    tm 3 0 3 5 (1),
    tm 3 1 2 2 (-2),
    tm 3 1 2 3 (4),
    tm 3 1 2 4 (-2),
    tm 3 1 3 2 (2),
    tm 3 1 3 3 (-4),
    tm 3 1 3 4 (2),
    tm 3 2 2 2 (1),
    tm 3 2 2 3 (-1),
    tm 3 2 3 2 (-1),
    tm 3 2 3 3 (1),
    tm 4 0 2 2 (-2),
    tm 4 0 2 3 (6),
    tm 4 0 2 4 (-6),
    tm 4 0 2 5 (2),
    tm 4 0 3 2 (2),
    tm 4 0 3 3 (-6),
    tm 4 0 3 4 (6),
    tm 4 0 3 5 (-2),
    tm 4 1 2 2 (4),
    tm 4 1 2 3 (-8),
    tm 4 1 2 4 (4),
    tm 4 1 3 2 (-4),
    tm 4 1 3 3 (8),
    tm 4 1 3 4 (-4),
    tm 4 2 2 2 (-2),
    tm 4 2 2 3 (2),
    tm 4 2 3 2 (2),
    tm 4 2 3 3 (-2),
    tm 5 0 2 2 (1),
    tm 5 0 2 3 (-3),
    tm 5 0 2 4 (3),
    tm 5 0 2 5 (-1),
    tm 5 0 3 2 (-1),
    tm 5 0 3 3 (3),
    tm 5 0 3 4 (-3),
    tm 5 0 3 5 (1),
    tm 5 1 2 2 (-2),
    tm 5 1 2 3 (4),
    tm 5 1 2 4 (-2),
    tm 5 1 3 2 (2),
    tm 5 1 3 3 (-4),
    tm 5 1 3 4 (2),
    tm 5 2 2 2 (1),
    tm 5 2 2 3 (-1),
    tm 5 2 3 2 (-1),
    tm 5 2 3 3 (1)]

/-- Column 1 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column1 : Poly :=
  [tm 0 2 2 4 (-1),
    tm 0 2 2 5 (1),
    tm 0 2 3 4 (1),
    tm 0 2 3 5 (-1),
    tm 0 3 2 3 (-2),
    tm 0 3 2 4 (3),
    tm 0 3 2 5 (-1),
    tm 0 3 3 3 (2),
    tm 0 3 3 4 (-3),
    tm 0 3 3 5 (1),
    tm 0 4 2 2 (-1),
    tm 0 4 2 3 (3),
    tm 0 4 2 4 (-2),
    tm 0 4 3 2 (1),
    tm 0 4 3 3 (-3),
    tm 0 4 3 4 (2),
    tm 0 5 2 2 (1),
    tm 0 5 2 3 (-1),
    tm 0 5 3 2 (-1),
    tm 0 5 3 3 (1),
    tm 1 2 2 4 (2),
    tm 1 2 2 5 (-2),
    tm 1 2 3 4 (-2),
    tm 1 2 3 5 (2),
    tm 1 3 2 3 (4),
    tm 1 3 2 4 (-6),
    tm 1 3 2 5 (2),
    tm 1 3 3 3 (-4),
    tm 1 3 3 4 (6),
    tm 1 3 3 5 (-2),
    tm 1 4 2 2 (2),
    tm 1 4 2 3 (-6),
    tm 1 4 2 4 (4),
    tm 1 4 3 2 (-2),
    tm 1 4 3 3 (6),
    tm 1 4 3 4 (-4),
    tm 1 5 2 2 (-2),
    tm 1 5 2 3 (2),
    tm 1 5 3 2 (2),
    tm 1 5 3 3 (-2),
    tm 2 2 2 4 (-1),
    tm 2 2 2 5 (1),
    tm 2 2 3 4 (1),
    tm 2 2 3 5 (-1),
    tm 2 3 2 3 (-2),
    tm 2 3 2 4 (3),
    tm 2 3 2 5 (-1),
    tm 2 3 3 3 (2),
    tm 2 3 3 4 (-3),
    tm 2 3 3 5 (1),
    tm 2 4 2 2 (-1),
    tm 2 4 2 3 (3),
    tm 2 4 2 4 (-2),
    tm 2 4 3 2 (1),
    tm 2 4 3 3 (-3),
    tm 2 4 3 4 (2),
    tm 2 5 2 2 (1),
    tm 2 5 2 3 (-1),
    tm 2 5 3 2 (-1),
    tm 2 5 3 3 (1)]

/-- Column 2 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column2 : Poly :=
  [tm 2 3 4 0 (1),
    tm 2 3 5 0 (-1),
    tm 2 4 4 0 (-2),
    tm 2 4 5 0 (2),
    tm 2 5 4 0 (1),
    tm 2 5 5 0 (-1),
    tm 3 3 3 0 (2),
    tm 3 3 4 0 (-3),
    tm 3 3 5 0 (1),
    tm 3 4 3 0 (-4),
    tm 3 4 4 0 (6),
    tm 3 4 5 0 (-2),
    tm 3 5 3 0 (2),
    tm 3 5 4 0 (-3),
    tm 3 5 5 0 (1),
    tm 4 3 2 0 (1),
    tm 4 3 3 0 (-3),
    tm 4 3 4 0 (2),
    tm 4 4 2 0 (-2),
    tm 4 4 3 0 (6),
    tm 4 4 4 0 (-4),
    tm 4 5 2 0 (1),
    tm 4 5 3 0 (-3),
    tm 4 5 4 0 (2),
    tm 5 3 2 0 (-1),
    tm 5 3 3 0 (1),
    tm 5 4 2 0 (2),
    tm 5 4 3 0 (-2),
    tm 5 5 2 0 (-1),
    tm 5 5 3 0 (1)]

/-- Column 2 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column2 : Poly :=
  [tm 2 3 0 2 (1),
    tm 2 3 0 3 (-1),
    tm 2 3 1 2 (-2),
    tm 2 3 1 3 (2),
    tm 2 3 2 2 (1),
    tm 2 3 2 3 (-1),
    tm 2 4 0 2 (-2),
    tm 2 4 0 3 (2),
    tm 2 4 1 2 (4),
    tm 2 4 1 3 (-4),
    tm 2 4 2 2 (-2),
    tm 2 4 2 3 (2),
    tm 2 5 0 2 (1),
    tm 2 5 0 3 (-1),
    tm 2 5 1 2 (-2),
    tm 2 5 1 3 (2),
    tm 2 5 2 2 (1),
    tm 2 5 2 3 (-1),
    tm 3 3 0 2 (-3),
    tm 3 3 0 3 (3),
    tm 3 3 1 2 (4),
    tm 3 3 1 3 (-4),
    tm 3 3 2 2 (-1),
    tm 3 3 2 3 (1),
    tm 3 4 0 2 (6),
    tm 3 4 0 3 (-6),
    tm 3 4 1 2 (-8),
    tm 3 4 1 3 (8),
    tm 3 4 2 2 (2),
    tm 3 4 2 3 (-2),
    tm 3 5 0 2 (-3),
    tm 3 5 0 3 (3),
    tm 3 5 1 2 (4),
    tm 3 5 1 3 (-4),
    tm 3 5 2 2 (-1),
    tm 3 5 2 3 (1),
    tm 4 3 0 2 (3),
    tm 4 3 0 3 (-3),
    tm 4 3 1 2 (-2),
    tm 4 3 1 3 (2),
    tm 4 4 0 2 (-6),
    tm 4 4 0 3 (6),
    tm 4 4 1 2 (4),
    tm 4 4 1 3 (-4),
    tm 4 5 0 2 (3),
    tm 4 5 0 3 (-3),
    tm 4 5 1 2 (-2),
    tm 4 5 1 3 (2),
    tm 5 3 0 2 (-1),
    tm 5 3 0 3 (1),
    tm 5 4 0 2 (2),
    tm 5 4 0 3 (-2),
    tm 5 5 0 2 (-1),
    tm 5 5 0 3 (1)]

/-- Column 2 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column2 : Poly :=
  [tm 2 0 4 2 (-1),
    tm 2 0 4 3 (1),
    tm 2 0 5 2 (1),
    tm 2 0 5 3 (-1),
    tm 2 1 4 2 (2),
    tm 2 1 4 3 (-2),
    tm 2 1 5 2 (-2),
    tm 2 1 5 3 (2),
    tm 2 2 4 2 (-1),
    tm 2 2 4 3 (1),
    tm 2 2 5 2 (1),
    tm 2 2 5 3 (-1),
    tm 3 0 3 2 (-2),
    tm 3 0 3 3 (2),
    tm 3 0 4 2 (3),
    tm 3 0 4 3 (-3),
    tm 3 0 5 2 (-1),
    tm 3 0 5 3 (1),
    tm 3 1 3 2 (4),
    tm 3 1 3 3 (-4),
    tm 3 1 4 2 (-6),
    tm 3 1 4 3 (6),
    tm 3 1 5 2 (2),
    tm 3 1 5 3 (-2),
    tm 3 2 3 2 (-2),
    tm 3 2 3 3 (2),
    tm 3 2 4 2 (3),
    tm 3 2 4 3 (-3),
    tm 3 2 5 2 (-1),
    tm 3 2 5 3 (1),
    tm 4 0 2 2 (-1),
    tm 4 0 2 3 (1),
    tm 4 0 3 2 (3),
    tm 4 0 3 3 (-3),
    tm 4 0 4 2 (-2),
    tm 4 0 4 3 (2),
    tm 4 1 2 2 (2),
    tm 4 1 2 3 (-2),
    tm 4 1 3 2 (-6),
    tm 4 1 3 3 (6),
    tm 4 1 4 2 (4),
    tm 4 1 4 3 (-4),
    tm 4 2 2 2 (-1),
    tm 4 2 2 3 (1),
    tm 4 2 3 2 (3),
    tm 4 2 3 3 (-3),
    tm 4 2 4 2 (-2),
    tm 4 2 4 3 (2),
    tm 5 0 2 2 (1),
    tm 5 0 2 3 (-1),
    tm 5 0 3 2 (-1),
    tm 5 0 3 3 (1),
    tm 5 1 2 2 (-2),
    tm 5 1 2 3 (2),
    tm 5 1 3 2 (2),
    tm 5 1 3 3 (-2),
    tm 5 2 2 2 (1),
    tm 5 2 2 3 (-1),
    tm 5 2 3 2 (-1),
    tm 5 2 3 3 (1)]

/-- Column 2 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column2 : Poly :=
  [tm 0 3 2 2 (1),
    tm 0 3 2 3 (-1),
    tm 0 3 3 2 (-3),
    tm 0 3 3 3 (3),
    tm 0 3 4 2 (3),
    tm 0 3 4 3 (-3),
    tm 0 3 5 2 (-1),
    tm 0 3 5 3 (1),
    tm 0 4 2 2 (-2),
    tm 0 4 2 3 (2),
    tm 0 4 3 2 (6),
    tm 0 4 3 3 (-6),
    tm 0 4 4 2 (-6),
    tm 0 4 4 3 (6),
    tm 0 4 5 2 (2),
    tm 0 4 5 3 (-2),
    tm 0 5 2 2 (1),
    tm 0 5 2 3 (-1),
    tm 0 5 3 2 (-3),
    tm 0 5 3 3 (3),
    tm 0 5 4 2 (3),
    tm 0 5 4 3 (-3),
    tm 0 5 5 2 (-1),
    tm 0 5 5 3 (1),
    tm 1 3 2 2 (-2),
    tm 1 3 2 3 (2),
    tm 1 3 3 2 (4),
    tm 1 3 3 3 (-4),
    tm 1 3 4 2 (-2),
    tm 1 3 4 3 (2),
    tm 1 4 2 2 (4),
    tm 1 4 2 3 (-4),
    tm 1 4 3 2 (-8),
    tm 1 4 3 3 (8),
    tm 1 4 4 2 (4),
    tm 1 4 4 3 (-4),
    tm 1 5 2 2 (-2),
    tm 1 5 2 3 (2),
    tm 1 5 3 2 (4),
    tm 1 5 3 3 (-4),
    tm 1 5 4 2 (-2),
    tm 1 5 4 3 (2),
    tm 2 3 2 2 (1),
    tm 2 3 2 3 (-1),
    tm 2 3 3 2 (-1),
    tm 2 3 3 3 (1),
    tm 2 4 2 2 (-2),
    tm 2 4 2 3 (2),
    tm 2 4 3 2 (2),
    tm 2 4 3 3 (-2),
    tm 2 5 2 2 (1),
    tm 2 5 2 3 (-1),
    tm 2 5 3 2 (-1),
    tm 2 5 3 3 (1)]

/-- Column 3 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column3 : Poly :=
  [tm 2 2 3 0 (1),
    tm 2 2 3 1 (-2),
    tm 2 2 3 2 (1),
    tm 2 2 4 0 (-2),
    tm 2 2 4 1 (4),
    tm 2 2 4 2 (-2),
    tm 2 2 5 0 (1),
    tm 2 2 5 1 (-2),
    tm 2 2 5 2 (1),
    tm 2 3 3 0 (-3),
    tm 2 3 3 1 (4),
    tm 2 3 3 2 (-1),
    tm 2 3 4 0 (6),
    tm 2 3 4 1 (-8),
    tm 2 3 4 2 (2),
    tm 2 3 5 0 (-3),
    tm 2 3 5 1 (4),
    tm 2 3 5 2 (-1),
    tm 2 4 3 0 (3),
    tm 2 4 3 1 (-2),
    tm 2 4 4 0 (-6),
    tm 2 4 4 1 (4),
    tm 2 4 5 0 (3),
    tm 2 4 5 1 (-2),
    tm 2 5 3 0 (-1),
    tm 2 5 4 0 (2),
    tm 2 5 5 0 (-1),
    tm 3 2 3 0 (-1),
    tm 3 2 3 1 (2),
    tm 3 2 3 2 (-1),
    tm 3 2 4 0 (2),
    tm 3 2 4 1 (-4),
    tm 3 2 4 2 (2),
    tm 3 2 5 0 (-1),
    tm 3 2 5 1 (2),
    tm 3 2 5 2 (-1),
    tm 3 3 3 0 (3),
    tm 3 3 3 1 (-4),
    tm 3 3 3 2 (1),
    tm 3 3 4 0 (-6),
    tm 3 3 4 1 (8),
    tm 3 3 4 2 (-2),
    tm 3 3 5 0 (3),
    tm 3 3 5 1 (-4),
    tm 3 3 5 2 (1),
    tm 3 4 3 0 (-3),
    tm 3 4 3 1 (2),
    tm 3 4 4 0 (6),
    tm 3 4 4 1 (-4),
    tm 3 4 5 0 (-3),
    tm 3 4 5 1 (2),
    tm 3 5 3 0 (1),
    tm 3 5 4 0 (-2),
    tm 3 5 5 0 (1)]

/-- Column 3 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column3 : Poly :=
  [tm 2 2 0 4 (-1),
    tm 2 2 0 5 (1),
    tm 2 2 1 4 (2),
    tm 2 2 1 5 (-2),
    tm 2 2 2 4 (-1),
    tm 2 2 2 5 (1),
    tm 2 3 0 3 (-2),
    tm 2 3 0 4 (3),
    tm 2 3 0 5 (-1),
    tm 2 3 1 3 (4),
    tm 2 3 1 4 (-6),
    tm 2 3 1 5 (2),
    tm 2 3 2 3 (-2),
    tm 2 3 2 4 (3),
    tm 2 3 2 5 (-1),
    tm 2 4 0 2 (-1),
    tm 2 4 0 3 (3),
    tm 2 4 0 4 (-2),
    tm 2 4 1 2 (2),
    tm 2 4 1 3 (-6),
    tm 2 4 1 4 (4),
    tm 2 4 2 2 (-1),
    tm 2 4 2 3 (3),
    tm 2 4 2 4 (-2),
    tm 2 5 0 2 (1),
    tm 2 5 0 3 (-1),
    tm 2 5 1 2 (-2),
    tm 2 5 1 3 (2),
    tm 2 5 2 2 (1),
    tm 2 5 2 3 (-1),
    tm 3 2 0 4 (1),
    tm 3 2 0 5 (-1),
    tm 3 2 1 4 (-2),
    tm 3 2 1 5 (2),
    tm 3 2 2 4 (1),
    tm 3 2 2 5 (-1),
    tm 3 3 0 3 (2),
    tm 3 3 0 4 (-3),
    tm 3 3 0 5 (1),
    tm 3 3 1 3 (-4),
    tm 3 3 1 4 (6),
    tm 3 3 1 5 (-2),
    tm 3 3 2 3 (2),
    tm 3 3 2 4 (-3),
    tm 3 3 2 5 (1),
    tm 3 4 0 2 (1),
    tm 3 4 0 3 (-3),
    tm 3 4 0 4 (2),
    tm 3 4 1 2 (-2),
    tm 3 4 1 3 (6),
    tm 3 4 1 4 (-4),
    tm 3 4 2 2 (1),
    tm 3 4 2 3 (-3),
    tm 3 4 2 4 (2),
    tm 3 5 0 2 (-1),
    tm 3 5 0 3 (1),
    tm 3 5 1 2 (2),
    tm 3 5 1 3 (-2),
    tm 3 5 2 2 (-1),
    tm 3 5 2 3 (1)]

/-- Column 3 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column3 : Poly :=
  [tm 2 0 3 2 (1),
    tm 2 0 3 3 (-3),
    tm 2 0 3 4 (3),
    tm 2 0 3 5 (-1),
    tm 2 0 4 2 (-2),
    tm 2 0 4 3 (6),
    tm 2 0 4 4 (-6),
    tm 2 0 4 5 (2),
    tm 2 0 5 2 (1),
    tm 2 0 5 3 (-3),
    tm 2 0 5 4 (3),
    tm 2 0 5 5 (-1),
    tm 2 1 3 2 (-2),
    tm 2 1 3 3 (4),
    tm 2 1 3 4 (-2),
    tm 2 1 4 2 (4),
    tm 2 1 4 3 (-8),
    tm 2 1 4 4 (4),
    tm 2 1 5 2 (-2),
    tm 2 1 5 3 (4),
    tm 2 1 5 4 (-2),
    tm 2 2 3 2 (1),
    tm 2 2 3 3 (-1),
    tm 2 2 4 2 (-2),
    tm 2 2 4 3 (2),
    tm 2 2 5 2 (1),
    tm 2 2 5 3 (-1),
    tm 3 0 3 2 (-1),
    tm 3 0 3 3 (3),
    tm 3 0 3 4 (-3),
    tm 3 0 3 5 (1),
    tm 3 0 4 2 (2),
    tm 3 0 4 3 (-6),
    tm 3 0 4 4 (6),
    tm 3 0 4 5 (-2),
    tm 3 0 5 2 (-1),
    tm 3 0 5 3 (3),
    tm 3 0 5 4 (-3),
    tm 3 0 5 5 (1),
    tm 3 1 3 2 (2),
    tm 3 1 3 3 (-4),
    tm 3 1 3 4 (2),
    tm 3 1 4 2 (-4),
    tm 3 1 4 3 (8),
    tm 3 1 4 4 (-4),
    tm 3 1 5 2 (2),
    tm 3 1 5 3 (-4),
    tm 3 1 5 4 (2),
    tm 3 2 3 2 (-1),
    tm 3 2 3 3 (1),
    tm 3 2 4 2 (2),
    tm 3 2 4 3 (-2),
    tm 3 2 5 2 (-1),
    tm 3 2 5 3 (1)]

/-- Column 3 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column3 : Poly :=
  [tm 0 2 3 4 (1),
    tm 0 2 3 5 (-1),
    tm 0 2 4 4 (-2),
    tm 0 2 4 5 (2),
    tm 0 2 5 4 (1),
    tm 0 2 5 5 (-1),
    tm 0 3 3 3 (2),
    tm 0 3 3 4 (-3),
    tm 0 3 3 5 (1),
    tm 0 3 4 3 (-4),
    tm 0 3 4 4 (6),
    tm 0 3 4 5 (-2),
    tm 0 3 5 3 (2),
    tm 0 3 5 4 (-3),
    tm 0 3 5 5 (1),
    tm 0 4 3 2 (1),
    tm 0 4 3 3 (-3),
    tm 0 4 3 4 (2),
    tm 0 4 4 2 (-2),
    tm 0 4 4 3 (6),
    tm 0 4 4 4 (-4),
    tm 0 4 5 2 (1),
    tm 0 4 5 3 (-3),
    tm 0 4 5 4 (2),
    tm 0 5 3 2 (-1),
    tm 0 5 3 3 (1),
    tm 0 5 4 2 (2),
    tm 0 5 4 3 (-2),
    tm 0 5 5 2 (-1),
    tm 0 5 5 3 (1)]

/-- Column 4 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column4 : Poly :=
  [tm 2 2 4 0 (-1),
    tm 2 2 4 1 (2),
    tm 2 2 4 2 (-1),
    tm 2 2 5 0 (1),
    tm 2 2 5 1 (-2),
    tm 2 2 5 2 (1),
    tm 2 3 4 0 (1),
    tm 2 3 4 1 (-2),
    tm 2 3 4 2 (1),
    tm 2 3 5 0 (-1),
    tm 2 3 5 1 (2),
    tm 2 3 5 2 (-1),
    tm 3 2 3 0 (-2),
    tm 3 2 3 1 (4),
    tm 3 2 3 2 (-2),
    tm 3 2 4 0 (3),
    tm 3 2 4 1 (-6),
    tm 3 2 4 2 (3),
    tm 3 2 5 0 (-1),
    tm 3 2 5 1 (2),
    tm 3 2 5 2 (-1),
    tm 3 3 3 0 (2),
    tm 3 3 3 1 (-4),
    tm 3 3 3 2 (2),
    tm 3 3 4 0 (-3),
    tm 3 3 4 1 (6),
    tm 3 3 4 2 (-3),
    tm 3 3 5 0 (1),
    tm 3 3 5 1 (-2),
    tm 3 3 5 2 (1),
    tm 4 2 2 0 (-1),
    tm 4 2 2 1 (2),
    tm 4 2 2 2 (-1),
    tm 4 2 3 0 (3),
    tm 4 2 3 1 (-6),
    tm 4 2 3 2 (3),
    tm 4 2 4 0 (-2),
    tm 4 2 4 1 (4),
    tm 4 2 4 2 (-2),
    tm 4 3 2 0 (1),
    tm 4 3 2 1 (-2),
    tm 4 3 2 2 (1),
    tm 4 3 3 0 (-3),
    tm 4 3 3 1 (6),
    tm 4 3 3 2 (-3),
    tm 4 3 4 0 (2),
    tm 4 3 4 1 (-4),
    tm 4 3 4 2 (2),
    tm 5 2 2 0 (1),
    tm 5 2 2 1 (-2),
    tm 5 2 2 2 (1),
    tm 5 2 3 0 (-1),
    tm 5 2 3 1 (2),
    tm 5 2 3 2 (-1),
    tm 5 3 2 0 (-1),
    tm 5 3 2 1 (2),
    tm 5 3 2 2 (-1),
    tm 5 3 3 0 (1),
    tm 5 3 3 1 (-2),
    tm 5 3 3 2 (1)]

/-- Column 4 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column4 : Poly :=
  [tm 2 2 0 3 (1),
    tm 2 2 0 4 (-2),
    tm 2 2 0 5 (1),
    tm 2 2 1 3 (-2),
    tm 2 2 1 4 (4),
    tm 2 2 1 5 (-2),
    tm 2 2 2 3 (1),
    tm 2 2 2 4 (-2),
    tm 2 2 2 5 (1),
    tm 2 3 0 3 (-1),
    tm 2 3 0 4 (2),
    tm 2 3 0 5 (-1),
    tm 2 3 1 3 (2),
    tm 2 3 1 4 (-4),
    tm 2 3 1 5 (2),
    tm 2 3 2 3 (-1),
    tm 2 3 2 4 (2),
    tm 2 3 2 5 (-1),
    tm 3 2 0 3 (-3),
    tm 3 2 0 4 (6),
    tm 3 2 0 5 (-3),
    tm 3 2 1 3 (4),
    tm 3 2 1 4 (-8),
    tm 3 2 1 5 (4),
    tm 3 2 2 3 (-1),
    tm 3 2 2 4 (2),
    tm 3 2 2 5 (-1),
    tm 3 3 0 3 (3),
    tm 3 3 0 4 (-6),
    tm 3 3 0 5 (3),
    tm 3 3 1 3 (-4),
    tm 3 3 1 4 (8),
    tm 3 3 1 5 (-4),
    tm 3 3 2 3 (1),
    tm 3 3 2 4 (-2),
    tm 3 3 2 5 (1),
    tm 4 2 0 3 (3),
    tm 4 2 0 4 (-6),
    tm 4 2 0 5 (3),
    tm 4 2 1 3 (-2),
    tm 4 2 1 4 (4),
    tm 4 2 1 5 (-2),
    tm 4 3 0 3 (-3),
    tm 4 3 0 4 (6),
    tm 4 3 0 5 (-3),
    tm 4 3 1 3 (2),
    tm 4 3 1 4 (-4),
    tm 4 3 1 5 (2),
    tm 5 2 0 3 (-1),
    tm 5 2 0 4 (2),
    tm 5 2 0 5 (-1),
    tm 5 3 0 3 (1),
    tm 5 3 0 4 (-2),
    tm 5 3 0 5 (1)]

/-- Column 4 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column4 : Poly :=
  [tm 2 0 4 3 (1),
    tm 2 0 4 4 (-2),
    tm 2 0 4 5 (1),
    tm 2 0 5 3 (-1),
    tm 2 0 5 4 (2),
    tm 2 0 5 5 (-1),
    tm 3 0 3 3 (2),
    tm 3 0 3 4 (-4),
    tm 3 0 3 5 (2),
    tm 3 0 4 3 (-3),
    tm 3 0 4 4 (6),
    tm 3 0 4 5 (-3),
    tm 3 0 5 3 (1),
    tm 3 0 5 4 (-2),
    tm 3 0 5 5 (1),
    tm 4 0 2 3 (1),
    tm 4 0 2 4 (-2),
    tm 4 0 2 5 (1),
    tm 4 0 3 3 (-3),
    tm 4 0 3 4 (6),
    tm 4 0 3 5 (-3),
    tm 4 0 4 3 (2),
    tm 4 0 4 4 (-4),
    tm 4 0 4 5 (2),
    tm 5 0 2 3 (-1),
    tm 5 0 2 4 (2),
    tm 5 0 2 5 (-1),
    tm 5 0 3 3 (1),
    tm 5 0 3 4 (-2),
    tm 5 0 3 5 (1)]

/-- Column 4 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column4 : Poly :=
  [tm 0 2 2 3 (1),
    tm 0 2 2 4 (-2),
    tm 0 2 2 5 (1),
    tm 0 2 3 3 (-3),
    tm 0 2 3 4 (6),
    tm 0 2 3 5 (-3),
    tm 0 2 4 3 (3),
    tm 0 2 4 4 (-6),
    tm 0 2 4 5 (3),
    tm 0 2 5 3 (-1),
    tm 0 2 5 4 (2),
    tm 0 2 5 5 (-1),
    tm 0 3 2 3 (-1),
    tm 0 3 2 4 (2),
    tm 0 3 2 5 (-1),
    tm 0 3 3 3 (3),
    tm 0 3 3 4 (-6),
    tm 0 3 3 5 (3),
    tm 0 3 4 3 (-3),
    tm 0 3 4 4 (6),
    tm 0 3 4 5 (-3),
    tm 0 3 5 3 (1),
    tm 0 3 5 4 (-2),
    tm 0 3 5 5 (1),
    tm 1 2 2 3 (-2),
    tm 1 2 2 4 (4),
    tm 1 2 2 5 (-2),
    tm 1 2 3 3 (4),
    tm 1 2 3 4 (-8),
    tm 1 2 3 5 (4),
    tm 1 2 4 3 (-2),
    tm 1 2 4 4 (4),
    tm 1 2 4 5 (-2),
    tm 1 3 2 3 (2),
    tm 1 3 2 4 (-4),
    tm 1 3 2 5 (2),
    tm 1 3 3 3 (-4),
    tm 1 3 3 4 (8),
    tm 1 3 3 5 (-4),
    tm 1 3 4 3 (2),
    tm 1 3 4 4 (-4),
    tm 1 3 4 5 (2),
    tm 2 2 2 3 (1),
    tm 2 2 2 4 (-2),
    tm 2 2 2 5 (1),
    tm 2 2 3 3 (-1),
    tm 2 2 3 4 (2),
    tm 2 2 3 5 (-1),
    tm 2 3 2 3 (-1),
    tm 2 3 2 4 (2),
    tm 2 3 2 5 (-1),
    tm 2 3 3 3 (1),
    tm 2 3 3 4 (-2),
    tm 2 3 3 5 (1)]

/-- Column 5 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column5 : Poly := []

/-- Column 5 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column5 : Poly :=
  [tm 2 2 0 3 (10),
    tm 2 2 0 4 (-10),
    tm 2 2 1 3 (-20),
    tm 2 2 1 4 (20),
    tm 2 2 2 3 (10),
    tm 2 2 2 4 (-10),
    tm 2 3 0 2 (10),
    tm 2 3 0 3 (-30),
    tm 2 3 0 4 (10),
    tm 2 3 1 2 (-20),
    tm 2 3 1 3 (60),
    tm 2 3 1 4 (-20),
    tm 2 3 2 2 (10),
    tm 2 3 2 3 (-30),
    tm 2 3 2 4 (10),
    tm 2 4 0 2 (-20),
    tm 2 4 0 3 (20),
    tm 2 4 1 2 (40),
    tm 2 4 1 3 (-40),
    tm 2 4 2 2 (-20),
    tm 2 4 2 3 (20),
    tm 2 5 0 2 (10),
    tm 2 5 1 2 (-20),
    tm 2 5 2 2 (10),
    tm 3 2 0 3 (-30),
    tm 3 2 0 4 (30),
    tm 3 2 1 3 (40),
    tm 3 2 1 4 (-40),
    tm 3 2 2 3 (-10),
    tm 3 2 2 4 (10),
    tm 3 3 0 2 (-30),
    tm 3 3 0 3 (90),
    tm 3 3 0 4 (-30),
    tm 3 3 1 2 (40),
    tm 3 3 1 3 (-120),
    tm 3 3 1 4 (40),
    tm 3 3 2 2 (-10),
    tm 3 3 2 3 (30),
    tm 3 3 2 4 (-10),
    tm 3 4 0 2 (60),
    tm 3 4 0 3 (-60),
    tm 3 4 1 2 (-80),
    tm 3 4 1 3 (80),
    tm 3 4 2 2 (20),
    tm 3 4 2 3 (-20),
    tm 3 5 0 2 (-30),
    tm 3 5 1 2 (40),
    tm 3 5 2 2 (-10),
    tm 4 2 0 3 (30),
    tm 4 2 0 4 (-30),
    tm 4 2 1 3 (-20),
    tm 4 2 1 4 (20),
    tm 4 3 0 2 (30),
    tm 4 3 0 3 (-90),
    tm 4 3 0 4 (30),
    tm 4 3 1 2 (-20),
    tm 4 3 1 3 (60),
    tm 4 3 1 4 (-20),
    tm 4 4 0 2 (-60),
    tm 4 4 0 3 (60),
    tm 4 4 1 2 (40),
    tm 4 4 1 3 (-40),
    tm 4 5 0 2 (30),
    tm 4 5 1 2 (-20),
    tm 5 2 0 3 (-10),
    tm 5 2 0 4 (10),
    tm 5 3 0 2 (-10),
    tm 5 3 0 3 (30),
    tm 5 3 0 4 (-10),
    tm 5 4 0 2 (20),
    tm 5 4 0 3 (-20),
    tm 5 5 0 2 (-10)]

/-- Column 5 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column5 : Poly :=
  [tm 2 0 4 3 (10),
    tm 2 0 4 4 (-10),
    tm 2 0 5 3 (-10),
    tm 2 0 5 4 (10),
    tm 2 1 4 2 (10),
    tm 2 1 4 3 (-20),
    tm 2 1 5 2 (-10),
    tm 2 1 5 3 (20),
    tm 2 2 4 2 (-10),
    tm 2 2 5 2 (10),
    tm 3 0 3 3 (20),
    tm 3 0 3 4 (-20),
    tm 3 0 4 3 (-30),
    tm 3 0 4 4 (30),
    tm 3 0 5 3 (10),
    tm 3 0 5 4 (-10),
    tm 3 1 3 2 (20),
    tm 3 1 3 3 (-40),
    tm 3 1 4 2 (-30),
    tm 3 1 4 3 (60),
    tm 3 1 5 2 (10),
    tm 3 1 5 3 (-20),
    tm 3 2 3 2 (-20),
    tm 3 2 4 2 (30),
    tm 3 2 5 2 (-10),
    tm 4 0 2 3 (10),
    tm 4 0 2 4 (-10),
    tm 4 0 3 3 (-30),
    tm 4 0 3 4 (30),
    tm 4 0 4 3 (20),
    tm 4 0 4 4 (-20),
    tm 4 1 2 2 (10),
    tm 4 1 2 3 (-20),
    tm 4 1 3 2 (-30),
    tm 4 1 3 3 (60),
    tm 4 1 4 2 (20),
    tm 4 1 4 3 (-40),
    tm 4 2 2 2 (-10),
    tm 4 2 3 2 (30),
    tm 4 2 4 2 (-20),
    tm 5 0 2 3 (-10),
    tm 5 0 2 4 (10),
    tm 5 0 3 3 (10),
    tm 5 0 3 4 (-10),
    tm 5 1 2 2 (-10),
    tm 5 1 2 3 (20),
    tm 5 1 3 2 (10),
    tm 5 1 3 3 (-20),
    tm 5 2 2 2 (10),
    tm 5 2 3 2 (-10)]

/-- Column 5 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column5 : Poly :=
  [tm 0 2 2 3 (10),
    tm 0 2 2 4 (-10),
    tm 0 2 3 3 (-30),
    tm 0 2 3 4 (30),
    tm 0 2 4 3 (30),
    tm 0 2 4 4 (-30),
    tm 0 2 5 3 (-10),
    tm 0 2 5 4 (10),
    tm 0 3 2 2 (10),
    tm 0 3 2 3 (-30),
    tm 0 3 2 4 (10),
    tm 0 3 3 2 (-30),
    tm 0 3 3 3 (90),
    tm 0 3 3 4 (-30),
    tm 0 3 4 2 (30),
    tm 0 3 4 3 (-90),
    tm 0 3 4 4 (30),
    tm 0 3 5 2 (-10),
    tm 0 3 5 3 (30),
    tm 0 3 5 4 (-10),
    tm 0 4 2 2 (-20),
    tm 0 4 2 3 (20),
    tm 0 4 3 2 (60),
    tm 0 4 3 3 (-60),
    tm 0 4 4 2 (-60),
    tm 0 4 4 3 (60),
    tm 0 4 5 2 (20),
    tm 0 4 5 3 (-20),
    tm 0 5 2 2 (10),
    tm 0 5 3 2 (-30),
    tm 0 5 4 2 (30),
    tm 0 5 5 2 (-10),
    tm 1 2 2 3 (-20),
    tm 1 2 2 4 (20),
    tm 1 2 3 3 (40),
    tm 1 2 3 4 (-40),
    tm 1 2 4 3 (-20),
    tm 1 2 4 4 (20),
    tm 1 3 2 2 (-20),
    tm 1 3 2 3 (60),
    tm 1 3 2 4 (-20),
    tm 1 3 3 2 (40),
    tm 1 3 3 3 (-120),
    tm 1 3 3 4 (40),
    tm 1 3 4 2 (-20),
    tm 1 3 4 3 (60),
    tm 1 3 4 4 (-20),
    tm 1 4 2 2 (40),
    tm 1 4 2 3 (-40),
    tm 1 4 3 2 (-80),
    tm 1 4 3 3 (80),
    tm 1 4 4 2 (40),
    tm 1 4 4 3 (-40),
    tm 1 5 2 2 (-20),
    tm 1 5 3 2 (40),
    tm 1 5 4 2 (-20),
    tm 2 2 2 3 (10),
    tm 2 2 2 4 (-10),
    tm 2 2 3 3 (-10),
    tm 2 2 3 4 (10),
    tm 2 3 2 2 (10),
    tm 2 3 2 3 (-30),
    tm 2 3 2 4 (10),
    tm 2 3 3 2 (-10),
    tm 2 3 3 3 (30),
    tm 2 3 3 4 (-10),
    tm 2 4 2 2 (-20),
    tm 2 4 2 3 (20),
    tm 2 4 3 2 (20),
    tm 2 4 3 3 (-20),
    tm 2 5 2 2 (10),
    tm 2 5 3 2 (-10)]

/-- Column 6 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column6 : Poly :=
  [tm 2 2 3 0 (-10),
    tm 2 2 3 1 (20),
    tm 2 2 3 2 (-10),
    tm 2 2 4 0 (20),
    tm 2 2 4 1 (-40),
    tm 2 2 4 2 (20),
    tm 2 2 5 0 (-10),
    tm 2 2 5 1 (20),
    tm 2 2 5 2 (-10),
    tm 2 3 3 0 (30),
    tm 2 3 3 1 (-40),
    tm 2 3 3 2 (10),
    tm 2 3 4 0 (-60),
    tm 2 3 4 1 (80),
    tm 2 3 4 2 (-20),
    tm 2 3 5 0 (30),
    tm 2 3 5 1 (-40),
    tm 2 3 5 2 (10),
    tm 2 4 3 0 (-30),
    tm 2 4 3 1 (20),
    tm 2 4 4 0 (60),
    tm 2 4 4 1 (-40),
    tm 2 4 5 0 (-30),
    tm 2 4 5 1 (20),
    tm 2 5 3 0 (10),
    tm 2 5 4 0 (-20),
    tm 2 5 5 0 (10),
    tm 3 2 2 0 (-10),
    tm 3 2 2 1 (20),
    tm 3 2 2 2 (-10),
    tm 3 2 3 0 (30),
    tm 3 2 3 1 (-60),
    tm 3 2 3 2 (30),
    tm 3 2 4 0 (-20),
    tm 3 2 4 1 (40),
    tm 3 2 4 2 (-20),
    tm 3 3 2 0 (30),
    tm 3 3 2 1 (-40),
    tm 3 3 2 2 (10),
    tm 3 3 3 0 (-90),
    tm 3 3 3 1 (120),
    tm 3 3 3 2 (-30),
    tm 3 3 4 0 (60),
    tm 3 3 4 1 (-80),
    tm 3 3 4 2 (20),
    tm 3 4 2 0 (-30),
    tm 3 4 2 1 (20),
    tm 3 4 3 0 (90),
    tm 3 4 3 1 (-60),
    tm 3 4 4 0 (-60),
    tm 3 4 4 1 (40),
    tm 3 5 2 0 (10),
    tm 3 5 3 0 (-30),
    tm 3 5 4 0 (20),
    tm 4 2 2 0 (10),
    tm 4 2 2 1 (-20),
    tm 4 2 2 2 (10),
    tm 4 2 3 0 (-10),
    tm 4 2 3 1 (20),
    tm 4 2 3 2 (-10),
    tm 4 3 2 0 (-30),
    tm 4 3 2 1 (40),
    tm 4 3 2 2 (-10),
    tm 4 3 3 0 (30),
    tm 4 3 3 1 (-40),
    tm 4 3 3 2 (10),
    tm 4 4 2 0 (30),
    tm 4 4 2 1 (-20),
    tm 4 4 3 0 (-30),
    tm 4 4 3 1 (20),
    tm 4 5 2 0 (-10),
    tm 4 5 3 0 (10)]

/-- Column 6 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column6 : Poly :=
  [tm 2 2 0 3 (10),
    tm 2 2 0 4 (-10),
    tm 2 2 1 3 (-20),
    tm 2 2 1 4 (10),
    tm 2 2 1 5 (10),
    tm 2 2 2 3 (10),
    tm 2 2 2 5 (-10),
    tm 2 3 0 2 (10),
    tm 2 3 0 3 (-30),
    tm 2 3 0 4 (10),
    tm 2 3 1 2 (-20),
    tm 2 3 1 3 (40),
    tm 2 3 1 4 (10),
    tm 2 3 1 5 (-10),
    tm 2 3 2 2 (10),
    tm 2 3 2 3 (-10),
    tm 2 3 2 4 (-20),
    tm 2 3 2 5 (10),
    tm 2 4 0 2 (-20),
    tm 2 4 0 3 (20),
    tm 2 4 1 2 (30),
    tm 2 4 1 3 (-10),
    tm 2 4 1 4 (-20),
    tm 2 4 2 2 (-10),
    tm 2 4 2 3 (-10),
    tm 2 4 2 4 (20),
    tm 2 5 0 2 (10),
    tm 2 5 1 2 (-10),
    tm 2 5 1 3 (-10),
    tm 2 5 2 3 (10),
    tm 3 2 0 3 (-30),
    tm 3 2 0 4 (20),
    tm 3 2 0 5 (10),
    tm 3 2 1 3 (40),
    tm 3 2 1 4 (-20),
    tm 3 2 1 5 (-20),
    tm 3 2 2 3 (-10),
    tm 3 2 2 4 (10),
    tm 3 3 0 2 (-30),
    tm 3 3 0 3 (70),
    tm 3 3 0 5 (-10),
    tm 3 3 1 2 (40),
    tm 3 3 1 3 (-80),
    tm 3 3 1 4 (-20),
    tm 3 3 1 5 (20),
    tm 3 3 2 2 (-10),
    tm 3 3 2 3 (30),
    tm 3 3 2 4 (-10),
    tm 3 4 0 2 (50),
    tm 3 4 0 3 (-30),
    tm 3 4 0 4 (-20),
    tm 3 4 1 2 (-60),
    tm 3 4 1 3 (20),
    tm 3 4 1 4 (40),
    tm 3 4 2 2 (20),
    tm 3 4 2 3 (-20),
    tm 3 5 0 2 (-20),
    tm 3 5 0 3 (-10),
    tm 3 5 1 2 (20),
    tm 3 5 1 3 (20),
    tm 3 5 2 2 (-10),
    tm 4 2 0 3 (30),
    tm 4 2 0 4 (-20),
    tm 4 2 0 5 (-10),
    tm 4 2 1 3 (-20),
    tm 4 2 1 4 (20),
    tm 4 3 0 2 (30),
    tm 4 3 0 3 (-70),
    tm 4 3 0 5 (10),
    tm 4 3 1 2 (-20),
    tm 4 3 1 3 (60),
    tm 4 3 1 4 (-20),
    tm 4 4 0 2 (-50),
    tm 4 4 0 3 (30),
    tm 4 4 0 4 (20),
    tm 4 4 1 2 (40),
    tm 4 4 1 3 (-40),
    tm 4 5 0 2 (20),
    tm 4 5 0 3 (10),
    tm 4 5 1 2 (-20),
    tm 5 2 0 3 (-10),
    tm 5 2 0 4 (10),
    tm 5 3 0 2 (-10),
    tm 5 3 0 3 (30),
    tm 5 3 0 4 (-10),
    tm 5 4 0 2 (20),
    tm 5 4 0 3 (-20),
    tm 5 5 0 2 (-10)]

/-- Column 6 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column6 : Poly :=
  [tm 2 0 3 2 (-10),
    tm 2 0 3 3 (30),
    tm 2 0 3 4 (-30),
    tm 2 0 3 5 (10),
    tm 2 0 4 2 (20),
    tm 2 0 4 3 (-50),
    tm 2 0 4 4 (50),
    tm 2 0 4 5 (-20),
    tm 2 0 5 2 (-10),
    tm 2 0 5 3 (20),
    tm 2 0 5 4 (-20),
    tm 2 0 5 5 (10),
    tm 2 1 3 2 (20),
    tm 2 1 3 3 (-40),
    tm 2 1 3 4 (20),
    tm 2 1 4 2 (-30),
    tm 2 1 4 3 (60),
    tm 2 1 4 4 (-40),
    tm 2 1 5 2 (10),
    tm 2 1 5 3 (-20),
    tm 2 1 5 4 (20),
    tm 2 2 3 2 (-10),
    tm 2 2 3 3 (10),
    tm 2 2 4 2 (10),
    tm 2 2 4 3 (-20),
    tm 2 2 5 3 (10),
    tm 3 0 2 2 (-10),
    tm 3 0 2 3 (30),
    tm 3 0 2 4 (-30),
    tm 3 0 2 5 (10),
    tm 3 0 3 2 (30),
    tm 3 0 3 3 (-70),
    tm 3 0 3 4 (70),
    tm 3 0 3 5 (-30),
    tm 3 0 4 2 (-20),
    tm 3 0 4 3 (30),
    tm 3 0 4 4 (-30),
    tm 3 0 4 5 (20),
    tm 3 0 5 3 (10),
    tm 3 0 5 4 (-10),
    tm 3 1 2 2 (20),
    tm 3 1 2 3 (-40),
    tm 3 1 2 4 (20),
    tm 3 1 3 2 (-40),
    tm 3 1 3 3 (80),
    tm 3 1 3 4 (-60),
    tm 3 1 4 2 (10),
    tm 3 1 4 3 (-20),
    tm 3 1 4 4 (40),
    tm 3 1 5 2 (10),
    tm 3 1 5 3 (-20),
    tm 3 2 2 2 (-10),
    tm 3 2 2 3 (10),
    tm 3 2 3 2 (10),
    tm 3 2 3 3 (-30),
    tm 3 2 4 2 (10),
    tm 3 2 4 3 (20),
    tm 3 2 5 2 (-10),
    tm 4 0 2 2 (10),
    tm 4 0 2 3 (-20),
    tm 4 0 2 4 (20),
    tm 4 0 2 5 (-10),
    tm 4 0 3 2 (-10),
    tm 4 0 3 5 (10),
    tm 4 0 4 3 (20),
    tm 4 0 4 4 (-20),
    tm 4 1 2 2 (-10),
    tm 4 1 2 3 (20),
    tm 4 1 2 4 (-20),
    tm 4 1 3 2 (-10),
    tm 4 1 3 3 (20),
    tm 4 1 3 4 (20),
    tm 4 1 4 2 (20),
    tm 4 1 4 3 (-40),
    tm 4 2 2 3 (-10),
    tm 4 2 3 2 (20),
    tm 4 2 3 3 (10),
    tm 4 2 4 2 (-20),
    tm 5 0 2 3 (-10),
    tm 5 0 2 4 (10),
    tm 5 0 3 3 (10),
    tm 5 0 3 4 (-10),
    tm 5 1 2 2 (-10),
    tm 5 1 2 3 (20),
    tm 5 1 3 2 (10),
    tm 5 1 3 3 (-20),
    tm 5 2 2 2 (10),
    tm 5 2 3 2 (-10)]

/-- Column 6 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column6 : Poly :=
  [tm 0 2 2 3 (10),
    tm 0 2 2 4 (-10),
    tm 0 2 3 3 (-30),
    tm 0 2 3 4 (30),
    tm 0 2 4 3 (30),
    tm 0 2 4 4 (-30),
    tm 0 2 5 3 (-10),
    tm 0 2 5 4 (10),
    tm 0 3 2 2 (10),
    tm 0 3 2 3 (-30),
    tm 0 3 2 4 (10),
    tm 0 3 3 2 (-30),
    tm 0 3 3 3 (90),
    tm 0 3 3 4 (-30),
    tm 0 3 4 2 (30),
    tm 0 3 4 3 (-90),
    tm 0 3 4 4 (30),
    tm 0 3 5 2 (-10),
    tm 0 3 5 3 (30),
    tm 0 3 5 4 (-10),
    tm 0 4 2 2 (-20),
    tm 0 4 2 3 (20),
    tm 0 4 3 2 (60),
    tm 0 4 3 3 (-60),
    tm 0 4 4 2 (-60),
    tm 0 4 4 3 (60),
    tm 0 4 5 2 (20),
    tm 0 4 5 3 (-20),
    tm 0 5 2 2 (10),
    tm 0 5 3 2 (-30),
    tm 0 5 4 2 (30),
    tm 0 5 5 2 (-10),
    tm 1 2 2 3 (-20),
    tm 1 2 2 4 (20),
    tm 1 2 3 3 (40),
    tm 1 2 3 4 (-40),
    tm 1 2 4 3 (-20),
    tm 1 2 4 4 (20),
    tm 1 3 2 2 (-20),
    tm 1 3 2 3 (60),
    tm 1 3 2 4 (-20),
    tm 1 3 3 2 (40),
    tm 1 3 3 3 (-120),
    tm 1 3 3 4 (40),
    tm 1 3 4 2 (-20),
    tm 1 3 4 3 (60),
    tm 1 3 4 4 (-20),
    tm 1 4 2 2 (40),
    tm 1 4 2 3 (-40),
    tm 1 4 3 2 (-80),
    tm 1 4 3 3 (80),
    tm 1 4 4 2 (40),
    tm 1 4 4 3 (-40),
    tm 1 5 2 2 (-20),
    tm 1 5 3 2 (40),
    tm 1 5 4 2 (-20),
    tm 2 2 2 3 (10),
    tm 2 2 2 4 (-10),
    tm 2 2 3 3 (-10),
    tm 2 2 3 4 (10),
    tm 2 3 2 2 (10),
    tm 2 3 2 3 (-30),
    tm 2 3 2 4 (10),
    tm 2 3 3 2 (-10),
    tm 2 3 3 3 (30),
    tm 2 3 3 4 (-10),
    tm 2 4 2 2 (-20),
    tm 2 4 2 3 (20),
    tm 2 4 3 2 (20),
    tm 2 4 3 3 (-20),
    tm 2 5 2 2 (10),
    tm 2 5 3 2 (-10)]

/-- Column 7 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column7 : Poly :=
  [tm 2 2 4 1 (-10),
    tm 2 2 4 2 (10),
    tm 2 2 5 1 (10),
    tm 2 2 5 2 (-10),
    tm 2 3 4 0 (-10),
    tm 2 3 4 1 (20),
    tm 2 3 5 0 (10),
    tm 2 3 5 1 (-20),
    tm 2 4 4 0 (10),
    tm 2 4 5 0 (-10),
    tm 3 2 3 1 (-20),
    tm 3 2 3 2 (20),
    tm 3 2 4 1 (30),
    tm 3 2 4 2 (-30),
    tm 3 2 5 1 (-10),
    tm 3 2 5 2 (10),
    tm 3 3 3 0 (-20),
    tm 3 3 3 1 (40),
    tm 3 3 4 0 (30),
    tm 3 3 4 1 (-60),
    tm 3 3 5 0 (-10),
    tm 3 3 5 1 (20),
    tm 3 4 3 0 (20),
    tm 3 4 4 0 (-30),
    tm 3 4 5 0 (10),
    tm 4 2 2 1 (-10),
    tm 4 2 2 2 (10),
    tm 4 2 3 1 (30),
    tm 4 2 3 2 (-30),
    tm 4 2 4 1 (-20),
    tm 4 2 4 2 (20),
    tm 4 3 2 0 (-10),
    tm 4 3 2 1 (20),
    tm 4 3 3 0 (30),
    tm 4 3 3 1 (-60),
    tm 4 3 4 0 (-20),
    tm 4 3 4 1 (40),
    tm 4 4 2 0 (10),
    tm 4 4 3 0 (-30),
    tm 4 4 4 0 (20),
    tm 5 2 2 1 (10),
    tm 5 2 2 2 (-10),
    tm 5 2 3 1 (-10),
    tm 5 2 3 2 (10),
    tm 5 3 2 0 (10),
    tm 5 3 2 1 (-20),
    tm 5 3 3 0 (-10),
    tm 5 3 3 1 (20),
    tm 5 4 2 0 (-10),
    tm 5 4 3 0 (10)]

/-- Column 7 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column7 : Poly :=
  [tm 2 2 0 4 (10),
    tm 2 2 0 5 (-10),
    tm 2 2 1 4 (-20),
    tm 2 2 1 5 (20),
    tm 2 2 2 4 (10),
    tm 2 2 2 5 (-10),
    tm 2 3 0 4 (-10),
    tm 2 3 1 4 (20),
    tm 2 3 2 4 (-10),
    tm 2 4 0 2 (-10),
    tm 2 4 0 3 (10),
    tm 2 4 1 2 (20),
    tm 2 4 1 3 (-20),
    tm 2 4 2 2 (-10),
    tm 2 4 2 3 (10),
    tm 2 5 0 2 (10),
    tm 2 5 1 2 (-20),
    tm 2 5 2 2 (10),
    tm 3 2 0 4 (-30),
    tm 3 2 0 5 (30),
    tm 3 2 1 4 (40),
    tm 3 2 1 5 (-40),
    tm 3 2 2 4 (-10),
    tm 3 2 2 5 (10),
    tm 3 3 0 4 (30),
    tm 3 3 1 4 (-40),
    tm 3 3 2 4 (10),
    tm 3 4 0 2 (30),
    tm 3 4 0 3 (-30),
    tm 3 4 1 2 (-40),
    tm 3 4 1 3 (40),
    tm 3 4 2 2 (10),
    tm 3 4 2 3 (-10),
    tm 3 5 0 2 (-30),
    tm 3 5 1 2 (40),
    tm 3 5 2 2 (-10),
    tm 4 2 0 4 (30),
    tm 4 2 0 5 (-30),
    tm 4 2 1 4 (-20),
    tm 4 2 1 5 (20),
    tm 4 3 0 4 (-30),
    tm 4 3 1 4 (20),
    tm 4 4 0 2 (-30),
    tm 4 4 0 3 (30),
    tm 4 4 1 2 (20),
    tm 4 4 1 3 (-20),
    tm 4 5 0 2 (30),
    tm 4 5 1 2 (-20),
    tm 5 2 0 4 (-10),
    tm 5 2 0 5 (10),
    tm 5 3 0 4 (10),
    tm 5 4 0 2 (10),
    tm 5 4 0 3 (-10),
    tm 5 5 0 2 (-10)]

/-- Column 7 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column7 : Poly :=
  [tm 2 0 4 3 (10),
    tm 2 0 4 4 (-10),
    tm 2 0 5 3 (-10),
    tm 2 0 5 4 (10),
    tm 2 1 4 2 (10),
    tm 2 1 4 3 (-20),
    tm 2 1 5 2 (-10),
    tm 2 1 5 3 (20),
    tm 2 2 4 2 (-10),
    tm 2 2 5 2 (10),
    tm 3 0 3 3 (20),
    tm 3 0 3 4 (-20),
    tm 3 0 4 3 (-30),
    tm 3 0 4 4 (30),
    tm 3 0 5 3 (10),
    tm 3 0 5 4 (-10),
    tm 3 1 3 2 (20),
    tm 3 1 3 3 (-40),
    tm 3 1 4 2 (-30),
    tm 3 1 4 3 (60),
    tm 3 1 5 2 (10),
    tm 3 1 5 3 (-20),
    tm 3 2 3 2 (-20),
    tm 3 2 4 2 (30),
    tm 3 2 5 2 (-10),
    tm 4 0 2 3 (10),
    tm 4 0 2 4 (-10),
    tm 4 0 3 3 (-30),
    tm 4 0 3 4 (30),
    tm 4 0 4 3 (20),
    tm 4 0 4 4 (-20),
    tm 4 1 2 2 (10),
    tm 4 1 2 3 (-20),
    tm 4 1 3 2 (-30),
    tm 4 1 3 3 (60),
    tm 4 1 4 2 (20),
    tm 4 1 4 3 (-40),
    tm 4 2 2 2 (-10),
    tm 4 2 3 2 (30),
    tm 4 2 4 2 (-20),
    tm 5 0 2 3 (-10),
    tm 5 0 2 4 (10),
    tm 5 0 3 3 (10),
    tm 5 0 3 4 (-10),
    tm 5 1 2 2 (-10),
    tm 5 1 2 3 (20),
    tm 5 1 3 2 (10),
    tm 5 1 3 3 (-20),
    tm 5 2 2 2 (10),
    tm 5 2 3 2 (-10)]

/-- Column 7 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column7 : Poly :=
  [tm 0 2 2 4 (10),
    tm 0 2 2 5 (-10),
    tm 0 2 3 4 (-30),
    tm 0 2 3 5 (30),
    tm 0 2 4 4 (30),
    tm 0 2 4 5 (-30),
    tm 0 2 5 4 (-10),
    tm 0 2 5 5 (10),
    tm 0 3 2 4 (-10),
    tm 0 3 3 4 (30),
    tm 0 3 4 4 (-30),
    tm 0 3 5 4 (10),
    tm 0 4 2 2 (-10),
    tm 0 4 2 3 (10),
    tm 0 4 3 2 (30),
    tm 0 4 3 3 (-30),
    tm 0 4 4 2 (-30),
    tm 0 4 4 3 (30),
    tm 0 4 5 2 (10),
    tm 0 4 5 3 (-10),
    tm 0 5 2 2 (10),
    tm 0 5 3 2 (-30),
    tm 0 5 4 2 (30),
    tm 0 5 5 2 (-10),
    tm 1 2 2 4 (-20),
    tm 1 2 2 5 (20),
    tm 1 2 3 4 (40),
    tm 1 2 3 5 (-40),
    tm 1 2 4 4 (-20),
    tm 1 2 4 5 (20),
    tm 1 3 2 4 (20),
    tm 1 3 3 4 (-40),
    tm 1 3 4 4 (20),
    tm 1 4 2 2 (20),
    tm 1 4 2 3 (-20),
    tm 1 4 3 2 (-40),
    tm 1 4 3 3 (40),
    tm 1 4 4 2 (20),
    tm 1 4 4 3 (-20),
    tm 1 5 2 2 (-20),
    tm 1 5 3 2 (40),
    tm 1 5 4 2 (-20),
    tm 2 2 2 4 (10),
    tm 2 2 2 5 (-10),
    tm 2 2 3 4 (-10),
    tm 2 2 3 5 (10),
    tm 2 3 2 4 (-10),
    tm 2 3 3 4 (10),
    tm 2 4 2 2 (-10),
    tm 2 4 2 3 (10),
    tm 2 4 3 2 (10),
    tm 2 4 3 3 (-10),
    tm 2 5 2 2 (10),
    tm 2 5 3 2 (-10)]

/-- Column 8 of the crossing-system row of non-spine tree 0. -/
def crossingRowNonSpine0Column8 : Poly :=
  [tm 2 2 3 0 (-10),
    tm 2 2 3 1 (20),
    tm 2 2 3 2 (-10),
    tm 2 2 4 0 (10),
    tm 2 2 4 1 (-20),
    tm 2 2 4 2 (10),
    tm 2 3 3 0 (30),
    tm 2 3 3 1 (-40),
    tm 2 3 3 2 (10),
    tm 2 3 4 0 (-30),
    tm 2 3 4 1 (40),
    tm 2 3 4 2 (-10),
    tm 2 4 3 0 (-30),
    tm 2 4 3 1 (20),
    tm 2 4 4 0 (30),
    tm 2 4 4 1 (-20),
    tm 2 5 3 0 (10),
    tm 2 5 4 0 (-10),
    tm 3 2 2 0 (-10),
    tm 3 2 2 1 (20),
    tm 3 2 2 2 (-10),
    tm 3 2 3 0 (30),
    tm 3 2 3 1 (-60),
    tm 3 2 3 2 (30),
    tm 3 2 4 0 (-10),
    tm 3 2 4 1 (20),
    tm 3 2 4 2 (-10),
    tm 3 3 2 0 (30),
    tm 3 3 2 1 (-40),
    tm 3 3 2 2 (10),
    tm 3 3 3 0 (-90),
    tm 3 3 3 1 (120),
    tm 3 3 3 2 (-30),
    tm 3 3 4 0 (30),
    tm 3 3 4 1 (-40),
    tm 3 3 4 2 (10),
    tm 3 4 2 0 (-30),
    tm 3 4 2 1 (20),
    tm 3 4 3 0 (90),
    tm 3 4 3 1 (-60),
    tm 3 4 4 0 (-30),
    tm 3 4 4 1 (20),
    tm 3 5 2 0 (10),
    tm 3 5 3 0 (-30),
    tm 3 5 4 0 (10),
    tm 4 2 2 0 (20),
    tm 4 2 2 1 (-40),
    tm 4 2 2 2 (20),
    tm 4 2 3 0 (-20),
    tm 4 2 3 1 (40),
    tm 4 2 3 2 (-20),
    tm 4 3 2 0 (-60),
    tm 4 3 2 1 (80),
    tm 4 3 2 2 (-20),
    tm 4 3 3 0 (60),
    tm 4 3 3 1 (-80),
    tm 4 3 3 2 (20),
    tm 4 4 2 0 (60),
    tm 4 4 2 1 (-40),
    tm 4 4 3 0 (-60),
    tm 4 4 3 1 (40),
    tm 4 5 2 0 (-20),
    tm 4 5 3 0 (20),
    tm 5 2 2 0 (-10),
    tm 5 2 2 1 (20),
    tm 5 2 2 2 (-10),
    tm 5 3 2 0 (30),
    tm 5 3 2 1 (-40),
    tm 5 3 2 2 (10),
    tm 5 4 2 0 (-30),
    tm 5 4 2 1 (20),
    tm 5 5 2 0 (10)]

/-- Column 8 of the crossing-system row of non-spine tree 1. -/
def crossingRowNonSpine1Column8 : Poly :=
  [tm 2 2 0 3 (10),
    tm 2 2 0 4 (-10),
    tm 2 2 1 3 (-20),
    tm 2 2 1 4 (20),
    tm 2 2 2 3 (10),
    tm 2 2 2 4 (-10),
    tm 2 3 0 2 (10),
    tm 2 3 0 3 (-30),
    tm 2 3 0 4 (10),
    tm 2 3 1 2 (-20),
    tm 2 3 1 3 (60),
    tm 2 3 1 4 (-20),
    tm 2 3 2 2 (10),
    tm 2 3 2 3 (-30),
    tm 2 3 2 4 (10),
    tm 2 4 0 2 (-20),
    tm 2 4 0 3 (20),
    tm 2 4 1 2 (40),
    tm 2 4 1 3 (-40),
    tm 2 4 2 2 (-20),
    tm 2 4 2 3 (20),
    tm 2 5 0 2 (10),
    tm 2 5 1 2 (-20),
    tm 2 5 2 2 (10),
    tm 3 2 0 3 (-30),
    tm 3 2 0 4 (30),
    tm 3 2 1 3 (40),
    tm 3 2 1 4 (-40),
    tm 3 2 2 3 (-10),
    tm 3 2 2 4 (10),
    tm 3 3 0 2 (-30),
    tm 3 3 0 3 (90),
    tm 3 3 0 4 (-30),
    tm 3 3 1 2 (40),
    tm 3 3 1 3 (-120),
    tm 3 3 1 4 (40),
    tm 3 3 2 2 (-10),
    tm 3 3 2 3 (30),
    tm 3 3 2 4 (-10),
    tm 3 4 0 2 (60),
    tm 3 4 0 3 (-60),
    tm 3 4 1 2 (-80),
    tm 3 4 1 3 (80),
    tm 3 4 2 2 (20),
    tm 3 4 2 3 (-20),
    tm 3 5 0 2 (-30),
    tm 3 5 1 2 (40),
    tm 3 5 2 2 (-10),
    tm 4 2 0 3 (30),
    tm 4 2 0 4 (-30),
    tm 4 2 1 3 (-20),
    tm 4 2 1 4 (20),
    tm 4 3 0 2 (30),
    tm 4 3 0 3 (-90),
    tm 4 3 0 4 (30),
    tm 4 3 1 2 (-20),
    tm 4 3 1 3 (60),
    tm 4 3 1 4 (-20),
    tm 4 4 0 2 (-60),
    tm 4 4 0 3 (60),
    tm 4 4 1 2 (40),
    tm 4 4 1 3 (-40),
    tm 4 5 0 2 (30),
    tm 4 5 1 2 (-20),
    tm 5 2 0 3 (-10),
    tm 5 2 0 4 (10),
    tm 5 3 0 2 (-10),
    tm 5 3 0 3 (30),
    tm 5 3 0 4 (-10),
    tm 5 4 0 2 (20),
    tm 5 4 0 3 (-20),
    tm 5 5 0 2 (-10)]

/-- Column 8 of the crossing-system row of non-spine tree 2. -/
def crossingRowNonSpine2Column8 : Poly :=
  [tm 2 0 3 2 (-10),
    tm 2 0 3 3 (30),
    tm 2 0 3 4 (-30),
    tm 2 0 3 5 (10),
    tm 2 0 4 2 (10),
    tm 2 0 4 3 (-20),
    tm 2 0 4 4 (20),
    tm 2 0 4 5 (-10),
    tm 2 0 5 3 (-10),
    tm 2 0 5 4 (10),
    tm 2 1 3 2 (20),
    tm 2 1 3 3 (-40),
    tm 2 1 3 4 (20),
    tm 2 1 4 2 (-10),
    tm 2 1 4 3 (20),
    tm 2 1 4 4 (-20),
    tm 2 1 5 2 (-10),
    tm 2 1 5 3 (20),
    tm 2 2 3 2 (-10),
    tm 2 2 3 3 (10),
    tm 2 2 4 3 (-10),
    tm 2 2 5 2 (10),
    tm 3 0 2 2 (-10),
    tm 3 0 2 3 (30),
    tm 3 0 2 4 (-30),
    tm 3 0 2 5 (10),
    tm 3 0 3 2 (30),
    tm 3 0 3 3 (-70),
    tm 3 0 3 4 (70),
    tm 3 0 3 5 (-30),
    tm 3 0 4 2 (-10),
    tm 3 0 4 5 (10),
    tm 3 0 5 3 (10),
    tm 3 0 5 4 (-10),
    tm 3 1 2 2 (20),
    tm 3 1 2 3 (-40),
    tm 3 1 2 4 (20),
    tm 3 1 3 2 (-40),
    tm 3 1 3 3 (80),
    tm 3 1 3 4 (-60),
    tm 3 1 4 2 (-10),
    tm 3 1 4 3 (20),
    tm 3 1 4 4 (20),
    tm 3 1 5 2 (10),
    tm 3 1 5 3 (-20),
    tm 3 2 2 2 (-10),
    tm 3 2 2 3 (10),
    tm 3 2 3 2 (10),
    tm 3 2 3 3 (-30),
    tm 3 2 4 2 (20),
    tm 3 2 4 3 (10),
    tm 3 2 5 2 (-10),
    tm 4 0 2 2 (20),
    tm 4 0 2 3 (-50),
    tm 4 0 2 4 (50),
    tm 4 0 2 5 (-20),
    tm 4 0 3 2 (-20),
    tm 4 0 3 3 (30),
    tm 4 0 3 4 (-30),
    tm 4 0 3 5 (20),
    tm 4 0 4 3 (20),
    tm 4 0 4 4 (-20),
    tm 4 1 2 2 (-30),
    tm 4 1 2 3 (60),
    tm 4 1 2 4 (-40),
    tm 4 1 3 2 (10),
    tm 4 1 3 3 (-20),
    tm 4 1 3 4 (40),
    tm 4 1 4 2 (20),
    tm 4 1 4 3 (-40),
    tm 4 2 2 2 (10),
    tm 4 2 2 3 (-20),
    tm 4 2 3 2 (10),
    tm 4 2 3 3 (20),
    tm 4 2 4 2 (-20),
    tm 5 0 2 2 (-10),
    tm 5 0 2 3 (20),
    tm 5 0 2 4 (-20),
    tm 5 0 2 5 (10),
    tm 5 0 3 3 (10),
    tm 5 0 3 4 (-10),
    tm 5 1 2 2 (10),
    tm 5 1 2 3 (-20),
    tm 5 1 2 4 (20),
    tm 5 1 3 2 (10),
    tm 5 1 3 3 (-20),
    tm 5 2 2 3 (10),
    tm 5 2 3 2 (-10)]

/-- Column 8 of the crossing-system row of non-spine tree 3. -/
def crossingRowNonSpine3Column8 : Poly :=
  [tm 0 2 2 3 (10),
    tm 0 2 2 4 (-10),
    tm 0 2 3 3 (-30),
    tm 0 2 3 4 (20),
    tm 0 2 3 5 (10),
    tm 0 2 4 3 (30),
    tm 0 2 4 4 (-20),
    tm 0 2 4 5 (-10),
    tm 0 2 5 3 (-10),
    tm 0 2 5 4 (10),
    tm 0 3 2 2 (10),
    tm 0 3 2 3 (-30),
    tm 0 3 2 4 (10),
    tm 0 3 3 2 (-30),
    tm 0 3 3 3 (70),
    tm 0 3 3 5 (-10),
    tm 0 3 4 2 (30),
    tm 0 3 4 3 (-70),
    tm 0 3 4 5 (10),
    tm 0 3 5 2 (-10),
    tm 0 3 5 3 (30),
    tm 0 3 5 4 (-10),
    tm 0 4 2 2 (-20),
    tm 0 4 2 3 (20),
    tm 0 4 3 2 (50),
    tm 0 4 3 3 (-30),
    tm 0 4 3 4 (-20),
    tm 0 4 4 2 (-50),
    tm 0 4 4 3 (30),
    tm 0 4 4 4 (20),
    tm 0 4 5 2 (20),
    tm 0 4 5 3 (-20),
    tm 0 5 2 2 (10),
    tm 0 5 3 2 (-20),
    tm 0 5 3 3 (-10),
    tm 0 5 4 2 (20),
    tm 0 5 4 3 (10),
    tm 0 5 5 2 (-10),
    tm 1 2 2 3 (-20),
    tm 1 2 2 4 (10),
    tm 1 2 2 5 (10),
    tm 1 2 3 3 (40),
    tm 1 2 3 4 (-20),
    tm 1 2 3 5 (-20),
    tm 1 2 4 3 (-20),
    tm 1 2 4 4 (20),
    tm 1 3 2 2 (-20),
    tm 1 3 2 3 (40),
    tm 1 3 2 4 (10),
    tm 1 3 2 5 (-10),
    tm 1 3 3 2 (40),
    tm 1 3 3 3 (-80),
    tm 1 3 3 4 (-20),
    tm 1 3 3 5 (20),
    tm 1 3 4 2 (-20),
    tm 1 3 4 3 (60),
    tm 1 3 4 4 (-20),
    tm 1 4 2 2 (30),
    tm 1 4 2 3 (-10),
    tm 1 4 2 4 (-20),
    tm 1 4 3 2 (-60),
    tm 1 4 3 3 (20),
    tm 1 4 3 4 (40),
    tm 1 4 4 2 (40),
    tm 1 4 4 3 (-40),
    tm 1 5 2 2 (-10),
    tm 1 5 2 3 (-10),
    tm 1 5 3 2 (20),
    tm 1 5 3 3 (20),
    tm 1 5 4 2 (-20),
    tm 2 2 2 3 (10),
    tm 2 2 2 5 (-10),
    tm 2 2 3 3 (-10),
    tm 2 2 3 4 (10),
    tm 2 3 2 2 (10),
    tm 2 3 2 3 (-10),
    tm 2 3 2 4 (-20),
    tm 2 3 2 5 (10),
    tm 2 3 3 2 (-10),
    tm 2 3 3 3 (30),
    tm 2 3 3 4 (-10),
    tm 2 4 2 2 (-10),
    tm 2 4 2 3 (-10),
    tm 2 4 2 4 (20),
    tm 2 4 3 2 (20),
    tm 2 4 3 3 (-20),
    tm 2 5 2 3 (10),
    tm 2 5 3 2 (-10)]

end GtzCollarDictionary
