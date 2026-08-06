import Gtz.Certificates.CollarChartReplay

/-!
# Bridge (ii): chart soundness -- the emitted chart polynomials ARE the flat
dictionary cores composed with the barycentric order-chart substitution

The rung-14b atlas replaces the flat weight simplex by 120 order charts.
For a permutation `tau` of the five barycentric weights `(w0, .., w4)` with
`w_tau1 >= .. >= w_tau5`, the chart coordinates `r2..r5` in `[0,1]^4` give

    w_taui = m_i(r) / N(r),   m_1 = 1, m_2 = r2, m_3 = r2 r3,
                              m_4 = r2 r3 r4, m_5 = r2 r3 r4 r5,
    N(r) = m_1 + .. + m_5,

and a flat core `c(w1..w4)` of total degree `d` maps to

    C(r) = N(r)^d * c(m(r)/N(r)).

This file builds that substitution INSIDE the calculus of the committed
checker `Gtz.Certificates.CollarChartReplay`, in the same homogenized
five-variable form `(h, r2, r3, r4, r5)` the certificates use: every
`m_i` is homogenized to degree four by the denominator variable `h`, so
`N` is homogeneous of degree four and `substituteFlatPoly` of a
degree-`d` flat core is homogeneous of degree `4 d` -- exactly the shape
the checker's corner and grouped bounds hypothesize.

The load-bearing theorem is `polyEval_substituteFlatPoly`: the substituted
polynomial, evaluated at a chart point, equals the flat core's
HOMOGENIZATION evaluated at `(N, m_1, .., m_4)`.  Since `N > 0` on the
domain (`normalizerValue_pos`), the sign of the chart polynomial at `r`
is the sign of the flat core at the weight point `w(r)` -- which is what
"chart soundness" means, and it is proved here rather than assumed.

What remains per chart is then a pure DATA check, one `decide` per core:
`canon (substituteFlatPoly ... flatCore) = canon (explicit atom product
times the certificate's cores)`.  That family is machine-generated; the
generic half is this file.
-/

namespace GtzCollarChartSoundness

open Gtz.CollarReplay

set_option maxRecDepth 200000

/-! ## The barycentric order-chart substitution -/

/-- The homogenized barycentric monomial of order slot `slot`:
`m_slot = r2 r3 .. r_{slot+1}`, lifted to degree four by the denominator
variable.  Slot `0` is the largest weight. -/
def slotMonomial : Nat → Poly
  | 0 => [tm 4 0 0 0 0 1]
  | 1 => [tm 3 1 0 0 0 1]
  | 2 => [tm 2 1 1 0 0 1]
  | 3 => [tm 1 1 1 1 0 1]
  | _ => [tm 0 1 1 1 1 1]

/-- The chart normalizer `N = m_1 + .. + m_5`, homogeneous of degree four. -/
def normalizerPoly : Poly :=
  [tm 4 0 0 0 0 1, tm 3 1 0 0 0 1, tm 2 1 1 0 0 1, tm 1 1 1 1 0 1,
   tm 0 1 1 1 1 1]

/-- One term of a flat dictionary core, in the four rim weights. -/
structure FlatTerm where
  expWeightOne : Nat
  expWeightTwo : Nat
  expWeightThree : Nat
  expWeightFour : Nat
  coeff : Int
deriving DecidableEq

abbrev FlatPoly := List FlatTerm

def flatTermDegree (flatTerm : FlatTerm) : Nat :=
  flatTerm.expWeightOne + flatTerm.expWeightTwo + flatTerm.expWeightThree
    + flatTerm.expWeightFour

/-- Flat term literal helper. -/
def ftm (expWeightOne expWeightTwo expWeightThree expWeightFour : Nat)
    (coeff : Int) : FlatTerm :=
  ⟨expWeightOne, expWeightTwo, expWeightThree, expWeightFour, coeff⟩

/-- An order chart is the assignment of an order slot to each of the four
rim weights (the spine weight `w0` takes the remaining slot). -/
structure OrderChart where
  slotOfWeightOne : Nat
  slotOfWeightTwo : Nat
  slotOfWeightThree : Nat
  slotOfWeightFour : Nat

def OrderChart.weightImageOne (chart : OrderChart) : Poly :=
  slotMonomial chart.slotOfWeightOne
def OrderChart.weightImageTwo (chart : OrderChart) : Poly :=
  slotMonomial chart.slotOfWeightTwo
def OrderChart.weightImageThree (chart : OrderChart) : Poly :=
  slotMonomial chart.slotOfWeightThree
def OrderChart.weightImageFour (chart : OrderChart) : Poly :=
  slotMonomial chart.slotOfWeightFour

/-- The chart image of ONE flat term: the weight images raised to the term's
exponents, times the normalizer to the complementary power. -/
def substituteFlatTerm (chart : OrderChart) (totalDegree : Nat)
    (flatTerm : FlatTerm) : Poly :=
  polyMul
    (polyMul
      (polyMul
        (polyMul
          (polyMul [tm 0 0 0 0 0 flatTerm.coeff]
            (powPoly chart.weightImageOne flatTerm.expWeightOne))
          (powPoly chart.weightImageTwo flatTerm.expWeightTwo))
        (powPoly chart.weightImageThree flatTerm.expWeightThree))
      (powPoly chart.weightImageFour flatTerm.expWeightFour))
    (powPoly normalizerPoly (totalDegree - flatTermDegree flatTerm))

/-- The chart image of a flat core. -/
def substituteFlatPoly (chart : OrderChart) (totalDegree : Nat) :
    FlatPoly → Poly
  | [] => []
  | flatTerm :: rest =>
      substituteFlatTerm chart totalDegree flatTerm
        ++ substituteFlatPoly chart totalDegree rest

/-! ## The substitution semantics -/

/-- The flat core's HOMOGENIZATION, evaluated at explicit integer values of
the normalizer and the four weight monomials: `sum_e c_e m^e N^(d-|e|)`. -/
def flatHomogeneousEval (totalDegree : Nat)
    (normalizerValue weightOne weightTwo weightThree weightFour : Int) :
    FlatPoly → Int
  | [] => 0
  | flatTerm :: rest =>
      flatTerm.coeff * intPow weightOne flatTerm.expWeightOne
          * intPow weightTwo flatTerm.expWeightTwo
          * intPow weightThree flatTerm.expWeightThree
          * intPow weightFour flatTerm.expWeightFour
          * intPow normalizerValue (totalDegree - flatTermDegree flatTerm)
        + flatHomogeneousEval totalDegree normalizerValue weightOne weightTwo
            weightThree weightFour rest

theorem polyEval_substituteFlatTerm (chart : OrderChart) (totalDegree : Nat)
    (flatTerm : FlatTerm) (den one two three four : Int) :
    polyEval (substituteFlatTerm chart totalDegree flatTerm) den one two
        three four
      = flatTerm.coeff
          * intPow (polyEval chart.weightImageOne den one two three four)
              flatTerm.expWeightOne
          * intPow (polyEval chart.weightImageTwo den one two three four)
              flatTerm.expWeightTwo
          * intPow (polyEval chart.weightImageThree den one two three four)
              flatTerm.expWeightThree
          * intPow (polyEval chart.weightImageFour den one two three four)
              flatTerm.expWeightFour
          * intPow (polyEval normalizerPoly den one two three four)
              (totalDegree - flatTermDegree flatTerm) := by
  unfold substituteFlatTerm
  rw [polyEval_mul, polyEval_mul, polyEval_mul, polyEval_mul, polyEval_mul,
    polyEval_powPoly, polyEval_powPoly, polyEval_powPoly, polyEval_powPoly,
    polyEval_powPoly]
  have coefficientValue :
      polyEval [tm 0 0 0 0 0 flatTerm.coeff] den one two three four
        = flatTerm.coeff := by
    show termEval (tm 0 0 0 0 0 flatTerm.coeff) den one two three four + 0 = _
    unfold termEval tm
    simp [intPow]
  rw [coefficientValue]

/-- THE SUBSTITUTION SEMANTICS: the chart image of a flat core, evaluated at
a chart point, is the flat core's homogenization evaluated at the
normalizer and the four weight monomials. -/
theorem polyEval_substituteFlatPoly (chart : OrderChart) (totalDegree : Nat)
    (flatPoly : FlatPoly) (den one two three four : Int) :
    polyEval (substituteFlatPoly chart totalDegree flatPoly) den one two
        three four
      = flatHomogeneousEval totalDegree
          (polyEval normalizerPoly den one two three four)
          (polyEval chart.weightImageOne den one two three four)
          (polyEval chart.weightImageTwo den one two three four)
          (polyEval chart.weightImageThree den one two three four)
          (polyEval chart.weightImageFour den one two three four)
          flatPoly := by
  induction flatPoly with
  | nil => rfl
  | cons flatTerm rest inductiveStep =>
      show polyEval (substituteFlatTerm chart totalDegree flatTerm
          ++ substituteFlatPoly chart totalDegree rest) den one two three four
        = _
      rw [polyEval_append, polyEval_substituteFlatTerm, inductiveStep]
      rfl

/-! ## Positivity of the normalizer -/

theorem slotMonomialValueIsPos {den one two three four : Int}
    (domain : PointLiesInDomain den one two three four) (slot : Nat) :
    0 < polyEval (slotMonomial slot) den one two three four := by
  obtain ⟨denGe, oneGe, _, twoGe, _, threeGe, _, fourGe, _⟩ := domain
  have denPos : 0 < den := by omega
  have onePos : 0 < one := by omega
  have twoPos : 0 < two := by omega
  have threePos : 0 < three := by omega
  have fourPos : 0 < four := by omega
  match slot with
  | 0 =>
      show 0 < termEval (tm 4 0 0 0 0 1) den one two three four + 0
      unfold termEval tm
      simp only [Int.one_mul, Int.add_zero, intPow]
      have := intPow_pos denPos 4
      simp [intPow] at this ⊢
      omega
  | 1 =>
      show 0 < termEval (tm 3 1 0 0 0 1) den one two three four + 0
      unfold termEval tm
      simp only [Int.add_zero]
      have denPow : 0 < intPow den 3 := intPow_pos denPos 3
      have onePow : 0 < intPow one 1 := intPow_pos onePos 1
      have product : 0 < intPow den 3 * intPow one 1 :=
        Int.mul_pos denPow onePow
      simp only [Int.one_mul, intPow] at product ⊢
      omega
  | 2 =>
      show 0 < termEval (tm 2 1 1 0 0 1) den one two three four + 0
      unfold termEval tm
      simp only [Int.add_zero]
      have product : 0 < intPow den 2 * intPow one 1 * intPow two 1 :=
        Int.mul_pos (Int.mul_pos (intPow_pos denPos 2) (intPow_pos onePos 1))
          (intPow_pos twoPos 1)
      simp only [Int.one_mul, intPow] at product ⊢
      omega
  | 3 =>
      show 0 < termEval (tm 1 1 1 1 0 1) den one two three four + 0
      unfold termEval tm
      simp only [Int.add_zero]
      have product : 0 < intPow den 1 * intPow one 1 * intPow two 1
          * intPow three 1 :=
        Int.mul_pos (Int.mul_pos (Int.mul_pos (intPow_pos denPos 1)
          (intPow_pos onePos 1)) (intPow_pos twoPos 1)) (intPow_pos threePos 1)
      simp only [Int.one_mul, intPow] at product ⊢
      omega
  | (n + 4) =>
      show 0 < termEval (tm 0 1 1 1 1 1) den one two three four + 0
      unfold termEval tm
      simp only [Int.add_zero]
      have product : 0 < intPow one 1 * intPow two 1 * intPow three 1
          * intPow four 1 :=
        Int.mul_pos (Int.mul_pos (Int.mul_pos (intPow_pos onePos 1)
          (intPow_pos twoPos 1)) (intPow_pos threePos 1))
          (intPow_pos fourPos 1)
      simp only [Int.one_mul, intPow] at product ⊢
      omega

/-- The chart normalizer is strictly positive at every point of the chart
domain, so dividing by it never flips a sign: this is the exact reason the
chart substitution is SIGN FAITHFUL. -/
theorem normalizerValueIsPos {den one two three four : Int}
    (domain : PointLiesInDomain den one two three four) :
    0 < polyEval normalizerPoly den one two three four := by
  have slotZero := slotMonomialValueIsPos domain 0
  have slotOne := slotMonomialValueIsPos domain 1
  have slotTwo := slotMonomialValueIsPos domain 2
  have slotThree := slotMonomialValueIsPos domain 3
  have slotFour := slotMonomialValueIsPos domain 4
  have expand : polyEval normalizerPoly den one two three four
      = polyEval (slotMonomial 0) den one two three four
        + (polyEval (slotMonomial 1) den one two three four
          + (polyEval (slotMonomial 2) den one two three four
            + (polyEval (slotMonomial 3) den one two three four
              + polyEval (slotMonomial 4) den one two three four))) := by
    simp [normalizerPoly, slotMonomial, polyEval]
  omega

/-! ## Chart soundness as a data check

With the semantics proved, "the emitted chart core IS the flat core composed
with the chart map" is the single polynomial identity below, one `decide`
per core: the substituted flat core equals the certificate's core product
(the atoms carry the sign, the cores carry the sign-undecided content).
`chartCoreMatchesSubstitution` packages the conclusion in the form the
checker consumes: equal values at every point. -/

theorem chartCoreMatchesSubstitution (chart : OrderChart) (totalDegree : Nat)
    (flatPoly : FlatPoly) (certificateProduct : Poly)
    (dataCheck :
      canon (substituteFlatPoly chart totalDegree flatPoly)
        = canon certificateProduct)
    (den one two three four : Int) :
    flatHomogeneousEval totalDegree
        (polyEval normalizerPoly den one two three four)
        (polyEval chart.weightImageOne den one two three four)
        (polyEval chart.weightImageTwo den one two three four)
        (polyEval chart.weightImageThree den one two three four)
        (polyEval chart.weightImageFour den one two three four)
        flatPoly
      = polyEval certificateProduct den one two three four := by
  rw [← polyEval_substituteFlatPoly]
  exact polyEval_eq_of_canon_eq _ _ dataCheck den one two three four

end GtzCollarChartSoundness
