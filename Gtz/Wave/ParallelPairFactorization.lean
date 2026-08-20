/-
# A parallel pair factorizes the mass distribution

The hinge's conclusion is a ZERO of the bracket budget
(`Gtz.hasParallelPair_iff_exists_pair_bracket_mass_zero`).  This module reads
that zero through the Plücker syzygy and finds that it does not merely delete
mass — it FACTORIZES what remains.

Run the syzygy from a base label `c` with the parallel pair `{a,b}` in the two
inner slots:

  `b_{cab}·b_{cde} − b_{cad}·b_{cbe} + b_{cae}·b_{cbd} = 0` .

The first product dies with the pair, and the other two must therefore be
EQUAL:

  `b_{cad}·b_{cbe} = b_{cae}·b_{cbd}`   (`Gtz.weightedBracket_factorization`)

— for every choice of the remaining labels.  In masses
(`Gtz.bracketMass_factorization`):

  `m_{acd}·m_{bce} = m_{ace}·m_{bcd}` .

That is a RANK-ONE condition on the surviving distribution: through each base
label, the mass vector carried by `a` and the mass vector carried by `b` are
proportional.  A parallel pair does not just empty its own four triples at
`(6,3)`; it forces the sixteen that remain into a product form.

Everything here is multiplicative — products of pairs of masses on both sides,
never a sum — which is the shape the campaign's aggregation doctrine demands,
and it is field-blind: the realness of this lane stays at
`Gtz.pair_mass_nonneg` and `Gtz.bracket_threeCycle_nonneg`.
-/
import Gtz.Wave.BracketPluckerSyzygy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. A parallel pair kills its brackets -/

/-- A parallel pair kills every bracket through it, at any base label and in
the inner slots. -/
theorem weightedBracket_eq_zero_of_parallel (D : WeightedDesign m 3)
    (c a b : Fin m) {ratio : ℝ} (hpar : D.atom b = ratio • D.atom a) :
    weightedBracket D c a b = 0 := by
  have hbr : atomBracket D c a b = 0 := by
    rw [atomBracket, hpar]
    simp only [tripleBracket_eq, Pi.smul_apply, smul_eq_mul]
    ring
  rw [weightedBracket, hbr, mul_zero]

/-! ## 2. The factorization -/

/-- **THE FACTORIZATION.**  When a bracket through the base vanishes, the
syzygy forces the two surviving products to agree:

  `b_{cad}·b_{cbe} = b_{cae}·b_{cbd}` . -/
theorem weightedBracket_factorization (D : WeightedDesign m 3) (c a b d e : Fin m)
    (hzero : weightedBracket D c a b = 0) :
    weightedBracket D c a d * weightedBracket D c b e
      = weightedBracket D c a e * weightedBracket D c b d := by
  have hsyz := weightedBracket_plucker D c a b d e
  rw [hzero, zero_mul, zero_sub, neg_add_eq_zero] at hsyz
  linarith [hsyz]

/-- **THE FACTORIZATION IN MASSES.**  Squaring: through every base label, the
masses carried by the two members of a parallel pair are proportional.

  `m_{cad}·m_{cbe} = m_{cae}·m_{cbd}` . -/
theorem bracketMass_factorization (D : WeightedDesign m 3) (c a b d e : Fin m)
    (hzero : weightedBracket D c a b = 0) :
    (D.weight c * (D.weight a * (D.weight d * atomBracket D c a d ^ 2)))
        * (D.weight c * (D.weight b * (D.weight e * atomBracket D c b e ^ 2)))
      = (D.weight c * (D.weight a * (D.weight e * atomBracket D c a e ^ 2)))
        * (D.weight c * (D.weight b * (D.weight d * atomBracket D c b d ^ 2))) := by
  have hfac := weightedBracket_factorization D c a b d e hzero
  have hsq := congrArg (fun x : ℝ => x ^ 2) hfac
  simp only [mul_pow, sq_weightedBracket] at hsq
  exact hsq

/-- **THE HINGE FACTORIZES THE DISTRIBUTION.**  A design with a parallel pair
has its whole mass distribution in product form through every base label: the
pair's two mass vectors are proportional at each base. -/
theorem bracketMass_factorization_of_parallel (D : WeightedDesign m 3)
    {a b : Fin m} {ratio : ℝ} (hpar : D.atom b = ratio • D.atom a)
    (c d e : Fin m) :
    (D.weight c * (D.weight a * (D.weight d * atomBracket D c a d ^ 2)))
        * (D.weight c * (D.weight b * (D.weight e * atomBracket D c b e ^ 2)))
      = (D.weight c * (D.weight a * (D.weight e * atomBracket D c a e ^ 2)))
        * (D.weight c * (D.weight b * (D.weight d * atomBracket D c b d ^ 2))) :=
  bracketMass_factorization D c a b d e
    (weightedBracket_eq_zero_of_parallel D c a b hpar)

/-- **THE CONTRAPOSITIVE — A FAILURE OF PRODUCT FORM REFUTES A PARALLEL PAIR
AT THAT LABEL.**  If any four labels break the product form, the pair `{a,b}`
is not parallel.  This is the hinge's conclusion tested by a POLYNOMIAL
identity in the masses, with no geometry and no field hypothesis. -/
theorem not_parallel_of_bracketMass_factorization_fails (D : WeightedDesign m 3)
    {a b : Fin m} (c d e : Fin m)
    (hbreak : (D.weight c * (D.weight a * (D.weight d * atomBracket D c a d ^ 2)))
        * (D.weight c * (D.weight b * (D.weight e * atomBracket D c b e ^ 2)))
      ≠ (D.weight c * (D.weight a * (D.weight e * atomBracket D c a e ^ 2)))
        * (D.weight c * (D.weight b * (D.weight d * atomBracket D c b d ^ 2))))
    (ratio : ℝ) : D.atom b ≠ ratio • D.atom a := fun hpar =>
  hbreak (bracketMass_factorization_of_parallel D hpar c d e)

end Gtz
