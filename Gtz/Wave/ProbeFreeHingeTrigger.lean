/-
# The probe is not information: a hinge trigger in pure pair currency

The corank-one arm's rigidity is the MIRROR: two weak dominators one swap apart
whose exchanged atoms read a null probe equally force a parallel pair
(`Gtz.hasParallelPair_of_mirror_dominators_of_readings_eq`).  Every statement in
that machine mentions the probe `w`, and the probe is not a design quantity — it
is an eigenvector, invisible to the pair currency the hinge is written in.  That
is why the arm's triggers have never been polynomial conditions on a design.

This module removes the probe.

## The adjugate, off the diagonal

`Gtz.pairGapMinor_eq_pairMinorTotal_mul_reading_first` says the DIAGONAL of the
Gram gap's adjugate is the second invariant times a squared reading.  The same
is true off the diagonal, and the off-diagonal cofactor is

  `pairAdjOff a b c := (a·c)(b·c) − (a·b)(l_c − 1)` ,

so that (`Gtz.pairMinorTotal_mul_readings_first` and its two permutations)

  **`pairMinorTotal a b c * ((a·w)(b·w)) = pairAdjOff a b c`** .

Together with the diagonal law this is `adj N = e2 · s sᵀ` entrywise, and it is
proved by four two-term column identities plus the normalization — no rank
hypothesis, no case split, and no positivity.

## The probe elimination

Every vector's reading of the probe now collapses to pair data.  For ANY vector
`v` (`Gtz.pairMinorTotal_mul_reading_sq`):

  **`pairMinorTotal a b c * (v·w)^2 = pairAdjForm a b c v`** ,

where `pairAdjForm` is the adjugate's quadratic form evaluated at the three
readings `(v·a, v·b, v·c)`.  The right side mentions no eigenvector.  **The null
probe of a weak dominator reads the whole design through the triple's own pair
minors and cofactors.**

## What the swap machine becomes

The landed `Gtz.swap_nullForm_of_null` prices a swap by the difference of two
squared readings.  Multiplied by the second invariant, that difference is a
difference of pair-currency polynomials
(`Gtz.pairMinorTotal_mul_swap_nullForm`):

  **`e2 · wᵀ(S_{C'} − 1)w = pairAdjForm a b c g_q − pairGapMinor b c`** .

So the whole swap census is one polynomial comparison, and the mirror's
equality case is one polynomial EQUATION:

  **`Gtz.hasParallelPair_of_pairAdjForm_eq`: if the shared pair is admissible,
  the swap weakly dominates, and `pairAdjForm a b c g_q = pairGapMinor b c`,
  then the design has a parallel pair.**

No probe appears in that statement.  Its contrapositive
(`Gtz.pairGapMinor_lt_pairAdjForm_of_not_hasParallelPair`) is the constraint a
`(6,3)` tie must satisfy at EVERY dominating swap over an admissible pair: a
STRICT polynomial inequality in leverages and inner products alone.

## The shared pair is read by both dominators

Two weak dominators over a common pair each compute that pair's minor from
their own probe (`Gtz.pairGapMinor_shared_transfer`):

  `e2(C)·(g_x·w)^2 = pairGapMinor g_y g_z = e2(C')·(g_q·w')^2` .

The shared pair minor is the exchange rate between the two probes.

[MEASURED before proving.  The off-diagonal law holds to `1.0e-13` and the
reading formula to `5.2e-13` over 30,000 random corank-one weak dominators with
an ARBITRARY probed vector, and `pairAdjForm a b c a = pairGapMinor b c` to
`9.5e-13` as the consistency check.  The certificates were verified symbolically
before any Lean was written.]
-/
import Gtz.Wave.NullProbeAdjugateLaw
import Gtz.Wave.MirrorPairMinorTrigger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The scalar core, off the diagonal

Four two-term identities say the columns of the adjugate are proportional to the
null vector.  They need only the three linear relations, and no normalization. -/

/-- The first column identity: the first diagonal cofactor against the second
entry equals the first off-diagonal cofactor against the first entry. -/
theorem adjugate_col_first (A B C P Q R s1 s2 s3 : ℝ)
    (h2 : P * s1 + B * s2 + R * s3 = 0)
    (h3 : Q * s1 + R * s2 + C * s3 = 0) :
    (B * C - R ^ 2) * s2 = (Q * R - P * C) * s1 := by
  linear_combination C * h2 - R * h3

/-- The second column identity. -/
theorem adjugate_col_second (A B C P Q R s1 s2 s3 : ℝ)
    (h1 : A * s1 + P * s2 + Q * s3 = 0)
    (h3 : Q * s1 + R * s2 + C * s3 = 0) :
    (A * C - Q ^ 2) * s1 = (Q * R - P * C) * s2 := by
  linear_combination C * h1 - Q * h3

/-- The third column identity, carrying the second off-diagonal cofactor. -/
theorem adjugate_col_third (A B C P Q R s1 s2 s3 : ℝ)
    (h2 : P * s1 + B * s2 + R * s3 = 0)
    (h3 : Q * s1 + R * s2 + C * s3 = 0) :
    (P * R - Q * B) * s2 = (Q * R - P * C) * s3 := by
  linear_combination P * h3 - Q * h2

/-- The fourth column identity. -/
theorem adjugate_col_fourth (A B C P Q R s1 s2 s3 : ℝ)
    (h1 : A * s1 + P * s2 + Q * s3 = 0)
    (h2 : P * s1 + B * s2 + R * s3 = 0) :
    (P * R - Q * B) * s3 = (A * B - P ^ 2) * s1 := by
  linear_combination P * h2 - B * h1

/-- **THE ADJUGATE LAW OFF THE DIAGONAL, IN SCALARS.**  The off-diagonal
cofactor is the adjugate's trace times the product of the two corresponding
entries of the unit null vector.  Assembled from the four column identities and
the normalization, with no case split and no rank hypothesis. -/
theorem adjugate_offDiag_core (A B C P Q R s1 s2 s3 : ℝ)
    (h1 : A * s1 + P * s2 + Q * s3 = 0)
    (h2 : P * s1 + B * s2 + R * s3 = 0)
    (h3 : Q * s1 + R * s2 + C * s3 = 0)
    (hn : s1 ^ 2 + s2 ^ 2 + s3 ^ 2 = 1) :
    Q * R - P * C
      = ((B * C - R ^ 2) + (A * C - Q ^ 2) + (A * B - P ^ 2)) * s1 * s2 := by
  have c1 := adjugate_col_first A B C P Q R s1 s2 s3 h2 h3
  have c2 := adjugate_col_second A B C P Q R s1 s2 s3 h1 h3
  have c3 := adjugate_col_third A B C P Q R s1 s2 s3 h2 h3
  have c4 := adjugate_col_fourth A B C P Q R s1 s2 s3 h1 h2
  linear_combination (-(Q * R - P * C)) * hn - s1 * c1 - s2 * c2 - s3 * c3 + s2 * c4

/-! ## 2. The cofactor of a pair, and the adjugate's quadratic form -/

/-- The off-diagonal cofactor of the Gram gap at the pair `(a,b)`, with `c` the
member the pair leaves out.  It is the companion of `Gtz.pairGapMinor`, which is
the diagonal cofactor. -/
noncomputable def pairAdjOff (a b c : Fin 3 → ℝ) : ℝ :=
  (a ⬝ᵥ c) * (b ⬝ᵥ c) - (a ⬝ᵥ b) * (leverageOf c - 1)

/-- The cofactor with the last two members interchanged, in canonical dot-product
order. -/
theorem pairAdjOff_swap_last (a b c : Fin 3 → ℝ) :
    pairAdjOff a c b = (a ⬝ᵥ b) * (b ⬝ᵥ c) - (a ⬝ᵥ c) * (leverageOf b - 1) := by
  rw [pairAdjOff, dotProduct_comm c b]

/-- The cofactor at the last pair, in canonical dot-product order. -/
theorem pairAdjOff_last_pair (a b c : Fin 3 → ℝ) :
    pairAdjOff b c a = (a ⬝ᵥ b) * (a ⬝ᵥ c) - (b ⬝ᵥ c) * (leverageOf a - 1) := by
  rw [pairAdjOff, dotProduct_comm b a, dotProduct_comm c a]

/-- **THE ADJUGATE FORM.**  The quadratic form of the Gram gap's adjugate,
evaluated at a vector's three readings of the triple.  Pure pair currency: three
pair minors, three cofactors, six readings. -/
noncomputable def pairAdjForm (a b c v : Fin 3 → ℝ) : ℝ :=
  pairGapMinor b c * (v ⬝ᵥ a) ^ 2
    + pairGapMinor a c * (v ⬝ᵥ b) ^ 2
    + pairGapMinor a b * (v ⬝ᵥ c) ^ 2
    + 2 * pairAdjOff a b c * ((v ⬝ᵥ a) * (v ⬝ᵥ b))
    + 2 * pairAdjOff a c b * ((v ⬝ᵥ a) * (v ⬝ᵥ c))
    + 2 * pairAdjOff b c a * ((v ⬝ᵥ b) * (v ⬝ᵥ c))

/-- The second invariant does not see the order of the triple. -/
theorem pairMinorTotal_swap_last (a b c : Fin 3 → ℝ) :
    pairMinorTotal a c b = pairMinorTotal a b c := by
  rw [pairMinorTotal, pairMinorTotal, pairGapMinor_comm c b]; ring

/-- The second invariant does not see a rotation of the triple. -/
theorem pairMinorTotal_rotate (a b c : Fin 3 → ℝ) :
    pairMinorTotal b c a = pairMinorTotal a b c := by
  rw [pairMinorTotal, pairMinorTotal, pairGapMinor_comm b a, pairGapMinor_comm c a]; ring

/-! ## 3. The off-diagonal law at a triple -/

/-- The reproduction with the last two members interchanged. -/
theorem nullProbe_reproduction_swap_last {a b c w : Fin 3 → ℝ}
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) :
    (a ⬝ᵥ w) • a + (c ⬝ᵥ w) • c + (b ⬝ᵥ w) • b = w := by
  rw [show ((a ⬝ᵥ w) • a + (c ⬝ᵥ w) • c + (b ⬝ᵥ w) • b)
      = ((a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c) from by abel]
  exact hrep

/-- The reproduction rotated. -/
theorem nullProbe_reproduction_rotate {a b c w : Fin 3 → ℝ}
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) :
    (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c + (a ⬝ᵥ w) • a = w := by
  rw [show ((b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c + (a ⬝ᵥ w) • a)
      = ((a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c) from by abel]
  exact hrep

/-- **THE OFF-DIAGONAL LAW, FIRST PAIR.**  The second invariant times the product
of the first two readings is the cofactor of that pair. -/
theorem pairMinorTotal_mul_readings_first (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairMinorTotal a b c * ((a ⬝ᵥ w) * (b ⬝ᵥ w)) = pairAdjOff a b c := by
  have hn : (a ⬝ᵥ w) ^ 2 + (b ⬝ᵥ w) ^ 2 + (c ⬝ᵥ w) ^ 2 = 1 := by
    rw [nullProbe_readings_resolve a b c w hrep]; exact hnorm
  have hcore := adjugate_offDiag_core (leverageOf a - 1) (leverageOf b - 1)
    (leverageOf c - 1) (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) (a ⬝ᵥ w) (b ⬝ᵥ w) (c ⬝ᵥ w)
    (nullProbe_row_first a b c w hrep)
    (nullProbe_row_second a b c w hrep)
    (nullProbe_row_third a b c w hrep) hn
  rw [pairMinorTotal, pairAdjOff, pairGapMinor, pairGapMinor, pairGapMinor]
  linear_combination -hcore

/-- **THE OFF-DIAGONAL LAW, SECOND PAIR.** -/
theorem pairMinorTotal_mul_readings_second (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairMinorTotal a b c * ((a ⬝ᵥ w) * (c ⬝ᵥ w)) = pairAdjOff a c b := by
  have h := pairMinorTotal_mul_readings_first a c b w
    (nullProbe_reproduction_swap_last hrep) hnorm
  rw [pairMinorTotal_swap_last] at h
  exact h

/-- **THE OFF-DIAGONAL LAW, THIRD PAIR.** -/
theorem pairMinorTotal_mul_readings_third (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairMinorTotal a b c * ((b ⬝ᵥ w) * (c ⬝ᵥ w)) = pairAdjOff b c a := by
  have h := pairMinorTotal_mul_readings_first b c a w
    (nullProbe_reproduction_rotate hrep) hnorm
  rw [pairMinorTotal_rotate] at h
  exact h

/-! ## 4. The probe elimination -/

/-- A vector reads the probe through its readings of the triple. -/
theorem dotProduct_probe_eq_readings (a b c w v : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) :
    v ⬝ᵥ w = (v ⬝ᵥ a) * (a ⬝ᵥ w) + (v ⬝ᵥ b) * (b ⬝ᵥ w) + (v ⬝ᵥ c) * (c ⬝ᵥ w) := by
  have h := congrArg (fun z => v ⬝ᵥ z) hrep
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  linear_combination -h

/-- **THE PROBE ELIMINATION.**  The second invariant times any vector's squared
reading of the null probe is the adjugate form at that vector's three readings
of the triple.  The right side contains no eigenvector: the probe has been
replaced by the triple's own pair minors and cofactors.

This is the statement that makes the corank-one arm's swap machine polynomial in
the design. -/
theorem pairMinorTotal_mul_reading_sq (a b c w v : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairMinorTotal a b c * (v ⬝ᵥ w) ^ 2 = pairAdjForm a b c v := by
  have hd1 := pairGapMinor_eq_pairMinorTotal_mul_reading_first a b c w hrep hnorm
  have hd2 := pairGapMinor_eq_pairMinorTotal_mul_reading_second a b c w hrep hnorm
  have hd3 := pairGapMinor_eq_pairMinorTotal_mul_reading_third a b c w hrep hnorm
  have ho1 := pairMinorTotal_mul_readings_first a b c w hrep hnorm
  have ho2 := pairMinorTotal_mul_readings_second a b c w hrep hnorm
  have ho3 := pairMinorTotal_mul_readings_third a b c w hrep hnorm
  rw [dotProduct_probe_eq_readings a b c w v hrep, pairAdjForm]
  linear_combination (-((v ⬝ᵥ a) ^ 2)) * hd1 + (-((v ⬝ᵥ b) ^ 2)) * hd2
    + (-((v ⬝ᵥ c) ^ 2)) * hd3
    + (2 * ((v ⬝ᵥ a) * (v ⬝ᵥ b))) * ho1 + (2 * ((v ⬝ᵥ a) * (v ⬝ᵥ c))) * ho2
    + (2 * ((v ⬝ᵥ b) * (v ⬝ᵥ c))) * ho3

/-- **THE FORM AT A MEMBER IS ITS OWN PAIR MINOR.**  The consistency check of the
elimination: the adjugate form evaluated at the first member returns the pair
minor of the other two. -/
theorem pairAdjForm_self (a b c w : Fin 3 → ℝ)
    (hrep : (a ⬝ᵥ w) • a + (b ⬝ᵥ w) • b + (c ⬝ᵥ w) • c = w) (hnorm : w ⬝ᵥ w = 1) :
    pairAdjForm a b c a = pairGapMinor b c := by
  rw [← pairMinorTotal_mul_reading_sq a b c w a hrep hnorm]
  exact (pairGapMinor_eq_pairMinorTotal_mul_reading_first a b c w hrep hnorm).symm

/-! ## 5. The swap census in pair currency -/

/-- **THE SWAP DEFECT IS A DIFFERENCE OF PAIR-CURRENCY POLYNOMIALS.**  The landed
`Gtz.swap_nullForm_of_null` prices a swap by two squared readings.  Multiplied by
the second invariant, both readings become pair data, and the probe disappears
from the price. -/
theorem pairMinorTotal_mul_swap_nullForm (D : WeightedDesign m 3)
    {x y z q : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : q ∉ ({x, y, z} : Finset (Fin m))) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ w = 0)
    (hnorm : w ⬝ᵥ w = 1) :
    pairMinorTotal (D.atom x) (D.atom y) (D.atom z)
        * (w ⬝ᵥ ((subsetSum D (insert q ((({x, y, z} : Finset (Fin m))).erase x)) - 1)
            *ᵥ w))
      = pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom q)
        - pairGapMinor (D.atom y) (D.atom z) := by
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hfix := mulVec_eq_of_gap_mulVec_eq_zero D _ hnull
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  have hform := swap_nullForm_of_null D hx hq hnull
  have hread := pairMinorTotal_mul_reading_sq (D.atom x) (D.atom y) (D.atom z) w
    (D.atom q) hrep hnorm
  have hdiag := pairGapMinor_eq_pairMinorTotal_mul_reading_first
    (D.atom x) (D.atom y) (D.atom z) w hrep hnorm
  rw [hform]
  linear_combination hread + hdiag

/-- **THE CENSUS IN PAIR CURRENCY.**  When the swap weakly dominates and the
shared pair is admissible, the adjugate form at the incoming atom is at least the
shared pair's minor.  No probe appears. -/
theorem pairGapMinor_le_pairAdjForm_of_dominates (D : WeightedDesign m 3)
    {x y z q : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : q ∉ ({x, y, z} : Finset (Fin m))) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ w = 0)
    (hnorm : w ⬝ᵥ w = 1)
    (hadm : 0 < pairGapMinor (D.atom y) (D.atom z))
    (hdom : Dominates D (insert q ((({x, y, z} : Finset (Fin m))).erase x))) :
    pairGapMinor (D.atom y) (D.atom z)
      ≤ pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom q) := by
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hfix := mulVec_eq_of_gap_mulVec_eq_zero D _ hnull
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  have hdiag := pairGapMinor_eq_pairMinorTotal_mul_reading_first
    (D.atom x) (D.atom y) (D.atom z) w hrep hnorm
  have htot : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
    nlinarith [sq_nonneg (D.atom x ⬝ᵥ w), hadm, hdiag]
  have hpsd := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 w
  rw [star_trivial] at hpsd
  have hswap := pairMinorTotal_mul_swap_nullForm D hxy hxz hyz hq hnull hnorm
  nlinarith [hswap, hpsd, htot]

/-! ## 6. The probe-free hinge trigger -/

/-- **THE HINGE TRIGGER, WITH NO PROBE.**  Let a triple weakly dominate with a
singular gap, let the swap at its first member weakly dominate too, and let the
shared pair be admissible.  If the adjugate form at the incoming atom EQUALS the
shared pair's minor, the design has a parallel pair.

Every hypothesis but the two dominations is a polynomial condition on leverages
and inner products.  This is the corank-one rigidity written in the currency the
hinge is stated in. -/
theorem hasParallelPair_of_pairAdjForm_eq (D : WeightedDesign m 3)
    {x y z q : Fin m} (hxq : x ≠ q) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : q ∉ ({x, y, z} : Finset (Fin m))) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ w = 0)
    (hnorm : w ⬝ᵥ w = 1)
    (hadm : 0 < pairGapMinor (D.atom y) (D.atom z))
    (hdom : Dominates D (insert q ((({x, y, z} : Finset (Fin m))).erase x)))
    (heq : pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom q)
      = pairGapMinor (D.atom y) (D.atom z)) :
    HasParallelPair D := by
  have hx : x ∈ ({x, y, z} : Finset (Fin m)) := by simp
  have hfix := mulVec_eq_of_gap_mulVec_eq_zero D _ hnull
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  have hdiag := pairGapMinor_eq_pairMinorTotal_mul_reading_first
    (D.atom x) (D.atom y) (D.atom z) w hrep hnorm
  have htot : 0 < pairMinorTotal (D.atom x) (D.atom y) (D.atom z) := by
    nlinarith [sq_nonneg (D.atom x ⬝ᵥ w), hadm, hdiag]
  -- the swap form vanishes, so the two exchanged atoms read the probe equally
  have hswap := pairMinorTotal_mul_swap_nullForm D hxy hxz hyz hq hnull hnorm
  rw [heq, sub_self] at hswap
  have hzeroForm : w ⬝ᵥ ((subsetSum D
      (insert q ((({x, y, z} : Finset (Fin m))).erase x)) - 1) *ᵥ w) = 0 := by
    rcases mul_eq_zero.mp hswap with h' | h'
    · exact absurd h' htot.ne'
    · exact h'
  have hreadeq : (D.atom x ⬝ᵥ w) ^ 2 = (D.atom q ⬝ᵥ w) ^ 2 := by
    have := swap_nullForm_of_null D hx hq hnull
    rw [hzeroForm] at this
    linarith
  -- the shared pair is admissible, so the common reading is not zero
  have hxread : (D.atom x ⬝ᵥ w) ^ 2 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdiag
    exact absurd hdiag hadm.ne'
  have hqread : D.atom q ⬝ᵥ w ≠ 0 := by
    intro h0
    rw [h0] at hreadeq
    exact hxread (by rw [hreadeq]; ring)
  exact hasParallelPair_of_mirror_dominators_of_readings_eq D hxq hx hq hnull hdom
    hreadeq hqread

/-- **THE CONSTRAINT A PRIMITIVE TIE MUST PAY.**  At a design with no parallel
pair, every dominating swap over an admissible shared pair satisfies a STRICT
polynomial inequality in leverages and inner products.  The census is never tight
on a primitive design. -/
theorem pairGapMinor_lt_pairAdjForm_of_not_hasParallelPair (D : WeightedDesign m 3)
    (hprim : ¬ HasParallelPair D) {x y z q : Fin m}
    (hxq : x ≠ q) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : q ∉ ({x, y, z} : Finset (Fin m))) {w : Fin 3 → ℝ}
    (hnull : (subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ w = 0)
    (hnorm : w ⬝ᵥ w = 1)
    (hadm : 0 < pairGapMinor (D.atom y) (D.atom z))
    (hdom : Dominates D (insert q ((({x, y, z} : Finset (Fin m))).erase x))) :
    pairGapMinor (D.atom y) (D.atom z)
      < pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom q) := by
  rcases (pairGapMinor_le_pairAdjForm_of_dominates D hxy hxz hyz hq hnull hnorm hadm
    hdom).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (hasParallelPair_of_pairAdjForm_eq D hxq hxy hxz hyz hq hnull hnorm
      hadm hdom heq.symm) hprim

/-! ## 7. The shared pair is the exchange rate between two probes -/

/-- **THE SHARED-PAIR TRANSFER.**  Two weak dominators over a common pair each
compute that pair's minor from their own null probe.  The shared pair minor is
the exchange rate between the two probes, and it is the only quantity both
dominators agree on without reference to an eigenvector. -/
theorem pairGapMinor_shared_transfer (D : WeightedDesign m 3)
    {x y z q : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hqy : q ≠ y) (hqz : q ≠ z) {w w' : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) (hnorm : w ⬝ᵥ w = 1)
    (hfix' : subsetSum D ({q, y, z} : Finset (Fin m)) *ᵥ w' = w')
    (hnorm' : w' ⬝ᵥ w' = 1) :
    pairMinorTotal (D.atom x) (D.atom y) (D.atom z) * (D.atom x ⬝ᵥ w) ^ 2
      = pairMinorTotal (D.atom q) (D.atom y) (D.atom z) * (D.atom q ⬝ᵥ w') ^ 2 := by
  obtain ⟨hfirst, -, -⟩ :=
    pairGapMinor_eq_pairMinorTotal_mul_reading_design D hxy hxz hyz hfix hnorm
  obtain ⟨hfirst', -, -⟩ :=
    pairGapMinor_eq_pairMinorTotal_mul_reading_design D hqy hqz hyz hfix' hnorm'
  rw [← hfirst, ← hfirst']

/-- **THE TRANSFER IS AN ADJUGATE-FORM IDENTITY.**  Written through the probe
elimination, the transfer says the two dominators' adjugate forms agree at their
own outgoing members. -/
theorem pairAdjForm_shared_transfer (D : WeightedDesign m 3)
    {x y z q : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hqy : q ≠ y) (hqz : q ≠ z) {w w' : Fin 3 → ℝ}
    (hfix : subsetSum D ({x, y, z} : Finset (Fin m)) *ᵥ w = w) (hnorm : w ⬝ᵥ w = 1)
    (hfix' : subsetSum D ({q, y, z} : Finset (Fin m)) *ᵥ w' = w')
    (hnorm' : w' ⬝ᵥ w' = 1) :
    pairAdjForm (D.atom x) (D.atom y) (D.atom z) (D.atom x)
      = pairAdjForm (D.atom q) (D.atom y) (D.atom z) (D.atom q) := by
  have hrep := nullProbe_reproduction_triple D hxy hxz hyz hfix
  have hrep' := nullProbe_reproduction_triple D hqy hqz hyz hfix'
  rw [pairAdjForm_self (D.atom x) (D.atom y) (D.atom z) w hrep hnorm,
    pairAdjForm_self (D.atom q) (D.atom y) (D.atom z) w' hrep' hnorm']

end Gtz
