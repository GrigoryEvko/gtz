/-
# The complexification test: what transports, and the exact step that does not

`Gtz/Complex/ComplexHingeRefutation.lean` shows that the campaign's hinge is FALSE
over `ℂ`, at rank two and at the target cell `(6,3)`.  Every instrument whose
ingredients all survive the passage to `ℂ` therefore admits
`Gtz.complexHingeSixDesign` as a feasible point and cannot prove
`Gtz.HingeHoldsAtSize 6 3`.  That makes one question worth ten minutes at the
start of every lane: does my route survive passage to `ℂ`?

This file is the apparatus for that question, applied to the campaign's largest
real engine, the rank-two tie classification of
`Gtz/Wave/RankTwoTieClassification.lean` and its rank-`k` budget in
`Gtz/Wave/CouplingRankBudget.lean`.  It transports the vocabulary, PROVES the
field-blind half over `ℂ`, and exhibits the first step that fails, with a
witness.

## PROVED HERE over `ℂ`, at every rank — the field-blind half

* `Gtz.sum_complexWeight_mul_complexLeverage` — `Sum_c t_c l_c = k`, the trace of
  Parseval.  The real twin is `Gtz.sum_weighted_leverage`.
* `Gtz.sum_complexWeight_mul_complexOverlap` — `Sum_d t_d |<g_c,g_d>| ^ 2 = l_c`,
  the row law of the squared Gram.  The real twin is
  `Gtz.sum_weight_mul_sq_atomPairing`.  Its proof is the same one line: the row is
  the quadratic form of Parseval at the atom.
* `Gtz.sum_complexVeroneseCoupling` — THE ROW LAW `Sum_d F_cd = t_c` of the
  rank-`k` coupling, over `ℂ`, at every rank.
* `Gtz.sum_complexWeight_mul_complexCouplingDiagFactor` — THE TRACE LAW
  `Sum_c t_c (1 - k (k - 1) + 2 (k - 1) l_c) = k ^ 2 - k + 1`, over `ℂ`, at every
  rank.
* `Gtz.complexLagrange` — Lagrange at rank two, `|<u,v>| ^ 2 + |J| ^ 2 = l_u l_v`
  with `J = u_0 v_1 - u_1 v_0`.  The real twin is
  `Gtz.sq_dotProduct_add_sq_planeWedge`.

So the whole of `Gtz/Wave/CouplingRankBudget.lean` is field-blind: its two laws
hold over `ℂ`, and its count `k ^ 2 - k + 1 <= m` is a consequence of those two
laws and of nonnegative entries alone.  A NO-GO needs no realness, and that one
consumes none.

## REFUTED HERE — the exact step that does not transport

The rank-two classification turns the two laws into a CLASSIFICATION by one more
step: the normalised coupling is an orthogonal projection, hence idempotent, hence
the relation `c ~ d :<-> F_cd > 0` is TRANSITIVE and its classes are the parallel
classes (`Gtz.tieCoupling_pos_trans`).  That step reads the Veronese
factorisation `F = R R^T - s s^T`, and `R` has THREE columns because
`dim_R Sym_2(R) = 3`.  Over `ℂ` the same factorisation needs FOUR columns, because
`dim_R Herm_2(C) = 4`, while the trace stays `2 k - 1 = 3`.  The trace sandwich
`Gtz.eq_of_trace_sandwich` then carries one dimension of slack.

`Gtz.not_complexCouplingPos_trans` lands the failure at
`Gtz.complexHingeDesign`, the `(4,2)` witness.  Its three relevant couplings are

    F_20 = 3/121 > 0 ,   F_03 = 3/121 > 0 ,   F_23 = 0 ,

so the relation is not transitive.  Over `ℝ` transitivity is a theorem at every
heavy design with no strictly dominating pair.  The witness has four pairwise
non-parallel atoms, so it has FOUR parallel classes where the real classification
proves exactly three, and that fourth class is the one dimension of slack.

The count itself is untouched: `3 = k ^ 2 - k + 1 <= 4 = m` holds at the witness,
which is why the count is a no-go and the classification is not.

## The `(6,3)` witness spends only the RANK-TWO extra dimension

`Gtz.complexHingeSixDesign` is BLOCK REDUCIBLE.  Its first five atoms have a
vanishing third coordinate and its sixth has vanishing first and second
coordinates (`Gtz.complexHingeSix_isCoordinateSplit`), so the atoms lie in the
`*`-subalgebra of `3 x 3` matrices with one `2 x 2` block and one `1 x 1` block.
The self-adjoint part of that subalgebra has real dimension `4 + 1 = 5` over `ℂ`
against `3 + 1 = 4` over `ℝ`, a difference of ONE.  Rank three offers a difference
of THREE, `9` against `6`.

`Gtz.complexHingeSixBargmann_eq_zero_of_spike` makes the same point in the
campaign's own coordinates: every Bargmann triple of the witness that contains the
spike VANISHES, because the spike is orthogonal to the other five atoms.  All the
phase defect of the `(6,3)` witness sits inside the five planar atoms, that is
inside a rank-TWO configuration.

**Consequence, stated plainly.**  The shipped `(6,3)` complex refutation consumes
only the rank-two realness dimension.  It exhibits no rank-three phase defect at
all.  An instrument that consumes the rank-THREE count, `5` against `8` on the
traceless part or `6` against `9` on the whole, is NOT refuted by any witness the
campaign owns.  Whether an irreducible complex `(6,3)` tie without a parallel pair
exists is open, and this file does not settle it.

## NOT PROVED HERE

* No complex analogue of the Laplacian step or of the leverage cap.  Those need a
  complex two-by-two positive-definiteness criterion, and the count above does not
  use them.
* Nothing about `Gtz.GtzWeighted 6 3` or about the real hinge.
* The dimensions `4 + 1` and `3 + 1` quoted above are cited from the shipped
  `Gtz.finrank_hermitianSubmodule` and `Gtz.two_mul_finrank_symmetricSubmodule`.
  The block submodule of `3 x 3` matrices is not built here, and its dimension is
  not mechanized.  What IS mechanized is the coordinate split that puts the atoms
  inside it.
-/
import Mathlib
import Gtz.Complex.ComplexWitness
import Gtz.Complex.ComplexHingeRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Complex

open scoped ComplexOrder

variable {m k : ℕ}

/-! ## Part A: the complex vocabulary -/

/-- The leverage of a complex atom. -/
noncomputable def complexLeverage (D : ComplexWeightedDesign m k) (atomIndex : Fin m) : ℂ :=
  star (D.atom atomIndex) ⬝ᵥ D.atom atomIndex

/-- The overlap of two complex atoms, `|<g_c, g_d>| ^ 2` written without a modulus:
the product of the two pairings, which is real and nonnegative. -/
noncomputable def complexOverlap (D : ComplexWeightedDesign m k)
    (atomFirst atomSecond : Fin m) : ℂ :=
  (star (D.atom atomFirst) ⬝ᵥ D.atom atomSecond)
    * (star (D.atom atomSecond) ⬝ᵥ D.atom atomFirst)

theorem complexOverlap_comm (D : ComplexWeightedDesign m k) (atomFirst atomSecond : Fin m) :
    complexOverlap D atomFirst atomSecond = complexOverlap D atomSecond atomFirst := by
  simp only [complexOverlap]; ring

theorem complexOverlap_self (D : ComplexWeightedDesign m k) (atomIndex : Fin m) :
    complexOverlap D atomIndex atomIndex = complexLeverage D atomIndex ^ 2 := by
  simp only [complexOverlap, complexLeverage]; ring

/-- The trace of a complex rank-one atom is its leverage. -/
theorem trace_complexAtom (vec : Fin k → ℂ) :
    Matrix.trace (complexAtom vec) = star vec ⬝ᵥ vec := by
  simp only [Matrix.trace, Matrix.diag_apply, complexAtom, Matrix.vecMulVec_apply,
    dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun index _ => by ring

/-- **THE COMPLEX TRACE READING OF PARSEVAL**, `Sum_c t_c l_c = k`.  The real twin
is `Gtz.sum_weighted_leverage`, and the proof is the same: take the trace of
Parseval. -/
theorem sum_complexWeight_mul_complexLeverage (D : ComplexWeightedDesign m k) :
    ∑ atomIndex, ((D.weight atomIndex : ℝ) : ℂ) * complexLeverage D atomIndex = (k : ℂ) := by
  have hcongr := congrArg Matrix.trace D.isParseval
  rw [Matrix.trace_sum, Matrix.trace_one, Fintype.card_fin] at hcongr
  rw [← hcongr]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [Matrix.trace_smul, trace_complexAtom, smul_eq_mul, complexLeverage]

/-- The overlap, read as a quadratic form of the second rank-one atom. -/
theorem complexOverlap_eq_dotProduct_complexAtom_mulVec (D : ComplexWeightedDesign m k)
    (atomFirst atomSecond : Fin m) :
    complexOverlap D atomFirst atomSecond
      = star (D.atom atomFirst) ⬝ᵥ (complexAtom (D.atom atomSecond) *ᵥ D.atom atomFirst) := by
  have hrow : complexAtom (D.atom atomSecond) *ᵥ D.atom atomFirst
      = (star (D.atom atomSecond) ⬝ᵥ D.atom atomFirst) • D.atom atomSecond := by
    funext coord
    simp only [complexAtom, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.star_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun other _ => by ring
  rw [hrow, dotProduct_smul, smul_eq_mul, complexOverlap]
  ring

/-- **THE COMPLEX ROW LAW OF THE SQUARED GRAM**, `Sum_d t_d |<g_c,g_d>| ^ 2 = l_c`.
The real twin is `Gtz.sum_weight_mul_sq_atomPairing`.  The row is the quadratic
form of Parseval at the atom, so the proof transports word for word. -/
theorem sum_complexWeight_mul_complexOverlap (D : ComplexWeightedDesign m k)
    (atomIndex : Fin m) :
    ∑ otherIndex, ((D.weight otherIndex : ℝ) : ℂ) * complexOverlap D atomIndex otherIndex
      = complexLeverage D atomIndex := by
  have hrewrite : ∀ otherIndex : Fin m,
      ((D.weight otherIndex : ℝ) : ℂ) * complexOverlap D atomIndex otherIndex
        = star (D.atom atomIndex)
            ⬝ᵥ ((((D.weight otherIndex : ℝ) : ℂ) • complexAtom (D.atom otherIndex))
              *ᵥ D.atom atomIndex) := by
    intro otherIndex
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← complexOverlap_eq_dotProduct_complexAtom_mulVec]
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) => hrewrite otherIndex,
    ← dotProduct_sum, ← Matrix.sum_mulVec, D.isParseval, Matrix.one_mulVec, complexLeverage]

/-! ## Part B: the rank-`k` coupling, over `ℂ` -/

/-- The complex diagonal factor, the transport of `Gtz.couplingDiagFactor`. -/
noncomputable def complexCouplingDiagFactor (rank : ℕ) (leverage : ℂ) : ℂ :=
  1 - (rank : ℂ) * ((rank : ℂ) - 1) + 2 * ((rank : ℂ) - 1) * leverage

/-- **The complex rank-`k` coupling**, the transport of `Gtz.veroneseCoupling` with
the squared pairing read as the overlap. -/
noncomputable def complexVeroneseCoupling (D : ComplexWeightedDesign m k)
    (atomFirst atomSecond : Fin m) : ℂ :=
  ((D.weight atomFirst : ℝ) : ℂ) * ((D.weight atomSecond : ℝ) : ℂ)
    * (1 - (k : ℂ) * ((k : ℂ) - 1)
        + ((k : ℂ) - 1) * (complexLeverage D atomFirst + complexLeverage D atomSecond)
        - complexLeverage D atomFirst * complexLeverage D atomSecond
        + complexOverlap D atomFirst atomSecond)

theorem complexVeroneseCoupling_comm (D : ComplexWeightedDesign m k)
    (atomFirst atomSecond : Fin m) :
    complexVeroneseCoupling D atomFirst atomSecond
      = complexVeroneseCoupling D atomSecond atomFirst := by
  simp only [complexVeroneseCoupling, complexOverlap_comm D atomFirst atomSecond]
  ring

theorem complexVeroneseCoupling_self (D : ComplexWeightedDesign m k) (atomIndex : Fin m) :
    complexVeroneseCoupling D atomIndex atomIndex
      = ((D.weight atomIndex : ℝ) : ℂ) ^ 2
        * complexCouplingDiagFactor k (complexLeverage D atomIndex) := by
  simp only [complexVeroneseCoupling, complexCouplingDiagFactor,
    complexOverlap_self D atomIndex]
  ring

/-- **THE ROW LAW TRANSPORTS.**  `Sum_d F_cd = t_c` over `ℂ`, at every rank and
with no hypothesis.  Compare `Gtz.sum_veroneseCoupling`: same statement, same three
Parseval sums, same proof. -/
theorem sum_complexVeroneseCoupling (D : ComplexWeightedDesign m k) (atomIndex : Fin m) :
    ∑ otherIndex, complexVeroneseCoupling D atomIndex otherIndex
      = ((D.weight atomIndex : ℝ) : ℂ) := by
  have hweights : ∑ otherIndex, ((D.weight otherIndex : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, D.weight_sum_one, Complex.ofReal_one]
  have hsplit : ∀ otherIndex : Fin m,
      complexVeroneseCoupling D atomIndex otherIndex
        = ((D.weight atomIndex : ℝ) : ℂ)
            * ((1 - (k : ℂ) * ((k : ℂ) - 1)
                  + ((k : ℂ) - 1) * complexLeverage D atomIndex)
                * ((D.weight otherIndex : ℝ) : ℂ)
              + (((k : ℂ) - 1) - complexLeverage D atomIndex)
                  * (((D.weight otherIndex : ℝ) : ℂ) * complexLeverage D otherIndex)
              + ((D.weight otherIndex : ℝ) : ℂ) * complexOverlap D atomIndex otherIndex) := by
    intro otherIndex
    simp only [complexVeroneseCoupling]
    ring
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) => hsplit otherIndex,
    ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hweights, sum_complexWeight_mul_complexLeverage D,
    sum_complexWeight_mul_complexOverlap D atomIndex]
  ring

/-- **THE TRACE LAW TRANSPORTS.**  `Sum_c t_c (1 - k (k - 1) + 2 (k - 1) l_c)
= k ^ 2 - k + 1` over `ℂ`, at every rank.  Compare
`Gtz.sum_weight_mul_couplingDiagFactor`. -/
theorem sum_complexWeight_mul_complexCouplingDiagFactor (D : ComplexWeightedDesign m k) :
    ∑ atomIndex, ((D.weight atomIndex : ℝ) : ℂ)
        * complexCouplingDiagFactor k (complexLeverage D atomIndex)
      = (k : ℂ) ^ 2 - (k : ℂ) + 1 := by
  have hweights : ∑ atomIndex, ((D.weight atomIndex : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, D.weight_sum_one, Complex.ofReal_one]
  have hsplit : ∀ atomIndex : Fin m,
      ((D.weight atomIndex : ℝ) : ℂ)
          * complexCouplingDiagFactor k (complexLeverage D atomIndex)
        = (1 - (k : ℂ) * ((k : ℂ) - 1)) * ((D.weight atomIndex : ℝ) : ℂ)
          + 2 * ((k : ℂ) - 1)
              * (((D.weight atomIndex : ℝ) : ℂ) * complexLeverage D atomIndex) := by
    intro atomIndex
    simp only [complexCouplingDiagFactor]
    ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hsplit atomIndex,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hweights,
    sum_complexWeight_mul_complexLeverage D]
  ring

/-! ## Part C: Lagrange at rank two, over `ℂ` -/

/-- The complex plane wedge, the determinant of the two atoms as columns. -/
noncomputable def complexPlaneWedge (leftVec rightVec : Fin 2 → ℂ) : ℂ :=
  leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0

/-- **LAGRANGE TRANSPORTS.**  `|<u,v>| ^ 2 + |J| ^ 2 = l_u l_v` at rank two over
`ℂ`.  The real twin is `Gtz.sq_dotProduct_add_sq_planeWedge`, and the wedge term
is the squared modulus rather than the square. -/
theorem complexLagrange (leftVec rightVec : Fin 2 → ℂ) :
    (star leftVec ⬝ᵥ rightVec) * (star rightVec ⬝ᵥ leftVec)
        + (starRingEnd ℂ) (complexPlaneWedge leftVec rightVec)
            * complexPlaneWedge leftVec rightVec
      = (star leftVec ⬝ᵥ leftVec) * (star rightVec ⬝ᵥ rightVec) := by
  simp only [complexPlaneWedge, dotProduct, Fin.sum_univ_two, Pi.star_apply, RCLike.star_def,
    map_sub, map_mul]
  ring

/-- The complex coupling at rank two, in wedge form: the transport of
`Gtz.tieCoupling`. -/
theorem complexVeroneseCoupling_rankTwo (D : ComplexWeightedDesign m 2)
    (atomFirst atomSecond : Fin m) :
    complexVeroneseCoupling D atomFirst atomSecond
      = ((D.weight atomFirst : ℝ) : ℂ) * ((D.weight atomSecond : ℝ) : ℂ)
        * (complexLeverage D atomFirst + complexLeverage D atomSecond - 1
            - (starRingEnd ℂ) (complexPlaneWedge (D.atom atomFirst) (D.atom atomSecond))
              * complexPlaneWedge (D.atom atomFirst) (D.atom atomSecond)) := by
  have hlagrange := complexLagrange (D.atom atomFirst) (D.atom atomSecond)
  simp only [complexVeroneseCoupling, complexOverlap, complexLeverage]
  push_cast
  linear_combination
    (((D.weight atomFirst : ℝ) : ℂ) * ((D.weight atomSecond : ℝ) : ℂ)) * hlagrange

/-! ## Part D: the step that does not transport -/

private theorem ofReal_pos_complex {value : ℝ} (hvalue : 0 < value) : (0 : ℂ) < (value : ℂ) := by
  rw [Complex.lt_def]
  simp [hvalue]

/-- The `(4,2)` witness has every leverage equal to two. -/
theorem complexHingeDesign_leverage (atomIndex : Fin 4) :
    complexLeverage complexHingeDesign atomIndex = 2 := by
  rw [complexLeverage]
  exact complexHingeNorm atomIndex

/-- The coupling of the pair `{2,0}` of the `(4,2)` witness. -/
theorem complexHingeCoupling_two_zero :
    complexVeroneseCoupling complexHingeDesign 2 0 = ((3 / 121 : ℝ) : ℂ) := by
  have hoverlap : complexOverlap complexHingeDesign 2 0 = 7 / 5 := complexHingeOv_two_zero
  simp only [complexVeroneseCoupling, complexHingeDesign_leverage, hoverlap]
  show ((complexHingeWeight 2 : ℝ) : ℂ) * ((complexHingeWeight 0 : ℝ) : ℂ)
      * (1 - (2 : ℂ) * ((2 : ℂ) - 1) + ((2 : ℂ) - 1) * (2 + 2) - 2 * 2 + 7 / 5)
    = ((3 / 121 : ℝ) : ℂ)
  simp only [complexHingeWeight, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  push_cast
  norm_num

/-- The coupling of the pair `{0,3}` of the `(4,2)` witness. -/
theorem complexHingeCoupling_zero_three :
    complexVeroneseCoupling complexHingeDesign 0 3 = ((3 / 121 : ℝ) : ℂ) := by
  have hoverlap : complexOverlap complexHingeDesign 0 3 = 7 / 5 := complexHingeOv_zero_three
  simp only [complexVeroneseCoupling, complexHingeDesign_leverage, hoverlap]
  show ((complexHingeWeight 0 : ℝ) : ℂ) * ((complexHingeWeight 3 : ℝ) : ℂ)
      * (1 - (2 : ℂ) * ((2 : ℂ) - 1) + ((2 : ℂ) - 1) * (2 + 2) - 2 * 2 + 7 / 5)
    = ((3 / 121 : ℝ) : ℂ)
  simp only [complexHingeWeight, Matrix.cons_val_zero, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_cons, Matrix.cons_val_one]
  push_cast
  norm_num

/-- The coupling of the pair `{2,3}` of the `(4,2)` witness VANISHES. -/
theorem complexHingeCoupling_two_three :
    complexVeroneseCoupling complexHingeDesign 2 3 = 0 := by
  have hoverlap : complexOverlap complexHingeDesign 2 3 = 1 := complexHingeOv_two_three
  simp only [complexVeroneseCoupling, complexHingeDesign_leverage, hoverlap]
  ring

/-- **THE STEP THAT DOES NOT TRANSPORT.**  Over `ℝ` the relation `F_cd > 0` is
TRANSITIVE at every heavy rank-two design with no strictly dominating pair
(`Gtz.tieCoupling_pos_trans`), because the normalised coupling is an idempotent.
Over `ℂ` it is not: at `Gtz.complexHingeDesign` the atom `0` couples strictly to
both `2` and `3`, and `2` does not couple to `3`.

The rank-two proof of transitivity reads the Veronese factorisation, whose matrix
has THREE columns because `dim_R Sym_2(R) = 3`.  Over `ℂ` it needs FOUR, because
`dim_R Herm_2(C) = 4`, while the trace stays `2 k - 1 = 3`.  The witness lives in
that one dimension of slack, and it has FOUR parallel classes. -/
theorem not_complexCouplingPos_trans :
    ¬ ∀ atomFirst atomMiddle atomLast : Fin 4,
        0 < complexVeroneseCoupling complexHingeDesign atomFirst atomMiddle →
        0 < complexVeroneseCoupling complexHingeDesign atomMiddle atomLast →
        0 < complexVeroneseCoupling complexHingeDesign atomFirst atomLast := by
  intro htrans
  have hone : (0 : ℂ) < complexVeroneseCoupling complexHingeDesign 2 0 := by
    rw [complexHingeCoupling_two_zero]
    exact ofReal_pos_complex (by norm_num)
  have htwo : (0 : ℂ) < complexVeroneseCoupling complexHingeDesign 0 3 := by
    rw [complexHingeCoupling_zero_three]
    exact ofReal_pos_complex (by norm_num)
  have hthree := htrans 2 0 3 hone htwo
  rw [complexHingeCoupling_two_three] at hthree
  exact lt_irrefl 0 hthree

/-- **The count is untouched.**  The trace law at the `(4,2)` witness reads
`3 = k ^ 2 - k + 1`, and the witness has four atoms, so the count
`k ^ 2 - k + 1 <= m` of `Gtz.rankPolynomial_le_size` is satisfied over `ℂ`.  The
count is a no-go and survives the passage; the classification does not. -/
theorem complexHingeDesign_traceLaw :
    ∑ atomIndex, ((complexHingeDesign.weight atomIndex : ℝ) : ℂ)
        * complexCouplingDiagFactor 2 (complexLeverage complexHingeDesign atomIndex)
      = 3 := by
  rw [sum_complexWeight_mul_complexCouplingDiagFactor complexHingeDesign]
  push_cast
  norm_num

/-! ## Part E: the `(6,3)` witness spends only the rank-two dimension -/

/-- A design of rank three splits along the coordinate `2` when every atom either
has a vanishing third coordinate or has vanishing first and second coordinates.
Such a design lies in the `*`-subalgebra with one `2 x 2` block and one `1 x 1`
block, so it is REDUCIBLE and carries no irreducible rank-three information. -/
def IsCoordinateSplit {size : ℕ} (D : ComplexWeightedDesign size 3) : Prop :=
  ∀ atomIndex : Fin size,
    D.atom atomIndex 2 = 0 ∨ (D.atom atomIndex 0 = 0 ∧ D.atom atomIndex 1 = 0)

/-- **THE `(6,3)` WITNESS IS BLOCK REDUCIBLE.**  Its first five atoms are planar
and its sixth is the spike. -/
theorem complexHingeSix_isCoordinateSplit : IsCoordinateSplit complexHingeSixDesign := by
  intro atomIndex
  fin_cases atomIndex
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rfl⟩

/-- The Bargmann triangle invariant of three complex atoms.  Over `ℝ` its square is
the product of the three overlaps; over `ℂ` the deficit is the squared imaginary
part, and that deficit is the whole phase defect (`Gtz.PhaseFreeData.triangleCap`). -/
noncomputable def complexBargmann (D : ComplexWeightedDesign m k)
    (atomFirst atomSecond atomThird : Fin m) : ℂ :=
  (star (D.atom atomFirst) ⬝ᵥ D.atom atomSecond)
    * (star (D.atom atomSecond) ⬝ᵥ D.atom atomThird)
    * (star (D.atom atomThird) ⬝ᵥ D.atom atomFirst)

/-- **EVERY BARGMANN TRIPLE OF THE `(6,3)` WITNESS THAT MEETS THE SPIKE VANISHES.**
The spike is orthogonal to the other five atoms, so a triple containing it carries
a zero factor.  All the phase defect of the witness therefore sits inside the five
PLANAR atoms, which is a rank-two configuration.

This is the precise sense in which the `(6,3)` refutation spends only the rank-two
extra dimension `dim_R Herm_2(C) - dim_R Sym_2(R) = 1`, and none of the three that
rank three offers. -/
theorem complexHingeSixBargmann_eq_zero_of_spike (atomFirst atomSecond atomThird : Fin 6)
    (hspike : atomFirst = 5 ∨ atomSecond = 5 ∨ atomThird = 5)
    (hdistinctFirst : atomFirst ≠ atomSecond) (hdistinctSecond : atomSecond ≠ atomThird)
    (hdistinctThird : atomThird ≠ atomFirst) :
    complexBargmann complexHingeSixDesign atomFirst atomSecond atomThird = 0 := by
  show (star (complexHingeSixAtom atomFirst) ⬝ᵥ complexHingeSixAtom atomSecond)
      * (star (complexHingeSixAtom atomSecond) ⬝ᵥ complexHingeSixAtom atomThird)
      * (star (complexHingeSixAtom atomThird) ⬝ᵥ complexHingeSixAtom atomFirst) = 0
  rcases hspike with hfirst | hsecond | hthird
  · subst hfirst
    rw [complexHingeSixOrth' atomSecond (Ne.symm hdistinctFirst)]
    ring
  · subst hsecond
    rw [complexHingeSixOrth atomFirst hdistinctFirst]
    ring
  · subst hthird
    rw [complexHingeSixOrth atomSecond hdistinctSecond]
    ring

/-- **THE LEDGER, in one statement.**  The two laws of the rank-`k` coupling hold
over `ℂ` at every rank, and the transitivity that turns them into the rank-two
classification does not. -/
theorem complexTransportLedger :
    (∀ D : ComplexWeightedDesign m k, ∀ atomIndex : Fin m,
        ∑ otherIndex, complexVeroneseCoupling D atomIndex otherIndex
          = ((D.weight atomIndex : ℝ) : ℂ))
      ∧ (∀ D : ComplexWeightedDesign m k,
        ∑ atomIndex, ((D.weight atomIndex : ℝ) : ℂ)
            * complexCouplingDiagFactor k (complexLeverage D atomIndex)
          = (k : ℂ) ^ 2 - (k : ℂ) + 1)
      ∧ ¬ ∀ atomFirst atomMiddle atomLast : Fin 4,
          0 < complexVeroneseCoupling complexHingeDesign atomFirst atomMiddle →
          0 < complexVeroneseCoupling complexHingeDesign atomMiddle atomLast →
          0 < complexVeroneseCoupling complexHingeDesign atomFirst atomLast :=
  ⟨fun D atomIndex => sum_complexVeroneseCoupling D atomIndex,
    fun D => sum_complexWeight_mul_complexCouplingDiagFactor D,
    not_complexCouplingPos_trans⟩

end Gtz
