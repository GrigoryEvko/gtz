/-
# The coupling budget: why the rank-two Laplacian route stops at rank two

`Gtz/Wave/RankTwoTieClassification.lean` proves the whole rank-two tie
classification from one matrix, the coupling

    F_cd = t_c t_d (l_c + l_d - 1 - J_cd ^ 2)     (`Gtz.tieCoupling`),

through three facts: the row law `Sum_d F_cd = t_c`, the Laplacian step (a
symmetric matrix with nonnegative entries and row sums `t` makes `diag t - F`
positive semidefinite), and a trace sandwich that identifies the normalised
coupling with a projection.  That file records that nothing lifts to rank three,
and it names the measured obstruction: at the `(5,3)` diamond a candidate
rank-three matrix has a diagonal entry larger than its row sum.

This file replaces the measurement by a theorem.  It builds the rank-`k`
coupling, proves the row law and the trace law at EVERY rank, and shows that the
entrywise nonnegativity the Laplacian step needs is IMPOSSIBLE at rank three,
at the two sizes that decide the campaign.

## The rank-`k` coupling, and why it is the only candidate

Ask for a coupling of the shape `F_cd = t_c t_d Phi(l_c, l_d, P_cd ^ 2)` with
`Phi` symmetric.  Parseval supplies exactly three sums of a design:

    Sum_d t_d = 1 ,  Sum_d t_d l_d = k ,  Sum_d t_d P_cd ^ 2 = l_c .

A row sum of `F` is therefore available only when `Phi` is affine in `l_d` and in
`P_cd ^ 2` separately.  `Gtz.sum_familyCoupling` computes that row sum for the
full four-parameter family `Phi = a + b (l_c + l_d) + e l_c l_d + c P_cd ^ 2`:

    Sum_d F_cd = t_c ((a + b k) + l_c (b + e k + c)) .

Three normalizations pin the family to one member.

* The row law `Sum_d F_cd = t_c` forces `a + b k = 1` and `b + e k + c = 0`.
* The diagonal is `F_cc = t_c ^ 2 (a + 2 b l_c + (e + c) l_c ^ 2)`, so the trace
  `Sum_c F_cc / t_c` is a Parseval invariant only when `e + c = 0`.
* The coefficient of `P_cd ^ 2` is the scale of the Veronese Gram, and `c = 1`
  is its natural value.

The three give `e = -1`, `b = k - 1` and `a = 1 - k (k - 1)`, which is
`Gtz.veroneseCoupling`.  At `k = 2` it is the shipped coupling, character for
character: `Gtz.veroneseCoupling_eq_tieCoupling`.

## The two laws, and the count

`Gtz.sum_veroneseCoupling` is the row law at every rank.  The diagonal factor is
`Gtz.couplingDiagFactor k l = 1 - k (k - 1) + 2 (k - 1) l`, and
`Gtz.sum_weight_mul_couplingDiagFactor` is the trace law:

    Sum_c t_c (1 - k (k - 1) + 2 (k - 1) l_c) = k ^ 2 - k + 1 .

At `k = 2` that constant is `3`, the shipped `2 k - 1`.  At `k = 3` it is SEVEN.

Nonnegative entries make each diagonal entry at most its own row sum, so each
term of the trace law is at most one.  A sum of `m` terms, each at most one, is
at most `m`.  That is `Gtz.rankPolynomial_le_size`:

    k ^ 2 - k + 1 <= m .

At rank three the count reads `7 <= m`, so a `(6,3)` design CANNOT have a
nonnegative coupling: `Gtz.exists_veroneseCoupling_neg_sixThree`.

## The sharpening at size seven

Size seven survives the count, and a second argument removes it.  Seven rank-one
symmetric `3 x 3` matrices are dependent, because `dim_R Sym_3(R) = 6`, and the
shipped `Gtz.exists_parsevalNullDirection` supplies the dependency.  A dependency
`Sum_c s_c g_c g_c^T = 0` is a NULL DIRECTION of the coupling:
`Gtz.dotProduct_couplingMatrix_mulVec_nonpos_of_stress` shows that the quadratic
form of the coupling at such a direction is `(1 - k (k - 1)) (Sum_c s_c) ^ 2`,
which is at most zero at every rank `k` of two or more.  The three cross terms
all carry a factor of the dependency and vanish.

`Gtz.one_le_sum_diag_div_of_formNonneg` then converts one null direction into one
unit of trace.  Its proof is two applications of the Cauchy-Schwarz inequality
for a nonnegative form and no square root: the entry bound
`((F x)_c) ^ 2 <= F_cc (x . F x)` comes from
`Gtz.FormNonneg.sq_dotProduct_mulVec_le`, and one arithmetic-geometric step per
index assembles it.  The result is `Gtz.rankPolynomial_add_one_le_size_of_stress`:

    k ^ 2 - k + 1 + 1 <= m .

At rank three that is `8 <= m`, so a `(7,3)` design cannot have a nonnegative
coupling either: `Gtz.exists_veroneseCoupling_neg_sevenThree`.  Size seven
decides all of rank three
(`Gtz.discriminantCovering_seven_iff_rank_three`), so the route is closed at the
cell that matters.

## The arithmetic behind the whole file

`Gtz.rankPolynomial_le_symmetricDimension_iff` is the one line that explains why
rank two is special.  The Veronese image of the atoms lives in the symmetric
`k x k` matrices, of dimension `k (k + 1) / 2`, and the trace law asks for
`k ^ 2 - k + 1`.  The two agree exactly when

    2 (k ^ 2 - k + 1) <= k (k + 1) ,  that is  k ^ 2 + 2 <= 3 k ,  that is  k <= 2 .

At `k = 2` the two numbers are `3` and `3`.  At `k = 3` they are `7` and `6`.
The deficit is one, and the file shows that one is enough.

## What this file does NOT claim

* It says nothing about `Gtz.GtzWeighted 6 3` or the hinge.  It closes ONE
  route, and a closed route is not a theorem about designs.
* The count is proved for the canonical member of the family only.  The
  uniqueness argument above is prose plus `Gtz.sum_familyCoupling`, which
  mechanizes the row-sum half of it.  Design-independence of the trace is not
  mechanized as a quantifier statement.
* Sizes of eight or more at rank three are NOT covered.  One null direction buys
  one unit of trace, and `m - 6` orthonormal null directions would buy `m - 6`,
  which would close every size.  That family is not built here.
* Every statement below is FIELD-BLIND.  Each ingredient is a Parseval sum or a
  real quadratic form, and the same count holds over the complex numbers with
  `P_cd ^ 2` read as the squared modulus.  A no-go needs no realness, and this
  one consumes none.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Quantitative.ChartHadamard
import Gtz.Reduction.StressWalk
import Gtz.Wave.RankTwoTieClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part A: the family, and the row sum that pins it -/

/-- The leverage of an atom is the dot product of the atom with itself. -/
theorem leverageOf_eq_self_dotProduct (vec : Fin k → ℝ) : leverageOf vec = vec ⬝ᵥ vec := by
  simp only [leverageOf, dotProduct, sq]

/-- **The row sum of the four-parameter family.**  For every choice of the four
coefficients the row sum of `t_c t_d (a + b (l_c + l_d) + e l_c l_d + c P_cd ^ 2)`
is `t_c ((a + b k) + l_c (b + e k + c))`.  Three Parseval sums and nothing else,
so the row law `Sum_d = t_c` holds exactly when `a + b k = 1` and
`b + e k + c = 0`. -/
theorem sum_familyCoupling (D : WeightedDesign m k)
    (constTerm linearTerm productTerm pairingTerm : ℝ) (atomIndex : Fin m) :
    ∑ otherIndex, D.weight atomIndex * D.weight otherIndex
        * (constTerm
            + linearTerm * (leverageOf (D.atom atomIndex) + leverageOf (D.atom otherIndex))
            + productTerm * (leverageOf (D.atom atomIndex) * leverageOf (D.atom otherIndex))
            + pairingTerm * (D.atom atomIndex ⬝ᵥ D.atom otherIndex) ^ 2)
      = D.weight atomIndex
          * ((constTerm + linearTerm * (k : ℝ))
              + leverageOf (D.atom atomIndex)
                  * (linearTerm + productTerm * (k : ℝ) + pairingTerm)) := by
  have hsplit : ∀ otherIndex : Fin m,
      D.weight atomIndex * D.weight otherIndex
          * (constTerm
              + linearTerm * (leverageOf (D.atom atomIndex) + leverageOf (D.atom otherIndex))
              + productTerm * (leverageOf (D.atom atomIndex) * leverageOf (D.atom otherIndex))
              + pairingTerm * (D.atom atomIndex ⬝ᵥ D.atom otherIndex) ^ 2)
        = D.weight atomIndex
            * ((constTerm + linearTerm * leverageOf (D.atom atomIndex)) * D.weight otherIndex
              + (linearTerm + productTerm * leverageOf (D.atom atomIndex))
                  * (D.weight otherIndex * leverageOf (D.atom otherIndex))
              + pairingTerm
                  * (D.weight otherIndex * (D.atom atomIndex ⬝ᵥ D.atom otherIndex) ^ 2)) := by
    intro otherIndex; ring
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) => hsplit otherIndex,
    ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, D.weight_sum_one, sum_weighted_leverage D,
    sum_weight_mul_sq_atomPairing D atomIndex]
  ring

/-! ## Part B: the canonical coupling -/

/-- **The diagonal factor** `1 - k (k - 1) + 2 (k - 1) l`.  At `k = 2` it is
`2 l - 1`, the factor of the shipped rank-two diagonal. -/
noncomputable def couplingDiagFactor (rank : ℕ) (leverage : ℝ) : ℝ :=
  1 - (rank : ℝ) * ((rank : ℝ) - 1) + 2 * ((rank : ℝ) - 1) * leverage

@[simp] theorem couplingDiagFactor_two (leverage : ℝ) :
    couplingDiagFactor 2 leverage = 2 * leverage - 1 := by
  simp only [couplingDiagFactor]
  push_cast
  ring

/-- **The rank-`k` coupling.**  The unique member of the family whose row sums are
the weights, whose trace is a Parseval invariant, and whose `P_cd ^ 2` coefficient
is one. -/
noncomputable def veroneseCoupling (D : WeightedDesign m k) (atomFirst atomSecond : Fin m) : ℝ :=
  D.weight atomFirst * D.weight atomSecond
    * (1 - (k : ℝ) * ((k : ℝ) - 1)
        + ((k : ℝ) - 1) * (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond))
        - leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond)
        + (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2)

theorem veroneseCoupling_comm (D : WeightedDesign m k) (atomFirst atomSecond : Fin m) :
    veroneseCoupling D atomFirst atomSecond = veroneseCoupling D atomSecond atomFirst := by
  simp only [veroneseCoupling, dotProduct_comm (D.atom atomFirst) (D.atom atomSecond)]
  ring

/-- **The diagonal**, `F_cc = t_c ^ 2 (1 - k (k - 1) + 2 (k - 1) l_c)`.  The two
`l_c ^ 2` terms cancel, and that cancellation is what makes the trace below a
Parseval invariant. -/
theorem veroneseCoupling_self (D : WeightedDesign m k) (atomIndex : Fin m) :
    veroneseCoupling D atomIndex atomIndex
      = D.weight atomIndex ^ 2 * couplingDiagFactor k (leverageOf (D.atom atomIndex)) := by
  simp only [veroneseCoupling, couplingDiagFactor,
    ← leverageOf_eq_self_dotProduct (D.atom atomIndex)]
  ring

/-- **THE ROW LAW**, at every rank and with no hypothesis: `Sum_d F_cd = t_c`.
Three Parseval sums, through `Gtz.sum_familyCoupling`. -/
theorem sum_veroneseCoupling (D : WeightedDesign m k) (atomIndex : Fin m) :
    ∑ otherIndex, veroneseCoupling D atomIndex otherIndex = D.weight atomIndex := by
  have hfamily := sum_familyCoupling D (1 - (k : ℝ) * ((k : ℝ) - 1)) ((k : ℝ) - 1) (-1) 1 atomIndex
  have hshape : ∀ otherIndex : Fin m,
      D.weight atomIndex * D.weight otherIndex
          * ((1 - (k : ℝ) * ((k : ℝ) - 1))
              + ((k : ℝ) - 1) * (leverageOf (D.atom atomIndex) + leverageOf (D.atom otherIndex))
              + (-1) * (leverageOf (D.atom atomIndex) * leverageOf (D.atom otherIndex))
              + 1 * (D.atom atomIndex ⬝ᵥ D.atom otherIndex) ^ 2)
        = veroneseCoupling D atomIndex otherIndex := by
    intro otherIndex; simp only [veroneseCoupling]; ring
  rw [Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) => hshape otherIndex]
    at hfamily
  rw [hfamily]
  ring

/-- **THE TRACE LAW**, at every rank and with no hypothesis:
`Sum_c t_c (1 - k (k - 1) + 2 (k - 1) l_c) = k ^ 2 - k + 1`.  Two Parseval sums.
At `k = 2` the constant is `3`, at `k = 3` it is `7`. -/
theorem sum_weight_mul_couplingDiagFactor (D : WeightedDesign m k) :
    ∑ atomIndex, D.weight atomIndex * couplingDiagFactor k (leverageOf (D.atom atomIndex))
      = (k : ℝ) ^ 2 - (k : ℝ) + 1 := by
  have hsplit : ∀ atomIndex : Fin m,
      D.weight atomIndex * couplingDiagFactor k (leverageOf (D.atom atomIndex))
        = (1 - (k : ℝ) * ((k : ℝ) - 1)) * D.weight atomIndex
          + 2 * ((k : ℝ) - 1) * (D.weight atomIndex * leverageOf (D.atom atomIndex)) := by
    intro atomIndex; simp only [couplingDiagFactor]; ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hsplit atomIndex,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, D.weight_sum_one,
    sum_weighted_leverage D]
  ring

/-- **The bridge to rank two.**  At `k = 2` the canonical coupling IS the shipped
`Gtz.tieCoupling`, by Lagrange: `P_cd ^ 2 + J_cd ^ 2 = l_c l_d`. -/
theorem veroneseCoupling_eq_tieCoupling (D : WeightedDesign m 2) (atomFirst atomSecond : Fin m) :
    veroneseCoupling D atomFirst atomSecond = tieCoupling D atomFirst atomSecond := by
  have hlagrange := sq_dotProduct_add_sq_planeWedge (D.atom atomFirst) (D.atom atomSecond)
  simp only [veroneseCoupling, tieCoupling]
  push_cast
  linear_combination (D.weight atomFirst * D.weight atomSecond) * hlagrange

/-! ## Part C: nonnegative entries force a count -/

/-- The diagonal entry never exceeds its own row sum. -/
theorem veroneseCoupling_self_le_weight (D : WeightedDesign m k)
    (hnonneg : ∀ atomFirst atomSecond : Fin m, 0 ≤ veroneseCoupling D atomFirst atomSecond)
    (atomIndex : Fin m) :
    veroneseCoupling D atomIndex atomIndex ≤ D.weight atomIndex := by
  have hsingle : veroneseCoupling D atomIndex atomIndex
      ≤ ∑ otherIndex, veroneseCoupling D atomIndex otherIndex :=
    Finset.single_le_sum (fun otherIndex _ => hnonneg atomIndex otherIndex)
      (Finset.mem_univ atomIndex)
  rwa [sum_veroneseCoupling D atomIndex] at hsingle

/-- **THE PER-ATOM CAP**, `t_c (1 - k (k - 1) + 2 (k - 1) l_c) <= 1`.  At `k = 2`
this is the shipped `Gtz.weight_mul_two_leverage_sub_one_le_one`, and the proof is
the same three lines: the diagonal is one term of a row whose total is `t_c`. -/
theorem weight_mul_couplingDiagFactor_le_one (D : WeightedDesign m k)
    (hnonneg : ∀ atomFirst atomSecond : Fin m, 0 ≤ veroneseCoupling D atomFirst atomSecond)
    (atomIndex : Fin m) :
    D.weight atomIndex * couplingDiagFactor k (leverageOf (D.atom atomIndex)) ≤ 1 := by
  have hdiag := veroneseCoupling_self_le_weight D hnonneg atomIndex
  rw [veroneseCoupling_self] at hdiag
  have hweight := D.weight_pos atomIndex
  nlinarith [hdiag, hweight]

/-- **THE COUNT.**  A design whose coupling has no negative entry carries at least
`k ^ 2 - k + 1` atoms.  The trace law is a sum of `m` terms, each capped at one. -/
theorem rankPolynomial_le_size (D : WeightedDesign m k)
    (hnonneg : ∀ atomFirst atomSecond : Fin m, 0 ≤ veroneseCoupling D atomFirst atomSecond) :
    (k : ℝ) ^ 2 - (k : ℝ) + 1 ≤ (m : ℝ) := by
  have htrace := sum_weight_mul_couplingDiagFactor D
  have hcap : ∑ atomIndex : Fin m,
      D.weight atomIndex * couplingDiagFactor k (leverageOf (D.atom atomIndex))
        ≤ ∑ _atomIndex : Fin m, (1 : ℝ) :=
    Finset.sum_le_sum fun atomIndex _ => weight_mul_couplingDiagFactor_le_one D hnonneg atomIndex
  rw [htrace, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcap
  exact hcap

/-! ## Part D: the coupling as a matrix, and its Laplacian -/

/-- The coupling, as an `m x m` matrix. -/
noncomputable def couplingMatrix (D : WeightedDesign m k) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun atomFirst atomSecond => veroneseCoupling D atomFirst atomSecond

@[simp] theorem couplingMatrix_apply (D : WeightedDesign m k) (atomFirst atomSecond : Fin m) :
    couplingMatrix D atomFirst atomSecond = veroneseCoupling D atomFirst atomSecond := rfl

theorem couplingMatrix_transpose (D : WeightedDesign m k) :
    (couplingMatrix D)ᵀ = couplingMatrix D := by
  ext atomFirst atomSecond
  simp only [Matrix.transpose_apply, couplingMatrix_apply]
  exact veroneseCoupling_comm D atomSecond atomFirst

/-- **The Laplacian identity at every rank.**  The Dirichlet form of
`diag t - F` is the edge sum.  The rank-two case is the shipped
`Gtz.laplacian_identity`, and only the row law is used. -/
theorem laplacian_identity_veroneseCoupling (D : WeightedDesign m k) (probe : Fin m → ℝ) :
    (∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2)
        - ∑ atomIndex, ∑ otherIndex,
            probe atomIndex * (veroneseCoupling D atomIndex otherIndex * probe otherIndex)
      = (1 / 2) * ∑ atomIndex, ∑ otherIndex,
          veroneseCoupling D atomIndex otherIndex * (probe atomIndex - probe otherIndex) ^ 2 := by
  have hrowFirst : ∑ atomIndex, ∑ otherIndex,
      veroneseCoupling D atomIndex otherIndex * probe atomIndex ^ 2
        = ∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2 := by
    refine Finset.sum_congr rfl fun atomIndex _ => ?_
    rw [← Finset.sum_mul, sum_veroneseCoupling D atomIndex]
  have hrowSecond : ∑ atomIndex, ∑ otherIndex,
      veroneseCoupling D atomIndex otherIndex * probe otherIndex ^ 2
        = ∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun otherIndex _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    rw [← sum_veroneseCoupling D otherIndex]
    exact Finset.sum_congr rfl fun atomIndex _ => veroneseCoupling_comm D atomIndex otherIndex
  have hexpand : ∀ atomIndex otherIndex : Fin m,
      veroneseCoupling D atomIndex otherIndex * (probe atomIndex - probe otherIndex) ^ 2
        = veroneseCoupling D atomIndex otherIndex * probe atomIndex ^ 2
          + veroneseCoupling D atomIndex otherIndex * probe otherIndex ^ 2
          - 2 * (probe atomIndex
              * (veroneseCoupling D atomIndex otherIndex * probe otherIndex)) :=
    fun _ _ => by ring
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) =>
    Finset.sum_congr rfl fun otherIndex (_ : otherIndex ∈ Finset.univ) =>
      hexpand atomIndex otherIndex]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hrowFirst, hrowSecond]
  ring

theorem dotProduct_couplingMatrix_mulVec (D : WeightedDesign m k) (probe : Fin m → ℝ) :
    probe ⬝ᵥ (couplingMatrix D *ᵥ probe)
      = ∑ atomIndex, ∑ otherIndex,
          probe atomIndex * (veroneseCoupling D atomIndex otherIndex * probe otherIndex) := by
  simp only [dotProduct, Matrix.mulVec, couplingMatrix_apply, Finset.mul_sum]

theorem dotProduct_diagonal_mulVec (weightVec probe : Fin m → ℝ) :
    probe ⬝ᵥ (Matrix.diagonal weightVec *ᵥ probe)
      = ∑ atomIndex, weightVec atomIndex * probe atomIndex ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun atomIndex _ => by ring

/-- **The Laplacian step at every rank.**  Nonnegative entries and the row law make
`diag t - F` a nonnegative form. -/
theorem formNonneg_diagonal_sub_couplingMatrix (D : WeightedDesign m k)
    (hnonneg : ∀ atomFirst atomSecond : Fin m, 0 ≤ veroneseCoupling D atomFirst atomSecond) :
    FormNonneg (Matrix.diagonal D.weight - couplingMatrix D) := by
  intro probe
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_diagonal_mulVec,
    dotProduct_couplingMatrix_mulVec, laplacian_identity_veroneseCoupling D probe]
  have hterms : (0 : ℝ) ≤ ∑ atomIndex, ∑ otherIndex,
      veroneseCoupling D atomIndex otherIndex * (probe atomIndex - probe otherIndex) ^ 2 :=
    Finset.sum_nonneg fun atomIndex _ => Finset.sum_nonneg fun otherIndex _ =>
      mul_nonneg (hnonneg atomIndex otherIndex) (sq_nonneg _)
  linarith

theorem transpose_diagonal_sub_couplingMatrix (D : WeightedDesign m k) :
    (Matrix.diagonal D.weight - couplingMatrix D)ᵀ = Matrix.diagonal D.weight - couplingMatrix D := by
  rw [Matrix.transpose_sub, Matrix.diagonal_transpose, couplingMatrix_transpose]

/-! ## Part E: a Parseval dependency is a null direction of the coupling -/

/-- The squared pairing, read as a quadratic form of the rank-one atom. -/
theorem sq_dotProduct_eq_dotProduct_atomMatrix_mulVec (leftVec rightVec : Fin k → ℝ) :
    (leftVec ⬝ᵥ rightVec) ^ 2 = leftVec ⬝ᵥ (atomMatrix rightVec *ᵥ leftVec) := by
  have hleft : (leftVec ⬝ᵥ rightVec) ^ 2
      = ∑ rowIndex, ∑ colIndex,
          (leftVec rowIndex * rightVec rowIndex) * (leftVec colIndex * rightVec colIndex) := by
    rw [sq, dotProduct, Finset.sum_mul_sum]
  have hright : leftVec ⬝ᵥ (atomMatrix rightVec *ᵥ leftVec)
      = ∑ rowIndex, ∑ colIndex,
          leftVec rowIndex * (rightVec rowIndex * rightVec colIndex * leftVec colIndex) := by
    simp only [dotProduct, Matrix.mulVec, atomMatrix, Matrix.vecMulVec_apply, Finset.mul_sum]
  rw [hleft, hright]
  exact Finset.sum_congr rfl fun rowIndex _ =>
    Finset.sum_congr rfl fun colIndex _ => by ring

/-- **The trace of a Parseval dependency vanishes.** -/
theorem sum_stress_mul_leverageOf_eq_zero (D : WeightedDesign m k) (stress : Fin m → ℝ)
    (hstress : ∑ atomIndex, stress atomIndex • atomMatrix (D.atom atomIndex) = 0) :
    ∑ atomIndex, stress atomIndex * leverageOf (D.atom atomIndex) = 0 := by
  have hcongr := congrArg Matrix.trace hstress
  rw [Matrix.trace_sum, Matrix.trace_zero] at hcongr
  rw [← hcongr]
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]

/-- **Every row of the squared Gram against a Parseval dependency vanishes.**  The
row is the quadratic form of the dependency at the atom, and the dependency is
zero. -/
theorem sum_stress_mul_sq_atomPairing_eq_zero (D : WeightedDesign m k) (stress : Fin m → ℝ)
    (hstress : ∑ atomIndex, stress atomIndex • atomMatrix (D.atom atomIndex) = 0)
    (atomFirst : Fin m) :
    ∑ atomSecond, stress atomSecond * (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2 = 0 := by
  have hrewrite : ∀ atomSecond : Fin m,
      stress atomSecond * (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2
        = D.atom atomFirst ⬝ᵥ ((stress atomSecond • atomMatrix (D.atom atomSecond))
            *ᵥ D.atom atomFirst) := by
    intro atomSecond
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← sq_dotProduct_eq_dotProduct_atomMatrix_mulVec]
  rw [Finset.sum_congr rfl fun atomSecond (_ : atomSecond ∈ Finset.univ) => hrewrite atomSecond,
    ← dotProduct_sum, ← Matrix.sum_mulVec, hstress, Matrix.zero_mulVec, dotProduct_zero]

/-- **THE NULL DIRECTION.**  Let `s` be a Parseval dependency of the atoms,
`Sum_c s_c g_c g_c^T = 0`, and let `x_c = s_c / t_c`.  Then the quadratic form of
the coupling at `x` is `(1 - k (k - 1)) (Sum_c s_c) ^ 2`, which is at most zero at
every rank of two or more.

Three of the four terms of the coupling carry a factor of the dependency and
vanish: the squared-pairing term is the quadratic form of the dependency at each
atom, and the two leverage terms carry its trace. -/
theorem dotProduct_couplingMatrix_mulVec_nonpos_of_stress (D : WeightedDesign m k)
    (hrank : 2 ≤ k) (stress : Fin m → ℝ)
    (hstress : ∑ atomIndex, stress atomIndex • atomMatrix (D.atom atomIndex) = 0) :
    (fun atomIndex => stress atomIndex / D.weight atomIndex)
        ⬝ᵥ (couplingMatrix D *ᵥ fun atomIndex => stress atomIndex / D.weight atomIndex) ≤ 0 := by
  set probe : Fin m → ℝ := fun atomIndex => stress atomIndex / D.weight atomIndex with hprobe
  have hcancel : ∀ atomIndex : Fin m,
      D.weight atomIndex * probe atomIndex = stress atomIndex := by
    intro atomIndex
    have hne : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
    show D.weight atomIndex * (stress atomIndex / D.weight atomIndex) = stress atomIndex
    field_simp
  have htrace := sum_stress_mul_leverageOf_eq_zero D stress hstress
  have hrowZero := sum_stress_mul_sq_atomPairing_eq_zero D stress hstress
  -- Stage one: the inner sum against a fixed atom.
  have hstageOne : ∀ atomFirst : Fin m,
      ∑ atomSecond, stress atomSecond
          * (1 - (k : ℝ) * ((k : ℝ) - 1)
              + ((k : ℝ) - 1) * (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond))
              - leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond)
              + (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2)
        = (1 - (k : ℝ) * ((k : ℝ) - 1) + ((k : ℝ) - 1) * leverageOf (D.atom atomFirst))
            * ∑ atomIndex, stress atomIndex := by
    intro atomFirst
    have hsplit : ∀ atomSecond : Fin m,
        stress atomSecond
            * (1 - (k : ℝ) * ((k : ℝ) - 1)
                + ((k : ℝ) - 1) * (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond))
                - leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond)
                + (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2)
          = (1 - (k : ℝ) * ((k : ℝ) - 1) + ((k : ℝ) - 1) * leverageOf (D.atom atomFirst))
              * stress atomSecond
            + (((k : ℝ) - 1) - leverageOf (D.atom atomFirst))
                * (stress atomSecond * leverageOf (D.atom atomSecond))
            + stress atomSecond * (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2 := by
      intro atomSecond; ring
    rw [Finset.sum_congr rfl fun atomSecond (_ : atomSecond ∈ Finset.univ) => hsplit atomSecond,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      htrace, hrowZero atomFirst]
    ring
  -- Stage two: the outer sum.
  have hstageTwo : ∑ atomFirst, stress atomFirst
        * ((1 - (k : ℝ) * ((k : ℝ) - 1) + ((k : ℝ) - 1) * leverageOf (D.atom atomFirst))
            * ∑ atomIndex, stress atomIndex)
      = (1 - (k : ℝ) * ((k : ℝ) - 1)) * (∑ atomIndex, stress atomIndex) ^ 2 := by
    have hsplit : ∀ atomFirst : Fin m,
        stress atomFirst
            * ((1 - (k : ℝ) * ((k : ℝ) - 1) + ((k : ℝ) - 1) * leverageOf (D.atom atomFirst))
                * ∑ atomIndex, stress atomIndex)
          = ((1 - (k : ℝ) * ((k : ℝ) - 1)) * ∑ atomIndex, stress atomIndex) * stress atomFirst
            + (((k : ℝ) - 1) * ∑ atomIndex, stress atomIndex)
                * (stress atomFirst * leverageOf (D.atom atomFirst)) := by
      intro atomFirst; ring
    rw [Finset.sum_congr rfl fun atomFirst (_ : atomFirst ∈ Finset.univ) => hsplit atomFirst,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, htrace]
    ring
  -- The quadratic form collapses to the constant term.
  have hquad : probe ⬝ᵥ (couplingMatrix D *ᵥ probe)
      = (1 - (k : ℝ) * ((k : ℝ) - 1)) * (∑ atomIndex, stress atomIndex) ^ 2 := by
    rw [dotProduct_couplingMatrix_mulVec, ← hstageTwo]
    refine Finset.sum_congr rfl fun atomFirst _ => ?_
    rw [← hstageOne atomFirst, Finset.mul_sum]
    refine Finset.sum_congr rfl fun atomSecond _ => ?_
    have hfirst := hcancel atomFirst
    have hsecond := hcancel atomSecond
    simp only [veroneseCoupling]
    linear_combination
      (D.weight atomSecond * probe atomSecond
          * (1 - (k : ℝ) * ((k : ℝ) - 1)
              + ((k : ℝ) - 1) * (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond))
              - leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond)
              + (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2)) * hfirst
      + (stress atomFirst
          * (1 - (k : ℝ) * ((k : ℝ) - 1)
              + ((k : ℝ) - 1) * (leverageOf (D.atom atomFirst) + leverageOf (D.atom atomSecond))
              - leverageOf (D.atom atomFirst) * leverageOf (D.atom atomSecond)
              + (D.atom atomFirst ⬝ᵥ D.atom atomSecond) ^ 2)) * hsecond
  rw [hquad]
  have hcast : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrank
  have hconst : 1 - (k : ℝ) * ((k : ℝ) - 1) ≤ 0 := by nlinarith [hcast]
  have hsquare : (0 : ℝ) ≤ (∑ atomIndex, stress atomIndex) ^ 2 := sq_nonneg _
  nlinarith [hconst, hsquare]

/-! ## Part F: one null direction buys one unit of trace -/

/-- **Cauchy-Schwarz for a nonnegative form.**  The polarised companion of
`Gtz.FormNonneg.mulVec_eq_zero`, by the same discriminant argument. -/
theorem FormNonneg.sq_dotProduct_mulVec_le {size : ℕ} {gram : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : gramᵀ = gram) (hform : FormNonneg gram) (leftVec rightVec : Fin size → ℝ) :
    (leftVec ⬝ᵥ (gram *ᵥ rightVec)) ^ 2
      ≤ (leftVec ⬝ᵥ (gram *ᵥ leftVec)) * (rightVec ⬝ᵥ (gram *ᵥ rightVec)) := by
  have hswap : rightVec ⬝ᵥ (gram *ᵥ leftVec) = leftVec ⬝ᵥ (gram *ᵥ rightVec) := by
    rw [dotProduct_symm_mulVec hsymm, dotProduct_comm]
  have hexpand : ∀ scale : ℝ,
      (leftVec + scale • rightVec) ⬝ᵥ (gram *ᵥ (leftVec + scale • rightVec))
        = leftVec ⬝ᵥ (gram *ᵥ leftVec)
          + 2 * scale * (leftVec ⬝ᵥ (gram *ᵥ rightVec))
          + scale ^ 2 * (rightVec ⬝ᵥ (gram *ᵥ rightVec)) := by
    intro scale
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      dotProduct_add, smul_dotProduct, smul_dotProduct, dotProduct_smul,
      dotProduct_smul, hswap]
    simp only [smul_eq_mul]
    ring
  rcases eq_or_lt_of_le (hform rightVec) with hzero | hpos
  · have hall : ∀ scale : ℝ,
        0 ≤ leftVec ⬝ᵥ (gram *ᵥ leftVec) + 2 * scale * (leftVec ⬝ᵥ (gram *ᵥ rightVec)) := by
      intro scale
      have hval := hform (leftVec + scale • rightVec)
      rw [hexpand scale, ← hzero] at hval
      linarith
    have hcrossZero : leftVec ⬝ᵥ (gram *ᵥ rightVec) = 0 := by
      by_contra hne
      have hval := hall (-(leftVec ⬝ᵥ (gram *ᵥ leftVec) + 1)
        / (2 * (leftVec ⬝ᵥ (gram *ᵥ rightVec))))
      have hstep : 2 * (-(leftVec ⬝ᵥ (gram *ᵥ leftVec) + 1)
            / (2 * (leftVec ⬝ᵥ (gram *ᵥ rightVec)))) * (leftVec ⬝ᵥ (gram *ᵥ rightVec))
          = -(leftVec ⬝ᵥ (gram *ᵥ leftVec) + 1) := by
        field_simp
      rw [hstep] at hval
      linarith
    rw [hcrossZero, ← hzero]
    norm_num
  · have hval := hform (leftVec
      + (-((leftVec ⬝ᵥ (gram *ᵥ rightVec)) / (rightVec ⬝ᵥ (gram *ᵥ rightVec)))) • rightVec)
    rw [hexpand] at hval
    have hkey : leftVec ⬝ᵥ (gram *ᵥ leftVec)
          + 2 * (-((leftVec ⬝ᵥ (gram *ᵥ rightVec)) / (rightVec ⬝ᵥ (gram *ᵥ rightVec))))
              * (leftVec ⬝ᵥ (gram *ᵥ rightVec))
          + (-((leftVec ⬝ᵥ (gram *ᵥ rightVec)) / (rightVec ⬝ᵥ (gram *ᵥ rightVec)))) ^ 2
              * (rightVec ⬝ᵥ (gram *ᵥ rightVec))
        = leftVec ⬝ᵥ (gram *ᵥ leftVec)
          - (leftVec ⬝ᵥ (gram *ᵥ rightVec)) ^ 2 / (rightVec ⬝ᵥ (gram *ᵥ rightVec)) := by
      field_simp
      ring
    rw [hkey] at hval
    have hstep : (leftVec ⬝ᵥ (gram *ᵥ rightVec)) ^ 2 / (rightVec ⬝ᵥ (gram *ᵥ rightVec))
        ≤ leftVec ⬝ᵥ (gram *ᵥ leftVec) := by linarith
    rwa [div_le_iff₀ hpos] at hstep

/-- **ONE NULL DIRECTION IS ONE UNIT OF TRACE.**  Let `gram` be a symmetric
nonnegative form, let `w` be positive, and let `x` be a nonzero vector at which
the form is at least the `w`-weighted square of `x`.  Then the `w`-weighted trace
`Sum_c gram_cc / w_c` is at least one.

The proof uses no square root and no eigenvalue.  Cauchy-Schwarz bounds each
entry of `gram x` by `gram_cc (x . gram x)`, one arithmetic-geometric step per
index turns that into `x . gram x <= mass / 2 + (x . gram x) trace / 2`, and the
hypothesis `mass <= x . gram x` closes the argument. -/
theorem one_le_sum_diag_div_of_formNonneg {size : ℕ} {gram : Matrix (Fin size) (Fin size) ℝ}
    (hsymm : gramᵀ = gram) (hform : FormNonneg gram)
    (scaleVec : Fin size → ℝ) (hscale : ∀ index, 0 < scaleVec index)
    (probe : Fin size → ℝ) (hprobe : probe ≠ 0)
    (hdominates : ∑ index, scaleVec index * probe index ^ 2 ≤ probe ⬝ᵥ (gram *ᵥ probe)) :
    1 ≤ ∑ index, gram index index / scaleVec index := by
  set massValue := ∑ index, scaleVec index * probe index ^ 2 with hmassValue
  set quadValue := probe ⬝ᵥ (gram *ᵥ probe) with hquadValue
  set traceValue := ∑ index, gram index index / scaleVec index with htraceValue
  have hmassPos : 0 < massValue := by
    obtain ⟨index, hindex⟩ := Function.ne_iff.mp hprobe
    refine Finset.sum_pos' (fun other _ => mul_nonneg (hscale other).le (sq_nonneg _))
      ⟨index, Finset.mem_univ index, mul_pos (hscale index) ?_⟩
    have hsq : probe index ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using hindex)
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hsq)
  have hquadPos : 0 < quadValue := lt_of_lt_of_le hmassPos hdominates
  have hentryBound : ∀ index : Fin size,
      ((gram *ᵥ probe) index) ^ 2 ≤ gram index index * quadValue := by
    intro index
    have hcs := hform.sq_dotProduct_mulVec_le hsymm (Pi.single index 1) probe
    rw [dotProduct_single_mulVec_single] at hcs
    have hleft : (Pi.single index (1 : ℝ)) ⬝ᵥ (gram *ᵥ probe) = (gram *ᵥ probe) index := by
      rw [single_dotProduct, one_mul]
    rwa [hleft] at hcs
  have hpointwise : ∀ index : Fin size,
      probe index * (gram *ᵥ probe) index
        ≤ scaleVec index * probe index ^ 2 / 2
          + gram index index * quadValue / (2 * scaleVec index) := by
    intro index
    have hpos := hscale index
    have hamgm : probe index * (gram *ᵥ probe) index
        ≤ scaleVec index * probe index ^ 2 / 2
          + ((gram *ᵥ probe) index) ^ 2 / (2 * scaleVec index) := by
      rw [div_add_div _ _ (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * scaleVec index ≠ 0),
        le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * scaleVec index))]
      nlinarith [sq_nonneg (scaleVec index * probe index - (gram *ᵥ probe) index), hpos]
    have hsecond : ((gram *ᵥ probe) index) ^ 2 / (2 * scaleVec index)
        ≤ gram index index * quadValue / (2 * scaleVec index) :=
      div_le_div_of_nonneg_right (hentryBound index) (by positivity) |>.trans_eq rfl
    linarith
  have hsum : quadValue ≤ massValue / 2 + quadValue * traceValue / 2 := by
    have hleft : quadValue = ∑ index, probe index * (gram *ᵥ probe) index := by
      rw [hquadValue, dotProduct]
    have hright : ∑ index, (scaleVec index * probe index ^ 2 / 2
          + gram index index * quadValue / (2 * scaleVec index))
        = massValue / 2 + quadValue * traceValue / 2 := by
      rw [Finset.sum_add_distrib, hmassValue, htraceValue, Finset.sum_div, Finset.mul_sum,
        Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun index _ => ?_
      have hpos : scaleVec index ≠ 0 := (hscale index).ne'
      field_simp
    calc quadValue = ∑ index, probe index * (gram *ᵥ probe) index := hleft
      _ ≤ ∑ index, (scaleVec index * probe index ^ 2 / 2
            + gram index index * quadValue / (2 * scaleVec index)) :=
          Finset.sum_le_sum fun index _ => hpointwise index
      _ = massValue / 2 + quadValue * traceValue / 2 := hright
  by_contra hcontra
  push_neg at hcontra
  nlinarith [hsum, hdominates, hmassPos, hquadPos, hcontra]

/-! ## Part G: the two headline no-goes at rank three -/

/-- The `w`-weighted trace of `diag t - F` is `m` minus the trace law. -/
theorem sum_diag_diagonal_sub_couplingMatrix_div (D : WeightedDesign m k) :
    ∑ atomIndex, (Matrix.diagonal D.weight - couplingMatrix D) atomIndex atomIndex
        / D.weight atomIndex
      = (m : ℝ) - ((k : ℝ) ^ 2 - (k : ℝ) + 1) := by
  have hentry : ∀ atomIndex : Fin m,
      (Matrix.diagonal D.weight - couplingMatrix D) atomIndex atomIndex / D.weight atomIndex
        = 1 - D.weight atomIndex * couplingDiagFactor k (leverageOf (D.atom atomIndex)) := by
    intro atomIndex
    have hpos : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, couplingMatrix_apply,
      veroneseCoupling_self]
    field_simp
  rw [Finset.sum_congr rfl fun atomIndex (_ : atomIndex ∈ Finset.univ) => hentry atomIndex,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sum_weight_mul_couplingDiagFactor D]

/-- **THE SHARPENED COUNT.**  A design that carries a nonzero Parseval dependency
and whose coupling has no negative entry carries at least `k ^ 2 - k + 2` atoms.
The dependency is a null direction of the coupling, and one null direction is one
unit of trace. -/
theorem rankPolynomial_add_one_le_size_of_stress (D : WeightedDesign m k) (hrank : 2 ≤ k)
    (hnonneg : ∀ atomFirst atomSecond : Fin m, 0 ≤ veroneseCoupling D atomFirst atomSecond)
    (stress : Fin m → ℝ) (hne : stress ≠ 0)
    (hstress : ∑ atomIndex, stress atomIndex • atomMatrix (D.atom atomIndex) = 0) :
    (k : ℝ) ^ 2 - (k : ℝ) + 1 + 1 ≤ (m : ℝ) := by
  set probe : Fin m → ℝ := fun atomIndex => stress atomIndex / D.weight atomIndex with hprobe
  have hprobeNe : probe ≠ 0 := by
    obtain ⟨atomIndex, hatom⟩ := Function.ne_iff.mp hne
    refine Function.ne_iff.mpr ⟨atomIndex, ?_⟩
    have hstressNe : stress atomIndex ≠ 0 := by simpa using hatom
    have hweightNe : D.weight atomIndex ≠ 0 := (D.weight_pos atomIndex).ne'
    simp only [hprobe, Pi.zero_apply]
    exact div_ne_zero hstressNe hweightNe
  have hnull := dotProduct_couplingMatrix_mulVec_nonpos_of_stress D hrank stress hstress
  have hdom : ∑ atomIndex, D.weight atomIndex * probe atomIndex ^ 2
      ≤ probe ⬝ᵥ ((Matrix.diagonal D.weight - couplingMatrix D) *ᵥ probe) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_diagonal_mulVec]
    linarith [hnull]
  have hunit := one_le_sum_diag_div_of_formNonneg
    (transpose_diagonal_sub_couplingMatrix D)
    (formNonneg_diagonal_sub_couplingMatrix D hnonneg) D.weight D.weight_pos probe hprobeNe hdom
  rw [sum_diag_diagonal_sub_couplingMatrix_div D] at hunit
  linarith

/-- **THE ARITHMETIC.**  The trace law asks for `k ^ 2 - k + 1`, and the Veronese
image of the atoms lives in the symmetric `k x k` matrices, of dimension
`k (k + 1) / 2`.  The two agree only at ranks one and two.  In division-free form:
`2 (k ^ 2 - k + 1) <= k (k + 1)` exactly when `k <= 2`. -/
theorem rankPolynomial_le_symmetricDimension_iff (rank : ℕ) (hrank : 1 ≤ rank) :
    2 * (rank ^ 2 + 1) ≤ rank * (rank + 1) + 2 * rank ↔ rank ≤ 2 := by
  have hpow : rank ^ 2 = rank * rank := by ring
  have hexp : rank * (rank + 1) = rank * rank + rank := by ring
  rw [hpow, hexp]
  constructor
  · intro hle
    by_contra hcontra
    push_neg at hcontra
    have hthree : 3 ≤ rank := hcontra
    have hsquare : 3 * rank ≤ rank * rank := Nat.mul_le_mul hthree (le_refl rank)
    omega
  · intro hle
    interval_cases rank <;> norm_num

/-- **NO `(6,3)` DESIGN HAS A NONNEGATIVE COUPLING.**  The trace law asks for
seven, and six atoms supply at most six. -/
theorem exists_veroneseCoupling_neg_sixThree (D : WeightedDesign 6 3) :
    ∃ atomFirst atomSecond : Fin 6, veroneseCoupling D atomFirst atomSecond < 0 := by
  by_contra hcontra
  push_neg at hcontra
  have hcount := rankPolynomial_le_size D fun atomFirst atomSecond => hcontra atomFirst atomSecond
  norm_num at hcount

/-- **NO `(7,3)` DESIGN HAS A NONNEGATIVE COUPLING.**  Seven rank-one symmetric
`3 x 3` matrices are dependent, because `dim_R Sym_3(R) = 6`, and the dependency
is a null direction that buys the eighth unit of trace that seven atoms cannot
pay.  Size seven decides all of rank three. -/
theorem exists_veroneseCoupling_neg_sevenThree (D : WeightedDesign 7 3) :
    ∃ atomFirst atomSecond : Fin 7, veroneseCoupling D atomFirst atomSecond < 0 := by
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨stress, hne, hstress⟩ :=
    exists_parsevalNullDirection D.atom (by norm_num : 3 * (3 + 1) / 2 < 7)
  have hcount := rankPolynomial_add_one_le_size_of_stress D (by norm_num)
    (fun atomFirst atomSecond => hcontra atomFirst atomSecond) stress hne hstress
  norm_num at hcount

/-- **THE TWO CELLS TOGETHER.**  At the two sizes that decide rank three, the
coupling always has a strictly negative entry, so the Laplacian step of the
rank-two classification is unavailable. -/
theorem exists_veroneseCoupling_neg_rankThree_sixOrSeven :
    (∀ D : WeightedDesign 6 3, ∃ atomFirst atomSecond : Fin 6,
        veroneseCoupling D atomFirst atomSecond < 0)
      ∧ ∀ D : WeightedDesign 7 3, ∃ atomFirst atomSecond : Fin 7,
        veroneseCoupling D atomFirst atomSecond < 0 :=
  ⟨exists_veroneseCoupling_neg_sixThree, exists_veroneseCoupling_neg_sevenThree⟩

/-! ## Part H: the rank-two side of the same laws -/

/-- At rank two the trace law is the shipped `2 k - 1 = 3`. -/
theorem sum_weight_mul_couplingDiagFactor_rankTwo (D : WeightedDesign m 2) :
    ∑ atomIndex, D.weight atomIndex * (2 * leverageOf (D.atom atomIndex) - 1) = 3 := by
  have hlaw := sum_weight_mul_couplingDiagFactor D
  simp only [couplingDiagFactor_two] at hlaw
  rw [hlaw]
  norm_num

/-- **The count is sharp at rank two.**  A rank-two design with no strictly
dominating pair carries at least three atoms, and three is exactly the number of
classes of `Gtz.rankTwoTieClassification`. -/
theorem three_le_size_of_noStrictPair {size : ℕ} (D : WeightedDesign size 2)
    (hheavy : ∀ atomIndex : Fin size, 1 ≤ leverageOf (D.atom atomIndex))
    (hnostrict : NoStrictPair D) : (3 : ℝ) ≤ (size : ℝ) := by
  have hnonneg : ∀ atomFirst atomSecond : Fin size,
      0 ≤ veroneseCoupling D atomFirst atomSecond := by
    intro atomFirst atomSecond
    rw [veroneseCoupling_eq_tieCoupling]
    exact tieCoupling_nonneg D hheavy hnostrict atomFirst atomSecond
  have hcount := rankPolynomial_le_size D hnonneg
  push_cast at hcount
  linarith

end Gtz
