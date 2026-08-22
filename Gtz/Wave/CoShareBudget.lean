/-
# The co-share pair budget: one exact law at EVERY design, rank and size

Write `t_c` for the weight, `l_c` for the leverage, `b_cd = <g_c, g_d>` for the
pairing, and

    `u_c := 1 - t_c l_c`      (`Gtz.designCoShare`, the co-share)

for the deficit of the Parseval share.  The co-shares are the diagonal of the
complementary projection `Gtz.coProjection`, a symmetric idempotent of `R^m` whose
trace is the CORANK `m - k`.

**THE PAIR LAW (`Gtz.weight_mul_sq_dotProduct_le_coShare_mul`).**  At every weighted
design, every rank, every size and every pair of distinct atoms,

    `t_c t_d b_cd^2  <=  u_c u_d` .

**THE BUDGET (`Gtz.sum_offDiag_coShareSlack_eq_corank_mul`).**  The total slack of
that law is a function of the corank ALONE:

    `sum_{c != d} (u_c u_d - t_c t_d b_cd^2)  =  (m - k) (m - k - 1)` .

Both are unconditional.  No heaviness, no domination hypothesis, no tie, no
stationarity: they hold at every design there is.

## Why this is exactly the right pair of statements

The two are one identity read twice.  Set `Pi := coProjection D`.  Idempotence and
symmetry make each row of the entrywise square its own diagonal entry,
`sum_e Pi_ce^2 = Pi_cc = u_c`, so `Pi` has a nonnegative diagonal and the
CAUCHY-SCHWARZ minor `Pi_cd^2 <= Pi_cc Pi_dd` is the pair law once
`Pi_cd = -sqrt(t_c t_d) b_cd` is read off `Gtz.coProjection_offDiag`.  Summing the
minors over ALL ordered pairs is a trace computation and nothing else:

    `sum_{c,d} Pi_cc Pi_dd = (tr Pi)^2 = (m-k)^2` ,
    `sum_{c,d} Pi_cd^2     = tr(Pi^T Pi) = tr(Pi Pi) = tr Pi = m - k` ,

and the diagonal terms of the difference vanish identically.  So the slack is
CONSERVED: a design cannot buy tightness at one pair without paying at another.

## What it recovers, and what it adds

* **Corank one is the equality case.**  At `m = k + 1` the budget is `1 * 0 = 0`, so
  every term of a nonnegative sum vanishes and the pair law is SATURATED at every
  pair (`Gtz.coShareSlack_eq_zero_of_corankOne`).  The tree already lands that
  equality as `Gtz.weight_mul_sq_dotProduct_eq_coShare_mul`, through the rank-one
  outer square of `Gtz.exists_coAxis`.  Here it drops out of the budget with no
  axis, no outer square and no trace-one argument -- and, unlike that route, the
  budget also says what happens at every OTHER corank.
* **At `(6,3)` the budget is SIX.**  Fifteen unordered pairs share it, so some pair
  of every `(6,3)` design carries slack at least `1/5`
  (`Gtz.exists_coShareSlack_sixThree`).  That is a floor on a pair quantity at the
  open cell which needs no hypothesis at all, and it is sharp in the sense that the
  total is exactly six.
* **The co-shares are nonnegative at every rank and size**
  (`Gtz.designCoShare_nonneg_ofAnyRank`), because a row of the entrywise square is
  a sum of squares.  The tree proves this only at corank one
  (`Gtz.designCoShare_nonneg`), where it reads off the outer square.

## Honest scope

The budget is an identity, not a decision procedure.  It constrains the pairs of a
design without mentioning domination, so on its own it decides no cell.  What it
does supply is a conserved quantity: any argument that forces slack to be small at
many pairs must account for `(m-k)(m-k-1)` somewhere, and at `(6,3)` that quantity
is six and cannot be spent twice.

[MEASURED before proving, in exact rational arithmetic outside Lean: the pair law
and the budget at the `(6,3)` octahedron, the `(6,3)` icosahedron, the `(5,3)`
diamond and the `(4,3)` regular tetrahedron, and at random designs of rank two
through five and size four through ten.  Corank-one saturation reproduced to
`1e-15` at `(3,2)`, `(4,3)`, `(5,4)` and `(6,5)`.]
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Quantitative.ChartHadamard
import Gtz.Wave.CorankOneRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1: a discriminant

The only analytic input: a quadratic in one real variable that never goes negative
has a nonpositive discriminant. -/

/-- **THE DISCRIMINANT BOUND.**  If `A + 2 s B + s^2 C` is nonnegative at every real
`s`, then `B^2 <= A C`.  The degenerate case `C = 0` is handled by a shift that
drives the linear term below `-1`. -/
theorem sq_le_mul_of_quadraticForm_nonneg {constTerm crossTerm leadTerm : ℝ}
    (hlead : 0 ≤ leadTerm)
    (hform : ∀ scale : ℝ, 0 ≤ constTerm + 2 * scale * crossTerm + scale ^ 2 * leadTerm) :
    crossTerm ^ 2 ≤ constTerm * leadTerm := by
  rcases eq_or_lt_of_le hlead with hzero | hpos
  · have hcrossZero : crossTerm = 0 := by
      by_contra hne
      have hbad := hform (-(constTerm + 1) / (2 * crossTerm))
      rw [← hzero] at hbad
      have hclear : (-(constTerm + 1) / (2 * crossTerm)) * crossTerm
          = -(constTerm + 1) / 2 := by
        field_simp
      rw [mul_zero, add_zero, mul_assoc, hclear] at hbad
      linarith
    rw [hcrossZero, ← hzero]
    norm_num
  · have hbad := hform (-crossTerm / leadTerm)
    have hsquare : (-crossTerm / leadTerm) ^ 2 * leadTerm = crossTerm ^ 2 / leadTerm := by
      field_simp
    have hlinear : 2 * (-crossTerm / leadTerm) * crossTerm
        = -(2 * (crossTerm ^ 2 / leadTerm)) := by
      field_simp
    rw [hsquare, hlinear] at hbad
    have hkey : crossTerm ^ 2 / leadTerm ≤ constTerm := by linarith
    rw [div_le_iff₀ hpos] at hkey
    linarith

/-! ## Part 2: the entrywise square of the complementary projection -/

/-- The complementary projection reads its entries either way round. -/
theorem coProjection_comm (D : WeightedDesign m k) (rowIndex colIndex : Fin m) :
    coProjection D colIndex rowIndex = coProjection D rowIndex colIndex := by
  have hentry := congrFun (congrFun (coProjection_transpose D) rowIndex) colIndex
  rwa [Matrix.transpose_apply] at hentry

/-- **THE ROW LAW OF THE ENTRYWISE SQUARE.**  Idempotence and symmetry make the row
sum of the squared entries the diagonal entry, that is the CO-SHARE. -/
theorem sum_sq_coProjection_row (D : WeightedDesign m k) (rowIndex : Fin m) :
    ∑ colIndex, coProjection D rowIndex colIndex ^ 2 = designCoShare D rowIndex := by
  have hidem := congrFun (congrFun (coProjection_mul_self D) rowIndex) rowIndex
  rw [Matrix.mul_apply] at hidem
  rw [← coProjection_diag D rowIndex, ← hidem]
  refine Finset.sum_congr rfl fun colIndex _ => ?_
  rw [pow_two]
  congr 1
  exact (coProjection_comm D rowIndex colIndex).symm

/-- **THE CO-SHARES ARE NONNEGATIVE AT EVERY RANK AND SIZE.**  The tree proves this
at corank one only (`Gtz.designCoShare_nonneg`), by reading the outer square.  Here
it is a row of a sum of squares. -/
theorem designCoShare_nonneg_ofAnyRank (D : WeightedDesign m k) (atomIndex : Fin m) :
    0 ≤ designCoShare D atomIndex := by
  rw [← sum_sq_coProjection_row D atomIndex]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The cross row law: the pairing of two rows of the projection is the entry. -/
theorem sum_mul_coProjection_row (D : WeightedDesign m k) (rowFirst rowSecond : Fin m) :
    ∑ colIndex, coProjection D rowFirst colIndex * coProjection D rowSecond colIndex
      = coProjection D rowFirst rowSecond := by
  have hidem := congrFun (congrFun (coProjection_mul_self D) rowFirst) rowSecond
  rw [Matrix.mul_apply] at hidem
  rw [← hidem]
  refine Finset.sum_congr rfl fun colIndex _ => ?_
  congr 1
  exact (coProjection_comm D rowSecond colIndex).symm

/-- **THE CAUCHY-SCHWARZ MINOR OF THE COMPLEMENTARY PROJECTION.**  Every two by two
principal minor of `Gtz.coProjection` is nonnegative. -/
theorem sq_coProjection_le_coShare_mul (D : WeightedDesign m k) (rowFirst rowSecond : Fin m) :
    coProjection D rowFirst rowSecond ^ 2
      ≤ designCoShare D rowFirst * designCoShare D rowSecond := by
  refine sq_le_mul_of_quadraticForm_nonneg (designCoShare_nonneg_ofAnyRank D rowSecond)
    fun scale => ?_
  have hexpand : designCoShare D rowFirst + 2 * scale * coProjection D rowFirst rowSecond
        + scale ^ 2 * designCoShare D rowSecond
      = ∑ colIndex, (coProjection D rowFirst colIndex
          + scale * coProjection D rowSecond colIndex) ^ 2 := by
    have hterm : ∀ colIndex : Fin m,
        (coProjection D rowFirst colIndex + scale * coProjection D rowSecond colIndex) ^ 2
          = coProjection D rowFirst colIndex ^ 2
            + 2 * scale * (coProjection D rowFirst colIndex
                * coProjection D rowSecond colIndex)
            + scale ^ 2 * coProjection D rowSecond colIndex ^ 2 := fun _ => by ring
    rw [Finset.sum_congr rfl fun colIndex (_ : colIndex ∈ Finset.univ) => hterm colIndex,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_sq_coProjection_row D rowFirst, sum_sq_coProjection_row D rowSecond,
      sum_mul_coProjection_row D rowFirst rowSecond]
  rw [hexpand]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Part 3: the pair law in design vocabulary -/

/-- The off-diagonal entry of the complementary projection, squared. -/
theorem sq_coProjection_offDiag (D : WeightedDesign m k) {rowFirst rowSecond : Fin m}
    (hdistinct : rowFirst ≠ rowSecond) :
    coProjection D rowFirst rowSecond ^ 2
      = D.weight rowFirst * D.weight rowSecond * (D.atom rowFirst ⬝ᵥ D.atom rowSecond) ^ 2 := by
  rw [coProjection_offDiag D hdistinct, neg_pow, mul_pow, mul_pow,
    Real.sq_sqrt (D.weight_pos rowFirst).le, Real.sq_sqrt (D.weight_pos rowSecond).le]
  norm_num

/-- **THE PAIR LAW.**  At every weighted design, every rank, every size and every
pair of distinct atoms, `t_c t_d <g_c, g_d>^2 <= u_c u_d`. -/
theorem weight_mul_sq_dotProduct_le_coShare_mul (D : WeightedDesign m k)
    {rowFirst rowSecond : Fin m} (hdistinct : rowFirst ≠ rowSecond) :
    D.weight rowFirst * D.weight rowSecond * (D.atom rowFirst ⬝ᵥ D.atom rowSecond) ^ 2
      ≤ designCoShare D rowFirst * designCoShare D rowSecond := by
  rw [← sq_coProjection_offDiag D hdistinct]
  exact sq_coProjection_le_coShare_mul D rowFirst rowSecond

/-- The slack of the pair law at an ordered pair. -/
noncomputable def coShareSlack (D : WeightedDesign m k) (rowFirst rowSecond : Fin m) : ℝ :=
  designCoShare D rowFirst * designCoShare D rowSecond
    - D.weight rowFirst * D.weight rowSecond * (D.atom rowFirst ⬝ᵥ D.atom rowSecond) ^ 2

theorem coShareSlack_nonneg (D : WeightedDesign m k) {rowFirst rowSecond : Fin m}
    (hdistinct : rowFirst ≠ rowSecond) : 0 ≤ coShareSlack D rowFirst rowSecond := by
  rw [coShareSlack, sub_nonneg]
  exact weight_mul_sq_dotProduct_le_coShare_mul D hdistinct

/-! ## Part 4: the budget -/

/-- The total mass of the entrywise square of the complementary projection is the
CORANK: two trace readings and idempotence. -/
theorem sum_sq_coProjection_eq_corank (D : WeightedDesign m k) :
    ∑ rowIndex, ∑ colIndex, coProjection D rowIndex colIndex ^ 2 = (m : ℝ) - (k : ℝ) := by
  rw [← trace_transpose_mul_self (coProjection D), coProjection_transpose,
    coProjection_mul_self, trace_coProjection]

/-- The total mass of the co-share outer product is the SQUARED corank. -/
theorem sum_coShare_mul_coShare (D : WeightedDesign m k) :
    ∑ rowIndex, ∑ colIndex, designCoShare D rowIndex * designCoShare D colIndex
      = ((m : ℝ) - (k : ℝ)) ^ 2 := by
  have hrow : ∀ rowIndex : Fin m,
      ∑ colIndex, designCoShare D rowIndex * designCoShare D colIndex
        = designCoShare D rowIndex * ((m : ℝ) - (k : ℝ)) := by
    intro rowIndex
    rw [← Finset.mul_sum, sum_designCoShare D]
  rw [Finset.sum_congr rfl fun rowIndex (_ : rowIndex ∈ Finset.univ) => hrow rowIndex,
    ← Finset.sum_mul, sum_designCoShare D]
  ring

/-- **THE BUDGET, OVER ALL ORDERED PAIRS.**  The diagonal terms vanish identically,
so this is already the off-diagonal statement. -/
theorem sum_coShareSlack_full (D : WeightedDesign m k) :
    ∑ rowIndex, ∑ colIndex,
        (designCoShare D rowIndex * designCoShare D colIndex
          - coProjection D rowIndex colIndex ^ 2)
      = ((m : ℝ) - (k : ℝ)) ^ 2 - ((m : ℝ) - (k : ℝ)) := by
  have hsplit : ∀ rowIndex : Fin m,
      ∑ colIndex, (designCoShare D rowIndex * designCoShare D colIndex
          - coProjection D rowIndex colIndex ^ 2)
        = (∑ colIndex, designCoShare D rowIndex * designCoShare D colIndex)
          - ∑ colIndex, coProjection D rowIndex colIndex ^ 2 := by
    intro rowIndex
    rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun rowIndex (_ : rowIndex ∈ Finset.univ) => hsplit rowIndex,
    Finset.sum_sub_distrib, sum_coShare_mul_coShare D, sum_sq_coProjection_eq_corank D]

/-- **THE BUDGET.**  The total slack of the pair law over the ordered pairs of
DISTINCT atoms is a function of the corank alone. -/
theorem sum_offDiag_coShareSlack_eq_corank_mul (D : WeightedDesign m k) :
    ∑ pair ∈ (Finset.univ : Finset (Fin m)).offDiag, coShareSlack D pair.1 pair.2
      = ((m : ℝ) - (k : ℝ)) * ((m : ℝ) - (k : ℝ) - 1) := by
  classical
  have hcongr : ∀ pair ∈ (Finset.univ : Finset (Fin m)).offDiag,
      coShareSlack D pair.1 pair.2
        = designCoShare D pair.1 * designCoShare D pair.2
          - coProjection D pair.1 pair.2 ^ 2 := by
    intro pair hpair
    rw [coShareSlack, sq_coProjection_offDiag D (Finset.mem_offDiag.mp hpair).2.2]
  have hdiag : ∀ rowIndex : Fin m,
      designCoShare D rowIndex * designCoShare D rowIndex
        - coProjection D rowIndex rowIndex ^ 2 = 0 := by
    intro rowIndex
    rw [coProjection_diag]
    ring
  rw [Finset.sum_congr rfl hcongr,
    sum_offDiag_eq_sum_sub_diagonal
      (fun rowIndex colIndex => designCoShare D rowIndex * designCoShare D colIndex
        - coProjection D rowIndex colIndex ^ 2),
    Finset.sum_congr rfl fun rowIndex (_ : rowIndex ∈ Finset.univ) => hdiag rowIndex,
    Finset.sum_const_zero, sub_zero, sum_coShareSlack_full D]
  ring

/-! ## Part 5: the two ends of the budget -/

/-- **CORANK ONE SATURATES THE PAIR LAW.**  The budget is `1 * 0 = 0` there, and a
nonnegative sum of zero total is zero term by term.  This is a second proof of the
tree's `Gtz.weight_mul_sq_dotProduct_eq_coShare_mul`, with no outer square. -/
theorem coShareSlack_eq_zero_of_corankOne (D : WeightedDesign (k + 1) k)
    {rowFirst rowSecond : Fin (k + 1)} (hdistinct : rowFirst ≠ rowSecond) :
    coShareSlack D rowFirst rowSecond = 0 := by
  classical
  have hbudget := sum_offDiag_coShareSlack_eq_corank_mul D
  have hzero : ((((k : ℕ) + 1 : ℕ) : ℝ) - (k : ℝ)) * ((((k : ℕ) + 1 : ℕ) : ℝ) - (k : ℝ) - 1) = 0 := by
    push_cast
    ring
  rw [hzero] at hbudget
  have hmem : (rowFirst, rowSecond) ∈ (Finset.univ : Finset (Fin (k + 1))).offDiag :=
    Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hdistinct⟩
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun pair hpair =>
    coShareSlack_nonneg D (Finset.mem_offDiag.mp hpair).2.2).mp hbudget
  exact hall (rowFirst, rowSecond) hmem

/-- **THE `(6,3)` BUDGET IS SIX.** -/
theorem sum_offDiag_coShareSlack_sixThree (D : WeightedDesign 6 3) :
    ∑ pair ∈ (Finset.univ : Finset (Fin 6)).offDiag, coShareSlack D pair.1 pair.2 = 6 := by
  rw [sum_offDiag_coShareSlack_eq_corank_mul D]
  norm_num

/-- **SOME PAIR OF EVERY `(6,3)` DESIGN CARRIES SLACK AT LEAST `1/5`.**  Thirty
ordered pairs share a budget of six, so the largest term is at least the average.
No hypothesis at all: this holds at every design of the open cell. -/
theorem exists_coShareSlack_sixThree (D : WeightedDesign 6 3) :
    ∃ rowFirst rowSecond : Fin 6, rowFirst ≠ rowSecond
      ∧ 1 / 5 ≤ coShareSlack D rowFirst rowSecond := by
  classical
  by_contra hcontra
  push_neg at hcontra
  have hcard : ((Finset.univ : Finset (Fin 6)).offDiag).card = 30 := by decide
  have hbound : ∑ pair ∈ (Finset.univ : Finset (Fin 6)).offDiag, coShareSlack D pair.1 pair.2
      < ∑ _pair ∈ (Finset.univ : Finset (Fin 6)).offDiag, (1 / 5 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ fun pair hpair => ?_
    · exact ⟨(0, 1), Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, by decide⟩⟩
    · exact hcontra pair.1 pair.2 (Finset.mem_offDiag.mp hpair).2.2
  rw [sum_offDiag_coShareSlack_sixThree D, Finset.sum_const, hcard] at hbound
  norm_num at hbound
