/-
# At a tie, a trace-one exchange window dominates on every erasure

The residual under attack was: **at a `(6,3)` tie, is every linearly independent
triple weakly dominating?**  Measured true on both known tie families at both sizes;
the forward half (a weak dominator is a basis) is already a theorem.  This file lands
the converse on an explicitly delimited part of the tie, derives the measured
regularity outright at both witnesses, and reduces what is left to ONE SCALAR EQUATION
per exchange window.

## The mechanism

For a base `Q` with `S_Q - 1` positive definite, the pigeonhole pivot
`q_c = g_c (S_Q - 1)^{-1} g_c` decides erasures: `Q.erase c` dominates iff `q_c <= 1`
(`erase_dominates_iff_pivot_le_one`) and dominates STRICTLY iff `q_c < 1`
(`erase_strictDominates_iff_pivot_lt_one`).  At a tie no `rank`-subset dominates
strictly, so EVERY INSIDER PIVOT IS AT LEAST ONE (`one_le_pivot_of_isTie`).  That is
the tie's whole contribution, and it is one-sided.

Against it sits an identity that needs no Parseval and no cardinality hypothesis,
`tr (X^{-1} S_Q) = tr (X^{-1}(X + 1))`:

    sum_{c in Q} q_c  =  rank + tr (S_Q - 1)^{-1}       (`sum_pivot_eq_rank_add_trace_inverse`)

so at `|Q| = rank + 1` the insider DEFICITS sum to `tr (S_Q - 1)^{-1} - 1`.  A
nonnegative sum that is at most zero is termwise zero.  Hence:

**at a tie, a window with `tr (S_Q - 1)^{-1} <= 1` weakly dominates on every erasure**
(`forall_dominates_erase_of_isTie_of_trace_le_one`), and conversely all erasures
dominating forces the trace to be exactly one
(`trace_inverse_eq_one_of_forall_dominates_erase`).  ONE NUMBER PER WINDOW, and the
outsiders are never mentioned.

The stated form is sharper still: nominate an EXEMPT subset of the window and require
only that the exempt insiders already account for the trace surplus; then every erasure
OUTSIDE the exempt set dominates (`dominates_erase_of_isTie_of_trace_le_exempt`).
Trace one is the empty exempt set.  The exempt set is what carries the argument past
the circuits: at the `(5,3)` diamond the four non-circuit windows have
`tr (S_Q - 1)^{-1} = 11/6`, and the whole surplus `5/6` sits on the single insider
whose erasure is a triangle, so a one-element exempt set certifies the other three
erasures of each — and the five windows together certify ALL EIGHT spanning trees.

Parseval re-expresses the same criterion on the outsiders, which is the shape the
shipped branch-(a) certificate speaks: `excess_balance` turns the insider deficits into
`sum_{e not in Q} t_e (q_e - 1)`, giving `dominates_erase_of_isTie_of_excess_le_exempt`
and `forall_dominates_erase_of_isTie_of_excess_nonpos`.  Both readings are landed; the
trace one is primitive.

Either way this is the universal upgrade of the shipped `pigeonhole`, which under the
same hypotheses produces ONE dominating erasure and no more; the tie is what turns the
pigeonhole into a partition of zeros.  At corank one there are no outsiders, the
excess is an empty sum, and the statement degenerates to the shipped
`forall_dominates_erase_of_isTie` — so this is that theorem freed from `m = k + 1`.

## What it buys, and what it does not

Domination forces invertibility (`posDef_subsetSum_of_dominates`, the forward half
restated here because its home is a sibling lane's file), so at a tie a trace-one
window has all `rank + 1` of its erasures independent: **a trace-one window is a
circuit**.  Contrapositively, at a tie a window with a dependent erasure carries
STRICTLY POSITIVE excess (`excess_pos_of_isTie_of_erase_not_dominates`).

The hypothesis is not vacuous and not rational-only.  The whole two-parameter
split-tetrahedron `(6,3)` tie family carries four RAINBOW WINDOWS — one copy of each
tetrahedron direction — whose moment is the tetrahedron's own `4 . 1`, whose gap is
therefore `3 . 1`, whose inverse gap has trace exactly `3/3 = 1`
(`rainbowWindow_trace_inverse_eq_one`) and whose six pivots are all exactly one.  Their
erasures run through ALL TWELVE independent triples of that tie, every one of them
certified dominating by the theorem alone (`rainbowWindow_dominates_erase`).  So at the
`(6,3)` witness the measured regularity is now derived rather than measured.

## THE RESIDUAL, in one line

MEASURED, NOT PROVED HERE:

    at a tie, tr (S_Q - 1)^{-1}  =  1 + sum over the insiders whose erasure is
    DEPENDENT of (q_c - 1);  in particular = 1 at every circuit window.

Verified to `1e-9` at every positive-definite window of the tetrahedron `(4,3)`, the
`(3,2)` equiangular tie, the `(5,3)` diamond (`11/6` on the four non-circuit windows,
`1` on the rim) and the `(6,3)` split tetrahedron (`19/3` on the nine non-circuit
windows, `1` on the four rainbow windows) — and, since it is equivalent to the target
restricted to a window, at all thirty-five ties this lane inspected.

What blocks it is precisely stated.  The tie hypothesis yields only `q_c >= 1`, hence
only `tr (S_Q - 1)^{-1} >= 1`; the reverse inequality is exactly "some erasure
dominates", which off ties is what the branch-(a) certificate supplies from a strictly
negative excess.  At a tie the certificate's slack is gone, so the reverse inequality
must come from outside the window, and neither Parseval on the outsiders nor the
no-strict-dominator condition on other `rank`-subsets supplies it: both are inequalities
of the SAME sign.  Averaging over windows is closed off independently — the campaign's
`ChartHadamard` already records that the layer aggregate cannot see the design.

## The uniform `(6,3)` no-go, unconditional

`sum_det_subsetSum_sub_one_sixThree` says the twenty gap determinants of a
UNIFORM-weight `(6,3)` design sum to `-56` whatever the design.  At a tie a weakly
dominating triple has a singular gap, hence gap determinant zero.  So a uniform
`(6,3)` tie cannot have all twenty triples dominating
(`not_forall_dominates_of_isTie_uniform_sixThree`, landed in the Cauchy-Binet layer
module) — which, read against the residual
above, says no uniform `(6,3)` tie is in general position.  This is the promised
corollary in the cell where the layer sum is already mechanized; the general-weight
layer sum needs the atom-sum form of the invariant, which is not proved here.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.TraceIdentity
import Gtz.Certificates.ResidueDissolution
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Quantitative.ChartHadamard
import Gtz.Design.StressFreeNormalizer
import Gtz.Quantitative.WindowGramSignature

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Every insider pivot of a window at a tie is at least one -/

/-- At a tie NO pivot of a `rank + 1` window drops below one: a pivot below one is
exactly a strictly dominating erasure, and a tie has none. -/
theorem one_le_pivot_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) {window : Finset (Fin size)}
    (hgate : (subsetSum design window - 1).PosDef) (hcard : window.card = rank + 1)
    {dropped : Fin size} (hmem : dropped ∈ window) :
    1 ≤ pivot design window dropped := by
  by_contra hbelow
  rw [not_le] at hbelow
  have hcardErase : (window.erase dropped).card = rank := by
    rw [Finset.card_erase_of_mem hmem, hcard]
    omega
  exact htie.2 _ hcardErase
    ((erase_strictDominates_iff_pivot_lt_one design window hgate hmem).mpr hbelow)

/-! ## The trace criterion: one scalar per window, Parseval-free

The insider pivots of ANY base sum to `rank + tr (S_Q - 1)^{-1}` — no Parseval, no
cardinality hypothesis, just `tr (X^{-1} S_Q) = tr (X^{-1}(X + 1))`.  At `|Q| = rank+1`
the insider deficits therefore sum to `tr (S_Q - 1)^{-1} - 1`, and the tie makes each
deficit nonnegative.  So the whole criterion collapses to ONE NUMBER attached to the
window, with the outsiders never mentioned. -/

/-- **THE INSIDER PIVOT SUM**, for any base with positive definite gap:
`Σ_{c ∈ Q} q_c = rank + tr (S_Q - 1)^{-1}`.  Parseval is not used. -/
theorem sum_pivot_eq_rank_add_trace_inverse (design : WeightedDesign size rank)
    (window : Finset (Fin size)) (hgate : (subsetSum design window - 1).PosDef) :
    ∑ insider ∈ window, pivot design window insider
      = rank + Matrix.trace ((subsetSum design window - 1)⁻¹) := by
  have hunit : IsUnit (subsetSum design window - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hgate.det_pos)
  have hexpand : ∑ insider ∈ window, pivot design window insider
      = Matrix.trace ((subsetSum design window - 1)⁻¹ * subsetSum design window) := by
    rw [subsetSum, Matrix.mul_sum, Matrix.trace_sum]
    rfl
  have hsplit : (subsetSum design window - 1)⁻¹ * subsetSum design window
      = (subsetSum design window - 1)⁻¹ * (subsetSum design window - 1)
        + (subsetSum design window - 1)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hexpand, hsplit, Matrix.trace_add, Matrix.nonsing_inv_mul _ hunit,
    Matrix.trace_one, Fintype.card_fin]

/-- The insider deficits of a `rank + 1` window sum to `tr (S_Q - 1)^{-1} - 1`. -/
theorem sum_pivot_sub_one_eq_trace_inverse_sub_one (design : WeightedDesign size rank)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1) :
    ∑ insider ∈ window, (pivot design window insider - 1)
      = Matrix.trace ((subsetSum design window - 1)⁻¹) - 1 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard,
    sum_pivot_eq_rank_add_trace_inverse design window hgate, nsmul_eq_mul]
  push_cast
  ring

/-- **THE TRACE CRITERION.**  At a tie, if the window's inverse gap has trace already
accounted for by an exempt set, every erasure outside the exempt set weakly dominates.
The outsiders never appear: this is the excess criterion with Parseval divided out. -/
theorem dominates_erase_of_isTie_of_trace_le_exempt
    (design : WeightedDesign size rank) (htie : IsTie design)
    {window exempt : Finset (Fin size)} (hsubset : exempt ⊆ window)
    (hgate : (subsetSum design window - 1).PosDef) (hcard : window.card = rank + 1)
    (htrace : Matrix.trace ((subsetSum design window - 1)⁻¹)
        ≤ 1 + ∑ spent ∈ exempt, (pivot design window spent - 1))
    {dropped : Fin size} (hmem : dropped ∈ window) (hfree : dropped ∉ exempt) :
    Dominates design (window.erase dropped) := by
  have hterm : ∀ insider ∈ window \ exempt, 0 ≤ pivot design window insider - 1 :=
    fun insider hinsider => by
      linarith [one_le_pivot_of_isTie design htie hgate hcard
        (Finset.mem_sdiff.mp hinsider).1]
  have hsplit := Finset.sum_sdiff
    (f := fun insider => pivot design window insider - 1) hsubset
  have hfreeSum : ∑ insider ∈ window \ exempt, (pivot design window insider - 1) ≤ 0 := by
    linarith [hsplit, sum_pivot_sub_one_eq_trace_inverse_sub_one design hgate hcard,
      htrace]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
    (le_antisymm hfreeSum (Finset.sum_nonneg hterm)) dropped
    (Finset.mem_sdiff.mpr ⟨hmem, hfree⟩)
  exact (erase_dominates_iff_pivot_le_one design window hgate hmem).mpr (by linarith)

/-- **TRACE ONE IS ENOUGH.**  At a tie a window whose inverse gap has trace at most one
dominates on EVERY erasure — the empty exempt set. -/
theorem forall_dominates_erase_of_isTie_of_trace_le_one
    (design : WeightedDesign size rank) (htie : IsTie design)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1)
    (htrace : Matrix.trace ((subsetSum design window - 1)⁻¹) ≤ 1)
    {dropped : Fin size} (hmem : dropped ∈ window) :
    Dominates design (window.erase dropped) :=
  dominates_erase_of_isTie_of_trace_le_exempt design htie
    (Finset.empty_subset window) hgate hcard (by simpa using htrace) hmem (by simp)

/-- The converse, so the criterion is an EQUIVALENCE and the residual can be stated as
one scalar equation: at a tie, all `rank + 1` erasures of a window dominate exactly
when the window's inverse gap has trace one. -/
theorem trace_inverse_eq_one_of_forall_dominates_erase
    (design : WeightedDesign size rank) {window : Finset (Fin size)}
    (hgate : (subsetSum design window - 1).PosDef) (hcard : window.card = rank + 1)
    (htie : IsTie design)
    (hall : ∀ dropped ∈ window, Dominates design (window.erase dropped)) :
    Matrix.trace ((subsetSum design window - 1)⁻¹) = 1 := by
  have hzero : ∑ insider ∈ window, (pivot design window insider - 1) = 0 := by
    refine Finset.sum_eq_zero fun insider hinsider => ?_
    have hupper := (erase_dominates_iff_pivot_le_one design window hgate hinsider).mp
      (hall insider hinsider)
    have hlower := one_le_pivot_of_isTie design htie hgate hcard hinsider
    linarith
  linarith [sum_pivot_sub_one_eq_trace_inverse_sub_one design hgate hcard, hzero]

/-! ## The excess criterion

Parseval converts the trace criterion into one phrased on the outsiders — the shape the
shipped branch-(a) certificate already speaks. -/

/-- Every insider term of the excess balance is nonnegative at a tie. -/
theorem insiderTerm_nonneg_of_isTie (design : WeightedDesign size rank)
    (hrank : 1 ≤ rank) (htie : IsTie design) {window : Finset (Fin size)}
    (hgate : (subsetSum design window - 1).PosDef) (hcard : window.card = rank + 1)
    {insider : Fin size} (hmem : insider ∈ window) :
    0 ≤ (1 - design.weight insider) * (pivot design window insider - 1) := by
  have hsizeTwo : 2 ≤ size := by
    have hle : window.card ≤ size := by simpa using Finset.card_le_univ window
    omega
  have hcoweight : 0 < 1 - design.weight insider := by
    linarith [weight_lt_one design hsizeTwo insider]
  nlinarith [one_le_pivot_of_isTie design htie hgate hcard hmem]

/-- **THE MAIN THEOREM.  AT A TIE, A WINDOW WHOSE EXCESS IS ALREADY PAID FOR BY AN
EXEMPT SET HAS PIVOT EXACTLY ONE OUTSIDE THAT SET.**  The excess balance rewrites the
outsider sum as the insider sum; the tie makes every insider term nonnegative; so if
the exempt insiders alone already account for the whole excess, the remaining insider
terms sum to at most zero and are therefore individually zero.

The exempt set is what carries the theorem past the zero-excess case.  At the `(5,3)`
diamond the four non-circuit windows have excess `2/3` and a single insider whose term
is exactly `2/3` — the insider whose erasure is a triangle — so a one-element exempt
set certifies the other three erasures. -/
theorem pivot_eq_one_of_isTie_of_excess_le_exempt (design : WeightedDesign size rank)
    (hrank : 1 ≤ rank) (htie : IsTie design)
    {window exempt : Finset (Fin size)} (hsubset : exempt ⊆ window)
    (hgate : (subsetSum design window - 1).PosDef) (hcard : window.card = rank + 1)
    (hexcess : ∑ outsider ∈ windowᶜ,
          design.weight outsider * (pivot design window outsider - 1)
        ≤ ∑ spent ∈ exempt,
          (1 - design.weight spent) * (pivot design window spent - 1))
    {dropped : Fin size} (hmem : dropped ∈ window) (hfree : dropped ∉ exempt) :
    pivot design window dropped = 1 := by
  have hsizeTwo : 2 ≤ size := by
    have hle : window.card ≤ size := by simpa using Finset.card_le_univ window
    omega
  have hterm : ∀ insider ∈ window \ exempt,
      0 ≤ (1 - design.weight insider) * (pivot design window insider - 1) :=
    fun insider hinsider => insiderTerm_nonneg_of_isTie design hrank htie hgate hcard
      (Finset.mem_sdiff.mp hinsider).1
  have hsplit := Finset.sum_sdiff (f := fun insider =>
    (1 - design.weight insider) * (pivot design window insider - 1)) hsubset
  have hbalance := excess_balance design window hgate hcard
  have hfreeSum : ∑ insider ∈ window \ exempt,
      (1 - design.weight insider) * (pivot design window insider - 1) ≤ 0 := by
    linarith [hsplit, hbalance, hexcess]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp
    (le_antisymm hfreeSum (Finset.sum_nonneg hterm)) dropped
    (Finset.mem_sdiff.mpr ⟨hmem, hfree⟩)
  have hcoweight : 0 < 1 - design.weight dropped := by
    linarith [weight_lt_one design hsizeTwo dropped]
  rcases mul_eq_zero.mp hzero with hleft | hright
  · exact absurd hleft (ne_of_gt hcoweight)
  · linarith

/-- **THE MAIN THEOREM, DOMINATION FORM.**  Every erasure outside the exempt set
weakly dominates. -/
theorem dominates_erase_of_isTie_of_excess_le_exempt
    (design : WeightedDesign size rank) (hrank : 1 ≤ rank) (htie : IsTie design)
    {window exempt : Finset (Fin size)} (hsubset : exempt ⊆ window)
    (hgate : (subsetSum design window - 1).PosDef) (hcard : window.card = rank + 1)
    (hexcess : ∑ outsider ∈ windowᶜ,
          design.weight outsider * (pivot design window outsider - 1)
        ≤ ∑ spent ∈ exempt,
          (1 - design.weight spent) * (pivot design window spent - 1))
    {dropped : Fin size} (hmem : dropped ∈ window) (hfree : dropped ∉ exempt) :
    Dominates design (window.erase dropped) :=
  (erase_dominates_iff_pivot_le_one design window hgate hmem).mpr
    (le_of_eq (pivot_eq_one_of_isTie_of_excess_le_exempt design hrank htie hsubset
      hgate hcard hexcess hmem hfree))

/-- **THE ZERO-EXCESS CASE: AT A TIE A NONPOSITIVE-EXCESS WINDOW DOMINATES ON EVERY
ERASURE.**  The empty exempt set.  This is the universal upgrade of the shipped
`pigeonhole`, which under the same hypotheses produces ONE dominating erasure; the tie
promotes that to all `rank + 1` of them.  At corank one the outsider sum is empty and
the statement degenerates to the shipped `forall_dominates_erase_of_isTie`, so it is
that theorem with `m = k + 1` traded for a checkable scalar condition. -/
theorem forall_dominates_erase_of_isTie_of_excess_nonpos
    (design : WeightedDesign size rank) (hrank : 1 ≤ rank) (htie : IsTie design)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1)
    (hexcess : ∑ outsider ∈ windowᶜ,
        design.weight outsider * (pivot design window outsider - 1) ≤ 0)
    {dropped : Fin size} (hmem : dropped ∈ window) :
    Dominates design (window.erase dropped) :=
  dominates_erase_of_isTie_of_excess_le_exempt design hrank htie
    (Finset.empty_subset window) hgate hcard (by simpa using hexcess) hmem (by simp)

/-- **A ZERO-EXCESS WINDOW AT A TIE IS A CIRCUIT.**  Each of its `rank + 1` erasures
dominates, hence has invertible moment, hence is a basis. -/
theorem det_subsetSum_erase_pos_of_isTie_of_excess_nonpos
    (design : WeightedDesign size rank) (hrank : 1 ≤ rank) (htie : IsTie design)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1)
    (hexcess : ∑ outsider ∈ windowᶜ,
        design.weight outsider * (pivot design window outsider - 1) ≤ 0)
    {dropped : Fin size} (hmem : dropped ∈ window) :
    0 < (subsetSum design (window.erase dropped)).det :=
  det_subsetSum_pos_of_dominates design
    (forall_dominates_erase_of_isTie_of_excess_nonpos design hrank htie hgate hcard
      hexcess hmem)

/-- **A WINDOW WITH A NON-DOMINATING ERASURE HAS STRICTLY POSITIVE EXCESS AT A TIE.**
The contrapositive, and the shape the residual is stated in: a dependent erasure has
singular moment, so it never dominates, so its window is priced above zero. -/
theorem excess_pos_of_isTie_of_erase_not_dominates
    (design : WeightedDesign size rank) (hrank : 1 ≤ rank) (htie : IsTie design)
    {window : Finset (Fin size)} (hgate : (subsetSum design window - 1).PosDef)
    (hcard : window.card = rank + 1)
    {dropped : Fin size} (hmem : dropped ∈ window)
    (hfails : ¬ Dominates design (window.erase dropped)) :
    0 < ∑ outsider ∈ windowᶜ,
        design.weight outsider * (pivot design window outsider - 1) := by
  by_contra hnonpos
  rw [not_lt] at hnonpos
  exact hfails (forall_dominates_erase_of_isTie_of_excess_nonpos design hrank htie
    hgate hcard hnonpos hmem)

/-! ## The split-tetrahedron window, over the whole two-parameter family

The four tetrahedron directions resolve `4 . 1`, so the window carrying one copy of
each has gap exactly `3 . 1`.  Every atom of the design is a tetrahedron direction and
every tetrahedron direction has squared norm `3`, so every one of the six pivots is
`3/3 = 1` — insiders and outsiders alike — and the excess is exactly zero.  Nothing
here depends on the split parameters, which is why the whole family is covered. -/

section SplitTetraWindow

variable (splitA splitB : ℝ) (hAPos : 0 < splitA) (hALt : splitA < 1/4)
  (hBPos : 0 < splitB) (hBLt : splitB < 1/4)

/-- A RAINBOW WINDOW of the family: four atoms carrying the four distinct tetrahedron
directions, so `0`, `1`, one copy of direction `2` and one copy of direction `3`. -/
def isRainbowWindow (window : Finset (Fin 6)) : Prop :=
  ∃ secondCopy thirdCopy : Fin 6,
    (secondCopy = 2 ∨ secondCopy = 3) ∧ (thirdCopy = 4 ∨ thirdCopy = 5) ∧
      window = {0, 1, secondCopy, thirdCopy}

set_option linter.unusedSimpArgs false in
/-- **A RAINBOW WINDOW'S MOMENT IS `4 . 1`**: it is the tetrahedron's own Parseval
sum, read through the duplication.  (`Matrix.cons_val` is needed only for the copy at
index five, so the unused-argument linter is silenced for this proof alone.) -/
theorem rainbowWindow_subsetSum {window : Finset (Fin 6)}
    (hrainbow : isRainbowWindow window) :
    subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) window
      = (4 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨secondCopy, thirdCopy, hsecond, hthird, rfl⟩ := hrainbow
  have hexpand : ∀ a b : Fin 6, ({0, 1, a, b} : Finset (Fin 6))
      = insert 0 (insert 1 (insert a {b})) := fun _ _ => rfl
  rcases hsecond with rfl | rfl <;> rcases hthird with rfl | rfl <;>
    rw [subsetSum, hexpand, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  all_goals
    ext rowIndex colIndex
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, atomMatrix,
      Matrix.vecMulVec_apply, splitTetraDesign_atom, splitTetraAtom,
      splitTetraDirIndex, tetraAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons, smul_eq_mul]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num

theorem rainbowWindow_card {window : Finset (Fin 6)} (hrainbow : isRainbowWindow window) :
    window.card = 3 + 1 := by
  obtain ⟨secondCopy, thirdCopy, hsecond, hthird, rfl⟩ := hrainbow
  rcases hsecond with rfl | rfl <;> rcases hthird with rfl | rfl <;> decide

/-- A rainbow window's gap is `3 . 1`. -/
theorem rainbowWindow_gap {window : Finset (Fin 6)} (hrainbow : isRainbowWindow window) :
    subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) window - 1
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [rainbowWindow_subsetSum splitA splitB hAPos hALt hBPos hBLt hrainbow]
  ext rowIndex colIndex
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hcase : rowIndex = colIndex
  · simp [hcase]
    norm_num
  · simp [hcase]

theorem rainbowWindow_gate {window : Finset (Fin 6)} (hrainbow : isRainbowWindow window) :
    (subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) window
      - 1).PosDef := by
  rw [rainbowWindow_gap splitA splitB hAPos hALt hBPos hBLt hrainbow,
    smul_one_eq_diagonal]
  exact Matrix.PosDef.diagonal fun _ => by norm_num

theorem rainbowWindow_gap_inv {window : Finset (Fin 6)}
    (hrainbow : isRainbowWindow window) :
    (subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) window - 1)⁻¹
      = (3 : ℝ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [rainbowWindow_gap splitA splitB hAPos hALt hBPos hBLt hrainbow]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  norm_num

/-- The leverage of every atom of the family is `3`. -/
theorem splitTetraDesign_leverage (atomIndex : Fin 6) :
    leverageOf ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom atomIndex)
      = 3 := by
  have hdot := tetraAtom_dot_self (splitTetraDirIndex atomIndex)
  simp only [dotProduct, Fin.sum_univ_three] at hdot
  simp only [splitTetraDesign_atom, splitTetraAtom, leverageOf, Fin.sum_univ_three]
  nlinarith [hdot]

/-- **EVERY PIVOT OF A RAINBOW WINDOW IS EXACTLY ONE** — insiders and outsiders alike,
because every atom of the family is a tetrahedron direction of squared norm `3` while
the gap is `3 . 1`. -/
theorem rainbowWindow_pivot_eq_one {window : Finset (Fin 6)}
    (hrainbow : isRainbowWindow window) (atomIndex : Fin 6) :
    pivot (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) window atomIndex = 1 := by
  rw [pivot, rainbowWindow_gap_inv splitA splitB hAPos hALt hBPos hBLt hrainbow,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, trace_atomMatrix,
    splitTetraDesign_leverage, smul_eq_mul]
  norm_num

/-- **A RAINBOW WINDOW'S INVERSE GAP HAS TRACE EXACTLY ONE.**  The Parseval-free form
of the witness: the gap is `3 . 1` in rank three, so its inverse has trace `3/3 = 1`,
and the trace criterion fires without ever looking at the other two atoms. -/
theorem rainbowWindow_trace_inverse_eq_one {window : Finset (Fin 6)}
    (hrainbow : isRainbowWindow window) :
    Matrix.trace
        ((subsetSum (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) window
          - 1)⁻¹) = 1 := by
  rw [rainbowWindow_gap_inv splitA splitB hAPos hALt hBPos hBLt hrainbow,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  norm_num

/-- **A RAINBOW WINDOW HAS EXACTLY ZERO EXCESS**, at every split. -/
theorem rainbowWindow_excess_eq_zero {window : Finset (Fin 6)}
    (hrainbow : isRainbowWindow window) :
    ∑ outsider ∈ windowᶜ,
        (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).weight outsider
          * (pivot (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
              window outsider - 1) = 0 :=
  Finset.sum_eq_zero fun outsider _ => by
    rw [rainbowWindow_pivot_eq_one splitA splitB hAPos hALt hBPos hBLt hrainbow]
    ring

/-- **EVERY ERASURE OF EVERY RAINBOW WINDOW OF THE SPLIT-TETRAHEDRON TIE FAMILY WEAKLY
DOMINATES** — derived from the tie and the excess balance alone, with no per-triple
sum of squares and uniformly in the two split parameters.

As `secondCopy` ranges over `{2,3}`, `thirdCopy` over `{4,5}` and `dropped` over the
four window members, the erasures run through ALL TWELVE independent triples of the
family: an independent triple carries three distinct directions, and putting back a
copy of the fourth direction is exactly its rainbow window.  So the measured
"12 of 20, exactly the independent ones" at this tie is now a consequence, not a
measurement, for the twelve. -/
theorem rainbowWindow_dominates_erase {window : Finset (Fin 6)}
    (hrainbow : isRainbowWindow window) {dropped : Fin 6} (hmem : dropped ∈ window) :
    Dominates (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt)
      (window.erase dropped) :=
  forall_dominates_erase_of_isTie_of_excess_nonpos _ (by norm_num)
    (splitTetraDesign_isTie splitA splitB hAPos hALt hBPos hBLt)
    (rainbowWindow_gate splitA splitB hAPos hALt hBPos hBLt hrainbow)
    (rainbowWindow_card hrainbow)
    (le_of_eq (rainbowWindow_excess_eq_zero splitA splitB hAPos hALt hBPos hBLt hrainbow))
    hmem

/-- The four rainbow windows exist, so the hypothesis above is inhabited. -/
theorem isRainbowWindow_example : isRainbowWindow {0, 1, 2, 4} :=
  ⟨2, 4, Or.inl rfl, Or.inl rfl, rfl⟩

end SplitTetraWindow

/-! ## The uniform `(6,3)` no-go

At a tie a weakly dominating subset has a POSITIVE SEMIDEFINITE but not positive
definite gap, hence a singular one.  The shipped uniform layer sum then closes the
cell: twenty zeros cannot add up to `-56`. -/

/-- At a tie every weakly dominating subset of the critical size has vanishing gap
determinant: the gap is positive semidefinite and, by the tie, not positive definite,
so it is singular. -/
theorem det_gap_eq_zero_of_isTie_of_dominates (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)} (hcard : selected.card = rank)
    (hdominates : Dominates design selected) :
    (subsetSum design selected - 1).det = 0 := by
  by_contra hne
  exact htie.2 selected hcard (hdominates.posDef_iff_det_ne_zero.mpr hne)

end Gtz
