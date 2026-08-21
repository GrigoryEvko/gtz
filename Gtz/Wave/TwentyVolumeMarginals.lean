/-
# The twenty volumes as a measure: marginals, the pair total, and the tie in volume currency

At `(6,3)` the chart of a design is a rank-three projection `P` on `ℝ⁶`, and the
twenty numbers

    `nu_T := det P[T,T] = (∏_{c ∈ T} t_c) · [g_T]²`

total one (`Gtz.volume_budget_sixThree`).  They are the masses of a determinantal
measure on the triples, and the campaign reads the hinge through two GROUPINGS of
them: the four triples through a pair total that pair's squared area, and the four
triples inside the complementary quadruple total that pair's cap slack.  Both
groupings are landed.  What was never written down is the rest of the measure.

## The three marginals

This module names the three quantities and proves that each is a sum of the
volumes above it.

    `Gtz.selectionVolume D a b c = t_a t_b t_c [g_a,g_b,g_c]²`      the triple mass
    `Gtz.pairVolume D p q       = t_p t_q · crossNormSq(g_p,g_q)`   the pair mass
    `Gtz.shareOf D c           = t_c · l_c`                         the point mass

* **`Gtz.sum_selectionVolume_eq_pairVolume`** — `∑_r nu_{pqr} = delta_pq`.  The
  landed row law, read in the volume vocabulary.
* **`Gtz.sum_pairVolume_eq_two_mul_shareOf`** — `∑_q delta_pq = 2 s_p`, hence
  **`Gtz.sum_sum_selectionVolume_eq_two_mul_shareOf`**: the ten triples through a
  label total that label's share.  This is the ONE-POINT MARGINAL and it is new.
  Two landed row laws give it in four lines, and it says that the leverage of an
  atom is a sum of ten volumes.

## The pair total, and a near-parallel pair at every design

Summing the one-point marginal over the labels prices the whole pair layer:

  **`Gtz.sum_sum_pairVolume`:  `∑_p ∑_q delta_pq = 2k`** at every `(m,3)` design,

so the fifteen pairs of a `(6,3)` design carry pair mass exactly three
(`Gtz.sum_fifteen_pairVolume_sixThree`), and by the pigeonhole

  **`Gtz.exists_pairVolume_le_one_fifth_sixThree`: every `(6,3)` design carries a
  pair with `t_p t_q · crossNormSq(g_p,g_q) ≤ 1/5`.**

The constant is SHARP: the six diagonals of the icosahedron give a chart with
constant diagonal `1/2` and constant squared off-diagonal `1/20`, so all fifteen
pair masses are exactly `1/5`.  The complementary total is the same
(`Gtz.sum_fifteen_pairCapSlack_sixThree`), so every `(6,3)` design also carries a
pair whose cap slack is at most `1/5`
(`Gtz.exists_pairCapSlack_le_one_fifth_sixThree`).  These are the first
QUANTITATIVE readings the campaign has of the two halves of the hinge dictionary:
the hinge asks for a pair whose mass is zero, and this says some pair's mass is
already at most a fifth, on both sides at once.

The pair total is not an accident of size six.  It is the design-side reading of
`tr(P²) = tr(P)`: the off-diagonal squares of the chart total `(k - ∑_c s_c²)/2`,
and the pair masses differ from `s_p s_q` by exactly those squares.

## The light-and-heavy dichotomy

`delta_pq - delta'_pq = s_p + s_q - 1` and both are nonnegative, so

  **`Gtz.crossNormSq_pos_of_one_lt_shareOf_sum`** — a pair whose shares total more
  than one is NOT parallel, and
  **`Gtz.pairCapSlack_pos_of_shareOf_sum_lt_one`** — a pair whose shares total less
  than one has a NON-COPLANAR complementary quadruple.

Since the fifteen share sums of a `(6,3)` design average exactly one
(`Gtz.exists_shareOf_sum_le_one_sixThree`, `Gtz.exists_one_le_shareOf_sum_sixThree`), every design
carries a pair of each kind.  The hinge's target is therefore confined to the
light half of the pair list, and its dual target to the heavy half.

## The tie, in volume currency

  **`Gtz.weightProd_mul_tripleGapDet_eq_marginal`:**

    `t_a t_b t_c · D_abc = nu_abc − (t_c delta_ab + t_b delta_ac + t_a delta_bc)`
    `                    + (t_b t_c s_a + t_a t_c s_b + t_a t_b s_c) − t_a t_b t_c` .

Every term on the right is a volume marginal times a weight.  With the marginals
above, the whole right side is a polynomial in the twenty volumes and the six
weights, so the SYLVESTER CONDITION of a triple — hence domination, hence a tie —
lives in that currency and nowhere smaller.  The identity also shows exactly how
the weights enter: the volumes alone cannot decide a tie, because they are a
function of the projection while the tie compares the projection to the weights.

At a tie some triple makes the relation an EQUALITY
(`Gtz.marginal_tie_equality_of_isTie_sixThree`), because a weak dominator that is
not strict has a singular gap.

## Hadamard, and negative association

  **`Gtz.hadamard_sq_tripleBracket`:  `[g_a,g_b,g_c]² ≤ l_a l_b l_c`** ,

the rank-three Hadamard inequality with NO hypothesis, one line from the landed
`Gtz.sq_tripleBracket_le_pairGramDet_mul_leverage`.  Scaled by the weights it is
NEGATIVE ASSOCIATION on the twenty volumes,

  `nu_T ≤ delta_pq · s_r`  and  `nu_T ≤ s_a s_b s_c`

(`Gtz.selectionVolume_le_pairVolume_mul_shareOf`,
`Gtz.selectionVolume_le_shareOf_prod`), and against the budget it forces
**`Gtz.one_le_sum_twenty_shareOf_prod_sixThree`**: the twenty share products of a
`(6,3)` design total at least one.

## The generating polynomial

  **`Gtz.sixThree_volume_generating`:**
  `det(∑_c z_c t_c g_c g_cᵀ) = ∑_T (∏_{i ∈ T} z_i) · nu_T` ,

one line from the landed `Gtz.det_sixAtomCombo`.  The left side is
`det(1 - P + P·diag z)` in the chart, so this is the multi-affine generating
polynomial of the determinantal measure.  Its positive-orthant half of real
stability is proved here — `Gtz.posDef_scaledAtomSum` and
`Gtz.sixThree_volume_generating_pos` — because a positive combination of the
design's atoms dominates the smallest coefficient times the identity.

[MEASURED before proving, `scratchpad/tv-search`, double precision, twenty
thousand random `(6,3)` charts.  `|∑_{p<q} delta_pq − 3| ≤ 2.2e-15`,
`|∑_{p<q} delta'_pq − 3| ≤ 3.1e-15`, `|∑_T nu_T − 1| ≤ 1.3e-15`.  The icosahedron
chart `P = (1 + C/√5)/2` with `C` the symmetric conference matrix of order six is
a projection of rank three with `s ≡ 1/2` and `P_pq² ≡ 1/20`, so all fifteen pair
masses equal `1/5` and the ceiling is attained.  That chart is NOT a tie: its
triples with positive three-cycle have `S_T − 1` positive definite with smallest
eigenvalue `0.658`.]
-/
import Gtz.Wave.ComplementVolumeRowLaw
import Gtz.Wave.VolumeFloorSizeSix
import Gtz.Wave.FlatPairWeakSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The three volumes -/

/-- **THE POINT MASS** of a label: its weighted leverage.  The chart reads it as
the diagonal entry `P_cc` of the projection. -/
noncomputable def shareOf (D : WeightedDesign m k) (label : Fin m) : ℝ :=
  D.weight label * leverageOf (D.atom label)

/-- **THE PAIR MASS** of a pair: its weighted squared area.  The chart reads it as
the two-by-two principal minor `det P[{p,q}]`, and it vanishes exactly at a
parallel pair. -/
noncomputable def pairVolume (D : WeightedDesign m 3) (first second : Fin m) : ℝ :=
  D.weight first * D.weight second * crossNormSq (D.atom first) (D.atom second)

/-- **THE TRIPLE MASS** of a triple: its weighted squared volume.  The chart reads
it as the three-by-three principal minor `det P[T,T]`, and the twenty of them
total one at `(6,3)`. -/
noncomputable def selectionVolume (D : WeightedDesign m 3) (first second third : Fin m) : ℝ :=
  D.weight first * D.weight second * D.weight third
    * tripleBracket (D.atom first) (D.atom second) (D.atom third) ^ 2

/-- The point masses of a design total its rank. -/
theorem sum_shareOf (D : WeightedDesign m k) : ∑ label, shareOf D label = (k : ℝ) := by
  simpa only [shareOf] using sum_weighted_leverage D

theorem shareOf_nonneg (D : WeightedDesign m k) (label : Fin m) : 0 ≤ shareOf D label := by
  refine mul_nonneg (D.weight_pos label).le ?_
  simpa [leverageOf] using
    Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => sq_nonneg (D.atom label i)

theorem shareOf_le_one (D : WeightedDesign m k) (label : Fin m) : shareOf D label ≤ 1 :=
  weight_mul_leverage_le_one_of_design D label

theorem pairVolume_nonneg (D : WeightedDesign m 3) (first second : Fin m) :
    0 ≤ pairVolume D first second :=
  mul_nonneg (mul_nonneg (D.weight_pos first).le (D.weight_pos second).le)
    (crossNormSq_nonneg _ _)

theorem pairVolume_comm (D : WeightedDesign m 3) (first second : Fin m) :
    pairVolume D first second = pairVolume D second first := by
  rw [pairVolume, pairVolume, crossNormSq_eq_leverage_mul_sub_sq,
    crossNormSq_eq_leverage_mul_sub_sq, dotProduct_comm]
  ring

theorem pairVolume_self (D : WeightedDesign m 3) (label : Fin m) :
    pairVolume D label label = 0 := by
  rw [pairVolume, crossNormSq_self, mul_zero]

theorem selectionVolume_nonneg (D : WeightedDesign m 3) (first second third : Fin m) :
    0 ≤ selectionVolume D first second third :=
  mul_nonneg (mul_nonneg (mul_nonneg (D.weight_pos first).le (D.weight_pos second).le)
    (D.weight_pos third).le) (sq_nonneg _)

/-! ### The squared bracket is a symmetric function of its three slots

The bracket changes sign under a transposition, so its square does not change at
all.  The tree owns the two degenerate readings `Gtz.tripleBracket_repeat_outer`
and `Gtz.tripleBracket_repeat_right`; the third one and the two transpositions are
proved here. -/

/-- The bracket of a repeated LEADING pair vanishes.  The tree owns the other two
degenerate readings (`Gtz.tripleBracket_repeat_outer` and
`Gtz.tripleBracket_repeat_first` are both `[a b a] = 0`, and
`Gtz.tripleBracket_repeat_right` is `[a b b] = 0`) but not this one. -/
theorem tripleBracket_repeat_lead (leftVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec leftVec rightVec = 0 := by
  rw [tripleBracket, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The squared bracket is unchanged when the last two slots swap. -/
theorem sq_tripleBracket_swap_right (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleBracket firstVec secondVec thirdVec ^ 2
      = tripleBracket firstVec thirdVec secondVec ^ 2 := by
  simp only [tripleBracket, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The squared bracket is unchanged when the first two slots swap. -/
theorem sq_tripleBracket_swap_left (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleBracket firstVec secondVec thirdVec ^ 2
      = tripleBracket secondVec firstVec thirdVec ^ 2 := by
  simp only [tripleBracket, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

theorem selectionVolume_swap_right (D : WeightedDesign m 3) (first second third : Fin m) :
    selectionVolume D first second third = selectionVolume D first third second := by
  rw [selectionVolume, selectionVolume, sq_tripleBracket_swap_right]
  ring

theorem selectionVolume_swap_left (D : WeightedDesign m 3) (first second third : Fin m) :
    selectionVolume D first second third = selectionVolume D second first third := by
  rw [selectionVolume, selectionVolume, sq_tripleBracket_swap_left]
  ring

theorem selectionVolume_repeat_first (D : WeightedDesign m 3) (first second : Fin m) :
    selectionVolume D first first second = 0 := by
  rw [selectionVolume, tripleBracket_repeat_lead]
  ring

theorem selectionVolume_repeat_outer (D : WeightedDesign m 3) (first second : Fin m) :
    selectionVolume D first second first = 0 := by
  rw [selectionVolume, tripleBracket_repeat_outer]
  ring

theorem selectionVolume_repeat_right (D : WeightedDesign m 3) (first second : Fin m) :
    selectionVolume D first second second = 0 := by
  rw [selectionVolume, tripleBracket_repeat_right]
  ring

/-! ## 2. The two-point marginal

The landed row law says the weighted squared volumes of the triples through a
pair total that pair's squared area.  Scaled by the two weights it says that the
pair mass is the total of the triple masses above it. -/

/-- **THE TWO-POINT MARGINAL.**  The triple masses through a pair total the pair
mass.  This is `Gtz.sum_weight_mul_sq_tripleBracket_crossNormSq` in the volume
vocabulary, at every `(m,3)` design. -/
theorem sum_selectionVolume_eq_pairVolume (D : WeightedDesign m 3) (first second : Fin m) :
    ∑ third, selectionVolume D first second third = pairVolume D first second := by
  have hrow := sum_weight_mul_sq_tripleBracket_crossNormSq D first second
  rw [pairVolume, ← hrow, Finset.mul_sum]
  exact Finset.sum_congr rfl fun third _ => by rw [selectionVolume]; ring

/-! ## 3. The one-point marginal

Summing the two-point marginal over the partner spends the landed wedge row law
`∑_b t_b·w_ab = 2·l_a`, and the point mass falls out. -/

/-- **THE PAIR MASSES AT A LABEL TOTAL TWICE ITS POINT MASS.**  The wedge row law,
scaled by the label's own weight. -/
theorem sum_pairVolume_eq_two_mul_shareOf (D : WeightedDesign m 3) (center : Fin m) :
    ∑ partner, pairVolume D center partner = 2 * shareOf D center := by
  calc ∑ partner, pairVolume D center partner
      = D.weight center * ∑ partner, D.weight partner
          * crossNormSq (D.atom center) (D.atom partner) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun partner _ => by rw [pairVolume]; ring
    _ = D.weight center * (2 * leverageOf (D.atom center)) := by
        rw [sum_weight_mul_crossNormSq D center]
    _ = 2 * shareOf D center := by rw [shareOf]; ring

/-- **THE ONE-POINT MARGINAL.**  The triple masses through a label total that
label's point mass, counted twice by the ordered double sum.  At `(6,3)` the ten
triples through a label total its share, so an atom's leverage is a sum of ten
volumes.  This is new, and it is two landed row laws deep. -/
theorem sum_sum_selectionVolume_eq_two_mul_shareOf (D : WeightedDesign m 3) (center : Fin m) :
    ∑ partner, ∑ third, selectionVolume D center partner third = 2 * shareOf D center := by
  rw [Finset.sum_congr rfl fun partner _ =>
    sum_selectionVolume_eq_pairVolume D center partner]
  exact sum_pairVolume_eq_two_mul_shareOf D center

/-! ## 4. The pair total, and a near-parallel pair at every design -/

/-- **THE PAIR TOTAL.**  The pair masses of an `(m,3)` design total twice the rank,
counted by the ordered double sum.  Nothing about the size enters. -/
theorem sum_sum_pairVolume (D : WeightedDesign m 3) :
    ∑ first, ∑ second, pairVolume D first second = 6 := by
  rw [Finset.sum_congr rfl fun first _ => sum_pairVolume_eq_two_mul_shareOf D first,
    ← Finset.mul_sum, sum_shareOf]
  norm_num

/-- **THE FIFTEEN PAIR MASSES OF A `(6,3)` DESIGN TOTAL THREE.**  The ordered
double sum counts each unordered pair twice and the diagonal contributes
nothing. -/
theorem sum_fifteen_pairVolume_sixThree (D : WeightedDesign 6 3) :
    pairVolume D 0 1 + pairVolume D 0 2 + pairVolume D 0 3 + pairVolume D 0 4
        + pairVolume D 0 5 + pairVolume D 1 2 + pairVolume D 1 3 + pairVolume D 1 4
        + pairVolume D 1 5 + pairVolume D 2 3 + pairVolume D 2 4 + pairVolume D 2 5
        + pairVolume D 3 4 + pairVolume D 3 5 + pairVolume D 4 5
      = 3 := by
  have htotal := sum_sum_pairVolume D
  rw [Fin.sum_univ_six] at htotal
  simp only [Fin.sum_univ_six] at htotal
  have hself : ∀ label : Fin 6, pairVolume D label label = 0 := pairVolume_self D
  rw [hself 0, hself 1, hself 2, hself 3, hself 4, hself 5] at htotal
  rw [pairVolume_comm D 1 0, pairVolume_comm D 2 0, pairVolume_comm D 2 1,
    pairVolume_comm D 3 0, pairVolume_comm D 3 1, pairVolume_comm D 3 2,
    pairVolume_comm D 4 0, pairVolume_comm D 4 1, pairVolume_comm D 4 2,
    pairVolume_comm D 4 3, pairVolume_comm D 5 0, pairVolume_comm D 5 1,
    pairVolume_comm D 5 2, pairVolume_comm D 5 3, pairVolume_comm D 5 4] at htotal
  linarith

/-- **EVERY `(6,3)` DESIGN CARRIES A NEARLY PARALLEL PAIR.**  Fifteen pair masses
total three, so one of them is at most a fifth.  The hinge asks for a pair of mass
ZERO; this is the unconditional quantitative shadow of that question.

SHARP.  The six diagonals of the icosahedron give a chart with constant diagonal
`1/2` and constant squared off-diagonal `1/20`, so all fifteen pair masses are
exactly `1/5`. -/
theorem exists_pairVolume_le_one_fifth_sixThree (D : WeightedDesign 6 3) :
    ∃ first second : Fin 6, first ≠ second ∧ pairVolume D first second ≤ 1 / 5 := by
  by_contra hcon
  push Not at hcon
  have htotal := sum_fifteen_pairVolume_sixThree D
  linarith [hcon 0 1 (by decide), hcon 0 2 (by decide), hcon 0 3 (by decide),
    hcon 0 4 (by decide), hcon 0 5 (by decide), hcon 1 2 (by decide),
    hcon 1 3 (by decide), hcon 1 4 (by decide), hcon 1 5 (by decide),
    hcon 2 3 (by decide), hcon 2 4 (by decide), hcon 2 5 (by decide),
    hcon 3 4 (by decide), hcon 3 5 (by decide), hcon 4 5 (by decide)]

/-! ## 5. The complementary pair total

The cap slack of a pair is its pair mass shifted by the two point masses, so the
complementary layer totals three as well. -/

/-- **THE CAP SLACK IS THE PAIR MASS, SHIFTED BY THE TWO POINT MASSES.** -/
theorem pairCapSlack_eq_one_sub_shareOf_add_pairVolume (D : WeightedDesign m 3)
    (first second : Fin m) :
    pairCapSlack D first second
      = 1 - shareOf D first - shareOf D second + pairVolume D first second := by
  rw [pairCapSlack, shareOf, shareOf, pairVolume, crossNormSq_eq_leverage_mul_sub_sq]
  ring

/-- **THE FIFTEEN CAP SLACKS OF A `(6,3)` DESIGN TOTAL THREE.**  Each label appears
in five pairs and the point masses total three, so the shift cancels the fifteen
ones exactly. -/
theorem sum_fifteen_pairCapSlack_sixThree (D : WeightedDesign 6 3) :
    pairCapSlack D 0 1 + pairCapSlack D 0 2 + pairCapSlack D 0 3 + pairCapSlack D 0 4
        + pairCapSlack D 0 5 + pairCapSlack D 1 2 + pairCapSlack D 1 3 + pairCapSlack D 1 4
        + pairCapSlack D 1 5 + pairCapSlack D 2 3 + pairCapSlack D 2 4 + pairCapSlack D 2 5
        + pairCapSlack D 3 4 + pairCapSlack D 3 5 + pairCapSlack D 4 5
      = 3 := by
  have hshares := sum_shareOf D
  rw [Fin.sum_univ_six] at hshares
  have hpairs := sum_fifteen_pairVolume_sixThree D
  simp only [pairCapSlack_eq_one_sub_shareOf_add_pairVolume]
  push_cast at hshares
  linarith

/-- **EVERY `(6,3)` DESIGN CARRIES A PAIR WHOSE COMPLEMENT IS NEARLY COPLANAR.**
The dual of `Gtz.exists_pairVolume_le_one_fifth_sixThree`: fifteen cap slacks
total three, so one of them is at most a fifth.  The hinge's other half asks for a
cap slack of ZERO. -/
theorem exists_pairCapSlack_le_one_fifth_sixThree (D : WeightedDesign 6 3) :
    ∃ first second : Fin 6, first ≠ second ∧ pairCapSlack D first second ≤ 1 / 5 := by
  by_contra hcon
  push Not at hcon
  have htotal := sum_fifteen_pairCapSlack_sixThree D
  linarith [hcon 0 1 (by decide), hcon 0 2 (by decide), hcon 0 3 (by decide),
    hcon 0 4 (by decide), hcon 0 5 (by decide), hcon 1 2 (by decide),
    hcon 1 3 (by decide), hcon 1 4 (by decide), hcon 1 5 (by decide),
    hcon 2 3 (by decide), hcon 2 4 (by decide), hcon 2 5 (by decide),
    hcon 3 4 (by decide), hcon 3 5 (by decide), hcon 4 5 (by decide)]

/-! ## 6. The light-and-heavy dichotomy

The two layers differ by exactly `s_p + s_q - 1`, so the sign of that number
decides which of the two degeneracies a pair is forbidden. -/

/-- **THE CAP SLACK IS THE DETERMINANT OF THE PAIR'S WEIGHTED COMPLEMENT.**  The
landed `Gtz.det_weightedComplement_pair` evaluates that determinant in the pair's
own vocabulary, and the identity above is the same polynomial. -/
theorem pairCapSlack_eq_det_weightedComplement (D : WeightedDesign m 3)
    {first second : Fin m} (hne : first ≠ second) :
    pairCapSlack D first second
      = (∑ c ∈ ({first, second} : Finset (Fin m))ᶜ,
          D.weight c • atomMatrix (D.atom c)).det := by
  classical
  rw [det_weightedComplement_pair D hne,
    pairCapSlack_eq_one_sub_shareOf_add_pairVolume, shareOf, shareOf, pairVolume]

/-- **THE PAIRING CAP AT EVERY SIZE.**  The complement of a pair is positive
semidefinite, so its determinant is nonnegative.  The landed
`Gtz.pairCapSlack_nonneg'` proves this at `(6,3)` through the Naimark dual and the
four complementary volumes; this proof needs neither, and it holds at every
`(m,3)` design. -/
theorem pairCapSlack_nonneg_of_ne (D : WeightedDesign m 3) {first second : Fin m}
    (hne : first ≠ second) : 0 ≤ pairCapSlack D first second := by
  classical
  rw [pairCapSlack_eq_det_weightedComplement D hne]
  exact (posSemidef_weightedSubsum D (({first, second} : Finset (Fin m))ᶜ)).det_nonneg

/-- **THE TWO LAYERS DIFFER BY THE SHARE DEFICIT.** -/
theorem pairVolume_sub_pairCapSlack (D : WeightedDesign m 3) (first second : Fin m) :
    pairVolume D first second - pairCapSlack D first second
      = shareOf D first + shareOf D second - 1 := by
  rw [pairCapSlack_eq_one_sub_shareOf_add_pairVolume]
  ring

/-- **A HEAVY PAIR IS NOT PARALLEL.**  When the two shares total more than one the
pair mass is strictly positive, so the two atoms are independent.  The landed
`Gtz.share_add_share_le_one_of_crossNormSq_eq_zero` is the contrapositive on the
squared area; this is the reading on the mass. -/
theorem pairVolume_pos_of_one_lt_shareOf_sum (D : WeightedDesign m 3) {first second : Fin m}
    (hne : first ≠ second) (hheavy : 1 < shareOf D first + shareOf D second) :
    0 < pairVolume D first second := by
  have hslack := pairVolume_sub_pairCapSlack D first second
  have hcapNonneg := pairCapSlack_nonneg_of_ne D hne
  linarith

/-- **A HEAVY PAIR IS NOT PARALLEL, ON THE SQUARED AREA.** -/
theorem crossNormSq_pos_of_one_lt_shareOf_sum (D : WeightedDesign m 3) {first second : Fin m}
    (hne : first ≠ second) (hheavy : 1 < shareOf D first + shareOf D second) :
    0 < crossNormSq (D.atom first) (D.atom second) := by
  have hmass := pairVolume_pos_of_one_lt_shareOf_sum D hne hheavy
  rw [pairVolume] at hmass
  by_contra hcon
  push Not at hcon
  nlinarith [hmass, mul_pos (D.weight_pos first) (D.weight_pos second), hcon]

/-- **A LIGHT PAIR HAS A NON-DEGENERATE COMPLEMENT.**  When the two shares total
less than one the cap slack is strictly positive, so at `(6,3)` the complementary
quadruple is NOT coplanar.  This is the exact dual of the landed statement that a
parallel pair is light, and it needs no dual design. -/
theorem pairCapSlack_pos_of_shareOf_sum_lt_one (D : WeightedDesign m 3) (first second : Fin m)
    (hlight : shareOf D first + shareOf D second < 1) :
    0 < pairCapSlack D first second := by
  have hslack := pairCapSlack_eq_one_sub_shareOf_add_pairVolume D first second
  have hmass := pairVolume_nonneg D first second
  linarith

/-- **A `(6,3)` DESIGN CARRIES A LIGHT PAIR.**  The fifteen share sums average
exactly one, because each label sits in five pairs and the six shares total
three. -/
theorem exists_shareOf_sum_le_one_sixThree (D : WeightedDesign 6 3) :
    ∃ first second : Fin 6, first ≠ second ∧ shareOf D first + shareOf D second ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hshares := sum_shareOf D
  rw [Fin.sum_univ_six] at hshares
  push_cast at hshares
  linarith [hcon 0 1 (by decide), hcon 0 2 (by decide), hcon 0 3 (by decide),
    hcon 0 4 (by decide), hcon 0 5 (by decide), hcon 1 2 (by decide),
    hcon 1 3 (by decide), hcon 1 4 (by decide), hcon 1 5 (by decide),
    hcon 2 3 (by decide), hcon 2 4 (by decide), hcon 2 5 (by decide),
    hcon 3 4 (by decide), hcon 3 5 (by decide), hcon 4 5 (by decide)]

/-- **A `(6,3)` DESIGN CARRIES A HEAVY PAIR**, hence a pair that CANNOT be
parallel. -/
theorem exists_one_le_shareOf_sum_sixThree (D : WeightedDesign 6 3) :
    ∃ first second : Fin 6, first ≠ second ∧ 1 ≤ shareOf D first + shareOf D second := by
  by_contra hcon
  push Not at hcon
  have hshares := sum_shareOf D
  rw [Fin.sum_univ_six] at hshares
  push_cast at hshares
  linarith [hcon 0 1 (by decide), hcon 0 2 (by decide), hcon 0 3 (by decide),
    hcon 0 4 (by decide), hcon 0 5 (by decide), hcon 1 2 (by decide),
    hcon 1 3 (by decide), hcon 1 4 (by decide), hcon 1 5 (by decide),
    hcon 2 3 (by decide), hcon 2 4 (by decide), hcon 2 5 (by decide),
    hcon 3 4 (by decide), hcon 3 5 (by decide), hcon 4 5 (by decide)]

/-! ## 7. Hadamard at rank three, and negative association -/

/-- **HADAMARD AT RANK THREE.**  The squared volume of three vectors never exceeds
the product of their three squared lengths.  One line from the landed
`Gtz.sq_tripleBracket_le_pairGramDet_mul_leverage`, which caps the squared bracket
by the pair's squared area times the third leverage.

This UNCONDITIONAL form strengthens the landed `Gtz.sq_tripleBracket_le_leverage_prod`,
which reaches the same conclusion from two positive pair minors and three strict
leverages.  Negative association needs the free form, because it is asked at every
triple of every design and most triples of a design are not admissible. -/
theorem hadamard_sq_tripleBracket (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleBracket firstVec secondVec thirdVec ^ 2
      ≤ leverageOf firstVec * leverageOf secondVec * leverageOf thirdVec := by
  have hcap := sq_tripleBracket_le_pairGramDet_mul_leverage firstVec secondVec thirdVec
  have hthird : 0 ≤ leverageOf thirdVec := by
    simpa [leverageOf] using
      Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => sq_nonneg (thirdVec i)
  nlinarith [hcap, hthird, sq_nonneg (firstVec ⬝ᵥ secondVec)]

/-- **NEGATIVE ASSOCIATION, PAIR AGAINST POINT.**  A triple mass never exceeds the
pair mass of two of its labels times the point mass of the third.  In the
determinantal reading: the chance of drawing the triple never exceeds the chance
of drawing the pair times the chance of drawing the point. -/
theorem selectionVolume_le_pairVolume_mul_shareOf (D : WeightedDesign m 3)
    (first second third : Fin m) :
    selectionVolume D first second third ≤ pairVolume D first second * shareOf D third := by
  have hcap := sq_tripleBracket_le_pairGramDet_mul_leverage (D.atom first) (D.atom second)
    (D.atom third)
  have hweights : 0 < D.weight first * D.weight second * D.weight third :=
    mul_pos (mul_pos (D.weight_pos first) (D.weight_pos second)) (D.weight_pos third)
  rw [selectionVolume, pairVolume, shareOf, crossNormSq_eq_leverage_mul_sub_sq]
  nlinarith [hcap, hweights]

/-- **NEGATIVE ASSOCIATION, THREE POINTS.**  A triple mass never exceeds the
product of the three point masses.  The prior lane measured this at eight hundred
designs and did not prove it; it is Hadamard scaled by the weights. -/
theorem selectionVolume_le_shareOf_prod (D : WeightedDesign m 3) (first second third : Fin m) :
    selectionVolume D first second third
      ≤ shareOf D first * shareOf D second * shareOf D third := by
  have hcap := hadamard_sq_tripleBracket (D.atom first) (D.atom second) (D.atom third)
  have hweights : 0 < D.weight first * D.weight second * D.weight third :=
    mul_pos (mul_pos (D.weight_pos first) (D.weight_pos second)) (D.weight_pos third)
  rw [selectionVolume, shareOf, shareOf, shareOf]
  nlinarith [hcap, hweights]

/-- **THE TWENTY SHARE PRODUCTS OF A `(6,3)` DESIGN TOTAL AT LEAST ONE.**  Negative
association caps each triple mass by its share product, and the twenty triple
masses total one.  With the six shares totalling three and each at most one, this
is a genuine constraint: the share vector `(1,1,1,0,0,0)` attains it. -/
theorem one_le_sum_twenty_shareOf_prod_sixThree (D : WeightedDesign 6 3) :
    1 ≤ shareOf D 0 * shareOf D 1 * shareOf D 2 + shareOf D 0 * shareOf D 1 * shareOf D 3
      + shareOf D 0 * shareOf D 1 * shareOf D 4 + shareOf D 0 * shareOf D 1 * shareOf D 5
      + shareOf D 0 * shareOf D 2 * shareOf D 3 + shareOf D 0 * shareOf D 2 * shareOf D 4
      + shareOf D 0 * shareOf D 2 * shareOf D 5 + shareOf D 0 * shareOf D 3 * shareOf D 4
      + shareOf D 0 * shareOf D 3 * shareOf D 5 + shareOf D 0 * shareOf D 4 * shareOf D 5
      + shareOf D 1 * shareOf D 2 * shareOf D 3 + shareOf D 1 * shareOf D 2 * shareOf D 4
      + shareOf D 1 * shareOf D 2 * shareOf D 5 + shareOf D 1 * shareOf D 3 * shareOf D 4
      + shareOf D 1 * shareOf D 3 * shareOf D 5 + shareOf D 1 * shareOf D 4 * shareOf D 5
      + shareOf D 2 * shareOf D 3 * shareOf D 4 + shareOf D 2 * shareOf D 3 * shareOf D 5
      + shareOf D 2 * shareOf D 4 * shareOf D 5
      + shareOf D 3 * shareOf D 4 * shareOf D 5 := by
  have hbudget := volume_budget_sixThree D
  have hstep : ∀ a b c : Fin 6, D.weight a * D.weight b * D.weight c
      * tripleBracket (D.atom a) (D.atom b) (D.atom c) ^ 2
      ≤ shareOf D a * shareOf D b * shareOf D c := by
    intro a b c
    have h := selectionVolume_le_shareOf_prod D a b c
    rwa [selectionVolume] at h
  linarith [hstep 0 1 2, hstep 0 1 3, hstep 0 1 4, hstep 0 1 5, hstep 0 2 3, hstep 0 2 4,
    hstep 0 2 5, hstep 0 3 4, hstep 0 3 5, hstep 0 4 5, hstep 1 2 3, hstep 1 2 4,
    hstep 1 2 5, hstep 1 3 4, hstep 1 3 5, hstep 1 4 5, hstep 2 3 4, hstep 2 3 5,
    hstep 2 4 5, hstep 3 4 5]

/-! ## 8. The tie, in volume currency -/

/-- **THE SYLVESTER DETERMINANT OF A TRIPLE, IN VOLUME CURRENCY.**  Scaling the
landed characteristic expansion by the three weights turns every term into a
volume marginal times a weight: the triple mass, the three pair masses of the
triple, the three point masses, and the weight product.

With the marginals of sections 2 and 3 this is a polynomial in the twenty volumes
and the six weights.  It also shows why the volumes alone cannot decide a tie: the
volumes are a function of the chart projection while the weights enter this
identity separately. -/
theorem weightProd_mul_tripleGapDet_eq_marginal (D : WeightedDesign m 3) (a b c : Fin m) :
    D.weight a * D.weight b * D.weight c
        * tripleGapDet (D.atom a) (D.atom b) (D.atom c)
      = selectionVolume D a b c
        - (D.weight c * pairVolume D a b + D.weight b * pairVolume D a c
            + D.weight a * pairVolume D b c)
        + (D.weight b * D.weight c * shareOf D a + D.weight a * D.weight c * shareOf D b
            + D.weight a * D.weight b * shareOf D c)
        - D.weight a * D.weight b * D.weight c := by
  rw [tripleGapDet_eq_thirdInvariant, selectionVolume, pairVolume, pairVolume, pairVolume,
    shareOf, shareOf, shareOf, triplePairAreaSum, tripleLeverageSum]
  ring

/-- The gap determinant of a triple is the determinant of its Gram gap. -/
theorem tripleGapDet_eq_det_tripleGram_sub_one (firstVec secondVec thirdVec : Fin 3 → ℝ) :
    tripleGapDet firstVec secondVec thirdVec
      = (tripleGram firstVec secondVec thirdVec - 1).det := by
  rw [tripleGapDet, Matrix.det_fin_three]
  simp only [gap_zero_zero, gap_one_one, gap_two_two, gap_zero_one, gap_zero_two,
    gap_one_two, gap_one_zero, gap_two_zero, gap_two_one]
  ring

/-- **A WEAK DOMINATOR HAS A NONNEGATIVE GAP DETERMINANT.** -/
theorem tripleGapDet_nonneg_of_dominates_triple (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    0 ≤ tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  have hpsd := (dominates_triple_iff_tripleGram_posSemidef D x y z hxy hxz hyz).mp hdom
  rw [tripleGapDet_eq_det_tripleGram_sub_one]
  exact hpsd.det_nonneg

/-- **A WEAK DOMINATOR THAT IS NOT STRICT HAS A VANISHING GAP DETERMINANT.**  A
positive semidefinite matrix is positive definite exactly when its determinant is
nonzero, so the gap of a tie's dominator is singular. -/
theorem tripleGapDet_eq_zero_of_dominates_of_not_posDef (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m)))
    (hnotstrict : ¬ (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) = 0 := by
  have hpsd := (dominates_triple_iff_tripleGram_posSemidef D x y z hxy hxz hyz).mp hdom
  have hnot : ¬ (tripleGram (D.atom x) (D.atom y) (D.atom z) - 1).PosDef := by
    intro hstrict
    exact hnotstrict ((subsetSum_posDef_iff_tripleGram D x y z hxy hxz hyz).mpr hstrict)
  rw [tripleGapDet_eq_det_tripleGram_sub_one]
  by_contra hne
  exact hnot (hpsd.posDef_iff_det_ne_zero.mpr hne)

/-- **THE MARGINAL RELATION AT A WEAK DOMINATOR.**  Its gap determinant is
nonnegative, so the triple mass and the three point masses together dominate the
three pair masses and the weight product. -/
theorem marginal_relation_of_dominates (D : WeightedDesign m 3) (x y z : Fin m)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin m))) :
    D.weight z * pairVolume D x y + D.weight y * pairVolume D x z
        + D.weight x * pairVolume D y z + D.weight x * D.weight y * D.weight z
      ≤ selectionVolume D x y z
        + (D.weight y * D.weight z * shareOf D x + D.weight x * D.weight z * shareOf D y
          + D.weight x * D.weight y * shareOf D z) := by
  have hlaw := weightProd_mul_tripleGapDet_eq_marginal D x y z
  have hdet := tripleGapDet_nonneg_of_dominates_triple D x y z hxy hxz hyz hdom
  have hprod : 0 < D.weight x * D.weight y * D.weight z :=
    mul_pos (mul_pos (D.weight_pos x) (D.weight_pos y)) (D.weight_pos z)
  nlinarith [hlaw, hdet, hprod]

/-- **THE MARGINAL RELATION IS AN EQUALITY AT A TIE.**  A tie carries a weak
dominator and no strict one, so that dominator's gap determinant vanishes and the
marginal relation closes.  This is the tie condition of `Gtz.IsTie` written
entirely in the volume vocabulary: one linear relation among a triple mass, three
pair masses, three point masses and the weight product. -/
theorem marginal_tie_equality_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdom : Dominates D ({x, y, z} : Finset (Fin 6))) :
    selectionVolume D x y z
        + (D.weight y * D.weight z * shareOf D x + D.weight x * D.weight z * shareOf D y
          + D.weight x * D.weight y * shareOf D z)
      = D.weight z * pairVolume D x y + D.weight y * pairVolume D x z
        + D.weight x * pairVolume D y z + D.weight x * D.weight y * D.weight z := by
  have hcard : ({x, y, z} : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hzero := tripleGapDet_eq_zero_of_dominates_of_not_posDef D x y z hxy hxz hyz hdom
    (htie.2 _ hcard)
  have hlaw := weightProd_mul_tripleGapDet_eq_marginal D x y z
  rw [hzero, mul_zero] at hlaw
  linarith

/-! ## 9. The generating polynomial of the twenty volumes -/

/-- **A POSITIVE COMBINATION OF THE ATOMS IS POSITIVE DEFINITE.**  Parseval makes
the design's own weighted total the identity, so any coefficient vector bounded
below by a positive number gives a matrix bounded below by that number times the
identity.  No rank argument and no spanning hypothesis appear. -/
theorem posDef_scaledAtomSum (D : WeightedDesign m k) [Nonempty (Fin m)]
    {scale : Fin m → ℝ} (hscale : ∀ c, 0 < scale c) :
    (∑ c, (scale c * D.weight c) • atomMatrix (D.atom c)).PosDef := by
  classical
  obtain ⟨argmin, hargmin⟩ := Finite.exists_min scale
  have hfloorPos : 0 < scale argmin := hscale argmin
  have hsplit : ∑ c, (scale c * D.weight c) • atomMatrix (D.atom c)
      = scale argmin • (1 : Matrix (Fin k) (Fin k) ℝ)
        + ∑ c, ((scale c - scale argmin) * D.weight c) • atomMatrix (D.atom c) := by
    rw [← D.isParseval, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_smul, ← add_smul]
    congr 1
    ring
  rw [hsplit]
  refine Matrix.PosDef.add_posSemidef (Matrix.PosDef.smul Matrix.PosDef.one hfloorPos) ?_
  refine Matrix.posSemidef_sum Finset.univ fun c _ => ?_
  exact (posSemidef_atomMatrix (D.atom c)).smul
    (mul_nonneg (by linarith [hargmin c]) (D.weight_pos c).le)

/-- **THE GENERATING POLYNOMIAL OF THE TWENTY VOLUMES.**  Scaling the atoms of a
`(6,3)` design by an arbitrary vector and taking the determinant produces the
multi-affine generating polynomial of the twenty triple masses.  In the chart the
left side is `det(1 - P + P·diag z)`, so this is the generating polynomial of the
determinantal measure.  One line from the landed `Gtz.det_sixAtomCombo`. -/
theorem sixThree_volume_generating (D : WeightedDesign 6 3) (scale : Fin 6 → ℝ) :
    (∑ c, (scale c * D.weight c) • atomMatrix (D.atom c)).det
      = scale 0 * scale 1 * scale 2 * selectionVolume D 0 1 2
        + scale 0 * scale 1 * scale 3 * selectionVolume D 0 1 3
        + scale 0 * scale 1 * scale 4 * selectionVolume D 0 1 4
        + scale 0 * scale 1 * scale 5 * selectionVolume D 0 1 5
        + scale 0 * scale 2 * scale 3 * selectionVolume D 0 2 3
        + scale 0 * scale 2 * scale 4 * selectionVolume D 0 2 4
        + scale 0 * scale 2 * scale 5 * selectionVolume D 0 2 5
        + scale 0 * scale 3 * scale 4 * selectionVolume D 0 3 4
        + scale 0 * scale 3 * scale 5 * selectionVolume D 0 3 5
        + scale 0 * scale 4 * scale 5 * selectionVolume D 0 4 5
        + scale 1 * scale 2 * scale 3 * selectionVolume D 1 2 3
        + scale 1 * scale 2 * scale 4 * selectionVolume D 1 2 4
        + scale 1 * scale 2 * scale 5 * selectionVolume D 1 2 5
        + scale 1 * scale 3 * scale 4 * selectionVolume D 1 3 4
        + scale 1 * scale 3 * scale 5 * selectionVolume D 1 3 5
        + scale 1 * scale 4 * scale 5 * selectionVolume D 1 4 5
        + scale 2 * scale 3 * scale 4 * selectionVolume D 2 3 4
        + scale 2 * scale 3 * scale 5 * selectionVolume D 2 3 5
        + scale 2 * scale 4 * scale 5 * selectionVolume D 2 4 5
        + scale 3 * scale 4 * scale 5 * selectionVolume D 3 4 5 := by
  rw [Fin.sum_univ_six, det_sixAtomCombo]
  simp only [selectionVolume]
  ring

/-- **THE GENERATING POLYNOMIAL IS STRICTLY POSITIVE ON THE POSITIVE ORTHANT.**
This is the real half of the stability of the determinantal measure, proved from
Parseval alone.  At the all-ones vector it reproduces the volume budget. -/
theorem sixThree_volume_generating_pos (D : WeightedDesign 6 3) {scale : Fin 6 → ℝ}
    (hscale : ∀ c, 0 < scale c) :
    0 < scale 0 * scale 1 * scale 2 * selectionVolume D 0 1 2
      + scale 0 * scale 1 * scale 3 * selectionVolume D 0 1 3
      + scale 0 * scale 1 * scale 4 * selectionVolume D 0 1 4
      + scale 0 * scale 1 * scale 5 * selectionVolume D 0 1 5
      + scale 0 * scale 2 * scale 3 * selectionVolume D 0 2 3
      + scale 0 * scale 2 * scale 4 * selectionVolume D 0 2 4
      + scale 0 * scale 2 * scale 5 * selectionVolume D 0 2 5
      + scale 0 * scale 3 * scale 4 * selectionVolume D 0 3 4
      + scale 0 * scale 3 * scale 5 * selectionVolume D 0 3 5
      + scale 0 * scale 4 * scale 5 * selectionVolume D 0 4 5
      + scale 1 * scale 2 * scale 3 * selectionVolume D 1 2 3
      + scale 1 * scale 2 * scale 4 * selectionVolume D 1 2 4
      + scale 1 * scale 2 * scale 5 * selectionVolume D 1 2 5
      + scale 1 * scale 3 * scale 4 * selectionVolume D 1 3 4
      + scale 1 * scale 3 * scale 5 * selectionVolume D 1 3 5
      + scale 1 * scale 4 * scale 5 * selectionVolume D 1 4 5
      + scale 2 * scale 3 * scale 4 * selectionVolume D 2 3 4
      + scale 2 * scale 3 * scale 5 * selectionVolume D 2 3 5
      + scale 2 * scale 4 * scale 5 * selectionVolume D 2 4 5
      + scale 3 * scale 4 * scale 5 * selectionVolume D 3 4 5 := by
  rw [← sixThree_volume_generating D scale]
  exact (posDef_scaledAtomSum D hscale).det_pos

/-- **THE VOLUME BUDGET, FROM THE GENERATING POLYNOMIAL.**  Reading it at the
all-ones vector recovers `Gtz.volume_budget_sixThree`, so the budget is the value
of one polynomial at one point. -/
theorem sixThree_volume_generating_one (D : WeightedDesign 6 3) :
    selectionVolume D 0 1 2 + selectionVolume D 0 1 3 + selectionVolume D 0 1 4
        + selectionVolume D 0 1 5 + selectionVolume D 0 2 3 + selectionVolume D 0 2 4
        + selectionVolume D 0 2 5 + selectionVolume D 0 3 4 + selectionVolume D 0 3 5
        + selectionVolume D 0 4 5 + selectionVolume D 1 2 3 + selectionVolume D 1 2 4
        + selectionVolume D 1 2 5 + selectionVolume D 1 3 4 + selectionVolume D 1 3 5
        + selectionVolume D 1 4 5 + selectionVolume D 2 3 4 + selectionVolume D 2 3 5
        + selectionVolume D 2 4 5 + selectionVolume D 3 4 5
      = 1 := by
  have hbudget := volume_budget_sixThree D
  simp only [selectionVolume]
  linarith

end Gtz
