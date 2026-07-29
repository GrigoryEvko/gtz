/-
# V2 of the pen campaign: the capacity order statistics of a uniform-share design

The V6 layer of the pen argument reads domination of a triple `T` off the matrix
`D_tau[T] + M[T]`, where `M = Gamma - 1` is the hollow correlation matrix of the
directions and `D_tau = diag(tau_a, tau_b, tau_c)` is built from the WEIGHTS
through

    tau_c = 1 - 1/l_c        (`Gtz.atomCapacity`, the atom's CAPACITY),

`l_c = |g_c|^2` being the leverage.  So the covering question is: which capacity
vectors `tau` can an adversary present?  V2 answers it, and the answer is a
budget: the adversary has a fixed total to spend and a hard per-atom ceiling, so
he cannot make many atoms cheap at once.

## The engine, and it is one identity

Everything here descends from ONE law, which is new in this file:

**THE RECIPROCAL LEVERAGE LAW** (`sum_inv_leverage_of_uniformShare`).  On a
design whose every share `s_c = t_c l_c` equals `k/m`,

    sum_c 1/l_c = m/k.

The proof is two lines: uniform share forces `1/l_c = (m/k) t_c` atom by atom
(`inv_leverage_eq_size_div_rank_mul_weight`), and the weights sum to one.  Its
capacity reading is `sum_c tau_c = m - m/k` (`sum_atomCapacity_of_uniformShare`),
which at `(6,3)` is the pen's `sum tau = 4`.

The reciprocal leverages are POSITIVE, and that is the only ceiling the argument
needs — the pen's `tau_c < 1` in disguise.  So the order statistics are just
"the minimum is at most the average, and strictly so once something positive is
thrown away":

**THE LEVERAGE ORDER STATISTICS.**  On a uniform-share `(m,k)` design, every
probe subset `P` of `j` atoms contains an atom of leverage

    l >= j k / m      when j = m,     l > j k / m      when j < m

(`exists_card_mul_rank_le_size_mul_leverage`,
`exists_card_mul_rank_lt_size_mul_leverage`, both stated division-free as
`j * k <= m * l`).  One formula replaces the pen's four separate constants; at
`(6,3)` it gives, for `j = 6, 5, 4, 3`,

    l_(1) >= 3,   l_(2) > 5/2,   l_(3) > 2,   l_(4) > 3/2,

equivalently `tau_(1) >= 2/3`, `tau_(2) > 3/5`, `tau_(3) > 1/2`, `tau_(4) > 1/3`
— the pen's list, with the missing second entry filled in.  The pattern of
strictness the pen reports (non-strict at the top, strict below) is not a
convention: it is exactly whether the discarded complement is empty.

Its cardinality dual is `card_mul_rank_lt_size_mul_of_forall_leverage_le`: at
most `j` atoms can have leverage at most `cap` where `j k < m * cap`, with the
capacity twin `card_mul_rank_mul_slack_lt_size_of_forall_atomCapacity_le`.  At
`(6,3)` this is the pen's TWO-CHEAP-ATOM statement — at most two atoms have
leverage at most `3/2`, equivalently capacity at most `1/3`, equivalently weight
at least `1/3` — and it also gives the strictly sharper
`card_le_one_of_forall_leverage_le_one_six_three`: at most ONE atom of a
uniform-share `(6,3)` design is light.

## The form a covering argument actually wants

An order statistic says "every probe contains a heavy atom".  A covering argument
wants the dual: a SUBSET all of whose atoms are heavy at once.  That is
`exists_subset_card_forall_lt_atomCapacity`, and at `(6,3)` it delivers a
uniformly heavy TRIPLE above `1/2` (`exists_heavy_triple_atomCapacity_six_three`,
leverages above `2`) and a uniformly heavy PAIR above `3/5`
(`exists_heavy_pair_atomCapacity_six_three`, leverages above `5/2`) — the latter
being exactly the input the pen's PAIR-SUM GATE takes.

Its side condition `1 < k (1 - level)` fails precisely at `level = 1 - 1/k`, and
the failure is real rather than technical: `Gtz.icosaDesign` has every capacity
equal to `2/3`, so no uniformly heavy subset above `2/3` exists and the top
statistic is genuinely non-strict.

## What is sharper than the landed heaviness profile, and what agrees

The landed profile bounds the SHARE of the heavy set,
`share(H) >= k - 1 - threshold`.  Turning that into a COUNT needs a per-atom
share value.  Through the ceiling `s_c <= 1`, which is what
`Gtz.rank_sub_one_sub_threshold_le_card_heavySet` does, it gives
`card >= k - 1 - threshold`: at `(6,3)` that is `card {l >= 2} >= 1` and
`card {l >= 3/2} >= 2`.  Through the exact uniform share `k/m = 1/2` it gives 2
and 3.  V2 gives 3 and 4 at the same two thresholds, so it beats BOTH readings.

The reason is that the two arguments consume different laws.  The profile runs on
`sum_c t_c (l_c - 1) = k - 1` together with `s_c <= 1`, and is size-free.  V2 runs
on `sum_c 1/l_c = m/k`, which is the exact consequence of uniform share and knows
`m`.  Neither dominates the other off this stratum; on it, V2 wins below the top.

At the top the two AGREE, and that is the cross-check this file was asked to run.
The `j = m` instance of the order statistic is
`exists_rank_le_leverage_of_uniformShare`: some atom has `l >= k`.  That is
exactly the landed `Gtz.exists_leverage_ge_rank` — which carries NO uniform-share
hypothesis and is therefore strictly more general.  No disagreement, and
`exists_three_le_leverage_six_three_without_uniformShare` records the agreement in
the kernel by proving the pen's `l_(1) >= 3` from the landed route with the
uniform-share hypothesis deleted.

## What survives without uniform share

The `(7,3)` frontier object is all-heavy but NOT uniform-share, so no COUNT above
applies to it.  What survives is
`sum_atomShare_mul_slack_le_one_of_forall_atomCapacity_le`: the cheap atoms carry
share at most `1/(1 - level)`, at every size and rank.  The honest report is that
this is the landed heaviness profile re-coordinatized — at `level = 0` it IS
`Gtz.sum_atomShare_le_one_of_light` — stated in capacities because that is the
coordinate the pen's criterion uses.  A bound on the NUMBER of cheap atoms cannot
be recovered: shares may be arbitrarily small.

## A FALSE ITEM, corrected — and it is a NAME COLLISION, not an arithmetic slip

The brief this file was written from asks for the `(m,3)` generalization "the
statement is `sum tau = m - 2` with `tau < 1`".  There are TWO objects called
`tau` in the pen, they agree on the `(6,3)` stratum, and the `m - 2` reading
belongs to the wrong one.

* The WEIGHT SLACK `1 - 2 t_c`.  Its total is `m - 2` at every size and rank,
  trivially, since the weights sum to one.  (The sibling cheap-atom module lands
  it as `Gtz.atomWeightSlack` / `Gtz.sum_atomWeightSlack`.)
* The CAPACITY `1 - 1/l_c`, `Gtz.atomCapacity` here.  This is the one that sits on
  the diagonal of the domination criterion `diag(tau) + M[T] >= 0`, because
  domination of a triple is `Gamma[T] >= diag(1/l_c)`.  At uniform share its total
  is `m - m/k`.

They agree at an atom exactly when that atom's share is `1/2`
(`atomCapacity_eq_one_sub_two_mul_weight_iff`), so on a uniform-share design
exactly when `m = 2k`.  At `(m,3)` with `m /= 6` the criterion diagonal is
`1 - (m/3) t_c`, not `1 - 2 t_c` (`atomCapacity_eq_one_sub_size_div_rank_mul_weight`),
and it sums to `m - m/3`.  `m - m/k = m - 2` iff `m = 2k`
(`size_sub_size_div_rank_eq_size_sub_two_iff`): `m - 2` interpolates along the
SELF-DUAL family `(2k, k)`, not along `(m,3)`.

Kernel-checked on a landed design rather than asserted: `Gtz.tetraDesign` is a
uniform-share `(4,3)` design whose capacity total is `8/3`
(`sum_atomCapacity_tetraDesign`), while `m - 2 = 2`
(`sum_atomCapacity_tetraDesign_ne_size_sub_two`).  At `(7,3)` the capacity total
is `14/3` (`sum_atomCapacity_of_uniformShare_seven_three`), not `5`.

What this does and does not break.  It does NOT move the LEVERAGE statistics:
`l > j k / m` is the same formula whichever slack one reasons through, because
`1/l_c = (m/k) t_c` is exactly the reciprocal law, so the weight route and the
leverage route are the same computation.  It DOES move every capacity-phrased
constant.  At `(7,3)` the capacity statistics are

    tau_(1) >= 2/3,   tau_(2) > 11/18,   tau_(3) > 8/15,   tau_(4) > 5/12,

whereas the `m - 2` reading would return the `(6,3)` list `2/3, 3/5, 1/2, 1/3` —
uniformly TOO LARGE, hence unsound in the direction that matters, since the
criterion diagonal at `(7,3)` is strictly below the weight slack at every atom of
positive weight.  In leverages the `(7,3)` list is `l_(1) >= 3` (unchanged, the
top constant being `k` and free of `m`), then `l_(2) > 18/7`, `l_(3) > 15/7`,
`l_(4) > 12/7`, and at most THREE atoms are cheap, not two.  The `(7,3)` block
below spells these out because the frontier workflow reads them.

## Scope

Everything here is about UNIFORM SHARE `s_c = k/m` with FREE weights and FREE
leverages.  That is strictly weaker than `Gtz.IsEqualShare`, which additionally
pins `t_c = 1/m` and `l_c = k` — see the warning in that structure's docstring,
and `uniformShare_of_isEqualShare` for the one-line bridge.  Nothing in this file
touches `Gtz.Dominates`, so none of it is invalidated by the fact that domination
is not invariant under share-preserving rescaling.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LeverageBound
import Gtz.Design.StressCertificate
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.Reductions
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.HollowInvolution

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The averaging engine

Four statements about a bare family of reals.  They know nothing about designs;
the design content is entirely in which family is fed to them. -/

/-- **DISCARDING NONNEGATIVE TERMS LOWERS A SUM.**  The partial sum over a probe
subset is at most the total whenever everything outside is nonnegative. -/
theorem sum_probe_le_sum_of_nonneg_off_probe (value : Fin m → ℝ)
    (probeSet : Finset (Fin m)) (hoff : ∀ atomIndex ∈ probeSetᶜ, 0 ≤ value atomIndex) :
    ∑ atomIndex ∈ probeSet, value atomIndex ≤ ∑ atomIndex, value atomIndex := by
  have hdiscarded : 0 ≤ ∑ atomIndex ∈ probeSetᶜ, value atomIndex := Finset.sum_nonneg hoff
  rw [← Finset.sum_add_sum_compl probeSet value]
  linarith

/-- **DISCARDING POSITIVE TERMS LOWERS A SUM STRICTLY.**  This is where the pen's
`tau_c < 1` enters: what is thrown away is a reciprocal leverage, hence positive,
so every proper probe subset misses a genuine amount of the budget.  The whole
strictness pattern of the order statistics is this one lemma firing or not. -/
theorem sum_probe_lt_sum_of_pos_off_probe (value : Fin m → ℝ)
    (probeSet : Finset (Fin m)) (hnonempty : probeSetᶜ.Nonempty)
    (hoff : ∀ atomIndex ∈ probeSetᶜ, 0 < value atomIndex) :
    ∑ atomIndex ∈ probeSet, value atomIndex < ∑ atomIndex, value atomIndex := by
  have hdiscarded : 0 < ∑ atomIndex ∈ probeSetᶜ, value atomIndex :=
    Finset.sum_pos hoff hnonempty
  rw [← Finset.sum_add_sum_compl probeSet value]
  linarith

/-- **THE MINIMUM IS AT MOST THE AVERAGE**, stated multiplicatively so that no
division appears anywhere in the chain. -/
theorem exists_card_mul_le_of_sum_probe_le (value : Fin m → ℝ)
    (probeSet : Finset (Fin m)) {total : ℝ} (hnonempty : probeSet.Nonempty)
    (hpartial : ∑ atomIndex ∈ probeSet, value atomIndex ≤ total) :
    ∃ atomIndex ∈ probeSet, (probeSet.card : ℝ) * value atomIndex ≤ total := by
  by_contra hnone
  push Not at hnone
  have hcardPositive : (0 : ℝ) < (probeSet.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hstrict : ∑ _atomIndex ∈ probeSet, total
      < ∑ atomIndex ∈ probeSet, (probeSet.card : ℝ) * value atomIndex :=
    Finset.sum_lt_sum_of_nonempty hnonempty hnone
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hstrict
  have hscaled := mul_le_mul_of_nonneg_left hpartial hcardPositive.le
  linarith

/-- **THE MINIMUM IS BELOW A STRICT AVERAGE.**  The strict twin. -/
theorem exists_card_mul_lt_of_sum_probe_lt (value : Fin m → ℝ)
    (probeSet : Finset (Fin m)) {total : ℝ} (hnonempty : probeSet.Nonempty)
    (hpartial : ∑ atomIndex ∈ probeSet, value atomIndex < total) :
    ∃ atomIndex ∈ probeSet, (probeSet.card : ℝ) * value atomIndex < total := by
  by_contra hnone
  push Not at hnone
  have hcardPositive : (0 : ℝ) < (probeSet.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hweak : ∑ _atomIndex ∈ probeSet, total
      ≤ ∑ atomIndex ∈ probeSet, (probeSet.card : ℝ) * value atomIndex :=
    Finset.sum_le_sum fun atomIndex hmember => hnone atomIndex hmember
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hweak
  have hscaled := mul_lt_mul_of_pos_left hpartial hcardPositive
  linarith

/-- A probe subset that misses an atom has a nonempty complement. -/
theorem compl_nonempty_of_card_lt_size (probeSet : Finset (Fin m))
    (hproper : probeSet.card < m) : probeSetᶜ.Nonempty := by
  refine Finset.card_pos.mp ?_
  rw [Finset.card_compl, Fintype.card_fin]
  omega

/-! ## The uniform-share stratum, and the reciprocal leverage law -/

/-- **A CONSTANT SHARE IS THE SHARE `k/m`.**  The shares sum to the rank
(`Gtz.sum_atomShare_eq_rank`), so there is no freedom in the constant. -/
theorem eq_rank_div_size_of_forall_atomShare_eq (D : WeightedDesign m k) {share : ℝ}
    (hconstant : ∀ atomIndex, atomShare D atomIndex = share) (hsize : 0 < m) :
    share = (k : ℝ) / (m : ℝ) := by
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsize
  have htotal := sum_atomShare_eq_rank D
  rw [Finset.sum_congr rfl fun atomIndex _ => hconstant atomIndex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  field_simp
  linarith [htotal]

/-- **THE BRIDGE FROM `Gtz.IsEqualShare`.**  Uniform weight `1/m` together with
uniform leverage `k` is strictly stronger than uniform share `k/m`; this is the
implication, so every landed equal-share witness (`Gtz.icosaDesign`,
`Gtz.octahedronDesign`, `Gtz.tetraDesign`) feeds the theorems below. -/
theorem uniformShare_of_isEqualShare (D : WeightedDesign m k) (hequal : IsEqualShare D)
    (atomIndex : Fin m) : atomShare D atomIndex = (k : ℝ) / (m : ℝ) := by
  rw [atomShare, hequal.weight_eq, hequal.leverage_eq, inv_mul_eq_div]

/-- **NO ATOM OF A UNIFORM-SHARE DESIGN IS DEGENERATE.**  A share of `k/m > 0`
forces a positive leverage, by the landed `Gtz.leverageOf_pos_of_atomShare_pos`. -/
theorem leverageOf_pos_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (atomIndex : Fin m) : 0 < leverageOf (D.atom atomIndex) := by
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) atomIndex.isLt
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  refine leverageOf_pos_of_atomShare_pos D ?_
  rw [huniform atomIndex]
  exact div_pos hrankReal hsizeReal

/-- The reciprocal leverage of an atom of a uniform-share design is positive. -/
theorem inv_leverageOf_pos_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (atomIndex : Fin m) : 0 < (leverageOf (D.atom atomIndex))⁻¹ :=
  inv_pos.mpr (leverageOf_pos_of_uniformShare D hrank huniform atomIndex)

/-- **UNIFORM SHARE PINS THE RECIPROCAL LEVERAGE TO THE WEIGHT.**  From
`t_c l_c = k/m` one reads `1/l_c = (m/k) t_c`, atom by atom, with no summation.
This is the whole content of the reciprocal leverage law. -/
theorem inv_leverage_eq_size_div_rank_mul_weight (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (atomIndex : Fin m) :
    (leverageOf (D.atom atomIndex))⁻¹ = (m : ℝ) / (k : ℝ) * D.weight atomIndex := by
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) atomIndex.isLt
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hshare : D.weight atomIndex * leverageOf (D.atom atomIndex) = (k : ℝ) / (m : ℝ) :=
    huniform atomIndex
  refine inv_eq_of_mul_eq_one_left ?_
  rw [mul_assoc, hshare]
  field_simp

/-- **THE RECIPROCAL LEVERAGE LAW.**  On a uniform-share `(m,k)` design the
reciprocal leverages sum to `m/k`.  Every order statistic in this file is this
identity plus "the minimum is at most the average".

At `(6,3)` it reads `sum_c 1/l_c = 2`, i.e. the pen's `sum_c tau_c = 4`. -/
theorem sum_inv_leverage_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ)) :
    ∑ atomIndex, (leverageOf (D.atom atomIndex))⁻¹ = (m : ℝ) / (k : ℝ) := by
  rw [Finset.sum_congr rfl fun atomIndex _ =>
      inv_leverage_eq_size_div_rank_mul_weight D hrank huniform atomIndex,
    ← Finset.mul_sum, D.weight_sum_one, mul_one]

/-! ## The capacity of an atom -/

/-- **THE CAPACITY of an atom**, `tau_c = 1 - 1/l_c`.  It is the diagonal entry
the pen's criterion `D_tau[T] + M[T] >= 0` reads at that atom, and it is the
image of the leverage under the increasing bijection `l -> 1 - 1/l` from
`(0, infinity)` onto `(-infinity, 1)`.

The campaign's `tau` is taken twice already with other meanings — an excess
threshold in `Gtz/Design/FrameConservation.lean` and a margin scalar in
`Gtz/Corner/CoveringMargin.lean` — so the pen's letter is not reused. -/
noncomputable def atomCapacity (D : WeightedDesign m k) (atomIndex : Fin m) : ℝ :=
  1 - (leverageOf (D.atom atomIndex))⁻¹

/-- The capacity never reaches one; no hypothesis at all, since a degenerate atom
has `leverageOf = 0` and Lean's `0⁻¹ = 0` sends its capacity to exactly one. -/
theorem atomCapacity_le_one (D : WeightedDesign m k) (atomIndex : Fin m) :
    atomCapacity D atomIndex ≤ 1 := by
  have hnonneg : 0 ≤ (leverageOf (D.atom atomIndex))⁻¹ :=
    inv_nonneg.mpr (leverageOf_nonneg (D.atom atomIndex))
  rw [atomCapacity]
  linarith

/-- **THE PEN'S CEILING `tau_c < 1`**, and its exact content: the atom is not
degenerate.  On a uniform-share design this is automatic. -/
theorem atomCapacity_lt_one (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) : atomCapacity D atomIndex < 1 := by
  have hinvPositive : 0 < (leverageOf (D.atom atomIndex))⁻¹ := inv_pos.mpr hpositive
  rw [atomCapacity]
  linarith

/-- **THE CAPACITY/LEVERAGE DICTIONARY, non-strict and division-free.**
`level <= 1 - 1/l` is `1 <= (1 - level) * l`.  Reading it at
`level = 2/3, 3/5, 1/2, 1/3` returns `l >= 3, > 5/2, > 2, > 3/2`. -/
theorem le_atomCapacity_iff_one_le_mul (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) (level : ℝ) :
    level ≤ atomCapacity D atomIndex ↔ 1 ≤ (1 - level) * leverageOf (D.atom atomIndex) := by
  have hnonzero : leverageOf (D.atom atomIndex) ≠ 0 := hpositive.ne'
  have hexpand : (1 - (leverageOf (D.atom atomIndex))⁻¹) * leverageOf (D.atom atomIndex)
      = leverageOf (D.atom atomIndex) - 1 := by
    rw [sub_mul, inv_mul_cancel₀ hnonzero, one_mul]
  rw [atomCapacity]
  constructor
  · intro hlevel
    have hscaled := mul_le_mul_of_nonneg_right hlevel hpositive.le
    rw [hexpand] at hscaled
    nlinarith [hscaled]
  · intro hproduct
    have hstep : level * leverageOf (D.atom atomIndex)
        ≤ (1 - (leverageOf (D.atom atomIndex))⁻¹) * leverageOf (D.atom atomIndex) := by
      rw [hexpand]
      nlinarith [hproduct]
    exact le_of_mul_le_mul_right hstep hpositive

/-- **THE CAPACITY/LEVERAGE DICTIONARY, strict.** -/
theorem lt_atomCapacity_iff_one_lt_mul (D : WeightedDesign m k) {atomIndex : Fin m}
    (hpositive : 0 < leverageOf (D.atom atomIndex)) (level : ℝ) :
    level < atomCapacity D atomIndex ↔ 1 < (1 - level) * leverageOf (D.atom atomIndex) := by
  have hnonzero : leverageOf (D.atom atomIndex) ≠ 0 := hpositive.ne'
  have hexpand : (1 - (leverageOf (D.atom atomIndex))⁻¹) * leverageOf (D.atom atomIndex)
      = leverageOf (D.atom atomIndex) - 1 := by
    rw [sub_mul, inv_mul_cancel₀ hnonzero, one_mul]
  rw [atomCapacity]
  constructor
  · intro hlevel
    have hscaled := mul_lt_mul_of_pos_right hlevel hpositive
    rw [hexpand] at hscaled
    nlinarith [hscaled]
  · intro hproduct
    have hstep : level * leverageOf (D.atom atomIndex)
        < (1 - (leverageOf (D.atom atomIndex))⁻¹) * leverageOf (D.atom atomIndex) := by
      rw [hexpand]
      nlinarith [hproduct]
    exact lt_of_mul_lt_mul_right hstep hpositive.le

/-- **THE CAPACITY IS THE WEIGHT SLACK EXACTLY AT SHARE ONE HALF.**  The pen
writes its diagonal both ways, `tau_c = 1 - 2 t_c` and `tau_c = 1 - 1/l_c`, and on
the `(6,3)` stratum they coincide.  They coincide ONLY there: the two agree at an
atom precisely when that atom's share is `1/2`.

This is the whole of the `m - 2` question.  The weight-side reading
`1 - 2 t_c` sums to `m - 2` at every size and rank, trivially, because the weights
sum to one — but it is the diagonal of the domination criterion only at share
`1/2`, i.e. only when `m = 2k`.  What the criterion carries is the LEVERAGE-side
reading, `Gtz.atomCapacity`, and that one sums to `m - m/k`. -/
theorem atomCapacity_eq_one_sub_two_mul_weight_iff (D : WeightedDesign m k)
    {atomIndex : Fin m} (hpositive : 0 < leverageOf (D.atom atomIndex)) :
    atomCapacity D atomIndex = 1 - 2 * D.weight atomIndex ↔ atomShare D atomIndex = 1 / 2 := by
  have hnonzero : leverageOf (D.atom atomIndex) ≠ 0 := hpositive.ne'
  rw [atomCapacity, atomShare]
  constructor
  · intro hequal
    have hinverse : (leverageOf (D.atom atomIndex))⁻¹ = 2 * D.weight atomIndex := by linarith
    have hscaled : (leverageOf (D.atom atomIndex))⁻¹ * leverageOf (D.atom atomIndex)
        = 2 * D.weight atomIndex * leverageOf (D.atom atomIndex) := by rw [hinverse]
    rw [inv_mul_cancel₀ hnonzero] at hscaled
    linarith
  · intro hshare
    have hinverse : (leverageOf (D.atom atomIndex))⁻¹ = 2 * D.weight atomIndex := by
      refine inv_eq_of_mul_eq_one_left ?_
      linarith [hshare]
    rw [hinverse]

/-- **THE CAPACITY AT UNIFORM SHARE, in weight coordinates**: `tau_c = 1 - (m/k) t_c`.
The `(m/k)` here is the pen's `2`, and it is `2` exactly when `m = 2k`.  At `(7,3)`
the factor is `7/3`, so the criterion diagonal is strictly below the weight slack
`1 - 2 t_c` at every atom of positive weight. -/
theorem atomCapacity_eq_one_sub_size_div_rank_mul_weight (D : WeightedDesign m k)
    (hrank : 0 < k) (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (atomIndex : Fin m) :
    atomCapacity D atomIndex = 1 - (m : ℝ) / (k : ℝ) * D.weight atomIndex := by
  rw [atomCapacity, inv_leverage_eq_size_div_rank_mul_weight D hrank huniform atomIndex]

/-- **THE CAPACITY BUDGET.**  The reciprocal leverage law, read through the
dictionary: on a uniform-share `(m,k)` design the capacities sum to `m - m/k`.
At `(6,3)` this is the pen's `sum_c tau_c = 4`. -/
theorem sum_atomCapacity_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ)) :
    ∑ atomIndex, atomCapacity D atomIndex = (m : ℝ) - (m : ℝ) / (k : ℝ) := by
  simp only [atomCapacity]
  rw [Finset.sum_sub_distrib, sum_inv_leverage_of_uniformShare D hrank huniform,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ## The order statistics

Two master theorems.  Everything downstream is a numeral discharge. -/

/-- **THE LEVERAGE ORDER STATISTICS, non-strict.**  Every nonempty probe subset
of a uniform-share `(m,k)` design contains an atom with `j * k <= m * l`, where
`j` is the probe's cardinality.

At `j = m` this is `k <= l`, the landed `Gtz.exists_leverage_ge_rank`; below
`j = m` the strict twin applies and is sharper. -/
theorem exists_card_mul_rank_le_size_mul_leverage (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (probeSet : Finset (Fin m)) (hnonempty : probeSet.Nonempty) :
    ∃ atomIndex ∈ probeSet,
      (probeSet.card : ℝ) * (k : ℝ) ≤ (m : ℝ) * leverageOf (D.atom atomIndex) := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hpartial : ∑ atomIndex ∈ probeSet, (leverageOf (D.atom atomIndex))⁻¹
      ≤ (m : ℝ) / (k : ℝ) := by
    rw [← sum_inv_leverage_of_uniformShare D hrank huniform]
    exact sum_probe_le_sum_of_nonneg_off_probe _ probeSet fun atomIndex _ =>
      (inv_leverageOf_pos_of_uniformShare D hrank huniform atomIndex).le
  obtain ⟨atomIndex, hmember, hbound⟩ :=
    exists_card_mul_le_of_sum_probe_le _ probeSet hnonempty hpartial
  refine ⟨atomIndex, hmember, ?_⟩
  have hleverage : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_uniformShare D hrank huniform atomIndex
  have hleverageNonzero : leverageOf (D.atom atomIndex) ≠ 0 := hleverage.ne'
  have hrankNonzero : (k : ℝ) ≠ 0 := hrankReal.ne'
  have hscaled := mul_le_mul_of_nonneg_right hbound (mul_pos hleverage hrankReal).le
  have hleft : ((probeSet.card : ℝ) * (leverageOf (D.atom atomIndex))⁻¹)
        * (leverageOf (D.atom atomIndex) * (k : ℝ))
      = (probeSet.card : ℝ) * (k : ℝ) := by field_simp
  have hright : ((m : ℝ) / (k : ℝ)) * (leverageOf (D.atom atomIndex) * (k : ℝ))
      = (m : ℝ) * leverageOf (D.atom atomIndex) := by field_simp
  rw [hleft, hright] at hscaled
  exact hscaled

/-- **THE LEVERAGE ORDER STATISTICS, strict.**  A PROPER probe subset of a
uniform-share `(m,k)` design contains an atom with `j * k < m * l`.

Strictness is exactly the nonemptiness of the complement, through
`sum_probe_lt_sum_of_pos_off_probe`: what a proper probe discards is a positive
reciprocal leverage.  This is the pen's `tau_c < 1`, and it is what makes the
second, third and fourth order statistics strict while the first is not. -/
theorem exists_card_mul_rank_lt_size_mul_leverage (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (probeSet : Finset (Fin m)) (hnonempty : probeSet.Nonempty) (hproper : probeSet.card < m) :
    ∃ atomIndex ∈ probeSet,
      (probeSet.card : ℝ) * (k : ℝ) < (m : ℝ) * leverageOf (D.atom atomIndex) := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hpartial : ∑ atomIndex ∈ probeSet, (leverageOf (D.atom atomIndex))⁻¹
      < (m : ℝ) / (k : ℝ) := by
    rw [← sum_inv_leverage_of_uniformShare D hrank huniform]
    exact sum_probe_lt_sum_of_pos_off_probe _ probeSet
      (compl_nonempty_of_card_lt_size probeSet hproper) fun atomIndex _ =>
        inv_leverageOf_pos_of_uniformShare D hrank huniform atomIndex
  obtain ⟨atomIndex, hmember, hbound⟩ :=
    exists_card_mul_lt_of_sum_probe_lt _ probeSet hnonempty hpartial
  refine ⟨atomIndex, hmember, ?_⟩
  have hleverage : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_uniformShare D hrank huniform atomIndex
  have hleverageNonzero : leverageOf (D.atom atomIndex) ≠ 0 := hleverage.ne'
  have hrankNonzero : (k : ℝ) ≠ 0 := hrankReal.ne'
  have hscaled := mul_lt_mul_of_pos_right hbound (mul_pos hleverage hrankReal)
  have hleft : ((probeSet.card : ℝ) * (leverageOf (D.atom atomIndex))⁻¹)
        * (leverageOf (D.atom atomIndex) * (k : ℝ))
      = (probeSet.card : ℝ) * (k : ℝ) := by field_simp
  have hright : ((m : ℝ) / (k : ℝ)) * (leverageOf (D.atom atomIndex) * (k : ℝ))
      = (m : ℝ) * leverageOf (D.atom atomIndex) := by field_simp
  rw [hleft, hright] at hscaled
  exact hscaled

/-- **THE FIRST ORDER STATISTIC, and THE CROSS-CHECK.**  Taking the probe to be
everything gives `m * k <= m * l`, i.e. `l >= k` — the pen's `l_(1) >= 3` at rank
three, and the exact statement of the landed `Gtz.exists_leverage_ge_rank`.

The two AGREE.  The landed theorem is strictly more general: it needs no uniform
share, only `1 <= k`.  So V2's first entry is not new; entries two onward are,
because they see the exact share value rather than the ceiling `s_c <= 1` that
the heaviness profile converts through. -/
theorem exists_rank_le_leverage_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ)) (hsize : 0 < m) :
    ∃ atomIndex, (k : ℝ) ≤ leverageOf (D.atom atomIndex) := by
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hsize
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsize)
  obtain ⟨atomIndex, _, hbound⟩ :=
    exists_card_mul_rank_le_size_mul_leverage D hrank huniform Finset.univ hnonempty
  rw [Finset.card_univ, Fintype.card_fin] at hbound
  exact ⟨atomIndex, le_of_mul_le_mul_left (by linarith [hbound]) hsizeReal⟩

/-- **THE CAPACITY ORDER STATISTICS, strict.**  A proper nonempty probe subset
carries an atom of capacity above `level` as soon as `m <= j * k * (1 - level)`.

At `(6,3)` the four pen levels all saturate this budget exactly:
`(j, level) = (5, 3/5), (4, 1/2), (3, 1/3)` each give `j * k * (1 - level) = 6`. -/
theorem exists_lt_atomCapacity_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (probeSet : Finset (Fin m)) (hnonempty : probeSet.Nonempty) (hproper : probeSet.card < m)
    {level : ℝ} (hbudget : (m : ℝ) ≤ (probeSet.card : ℝ) * (k : ℝ) * (1 - level)) :
    ∃ atomIndex ∈ probeSet, level < atomCapacity D atomIndex := by
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨atomIndex, hmember, hbound⟩ :=
    exists_card_mul_rank_lt_size_mul_leverage D hrank huniform probeSet hnonempty hproper
  have hleverage : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_uniformShare D hrank huniform atomIndex
  have hproductNonneg : (0 : ℝ) ≤ (probeSet.card : ℝ) * (k : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hslackPositive : 0 < 1 - level := by
    nlinarith [hbudget, hsizeReal, hproductNonneg]
  refine ⟨atomIndex, hmember, (lt_atomCapacity_iff_one_lt_mul D hleverage level).mpr ?_⟩
  have hscaled : (probeSet.card : ℝ) * (k : ℝ) * (1 - level)
      < (m : ℝ) * leverageOf (D.atom atomIndex) * (1 - level) :=
    mul_lt_mul_of_pos_right hbound hslackPositive
  have hstep : (m : ℝ) < (m : ℝ) * (leverageOf (D.atom atomIndex) * (1 - level)) := by
    nlinarith [hbudget, hscaled]
  by_contra hcontra
  push Not at hcontra
  nlinarith [mul_le_mul_of_nonneg_left hcontra hsizeReal.le, hstep]

/-- **THE CAPACITY ORDER STATISTICS, non-strict.**  The `j = m` reading, which at
`(6,3)` is `tau_(1) >= 2/3` (budget `6 * 3 * (1/3) = 6`). -/
theorem exists_le_atomCapacity_of_uniformShare (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (probeSet : Finset (Fin m)) (hnonempty : probeSet.Nonempty)
    {level : ℝ} (hbudget : (m : ℝ) ≤ (probeSet.card : ℝ) * (k : ℝ) * (1 - level)) :
    ∃ atomIndex ∈ probeSet, level ≤ atomCapacity D atomIndex := by
  obtain ⟨firstIndex, hfirstMember⟩ := hnonempty
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) firstIndex.isLt
  obtain ⟨atomIndex, hmember, hbound⟩ :=
    exists_card_mul_rank_le_size_mul_leverage D hrank huniform probeSet ⟨firstIndex, hfirstMember⟩
  have hleverage : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_uniformShare D hrank huniform atomIndex
  have hproductNonneg : (0 : ℝ) ≤ (probeSet.card : ℝ) * (k : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hslackPositive : 0 < 1 - level := by
    nlinarith [hbudget, hsizeReal, hproductNonneg]
  refine ⟨atomIndex, hmember, (le_atomCapacity_iff_one_le_mul D hleverage level).mpr ?_⟩
  have hscaled : (probeSet.card : ℝ) * (k : ℝ) * (1 - level)
      ≤ (m : ℝ) * leverageOf (D.atom atomIndex) * (1 - level) :=
    mul_le_mul_of_nonneg_right hbound hslackPositive.le
  have hstep : (m : ℝ) ≤ (m : ℝ) * (leverageOf (D.atom atomIndex) * (1 - level)) := by
    nlinarith [hbudget, hscaled]
  by_contra hcontra
  push Not at hcontra
  nlinarith [mul_lt_mul_of_pos_left hcontra hsizeReal, hstep]

/-! ## The cheap-atom count -/

/-- **THE CHEAP-ATOM COUNT.**  On a uniform-share `(m,k)` design, a set of atoms
all of leverage at most `cap` — for any `cap` strictly below the rank — has
cardinality bounded by `j * k < m * cap`.

The side condition `cap < k` is not decoration: it is what forces the cheap set
to be PROPER, via the landed `Gtz.exists_leverage_ge_rank`, and properness is
what makes the count strict.  At `cap >= k` the statement is simply false with
the whole design as the cheap set.

At `(6,3)` this reads `j < 2 * cap`, giving the pen's TWO-CHEAP-ATOM gate at
`cap = 3/2` and the sharper ONE-LIGHT-ATOM bound at `cap = 1`. -/
theorem card_mul_rank_lt_size_mul_of_forall_leverage_le (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (cheapSet : Finset (Fin m)) {cap : ℝ} (hcapPositive : 0 < cap)
    (hcapBelowRank : cap < (k : ℝ))
    (hcheap : ∀ atomIndex ∈ cheapSet, leverageOf (D.atom atomIndex) ≤ cap) :
    (cheapSet.card : ℝ) * (k : ℝ) < (m : ℝ) * cap := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hproper : cheapSet.card < m := by
    by_contra hfull
    have hcapped : cheapSet.card ≤ m := by
      simpa [Fintype.card_fin] using Finset.card_le_univ cheapSet
    have hcardEq : cheapSet.card = Fintype.card (Fin m) := by
      rw [Fintype.card_fin]; omega
    have hisUniverse : cheapSet = Finset.univ := Finset.eq_univ_of_card cheapSet hcardEq
    obtain ⟨witnessIndex, hwitness⟩ := exists_leverage_ge_rank D hrank
    have hcheapWitness : leverageOf (D.atom witnessIndex) ≤ cap :=
      hcheap witnessIndex (by rw [hisUniverse]; exact Finset.mem_univ witnessIndex)
    linarith
  have hreciprocalFloor : (cheapSet.card : ℝ) * cap⁻¹
      ≤ ∑ atomIndex ∈ cheapSet, (leverageOf (D.atom atomIndex))⁻¹ := by
    have hpointwise : ∀ atomIndex ∈ cheapSet,
        cap⁻¹ ≤ (leverageOf (D.atom atomIndex))⁻¹ := fun atomIndex hmember => by
      have hleverage : 0 < leverageOf (D.atom atomIndex) :=
        leverageOf_pos_of_uniformShare D hrank huniform atomIndex
      simpa [one_div] using one_div_le_one_div_of_le hleverage (hcheap atomIndex hmember)
    calc (cheapSet.card : ℝ) * cap⁻¹ = ∑ _atomIndex ∈ cheapSet, cap⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ atomIndex ∈ cheapSet, (leverageOf (D.atom atomIndex))⁻¹ :=
          Finset.sum_le_sum hpointwise
  have hpartial : ∑ atomIndex ∈ cheapSet, (leverageOf (D.atom atomIndex))⁻¹
      < (m : ℝ) / (k : ℝ) := by
    rw [← sum_inv_leverage_of_uniformShare D hrank huniform]
    exact sum_probe_lt_sum_of_pos_off_probe _ cheapSet
      (compl_nonempty_of_card_lt_size cheapSet hproper) fun atomIndex _ =>
        inv_leverageOf_pos_of_uniformShare D hrank huniform atomIndex
  have hcombined : (cheapSet.card : ℝ) * cap⁻¹ < (m : ℝ) / (k : ℝ) := by linarith
  have hcapNonzero : cap ≠ 0 := hcapPositive.ne'
  have hrankNonzero : (k : ℝ) ≠ 0 := hrankReal.ne'
  rw [div_eq_mul_inv] at hcombined
  have hscaled := mul_lt_mul_of_pos_right hcombined (mul_pos hcapPositive hrankReal)
  have hleft : ((cheapSet.card : ℝ) * cap⁻¹) * (cap * (k : ℝ))
      = (cheapSet.card : ℝ) * (k : ℝ) := by field_simp
  have hright : ((m : ℝ) * (k : ℝ)⁻¹) * (cap * (k : ℝ)) = (m : ℝ) * cap := by
    field_simp
  rw [hleft, hright] at hscaled
  exact hscaled

/-- **THE CHEAP-ATOM COUNT IN CAPACITY COORDINATES.**  This is the form the
covering argument reads, because the pen's criterion `D_tau[T] + M[T] >= 0` is
stated in capacities: a set of atoms all of capacity at most `level` satisfies

    j * k * (1 - level) < m.

The side condition `1 < k * (1 - level)` is the capacity reading of `cap < k`,
i.e. `level < 1 - 1/k`; it is what makes the cheap set proper.  Proved directly
off the reciprocal leverage law, since `tau_c <= level` IS `1/l_c >= 1 - level`
by a linear rearrangement with no positivity needed.

At `(6,3)` the side condition is `level < 2/3` and the conclusion is
`j * (1 - level) < 2`: at `level = 1/3` it returns the two-cheap-atom gate. -/
theorem card_mul_rank_mul_slack_lt_size_of_forall_atomCapacity_le (D : WeightedDesign m k)
    (hrank : 0 < k) (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    (cheapSet : Finset (Fin m)) {level : ℝ} (hslack : 1 < (k : ℝ) * (1 - level))
    (hcheap : ∀ atomIndex ∈ cheapSet, atomCapacity D atomIndex ≤ level) :
    (cheapSet.card : ℝ) * (k : ℝ) * (1 - level) < (m : ℝ) := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  obtain ⟨sizeWitness, _⟩ := exists_leverage_ge_rank D hrank
  have hsizeReal : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) sizeWitness.isLt
  have hlaw := sum_inv_leverage_of_uniformShare D hrank huniform
  have hpointwise : ∀ atomIndex ∈ cheapSet,
      1 - level ≤ (leverageOf (D.atom atomIndex))⁻¹ := fun atomIndex hmember => by
    have hcapacity := hcheap atomIndex hmember
    rw [atomCapacity] at hcapacity
    linarith
  have hproper : cheapSet.card < m := by
    by_contra hfull
    have hcapped : cheapSet.card ≤ m := by
      simpa [Fintype.card_fin] using Finset.card_le_univ cheapSet
    have hcardEq : cheapSet.card = Fintype.card (Fin m) := by
      rw [Fintype.card_fin]; omega
    have hisUniverse : cheapSet = Finset.univ := Finset.eq_univ_of_card cheapSet hcardEq
    have hfloor : ∑ _atomIndex : Fin m, (1 - level)
        ≤ ∑ atomIndex, (leverageOf (D.atom atomIndex))⁻¹ :=
      Finset.sum_le_sum fun atomIndex _ =>
        hpointwise atomIndex (by rw [hisUniverse]; exact Finset.mem_univ atomIndex)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hlaw] at hfloor
    have hcancelled : (m : ℝ) * ((k : ℝ) * (1 - level)) ≤ (m : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_right hfloor hrankReal.le
      have hright : (m : ℝ) / (k : ℝ) * (k : ℝ) = (m : ℝ) := by
        field_simp
      rw [hright] at hscaled
      nlinarith [hscaled]
    nlinarith [hcancelled, hsizeReal]
  have hfloor : (cheapSet.card : ℝ) * (1 - level)
      ≤ ∑ atomIndex ∈ cheapSet, (leverageOf (D.atom atomIndex))⁻¹ := by
    calc (cheapSet.card : ℝ) * (1 - level) = ∑ _atomIndex ∈ cheapSet, (1 - level) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ atomIndex ∈ cheapSet, (leverageOf (D.atom atomIndex))⁻¹ :=
          Finset.sum_le_sum hpointwise
  have hpartial : ∑ atomIndex ∈ cheapSet, (leverageOf (D.atom atomIndex))⁻¹
      < (m : ℝ) / (k : ℝ) := by
    rw [← hlaw]
    exact sum_probe_lt_sum_of_pos_off_probe _ cheapSet
      (compl_nonempty_of_card_lt_size cheapSet hproper) fun atomIndex _ =>
        inv_leverageOf_pos_of_uniformShare D hrank huniform atomIndex
  have hcombined : (cheapSet.card : ℝ) * (1 - level) < (m : ℝ) / (k : ℝ) := by linarith
  have hrankNonzero : (k : ℝ) ≠ 0 := hrankReal.ne'
  have hscaled := mul_lt_mul_of_pos_right hcombined hrankReal
  have hright : (m : ℝ) / (k : ℝ) * (k : ℝ) = (m : ℝ) := by field_simp
  rw [hright] at hscaled
  nlinarith [hscaled]

/-- **A UNIFORMLY HEAVY SUBSET OF PRESCRIBED SIZE.**  The order statistics say
"every probe contains a heavy atom"; a covering argument wants the dual, a SUBSET
all of whose atoms are heavy AT ONCE.  That is this theorem: if the cheap-atom
count cannot reach `m - heavyCount + 1`, then `heavyCount` atoms clear `level`
simultaneously.

The side condition `1 < k * (1 - level)` fails exactly at `level = 1 - 1/k`, and
that failure is not an artefact: `Gtz.icosaDesign` has every capacity equal to
`2/3`, so at `(6,3)` the top statistic is genuinely non-strict and no uniformly
heavy subset above `2/3` exists.

At `(6,3)`: `heavyCount = 3` at `level = 1/2` and `heavyCount = 2` at
`level = 3/5`, both saturating `hroom` exactly at `6`. -/
theorem exists_subset_card_forall_lt_atomCapacity (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    {level : ℝ} (hslack : 1 < (k : ℝ) * (1 - level)) {heavyCount : ℕ}
    (hroom : (m : ℝ) ≤ ((m : ℝ) - (heavyCount : ℝ) + 1) * (k : ℝ) * (1 - level)) :
    ∃ heavySet : Finset (Fin m), heavySet.card = heavyCount ∧
      ∀ atomIndex ∈ heavySet, level < atomCapacity D atomIndex := by
  classical
  set cheapSet : Finset (Fin m) :=
    Finset.univ.filter fun atomIndex => atomCapacity D atomIndex ≤ level with hcheapDef
  have hcheapBound := card_mul_rank_mul_slack_lt_size_of_forall_atomCapacity_le D hrank huniform
    cheapSet hslack fun _atomIndex hmember => (Finset.mem_filter.mp hmember).2
  have hslackPositive : (0 : ℝ) < (k : ℝ) * (1 - level) := by linarith
  have hcheapCard : cheapSet.card + heavyCount ≤ m := by
    by_contra hcontra
    have hlarge : (m : ℝ) - (heavyCount : ℝ) + 1 ≤ (cheapSet.card : ℝ) := by
      have hnat : m + 1 ≤ cheapSet.card + heavyCount := by omega
      have hcast : ((m : ℝ)) + 1 ≤ (cheapSet.card : ℝ) + (heavyCount : ℝ) := by
        exact_mod_cast hnat
      linarith
    have hkey := mul_le_mul_of_nonneg_right hlarge hslackPositive.le
    nlinarith [hcheapBound, hkey, hroom]
  have hroomCard : heavyCount ≤ cheapSetᶜ.card := by
    have hsplit := Finset.card_add_card_compl cheapSet
    rw [Fintype.card_fin] at hsplit
    omega
  obtain ⟨heavySet, hsubset, hcard⟩ := Finset.exists_subset_card_eq hroomCard
  refine ⟨heavySet, hcard, fun atomIndex hmember => ?_⟩
  have hnotCheap : atomIndex ∈ cheapSetᶜ := hsubset hmember
  rw [Finset.mem_compl, hcheapDef, Finset.mem_filter] at hnotCheap
  push Not at hnotCheap
  exact hnotCheap (Finset.mem_univ atomIndex)

/-- **THE CHEAP-ATOM COUNT, read off the filter.**  The same bound with the
subset supplied by the statement rather than by the caller, which is what a
covering argument wants when it is asking "how many atoms can be cheap at all". -/
theorem card_filter_leverage_le_mul_rank_lt_size_mul (D : WeightedDesign m k) (hrank : 0 < k)
    (huniform : ∀ atomIndex, atomShare D atomIndex = (k : ℝ) / (m : ℝ))
    {cap : ℝ} [DecidablePred fun atomIndex : Fin m => leverageOf (D.atom atomIndex) ≤ cap]
    (hcapPositive : 0 < cap) (hcapBelowRank : cap < (k : ℝ)) :
    ((Finset.univ.filter fun atomIndex : Fin m =>
        leverageOf (D.atom atomIndex) ≤ cap).card : ℝ) * (k : ℝ) < (m : ℝ) * cap :=
  card_mul_rank_lt_size_mul_of_forall_leverage_le D hrank huniform _ hcapPositive hcapBelowRank
    fun _atomIndex hmember => (Finset.mem_filter.mp hmember).2

/-! ## Without uniform share: what survives is a SHARE bound

The `(7,3)` frontier object is all-heavy but is NOT uniform-share, so no count
above applies to it.  What does survive is the share statement, and the honest
report is that it is the landed heaviness profile
(`Gtz.rank_sub_one_sub_threshold_le_sum_atomShare`) re-coordinatized: at
`level = 0` it IS `Gtz.sum_atomShare_le_one_of_light`.  It is stated here in
capacities because that is the coordinate the pen's criterion uses, and it is
proved from the landed budget law rather than re-derived.

Note what CANNOT be recovered without uniform share: a bound on the NUMBER of
cheap atoms.  Shares may be arbitrarily small, so an unbounded number of atoms
can be cheap while their total share stays under the cap.  The counts in this
file are uniform-share statements and must not be transported. -/

/-- **THE BUDGET LAW IN CAPACITY COORDINATES**, `sum_c s_c tau_c = k - 1`, at
every size and rank and with no uniform-share hypothesis.  This is the landed
`Gtz.sum_atomShare_mul_one_sub_inv_leverage`; `Gtz.atomCapacity` is by definition
its summand's second factor. -/
theorem sum_atomShare_mul_atomCapacity (D : WeightedDesign m k)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex)) :
    ∑ atomIndex, atomShare D atomIndex * atomCapacity D atomIndex = (k : ℝ) - 1 :=
  sum_atomShare_mul_one_sub_inv_leverage D hpositive

/-- **THE CHEAP ATOMS CARRY SHARE AT MOST `1/(1 - level)`**, at every size and
rank, with no uniform-share hypothesis.  The proof is the budget law against the
share total `sum_c s_c = k` and the ceiling `tau_c <= 1`.

At `level = 0` this is the landed `Gtz.sum_atomShare_le_one_of_light`; at uniform
share `k/m` it returns `j * k / m * (1 - level) <= 1`, one step weaker than the
strict count above, the strictness being what the reciprocal law adds. -/
theorem sum_atomShare_mul_slack_le_one_of_forall_atomCapacity_le (D : WeightedDesign m k)
    (hpositive : ∀ atomIndex, 0 < leverageOf (D.atom atomIndex))
    (cheapSet : Finset (Fin m)) {level : ℝ}
    (hcheap : ∀ atomIndex ∈ cheapSet, atomCapacity D atomIndex ≤ level) :
    (∑ atomIndex ∈ cheapSet, atomShare D atomIndex) * (1 - level) ≤ 1 := by
  have hshareNonneg : ∀ atomIndex : Fin m, 0 ≤ atomShare D atomIndex := fun atomIndex => by
    rw [atomShare]
    exact mul_nonneg (D.weight_pos atomIndex).le (hpositive atomIndex).le
  have hbudgetSplit := Finset.sum_add_sum_compl cheapSet
    fun atomIndex => atomShare D atomIndex * atomCapacity D atomIndex
  rw [sum_atomShare_mul_atomCapacity D hpositive] at hbudgetSplit
  have hshareSplit := Finset.sum_add_sum_compl cheapSet fun atomIndex => atomShare D atomIndex
  rw [sum_atomShare_eq_rank D] at hshareSplit
  have hcheapBound : ∑ atomIndex ∈ cheapSet, atomShare D atomIndex * atomCapacity D atomIndex
      ≤ (∑ atomIndex ∈ cheapSet, atomShare D atomIndex) * level := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun atomIndex hmember =>
      mul_le_mul_of_nonneg_left (hcheap atomIndex hmember) (hshareNonneg atomIndex)
  have hrestBound : ∑ atomIndex ∈ cheapSetᶜ, atomShare D atomIndex * atomCapacity D atomIndex
      ≤ ∑ atomIndex ∈ cheapSetᶜ, atomShare D atomIndex :=
    Finset.sum_le_sum fun atomIndex _ => by
      nlinarith [atomCapacity_le_one D atomIndex, hshareNonneg atomIndex]
  nlinarith [hbudgetSplit, hshareSplit, hcheapBound, hrestBound]

/-! ## Rank three at six atoms: the pen's V2 list

`m = 6`, `k = 3`, so the uniform share is `1/2` and the reciprocal leverages sum
to `2`.  The four leverage constants and their four capacity twins. -/

/-- The `(6,3)` uniform share written the way the pen writes it. -/
theorem uniformShare_six_three_iff (D : WeightedDesign 6 3) :
    (∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((6 : ℕ) : ℝ))
      ↔ ∀ atomIndex, atomShare D atomIndex = 1 / 2 := by
  constructor <;> intro hshare atomIndex <;> rw [hshare atomIndex] <;> norm_num

/-- **`l_(1) >= 3`** — some atom of a uniform-share `(6,3)` design has leverage at
least the rank.  Equal to the landed `Gtz.exists_leverage_three_le` on this
stratum; the landed one needs no uniform share. -/
theorem exists_three_le_leverage_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ atomIndex, (3 : ℝ) ≤ leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hbound⟩ := exists_rank_le_leverage_of_uniformShare D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) (by norm_num)
  exact ⟨atomIndex, by exact_mod_cast hbound⟩

/-- **THE CROSS-CHECK, in the kernel.**  Exactly the conclusion of
`exists_three_le_leverage_six_three`, from the landed `Gtz.exists_leverage_three_le`,
with the uniform-share hypothesis DELETED.

The two routes AGREE, and this line is the record of it.  V2's first order
statistic is therefore not new; it is the landed leverage floor restricted to the
stratum, and the landed statement is strictly more general.  Every later
statistic in the list IS new, because it reads the exact share `k/m` where the
heaviness profile can only read the ceiling `s_c <= 1`. -/
theorem exists_three_le_leverage_six_three_without_uniformShare (D : WeightedDesign 6 3) :
    ∃ atomIndex, (3 : ℝ) ≤ leverageOf (D.atom atomIndex) :=
  exists_leverage_three_le D

/-- **`l_(2) > 5/2`** — the entry the pen's list omits.  Every five atoms of a
uniform-share `(6,3)` design contain one of leverage strictly above `5/2`. -/
theorem exists_five_halves_lt_leverage_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (probeSet : Finset (Fin 6)) (hcard : probeSet.card = 5) :
    ∃ atomIndex ∈ probeSet, (5 : ℝ) / 2 < leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hmember, hbound⟩ := exists_card_mul_rank_lt_size_mul_leverage D
    (by norm_num) ((uniformShare_six_three_iff D).mpr huniform) probeSet
    (Finset.card_pos.mp (by omega)) (by omega)
  rw [hcard] at hbound
  refine ⟨atomIndex, hmember, ?_⟩
  push_cast at hbound
  linarith

/-- **`l_(3) > 2`** — every four atoms contain one of leverage strictly above two.
Sharper than the heaviness profile, which gives only two such atoms in six. -/
theorem exists_two_lt_leverage_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (probeSet : Finset (Fin 6)) (hcard : probeSet.card = 4) :
    ∃ atomIndex ∈ probeSet, (2 : ℝ) < leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hmember, hbound⟩ := exists_card_mul_rank_lt_size_mul_leverage D
    (by norm_num) ((uniformShare_six_three_iff D).mpr huniform) probeSet
    (Finset.card_pos.mp (by omega)) (by omega)
  rw [hcard] at hbound
  refine ⟨atomIndex, hmember, ?_⟩
  push_cast at hbound
  linarith

/-- **`l_(4) > 3/2`** — every three atoms contain one of leverage strictly above
`3/2`.  Sharper than the heaviness profile, which gives only three such atoms in
six.  Its contrapositive is the two-cheap-atom gate. -/
theorem exists_three_halves_lt_leverage_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (probeSet : Finset (Fin 6)) (hcard : probeSet.card = 3) :
    ∃ atomIndex ∈ probeSet, (3 : ℝ) / 2 < leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hmember, hbound⟩ := exists_card_mul_rank_lt_size_mul_leverage D
    (by norm_num) ((uniformShare_six_three_iff D).mpr huniform) probeSet
    (Finset.card_pos.mp (by omega)) (by omega)
  rw [hcard] at hbound
  refine ⟨atomIndex, hmember, ?_⟩
  push_cast at hbound
  linarith

/-- **`tau_(1) >= 2/3`**, the capacity twin of `l_(1) >= 3`. -/
theorem exists_two_thirds_le_atomCapacity_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ atomIndex, (2 : ℝ) / 3 ≤ atomCapacity D atomIndex := by
  obtain ⟨atomIndex, _, hbound⟩ := exists_le_atomCapacity_of_uniformShare D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) Finset.univ
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by norm_num)))
    (level := 2 / 3) (by rw [Finset.card_univ, Fintype.card_fin]; norm_num)
  exact ⟨atomIndex, hbound⟩

/-- **`tau_(2) > 3/5`**, the capacity twin of `l_(2) > 5/2`. -/
theorem exists_three_fifths_lt_atomCapacity_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (probeSet : Finset (Fin 6)) (hcard : probeSet.card = 5) :
    ∃ atomIndex ∈ probeSet, (3 : ℝ) / 5 < atomCapacity D atomIndex :=
  exists_lt_atomCapacity_of_uniformShare D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) probeSet
    (Finset.card_pos.mp (by omega)) (by omega) (level := 3 / 5) (by rw [hcard]; norm_num)

/-- **`tau_(3) > 1/2`**, the capacity twin of `l_(3) > 2`. -/
theorem exists_one_half_lt_atomCapacity_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (probeSet : Finset (Fin 6)) (hcard : probeSet.card = 4) :
    ∃ atomIndex ∈ probeSet, (1 : ℝ) / 2 < atomCapacity D atomIndex :=
  exists_lt_atomCapacity_of_uniformShare D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) probeSet
    (Finset.card_pos.mp (by omega)) (by omega) (level := 1 / 2) (by rw [hcard]; norm_num)

/-- **`tau_(4) > 1/3`**, the capacity twin of `l_(4) > 3/2`. -/
theorem exists_one_third_lt_atomCapacity_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (probeSet : Finset (Fin 6)) (hcard : probeSet.card = 3) :
    ∃ atomIndex ∈ probeSet, (1 : ℝ) / 3 < atomCapacity D atomIndex :=
  exists_lt_atomCapacity_of_uniformShare D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) probeSet
    (Finset.card_pos.mp (by omega)) (by omega) (level := 1 / 3) (by rw [hcard]; norm_num)

/-- **THE TWO-CHEAP-ATOM GATE.**  At most two atoms of a uniform-share `(6,3)`
design have leverage at most `3/2`, equivalently capacity at most `1/3`,
equivalently weight at least `1/3`.  This is the pen's "a third cheap atom is
arithmetically impossible". -/
theorem card_le_two_of_forall_leverage_le_three_halves_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (cheapSet : Finset (Fin 6))
    (hcheap : ∀ atomIndex ∈ cheapSet, leverageOf (D.atom atomIndex) ≤ 3 / 2) :
    cheapSet.card ≤ 2 := by
  have hcount := card_mul_rank_lt_size_mul_of_forall_leverage_le D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) cheapSet (cap := 3 / 2) (by norm_num)
    (by norm_num) hcheap
  push_cast at hcount
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast (by linarith : (cheapSet.card : ℝ) < 3))

/-- **THE TWO-CHEAP-ATOM GATE IN CAPACITY COORDINATES.**  The same statement read
on `tau`: at most two atoms of a uniform-share `(6,3)` design have capacity at
most `1/3`.  This is the form the pen's covering argument consumes, since `tau`
is what the criterion's diagonal carries. -/
theorem card_le_two_of_forall_atomCapacity_le_one_third_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (cheapSet : Finset (Fin 6))
    (hcheap : ∀ atomIndex ∈ cheapSet, atomCapacity D atomIndex ≤ 1 / 3) :
    cheapSet.card ≤ 2 := by
  have hcount := card_mul_rank_mul_slack_lt_size_of_forall_atomCapacity_le D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) cheapSet (level := 1 / 3) (by norm_num) hcheap
  push_cast at hcount
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast (by linarith : (cheapSet.card : ℝ) < 3))

/-- **AT MOST ONE LIGHT ATOM.**  Strictly sharper than what the landed heaviness
profile gives here: `Gtz.sum_atomShare_le_one_of_light` caps the light share at
one, which at uniform share `1/2` permits TWO light atoms, and two is not
attainable — two atoms of leverage at most one would need weights summing to at
least one, leaving nothing for the other four. -/
theorem card_le_one_of_forall_leverage_le_one_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2)
    (lightSet : Finset (Fin 6))
    (hlight : ∀ atomIndex ∈ lightSet, leverageOf (D.atom atomIndex) ≤ 1) :
    lightSet.card ≤ 1 := by
  have hcount := card_mul_rank_lt_size_mul_of_forall_leverage_le D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) lightSet (cap := 1) (by norm_num)
    (by norm_num) hlight
  push_cast at hcount
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast (by linarith : (lightSet.card : ℝ) < 2))

/-- **A UNIFORMLY HEAVY TRIPLE EXISTS.**  Some three atoms of a uniform-share
`(6,3)` design have capacity above `1/2` SIMULTANEOUSLY.  The pen's `tau_(3) > 1/2`
read as a subset rather than as a probe statement, which is what the covering
argument needs when it selects a candidate triple. -/
theorem exists_heavy_triple_atomCapacity_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ heavyTriple : Finset (Fin 6), heavyTriple.card = 3 ∧
      ∀ atomIndex ∈ heavyTriple, (1 : ℝ) / 2 < atomCapacity D atomIndex :=
  exists_subset_card_forall_lt_atomCapacity D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) (level := 1 / 2) (by norm_num)
    (heavyCount := 3) (by norm_num)

/-- **A UNIFORMLY HEAVY TRIPLE, in leverages.**  Every atom of it has leverage
above two — so the triple the covering argument selects is never light, at any
weight vector on the stratum. -/
theorem exists_heavy_triple_leverage_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ heavyTriple : Finset (Fin 6), heavyTriple.card = 3 ∧
      ∀ atomIndex ∈ heavyTriple, (2 : ℝ) < leverageOf (D.atom atomIndex) := by
  obtain ⟨heavyTriple, hcard, hheavy⟩ := exists_heavy_triple_atomCapacity_six_three D huniform
  refine ⟨heavyTriple, hcard, fun atomIndex hmember => ?_⟩
  have hleverage : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_uniformShare D (by norm_num)
      ((uniformShare_six_three_iff D).mpr huniform) atomIndex
  have hproduct := (lt_atomCapacity_iff_one_lt_mul D hleverage (1 / 2)).mp
    (hheavy atomIndex hmember)
  linarith

/-- **A UNIFORMLY HEAVY PAIR EXISTS.**  Some two atoms have capacity above `3/5`
simultaneously — the pen's `tau_(2) > 3/5`, and exactly the input its PAIR-SUM
GATE takes ("the two heaviest atoms `{1,2}`"). -/
theorem exists_heavy_pair_atomCapacity_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ heavyPair : Finset (Fin 6), heavyPair.card = 2 ∧
      ∀ atomIndex ∈ heavyPair, (3 : ℝ) / 5 < atomCapacity D atomIndex :=
  exists_subset_card_forall_lt_atomCapacity D (by norm_num)
    ((uniformShare_six_three_iff D).mpr huniform) (level := 3 / 5) (by norm_num)
    (heavyCount := 2) (by norm_num)

/-- **A UNIFORMLY HEAVY PAIR, in leverages**: both atoms above `5/2`. -/
theorem exists_heavy_pair_leverage_six_three (D : WeightedDesign 6 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 1 / 2) :
    ∃ heavyPair : Finset (Fin 6), heavyPair.card = 2 ∧
      ∀ atomIndex ∈ heavyPair, (5 : ℝ) / 2 < leverageOf (D.atom atomIndex) := by
  obtain ⟨heavyPair, hcard, hheavy⟩ := exists_heavy_pair_atomCapacity_six_three D huniform
  refine ⟨heavyPair, hcard, fun atomIndex hmember => ?_⟩
  have hleverage : 0 < leverageOf (D.atom atomIndex) :=
    leverageOf_pos_of_uniformShare D (by norm_num)
      ((uniformShare_six_three_iff D).mpr huniform) atomIndex
  have hproduct := (lt_atomCapacity_iff_one_lt_mul D hleverage (3 / 5)).mp
    (hheavy atomIndex hmember)
  linarith

/-! ## Rank three at any size: the constants move with `m`

The `(7,3)` workflow reads these.  The first order statistic is `l >= k`, free of
`m`; every later one carries `m` explicitly, so the `(6,3)` numerals do NOT
transfer. -/

/-- **THE CHEAP-ATOM COUNT AT RANK THREE, any size.**  On a uniform-share `(m,3)`
design at most `j` atoms have leverage at most `3/2`, where `2 j < m`.  At `m = 6`
that is `j <= 2`; at `m = 7` it is `j <= 3`.  The constant is not size-free. -/
theorem two_mul_card_lt_size_of_forall_leverage_le_three_halves_rank_three
    (D : WeightedDesign m 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / (m : ℝ))
    (cheapSet : Finset (Fin m))
    (hcheap : ∀ atomIndex ∈ cheapSet, leverageOf (D.atom atomIndex) ≤ 3 / 2) :
    2 * (cheapSet.card : ℝ) < (m : ℝ) := by
  have hcount := card_mul_rank_lt_size_mul_of_forall_leverage_le D (by norm_num) huniform
    cheapSet (cap := 3 / 2) (by norm_num) (by norm_num) hcheap
  push_cast at hcount
  linarith

/-- **AT `(7,3)` THREE ATOMS MAY BE CHEAP.**  The two-cheap-atom gate is a `(6,3)`
statement, not a rank-three statement. -/
theorem card_le_three_of_forall_leverage_le_three_halves_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ))
    (cheapSet : Finset (Fin 7))
    (hcheap : ∀ atomIndex ∈ cheapSet, leverageOf (D.atom atomIndex) ≤ 3 / 2) :
    cheapSet.card ≤ 3 := by
  have hcount := two_mul_card_lt_size_of_forall_leverage_le_three_halves_rank_three D
    (by simpa using huniform) cheapSet hcheap
  push_cast at hcount
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast (by linarith : (cheapSet.card : ℝ) < 4))

/-- **`l_(2) > 18/7` AT `(7,3)`**, where `(6,3)` has `5/2`.  Every six atoms of a
uniform-share `(7,3)` design contain one of leverage strictly above `18/7`. -/
theorem exists_eighteen_sevenths_lt_leverage_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ))
    (probeSet : Finset (Fin 7)) (hcard : probeSet.card = 6) :
    ∃ atomIndex ∈ probeSet, (18 : ℝ) / 7 < leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hmember, hbound⟩ := exists_card_mul_rank_lt_size_mul_leverage D
    (by norm_num) huniform probeSet (Finset.card_pos.mp (by omega)) (by omega)
  rw [hcard] at hbound
  refine ⟨atomIndex, hmember, ?_⟩
  push_cast at hbound
  linarith

/-- **`l_(3) > 15/7` AT `(7,3)`**, where `(6,3)` has `2`. -/
theorem exists_fifteen_sevenths_lt_leverage_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ))
    (probeSet : Finset (Fin 7)) (hcard : probeSet.card = 5) :
    ∃ atomIndex ∈ probeSet, (15 : ℝ) / 7 < leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hmember, hbound⟩ := exists_card_mul_rank_lt_size_mul_leverage D
    (by norm_num) huniform probeSet (Finset.card_pos.mp (by omega)) (by omega)
  rw [hcard] at hbound
  refine ⟨atomIndex, hmember, ?_⟩
  push_cast at hbound
  linarith

/-- **`l_(4) > 12/7` AT `(7,3)`**, where `(6,3)` has `3/2`. -/
theorem exists_twelve_sevenths_lt_leverage_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ))
    (probeSet : Finset (Fin 7)) (hcard : probeSet.card = 4) :
    ∃ atomIndex ∈ probeSet, (12 : ℝ) / 7 < leverageOf (D.atom atomIndex) := by
  obtain ⟨atomIndex, hmember, hbound⟩ := exists_card_mul_rank_lt_size_mul_leverage D
    (by norm_num) huniform probeSet (Finset.card_pos.mp (by omega)) (by omega)
  rw [hcard] at hbound
  refine ⟨atomIndex, hmember, ?_⟩
  push_cast at hbound
  linarith

/-- **`tau_(1) >= 2/3` AT `(7,3)`** — the ONE capacity constant that does not move
with `m`, because the top statistic is `l >= k` and `1 - 1/k` is size-free. -/
theorem exists_two_thirds_le_atomCapacity_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) :
    ∃ atomIndex, (2 : ℝ) / 3 ≤ atomCapacity D atomIndex := by
  obtain ⟨atomIndex, _, hbound⟩ := exists_le_atomCapacity_of_uniformShare D (by norm_num)
    huniform Finset.univ
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by norm_num)))
    (level := 2 / 3) (by rw [Finset.card_univ, Fintype.card_fin]; norm_num)
  exact ⟨atomIndex, hbound⟩

/-- **`tau_(2) > 11/18` AT `(7,3)`**, where `(6,3)` has `3/5 = 10.8/18`.  Reading
the `(6,3)` constant here would UNDERSTATE the threshold and so overstate what a
weight vector may present. -/
theorem exists_eleven_eighteenths_lt_atomCapacity_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ))
    (probeSet : Finset (Fin 7)) (hcard : probeSet.card = 6) :
    ∃ atomIndex ∈ probeSet, (11 : ℝ) / 18 < atomCapacity D atomIndex :=
  exists_lt_atomCapacity_of_uniformShare D (by norm_num) huniform probeSet
    (Finset.card_pos.mp (by omega)) (by omega) (level := 11 / 18) (by rw [hcard]; norm_num)

/-- **`tau_(3) > 8/15` AT `(7,3)`**, where `(6,3)` has `1/2`. -/
theorem exists_eight_fifteenths_lt_atomCapacity_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ))
    (probeSet : Finset (Fin 7)) (hcard : probeSet.card = 5) :
    ∃ atomIndex ∈ probeSet, (8 : ℝ) / 15 < atomCapacity D atomIndex :=
  exists_lt_atomCapacity_of_uniformShare D (by norm_num) huniform probeSet
    (Finset.card_pos.mp (by omega)) (by omega) (level := 8 / 15) (by rw [hcard]; norm_num)

/-- **`tau_(4) > 5/12` AT `(7,3)`**, where `(6,3)` has `1/3`. -/
theorem exists_five_twelfths_lt_atomCapacity_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ))
    (probeSet : Finset (Fin 7)) (hcard : probeSet.card = 4) :
    ∃ atomIndex ∈ probeSet, (5 : ℝ) / 12 < atomCapacity D atomIndex :=
  exists_lt_atomCapacity_of_uniformShare D (by norm_num) huniform probeSet
    (Finset.card_pos.mp (by omega)) (by omega) (level := 5 / 12) (by rw [hcard]; norm_num)

/-! ## The `m - 2` reading is the `m = 2k` reading

The capacity total of a uniform-share design is `m - m/k`.  The brief this file
was written from records it as `m - 2` and asks for the `(m,3)` generalization at
that constant; `m - 2` is instead the constant of the SELF-DUAL family `m = 2k`,
and the two coincide at `(6,3)` by accident of arithmetic. -/

/-- **THE INTERPOLATION IS ALONG THE RANK AXIS, NOT THE SIZE AXIS.**  The capacity
total `m - m/k` equals `m - 2` exactly when `m = 2k`. -/
theorem size_sub_size_div_rank_eq_size_sub_two_iff (hrank : 0 < k) :
    (m : ℝ) - (m : ℝ) / (k : ℝ) = (m : ℝ) - 2 ↔ (m : ℝ) = 2 * (k : ℝ) := by
  have hrankReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  have hrankNonzero : (k : ℝ) ≠ 0 := hrankReal.ne'
  constructor
  · intro hequal
    have hquotient : (m : ℝ) / (k : ℝ) = 2 := by linarith
    field_simp at hquotient
    linarith
  · intro hdouble
    rw [hdouble]
    field_simp

/-- `Gtz.tetraDesign` is a UNIFORM-SHARE `(4,3)` design.  The landed
`Gtz.atomShare_tetraDesign` says every share is `3/4`; this is that value read as
`k/m`, which is the shape the theorems above consume. -/
theorem atomShare_tetraDesign_eq_rank_div_size (atomIndex : Fin 4) :
    atomShare tetraDesign atomIndex = ((3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) := by
  rw [atomShare_tetraDesign atomIndex]
  norm_num

/-- **THE CAPACITY TOTAL OF THE TETRAHEDRON IS `8/3`.**  Every atom has leverage
three, so every capacity is `2/3`, and there are four of them.  It agrees with
`m - m/k = 4 - 4/3`. -/
theorem sum_atomCapacity_tetraDesign :
    ∑ atomIndex, atomCapacity tetraDesign atomIndex = 8 / 3 := by
  have htotal := sum_atomCapacity_of_uniformShare tetraDesign (by norm_num)
    atomShare_tetraDesign_eq_rank_div_size
  rw [htotal]
  norm_num

/-- **THE REFUTATION, kernel-checked on a landed design.**  `Gtz.tetraDesign` is a
uniform-share `(4,3)` design whose capacity total is `8/3`, not `4 - 2 = 2`.  So
"`sum tau = m - 2`" is not the `(m,3)` law; `m - m/k` is. -/
theorem sum_atomCapacity_tetraDesign_ne_size_sub_two :
    (∑ atomIndex, atomCapacity tetraDesign atomIndex) ≠ ((4 : ℕ) : ℝ) - 2 := by
  rw [sum_atomCapacity_tetraDesign]
  norm_num

/-- **AND THE `(7,3)` TOTAL IS `14/3`, NOT `5`.**  The numeric statement behind the
corrected `(7,3)` constants. -/
theorem sum_atomCapacity_of_uniformShare_seven_three (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = ((3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) :
    ∑ atomIndex, atomCapacity D atomIndex = 14 / 3 := by
  rw [sum_atomCapacity_of_uniformShare D (by norm_num) huniform]
  norm_num

end Gtz
