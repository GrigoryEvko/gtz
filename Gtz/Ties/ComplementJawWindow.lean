/-
# The complement jaw window and the needle law at light-weight ties

The two terminal charts of the tie descent at `(6,3)` are the rank-one chart
(`S_C0 = 1 + lam w wᵀ`) and the needle chart (one large gap eigenvalue).  The
numerical probe of the charts found one selection mechanism at every capped
floor: the complement triple closes the chart while the jaw budget
`tin * (1 + lam) + tout` stays below one, and the budget is exactly the
balance quantity at every measured argmin.  This file makes the mechanism a
set of theorems.

The engine is the landed `Gtz.posDef_subsetSum_of_outside_share_lt`
(`Gtz.Design.ComplementEngine`).  The file consumes it in the two directions:

* FORWARD, the jaw.  `posDef_subsetSum_of_offside_quadCap` prices the offside
  weighted mass through a quadratic cap `kappa` on the offside atom sum, and
  gives the strict domination of `C` from `tin * kappa + tout < 1`.
  `posDef_compl_of_rankOneGap_jaw` instantiates `kappa = 1 + lam` at the
  rank-one gap shape.  This is the C3 foil law of the chart probe: at a small
  needle and light weights the complement is strict.
* BACKWARD, the needle law.  At a tie no `k`-subset is strict, so the engine
  hands back a direction that carries the offside mass.
  `exists_needle_direction_of_isTie`: at a tie with all weights at most `tau`,
  every `k`-subset with a `k`-sized complement reads a direction whose
  quadratic mass is at least `(1 - tau) / tau`.
  `exists_gapNeedle_of_isTie` reads the same direction on the gap matrix:
  the gap form is at least `(1 - 2 tau) / tau` there.  At `tau = 1/10` the
  bound is `8`.  That is the lower window edge of the needle chart, now a
  theorem: LIGHT-WEIGHT TIES ARE NEEDLES.
* THE BUDGET READINGS.  `one_le_jaw_budget_of_isTie_of_rankOneGap`: at a tie
  whose tied set carries the rank-one gap shape, the jaw budget is at least
  one.  `one_le_weight_budget_of_isTie_of_gapCap`: a cap `Lam` on the gap
  form forces `1 <= tau * (2 + Lam)` — the weight floor of bounded ties.
* THE NEEDLE CHART.  `sum_sq_le_of_needleGap` prices the rank-two gap shape
  at the sharp cap `1 + s1` through Bessel on the orthonormal gap frame.
  `posDef_compl_of_needleGap_jaw` and `one_le_jaw_budget_of_isTie_of_needleGap`
  are its jaw and its budget: the second eigenvalue never enters the budget.
* THE WELD RIVET.  `posDef_subsetSum_of_weighted_floor`: a carrier floor
  strictly above the own weights closes the set, with no Parseval read.
  `posDef_subsetSum_of_floor_gt_weights` is the numeric form: every landed
  carrier floor becomes a strictness certificate on its light region.
* THE LIGHT-ATOM LAW.  `exists_weight_mul_le_of_direction_mass` is the
  direction-mass pigeonhole through Parseval, and the two chart instances
  read it at the gap axis: a needle of size `lam` forces a tied-set weight
  at most `1 / (1 + lam)`.  The needle eats its own carrier's weight.

Every proof is a quadratic-form computation.  No eigenvalue, no spectral
theorem, no square root.  The mass law `weight_sum_one` is read only through
`dotProduct_eq_sum_weight_mul_pair` in the light-atom pigeonhole; every other
statement survives on sub-unit total mass unchanged.

PROBE PROVENANCE (scratchpad `terminal_charts.c`, calibration gates a
through d green).  The capped chart-one floors sit at the jaw balance:
floor `0.900` at `tau = 1/10` with `lam = 7.100`, floor `1.552` at
`tau = 3/40` with `lam = 9.78`, floor `2.831` at `tau = 1/20` with
`lam = 15.17`, winner the complement with the double exchanges tied.  The
mass-one free-weight floor is an exact sharp ZERO at the degenerate boundary
(five weights to zero, one to one).  An earlier `-3.9e-6` reading there was
float-noise harvesting at a weight clamp; the stable compressed margins
remove it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.ComplementEngine
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.RayleighCertificate
import Gtz.Ties.TotalTieCorankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The engine contrapositive -/

/-- **The offside mass of a non-strict subset.**  If `C` is not strictly
dominating and every weight in `C` is at most `maxWeight`, some nonzero
direction reads at least `1 - maxWeight` of the weighted offside mass.  This
is the contrapositive of the landed complement engine, packaged as a
producer. -/
theorem exists_offside_mass_of_not_posDef (D : WeightedDesign m k)
    (C : Finset (Fin m)) (maxWeight : ℝ) (hmaxPos : 0 < maxWeight)
    (hbound : ∀ label ∈ C, D.weight label ≤ maxWeight)
    (hnot : ¬ (subsetSum D C - 1).PosDef) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      (1 - maxWeight) * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ Cᶜ, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 := by
  by_contra hcon
  push Not at hcon
  exact hnot (posDef_subsetSum_of_outside_share_lt D C maxWeight hmaxPos hbound
    (fun probe hne => hcon probe hne))

/-! ## The jaw: a quadratic cap on the offside atoms closes the subset -/

/-- **The quadratic-cap jaw.**  Suppose the atoms OUTSIDE `C` obey the
quadratic cap `kappa` and their weights stay at most `tin`, while the weights
inside `C` stay at most `tout`.  The budget `tin * kappa + tout < 1` makes
`C` strictly dominating. -/
theorem posDef_subsetSum_of_offside_quadCap (D : WeightedDesign m k)
    (C : Finset (Fin m)) (tin tout kappa : ℝ)
    (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hinW : ∀ label ∈ Cᶜ, D.weight label ≤ tin)
    (houtW : ∀ label ∈ C, D.weight label ≤ tout)
    (hcap : ∀ probe : Fin k → ℝ,
      ∑ label ∈ Cᶜ, (D.atom label ⬝ᵥ probe) ^ 2 ≤ kappa * (probe ⬝ᵥ probe))
    (hjaw : tin * kappa + tout < 1) :
    (subsetSum D C - 1).PosDef := by
  apply posDef_subsetSum_of_outside_share_lt D C tout htoutPos houtW
  intro probe hne
  have hpp : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  have hstep : ∑ label ∈ Cᶜ, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2
      ≤ tin * (kappa * (probe ⬝ᵥ probe)) := by
    calc ∑ label ∈ Cᶜ, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2
        ≤ ∑ label ∈ Cᶜ, tin * (D.atom label ⬝ᵥ probe) ^ 2 :=
          Finset.sum_le_sum (fun label hmem =>
            mul_le_mul_of_nonneg_right (hinW label hmem) (sq_nonneg _))
      _ = tin * ∑ label ∈ Cᶜ, (D.atom label ⬝ᵥ probe) ^ 2 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ tin * (kappa * (probe ⬝ᵥ probe)) :=
          mul_le_mul_of_nonneg_left (hcap probe) htinNonneg
  nlinarith [hstep, hpp]

/-- The rank-one gap shape gives the quadratic cap `1 + lam` on the tied
set's atom sum.  One Cauchy–Schwarz step, no eigenvalue. -/
theorem sum_sq_le_of_rankOneGap (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (lam : ℝ) (gapDir : Fin k → ℝ)
    (hlam : 0 ≤ lam) (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C0 = 1 + lam • atomMatrix gapDir)
    (probe : Fin k → ℝ) :
    ∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2 ≤ (1 + lam) * (probe ⬝ᵥ probe) := by
  have hsum := dotProduct_subsetSum_mulVec_of_finset D C0 probe
  rw [hgap, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    atomMatrix, vecMulVec_mulVec_eq] at hsum
  have hmul : probe ⬝ᵥ (probe + lam • ((gapDir ⬝ᵥ probe) • gapDir))
      = probe ⬝ᵥ probe + lam * ((gapDir ⬝ᵥ probe) * (probe ⬝ᵥ gapDir)) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hmul, dotProduct_comm probe gapDir] at hsum
  have hcs : (gapDir ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
    have hbound := dotProduct_sq_le_mul gapDir probe
    rwa [hunit, one_mul] at hbound
  rw [← hsum]
  nlinarith [hcs, dotProduct_self_nonneg probe]

/-- **The rank-one jaw** (the C3 foil law of the chart probe).  At the
rank-one gap shape on `C0` with needle size `lam`, the budget
`tin * (1 + lam) + tout < 1` makes the complement of `C0` strictly
dominating. -/
theorem posDef_compl_of_rankOneGap_jaw (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (tin tout lam : ℝ) (gapDir : Fin k → ℝ)
    (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hlam : 0 ≤ lam) (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C0 = 1 + lam • atomMatrix gapDir)
    (hinW : ∀ label ∈ C0, D.weight label ≤ tin)
    (houtW : ∀ label ∈ C0ᶜ, D.weight label ≤ tout)
    (hjaw : tin * (1 + lam) + tout < 1) :
    (subsetSum D C0ᶜ - 1).PosDef := by
  apply posDef_subsetSum_of_offside_quadCap D C0ᶜ tin tout (1 + lam)
    htoutPos htinNonneg ?_ houtW ?_ hjaw
  · intro label hmem
    rw [compl_compl] at hmem
    exact hinW label hmem
  · intro probe
    rw [compl_compl]
    exact sum_sq_le_of_rankOneGap D C0 lam gapDir hlam hunit hgap probe

/-- **The jaw budget of a rank-one tie.**  At a tie whose tied set carries the
rank-one gap shape, the jaw budget is at least one:
`1 <= tin * (1 + lam) + tout`.  The rank-one chart is confined to the jaw
boundary. -/
theorem one_le_jaw_budget_of_isTie_of_rankOneGap (D : WeightedDesign m k)
    (htie : IsTie D) (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k)
    (tin tout lam : ℝ) (gapDir : Fin k → ℝ)
    (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hlam : 0 ≤ lam) (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C0 = 1 + lam • atomMatrix gapDir)
    (hinW : ∀ label ∈ C0, D.weight label ≤ tin)
    (houtW : ∀ label ∈ C0ᶜ, D.weight label ≤ tout) :
    1 ≤ tin * (1 + lam) + tout := by
  by_contra hcon
  push Not at hcon
  exact htie.2 C0ᶜ hcompl (posDef_compl_of_rankOneGap_jaw D C0 tin tout lam
    gapDir htoutPos htinNonneg hlam hunit hgap hinW houtW hcon)

/-! ## The needle law at a tie -/

/-- **The needle direction of a light-weight tie.**  At a tie with every
weight at most `tau`, each subset `C0` with a `k`-sized complement reads a
nonzero direction whose quadratic atom mass on `C0` is at least
`(1 - tau) / tau` of the direction's norm.  The cardinality of `C0` itself is
not read. -/
theorem exists_needle_direction_of_isTie (D : WeightedDesign m k)
    (htie : IsTie D) (tau : ℝ) (htauPos : 0 < tau)
    (hbound : ∀ label, D.weight label ≤ tau)
    (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      (1 - tau) * (probe ⬝ᵥ probe)
        ≤ tau * ∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2 := by
  obtain ⟨probe, hne, hmass⟩ := exists_offside_mass_of_not_posDef D C0ᶜ tau
    htauPos (fun label _ => hbound label) (htie.2 C0ᶜ hcompl)
  rw [compl_compl] at hmass
  refine ⟨probe, hne, ?_⟩
  calc (1 - tau) * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ C0, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 := hmass
    _ ≤ ∑ label ∈ C0, tau * (D.atom label ⬝ᵥ probe) ^ 2 :=
        Finset.sum_le_sum (fun label _ =>
          mul_le_mul_of_nonneg_right (hbound label) (sq_nonneg _))
    _ = tau * ∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2 :=
        (Finset.mul_sum _ _ _).symm

/-- **The gap needle.**  The needle direction read on the gap matrix: at a
tie with weights at most `tau`, the gap form of `C0` is at least
`(1 - 2 tau) / tau` along some nonzero direction.  At `tau = 1/10` the bound
is `8` — the lower window edge of the needle chart. -/
theorem exists_gapNeedle_of_isTie (D : WeightedDesign m k)
    (htie : IsTie D) (tau : ℝ) (htauPos : 0 < tau)
    (hbound : ∀ label, D.weight label ≤ tau)
    (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k) :
    ∃ probe : Fin k → ℝ, probe ≠ 0 ∧
      (1 - 2 * tau) * (probe ⬝ᵥ probe)
        ≤ tau * (probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe)) := by
  obtain ⟨probe, hne, hneedle⟩ :=
    exists_needle_direction_of_isTie D htie tau htauPos hbound C0 hcompl
  refine ⟨probe, hne, ?_⟩
  have hgapForm : tau * (probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe))
      = tau * (∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2)
        - tau * (probe ⬝ᵥ probe) := by
    rw [dominationGap_form]
    ring
  rw [hgapForm]
  linarith [hneedle]

/-- **The weight budget of a bounded tie.**  A cap `Lam` on the gap form of a
`k`-complemented subset forces `1 <= tau * (2 + Lam)` at every tie with
weights at most `tau`.  Read backward: ties with a bounded gap have a heavy
atom. -/
theorem one_le_weight_budget_of_isTie_of_gapCap (D : WeightedDesign m k)
    (htie : IsTie D) (tau Lam : ℝ) (htauPos : 0 < tau)
    (hbound : ∀ label, D.weight label ≤ tau)
    (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k)
    (hcap : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe) ≤ Lam * (probe ⬝ᵥ probe)) :
    1 ≤ tau * (2 + Lam) := by
  obtain ⟨probe, hne, hneedle⟩ :=
    exists_gapNeedle_of_isTie D htie tau htauPos hbound C0 hcompl
  have hpp : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hne
  have hcapped : tau * (probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe))
      ≤ tau * (Lam * (probe ⬝ᵥ probe)) :=
    mul_le_mul_of_nonneg_left (hcap probe) (le_of_lt htauPos)
  nlinarith [hneedle, hcapped, hpp]

/-! ## The needle chart: the rank-two gap -/

/-- Bessel's inequality for an orthonormal pair, at the dot-product level. -/
theorem sq_add_sq_le_of_orthonormal_pair (dirOne dirTwo probe : Fin k → ℝ)
    (hunitOne : dirOne ⬝ᵥ dirOne = 1) (hunitTwo : dirTwo ⬝ᵥ dirTwo = 1)
    (hortho : dirOne ⬝ᵥ dirTwo = 0) :
    (dirOne ⬝ᵥ probe) ^ 2 + (dirTwo ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
  have hres := dotProduct_self_nonneg
    (probe - (dirOne ⬝ᵥ probe) • dirOne - (dirTwo ⬝ᵥ probe) • dirTwo)
  have hcommOne : probe ⬝ᵥ dirOne = dirOne ⬝ᵥ probe := dotProduct_comm _ _
  have hcommTwo : probe ⬝ᵥ dirTwo = dirTwo ⬝ᵥ probe := dotProduct_comm _ _
  have hcommOT : dirTwo ⬝ᵥ dirOne = 0 := by rw [dotProduct_comm]; exact hortho
  have hexp : (probe - (dirOne ⬝ᵥ probe) • dirOne - (dirTwo ⬝ᵥ probe) • dirTwo) ⬝ᵥ
        (probe - (dirOne ⬝ᵥ probe) • dirOne - (dirTwo ⬝ᵥ probe) • dirTwo)
      = probe ⬝ᵥ probe - (dirOne ⬝ᵥ probe) ^ 2 - (dirTwo ⬝ᵥ probe) ^ 2 := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, hcommOne, hcommTwo, hcommOT, hortho, hunitOne, hunitTwo]
    ring
  rw [hexp] at hres
  linarith [hres]

/-- The needle gap shape gives the sharp quadratic cap `1 + s1`: the second
eigenvalue never enters, by Bessel on the orthonormal gap frame. -/
theorem sum_sq_le_of_needleGap (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (s1 s2 : ℝ) (dirOne dirTwo : Fin k → ℝ)
    (hs2 : 0 ≤ s2) (hle : s2 ≤ s1)
    (hunitOne : dirOne ⬝ᵥ dirOne = 1) (hunitTwo : dirTwo ⬝ᵥ dirTwo = 1)
    (hortho : dirOne ⬝ᵥ dirTwo = 0)
    (hgap : subsetSum D C0 = 1 + s1 • atomMatrix dirOne + s2 • atomMatrix dirTwo)
    (probe : Fin k → ℝ) :
    ∑ label ∈ C0, (D.atom label ⬝ᵥ probe) ^ 2 ≤ (1 + s1) * (probe ⬝ᵥ probe) := by
  have hsum := dotProduct_subsetSum_mulVec_of_finset D C0 probe
  rw [hgap, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, atomMatrix, atomMatrix,
    vecMulVec_mulVec_eq, vecMulVec_mulVec_eq] at hsum
  have hcommOne : probe ⬝ᵥ dirOne = dirOne ⬝ᵥ probe := dotProduct_comm _ _
  have hcommTwo : probe ⬝ᵥ dirTwo = dirTwo ⬝ᵥ probe := dotProduct_comm _ _
  have hform : probe ⬝ᵥ (probe + s1 • ((dirOne ⬝ᵥ probe) • dirOne)
        + s2 • ((dirTwo ⬝ᵥ probe) • dirTwo))
      = probe ⬝ᵥ probe + s1 * (dirOne ⬝ᵥ probe) ^ 2
        + s2 * (dirTwo ⬝ᵥ probe) ^ 2 := by
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hcommOne, hcommTwo]
    ring
  rw [hform] at hsum
  have hbessel := sq_add_sq_le_of_orthonormal_pair dirOne dirTwo probe
    hunitOne hunitTwo hortho
  have hs1 : 0 ≤ s1 := le_trans hs2 hle
  rw [← hsum]
  linarith [mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg (dirTwo ⬝ᵥ probe)),
    mul_nonneg hs1 (sub_nonneg.mpr hbessel)]

/-- **The needle jaw.**  At the rank-two gap shape with sizes `s2 <= s1`, the
budget `tin * (1 + s1) + tout < 1` makes the complement strictly
dominating.  The second eigenvalue is priced away by Bessel. -/
theorem posDef_compl_of_needleGap_jaw (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (tin tout s1 s2 : ℝ) (dirOne dirTwo : Fin k → ℝ)
    (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hs2 : 0 ≤ s2) (hle : s2 ≤ s1)
    (hunitOne : dirOne ⬝ᵥ dirOne = 1) (hunitTwo : dirTwo ⬝ᵥ dirTwo = 1)
    (hortho : dirOne ⬝ᵥ dirTwo = 0)
    (hgap : subsetSum D C0 = 1 + s1 • atomMatrix dirOne + s2 • atomMatrix dirTwo)
    (hinW : ∀ label ∈ C0, D.weight label ≤ tin)
    (houtW : ∀ label ∈ C0ᶜ, D.weight label ≤ tout)
    (hjaw : tin * (1 + s1) + tout < 1) :
    (subsetSum D C0ᶜ - 1).PosDef := by
  apply posDef_subsetSum_of_offside_quadCap D C0ᶜ tin tout (1 + s1)
    htoutPos htinNonneg ?_ houtW ?_ hjaw
  · intro label hmem
    rw [compl_compl] at hmem
    exact hinW label hmem
  · intro probe
    rw [compl_compl]
    exact sum_sq_le_of_needleGap D C0 s1 s2 dirOne dirTwo hs2 hle
      hunitOne hunitTwo hortho hgap probe

/-- **The jaw budget of a needle tie.**  At a tie whose tied set carries the
rank-two gap shape, the budget reads the LARGE eigenvalue only:
`1 <= tin * (1 + s1) + tout`.  With all weights at most `tau` this is
`s1 >= (1 - 2 tau) / tau`, the value `8` at `tau = 1/10` — the lower window
edge of the needle chart read off the parametrization. -/
theorem one_le_jaw_budget_of_isTie_of_needleGap (D : WeightedDesign m k)
    (htie : IsTie D) (C0 : Finset (Fin m)) (hcompl : C0ᶜ.card = k)
    (tin tout s1 s2 : ℝ) (dirOne dirTwo : Fin k → ℝ)
    (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hs2 : 0 ≤ s2) (hle : s2 ≤ s1)
    (hunitOne : dirOne ⬝ᵥ dirOne = 1) (hunitTwo : dirTwo ⬝ᵥ dirTwo = 1)
    (hortho : dirOne ⬝ᵥ dirTwo = 0)
    (hgap : subsetSum D C0 = 1 + s1 • atomMatrix dirOne + s2 • atomMatrix dirTwo)
    (hinW : ∀ label ∈ C0, D.weight label ≤ tin)
    (houtW : ∀ label ∈ C0ᶜ, D.weight label ≤ tout) :
    1 ≤ tin * (1 + s1) + tout := by
  by_contra hcon
  push Not at hcon
  exact htie.2 C0ᶜ hcompl (posDef_compl_of_needleGap_jaw D C0 tin tout s1 s2
    dirOne dirTwo htoutPos htinNonneg hs2 hle hunitOne hunitTwo hortho hgap
    hinW houtW hcon)

/-! ## The weld rivet: a carrier floor above the own weights closes the set -/

/-- **The weld rivet.**  If the weighted carrier of `C` stays strictly above
`tmax` in every direction, and `tmax` bounds the weights of `C`, then `C`
strictly dominates.  This turns every quantitative carrier floor into a
strictness certificate on the region where the floor beats the weights.  The
Parseval law is not read. -/
theorem posDef_subsetSum_of_weighted_floor (D : WeightedDesign m k)
    (C : Finset (Fin m)) (tmax : ℝ) (htmaxPos : 0 < tmax)
    (hbound : ∀ label ∈ C, D.weight label ≤ tmax)
    (hfloor : ∀ probe : Fin k → ℝ, probe ≠ 0 →
      tmax * (probe ⬝ᵥ probe)
        < ∑ label ∈ C, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2) :
    (subsetSum D C - 1).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq (transpose_subsetSum_sub_one D C),
      fun probe hprobeNe => ?_⟩
  rw [star_trivial]
  have hquad : probe ⬝ᵥ (subsetSum D C - 1) *ᵥ probe
      = (∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2) - probe ⬝ᵥ probe := by
    rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
      Matrix.one_mulVec]
  rw [hquad]
  have hinside : ∑ c ∈ C, D.weight c * (D.atom c ⬝ᵥ probe) ^ 2
      ≤ tmax * ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    nlinarith [hbound c hc, sq_nonneg (D.atom c ⬝ᵥ probe)]
  have hchain : tmax * (probe ⬝ᵥ probe)
      < tmax * ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 :=
    lt_of_lt_of_le (hfloor probe hprobeNe) hinside
  have hfinal : probe ⬝ᵥ probe < ∑ c ∈ C, (D.atom c ⬝ᵥ probe) ^ 2 :=
    lt_of_mul_lt_mul_left hchain htmaxPos.le
  linarith

/-- The numeric form of the rivet: a scalar carrier floor strictly above every
weight of `C` closes `C`.  With the landed floor `1/10` this closes the whole
region where the carrier triple's weights sit below `1/10`. -/
theorem posDef_subsetSum_of_floor_gt_weights (D : WeightedDesign m k)
    (C : Finset (Fin m)) (floor tmax : ℝ) (htmaxPos : 0 < tmax)
    (hbound : ∀ label ∈ C, D.weight label ≤ tmax) (hlt : tmax < floor)
    (hfloor : ∀ probe : Fin k → ℝ, floor * (probe ⬝ᵥ probe)
      ≤ ∑ label ∈ C, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2) :
    (subsetSum D C - 1).PosDef := by
  refine posDef_subsetSum_of_weighted_floor D C tmax htmaxPos hbound
    (fun probe hprobeNe => ?_)
  have hpp : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
  calc tmax * (probe ⬝ᵥ probe) < floor * (probe ⬝ᵥ probe) := by nlinarith [hpp]
    _ ≤ ∑ label ∈ C, D.weight label * (D.atom label ⬝ᵥ probe) ^ 2 := hfloor probe

/-! ## The light-atom law: a needle forces a light weight -/

/-- **The direction-mass pigeonhole.**  If the atoms of `C0` read the total
square mass `mass` along a unit direction, some label of `C0` has
`weight * mass <= 1`.  The proof reads the Parseval law along the direction:
the weighted total is one, and a set whose every weight beats `1 / mass`
carries more than its share. -/
theorem exists_weight_mul_le_of_direction_mass (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (dir : Fin k → ℝ) (hunit : dir ⬝ᵥ dir = 1)
    (mass : ℝ) (hmassPos : 0 < mass)
    (hmass : ∑ label ∈ C0, (D.atom label ⬝ᵥ dir) ^ 2 = mass) :
    ∃ label ∈ C0, D.weight label * mass ≤ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have huniv : (1 : ℝ) = ∑ c, D.weight c * (D.atom c ⬝ᵥ dir) ^ 2 := by
    rw [← hunit, dotProduct_eq_sum_weight_mul_pair D dir dir]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hsub : ∑ c ∈ C0, D.weight c * (D.atom c ⬝ᵥ dir) ^ 2
      ≤ ∑ c, D.weight c * (D.atom c ⬝ᵥ dir) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C0)
      (fun c _ _ => mul_nonneg (D.weight_pos c).le (sq_nonneg _))
  have hcarrier : ∃ c ∈ C0, 0 < (D.atom c ⬝ᵥ dir) ^ 2 := by
    by_contra hzero
    push Not at hzero
    have hall : ∀ c ∈ C0, (D.atom c ⬝ᵥ dir) ^ 2 = 0 :=
      fun c hc => le_antisymm (hzero c hc) (sq_nonneg _)
    rw [Finset.sum_congr rfl hall, Finset.sum_const_zero] at hmass
    exact absurd hmass.symm (ne_of_gt hmassPos)
  obtain ⟨carrier, hcarrierMem, hcarrierPos⟩ := hcarrier
  have hstrict : ∑ c ∈ C0, (D.atom c ⬝ᵥ dir) ^ 2
      < ∑ c ∈ C0, mass * (D.weight c * (D.atom c ⬝ᵥ dir) ^ 2) := by
    refine Finset.sum_lt_sum (fun c hc => ?_) ⟨carrier, hcarrierMem, ?_⟩
    · nlinarith [(hcon c hc).le, sq_nonneg (D.atom c ⬝ᵥ dir), hmassPos]
    · nlinarith [hcon carrier hcarrierMem, hcarrierPos, hmassPos]
  rw [hmass, ← Finset.mul_sum] at hstrict
  nlinarith [hstrict, hsub, huniv.symm.le, hmassPos]

/-- **The light-atom law, rank-one chart.**  The rank-one gap shape on `C0`
forces a label of `C0` with `weight * (1 + lam) <= 1`: the needle collapses
one weight of the tied set at the rate the needle grows. -/
theorem exists_light_weight_of_rankOneGap (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (lam : ℝ) (gapDir : Fin k → ℝ)
    (hlam : 0 ≤ lam) (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C0 = 1 + lam • atomMatrix gapDir) :
    ∃ label ∈ C0, D.weight label * (1 + lam) ≤ 1 := by
  refine exists_weight_mul_le_of_direction_mass D C0 gapDir hunit (1 + lam)
    (by linarith) ?_
  have hsum := dotProduct_subsetSum_mulVec_of_finset D C0 gapDir
  rw [hgap, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    atomMatrix, vecMulVec_mulVec_eq, hunit, one_smul] at hsum
  rw [← hsum, dotProduct_add, dotProduct_smul, smul_eq_mul, hunit]
  ring

/-- **The light-atom law, needle chart.**  The rank-two gap shape forces a
label of `C0` with `weight * (1 + s1) <= 1`. -/
theorem exists_light_weight_of_needleGap (D : WeightedDesign m k)
    (C0 : Finset (Fin m)) (s1 s2 : ℝ) (dirOne dirTwo : Fin k → ℝ)
    (hs2 : 0 ≤ s2) (hle : s2 ≤ s1)
    (hunitOne : dirOne ⬝ᵥ dirOne = 1) (hortho : dirOne ⬝ᵥ dirTwo = 0)
    (hgap : subsetSum D C0 = 1 + s1 • atomMatrix dirOne + s2 • atomMatrix dirTwo) :
    ∃ label ∈ C0, D.weight label * (1 + s1) ≤ 1 := by
  have hs1 : 0 ≤ s1 := le_trans hs2 hle
  refine exists_weight_mul_le_of_direction_mass D C0 dirOne hunitOne (1 + s1)
    (by linarith) ?_
  have hsum := dotProduct_subsetSum_mulVec_of_finset D C0 dirOne
  rw [hgap, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, atomMatrix, atomMatrix,
    vecMulVec_mulVec_eq, vecMulVec_mulVec_eq, hunitOne, one_smul] at hsum
  have hcommOT : dirTwo ⬝ᵥ dirOne = 0 := by rw [dotProduct_comm]; exact hortho
  rw [hcommOT] at hsum
  rw [← hsum, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, hunitOne]
  have hzeroSmul : dirOne ⬝ᵥ ((0 : ℝ) • dirTwo) = 0 := by
    rw [dotProduct_smul, smul_eq_mul, zero_mul]
  rw [hzeroSmul]
  ring

/-! ## The `(6,3)` instances -/

/-- Every triple of six labels has a triple complement. -/
theorem card_compl_three_of_card_three (C0 : Finset (Fin 6)) (hcard : C0.card = 3) :
    C0ᶜ.card = 3 := by
  rw [Finset.card_compl, Fintype.card_fin, hcard]

/-- The gap needle at the deciding cell: at a `(6,3)` tie with weights at
most `tau`, every triple's gap form gets to `(1 - 2 tau) / tau` along some
direction. -/
theorem exists_gapNeedle_of_isTie_six_three (D : WeightedDesign 6 3)
    (htie : IsTie D) (tau : ℝ) (htauPos : 0 < tau)
    (hbound : ∀ label, D.weight label ≤ tau)
    (C0 : Finset (Fin 6)) (hcard : C0.card = 3) :
    ∃ probe : Fin 3 → ℝ, probe ≠ 0 ∧
      (1 - 2 * tau) * (probe ⬝ᵥ probe)
        ≤ tau * (probe ⬝ᵥ ((subsetSum D C0 - 1) *ᵥ probe)) :=
  exists_gapNeedle_of_isTie D htie tau htauPos hbound C0
    (card_compl_three_of_card_three C0 hcard)

/-- The jaw budget at the deciding cell: a `(6,3)` tie with the rank-one gap
shape on a triple pays the budget `1 <= tin * (1 + lam) + tout`. -/
theorem one_le_jaw_budget_of_isTie_of_rankOneGap_six_three
    (D : WeightedDesign 6 3) (htie : IsTie D)
    (C0 : Finset (Fin 6)) (hcard : C0.card = 3)
    (tin tout lam : ℝ) (gapDir : Fin 3 → ℝ)
    (htoutPos : 0 < tout) (htinNonneg : 0 ≤ tin)
    (hlam : 0 ≤ lam) (hunit : gapDir ⬝ᵥ gapDir = 1)
    (hgap : subsetSum D C0 = 1 + lam • atomMatrix gapDir)
    (hinW : ∀ label ∈ C0, D.weight label ≤ tin)
    (houtW : ∀ label ∈ C0ᶜ, D.weight label ≤ tout) :
    1 ≤ tin * (1 + lam) + tout :=
  one_le_jaw_budget_of_isTie_of_rankOneGap D htie C0
    (card_compl_three_of_card_three C0 hcard) tin tout lam gapDir
    htoutPos htinNonneg hlam hunit hgap hinW houtW

end Gtz
