/-
# The crux value controls the collar geometry

Two lanes of this campaign were developed by agents who could not see each other and
who each concluded, separately, that a leverage cap at a crux was unavailable.

  * The **collar lane** (gap 3) works on `Gtz.collaredSet`, the compact class of
    configurations with a positive weight floor.  Its own adjudication --
    `Gtz.weight_mul_leverageCap_sub_le` -- shows that a leverage cap yields only an
    UPPER bound on the weights, never a floor, and concludes that the crux funnel
    cannot cap the leverage.  That is correct about the direction it tests.

  * The **value lane** (gap 4) proves `Gtz.SixThreeCrux.hasWeightFloor_neg_chartObjective`:
    at a crux every weight is at least `-chartObjective`, which is strictly positive.

The two were landed in the same slot and never joined.  Joining them is immediate and
reverses the collar lane's verdict in the one direction that matters:

  **A CRUX HAS A WEIGHT FLOOR, THEREFORE IT HAS A LEVERAGE CAP, AND THE CAP IS THE
  RECIPROCAL OF THE CRUX VALUE.**

`Gtz.SixThreeCrux.leverageOf_le_inv_neg_chartObjective` is that statement.  The
implication the collar lane refuted -- cap to floor -- is still refuted; what is
supplied here is the converse, floor to cap, which the value lane had already made
available and which nothing had consumed.

## What this buys, stated exactly

* **THE COLLAR CLASS IS INHABITED BY EVERY CRUX, AT AN EXPLICIT FLOOR.**
  `Gtz.SixThreeCrux.mem_collaredSet_neg_chartObjective`.  The collar lane's
  compactness machinery therefore applies to cruxes; it was never shown to before.

* **ONE FLOOR SERVES EVERY CRUX.**  `Gtz.SixThreeCrux.mem_collaredSet_neg_chartObjective_of_other`
  places an arbitrary crux in the collared class cut out by a DIFFERENT crux's value.
  This is the uniformity the collar lane's measured erosion was thought to destroy: it
  holds because all cruxes share one chart value
  (`Gtz.SixThreeCrux.chartObjective_eq`), not because any constant is uniform.

* **GAP 2 AND GAP 3 ARE THE SAME UNKNOWN NUMBER.**
  `Gtz.SixThreeCrux.leverageOf_le_inv_of_chartValueBandExclusion`: an a-priori value
  band of width `band` is exactly a leverage cap of `1 / band` at every crux.  The
  value lane's missing epsilon and the collar lane's missing cap are reciprocals of
  each other, so neither lane can be closed without the other.

* **A SHARPENING, FROM THE THIRD LANE.**  Feeding the sharp box's quadratic floor
  `Gtz.SixThreeCrux.pairingMassFloor` through the weighted diagonal law
  `Gtz.sum_weight_mul_atomPairing_mul_atomPairing` gives
  `Gtz.SixThreeCrux.atomShare_lt_one_sub_neg_chartObjective`: every atom share is
  strictly below `1 - (-chartObjective)`, sharpening the shipped `share < 1`.
  Dividing by the weight floor improves the cap to `1 / (-chartObjective) - 1`
  (`Gtz.SixThreeCrux.leverageOf_lt_inv_neg_chartObjective_sub_one`).

## What this does NOT do

It does not move `Gtz.GtzWeighted 6 3`, and it supplies no number.  `-chartObjective`
at a crux is positive and at most `4/27`, so the cap it names is at least `27/4` and
has no upper bound without an a-priori lower bound on the crux value -- which IS gap 2.
Every statement here is conditional on a crux, a structure that is empty exactly when
the conjecture holds, so none of it can be exhibited.  What changes is the map: two
lanes that were being costed separately are now known to be the same lane.
-/
import Gtz.Quantitative.ValueLaneBandExclusion
import Gtz.Quantitative.SixThreeFrontierSharp
import Gtz.Design.CollaredCompact
import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.FrameConservation
import Gtz.Design.NearPencilTransport

namespace Gtz

/-! ## The cap -/

/-- **THE CRUX LEVERAGE CAP.**  At a crux every leverage is at most the reciprocal of
the crux's own chart value.  The whole proof is the shipped Parseval bound
`Gtz.leverage_le_inv_floor_of_parseval` applied to the shipped crux weight floor
`Gtz.SixThreeCrux.hasWeightFloor_neg_chartObjective`; nothing else enters.  The collar
lane's `Gtz.weight_mul_leverageCap_sub_le` refutes the CONVERSE (a cap does not give a
floor) and is untouched by this. -/
theorem SixThreeCrux.leverageOf_le_inv_neg_chartObjective (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    leverageOf (crux.design.atom atomIndex)
      ≤ 1 / -chartObjective (chartPointOfDesign crux.design) :=
  leverage_le_inv_floor_of_parseval crux.design.isParseval crux.pos_neg_chartObjective
    crux.hasWeightFloor_neg_chartObjective atomIndex

/-! ## The collar class -/

/-- **EVERY CRUX IS COLLARED, AT ITS OWN VALUE.**  The weight floor comes from the value
lane and the leverage floor from `Gtz.AllHeavy`, so the crux's raw configuration lies in
the compact class `Gtz.collaredSet 6 3` cut out at floor `-chartObjective`.  Before this
the collar lane had no theorem placing a crux in its own class. -/
theorem SixThreeCrux.mem_collaredSet_neg_chartObjective (crux : SixThreeCrux) :
    (crux.design.atom, crux.design.weight)
      ∈ collaredSet 6 3 (-chartObjective (chartPointOfDesign crux.design)) :=
  design_mem_collaredSet crux.design crux.hasWeightFloor_neg_chartObjective
    (fun atomIndex => le_of_lt (crux.isAllHeavy atomIndex))

/-- **THE FLOOR IS UNIFORM ACROSS CRUXES.**  An arbitrary crux lies in the collared class
cut out by a DIFFERENT crux's value.  The two floors coincide because every crux is a
global minimiser of one objective on one domain, so all cruxes carry the same chart
value (`Gtz.SixThreeCrux.chartObjective_eq`).  Consequently a single compact class
contains every crux, and the collar lane never needs a floor-uniform constant -- the
measured erosion of that constant, which was thought to be the lane's obstruction, is
not on the path. -/
theorem SixThreeCrux.mem_collaredSet_neg_chartObjective_of_other (base crux : SixThreeCrux) :
    (crux.design.atom, crux.design.weight)
      ∈ collaredSet 6 3 (-chartObjective (chartPointOfDesign base.design)) := by
  refine design_mem_collaredSet crux.design ?_
    (fun atomIndex => le_of_lt (crux.isAllHeavy atomIndex))
  rw [SixThreeCrux.chartObjective_eq base crux]
  exact crux.hasWeightFloor_neg_chartObjective

/-! ## Gap 2 and gap 3 are reciprocals -/

/-- **A VALUE BAND IS A LEVERAGE CAP.**  If no crux has chart value above `-band` then
every crux leverage is at most `1 / band`.  This is the exact exchange rate between the
value lane's missing a-priori band (gap 2) and the collar lane's missing leverage cap
(gap 3): they are reciprocal statements of one unknown, so a bound on either is a bound
on the other and neither can be closed alone. -/
theorem SixThreeCrux.leverageOf_le_inv_of_chartValueBandExclusion {band : ℝ}
    (hband : 0 < band) (hexcl : ChartValueBandExclusion band) (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    leverageOf (crux.design.atom atomIndex) ≤ 1 / band := by
  refine leverage_le_inv_floor_of_parseval crux.design.isParseval hband ?_ atomIndex
  intro other
  refine le_trans ?_ (crux.hasWeightFloor_neg_chartObjective other)
  have hvalue := hexcl crux
  linarith

/-- **A VALUE BAND PUTS EVERY CRUX IN ONE EXPLICIT COMPACT CLASS.**  The companion of
the cap above: under a band exclusion at width `band`, every crux lies in
`Gtz.collaredSet 6 3 band`, a class named by an explicit number rather than by the
unknown crux value. -/
theorem SixThreeCrux.mem_collaredSet_of_chartValueBandExclusion {band : ℝ}
    (hexcl : ChartValueBandExclusion band) (crux : SixThreeCrux) :
    (crux.design.atom, crux.design.weight) ∈ collaredSet 6 3 band := by
  refine design_mem_collaredSet crux.design ?_
    (fun atomIndex => le_of_lt (crux.isAllHeavy atomIndex))
  intro other
  refine le_trans ?_ (crux.hasWeightFloor_neg_chartObjective other)
  have hvalue := hexcl crux
  linarith

/-! ## The sharpening from the quadratic floor -/

/-- **THE CRUX SHARE BOUND.**  Every atom share at a crux is strictly below
`1 - (-chartObjective)`, sharpening the shipped `share < 1` by exactly the crux value.

Three lanes meet here.  The weighted diagonal law
`Gtz.sum_weight_mul_atomPairing_mul_atomPairing` at a repeated index says
`t_c * L_c ^ 2 + sum_{d != c} t_d * p_cd ^ 2 = L_c`.  The sharp box's quadratic floor
`Gtz.SixThreeCrux.pairingMassFloor` says `L_c < sum_{d != c} p_cd ^ 2`.  The value
lane's weight floor lets the second be inserted into the first with a factor
`-chartObjective`.  Dividing by `L_c > 1` gives the bound. -/
theorem SixThreeCrux.atomShare_lt_one_sub_neg_chartObjective (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    atomShare crux.design atomIndex
      < 1 - -chartObjective (chartPointOfDesign crux.design) := by
  have hfloorPos : 0 < -chartObjective (chartPointOfDesign crux.design) :=
    crux.pos_neg_chartObjective
  have hweight := crux.hasWeightFloor_neg_chartObjective
  have hheavy : 1 < leverageOf (crux.design.atom atomIndex) := crux.isAllHeavy atomIndex
  have hleverageDot : leverageOf (crux.design.atom atomIndex)
      = crux.design.atom atomIndex ⬝ᵥ crux.design.atom atomIndex :=
    leverageOf_eq_dotProduct_self _
  have hdiagonal := sum_weight_mul_atomPairing_mul_atomPairing crux.design atomIndex atomIndex
  have hsplit := Finset.sum_compl_add_sum ({atomIndex} : Finset (Fin 6))
    (fun other => crux.design.weight other
      * ((crux.design.atom atomIndex ⬝ᵥ crux.design.atom other)
        * (crux.design.atom other ⬝ᵥ crux.design.atom atomIndex)))
  rw [Finset.sum_singleton, hdiagonal, ← hleverageDot] at hsplit
  have htail :
      -chartObjective (chartPointOfDesign crux.design)
          * ∑ other ∈ ({atomIndex}ᶜ : Finset (Fin 6)),
              (crux.design.atom atomIndex ⬝ᵥ crux.design.atom other) ^ 2
        ≤ ∑ other ∈ ({atomIndex}ᶜ : Finset (Fin 6)), crux.design.weight other
            * ((crux.design.atom atomIndex ⬝ᵥ crux.design.atom other)
              * (crux.design.atom other ⬝ᵥ crux.design.atom atomIndex)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun other _ => ?_)
    rw [dotProduct_comm (crux.design.atom other), ← sq]
    exact mul_le_mul_of_nonneg_right (hweight other) (sq_nonneg _)
  have hstrict := (mul_lt_mul_iff_of_pos_left hfloorPos).2 (crux.pairingMassFloor atomIndex)
  have hleveragePos : (0 : ℝ) < leverageOf (crux.design.atom atomIndex) := by linarith
  have hproduct : leverageOf (crux.design.atom atomIndex)
        * (-chartObjective (chartPointOfDesign crux.design)
          + crux.design.weight atomIndex * leverageOf (crux.design.atom atomIndex))
      < leverageOf (crux.design.atom atomIndex) * 1 := by
    nlinarith [hsplit, htail, hstrict]
  have hcancel := lt_of_mul_lt_mul_left hproduct (le_of_lt hleveragePos)
  rw [atomShare]
  linarith

/-- **THE SHARPENED CAP.**  Dividing the share bound by the weight floor improves
`Gtz.SixThreeCrux.leverageOf_le_inv_neg_chartObjective` by a full unit: every crux
leverage is strictly below `1 / (-chartObjective) - 1`.  Since the crux value is at most
`4 / 27`, the cap this names is still at least `23 / 4`, so the improvement is
structural rather than numerical. -/
theorem SixThreeCrux.leverageOf_lt_inv_neg_chartObjective_sub_one (crux : SixThreeCrux)
    (atomIndex : Fin 6) :
    leverageOf (crux.design.atom atomIndex)
      < 1 / -chartObjective (chartPointOfDesign crux.design) - 1 := by
  have hfloorPos : 0 < -chartObjective (chartPointOfDesign crux.design) :=
    crux.pos_neg_chartObjective
  have hshare := crux.atomShare_lt_one_sub_neg_chartObjective atomIndex
  have hweight := crux.hasWeightFloor_neg_chartObjective atomIndex
  have hscaled : -chartObjective (chartPointOfDesign crux.design)
      * leverageOf (crux.design.atom atomIndex) ≤ atomShare crux.design atomIndex := by
    rw [atomShare]
    exact mul_le_mul_of_nonneg_right hweight (leverageOf_nonneg _)
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hfloorPos]
  nlinarith [hshare, hscaled]

end Gtz
