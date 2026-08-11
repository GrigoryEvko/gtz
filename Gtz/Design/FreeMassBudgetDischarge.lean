import Gtz.Design.StressFreeStratum
import Gtz.Design.BalancedStratum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The free-mass budget hypothesis is a landed theorem, and the stress-free hinge
# arm has exactly one open hypothesis

`Gtz.FreeMassBudgetCertificate` (`Gtz/Design/StressFreeStratum.lean:1012`) is
DEFINED as, verbatim, the statement of `Gtz.posDef_gap_of_freeMassBudget`
(`Gtz/Design/BalancedStratum.lean:309`).  That module's own docstring says so:
"It stands here as a named hypothesis so that this module carries no duplicate
of it; every use below is discharged by that theorem."  It is therefore not open
content, and the three consumers in `StressFreeStratum` that carry it as a
hypothesis can be restated with that hypothesis removed.

The consequence for the record is arithmetical, not mathematical: the stress-free
arm of the `(6,3)` hinge has ONE open hypothesis, `Gtz.NoStressResidual 6`, not
two.  And `NoStressResidual 6` is strictly stronger than the conclusion it is
used to reach: it demands a STRICTLY dominating triple for every primitive
stress-free design, including designs that are not ties at all, so it entails
`GtzWeighted 6 3` on that stratum and not merely the weak-to-strict upgrade.
-/

namespace Gtz

open Matrix

/-- **The free-mass budget hypothesis is discharged, at every size and rank.**
It is definitionally the statement of `Gtz.posDef_gap_of_freeMassBudget`. -/
theorem freeMassBudgetCertificate_holds (size rank : ℕ) :
    FreeMassBudgetCertificate size rank :=
  fun design selected hfreePosDef hbudget =>
    posDef_gap_of_freeMassBudget design selected hfreePosDef hbudget

/-- Either strict certificate produces a strictly dominating subset,
unconditionally. -/
theorem posDef_gap_of_hasStrictCertificate_unconditional {size : ℕ}
    (design : WeightedDesign size 3) (selected : Finset (Fin size))
    (hcertificate : HasStrictCertificate design selected) :
    (subsetSum design selected - 1).PosDef :=
  posDef_gap_of_hasStrictCertificate (freeMassBudgetCertificate_holds size 3)
    design selected hcertificate

/-- **No triple of a tie carries a strict certificate.**  This is why the
certificate arm of `Gtz.sixThree_exists_posDef_triple_of_stressFree` is empty on
the whole tie locus: the case split there is vacuous at every tie, so the
residual carries the entire statement. -/
theorem not_hasStrictCertificate_of_isTie {size : ℕ} (design : WeightedDesign size 3)
    (htie : IsTie design) (selected : Finset (Fin size)) (hcard : selected.card = 3) :
    ¬ HasStrictCertificate design selected := fun hcertificate =>
  htie.2 selected hcard
    (posDef_gap_of_hasStrictCertificate_unconditional design selected hcertificate)

/-- **The stress-free arm of the `(6,3)` hinge, with the discharged hypothesis
removed: one open Prop, not two.** -/
theorem sixThree_hasParallelPair_of_isTie_of_stressFree_ofResidual
    (hresidual : NoStressResidual 6) (design : WeightedDesign 6 3) (htie : IsTie design)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    HasParallelPair design :=
  sixThree_hasParallelPair_of_isTie_of_stressFree
    (freeMassBudgetCertificate_holds 6 3) hresidual design htie hstressFree

/-- The same for the positive form. -/
theorem sixThree_exists_posDef_triple_of_stressFree_ofResidual
    (hresidual : NoStressResidual 6) (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design)
    (hstressFree : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) :
    ∃ dominatingTriple : Finset (Fin 6), dominatingTriple.card = 3
      ∧ (subsetSum design dominatingTriple - 1).PosDef :=
  sixThree_exists_posDef_triple_of_stressFree (freeMassBudgetCertificate_holds 6 3)
    hresidual design hprimitive hstressFree

end Gtz
