/-
# The split-tetrahedron first-order certificate, made QUANTITATIVE

`Gtz.Ties.StratumFirstOrder` proves the Farkas identity at `splitSevenDesign` and reads
two consequences off it: some rainbow tie-form velocity is nonnegative
(`rainbowSeven_exists_nonnegative_velocity`), and some is strictly positive as soon as any
is nonzero (`rainbowSeven_exists_positive_velocity`).  Both are EXISTENCE statements with
no constant attached.  This file supplies the constant.

## What is new here, and what is merely wired

Nothing in this file is a new inequality.  The engine is
`Gtz.covector_forces_firing` / `Gtz.firing_margin_ge_of_covector_and_floor`
(`Gtz.Quantitative.CollarRate`), the field-blind Stiemke firing already shipped for the
collar-rate reduction: a nonnegative covector of total mass one annihilating a family of
rates forces the family's supremum above `covector chosen · (− rate chosen)`.  What was
missing was the OBSERVATION that the split tetrahedron's twenty rainbow multipliers are
exactly such a covector — `rainbowSevenMultiplier_pos`,
`rainbowSevenMultiplier_sum_one`, `splitSevenDesign_farkasIdentity_zero` are its three
hypotheses verbatim — and the instantiation.  Both theorems below are one application
each.

## PROVED here (kernel-checked)

* `rainbowSevenVelocityFamily` — the twenty tie-form velocities of an admissible
  direction as one `Fin 20 → ℝ` family, so the firing engine can consume them.
* `rainbowSevenMultiplier_floor` — every multiplier is at least `1/32`, by exhaustion
  over the twenty entries.
* `rainbowSeven_firingMargin_ge_multiplier_mul_descent` — the largest tie-form velocity
  is at least the chosen triple's own multiplier times its own descent.  Instantiates
  `covector_forces_firing`.
* `rainbowSeven_firingMargin_ge_floor_mul_bound` — **the sharp-maximum law**: along every
  admissible tangent direction, the largest of the twenty tie-form velocities is at least
  `1/32` of any lower bound on the magnitude of a single entry.  Instantiates
  `firing_margin_ge_of_covector_and_floor`.

## What this buys, stated without inflation

`rainbowSeven_exists_nonnegative_velocity` closes the elementary route to a nearby
counterexample: no admissible direction pushes all twenty tie forms down.  The theorems
here say more — the rise is bounded below by a fixed fraction of the fall, so the maximum
tie-form velocity is a SHARP function of the direction, growing linearly in the size of
the largest single velocity rather than merely being nonnegative.  In the vocabulary of
nonsmooth analysis this is the statement that the max-function
`direction ↦ max_T (tie-form velocity of T)` has a weak sharp minimum at the stratum with
modulus at least `1/32`; the shipped Stiemke firing IS the finite-dimensional error-bound
lemma behind it.  [The nonsmooth-analysis reading is CITED framing — Burke–Ferris weak
sharp minima, Azé–Corvellec strong slope; the inequality itself is proved here.]

The sharp constant available from these multipliers is `1/31`, not `1/32`: the engine's
own conclusion is `λ_chosen · (−rate) ≤ sup`, so `sup ≥ (λ/(1−λ))·(−rate)` and the worst
`λ` is `1/32`.  `firing_margin_ge_of_covector_and_floor` throws the `1/(1−λ)` away in
exchange for a two-sided statement covering the case where the chosen entry is already
positive.  `1/32` is what is proved below; `1/31` is what the same certificate supports
on the negative branch alone.

## HONEST SCOPE — what is NOT established

The bound is on tie-form VELOCITIES at frozen probes, exactly as in
`Gtz.Ties.StratumFirstOrder`, and the bridge from velocities to `Dominates` still runs in
one direction only (`rainbowSevenTriple_ray_not_posSemidef_of_velocity_neg`).  A large
positive tie-form velocity does NOT keep a triple dominating —
`stratumCriticalRay_not_posSemidef` exhibits a critical velocity whose frozen form rises
at order two while its triple's gap determinant goes negative at every nonzero step.  So
this file does not close `SplitSevenNeighbourhoodCovering` and does not weaken the
counterexample.  What it removes is the ambiguity in the word "no first-order descent":
the certificate is not merely a sign condition, it carries a rate.

The bound is also silent exactly where the first-order package was already silent: on the
critical cone, where every tie-form velocity vanishes and the hypothesis
`bound ≤ |velocity chosen|` can only be satisfied by `bound = 0`.  That cone is the tie
stratum itself; the module header of `Gtz.Ties.StratumFirstOrder` describes it.

## MEASURED, not proved here

Nothing.  Every number below is a kernel computation.
-/
import Mathlib
import Gtz.Ties.StratumFirstOrder
import Gtz.Quantitative.CollarRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-- The twenty rainbow tie-form velocities of an admissible direction, as one family.
Packaging the velocities as a `Fin 20 → ℝ` is what lets the shipped Stiemke firing engine
consume them; there is no content here beyond the currying. -/
noncomputable def rainbowSevenVelocityFamily (atomVelocity : Fin 7 → Fin 3 → ℝ)
    (tripleIndex : Fin 20) : ℝ :=
  gapFormVelocity splitSevenDesign atomVelocity (rainbowSevenTriple tripleIndex)
    (tetraAtom (rainbowSevenMissedDirection tripleIndex))

/-- **The uniform positivity floor of the certificate.**  Every one of the twenty
multipliers is at least `1/32` — eight of them attain it, the other twelve are `1/16`.
This is the number that becomes the sharp-minimum modulus below. -/
theorem rainbowSevenMultiplier_floor (tripleIndex : Fin 20) :
    (1 : ℝ) / 32 ≤ rainbowSevenMultiplier tripleIndex := by
  fin_cases tripleIndex <;> norm_num [rainbowSevenMultiplier]

/-- **The quantitative upgrade of `rainbowSeven_exists_nonnegative_velocity`.**  Along
every admissible tangent direction, the largest of the twenty tie-form velocities is at
least the chosen triple's multiplier times that triple's own descent: you cannot drive one
rainbow triple's tie form down without some rainbow triple's tie form rising by at least
`λ_chosen` times as much.

The existence statement in `Gtz.Ties.StratumFirstOrder` is the special case that reads off
only the sign.  The engine is `Gtz.covector_forces_firing`; its three hypotheses are the
positivity, the total mass, and the Farkas identity, verbatim. -/
theorem rainbowSeven_firingMargin_ge_multiplier_mul_descent
    (atomVelocity : Fin 7 → Fin 3 → ℝ) (weightVelocity : Fin 7 → ℝ)
    (hmass : ∑ atomIndex, weightVelocity atomIndex = 0)
    (htrace : parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0)
    (chosenIndex : Fin 20) :
    rainbowSevenMultiplier chosenIndex * (-rainbowSevenVelocityFamily atomVelocity chosenIndex)
      ≤ (Finset.univ : Finset (Fin 20)).sup' ⟨chosenIndex, Finset.mem_univ chosenIndex⟩
          (rainbowSevenVelocityFamily atomVelocity) :=
  covector_forces_firing Finset.univ chosenIndex (Finset.mem_univ chosenIndex)
    rainbowSevenMultiplier (rainbowSevenVelocityFamily atomVelocity)
    (fun tripleIndex _ => (rainbowSevenMultiplier_pos tripleIndex).le)
    rainbowSevenMultiplier_sum_one
    (splitSevenDesign_farkasIdentity_zero atomVelocity weightVelocity hmass htrace)

/-- **THE SHARP-MAXIMUM LAW AT THE SPLIT TETRAHEDRON.**  Along every admissible tangent
direction, the largest of the twenty tie-form velocities is at least `1/32` of any lower
bound on the MAGNITUDE of a single one of them — whichever sign that one carries.

This is what "no first-order descent" means with a constant attached.  The two-sided
handling is the engine's: a negative dominant entry fires through the certificate, a
positive one clears the bound directly.  It says nothing about whether a triple SURVIVES
the perturbation; see the module header and `stratumCriticalRay_not_posSemidef`. -/
theorem rainbowSeven_firingMargin_ge_floor_mul_bound
    (atomVelocity : Fin 7 → Fin 3 → ℝ) (weightVelocity : Fin 7 → ℝ)
    (hmass : ∑ atomIndex, weightVelocity atomIndex = 0)
    (htrace : parsevalTraceVelocity splitSevenDesign atomVelocity weightVelocity = 0)
    (chosenIndex : Fin 20) (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hfloor : bound ≤ |rainbowSevenVelocityFamily atomVelocity chosenIndex|) :
    (1 : ℝ) / 32 * bound
      ≤ (Finset.univ : Finset (Fin 20)).sup' ⟨chosenIndex, Finset.mem_univ chosenIndex⟩
          (rainbowSevenVelocityFamily atomVelocity) :=
  firing_margin_ge_of_covector_and_floor Finset.univ chosenIndex (Finset.mem_univ chosenIndex)
    rainbowSevenMultiplier (rainbowSevenVelocityFamily atomVelocity) (1 / 32) bound
    (fun tripleIndex _ => (rainbowSevenMultiplier_pos tripleIndex).le)
    rainbowSevenMultiplier_sum_one
    (splitSevenDesign_farkasIdentity_zero atomVelocity weightVelocity hmass htrace)
    (rainbowSevenMultiplier_floor chosenIndex) (by norm_num) (by norm_num)
    hboundNonneg hfloor

end Gtz
