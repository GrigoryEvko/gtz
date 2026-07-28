/-
# The volume-average law is false

Volume sampling is the projection determinantal measure on `rank`-subsets,
`π(C) = det P_C` (`Gtz.shadowDeterminant`), a probability measure by Cauchy–Binet
(`Gtz.sum_shadowDeterminant_eq_one`).  The **volume-average law** proposed for this
campaign is that the π-average of the least eigenvalue clears the domination
threshold,

    Φ_S(D)  =  E_π[ λ_min(S_C) ] − 1  ≥  0     for every real weighted design.

It would prove GTZ outright, uniformly in size and rank, because an average never
exceeds a maximum: `exists_dominates_of_hasDominatingVolumeSamplingAverage` below is
that implication, and it is the whole reason the functional was worth attacking.  It is
also a smooth statement, where `max_C λ_min(S_C)` is a max of mins and nonsmooth twice
over — the structural reason the law was proposed.

**THE LAW IS FALSE.**  `not_forall_hasDominatingVolumeSamplingAverage` refutes it at an
exactly rational `(3,2)` design with integer atoms `(−4,1)`, `(0,1)`, `(1,1)` and
weights `(1/20, 3/4, 1/5)`.  There

    π = (3/5, 1/4, 3/20)     E_π[λ_min(S_C)]  ≤  2161/2210  =  0.97783 …  <  1,

so `Φ_S < 0` by a margin of at least `49/2210`.  The three least eigenvalues are the
surds `9 − √65`, `(19 − √261)/2`, `(3 − √5)/2` and their true π-average is
`0.97550 …`; no surd appears below, because the refutation only ever needs the
Rayleigh quotient at three explicit integer probes, `(1,4)`, `(1,5)`, `(5,−3)`.

## Two witnesses, because the first one is not all-heavy

The design above has leverages `17`, `1`, `2` — atom `1` sits EXACTLY at the heaviness
threshold, so it is not `Gtz.AllHeavy` and by itself leaves open the retreat "the law
might survive on the all-heavy stratum", the stratum the campaign's reductions operate
on.  `exists_allHeavy_design_failing_volumeSamplingAverage_law` closes that with a
second `(3,2)` design, atoms `(0, 6/5)`, `(1, −3/5)`, `(3, 9/5)` and weights
`(4/9, 1/2, 1/18)`, whose leverages are `36/25`, `34/25`, `306/25` — all strictly above
one — and whose margin is three times larger:

    π = (8/25, 8/25, 9/25)     E_π[λ_min(S_C)]  ≤  127994/138125  =  0.92665 …

against a true value of `0.91613 …`.  Both witnesses are corank one, `m = k + 1`, the
stratum where the ties are completely classified, and both have non-uniform weights
bounded away from zero.

## What is refuted, and what is not

NOT refuted, and nothing here says otherwise: `GtzWeighted`.  Each witness has a
dominating `2`-subset exhibited in the statement
(`volumeAverageKillDesign_dominates_zeroTwo`,
`heavyVolumeAverageKillDesign_dominates_oneTwo`), and `Gtz.gtz_rank_two` proves
`GtzWeightedAll 2` anyway.  Rank two is exactly why the witnesses are safe: they live
where the existence of a dominating subset is a theorem, so they can carry no
information about `(6,3)` or `(7,3)`.

NOT vacuous either.  The law's hypothesis is satisfiable and is satisfied with EQUALITY
at the regular tetrahedron: `tetraDesign_hasDominatingVolumeSamplingAverage`, because
all four triples dominate (`tetraDesign_dominates_of_card_three`, which the repository
had only for `{0,1,2}`) and the masses sum to one.  So the law is tight at the known
extremal design and fails elsewhere; the refutation is about the functional, not about
a badly posed statement.

NOT refuted either: the MATRIX average.  `Gtz.posSemidef_leverageWeightedAtomSum_sub_one`
says `E_π[S_C] ⪰ 1` for every design, and at this very witness that is verified
unconditionally and by hand:
`volumeAverageKillDesign_posSemidef_expectedSubsetSum_sub_one` computes
`E_π[S_C] = !![14, −3; −3, 2]` and exhibits the sum of squares putting it above the
identity.  So the two averages separate at one design — the matrix average clears the
threshold, the eigenvalue average does not — and the general reason is
`posSemidef_expectedSubsetSum_sub_volumeSamplingAverage_smul_one`: `λ_min` is concave,
so `E_π[λ_min] ≤ λ_min(E_π)` always, the wrong direction.  The law asked the
fluctuation of `λ_min` under π not to eat the whole gap between them.  It does.

## Why the law is stated existentially

`IsBelowSubsetSpectrum D C v` says `S_C ⪰ v·I`, so `v ≤ λ_min(S_C)`; the LARGEST such
`v` is `λ_min(S_C)` itself.  Hence

    E_π[λ_min(S_C)] ≥ 1   ⟺   SOME below-spectrum assignment averages to at least 1,

which is `HasDominatingVolumeSamplingAverage`.  Stating the law over ALL below-spectrum
assignments would be refutable by the constant assignment `v ≡ 0`
(`isBelowSubsetSpectrum_zero`), which says nothing; the existential form is the honest
one, and it is the one refuted here.  This route also keeps `λ_min` out of the
development entirely: no eigenvalue machinery, no spectral theorem, no surds, and the
refutation is an upper bound on every below-spectrum assignment at once.

## The elementary-symmetric identity, which survives the law's death

`sum_shadowDeterminant_eq_one` and the evaluation
`Gtz.shadowDeterminant_eq_weightProduct_mul_detSubsetSum` together say
`∑_C (∏_{c ∈ C} t_c) det S_C = 1`, so `exists_detSubsetSum_ge_inv_weightElementary`:
some `k`-subset has

    det S_C  ≥  1 / e_k(t),        e_k(t) = ∑_{|C| = k} ∏_{c ∈ C} t_c,

and at uniform weights `e_k = C(m,k)/m^k`, giving `det S_C ≥ m^k / C(m,k)` with NO
Maclaurin inequality — the uniform case is an exact evaluation of `e_k`.  It is SHARP
at the tetrahedron, where `e_3 = 1/16` and every triple has `det S_C = 16`
(`tetraDesign_detSubsetSum_eq` and `tetraDesign_weightElementary_three`), so all the
relations are equalities at the known extremal design.  This is stronger than what
`Gtz.exists_shadowDeterminant_ge_inv_binomial` yields — strictly so whenever the rank is
below the size — and it bounds a DETERMINANT, hence bounds `λ_min` from ABOVE and is not
a step toward GTZ.

**The degenerate case is handled explicitly, because the natural statement is false.**
`E_π[1/det S_C] = e_k(t)` is FALSE as soon as one `k`-subset is dependent: the
dependent subsets carry π-mass zero, so the sum runs over the independent subsets only.
`sum_shadowDeterminant_div_detSubsetSum_eq_independentWeightProduct` is the true
identity and `sum_independentWeightProduct_lt_weightElementary_of_dependentSubset`
shows the gap is strict exactly when a dependent subset exists.  Note the trap the
division form sets in Lean: `x/0 = 0`, so the identity in the shape
`∑_C det P_C / det S_C = e_k(t)` would not typecheck-and-fail — it would typecheck and
be PROVABLE for the restricted sum while reading as the false claim.  The statement
here names the restriction.

## Deliberately absent

* No claim about the chart-side average `Φ_W = E_π[λ_min(P_C − diag t_C)]`.  It dies
  at the same witness — the rationalised chart gaps `Gram_C − I − v·diag(1/t_C)` give
  `Φ_W ≤ −23221/440800` there — but the chart block of THIS design has irrational
  entries and mechanising the level congruence that removes them is a separate build.
  What is refuted here is the `S`-side law, which is the primary half.
* No claim that `E_π[λ_min]` is the largest average of its kind, and no claim about
  any tilted measure `det P_C · (det S_C)^s`.  The tilt was scanned numerically and
  died at every scanned exponent; nothing about it is asserted here.
* No minimality claim for the witness.
* No restatement of `E_π[tr S_C] ≥ rank²`.  That is
  `Gtz.sq_rank_le_expectedElementary_one`, unconditional and already shipped; go there.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.StressCertificate
import Gtz.Design.VolumeSamplingAverage
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.PsdKit
import Gtz.Quantitative.VolumeSelectionFailure
import Gtz.Reduction.ExchangeInvariant
import Gtz.Reduction.MixedCharPolynomial
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Below the spectrum, without the spectrum

A real number sits below a subset's spectrum exactly when the shifted atom sum is
positive semidefinite.  This is `v ≤ λ_min(S_C)` with no eigenvalue named, and every
statement in this file is phrased through it. -/

/-- **`value` lies below the spectrum of the selected atoms**: `S_C ⪰ value·I`.
Equivalently `value ≤ λ_min(S_C)`, and the largest `value` with this property IS
`λ_min(S_C)`; nothing below needs that identification. -/
def IsBelowSubsetSpectrum (D : WeightedDesign m k) (selected : Finset (Fin m))
    (value : ℝ) : Prop :=
  (subsetSum D selected - value • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef

/-- **The Rayleigh reading.**  A value below the spectrum is bounded at every probe by
the total squared projection of the selected atoms — this is the only consequence the
refutation uses, and it turns each eigenvalue bound into an integer computation. -/
theorem isBelowSubsetSpectrum_form_le (D : WeightedDesign m k)
    {selected : Finset (Fin m)} {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum D selected value) (probe : Fin k → ℝ) :
    value * (probe ⬝ᵥ probe) ≤ ∑ atomIndex ∈ selected, (D.atom atomIndex ⬝ᵥ probe) ^ 2 := by
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbelow).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, subsetSum_form_eq_sum_sq] at hform
  linarith

/-- Zero always lies below the spectrum: an atom sum is positive semidefinite.  This is
why the law must be stated existentially — quantifying over ALL below-spectrum
assignments would make it refutable by the constant `0`, which asserts nothing. -/
theorem isBelowSubsetSpectrum_zero (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    IsBelowSubsetSpectrum D selected 0 := by
  rw [IsBelowSubsetSpectrum, zero_smul, sub_zero]
  exact posSemidef_subsetSum D selected

/-- **A below-spectrum value reaching one forces domination.**  `S_C ⪰ value·I ⪰ I`;
the only content is transitivity read on the quadratic form. -/
theorem dominates_of_one_le_isBelowSubsetSpectrum (D : WeightedDesign m k)
    {selected : Finset (Fin m)} {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum D selected value) (hone : 1 ≤ value) :
    Dominates D selected := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨((posSemidef_subsetSum D selected).1).sub Matrix.isHermitian_one, fun probe => ?_⟩
  rw [star_trivial, dominationGap_form]
  have hbound := isBelowSubsetSpectrum_form_le D hbelow probe
  have hnormSq : 0 ≤ probe ⬝ᵥ probe := by
    rw [dotProduct_self_eq_sum_sq]
    exact Finset.sum_nonneg fun coord _ => sq_nonneg _
  nlinarith [hbound, hnormSq, hone]

/-! ## The volume-sampling average and the law -/

/-- **The volume-sampling average** of a per-subset value: `∑_{|C| = rank} det P_C · v_C`.
The coefficients are a probability measure (`Gtz.shadowDeterminant_nonneg`,
`Gtz.sum_shadowDeterminant_eq_one`), so this is a genuine expectation. -/
noncomputable def volumeSamplingAverage (D : WeightedDesign m k)
    (leastValue : Finset (Fin m) → ℝ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
    shadowDeterminant D selected * leastValue selected

/-- **THE VOLUME-AVERAGE LAW, at one design.**  Some assignment lying below every
subset's spectrum has volume-sampling average at least one.  This is `E_π[λ_min(S_C)] ≥ 1`
with `λ_min` never named: the largest below-spectrum assignment IS `λ_min`, so the
existential holds iff the inequality holds at `λ_min`, and is strictly weaker at any
other assignment.

That identification is argued, NOT mechanized — it needs `λ_min` to exist, i.e. the
spectral theorem, which nothing in this file uses.  Neither direction of the refutation
depends on it: `volumeAverageKillDesign_volumeSamplingAverage_le` bounds EVERY
below-spectrum assignment at once, so the witness kills the existential outright. -/
def HasDominatingVolumeSamplingAverage (D : WeightedDesign m k) : Prop :=
  ∃ leastValue : Finset (Fin m) → ℝ,
    (∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      IsBelowSubsetSpectrum D selected (leastValue selected))
    ∧ 1 ≤ volumeSamplingAverage D leastValue

/-- **THE IMPLICATION THE LAW WAS FOR.**  An average never exceeds a maximum, so a
design satisfying the volume-average law has a dominating `rank`-subset.  This is
GTZ at that design, and it is four lines: pick the subset where the assignment is
largest, bound the average by its value there using
`Gtz.sum_shadowDeterminant_eq_one`, and hand the resulting `1 ≤ value` to
`dominates_of_one_le_isBelowSubsetSpectrum`.

The implication is unconditional and survives the law's refutation intact.  It is
named for the implication and NOT for GTZ: the hypothesis is false in general
(`not_forall_hasDominatingVolumeSamplingAverage`), so this proves nothing about any
open cell. -/
theorem exists_dominates_of_hasDominatingVolumeSamplingAverage (D : WeightedDesign m k)
    (hlaw : HasDominatingVolumeSamplingAverage D) :
    ∃ selected : Finset (Fin m), selected.card = k ∧ Dominates D selected := by
  obtain ⟨leastValue, hbelow, haverage⟩ := hlaw
  have hfamilyNonempty : ((Finset.univ : Finset (Fin m)).powersetCard k).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using rank_le_of_design D)
  obtain ⟨best, hbestMem, hbestMax⟩ :=
    Finset.exists_max_image ((Finset.univ : Finset (Fin m)).powersetCard k) leastValue
      hfamilyNonempty
  have hbounded : volumeSamplingAverage D leastValue ≤ leastValue best := by
    have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        shadowDeterminant D selected * leastValue selected
          ≤ shadowDeterminant D selected * leastValue best := fun selected hmem =>
      mul_le_mul_of_nonneg_left (hbestMax selected hmem)
        (shadowDeterminant_nonneg D (Finset.mem_powersetCard.mp hmem).2)
    have hsummed := Finset.sum_le_sum hterm
    rwa [← Finset.sum_mul, sum_shadowDeterminant_eq_one D, one_mul] at hsummed
  exact ⟨best, (Finset.mem_powersetCard.mp hbestMem).2,
    dominates_of_one_le_isBelowSubsetSpectrum D (hbelow best hbestMem)
      (le_trans haverage hbounded)⟩

/-- **The eigenvalue average never beats the matrix average.**  Averaging the
below-spectrum certificates gives a below-spectrum certificate for the averaged matrix:
`E_π[S_C] ⪰ (E_π[v_C])·I`.  This is concavity of `λ_min` in the below-spectrum
vocabulary, and it is the WRONG direction for the law — `Gtz.posSemidef_leverageWeightedAtomSum_sub_one`
puts the matrix average above the identity for every design, and this says only that
the eigenvalue average is at most the matrix average's least eigenvalue.  The whole
content of the refutation below is that the gap between them can exceed the slack. -/
theorem posSemidef_expectedSubsetSum_sub_volumeSamplingAverage_smul_one
    (D : WeightedDesign m k) (leastValue : Finset (Fin m) → ℝ)
    (hbelow : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      IsBelowSubsetSpectrum D selected (leastValue selected)) :
    (expectedSubsetSum D
      - volumeSamplingAverage D leastValue • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef := by
  have hsplit : expectedSubsetSum D
        - volumeSamplingAverage D leastValue • (1 : Matrix (Fin k) (Fin k) ℝ)
      = ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          shadowDeterminant D selected
            • (subsetSum D selected - leastValue selected • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    rw [expectedSubsetSum, volumeSamplingAverage, Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun selected _ => ?_
    rw [smul_sub, smul_smul]
  rw [hsplit]
  exact Matrix.posSemidef_sum _ fun selected hmem =>
    (hbelow selected hmem).smul
      (shadowDeterminant_nonneg D (Finset.mem_powersetCard.mp hmem).2)

/-! ### The law is not absurd: it holds with equality at the tetrahedron

Before refuting the law it is worth exhibiting a design where it holds, so the
refutation reads as a fact about the functional rather than about a badly posed
statement.  At the regular tetrahedron EVERY triple dominates, so the constant
assignment `1` lies below every spectrum and averages to exactly `1`: the law holds
there, with no slack whatsoever.  That is the known extremal design, and the law being
TIGHT exactly there is why it was worth attacking. -/

/-- **A design all of whose `rank`-subsets dominate satisfies the law**, with the
constant assignment `1`: domination IS `IsBelowSubsetSpectrum … 1`, and the masses sum
to one. -/
theorem hasDominatingVolumeSamplingAverage_of_forall_dominates (D : WeightedDesign m k)
    (hdominates : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      Dominates D selected) :
    HasDominatingVolumeSamplingAverage D := by
  refine ⟨fun _ => 1, fun selected hmem => ?_, ?_⟩
  · rw [IsBelowSubsetSpectrum, one_smul]
    exact hdominates selected hmem
  · rw [volumeSamplingAverage]
    simp only [mul_one]
    rw [sum_shadowDeterminant_eq_one D]

/-- The tetrahedron's leverage is `3` at every vertex. -/
theorem leverageOf_tetraAtom (vertex : Fin 4) : leverageOf (tetraAtom vertex) = 3 := by
  rw [leverageOf, ← dotProduct_self_eq_sum_sq, tetraAtom_dot_self]

/-- **Every tetrahedron triple dominates.**  A triple omits one vertex `d`; Parseval at
uniform weight `1/4` makes the total squared projection `4|x|²`, so the triple's is
`4|x|² − ⟨g_d,x⟩²`, and Cauchy–Schwarz caps `⟨g_d,x⟩² ≤ 3|x|²` because every vertex has
leverage `3`.  The gap is therefore `3|x|² − ⟨g_d,x⟩² ≥ 0` at every probe.  The
repository proves this for `{0,1,2}` alone
(`Gtz.tetraDesign_dominates`); the four-triple statement is what the law needs. -/
theorem tetraDesign_dominates_of_card_three (selected : Finset (Fin 4))
    (hcard : selected.card = 3) : Dominates tetraDesign selected := by
  obtain ⟨missing, hmissing⟩ : ∃ vertex : Fin 4, vertex ∉ selected := by
    by_contra hall
    push Not at hall
    have hfull : selected = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [hfull, Finset.card_univ, Fintype.card_fin] at hcard
    exact absurd hcard (by norm_num)
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨((posSemidef_subsetSum tetraDesign selected).1).sub Matrix.isHermitian_one,
      fun probe => ?_⟩
  rw [star_trivial, dominationGap_form]
  have herased : selected = Finset.univ.erase missing := by
    refine Finset.eq_of_subset_of_card_le
      (fun vertex hvertex => Finset.mem_erase.mpr
        ⟨fun heq => hmissing (heq ▸ hvertex), Finset.mem_univ vertex⟩) ?_
    rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ missing), Finset.card_univ,
      Fintype.card_fin]
  have htotal : ∑ vertex, tetraDesign.weight vertex * (tetraDesign.atom vertex ⬝ᵥ probe) ^ 2
      = probe ⬝ᵥ probe := sum_weight_mul_atomOverlap_sq tetraDesign probe
  have hsplit : (tetraDesign.atom missing ⬝ᵥ probe) ^ 2
        + ∑ vertex ∈ Finset.univ.erase missing, (tetraDesign.atom vertex ⬝ᵥ probe) ^ 2
      = ∑ vertex, (tetraDesign.atom vertex ⬝ᵥ probe) ^ 2 :=
    Finset.add_sum_erase Finset.univ
      (fun vertex => (tetraDesign.atom vertex ⬝ᵥ probe) ^ 2) (Finset.mem_univ missing)
  have hquarter : ∑ vertex, tetraDesign.weight vertex * (tetraDesign.atom vertex ⬝ᵥ probe) ^ 2
      = (1/4 : ℝ) * ∑ vertex, (tetraDesign.atom vertex ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    rfl
  have hcauchy : (tetraDesign.atom missing ⬝ᵥ probe) ^ 2 ≤ 3 * (probe ⬝ᵥ probe) := by
    have hbound := atomOverlap_sq_le_leverage_mul_normSq (tetraDesign.atom missing) probe
    rwa [show tetraDesign.atom missing = tetraAtom missing from rfl, leverageOf_tetraAtom]
      at hbound
  rw [herased]
  rw [hquarter] at htotal
  linarith [hsplit, htotal, hcauchy]

/-- **THE LAW HOLDS AT THE TETRAHEDRON, WITH EQUALITY.**  All four triples dominate, so
the constant assignment `1` is below every spectrum and averages to exactly `1` — the
law's hypothesis is satisfiable, and satisfied with zero slack at the known extremal
design.  So the refutations below are about the functional, not about a vacuous or
unsatisfiable statement. -/
theorem tetraDesign_hasDominatingVolumeSamplingAverage :
    HasDominatingVolumeSamplingAverage tetraDesign :=
  hasDominatingVolumeSamplingAverage_of_forall_dominates tetraDesign
    fun selected hmem =>
      tetraDesign_dominates_of_card_three selected (Finset.mem_powersetCard.mp hmem).2

/-! ## The refuting witness at `(3,2)`

Three integer atoms in `ℝ²` and weights of denominator `20`.  Corank one, all leverages
above one, weights non-uniform but bounded below by `1/20`.  Everything below is exact
rational arithmetic and the least eigenvalues are never computed — three explicit
integer probes bound them from above, which is the direction the refutation needs. -/

/-- The three atoms of the volume-average witness: `(−4,1)`, `(0,1)`, `(1,1)`. -/
noncomputable def volumeAverageKillAtom : Fin 3 → Fin 2 → ℝ :=
  ![![-4, 1], ![0, 1], ![1, 1]]

/-- The exactly rational `(3,2)` design at which the volume-average law fails.
Parseval is the integer identity `(1/20)g₀g₀ᵀ + (3/4)g₁g₁ᵀ + (1/5)g₂g₂ᵀ = I₂`. -/
noncomputable def volumeAverageKillDesign : WeightedDesign 3 2 where
  atom := volumeAverageKillAtom
  weight := ![1/20, 3/4, 1/5]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_three, smul_eq_mul, volumeAverageKillAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- The three leverages are `17`, `1`, `2`.  Recorded because the middle atom sits
EXACTLY at the heaviness threshold, so this witness is not `Gtz.AllHeavy` — the strict
inequality fails at atom `1`.  That gap is closed separately by
`heavyVolumeAverageKillDesign_allHeavy` below, at a second witness whose every leverage
exceeds one; the reader should not have to take the stratum on trust. -/
theorem volumeAverageKillDesign_leverage_eq (atomIndex : Fin 3) :
    leverageOf (volumeAverageKillDesign.atom atomIndex) = ![17, 1, 2] atomIndex := by
  fin_cases atomIndex <;>
    norm_num [volumeAverageKillDesign, volumeAverageKillAtom, leverageOf, Fin.sum_univ_two]

/-! ### The three volume-sampling masses

`det P_C = (∏_{c ∈ C} t_c) · det S_C`, evaluated through
`Gtz.weightScaledVolumeScore_pair`, whose closed form is the squared `2 × 2` minor of
the two selected atoms. -/

/-- `π({0,1}) = (1/20)(3/4)·(−4)² = 3/5`. -/
theorem volumeAverageKillDesign_shadowDeterminant_zeroOne :
    shadowDeterminant volumeAverageKillDesign {0, 1} = 3/5 := by
  rw [← weightScaledVolumeScore_eq_shadowDeterminant_ofCard volumeAverageKillDesign
      (show ({0, 1} : Finset (Fin 3)).card = 2 by decide),
    weightScaledVolumeScore_pair volumeAverageKillDesign (show (0 : Fin 3) ≠ 1 by decide)]
  simp only [volumeAverageKillDesign, volumeAverageKillAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- `π({0,2}) = (1/20)(1/5)·(−5)² = 1/4`. -/
theorem volumeAverageKillDesign_shadowDeterminant_zeroTwo :
    shadowDeterminant volumeAverageKillDesign {0, 2} = 1/4 := by
  rw [← weightScaledVolumeScore_eq_shadowDeterminant_ofCard volumeAverageKillDesign
      (show ({0, 2} : Finset (Fin 3)).card = 2 by decide),
    weightScaledVolumeScore_pair volumeAverageKillDesign (show (0 : Fin 3) ≠ 2 by decide)]
  simp only [volumeAverageKillDesign, volumeAverageKillAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- `π({1,2}) = (3/4)(1/5)·(−1)² = 3/20`. -/
theorem volumeAverageKillDesign_shadowDeterminant_oneTwo :
    shadowDeterminant volumeAverageKillDesign {1, 2} = 3/20 := by
  rw [← weightScaledVolumeScore_eq_shadowDeterminant_ofCard volumeAverageKillDesign
      (show ({1, 2} : Finset (Fin 3)).card = 2 by decide),
    weightScaledVolumeScore_pair volumeAverageKillDesign (show (1 : Fin 3) ≠ 2 by decide)]
  simp only [volumeAverageKillDesign, volumeAverageKillAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- The three masses sum to one, as Cauchy–Binet requires — computed here rather than
quoted, as an arithmetic check on the three evaluations above. -/
theorem volumeAverageKillDesign_shadowDeterminant_sum :
    shadowDeterminant volumeAverageKillDesign {0, 1}
        + shadowDeterminant volumeAverageKillDesign {0, 2}
        + shadowDeterminant volumeAverageKillDesign {1, 2} = 1 := by
  rw [volumeAverageKillDesign_shadowDeterminant_zeroOne,
    volumeAverageKillDesign_shadowDeterminant_zeroTwo,
    volumeAverageKillDesign_shadowDeterminant_oneTwo]
  norm_num

/-! ### The three eigenvalue bounds, from three integer probes -/

/-- The pair reading of `isBelowSubsetSpectrum_form_le`: two atoms, two squared
pairings, and a `norm_num` computation on integers. -/
theorem isBelowSubsetSpectrum_pair_form_le {size dim : ℕ} (D : WeightedDesign size dim)
    {first second : Fin size} (hne : first ≠ second) {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum D {first, second} value) (probe : Fin dim → ℝ) :
    value * (probe ⬝ᵥ probe)
      ≤ (D.atom first ⬝ᵥ probe) ^ 2 + (D.atom second ⬝ᵥ probe) ^ 2 := by
  have hform := isBelowSubsetSpectrum_form_le D hbelow probe
  rwa [Finset.sum_insert (by simpa using hne), Finset.sum_singleton] at hform

/-- At `{0,1}` the probe `(1,4)` is ORTHOGONAL to the first atom and sees only the
second: total squared projection `16` against `|x|² = 17`, so every below-spectrum value
is at most `16/17`.  The true least eigenvalue is `9 − √65 = 0.93774 …`. -/
theorem volumeAverageKillDesign_isBelowSubsetSpectrum_zeroOne_le {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum volumeAverageKillDesign {0, 1} value) :
    value ≤ 16/17 := by
  have hform := isBelowSubsetSpectrum_pair_form_le volumeAverageKillDesign
    (show (0 : Fin 3) ≠ 1 by decide) hbelow ![1, 4]
  simp only [volumeAverageKillDesign, volumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hform
  linarith

/-- At `{0,2}` the probe `(1,5)` gives `1 + 36 = 37` against `|x|² = 26`, so every
below-spectrum value is at most `37/26`.  The true least eigenvalue is
`(19 − √261)/2 = 1.42225 …`; this is the one subset whose eigenvalue exceeds one, and
the bound is deliberately loose there because it is the two failing subsets that carry
the mass. -/
theorem volumeAverageKillDesign_isBelowSubsetSpectrum_zeroTwo_le {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum volumeAverageKillDesign {0, 2} value) :
    value ≤ 37/26 := by
  have hform := isBelowSubsetSpectrum_pair_form_le volumeAverageKillDesign
    (show (0 : Fin 3) ≠ 2 by decide) hbelow ![1, 5]
  simp only [volumeAverageKillDesign, volumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hform
  linarith

/-- At `{1,2}` the probe `(5,−3)` gives `9 + 4 = 13` against `|x|² = 34`, so every
below-spectrum value is at most `13/34`.  The true least eigenvalue is
`(3 − √5)/2 = 0.38197 …`. -/
theorem volumeAverageKillDesign_isBelowSubsetSpectrum_oneTwo_le {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum volumeAverageKillDesign {1, 2} value) :
    value ≤ 13/34 := by
  have hform := isBelowSubsetSpectrum_pair_form_le volumeAverageKillDesign
    (show (1 : Fin 3) ≠ 2 by decide) hbelow ![5, -3]
  simp only [volumeAverageKillDesign, volumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hform
  linarith

/-! ### The average, and the refutation -/

/-- The three `2`-subsets of `Fin 3` are the whole family, so the volume-sampling
average at rank two and size three is a three-term sum. -/
theorem volumeSamplingAverage_atSizeThreeRankTwo (D : WeightedDesign 3 2)
    (leastValue : Finset (Fin 3) → ℝ) :
    volumeSamplingAverage D leastValue
      = shadowDeterminant D {0, 1} * leastValue {0, 1}
        + shadowDeterminant D {0, 2} * leastValue {0, 2}
        + shadowDeterminant D {1, 2} * leastValue {1, 2} := by
  rw [volumeSamplingAverage,
    show (Finset.univ : Finset (Fin 3)).powersetCard 2 = {{0, 1}, {0, 2}, {1, 2}} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    add_assoc]

/-- **THE CERTIFICATE.**  Every assignment lying below all three spectra has
volume-sampling average at most `2161/2210 = 0.977828 …`, from
`(3/5)(16/17) + (1/4)(37/26) + (3/20)(13/34)`.  The true π-average of the least
eigenvalues is `0.975503 …`, so the certificate is loose by `0.0023` and still clears
the threshold by `49/2210`. -/
theorem volumeAverageKillDesign_volumeSamplingAverage_le
    (leastValue : Finset (Fin 3) → ℝ)
    (hbelow : ∀ selected ∈ (Finset.univ : Finset (Fin 3)).powersetCard 2,
      IsBelowSubsetSpectrum volumeAverageKillDesign selected (leastValue selected)) :
    volumeSamplingAverage volumeAverageKillDesign leastValue ≤ 2161/2210 := by
  have hzeroOne := volumeAverageKillDesign_isBelowSubsetSpectrum_zeroOne_le
    (hbelow {0, 1} (by decide))
  have hzeroTwo := volumeAverageKillDesign_isBelowSubsetSpectrum_zeroTwo_le
    (hbelow {0, 2} (by decide))
  have honeTwo := volumeAverageKillDesign_isBelowSubsetSpectrum_oneTwo_le
    (hbelow {1, 2} (by decide))
  rw [volumeSamplingAverage_atSizeThreeRankTwo,
    volumeAverageKillDesign_shadowDeterminant_zeroOne,
    volumeAverageKillDesign_shadowDeterminant_zeroTwo,
    volumeAverageKillDesign_shadowDeterminant_oneTwo]
  linarith

/-- **The witness fails the law.** -/
theorem volumeAverageKillDesign_not_hasDominatingVolumeSamplingAverage :
    ¬ HasDominatingVolumeSamplingAverage volumeAverageKillDesign := by
  rintro ⟨leastValue, hbelow, haverage⟩
  have hbound := volumeAverageKillDesign_volumeSamplingAverage_le leastValue hbelow
  linarith

/-- **A `2`-subset does dominate**, so the witness refutes the LAW and not
`GtzWeighted`.  The gap form of `{0,2}` is `(16x₀ − 3x₁)²/16 + (7/16)x₁²`, a manifest
sum of squares; the gap determinant is `7`. -/
theorem volumeAverageKillDesign_dominates_zeroTwo :
    Dominates volumeAverageKillDesign {0, 2} := by
  refine dominates_pair_of_coercive volumeAverageKillDesign
    (show (0 : Fin 3) ≠ 2 by decide) fun testVec => ?_
  simp only [volumeAverageKillDesign, volumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [sq_nonneg (16 * testVec 0 - 3 * testVec 1), sq_nonneg (testVec 1),
    sq_nonneg (testVec 0)]

/-- **THE VOLUME-AVERAGE LAW IS FALSE.**  There is a real weighted `(3,2)` design at
which no below-spectrum assignment averages to one under volume sampling — equivalently
`E_π[λ_min(S_C)] < 1`.  The cell is corank one and rank two, where `Gtz.gtz_rank_two`
proves `GtzWeightedAll 2`, so nothing here bears on `(6,3)` or `(7,3)`; what fails is
the averaging law alone. -/
theorem not_forall_hasDominatingVolumeSamplingAverage :
    ¬ ∀ D : WeightedDesign 3 2, HasDominatingVolumeSamplingAverage D := by
  intro hlaw
  exact volumeAverageKillDesign_not_hasDominatingVolumeSamplingAverage
    (hlaw volumeAverageKillDesign)

/-- **The refutation with the dominating subset exhibited**, so that the statement
carries its own proof that `GtzWeighted` is untouched: the design fails the law and
still has a dominating `2`-subset. -/
theorem exists_design_failing_volumeSamplingAverage_law_with_dominator :
    ∃ (D : WeightedDesign 3 2) (dominator : Finset (Fin 3)),
      ¬ HasDominatingVolumeSamplingAverage D
      ∧ dominator.card = 2 ∧ Dominates D dominator :=
  ⟨volumeAverageKillDesign, {0, 2},
    volumeAverageKillDesign_not_hasDominatingVolumeSamplingAverage,
    by decide, volumeAverageKillDesign_dominates_zeroTwo⟩

/-! ### The matrix average at the same design clears the threshold

`Gtz.posSemidef_leverageWeightedAtomSum_sub_one` proves `E_π[S_C] ⪰ 1` for every
design; here the same fact is verified at the witness directly from the three masses,
with no marginal identity and no hypothesis, so the separation between the two averages
is exhibited on one design rather than argued. -/

/-- The volume-sampling expectation of the atom sum at the witness is the integer matrix
`!![14, −3; −3, 2]`.  Its least eigenvalue is `8 − 3√5 = 1.29180 …`, comfortably above
one, while the AVERAGE of the three least eigenvalues is `0.97550 …`. -/
theorem volumeAverageKillDesign_expectedSubsetSum_eq :
    expectedSubsetSum volumeAverageKillDesign = !![14, -3; -3, 2] := by
  rw [expectedSubsetSum,
    show (Finset.univ : Finset (Fin 3)).powersetCard 2 = {{0, 1}, {0, 2}, {1, 2}} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    volumeAverageKillDesign_shadowDeterminant_zeroOne,
    volumeAverageKillDesign_shadowDeterminant_zeroTwo,
    volumeAverageKillDesign_shadowDeterminant_oneTwo,
    subsetSum_pair volumeAverageKillDesign (show (0 : Fin 3) ≠ 1 by decide),
    subsetSum_pair volumeAverageKillDesign (show (0 : Fin 3) ≠ 2 by decide),
    subsetSum_pair volumeAverageKillDesign (show (1 : Fin 3) ≠ 2 by decide)]
  ext rowIndex colIndex
  simp only [Matrix.add_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul, volumeAverageKillDesign, volumeAverageKillAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  fin_cases rowIndex <;> fin_cases colIndex <;> norm_num

/-- **The matrix average clears the threshold at the witness, unconditionally.**
`E_π[S_C] − I = !![13, −3; −3, 1]`, whose form is `(13x₀ − 3x₁)²/13 + (4/13)x₁²`.  So at
one design the matrix average is above the identity and the eigenvalue average is below
it: the two are genuinely different functionals, and the law confused them. -/
theorem volumeAverageKillDesign_posSemidef_expectedSubsetSum_sub_one :
    (expectedSubsetSum volumeAverageKillDesign
      - (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
  have hgap : expectedSubsetSum volumeAverageKillDesign - (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = !![13, -3; -3, 1] := by
    rw [volumeAverageKillDesign_expectedSubsetSum_eq]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      norm_num [Matrix.sub_apply, Matrix.one_apply]
  rw [hgap]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_, ?_⟩
  · ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num
  · intro probe
    have hform : star probe ⬝ᵥ ((!![13, -3; -3, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ probe)
        = 13 * probe 0 ^ 2 - 6 * probe 0 * probe 1 + probe 1 ^ 2 := by
      rw [star_trivial, dotProduct, Fin.sum_univ_two]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      norm_num
      ring
    rw [hform]
    nlinarith [sq_nonneg (13 * probe 0 - 3 * probe 1), sq_nonneg (probe 1)]

/-! ## The second witness: every leverage strictly above one

The witness above has an atom of leverage exactly one, so it does not certify that the
law fails on the ALL-HEAVY stratum — the stratum on which the campaign's reductions
operate, and the one a reader would ask about next.  This second `(3,2)` design closes
that: leverages `36/25`, `34/25`, `306/25`, all strictly above one, weights
`(4/9, 1/2, 1/18)`, and a margin THREE TIMES larger than the first witness's.

    π = (8/25, 8/25, 9/25)      E_π[λ_min(S_C)]  =  0.916134 …

with the certificate `127994/138125 = 0.926653 …` from the three integer probes
`(2,1)`, `(2,−3)`, `(3,−5)`.  The true least eigenvalues are `(7 − √13)/5`,
`1.024022 …` and `1.031118 …`; again none of them is computed. -/

/-- The three atoms of the all-heavy witness: `(0, 6/5)`, `(1, −3/5)`, `(3, 9/5)`. -/
noncomputable def heavyVolumeAverageKillAtom : Fin 3 → Fin 2 → ℝ :=
  ![![0, 6/5], ![1, -(3/5)], ![3, 9/5]]

/-- The all-heavy exactly rational `(3,2)` design at which the volume-average law
fails. -/
noncomputable def heavyVolumeAverageKillDesign : WeightedDesign 3 2 where
  atom := heavyVolumeAverageKillAtom
  weight := ![4/9, 1/2, 1/18]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_three, smul_eq_mul, heavyVolumeAverageKillAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- **Every leverage strictly exceeds one** — `36/25`, `34/25`, `306/25` — so this
witness lies in the all-heavy stratum. -/
theorem heavyVolumeAverageKillDesign_allHeavy : AllHeavy heavyVolumeAverageKillDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, leverageOf,
      Fin.sum_univ_two]

/-- `π({0,1}) = (4/9)(1/2)·(−6/5)² = 8/25`. -/
theorem heavyVolumeAverageKillDesign_shadowDeterminant_zeroOne :
    shadowDeterminant heavyVolumeAverageKillDesign {0, 1} = 8/25 := by
  rw [← weightScaledVolumeScore_eq_shadowDeterminant_ofCard heavyVolumeAverageKillDesign
      (show ({0, 1} : Finset (Fin 3)).card = 2 by decide),
    weightScaledVolumeScore_pair heavyVolumeAverageKillDesign
      (show (0 : Fin 3) ≠ 1 by decide)]
  simp only [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- `π({0,2}) = (4/9)(1/18)·(−18/5)² = 8/25`. -/
theorem heavyVolumeAverageKillDesign_shadowDeterminant_zeroTwo :
    shadowDeterminant heavyVolumeAverageKillDesign {0, 2} = 8/25 := by
  rw [← weightScaledVolumeScore_eq_shadowDeterminant_ofCard heavyVolumeAverageKillDesign
      (show ({0, 2} : Finset (Fin 3)).card = 2 by decide),
    weightScaledVolumeScore_pair heavyVolumeAverageKillDesign
      (show (0 : Fin 3) ≠ 2 by decide)]
  simp only [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- `π({1,2}) = (1/2)(1/18)·(18/5)² = 9/25`. -/
theorem heavyVolumeAverageKillDesign_shadowDeterminant_oneTwo :
    shadowDeterminant heavyVolumeAverageKillDesign {1, 2} = 9/25 := by
  rw [← weightScaledVolumeScore_eq_shadowDeterminant_ofCard heavyVolumeAverageKillDesign
      (show ({1, 2} : Finset (Fin 3)).card = 2 by decide),
    weightScaledVolumeScore_pair heavyVolumeAverageKillDesign
      (show (1 : Fin 3) ≠ 2 by decide)]
  simp only [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  norm_num

/-- At `{0,1}` the probe `(2,1)` gives `36/25 + 49/25` against `|x|² = 5`, so every
below-spectrum value is at most `17/25`.  The true least eigenvalue is
`(7 − √13)/5 = 0.678890 …`. -/
theorem heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_zeroOne_le {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum heavyVolumeAverageKillDesign {0, 1} value) :
    value ≤ 17/25 := by
  have hform := isBelowSubsetSpectrum_pair_form_le heavyVolumeAverageKillDesign
    (show (0 : Fin 3) ≠ 1 by decide) hbelow ![2, 1]
  simp only [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hform
  linarith

/-- At `{0,2}` the probe `(2,−3)` gives `324/25 + 9/25` against `|x|² = 13`, so every
below-spectrum value is at most `333/325`.  The true least eigenvalue is
`1.024022 …`, so this bound is tight to five decimals. -/
theorem heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_zeroTwo_le {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum heavyVolumeAverageKillDesign {0, 2} value) :
    value ≤ 333/325 := by
  have hform := isBelowSubsetSpectrum_pair_form_le heavyVolumeAverageKillDesign
    (show (0 : Fin 3) ≠ 2 by decide) hbelow ![2, -3]
  simp only [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hform
  linarith

/-- At `{1,2}` the probe `(3,−5)` is ORTHOGONAL to the third atom and sees only the
second: `36` against `|x|² = 34`, so every below-spectrum value is at most `18/17`.
The true least eigenvalue is `1.031118 …`. -/
theorem heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_oneTwo_le {value : ℝ}
    (hbelow : IsBelowSubsetSpectrum heavyVolumeAverageKillDesign {1, 2} value) :
    value ≤ 18/17 := by
  have hform := isBelowSubsetSpectrum_pair_form_le heavyVolumeAverageKillDesign
    (show (1 : Fin 3) ≠ 2 by decide) hbelow ![3, -5]
  simp only [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hform
  linarith

/-- **THE ALL-HEAVY CERTIFICATE.**  Every below-spectrum assignment averages at most
`(8/25)(17/25) + (8/25)(333/325) + (9/25)(18/17) = 127994/138125 = 0.926653 …`, stated
here at the round `24/25` it clears.  The true π-average is `0.916134 …`. -/
theorem heavyVolumeAverageKillDesign_volumeSamplingAverage_le
    (leastValue : Finset (Fin 3) → ℝ)
    (hbelow : ∀ selected ∈ (Finset.univ : Finset (Fin 3)).powersetCard 2,
      IsBelowSubsetSpectrum heavyVolumeAverageKillDesign selected (leastValue selected)) :
    volumeSamplingAverage heavyVolumeAverageKillDesign leastValue ≤ 24/25 := by
  have hzeroOne := heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_zeroOne_le
    (hbelow {0, 1} (by decide))
  have hzeroTwo := heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_zeroTwo_le
    (hbelow {0, 2} (by decide))
  have honeTwo := heavyVolumeAverageKillDesign_isBelowSubsetSpectrum_oneTwo_le
    (hbelow {1, 2} (by decide))
  rw [volumeSamplingAverage_atSizeThreeRankTwo,
    heavyVolumeAverageKillDesign_shadowDeterminant_zeroOne,
    heavyVolumeAverageKillDesign_shadowDeterminant_zeroTwo,
    heavyVolumeAverageKillDesign_shadowDeterminant_oneTwo]
  linarith

/-- **The all-heavy witness fails the law.** -/
theorem heavyVolumeAverageKillDesign_not_hasDominatingVolumeSamplingAverage :
    ¬ HasDominatingVolumeSamplingAverage heavyVolumeAverageKillDesign := by
  rintro ⟨leastValue, hbelow, haverage⟩
  have hbound := heavyVolumeAverageKillDesign_volumeSamplingAverage_le leastValue hbelow
  linarith

/-- **A `2`-subset dominates at the all-heavy witness too.**  The gap form of `{1,2}` is
`(45x₀ + 24x₁)²/225 + (1/25)x₁²`; the gap determinant is `9/25`, so `{1,2}` dominates
strictly but barely — its least eigenvalue is `1.031118 …`. -/
theorem heavyVolumeAverageKillDesign_dominates_oneTwo :
    Dominates heavyVolumeAverageKillDesign {1, 2} := by
  refine dominates_pair_of_coercive heavyVolumeAverageKillDesign
    (show (1 : Fin 3) ≠ 2 by decide) fun testVec => ?_
  simp only [heavyVolumeAverageKillDesign, heavyVolumeAverageKillAtom, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith [sq_nonneg (45 * testVec 0 + 24 * testVec 1), sq_nonneg (testVec 1),
    sq_nonneg (testVec 0)]

/-- **THE LAW FAILS ON THE ALL-HEAVY STRATUM.**  There is a real weighted `(3,2)` design
with every leverage strictly above one at which no below-spectrum assignment averages to
one under volume sampling — and it still has a dominating `2`-subset, so `GtzWeighted`
is untouched.  Together with `not_forall_hasDominatingVolumeSamplingAverage` this closes
the obvious retreat: the failure is not an artefact of a light atom. -/
theorem exists_allHeavy_design_failing_volumeSamplingAverage_law :
    ∃ (D : WeightedDesign 3 2) (dominator : Finset (Fin 3)),
      AllHeavy D
      ∧ ¬ HasDominatingVolumeSamplingAverage D
      ∧ dominator.card = 2 ∧ Dominates D dominator :=
  ⟨heavyVolumeAverageKillDesign, {1, 2}, heavyVolumeAverageKillDesign_allHeavy,
    heavyVolumeAverageKillDesign_not_hasDominatingVolumeSamplingAverage,
    by decide, heavyVolumeAverageKillDesign_dominates_oneTwo⟩

/-! ## The elementary-symmetric identity

`Gtz.sum_shadowDeterminant_eq_one` says the masses sum to one and
`Gtz.shadowDeterminant_eq_weightProduct_mul_detSubsetSum` evaluates each mass as
`(∏_{c ∈ C} t_c)·det S_C`.  Together they force one subset determinant above
`1/e_k(t)`.  Nothing here depends on the law or on its refutation. -/

/-- **The elementary symmetric polynomial of the weights**,
`e_level(t) = ∑_{|C| = level} ∏_{c ∈ C} t_c`.  At `level = rank` this is the exact
normaliser of the volume-sampling masses' determinant factorisation. -/
noncomputable def weightElementary (D : WeightedDesign m k) (level : ℕ) : ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard level,
    ∏ atomIndex ∈ selected, D.weight atomIndex

/-- Every weight product over a subset is positive.  Named for the subset because
`Gtz.weightProduct_pos` is already taken, by the three-atom product of
`Gtz.Quantitative.ProjectionChartLegs`. -/
theorem subsetWeightProduct_pos (D : WeightedDesign m k) (selected : Finset (Fin m)) :
    0 < ∏ atomIndex ∈ selected, D.weight atomIndex :=
  Finset.prod_pos fun atomIndex _ => D.weight_pos atomIndex

/-- `e_rank(t) > 0`: the family of `rank`-subsets is nonempty because the rank is at
most the size, and every term is a positive product. -/
theorem weightElementary_pos (D : WeightedDesign m k) : 0 < weightElementary D k := by
  refine Finset.sum_pos (fun selected _ => subsetWeightProduct_pos D selected) ?_
  exact Finset.powersetCard_nonempty.mpr (by simpa using rank_le_of_design D)

/-- **THE ELEMENTARY-SYMMETRIC BOUND.**  Some `rank`-subset has
`det S_C ≥ 1 / e_rank(t)`.  Three steps and no inequality beyond "a term is at most the
maximum": the masses sum to one, each mass is `(∏_{c ∈ C} t_c)·det S_C`, and bounding
every determinant by the largest gives `1 ≤ (max_C det S_C)·e_rank(t)`.  Weight-explicit
and uniform in size and rank; it supersedes what
`Gtz.exists_shadowDeterminant_ge_inv_binomial` yields, which after AM–GM on the weight
product gives only `rank^rank / C(size,rank)` — strictly, whenever the rank is below the
size, since `1/e_rank(t) ≥ size^rank/C(size,rank)`.

This bounds a DETERMINANT, hence bounds `λ_min` from ABOVE, never below; it is not a
step toward GTZ and is not offered as one. -/
theorem exists_detSubsetSum_ge_inv_weightElementary (D : WeightedDesign m k) :
    ∃ selected : Finset (Fin m), selected.card = k ∧
      (weightElementary D k)⁻¹ ≤ (subsetSum D selected).det := by
  have hfamilyNonempty : ((Finset.univ : Finset (Fin m)).powersetCard k).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simpa using rank_le_of_design D)
  obtain ⟨best, hbestMem, hbestMax⟩ :=
    Finset.exists_max_image ((Finset.univ : Finset (Fin m)).powersetCard k)
      (fun selected => (subsetSum D selected).det) hfamilyNonempty
  refine ⟨best, (Finset.mem_powersetCard.mp hbestMem).2, ?_⟩
  have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
      shadowDeterminant D selected
        ≤ (∏ atomIndex ∈ selected, D.weight atomIndex) * (subsetSum D best).det := by
    intro selected hmem
    rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum D
      (Finset.mem_powersetCard.mp hmem).2]
    exact mul_le_mul_of_nonneg_left (hbestMax selected hmem) (subsetWeightProduct_pos D selected).le
  have hsummed := Finset.sum_le_sum hterm
  rw [sum_shadowDeterminant_eq_one D, ← Finset.sum_mul, ← weightElementary] at hsummed
  rw [inv_le_iff_one_le_mul₀ (weightElementary_pos D)]
  linarith

/-- At uniform weights `e_level(t) = C(size, level)·t^level` — an exact evaluation, not
an inequality.  So the uniform case of the bound needs no Maclaurin argument. -/
theorem weightElementary_of_uniformWeight (D : WeightedDesign m k) (level : ℕ)
    {uniform : ℝ} (huniform : ∀ atomIndex : Fin m, D.weight atomIndex = uniform) :
    weightElementary D level = (m.choose level : ℝ) * uniform ^ level := by
  have hterm : ∀ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard level,
      ∏ atomIndex ∈ selected, D.weight atomIndex = uniform ^ level := by
    intro selected hmem
    rw [Finset.prod_congr rfl fun atomIndex _ => huniform atomIndex, Finset.prod_const,
      (Finset.mem_powersetCard.mp hmem).2]
  rw [weightElementary, Finset.sum_congr rfl hterm, Finset.sum_const,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The uniform-weight bound**: at `t ≡ 1/size` some `rank`-subset has
`det S_C ≥ size^rank / C(size, rank)`.  At `(4,3)` that is `64/4 = 16`, which the
tetrahedron attains exactly; at `(6,3)` it is `54/5` and at `(7,3)` it is `49/5`. -/
theorem exists_detSubsetSum_ge_pow_div_choose (D : WeightedDesign m k)
    (huniform : ∀ atomIndex : Fin m, D.weight atomIndex = (m : ℝ)⁻¹) :
    ∃ selected : Finset (Fin m), selected.card = k ∧
      (m : ℝ) ^ k / (m.choose k : ℝ) ≤ (subsetSum D selected).det := by
  obtain ⟨best, hcard, hbound⟩ := exists_detSubsetSum_ge_inv_weightElementary D
  refine ⟨best, hcard, le_trans (le_of_eq ?_) hbound⟩
  have hsizePos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast pos_of_weightedDesign D
  have hchoosePos : (0 : ℝ) < (m.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (rank_le_of_design D)
  rw [weightElementary_of_uniformWeight D k huniform, inv_pow, mul_inv, inv_inv,
    div_eq_mul_inv, mul_comm]

/-! ### The degenerate case, stated so it cannot be misread

The natural-looking identity `E_π[1/det S_C] = e_rank(t)` is FALSE the moment one
`rank`-subset is dependent: that subset carries mass zero, so it drops out of the
average while remaining in `e_rank(t)`.  In Lean the division form is worse than false —
`x/0 = 0` makes it PROVABLE, for the restricted sum, while reading as the false claim.
The restriction is therefore named in the statement. -/

/-- **The identity, restricted to the independent subsets.**  Each independent subset
contributes exactly its weight product; each dependent subset contributes zero, since
its mass and its determinant both vanish and `x/0 = 0`. -/
theorem sum_shadowDeterminant_div_detSubsetSum_eq_independentWeightProduct
    (D : WeightedDesign m k) :
    ∑ selected ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        shadowDeterminant D selected / (subsetSum D selected).det
      = ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).filter
          (fun selected => (subsetSum D selected).det ≠ 0),
          ∏ atomIndex ∈ selected, D.weight atomIndex := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin m)).powersetCard k)
    (fun selected => (subsetSum D selected).det ≠ 0)]
  have hindependent : ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).filter
        (fun selected => (subsetSum D selected).det ≠ 0),
        shadowDeterminant D selected / (subsetSum D selected).det
      = ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).filter
          (fun selected => (subsetSum D selected).det ≠ 0),
          ∏ atomIndex ∈ selected, D.weight atomIndex := by
    refine Finset.sum_congr rfl fun selected hmem => ?_
    obtain ⟨hfamily, hnonzero⟩ := Finset.mem_filter.mp hmem
    rw [shadowDeterminant_eq_weightProduct_mul_detSubsetSum D
      (Finset.mem_powersetCard.mp hfamily).2, mul_div_assoc, div_self hnonzero, mul_one]
  have hdependent : ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).filter
        (fun selected => ¬ (subsetSum D selected).det ≠ 0),
        shadowDeterminant D selected / (subsetSum D selected).det = 0 := by
    refine Finset.sum_eq_zero fun selected hmem => ?_
    rw [not_not.mp (Finset.mem_filter.mp hmem).2, div_zero]
  rw [hindependent, hdependent, add_zero]

/-- The restricted sum is at most `e_rank(t)`: the independent subsets are a subfamily
and every weight product is positive. -/
theorem sum_independentWeightProduct_le_weightElementary (D : WeightedDesign m k) :
    ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).filter
        (fun selected => (subsetSum D selected).det ≠ 0),
        ∏ atomIndex ∈ selected, D.weight atomIndex
      ≤ weightElementary D k := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun selected _ _ => (subsetWeightProduct_pos D selected).le

/-- **The gap is strict exactly when a dependent subset exists.**  One dependent
`rank`-subset already separates the restricted sum from `e_rank(t)` by its own positive
weight product — the octahedron at `(6,3)` has twelve of its twenty triples dependent,
so the gap there is large, not marginal. -/
theorem sum_independentWeightProduct_lt_weightElementary_of_dependentSubset
    (D : WeightedDesign m k) {witness : Finset (Fin m)}
    (hmem : witness ∈ (Finset.univ : Finset (Fin m)).powersetCard k)
    (hdependent : (subsetSum D witness).det = 0) :
    ∑ selected ∈ ((Finset.univ : Finset (Fin m)).powersetCard k).filter
        (fun selected => (subsetSum D selected).det ≠ 0),
        ∏ atomIndex ∈ selected, D.weight atomIndex
      < weightElementary D k := by
  classical
  refine Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _) hmem ?_
    (subsetWeightProduct_pos D witness) fun selected _ _ => (subsetWeightProduct_pos D selected).le
  rw [Finset.mem_filter, not_and]
  exact fun _ => not_not.mpr hdependent

/-! ### Sharpness at the tetrahedron

The bound `det S_C ≥ 1/e_rank(t)` is attained at the regular tetrahedron: `e_3 = 1/16`
and EVERY triple has `det S_C = 16`, spectrum `(4,4,1)`.  So the uniform-weight form
`size^rank / C(size,rank) = 64/4 = 16` is an equality there too, at the design that is
the known extremal one. -/

/-- A three-element subset sum is the sum of its three atoms. -/
theorem subsetSum_triple (D : WeightedDesign m k) {first second third : Fin m}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    subsetSum D {first, second, third}
      = atomMatrix (D.atom first) + atomMatrix (D.atom second) + atomMatrix (D.atom third) := by
  rw [subsetSum, Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]

/-- **The four `3`-subsets of `Fin 4`**, enumerated by decision. -/
theorem finset_card_three_cases_atSizeFour (C : Finset (Fin 4)) (hcard : C.card = 3) :
    C = {0, 1, 2} ∨ C = {0, 1, 3} ∨ C = {0, 2, 3} ∨ C = {1, 2, 3} := by
  revert hcard
  revert C
  decide

/-- **Every tetrahedron triple has determinant `16`.**  Each atom sum is
`4I − g_dg_dᵀ` for the omitted vertex `d`, with spectrum `(4,4,1)`; computed here at all
four triples rather than argued. -/
theorem tetraDesign_detSubsetSum_eq (C : Finset (Fin 4)) (hcard : C.card = 3) :
    (subsetSum tetraDesign C).det = 16 := by
  have hentry : ∀ first second third : Fin 4, first ≠ second → first ≠ third → second ≠ third →
      (subsetSum tetraDesign {first, second, third}).det
        = (atomMatrix (tetraAtom first) + atomMatrix (tetraAtom second)
            + atomMatrix (tetraAtom third)).det := by
    intro first second third hfirstSecond hfirstThird hsecondThird
    rw [subsetSum_triple tetraDesign hfirstSecond hfirstThird hsecondThird]
    rfl
  rcases finset_card_three_cases_atSizeFour C hcard with rfl | rfl | rfl | rfl <;>
    [ rw [hentry 0 1 2 (by decide) (by decide) (by decide)];
      rw [hentry 0 1 3 (by decide) (by decide) (by decide)];
      rw [hentry 0 2 3 (by decide) (by decide) (by decide)];
      rw [hentry 1 2 3 (by decide) (by decide) (by decide)] ] <;>
  · rw [Matrix.det_fin_three]
    simp only [Matrix.add_apply, atomMatrix, Matrix.vecMulVec_apply, tetraAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons]
    norm_num

/-- The tetrahedron's third elementary symmetric weight polynomial is `1/16`, so the
bound reads `det S_C ≥ 16` — attained at every triple. -/
theorem tetraDesign_weightElementary_three : weightElementary tetraDesign 3 = 1/16 := by
  rw [weightElementary_of_uniformWeight tetraDesign 3 (uniform := (1 : ℝ)/4) (fun _ => rfl)]
  norm_num

/-- **THE BOUND IS SHARP.**  At the tetrahedron `1/e_3(t) = 16` and every triple has
`det S_C = 16`, so `exists_detSubsetSum_ge_inv_weightElementary` is an equality at the
known extremal design — and so is its uniform-weight form `4³/C(4,3) = 16`. -/
theorem tetraDesign_detSubsetSum_eq_inv_weightElementary (C : Finset (Fin 4))
    (hcard : C.card = 3) :
    (subsetSum tetraDesign C).det = (weightElementary tetraDesign 3)⁻¹ := by
  rw [tetraDesign_detSubsetSum_eq C hcard, tetraDesign_weightElementary_three]
  norm_num

end Gtz
