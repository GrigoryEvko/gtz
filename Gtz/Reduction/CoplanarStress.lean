/-
# Branch (iii) of the (6,3) stress trichotomy: the coplanar-support stratum

A `(6,3)` design in stratum (iii) carries a nonzero stress whose supported
atoms all annihilate a common nonzero probe.  This file pins the stratum's
geometry for PRIMITIVE designs and reduces its domination question to a
purely planar target inequality:

* `hasParallelAtomPair_of_supportSpan_le_one` — a stress whose supported
  atoms span at most a line forces a parallel pair, with NO uniqueness
  hypothesis on the stress space (the taxonomy's sibling lemma needs one);
* `sixThree_primitiveCoplanar_structure` — for a primitive design the
  coplanar stress has support span EXACTLY two, support size four or five,
  and one or two off-plane atoms;
* `dominates_insert_carrier_iff_planarTarget` — at EVERY size and rank:
  a subset consisting of planar atoms plus one steep carrier dominates
  IFF the planar atoms beat an explicit in-plane target, the carrier's
  normal-direction surplus paying for its in-plane tilt through one
  completing-the-square identity.  No Schur complement, no adapted basis,
  no matrix square root — the whole reduction is dot-product arithmetic;
* `one_lt_probePairing_sq_of_unique_carrier` — when the carrier is the ONLY
  off-plane atom, its steepness is automatic from Parseval:
  `t_b * alpha^2 = 1` with `t_b < 1`;
* `dominates_of_singleCarrier_of_planarPair` — the conditional kill: a
  single-carrier stratum-(iii) design with a planar pair meeting the target
  has a dominating triple.

At `(6,3)` the last two bullets are superseded and kept only because they hold
at every size and rank: a sole off-plane atom is forced PARALLEL to the probe
(`soleOffPlane_normal_eq_smul_pole`), so the tilt `h` vanishes and the target
is the plain in-plane identity, and the single-carrier verdict is already
strict in-tree (`exists_posDef_of_soleOffPlane`, `not_isTie_of_soleOffPlane`).
The stratum's residual is the TWO-off-plane-pole substratum — see
`Gtz/Design/TwoPoleStratum.lean` and its `SixThreeTwoPoleSelection`.
-/
import Mathlib
import Gtz.Reduction.StressSupportTaxonomy
import Gtz.Reduction.HingeFunnel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {n k : ℕ}

/-! ## Part 1: the scalar core of the carrier reduction -/

/-- **The tilted-witness harvest.**  If the tilted test vector's moment
inequality holds — the instance of domination at
`(alpha^2 - 1) • w - (alpha * beta) • probe` — then the planar gap beats the
carrier's in-plane pairing.  Division-free: the steepness factor is peeled
off by `le_of_mul_le_mul_left`. -/
theorem scaledGap_bound_of_tiltedMoment {alpha beta planarMoment planarNormSq : ℝ}
    (hsteep : 1 < alpha ^ 2)
    (htilted : (alpha ^ 2 - 1) ^ 2 * planarNormSq + alpha ^ 2 * beta ^ 2
      ≤ beta ^ 2 + (alpha ^ 2 - 1) ^ 2 * planarMoment) :
    beta ^ 2 ≤ (alpha ^ 2 - 1) * (planarMoment - planarNormSq) := by
  have hpos : 0 < alpha ^ 2 - 1 := by linarith
  have hkey : (alpha ^ 2 - 1) * beta ^ 2
      ≤ (alpha ^ 2 - 1) * ((alpha ^ 2 - 1) * (planarMoment - planarNormSq)) := by
    nlinarith [htilted]
  exact le_of_mul_le_mul_left hkey hpos

/-- **The completing-the-square payoff.**  Given the planar gap bound, every
decomposed test vector satisfies the moment inequality: multiplying through
by the steepness factor turns the deficit into the perfect square
`((alpha^2 - 1) * xi + alpha * beta)^2`. -/
theorem momentFloor_of_scaledGap {alpha beta xi planarMoment planarNormSq : ℝ}
    (hsteep : 1 < alpha ^ 2)
    (hgap : beta ^ 2 ≤ (alpha ^ 2 - 1) * (planarMoment - planarNormSq)) :
    planarNormSq + xi ^ 2 ≤ (beta + xi * alpha) ^ 2 + planarMoment := by
  have hpos : 0 < alpha ^ 2 - 1 := by linarith
  have hmul : 0 ≤ (alpha ^ 2 - 1)
      * ((beta + xi * alpha) ^ 2 + planarMoment - planarNormSq - xi ^ 2) := by
    nlinarith [hgap, sq_nonneg ((alpha ^ 2 - 1) * xi + alpha * beta)]
  nlinarith [hmul, hpos]

/-! ## Part 2: the carrier reduction, at every size and rank -/

/-- **Domination through one steep carrier is a PLANAR question.**  Fix a unit
probe, a set of atoms orthogonal to it, and one carrier atom whose pairing
with the probe exceeds one in square.  The enlarged subset dominates IFF for
every in-plane direction the planar atoms' moment exceeds the plain identity
target PLUS the carrier's in-plane tilt, scaled by the inverse surplus.

Both directions are elementary: forward evaluates domination at the tilted
witness `(alpha^2 - 1) • w - (alpha * beta) • probe`; backward decomposes an
arbitrary test vector along the probe and completes the square.  This is the
Schur-complement reduction of the coplanar stratum with the Schur machinery
dissolved into two scalar inequalities. -/
theorem dominates_insert_carrier_iff_planarTarget {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (carrierLabel : Fin size) (probe : Fin rank → ℝ)
    (hunit : probe ⬝ᵥ probe = 1)
    (hcarrierFree : carrierLabel ∉ selected)
    (hplanarSelected : ∀ c ∈ selected, design.atom c ⬝ᵥ probe = 0)
    (hsteep : 1 < (design.atom carrierLabel ⬝ᵥ probe) ^ 2) :
    Dominates design (insert carrierLabel selected)
      ↔ ∀ inPlaneVec : Fin rank → ℝ, inPlaneVec ⬝ᵥ probe = 0 →
          (design.atom carrierLabel ⬝ᵥ inPlaneVec) ^ 2
            ≤ ((design.atom carrierLabel ⬝ᵥ probe) ^ 2 - 1)
              * (∑ c ∈ selected, (design.atom c ⬝ᵥ inPlaneVec) ^ 2
                  - inPlaneVec ⬝ᵥ inPlaneVec) := by
  classical
  rw [dominates_iff_forall_moment_ge]
  constructor
  · -- forward: harvest the tilted witness
    intro hmoment inPlaneVec hplanarVec
    set alpha := design.atom carrierLabel ⬝ᵥ probe with halphaDef
    set beta := design.atom carrierLabel ⬝ᵥ inPlaneVec with hbetaDef
    have hplanarVec' : probe ⬝ᵥ inPlaneVec = 0 := by
      rw [dotProduct_comm]; exact hplanarVec
    set tilted : Fin rank → ℝ :=
      (alpha ^ 2 - 1) • inPlaneVec - (alpha * beta) • probe with htiltedDef
    have hinstance := hmoment tilted
    -- the tilted vector's self-pairing
    have hself : tilted ⬝ᵥ tilted
        = (alpha ^ 2 - 1) ^ 2 * (inPlaneVec ⬝ᵥ inPlaneVec)
          + alpha ^ 2 * beta ^ 2 := by
      simp only [htiltedDef, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hunit, hplanarVec, hplanarVec']
      ring
    -- planar atoms see only the in-plane component, scaled
    have hselectedPairing : ∀ c ∈ selected,
        design.atom c ⬝ᵥ tilted = (alpha ^ 2 - 1) * (design.atom c ⬝ᵥ inPlaneVec) := by
      intro c hc
      simp only [htiltedDef, dotProduct_sub, dotProduct_smul, smul_eq_mul,
        hplanarSelected c hc]
      ring
    -- the carrier sees exactly minus its in-plane pairing
    have hcarrierPairing : design.atom carrierLabel ⬝ᵥ tilted = -beta := by
      simp only [htiltedDef, dotProduct_sub, dotProduct_smul, smul_eq_mul,
        ← halphaDef, ← hbetaDef]
      ring
    rw [Finset.sum_insert hcarrierFree] at hinstance
    simp only [momentCoord] at hinstance
    rw [hself, hcarrierPairing] at hinstance
    have hsum : ∑ c ∈ selected, (design.atom c ⬝ᵥ tilted) ^ 2
        = (alpha ^ 2 - 1) ^ 2 * ∑ c ∈ selected, (design.atom c ⬝ᵥ inPlaneVec) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c hc => by rw [hselectedPairing c hc]; ring
    rw [hsum] at hinstance
    refine scaledGap_bound_of_tiltedMoment hsteep ?_
    nlinarith [hinstance]
  · -- backward: decompose an arbitrary test vector along the probe
    intro htarget testVec
    set alpha := design.atom carrierLabel ⬝ᵥ probe with halphaDef
    set xi := testVec ⬝ᵥ probe with hxiDef
    set inPlaneVec : Fin rank → ℝ := testVec - xi • probe with hwDef
    have hplanarVec : inPlaneVec ⬝ᵥ probe = 0 := by
      simp only [hwDef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit,
        ← hxiDef]
      ring
    -- every pairing at the test vector, through the decomposition
    have hpairing : ∀ label : Fin size,
        design.atom label ⬝ᵥ inPlaneVec
          = design.atom label ⬝ᵥ testVec - xi * (design.atom label ⬝ᵥ probe) := by
      intro label
      simp only [hwDef, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hcommPairing : probe ⬝ᵥ testVec = xi := by
      rw [dotProduct_comm]
    have hselfSplit : inPlaneVec ⬝ᵥ inPlaneVec = testVec ⬝ᵥ testVec - xi ^ 2 := by
      simp only [hwDef, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hunit, ← hxiDef, hcommPairing]
      ring
    set beta := design.atom carrierLabel ⬝ᵥ inPlaneVec with hbetaDef
    have hgap := htarget inPlaneVec hplanarVec
    rw [Finset.sum_insert hcarrierFree]
    simp only [momentCoord]
    have hcarrierAtTest : design.atom carrierLabel ⬝ᵥ testVec = beta + xi * alpha := by
      rw [hbetaDef, hpairing carrierLabel, ← halphaDef]
      ring
    have hselectedAtTest : ∑ c ∈ selected, (design.atom c ⬝ᵥ testVec) ^ 2
        = ∑ c ∈ selected, (design.atom c ⬝ᵥ inPlaneVec) ^ 2 := by
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [hpairing c, hplanarSelected c hc]
      ring
    rw [hcarrierAtTest, hselectedAtTest]
    have hfloor := momentFloor_of_scaledGap (planarNormSq := inPlaneVec ⬝ᵥ inPlaneVec)
      (xi := xi) hsteep hgap
    rw [hselfSplit] at hfloor
    linarith

/-! ## Part 3: steepness is automatic for a unique carrier -/

/-- **Parseval at the probe collapses onto the unique carrier**: when every
other atom is in-plane, the carrier's weighted squared pairing is exactly the
probe's norm, i.e. one. -/
theorem probePairing_sq_mul_weight_eq_one_of_unique_carrier {size rank : ℕ}
    (design : WeightedDesign size rank) (probe : Fin rank → ℝ)
    (hunit : probe ⬝ᵥ probe = 1) (carrierLabel : Fin size)
    (huniqueCarrier : ∀ c, c ≠ carrierLabel → design.atom c ⬝ᵥ probe = 0) :
    design.weight carrierLabel * (design.atom carrierLabel ⬝ᵥ probe) ^ 2 = 1 := by
  have hform : probe ⬝ᵥ ((∑ c, design.weight c • atomMatrix (design.atom c)) *ᵥ probe)
      = ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2 :=
    weighted_atomForm_eq_on Finset.univ design.weight design.atom probe
  rw [design.isParseval, Matrix.one_mulVec, hunit] at hform
  have hcollapse : ∑ c, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      = design.weight carrierLabel * (design.atom carrierLabel ⬝ᵥ probe) ^ 2 := by
    refine Finset.sum_eq_single carrierLabel (fun c _ hc => ?_)
      (fun habsent => absurd (Finset.mem_univ carrierLabel) habsent)
    rw [huniqueCarrier c hc]
    ring
  rw [hcollapse] at hform
  exact hform.symm

/-- **The unique carrier is automatically steep**: its squared pairing with
the probe is `1 / t_b > 1`, because the other atoms carry positive weight. -/
theorem one_lt_probePairing_sq_of_unique_carrier {size rank : ℕ}
    (hsize : 1 < size) (design : WeightedDesign size rank) (probe : Fin rank → ℝ)
    (hunit : probe ⬝ᵥ probe = 1) (carrierLabel : Fin size)
    (huniqueCarrier : ∀ c, c ≠ carrierLabel → design.atom c ⬝ᵥ probe = 0) :
    1 < (design.atom carrierLabel ⬝ᵥ probe) ^ 2 := by
  have hproduct := probePairing_sq_mul_weight_eq_one_of_unique_carrier
    design probe hunit carrierLabel huniqueCarrier
  obtain ⟨otherLabel, hother⟩ :=
    Fintype.exists_ne_of_one_lt_card (by simpa using hsize) carrierLabel
  have hotherWeight : design.weight otherLabel ≤ ∑ c ∈ Finset.univ.erase carrierLabel,
      design.weight c :=
    Finset.single_le_sum (fun c _ => (design.weight_pos c).le)
      (Finset.mem_erase.mpr ⟨hother, Finset.mem_univ otherLabel⟩)
  have hsplit : design.weight carrierLabel
      + ∑ c ∈ Finset.univ.erase carrierLabel, design.weight c = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ carrierLabel)]
    exact design.weight_sum_one
  have hcarrierWeightSmall : design.weight carrierLabel < 1 := by
    have hotherPos := design.weight_pos otherLabel
    linarith
  nlinarith [design.weight_pos carrierLabel, hproduct, hcarrierWeightSmall]

/-! ## Part 4: low support rank forces a parallel pair — no uniqueness needed -/

/-- **A stress whose supported atoms span at most a line yields a parallel
pair.**  The taxonomy's `Gtz.hasParallelAtomPair_of_finrank_le_one` assumes
the stress space is a line; this version drops that hypothesis.  Rank zero
puts a zero atom at any supported label; rank one puts two supported atoms on
one generator, and the span-relative split law supplies the second label. -/
theorem hasParallelAtomPair_of_supportSpan_le_one (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ} (hstressNonzero : stressCoeff ≠ 0) (hsize : 1 < n)
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hrank : Module.finrank ℝ (supportSpan atomFamily stressCoeff) ≤ 1) :
    hasParallelAtomPair atomFamily := by
  have hcases : Module.finrank ℝ (supportSpan atomFamily stressCoeff) = 0
      ∨ Module.finrank ℝ (supportSpan atomFamily stressCoeff) = 1 := by omega
  rcases hcases with hzero | hone
  · obtain ⟨liveLabel, hlive⟩ := Function.ne_iff.mp hstressNonzero
    have hliveSupported : stressCoeff liveLabel ≠ 0 := by simpa using hlive
    have hbot : supportSpan atomFamily stressCoeff = ⊥ :=
      Submodule.finrank_eq_zero.mp hzero
    have hzeroAtom : atomFamily liveLabel = 0 := by
      have hmem := atom_mem_supportSpan atomFamily hliveSupported
      rw [hbot] at hmem
      simpa using hmem
    obtain ⟨otherLabel, hother⟩ :=
      Fintype.exists_ne_of_one_lt_card (by simpa using hsize) liveLabel
    exact ⟨otherLabel, liveLabel, 0, hother, by rw [hzeroAtom, zero_smul]⟩
  · obtain ⟨generator, hgenerator⟩ := exists_generator_of_finrank_eq_one hone
    have hlower := twice_finrank_supportSpan_le_card_stressSupport atomFamily hstress
    rw [hone] at hlower
    obtain ⟨firstLabel, hfirstMem, secondLabel, hsecondMem, hdistinct⟩ :=
      Finset.one_lt_card.mp (by omega : 1 < (stressSupport stressCoeff).card)
    obtain ⟨alpha, halpha⟩ := hgenerator (atomFamily firstLabel)
      (atom_mem_supportSpan atomFamily (mem_stressSupport_iff.mp hfirstMem))
    obtain ⟨beta, hbeta⟩ := hgenerator (atomFamily secondLabel)
      (atom_mem_supportSpan atomFamily (mem_stressSupport_iff.mp hsecondMem))
    by_cases halphaZero : alpha = 0
    · exact ⟨secondLabel, firstLabel, 0, hdistinct.symm, by
        rw [halpha, halphaZero, zero_smul, zero_smul]⟩
    · exact ⟨firstLabel, secondLabel, beta / alpha, hdistinct, by
        rw [hbeta, halpha, smul_smul, div_mul_cancel₀ _ halphaZero]⟩

/-! ## Part 5: the primitive coplanar structure at (6,3) -/

/-- **THE PRIMITIVE STRATUM-(iii) NORMAL FORM.**  A primitive `(6,3)` design
whose stress is coplanar has: support span of dimension EXACTLY two, support
size four or five, and one or two atoms off the plane.  Every other apparent
case — collinear or vanishing support, full coplanar support, an all-planar
design — collapses into a parallel pair or contradicts Parseval. -/
theorem sixThree_primitiveCoplanar_structure (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ} {probe : Fin 3 → ℝ}
    (hstressNonzero : stressCoeff ≠ 0) (hprobeNonzero : probe ≠ 0)
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hcoplanar : ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0)
    (hprimitive : ¬ HasParallelPair design) :
    Module.finrank ℝ (supportSpan design.atom stressCoeff) = 2
      ∧ 4 ≤ (stressSupport stressCoeff).card
      ∧ (stressSupport stressCoeff).card ≤ 5
      ∧ 1 ≤ (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0).card
      ∧ (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0).card ≤ 2 := by
  have hnoPair : ¬ hasParallelAtomPair design.atom := fun hpair =>
    hprimitive ((hasParallelPair_iff_hasParallelAtomPair design).mpr hpair)
  -- the support cannot span: the probe annihilates it
  have hnotSpanning : ¬ hasSpanningSupport design.atom stressCoeff := fun hspanning =>
    hprobeNonzero (hspanning probe hcoplanar)
  -- rank at most two
  have hrankLe : Module.finrank ℝ (supportSpan design.atom stressCoeff) ≤ 2 := by
    by_contra hlarge
    have hrankLe3 : Module.finrank ℝ (supportSpan design.atom stressCoeff) ≤ 3 := by
      have hambient := Submodule.finrank_le (supportSpan design.atom stressCoeff)
      rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hambient
    have hrankEq : Module.finrank ℝ (supportSpan design.atom stressCoeff) = 3 := by
      omega
    exact hnotSpanning (hasSpanningSupport_of_finrank_eq design.atom stressCoeff hrankEq)
  -- rank at least two, else a parallel pair
  have hrankGe : 2 ≤ Module.finrank ℝ (supportSpan design.atom stressCoeff) := by
    by_contra hsmall
    exact hnoPair (hasParallelAtomPair_of_supportSpan_le_one design.atom
      hstressNonzero (by norm_num) hstress (by omega))
  have hrankEq : Module.finrank ℝ (supportSpan design.atom stressCoeff) = 2 := by
    omega
  -- support size at least four: the span-relative split law
  have hsupportGe : 4 ≤ (stressSupport stressCoeff).card := by
    have hlower := twice_finrank_supportSpan_le_card_stressSupport design.atom hstress
    rw [hrankEq] at hlower
    omega
  -- some coordinate vanishes, so the support misses a label
  have hsupportLe : (stressSupport stressCoeff).card ≤ 5 := by
    have hvanish : ∃ c, stressCoeff c = 0 := by
      by_contra hfull
      push Not at hfull
      exact hprobeNonzero (weightedDesign_atoms_span design fun c =>
        hcoplanar c (hfull c))
    obtain ⟨zeroLabel, hzeroLabel⟩ := hvanish
    have hsubset : stressSupport stressCoeff ⊆ Finset.univ.erase zeroLabel := by
      intro c hc
      exact Finset.mem_erase.mpr ⟨fun hEq =>
        (mem_stressSupport_iff.mp hc) (hEq ▸ hzeroLabel), Finset.mem_univ c⟩
    have hcount := Finset.card_le_card hsubset
    rwa [Finset.card_erase_of_mem (Finset.mem_univ zeroLabel), Finset.card_univ,
      Fintype.card_fin] at hcount
  -- an off-plane atom exists: the design spans
  have hoffExists : ∃ b, design.atom b ⬝ᵥ probe ≠ 0 := by
    by_contra hallPlanar
    push Not at hallPlanar
    exact hprobeNonzero (weightedDesign_atoms_span design hallPlanar)
  obtain ⟨offLabel, hoffLabel⟩ := hoffExists
  have hoffGe : 1 ≤ (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0).card :=
    Finset.card_pos.mpr ⟨offLabel, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoffLabel⟩⟩
  -- off-plane atoms are unsupported, so at most two of them
  have hoffLe : (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0).card ≤ 2 := by
    have hsubset : (Finset.univ.filter fun c => design.atom c ⬝ᵥ probe ≠ 0)
        ⊆ (stressSupport stressCoeff)ᶜ := by
      intro c hc
      rw [Finset.mem_compl, mem_stressSupport_iff]
      intro hsupported
      exact (Finset.mem_filter.mp hc).2 (hcoplanar c hsupported)
    have hcount := Finset.card_le_card hsubset
    rw [Finset.card_compl, Fintype.card_fin] at hcount
    omega
  exact ⟨hrankEq, hsupportGe, hsupportLe, hoffGe, hoffLe⟩

/-! ## Part 6: the packaged conditional kill -/

/-- **A single-carrier stratum-(iii) design with a target-beating planar pair
has a dominating triple.**  Steepness is automatic (Part 3); the reduction is
the carrier iff (Part 2).  The one open input is the PLANAR PAIR — the
anisotropic rank-two selection problem, this stratum's residual wall. -/
theorem dominates_of_singleCarrier_of_planarPair (design : WeightedDesign 6 3)
    (probe : Fin 3 → ℝ) (hunit : probe ⬝ᵥ probe = 1) (carrierLabel : Fin 6)
    (huniqueCarrier : ∀ c, c ≠ carrierLabel → design.atom c ⬝ᵥ probe = 0)
    (firstLabel secondLabel : Fin 6)
    (hpairDistinct : firstLabel ≠ secondLabel)
    (hfirstNotCarrier : firstLabel ≠ carrierLabel)
    (hsecondNotCarrier : secondLabel ≠ carrierLabel)
    (htarget : ∀ inPlaneVec : Fin 3 → ℝ, inPlaneVec ⬝ᵥ probe = 0 →
        (design.atom carrierLabel ⬝ᵥ inPlaneVec) ^ 2
          ≤ ((design.atom carrierLabel ⬝ᵥ probe) ^ 2 - 1)
            * ((design.atom firstLabel ⬝ᵥ inPlaneVec) ^ 2
                + (design.atom secondLabel ⬝ᵥ inPlaneVec) ^ 2
                - inPlaneVec ⬝ᵥ inPlaneVec)) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates design C := by
  classical
  have hsteep : 1 < (design.atom carrierLabel ⬝ᵥ probe) ^ 2 :=
    one_lt_probePairing_sq_of_unique_carrier (by norm_num) design probe hunit
      carrierLabel huniqueCarrier
  have hnotMemPair : carrierLabel ∉ ({firstLabel, secondLabel} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨fun hEq => hfirstNotCarrier hEq.symm, fun hEq => hsecondNotCarrier hEq.symm⟩
  have hplanarPair : ∀ c ∈ ({firstLabel, secondLabel} : Finset (Fin 6)),
      design.atom c ⬝ᵥ probe = 0 := by
    intro c hc
    rcases Finset.mem_insert.mp hc with hEq | hEq
    · exact hEq ▸ huniqueCarrier firstLabel hfirstNotCarrier
    · exact (Finset.mem_singleton.mp hEq) ▸ huniqueCarrier secondLabel hsecondNotCarrier
  have hsumPair : ∀ inPlaneVec : Fin 3 → ℝ,
      ∑ c ∈ ({firstLabel, secondLabel} : Finset (Fin 6)),
          (design.atom c ⬝ᵥ inPlaneVec) ^ 2
        = (design.atom firstLabel ⬝ᵥ inPlaneVec) ^ 2
          + (design.atom secondLabel ⬝ᵥ inPlaneVec) ^ 2 := by
    intro inPlaneVec
    rw [Finset.sum_insert (by simpa using hpairDistinct), Finset.sum_singleton]
  refine ⟨insert carrierLabel {firstLabel, secondLabel}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hnotMemPair,
      Finset.card_insert_of_notMem (by simpa using hpairDistinct),
      Finset.card_singleton]
  · rw [dominates_insert_carrier_iff_planarTarget design _ _ probe hunit
      hnotMemPair hplanarPair hsteep]
    intro inPlaneVec hplanarVec
    rw [hsumPair inPlaneVec]
    exact htarget inPlaneVec hplanarVec

end Gtz
