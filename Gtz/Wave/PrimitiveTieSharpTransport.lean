/-
# The tie transports across the sharp duality, and the five-set package

`Gtz/Wave/PrimitiveTiePackage.lean` names the one missing link of its own chain:

> It does not land "every five-set of a primitive tie dominates strictly", nor
> "the sharp dual of a primitive tie is a primitive tie".  Both need `IsTie` to
> transport across the sharp duality, and the STRICT half of that transport is
> not in the tree.

This module lands that strict half, and then the chain it unblocks.

## Part A -- the strict flip

`Gtz.dominates_iff_dominates_naimarkSharpDesign_compl` is the WEAK flip: a
`k`-selection dominates `D` exactly when its complement dominates the sharp
design.  `Gtz.IsTie` also quantifies a `PosDef` over every selection, so the weak
flip alone cannot move a tie.

Part A repeats the weak chain one Loewner notch up.  Every step of that chain is
either an invertible congruence or a rectangular transpose flip, and both have
definite twins in the tree (`Gtz.posDef_congr_right`,
`Gtz.posDef_one_sub_transpose_comm`, `Gtz.posDef_transpose_mul_sub_one_comm`).
Nothing new is needed, and the result is

  **`Gtz.posDef_gap_iff_posDef_gap_naimarkSharpDesign_compl`** -- a `k`-selection
  dominates `D` STRICTLY exactly when its complement dominates the sharp design
  STRICTLY.

## Part B -- the tie transports

Read both flips along a subset and its complement.  Complementation carries the
`k`-subsets onto the `r`-subsets and back, so the two clauses of `Gtz.IsTie` move
across together, at every weight, every rank and every size:

  **`Gtz.isTie_naimarkSharpDesign_of_isTie`**, and at the self-dual cell the
  biconditional **`Gtz.isTie_naimarkSharpDesign_iff_sixThree`**.

`Gtz.isTie_naimarkDual_iff_of_uniform` (Gtz/Wave/GaleSelfDualCell.lean) is the
landed transport across the NAIMARK DUAL and it needs the weight to be UNIFORM.
This one is across the SHARP DESIGN, which carries the design's own weights, and
it holds at every weight.

With `Gtz.isPrimitiveDesign_naimarkSharpDesign_of_isPrimitiveDesign_of_isTie`
this says the sharp duality acts on the PRIMITIVE `(6,3)` TIES, and
`Gtz.naimarkSharpDesign_ne_self` says it acts freely.

## Part C -- every five-set of a primitive tie dominates strictly

The sharp share of `Gtz/Wave/SharpShareCoAtom.lean` is computed without a
whitener, so nothing tied it to the NAMED sharp design.  The landed
`Gtz.whiten_mul_transpose_eq_inv` (Gtz/Wave/ChartSharpDesignGap.lean) supplies
the one identity that does, `W Wᵀ = (Omega - 1)⁻¹`, and hence
`shat_c = t_c * l_c(E)` (`Gtz.naimarkSharpShare_eq_weight_mul_leverage`).
So the sharp design is ALL-HEAVY exactly when every co-atom reading is below one,
which by the co-atom dichotomy is exactly the strict domination of every
five-set.

Chaining Parts B and C with the landed all-heaviness of a primitive tie:

  **`Gtz.forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie_sixThree`** -- at
  a primitive `(6,3)` tie ALL SIX five-sets dominate strictly.

The tree previously had only `Gtz.exists_posDef_gap_erase_sixThree`, a count of
two out of six with no hypothesis.  The gain is the other four, and it is exactly
what primitivity buys.

## Part D -- the package

`Gtz.sixThree_primitiveTie_selfDualPackage` states the five clauses the campaign
wanted as one theorem: all-heavy, no four coplanar, every five-set strict, the
sharp dual is again a primitive tie with the same three properties, and the
duality is an involution with no fixed point.

## The field verdict

Parts A and B are FIELD-BLIND.  The congruence and transpose flips are statements
about a quadratic form over an ordered field and survive verbatim over `C` with
`ᴴ` in place of `ᵀ`; so does the Naimark dual.  So no theorem of Parts A and B
can prove `Gtz.HingeHoldsAtSize 6 3`, and none of them claims to.

Part C is NOT field-blind, at exactly one step.  It consumes
`Gtz.allHeavy_of_isPrimitiveDesign_of_isTie_sixThree`, which consumes the funnel
closure `Gtz.hasParallelPair_of_isTie_sixThree_of_unitAtom`, which consumes the
rank-two three-class law.  Complex GTZ at four atoms and rank two is FALSE
(`Gtz.complexHingeSixDesign` and the qubit SIC), so `Gtz.gtz_rank_two` is
real-only and the chain is exempt.  That is the named failing step.

Part D is a conjunction of Parts B, C and the landed primitivity transport, so it
inherits the same verdict: one real-only step, named.

## What this module does NOT claim

* It does not claim the hinge, nor any statement equivalent to it.  Every clause
  here has the shape `∀ design, IsPrimitiveDesign design → IsTie design → …`,
  which `Gtz.onPathRegistryCollapse` records as IMPLIED by the hinge.
* It does not claim that the five-set clause is INDEPENDENT of the six clauses of
  `Gtz.sixThree_primitiveTie_normalForm`.  It is a clause on the residual, not
  progress against it.
* It does not close the parallel-pair-versus-four-coplanar equivalence that
  `Gtz/Wave/SharpDesignInvolution.lean` names as missing.  Part C uses only the
  half that is landed.
-/
import Gtz.Wave.PrimitiveTiePackage
import Gtz.Wave.GaleSelfDualCell
import Gtz.Wave.ChartSharpDesignGap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k r : ℕ} {D : WeightedDesign m k}

/-! ## Part A -- the strict flip

The weak chain of `Gtz.naimark_dominates_iff_reading_le` is three steps: the
square transpose flip onto the Gram, one positive diagonal congruence, and the
rectangular transpose flip onto the dual reading.  Each has a definite twin. -/

/-- **STRICT DOMINATION IS A STRICT CONTRACTION OF THE DUAL READING.**  The
definite twin of `Gtz.naimark_dominates_iff_reading_le`, step for step: the same
positive diagonal congruence and the same rectangular flip, read with
`Gtz.posDef_congr_right` and `Gtz.posDef_one_sub_transpose_comm`. -/
theorem posDef_gap_iff_reading_lt (N : NaimarkDual D r) (hm : 2 ≤ m)
    {pick : Fin k → Fin m} (hpick : Function.Injective pick) :
    (subsetSum D (Finset.image pick Finset.univ) - 1).PosDef
      ↔ ((1 : Matrix (Fin r) (Fin r) ℝ) - naimarkReading N pick).PosDef := by
  classical
  set gapEntry : Fin k → ℝ := fun a => (D.weight (pick a))⁻¹ - 1 with hgapEntry
  have hgapPos : ∀ a, 0 < gapEntry a := fun a => naimarkCap_diag_pos D hm pick a
  set scale : Fin k → ℝ := fun a => Real.sqrt (gapEntry a)⁻¹ with hscale
  have hscalePos : ∀ a, 0 < scale a := fun a =>
    Real.sqrt_pos.mpr (inv_pos.mpr (hgapPos a))
  have hscaleSq : ∀ a, scale a * scale a = (gapEntry a)⁻¹ := fun a =>
    Real.mul_self_sqrt (inv_pos.mpr (hgapPos a)).le
  set congruence : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal scale with hcongruence
  have hcongrUnit : IsUnit congruence.det := by
    rw [hcongruence, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => (hscalePos a).ne'
  have hsymm : (naimarkCap D pick - naimarkCoGram N pick)ᵀ
      = naimarkCap D pick - naimarkCoGram N pick := by
    rw [Matrix.transpose_sub, naimarkCap, Matrix.diagonal_transpose]
    congr 1
    ext a b
    simp only [naimarkCoGram, Matrix.transpose_apply, Matrix.of_apply]
    exact dotProduct_comm _ _
  have hshape : congruenceᵀ * (naimarkCap D pick - naimarkCoGram N pick) * congruence
      = 1 - (congruence * naimarkCoRows N pick) * (congruence * naimarkCoRows N pick)ᵀ := by
    rw [naimarkCoGram_eq_mul, naimarkCap, hcongruence, Matrix.diagonal_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    · rw [Matrix.diagonal_mul_diagonal]
      have hone : (fun a => scale a * gapEntry a * scale a) = fun _ : Fin k => (1 : ℝ) := by
        funext a
        have hsq := hscaleSq a
        have hne : gapEntry a ≠ 0 := (hgapPos a).ne'
        field_simp at hsq ⊢
        linarith [hsq]
      rw [hone, Matrix.diagonal_one]
    · rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
      simp only [Matrix.mul_assoc]
  have hprod : (congruence * naimarkCoRows N pick)ᵀ * (congruence * naimarkCoRows N pick)
      = naimarkReading N pick := by
    rw [Matrix.transpose_mul, hcongruence, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal scale) (Matrix.diagonal scale) (naimarkCoRows N pick),
      Matrix.diagonal_mul_diagonal]
    have hcoef : (fun a => scale a * scale a)
        = fun a => D.weight (pick a) / (1 - D.weight (pick a)) := by
      funext a
      rw [hscaleSq a, hgapEntry]
      exact naimarkCap_inv_eq D hm pick a
    rw [hcoef, ← Matrix.mul_assoc]
    exact naimark_coRows_reading N pick _
  rw [posDef_gap_iff_naimarkGram D hpick, naimark_gap_eq_cap_sub N hpick,
    posDef_congr_right hsymm hcongrUnit, hshape,
    ← posDef_one_sub_transpose_comm (congruence * naimarkCoRows N pick), hprod]

/-- **STRICT DOMINATION IS A STRICT READING OF THE COMPLEMENT.**  The definite
twin of `Gtz.naimark_dominates_iff_compl_reading`. -/
theorem posDef_gap_iff_compl_reading_lt (N : NaimarkDual D r) (hm : 2 ≤ m)
    (sel : Fin k → Fin m) (cosel : Fin r → Fin m)
    (hpart : Function.Bijective (Sum.elim sel cosel)) :
    (subsetSum D (Finset.image sel Finset.univ) - 1).PosDef
      ↔ (naimarkReading N cosel - naimarkSharpTarget N).PosDef := by
  have hselinj : Function.Injective sel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inl a) = Sum.elim sel cosel (Sum.inl b) := hab
    exact Sum.inl.inj (hpart.1 h)
  rw [posDef_gap_iff_reading_lt N hm hselinj]
  have hswap := naimark_reading_eq_omega_compl N sel cosel hpart
  have hleft : (1 : Matrix (Fin r) (Fin r) ℝ) - naimarkReading N sel
      = naimarkReading N cosel - naimarkSharpTarget N := by
    rw [naimarkReading, hswap, naimarkSharpTarget, naimarkReading]
    abel
  rw [hleft]

/-- **THE SHARP DESIGN DOMINATES STRICTLY AT THE STRICT DUAL READING.**  The
definite twin of `Gtz.dominates_naimarkSharpDesign_iff_reading`. -/
theorem posDef_gap_naimarkSharpDesign_iff_reading {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) {cosel : Fin r → Fin m} (hcoinj : Function.Injective cosel) :
    (subsetSum (naimarkSharpDesign F hm) (Finset.image cosel Finset.univ) - 1).PosDef
      ↔ (naimarkReading N cosel - naimarkSharpTarget N).PosDef := by
  classical
  rw [subsetSum, Finset.sum_image fun left _ right _ hlr => hcoinj hlr]
  have hshapes : ∑ j, atomMatrix ((naimarkSharpDesign F hm).atom (cosel j)) - 1
      = F.whitenᵀ * (naimarkReading N cosel - naimarkSharpTarget N) * F.whiten := by
    have hleftSum : ∑ j, atomMatrix ((naimarkSharpDesign F hm).atom (cosel j))
        = F.whitenᵀ * naimarkReading N cosel * F.whiten := by
      rw [naimarkReading, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [naimarkSharpDesign_atom, atomMatrix_naimarkSharpAtom F hm (cosel j)]
    rw [hleftSum, Matrix.mul_sub, Matrix.sub_mul, F.spec]
  have hsymm : (naimarkReading N cosel - naimarkSharpTarget N)ᵀ
      = naimarkReading N cosel - naimarkSharpTarget N := by
    rw [Matrix.transpose_sub, naimarkSharpTarget, naimarkOmega, naimarkReading,
      Matrix.transpose_sub, Matrix.transpose_one]
    congr 1
    · rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
    · congr 1
      rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
  rw [hshapes]
  exact (posDef_congr_right hsymm F.unit).symm

/-- **THE STRICT FLIP, AS A BICONDITIONAL.**  A `k`-selection dominates `D`
STRICTLY exactly when its complement dominates the named sharp design STRICTLY.
This is the half of the transport that `Gtz/Wave/PrimitiveTiePackage.lean` names
as missing. -/
theorem posDef_gap_iff_posDef_gap_naimarkSharpDesign_compl {N : NaimarkDual D r}
    (F : SharpFrame N) (hm : 2 ≤ m) (sel : Fin k → Fin m) (cosel : Fin r → Fin m)
    (hpart : Function.Bijective (Sum.elim sel cosel)) :
    (subsetSum D (Finset.image sel Finset.univ) - 1).PosDef
      ↔ (subsetSum (naimarkSharpDesign F hm) (Finset.image cosel Finset.univ) - 1).PosDef := by
  have hcoinj : Function.Injective cosel := by
    intro a b hab
    have h : Sum.elim sel cosel (Sum.inr a) = Sum.elim sel cosel (Sum.inr b) := hab
    exact Sum.inr.inj (hpart.1 h)
  rw [posDef_gap_iff_compl_reading_lt N hm sel cosel hpart,
    posDef_gap_naimarkSharpDesign_iff_reading F hm hcoinj]

/-! ## Part B -- the tie transports, at every cell

The two flips are stated along index maps.  A subset and its complement give the
order embeddings the flips need, and complementation is an involution of the
subsets that carries the `k`-subsets onto the `r`-subsets, so both clauses of
`Gtz.IsTie` move across at once.

`Gtz.isTie_naimarkDual_iff_of_uniform` (Gtz/Wave/GaleSelfDualCell.lean) is the
landed transport across the NAIMARK DUAL, and it needs the weight to be UNIFORM.
The transport below is across the SHARP DESIGN, which carries the design's own
weights, and it holds at every weight. -/

/-- A subset and its complement enumerate the ground set. -/
theorem sumElim_orderEmbOfFin_bijective {size left right : ℕ} (selected : Finset (Fin size))
    (hcard : selected.card = left) (hcompl : selectedᶜ.card = right) :
    Function.Bijective (Sum.elim (selected.orderEmbOfFin hcard)
      (selectedᶜ.orderEmbOfFin hcompl)) := by
  classical
  have htotal : left + right = size := by
    have hsplit := Finset.card_add_card_compl selected
    rw [hcard, hcompl, Fintype.card_fin] at hsplit
    exact hsplit
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [htotal]⟩
  rintro (a | a) (b | b) hab
  · exact congrArg Sum.inl ((selected.orderEmbOfFin hcard).injective hab)
  · exfalso
    have hin : selected.orderEmbOfFin hcard a ∈ selected := selected.orderEmbOfFin_mem hcard a
    have hout : selectedᶜ.orderEmbOfFin hcompl b ∈ selectedᶜ := selectedᶜ.orderEmbOfFin_mem hcompl b
    rw [Finset.mem_compl] at hout
    exact hout (by rwa [show selected.orderEmbOfFin hcard a
      = selectedᶜ.orderEmbOfFin hcompl b from hab] at hin)
  · exfalso
    have hin : selected.orderEmbOfFin hcard b ∈ selected := selected.orderEmbOfFin_mem hcard b
    have hout : selectedᶜ.orderEmbOfFin hcompl a ∈ selectedᶜ := selectedᶜ.orderEmbOfFin_mem hcompl a
    rw [Finset.mem_compl] at hout
    exact hout (by rwa [show selected.orderEmbOfFin hcard b
      = selectedᶜ.orderEmbOfFin hcompl a from hab.symm] at hin)
  · exact congrArg Sum.inr ((selectedᶜ.orderEmbOfFin hcompl).injective hab)

/-- **THE WEAK FLIP ON SUBSETS.**  `Gtz.dominates_iff_dominates_naimarkSharpDesign_compl`
read along a `k`-subset and its complement. -/
theorem dominates_iff_dominates_naimarkSharpDesign_compl_finset {N : NaimarkDual D r}
    (F : SharpFrame N) (hm : 2 ≤ m) (selected : Finset (Fin m)) (hcard : selected.card = k) :
    Dominates D selected ↔ Dominates (naimarkSharpDesign F hm) selectedᶜ := by
  have hcompl := card_compl_of_naimark N hcard
  have hflip := dominates_iff_dominates_naimarkSharpDesign_compl F hm
    (selected.orderEmbOfFin hcard) (selectedᶜ.orderEmbOfFin hcompl)
    (sumElim_orderEmbOfFin_bijective selected hcard hcompl)
  rwa [image_orderEmbOfFin_univ hcard, image_orderEmbOfFin_univ hcompl] at hflip

/-- **THE STRICT FLIP ON SUBSETS.** -/
theorem posDef_gap_iff_posDef_gap_naimarkSharpDesign_compl_finset {N : NaimarkDual D r}
    (F : SharpFrame N) (hm : 2 ≤ m) (selected : Finset (Fin m)) (hcard : selected.card = k) :
    (subsetSum D selected - 1).PosDef
      ↔ (subsetSum (naimarkSharpDesign F hm) selectedᶜ - 1).PosDef := by
  have hcompl := card_compl_of_naimark N hcard
  have hflip := posDef_gap_iff_posDef_gap_naimarkSharpDesign_compl F hm
    (selected.orderEmbOfFin hcard) (selectedᶜ.orderEmbOfFin hcompl)
    (sumElim_orderEmbOfFin_bijective selected hcard hcompl)
  rwa [image_orderEmbOfFin_univ hcard, image_orderEmbOfFin_univ hcompl] at hflip

/-- The complement of an `r`-subset has card `k`. -/
theorem card_compl_of_naimark' {N : NaimarkDual D r} {selected : Finset (Fin m)}
    (hcard : selected.card = r) : selectedᶜ.card = k := by
  have hadd := N.rankAdd
  rw [Finset.card_compl, hcard, Fintype.card_fin]
  omega

/-- **A TIE PASSES TO THE SHARP DESIGN**, at every weight, at every rank and every
size.  The weak flip carries the dominating selection to the complementary
selection, and the strict flip carries the refusal of every strict dominator to
the refusal of every strict dominator. -/
theorem isTie_naimarkSharpDesign_of_isTie {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m)
    (htie : IsTie D) : IsTie (naimarkSharpDesign F hm) := by
  classical
  obtain ⟨⟨C, hcard, hdom⟩, hnostrict⟩ := htie
  refine ⟨⟨Cᶜ, card_compl_of_naimark N hcard,
    (dominates_iff_dominates_naimarkSharpDesign_compl_finset F hm C hcard).mp hdom⟩,
    fun S hcardS hstrict => ?_⟩
  refine hnostrict Sᶜ (card_compl_of_naimark' (N := N) hcardS) ?_
  refine (posDef_gap_iff_posDef_gap_naimarkSharpDesign_compl_finset F hm Sᶜ
    (card_compl_of_naimark' (N := N) hcardS)).mpr ?_
  rwa [compl_compl]

/-- **THE TIE TRANSPORTS ACROSS THE SHARP DUALITY.**  A `(6,3)` design is a tie
exactly when its sharp design is.  The cell is self-dual, so the transport reads
in both directions at the same cell.

This is the missing link `Gtz/Wave/PrimitiveTiePackage.lean` names.  With
`Gtz.isPrimitiveDesign_naimarkSharpDesign_of_isPrimitiveDesign_of_isTie` the
sharp duality acts on the PRIMITIVE `(6,3)` ties, and by
`Gtz.naimarkSharpDesign_ne_self` it acts freely. -/
theorem isTie_naimarkSharpDesign_iff_sixThree (D : WeightedDesign 6 3) {N : NaimarkDual D 3}
    (F : SharpFrame N) (hsix : (2 : ℕ) ≤ 6) :
    IsTie (naimarkSharpDesign F hsix) ↔ IsTie D := by
  classical
  refine ⟨fun hdual => ⟨?_, fun S hcardS hstrict => ?_⟩,
    isTie_naimarkSharpDesign_of_isTie F hsix⟩
  · obtain ⟨C, hcard, hdom⟩ := hdual.1
    refine ⟨Cᶜ, card_compl_of_naimark' (N := N) hcard, ?_⟩
    refine (dominates_iff_dominates_naimarkSharpDesign_compl_finset F hsix Cᶜ
      (card_compl_of_naimark' (N := N) hcard)).mpr ?_
    rwa [compl_compl]
  · exact hdual.2 Sᶜ (card_compl_of_naimark N hcardS)
      ((posDef_gap_iff_posDef_gap_naimarkSharpDesign_compl_finset F hsix S hcardS).mp hstrict)

/-! ## Part C -- the sharp share of the NAMED sharp design

`Gtz.naimarkSharpShare` is computed with no whitener at all, so nothing tied it
to `Gtz.naimarkSharpDesign`.  The whitening congruence supplies the one identity
that does. -/

/-- **THE SHARP SHARE IS THE SHARE OF THE NAMED SHARP DESIGN.**  The whitener
resolves the sharp target, so the sharp atom's leverage is the whitener-free
reading of `Gtz/Wave/SharpShareCoAtom.lean` scaled by `t_c/(1 - t_c)`.

This is the bridge between the two halves of the campaign's sharp calculus: one
half names the design and cannot read it, the other reads it and cannot name
it. -/
theorem naimarkSharpShare_eq_weight_mul_leverage {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) (label : Fin m) :
    naimarkSharpShare D N label
      = D.weight label * leverageOf (naimarkSharpAtom F label) := by
  have hsq : sharpScale D label * sharpScale D label = D.weight label / (1 - D.weight label) :=
    Real.mul_self_sqrt (sharpScale_nonneg D hm label)
  have hadj := dotProduct_mulVec_transpose F.whiten
    (sharpScale D label • N.co label) (F.whitenᵀ *ᵥ (sharpScale D label • N.co label))
  have hlev : leverageOf (naimarkSharpAtom F label)
      = sharpScale D label * (sharpScale D label
        * (N.co label ⬝ᵥ ((naimarkSharpTarget N)⁻¹ *ᵥ N.co label))) := by
    rw [leverageOf_eq_dotProduct, naimarkSharpAtom, hadj, Matrix.mulVec_mulVec,
      whiten_mul_transpose_eq_inv F hm, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul]
  rw [hlev, naimarkSharpShare, naimarkSharpCoeff]
  linear_combination (-(D.weight label
    * (N.co label ⬝ᵥ ((naimarkSharpTarget N)⁻¹ *ᵥ N.co label)))) * hsq

/-- **THE SHARP DESIGN IS ALL-HEAVY EXACTLY WHEN EVERY FIVE-SET DOMINATES
STRICTLY.**  `Gtz.forall_weight_lt_naimarkSharpShare_iff` in the vocabulary of
the NAMED sharp design. -/
theorem allHeavy_naimarkSharpDesign_iff {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m) :
    AllHeavy (naimarkSharpDesign F hm)
      ↔ ∀ label : Fin m, (subsetSum D (Finset.univ.erase label) - 1).PosDef := by
  rw [← forall_weight_lt_naimarkSharpShare_iff D N hm]
  constructor
  · intro hheavy label
    have hshare := naimarkSharpShare_eq_weight_mul_leverage F hm label
    have hlev : (1 : ℝ) < leverageOf (naimarkSharpAtom F label) := hheavy label
    nlinarith [hshare, hlev, D.weight_pos label]
  · intro hall label
    have hshare := naimarkSharpShare_eq_weight_mul_leverage F hm label
    have hlt := hall label
    show (1 : ℝ) < leverageOf (naimarkSharpAtom F label)
    nlinarith [hshare, hlt, D.weight_pos label]

/-- **EVERY FIVE-SET OF A PRIMITIVE `(6,3)` TIE DOMINATES STRICTLY.**

The chain: the sharp dual of a primitive tie is primitive
(`Gtz.isPrimitiveDesign_naimarkSharpDesign_of_isPrimitiveDesign_of_isTie`) and is
a tie (Part B), hence all-heavy
(`Gtz.allHeavy_of_isPrimitiveDesign_of_isTie_sixThree`), and all-heaviness of the
sharp design is the strictness of every five-set (Part C).

The tree owned only `Gtz.exists_posDef_gap_erase_sixThree`, which gives two of
the six with no hypothesis.  Primitivity buys the other four. -/
theorem forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie_sixThree (D : WeightedDesign 6 3)
    {N : NaimarkDual D 3} (F : SharpFrame N) (hsix : (2 : ℕ) ≤ 6)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) (label : Fin 6) :
    (subsetSum D (Finset.univ.erase label) - 1).PosDef := by
  have hdualTie : IsTie (naimarkSharpDesign F hsix) :=
    (isTie_naimarkSharpDesign_iff_sixThree D F hsix).mpr htie
  have hdualPrim : IsPrimitiveDesign (naimarkSharpDesign F hsix) :=
    isPrimitiveDesign_naimarkSharpDesign_of_isPrimitiveDesign_of_isTie D N F hsix hprimitive htie
  have hheavy := allHeavy_of_isPrimitiveDesign_of_isTie_sixThree (naimarkSharpDesign F hsix)
    hdualPrim hdualTie
  exact (allHeavy_naimarkSharpDesign_iff F hsix).mp hheavy label

/-- **EVERY CO-ATOM READING OF A PRIMITIVE `(6,3)` TIE IS BELOW ONE.**  The same
statement in the scalar vocabulary of `Gtz/Wave/SharpFiveSetCriterion.lean`. -/
theorem totalGapReading_lt_one_of_isPrimitiveDesign_of_isTie_sixThree (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) (label : Fin 6) :
    totalGapReading D label < 1 := by
  obtain ⟨N⟩ := exists_naimarkDual D (r := 3) (by norm_num)
  obtain ⟨F⟩ := exists_sharpFrame N (by norm_num)
  exact (posDef_gap_erase_iff D (by norm_num) label).mp
    (forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie_sixThree D F (by norm_num)
      hprimitive htie label)

/-- **THE FIVE-SET CLAUSE, WITHOUT A NAMED DUAL.**  Every one of the six
five-sets of a primitive `(6,3)` tie dominates strictly.  The dual, the frame and
the whitener have all been discharged. -/
theorem forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) (label : Fin 6) :
    (subsetSum D (Finset.univ.erase label) - 1).PosDef :=
  (posDef_gap_erase_iff D (by norm_num) label).mpr
    (totalGapReading_lt_one_of_isPrimitiveDesign_of_isTie_sixThree D hprimitive htie label)

/-! ## Part D -- the package -/

/-- **THE PRIMITIVE `(6,3)` TIE PACKAGE.**  Everything the campaign carries
separately about a `(6,3)` counterexample, as one theorem.

Let `D` be a primitive `(6,3)` tie and `E` its sharp design.  Then

1. `D` is ALL-HEAVY,
2. no four atoms of `D` are coplanar,
3. every one of the six five-sets of `D` dominates STRICTLY,
4. `E` is again a primitive tie, and clauses 1 to 3 hold of `E` as well,
5. `E` is never `D`.

Clause 5 with the involution `Gtz.naimarkSharpAtom_secondSharpFrame` makes the
sharp duality a FREE involution on the primitive `(6,3)` ties: they come in pairs.

This is a clause on the residual, not progress against it.  Every statement here
has the shape `∀ design, IsPrimitiveDesign design → IsTie design → …`, which
`Gtz.onPathRegistryCollapse` records as IMPLIED by the hinge. -/
theorem sixThree_primitiveTie_selfDualPackage (D : WeightedDesign 6 3) {N : NaimarkDual D 3}
    (F : SharpFrame N) (hsix : (2 : ℕ) ≤ 6)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    AllHeavy D
      ∧ (∀ x y z w : Fin 6, x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
          ¬ FourCoplanar D x y z w)
      ∧ (∀ label : Fin 6, (subsetSum D (Finset.univ.erase label) - 1).PosDef)
      ∧ IsPrimitiveDesign (naimarkSharpDesign F hsix)
      ∧ IsTie (naimarkSharpDesign F hsix)
      ∧ AllHeavy (naimarkSharpDesign F hsix)
      ∧ (∀ x y z w : Fin 6, x ≠ y → x ≠ z → x ≠ w → y ≠ z → y ≠ w → z ≠ w →
          ¬ FourCoplanar (naimarkSharpDesign F hsix) x y z w)
      ∧ (∀ label : Fin 6,
          (subsetSum (naimarkSharpDesign F hsix) (Finset.univ.erase label) - 1).PosDef)
      ∧ naimarkSharpDesign F hsix ≠ D := by
  have hdualTie : IsTie (naimarkSharpDesign F hsix) :=
    (isTie_naimarkSharpDesign_iff_sixThree D F hsix).mpr htie
  have hdualPrim : IsPrimitiveDesign (naimarkSharpDesign F hsix) :=
    isPrimitiveDesign_naimarkSharpDesign_of_isPrimitiveDesign_of_isTie D N F hsix hprimitive htie
  exact ⟨allHeavy_of_isPrimitiveDesign_of_isTie_sixThree D hprimitive htie,
    fun x y z w hxy hxz hxw hyz hyw hzw hflat =>
      not_fourCoplanar_of_isPrimitiveDesign_of_isTie D hprimitive htie hxy hxz hxw hyz hyw hzw
        hflat,
    forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie D hprimitive htie,
    hdualPrim, hdualTie,
    allHeavy_of_isPrimitiveDesign_of_isTie_sixThree _ hdualPrim hdualTie,
    fun x y z w hxy hxz hxw hyz hyw hzw hflat =>
      not_fourCoplanar_of_isPrimitiveDesign_of_isTie _ hdualPrim hdualTie hxy hxz hxw hyz hyw hzw
        hflat,
    forall_posDef_gap_erase_of_isPrimitiveDesign_of_isTie _ hdualPrim hdualTie,
    naimarkSharpDesign_ne_self N F hsix⟩

/-- **THE PACKAGE, WITH THE DUAL OBTAINED.**  Every primitive `(6,3)` tie carries
a dual and a whitening frame, so the package applies to every one of them with no
data supplied. -/
theorem exists_sixThree_primitiveTie_selfDualPackage (D : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign D) (htie : IsTie D) :
    ∃ (N : NaimarkDual D 3) (F : SharpFrame N) (hsix : (2 : ℕ) ≤ 6),
      AllHeavy D
        ∧ (∀ label : Fin 6, (subsetSum D (Finset.univ.erase label) - 1).PosDef)
        ∧ IsPrimitiveDesign (naimarkSharpDesign F hsix)
        ∧ IsTie (naimarkSharpDesign F hsix)
        ∧ naimarkSharpDesign F hsix ≠ D := by
  obtain ⟨N⟩ := exists_naimarkDual D (r := 3) (by norm_num)
  obtain ⟨F⟩ := exists_sharpFrame N (by norm_num)
  obtain ⟨hheavy, _, hfive, hdualPrim, hdualTie, _, _, _, hne⟩ :=
    sixThree_primitiveTie_selfDualPackage D F (by norm_num) hprimitive htie
  exact ⟨N, F, by norm_num, hheavy, hfive, hdualPrim, hdualTie, hne⟩

end Gtz
