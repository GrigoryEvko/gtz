import Gtz.Wave.A1NeedleTieDegeneracy
import Gtz.Reduction.ConnectednessRouteCalibration
import Gtz.Reduction.TrichotomyLedger
import Gtz.Design.SphereExistence
import Gtz.Ties.TetrahedronCertifiedTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The `(6,3)` tie hypothesis `atom i = atom j` is FALSE, and its repair

`Gtz.heavyNeedleResidual_of_tie_repeats_an_atom` retires the registry axiom
`Skeleton.obligationBaseTripleTightUThreeSix` from one hypothesis:

  every `(6,3)` tie carries two distinct labels with EQUAL atom vectors.

This module refutes that hypothesis outright, and repairs the route.

## Why it had to fail

`Gtz.atomMatrix` is `Matrix.vecMulVec g g`, so it is blind to the sign of `g`.
Parseval, `Gtz.subsetSum`, `Gtz.Dominates` and `Gtz.IsTie` read the atoms ONLY
through `atomMatrix`.  So `IsTie` is invariant under the group that flips the
sign of any subset of the atoms, and `Gtz.signFlipDesign` mechanizes that
group.  The predicate "two atoms are EQUAL" is not invariant under it: flip one
member of an equal pair and the pair stops being equal while the design stays a
tie.  A hypothesis that is not invariant under a symmetry of its own conclusion
is the wrong hypothesis.

## The witness

`Gtz.antipodalTetraDesign` is the regular tetrahedron `(4,3)` tie with two of
its four directions split into antipodal pairs.  Its six atoms are six of the
eight vectors of `{-1, 1}^3`, its weights are `1/8` four times and `1/4` twice,
and Parseval is exact because the four tetrahedron atoms sum to `4` times the
identity.  Every triple that reads three distinct directions has gap `3 - a aᵀ`
at the missing direction `a`, which is positive semidefinite by Cauchy-Schwarz
and singular at `a`.  Every triple that reads a direction twice is rank
deficient.  So the design is a tie, its six atoms are pairwise DISTINCT, and
the hypothesis fails.

## What survives, and what the repair costs

The witness still has a parallel pair, at ratio `-1`.  Two repaired bridges are
below, and each reaches the same registry axiom:

- `Gtz.heavyNeedleResidual_of_tie_hasCloneMatrixPair`, from equal atom
  MATRICES, which is the sign-flip closure of the refuted hypothesis;
- `Gtz.heavyNeedleResidual_of_tie_hasParallelPair`, from
  `Gtz.HasParallelPair`, which is weaker still and is EXACTLY the conclusion
  that `Gtz.sixThree_hasParallelPair_of_isTie_of_coplanarStress_unconditional`
  already delivers on the coplanar-stress branch.

The mechanism is `Gtz.tripleBracket_eq_zero_of_atomMatrix_eq_outer`: two atoms
with the same rank-one matrix have all three of their `2 x 2` minors zero, so
the bracket vanishes at every third label and line-freeness dies.

## The reconnaissance this module does NOT settle

Whether a `(6,3)` tie can have six pairwise NON-PARALLEL atoms is open here.
The witness has four directions, which agrees with the census.  A directed
search over the primitive stratum drove the objective
`max over triples of lambda_min` to `1 + 9.3e-13` but only by sending a length
ratio to `e^17` or a leverage to `2.5e-5`, and every near hit was STRICTLY
above one in 34-digit arithmetic.  With non-degeneracy floors in place the
margin stalls near `5e-4`.  So the primitive infimum appears to BE one, and no
uniform margin bound can prove the parallel-pair conjecture.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## The landed sign flip fixes every tie

`Gtz.negateAtom` is the one-atom sign flip, landed with its Parseval proof and
its parallel-freeness transfer.  What it never carried is the transfer that
matters here: the flip fixes every subset sum, hence every domination fact,
hence the tie predicate itself. -/

/-- **Every subset sum is fixed by a sign flip.**  This is the whole content:
`Gtz.IsTie` reads the atoms only through their rank-one matrices. -/
theorem subsetSum_negateAtom (D : WeightedDesign m k) (flipLabel : Fin m)
    (selected : Finset (Fin m)) :
    subsetSum (negateAtom D flipLabel) selected = subsetSum D selected := by
  refine Finset.sum_congr rfl fun atomLabel _ => ?_
  by_cases hhit : atomLabel = flipLabel
  · subst hhit
    rw [negateAtom_atom_self, atomMatrix_neg]
  · rw [negateAtom_atom_other D hhit]

theorem dominates_negateAtom_iff (D : WeightedDesign m k) (flipLabel : Fin m)
    (selected : Finset (Fin m)) :
    Dominates (negateAtom D flipLabel) selected ↔ Dominates D selected := by
  unfold Dominates
  rw [subsetSum_negateAtom]

/-- **A SIGN FLIP CARRIES A TIE TO A TIE.**  The refuted hypothesis is not
invariant under this action, and the tie predicate is.  That mismatch is the
whole reason the hypothesis had to be false. -/
theorem isTie_negateAtom_iff (D : WeightedDesign m k) (flipLabel : Fin m) :
    IsTie (negateAtom D flipLabel) ↔ IsTie D := by
  unfold IsTie
  constructor
  · rintro ⟨⟨selected, hcard, hdom⟩, hnostrict⟩
    refine ⟨⟨selected, hcard, (dominates_negateAtom_iff D flipLabel selected).mp hdom⟩,
      fun other hother => ?_⟩
    have hkill := hnostrict other hother
    rwa [subsetSum_negateAtom] at hkill
  · rintro ⟨⟨selected, hcard, hdom⟩, hnostrict⟩
    refine ⟨⟨selected, hcard, (dominates_negateAtom_iff D flipLabel selected).mpr hdom⟩,
      fun other hother => ?_⟩
    rw [subsetSum_negateAtom]
    exact hnostrict other hother

/-! ## Equal atom matrices kill every bracket -/

/-- **TWO ATOMS WITH THE SAME RANK-ONE MATRIX HAVE VANISHING `2 x 2` MINORS**,
at EVERY slot pair.  The minor squared is an exact combination of three entry
identities, so the minor is zero.  This is the sign-blind replacement for atom
equality, and it needs no case split on the slots.

The combination is `v_b² (u_a u_a - v_a v_a) + v_a² (u_b u_b - v_b v_b)
- 2 v_a v_b (u_a u_b - v_a v_b)`, which is `(u_a v_b - u_b v_a)²` on the nose. -/
theorem crossMinor_slot_eq_zero_of_atomMatrix_eq (leftVec rightVec : Fin 3 → ℝ)
    (hclone : atomMatrix leftVec = atomMatrix rightVec) (leftSlot rightSlot : Fin 3) :
    leftVec leftSlot * rightVec rightSlot - leftVec rightSlot * rightVec leftSlot = 0 := by
  have hentry : ∀ i j : Fin 3, leftVec i * leftVec j = rightVec i * rightVec j := by
    intro i j
    simpa [atomMatrix, Matrix.vecMulVec_apply] using congrFun (congrFun hclone i) j
  refine sq_eq_zero_iff.mp ?_
  linear_combination (rightVec rightSlot) ^ 2 * hentry leftSlot leftSlot
    + (rightVec leftSlot) ^ 2 * hentry rightSlot rightSlot
    - 2 * rightVec leftSlot * rightVec rightSlot * hentry leftSlot rightSlot

/-- The three minors of a clone pair, named. -/
theorem crossMinor_eq_zero_of_atomMatrix_eq (leftVec rightVec : Fin 3 → ℝ)
    (hclone : atomMatrix leftVec = atomMatrix rightVec) :
    leftVec 0 * rightVec 1 - leftVec 1 * rightVec 0 = 0
      ∧ leftVec 0 * rightVec 2 - leftVec 2 * rightVec 0 = 0
      ∧ leftVec 1 * rightVec 2 - leftVec 2 * rightVec 1 = 0 :=
  ⟨crossMinor_slot_eq_zero_of_atomMatrix_eq leftVec rightVec hclone 0 1,
    crossMinor_slot_eq_zero_of_atomMatrix_eq leftVec rightVec hclone 0 2,
    crossMinor_slot_eq_zero_of_atomMatrix_eq leftVec rightVec hclone 1 2⟩

/-- **A CLONE PAIR IS A PARALLEL PAIR.**  So the clone-matrix hypothesis implies
the parallel-pair hypothesis, and
`Gtz.heavyNeedleResidual_of_tie_hasParallelPair` subsumes
`Gtz.heavyNeedleResidual_of_tie_hasCloneMatrixPair`.  The campaign has ONE
statement to prove, not two. -/
theorem hasParallelPair_of_atomMatrix_eq {D : WeightedDesign m 3}
    {firstLabel secondLabel : Fin m} (hdistinct : firstLabel ≠ secondLabel)
    (hclone : atomMatrix (D.atom firstLabel) = atomMatrix (D.atom secondLabel)) :
    HasParallelPair D := by
  by_cases hzero : D.atom secondLabel = 0
  · exact ⟨firstLabel, secondLabel, 0, hdistinct, by rw [hzero]; module⟩
  · obtain ⟨pivotSlot, hpivot⟩ : ∃ slot : Fin 3, D.atom secondLabel slot ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hzero (funext fun slot => hall slot)
    refine ⟨secondLabel, firstLabel,
      D.atom firstLabel pivotSlot / D.atom secondLabel pivotSlot, hdistinct.symm, ?_⟩
    funext slot
    have hminor := crossMinor_slot_eq_zero_of_atomMatrix_eq _ _ hclone slot pivotSlot
    show D.atom firstLabel slot
      = D.atom firstLabel pivotSlot / D.atom secondLabel pivotSlot * D.atom secondLabel slot
    rw [div_mul_eq_mul_div, eq_div_iff hpivot]
    linarith [hminor]

/-- **Clones in the two OUTER slots kill the bracket.**  This is the slot
arrangement `Gtz.atomBracket_ne_zero_of_lineFree` presents. -/
theorem tripleBracket_eq_zero_of_atomMatrix_eq_outer (leftVec midVec rightVec : Fin 3 → ℝ)
    (hclone : atomMatrix leftVec = atomMatrix rightVec) :
    tripleBracket leftVec midVec rightVec = 0 := by
  obtain ⟨hxy, hxz, hyz⟩ := crossMinor_eq_zero_of_atomMatrix_eq leftVec rightVec hclone
  rw [tripleBracket_eq]
  linear_combination (-(midVec 0)) * hyz + midVec 1 * hxz + (-(midVec 2)) * hxy

/-- **Equal atom matrices are a line-degeneracy.**  The strictly weaker,
sign-blind form of `Gtz.not_hasLinePattern_lineFree_of_atom_eq`. -/
theorem not_hasLinePattern_lineFree_of_atomMatrix_eq (design : WeightedDesign 6 3)
    {firstLabel secondLabel : Fin 6} (hdistinct : firstLabel ≠ secondLabel)
    (hclone : atomMatrix (design.atom firstLabel) = atomMatrix (design.atom secondLabel)) :
    ¬ HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) := by
  intro hlineFree
  obtain ⟨thirdLabel, hthirdFirst, hthirdSecond⟩ :=
    exists_thirdLabel_off_pair firstLabel secondLabel hdistinct
  refine atomBracket_ne_zero_of_lineFree design hlineFree hthirdFirst hdistinct
    hthirdSecond ?_
  exact tripleBracket_eq_zero_of_atomMatrix_eq_outer _ _ _ hclone

/-- **A parallel pair is a line-degeneracy.**  The weakest of the three forms,
and the one the `(6,3)` hinge already concludes.  This is the landed
`Gtz.not_hasLinePattern_of_hasParallelPair` at the empty line family, which is
the first entry of `Gtz.lineFamiliesSix`. -/
theorem not_hasLinePattern_lineFree_of_hasParallelPair (design : WeightedDesign 6 3)
    (hparallel : HasParallelPair design) :
    ¬ HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  not_hasLinePattern_of_hasParallelPair (by decide) design hparallel

/-! ## The witness: a `(6,3)` tie with six pairwise distinct atoms -/

/-- Six of the eight vectors of `{-1, 1}^3`: the four tetrahedron directions
`(1,1,1)`, `(1,-1,-1)`, `(-1,1,-1)`, `(-1,-1,1)`, with the first two each
carrying their antipode as a second label. -/
noncomputable def antipodalTetraAtom : Fin 6 → Fin 3 → ℝ
  | 0 => ![1, 1, 1]
  | 1 => ![-1, -1, -1]
  | 2 => ![1, -1, -1]
  | 3 => ![-1, 1, 1]
  | 4 => ![-1, 1, -1]
  | 5 => ![-1, -1, 1]

/-- Weight `1/8` on each split label and `1/4` on each unsplit one. -/
noncomputable def antipodalTetraWeight : Fin 6 → ℝ
  | 0 => 1 / 8
  | 1 => 1 / 8
  | 2 => 1 / 8
  | 3 => 1 / 8
  | 4 => 1 / 4
  | 5 => 1 / 4

/-- The witness as a weighted `(6,3)` design.  Parseval is exact: the four
tetrahedron rank-one matrices sum to four times the identity, and every label
pair contributes weight `1/4` to its direction. -/
noncomputable def antipodalTetraDesign : WeightedDesign 6 3 where
  atom := antipodalTetraAtom
  weight := antipodalTetraWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [antipodalTetraWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [antipodalTetraWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [antipodalTetraAtom, antipodalTetraWeight, atomMatrix,
        Matrix.cons_val_two] <;> norm_num

theorem antipodalTetraDesign_atom :
    antipodalTetraDesign.atom = antipodalTetraAtom := rfl

theorem antipodalTetraDesign_weight :
    antipodalTetraDesign.weight = antipodalTetraWeight := rfl

/-- Label one carries the antipode of label zero. -/
theorem antipodalTetraDesign_atom_one :
    antipodalTetraDesign.atom 1 = -antipodalTetraDesign.atom 0 := by
  ext slot
  fin_cases slot <;>
    norm_num [antipodalTetraDesign, antipodalTetraAtom, Matrix.cons_val_two]

/-- Label three carries the antipode of label two. -/
theorem antipodalTetraDesign_atom_three :
    antipodalTetraDesign.atom 3 = -antipodalTetraDesign.atom 2 := by
  ext slot
  fin_cases slot <;>
    norm_num [antipodalTetraDesign, antipodalTetraAtom, Matrix.cons_val_two]

/-- **THE SIX ATOMS ARE PAIRWISE DISTINCT.**  The functional
`v 0 + 2 * v 1 + 4 * v 2` separates them, with values
`7, -7, -5, 5, -3, 1`. -/
theorem antipodalTetraDesign_atom_injective :
    Function.Injective antipodalTetraDesign.atom := by
  intro firstLabel secondLabel hatomEq
  have hsep : antipodalTetraDesign.atom firstLabel 0
        + 2 * antipodalTetraDesign.atom firstLabel 1
        + 4 * antipodalTetraDesign.atom firstLabel 2
      = antipodalTetraDesign.atom secondLabel 0
        + 2 * antipodalTetraDesign.atom secondLabel 1
        + 4 * antipodalTetraDesign.atom secondLabel 2 := by
    rw [hatomEq]
  fin_cases firstLabel <;> fin_cases secondLabel <;>
    first
      | rfl
      | (exfalso;
         norm_num [antipodalTetraDesign, antipodalTetraAtom, Matrix.cons_val_two] at hsep)

/-- **WEAK DOMINATION** at the triple `{0, 2, 4}`, whose gap is
`3 - a aᵀ` at the missing direction `a = (-1,-1,1)`.  The exact sum of squares
is `(x - y)^2 + (x + z)^2 + (y + z)^2`. -/
theorem antipodalTetraDesign_dominates :
    Dominates antipodalTetraDesign ({0, 2, 4} : Finset (Fin 6)) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probeVec => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0, 2, 4} : Finset (Fin 6)) fun label _ =>
      posSemidef_atomMatrix (antipodalTetraDesign.atom label)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, dotProduct_tripleGap_mulVec antipodalTetraDesign
      (by decide) (by decide) (by decide)]
    have hform : (antipodalTetraDesign.atom 0 ⬝ᵥ probeVec) ^ 2
        + (antipodalTetraDesign.atom 2 ⬝ᵥ probeVec) ^ 2
        + (antipodalTetraDesign.atom 4 ⬝ᵥ probeVec) ^ 2 - probeVec ⬝ᵥ probeVec
        = (probeVec 0 - probeVec 1) ^ 2 + (probeVec 0 + probeVec 2) ^ 2
          + (probeVec 1 + probeVec 2) ^ 2 := by
      simp [antipodalTetraDesign, antipodalTetraAtom, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_two]
      ring
    rw [hform]
    positivity

/-- The tight direction of the dominating triple is the missing tetrahedron
direction, so the gap is singular and the triple is not strict. -/
theorem antipodalTetraDesign_tight_direction :
    (![(-1 : ℝ), -1, 1] : Fin 3 → ℝ) ⬝ᵥ
      ((subsetSum antipodalTetraDesign ({0, 2, 4} : Finset (Fin 6)) - 1)
        *ᵥ ![(-1 : ℝ), -1, 1]) = 0 := by
  rw [dotProduct_tripleGap_mulVec antipodalTetraDesign (by decide) (by decide) (by decide)]
  norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- **NO CARD-THREE SUBSET DOMINATES STRICTLY.**  Twelve triples read three
distinct directions and are tight, with Rayleigh value exactly zero at the
missing direction.  Eight triples read a direction twice and are rank
deficient, with Rayleigh value `-2` at the common normal.  Nine probes with
entries in `{-1, 0, 1}` cover all twenty. -/
theorem antipodalTetraDesign_not_posDef_cardThree
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ¬ (subsetSum antipodalTetraDesign selected - 1).PosDef := by
  have hmem : selected ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 6)) := by
    simp [Finset.mem_powersetCard, hcard]
  have hprobeNe : ∀ (probe : Fin 3 → ℝ) (slot : Fin 3), probe slot ≠ 0 → probe ≠ 0 := by
    intro probe slot hslot hzero
    exact hslot (by rw [hzero]; rfl)
  have hkill : ∀ (first second third : Fin 6) (probe : Fin 3 → ℝ),
      first ≠ second → first ≠ third → second ≠ third → probe ≠ 0 →
      (antipodalTetraDesign.atom first ⬝ᵥ probe) ^ 2
          + (antipodalTetraDesign.atom second ⬝ᵥ probe) ^ 2
          + (antipodalTetraDesign.atom third ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe ≤ 0 →
      ¬ (subsetSum antipodalTetraDesign
          ({first, second, third} : Finset (Fin 6)) - 1).PosDef := by
    intro first second third probe hfirstSecond hfirstThird hsecondThird hprobe hvalue
    refine not_posDef_of_dotProduct_mulVec_nonpos _ probe hprobe ?_
    rw [dotProduct_tripleGap_mulVec antipodalTetraDesign
      hfirstSecond hfirstThird hsecondThird]
    exact hvalue
  have hZeroOneNegOne : (![0, 1, -1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 1 (by norm_num)
  have hOneZeroNegOne : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneNegOneZero : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneOneNegOne : (![1, 1, -1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneNegOneOne : (![1, -1, 1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneNegOneNegOne : (![1, -1, -1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneOneZero : (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneZeroOne : (![1, 0, 1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  have hOneOneOne : (![1, 1, 1] : Fin 3 → ℝ) ≠ 0 := hprobeNe _ 0 (by norm_num)
  rcases cardThreeFinsetsOfSix_enumeration selected hmem with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h
  · exact hkill 0 1 2 ![0, 1, -1] (by decide) (by decide) (by decide) hZeroOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 1 3 ![0, 1, -1] (by decide) (by decide) (by decide) hZeroOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 1 4 ![1, 0, -1] (by decide) (by decide) (by decide) hOneZeroNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 1 5 ![1, -1, 0] (by decide) (by decide) (by decide) hOneNegOneZero (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 2 3 ![0, 1, -1] (by decide) (by decide) (by decide) hZeroOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 2 4 ![1, 1, -1] (by decide) (by decide) (by decide) hOneOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 2 5 ![1, -1, 1] (by decide) (by decide) (by decide) hOneNegOneOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 3 4 ![1, 1, -1] (by decide) (by decide) (by decide) hOneOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 3 5 ![1, -1, 1] (by decide) (by decide) (by decide) hOneNegOneOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 0 4 5 ![1, -1, -1] (by decide) (by decide) (by decide) hOneNegOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 2 3 ![0, 1, -1] (by decide) (by decide) (by decide) hZeroOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 2 4 ![1, 1, -1] (by decide) (by decide) (by decide) hOneOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 2 5 ![1, -1, 1] (by decide) (by decide) (by decide) hOneNegOneOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 3 4 ![1, 1, -1] (by decide) (by decide) (by decide) hOneOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 3 5 ![1, -1, 1] (by decide) (by decide) (by decide) hOneNegOneOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 1 4 5 ![1, -1, -1] (by decide) (by decide) (by decide) hOneNegOneNegOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 2 3 4 ![1, 1, 0] (by decide) (by decide) (by decide) hOneOneZero (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 2 3 5 ![1, 0, 1] (by decide) (by decide) (by decide) hOneZeroOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 2 4 5 ![1, 1, 1] (by decide) (by decide) (by decide) hOneOneOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])
  · exact hkill 3 4 5 ![1, 1, 1] (by decide) (by decide) (by decide) hOneOneOne (by
      norm_num [antipodalTetraDesign, antipodalTetraAtom, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_two])

/-- **THE WITNESS IS AN EXACT TIE.** -/
theorem antipodalTetraDesign_isTie : IsTie antipodalTetraDesign :=
  ⟨⟨({0, 2, 4} : Finset (Fin 6)), by decide, antipodalTetraDesign_dominates⟩,
    antipodalTetraDesign_not_posDef_cardThree⟩

/-! ## The refutation -/

/-- **A `(6,3)` TIE WITH SIX PAIRWISE DISTINCT ATOMS EXISTS.** -/
theorem exists_isTie_sixThree_atom_injective :
    ∃ design : WeightedDesign 6 3, IsTie design ∧ Function.Injective design.atom :=
  ⟨antipodalTetraDesign, antipodalTetraDesign_isTie, antipodalTetraDesign_atom_injective⟩

/-- **THE HYPOTHESIS OF `Gtz.heavyNeedleResidual_of_tie_repeats_an_atom` IS
FALSE.**  That theorem is therefore a door that cannot open, and the registry
axiom does NOT follow from it. -/
theorem not_forall_sixThree_isTie_repeats_an_atom :
    ¬ (∀ design : WeightedDesign 6 3, IsTie design →
        ∃ firstLabel secondLabel : Fin 6,
          firstLabel ≠ secondLabel ∧ design.atom firstLabel = design.atom secondLabel) := by
  intro hrepeat
  obtain ⟨firstLabel, secondLabel, hdistinct, hatomEq⟩ :=
    hrepeat antipodalTetraDesign antipodalTetraDesign_isTie
  exact hdistinct (antipodalTetraDesign_atom_injective hatomEq)

/-- **The general reason.**  A tie with a repeated NONZERO atom always yields a
second tie in which that same pair is distinct, because the sign flip at one
member of the pair fixes the tie and moves the atom. -/
theorem exists_isTie_atom_ne_of_isTie_of_atom_eq (D : WeightedDesign m k)
    (htie : IsTie D) {firstLabel secondLabel : Fin m} (hdistinct : firstLabel ≠ secondLabel)
    (hatomEq : D.atom firstLabel = D.atom secondLabel) (hne : D.atom secondLabel ≠ 0) :
    ∃ E : WeightedDesign m k, IsTie E ∧ E.atom firstLabel ≠ E.atom secondLabel := by
  refine ⟨negateAtom D secondLabel, (isTie_negateAtom_iff D secondLabel).mpr htie, ?_⟩
  rw [negateAtom_atom_other D hdistinct, negateAtom_atom_self, hatomEq]
  intro hcontra
  refine hne ?_
  funext slot
  have hslot := congrFun hcontra slot
  simp only [Pi.neg_apply] at hslot
  simp only [Pi.zero_apply]
  linarith

/-! ## The repair: two bridges to the same registry axiom -/

/-- **THE REPAIRED ROUTE, sign-blind form.**  If every `(6,3)` tie carries two
distinct labels with equal atom MATRICES, the registry axiom follows.  This
hypothesis is the sign-flip closure of the refuted one, so it is invariant
under the group that fixes `Gtz.IsTie`, and the witness above satisfies it. -/
theorem heavyNeedleResidual_of_tie_hasCloneMatrixPair
    (hclone : ∀ design : WeightedDesign 6 3, IsTie design →
      ∃ firstLabel secondLabel : Fin 6, firstLabel ≠ secondLabel ∧
        atomMatrix (design.atom firstLabel) = atomMatrix (design.atom secondLabel)) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  refine heavyNeedleResidual_of_pinnedStratumTieFree ?_
  intro design hlineFree _hoffConic htie
  obtain ⟨firstLabel, secondLabel, hdistinct, hEq⟩ := hclone design htie
  exact not_hasLinePattern_lineFree_of_atomMatrix_eq design hdistinct hEq hlineFree

/-- **THE REPAIRED ROUTE, weakest form.**  If every `(6,3)` tie has a parallel
pair, the registry axiom follows.  This is EXACTLY the conclusion that
`Gtz.sixThree_hasParallelPair_of_isTie_of_coplanarStress_unconditional`
delivers on the coplanar-stress branch, so the A1 route and the hinge route
now ask for one and the same statement. -/
theorem heavyNeedleResidual_of_tie_hasParallelPair
    (hparallel : ∀ design : WeightedDesign 6 3, IsTie design → HasParallelPair design) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  refine heavyNeedleResidual_of_pinnedStratumTieFree ?_
  intro design hlineFree _hoffConic htie
  exact not_hasLinePattern_lineFree_of_hasParallelPair design (hparallel design htie) hlineFree

/-! ## What a proof of the repaired hypothesis must consume

The repaired hypothesis is FALSE one size down, so no size-generic argument can
reach it.  This is not a measurement.  It is two landed theorems put together. -/

/-- **THE PARALLEL-PAIR HYPOTHESIS FAILS AT SIZE FOUR.**  `Gtz.tetraDesign` is a
certified tie (`Gtz.tetraDesign_isTie`) with no parallel pair
(`Gtz.tetraDesign_not_hasParallelPair`).  So any proof of the hypothesis of
`Gtz.heavyNeedleResidual_of_tie_hasParallelPair` must consume `m = 6`, and the
tetrahedron is the exact obstruction to a size-generic argument. -/
theorem not_forall_isTie_hasParallelPair_fourThree :
    ¬ (∀ design : WeightedDesign 4 3, IsTie design → HasParallelPair design) := fun hhinge =>
  tetraDesign_not_hasParallelPair (hhinge tetraDesign tetraDesign_isTie)

/-- **THE CLONE-MATRIX HYPOTHESIS FAILS AT SIZE FOUR TOO**, because a clone pair
is a parallel pair. -/
theorem not_forall_isTie_hasCloneMatrixPair_fourThree :
    ¬ (∀ design : WeightedDesign 4 3, IsTie design →
        ∃ firstLabel secondLabel : Fin 4, firstLabel ≠ secondLabel ∧
          atomMatrix (design.atom firstLabel) = atomMatrix (design.atom secondLabel)) := by
  intro hclone
  refine not_forall_isTie_hasParallelPair_fourThree fun design htie => ?_
  obtain ⟨firstLabel, secondLabel, hdistinct, hEq⟩ := hclone design htie
  exact hasParallelPair_of_atomMatrix_eq hdistinct hEq

/-! ## The witness against the two repaired hypotheses -/

/-- The witness has a parallel pair, at ratio `-1`. -/
theorem antipodalTetraDesign_hasParallelPair : HasParallelPair antipodalTetraDesign :=
  ⟨0, 1, -1, by decide, by rw [antipodalTetraDesign_atom_one]; module⟩

/-- The witness has two labels with equal atom matrices. -/
theorem antipodalTetraDesign_hasCloneMatrixPair :
    ∃ firstLabel secondLabel : Fin 6, firstLabel ≠ secondLabel ∧
      atomMatrix (antipodalTetraDesign.atom firstLabel)
        = atomMatrix (antipodalTetraDesign.atom secondLabel) :=
  ⟨0, 1, by decide, by rw [antipodalTetraDesign_atom_one, atomMatrix_neg]⟩

/-- **THE WITNESS DOES NOT ENTER THE ANTECEDENT REGION.**  It is line
degenerate, so it is not the line-free off-conic tie that
`Gtz.not_heavyNeedleResidual_iff_exists_lineFreeOffConicTie` asks for, and the
registry axiom is untouched by it. -/
theorem not_lineFree_antipodalTetraDesign :
    ¬ HasLinePattern antipodalTetraDesign
        (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  not_hasLinePattern_lineFree_of_hasParallelPair _ antipodalTetraDesign_hasParallelPair

/-- The witness carries a nonzero stress, so it is not stress-free either. -/
theorem not_isStressFree_antipodalTetraDesign :
    ¬ IsStressFreeDesign antipodalTetraDesign := by
  intro hstressFree
  have hstressNe : (![1, -1, 0, 0, 0, 0] : Fin 6 → ℝ) ≠ 0 := by
    intro hzero
    have hread : (1 : ℝ) = 0 := by simpa using congrFun hzero 0
    norm_num at hread
  refine hstressNe (hstressFree _ ?_)
  have hmatrixEq : atomMatrix (antipodalTetraDesign.atom 1)
      = atomMatrix (antipodalTetraDesign.atom 0) := by
    rw [antipodalTetraDesign_atom_one, atomMatrix_neg]
  rw [Fin.sum_univ_six]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [hmatrixEq]
  simp

end Gtz
