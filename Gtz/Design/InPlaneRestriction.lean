/-
# In-plane restriction, the one-line constraint algebra, and two anatomy witnesses

Three things live here.

The CONSTRAINT ALGEBRA (C0-C6) of the one-line stratum: polarized Parseval split
over a line set and its complement, the normal identity (free heights carry the
whole unit mass), the cross identity (free height-times-shadow readings cancel),
in-plane Parseval, the line part below the identity, the height/shadow split of
leverage, and heaviness bounding the shadow.

The IN-PLANE RESTRICTION: reading every atom against an orthonormal pair
spanning a plane gives a genuine `WeightedDesign size 2` with the SAME weights,
so rank-two GTZ -- a THEOREM in this tree (`Gtz.gtz_rank_two`) -- applies
verbatim and hands back a covering PAIR.  That pair's membership decides which
anatomy is available; it is not uniform across the stratum.

Two WITNESSES that make the non-uniformity concrete.  `narrowConeDesign` crams
the three line atoms into an in-plane cone: no line pair covers the plane, so
no two-line-plus-one-free subset dominates, and the free triple is the only
strict dominator.  `shadowLineDesign` crams the three FREE shadows near one
in-plane line: the free triple fails to dominate even weakly, no line pair
covers either, and the strict dominator is one line atom plus two free atoms.
Together they refute both uniform anatomy rules -- "always LLF" and "always
FFF" -- at heavy designs of the one-line stratum.
-/
import Gtz.Design.LineClassObstructions
import Gtz.Reduction.Reductions

set_option maxHeartbeats 4000000

namespace Gtz
open Matrix

/-! # The in-plane restriction is itself a weighted design of rank two

So the whole in-plane half of the one-line problem is an instance of
`Gtz.gtz_rank_two`, which is a THEOREM. -/

/-- Every Parseval entry of the restricted design is a basis pairing. -/
theorem weightedPairSum_eq_dotProduct {size : ℕ} (design : WeightedDesign size 3)
    (leftBasis rightBasis : Fin 3 → ℝ) :
    ∑ label, design.weight label
        * ((design.atom label ⬝ᵥ leftBasis) * (design.atom label ⬝ᵥ rightBasis))
      = leftBasis ⬝ᵥ rightBasis :=
  (dotProduct_eq_sum_weight_mul_pair design leftBasis rightBasis).symm

/-- **The in-plane restriction.**  Reading every atom against an orthonormal
pair spanning the plane gives a weighted design of rank TWO with the SAME
weights: the Parseval entries are exactly the basis pairings. -/
noncomputable def inPlaneRestriction {size : ℕ} (design : WeightedDesign size 3)
    (basisFirst basisSecond : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0) : WeightedDesign size 2 where
  atom := fun label =>
    ![design.atom label ⬝ᵥ basisFirst, design.atom label ⬝ᵥ basisSecond]
  weight := design.weight
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one
  isParseval := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
        Matrix.vecMulVec_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.one_apply_eq,
        Matrix.one_apply_ne, ne_eq, Fin.zero_eta, Fin.mk_one, Fin.reduceEq,
        not_false_eq_true]
    · rw [weightedPairSum_eq_dotProduct design basisFirst basisFirst, hfirstUnit]
    · rw [weightedPairSum_eq_dotProduct design basisFirst basisSecond, horth]
    · rw [weightedPairSum_eq_dotProduct design basisSecond basisFirst,
        dotProduct_comm, horth]
    · rw [weightedPairSum_eq_dotProduct design basisSecond basisSecond, hsecondUnit]

/-- **The in-plane dispatch theorem.**  On EVERY rank-three weighted design and
every orthonormal in-plane frame there is a PAIR of atoms whose readings cover
the whole plane.  Proof: the in-plane restriction is a rank-two weighted design,
and rank-two GTZ (`Gtz.gtz_rank_two`) is a theorem.

For the one-line stratum this says the covering pair is drawn from
`{three line atoms} union {three free shadows}` -- so the anatomy of the
strictly dominating triple is DICTATED by which pair rank-two GTZ returns, and
is NOT uniform across the stratum. -/
theorem exists_inPlane_dominating_pair {size : ℕ} (design : WeightedDesign size 3)
    (basisFirst basisSecond : Fin 3 → ℝ)
    (hfirstUnit : basisFirst ⬝ᵥ basisFirst = 1)
    (hsecondUnit : basisSecond ⬝ᵥ basisSecond = 1)
    (horth : basisFirst ⬝ᵥ basisSecond = 0) :
    ∃ pairFirst pairSecond : Fin size, pairFirst ≠ pairSecond ∧
      ∀ (alpha beta : ℝ),
        (alpha • basisFirst + beta • basisSecond)
            ⬝ᵥ (alpha • basisFirst + beta • basisSecond)
          ≤ (design.atom pairFirst ⬝ᵥ (alpha • basisFirst + beta • basisSecond)) ^ 2
            + (design.atom pairSecond
                ⬝ᵥ (alpha • basisFirst + beta • basisSecond)) ^ 2 := by
  classical
  obtain ⟨pair, hcard, hdominates⟩ :=
    gtz_rank_two size (inPlaneRestriction design basisFirst basisSecond
      hfirstUnit hsecondUnit horth)
  obtain ⟨pairFirst, pairSecond, hne, hpair⟩ := Finset.card_eq_two.mp hcard
  refine ⟨pairFirst, pairSecond, hne, fun alpha beta => ?_⟩
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 ![alpha, beta]
  rw [star_trivial, dominationGap_form, hpair, Finset.sum_insert (by simp [hne]),
    Finset.sum_singleton] at hform
  have hreading : ∀ label : Fin size,
      (inPlaneRestriction design basisFirst basisSecond hfirstUnit hsecondUnit horth).atom
          label ⬝ᵥ ![alpha, beta]
        = design.atom label ⬝ᵥ (alpha • basisFirst + beta • basisSecond) := by
    intro label
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [inPlaneRestriction, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, smul_eq_mul]
    ring
  have hcoeffNorm : (![alpha, beta] : Fin 2 → ℝ) ⬝ᵥ ![alpha, beta]
      = alpha ^ 2 + beta ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hlength : (alpha • basisFirst + beta • basisSecond)
      ⬝ᵥ (alpha • basisFirst + beta • basisSecond) = alpha ^ 2 + beta ^ 2 := by
    have hsym : basisSecond ⬝ᵥ basisFirst = 0 := by rw [dotProduct_comm]; exact horth
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hfirstUnit, hsecondUnit, horth, hsym]
    ring
  rw [hreading pairFirst, hreading pairSecond, hcoeffNorm] at hform
  rw [hlength]
  linarith

/-! ## R3 constraint algebra for the one-line stratum -/

/-- (C0) The polarized Parseval split over a line set and its complement. -/
theorem lineSplit_polarizedParseval {size rank : ℕ} (design : WeightedDesign size rank)
    (lineSet : Finset (Fin size)) (leftVec rightVec : Fin rank → ℝ) :
    (∑ lineLabel ∈ lineSet, design.weight lineLabel
        * ((design.atom lineLabel ⬝ᵥ leftVec) * (design.atom lineLabel ⬝ᵥ rightVec)))
      + (∑ freeLabel ∈ lineSetᶜ, design.weight freeLabel
        * ((design.atom freeLabel ⬝ᵥ leftVec) * (design.atom freeLabel ⬝ᵥ rightVec)))
      = leftVec ⬝ᵥ rightVec := by
  rw [Finset.sum_add_sum_compl lineSet
    (fun atomLabel => design.weight atomLabel
      * ((design.atom atomLabel ⬝ᵥ leftVec) * (design.atom atomLabel ⬝ᵥ rightVec)))]
  exact (dotProduct_eq_sum_weight_mul_pair design leftVec rightVec).symm

/-- **(C1) The normal identity.**  At a UNIT normal killed by every line atom the
free atoms' weighted squared heights sum to exactly one. -/
theorem oneLine_normalIdentity {size rank : ℕ} (design : WeightedDesign size rank)
    (lineSet : Finset (Fin size)) (unitNormal : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (horthogonal : ∀ lineLabel ∈ lineSet, design.atom lineLabel ⬝ᵥ unitNormal = 0) :
    ∑ freeLabel ∈ lineSetᶜ,
        design.weight freeLabel * (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 = 1 := by
  have hsplit := lineSplit_polarizedParseval design lineSet unitNormal unitNormal
  have hlineZero : (∑ lineLabel ∈ lineSet, design.weight lineLabel
      * ((design.atom lineLabel ⬝ᵥ unitNormal) * (design.atom lineLabel ⬝ᵥ unitNormal))) = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by rw [horthogonal lineLabel hmem]; ring
  rw [hlineZero, zero_add, hunit] at hsplit
  rw [← hsplit]
  exact Finset.sum_congr rfl fun freeLabel _ => by ring

/-- **(C2) The cross identity.**  Against any in-plane probe the free atoms'
weighted height-times-shadow readings CANCEL exactly. -/
theorem oneLine_crossIdentity {size rank : ℕ} (design : WeightedDesign size rank)
    (lineSet : Finset (Fin size)) (unitNormal probe : Fin rank → ℝ)
    (hprobeFlat : probe ⬝ᵥ unitNormal = 0)
    (horthogonal : ∀ lineLabel ∈ lineSet, design.atom lineLabel ⬝ᵥ unitNormal = 0) :
    ∑ freeLabel ∈ lineSetᶜ, design.weight freeLabel
        * ((design.atom freeLabel ⬝ᵥ unitNormal) * (design.atom freeLabel ⬝ᵥ probe)) = 0 := by
  have hsplit := lineSplit_polarizedParseval design lineSet unitNormal probe
  have hlineZero : (∑ lineLabel ∈ lineSet, design.weight lineLabel
      * ((design.atom lineLabel ⬝ᵥ unitNormal) * (design.atom lineLabel ⬝ᵥ probe))) = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by rw [horthogonal lineLabel hmem]; ring
  have hnormalProbe : unitNormal ⬝ᵥ probe = 0 := by
    rw [dotProduct_comm]; exact hprobeFlat
  rw [hlineZero, zero_add, hnormalProbe] at hsplit
  exact hsplit

/-- **(C3) The in-plane Parseval identity.**  Along in-plane probes the line
atoms and the free atoms' SHADOWS jointly resolve the in-plane identity; the
heights are invisible. -/
theorem oneLine_inPlaneParseval {size rank : ℕ} (design : WeightedDesign size rank)
    (lineSet : Finset (Fin size)) (leftProbe rightProbe : Fin rank → ℝ) :
    (∑ lineLabel ∈ lineSet, design.weight lineLabel
        * ((design.atom lineLabel ⬝ᵥ leftProbe) * (design.atom lineLabel ⬝ᵥ rightProbe)))
      + (∑ freeLabel ∈ lineSetᶜ, design.weight freeLabel
        * ((design.atom freeLabel ⬝ᵥ leftProbe) * (design.atom freeLabel ⬝ᵥ rightProbe)))
      = leftProbe ⬝ᵥ rightProbe :=
  lineSplit_polarizedParseval design lineSet leftProbe rightProbe

/-- **(C4) The line part is Loewner-BELOW the identity**, in every direction:
the weighted line mass along any probe never reaches the probe's own square. -/
theorem oneLine_linePart_le_identity {size rank : ℕ} (design : WeightedDesign size rank)
    (lineSet : Finset (Fin size)) (probe : Fin rank → ℝ) :
    ∑ lineLabel ∈ lineSet, design.weight lineLabel
        * (design.atom lineLabel ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
  have hsplit := lineSplit_polarizedParseval design lineSet probe probe
  have hfreeNonneg : 0 ≤ ∑ freeLabel ∈ lineSetᶜ, design.weight freeLabel
      * ((design.atom freeLabel ⬝ᵥ probe) * (design.atom freeLabel ⬝ᵥ probe)) :=
    Finset.sum_nonneg fun freeLabel _ =>
      mul_nonneg (design.weight_pos freeLabel).le (mul_self_nonneg _)
  have hrewrite : (∑ lineLabel ∈ lineSet, design.weight lineLabel
        * ((design.atom lineLabel ⬝ᵥ probe) * (design.atom lineLabel ⬝ᵥ probe)))
      = ∑ lineLabel ∈ lineSet, design.weight lineLabel
        * (design.atom lineLabel ⬝ᵥ probe) ^ 2 :=
    Finset.sum_congr rfl fun lineLabel _ => by ring
  rw [hrewrite] at hsplit
  linarith

/-- **(C5) The height/shadow split of leverage.**  At a unit normal the leverage
of an atom is its squared height plus its squared shadow. -/
theorem leverage_split_at_unitNormal {rank : ℕ} (atomVec unitNormal : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) :
    leverageOf atomVec
      = (atomVec ⬝ᵥ unitNormal) ^ 2
        + (atomVec - (atomVec ⬝ᵥ unitNormal) • unitNormal)
            ⬝ᵥ (atomVec - (atomVec ⬝ᵥ unitNormal) • unitNormal) := by
  have hexpand : (atomVec - (atomVec ⬝ᵥ unitNormal) • unitNormal)
        ⬝ᵥ (atomVec - (atomVec ⬝ᵥ unitNormal) • unitNormal)
      = atomVec ⬝ᵥ atomVec - (atomVec ⬝ᵥ unitNormal) ^ 2 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hunit, dotProduct_comm unitNormal atomVec]
    ring
  rw [hexpand, leverageOf_eq_dotProduct]
  ring

/-- **(C6) Heaviness bounds the shadow from below.**  A heavy atom whose height
is short has a long shadow. -/
theorem heavy_shadow_lower_bound {rank : ℕ} (atomVec unitNormal : Fin rank → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (hheavy : 1 ≤ leverageOf atomVec) :
    1 - (atomVec ⬝ᵥ unitNormal) ^ 2
      ≤ (atomVec - (atomVec ⬝ᵥ unitNormal) • unitNormal)
          ⬝ᵥ (atomVec - (atomVec ⬝ᵥ unitNormal) • unitNormal) := by
  have hsplit := leverage_split_at_unitNormal atomVec unitNormal hunit
  linarith

/-! ## The LLF no-go: a strictly dominating two-line-plus-one-free triple forces
the LINE PAIR ALONE to strictly dominate inside the plane. -/

/-- **(C7) The LLF necessity lemma.**  If a subset consisting of two atoms
invisible along the normal plus one atom with nonzero height has a POSITIVE
DEFINITE gap, then the two invisible atoms alone strictly over-cover every
in-plane probe -- with the free atom's shadow reading as explicit slack.  The
probe is tilted out of the plane by exactly the amount that annihilates the free
atom, which the two flat atoms cannot see. -/
theorem llf_posDef_forces_linePair_inPlane_domination {size : ℕ}
    (design : WeightedDesign size 3)
    (lineFirst lineSecond freeLabel : Fin size) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstFlat : design.atom lineFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom lineSecond ⬝ᵥ unitNormal = 0)
    (hheightNe : design.atom freeLabel ⬝ᵥ unitNormal ≠ 0)
    (hdistinctFirstSecond : lineFirst ≠ lineSecond)
    (hdistinctFirstFree : lineFirst ≠ freeLabel)
    (hdistinctSecondFree : lineSecond ≠ freeLabel)
    (hposDef : (subsetSum design
      ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)) - 1).PosDef)
    (probe : Fin 3 → ℝ) (hprobeFlat : probe ⬝ᵥ unitNormal = 0) (hprobeNe : probe ≠ 0) :
    probe ⬝ᵥ probe
        + (design.atom freeLabel ⬝ᵥ probe) ^ 2
            / (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
      < (design.atom lineFirst ⬝ᵥ probe) ^ 2
        + (design.atom lineSecond ⬝ᵥ probe) ^ 2 := by
  set tilt : ℝ := -(design.atom freeLabel ⬝ᵥ probe)
    / (design.atom freeLabel ⬝ᵥ unitNormal) with htilt
  set tilted : Fin 3 → ℝ := probe + tilt • unitNormal with htilted
  have hnormalProbe : unitNormal ⬝ᵥ probe = 0 := by
    rw [dotProduct_comm]; exact hprobeFlat
  have htiltedNe : tilted ≠ 0 := by
    intro hzero
    have hsum : probe + tilt • unitNormal = 0 := by rw [← htilted]; exact hzero
    have happly := congrArg (fun testVec : Fin 3 → ℝ => testVec ⬝ᵥ probe) hsum
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hnormalProbe,
      mul_zero, add_zero, zero_dotProduct] at happly
    exact hprobeNe (dotProduct_self_eq_zero.mp happly)
  have hfreeKilled : design.atom freeLabel ⬝ᵥ tilted = 0 := by
    rw [htilted, dotProduct_add, dotProduct_smul, smul_eq_mul, htilt,
      div_mul_cancel₀ _ hheightNe]
    ring
  have hfirstSame : design.atom lineFirst ⬝ᵥ tilted = design.atom lineFirst ⬝ᵥ probe := by
    rw [htilted, dotProduct_add, dotProduct_smul, smul_eq_mul, hfirstFlat, mul_zero,
      add_zero]
  have hsecondSame : design.atom lineSecond ⬝ᵥ tilted = design.atom lineSecond ⬝ᵥ probe := by
    rw [htilted, dotProduct_add, dotProduct_smul, smul_eq_mul, hsecondFlat, mul_zero,
      add_zero]
  have htiltedNorm : tilted ⬝ᵥ tilted = probe ⬝ᵥ probe + tilt ^ 2 := by
    rw [htilted]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hprobeFlat, hnormalProbe, hunit]
    ring
  have hvalue := hposDef.dotProduct_mulVec_pos htiltedNe
  rw [star_trivial, dominationGap_form] at hvalue
  have hsumThree : ∑ selectedLabel ∈
      ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)),
        (design.atom selectedLabel ⬝ᵥ tilted) ^ 2
      = (design.atom lineFirst ⬝ᵥ tilted) ^ 2
        + (design.atom lineSecond ⬝ᵥ tilted) ^ 2
        + (design.atom freeLabel ⬝ᵥ tilted) ^ 2 := by
    rw [Finset.sum_insert (by simp [hdistinctFirstSecond, hdistinctFirstFree]),
      Finset.sum_insert (by simp [hdistinctSecondFree]), Finset.sum_singleton, add_assoc]
  rw [hsumThree, hfirstSame, hsecondSame, hfreeKilled, htiltedNorm] at hvalue
  have htiltSq : tilt ^ 2
      = (design.atom freeLabel ⬝ᵥ probe) ^ 2
        / (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
    rw [htilt, div_pow, neg_sq]
  rw [htiltSq] at hvalue
  linarith

/-- **(C8) The contrapositive kill.**  A single in-plane probe on which the line
pair fails to strictly over-cover refutes EVERY two-line-plus-one-free triple
built on that pair. -/
theorem llf_not_posDef_of_linePair_inPlane_failure {size : ℕ}
    (design : WeightedDesign size 3)
    (lineFirst lineSecond freeLabel : Fin size) (unitNormal : Fin 3 → ℝ)
    (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hfirstFlat : design.atom lineFirst ⬝ᵥ unitNormal = 0)
    (hsecondFlat : design.atom lineSecond ⬝ᵥ unitNormal = 0)
    (hheightNe : design.atom freeLabel ⬝ᵥ unitNormal ≠ 0)
    (hdistinctFirstSecond : lineFirst ≠ lineSecond)
    (hdistinctFirstFree : lineFirst ≠ freeLabel)
    (hdistinctSecondFree : lineSecond ≠ freeLabel)
    (probe : Fin 3 → ℝ) (hprobeFlat : probe ⬝ᵥ unitNormal = 0) (hprobeNe : probe ≠ 0)
    (hfailure : (design.atom lineFirst ⬝ᵥ probe) ^ 2
      + (design.atom lineSecond ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe) :
    ¬ (subsetSum design
        ({lineFirst, lineSecond, freeLabel} : Finset (Fin size)) - 1).PosDef := by
  intro hposDef
  have hstrict := llf_posDef_forces_linePair_inPlane_domination design lineFirst
    lineSecond freeLabel unitNormal hunit hfirstFlat hsecondFlat hheightNe
    hdistinctFirstSecond hdistinctFirstFree hdistinctSecondFree hposDef probe
    hprobeFlat hprobeNe
  have hslackNonneg : 0 ≤ (design.atom freeLabel ⬝ᵥ probe) ^ 2
      / (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith


/-! # WITNESS A -- the narrow-cone one-line design

Three line atoms crammed into an in-plane cone of half-angle `arctan (1/2)`,
heavy, exact Parseval, exact one-line pattern.  Purpose: kill the LLF anatomy. -/

noncomputable def narrowConeAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1, 1/2, 0]
  | 1 => ![1, 0, 0]
  | 2 => ![1, -1/2, 0]
  | 3 => ![1, 0, 2]
  | 4 => ![1, 8/3, -2]
  | 5 => ![1, -8/3, -2]

noncomputable def narrowConeWeight : Fin 6 → ℝ
  | 0 => 2/9
  | 1 => 11/36
  | 2 => 2/9
  | 3 => 1/8
  | 4 => 1/16
  | 5 => 1/16

noncomputable def narrowConeDesign : WeightedDesign 6 3 where
  atom := narrowConeAtom
  weight := narrowConeWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [narrowConeWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [narrowConeWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [narrowConeAtom, narrowConeWeight, atomMatrix] <;> norm_num

theorem narrowConeDesign_hasLinePattern :
    HasLinePattern narrowConeDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, narrowConeDesign,
            narrowConeAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, narrowConeDesign,
            narrowConeAtom, Matrix.cons_val_two])
          (by decide)

theorem narrowConeDesign_heavy (label : Fin 6) :
    1 ≤ leverageOf (narrowConeDesign.atom label) := by
  fin_cases label <;>
    norm_num [leverageOf, Fin.sum_univ_three, narrowConeDesign, narrowConeAtom,
      Matrix.cons_val_two]

/-- The line normal is the third coordinate direction. -/
def narrowConeNormal : Fin 3 → ℝ := ![0, 0, 1]

theorem narrowConeNormal_unit : narrowConeNormal ⬝ᵥ narrowConeNormal = 1 := by
  norm_num [narrowConeNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem narrowCone_lineAtoms_flat (lineLabel : Fin 6)
    (hmem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6))) :
    narrowConeDesign.atom lineLabel ⬝ᵥ narrowConeNormal = 0 := by
  fin_cases hmem <;>
    norm_num [narrowConeDesign, narrowConeAtom, narrowConeNormal, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two]

theorem narrowCone_freeAtoms_height_ne_zero (freeLabel : Fin 6)
    (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    narrowConeDesign.atom freeLabel ⬝ᵥ narrowConeNormal ≠ 0 := by
  fin_cases hmem <;>
    norm_num [narrowConeDesign, narrowConeAtom, narrowConeNormal, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two]

/-! ## The three line pairs all FAIL to cover the plane -/

/-- Probe killing atom `0`: the pair `{0,1}` reads only `1` against squared
length `5`. -/
theorem narrowCone_pairZeroOne_fails :
    (narrowConeDesign.atom 0 ⬝ᵥ ![1, -2, 0]) ^ 2
        + (narrowConeDesign.atom 1 ⬝ᵥ ![1, -2, 0]) ^ 2
      ≤ (![1, -2, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, -2, 0] := by
  norm_num [narrowConeDesign, narrowConeAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- Probe killing atom `2`: the pair `{1,2}` reads only `1` against `5`. -/
theorem narrowCone_pairOneTwo_fails :
    (narrowConeDesign.atom 1 ⬝ᵥ ![1, 2, 0]) ^ 2
        + (narrowConeDesign.atom 2 ⬝ᵥ ![1, 2, 0]) ^ 2
      ≤ (![1, 2, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 2, 0] := by
  norm_num [narrowConeDesign, narrowConeAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- The transverse in-plane probe: the pair `{0,2}` reads `1/2` against `1`.
This is the narrowness of the cone made numerical. -/
theorem narrowCone_pairZeroTwo_fails :
    (narrowConeDesign.atom 0 ⬝ᵥ ![0, 1, 0]) ^ 2
        + (narrowConeDesign.atom 2 ⬝ᵥ ![0, 1, 0]) ^ 2
      ≤ (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ ![0, 1, 0] := by
  norm_num [narrowConeDesign, narrowConeAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-- The weighted line mass in the transverse in-plane direction is only `1/9`:
the whole in-plane identity there is carried by the free atoms' shadows. -/
theorem narrowCone_lineMass_transverse :
    ∑ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)), narrowConeDesign.weight lineLabel
        * (narrowConeDesign.atom lineLabel ⬝ᵥ ![0, 1, 0]) ^ 2 = 1/9 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [narrowConeDesign, narrowConeAtom, narrowConeWeight, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]

/-! ## The free triple DOES strictly dominate -/

theorem narrowCone_freeTripleGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum narrowConeDesign {3, 4, 5} - 1) *ᵥ vecArg)
      = 2 * (vecArg 0 - vecArg 2) ^ 2 + 9 * vecArg 2 ^ 2
        + (119/9) * vecArg 1 ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [narrowConeDesign, narrowConeAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem narrowCone_freeTripleGap_posDef :
    (subsetSum narrowConeDesign {3, 4, 5} - 1).PosDef := by
  have squarePos : ∀ realVal : ℝ, realVal ≠ 0 → 0 < realVal ^ 2 := fun realVal hne =>
    lt_of_le_of_ne (sq_nonneg realVal) (Ne.symm (pow_ne_zero 2 hne))
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact ((Matrix.posSemidef_sum ({3, 4, 5} : Finset (Fin 6)) fun freeLabel _ =>
      posSemidef_atomMatrix (narrowConeDesign.atom freeLabel)).1).sub Matrix.isHermitian_one
  · rw [star_trivial, narrowCone_freeTripleGap_form]
    have hcoord : vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by
        funext coordIndex
        fin_cases coordIndex <;> simp [hall.1, hall.2.1, hall.2.2])
    rcases hcoord with hfirst | hsecond | hthird
    · rcases eq_or_ne (vecArg 2) 0 with hzero | hnonzero
      · have hdiff : vecArg 0 - vecArg 2 ≠ 0 := by rw [hzero, sub_zero]; exact hfirst
        nlinarith [squarePos _ hdiff, sq_nonneg (vecArg 1), sq_nonneg (vecArg 2)]
      · nlinarith [squarePos _ hnonzero, sq_nonneg (vecArg 1),
          sq_nonneg (vecArg 0 - vecArg 2)]
    · nlinarith [squarePos _ hsecond, sq_nonneg (vecArg 2),
        sq_nonneg (vecArg 0 - vecArg 2)]
    · nlinarith [squarePos _ hthird, sq_nonneg (vecArg 1),
        sq_nonneg (vecArg 0 - vecArg 2)]


/-! # WITNESS B -- the collinear-shadow one-line design

The three free atoms' in-plane shadows are crammed near one in-plane line, so
the FREE TRIPLE does not even weakly dominate; the line atoms are long in the
transverse in-plane direction but short along the shadows' direction, so no
line PAIR covers the plane either.  The strictly dominating triple here is
one line atom plus two free atoms. -/

noncomputable def shadowLineAtom : Fin 6 → (Fin 3 → ℝ)
  | 0 => ![1/2, 2, 0]
  | 1 => ![0, 2, 0]
  | 2 => ![-1/2, 2, 0]
  | 3 => ![22/15, 1/2, 1]
  | 4 => ![-22/15, 1/2, 1]
  | 5 => ![0, -1/2, 5/4]

noncomputable def shadowLineWeight : Fin 6 → ℝ
  | 0 => 178/2025
  | 1 => 49/2025
  | 2 => 178/2025
  | 3 => 2/9
  | 4 => 2/9
  | 5 => 16/45

noncomputable def shadowLineDesign : WeightedDesign 6 3 where
  atom := shadowLineAtom
  weight := shadowLineWeight
  weight_pos := by intro label; fin_cases label <;> norm_num [shadowLineWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [shadowLineWeight]
  isParseval := by
    rw [Fin.sum_univ_six]
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;>
      simp [shadowLineAtom, shadowLineWeight, atomMatrix] <;> norm_num

theorem shadowLineDesign_hasLinePattern :
    HasLinePattern shadowLineDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    first
      | exact absurd rfl hleftMid
      | exact absurd rfl hleftRight
      | exact absurd rfl hmidRight
      | exact iff_of_false
          (by norm_num [atomBracket, tripleBracket_eq, shadowLineDesign,
            shadowLineAtom, Matrix.cons_val_two])
          (by decide)
      | exact iff_of_true
          (by norm_num [atomBracket, tripleBracket_eq, shadowLineDesign,
            shadowLineAtom, Matrix.cons_val_two])
          (by decide)

theorem shadowLineDesign_heavy (label : Fin 6) :
    1 ≤ leverageOf (shadowLineDesign.atom label) := by
  fin_cases label <;>
    norm_num [leverageOf, Fin.sum_univ_three, shadowLineDesign, shadowLineAtom,
      Matrix.cons_val_two]

def shadowLineNormal : Fin 3 → ℝ := ![0, 0, 1]

theorem shadowLineNormal_unit : shadowLineNormal ⬝ᵥ shadowLineNormal = 1 := by
  norm_num [shadowLineNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem shadowLine_lineAtoms_flat (lineLabel : Fin 6)
    (hmem : lineLabel ∈ ({0, 1, 2} : Finset (Fin 6))) :
    shadowLineDesign.atom lineLabel ⬝ᵥ shadowLineNormal = 0 := by
  fin_cases hmem <;>
    norm_num [shadowLineDesign, shadowLineAtom, shadowLineNormal, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two]

theorem shadowLine_freeAtoms_height_ne_zero (freeLabel : Fin 6)
    (hmem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6))) :
    shadowLineDesign.atom freeLabel ⬝ᵥ shadowLineNormal ≠ 0 := by
  fin_cases hmem <;>
    norm_num [shadowLineDesign, shadowLineAtom, shadowLineNormal, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two]

/-! ## The FREE TRIPLE does not even weakly dominate -/

/-- Along the transverse in-plane direction the three free shadows read only
`3/4` against squared length `1`. -/
theorem shadowLine_freeTriple_gap_negative :
    (![0, 1, 0] : Fin 3 → ℝ)
        ⬝ᵥ ((subsetSum shadowLineDesign {3, 4, 5} - 1) *ᵥ ![0, 1, 0]) = -(1/4) := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [shadowLineDesign, shadowLineAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem shadowLine_freeTriple_not_dominates :
    ¬ Dominates shadowLineDesign ({3, 4, 5} : Finset (Fin 6)) := by
  intro hdominates
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 ![0, 1, 0]
  rw [star_trivial, shadowLine_freeTriple_gap_negative] at hnonneg
  norm_num at hnonneg

/-! ## No line PAIR covers the plane either -/

theorem shadowLine_pairZeroOne_fails :
    (shadowLineDesign.atom 0 ⬝ᵥ ![1, 0, 0]) ^ 2
        + (shadowLineDesign.atom 1 ⬝ᵥ ![1, 0, 0]) ^ 2
      ≤ (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] := by
  norm_num [shadowLineDesign, shadowLineAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem shadowLine_pairZeroTwo_fails :
    (shadowLineDesign.atom 0 ⬝ᵥ ![1, 0, 0]) ^ 2
        + (shadowLineDesign.atom 2 ⬝ᵥ ![1, 0, 0]) ^ 2
      ≤ (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] := by
  norm_num [shadowLineDesign, shadowLineAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

theorem shadowLine_pairOneTwo_fails :
    (shadowLineDesign.atom 1 ⬝ᵥ ![1, 0, 0]) ^ 2
        + (shadowLineDesign.atom 2 ⬝ᵥ ![1, 0, 0]) ^ 2
      ≤ (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ ![1, 0, 0] := by
  norm_num [shadowLineDesign, shadowLineAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]

/-! ## The answer here is LINE + FREE + FREE -/

theorem shadowLine_mixedTripleGap_form (vecArg : Fin 3 → ℝ) :
    vecArg ⬝ᵥ ((subsetSum shadowLineDesign {1, 3, 4} - 1) *ᵥ vecArg)
      = (743/225) * vecArg 0 ^ 2 + (5/2) * vecArg 1 ^ 2
        + (vecArg 1 + vecArg 2) ^ 2 := by
  rw [dominationGap_form, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [shadowLineDesign, shadowLineAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two]
  ring

theorem shadowLine_mixedTripleGap_posDef :
    (subsetSum shadowLineDesign {1, 3, 4} - 1).PosDef := by
  have squarePos : ∀ realVal : ℝ, realVal ≠ 0 → 0 < realVal ^ 2 := fun realVal hne =>
    lt_of_le_of_ne (sq_nonneg realVal) (Ne.symm (pow_ne_zero 2 hne))
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun vecArg hne => ?_⟩
  · exact ((Matrix.posSemidef_sum ({1, 3, 4} : Finset (Fin 6)) fun selectedLabel _ =>
      posSemidef_atomMatrix (shadowLineDesign.atom selectedLabel)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, shadowLine_mixedTripleGap_form]
    have hcoord : vecArg 0 ≠ 0 ∨ vecArg 1 ≠ 0 ∨ vecArg 2 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (by
        funext coordIndex
        fin_cases coordIndex <;> simp [hall.1, hall.2.1, hall.2.2])
    rcases hcoord with hfirst | hsecond | hthird
    · nlinarith [squarePos _ hfirst, sq_nonneg (vecArg 1),
        sq_nonneg (vecArg 1 + vecArg 2)]
    · nlinarith [squarePos _ hsecond, sq_nonneg (vecArg 0),
        sq_nonneg (vecArg 1 + vecArg 2)]
    · rcases eq_or_ne (vecArg 1) 0 with hzero | hnonzero
      · have hsum : vecArg 1 + vecArg 2 ≠ 0 := by rw [hzero, zero_add]; exact hthird
        nlinarith [squarePos _ hsum, sq_nonneg (vecArg 0), sq_nonneg (vecArg 1)]
      · nlinarith [squarePos _ hnonzero, sq_nonneg (vecArg 0),
          sq_nonneg (vecArg 1 + vecArg 2)]


/-! # THE COMPOSITE KILLS -/

theorem narrowCone_probeCross_flat :
    (![1, -2, 0] : Fin 3 → ℝ) ⬝ᵥ narrowConeNormal = 0 := by
  norm_num [narrowConeNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem narrowCone_probeCross_ne : (![1, -2, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero 0
  simp at hcoord

theorem narrowCone_probeTransverse_flat :
    (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ narrowConeNormal = 0 := by
  norm_num [narrowConeNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem narrowCone_probeTransverse_ne : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero 1
  simp at hcoord

theorem narrowCone_probeSecond_flat :
    (![1, 2, 0] : Fin 3 → ℝ) ⬝ᵥ narrowConeNormal = 0 := by
  norm_num [narrowConeNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem narrowCone_probeSecond_ne : (![1, 2, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero 0
  simp at hcoord

/-- **WITNESS A KILLS THE LLF ANATOMY.**  No subset made of two line atoms and
one free atom strictly dominates, for ANY choice of the two line atoms and ANY
choice of the free atom. -/
theorem narrowCone_no_llf_posDef (lineFirst lineSecond freeLabel : Fin 6)
    (hfirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hsecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfreeMem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hdistinct : lineFirst ≠ lineSecond) :
    ¬ (subsetSum narrowConeDesign
        ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) - 1).PosDef := by
  have hheight := narrowCone_freeAtoms_height_ne_zero freeLabel hfreeMem
  have hfirstFree : lineFirst ≠ freeLabel := by
    fin_cases hfirstMem <;> fin_cases hfreeMem <;> decide
  have hsecondFree : lineSecond ≠ freeLabel := by
    fin_cases hsecondMem <;> fin_cases hfreeMem <;> decide
  have hflatFirst := narrowCone_lineAtoms_flat lineFirst hfirstMem
  have hflatSecond := narrowCone_lineAtoms_flat lineSecond hsecondMem
  fin_cases hfirstMem <;> fin_cases hsecondMem
  · exact absurd rfl hdistinct
  · exact llf_not_posDef_of_linePair_inPlane_failure narrowConeDesign 0 1 freeLabel
      narrowConeNormal narrowConeNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, -2, 0] narrowCone_probeCross_flat
      narrowCone_probeCross_ne narrowCone_pairZeroOne_fails
  · exact llf_not_posDef_of_linePair_inPlane_failure narrowConeDesign 0 2 freeLabel
      narrowConeNormal narrowConeNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![0, 1, 0] narrowCone_probeTransverse_flat
      narrowCone_probeTransverse_ne narrowCone_pairZeroTwo_fails
  · exact llf_not_posDef_of_linePair_inPlane_failure narrowConeDesign 1 0 freeLabel
      narrowConeNormal narrowConeNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, -2, 0] narrowCone_probeCross_flat
      narrowCone_probeCross_ne (by linarith [narrowCone_pairZeroOne_fails])
  · exact absurd rfl hdistinct
  · exact llf_not_posDef_of_linePair_inPlane_failure narrowConeDesign 1 2 freeLabel
      narrowConeNormal narrowConeNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 2, 0] narrowCone_probeSecond_flat
      narrowCone_probeSecond_ne narrowCone_pairOneTwo_fails
  · exact llf_not_posDef_of_linePair_inPlane_failure narrowConeDesign 2 0 freeLabel
      narrowConeNormal narrowConeNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![0, 1, 0] narrowCone_probeTransverse_flat
      narrowCone_probeTransverse_ne (by linarith [narrowCone_pairZeroTwo_fails])
  · exact llf_not_posDef_of_linePair_inPlane_failure narrowConeDesign 2 1 freeLabel
      narrowConeNormal narrowConeNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 2, 0] narrowCone_probeSecond_flat
      narrowCone_probeSecond_ne (by linarith [narrowCone_pairOneTwo_fails])
  · exact absurd rfl hdistinct

theorem shadowLine_probeShadow_flat :
    (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ shadowLineNormal = 0 := by
  norm_num [shadowLineNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]

theorem shadowLine_probeShadow_ne : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero 0
  simp at hcoord

/-- **WITNESS B KILLS THE LLF ANATOMY TOO** -- and here the free triple is dead
as well, so the strictly dominating triple must be LINE + FREE + FREE. -/
theorem shadowLine_no_llf_posDef (lineFirst lineSecond freeLabel : Fin 6)
    (hfirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hsecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hfreeMem : freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hdistinct : lineFirst ≠ lineSecond) :
    ¬ (subsetSum shadowLineDesign
        ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) - 1).PosDef := by
  have hheight := shadowLine_freeAtoms_height_ne_zero freeLabel hfreeMem
  have hfirstFree : lineFirst ≠ freeLabel := by
    fin_cases hfirstMem <;> fin_cases hfreeMem <;> decide
  have hsecondFree : lineSecond ≠ freeLabel := by
    fin_cases hsecondMem <;> fin_cases hfreeMem <;> decide
  have hflatFirst := shadowLine_lineAtoms_flat lineFirst hfirstMem
  have hflatSecond := shadowLine_lineAtoms_flat lineSecond hsecondMem
  fin_cases hfirstMem <;> fin_cases hsecondMem
  · exact absurd rfl hdistinct
  · exact llf_not_posDef_of_linePair_inPlane_failure shadowLineDesign 0 1 freeLabel
      shadowLineNormal shadowLineNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 0, 0] shadowLine_probeShadow_flat
      shadowLine_probeShadow_ne shadowLine_pairZeroOne_fails
  · exact llf_not_posDef_of_linePair_inPlane_failure shadowLineDesign 0 2 freeLabel
      shadowLineNormal shadowLineNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 0, 0] shadowLine_probeShadow_flat
      shadowLine_probeShadow_ne shadowLine_pairZeroTwo_fails
  · exact llf_not_posDef_of_linePair_inPlane_failure shadowLineDesign 1 0 freeLabel
      shadowLineNormal shadowLineNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 0, 0] shadowLine_probeShadow_flat
      shadowLine_probeShadow_ne (by linarith [shadowLine_pairZeroOne_fails])
  · exact absurd rfl hdistinct
  · exact llf_not_posDef_of_linePair_inPlane_failure shadowLineDesign 1 2 freeLabel
      shadowLineNormal shadowLineNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 0, 0] shadowLine_probeShadow_flat
      shadowLine_probeShadow_ne shadowLine_pairOneTwo_fails
  · exact llf_not_posDef_of_linePair_inPlane_failure shadowLineDesign 2 0 freeLabel
      shadowLineNormal shadowLineNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 0, 0] shadowLine_probeShadow_flat
      shadowLine_probeShadow_ne (by linarith [shadowLine_pairZeroTwo_fails])
  · exact llf_not_posDef_of_linePair_inPlane_failure shadowLineDesign 2 1 freeLabel
      shadowLineNormal shadowLineNormal_unit hflatFirst hflatSecond hheight
      hdistinct hfirstFree hsecondFree ![1, 0, 0] shadowLine_probeShadow_flat
      shadowLine_probeShadow_ne (by linarith [shadowLine_pairOneTwo_fails])
  · exact absurd rfl hdistinct

/-! ## The two headline refutations, packaged -/

/-- **"Always pick two line atoms plus one free atom" is REFUTED**, at a heavy
one-line design with a strictly dominating triple. -/
theorem refutes_uniform_llf_rule :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
      ∧ (∃ selected : Finset (Fin 6), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef)
      ∧ (∀ lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)),
          ∀ lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
          ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), lineFirst ≠ lineSecond →
            ¬ (subsetSum design
              ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) - 1).PosDef) :=
  ⟨narrowConeDesign, narrowConeDesign_hasLinePattern, narrowConeDesign_heavy,
    ⟨{3, 4, 5}, by decide, narrowCone_freeTripleGap_posDef⟩,
    fun lineFirst hfirst lineSecond hsecond freeLabel hfree hdistinct =>
      narrowCone_no_llf_posDef lineFirst lineSecond freeLabel hfirst hsecond hfree
        hdistinct⟩

/-- **"Always pick the free triple" is REFUTED** -- and so is LLF at the same
design, so the only surviving anatomy there is LINE + FREE + FREE. -/
theorem refutes_uniform_fff_rule :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
      ∧ ¬ Dominates design ({3, 4, 5} : Finset (Fin 6))
      ∧ (∀ lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)),
          ∀ lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
          ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)), lineFirst ≠ lineSecond →
            ¬ (subsetSum design
              ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) - 1).PosDef)
      ∧ (subsetSum design ({1, 3, 4} : Finset (Fin 6)) - 1).PosDef :=
  ⟨shadowLineDesign, shadowLineDesign_hasLinePattern, shadowLineDesign_heavy,
    shadowLine_freeTriple_not_dominates,
    (fun lineFirst hfirst lineSecond hsecond freeLabel hfree hdistinct =>
      shadowLine_no_llf_posDef lineFirst lineSecond freeLabel hfirst hsecond hfree
        hdistinct),
    shadowLine_mixedTripleGap_posDef⟩

end Gtz
