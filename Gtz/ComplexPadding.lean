/-
# Complex weighted (6,3) is FALSE: the padded SIC

The first genuinely open real case is complex-false, in the kernel. The
construction pads the SIC refutation of (4,2) up one rank: scale the four SIC
atoms by `√(10/9)` at weights `9/40`, embed them in ℂ³ with third coordinate
zero, and add two antipodal spike atoms `±√10·e₂` at weights `1/20`. The six
weights sum to one and Parseval holds blockwise. No 3-subset dominates:

* three old atoms — every old atom is flat in the third coordinate, so the
  excess at `e₂` is `−1`;
* both spikes and one old atom — the top-left 2×2 block of the excess is a
  RANK-ONE update minus the identity, determinant `−11/9`;
* one spike and two old atoms — the top-left block is the scaled SIC pair
  excess, determinant `(11/9)² − (10/9)²·(4/3) = −37/243 < 0`: the scaling by
  `10/9 < 1/(2−2/√3)` is not enough to rescue any pair.

A principal block of a positive semidefinite matrix is positive semidefinite,
so each failure kills the whole subset. Combined with the real ledger this is
the sharpest field statement the campaign owns: weighted (6,3) — the single
binding object of GTZ(3) — holds over ℝ only if realness is consumed, because
over ℂ it is simply false.
-/
import Mathlib
import Gtz.ComplexWitness

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

/-! ### Block tools -/

/-- The top-left 2×2 block of a 3×3 complex matrix. -/
def topLeftBlock (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun rowIndex colIndex => M rowIndex.castSucc colIndex.castSucc

/-- Extending a plane vector by a zero third coordinate. -/
def extendFlat (planeVec : Fin 2 → ℂ) : Fin 3 → ℂ :=
  ![planeVec 0, planeVec 1, 0]

theorem topLeftBlock_add (M N : Matrix (Fin 3) (Fin 3) ℂ) :
    topLeftBlock (M + N) = topLeftBlock M + topLeftBlock N := rfl

theorem topLeftBlock_sub (M N : Matrix (Fin 3) (Fin 3) ℂ) :
    topLeftBlock (M - N) = topLeftBlock M - topLeftBlock N := rfl

theorem extendFlat_zero (planeVec : Fin 2 → ℂ) :
    extendFlat planeVec 0 = planeVec 0 := rfl
theorem extendFlat_one (planeVec : Fin 2 → ℂ) :
    extendFlat planeVec 1 = planeVec 1 := rfl
theorem extendFlat_two (planeVec : Fin 2 → ℂ) :
    extendFlat planeVec 2 = 0 := rfl

theorem topLeftBlock_one : topLeftBlock 1 = 1 := by
  ext rowIndex colIndex
  simp only [topLeftBlock, Matrix.one_apply, Fin.castSucc_inj]

/-- The quadratic form of the block is the form of the extension. -/
theorem quadForm_extendFlat (M : Matrix (Fin 3) (Fin 3) ℂ)
    (planeVec : Fin 2 → ℂ) :
    star (extendFlat planeVec) ⬝ᵥ (M *ᵥ extendFlat planeVec)
      = star planeVec ⬝ᵥ (topLeftBlock M *ᵥ planeVec) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two,
    Pi.star_apply, extendFlat_zero, extendFlat_one, extendFlat_two,
    topLeftBlock, star_zero]
  have h0 : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  have h1 : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
  rw [h0, h1]
  ring

/-- A principal block of a positive semidefinite matrix is positive
semidefinite. -/
theorem posSemidef_topLeftBlock {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hpsd : M.PosSemidef) : (topLeftBlock M).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun planeVec => ?_⟩
  · have hherm := hpsd.isHermitian
    refine Matrix.IsHermitian.ext fun rowIndex colIndex => ?_
    exact hherm.apply rowIndex.castSucc colIndex.castSucc
  · rw [← quadForm_extendFlat]
    exact hpsd.dotProduct_mulVec_nonneg _

/-- A 2×2 complex matrix whose determinant has negative real part is not
positive semidefinite. -/
theorem not_posSemidef_of_det_re_neg {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hneg : M.det.re < 0) : ¬ M.PosSemidef := by
  intro hpsd
  have hnonneg := hpsd.det_nonneg
  have hre := (Complex.le_def.mp hnonneg).1
  simp only [Complex.zero_re] at hre
  linarith

/-! ### The level-σ pair determinants -/

/-- The scaled SIC atoms: `√(10/9)` times the plane atoms. -/
noncomputable def scaleAmpC : ℂ := ((Real.sqrt (10 / 9) : ℝ) : ℂ)

theorem scaleAmpC_conj : (starRingEnd ℂ) scaleAmpC = scaleAmpC :=
  Complex.conj_ofReal _

theorem scaleAmpC_sq : scaleAmpC * scaleAmpC = 10 / 9 := by
  rw [scaleAmpC, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 10/9)]
  norm_num

noncomputable def scaledSic (c : Fin 4) : Fin 2 → ℂ :=
  scaleAmpC • sicAtom c

theorem scaledSic_norm (c : Fin 4) :
    star (scaledSic c) ⬝ᵥ scaledSic c = 20 / 9 := by
  have hbase := sicNorm c
  have hpull : star (scaledSic c) ⬝ᵥ scaledSic c
      = scaleAmpC * scaleAmpC * (star (sicAtom c) ⬝ᵥ sicAtom c) := by
    simp only [scaledSic, star_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, RCLike.star_def, scaleAmpC_conj]
    ring
  rw [hpull, hbase, scaleAmpC_sq]
  norm_num

theorem scaledSic_overlap {first second : Fin 4} (hne : first ≠ second) :
    (star (scaledSic first) ⬝ᵥ scaledSic second)
      * (star (scaledSic second) ⬝ᵥ scaledSic first) = 400 / 243 := by
  have hbase := sicOverlap hne
  have hpull : ∀ left right : Fin 4,
      star (scaledSic left) ⬝ᵥ scaledSic right
        = scaleAmpC * scaleAmpC * (star (sicAtom left) ⬝ᵥ sicAtom right) := by
    intro left right
    simp only [scaledSic, star_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, RCLike.star_def, scaleAmpC_conj]
    ring
  rw [hpull, hpull, scaleAmpC_sq]
  have hshuffle : 10 / 9 * (star (sicAtom first) ⬝ᵥ sicAtom second)
      * (10 / 9 * (star (sicAtom second) ⬝ᵥ sicAtom first))
      = (10 / 9) ^ 2 * ((star (sicAtom first) ⬝ᵥ sicAtom second)
        * (star (sicAtom second) ⬝ᵥ sicAtom first)) := by ring
  rw [hshuffle, hbase]
  norm_num

/-- **The scaled pair fails**: the scaled SIC pair excess has determinant
`−37/243 < 0`. The `10/9` boost is not enough — no scaling below
`1/(2−2/√3)` could be. -/
theorem scaledPair_not_posSemidef {first second : Fin 4} (hne : first ≠ second) :
    ¬ (complexAtom (scaledSic first) + complexAtom (scaledSic second)
      - 1).PosSemidef := by
  refine not_posSemidef_of_det_re_neg ?_
  rw [det_pair_excess, scaledSic_norm, scaledSic_norm]
  have hcross := scaledSic_overlap hne
  have hvalue : (20 / 9 - 1 : ℂ) * (20 / 9 - 1)
      - (star (scaledSic first) ⬝ᵥ scaledSic second)
        * (star (scaledSic second) ⬝ᵥ scaledSic first)
      = -(37 / 243) := by
    rw [hcross]
    norm_num
  rw [hvalue]
  norm_num

/-- **The rank-one block fails**: one scaled atom alone against the identity
has determinant `−11/9`. -/
theorem scaledSingle_not_posSemidef (c : Fin 4) :
    ¬ (complexAtom (scaledSic c) + complexAtom (0 : Fin 2 → ℂ)
      - 1).PosSemidef := by
  refine not_posSemidef_of_det_re_neg ?_
  rw [det_pair_excess, scaledSic_norm]
  have hzero : star (0 : Fin 2 → ℂ) ⬝ᵥ (0 : Fin 2 → ℂ) = 0 := by
    simp
  have hcrossLeft : star (scaledSic c) ⬝ᵥ (0 : Fin 2 → ℂ) = 0 := by
    simp
  have hcrossRight : star (0 : Fin 2 → ℂ) ⬝ᵥ scaledSic c = 0 := by
    simp
  rw [hzero, hcrossLeft, hcrossRight]
  norm_num

/-! ### The padded design -/

noncomputable def spikeAmpC : ℂ := ((Real.sqrt 10 : ℝ) : ℂ)

theorem spikeAmpC_conj : (starRingEnd ℂ) spikeAmpC = spikeAmpC :=
  Complex.conj_ofReal _

theorem spikeAmpC_sq : spikeAmpC * spikeAmpC = 10 := by
  rw [spikeAmpC, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 10)]
  norm_num

/-- The six padded atoms: four flat scaled SIC atoms and two spikes. -/
noncomputable def paddedAtom : Fin 6 → Fin 3 → ℂ :=
  ![extendFlat (scaledSic 0), extendFlat (scaledSic 1),
    extendFlat (scaledSic 2), extendFlat (scaledSic 3),
    ![0, 0, spikeAmpC], ![0, 0, -spikeAmpC]]

noncomputable def paddedWeight : Fin 6 → ℝ :=
  ![9/40, 9/40, 9/40, 9/40, 1/20, 1/20]

theorem paddedAtom_spike_four : paddedAtom 4 = ![0, 0, spikeAmpC] := rfl
theorem paddedAtom_spike_five : paddedAtom 5 = ![0, 0, -spikeAmpC] := rfl

/-- An old index of the padded design, recast into `Fin 4`. -/
def oldIndexOf (c : Fin 6) (hfour : c ≠ 4) (hfive : c ≠ 5) : Fin 4 :=
  ⟨c.val, by
    have hvalFour : c.val ≠ 4 := fun h => hfour (Fin.ext h)
    have hvalFive : c.val ≠ 5 := fun h => hfive (Fin.ext h)
    omega⟩

theorem oldIndexOf_ne {c d : Fin 6} (hc4 : c ≠ 4) (hc5 : c ≠ 5)
    (hd4 : d ≠ 4) (hd5 : d ≠ 5) (hne : c ≠ d) :
    oldIndexOf c hc4 hc5 ≠ oldIndexOf d hd4 hd5 := by
  intro heq
  have hval := congrArg Fin.val heq
  exact hne (Fin.ext hval)

theorem paddedAtom_old (c : Fin 6) (hfour : c ≠ 4) (hfive : c ≠ 5) :
    paddedAtom c = extendFlat (scaledSic (oldIndexOf c hfour hfive)) := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hfour
  · exact absurd rfl hfive

/-! ### Block values of the padded atoms -/

theorem extendFlat_castSucc (planeVec : Fin 2 → ℂ) (i : Fin 2) :
    extendFlat planeVec i.castSucc = planeVec i := by
  fin_cases i
  · rfl
  · rfl

theorem topLeft_atom_extend (planeVec : Fin 2 → ℂ) :
    topLeftBlock (complexAtom (extendFlat planeVec))
      = complexAtom planeVec := by
  ext rowIndex colIndex
  simp only [topLeftBlock, complexAtom, Matrix.vecMulVec_apply, Pi.star_apply,
    extendFlat_castSucc]

theorem topLeft_atom_spike (spikeVal : ℂ) :
    topLeftBlock (complexAtom ![0, 0, spikeVal]) = 0 := by
  ext rowIndex colIndex
  have hflat : (![0, 0, spikeVal] : Fin 3 → ℂ) rowIndex.castSucc = 0 := by
    fin_cases rowIndex
    · rfl
    · rfl
  simp only [topLeftBlock, complexAtom, Matrix.vecMulVec_apply, Pi.star_apply,
    hflat, zero_mul, Matrix.zero_apply]

theorem complexAtom_zero_plane : complexAtom (0 : Fin 2 → ℂ) = 0 := by
  ext rowIndex colIndex
  simp [complexAtom, Matrix.vecMulVec_apply]

/-! ### Parseval for the padded design -/

theorem paddedParseval :
    ∑ c, ((paddedWeight c : ℝ) : ℂ) • complexAtom (paddedAtom c) = 1 := by
  have hEntry : ∀ i j : Fin 2,
      ((1 : ℂ)/4) * (sicAtom 0 i * (starRingEnd ℂ) (sicAtom 0 j))
        + ((1 : ℂ)/4) * (sicAtom 1 i * (starRingEnd ℂ) (sicAtom 1 j))
        + ((1 : ℂ)/4) * (sicAtom 2 i * (starRingEnd ℂ) (sicAtom 2 j))
        + ((1 : ℂ)/4) * (sicAtom 3 i * (starRingEnd ℂ) (sicAtom 3 j))
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro i j
    have hentry := congrFun (congrFun sicParseval i) j
    simpa [Matrix.sum_apply, Matrix.smul_apply, complexAtom,
      Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, smul_eq_mul,
      Fin.sum_univ_four, mul_assoc, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_ofNat] using hentry
  ext rowIndex colIndex
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, complexAtom, Matrix.vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, smul_eq_mul, Fin.sum_univ_six]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [paddedAtom, paddedWeight, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
      Matrix.cons_val', Matrix.empty_val'] <;>
    simp [extendFlat, scaledSic, Pi.smul_apply, smul_eq_mul, map_mul, map_neg,
      scaleAmpC_conj, spikeAmpC_conj, Matrix.one_apply]
  · -- (0,0)
    have h := hEntry 0 0
    simp [Matrix.one_apply] at h
    linear_combination (9/40 : ℂ) * (sicAtom 0 0 * (starRingEnd ℂ) (sicAtom 0 0)
        + sicAtom 1 0 * (starRingEnd ℂ) (sicAtom 1 0)
        + sicAtom 2 0 * (starRingEnd ℂ) (sicAtom 2 0)
        + sicAtom 3 0 * (starRingEnd ℂ) (sicAtom 3 0)) * scaleAmpC_sq
      + h
  · -- (0,1)
    have h := hEntry 0 1
    simp [Matrix.one_apply] at h
    linear_combination (9/40 : ℂ) * (sicAtom 0 0 * (starRingEnd ℂ) (sicAtom 0 1)
        + sicAtom 1 0 * (starRingEnd ℂ) (sicAtom 1 1)
        + sicAtom 2 0 * (starRingEnd ℂ) (sicAtom 2 1)
        + sicAtom 3 0 * (starRingEnd ℂ) (sicAtom 3 1)) * scaleAmpC_sq
      + h
  · -- (1,0)
    have h := hEntry 1 0
    simp [Matrix.one_apply] at h
    linear_combination (9/40 : ℂ) * (sicAtom 0 1 * (starRingEnd ℂ) (sicAtom 0 0)
        + sicAtom 1 1 * (starRingEnd ℂ) (sicAtom 1 0)
        + sicAtom 2 1 * (starRingEnd ℂ) (sicAtom 2 0)
        + sicAtom 3 1 * (starRingEnd ℂ) (sicAtom 3 0)) * scaleAmpC_sq
      + h
  · -- (1,1)
    have h := hEntry 1 1
    simp [Matrix.one_apply] at h
    linear_combination (9/40 : ℂ) * (sicAtom 0 1 * (starRingEnd ℂ) (sicAtom 0 1)
        + sicAtom 1 1 * (starRingEnd ℂ) (sicAtom 1 1)
        + sicAtom 2 1 * (starRingEnd ℂ) (sicAtom 2 1)
        + sicAtom 3 1 * (starRingEnd ℂ) (sicAtom 3 1)) * scaleAmpC_sq
      + h
  · -- (2,2)
    linear_combination (1/10 : ℂ) * spikeAmpC_sq

/-! ### The padded design and the case analysis -/

/-- The padded SIC as a complex weighted (6,3) design. -/
noncomputable def paddedDesign : ComplexWeightedDesign 6 3 where
  atom := paddedAtom
  weight := paddedWeight
  weight_pos := by
    intro c
    fin_cases c <;> norm_num [paddedWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six,
      show paddedWeight 0 = 9/40 from rfl, show paddedWeight 1 = 9/40 from rfl,
      show paddedWeight 2 = 9/40 from rfl, show paddedWeight 3 = 9/40 from rfl,
      show paddedWeight 4 = 1/20 from rfl, show paddedWeight 5 = 1/20 from rfl]
    norm_num
  isParseval := paddedParseval

theorem topLeft_spike_four :
    topLeftBlock (complexAtom (paddedAtom 4)) = 0 := by
  rw [paddedAtom_spike_four]
  exact topLeft_atom_spike spikeAmpC

theorem topLeft_spike_five :
    topLeftBlock (complexAtom (paddedAtom 5)) = 0 := by
  rw [paddedAtom_spike_five]
  exact topLeft_atom_spike (-spikeAmpC)

/-- The single-old-atom excess cannot be positive semidefinite. -/
theorem scaledSingle_excess_not_psd (c : Fin 4) :
    ¬ (complexAtom (scaledSic c) - 1).PosSemidef := by
  have hpair := scaledSingle_not_posSemidef c
  rwa [complexAtom_zero_plane, add_zero] at hpair

/-- **The one-spike kill**: a spike with a zero top-left block plus two old
atoms cannot yield a positive semidefinite excess — the block collapses to the
scaled SIC pair, whose determinant is negative. -/
theorem oneSpike_kill {spikeIdx oldFirst oldSecond : Fin 6}
    (hne : oldFirst ≠ oldSecond)
    (hfirstFour : oldFirst ≠ 4) (hfirstFive : oldFirst ≠ 5)
    (hsecondFour : oldSecond ≠ 4) (hsecondFive : oldSecond ≠ 5)
    (hspikeBlock : topLeftBlock (complexAtom (paddedAtom spikeIdx)) = 0)
    (hpsd : (complexAtom (paddedAtom spikeIdx)
      + (complexAtom (paddedAtom oldFirst)
        + complexAtom (paddedAtom oldSecond)) - 1).PosSemidef) : False := by
  have hblock := posSemidef_topLeftBlock hpsd
  rw [topLeftBlock_sub, topLeftBlock_add, topLeftBlock_add, hspikeBlock,
    topLeftBlock_one, zero_add, paddedAtom_old oldFirst hfirstFour hfirstFive,
    paddedAtom_old oldSecond hsecondFour hsecondFive, topLeft_atom_extend,
    topLeft_atom_extend] at hblock
  exact scaledPair_not_posSemidef
    (oldIndexOf_ne hfirstFour hfirstFive hsecondFour hsecondFive hne) hblock

/-- The quadratic form of a 3×3 matrix at the third basis vector reads the
corner entry. -/
theorem quadForm_basisTwo (M : Matrix (Fin 3) (Fin 3) ℂ) :
    star (![0, 0, 1] : Fin 3 → ℂ) ⬝ᵥ (M *ᵥ ![0, 0, 1]) = M 2 2 := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, star_zero,
    star_one]
  simp

/-- **The all-old kill**: a subset of flat atoms leaves the third coordinate
empty, so the excess at the third basis vector is `−1`. -/
theorem allOld_kill {C : Finset (Fin 6)}
    (hflat : ∀ c ∈ C, paddedAtom c 2 = 0)
    (hpsd : ((∑ c ∈ C, complexAtom (paddedAtom c)) - 1).PosSemidef) :
    False := by
  have hform := hpsd.dotProduct_mulVec_nonneg (![0, 0, 1] : Fin 3 → ℂ)
  rw [quadForm_basisTwo] at hform
  have hcorner : ((∑ c ∈ C, complexAtom (paddedAtom c)) - 1) 2 2 = -1 := by
    rw [Matrix.sub_apply, Matrix.sum_apply, Matrix.one_apply_eq]
    have hterms : ∀ c ∈ C, complexAtom (paddedAtom c) 2 2 = 0 := by
      intro c hc
      simp [complexAtom, Matrix.vecMulVec_apply, hflat c hc]
    rw [Finset.sum_congr rfl hterms]
    simp
  rw [hcorner] at hform
  have hre := (Complex.le_def.mp hform).1
  norm_num at hre

/-! ### The headline -/

/-- **Complex weighted (6,3) is FALSE.** The padded SIC has no dominating
3-subset: all-old subsets die on the third coordinate, both-spike subsets die
on a rank-one block, one-spike subsets die on the scaled SIC pair determinant.
The first genuinely open case of GTZ is complex-false — every proof of
weighted (6,3) over ℝ must consume realness. -/
theorem complexGtzWeighted_six_three_fails : ¬ ComplexGtzWeighted 6 3 := by
  intro hcontra
  obtain ⟨C, hcard, hdom⟩ := hcontra paddedDesign
  rw [ComplexDominates] at hdom
  change ((∑ c ∈ C, complexAtom (paddedAtom c)) - 1).PosSemidef at hdom
  by_cases hfour : (4 : Fin 6) ∈ C <;> by_cases hfive : (5 : Fin 6) ∈ C
  · -- both spikes plus one old atom
    have hcardErase : ((C.erase 4).erase 5).card = 1 := by
      rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨by decide, hfive⟩),
        Finset.card_erase_of_mem hfour, hcard]
    obtain ⟨oldIdx, holdSet⟩ := Finset.card_eq_one.mp hcardErase
    have holdMem : oldIdx ∈ (C.erase 4).erase 5 := by
      rw [holdSet]
      exact Finset.mem_singleton_self oldIdx
    have holdFive : oldIdx ≠ 5 := (Finset.mem_erase.mp holdMem).1
    have holdFour : oldIdx ≠ 4 :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp holdMem).2).1
    have holdInC : oldIdx ∈ C :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp holdMem).2).2
    have hCset : insert (4 : Fin 6) (insert 5 {oldIdx}) = C := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.mp hx with hx4 | hx'
        · exact hx4 ▸ hfour
        rcases Finset.mem_insert.mp hx' with hx5 | hxold
        · exact hx5 ▸ hfive
        · exact (Finset.mem_singleton.mp hxold) ▸ holdInC
      · rw [hcard, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
        · simp
        · exact fun h => holdFive (Finset.mem_singleton.mp h).symm
        · intro h
          rcases Finset.mem_insert.mp h with h45 | h4old
          · exact absurd h45 (by decide)
          · exact holdFour (Finset.mem_singleton.mp h4old).symm
    rw [← hCset, Finset.sum_insert, Finset.sum_insert,
      Finset.sum_singleton] at hdom
    · -- kill via the top-left block: two zero spikes and one rank-one atom
      have hblock := posSemidef_topLeftBlock hdom
      rw [topLeftBlock_sub, topLeftBlock_add, topLeftBlock_add,
        topLeft_spike_four, topLeft_spike_five, topLeftBlock_one, zero_add,
        zero_add, paddedAtom_old oldIdx holdFour holdFive,
        topLeft_atom_extend] at hblock
      exact scaledSingle_excess_not_psd _ hblock
    · exact fun h => holdFive (Finset.mem_singleton.mp h).symm
    · intro h
      rcases Finset.mem_insert.mp h with h45 | h4old
      · exact absurd h45 (by decide)
      · exact holdFour (Finset.mem_singleton.mp h4old).symm
  · -- spike 4 plus two old atoms
    have hcardErase : (C.erase 4).card = 2 := by
      rw [Finset.card_erase_of_mem hfour, hcard]
    obtain ⟨oldFirst, oldSecond, hne, hpairSet⟩ :=
      Finset.card_eq_two.mp hcardErase
    have hfirstMem : oldFirst ∈ C.erase 4 := by
      rw [hpairSet]; exact Finset.mem_insert_self _ _
    have hsecondMem : oldSecond ∈ C.erase 4 := by
      rw [hpairSet]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hfirstFour : oldFirst ≠ 4 := (Finset.mem_erase.mp hfirstMem).1
    have hsecondFour : oldSecond ≠ 4 := (Finset.mem_erase.mp hsecondMem).1
    have hfirstInC : oldFirst ∈ C := (Finset.mem_erase.mp hfirstMem).2
    have hsecondInC : oldSecond ∈ C := (Finset.mem_erase.mp hsecondMem).2
    have hfirstFive : oldFirst ≠ 5 := fun h => hfive (h ▸ hfirstInC)
    have hsecondFive : oldSecond ≠ 5 := fun h => hfive (h ▸ hsecondInC)
    have hCset : insert (4 : Fin 6) {oldFirst, oldSecond} = C := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.mp hx with hx4 | hxpair
        · exact hx4 ▸ hfour
        rcases Finset.mem_insert.mp hxpair with hxf | hxs
        · exact hxf ▸ hfirstInC
        · exact (Finset.mem_singleton.mp hxs) ▸ hsecondInC
      · rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair hne]
        intro h
        rcases Finset.mem_insert.mp h with h4f | h4s
        · exact hfirstFour h4f.symm
        · exact hsecondFour (Finset.mem_singleton.mp h4s).symm
    rw [← hCset, Finset.sum_insert, Finset.sum_pair hne] at hdom
    · exact oneSpike_kill hne hfirstFour hfirstFive hsecondFour hsecondFive
        topLeft_spike_four hdom
    · intro h
      rcases Finset.mem_insert.mp h with h4f | h4s
      · exact hfirstFour h4f.symm
      · exact hsecondFour (Finset.mem_singleton.mp h4s).symm
  · -- spike 5 plus two old atoms
    have hcardErase : (C.erase 5).card = 2 := by
      rw [Finset.card_erase_of_mem hfive, hcard]
    obtain ⟨oldFirst, oldSecond, hne, hpairSet⟩ :=
      Finset.card_eq_two.mp hcardErase
    have hfirstMem : oldFirst ∈ C.erase 5 := by
      rw [hpairSet]; exact Finset.mem_insert_self _ _
    have hsecondMem : oldSecond ∈ C.erase 5 := by
      rw [hpairSet]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hfirstFive : oldFirst ≠ 5 := (Finset.mem_erase.mp hfirstMem).1
    have hsecondFive : oldSecond ≠ 5 := (Finset.mem_erase.mp hsecondMem).1
    have hfirstInC : oldFirst ∈ C := (Finset.mem_erase.mp hfirstMem).2
    have hsecondInC : oldSecond ∈ C := (Finset.mem_erase.mp hsecondMem).2
    have hfirstFour : oldFirst ≠ 4 := fun h => hfour (h ▸ hfirstInC)
    have hsecondFour : oldSecond ≠ 4 := fun h => hfour (h ▸ hsecondInC)
    have hCset : insert (5 : Fin 6) {oldFirst, oldSecond} = C := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.mp hx with hx5 | hxpair
        · exact hx5 ▸ hfive
        rcases Finset.mem_insert.mp hxpair with hxf | hxs
        · exact hxf ▸ hfirstInC
        · exact (Finset.mem_singleton.mp hxs) ▸ hsecondInC
      · rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair hne]
        intro h
        rcases Finset.mem_insert.mp h with h5f | h5s
        · exact hfirstFive h5f.symm
        · exact hsecondFive (Finset.mem_singleton.mp h5s).symm
    rw [← hCset, Finset.sum_insert, Finset.sum_pair hne] at hdom
    · exact oneSpike_kill hne hfirstFour hfirstFive hsecondFour hsecondFive
        topLeft_spike_five hdom
    · intro h
      rcases Finset.mem_insert.mp h with h5f | h5s
      · exact hfirstFive h5f.symm
      · exact hsecondFive (Finset.mem_singleton.mp h5s).symm
  · -- all three atoms old: die on the third coordinate
    refine allOld_kill (fun c hc => ?_) hdom
    have hcFour : c ≠ 4 := fun h => hfour (h ▸ hc)
    have hcFive : c ≠ 5 := fun h => hfive (h ▸ hc)
    rw [paddedAtom_old c hcFour hcFive]
    exact extendFlat_two _

end Gtz
