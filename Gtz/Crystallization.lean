/-
# Crystallization: M(k) = k(k+1)/2 + 1 — bounded support at the sharp constant

The kernel walk (proven informally at k=3 in `gtz_proof_gtz3_crystallization.md`,
general k in `gtz_proof_gtz_allk_lift.md` §3.3; verified at scale):

1. The moment map w ↦ (upper triangle of Σ w_c g_c g_cᵀ, Σ w_c) is linear into a
   space of dimension k(k+1)/2 + 1 (the atoms are symmetric, so the upper
   triangle carries everything — `Sym2.sortEquiv` + `Sym2.card` give the count).
2. When m exceeds that dimension the map has a null direction δ ≠ 0: a weight
   perturbation preserving Parseval and the total mass. Since Σδ = 0 and δ ≠ 0,
   δ has a strictly positive coordinate; walking t − s·δ to the first vanishing
   weight (s* = min over δ_c > 0 of t_c/δ_c) produces nonnegative weights
   summing to 1, still Parseval, with the argmin weight exactly 0.
3. The positive-weight support S is a strictly smaller atom family carrying a
   genuine design; domination is weight-free (`subsetSum` never reads weights),
   so a dominating k-subset of the reduced design pulls back verbatim.

Strong induction then reduces every size to the canonical range m ≤ M(k):
`crystallization` at the sharp constant, no Carathéodory needed — the kernel
walk IS the support-reduction step of Carathéodory, done by hand to keep the
pulled-back subset inside the ORIGINAL atom family.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.SchurRankOne

namespace Gtz

open Matrix

variable {m k : ℕ}

/-- The upper-triangle coordinates of a matrix, as a linear map. Together with
symmetry these determine the matrix (`symmetric_eq_zero_of_coords_eq_zero`). -/
def upperTriangleCoords :
    Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ] ({ p : Fin k × Fin k // p.1 ≤ p.2 } → ℝ) where
  toFun M := fun p => M p.val.1 p.val.2
  map_add' M N := by
    funext p
    simp [Matrix.add_apply]
  map_smul' r M := by
    funext p
    simp [Matrix.smul_apply]

/-- A symmetric matrix vanishing on the upper triangle vanishes. -/
theorem symmetric_eq_zero_of_coords_eq_zero {M : Matrix (Fin k) (Fin k) ℝ}
    (hMT : Mᵀ = M) (hcoords : upperTriangleCoords M = 0) : M = 0 := by
  ext i j
  rcases le_total i j with hij | hji
  · exact congrFun hcoords ⟨(i, j), hij⟩
  · have hupper := congrFun hcoords ⟨(j, i), hji⟩
    have hsymm := congrFun (congrFun hMT j) i
    rw [Matrix.transpose_apply] at hsymm
    rw [Matrix.zero_apply, hsymm]
    exact hupper

/-- The moment map of an atom family: w ↦ (upper triangle of Σ w_c g_c g_cᵀ,
Σ w_c). Its kernel directions are the Parseval-preserving perturbations. -/
def momentMap (g : Fin m → (Fin k → ℝ)) :
    (Fin m → ℝ) →ₗ[ℝ] ({ p : Fin k × Fin k // p.1 ≤ p.2 } → ℝ) × ℝ where
  toFun w := (upperTriangleCoords (∑ c, w c • atomMatrix (g c)), ∑ c, w c)
  map_add' u v := by
    simp [Pi.add_apply, add_smul, Finset.sum_add_distrib, Prod.mk_add_mk]
  map_smul' r w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_mk, mul_smul,
      ← Finset.smul_sum, ← Finset.mul_sum, map_smul]

/-- There are k(k+1)/2 ordered pairs i ≤ j in Fin k. -/
theorem card_orderedPairs :
    Fintype.card { p : Fin k × Fin k // p.1 ≤ p.2 } = k * (k + 1) / 2 := by
  rw [← Fintype.card_congr Sym2.sortEquiv, Sym2.card, Fintype.card_fin,
    Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- **The null direction.** More atoms than k(k+1)/2 + 1 force a nonzero weight
perturbation annihilating both Parseval and the total mass. -/
theorem exists_null_direction (g : Fin m → (Fin k → ℝ))
    (hm : k * (k + 1) / 2 + 1 < m) :
    ∃ delta : Fin m → ℝ, delta ≠ 0 ∧
      (∑ c, delta c • atomMatrix (g c)) = 0 ∧ (∑ c, delta c) = 0 := by
  have hnotinj : ¬ Function.Injective (momentMap g) := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_pi, Module.finrank_prod, Module.finrank_pi,
      Module.finrank_self, Fintype.card_fin, card_orderedPairs] at hle
    exact absurd hm (not_lt.mpr hle)
  rw [← LinearMap.ker_eq_bot] at hnotinj
  obtain ⟨delta, hmem, hne⟩ := (Submodule.ne_bot_iff _).mp hnotinj
  have hzero := LinearMap.mem_ker.mp hmem
  have hcoords : upperTriangleCoords (∑ c, delta c • atomMatrix (g c)) = 0 :=
    congrArg Prod.fst hzero
  have hsum : (∑ c, delta c) = 0 := congrArg Prod.snd hzero
  -- the perturbed frame matrix is symmetric, so the upper triangle kills it
  have hsymmT : (∑ c, delta c • atomMatrix (g c))ᵀ
      = ∑ c, delta c • atomMatrix (g c) := by
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (g c)).1]
  exact ⟨delta, hne, symmetric_eq_zero_of_coords_eq_zero hsymmT hcoords, hsum⟩

/-- Summing a function over the order enumeration of a finite support is
summing it over the support. -/
theorem sum_orderIsoOfFin {M : Type*} [AddCommMonoid M] (S : Finset (Fin m))
    {n : ℕ} (hcard : S.card = n) (f : Fin m → M) :
    ∑ i : Fin n, f (S.orderIsoOfFin hcard i).val = ∑ c ∈ S, f c := by
  rw [← Finset.sum_coe_sort S f]
  exact Fintype.sum_equiv (S.orderIsoOfFin hcard).toEquiv _ _ fun i => rfl

/-- **Kernel-walk support reduction**: a design with more than k(k+1)/2 + 1
atoms admits a strictly smaller design on a sub-family of its own atoms. -/
theorem exists_reduced_design (D : WeightedDesign m k)
    (hm : k * (k + 1) / 2 + 1 < m) :
    ∃ msmall : ℕ, msmall < m ∧ ∃ Dsmall : WeightedDesign msmall k,
      ∃ inject : Fin msmall → Fin m, Function.Injective inject ∧
        ∀ i, Dsmall.atom i = D.atom (inject i) := by
  obtain ⟨delta, hdne, hdA, hdsum⟩ := exists_null_direction D.atom hm
  -- δ has a strictly positive coordinate (Σδ = 0 and δ ≠ 0)
  have hpos : ∃ c, 0 < delta c := by
    by_contra hno
    push Not at hno
    have hallzero : ∀ c ∈ Finset.univ, delta c = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos fun c _ => hno c).mp hdsum
    exact hdne (funext fun c => hallzero c (Finset.mem_univ c))
  obtain ⟨cpos, hcpos⟩ := hpos
  -- the walk length: the first weight to vanish
  set raisers : Finset (Fin m) := Finset.univ.filter (fun c => 0 < delta c)
    with hraisers
  have hraisersne : raisers.Nonempty :=
    ⟨cpos, Finset.mem_filter.mpr ⟨Finset.mem_univ cpos, hcpos⟩⟩
  obtain ⟨cstar, hcstarmem, hmin⟩ :=
    Finset.exists_min_image raisers (fun c => D.weight c / delta c) hraisersne
  have hdstar : 0 < delta cstar := (Finset.mem_filter.mp hcstarmem).2
  set walkLen : ℝ := D.weight cstar / delta cstar with hwalkLen
  -- the walked weights: nonnegative, sum 1, Parseval, and zero at cstar
  set walked : Fin m → ℝ := fun c => D.weight c - walkLen * delta c with hwalked
  have hwnonneg : ∀ c, 0 ≤ walked c := by
    intro c
    rcases le_or_gt (delta c) 0 with hnonpos | hposc
    · have hlen : 0 < walkLen := div_pos (D.weight_pos cstar) hdstar
      have hwc := D.weight_pos c
      simp only [hwalked]
      nlinarith
    · have hcmem : c ∈ raisers :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ c, hposc⟩
      have hle := (le_div_iff₀ hposc).mp (hmin c hcmem)
      simp only [hwalked]
      linarith
  have hwstar : walked cstar = 0 := by
    simp only [hwalked, hwalkLen]
    rw [div_mul_cancel₀ _ (ne_of_gt hdstar), sub_self]
  have hwsum : ∑ c, walked c = 1 := by
    simp only [hwalked]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdsum, mul_zero, sub_zero,
      D.weight_sum_one]
  have hwpars : ∑ c, walked c • atomMatrix (D.atom c) = 1 := by
    simp only [hwalked, sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hdA, smul_zero, sub_zero,
      D.isParseval]
  -- the positive-weight support: a strictly smaller atom family
  set support : Finset (Fin m) := Finset.univ.filter (fun c => 0 < walked c)
    with hsupport
  have hcstarout : cstar ∉ support := by
    simp [hsupport, hwstar]
  have hsupportlt : support.card < m := by
    have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
    have hsub : support ⊆ Finset.univ.erase cstar := fun c hc =>
      Finset.mem_erase.mpr ⟨fun heq => hcstarout (heq ▸ hc), Finset.mem_univ c⟩
    calc support.card ≤ (Finset.univ.erase cstar).card := Finset.card_le_card hsub
      _ < m := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ cstar), Finset.card_univ,
            Fintype.card_fin]
          omega
  -- outside the support the walked weights vanish, so sums restrict
  have houtside : ∀ c ∈ Finset.univ, c ∉ support → walked c = 0 := by
    intro c _ hc
    have hnotpos : ¬ 0 < walked c := fun hposc =>
      hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hposc⟩)
    exact le_antisymm (not_lt.mp hnotpos) (hwnonneg c)
  have hsumS : ∑ c ∈ support, walked c = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support) houtside]
    exact hwsum
  have hparsS : ∑ c ∈ support, walked c • atomMatrix (D.atom c) = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support)
      (fun c hcu hcs => by rw [houtside c hcu hcs, zero_smul])]
    exact hwpars
  refine ⟨support.card, hsupportlt,
    { atom := fun i => D.atom (support.orderIsoOfFin rfl i).val
      weight := fun i => walked (support.orderIsoOfFin rfl i).val
      weight_pos := fun i =>
        (Finset.mem_filter.mp (support.orderIsoOfFin rfl i).2).2
      weight_sum_one := ?_
      isParseval := ?_ },
    fun i => (support.orderIsoOfFin rfl i).val,
    fun a b hab => (support.orderIsoOfFin rfl).toEquiv.injective
      (Subtype.val_injective hab),
    fun i => rfl⟩
  · rw [sum_orderIsoOfFin support rfl walked]
    exact hsumS
  · rw [sum_orderIsoOfFin support rfl (fun c => walked c • atomMatrix (D.atom c))]
    exact hparsS

/-- **Crystallization at the sharp constant.** If weighted GTZ(k) holds for
every size m ≤ M(k) = k(k+1)/2 + 1, it holds for every size: larger designs
always reduce, and domination pulls back along the atom sub-family. -/
theorem crystallization (k : ℕ)
    (hsmall : ∀ m, m ≤ k * (k + 1) / 2 + 1 → GtzWeighted m k) :
    GtzWeightedAll k := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases le_or_gt m (k * (k + 1) / 2 + 1) with hle | hgt
    · exact hsmall m hle
    · intro D
      obtain ⟨msmall, hlt, Dsmall, inject, hinj, hatoms⟩ :=
        exists_reduced_design D hgt
      obtain ⟨Csmall, hcard, hdom⟩ := ih msmall hlt Dsmall
      refine ⟨Csmall.image inject, ?_, ?_⟩
      · rw [Finset.card_image_of_injective _ hinj, hcard]
      · show (subsetSum D (Csmall.image inject) - 1).PosSemidef
        have hsums : subsetSum D (Csmall.image inject) = subsetSum Dsmall Csmall := by
          rw [subsetSum, Finset.sum_image fun x _ y _ hxy => hinj hxy, subsetSum]
          exact Finset.sum_congr rfl fun i _ => by rw [hatoms i]
        rw [hsums]
        exact hdom

end Gtz
