import Gtz.Wave.OneAxisZeroFourSets
import Gtz.Design.TightAntecedentMining

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# The refusal budget of the one-zero corner, and the Z1 assembly

At a corank-two corner whose gap axis one inside atom `x` reads at zero — the
`Z1` stratum — the atom `x` is unit.  A card-3 subset that contains an atom of
leverage at most one never dominates strictly
(`Gtz.notPosDef_of_mem_leverage_le_one`), so on `Z1` every triple through `x`
is refused with no tie hypothesis
(`Gtz.corner_oneAxisZero_xTriple_not_posDef`).  The tie condition of a `Z1`
corner therefore collapses to the ten `x`-avoiding refusals
(`Gtz.corner_oneAxisZero_isTie_iff_xAvoiding`), and each of those is one
double downdate of the erase-`x` anchor `B = S_{univ∖{x}} − 1`, which is
positive definite outright.  The tie IS the pair system of the anchor
(`Gtz.corner_oneAxisZero_isTie_iff_pairSystem`):

  a `Z1` corner ties exactly when every pair `a ≠ b` of the five anchored
  atoms obeys `1 ≤ r_a` or `(1 − r_a)(1 − r_b) ≤ ρ_ab²` at `B⁻¹`.

## The cells collapse further

The four-set dichotomy (`Gtz.corner_oneAxisZero_fourSet_split`) splits `Z1`
by the two four-sets `A_e = S_{{e}∪Cᶜ} − 1`.  When `A_z` fails, `A_y` is
positive definite and the whole tie condition is THREE floors: every outside
atom reads `A_y⁻¹` at least at one
(`Gtz.corner_oneAxisZero_heavyInside_isTie_iff`).  The complement refusal and
the three `z`-side refusals are then downdates of the failed `A_z`, the
census refusals come from the corner, and the `x`-triples from the unit atom.
When BOTH four-sets are positive definite, the tie condition is seven floors:
the six outside readings at `A_y⁻¹` and `A_z⁻¹`, and the reading of `y`
itself at `A_y⁻¹` — that last floor is the complement refusal
(`Gtz.corner_oneAxisZero_bothLight_isTie_iff`).

## The assembly and its one residual

`Gtz.OneAxisZeroPairCoverage` names the single unproven statement: the pair
system of the anchor is infeasible on `Z1` proper (`0 < lam`, both other
inside axis readings nonzero).  Granting it, a `(6,3)` tie has no `Z1` corner
(`Gtz.corner_oneAxisZero_absurd`), and the coverage Prop is EXACTLY the
emptiness of the stratum (`Gtz.oneAxisZeroPairCoverage_iff`): the pair system
loses nothing, because on `Z1` it is the tie.  Measured: a fresh 3.3·10⁹
sample sweep of the stratum finds no configuration that satisfies the pair
system, and the 71 exact stragglers of the aggregate battery all violate it
with best margin `0.079` — always at a one-inside triple, never at the
complement.

The `Z1` hypotheses are not decoration: `ledgerFoil` and `residualFoil` carry
corners with TWO zero axis readings (the dead `Z2` shape), and
`signCoherentFoil` reads all three inside atoms off the axis.  The pair
system's laws are tie-necessary and fail at all three foils.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Refusal survives a downdate -/

/-- A matrix that is not positive definite stays so after a rank-one
downdate: the downdated form plus the atom is the matrix again. -/
theorem not_posDef_sub_vecMulVec_of_not_posDef {k : ℕ}
    {M : Matrix (Fin k) (Fin k) ℝ} (hM : ¬ M.PosDef) (g : Fin k → ℝ) :
    ¬ (M - Matrix.vecMulVec g g).PosDef := by
  intro hPD
  refine hM ?_
  have hsum : M = (M - Matrix.vecMulVec g g) + Matrix.vecMulVec g g := by abel
  rw [hsum]
  exact hPD.add_posSemidef
    (show (Matrix.vecMulVec g g).PosSemidef from posSemidef_atomMatrix g)

/-! ## 2. The zero-reading inside atom is unit, and poisons its triples -/

/-- **The zero atom of the corner is unit.**  The heavy-excess identity of the
corner pins the leverage of an inside atom that reads the axis at zero. -/
theorem corner_oneAxisZero_unit (D : WeightedDesign m 3) (C : Finset (Fin m))
    (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hunit : u ⬝ᵥ u = 1) (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin m} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0) :
    D.atom x ⬝ᵥ D.atom x = 1 := by
  have hone : (0 : ℝ) < 1 + lam := by linarith
  have hexX := corner_heavyExcess_axis D C hcard hlam hunit hgap hx
  simp only [heavyExcess] at hexX
  rw [hax, show leverageOf (D.atom x) = D.atom x ⬝ᵥ D.atom x from
    (dotProduct_self_eq_sum_sq (D.atom x)).symm] at hexX
  have hcancel := mul_left_cancel₀ (ne_of_gt hone)
    (show (1 + lam) * (D.atom x ⬝ᵥ D.atom x - 1) = (1 + lam) * 0 by
      rw [mul_zero]
      nlinarith [hexX])
  linarith

/-- **Every triple through the zero atom is refused, with no tie.**  The zero
atom is unit, and a card-3 subset with a member of leverage at most one never
dominates strictly. -/
theorem corner_oneAxisZero_xTriple_not_posDef (D : WeightedDesign m 3)
    (C : Finset (Fin m)) (hcard : C.card = 3) {lam : ℝ} (hlam : 0 ≤ lam)
    {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D C - 1 = lam • atomMatrix u)
    {x : Fin m} (hx : x ∈ C) (hax : D.atom x ⬝ᵥ u = 0)
    {T : Finset (Fin m)} (hT : T.card = 3) (hxT : x ∈ T) :
    ¬ (subsetSum D T - 1).PosDef := by
  classical
  have hlev : leverageOf (D.atom x) ≤ 1 := by
    rw [show leverageOf (D.atom x) = D.atom x ⬝ᵥ D.atom x from
      (dotProduct_self_eq_sum_sq (D.atom x)).symm,
      corner_oneAxisZero_unit D C hcard hlam hunit hgap hx hax]
  obtain ⟨a, b, hab, hTe⟩ : ∃ a b : Fin m, a ≠ b ∧ T.erase x = {a, b} := by
    have hc2 : (T.erase x).card = 2 := by
      rw [Finset.card_erase_of_mem hxT, hT]
    exact Finset.card_eq_two.mp hc2
  have hTeq : T = {x, a, b} := by
    rw [← Finset.insert_erase hxT, hTe]
  rw [hTeq]
  exact notPosDef_of_mem_leverage_le_one D x a b hlev

/-! ## 3. The refusal budget: the tie of a `Z1` corner is ten refusals -/

/-- **THE REFUSAL BUDGET.**  At a corank-two corner whose gap axis the inside
atom `x` reads at zero, the design ties exactly when every card-3 subset that
avoids `x` fails to dominate strictly.  The triples through `x` are free, and
the corner itself is the weak dominator. -/
theorem corner_oneAxisZero_isTie_iff_xAvoiding (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    IsTie D ↔ ∀ T : Finset (Fin m), T.card = 3 → x ∉ T →
      ¬ (subsetSum D T - 1).PosDef := by
  constructor
  · intro htie T hT _
    exact htie.2 T hT
  · intro hten
    refine ⟨⟨{x, y, z}, card_triple_eq hxy hxz hyz, ?_⟩, fun T hT => ?_⟩
    · rw [Dominates, hgap]
      exact (posSemidef_atomMatrix u).smul hlam
    · by_cases hxT : x ∈ T
      · exact corner_oneAxisZero_xTriple_not_posDef D _
          (card_triple_eq hxy hxz hyz) hlam hunit hgap (by simp) hax hT hxT
      · exact hten T hT hxT

/-! ## 4. Every `x`-avoiding triple is one pair of the erase-`x` anchor -/

/-- A card-3 subset of `Fin 6` that avoids `x` is the erase-`x` five-set with
one pair removed. -/
theorem xAvoiding_pair_surgery {x : Fin 6} {T : Finset (Fin 6)}
    (hT : T.card = 3) (hxT : x ∉ T) :
    ∃ a ∈ (univ : Finset (Fin 6)).erase x, ∃ b ∈ (univ : Finset (Fin 6)).erase x,
      a ≠ b ∧ T = (((univ : Finset (Fin 6)).erase x).erase a).erase b := by
  classical
  set F : Finset (Fin 6) := (univ : Finset (Fin 6)).erase x with hF
  have hTF : T ⊆ F := fun t ht =>
    Finset.mem_erase.mpr ⟨fun h => hxT (h ▸ ht), Finset.mem_univ t⟩
  have hFcard : F.card = 5 := by
    rw [hF, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  have hdiff : (F \ T).card = 2 := by
    rw [card_sdiff, Finset.inter_eq_left.mpr hTF, hFcard, hT]
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hdiff
  have haF : a ∈ F :=
    (Finset.mem_sdiff.mp (by rw [hset]; exact Finset.mem_insert_self a {b})).1
  have hbF : b ∈ F := (Finset.mem_sdiff.mp (by rw [hset]; simp)).1
  refine ⟨a, haF, b, hbF, hab, ?_⟩
  have hTrec : T = F \ (F \ T) := by
    ext t
    simp only [Finset.mem_sdiff]
    constructor
    · intro ht
      exact ⟨hTF ht, fun h => h.2 ht⟩
    · rintro ⟨htF, h⟩
      by_contra hn
      exact h ⟨htF, hn⟩
  have hsplit : F \ ({a, b} : Finset (Fin 6)) = (F.erase a).erase b := by
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase, not_or]
    tauto
  rw [hTrec, hset, hsplit]

/-! ## 5. The pair system of the anchor is the tie -/

/-- **THE TIE OF A `Z1` CORNER IS THE PAIR SYSTEM OF ITS ANCHOR.**  The
erase-`x` anchor `B` is positive definite outright, each `x`-avoiding triple
is one pair of the anchored five-set, and the depth-two criterion converts
each refusal into the reading disjunction — an equivalence, not a floor. -/
theorem corner_oneAxisZero_isTie_iff_pairSystem (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) :
    IsTie D ↔ ∀ a ∈ (univ : Finset (Fin 6)).erase x,
      ∀ b ∈ (univ : Finset (Fin 6)).erase x, a ≠ b →
      1 ≤ D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a)
      ∨ (1 - D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a))
        * (1 - D.atom b ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b))
        ≤ (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b)) ^ 2 := by
  classical
  have hPD : (subsetSum D ((univ : Finset (Fin 6)).erase x) - 1).PosDef :=
    corner_oneAxisZero_fiveSet_posDef D hxy hxz hyz hlam hunit hgap hax
  have hFcard : ((univ : Finset (Fin 6)).erase x).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      Fintype.card_fin]
  constructor
  · intro htie a ha b hb hab
    exact tie_fiveSet_pair_reading D htie _ hFcard hPD ha hb hab
  · intro hpairs
    rw [corner_oneAxisZero_isTie_iff_xAvoiding D hxy hxz hyz hlam hunit hgap hax]
    intro T hT hxT
    obtain ⟨a, ha, b, hb, hab, hTab⟩ := xAvoiding_pair_surgery hT hxT
    rw [hTab, subsetSum_erase_erase_sub_one D _ ha hb hab]
    exact (not_posDef_sub_two_vecMulVec_iff _ hPD (D.atom a) (D.atom b)).mpr
      (hpairs a ha b hb hab)

/-! ## 6. The trichotomy of the `x`-avoiding triples -/

/-- A card-3 subset with one specified member whose other members avoid a
corner triple is the member's four-set with one outside atom removed. -/
theorem oneInside_triple_form {x y z e : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (heC : e ∈ ({x, y, z} : Finset (Fin 6)))
    {T : Finset (Fin 6)} (hT : T.card = 3) (heT : e ∈ T)
    (hsub : T.erase e ⊆ (({x, y, z} : Finset (Fin 6))ᶜ)) :
    ∃ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      T = (insert e (({x, y, z} : Finset (Fin 6))ᶜ)).erase d := by
  classical
  set K : Finset (Fin 6) := ({x, y, z} : Finset (Fin 6))ᶜ with hK
  have hKcard : K.card = 3 :=
    card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)
  have hTe : (T.erase e).card = 2 := by
    rw [Finset.card_erase_of_mem heT, hT]
  have hdcard : (K \ T.erase e).card = 1 := by
    rw [card_sdiff, Finset.inter_eq_left.mpr hsub, hKcard, hTe]
  obtain ⟨d, hdset⟩ := Finset.card_eq_one.mp hdcard
  have hdmem : d ∈ K \ T.erase e := by
    rw [hdset]
    exact Finset.mem_singleton_self d
  have hdK : d ∈ K := (Finset.mem_sdiff.mp hdmem).1
  have hdT : d ∉ T.erase e := (Finset.mem_sdiff.mp hdmem).2
  have hde : d ≠ e := by
    intro h
    exact (Finset.mem_compl.mp (hK ▸ hdK)) (h ▸ heC)
  have hKd : K.erase d = T.erase e := by
    have hsub2 : T.erase e ⊆ K.erase d := fun t ht =>
      Finset.mem_erase.mpr ⟨fun h => hdT (h ▸ ht), hsub ht⟩
    refine (Finset.eq_of_subset_of_card_le hsub2 ?_).symm
    rw [Finset.card_erase_of_mem hdK, hKcard, hTe]
  refine ⟨d, hdK, ?_⟩
  have hstep : (insert e K).erase d = T := by
    rw [Finset.erase_insert_of_ne (Ne.symm hde), hKd, Finset.insert_erase heT]
  exact hstep.symm

/-- **The trichotomy.**  An `x`-avoiding triple of `Fin 6` shares two atoms
with the corner triple, or is the complement, or is one of the two inside
four-sets with one outside atom removed. -/
theorem corner_xAvoiding_trichotomy {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) {T : Finset (Fin 6)} (hT : T.card = 3) (hxT : x ∉ T) :
    2 ≤ (T ∩ ({x, y, z} : Finset (Fin 6))).card
    ∨ T = (({x, y, z} : Finset (Fin 6))ᶜ)
    ∨ (∃ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        T = (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).erase d)
    ∨ (∃ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        T = (insert z (({x, y, z} : Finset (Fin 6))ᶜ)).erase d) := by
  classical
  by_cases hy : y ∈ T
  · by_cases hz : z ∈ T
    · left
      have hsub : ({y, z} : Finset (Fin 6)) ⊆ T ∩ ({x, y, z} : Finset (Fin 6)) := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact Finset.mem_inter.mpr ⟨hy, by simp⟩
        · rw [Finset.mem_singleton.mp ht]
          exact Finset.mem_inter.mpr ⟨hz, by simp⟩
      calc 2 = ({y, z} : Finset (Fin 6)).card := (Finset.card_pair hyz).symm
        _ ≤ _ := Finset.card_le_card hsub
    · right; right; left
      refine oneInside_triple_form hxy hxz hyz (by simp) hT hy ?_
      intro t ht
      have htT := Finset.mem_of_mem_erase ht
      have hty := Finset.ne_of_mem_erase ht
      refine Finset.mem_compl.mpr ?_
      intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact hxT htT
      · rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact hty rfl
        · rw [Finset.mem_singleton.mp hmem] at htT
          exact hz htT
  · by_cases hz : z ∈ T
    · right; right; right
      refine oneInside_triple_form hxy hxz hyz (by simp) hT hz ?_
      intro t ht
      have htT := Finset.mem_of_mem_erase ht
      have htz := Finset.ne_of_mem_erase ht
      refine Finset.mem_compl.mpr ?_
      intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact hxT htT
      · rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact hy htT
        · exact htz (Finset.mem_singleton.mp hmem)
    · right; left
      have hsub : T ⊆ (({x, y, z} : Finset (Fin 6))ᶜ) := by
        intro t ht
        refine Finset.mem_compl.mpr ?_
        intro hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · exact hxT ht
        · rcases Finset.mem_insert.mp hmem with rfl | hmem
          · exact hy ht
          · rw [Finset.mem_singleton.mp hmem] at ht
            exact hz ht
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [hT, card_compl_eq_three_of_card_eq_three _ (card_triple_eq hxy hxz hyz)]

/-! ## 7. The heavy-inside cell: the tie is three floors -/

/-- **THE HEAVY-INSIDE COLLAPSE.**  At a `Z1` corner where the four-set
through `z` fails, the four-set through `y` is positive definite by the
dichotomy, and the WHOLE tie condition is three floors: every outside atom
reads the inverse gap of the `y` four-set at least at one.  The complement
and the `z`-side triples are downdates of the failed four-set, the census
triples come from the corner, and the `x`-triples from the unit atom. -/
theorem corner_oneAxisZero_heavyInside_isTie_iff (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔ ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      1 ≤ D.atom d ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom d) := by
  classical
  have hcardC : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  have hKcard : ((({x, y, z} : Finset (Fin 6))ᶜ)).card = 3 :=
    card_compl_eq_three_of_card_eq_three _ hcardC
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hFycard : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hyK, hKcard]
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  constructor
  · intro htie d hd
    exact fourSet_leverage_ge_one D htie _ hFycard hAy (Finset.mem_insert_of_mem hd)
  · intro hfloors
    rw [corner_oneAxisZero_isTie_iff_xAvoiding D hxy hxz hyz hlam.le hunit hgap hax]
    intro T hT hxT
    rcases corner_xAvoiding_trichotomy hxy hxz hyz hT hxT with
      hshare | hcompl | hyform | hzform
    · exact corner_census_not_posDef D _ hcardC hgap T hT hshare
    · rw [hcompl, ← Finset.erase_insert hzK,
        subsetSum_erase_sub_one_rankOne D _ (Finset.mem_insert_self z _)]
      exact not_posDef_sub_vecMulVec_of_not_posDef hnotz _
    · obtain ⟨d, hd, hTd⟩ := hyform
      rw [hTd, subsetSum_erase_sub_one_rankOne D _ (Finset.mem_insert_of_mem hd)]
      intro hPD
      exact absurd (hfloors d hd)
        (not_le.mpr ((posDef_sub_vecMulVec_iff _ hAy (D.atom d)).mp hPD))
    · obtain ⟨d, hd, hTd⟩ := hzform
      rw [hTd, subsetSum_erase_sub_one_rankOne D _ (Finset.mem_insert_of_mem hd)]
      exact not_posDef_sub_vecMulVec_of_not_posDef hnotz _

/-! ## 8. The both-light cell: the tie is seven floors -/

/-- **THE BOTH-LIGHT COLLAPSE.**  At a `Z1` corner where BOTH inside four-sets
are positive definite, the tie condition is seven floors: the six outside
readings at the two inverse gaps, and the reading of `y` at its own four-set —
that seventh floor is the complement refusal.  No dichotomy and no gap-scale
positivity is consumed. -/
theorem corner_oneAxisZero_bothLight_isTie_iff (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔
      (1 ≤ D.atom y ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom y))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d))
      ∧ (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
          1 ≤ D.atom d ⬝ᵥ
            ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom d)) := by
  classical
  have hcardC : ({x, y, z} : Finset (Fin 6)).card = 3 := card_triple_eq hxy hxz hyz
  have hKcard : ((({x, y, z} : Finset (Fin 6))ᶜ)).card = 3 :=
    card_compl_eq_three_of_card_eq_three _ hcardC
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hzK : z ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hFycard : (insert y (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hyK, hKcard]
  have hFzcard : (insert z (({x, y, z} : Finset (Fin 6))ᶜ)).card = 4 := by
    rw [Finset.card_insert_of_notMem hzK, hKcard]
  constructor
  · intro htie
    refine ⟨?_, fun d hd => ?_, fun d hd => ?_⟩
    · exact fourSet_leverage_ge_one D htie _ hFycard hAy (Finset.mem_insert_self y _)
    · exact fourSet_leverage_ge_one D htie _ hFycard hAy (Finset.mem_insert_of_mem hd)
    · exact fourSet_leverage_ge_one D htie _ hFzcard hAz (Finset.mem_insert_of_mem hd)
  · rintro ⟨hyfloor, hyfloors, hzfloors⟩
    rw [corner_oneAxisZero_isTie_iff_xAvoiding D hxy hxz hyz hlam hunit hgap hax]
    intro T hT hxT
    rcases corner_xAvoiding_trichotomy hxy hxz hyz hT hxT with
      hshare | hcompl | hyform | hzform
    · exact corner_census_not_posDef D _ hcardC hgap T hT hshare
    · rw [hcompl, ← Finset.erase_insert hyK,
        subsetSum_erase_sub_one_rankOne D _ (Finset.mem_insert_self y _)]
      intro hPD
      exact absurd hyfloor
        (not_le.mpr ((posDef_sub_vecMulVec_iff _ hAy (D.atom y)).mp hPD))
    · obtain ⟨d, hd, hTd⟩ := hyform
      rw [hTd, subsetSum_erase_sub_one_rankOne D _ (Finset.mem_insert_of_mem hd)]
      intro hPD
      exact absurd (hyfloors d hd)
        (not_le.mpr ((posDef_sub_vecMulVec_iff _ hAy (D.atom d)).mp hPD))
    · obtain ⟨d, hd, hTd⟩ := hzform
      rw [hTd, subsetSum_erase_sub_one_rankOne D _ (Finset.mem_insert_of_mem hd)]
      intro hPD
      exact absurd (hzfloors d hd)
        (not_le.mpr ((posDef_sub_vecMulVec_iff _ hAz (D.atom d)).mp hPD))

/-! ## 9. The coverage residual, and the assembly -/

/-- **THE COVERAGE RESIDUAL OF THE `Z1` STRATUM.**  On `Z1` proper — positive
gap scale, one zero inside axis reading, the other two nonzero — the pair
system of the erase-`x` anchor is infeasible.  This is the ONE statement of
the `Z1` arm left unproven.  By `Gtz.corner_oneAxisZero_isTie_iff_pairSystem`
it says exactly that no `(6,3)` tie carries a `Z1` corner. -/
def OneAxisZeroPairCoverage : Prop :=
  ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
    ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
    subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
    D.atom x ⬝ᵥ u = 0 → D.atom y ⬝ᵥ u ≠ 0 → D.atom z ⬝ᵥ u ≠ 0 →
    (∀ a ∈ (univ : Finset (Fin 6)).erase x,
      ∀ b ∈ (univ : Finset (Fin 6)).erase x, a ≠ b →
      1 ≤ D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a)
      ∨ (1 - D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a))
        * (1 - D.atom b ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b))
        ≤ (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b)) ^ 2) →
    False

/-- **THE `Z1` ASSEMBLY.**  A `(6,3)` tie with a corank-two corner in the
`Z1` proper stratum contradicts the coverage residual: the tie supplies the
pair system of the anchor, and the residual refuses it. -/
theorem corner_oneAxisZero_absurd (D : WeightedDesign 6 3) (htie : IsTie D)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hay : D.atom y ⬝ᵥ u ≠ 0)
    (haz : D.atom z ⬝ᵥ u ≠ 0) (hcov : OneAxisZeroPairCoverage) : False :=
  hcov D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz
    ((corner_oneAxisZero_isTie_iff_pairSystem D hxy hxz hyz hlam.le hunit hgap
      hax).mp htie)

/-- **The residual is exact.**  The coverage Prop holds if and only if no
`(6,3)` tie carries a `Z1` proper corner: the pair system loses nothing.  The
forward arrow is the assembly.  The backward arrow rebuilds the tie from the
pair system through the refusal budget. -/
theorem oneAxisZeroPairCoverage_iff :
    OneAxisZeroPairCoverage ↔
      ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
      ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
      subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
      D.atom x ⬝ᵥ u = 0 → D.atom y ⬝ᵥ u ≠ 0 → D.atom z ⬝ᵥ u ≠ 0 →
      ¬ IsTie D := by
  constructor
  · intro hcov D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz htie
    exact corner_oneAxisZero_absurd D htie hxy hxz hyz hlam hunit hgap
      hax hay haz hcov
  · intro hempty D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz hpairs
    exact hempty D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz
      ((corner_oneAxisZero_isTie_iff_pairSystem D hxy hxz hyz hlam.le hunit
        hgap hax).mpr hpairs)

end Gtz
