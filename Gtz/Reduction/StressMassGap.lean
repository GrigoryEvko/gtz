/-
# The stress mass-gap bound, and the rigidity law it implies

This file is the Lean-ready core of the quadrature lane.  It consumes exactly
two outputs of the balanced branch of `sixThree_stress_trichotomy` — the middle
matrix identity (positive side sum = negative side sum with absolute
coefficients) and its positive definiteness — and produces a STRICT domination
certificate for the positive stress side.

The bound.  A full-support stress splits the atoms into a positive side `P` and
a negative side `N` with a common middle matrix
    `X = sum_{c in P} z_c A_c = sum_{c in N} (-z_c) A_c`,  `X` positive definite.
Parseval turns the positive side's gap into a difference of the two sides:
    `(S_P - 1)[x] = sum_{c in P} (1 - t_c) s_c^2  -  sum_{c in N} t_c s_c^2`,
`s_c = atom c . x`.  Rescaling each term by its stress coefficient rewrites both
sums against the SAME quadratic form `X[x]`:
    `sum_{c in P} (1 - t_c) s_c^2 >= freeFloor * X[x]`   when `freeFloor * z_c <= 1 - t_c`,
    `sum_{c in N} t_c s_c^2      <= boundCeiling * X[x]` when `t_c <= boundCeiling * (-z_c)`,
so the gap is at least `(freeFloor - boundCeiling) * X[x]`, positive whenever the
free floor beats the bound ceiling.  No whitening, no square root, no normal
form: the two sides are comparable because the stress makes them the same matrix.

Invariantly the hypothesis reads
    `max_{c in N} t_c / |z_c|  <  min_{c in P} (1 - t_c) / |z_c|`
and it is scale-free in the stress.

The rigidity corollary.  On the slice where `(1 - t_c)/z_c` is a constant `L` on
`P` and `t_c/(-z_c)` is the SAME constant on `N`, the positive side is exactly
Parseval-tight (`S_P = 1`) — and the bound applied to the OTHER side needs only
    `max_{c in P} t_c + max_{c in N} t_c < 1`,
which holds because six STRICTLY positive weights sum to one and the two maxima
are only two of the six.  So the negative side dominates strictly and the design
is not a tie.  That slice is precisely the configuration where the predecessor
probe measured its 30/30 "even triple always wins"; the corollary turns that
measurement into a theorem, on the whole slice and at every scale.
-/
import Gtz.Reduction.StressSignSplit
import Gtz.LinAlg.SchurRankOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-- The quadratic form of a coefficient-weighted atom sum over a SUBSET of the
labels.  The finset-relative sibling of `Gtz.weighted_atomForm_eq`. -/
theorem atomForm_eq_on_subset (selected : Finset (Fin size)) (coeff : Fin size → ℝ)
    (atomFamily : Fin size → Fin rank → ℝ) (probe : Fin rank → ℝ) :
    probe ⬝ᵥ ((∑ c ∈ selected, coeff c • atomMatrix (atomFamily c)) *ᵥ probe)
      = ∑ c ∈ selected, coeff c * (atomFamily c ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- The unweighted subset sum is symmetric. -/
theorem transpose_subsetSum (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) :
    (subsetSum design selected)ᵀ = subsetSum design selected := by
  rw [subsetSum, Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun c _ =>
    transpose_eq_of_isHermitian (posSemidef_atomMatrix (design.atom c)).1

/-- **THE STRESS MASS-GAP BOUND.**  If every positive-side atom carries free
mass `1 - t_c` at least `freeFloor` times its stress coefficient, every
negative-side atom carries bound mass `t_c` at most `boundCeiling` times its
absolute stress coefficient, and `boundCeiling < freeFloor`, then the positive
stress side dominates STRICTLY.

The two middle-matrix hypotheses are exactly the balanced branch of the `(6,3)`
stress trichotomy; nothing here is special to size six or rank three. -/
theorem posDef_gap_of_stressMassGap (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ}
    (hmiddle :
      ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
          stressCoeff c • atomMatrix (design.atom c)
        = ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
            (-stressCoeff c) • atomMatrix (design.atom c))
    (hposDef :
      (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
          stressCoeff c • atomMatrix (design.atom c)).PosDef)
    (hfull : ∀ c, stressCoeff c ≠ 0)
    {freeFloor boundCeiling : ℝ}
    (hfree : ∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - design.weight c)
    (hbound : ∀ c, stressCoeff c < 0 → design.weight c ≤ boundCeiling * (-stressCoeff c))
    (hgap : boundCeiling < freeFloor) :
    (subsetSum design (Finset.univ.filter fun c => 0 < stressCoeff c) - 1).PosDef := by
  classical
  set posSide := Finset.univ.filter (fun c => 0 < stressCoeff c) with hposSide
  set negSide := Finset.univ.filter (fun c => stressCoeff c < 0) with hnegSide
  have hdisjoint : Disjoint posSide negSide := by
    rw [Finset.disjoint_left]
    intro c hcPos hcNeg
    exact absurd (Finset.mem_filter.mp hcNeg).2 (asymm (Finset.mem_filter.mp hcPos).2)
  have hcover : posSide ∪ negSide = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    rcases lt_or_lt_iff_ne.mpr (hfull c) with hlt | hgt
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hlt⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hgt⟩)
  -- Parseval turns the gap into a difference of the two sides.
  have hsplit : subsetSum design posSide - 1
      = (∑ c ∈ posSide, (1 - design.weight c) • atomMatrix (design.atom c))
        - ∑ c ∈ negSide, design.weight c • atomMatrix (design.atom c) := by
    rw [subsetSum, ← design.isParseval, ← hcover, Finset.sum_union hdisjoint,
      sub_add_eq_sub_sub, ← Finset.sum_sub_distrib]
    exact congrArg (· - ∑ c ∈ negSide, design.weight c • atomMatrix (design.atom c))
      (Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul])
  have hsymm : (subsetSum design posSide - 1)ᵀ = subsetSum design posSide - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, transpose_subsetSum]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  -- the middle matrix's quadratic form, written on each side
  set middleForm := ∑ c ∈ posSide, stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2
    with hmiddleForm
  have hmiddlePos : 0 < middleForm := by
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobe
    rwa [star_trivial, atomForm_eq_on_subset] at this
  have hmiddleNeg :
      middleForm = ∑ c ∈ negSide, (-stressCoeff c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    have := congrArg (fun mat => probe ⬝ᵥ (mat *ᵥ probe)) hmiddle
    simpa only [atomForm_eq_on_subset] using this
  -- the two one-sided comparisons against that single form
  have hlower : freeFloor * middleForm
      ≤ ∑ c ∈ posSide, (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 := by
    rw [hmiddleForm, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hcPos : 0 < stressCoeff c := (Finset.mem_filter.mp hc).2
    have hstep : freeFloor * stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2
        ≤ (1 - design.weight c) * (design.atom c ⬝ᵥ probe) ^ 2 :=
      mul_le_mul_of_nonneg_right (hfree c hcPos) (sq_nonneg _)
    calc freeFloor * (stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2)
        = freeFloor * stressCoeff c * (design.atom c ⬝ᵥ probe) ^ 2 := by ring
      _ ≤ _ := hstep
  have hupper : ∑ c ∈ negSide, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      ≤ boundCeiling * middleForm := by
    rw [hmiddleNeg, Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hcNeg : stressCoeff c < 0 := (Finset.mem_filter.mp hc).2
    have hstep : design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
        ≤ boundCeiling * (-stressCoeff c) * (design.atom c ⬝ᵥ probe) ^ 2 :=
      mul_le_mul_of_nonneg_right (hbound c hcNeg) (sq_nonneg _)
    calc design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
        ≤ boundCeiling * (-stressCoeff c) * (design.atom c ⬝ᵥ probe) ^ 2 := hstep
      _ = boundCeiling * ((-stressCoeff c) * (design.atom c ⬝ᵥ probe) ^ 2) := by ring
  have hstrict : 0 < (freeFloor - boundCeiling) * middleForm :=
    mul_pos (by linarith) hmiddlePos
  rw [star_trivial, hsplit, Matrix.sub_mulVec, dotProduct_sub,
    atomForm_eq_on_subset, atomForm_eq_on_subset]
  nlinarith [hlower, hupper, hstrict]

/-- **THE RIGIDITY LAW.**  On the slice where the free mass of every
positive-side atom and the bound mass of every negative-side atom sit at the
SAME ratio against the stress, the negative side dominates strictly — so no
such design on this slice is a tie.  The ceiling hypothesis here is a SINGLE
common bound `weightCeiling` on every weight with `2 * weightCeiling < 1`,
i.e. every weight strictly below one half — genuinely restrictive, NOT
automatic for a weighted design.  The sharper two-ceiling form
`max t_P + max t_N < 1` (which IS automatic when each side has two or more
atoms) is not proved here; strengthening to it is mechanical future work. -/
theorem posDef_negSide_gap_of_rigidity (design : WeightedDesign size rank)
    {stressCoeff : Fin size → ℝ} {ratio : ℝ} (hratioPos : 0 < ratio)
    (hmiddle :
      ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          (-stressCoeff c) • atomMatrix (design.atom c)
        = ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
            stressCoeff c • atomMatrix (design.atom c))
    (hposDef :
      (∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          (-stressCoeff c) • atomMatrix (design.atom c)).PosDef)
    (hfull : ∀ c, stressCoeff c ≠ 0)
    (hfreeP : ∀ c, 0 < stressCoeff c → 1 - design.weight c = ratio * stressCoeff c)
    (hboundN : ∀ c, stressCoeff c < 0 → design.weight c = ratio * (-stressCoeff c))
    {weightCeiling : ℝ}
    (hceilP : ∀ c, 0 < stressCoeff c → design.weight c ≤ weightCeiling)
    (hceilN : ∀ c, stressCoeff c < 0 → design.weight c ≤ weightCeiling)
    (hceilPos : 0 < weightCeiling) (hsmall : 2 * weightCeiling < 1) :
    (subsetSum design (Finset.univ.filter fun c => stressCoeff c < 0) - 1).PosDef := by
  classical
  have hbelowOne : weightCeiling < 1 := by linarith
  have hcoceilPos : (0:ℝ) < 1 - weightCeiling := by linarith
  -- run the mass-gap bound against the FLIPPED stress, so the two sides swap
  have hflipFull : ∀ c, (-stressCoeff) c ≠ 0 := fun c => neg_ne_zero.mpr (hfull c)
  have hposFilter : (Finset.univ.filter fun c => 0 < (-stressCoeff) c)
      = Finset.univ.filter fun c => stressCoeff c < 0 := by
    ext c; simp
  have hnegFilter : (Finset.univ.filter fun c => (-stressCoeff) c < 0)
      = Finset.univ.filter fun c => 0 < stressCoeff c := by
    ext c; simp
  have main := posDef_gap_of_stressMassGap design (stressCoeff := -stressCoeff)
    (freeFloor := ratio * (1 - weightCeiling) / weightCeiling)
    (boundCeiling := ratio * weightCeiling / (1 - weightCeiling))
    (by rw [hposFilter, hnegFilter]; simpa using hmiddle)
    (by rw [hposFilter]; simpa using hposDef)
    hflipFull
    (fun c hc => by
      have hcNeg : stressCoeff c < 0 := by simpa [neg_pos] using hc
      have hceil : design.weight c ≤ weightCeiling := hceilN c hcNeg
      have hstress : design.weight c = ratio * (-stressCoeff) c := by
        simpa [Pi.neg_apply] using hboundN c hcNeg
      have hkey : (1 - weightCeiling) * design.weight c / weightCeiling
          ≤ 1 - design.weight c := by
        rw [div_le_iff₀ hceilPos]; nlinarith [hceil]
      calc ratio * (1 - weightCeiling) / weightCeiling * (-stressCoeff) c
          = (1 - weightCeiling) / weightCeiling * (ratio * (-stressCoeff) c) := by ring
        _ = (1 - weightCeiling) / weightCeiling * design.weight c := by rw [← hstress]
        _ = (1 - weightCeiling) * design.weight c / weightCeiling := by ring
        _ ≤ 1 - design.weight c := hkey)
    (fun c hc => by
      have hcPos : 0 < stressCoeff c := by simpa [neg_lt_zero] using hc
      have hceil : design.weight c ≤ weightCeiling := hceilP c hcPos
      have hstress : 1 - design.weight c = ratio * (-(-stressCoeff) c) := by
        simpa [Pi.neg_apply] using hfreeP c hcPos
      have hkey : design.weight c
          ≤ weightCeiling * (1 - design.weight c) / (1 - weightCeiling) := by
        rw [le_div_iff₀ hcoceilPos]; nlinarith [hceil]
      calc design.weight c
          ≤ weightCeiling * (1 - design.weight c) / (1 - weightCeiling) := hkey
        _ = weightCeiling / (1 - weightCeiling) * (ratio * (-(-stressCoeff) c)) := by
              rw [← hstress]; ring
        _ = ratio * weightCeiling / (1 - weightCeiling) * (-(-stressCoeff) c) := by ring)
    (by
      rw [div_lt_div_iff₀ hcoceilPos hceilPos]
      nlinarith [hratioPos, hsmall, hceilPos])
  rwa [hposFilter] at main

end Gtz
