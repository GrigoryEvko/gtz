/-
# Every weighted design has a Naimark dual, and what that does to `(6,3)`

`Gtz/Wave/NaimarkDualDesign.lean` builds the theory of a Naimark dual frame but
assumes one is given.  This module produces it, and then spends it on the open
cell.

## Existence

`Gtz.exists_naimarkDual`:

  **Every `(m,k)` design carries a Naimark dual of rank `r` whenever `k + r = m`.**

The `k` vectors `c ↦ √(t_c) · g_c i` of `ℝ^m` are orthonormal, because Parseval
says exactly that.  Their span is a `k`-plane, its orthogonal complement is an
`r`-plane, and any orthonormal basis `Λ` of that complement, divided row by row
by `√(t_c)`, is a Naimark dual frame.  The dependency law is orthogonality
between the two planes and the dual Parseval law is orthonormality of `Λ`.

## The dual form of the conjecture at six points

At `(6,3)` the dual of a design is again a `(6,3)` design with the SAME weights,
so duality is an involution on the open cell.  Under it, a LOWER Loewner bound on
the Gram of a triple becomes an UPPER Loewner bound on the Gram of a triple, with
an explicit diagonal cap.  `Gtz.gtzWeighted_six_three_iff_gram_cap`:

  **`GtzWeighted 6 3`  ⟺  every `(6,3)` design has a triple `T` whose Gram
   satisfies `Gram_T ⪯ diag((1 - t_c)/t_c)`.**

Both sides quantify over all `(6,3)` designs, and the passage between them is the
involution, not a weakening.  This is the first form of the open cell in which
the wanted inequality points the other way.

`Gtz.sixThree_dual_design` records the dictionary: the dual of a `(6,3)` design
has the same weights, leverage `1/t_c - ℓ_c` at each atom, the same cross norms,
and the NEGATED Bargmann 3-cycle on every triangle.

[MEASURED before proving.  On 40 random `(6,3)` designs and at the regular
tetrahedron, `K4` at six, the icosahedron, the coordinate diagonal and the split
tetrahedron, the cap `Gram*_T ⪯ diag((1-t)/t)` agreed with domination on every
one of the twenty triples, with zero mismatches, and reproduced the domination
counts 4/4, 4/20, 10/20, 1/20 and 12/20.]
-/
import Gtz.Wave.NaimarkDualDesign

namespace Gtz

open Matrix Finset

open scoped RealInnerProductSpace

variable {m k r : ℕ}

/-! ## 0. Two square-root cancellations -/

/-- A positive weight cancels one of its square roots out of a quotient. -/
theorem weight_mul_div_sqrt {w : ℝ} (hw : 0 < w) (x : ℝ) :
    w * (x / Real.sqrt w) = Real.sqrt w * x := by
  have hroot : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw.le
  have hne : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  set root := Real.sqrt w with hrootdef
  clear_value root
  rw [← hroot]
  field_simp

/-- A positive weight cancels both of its square roots out of a product of
quotients. -/
theorem weight_mul_div_sqrt_two {w : ℝ} (hw : 0 < w) (x y : ℝ) :
    w * (x / Real.sqrt w * (y / Real.sqrt w)) = x * y := by
  have hroot : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw.le
  have hne : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
  set root := Real.sqrt w with hrootdef
  clear_value root
  rw [← hroot]
  field_simp

/-! ## 1. The design plane in `ℝ^m` -/

/-- The `i`-th square-rooted column of a design, as a vector of `ℝ^m`. -/
noncomputable def rootDesignVector (D : WeightedDesign m k) (i : Fin k) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun c => Real.sqrt (D.weight c) * D.atom c i

@[simp] theorem rootDesignVector_apply (D : WeightedDesign m k) (i : Fin k) (c : Fin m) :
    rootDesignVector D i c = Real.sqrt (D.weight c) * D.atom c i := rfl

/-- **PARSEVAL IS ORTHONORMALITY.**  The square-rooted columns of a design are an
orthonormal family in `ℝ^m`. -/
theorem rootDesignVector_orthonormal (D : WeightedDesign m k) :
    Orthonormal ℝ (rootDesignVector D) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [PiLp.inner_apply]
  have hpar : (∑ c, D.weight c • atomMatrix (D.atom c)) i j
      = (1 : Matrix (Fin k) (Fin k) ℝ) i j := by rw [D.isParseval]
  simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul, Matrix.one_apply] at hpar
  rw [← hpar]
  refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
  have hroot : Real.sqrt (D.weight c) * Real.sqrt (D.weight c) = D.weight c :=
    Real.mul_self_sqrt (D.weight_pos c).le
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, rootDesignVector_apply]
  linear_combination (D.atom c i * D.atom c j) * hroot

/-- The plane spanned by the square-rooted columns of a design. -/
noncomputable def designPlane (D : WeightedDesign m k) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (Set.range (rootDesignVector D))

theorem rootDesignVector_mem (D : WeightedDesign m k) (i : Fin k) :
    rootDesignVector D i ∈ designPlane D :=
  Submodule.subset_span ⟨i, rfl⟩

/-- The design plane has dimension the rank. -/
theorem finrank_designPlane (D : WeightedDesign m k) :
    Module.finrank ℝ (designPlane D) = k := by
  rw [designPlane, finrank_span_eq_card (rootDesignVector_orthonormal D).linearIndependent]
  simp

/-- The complement of the design plane has dimension the corank. -/
theorem finrank_designPlane_orthogonal (D : WeightedDesign m k) (hr : k + r = m) :
    Module.finrank ℝ (designPlane D)ᗮ = r := by
  have hsum := (designPlane D).finrank_add_finrank_orthogonal
  rw [finrank_designPlane D, finrank_euclideanSpace_fin] at hsum
  omega

/-! ## 2. Existence -/

/-- **EVERY WEIGHTED DESIGN HAS A NAIMARK DUAL.**  Take an orthonormal basis of
the orthogonal complement of the design plane and divide each row by the square
root of its weight.  The dependency law is orthogonality between the two planes,
and the dual Parseval law is orthonormality of the basis. -/
theorem exists_naimarkDual (D : WeightedDesign m k) (hr : k + r = m) :
    Nonempty (NaimarkDual D r) := by
  classical
  have hfr : Module.finrank ℝ (designPlane D)ᗮ = r := finrank_designPlane_orthogonal D hr
  let basis : OrthonormalBasis (Fin r) ℝ (designPlane D)ᗮ :=
    (stdOrthonormalBasis ℝ (designPlane D)ᗮ).reindex (finCongr hfr)
  -- the basis is orthonormal after the coercion into the ambient space
  have hortho : ∀ i j : Fin r,
      ∑ c, (basis i : EuclideanSpace ℝ (Fin m)) c * (basis j : EuclideanSpace ℝ (Fin m)) c
        = if i = j then 1 else 0 := by
    intro i j
    have hb := orthonormal_iff_ite.mp basis.orthonormal i j
    rw [Submodule.coe_inner, PiLp.inner_apply] at hb
    rw [← hb]
    refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
    simp [RCLike.inner_apply, mul_comm]
  -- the basis is orthogonal to the design plane
  have hdep : ∀ (i : Fin k) (j : Fin r),
      ∑ c, Real.sqrt (D.weight c) * D.atom c i * (basis j : EuclideanSpace ℝ (Fin m)) c = 0 := by
    intro i j
    have hmem : (basis j : EuclideanSpace ℝ (Fin m)) ∈ (designPlane D)ᗮ := (basis j).2
    have hzero : ⟪rootDesignVector D i, (basis j : EuclideanSpace ℝ (Fin m))⟫ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hmem _ (rootDesignVector_mem D i)
    rw [PiLp.inner_apply] at hzero
    rw [← hzero]
    refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
    simp [RCLike.inner_apply, mul_comm]
  refine ⟨{ co := fun c j => (basis j : EuclideanSpace ℝ (Fin m)) c / Real.sqrt (D.weight c)
            rankAdd := hr
            dependency := ?_
            coParseval := ?_ }⟩
  · intro i j
    rw [← hdep i j]
    refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
    have hcancel := weight_mul_div_sqrt (D.weight_pos c)
      ((basis j : EuclideanSpace ℝ (Fin m)) c)
    linear_combination (D.atom c i) * hcancel
  · ext i j
    have hone : (1 : Matrix (Fin r) (Fin r) ℝ) i j = if i = j then 1 else 0 := by
      simp [Matrix.one_apply]
    rw [hone, ← hortho i j]
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul]
    refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = Finset.univ) fun c _ => ?_
    exact weight_mul_div_sqrt_two (D.weight_pos c) _ _

/-! ## 3. The dictionary at six points -/

/-- **THE `(6,3)` DUAL DICTIONARY.**  At six points and rank three the Naimark
dual of a design is again a `(6,3)` design.  It carries the same weights, its
leverage at each atom is `1/t_c - ℓ_c`, every cross norm is unchanged, and every
Bargmann 3-cycle is negated. -/
theorem sixThree_dual_design (D : WeightedDesign 6 3) (N : NaimarkDual D 3) :
    (∀ c, N.dual.weight c = D.weight c)
      ∧ (∀ c, leverageOf (N.dual.atom c) = (D.weight c)⁻¹ - leverageOf (D.atom c))
      ∧ (∀ c d, c ≠ d → (N.dual.atom c ⬝ᵥ N.dual.atom d) ^ 2 = (D.atom c ⬝ᵥ D.atom d) ^ 2)
      ∧ (∀ a b c, a ≠ b → a ≠ c → b ≠ c →
          (N.dual.atom a ⬝ᵥ N.dual.atom b) * (N.dual.atom a ⬝ᵥ N.dual.atom c)
              * (N.dual.atom b ⬝ᵥ N.dual.atom c)
            = -((D.atom a ⬝ᵥ D.atom b) * (D.atom a ⬝ᵥ D.atom c)
                * (D.atom b ⬝ᵥ D.atom c))) := by
  refine ⟨fun c => rfl, fun c => naimark_coLeverage N c, fun c d hcd => ?_,
    fun a b c hab hac hbc => ?_⟩
  · exact naimark_crossNormSq_invariant N hcd
  · exact naimark_threeCycle_neg N hab hac hbc

/-! ## 4. The dual form of the open cell -/

/-- A triple whose Gram is capped by the diagonal `(1 - t_c)/t_c`. -/
def CappedTriple (D : WeightedDesign 6 3) (pick : Fin 3 → Fin 6) : Prop :=
  Function.Injective pick ∧ (naimarkCap D pick - naimarkGram D pick).PosSemidef

/-- **THE DUAL FORM OF THE `(6,3)` CONJECTURE.**  Weighted GTZ at six points and
rank three holds exactly when every `(6,3)` design has a triple whose Gram is
BELOW the diagonal `(1 - t_c)/t_c` in the Loewner order.  The primal statement
asks for a Gram above the identity.  Duality is an involution on the class of
`(6,3)` designs, so the two quantified statements are equivalent, and the wanted
inequality points the other way. -/
theorem gtzWeighted_six_three_iff_gram_cap :
    GtzWeighted 6 3 ↔ ∀ E : WeightedDesign 6 3, ∃ pick : Fin 3 → Fin 6, CappedTriple E pick := by
  constructor
  · intro hgtz E
    obtain ⟨N⟩ := exists_naimarkDual E (r := 3) (by norm_num)
    obtain ⟨selected, hcard, hdom⟩ := hgtz N.dual
    refine ⟨selected.orderEmbOfFin hcard, (selected.orderEmbOfFin hcard).injective, ?_⟩
    have himage : Finset.image (selected.orderEmbOfFin hcard) Finset.univ = selected := by
      apply Finset.coe_injective
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.range_orderEmbOfFin]
    rw [← himage] at hdom
    exact (naimark_dominates_iff_coGram_le N.flip
      (selected.orderEmbOfFin hcard).injective).mp hdom
  · intro hcap D
    obtain ⟨N⟩ := exists_naimarkDual D (r := 3) (by norm_num)
    obtain ⟨pick, hinj, hpsd⟩ := hcap N.dual
    refine ⟨Finset.image pick Finset.univ, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · exact (naimark_dominates_iff_coGram_le N hinj).mpr hpsd

/-- **THE CAP IS THE DOMINATION OF THE DUAL.**  For a fixed design and a fixed
Naimark dual, the capped triples of the dual are exactly the dominating triples
of the design. -/
theorem cappedTriple_dual_iff_dominates (D : WeightedDesign 6 3) (N : NaimarkDual D 3)
    {pick : Fin 3 → Fin 6} (hpick : Function.Injective pick) :
    CappedTriple N.dual pick ↔ Dominates D (Finset.image pick Finset.univ) := by
  rw [CappedTriple, naimark_dominates_iff_coGram_le N hpick]
  exact ⟨fun h => h.2, fun h => ⟨hpick, h⟩⟩

/-- **THE `(6,3)` CELL IS CLOSED UNDER DUALITY.**  Every `(6,3)` design is the
Naimark dual of a `(6,3)` design with the same weights and the same Gram. -/
theorem sixThree_dual_surjective (E : WeightedDesign 6 3) :
    ∃ (D : WeightedDesign 6 3) (N : NaimarkDual D 3),
      (∀ c, N.dual.weight c = E.weight c)
        ∧ ∀ c d, N.dual.atom c ⬝ᵥ N.dual.atom d = E.atom c ⬝ᵥ E.atom d := by
  obtain ⟨N⟩ := exists_naimarkDual E (r := 3) (by norm_num)
  exact ⟨N.dual, N.flip, fun c => rfl, fun c d => rfl⟩

end Gtz
