import Mathlib
import Gtz.Reduction.StressSignSplit

/-!
# The PF-cluster pair engine at rank 3: the provable core

Three kernel bricks extracted from the PF-cluster port of Nesterenko's k = 2
equality engine (arXiv 2604.14050) to branch (i) of the (6,3) trichotomy.

* `parseval_pairing_eq_norm_sq` — the square-Gram law: pairing Parseval with a
  single atom gives `sum_d t_d (g_d . g_c)^2 = |g_c|^2`.  In mass coordinates
  this is `G2 s = 1` with `G2` the PF-cluster square Gram — the engine's port
  of entry, at every size and rank.
* `pairFailure_iff_engineForm` — the k = 3 pair-failure normal form: the
  chi-test at threshold `tau` rewrites exactly into the engine's
  `M_ij = <w_i, w_j> - (2/3) z_i z_j + shift` shape.  Pure ring algebra;
  stated over the raw pairing data so the engine's bookkeeping is kernel-true.
* `exists_offPair_probe_mass_quarter` — the stage-2 pigeonhole: a unit probe
  orthogonal to two atoms of a (6,3) design pushes Parseval mass 1 onto the
  remaining four atoms, so one of them carries at least 1/4 — strictly above
  the 1/6 the completion bound needs.

The trace leg (masses sum to the rank) is `Gtz.sum_weight_mul_leverage`.

These three are the part of the k = 2 engine that is TRUE at rank 3; the two
inequality legs do not survive the port, and K4 says why exactly.  Its
charpoly is `x (x - 1/8)^2 (x - 1/4)^3`, so the spectral floor is
`lambda_1 = 1/4 < 1/3` with positive inertia `5 = dim Sym0(3)`: the squares
fill the space and no inertia contradiction exists.  And none of the twelve
completions of K4's three `2/n`-strong (opposite) pairs dominates, while the
dominators are exactly the four stars, which contain no strong pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix

namespace Gtz

/-- **The square-Gram law.**  Pairing Parseval against the direction of one
atom: the `t`-weighted squared inner products against atom `c` sum to that
atom's squared length.  This is `G2 s = 1` in mass coordinates — the exact
matrix the Perron–Frobenius cluster engine runs on. -/
theorem parseval_pairing_eq_norm_sq {size rank : ℕ}
    (design : WeightedDesign size rank) (label : Fin size) :
    ∑ other, design.weight other
        * (design.atom other ⬝ᵥ design.atom label) ^ 2
      = design.atom label ⬝ᵥ design.atom label := by
  have happlied : design.atom label ⬝ᵥ
      ((∑ c, design.weight c • atomMatrix (design.atom c)) *ᵥ design.atom label)
        = design.atom label ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ design.atom label) := by
    rw [design.isParseval]
  simpa [weighted_atomForm_eq, Matrix.one_mulVec] using happlied

/-- **The pair-failure normal form.**  For masses `sI, sJ`, squared pairing
`pairingSq`, traceless square inner `wInner := pairingSq - sI * sJ / 3`, shifted
masses `zI := sI - 3 * theta`, `zJ := sJ - 3 * theta`, and threshold
`tau := 2 * theta`: the chi-test at `tau` fails strictly iff the engine matrix
entry `wInner - (2/3) zI zJ + 2 theta^2` is positive.  Pure algebra — this is
the bookkeeping identity the whole Case-B engine rides, valid for every
threshold parameter `theta`. -/
theorem pairFailure_iff_engineForm (sI sJ pairingSq theta : ℝ) :
    ((sI - 2 * theta) * (sJ - 2 * theta) < pairingSq)
      ↔ 0 < (pairingSq - sI * sJ / 3)
            - 2 / 3 * ((sI - 3 * theta) * (sJ - 3 * theta))
            + 2 * theta ^ 2 := by
  constructor <;> intro hside <;> nlinarith [hside]

/-- **The stage-2 pigeonhole.**  A unit probe orthogonal to two atoms of a
(6,3) design leaves the full Parseval mass 1 on the remaining four atoms, so
some off-pair atom carries weighted probe mass at least 1/4.  The completion
bound needs only 1/6, so the pigeonhole has slack 1/4 - 1/6 = 1/12.  The
bound is sharp — at K4 every off-pair atom carries exactly 1/4 — and probe
mass alone does not buy a PSD completion: K4 refutes that implication
exactly. -/
theorem exists_offPair_probe_mass_quarter
    (design : WeightedDesign 6 3) (firstLabel secondLabel : Fin 6)
    (hlabelsDistinct : firstLabel ≠ secondLabel)
    (probe : Fin 3 → ℝ) (hunit : probe ⬝ᵥ probe = 1)
    (hfirstPerp : design.atom firstLabel ⬝ᵥ probe = 0)
    (hsecondPerp : design.atom secondLabel ⬝ᵥ probe = 0) :
    ∃ offLabel : Fin 6, offLabel ≠ firstLabel ∧ offLabel ≠ secondLabel ∧
      1 / 4 ≤ design.weight offLabel * (design.atom offLabel ⬝ᵥ probe) ^ 2 := by
  classical
  have hparseval : probe ⬝ᵥ
      ((∑ c, design.weight c • atomMatrix (design.atom c)) *ᵥ probe)
        = probe ⬝ᵥ ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ probe) := by
    rw [design.isParseval]
  rw [weighted_atomForm_eq, Matrix.one_mulVec, hunit] at hparseval
  -- the off-pair labels carry total mass exactly 1
  set offPair : Finset (Fin 6) :=
    (Finset.univ.erase firstLabel).erase secondLabel with hoffPair
  have hoffSum : ∑ c ∈ offPair, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      = 1 := by
    rw [← hparseval]
    refine Finset.sum_subset (Finset.subset_univ offPair) ?_
    intro c _ hnotOff
    rw [hoffPair] at hnotOff
    have hor : c = secondLabel ∨ c = firstLabel := by
      by_contra hneither
      rw [not_or] at hneither
      exact hnotOff (Finset.mem_erase.mpr ⟨hneither.1,
        Finset.mem_erase.mpr ⟨hneither.2, Finset.mem_univ c⟩⟩)
    rcases hor with rfl | rfl
    · rw [hsecondPerp]; ring
    · rw [hfirstPerp]; ring
  -- the off-pair set has at most four elements
  have hcard : offPair.card = 4 := by
    rw [hoffPair,
      Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hlabelsDistinct.symm, Finset.mem_univ secondLabel⟩),
      Finset.card_erase_of_mem (Finset.mem_univ firstLabel)]
    simp
  -- pigeonhole: max >= average = 1/4
  by_contra hallBelow
  have hallStrictBelow : ∀ label : Fin 6, label ≠ firstLabel → label ≠ secondLabel →
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 < 1 / 4 := by
    intro label hnotFirst hnotSecond
    by_contra hnotBelow
    exact hallBelow ⟨label, hnotFirst, hnotSecond, not_lt.mp hnotBelow⟩
  have hnonempty : offPair.Nonempty := by
    rw [← Finset.card_pos, hcard]
    norm_num
  have hstrict : ∑ c ∈ offPair, design.weight c * (design.atom c ⬝ᵥ probe) ^ 2
      < ∑ _c ∈ offPair, (1 / 4 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hnonempty ?_
    intro c hmem
    rw [hoffPair, Finset.mem_erase, Finset.mem_erase] at hmem
    exact hallStrictBelow c hmem.2.1 hmem.1
  rw [hoffSum, Finset.sum_const, nsmul_eq_mul, hcard] at hstrict
  norm_num at hstrict

end Gtz
