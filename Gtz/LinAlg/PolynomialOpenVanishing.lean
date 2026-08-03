/-
# Polynomial vanishing on open sets

Module 2 of the genericity reduction for the open `(6,3)` cell — keystone K5:
a REAL multivariate polynomial that vanishes on a NONEMPTY OPEN subset of its
coordinate space is the zero polynomial.  This is the entire topological input
of the star-propagation argument; no analytic identity theorem, no
connectedness, no manifold structure — only "a one-variable real polynomial
with infinitely many roots is zero", applied once per variable.

Route (`mvPoly_eq_zero_of_eval_eq_zero_on_box`, induction on the variable
count): an open box slices along its first coordinate into one-variable
polynomials over an interval, which is infinite, so every slice is the zero
polynomial of `Polynomial (MvPolynomial (Fin tailCount) ℝ)`; its coefficients
then vanish on the tail box and die by the induction hypothesis.  The bridge
between multivariate evaluation and the sliced one-variable evaluation is
`MvPolynomial.eval_eq_eval_mv_eval'`; the base case is
`MvPolynomial.funext` (a polynomial in zero variables vanishing at the one
point vanishes at every point).

`mvPoly_eq_zero_of_eval_eq_zero_on_open` transports the box statement to an
arbitrary `Fintype` variable index and an arbitrary nonempty open subset of the
sup-metric pi space: every open set contains a metric ball around each of its
points, and a sup-metric ball IS a box (`dist_pi_lt_iff`), pulled through
`MvPolynomial.rename` along `Fintype.equivFin`.

The propagation module (`Gtz.Reduction.ChartPullback`) consumes the open-set
form with the variable index instantiated at the chart parameter index — that
is where "an open set of failing designs" becomes "a zero polynomial".

Backtick convention for this file's docstrings: multi-character backticked
tokens are declaration names (kernel-checked).
-/
import Mathlib

namespace Gtz

/-- **K5, BOX FORM.**  A real multivariate polynomial on finitely many
variables that vanishes on a nonempty open box is the zero polynomial.
Induction on the variable count: slicing along the first coordinate turns the
box hypothesis into one-variable polynomials vanishing on an infinite interval,
so every coefficient — a polynomial in the tail variables — vanishes on the
tail box. -/
theorem mvPoly_eq_zero_of_eval_eq_zero_on_box :
    ∀ {varCount : ℕ} (poly : MvPolynomial (Fin varCount) ℝ)
      (lower upper : Fin varCount → ℝ),
      (∀ index, lower index < upper index) →
      (∀ point : Fin varCount → ℝ,
        (∀ index, point index ∈ Set.Ioo (lower index) (upper index)) →
        MvPolynomial.eval point poly = 0) →
      poly = 0 := by
  intro varCount
  induction varCount with
  | zero =>
      intro poly lower upper _ hvanish
      apply MvPolynomial.funext
      intro point
      rw [map_zero]
      exact hvanish point (fun index => index.elim0)
  | succ tailCount tailInduction =>
      intro poly lower upper hlt hvanish
      have hcoeff : ∀ coeffIndex : ℕ,
          (MvPolynomial.finSuccEquiv ℝ tailCount poly).coeff coeffIndex = 0 := by
        intro coeffIndex
        apply tailInduction _ (fun index => lower index.succ)
          (fun index => upper index.succ) (fun index => hlt index.succ)
        intro tailPoint htail
        have hsliceZero :
            Polynomial.map (MvPolynomial.eval tailPoint)
              (MvPolynomial.finSuccEquiv ℝ tailCount poly) = 0 := by
          apply Polynomial.eq_zero_of_infinite_isRoot
          have hsubset : Set.Ioo (lower 0) (upper 0) ⊆
              {value | Polynomial.IsRoot (Polynomial.map (MvPolynomial.eval tailPoint)
                (MvPolynomial.finSuccEquiv ℝ tailCount poly)) value} := by
            intro value hvalue
            show Polynomial.eval value _ = 0
            rw [← MvPolynomial.eval_eq_eval_mv_eval']
            apply hvanish
            intro index
            refine Fin.cases ?_ ?_ index
            · rw [Fin.cons_zero]
              exact hvalue
            · intro tailIndex
              rw [Fin.cons_succ]
              exact htail tailIndex
          exact (Set.infinite_coe_iff.mp (Set.Ioo.infinite (hlt 0))).mono hsubset
        have hcoeffSlice := congrArg (fun slice => Polynomial.coeff slice coeffIndex)
          hsliceZero
        simpa [Polynomial.coeff_map] using hcoeffSlice
      have hslice : MvPolynomial.finSuccEquiv ℝ tailCount poly = 0 :=
        Polynomial.ext fun coeffIndex => by
          rw [hcoeff coeffIndex, Polynomial.coeff_zero]
      apply (MvPolynomial.finSuccEquiv ℝ tailCount).injective
      rw [hslice, map_zero]

/-- **K5, OPEN-SET FORM (the consumable).**  A real multivariate polynomial on
a finite variable index that vanishes on a NONEMPTY OPEN subset of its
coordinate space is the zero polynomial.  The open set contains a sup-metric
ball around any of its points, a sup-metric ball is a box
(`dist_pi_lt_iff`), and the box form applies through `MvPolynomial.rename`
along `Fintype.equivFin`. -/
theorem mvPoly_eq_zero_of_eval_eq_zero_on_open {vars : Type*} [Fintype vars]
    (poly : MvPolynomial vars ℝ) {vanishingSet : Set (vars → ℝ)}
    (hopen : IsOpen vanishingSet) (hnonempty : vanishingSet.Nonempty)
    (hvanish : ∀ point ∈ vanishingSet, MvPolynomial.eval point poly = 0) :
    poly = 0 := by
  classical
  obtain ⟨center, hcenter⟩ := hnonempty
  obtain ⟨radius, hradius, hball⟩ := Metric.isOpen_iff.mp hopen center hcenter
  set varEquiv := Fintype.equivFin vars with hvarEquiv
  have hrenamed : MvPolynomial.rename (⇑varEquiv) poly = 0 := by
    apply mvPoly_eq_zero_of_eval_eq_zero_on_box _
      (fun index => center (varEquiv.symm index) - radius)
      (fun index => center (varEquiv.symm index) + radius)
      (fun index => by linarith)
    intro point hpoint
    rw [MvPolynomial.eval_rename]
    apply hvanish
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hradius]
    intro varIndex
    have hmem := hpoint (varEquiv varIndex)
    rw [Equiv.symm_apply_apply] at hmem
    rw [Function.comp_apply, Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
  have hinjective := MvPolynomial.rename_injective (R := ℝ) (⇑varEquiv) varEquiv.injective
  apply hinjective
  rw [hrenamed, map_zero]

end Gtz
