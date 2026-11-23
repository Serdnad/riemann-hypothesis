module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Coord

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

private theorem coneMap_monomial' (x : ι → Ω) (e : ι →₀ ℕ) (a : o) :
    coneMap o x (monomial e a) = Polynomial.C (aeval x (monomial e a)) * Polynomial.X ^ e.degree := by
  unfold coneMap
  rw [aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, map_mul, mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, Polynomial.C_pow,
    Finset.prod_pow_eq_pow_sum]
  congr 1

private theorem coeff_coneMap_eq_aeval_homogeneousComponent (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  classical

  conv_lhs => rw [f.as_sum, map_sum]
  rw [Polynomial.finsetSum_coeff]
  simp only [coneMap_monomial', Polynomial.coeff_C_mul_X_pow]

  rw [homogeneousComponent_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases eq_or_ne e.degree d with h | h
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coneMap_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) :
    coneMap o x f = Polynomial.C (aeval x f) * Polynomial.X ^ n := by
  ext d
  rw [coeff_coneMap_eq_aeval_homogeneousComponent, Polynomial.coeff_C_mul_X_pow,
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf)]
  rcases eq_or_ne d n with rfl | h
  · simp
  · rw [if_neg h, if_neg h, map_zero]

theorem mem_coordIdeal_of_isHomogeneous (x : ι → Ω) {f : MvPolynomial ι o} {n : ℕ}
    (hf : f.IsHomogeneous n) (h : aeval x f = 0) : f ∈ coordIdeal o x := by
  rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous o x hf, h, map_zero, zero_mul]

theorem coeff_coneMap (x : ι → Ω) (f : MvPolynomial ι o) (d : ℕ) :
    (coneMap o x f).coeff d = aeval x (homogeneousComponent d f) := by
  exact coeff_coneMap_eq_aeval_homogeneousComponent o x f d

theorem coordIdeal_isHomogIdeal (x : ι → Ω) : IsHomogIdeal o (coordIdeal o x) := by
  intro f hf d
  rw [coordIdeal, RingHom.mem_ker] at hf ⊢
  rw [coneMap_of_isHomogeneous o x (homogeneousComponent_isHomogeneous d f), ← coeff_coneMap, hf,
    Polynomial.coeff_zero, map_zero, zero_mul]

end Coord

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

variable {ι : Type*} [Fintype ι]

def fsLp (ι : Type*) [Fintype ι] : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).symm :
    (ι → ℂ) →L[ℂ] EuclideanSpace ℂ ι).restrictScalars ℝ

lemma fsLp_apply (z : ι → ℂ) : fsLp ι z = WithLp.toLp 2 z := rfl

lemma fsLp_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : fsLp ι z ≠ 0 := by
  rw [fsLp_apply]
  intro h
  apply hz
  have h2 := congrArg (WithLp.ofLp (p := 2)) h
  simpa using h2

lemma fsLp_smul_I (w : ι → ℂ) : fsLp ι (Complex.I • w) = Complex.I • fsLp ι w := rfl

lemma fsLp_normSq_ne_zero {z : ι → ℂ} (hz : z ≠ 0) : ‖fsLp ι z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (fsLp_ne_zero hz))

def fsGrad (y : ι → ℂ) : (ι → ℂ) →L[ℝ] ℝ :=
  (‖fsLp ι y‖ ^ 2)⁻¹ • (innerSL ℝ (fsLp ι y)).comp (fsLp ι)

lemma fsGrad_apply (y v : ι → ℂ) :
    fsGrad y v = (‖fsLp ι y‖ ^ 2)⁻¹ * inner ℝ (fsLp ι y) (fsLp ι v) := rfl

lemma hasFDerivAt_logFs {y : ι → ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z => Real.log ‖fsLp ι z‖) (fsGrad y) y := by
  have h0 : fsLp ι y ≠ 0 := fsLp_ne_zero hy
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) y := (fsLp ι).hasFDerivAt
  have h1 := (HasFDerivAt.log (HasFDerivAt.norm_sq hL) (fsLp_normSq_ne_zero hy)).const_mul (1 / 2 : ℝ)
  have hfun : (fun z => Real.log ‖fsLp ι z‖) = fun z => 1 / 2 * Real.log (‖fsLp ι z‖ ^ 2) := by
    funext z
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  refine h1.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro v
  rw [fsGrad_apply]
  simp
  ring

lemma fderiv_logFs_eventuallyEq {z : ι → ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fun z => Real.log ‖fsLp ι z‖) =ᶠ[nhds z] fsGrad := by
  filter_upwards [eventually_ne_nhds hz] with y hy using (hasFDerivAt_logFs hy).fderiv

lemma hess_logFs {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z => Real.log ‖fsLp ι z‖)) z w w =
      ‖fsLp ι w‖ ^ 2 / ‖fsLp ι z‖ ^ 2 -
        2 * inner ℝ (fsLp ι z) (fsLp ι w) ^ 2 / (‖fsLp ι z‖ ^ 2) ^ 2 := by
  have hL : HasFDerivAt (fsLp ι) (fsLp ι) z := (fsLp ι).hasFDerivAt
  have h0 := fsLp_normSq_ne_zero hz
  have hc := (hasDerivAt_inv h0).comp_hasFDerivAt z (HasFDerivAt.norm_sq hL)
  have hT : HasFDerivAt (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι))
      (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))) z :=
    (((ContinuousLinearMap.compL ℝ (ι → ℂ) (EuclideanSpace ℂ ι) ℝ).flip (fsLp ι)).comp
      ((innerSL ℝ).comp (fsLp ι))).hasFDerivAt
  have hG := HasFDerivAt.smul hc hT
  rw [(fderiv_logFs_eventuallyEq hz).fderiv_eq]
  have hfG : (fsGrad (ι := ι)) = ((fun y : ℝ => y⁻¹) ∘ fun x => ‖fsLp ι x‖ ^ 2) •
      (fun y => (innerSL ℝ (fsLp ι y)).comp (fsLp ι)) := rfl
  rw [hfG, hG.fderiv]
  simp
  field_simp
  ring

lemma inner_sq_add_inner_I_sq (x y : EuclideanSpace ℂ ι) :
    inner ℝ x y ^ 2 + inner ℝ x (Complex.I • y) ^ 2 = ‖inner ℂ x y‖ ^ 2 := by
  have e0 : ∀ u v : EuclideanSpace ℂ ι, inner ℝ u v = (inner ℂ u v).re := by
    intro u v
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    first
    | rfl
    | simp [Complex.inner, RCLike.inner_apply]
    | simp [Complex.inner, mul_comm]
  rw [e0, e0, inner_smul_right, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.I_re, Complex.I_im]
  ring

theorem fsMetric_isSmooth : IsSmoothMetric (fsMetric (ι := ι)) := by
  intro z hz
  change ContDiffWithinAt ℝ _ (fun z => ‖fsLp ι z‖) _ z
  have h0 : fsLp ι z ≠ 0 := fsLp_ne_zero hz
  have hn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℂ ι => ‖u‖) (fsLp ι z) := by
    first
    | exact contDiffAt_norm ℝ h0
    | exact contDiffAt_norm h0
  exact (hn.comp z (fsLp ι).contDiff.contDiffAt).contDiffWithinAt

theorem leviForm_fsMetric {z : ι → ℂ} (hz : z ≠ 0) (w : ι → ℂ) :
    leviForm (fun z => Real.log ((fsMetric (ι := ι)).ρ z)) z w =
      (‖fsLp ι w‖ ^ 2 * ‖fsLp ι z‖ ^ 2 - ‖inner ℂ (fsLp ι z) (fsLp ι w)‖ ^ 2) /
        (2 * (‖fsLp ι z‖ ^ 2) ^ 2) := by
  change leviForm (fun z => Real.log ‖fsLp ι z‖) z w = _
  unfold leviForm
  rw [hess_logFs hz, hess_logFs hz, fsLp_smul_I, norm_smul, Complex.norm_I, one_mul,
    ← inner_sq_add_inner_I_sq]
  have h0 := fsLp_normSq_ne_zero hz
  field_simp
  ring

theorem fsMetric_isSemipositive : IsSemipositive (fsMetric (ι := ι)) := by
  refine ⟨fsMetric_isSmooth, fun z hz w => ?_⟩
  rw [leviForm_fsMetric hz]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (fsLp ι z) (fsLp ι w)
  have h2 := mul_self_le_mul_self (norm_nonneg _) hcs
  apply div_nonneg
  · nlinarith [h2]
  · positivity

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
