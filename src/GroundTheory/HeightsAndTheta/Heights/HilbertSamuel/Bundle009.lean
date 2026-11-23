module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle007
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology ComplexConjugate

noncomputable section

namespace LeviFSInvariant

variable {J : Type} [Fintype J]

def sqSum (z : J → ℂ) : ℝ := ∑ p, ‖z p‖ ^ 2

def reInner (a : J → ℂ) : (J → ℂ) →L[ℝ] ℝ :=
  ∑ p, ((a p).re • (Complex.reCLM.comp (ContinuousLinearMap.proj p)) +
    (a p).im • (Complex.imCLM.comp (ContinuousLinearMap.proj p)))

theorem reInner_apply (a b : J → ℂ) :
    reInner a b = ∑ p, ((a p).re * (b p).re + (a p).im * (b p).im) := by
  simp [reInner]

theorem reInner_comm (a b : J → ℂ) : reInner a b = reInner b a := by
  simp only [reInner_apply]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem reInner_self (a : J → ℂ) : reInner a a = sqSum a := by
  simp only [reInner_apply, sqSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]

theorem continuous_sqSum : Continuous (sqSum : (J → ℂ) → ℝ) := by
  unfold sqSum
  fun_prop

theorem hasFDerivAt_sqSum (z : J → ℂ) : HasFDerivAt sqSum ((2 : ℝ) • reInner z) z := by
  have h := HasFDerivAt.sum (u := Finset.univ) (A := fun p (x : J → ℂ) => ‖x p‖ ^ 2)
    fun p _ => (hasFDerivAt_apply p z).norm_sq
  rw [show (∑ p ∈ Finset.univ, fun x : J → ℂ => ‖x p‖ ^ 2) = sqSum from by
    funext x; simp [sqSum, Finset.sum_apply]] at h
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, reInner_apply, Complex.inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

def phi (z : J → ℂ) : ℝ := Real.log (sqSum z) * (1 / 2)

theorem hasFDerivAt_phi {z : J → ℂ} (hz : sqSum z ≠ 0) :
    HasFDerivAt phi ((sqSum z)⁻¹ • reInner z) z := by
  have h := ((hasFDerivAt_sqSum z).log hz).mul_const (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

theorem contDiffAt_phi {z : J → ℂ} (hz : sqSum z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n phi z := by
  have hs : ContDiff ℝ n (sqSum : (J → ℂ) → ℝ) :=
    ContDiff.sum fun p _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) p)
  exact (hs.contDiffAt.log hz).mul contDiffAt_const

theorem fderiv_fderiv_phi {z : J → ℂ} (hz : sqSum z ≠ 0) (u : J → ℂ) :
    fderiv ℝ (fderiv ℝ phi) z u u =
      sqSum u / sqSum z - 2 * reInner z u ^ 2 / sqSum z ^ 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ phi) z :=
    ((contDiffAt_phi hz (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : fderiv ℝ (fderiv ℝ phi) z u u = fderiv ℝ (fun z' => fderiv ℝ phi z' u) z u := by
    rw [fderiv_clm_apply hd (differentiableAt_const u)]
    simp
  have hopen : IsOpen {z' : J → ℂ | sqSum z' ≠ 0} := isOpen_ne_fun continuous_sqSum continuous_const
  have heq : (fun z' => fderiv ℝ phi z' u) =ᶠ[𝓝 z]
      fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z' := by
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    rw [(hasFDerivAt_phi hz').fderiv]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      reInner_comm z' u]
    ring
  have hinv := (hasFDerivAt_inv hz).comp z (hasFDerivAt_sqSum z)
  have hG := (reInner u).hasFDerivAt.mul hinv
  rw [h1, heq.fderiv_eq]
  rw [show (fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z') =
    (⇑(reInner u) * ((fun x : ℝ => x⁻¹) ∘ sqSum)) from rfl, hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, reInner_self, reInner_comm u z]
  field_simp
  ring

theorem leviForm_phi {z : J → ℂ} (hz : sqSum z ≠ 0) (w : J → ℂ) :
    leviForm phi z w = (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) /
      (2 * sqSum z ^ 2) := by
  have hw : sqSum (Complex.I • w) = sqSum w := by
    simp [sqSum]
  unfold leviForm
  rw [fderiv_fderiv_phi hz, fderiv_fderiv_phi hz, hw]
  field_simp
  ring

def herm (a b : J → ℂ) : ℂ := ∑ p, conj (a p) * b p

theorem herm_self (a : J → ℂ) : herm a a = (sqSum a : ℂ) := by
  simp only [herm, sqSum, Complex.ofReal_sum, Complex.ofReal_pow]
  exact Finset.sum_congr rfl fun p _ => Complex.conj_mul' (a p)

theorem herm_swap (a b : J → ℂ) : herm b a = conj (herm a b) := by

  simp only [herm, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem reInner_sq_add (a b : J → ℂ) :
    ((reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2 : ℝ) : ℂ) = herm a b * herm b a := by
  have hre : (herm a b).re = reInner a b := by
    simp only [herm, Complex.re_sum, reInner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    exact Finset.sum_congr rfl fun p _ => by ring
  have him : (herm a b).im = -reInner a (Complex.I • b) := by
    simp only [herm, Complex.im_sum, reInner_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [herm_swap a b, Complex.mul_conj, Complex.normSq_apply, hre, him]
  push_cast
  ring

theorem herm_smul_left (c : ℂ) (a b : J → ℂ) : herm (c • a) b = conj c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem herm_add_right (a b b' : J → ℂ) : herm a (b + b') = herm a b + herm a b' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem herm_add_left (a a' b : J → ℂ) : herm (a + a') b = herm a b + herm a' b := by
  simp only [herm, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem herm_smul_right (c : ℂ) (a b : J → ℂ) : herm a (c • b) = c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem sqSum_ne_zero {a : J → ℂ} (ha : a ≠ 0) : sqSum a ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
  exact Finset.single_le_sum (f := fun p => ‖a p‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end LeviFSInvariant


open LeviFSInvariant in
theorem LeviFSInvariant.proof : LeviFSInvariant.Statement := by
  intro M _ a b c μ ha hc
  have hf : (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) = phi := by
    funext u
    simp only [phi, sqSum]
    ring
  have hca : c • a ≠ 0 := smul_ne_zero hc ha
  rw [hf, leviForm_phi (sqSum_ne_zero hca), leviForm_phi (sqSum_ne_zero ha)]
  have hS : sqSum (c • a) = ‖c‖ ^ 2 * sqSum a := by
    apply Complex.ofReal_injective
    rw [← herm_self, herm_smul_left, herm_smul_right, herm_self]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have key : ∀ a b : M → ℂ,
      ((sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2) : ℝ) : ℂ) =
        herm a a * herm b b - herm a b * herm b a := by
    intro a b
    rw [Complex.ofReal_sub, Complex.ofReal_mul, reInner_sq_add, herm_self, herm_self]
  have hN' : herm (c • a) (c • a) * herm (c • b + μ • a) (c • b + μ • a) -
      herm (c • a) (c • b + μ • a) * herm (c • b + μ • a) (c • a) =
      (((‖c‖ ^ 2) ^ 2 : ℝ) : ℂ) * (herm a a * herm b b - herm a b * herm b a) := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have hN : sqSum (c • a) * sqSum (c • b + μ • a) -
      (reInner (c • a) (c • b + μ • a) ^ 2 + reInner (c • a) (Complex.I • (c • b + μ • a)) ^ 2) =
      (‖c‖ ^ 2) ^ 2 * (sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2)) := by
    apply Complex.ofReal_injective
    rw [key, Complex.ofReal_mul, key, hN']
  rw [hN, hS]
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormCharpoly

theorem aeval_mul_of_isHomogeneous {σ' Ω : Type*} [Field Ω] [CharZero Ω] {p : MvPolynomial σ' ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (μ : Ω) (f : σ' → Ω) :
    aeval (fun j => μ * f j) p = μ ^ d * aeval f p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end FibreNormCharpoly

namespace ProjLine

open ProjLine

end ProjLine

namespace FibreNormCharpoly

open ProjLine

end FibreNormCharpoly

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X]

structure HolLineBundle (A : FinHolAtlas D X) where

  g : Fin A.n → Fin A.n → X → ℂ
  holo : ∀ j k, A.HoloOn ((A.chart j).source ∩ (A.chart k).source) (g j k)
  ne_zero : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, g j k x ≠ 0
  cocycle : ∀ j k l, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source ∩ (A.chart l).source,
    g j l x = g j k x * g k l x

namespace HolLineBundle

variable {A : FinHolAtlas D X} (L : HolLineBundle A)

def sections (n : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
    (∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = L.g j k x ^ n * f k x) ∧
    ∀ j, ∀ x ∉ (A.chart j).source, f j x = 0}
  add_mem' := by
    rintro f f' ⟨hf, hc, hz⟩ ⟨hf', hc', hz'⟩
    refine ⟨fun j k => (hf j k).add (hf' j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.add_apply, hc j k x hx, hc' j k x hx]; ring
    · simp [hz j x hx, hz' j x hx]
  zero_mem' := by
    refine ⟨fun j k => ?_, fun j k x _ => by simp, fun j x _ => rfl⟩
    exact analyticOnNhd_const
  smul_mem' := by
    rintro c f ⟨hf, hc, hz⟩
    refine ⟨fun j k => analyticOnNhd_const.mul (hf j k), fun j k x hx => ?_, fun j x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hc j k x hx]; ring
    · simp [hz j x hx]

end HolLineBundle

structure Weight {A : FinHolAtlas D X} (L : HolLineBundle A) where

  φ : Fin A.n → X → ℝ
  smooth : ∀ j, A.SmoothOn (A.chart j).source (φ j)
  compat : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L.g j k x‖ ^ 2)

namespace Weight

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def IsSemipositive (W : Weight L) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, ∀ w : Fin D → ℂ, 0 ≤ levi (W.φ j ∘ (A.chart j).symm) y w

def lerp (W₀ W₁ : Weight L) (t : ℝ) : Weight L where
  φ j x := W₀.φ j x + t * (W₁.φ j x - W₀.φ j x)
  smooth j k := (W₀.smooth j k).add (contDiffOn_const.mul ((W₁.smooth j k).sub (W₀.smooth j k)))
  compat j k x hx := by rw [W₀.compat j k x hx, W₁.compat j k x hx]; ring

def diff (W₁ W₀ : Weight L) (x : X) : ℝ :=
  W₁.φ (chartIdx A x) x - W₀.φ (chartIdx A x) x

theorem diff_eq (W₁ W₀ : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    diff W₁ W₀ x = W₁.φ j x - W₀.φ j x := by
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  rw [diff, W₁.compat (chartIdx A x) j x ⟨hi, hx⟩, W₀.compat (chartIdx A x) j x ⟨hi, hx⟩]
  ring

end Weight

structure SmoothVolume [MeasurableSpace X] (A : FinHolAtlas D X) where

  μ : Measure X
  isProb : IsProbabilityMeasure μ

  dens : Fin A.n → (Fin D → ℂ) → ℝ
  smooth : ∀ j, ContDiffOn ℝ ∞ (dens j) (A.chart j).target
  pos : ∀ j, ∀ y ∈ (A.chart j).target, 0 < dens j y
  chart_lintegral : ∀ j (g : X → ℝ≥0∞), Measurable g →
    ∫⁻ x in (A.chart j).source, g x ∂μ =
      ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (dens j y)

variable {A : FinHolAtlas D X} {L : HolLineBundle A}

def ptNormSq (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) : ℝ :=
  ‖s (chartIdx A x) x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x)

variable [MeasurableSpace X]

def sectionL2NormSq (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) : ℝ :=
  ∫ x, ptNormSq W n s x ∂dV.μ

def bergman (W : Weight L) (dV : SmoothVolume A) (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ)
    (x : X) : ℝ :=
  ⨆ s : V, ptNormSq W n (s : Fin A.n → X → ℂ) x / sectionL2NormSq W dV n s

def chernTopDens (W : Weight L) (j : Fin A.n) (y : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ j ∘ (A.chart j).symm) y).det).re

def bergmanDens (W : Weight L) (dV : SmoothVolume A) (x : X) : ℝ :=
  chernTopDens W (chartIdx A x) (A.chart (chartIdx A x) x) /
    ((D.factorial : ℝ) * dV.dens (chartIdx A x) (A.chart (chartIdx A x) x))

def gram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} (e : ι → Fin A.n → X → ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun a b => ∫ x, e a (chartIdx A x) x * conj (e b (chartIdx A x) x) *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ) ∂dV.μ

def chiGram (W : Weight L) (dV : SmoothVolume A) (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → Fin A.n → X → ℂ) : ℝ :=
  -(1 / 2) * Real.log (gram W dV n e).det.re

end

noncomputable def gaussDiscMass (lam R : ℝ) : ℝ :=
  if lam = 0 then Real.pi * R ^ 2 else Real.pi * (1 - Real.exp (-lam * R ^ 2)) / lam

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRationalProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_prod_zpow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g d) :
    aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  have hsub : ∀ f : (Σ k, ι k) → Ω, ∏ p ∈ m.support, f p ^ m p = ∏ p, f p ^ m p := fun f =>
    Finset.prod_subset (Finset.subset_univ _) (fun p _ hp => by simp [Finsupp.notMem_support_iff.mp hp])
  have hden : ∏ p, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [hsub, div_pow, Finset.prod_div_distrib, hden, zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
  ring


end NmSectionsRationalProof


end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComplexFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    P.IsPrime → IsRelevant P →
    ∀ F : MvPolynomial (Σ k, ι k) ℂ, (∀ z ∈ mcPts P, eval z F = 0) →
      F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
