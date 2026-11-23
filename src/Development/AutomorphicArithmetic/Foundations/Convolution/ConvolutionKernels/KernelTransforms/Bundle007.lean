module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle006
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem finprod_fib {A B M : Type*} [CommMonoid M] (π : A → B) (p : A → B → Prop)
    (hp : ∀ a b, p a b ↔ π a = b) (f : A → M) (hf : (Function.mulSupport f).Finite) :
    ∏ᶠ b : B, ∏ᶠ a : {a : A // p a b}, f a.1 = ∏ᶠ a : A, f a := by
  classical
  have hG : ∀ b, ∏ᶠ a : {a : A // p a b}, f a.1 = ∏ a ∈ hf.toFinset with π a = b, f a := by
    intro b
    rw [finprod_subtype_eq_finprod_cond]
    refine finprod_cond_eq_prod_of_cond_iff _ fun {x} hx => ?_
    simp [hp, Function.mem_mulSupport, hx]
  simp_rw [hG]
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf subset_rfl]
  rw [finprod_eq_prod_of_mulSupport_subset (s := hf.toFinset.image π)]
  · exact Finset.prod_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) f
  · intro b hb
    by_contra hb'
    refine hb ?_
    refine Finset.prod_eq_one fun x hx => ?_
    exfalso
    rw [Finset.mem_filter] at hx
    exact hb' (by simpa using ⟨x, by simpa using hx.1, hx.2⟩)

theorem UpperTheory.ConvolutionTheory.Tf.tensEProd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
      (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
      (∀ᶠ w : Pl E in Filter.cofinite, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator 1) →
      ∀ g : AdelicGLn.AdelicGL E n,
        ∏ᶠ v : Pl F, GM.prodFn (v := v) (fun w => h w.1) (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = ∏ᶠ w : Pl E, h w (finAt w g) := by
  intro F E _ _ _ _ _ n h hh g
  have hS : (Function.mulSupport fun w : Pl E => h w (finAt w g)).Finite := by
    have hev : ∀ᶠ w : Pl E in Filter.cofinite, h w (finAt w g) = 1 := by
      filter_upwards [hh, AdelicGLn.eventually_mem_integralGL E n g] with w h1 h2
      rw [h1, Set.indicator_of_mem (by exact h2)]
      rfl
    exact Filter.eventually_cofinite.1 hev
  have e : ∀ v : Pl F, GM.prodFn (v := v) (fun w => h w.1) (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g)
      = ∏ᶠ w : {w : Pl E // w.asIdeal.LiesOver v.asIdeal}, h w.1 (finAt w.1 g) := by
    intro v
    refine finprod_congr fun w => ?_
    have : GM.cmp w (PositivityTheory.Rg.Tf.Geo.mapGL n (PositivityTheory.Rg.Tf.Geo.atFin v) g) = finAt w.1 g := by
      ext i j
      rfl
    rw [this]
  simp_rw [e]
  refine finprod_fib (fun w : Pl E => w.under (𝓞 F)) (fun w v => w.asIdeal.LiesOver v.asIdeal) ?_ _ hS
  intro w v
  constructor
  · intro hl
    ext1
    exact (hl.over).symm
  · rintro rfl
    exact ⟨rfl⟩
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.compatEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
      (∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ (ν : Measure (archGroup K n)) (_ : ν.IsHaarMeasure), Compat μ ν m) ∧
      (∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure], ∃ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) (_ : m.IsHaarMeasure), Compat μ ν m) ∧
      ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ (μ : Measure (normOneGL (K := K) (n := n))) (_ : μ.IsHaarMeasure), Compat μ ν m := by
  intro K _ _ n hn
  have main : ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
      (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ c : NNReal, c ≠ 0 ∧
      Compat μ (c • ν) m ∧ Compat μ ν (c • m) ∧ Compat (c⁻¹ • μ) ν m := by
    intro μ _ ν _ m _
    obtain ⟨c, hc, h⟩ := UpperTheory.ConvolutionTheory.Tf.tensMeas K n hn μ ν m
    lift c to NNReal using hc.le
    have h' : ∀ (β : TI K n) (e : TF K n) (Θ : normOneGL (K := K) (n := n) → ℂ), Continuous Θ → ∫ x, tens β e x * Θ x ∂μ =
        ((c : ℝ) : ℂ) * ∫ a, ∫ y, β a * e y * Θ (archP K n a * MultiplicityOne.finProj K n y) ∂m ∂ν := fun β e Θ hΘ => by
      rw [← h β e Θ hΘ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1 x]
      rfl
    have hc0 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    refine ⟨c, by exact_mod_cast hc.ne', fun β e Θ hΘ => ?_, fun β e Θ hΘ => ?_, fun β e Θ hΘ => ?_⟩
    · rw [h' β e Θ hΘ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · rw [h' β e Θ hΘ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      dsimp only
      rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · rw [integral_smul_nnreal_measure, h' β e Θ hΘ, NNReal.smul_def, Complex.real_smul, ← mul_assoc, NNReal.coe_inv,
        Complex.ofReal_inv, inv_mul_cancel₀ hc0, one_mul]
  refine ⟨fun μ _ m _ => ?_, fun μ _ ν _ => ?_, fun ν _ m _ => ?_⟩
  · obtain ⟨c, hc, h, -, -⟩ := main μ Measure.haar m
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ hc, h⟩
  · obtain ⟨c, hc, -, h, -⟩ := main μ ν Measure.haar
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ hc, h⟩
  · obtain ⟨c, hc, -, -, h⟩ := main Measure.haar ν m
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hc), h⟩
end
