module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle008
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle004
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle002
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem finAt_mem_of_integral {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K)
    {u : AdelicGLn.FiniteAdelicGL K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    finAt w (finEmb K n u) ∈ GLnLocal.integralGL (w.adicCompletion K) n := by
  have e : finAt w (finEmb K n u) = AdelicGLn.finiteRestrictedEquiv K n u w := by
    show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n u)).2) w = _
    rw [prodEquiv_finEmb]
  rw [e]
  exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 hu w

theorem UpperTheory.ConvolutionTheory.Tf.ampComm :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (𝔞 : Amp μ),
      (∀ τ i, zc τ i ∈ Subalgebra.center ℂ (UC K n)) →
      0 ≤ 𝔞.A ∧ ‖𝔞.A‖ ≤ 1 ∧ (∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) ∧ IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
      (∀ x, Commute 𝔞.A (𝔞.Z x)) ∧ (∀ x y, Commute (𝔞.Z x) (𝔞.Z y)) ∧
      ∀ w ∉ 𝔞.S, ∀ i, Commute 𝔞.A (Tsph μ w i) ∧ ∀ x, Commute (𝔞.Z x) (Tsph μ w i) := by
  intro K _ _ _ n μ _ 𝔞 hz
  obtain ⟨-, -, a1, a2, -, -, -, -, hT⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ 𝔞.U
  obtain ⟨hconv, -, -, -, -, -, -, -, hρ⟩ := UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n))
  have hA : ∀ β : TI K n, Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U) = Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U) := fun _ => rfl
  have hOP : ∀ β : TI K n, Commute (Oinf μ 𝔞.ν β) (prj (fixF μ 𝔞.U)) := fun β => hT _ fun u _ => hρ β u
  have hPP : prj (fixF μ 𝔞.U) * prj (fixF μ 𝔞.U) = prj (fixF μ 𝔞.U) :=
    ContinuousLinearMap.ext fun v => a2 _ (a1 v)
  have hcomp : ∀ β γ : TI K n, conv 𝔞.ν β γ = conv 𝔞.ν γ β →
      Commute (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) (Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U)) := by
    intro β γ h
    have e : ∀ β γ : TI K n, (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) * (Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U)) =
        Oinf μ 𝔞.ν (conv 𝔞.ν β γ) * prj (fixF μ 𝔞.U) := by
      intro β γ
      rw [(hOP γ).symm.mul_mul_mul_comm, hPP, (hconv β γ).1]
      rfl
    show _ * _ = _ * _
    rw [e, e, h]
  have hs := 𝔞.smooth
  have hl := UpperTheory.ConvolutionTheory.Tf.lactSpec K n 𝔞.a₀ hs
  obtain ⟨-, -, hsm, -, hmul, -⟩ := hl
  have hswap : ∀ u ∈ Subalgebra.center ℂ (UC K n), ∀ β : TI K n, SmoothT β →
      conv 𝔞.ν (lact u 𝔞.a₀) β = conv 𝔞.ν 𝔞.a₀ (lact u β) := fun u hu β hβ =>
    (UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν 𝔞.a₀ β hs).2.2 inferInstance hβ u hu
  have hHop : ∀ w ∉ 𝔞.S, ∀ (x : GL (Fin n) (w.adicCompletion K)) (β : TI K n),
      Commute (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x) := by
    intro w hw x β
    have hO := GLnLocal.isOpen_integralGL (w.adicCompletion K) n
    have hC := GLnLocal.isCompact_integralGL (w.adicCompletion K) n
    have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
      (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
    have h1 : Commute (Oinf μ 𝔞.ν β) (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x) :=
      (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w _ x hO hC).2.2.2.2.1 _ fun g => hρ β _
    have h2 := (UpperTheory.ConvolutionTheory.Tf.hopLevel K n μ (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) w _ x 𝔞.U hO hC 𝔞.isOpen hUc
      (𝔞.max w hw) fun u hu => finAt_mem_of_integral w (𝔞.le hu)).1
    exact h1.mul_left h2.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hpos : (Oinf μ 𝔞.ν 𝔞.a₀).IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive).1 𝔞.pos
    have hadj : ContinuousLinearMap.adjoint (prj (fixF μ 𝔞.U)) = prj (fixF μ 𝔞.U) :=
      (isSelfAdjoint_starProjection _).adjoint_eq
    have h := hpos.conj_adjoint (prj (fixF μ 𝔞.U))
    rw [hadj] at h
    have e : prj (fixF μ 𝔞.U) ∘L Oinf μ 𝔞.ν 𝔞.a₀ ∘L prj (fixF μ 𝔞.U) = 𝔞.A := by
      show prj (fixF μ 𝔞.U) * (Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U)) = Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U)
      rw [← mul_assoc, ← (hOP _).eq, mul_assoc, hPP]
    rw [e] at h
    exact (ContinuousLinearMap.nonneg_iff_isPositive).2 h
  · calc ‖𝔞.A‖ ≤ ‖Oinf μ 𝔞.ν 𝔞.a₀‖ * ‖prj (fixF μ 𝔞.U)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul 𝔞.norm_le (Submodule.starProjection_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro v
    have e : 𝔞.A v = prj (fixF μ 𝔞.U) (Oinf μ 𝔞.ν 𝔞.a₀ v) :=
      congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hOP 𝔞.a₀).eq
    rw [e]
    exact a1 _
  · exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
  · intro x
    exact hcomp _ _ (hswap _ (hz x.1 x.2) _ hs).symm
  · intro x y
    refine hcomp _ _ ?_
    rw [hswap _ (hz x.1 x.2) _ (hsm _).1, hswap _ (hz y.1 y.2) _ (hsm _).1, ← (hmul _ _).1, ← (hmul _ _).1,
      (Subalgebra.mem_center_iff.1 (hz x.1 x.2) (zc y.1 y.2))]
  · intro w hw i
    refine ⟨(hHop w hw _ _).smul_right _, fun x => (hHop w hw _ _).smul_right _⟩
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem UpperTheory.ConvolutionTheory.Tf.height_centralSection_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (s : {r : ℝ // 0 < r}) {L : ℝ} (hL : 1 ≤ L) (h1 : (s : ℝ) ≤ L) (h2 : (s : ℝ)⁻¹ ≤ L) :
    AutomorphicForm.height (centralSection K n s) ≤ L ^ (2 * Fintype.card (InfinitePlace K)) := by
  set e : ℝ := ((n * Module.finrank ℚ K : ℝ))⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, ← Nat.cast_mul]
    exact Nat.cast_inv_le_one _
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ L → x ^ e ≤ L := fun x hx hxL =>
    calc x ^ e ≤ L ^ e := Real.rpow_le_rpow hx hxL he0
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL he1
      _ = L := Real.rpow_one L
  refine height_diagUnits_posIdele_le (K := K) (n := n) (ρ := fun _ => (s : ℝ) ^ e)
    (fun _ => Real.rpow_pos_of_pos s.2 e) hL fun _ => ⟨key _ s.2.le h1, ?_⟩
  rw [← Real.inv_rpow s.2.le]
  exact key _ (inv_pos.2 s.2).le h2

theorem UpperTheory.ConvolutionTheory.Tf.htProj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (c : ℕ), 1 ≤ C ∧ ∀ g : AdelicGLn.AdelicGL K n,
      AutomorphicForm.height (retractOne g : AdelicGLn.AdelicGL K n) ≤ C * AutomorphicForm.height g ^ c := by
  intro K _ _ n
  obtain ⟨D, N, -, hD⟩ := UpperTheory.adelicNorm_det_le_height_pow K n
  set m := 2 * Fintype.card (InfinitePlace K) with hm
  have hC : 1 ≤ heightConst K n := one_le_heightConst
  have hD1 : (1 : ℝ) ≤ max 1 D := le_max_left _ _
  refine ⟨heightConst K n * max 1 D ^ m, N * m + 1,
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD1), fun g => ?_⟩
  have hg := one_le_height g
  have hb : ∀ x : AdelicGLn.AdelicGL K n, AutomorphicForm.height x = AutomorphicForm.height g →
      (detModule K n x : ℝ) ≤ max 1 D * AutomorphicForm.height g ^ N := fun x hx => by
    refine (hD x).trans ?_
    rw [hx]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have h2 : (detModule K n g : ℝ)⁻¹ ≤ max 1 D * AutomorphicForm.height g ^ N := by
    have := hb g⁻¹ (height_inv g)
    rwa [map_inv, Positive.coe_inv] at this
  have hz := UpperTheory.ConvolutionTheory.Tf.height_centralSection_le K n (detModule K n g)
    (one_le_mul_of_one_le_of_one_le hD1 (one_le_pow₀ hg)) (hb g rfl) h2
  rw [coe_retractOne]
  refine (height_mul_le _ _).trans ?_
  rw [height_inv]
  calc heightConst K n * AutomorphicForm.height g *
        AutomorphicForm.height (centralSection K n (detModule K n g))
      ≤ heightConst K n * AutomorphicForm.height g * (max 1 D * AutomorphicForm.height g ^ N) ^ m :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring
end
