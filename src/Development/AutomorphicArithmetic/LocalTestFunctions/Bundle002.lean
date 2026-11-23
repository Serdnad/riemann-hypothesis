module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.localOperator_commute_rhoF_of_trivial_at_place :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] (mw : Measure (Gw n w)) (φ : Gw n w → ℂ) (T : LL μ →L[ℂ] LL μ), IsOloc μ w mw φ T →
          ∀ h : AdelicGLn.FiniteAdelicGL K n, finAt w (finEmb K n h) = 1 → Commute T (rhoF μ h) := by
  intro K _ _ n μ _ w _ mw φ T hT h hh
  obtain ⟨-, -, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.2 h hh
  have hcomm : ∀ (g : Gw n w) (v : LL μ), rhoL μ w g (rhoF μ h v) = rhoF μ h (rhoL μ w g v) := by
    intro g v
    have e : rhoF μ (AdelicGLn.localEmbedding w g * h) = rhoF μ (h * AdelicGLn.localEmbedding w g) := by
      rw [hc g]
    rw [hmul, hmul] at e
    exact congrArg (fun S : LL μ →L[ℂ] LL μ => S v) e
  have key : ∀ u v : LL μ, ⟪u, T (rhoF μ h v)⟫_ℂ = ⟪u, rhoF μ h (T v)⟫_ℂ := by
    intro u v
    rw [← ContinuousLinearMap.adjoint_inner_left (rhoF μ h) (T v) u, hT u, hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show φ g * ⟪u, rhoL μ w g (rhoF μ h v)⟫_ℂ = φ g * ⟪ContinuousLinearMap.adjoint (rhoF μ h) u, rhoL μ w g v⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left, hcomm]
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  exact key u v
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem level_decomp (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (r : ℕ) (w : Fin r → Pl K) (hw : Function.Injective w) (J : ∀ i, Subgroup (Gw n (w i)))
    (A : LL μ →L[ℂ] LL μ) (hA : ∀ i, ∀ k ∈ J i, A ∘L rhoL μ (w i) k = A)
    (g : AdelicGLn.FiniteAdelicGL K n) (hg : ∀ i, finAt (w i) (finEmb K n g) ∈ J i) (S : Finset (Fin r)) :
    ∃ a : AdelicGLn.FiniteAdelicGL K n, A ∘L rhoF μ a = A ∧
      (∀ i ∈ S, finAt (w i) (finEmb K n a) = finAt (w i) (finEmb K n g)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), (∀ i ∈ S, v ≠ w i) → finAt v (finEmb K n a) = 1 := by
  classical
  obtain ⟨-, -, -, -, -, hmul, hone, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have e : ∀ (u : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
      finAt u (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y u := fun _ _ => rfl
  have emul : ∀ (u : HeightOneSpectrum (𝓞 K)) (y z : AdelicGLn.FiniteAdelicGL K n),
      finAt u (finEmb K n (y * z)) = finAt u (finEmb K n y) * finAt u (finEmb K n z) := by
    intro u y z
    rw [e, e, e, map_mul, RestrictedProduct.mul_apply]
  have eone : ∀ u : HeightOneSpectrum (𝓞 K), finAt u (finEmb K n 1) = 1 := by
    intro u
    rw [e, map_one, RestrictedProduct.one_apply]
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, by simp, fun v _ => eone v⟩
    rw [hone]
    exact ContinuousLinearMap.comp_id A
  | insert i S hi ih =>
    obtain ⟨a, h1, h2, h3⟩ := ih
    obtain ⟨-, l2, l3, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)
    refine ⟨a * AdelicGLn.localEmbedding (w i) (finAt (w i) (finEmb K n g)), ?_, ?_, ?_⟩
    · rw [hmul, ← ContinuousLinearMap.comp_assoc, h1]
      exact hA i _ (hg i)
    · intro j hj
      rw [emul]
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rw [l2, h3 _ (fun k hk e => hi (by rw [hw e]; exact hk)), one_mul]
      · have hne : w j ≠ w i := fun e => hi (hw e ▸ hj)
        rw [l3 _ hne, mul_one, h2 j hj]
    · intro v hv
      rw [emul, h3 v (fun j hj => hv j (Finset.mem_insert_of_mem hj)),
        l3 v (hv i (Finset.mem_insert_self _ _)), one_mul]

theorem UpperTheory.comp_proj_fixed_level_eq_of_local_invariance :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
          (r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (J : ∀ i, Subgroup (Gw n (w i))) (U US : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
          IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) →
          (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) →
          (∀ h, h ∈ US ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1) →
          ∀ A : LL μ →L[ℂ] LL μ, (∀ i, ∀ k ∈ J i, A ∘L rhoL μ (w i) k = A) → A ∘L prj (fixF μ U) = A ∘L prj (fixF μ US) := by
  intro K _ _ n μ _ m _ r w hw J U US hUo hUc hU hUS A hA
  obtain ⟨-, hmemU, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  obtain ⟨-, hmemS, b1, -, -, -, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ US
  have hle : fixF μ U ≤ fixF μ US := fun v hv => (hmemS v).2 fun u hu =>
    (hmemU v).1 hv u ((hU u).2 ⟨((hUS u).1 hu).1, fun i => by
      rw [((hUS u).1 hu).2 i]
      exact (J i).one_mem⟩)
  have hPQ : prj (fixF μ U) ∘L prj (fixF μ US) = prj (fixF μ U) := by
    unfold prj
    exact Submodule.starProjection_comp_starProjection_of_le (Submodule.topologicalClosure_mono hle)
  have hpt : ∀ g ∈ U, ∀ x ∈ fixF μ US, A (rhoF μ g x) = A x := by
    intro g hg x hx
    obtain ⟨hgi, hgJ⟩ := (hU g).1 hg
    obtain ⟨a, h1, h2, h3⟩ := level_decomp K n μ r w hw J A hA g hgJ Finset.univ
    have e : ∀ (u : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
        finAt u (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y u := fun _ _ => rfl
    have ec : ∀ u : HeightOneSpectrum (𝓞 K), finAt u (finEmb K n (a⁻¹ * g)) =
        (finAt u (finEmb K n a))⁻¹ * finAt u (finEmb K n g) := by
      intro u
      rw [e, e, e, map_mul, map_inv]
      rfl
    have hcomp : ∀ i, finAt (w i) (finEmb K n (a⁻¹ * g)) = 1 := by
      intro i
      rw [ec, h2 i (Finset.mem_univ i), inv_mul_cancel]
    have hb : a⁻¹ * g ∈ US := by
      refine (hUS _).2 ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, hcomp⟩
      rw [← e]
      by_cases hv : ∃ i, v = w i
      · obtain ⟨i, rfl⟩ := hv
        rw [hcomp i]
        exact one_mem _
      · rw [ec, h3 v (fun i _ h => hv ⟨i, h⟩), inv_one, one_mul, e]
        exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 hgi v
    have hga : rhoF μ g x = rhoF μ a x := by
      have hg' : g = a * (a⁻¹ * g) := (mul_inv_cancel_left a g).symm
      rw [hg', hmul, ContinuousLinearMap.comp_apply, (hmemS x).1 hx _ hb]
    rw [hga, ← ContinuousLinearMap.comp_apply, h1]
  have hcl : ∀ x ∈ fixF μ US, A (prj (fixF μ U) x) = A x := by
    intro x hx
    obtain ⟨e, he, hOe⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m U hUo hUc
    have hpos : (m.real U : ℝ) ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(hUo.measure_pos m ⟨1, U.one_mem⟩).ne', hUc.measure_lt_top.ne⟩
    have hO : Ofin μ m e x = ∫ h, e h • rhoF μ h x ∂m := by
      unfold Ofin
      rw [UnitaryRep.integrated_ccToL1_apply]
      rfl
    have hint : Integrable (fun h => e h • rhoF μ h x) m :=
      (e.continuous.smul (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).continuous_orbit x).comp
        MultiplicityOne.continuous_finProj)).integrable_of_hasCompactSupport e.hasCompactSupport.smul_right
    rw [← hOe, hO, ← ContinuousLinearMap.integral_comp_comm _ hint]
    have h2 : (fun h => A (e h • rhoF μ h x)) = fun h => e h • A x := by
      funext h
      rw [map_smul, he]
      by_cases hh : h ∈ U
      · rw [hpt h hh x hx]
      · rw [Set.indicator_of_notMem (show h ∉ (U : Set _) from hh), zero_smul, zero_smul]
    rw [h2, integral_smul_const]
    simp only [he]
    rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hpos), one_smul]
  refine ContinuousLinearMap.ext fun v => ?_
  have hPv : prj (fixF μ U) v = prj (fixF μ U) (prj (fixF μ US) v) := by
    rw [← ContinuousLinearMap.comp_apply, hPQ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hPv, hcl _ (b1 v)]
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.indicator_integral_away_mul_localEmbedding :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (i : Fin r) (y : Gw n (w i)) (x : AdelicGLn.FiniteAdelicGL K n),
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) (AdelicGLn.localEmbedding (w i) y * x) =
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x := by
  intro K _ _ n r w i y x
  have key : ∀ v, v ∉ Set.range w →
      finAt v (finEmb K n (AdelicGLn.localEmbedding (w i) y * x)) = finAt v (finEmb K n x) := by
    intro v hv
    have hne : v ≠ w i := fun h => hv ⟨i, h.symm⟩
    have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.1 v hne y
    have e : ∀ z : AdelicGLn.FiniteAdelicGL K n,
        finAt v (finEmb K n z) = AdelicGLn.finiteRestrictedEquiv K n z v := fun z => rfl
    rw [e] at h1
    rw [e, e, map_mul, RestrictedProduct.mul_apply, h1, one_mul]
  have hmem : (AdelicGLn.localEmbedding (w i) y * x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) ↔
      (x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) := by
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr fun v hv => by rw [key v hv]
  by_cases hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
end
