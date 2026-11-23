module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle005
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.DerivInt
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem commute_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H) (h1 : ∀ v ∈ V, T v ∈ V)
    (h2 : ∀ v ∈ V, ContinuousLinearMap.adjoint T v ∈ V) :
    (∀ v, prj V v ∈ V) ∧ (∀ v ∈ V, prj V v = v) ∧ (∀ v, ∀ w ∈ V, ⟪v - prj V v, w⟫_ℂ = 0) ∧ Commute T (prj V) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  have a1 : ∀ v, prj V v ∈ V := fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v)
  have a3 : ∀ v, ∀ w ∈ V, ⟪v - prj V v, w⟫_ℂ = 0 := fun v w hw =>
    Submodule.starProjection_inner_eq_zero v w ((hm _).2 hw)
  refine ⟨a1, fun v hv => Submodule.starProjection_eq_self_iff.2 ((hm _).2 hv), a3, ?_⟩
  refine ContinuousLinearMap.ext fun v => ?_
  show T (prj V v) = prj V (T v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm _).2 (h1 _ (a1 v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact a3 v _ (h2 w ((hm _).1 hw))

theorem UpperTheory.ConvolutionTheory.Tf.commPrj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
      IsClosed (fixF μ U : Set (LL μ)) ∧ (∀ v, v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v) ∧ (∀ v, prj (fixF μ U) v ∈ fixF μ U) ∧
      (∀ v ∈ fixF μ U, prj (fixF μ U) v = v) ∧ (∀ u ∈ U, rhoF μ u ∘L prj (fixF μ U) = prj (fixF μ U) ∧ prj (fixF μ U) ∘L rhoF μ u = prj (fixF μ U)) ∧
      (∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h') ∧ rhoF μ 1 = 1 ∧ (∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹) ∧
      ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → Commute T (prj (fixF μ U)) := by
  intro K _ _ n μ _ U
  have hmem : ∀ v, v ∈ fixF μ U ↔ ∀ u ∈ U, rhoF μ u v = v := fun v => by
    simp only [fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  have hcl : IsClosed (fixF μ U : Set (LL μ)) := by
    have : (fixF μ U : Set (LL μ)) = ⋂ u ∈ U, {v | rhoF μ u v = v} := by
      ext v
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_biInter fun u _ => isClosed_eq (rhoF μ u).continuous continuous_id
  have hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h' := fun h h' => by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [rhoF, map_mul, UnitaryRep.map_mul_apply, ContinuousLinearMap.comp_apply]
  have hone : rhoF μ 1 = 1 := by
    simp only [rhoF, map_one, UnitaryRep.map_one]
  have hadj : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹ := fun h => by
    unfold rhoF
    rw [UnitaryRep.adjoint_map, map_inv (MultiplicityOne.finProj K n)]
  have hpres : ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → ∀ v ∈ fixF μ U, T v ∈ fixF μ U := by
    intro T hT v hv
    rw [hmem] at hv ⊢
    intro u hu
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hT u hu).eq
    simp only [ContinuousLinearMap.mul_apply, hv u hu] at this
    exact this.symm
  have hT : ∀ T : LL μ →L[ℂ] LL μ, (∀ u ∈ U, Commute T (rhoF μ u)) → Commute T (prj (fixF μ U)) := by
    intro T hT
    refine (commute_prj _ hcl T (hpres T hT) (hpres _ fun u hu => ?_)).2.2.2
    have := (hT u⁻¹ (U.inv_mem hu)).star_star
    rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, hadj, inv_inv] at this
  obtain ⟨a1, a2, -, -⟩ := commute_prj _ hcl 0 (fun v _ => by simp) (fun v _ => by simp)
  have hl : ∀ u ∈ U, rhoF μ u ∘L prj (fixF μ U) = prj (fixF μ U) := fun u hu =>
    ContinuousLinearMap.ext fun v => (hmem _).1 (a1 v) u hu
  refine ⟨hcl, hmem, a1, a2, fun u hu => ⟨hl u hu, ?_⟩, hmul, hone, hadj, hT⟩
  have hfix : ∀ u ∈ U, ∀ v ∈ fixF μ U, rhoF μ u v ∈ fixF μ U := fun u hu v hv => by
    rw [(hmem v).1 hv u hu]; exact hv
  have hc := (commute_prj _ hcl (rhoF μ u) (hfix u hu) (by rw [hadj]; exact hfix _ (U.inv_mem hu))).2.2.2
  exact hc.eq.symm.trans (hl u hu)
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem integrable_slice {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (a : archGroup K n) :
    Integrable (fun s => β (a * zInf K n s)) GroundTheory.Global.posRealMeasure := by
  have hc : Continuous fun s : {r : ℝ // 0 < r} => β (a * zInf K n s) :=
    β.continuous.comp (continuous_const.mul continuous_zInf)
  refine hc.integrable_of_hasCompactSupport ?_
  have hD : IsCompact ((fun r : {r : ℝ // 0 < r} => r * (detA K n a)⁻¹) '' (detA K n '' tsupport β)) :=
    (β.hasCompactSupport.isCompact.image continuous_detA).image (continuous_id.mul continuous_const)
  refine HasCompactSupport.intro hD fun s hs => ?_
  by_contra hne
  exact hs ⟨s * detA K n a, mem_of_kernel_ne_zero hn hne, by simp⟩

private theorem kbar_add {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β β' : TI K n) (a : archGroup K n) : kbar (β + β' : TI K n) a = kbar β a + kbar β' a := by
  simp only [kbar, CompactlySupportedContinuousMap.add_apply]
  exact integral_add (integrable_slice hn β a) (integrable_slice hn β' a)

private theorem kbar_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (c : ℂ) (β : TI K n) (a : archGroup K n) : kbar (c • β : TI K n) a = c * kbar β a := by
  simp only [kbar, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

private theorem tensFun_support_bound {K : Type} [Field K] [NumberField K] {n : ℕ}
    (hn : 0 < n) (β : TI K n) (e : TF K n) :
    IsCompact (archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) ∧
      Function.support (tensFun β e) ⊆
        archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e := by
  refine ⟨(β.hasCompactSupport.isCompact.image continuous_archP).mul
    (e.hasCompactSupport.isCompact.image MultiplicityOne.continuous_finProj), ?_⟩
  intro x hx
  let a := infPart K n (x : AdelicGLn.AdelicGL K n)
  let h := finPart K n (x : AdelicGLn.AdelicGL K n)
  change kbar β a * e h ≠ 0 at hx
  have he := right_ne_zero_of_mul hx
  obtain ⟨s, hs⟩ : ∃ s, β (a * zInf K n s) ≠ 0 := by
    by_contra h0
    simp only [not_exists, ne_eq, not_not] at h0
    exact left_ne_zero_of_mul hx (by simp [kbar, h0])
  have hproj : archP K n (a * zInf K n s) * MultiplicityOne.finProj K n h = x := by
    have hf : MultiplicityOne.finProj K n h = retractOne (finEmb K n h) := rfl
    rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul]
    change retractOne (infEmb K n (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      finEmb K n (finPart K n (x : AdelicGLn.AdelicGL K n))) = x
    rw [infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
  rw [← hproj]
  exact Set.mul_mem_mul ⟨_, subset_tsupport _ hs, rfl⟩ ⟨_, subset_tsupport _ he, rfl⟩

private theorem tens_apply' {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (e : TF K n) (x : normOneGL (K := K) (n := n)) : tens β e x = tensFun β e x := by
  have h1 : Continuous (tensFun β e) := by
    unfold tensFun
    exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
      (continuous_infPart.comp continuous_subtype_val)).mul
      (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
  obtain ⟨hC, hS⟩ := tensFun_support_bound hn β e
  have h2 : HasCompactSupport (tensFun β e) :=
    hC.of_isClosed_subset isClosed_closure (closure_minimal hS hC.isClosed)
  have h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e) := ⟨h1, h2⟩
  rw [tens, dite_eq_left h]
  rfl

theorem UpperTheory.ConvolutionTheory.Tf.tensApply :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n), (∀ x, tens β e x = tensFun β e x) ∧
      (tsupport (tens β e) ⊆ archP K n '' tsupport β * MultiplicityOne.finProj K n '' tsupport e) ∧
      (∀ β', tens (β + β') e = tens β e + tens β' e) ∧ (∀ e', tens β (e + e') = tens β e + tens β e') ∧
      ∀ c : ℂ, tens (c • β) e = c • tens β e ∧ tens β (c • e) = c • tens β e := by
  intro K _ _ n hn β e
  refine ⟨tens_apply' hn β e, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hC, hS⟩ := tensFun_support_bound hn β e
    refine closure_minimal ?_ hC.isClosed
    intro x hx
    apply hS
    rwa [Function.mem_support, ← tens_apply' hn β e x]
  · intro β'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, kbar_add hn, add_mul]
  · intro e'
    ext x
    simp only [CompactlySupportedContinuousMap.add_apply, tens_apply' hn, tensFun, mul_add]
  · intro c
    constructor
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, kbar_smul,
        smul_eq_mul, mul_assoc]
    · ext x
      simp only [CompactlySupportedContinuousMap.smul_apply, tens_apply' hn, tensFun, smul_eq_mul]
      ring
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

open Matrix GlobalTheory.CuspRep in
private theorem matEq_exp (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ)
    (X : Matrix (Fin n) (Fin n) (Cinf K)) :
    UpperTheory.V.Cm.matEq K n (NormedSpace.exp X) = NormedSpace.exp (UpperTheory.V.Cm.matEq K n X) := by
  letI : Algebra ℚ (ArchMatrix K n) := Algebra.compHom _ (algebraMap ℚ ℝ)
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.map_exp (𝔸 := Matrix (Fin n) (Fin n) (Cinf K)) (UpperTheory.V.Cm.matEq K n)
    (show Continuous (UpperTheory.V.Cm.matEq K n) from (UpperTheory.V.Cm.archEq K n).continuous) X

theorem UpperTheory.ConvolutionTheory.Tf.expGen :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ),
      Subgroup.closure (Set.range (isExpLieAlgebra K n).expG) = ⊤ := by
  intro K _ _ _ n
  rw [eq_top_iff]
  intro z _
  have key := UpperTheory.V.AlgRepEndIrreducible.expGen K n
    ((Subgroup.closure (Set.range (isExpLieAlgebra K n).expG)).toSubmonoid.comap
      (UpperTheory.V.Cm.grpEq K n).toMonoidHom) ?_ ((UpperTheory.V.Cm.grpEq K n).symm z)
  · simpa using key
  · intro X y hy
    refine Subgroup.subset_closure ⟨⟨UpperTheory.V.Cm.matEq K n X, Submodule.mem_top⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    change NormedSpace.exp (UpperTheory.V.Cm.matEq K n X) = UpperTheory.V.Cm.matEq K n y.val
    rw [hy, matEq_exp]
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.sliceAct :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : CompactlySupportedContinuousMap (archGroup K n) ℂ)
      (hβ : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (Φ : normOneGL (K := K) (n := n) → ℂ), Continuous Φ →
      ∃ hF : liftOne (fun x => ∫ a, β a * Φ (x * archP K n a) ∂ν) ∈ archSmooth K n, ∀ (u : UEnv K n) (g : AdelicGLn.AdelicGL K n),
        (uAction u ⟨_, hF⟩ : AdelicGLn.AdelicGL K n → ℂ) g =
          ∫ a, ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β g⁻¹, hβ⟩ : archGroup K n → ℂ) a⁻¹ * Φ (retractOne g * archP K n a) ∂ν := by
  intro K _ _ n ν _ β hβ Φ hΦ
  have hc : HasCompactSupport (fun g : archGroup K n => β g⁻¹) :=
    β.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
  have hΘ : ∀ g : AdelicGLn.AdelicGL K n,
      Continuous (fun a : archGroup K n => Φ (retractOne g * archP K n a)) := fun g =>
    hΦ.comp (continuous_const.mul continuous_archP)
  have hs : ∀ g : AdelicGLn.AdelicGL K n,
      archSlice (liftOne (fun x => ∫ a, β a * Φ (x * archP K n a) ∂ν)) g =
        fun x => ∫ a, (fun g : archGroup K n => β g⁻¹) (a⁻¹ * x) * Φ (retractOne g * archP K n a) ∂ν := by
    intro g
    funext x
    rw [archSlice_apply, liftOne, retractOne_mul_infEmb,
      ← integral_mul_left_eq_self (μ := ν) (fun a => (fun g : archGroup K n => β g⁻¹) (a⁻¹ * x) *
        Φ (retractOne g * archP K n a)) x]
    congr 1
    funext a
    simp [map_mul, mul_assoc]
  have hD := fun g => UpperTheory.ConvolutionTheory.Tf.derivInt K n ν _ hβ hc _ (hΘ g)
  refine ⟨fun g => by rw [hs g]; exact (hD g).1, fun u g => ?_⟩
  obtain ⟨hF, h⟩ := hD g
  have h1 := h u 1
  simp only [mul_one] at h1
  rw [coe_uAction, uActFun, ← h1]
  exact congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f :
    (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) 1) (Subtype.ext (hs g))
end

section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.tensCont :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : CompactlySupportedContinuousMap (archGroup K n) ℂ) (e : CompactlySupportedContinuousMap (AdelicGLn.FiniteAdelicGL K n) ℂ),
    (Continuous fun x : normOneGL (K := K) (n := n) => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    (HasCompactSupport fun x : normOneGL (K := K) (n := n) => kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n))) ∧
    ∀ x : normOneGL (K := K) (n := n), kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
  intro K _ _ n hn β e
  have key : ∀ x : normOneGL (K := K) (n := n), kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) *
      e (finPart K n (x : AdelicGLn.AdelicGL K n)) ≠ 0 →
      ∃ a ∈ tsupport β, ∃ h ∈ tsupport e, x = archP K n a * MultiplicityOne.finProj K n h := by
    intro x hx
    have hk := left_ne_zero_of_mul hx
    have he := right_ne_zero_of_mul hx
    obtain ⟨s, hs⟩ : ∃ s, β (infPart K n (x : AdelicGLn.AdelicGL K n) * zInf K n s) ≠ 0 := by
      by_contra h0
      simp only [not_exists, ne_eq, not_not] at h0
      exact hk (by simp [kbar, h0])
    refine ⟨_, subset_tsupport _ hs, _, subset_tsupport _ he, ?_⟩
    have hf : ∀ h, MultiplicityOne.finProj K n h = retractOne (finEmb K n h) := fun h => rfl
    rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul,
      infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
  refine ⟨?_, ?_, key⟩
  · exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
      (continuous_infPart.comp continuous_subtype_val)).mul
      (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
  · have hC : IsCompact ((fun p : archGroup K n × AdelicGLn.FiniteAdelicGL K n =>
        archP K n p.1 * MultiplicityOne.finProj K n p.2) '' (tsupport β ×ˢ tsupport e)) :=
      (β.hasCompactSupport.isCompact.prod e.hasCompactSupport.isCompact).image
        ((continuous_archP.comp continuous_fst).mul
          (MultiplicityOne.continuous_finProj.comp continuous_snd))
    set_option synthInstance.maxHeartbeats 200000 in
      refine HasCompactSupport.intro hC fun x hx => ?_
    by_contra hne
    obtain ⟨a, ha, h, hh, rfl⟩ := key x hne
    exact hx ⟨(a, h), ⟨ha, hh⟩, rfl⟩
end
