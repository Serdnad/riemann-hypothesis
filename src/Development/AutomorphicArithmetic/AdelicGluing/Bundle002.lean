module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite
public import GroundTheory.AutomorphicForms.CuspidalProjection.Global
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle006
public import GroundTheory.AutomorphicForms.CuspidalProjection.OrthogonalProjectionOntoCompSubtypeL
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.CuspDecayHeights.HeightLe
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
import GroundTheory.AutomorphicForms.Bundle002

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem locally_constant_right_invariant_open_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) [CompactSpace K₀] [TotallyDisconnectedSpace K₀]
    (e : G → ℂ) (he : IsLocallyConstant e) (hc : HasCompactSupport e) :
    ∃ W : Subgroup G, IsOpen (W : Set G) ∧ ∀ k ∈ W, ∀ x, e (x * k) = e x := by
  letI : Inv (Set G) := Set.inv
  have hF : IsLocallyConstant fun p : G × G => e (p.1 * p.2) - e p.1 :=
    (he.comp_continuous (continuous_fst.mul continuous_snd)).sub (he.comp_continuous continuous_fst)
  have hN : IsOpen {p : G × G | e (p.1 * p.2) - e p.1 = 0} := hF.isOpen_fiber 0
  obtain ⟨A, V, -, hVo, hCA, h1V, hAV⟩ := generalized_tube_lemma (s := tsupport e) hc
    (isCompact_singleton (x := (1 : G))) hN (by
      rintro ⟨x, k⟩ ⟨-, hk⟩
      have hk' : k = 1 := hk
      simp [hk'])
  have h1 : (1 : G) ∈ V := h1V rfl
  have hinv : ∀ x ∈ tsupport e, ∀ k ∈ V, e (x * k) = e x :=
    fun x hx k hk => sub_eq_zero.1 (hAV (Set.mk_mem_prod (hCA hx) hk))
  have hVi : IsOpen (V ∩ V⁻¹) := hVo.inter hVo.inv
  have hUo : IsOpen ((↑) ⁻¹' (V ∩ V⁻¹) : Set K₀) := hVi.preimage continuous_subtype_val
  have hU1 : (1 : K₀) ∈ ((↑) ⁻¹' (V ∩ V⁻¹) : Set K₀) := by
    simp [h1]
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  refine ⟨(H.toOpenSubgroup.toSubgroup).map K₀.subtype, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hK.isOpenEmbedding_subtypeVal.isOpenMap _ H.toOpenSubgroup.isOpen
  · rintro _ ⟨u, hu, rfl⟩ x
    have hV : (u : G) ∈ V ∩ V⁻¹ := hH hu
    by_cases hx : x ∈ tsupport e
    · exact hinv x hx _ hV.1
    by_cases hxk : x * u ∈ tsupport e
    · have := hinv _ hxk _ hV.2
      simpa using this.symm
    · change e (x * u) = e x
      rw [image_eq_zero_of_notMem_tsupport hxk, image_eq_zero_of_notMem_tsupport hx]

theorem UpperTheory.exists_open_subgroup_rightInvariant_finiteAdelicGL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (e : TF K n), IsLocallyConstant e →
      ∃ W : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (W : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ k ∈ W, ∀ x, e (x * k) = e x := by
  intro K _ _ n e he
  exact locally_constant_right_invariant_open_subgroup (AdelicGLn.integralFiniteGL K n) (AdelicGLn.isOpen_integralFiniteGL K n) e he e.hasCompactSupport
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem conj_smooth {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) :
    (isExpLieAlgebra K n).IsSmoothFun fun g => conj (f g) := by
  letI := (isExpLieAlgebra K n).chartedSpace
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  exact hc.comp_contMDiff hf

theorem UpperTheory.cuspidalProjection_ccStar_tens_isLeftSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n), SmoothT β →
          (∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ u ∈ U, ∀ h, e (h * u) = e h) →
          IsLeftSmooth (CuspidalProjection.ccStar (tens β e)) := by
  intro K _ _ n hn β e hβ ⟨U, hUo, hU⟩
  let β' : TI K n := ⟨⟨fun a => conj (β a⁻¹), Complex.continuous_conj.comp (β.continuous.comp continuous_inv)⟩,
    (β.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩
  let e' : TF K n := ⟨⟨fun a => conj (e a⁻¹), Complex.continuous_conj.comp (e.continuous.comp continuous_inv)⟩,
    (e.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩
  have hL := UpperTheory.ConvolutionTheory.Tf.leftSm K n hn β e
  rw [hL.2 β' e' (fun _ => rfl) (fun _ => rfl)]
  refine (UpperTheory.ConvolutionTheory.Tf.leftSm K n hn β' e').1 ?_ ⟨U, hUo, fun u hu h => ?_⟩
  · have h1 := (UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ)).1
    exact conj_smooth ((isExpLieAlgebra K n).mem_smoothFuns.1 h1)
  · show conj (e (u * h)⁻¹) = conj (e h⁻¹)
    rw [mul_inv_rev, hU _ (U.inv_mem hu)]
end

section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem comp_integrated_of_left_inv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (u : G) (f : CompactlySupportedContinuousMap G ℂ) (hf : ∀ x, f (u * x) = f x) :
    π u ∘L π.integrated μ (UnitaryRep.ccToL1 μ f) = π.integrated μ (UnitaryRep.ccToL1 μ f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, UnitaryRep.inner_map_right, CuspidalProjection.inner_integrated_ccToL1,
    CuspidalProjection.inner_integrated_ccToL1, ← integral_mul_left_eq_self (μ := μ) _ u⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have h : f (u⁻¹ * x) = f x := by rw [← hf (u⁻¹ * x), mul_inv_cancel_left]
  rw [h, UnitaryRep.inner_map_left, inv_inv, UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply π u,
    mul_inv_cancel, UnitaryRep.map_one_apply]

theorem UpperTheory.rhoF_comp_Ofin_of_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
      (e : TF K n) (u : AdelicGLn.FiniteAdelicGL K n), (∀ x, e (u * x) = e x) → rhoF μ u ∘L Ofin μ m e = Ofin μ m e := by
  intro K _ _ n μ _ m _ e u hu
  exact comp_integrated_of_left_inv m ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n)
    MultiplicityOne.continuous_finProj) u e hu
end
