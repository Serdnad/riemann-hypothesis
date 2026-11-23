module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.Bundle001
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfPartialSumsNonneg
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open scoped Matrix
open MeasureTheory GlobalTheory.RealWeil

noncomputable section
open Complex
open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace Real FourierTransform ContDiff SchwartzMap

namespace GlobalTheory.RealWeil.FourierConjProductVanishing

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem ae_eq_zero_of_fourier_eq_zero {D : V → ℂ} (hD : Integrable D) (hF : ∀ ξ, 𝓕 D ξ = 0) :
    D =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hD.locallyIntegrable fun g hg hgc => ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  set ψ : 𝓢(V, ℂ) := hg₁.toSchwartzMap hg₂ with hψ
  set φ : 𝓢(V, ℂ) := 𝓕⁻ ψ with hφ
  have h0 : ∀ x, (𝓕 φ) x = (g x : ℂ) := fun x => by
    rw [hφ, FourierTransform.fourier_fourierInv_eq, hψ]
    simp
  have h1 : ∫ x, g x • D x = ∫ x, (𝓕 φ) x * D x := by
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [h0, Complex.real_smul]
  have h2 : ∫ x, (𝓕 φ) x * D x = ∫ x, φ x * 𝓕 D x := by
    have := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner (φ.integrable (μ := volume)) hD
    simpa using! this
  rw [h1, h2]
  simp [hF]

variable {l : Type} [Fintype l]

def pt (p q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) (fun i => q i)

theorem pPart_pt (p q : EuclideanSpace ℝ l) : pPart (pt p q) = p := by
  ext i; simp [pPart, pt]

theorem qPart_pt (p q : EuclideanSpace ℝ l) : qPart (pt p q) = q := by
  ext i; simp [qPart, pt]

theorem fourier_conj_mul_eq_zero (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) (p ξ : EuclideanSpace ℝ l) :
    𝓕 (fun x => conj (f x) * g (x + p)) ξ = 0 := by
  have h1 := h (pt p (-ξ))
  rw [L2.inner_def] at h1
  have h2 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x = 0 := by
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rho (pt p (-ξ)) g] with x hx
    rw [hx, RCLike.inner_apply, mul_comm]
  have h3 : ∫ x, conj (f x) * rhoFun (pt p (-ξ)) g x =
      cexp (((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) * 𝓕 (fun x => conj (f x) * g (x + p)) ξ := by
    rw [Real.fourier_eq', ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [rhoFun, phase, pPart_pt, qPart_pt, smul_eq_mul]
    have e : (((2 * π * ⟪-ξ, x⟫ + π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I) =
        ((π * ⟪p, -ξ⟫ : ℝ) : ℂ) * I + ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * I := by
      rw [inner_neg_left, real_inner_comm]
      push_cast
      ring
    rw [e, Complex.exp_add]
    ring
  rw [h2] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left (Complex.exp_ne_zero _)

theorem integrable_conj_mul_shift (f g : L2 l) (p : EuclideanSpace ℝ l) :
    Integrable (fun x => conj (f x) * g (x + p)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) f (rho (pt p 0) g)).congr ?_
  filter_upwards [coeFn_rho (pt p 0) g] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]
  simp [rhoFun, phase, pPart_pt, qPart_pt]

theorem eq_zero_or_eq_zero_of_inner_rho (f g : L2 l) (h : ∀ w, ⟪f, rho w g⟫_ℂ = 0) : f = 0 ∨ g = 0 := by
  have hz : ∀ p : EuclideanSpace ℝ l, ∀ᵐ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 = 0 := by
    intro p
    filter_upwards [ae_eq_zero_of_fourier_eq_zero (integrable_conj_mul_shift f g p)
      (fourier_conj_mul_eq_zero f g h p)] with x hx
    have hx' : conj ((f : _ → ℂ) x) * (g : _ → ℂ) (x + p) = 0 := hx
    rcases mul_eq_zero.1 hx' with h0 | h0
    · rw [map_eq_zero] at h0
      simp [h0]
    · simp [h0]
  have hfm : Measurable fun x => ‖(f : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable f).measurable.enorm.pow_const 2
  have hgm : Measurable fun x => ‖(g : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable g).measurable.enorm.pow_const 2
  have hprod : (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2) = 0 := by
    calc (∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2) * (∫⁻ x, ‖(g : _ → ℂ) x‖ₑ ^ 2)
        = ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ∫⁻ p, ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          rw [← lintegral_mul_const _ hfm]
          refine lintegral_congr fun x => ?_
          rw [lintegral_add_left_eq_self (fun y => ‖(g : _ → ℂ) y‖ₑ ^ 2) x]
      _ = ∫⁻ x, ∫⁻ p, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_congr fun x => ?_
          exact (lintegral_const_mul _ (hgm.comp (measurable_const_add x))).symm
      _ = ∫⁻ p, ∫⁻ x, ‖(f : _ → ℂ) x‖ₑ ^ 2 * ‖(g : _ → ℂ) (x + p)‖ₑ ^ 2 := by
          refine lintegral_lintegral_swap ?_
          exact ((hfm.comp measurable_fst).mul (hgm.comp measurable_add)).aemeasurable
      _ = 0 := by
          rw [← lintegral_zero]
          exact lintegral_congr fun p => lintegral_eq_zero_of_ae_eq_zero (hz p) |>.trans rfl
  have key : ∀ u : L2 l, (∫⁻ x, ‖(u : _ → ℂ) x‖ₑ ^ 2) = 0 → u = 0 := by
    intro u hu
    have hum : Measurable fun x => ‖(u : _ → ℂ) x‖ₑ ^ 2 := (Lp.stronglyMeasurable u).measurable.enorm.pow_const 2
    rw [lintegral_eq_zero_iff hum] at hu
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hu] with x hx
    simpa using hx
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact Or.inl (key f h0)
  · exact Or.inr (key g h0)

theorem rho_symm_apply (w : l ⊕ l → ℝ) (v : L2 l) :
    (rho w).symm v = (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹ • rho (-w) v := by
  rw [LinearIsometryEquiv.symm_apply_eq, map_smul, rho_rho, add_neg_cancel, rho_zero,
    inv_smul_smul₀ (Complex.exp_ne_zero _)]

def opSet (l : Type) [Fintype l] : Set (L2 l →L[ℂ] L2 l) :=
  Set.range fun cw : ℂ × (l ⊕ l → ℝ) => cw.1 • ((rho cw.2).toContinuousLinearEquiv : L2 l →L[ℂ] L2 l)

theorem star_mem_opSet : ∀ A ∈ opSet l, star A ∈ opSet l := by
  rintro _ ⟨⟨c, w⟩, rfl⟩
  refine ⟨⟨conj c * (cexp (((π * sympl w (-w) : ℝ) : ℂ) * I))⁻¹, -w⟩, ?_⟩
  rw [star_smul, ContinuousLinearMap.star_eq_adjoint]
  ext v
  have e := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) (LinearIsometryEquiv.adjoint_eq_symm (rho w))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at e ⊢
  rw [e, rho_symm_apply, smul_smul]
  rfl

theorem irreducible_opSet (S : Submodule ℂ (L2 l)) (hS : IsClosed (S : Set (L2 l)))
    (hst : ∀ A ∈ opSet l, ∀ v ∈ S, A v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  right
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  haveI : CompleteSpace S := hS.completeSpace_coe
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro f hf
  have hw : ∀ w, ⟪f, rho w g⟫_ℂ = 0 := by
    intro w
    have hm : rho w g ∈ S := by
      have := hst _ ⟨⟨1, w⟩, rfl⟩ g hg
      simpa using this
    exact Submodule.inner_left_of_mem_orthogonal hm hf
  exact (eq_zero_or_eq_zero_of_inner_rho f g hw).resolve_right hg0

end GlobalTheory.RealWeil.FourierConjProductVanishing

namespace GlobalTheory.RealWeil


open GlobalTheory.RealWeil.FourierConjProductVanishing in
theorem schur_rho_l2 : ∀ (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l), (∀ w v, U (rho w v) = rho w (U v)) →
    ∃ a : ℂ, ∀ v, U v = a • v := by
  intro l _ U hU
  obtain ⟨c, hc⟩ := Formalism.MainNotions.BridgeCSchur.schur_bounded (opSet l) star_mem_opSet
    (fun S hS hst => irreducible_opSet S hS hst) (U.toContinuousLinearEquiv : L2 l →L[ℂ] L2 l) (by
      rintro _ ⟨⟨c, w⟩, rfl⟩
      ext v
      simp [hU])
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun T : L2 l →L[ℂ] L2 l => T v) hc
  simpa using this

end GlobalTheory.RealWeil
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.FrobRestrict

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]

def toOm (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) : 𝓞 L →+* Ω :=
  (e.symm.toRingHom.comp L.val.toRingHom).comp (algebraMap (𝓞 L) L)

theorem toOm_apply (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (y : 𝓞 L) :
    toOm e L y = e.symm ((y : L) : AlgebraicClosure K) := rfl

theorem toOm_mem (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) (y : 𝓞 L) : toOm e L y ∈ A :=
  ReciprocityTheory.Gal.mem_of_isIntegral_int A ((Algebra.IsIntegral.isIntegral (R := ℤ) y).map (toOm e L).toIntAlgHom)

def toA (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) : 𝓞 L →+* A :=
  (toOm e L).codRestrict A (toOm_mem e L A)

def primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) : Ideal (𝓞 L) :=
  Ideal.comap (toA e L A) (IsLocalRing.maximalIdeal A)

theorem mem_primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) (y : 𝓞 L) : y ∈ primeBelow e L A ↔ A.valuation (toOm e L y) < 1 := by
  unfold primeBelow
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

instance (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) : (primeBelow e L A).IsPrime := by
  unfold primeBelow; infer_instance

theorem toOm_algebraMap (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (x : 𝓞 K) :
    toOm e L (algebraMap (𝓞 K) (𝓞 L) x) = algebraMap K Ω (x : K) := by
  rw [toOm_apply]
  have h1 : (((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) : AlgebraicClosure K) = algebraMap K (AlgebraicClosure K) (x : K) := rfl
  rw [h1, AlgEquiv.commutes]

theorem liesOver_primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) :
    (primeBelow e L A).LiesOver v.asIdeal := by
  constructor
  ext x
  rw [Ideal.mem_comap, mem_primeBelow, toOm_algebraMap]
  exact (hA x).symm

theorem isFrobAt_primeBelow (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v)
    (σ : Formalism.ConjugateSelfDual.G K Ω) (hσ : Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ) :
    IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) (primeBelow e L A) := by
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI := liesOver_primeBelow e L A v hA
  rw [ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_iff_forall]
  have hu : (primeBelow e L A).under (𝓞 K) = v.asIdeal := (Ideal.LiesOver.over).symm
  rw [hu]
  intro y
  rw [mem_primeBelow, map_sub, map_pow]
  have hy : toOm e L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y) = σ (toOm e L y) := by
    rw [toOm_apply, toOm_apply]
    have h2 : (((AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e) • y : 𝓞 L) : L) : AlgebraicClosure K)
        = ((e.symm.trans σ).trans e) ((y : L) : AlgebraicClosure K) := by
      rw [← AlgEquiv.restrictNormalHom_apply]; rfl
    rw [h2]
    simp
  rw [hy]
  exact hσ.2 _ ((A.valuation_le_one_iff _).mpr (toOm_mem e L A y))

theorem isFrobAt_restrict : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
    (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω,
    Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
    haveI := h.finiteDimensional; haveI := h.isGalois;
    IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) Q := by
  intro K _ _ Ω _ _ _ e L h v A hA σ hσ Q hQ hQv
  haveI := h.finiteDimensional
  haveI := h.isGalois
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI := liesOver_primeBelow e L A v hA
  exact ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_of_comm v (primeBelow e L A) Q h.comm _ (isFrobAt_primeBelow e L A v hA σ hσ)

end GlobalTheory.FrobRestrict
end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.CasimirHighest

theorem casimir_comm_gen {R I : Type*} [Ring R] [Fintype I] [DecidableEq I] (e : I → I → R)
    (he : ∀ i j k l, e i j * e k l - e k l * e i j =
      (if j = k then e i l else 0) - (if l = i then e k j else 0)) (k l : I) :
    (∑ a, ∑ b, e a b * e b a) * e k l = e k l * ∑ a, ∑ b, e a b * e b a := by
  rw [← sub_eq_zero]
  have h : ∀ a b, e a b * e b a * e k l - e k l * (e a b * e b a) =
      ((if a = k then e a b * e b l else 0) - (if l = b then e a b * e k a else 0)) +
      ((if b = k then e a l * e b a else 0) - (if l = a then e k b * e b a else 0)) := by
    intro a b
    have : e a b * e b a * e k l - e k l * (e a b * e b a) =
        e a b * (e b a * e k l - e k l * e b a) + (e a b * e k l - e k l * e a b) * e b a := by
      noncomm_ring
    rw [this, he, he]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a = k then e a b * e b l else 0),
    Finset.sum_comm (f := fun a b => if l = a then e k b * e b a else 0)]
  simp

theorem casimir_on_highest_rat {V : Type*} [AddCommGroup V] [Module ℂ V] {m : ℕ}
    (e : Fin m → Fin m → Module.End ℂ V)
    (he : ∀ i j, e i j * e j i - e j i * e i j = e i i - e j j)
    (v : V) (κ : Fin m → ℚ) (hv : ∀ i j, i < j → e i j v = 0)
    (hκ : ∀ i, e i i v = (κ i : ℂ) • v) :
    ∑ i, ∑ j, e i j (e j i v) =
      ((∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) : ℚ) : ℂ) • v := by
  have key : ∀ i j, e i j (e j i v) =
      (((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ) : ℂ) • v := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 := congrArg (fun f : Module.End ℂ V => f v) (he i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, hv i j h, map_zero, sub_zero,
        hκ] at h1
      rw [h1]
      simp [h, h.ne, sub_smul]
    · subst h
      simp [hκ, mul_smul]
    · simp [hv j i h, h.ne', not_lt.mpr h.le]
  have hz : ∑ i : Fin m, ∑ j : Fin m,
      ((if i = j then κ i * κ i else 0) + (if i < j then κ i else 0) -
        (if i < j then κ j else 0) : ℚ)
      = ∑ i, κ i ^ 2 + ∑ i : Fin m, κ i * ((m : ℚ) - 1 - 2 * (i : ℕ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if i < j then κ j else 0), ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have a1 : ∑ j : Fin m, (if i < j then κ i else 0) = ((m : ℚ) - 1 - (i : ℕ)) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi,
        nsmul_eq_mul]
      have := i.2
      congr 1
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    have a2 : ∑ j : Fin m, (if j < i then κ i else 0) = ((i : ℕ) : ℚ) * κ i := by
      rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio,
        nsmul_eq_mul]
    rw [a1, a2]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [key]
  rw [← hz]
  simp only [Rat.cast_sum, Finset.sum_smul]

theorem act_Eab_comm {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (i j k l : Ix p q) :
    act (Eab i j) * act (Eab k l) - act (Eab k l) * act (Eab i j) =
      (if j = k then act (Eab i l) else 0) - (if l = i then act (Eab k j) else 0) := by
  have m : ∀ i j k l : Ix p q, Eab i j * Eab k l = if j = k then Eab i l else 0 := by
    intro i j k l
    split_ifs with hh
    · subst hh; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne, hh]
  rw [← h, m, m, map_sub]
  split_ifs <;> simp

theorem casimir_central_and_highest : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → (∀ Z, casimir act * act Z = act Z * casimir act) ∧ ∀ (μ : Ix p q → ℚ) (v : V), v ∈ hwSub act μ → (∑ a, ∑ b, if sameBlock a b then act (Eab a b) (act (Eab b a) v) else 0) = ((∑ a, μ a ^ 2 + (∑ i : Fin p, μ (.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ))) + (∑ j : Fin q, μ (.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • v := by
  intro p q V _ _ act h
  refine ⟨fun Z => ?_, fun μ v hv => ?_⟩
  · have hZ : Z = ∑ k, ∑ l, Z k l • Eab k l := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    have hc : ∀ k l, casimir act * act (Eab k l) = act (Eab k l) * casimir act := fun k l =>
      casimir_comm_gen (fun a b => act (Eab a b)) (act_Eab_comm h) k l
    rw [hZ]

    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, hc]
  · simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
    obtain ⟨hw, hr⟩ := hv
    have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
      (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) v
      (fun i => μ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
      (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) v
      (fun i => μ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
    have s1 : ∀ i j, sameBlock (p := p) (q := q) (.inl i) (.inl j) := fun _ _ => trivial
    have s2 : ∀ i j, sameBlock (p := p) (q := q) (.inr i) (.inr j) := fun _ _ => trivial
    have s3 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inl i) (.inr j) := fun _ _ => id
    have s4 : ∀ i j, ¬ sameBlock (p := p) (q := q) (.inr i) (.inl j) := fun _ _ => id
    simp only [Fintype.sum_sum_type, if_pos (s1 _ _), if_pos (s2 _ _), if_neg (s3 _ _),
      if_neg (s4 _ _), Finset.sum_const_zero, add_zero, zero_add]
    rw [h1, h2, ← add_smul, ← Rat.cast_add]
    congr 2
    ring

end GlobalTheory.CasimirHighest
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm

namespace GlobalTheory.CompactHarm

variable {m k l : ℕ}

theorem omE_pp {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = true) (hv : linePos v = true)
    (P : Pol p q r s) :
    omE u v P = X u * pderiv v P + (if u = v then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, hu, hv, if_true]
  split_ifs <;> simp

theorem omE_nn {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (P : Pol p q r s) :
    omE u v P = -(X v * pderiv u P) - (if u = v then (1 / 2 : ℂ) else 0) • P := by
  have : omE u v P = -(pderiv u (X v * P)) + (if u = v then (1 / 2 : ℂ) else 0) • P := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, pderiv_X_mul']
  split_ifs
  · module
  · simp

end GlobalTheory.CompactHarm
end

section

open scoped Matrix
open Formalism.BasicNotions.TH

theorem _root_.GlobalTheory.T.exists_polar_decomposition_indefiniteUnitary : ∀ (R S : ℕ) (u : Mat R S), uᴴ * Jm R S * u = Jm R S → ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
    Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q := by
  first | exact @GlobalTheory.UnitaryPolar.polar | exact GlobalTheory.UnitaryPolar.polar | (intros; apply GlobalTheory.UnitaryPolar.polar <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_derived_actions_tensor_members : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), Continuous F.emb ∧ (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0) ∧ (∀ Y ∈ upq r s, ∀ P, HasDerivAt (fun t : ℝ => F.π (1, T2.expt (t • Y)) (F.ι P)) (F.ι (fockAct2 p q r s Y P)) 0) := by
  first | exact @GlobalTheory.FockEmbExp.fock_derived | exact GlobalTheory.FockEmbExp.fock_derived | (intros; apply GlobalTheory.FockEmbExp.fock_derived <;> assumption)
end
