module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle053
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.ArchFourier

open scoped FourierTransform SchwartzMap

theorem exists_schwartz_fourier_form {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (hn : ∀ x, (∀ y, B x y = 0) → x = 0) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ ei : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ), Function.Bijective ei ∧ ∀ (f : 𝓢(V, ℂ)) (y : V),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) * (B x y : ℂ)) ∂μ := by
  let T := toEuclidean (E := V)
  obtain ⟨R, hR⟩ := GlobalTheory.exists_equiv_inner_eq_form T B hs hn
  obtain ⟨a, ha, haI, -⟩ := GlobalTheory.exists_pos_integral_comp_equiv_haar T μ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let CR := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R
  let CT := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm
  let CRi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) R.symm
  let CTi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  let Fo := SchwartzMap.fourierTransformCLM ℂ (V := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) (E := ℂ)
  have h1 : ∀ g, CRi (CR g) = g := fun g => by ext x; simp [CRi, CR]
  have h2 : ∀ g, CR (CRi g) = g := fun g => by ext x; simp [CRi, CR]
  have h3 : ∀ g, CTi (CT g) = g := fun g => by ext x; simp [CTi, CT]
  have h4 : ∀ g, CT (CTi g) = g := fun g => by ext x; simp [CTi, CT]
  have h5 : ∀ g, 𝓕⁻ (Fo g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourierInv_fourier_eq g
  have h6 : ∀ g, Fo (𝓕⁻ g) = g := fun g => by
    simp only [Fo, SchwartzMap.fourierTransformCLM_apply]; exact FourierTransform.fourier_fourierInv_eq g
  refine ⟨(a : ℂ) • (CR.comp (Fo.comp CT)), ?_, fun f y => ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun g => (a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g)), fun f => ?_, fun g => ?_⟩
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, h1, h5, h3,
        FourierTransform.fourierInv_smul, smul_smul, inv_mul_cancel₀ ha', one_smul]
    · change (a : ℂ) • CR (Fo (CT ((a : ℂ)⁻¹ • CTi (𝓕⁻ (CRi g))))) = g
      rw [map_smul, map_smul, map_smul, h4, h6, h2, smul_smul, mul_inv_cancel₀ ha', one_smul]
  · have e1 : ((a : ℂ) • (CR.comp (Fo.comp CT))) f y = (a : ℂ) * 𝓕 (fun w => f (T.symm w)) (R y) := rfl
    rw [e1, Real.fourier_eq', ← haI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul, hR]
    rw [mul_comm]
    congr 2
    push_cast
    ring

end GlobalTheory.ArchFourier

namespace GlobalTheory.ArchFourier

noncomputable def traceDot (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y))
    (fun x x' y => by simp only [add_dotProduct, map_add (f := _)])
    (fun c x y => by simp only [smul_dotProduct, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [dotProduct_add, map_add (f := _)])
    (fun c x y => by simp only [dotProduct_smul, map_smul, smul_eq_mul])

theorem traceDot_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    traceDot F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) := rfl

theorem traceDot_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) : traceDot F κ x y = traceDot F κ y x := by
  rw [traceDot_apply, traceDot_apply, dotProduct_comm]

theorem traceDot_nondeg {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, traceDot F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [traceDot_apply, dotProduct_single] at this

theorem exists_fourier_sInf : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Bijective ei ∧ ∀ (f : SInf F κ) (y : κ → mixedEmbedding.mixedSpace F),
      ei f y = ∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ := by
  intro F _ _ κ _ _ _ μ _
  classical
  exact exists_schwartz_fourier_form (traceDot F κ) traceDot_comm traceDot_nondeg μ

end GlobalTheory.ArchFourier
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.FourierLocBij

def toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) : AddChar k Circle where
  toFun t := ⟨ψ t, by simp [Submonoid.unitSphere, hn t]⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ a b)

theorem coe_toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) (t : k) :
    ((toCircle ψ hn t : Circle) : ℂ) = ψ t := rfl

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem translate_fourier [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) {κ : Type} [Fintype κ]
    (m : Measure (κ → k)) [m.IsAddRightInvariant] (φ : (κ → k) → ℂ) (a y : κ → k) :
    ∫ x, φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m = (ψ (-(a ⬝ᵥ y)) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
  rw [← integral_add_right_eq_self (μ := m) (fun x => φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) (-a), ← integral_const_mul]
  congr 1
  funext x
  rw [neg_add_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, neg_dotProduct]
  ring

theorem bijOn_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    Set.BijOn (fun (φ : (κ → k) → ℂ) (y : κ → k) => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ)
      (SB (κ → k) : Set _) (SB (κ → k) : Set _) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hT : ∀ φ : (κ → k) → ℂ, (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) =
      fun y => ((r : ℝ) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
    intro φ
    funext y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have key := fun φ hφ => GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν φ hφ
  have hcomp : ∀ (e : (κ → k) ≃ₜ (κ → k)), ∀ f ∈ SB (κ → k), (fun x => f (e x)) ∈ SB (κ → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨fun φ hφ => ?_, fun φ₁ h₁ φ₂ h₂ he => ?_, fun g hg => ?_⟩
  · show (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (κ → k)
    rw [hT]
    exact Submodule.smul_mem _ ((r : ℝ) : ℂ) (key φ hφ).1
  · have he' : ∀ y, ∫ x, φ₁ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m = ∫ x, φ₂ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
      intro y
      have := congrFun he y
      simp only at this
      rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def,
        Complex.real_smul, Complex.real_smul] at this
      exact mul_left_cancel₀ hr' this
    funext a
    have h1a := (key _ (hcomp (Homeomorph.addRight a) _ h₁)).2
    have h2a := (key _ (hcomp (Homeomorph.addRight a) _ h₂)).2
    simp only [Homeomorph.coe_addRight, zero_add] at h1a h2a
    rw [← h1a, ← h2a]
    congr 1
    funext y
    rw [translate_fourier, translate_fourier, he']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.SplitWeil.FourierSurj.hat_surjective k κ ψ hc h1 ν hν).2 ⟨g, hg⟩
    refine ⟨((r : ℝ) : ℂ)⁻¹ • Φ.1, Submodule.smul_mem _ _ Φ.2, ?_⟩
    simp only
    rw [hT]
    funext y
    have hΦ' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ.1 = g := hΦ
    rw [← hΦ']
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hr', one_mul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm y]
    rfl

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourier_bijOn : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    Set.BijOn (fun (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) => ∫ x, φ x * ψ (x ⬝ᵥ y) ∂μ)
      (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := by
  intro F _ _ v ψ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (toCircle ψ hn) := Continuous.subtype_mk hc _
  have hne : toCircle ψ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [coe_toCircle] using congrArg (fun χ : AddChar (Fv F v) Circle => ((χ t : Circle) : ℂ)) h
  exact bijOn_circle (toCircle ψ hn) hcont hne κ μ

end GlobalTheory.FourierLocBij
end
end

section

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.DiffCoprimeP

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem not_le_differentIdeal_of_psiUnr {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl (F := F)) (hu : PsiUnr ψ v) : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  classical
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)

  have key : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      Valued.v x ≤ exp (-FractionalIdeal.count F v (codiff F)) := by
    intro x
    set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
    have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
    have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
    have k1 : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
        ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
      constructor
      · intro H β hβ
        have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact H _ (hβ v)
      · intro H y hy
        have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
          rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
        have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
          by_cases hw : w = v
          · subst hw
            change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_self]
            exact hy
          · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
            exact zero_mem _)
        rw [e] at this
        exact this
    rw [k1, ← h, mem_adelicIdeal_iff codiff_ne_zero]
    constructor
    · intro H
      have := H v
      rwa [hαv] at this
    · intro H w
      by_cases hw : w = v
      · subst hw
        rw [hαv]
        exact H
      · rw [hαw w hw, map_zero]
        exact zero_le
  set c := FractionalIdeal.count F v (codiff F) with hc

  have hc0 : c ≤ 0 := by
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    omega

  have hc1 : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact exp_ne_zero hπ.symm
    set x : Fv F v := ((π⁻¹ : F) : v.adicCompletion F) with hx
    have hvx : Valued.v x = exp 1 := by
      rw [hx, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ, ← exp_neg, neg_neg]
    have h1 : Valued.v x ≤ exp (-c) := by
      rw [hvx, exp_le_exp]
      omega
    have h2 := (hu x).1 ((key x).2 h1)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvx, ← exp_zero, exp_le_exp] at h2
    omega
  have hc2 : c = 0 := le_antisymm hc0 hc1
  intro hle
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv, ← hc, hc2, neg_zero] at h1
  have h2 := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 (Ideal.dvd_iff_le.2 hle)
  exact h2 (by exact_mod_cast h1.symm)

end GlobalTheory.DiffCoprimeP
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.StdCharUnrF

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → PsiUnr ψ v := by
  classical
  intro F _ _ ψ hψ v hv x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.StdCharUnrF
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.ConjLevi.RegularData

theorem isRegular_of_isRegSS : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular D.sp.cm.sig V.gram γ.1 := by
  intro D V γ h
  have hHN := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  refine ⟨⟨?_, D.sp.cm.deg2, ?_, ?_⟩, ?_, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V, γ.2, h⟩
  · haveI : Module.Finite (↥D.host.F) D.host.E :=
      Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
    exact ⟨Algebra.FormallyEtale.of_isSeparable _ _,
      Algebra.FinitePresentation.of_finiteType.1 inferInstance⟩
  · intro e
    simp [Formalism.BasicNotions.CMData.sig]
  · by_contra hne
    push_neg at hne
    have htop : (⊥ : Subalgebra (↥D.host.F) D.host.E) = ⊤ := by
      refine eq_top_iff.2 (fun e _ => ?_)
      rw [Algebra.mem_bot]
      have := (D.sp.cm.fixed e).1 (hne e)
      simpa using this
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
    rw [D.sp.cm.deg2] at h1
    norm_num at h1
  · ext i j
    simpa [Formalism.UG.IsHerm, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] using hHN.1 i j

end GlobalTheory.ConjLevi.RegularData
end
