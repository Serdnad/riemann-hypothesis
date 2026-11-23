module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle596
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelHermitianScaling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle573
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle589
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333

@[expose] public section

section

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
noncomputable section
namespace GlobalTheory.AdelicSchur
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.AdelicSchur
namespace GlobalTheory.AdelicSchur
theorem adelic_schur_lemma : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  intro _ F _ _ κ _ ψ hψ M hpres hcomm hiso
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  let μ : Measure (κ → AF F) := Measure.addHaar
  haveI hμH : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  have hL2 : ∀ φ ∈ schA F κ, MemLp φ 2 μ := fun φ hφ =>
    GlobalTheory.WeilM.schA_memLp_two F κ μ hμH φ hφ
  have hint : ∀ φ ∈ schA F κ, Integrable (fun x => ‖φ x‖ ^ 2) μ := fun φ hφ =>
    (hL2 φ hφ).integrable_norm_pow two_ne_zero
  have hnorm : ∀ φ ∈ schA F κ, ∫ x, ‖M φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
    intro φ hφ
    have h := hiso μ hμH φ hφ
    have e : ∀ g ∈ schA F κ, ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := fun g hg => by
      rw [ofReal_integral_eq_lintegral_ofReal (hint g hg) (Filter.Eventually.of_forall fun x => by positivity)]
      congr 1
      funext x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [e _ (hpres φ hφ), e φ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hψn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.HeisLineTheta.norm_psi hψ
  have hcy : ∀ y : κ → AF F, Continuous fun x : κ → AF F => ψ (x ⬝ᵥ y) := fun y =>
    hψ.1.comp (continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const)
  have hschr0 : ∀ (y : κ → AF F) (f : (κ → AF F) → ℂ) x, schr ψ (0, y) f x = ψ (x ⬝ᵥ y) * f x := by
    intro y f x
    simp [schr]
  have hdiag : ∀ φ ∈ schA F κ, ∀ x, ‖M φ x‖ = ‖φ x‖ := by
    intro φ hφ
    have hMφ := hpres φ hφ
    set D : (κ → AF F) → ℝ := fun x => ‖M φ x‖ ^ 2 - ‖φ x‖ ^ 2 with hD
    have hDi : Integrable D μ := (hint _ hMφ).sub (hint φ hφ)
    have hDc : Continuous D :=
      ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hMφ).norm.pow 2).sub
        ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ).norm.pow 2)
    have hbi : ∀ (y : κ → AF F) (c : ℂ) (f : (κ → AF F) → ℂ), f ∈ schA F κ →
        Integrable (fun x => (c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) μ := fun y c f hf =>
      (hint f hf).bdd_mul (Complex.continuous_re.comp (continuous_const.mul (hcy y))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, hψn, mul_one])
    have hre : ∀ (y : κ → AF F) (c : ℂ), ∫ x, (c * ψ (x ⬝ᵥ y)).re * D x ∂μ = 0 := by
      intro y c
      have hg : φ + c • schr ψ (0, y) φ ∈ schA F κ :=
        (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ))
      have hMg : M (φ + c • schr ψ (0, y) φ) = M φ + c • schr ψ (0, y) (M φ) := by
        rw [map_add (f := _), map_smul, hcomm _ φ hφ]
      have h1 := hnorm _ hg
      rw [hMg] at h1
      have hpt : ∀ f : (κ → AF F) → ℂ, (fun x => ‖(f + c • schr ψ (0, y) f) x‖ ^ 2) =
          fun x => (1 + ‖c‖ ^ 2) * ‖f x‖ ^ 2 + 2 * ((c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) := by
        intro f
        funext x
        rw [Pi.add_apply, Pi.smul_apply, hschr0, smul_eq_mul,
          show f x + c * (ψ (x ⬝ᵥ y) * f x) = (1 + c * ψ (x ⬝ᵥ y)) * f x by ring, norm_mul, mul_pow,
          norm_one_add_sq c _ (hψn _)]
        ring
      rw [hpt, hpt, integral_add ((hint _ hMφ).const_mul _) ((hbi y c _ hMφ).const_mul _),
        integral_add ((hint _ hφ).const_mul _) ((hbi y c _ hφ).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hnorm φ hφ] at h1
      have h2 : ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 ∂μ = ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 ∂μ := by
        linarith
      have e : (fun x => (c * ψ (x ⬝ᵥ y)).re * D x) =
          fun x => (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 - (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 := by
        funext x
        simp only [hD]
        ring
      rw [e, integral_sub (hbi y c _ hMφ) (hbi y c _ hφ), h2, sub_self]
    have hF : ∀ y : κ → AF F, ∫ x, ψ (x ⬝ᵥ y) * (D x : ℂ) ∂μ = 0 := by
      intro y
      have hI : Integrable (fun x => ψ (x ⬝ᵥ y) * (D x : ℂ)) μ :=
        hDi.ofReal.bdd_mul (hcy y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hψn _).le)
      apply Complex.ext
      · rw [Complex.zero_re, ← RCLike.re_to_complex, ← integral_re hI]
        have e : (fun x => RCLike.re (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((1 : ℂ) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re]
        rw [e]
        exact hre y 1
      · rw [Complex.zero_im, ← RCLike.im_to_complex, ← integral_im hI]
        have e : (fun x => RCLike.im (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((-Complex.I) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re, Complex.mul_im]
        rw [e]
        exact hre y (-Complex.I)
    have hD0 := GlobalTheory.CharFourierInj.real_eq_zero (G := κ → AF F) (A := κ → AF F) (fun y x => ψ (x ⬝ᵥ y)) hcy
      (fun y x x' => by simp only [add_dotProduct, AddChar.map_add_eq_mul])
      (fun y y' x => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
      (fun x => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
      (fun y x => hψn _) (fun x hx => GlobalTheory.AdelicSchur.sep ψ hψ x hx) μ D hDc hDi hF
    intro x
    have := congrFun hD0 x
    simp only [hD, Pi.zero_apply, sub_eq_zero] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have htwo : ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, ∀ x a,
      star (M φ x) * M φ' (x + a) = star (φ x) * φ' (x + a) := by
    intro φ hφ φ' hφ' x a
    apply conj_mul_eq
    intro c
    have hg : φ + c • schr ψ (a, 0) φ' ∈ schA F κ :=
      (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ'))
    have h1 := hdiag _ hg x
    rw [map_add (f := _), map_smul, hcomm _ φ' hφ'] at h1
    simpa [schr] using h1
  by_cases h0 : ∃ φ₀ ∈ schA F κ, ∃ x₀, φ₀ x₀ ≠ 0
  · obtain ⟨φ₀, hφ₀, x₀, hx₀⟩ := h0
    have hn1 : ‖M φ₀ x₀‖ = ‖φ₀ x₀‖ := hdiag φ₀ hφ₀ x₀
    have hs : star (M φ₀ x₀) ≠ 0 := by
      rw [star_ne_zero, ← norm_ne_zero_iff, hn1, norm_ne_zero_iff]
      exact hx₀
    refine ⟨star (φ₀ x₀) / star (M φ₀ x₀), fun φ hφ => funext fun x => ?_⟩
    have h2 := htwo φ₀ hφ₀ φ hφ x₀ (x - x₀)
    rw [add_sub_cancel] at h2
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs]
    exact (mul_comm _ _).trans h2
  · push_neg at h0
    refine ⟨0, fun φ hφ => ?_⟩
    have : φ = 0 := funext fun x => h0 φ hφ x
    rw [this, map_zero, smul_zero]
end GlobalTheory.AdelicSchur
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.adelic_intertwiner_eq_scalar : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  first | exact @_root_.GlobalTheory.AdelicSchur.adelic_schur_lemma | exact _root_.GlobalTheory.AdelicSchur.adelic_schur_lemma | (intros; apply _root_.GlobalTheory.AdelicSchur.adelic_schur_lemma <;> assumption)
end
end

section

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
noncomputable section
namespace GlobalTheory.ArchLocality
theorem theta_action_local_at_archimedean_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f f₁ := by
  intro _ F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hψ hW h hh f
  have hS := IsUWeilPair.isUSplitting hW
  set T := om (1, h) with hTdef
  have hpres : ∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d) := fun Φ hΦ => hS.pres (1, h) Φ hΦ
  have hcomm := comm_fin M ψ χX χW om hW h hh
  obtain ⟨r₀, hr₀1, hr₀⟩ := ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : evI F u = 0 := evI_fin
  have htr : ∀ Ψ ∈ schA F (Fin n × Fin d), T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ, schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G =
        fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, At (evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e2, e3, e1]
    ring
  have h0 := fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [tens]
  ring
end GlobalTheory.ArchLocality
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.theta_action_archimedean_locality : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f f₁ := by
  first | exact @_root_.GlobalTheory.ArchLocality.theta_action_local_at_archimedean_place | exact _root_.GlobalTheory.ArchLocality.theta_action_local_at_archimedean_place | (intros; apply _root_.GlobalTheory.ArchLocality.theta_action_local_at_archimedean_place <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.CoinvLine
variable {D : D7}
theorem coinvariants_kill_line_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  intro _ D ψ θ W W₁ X A A₁ B α β ωA ωB Pi rf rl p p' hθ _ _ hM Vs hJ γ hγ Ψ hΨ Ψ₁ _ hder
  have hω : IsWeilDatumO ψ W₁ X α (α / β) ωB := hM.weilB
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.2 one_ne_zero
  obtain ⟨g, h1, h2, h3, h4⟩ := GlobalTheory.OmegaDer.exists_line W₁ hc Vs hJ γ hγ
  have hg : ∀ t : ℝ, GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ (γ (Multiplicative.ofAdd t)) = g t :=
    fun t => by rw [← h1 t]; exact (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hJ).left_inv (g t)
  obtain ⟨Z, hZ⟩ := GlobalTheory.OmegaDer.exists_expInf hθ W₁ g h2 h3 h4
  have hst := fun τ => hM.mapB.stabM.2 τ (Z τ).1 (Z τ).2 Ψ hΨ
  choose Ψ' hΨ' hd using hst
  have hk : ∀ τ, p' (Ψ' τ) = 0 := fun τ => hM.mapB.invl τ (Z τ).1 (Z τ).2 Ψ hΨ (Ψ' τ) (hΨ' τ) (hd τ)
  have hsum : Ψ₁ = ∑ τ, Ψ' τ := by
    funext z
    rw [Finset.sum_apply]
    have e1 : (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
        (γ (Multiplicative.ofAdd t)), 1) Ψ z) = fun t : ℝ => ωB (GlobalTheory.SmoothForms.expInf θ W₁ (t • Z), 1) Ψ z := by
      funext t; rw [hg t, hZ t]
    have hz := hder z
    rw [e1] at hz
    rcases isEmpty_or_nonempty D.what₂.Tau with h0 | h0
    · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
      simp only [e] at hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact hz.unique (hasDerivAt_const _ _)
    · let 𝒮 : Set (GA D W₁ → ℂ) := {φ | ∃ f z, IsThetaFunO ψ W₁ X f ∧ φ = fun g => ωB (g, 1) f z}
      have hΘ := isThetaFunO_of_mem_algF hθ hψ A₁ B hΨ
      refine hz.unique (GlobalTheory.OmegaDer.der_sum hθ 𝒮 ?_ ?_ ⟨Ψ, z, hΘ, rfl⟩ Z (fun τ => Ψ' τ z) fun τ => hd τ z)
      · rintro _ ⟨f, z, hf, rfl⟩
        exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
      · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
        obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
        refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
        have := h (g, 1) z
        simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this

  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun τ _ => hk τ
end GlobalTheory.CoinvLine
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.weil_coinvariants_vanish_on_line_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  first | exact @_root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative | exact _root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative | (intros; apply _root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqTower.StageExists

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.HeckeCharsOfSquare in
theorem exists_quadratic_tower_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W hψ i j p q A A' WW ΛA ΛA' ΛW sA sA' sW hp hq kA kA'
    nA nA' nW hrk => ?_⟩⟩
  obtain ⟨rA, eA, hA⟩ := rig_exists nA _ sA
  obtain ⟨rA', eA', hA'⟩ := rig_exists nA' _ sA'
  obtain ⟨rW, eW, hW⟩ := rig_exists nW _ sW
  have ch := TopExists.chars G hL W i j
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (ch t).2.1
    (ch t).2.2.2.1 (resEta_of_mod (ch t).2.2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.2 (by omega))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (ch t).1
    (ch t).2.2.1 (resEta_of_mod (ch t).2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.1 (by omega))
  obtain ⟨vac, hv⟩ := (vac_exists hψ hθ nA nW hA hW).1
  obtain ⟨vac', hv'⟩ := (vac_exists hψ hθ nA' nW hA' hW).2
  choose e he using TopExists.idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ _ WW rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ _ WW rA' rW _ _ _ _ A.rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨hp, hq, kA, kA', nA, nA', nW,
      ⟨hrk, hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩, eA, eA', eW⟩
end GlobalTheory.SqTower.StageExists
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quadratic_tower_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  first | exact @_root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | exact _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | (intros; apply _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage <;> assumption)
end
end
