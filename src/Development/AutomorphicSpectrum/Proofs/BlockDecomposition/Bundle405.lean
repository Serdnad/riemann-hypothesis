module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle392
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import GroundTheory.PAdicHodge.UnramifiedClosure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle395
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle274
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle365
import GroundTheory.PAdicHodge.BdRTGalois
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle394
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.TransDeriv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}

theorem descend_eq_sec {X : Type} {f : G → X} (h : LeftInv Γ f) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) :
    descend Γ f q = f (sec Γ q) := by
  conv_lhs => rw [← mk_sec q]
  exact h.descend_mk _

theorem sec_mul_eq {X : Type} {f : G → X} (h : LeftInv Γ f) (g : G) :
    (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => f (sec Γ q * g)) = descend Γ f ∘ rmul Γ g := by
  funext q
  have e : rmul Γ g q = mk Γ (sec Γ q * g) := by
    conv_lhs => rw [← mk_sec q]
    rfl
  rw [Function.comp_apply, e, h.descend_mk]

variable [μ.IsMulLeftInvariant]

theorem inner_toL2_eq_integral {f : G → ℂ} (hf : MemL2Quotient Γ μ f) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) :
    ⟪u, hf.toL2⟫_ℂ = ∫ q : GlobalTheory.AutomorphicL2Unitary.Quot Γ, conj (u q) * f (sec Γ q) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toL2] with q e
  rw [e, descend_eq_sec hf.1]
  simp [mul_comm]

theorem sub_eq_integral {φ ψ : G → ℂ} {c : ℝ → G} (hψ : Continuous ψ) (hc : Continuous c) (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (x : G) (t : ℝ) :
    φ (x * c t) - φ x = ∫ s in (0 : ℝ)..t, ψ (x * c s) := by
  have hs : ∀ s, HasDerivAt (fun r => φ (x * c r)) (ψ (x * c s)) s := fun s => by
    have h2 : HasDerivAt (fun t => φ (x * c s * c t)) (ψ (x * c s)) (s - s) := by simpa using hd (x * c s)
    have h3 := h2.comp_sub_const s s
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
    have : c r = c s * c (r - s) := by rw [← hadd]; congr 1; ring
    simp only [this, mul_assoc]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hs s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp [h0]

theorem integrable_pair [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] {ψ : G → ℂ}
    (hψ : MemL2Quotient Γ μ ψ) (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (u : GlobalTheory.AutomorphicL2Unitary.L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) := by
  have hsec := (measurableEmbedding_sec (Γ := Γ)).measurable
  have hm : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => ψ (sec Γ p.2 * c p.1)) :=
    hψc.measurable.comp ((hsec.comp measurable_snd).mul (hc.measurable.comp measurable_fst))
  have hu : Measurable (fun p : ℝ × GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u p.2)) :=
    Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hF : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) :=
    hu.mul hm
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hF.enorm.aemeasurable]
  set C : ENNReal := eLpNorm u 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) * eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) with hC
  have hb : ∀ s, ∫⁻ q, ‖Function.uncurry (fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => conj (u q) * ψ (sec Γ q * c s)) (s, q)‖ₑ
      ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ ≤ C := fun s => by
    have h1 := eLpNorm_le_eLpNorm_mul_eLpNorm (μ := GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (q := 2) (r := 1)
      (fun a b : ℂ => conj a * b) 1 (by fun_prop)
      (Lp.aestronglyMeasurable u) ((hψ.mul_right (c s)).2.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => by simp)
    have h2 : eLpNorm (descend Γ fun x => ψ (x * c s)) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) = eLpNorm (descend Γ ψ) 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
      have e : descend Γ (fun x => ψ (x * c s)) = descend Γ ψ ∘ rmul Γ (c s) := by
        funext q
        rw [descend_eq_sec (hψ.1.mul_right (c s)), ← sec_mul_eq hψ.1]
      rw [e]
      exact eLpNorm_comp_measurePreserving hψ.2.aestronglyMeasurable (measurePreserving_rmul (c s))
    have hm₁ : AEStronglyMeasurable (fun q => conj (u q) * descend Γ (fun x => ψ (x * c s)) q)
        (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).mul
        (hψ.mul_right (c s)).2.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hm₁, h2] at h1
    simp only [ENNReal.coe_one, one_mul] at h1
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun q => ?_
    simp only [Function.uncurry, descend_eq_sec (hψ.1.mul_right (c s))]
  refine lt_of_le_of_lt (lintegral_mono hb) ?_
  rw [lintegral_const, Measure.restrict_apply_univ]
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (Lp.memLp u) hψ.2) ?_
  simp [Set.uIoc, Real.volume_Ioc]

variable [μ.IsMulRightInvariant] [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ]

theorem R_sub_eq_integral {φ ψ : G → ℂ} (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) {c : ℝ → G} (hc : Continuous c) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hd : ∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) (t : ℝ) :
    R Γ μ (c t) hφ.toL2 - hφ.toL2 = ∫ s in (0 : ℝ)..t, R Γ μ (c s) hψ.toL2 := by
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  refine ext_inner_left ℂ fun u => ?_
  have e1 := (innerSL ℂ u).intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 t)
  simp only [innerSL_apply_apply] at e1
  rw [← e1, inner_sub_right]
  simp only [right_translate_toL2, inner_toL2_eq_integral]
  have hi : ∀ {f : G → ℂ} (hf : MemL2Quotient Γ μ f),
      Integrable (fun q : GlobalTheory.AutomorphicL2Unitary.Quot Γ => conj (u q) * f (sec Γ q)) (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := fun {f} hf => by
    have h := (Lp.memLp u).star.integrable_mul hf.2
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [descend_eq_sec hf.1]
  rw [← integral_sub (hi (hφ.mul_right (c t))) (hi hφ), intervalIntegral.intervalIntegral_eq_integral_uIoc,
    integral_integral_swap (integrable_pair hψ hψc hc u t), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [integral_const_mul]
  rw [← mul_sub, sub_eq_integral hψc hc h0 hadd hd, intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [mul_smul_comm]

theorem hasDerivAt_R : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (φ ψ : G → ℂ) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ) (c : ℝ → G), Continuous φ → Continuous ψ → Continuous c → c 0 = 1 → (∀ s t, c (s + t) = c s * c t) → (∀ g, HasDerivAt (fun t => φ (g * c t)) (ψ g) 0) → ∀ t, HasDerivAt (fun s => R Γ μ (c s) hφ.toL2) (R Γ μ (c t) hψ.toL2) t := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c _ hψc hc h0 hadd hd t
  have hcont : Continuous fun s => R Γ μ (c s) hψ.toL2 := (continuous_R _).comp hc
  have e : (fun s => R Γ μ (c s) hφ.toL2) = fun s => hφ.toL2 + ∫ r in (0 : ℝ)..s, R Γ μ (c r) hψ.toL2 := by
    funext s
    rw [← R_sub_eq_integral hφ hψ hψc hc h0 hadd hd s]
    abel
  rw [e]
  exact (hcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _

end GlobalTheory.CompanionTheory.TransDeriv
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ModCompactParab

theorem deltaHalf_leviProj_eq_one_of_isCompact :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ)
      (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) →
      ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K →
        deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  intro k _ _ _ _ a b n e K hK p hp
  let χ : parab k (two e) →* ℂˣ := (deltaHalf k (Two (Fin a) (Fin b))).comp (leviProj k (two e))
  have hχ : Continuous (leviProj k (two e)) := GlobalTheory.ParabLevel.continuous_leviProj (R := k) (two e)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : parab k (two e) → GL (Fin n) k) :=
    (GlobalTheory.ParabLevel.isClosed_parab_two (R := k) e).isClosedEmbedding_subtypeVal
  let H : Subgroup (parab k (two e)) := K.subgroupOf (parab k (two e))
  have hH : IsCompact (H : Set (parab k (two e))) := hemb.isCompact_preimage hK
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hopen : IsOpen ((χ.ker.subgroupOf H : Subgroup H) : Set H) :=
    (isSmoothChar_deltaHalf k (m := Two (Fin a) (Fin b))).preimage (hχ.comp continuous_subtype_val)
  haveI : Finite (H ⧸ χ.ker.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hidx : (χ.ker.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx (⟨p, hp⟩ : H)
  have hpow : deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) ^ m = 1 := by
    have h := Subgroup.mem_subgroupOf.1 hmem
    simpa [χ, MonoidHom.mem_ker, map_pow] using h
  have hreal : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) ^ m = 1 := by
    have h := congrArg (fun u : ℂˣ => (u : ℂ)) hpow
    simp only [Units.val_pow_eq_pow_val, val_deltaHalf, Units.val_one] at h
    exact_mod_cast h
  have hone : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) = 1 :=
    (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) hm.ne').1 hreal
  ext
  rw [val_deltaHalf, hone]
  simp

end GlobalTheory.CompanionTheory.ModCompactParab
end
end

section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GodementCoeff

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure]
  [ν.IsMulRightInvariant] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

private theorem integrableOn_and_setIntegral_sq_le_of_isU (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) {s : Set Γ} (hs : MeasurableSet s)
    (hs' : ν s ≠ ⊤) :
    IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν ∧
      ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hcont : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hbd : ∀ g, ‖⟪b, ρ g v⟫_ℂ‖ ≤ ‖b‖ * ‖v‖ := fun g =>
    (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  have hc2 : IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν := by
    refine Measure.integrableOn_of_bounded (M := (‖b‖ * ‖v‖) ^ 2) hs'
      (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd g) 2
  set f : Γ → ℂ := s.indicator (fun g => starRingEnd ℂ ⟪b, ρ g v⟫_ℂ) with hfdef
  have hfm : Measurable f := ((Complex.continuous_conj.comp hcont).measurable).indicator hs
  have hfi : Integrable f ν := by
    refine (integrable_indicator_iff hs).mpr (Measure.integrableOn_of_bounded (M := ‖b‖ * ‖v‖) hs'
      (Complex.continuous_conj.comp hcont).aestronglyMeasurable (ae_of_all _ fun g => ?_))
    rw [Complex.norm_conj]
    exact hbd g
  have hfeq : (fun g => ‖f g‖ ^ 2) = s.indicator (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) := by
    funext g
    by_cases hg : g ∈ s <;> simp [hfdef, hg, norm_inner_symm]
  have hf2 : Integrable (fun g => ‖f g‖ ^ 2) ν := by
    rw [hfeq]
    exact (integrable_indicator_iff hs).mpr hc2
  have hG := GlobalTheory.CompanionTheory.Godement.norm_sq_integral_smul_le ν ρ hρ v hm f hfm hfi hf2
  rw [hfeq, integral_indicator hs] at hG
  have hint : Integrable (fun g => f g • ρ g v) ν :=
    hfi.smul_of_top_left (memLp_top_of_bound (hρ.cont v).aestronglyMeasurable ‖v‖
      (ae_of_all _ fun g => (hρ.norm g v).le))
  set I := ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν with hIdef
  set w := ∫ g, f g • ρ g v ∂ν with hwdef
  have hinner : ⟪b, w⟫_ℂ = (I : ℂ) := by
    have h := (innerSL ℂ b).integral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    rw [hwdef, ← h, hIdef, ← integral_indicator hs, ← integral_complex_ofReal]
    congr 1
    funext g
    by_cases hg : g ∈ s
    · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right,
        Complex.conj_mul']
      push_cast
      rfl
    · simp [hfdef, hg]
  have hI0 : 0 ≤ I := setIntegral_nonneg hs fun _ _ => by positivity
  have hM0 : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  have h1 : I ≤ ‖b‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) b w
    rwa [hinner, Complex.norm_real, Real.norm_of_nonneg hI0] at h
  refine ⟨hc2, ?_⟩
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : I * I ≤ I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
      calc I * I ≤ (‖b‖ * ‖w‖) * (‖b‖ * ‖w‖) := mul_self_le_mul_self hI0 h1
        _ = ‖b‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ ‖b‖ ^ 2 * (I * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) := by gcongr
        _ = I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by ring
    exact le_of_mul_le_mul_left h2 hpos

theorem sq_integrable_and_bound (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) :
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
      ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hK : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (sq_nonneg _)
  have hcont : Continuous fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 :=
    (continuous_const.inner (hρ.cont v)).norm.pow 2
  have key : ∀ s, MeasurableSet s → ν s ≠ ⊤ → ∫⁻ g in s, ‖‖⟪b, ρ g v⟫_ℂ‖ ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
    intro s hs hs'
    obtain ⟨hi, hle⟩ := integrableOn_and_setIntegral_sq_le_of_isU ν ρ hρ v hm b hs hs'
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
    apply ENNReal.ofReal_le_ofReal
    simpa only [norm_pow, norm_norm] using hle
  have hInt : Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν :=
    integrable_of_forall_fin_meas_le _ ENNReal.ofReal_lt_top hcont.aestronglyMeasurable key
  refine ⟨hInt, ?_⟩
  have hle := lintegral_le_of_forall_fin_meas_le _ key
  rw [← ofReal_integral_norm_eq_lintegral_enorm hInt, ENNReal.ofReal_le_ofReal_iff hK] at hle
  simpa only [norm_pow, norm_norm] using hle

end GlobalTheory.CompanionTheory.GodementCoeff

end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exact_degrees_of_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1) := by
  intro l _ K χ hN t ht
  haveI hfK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  obtain ⟨L, hLdef⟩ : ∃ L : IntermediateField ℚ_[l] (Om l),
      L = IntermediateField.normalClosure ℚ_[l] ↥K.1 (Om l) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ_[l] ↥L := by
    subst hLdef
    infer_instance
  have hμL : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ L := fun μ x => by
    subst hLdef
    exact μ.fieldRange_le_normalClosure ⟨x, rfl⟩
  have hKL : ∀ x ∈ K.1, x ∈ L := fun x hx => hμL K.1.val ⟨x, hx⟩
  let res : Gal(Om l/↥L) → GQ l := fun σ => σ.restrictScalars ℚ_[l]
  have hresv : ∀ (σ : Gal(Om l/↥L)) (y : ↥L), res σ y = y := fun σ y => σ.commutes y
  have hres : ∀ σ, res σ ∈ GK K := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hresv σ ⟨x, hKL x hx⟩
  obtain ⟨s, hs⟩ : ∃ s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l), ∀ μ, μ ∈ s :=
    ⟨(Set.toFinite (Set.univ : Set (↥K.1 →ₐ[ℚ_[l]] Om l))).toFinset, fun μ => by simp⟩
  have hT0 : (∏ μ ∈ s, t μ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => (ht μ).1
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2
      (GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
        GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one)
  obtain ⟨n, u, hTu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hT0 htirr
  have hTu' : ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l) := by
    rw [hTu, mul_comm]
  have hcyc : ∀ σ : Gal(Om l/↥L),
      (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot (res σ)) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) =
        (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun σ => by
    have h1 := GroundTheory.PAdicHodge.gal_smul_fontaineT σ (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h2 := GroundTheory.PAdicHodge.gal_smul_fontaineT (Formalism.Per6.toBot (res σ))
      (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h3 := h2.symm.trans h1
    exact (algebraMap ℚ_[l] (Formalism.Per6.BdRp l)).injective (mul_right_cancel₀ htirr.ne_zero h3)
  have hn : n = 1 := GlobalTheory.T.hodge_tate_character_weight L (GlobalTheory.T.sen_period_finite_extension GlobalTheory.T.sen_unramified_character_period L) u n
    (fun σ => Algebra.norm ℚ_[l] ((χ ⟨res σ, hres σ⟩ : (↥K.1)ˣ) : ↥K.1))
    (fun σ => by
      rw [← hTu']
      exact GlobalTheory.T.galois_action_period_product K χ t s hs ht (res σ) (hres σ) fun μ x => hresv σ ⟨μ x, hμL μ x⟩)
    (fun σ hσ => (hN (res σ) (hres σ) hσ).trans (hcyc σ))
  subst hn
  intro μ
  exact GlobalTheory.T.period_product_filtration_levels s t K.1.val (hs _) u (by rw [hTu', pow_one]) ((ht _).2.2 rfl) μ (hs μ)

end GlobalTheory.CompanionTheory.LTPer
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Cramer

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem mul_adjugate_submatrix (M : Matrix ι (Fin n) K) (f₀ : Fin n → ι) (i : ι) (j : Fin n) :
    (M * adjugate (M.submatrix f₀ id)) i j = mnr M (Function.update f₀ j i) := by
  have h1 : (M * adjugate (M.submatrix f₀ id)) i j = cramer (M.submatrix f₀ id)ᵀ (M i) j := by
    rw [cramer_eq_adjugate_mulVec, ← adjugate_transpose]
    simp [mulVec, dotProduct, Matrix.mul_apply, transpose_apply, mul_comm]
  rw [h1, cramer_transpose_apply]
  unfold mnr
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab; simp
  · simp [updateRow_apply, hab, Function.update_apply]

theorem eq_mul_of_minor_ratio (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι)
    (h0 : mnr M f₀ ≠ 0) (h0' : mnr M' f₀' ≠ 0)
    (h : ∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') : ∃ c : GL (Fin n) K, M' = M * c.1 := by
  set c := mnr M' f₀' / mnr M f₀ with hcdef
  have hc : ∀ f, mnr M' f = c * mnr M f := fun f => by
    calc mnr M' f = mnr M' f / mnr M' f₀' * mnr M' f₀' := by rw [div_mul_cancel₀ _ h0']
      _ = mnr M f / mnr M f₀ * mnr M' f₀' := by rw [h f]
      _ = c * mnr M f := by rw [hcdef]; ring
  have hc0 : c ≠ 0 := div_ne_zero h0' h0
  set A := M.submatrix f₀ id with hA
  set A' := M'.submatrix f₀ id with hA'
  have hdA : A.det = mnr M f₀ := rfl
  have hdA' : A'.det = c * A.det := hc f₀
  have hA0 : A.det ≠ 0 := h0
  have hdA'0 : A'.det ≠ 0 := by rw [hdA']; exact mul_ne_zero hc0 h0
  have key : M' * adjugate A' = c • (M * adjugate A) := by
    ext i j
    rw [mul_adjugate_submatrix, Matrix.smul_apply, mul_adjugate_submatrix, hc, smul_eq_mul]
  have e1 : M' * adjugate A' * A' = A'.det • M' := by
    rw [Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one]
  have hP : (A⁻¹ * A').det ≠ 0 := by
    rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero h0) hdA'0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (A⁻¹ * A') hP, ?_⟩
  show M' = M * (A⁻¹ * A')
  rw [inv_def, Ring.inverse_eq_inv']
  have e2 : M * ((A.det)⁻¹ • adjugate A * A') = ((A.det)⁻¹ * c⁻¹) • (M' * adjugate A' * A') := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel_right₀ hc0, Matrix.mul_assoc]
  rw [e2, e1, smul_smul, hdA']
  rw [show A.det⁻¹ * c⁻¹ * (c * A.det) = 1 by field_simp, one_smul]

end GlobalTheory.CompanionTheory.GodementH.Cramer

theorem GlobalTheory.CompanionTheory.GodementH.Cramer.main : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M M' : Matrix ι (Fin n) K) (f₀ f₀' : Fin n → ι),
    mnr M f₀ ≠ 0 → mnr M' f₀' ≠ 0 → (∀ f, mnr M f / mnr M f₀ = mnr M' f / mnr M' f₀') → ∃ c : GL (Fin n) K, M' = M * c.1 := by
  intro K _ ι _ _ n M M' f₀ f₀' h0 h0' h
  exact GlobalTheory.CompanionTheory.GodementH.Cramer.eq_mul_of_minor_ratio M M' f₀ f₀' h0 h0' h
end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.continuous_unitary_root_map : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n), Continuous (uR σ hU.1 a h : L → GU σ n) := by
  first | exact @GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | exact GlobalTheory.CompanionTheory.SwapRoot.continuous_uR | (intros; apply GlobalTheory.CompanionTheory.SwapRoot.continuous_uR <;> assumption)
end
