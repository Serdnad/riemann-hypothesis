module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle681
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle762
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle690
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle737
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle724
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RallisExch

theorem exch_general {X ι : Type*} [MeasurableSpace X] [Countable ι] (ν : Measure X) [SFinite ν] (𝓖 : Set X)
    (T : ι → X × X → ℂ) (a b : X → ℂ)
    (hT : ∀ Y, AEStronglyMeasurable (T Y) ((ν.prod ν).restrict (𝓖 ×ˢ 𝓖)))
    (ha : AEStronglyMeasurable a (ν.restrict 𝓖)) (hb : AEStronglyMeasurable b (ν.restrict 𝓖))
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' Y, ‖T Y (g₁, g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    (∀ Y, IntegrableOn (fun p : X × X => star (a p.1) * b p.2 * T Y p) (𝓖 ×ˢ 𝓖) (ν.prod ν)) ∧
    Summable (fun Y => ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * T Y p ∂(ν.prod ν)) ∧
    ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * ∑' Y, T Y p ∂(ν.prod ν) =
      ∑' Y, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * T Y p ∂(ν.prod ν) := by
  have hρ : (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) = (ν.restrict 𝓖).prod (ν.restrict 𝓖) :=
    (Measure.prod_restrict 𝓖 𝓖).symm
  set ρ := (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) with hρdef
  set F : ι → X × X → ℂ := fun Y p => star (a p.1) * b p.2 * T Y p with hFdef
  have ha' : AEStronglyMeasurable (fun p : X × X => star (a p.1)) ρ := by
    rw [hρ]; exact ha.star.comp_fst
  have hb' : AEStronglyMeasurable (fun p : X × X => b p.2) ρ := by
    rw [hρ]; exact hb.comp_snd
  have hF : ∀ Y, AEStronglyMeasurable (F Y) ρ := fun Y => (ha'.mul hb').mul (hT Y)
  have hnorm : ∀ Y p, ‖F Y p‖ₑ = ‖T Y p‖ₑ * ‖a p.1‖ₑ * ‖b p.2‖ₑ := by
    intro Y p
    have hs : ‖star (a p.1)‖ₑ = ‖a p.1‖ₑ := by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_star]
    simp only [F, enorm_mul, hs]; ring
  have hsum : ∑' Y, ∫⁻ p, ‖F Y p‖ₑ ∂ρ ≠ ⊤ := by
    rw [← lintegral_tsum (fun Y => (hF Y).enorm)]
    simp_rw [hnorm]
    rw [hρ, lintegral_prod _ ?_]
    · exact hfin
    · rw [← hρ]
      exact AEMeasurable.tsum fun Y => by
        simpa [hnorm] using (hF Y).enorm
  have hint : ∀ Y, Integrable (F Y) ρ := fun Y =>
    ⟨hF Y, lt_of_le_of_lt (ENNReal.le_tsum (f := fun Y => ∫⁻ p, ‖F Y p‖ₑ ∂ρ) Y)
      (lt_top_iff_ne_top.2 hsum)⟩
  refine ⟨hint, ?_, ?_⟩
  · refine Summable.of_norm_bounded (ENNReal.summable_toReal hsum) fun Y => ?_
    have h1 := enorm_integral_le_lintegral_enorm (μ := ρ) (F Y)
    rw [← ofReal_norm_eq_enorm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top hsum (ENNReal.le_tsum Y))).1 h1
  · have : (fun p : X × X => star (a p.1) * b p.2 * ∑' Y, T Y p) = fun p => ∑' Y, F Y p := by
      funext p; exact tsum_mul_left.symm
    rw [this]
    exact integral_tsum hF hsum

end GlobalTheory.RallisExch

namespace GlobalTheory.RallisExch

open scoped GlobalTheory.GaugeEx

theorem eisAbs_exchange : ∀ D : D7, EisAbs D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ Y : Lag W, IntegrableOn (fun p : GA D W × GA D W => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) (𝓖 ×ˢ 𝓖) (νW.prod νW)) ∧ Summable (fun Y : Lag W => ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW)) ∧ ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∑' Y : Lag W, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hE ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ h1 h2 hA1 hC1 hA2 hC2
  haveI : Countable (Lag W) := GlobalTheory.T.countable_doubled_hermitian_lagrangians D W
  haveI : SigmaFinite νW := by haveI := hS.haarW; infer_instance
  have hT : ∀ Y : Lag W, AEStronglyMeasurable
      (fun p : GA D W × GA D W => lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂))
      ((νW.prod νW).restrict (𝓖 ×ˢ 𝓖)) := fun Y =>
    (GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ h1 h2 (fr Y)).aestronglyMeasurable
  exact exch_general νW 𝓖 (fun Y p => lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) φ₁ φ₂ hT
    hA1.cont.aestronglyMeasurable hA2.cont.aestronglyMeasurable
    (hE ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2 φ₁ φ₂ hA1 hC1 hA2 hC2)

end GlobalTheory.RallisExch
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem graph_term_of_termMove {D : D7} (hTM : TermMove D) {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) {Y : Lag W} (hY : IsLagFrame W Y (1, c)) (g₁ g₂ : GA D W) :
    lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂) = thetaIP μ 𝓕 (om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂) f₁ := by
  have hmul : ∀ p q (f : WO V W → ℂ), om p (om q f) = om (p * q) f := fun p q f => by rw [map_mul]; rfl
  have p₁ := hS.weil.om_pres (1, g₁) f₁ h₁
  have p₂ := hS.weil.om_pres (1, g₂) f₂ h₂
  obtain ⟨hfr, hg⟩ := hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ p₁ p₂
  have e1 : om (1, g₁⁻¹) (om (1, γ⁻¹) (om (1, g₂) f₂)) = om (1, g₁⁻¹ * γ⁻¹ * g₂) f₂ := by
    rw [hmul, hmul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, one_mul, mul_assoc]
  have e2 : om (1, g₁⁻¹) (om (1, g₁) f₁) = f₁ := by
    rw [hmul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  rw [← hfr Y (1, c) hY, (hg γ hγ c hc).2,
    ← GlobalTheory.T.theta_pairing_invariant D ψ V W χV χW om μ 𝓕 hS.weil hS.covol (1, g₁⁻¹) _ _ (hS.weil.om_pres (1, γ⁻¹) _ p₂) p₁, e1, e2]


open scoped GlobalTheory.GaugeEx in
theorem rallis_graphs : ∀ D : D7, EisAbs D → TermMove D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧ ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW := by
  intro D hEA hTM ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI := hS.haarW
  obtain ⟨e, he⟩ := GlobalTheory.T.lagrangians_transverse_eq_graphs_rational_unitary D W
  haveI : Countable (Lag W) := GlobalTheory.T.countable_doubled_hermitian_lagrangians D W
  haveI : Countable (GQ W) := e.injective.countable
  choose c hc hcf using he
  let P : GA D W → ℂ := fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁
  have hT : ∀ (γ : GQ W) (p : GA D W × GA D W),
      lagTerm μ 𝓕 (fr (e γ).1) (om (1, p.1) f₁) (om (1, p.2) f₂) = P (p.1⁻¹ * (γ : GA D W)⁻¹ * p.2) :=
    fun γ p => graph_term_of_termMove hTM hS hf₁ hf₂ γ.2 (hc γ) (hcf γ) p.1 p.2
  have hPm : StronglyMeasurable P := by
    have h := GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ hf₁ hf₂ (1, 1)
    have hcont : Continuous fun g : GA D W => ((1 : GA D W), g) := continuous_const.prodMk continuous_id
    convert h.comp_measurable hcont.measurable using 1
    funext g
    simp only [Function.comp_apply]
    rw [lagTerm_one_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' γ : GQ W, ‖P (g₁⁻¹ * (γ : GA D W)⁻¹ * g₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ ∂νW ∂νW ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hEA ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂) ?_
    refine lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_
    have hinj : Function.Injective fun γ : GQ W => (e γ).1 := Subtype.val_injective.comp e.injective
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun Y => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ))
    refine tsum_congr fun γ => ?_
    rw [← hT γ (g₁, g₂)]
  obtain ⟨hI, hE⟩ := GlobalTheory.T.unfold_tsum_integral_fundamentalDomain νW (GQ W) 𝓖 hS.fdW φ₁ φ₂ P ha₁.cont ha₂.cont ha₂.left hPm hfin
  refine ⟨hI, ?_⟩
  refine ((e.tsum_eq (fun Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥} =>
    ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW))).symm.trans ?_).trans hE
  refine tsum_congr fun γ => ?_
  congr 1
  funext p
  rw [hT γ p]

end GlobalTheory.RawLift
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.Move

variable {D : D7}

theorem heisO_eval_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : symplOH S T 0 w = 0 := by
    simp [symplOH, symplO, hO]
  simp [heisO, h]

theorem mt_one_eq (S : HSp D) : mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_eq (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by simp [Formalism.L2.Theta.mt]

theorem actO_one_left (V W : HSp D) (γ : GA D W) (w : WO V W) :
    actO V W 1 γ w = HMul.hMul (mt W γ) (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) := by
  unfold actO
  rw [inv_one, mt_one_eq, Matrix.mul_one]

theorem om_rat_actO {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ) f (actO V W 1 γ w) = f w := by
  have h1 := H.om_heis 1 γ w f hf
  have h2 := H.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all H.std hf w)
  rw [← heisO_eval_zero ψ V W (actO V W 1 γ w) (om (1, γ) f), ← h1, h2, heisO_eval_zero]

theorem om_rat_inv_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ⁻¹) f w = f (actO V W 1 γ w) := by
  have h := om_rat_actO H (inv_mem hγ) hf (actO V W 1 γ w)
  have e : actO V W 1 γ⁻¹ (actO V W 1 γ w) = w := by
    rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc, ← mt_mul_eq, inv_mul_cancel, mt_one_eq, Matrix.one_mul]
  rwa [e] at h

theorem ratMul_eq_actO {V W : HSp D} {γ : GA D W} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) (u : WO V W) : ratMul c u = actO V W 1 γ u := by
  rw [actO_one_left, hc]
  rfl

theorem termMove : ∀ D : D7, TermMove D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr h f₁ f₂ h₁ h₂
  refine ⟨fun Y C hC => lagTerm_frame_indep D ψ V W μ 𝓕 h.covol h.weil.std f₁ f₂ h₁ h₂ Y C (fr Y) hC (h.frame Y),
    fun γ hγ c hc => ⟨fun C => ?_, ?_⟩⟩
  · unfold lagTerm
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← ratMul_ratMul, ratMul_eq_actO hc, om_rat_actO h.weil hγ h₁]
  · unfold lagTerm thetaIP
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [ratMul_one, om_rat_inv_apply h.weil hγ h₂, ratMul_eq_actO hc, mul_comm]

end GlobalTheory.RawLift.Move
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism



theorem exists_crys_prisms : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∃ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), PP.I = Ideal.span {(l : PP.A)} ∧ δ.comp p₀ = δ.comp p₁ ∧ (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) ∧ (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) ∧ (∀ τ y, j τ (PP.D.φ y) = φ₂ (j (τ - 1) y)) ∧ ∃ hS : ∀ τ y (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e, (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e) ∧ ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), Cr.I = Ideal.span {(l : Cr.A)} → (∀ x, eC (Cr.D.φ x) = frobC l (eC x)) → (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ g : ↥(GK (ϖ.field a)), ∃ ev : GlobalTheory.Prism.Hom PP Cr, ev.comp p₀ = h.comp (ϖ.toAinf a) ∧ ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) ∧ ∀ (y : PP.A) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (ev.f y) - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K fun τ => ⟨_, hS τ y i⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ sh φ₂ hsh hφC hφsh
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hlp : l.Prime := Fact.out
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps hlK
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := natCast_ne_zero_ps hl1
  have tf1 : ∀ x : ZMod a → K⟦X⟧, (l : ZMod a → K⟦X⟧) * x = 0 → x = 0 := tf_pi hl1
  have tf2 : ∀ x : ZMod a → K⟦X⟧⟦X⟧, (l : ZMod a → K⟦X⟧⟦X⟧) * x = 0 → x = 0 := tf_pi hl2
  have tfS : ∀ x : ↥(Sd t K e), (l : ↥(Sd t K e)) * x = 0 → x = 0 := tf_sub _ tf1
  have tfP : ∀ x : ↥(PPd t K e), (l : ↥(PPd t K e)) * x = 0 → x = 0 := tf_sub _ tf2
  haveI hcS := GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime l a e O K t
  haveI hcP := GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring l a e O K t
  have hSd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := GlobalTheory.T.mem_sdSet_of_mem_sd l a e O K t
  have hPd : ∀ F ∈ PPd t K e, F ∈ PPSet t K e := GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t

  let φS : ↥(Sd t K e) →+* ↥(Sd t K e) := (frobTot K a l).toRingHom.restrict (Sd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F hF)).1
  have hφS : ∀ F : ↥(Sd t K e), ∃ B, φS F = F ^ l + (l : ↥(Sd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DS : Delta l ↥(Sd t K e) := Delta.ofLift l φS tfS hφS
  let φP : ↥(PPd t K e) →+* ↥(PPd t K e) := (frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F hF)).1
  have hφP : ∀ F : ↥(PPd t K e), ∃ B, φP F = F ^ l + (l : ↥(PPd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DP : Delta l ↥(PPd t K e) := Delta.ofLift l φP tfP hφP

  let i0 : (Wq l a)⟦X⟧ →+* ↥(Sd t K e) := ((inclS t K).comp (frobS l a)).codRestrict (Sd t K e)
    fun x => Subring.subset_closure (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _)
  let iP0 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((constP a K).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _))
  let iP1 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1
  let dg : ↥(PPd t K e) →+* ↥(Sd t K e) := (diag a K).restrict (PPd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (diag_mem t e (hPd F hF))
  have hdg0 : ∀ x, dg (iP0 x) = i0 x := fun x => Subtype.ext (funext fun τ => constantCoeff_C _)
  obtain ⟨BE, hBE, hE⟩ := GlobalTheory.T.frobenius_eisenstein_mem_prime_mul_dividedPowerSeries l a e O K t
  have hE0 : i0 (eis l a e) = (l : ↥(Sd t K e)) * ⟨BE, Subring.subset_closure hBE⟩ := Subtype.ext hE
  have hEP0 : iP0 (eis l a e) = (l : ↥(PPd t K e)) * ⟨constP a K BE, Subring.subset_closure (constP_mem t e hBE)⟩ :=
    Subtype.ext (by
      change constP a K (inclS t K (frobS l a (eis l a e))) = _
      rw [hE, map_mul, map_natCast]; rfl)
  have hdiff : ∀ x, iP1 x - iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).2
    refine Ideal.mem_span_singleton'.2 ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext ?_⟩
    change B * (l : ZMod a → K⟦X⟧⟦X⟧) = _ - _
    rw [mul_comm]; exact h.symm
  have hmemS : ∀ x ∈ Ideal.span {eis l a e}, i0 x ∈ Ideal.span {(l : ↥(Sd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hE0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP0 : ∀ x ∈ Ideal.span {eis l a e}, iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hEP0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP1 : ∀ x ∈ Ideal.span {eis l a e}, iP1 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    have h := Ideal.add_mem _ (hdiff x) (hmemP0 x hx)
    rwa [sub_add_cancel] at h

  let str0 : ↥(OL (ϖ.field a)) →+* ↥(Sd t K e) ⧸ Ideal.span {(l : ↥(Sd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp i0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemS x hx)).comp (ϖ.strMap a)
  let strP : ↥(OL (ϖ.field a)) →+* ↥(PPd t K e) ⧸ Ideal.span {(l : ↥(PPd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp iP0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemP0 x hx)).comp (ϖ.strMap a)
  let S₀ : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DS (l : ↥(Sd t K e)) (nzd_of_tf tfS)
    (isUnit_delta_l DS tfS) (by rw [sup_idem]; exact hcS) (bdd_self l) str0
  let PP : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DP (l : ↥(PPd t K e)) (nzd_of_tf tfP)
    (isUnit_delta_l DP tfP) (by rw [sup_idem]; exact hcP) (bdd_self l) strP

  have hlift : ∀ r : ↥(OL (ϖ.field a)), ∃ x : (Wq l a)⟦X⟧, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r :=
    fun r => Ideal.Quotient.mk_surjective _
  have hstrP : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → strP r = Ideal.Quotient.mk _ (iP0 x) :=
    fun r x h => by simp only [strP, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]
  have hstr0 : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → str0 r = Ideal.Quotient.mk _ (i0 x) :=
    fun r x h => by simp only [str0, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]

  let p₀ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP0
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP0 fun x => Subtype.ext (funext fun τ => by
        change C (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (C (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφC, frob_toAc])
      f_I := hmemP0
      f_str := fun r x h => (hstrP r x h).symm }
  let p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP1
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP1 fun x => Subtype.ext (funext fun τ => by
        change sh (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (sh (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφsh, frob_toAc])
      f_I := hmemP1
      f_str := fun r x h => by
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) (iP1 x) = strP r
        rw [hstrP r x h, Ideal.Quotient.eq]
        exact hdiff x }
  let δ : GlobalTheory.Prism.Hom PP S₀ :=
    { f := dg
      f_δ := DP.map_δ_of_map_φ DS tfS dg fun y => Subtype.ext (funext fun τ => by
        change constantCoeff (φ₂ (y.1 (τ - 1))) = frob K l (constantCoeff (y.1 (τ - 1)))
        exact constantCoeff_φ₂ sh hsh l φ₂ hφC hφsh _)
      f_I := fun y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        exact (show ∀ c' : ↥(PPd t K e), dg (c' * (l : ↥(PPd t K e))) ∈ Ideal.span {(l : ↥(Sd t K e))} from
          fun c' => by rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
      f_str := fun r y h => by
        obtain ⟨x, hx⟩ := hlift r
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at h
        rw [hstrP r x hx] at h
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y) = str0 r
        rw [hstr0 r x hx, ← hdg0]
        exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
            Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y') =
            Ideal.Quotient.mk _ (dg (iP0 x)) from fun y' h' => by
          rw [Ideal.Quotient.eq] at h' ⊢
          rw [← map_sub]
          obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
          rw [← hc, map_mul, map_natCast]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y h }
  let j : ZMod a → ↥(PPd t K e) →+* K⟦X⟧⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ).comp (PPd t K e).subtype
  let j₀ : ZMod a → ↥(Sd t K e) →+* K⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ).comp (Sd t K e).subtype
  have hS1 : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e :=
    fun τ y i => GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t y.1 (hPd _ y.2) τ i
  have hS : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e :=
    fun τ y i => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ HasU.X_mem i) (hS1 τ y i)
  refine ⟨PP, S₀, p₀, p₁, δ, j, j₀, rfl, ?_, fun τ y => rfl, fun τ x => ⟨rfl, rfl⟩, fun τ y => rfl, hS, hS1, ?_⟩
  · exact Hom.ext' (RingHom.ext fun x => Subtype.ext (funext fun τ => by
      change constantCoeff (C (toAc t K (frobS l a x) τ : K⟦X⟧)) = constantCoeff (sh (toAc t K (frobS l a x) τ : K⟦X⟧))
      rw [constantCoeff_C, constantCoeff_sh sh hsh]))
  · intro Cr eC h hCI hCφ hh g
    obtain ⟨E, hEa, hEb, hEc, hEd⟩ := GlobalTheory.T.crystallineEval_ringHom_frobenius_taylor l a e O K t ϖ sh hsh φ₂ hφC hφsh g
    have tfC : ∀ x : Cr.A, (l : Cr.A) * x = 0 → x = 0 := fun x hx => eC.injective (by
      have h1 := congrArg eC hx
      rw [map_mul, map_natCast, map_zero] at h1
      rw [map_zero]; exact acris_nat_cancel hlp.ne_zero h1)
    have hev0 : ∀ x, eC.symm (E (iP0 x)) = h.f ((ϖ.toAinf a).f x) := fun x => eC.injective (by
      rw [RingEquiv.apply_symm_apply]; exact (hEa x _).trans (hh _).symm)
    let ev : GlobalTheory.Prism.Hom PP Cr :=
      { f := eC.symm.toRingHom.comp E
        f_δ := DP.map_δ_of_map_φ Cr.D tfC _ fun y => eC.injective (by
          change eC (eC.symm (E (φP y))) = eC (Cr.D.φ (eC.symm (E y)))
          rw [hCφ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
          exact hEc y.1 y.2 _)
        f_I := fun y hy => by
          rw [hCI]
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
          exact (show ∀ c' : ↥(PPd t K e), eC.symm (E (c' * (l : ↥(PPd t K e)))) ∈ Ideal.span {(l : Cr.A)} from
            fun c' => by
              rw [map_mul, map_mul, map_natCast, map_natCast]
              exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
        f_str := fun r y hy => by
          obtain ⟨x, hx⟩ := hlift r
          change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at hy
          rw [hstrP r x hx] at hy
          have h2 := (h.comp (ϖ.toAinf a)).f_str r x hx
          change Ideal.Quotient.mk Cr.I (h.f ((ϖ.toAinf a).f x)) = Cr.str r at h2
          rw [← h2, ← hev0]
          exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
              Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk Cr.I (eC.symm (E y')) =
              Ideal.Quotient.mk Cr.I (eC.symm (E (iP0 x))) from fun y' h' => by
            rw [Ideal.Quotient.eq] at h' ⊢
            rw [← map_sub, ← map_sub, hCI]
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
            rw [← hc, map_mul, map_mul, map_natCast, map_natCast]
            exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y hy }
    refine ⟨ev, Hom.ext' (RingHom.ext fun x => hev0 x), Hom.ext' (RingHom.ext fun x => eC.injective ?_), fun y r => ?_⟩
    · change eC (eC.symm (E (iP1 x))) = eC (h.f ((ainfHom (ϖ.field a) g).f ((ϖ.toAinf a).f x)))
      rw [RingEquiv.apply_symm_apply]
      exact (hEb x _).trans (hh _).symm
    · change ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (eC.symm (E y)) - _
      rw [RingEquiv.apply_symm_apply]
      exact hEd y.1 y.2 (hS · y) r

end GlobalTheory.CrysPrism
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  first | exact @GlobalTheory.BSP.seed_module_lAdic_closed | exact GlobalTheory.BSP.seed_module_lAdic_closed | (intros; apply GlobalTheory.BSP.seed_module_lAdic_closed <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  first | exact @GlobalTheory.BSP.HeightAprime.main | exact GlobalTheory.BSP.HeightAprime.main | (intros; apply GlobalTheory.BSP.HeightAprime.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem _root_.GlobalTheory.T.isUnit_discBasis_crystallineLattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  first | exact @GlobalTheory.BSP.height_Z_isUnit | exact GlobalTheory.BSP.height_Z_isUnit | (intros; apply GlobalTheory.BSP.height_Z_isUnit <;> assumption)
end
