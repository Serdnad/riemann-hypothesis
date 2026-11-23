module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle136
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle548
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle537
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle541
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle184
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle550
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaStepIntegrandFiniteDoubleCosets
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle549
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionOnAdelicFunctionsEqZeroOfNoLift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle564
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem enorm_fl_le {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (Th : GA D V → ℂ) (hTh : ∀ n, ‖Th n‖ ≤ 1)
    (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) :
    ‖fl ψ d W v vb vU Th x Ψ‖ₑ ≤
      ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ v.μ v.𝓕 Ψ (x ⬝ u.1.1) (x ⬝ b)‖ₑ ∂vb.μ ∂vU.ν := by
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun u => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun b => ?_)
  simp only [flFun]
  rw [enorm_mul]
  refine mul_le_of_le_one_left' ?_
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_one.2 (hTh _)

theorem liftS_mul {D : D7} {V W : HSp D} (om : Om V W) (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (G : GA D W → ℂ)
    (Φ : WO V W → ℂ) (n g : GA D V) : liftS om μ 𝓕 G Φ (n * g) = liftS om μ 𝓕 G (om (g, 1) Φ) n := by
  have e : ∀ h, thetaKO om (n * g) h Φ = thetaKO om n h (om (g, 1) Φ) := fun h => by
    simp only [thetaKO]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [liftS, Formalism.IndefR.Lift.liftInt, e]

theorem besPer_lift_eq_integral_kerBF : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∀ 𝓑 : Set (GA D J.W), IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ → IntegrableOn (kerBF s φ G Φ) 𝓑 s.vW.μ ∧ B.per ψ φ (s.lift G Φ) = ∫ h in 𝓑, kerBF s φ G Φ h ∂s.vW.μ := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ 𝓑 h𝓑
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨hb, hg, hx, hR, -, -⟩ := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  have hemb : Continuous (embA B.d B.o) :=
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D B.V B.V₀ ρ B.d).2.2.2.2.1.comp
      (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hTh := GlobalTheory.T.conjBesselCharacter_isUnfoldingThetaFunction_of_gram_zero D ψ s.weil.std ρ B J.W J.d.e hg
  have h𝓑' := h𝓑
  rw [← hR] at h𝓑'
  set Th : GA D B.V → ℂ := fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) with hThd
  have hn : ∀ n, ‖Th n‖ ≤ 1 := fun n => by
    simp only [hThd, norm_star, psiBes, psiE]
    exact (s.weil.std.1.2.1 _).le
  have hfl : ∀ p, fl ψ B.d J.W s.vS s.vT s.vU Th (rat J.d.e) (s.om p Φ) = flatBF s (s.om p Φ) 0 := fun p => by
    rw [← hx]
    exact GlobalTheory.T.flagUnipotentUnfolding_besselFourierJacobi_eq D ψ ρ B J s _ (s.weil.om_pres p Φ hΦ)
  have hom : ∀ g h, s.om (1, h) (s.om (g, 1) Φ) = s.om (g, h) Φ := fun g h => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

  have h1 : ∀ g, ∫ n in B.vN.𝓝, Th n.1 * s.lift G Φ (n.1 * g) ∂B.vN.ν =
      ∫ h in 𝓑, G h * flatBF s (s.om (g, h) Φ) 0 ∂s.vW.μ := fun g => by
    have := (GlobalTheory.T.unfold_over_flagUnipotent_thetaLift D hD ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS B.vN s.vT s.vU s.vW J.d.e Th
      hb hTh G (s.om (g, 1) Φ) hG (s.weil.om_pres _ Φ hΦ) 𝓑 h𝓑').2
    simp only [hom, hfl] at this
    simp only [Step.lift, liftS_mul]
    exact this

  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  haveI : BorelSpace (GA D B.A) := ⟨rfl⟩
  haveI : BorelSpace (GA D J.W) := ⟨rfl⟩
  haveI := B.vA.haar
  haveI := s.vW.haar
  obtain ⟨hc, hd, -⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D B.A (GQ B.A) le_rfl

  set f : GA D B.A → GA D J.W → ℂ := fun h₀ h => φ h₀ * (G h * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0) with hf
  have hcont : Continuous (Function.uncurry f) := by
    have h2 := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hb.1 Φ hΦ
    rw [← hx] at h2
    have h3 : Continuous fun p : GA D B.A × GA D J.W =>
        (((embA B.d B.o p.1, p.2), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((hemb.comp continuous_fst).prodMk continuous_snd).prodMk continuous_const
    have h4 := h2.comp h3
    simp only [Function.comp_def] at h4
    have h5 : Continuous fun p : GA D B.A × GA D J.W => flatBF s (s.om (embA B.d B.o p.1, p.2) Φ) 0 := by
      simp only [flatBF, flat]
      exact h4
    exact (hφ.2.comp continuous_fst).mul ((hG.2.1.comp continuous_snd).mul h5)
  have hinv := (GlobalTheory.T.unfoldedBesselJacobiKernel_laws D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ).2.2.1
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.unfolded_besselJacobi_integral_abs_le D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS s.vT s.vU s.vW J.d.e
    hb G Φ hG hΦ 𝓑 h𝓑'
  have hint : Integrable (Function.uncurry f) ((B.vA.μ.restrict B.vA.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
    refine GlobalTheory.fubini_compact_quotient (GA D B.A) B.vA.μ (GQ B.A) hc hd B.cpt B.vA.𝓕 B.vA.fund (GA D J.W) _ f
      hcont.measurable (fun γ hγ h x => by simp only [hf, hφ.1 γ hγ, hinv γ hγ]) fun K hK => ?_
    have hq : Continuous fun h₀ => ‖φ h₀‖ * (C * height B.V (embA B.d B.o h₀) ^ A) :=
      hφ.2.norm.mul (continuous_const.mul (((continuous_height B.V).comp hemb).pow A))
    obtain ⟨M, hM⟩ := hK.bddAbove_image hq.continuousOn
    refine ⟨M.toNNReal, fun h₀ hh => ?_⟩
    calc ∫⁻ h in 𝓑, ‖f h₀ h‖ₑ ∂s.vW.μ
        = ‖φ h₀‖ₑ * ∫⁻ h in 𝓑, ‖G h‖ₑ * ‖flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0‖ₑ ∂s.vW.μ := by
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          simp only [hf, enorm_mul]
      _ ≤ ‖φ h₀‖ₑ * ENNReal.ofReal (C * height B.V (embA B.d B.o h₀) ^ A) := by
          refine mul_le_mul_right (le_trans (lintegral_mono fun h => mul_le_mul_right ?_ _) (hC _)) _
          rw [← hfl]
          exact enorm_fl_le ψ B.d J.W s.vS s.vT s.vU Th hn _ _
      _ = ENNReal.ofReal (‖φ h₀‖ * (C * height B.V (embA B.d B.o h₀) ^ A)) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ M.toNNReal := ENNReal.ofReal_le_ofReal (hM ⟨h₀, hh, rfl⟩)
  have hker : kerBF s φ G Φ = fun h => ∫ h₀ in B.vA.𝓕, f h₀ h ∂B.vA.μ := by
    funext h
    simp only [kerBF, hf]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_left_comm _ _ _)
  rw [hker]
  refine ⟨hint.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hint]
  simp only [BesLev.per, besPer, besFun, hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
  simp only
  rw [integral_const_mul, ← h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hThd]
  ring

end GlobalTheory.Unf
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.jacobiToBessel_second_step_flat_support_ramified : ∀ D : D7, GlobalTheory.FinPl.SuppSecond D := by
  first | exact @GlobalTheory.FinPl.suppSecond_holds | exact GlobalTheory.FinPl.suppSecond_holds | (intros; apply GlobalTheory.FinPl.suppSecond_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

theorem _root_.GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∀ q₂ ∈ GfC (c.V (j + 1 + 1)), integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1 + 1), q₂ = r * y * (κ * k) := by
  first | exact @GlobalTheory.DStepSuppSecond.integ_support | exact GlobalTheory.DStepSuppSecond.integ_support | (intros; apply GlobalTheory.DStepSuppSecond.integ_support <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

theorem _root_.GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ GfC (c.V (j + 1)), ∀ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1), q₁ = r * y * (κ * k) := by
  first | exact @GlobalTheory.DStepSupp.main | exact GlobalTheory.DStepSupp.main | (intros; apply GlobalTheory.DStepSupp.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.doubleThetaStep_integrand_finite_doubleCosets : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (r : ℕ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → (∃ T : Finset (grpAt S.J.W (places fun i => Q i.succ) × GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k), ∀ x y, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ ((jacGrp S.J.d).subgroupOf (grpAt S.J.W (places fun i => Q i.succ))).prod (RFJ (Q 0).k (Q 0).n₁ ((Q 0).c + 1 + 1) (σ + 1)), ∃ κ ∈ (levJ fun i => Q i.succ).prod (Q 0).L₁.J, x = r * t * κ) ∧ ∀ x, ∃ T : Finset (grpAt S.B'.V (places fun i => Q i.succ) × GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k), ∀ y, pint Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x y ≠ 0 → ∃ t ∈ T, ∃ r ∈ ((besGrp S.B'.d S.B'.o).subgroupOf (grpAt S.B'.V (places fun i => Q i.succ))).prod (R (Q 0).k (Q 0).n₂ ((Q 0).c + 1) (σ + 1)), ∃ κ ∈ (levB fun i => Q i.succ).prod (Q 0).L₂.J, y = r * t * κ := by
  first | exact @GlobalTheory.QCells.finite_cells | exact GlobalTheory.QCells.finite_cells | (intros; apply GlobalTheory.QCells.finite_cells <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.UpInjRow

theorem upInj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → R.Sb = R.Pg → (∀ t P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R t P) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → BForm R SF ∧ UpInj R := by
  intro hDS hHCF hHCM hCW hCRD hHowe hWS hHecke hSEC hUD D G _ _ Pl0 T A Ks _ _ _ R F hGiv hcc _hSb hFix SF hSF
  have hSc := GlobalTheory.T.thetaChainStep_positive_scalar_standingHypotheses hDS hHCF hHCM hCW hCRD hHowe hWS hHecke hSEC hUD R F hGiv hcc
  have hK := GlobalTheory.T.thetaLift_adjoint_keeps_spherical_parts_off_tuple hCRD hHowe R F hGiv.core hFix
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R
  have hB := GlobalTheory.ChainScalar.bForm R F hGiv.core hS hSc hK SF hSF
  exact ⟨hB, GlobalTheory.Core.Rk.upInj_of_bForm R F hGiv.core hS hGiv.irr hSc SF hSF hB⟩

end GlobalTheory.Core.Rk.UpInjRow
end
