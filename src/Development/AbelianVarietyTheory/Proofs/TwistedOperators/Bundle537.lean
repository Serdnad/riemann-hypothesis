module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle190
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle286
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.continuousMean_vanishing_on_strips_at_one : ∀ (D : D7) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (R K : Subgroup (GA D W)), IsClosed (R : Set (GA D W)) → (∀ a ∈ GinfC W, ∀ b ∈ GfC W, a * b ∈ R → a ∈ R ∧ b ∈ R) → K ≤ GfC W → IsCompact (K : Set (GA D W)) → IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) → ∀ (μR : Measure R), μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (𝓡 : Set R) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ W ⊓ R).subgroupOf R) 𝓡 μR → IsFundamentalDomain (GQ W ⊓ R : Subgroup (GA D W)) 𝓑 vW.μ → ∀ f : GA D W → ℂ, Measurable f → (∀ γ ∈ GQ W ⊓ R, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 vW.μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → (Continuous fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) → (∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W R C) ∧ ∫ h in 𝓑 ∩ strip W R C, f h ∂vW.μ = 0) → ∫ r in 𝓡, f r ∂μR = 0 := by
  first | exact @GlobalTheory.StripVanish.mean_eq_zero_of_strips | exact GlobalTheory.StripVanish.mean_eq_zero_of_strips | (intros; apply GlobalTheory.StripVanish.mean_eq_zero_of_strips <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.FromBes

theorem conjBessel_isTh (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (ρ : ℕ) (B : BesL D ρ) (W : HSp D)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx₀ : gramQ W x₀ = 0) :
    IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  have hC := GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  set z := vecB B.o B.ζ with hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_star.comp ((hC.1 z).comp continuous_subtype_val)
  · intro γ hγ hγN n hn
    rw [psiBes_mul B.d ψ 1 z hγN hn, hC.2.1 z γ hγ, one_mul]
  · intro c n hn
    rw [psiBes_mul B.d ψ 1 z (B.d.nC_mem_NFlag c) hn, psiBes_nC, one_mul,
      GlobalTheory.Unf.CutChar.psi_qS_eq_one D ψ hψ B.V B.V₀ ρ B.d W x₀ hx₀ c, star_one, one_mul]
  · intro j a haj hai _
    obtain ⟨s, hs⟩ := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
    have key : ∃ v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧ (∀ i k : Fin ρ, k ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (Pi.single k 1)) v * GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a i = 0) ∧ ∀ u : GA D B.V, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv B.V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → (∀ i : {i : Fin ρ // i ≤ j}, u ∈ fixer B.V (B.d.jX.submatrix id fun _ : Fin 1 => i.1)) ∧ simpleSum B.d z u = s := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.2) with h | h
      · exact GlobalTheory.T.exists_transvection_fixing_first_vectors_sum D B.V B.V₀ ρ B.d z j a haj hai h s
      · exact GlobalTheory.T.exists_transvection_fixing_isotropic_last_sum D B.V B.V₀ ρ B.d z (GlobalTheory.Unf.CutChar.vecB_norm_ne D B.V₀ B.A B.L B.o B.ζ B.line) j a haj hai h s
    obtain ⟨v, hv0, hvT, hv⟩ := key
    obtain ⟨u, hu⟩ := GlobalTheory.T.transvection_isUnitaryAdelic D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hv0
    obtain ⟨hfix, hus⟩ := hv u hu
    have huN : u ∈ Nfix B.d j :=
      ⟨GlobalTheory.T.transvection_strictUpper_mem_flagUnipotentRadical D B.V B.V₀ ρ B.d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a) v hvT u hu, Subgroup.mem_iInf.2 hfix⟩
    have hval : psiBes ψ B.d 1 z u = psiE ψ s := by
      rw [psiBes, hus, map_one, one_mul]
    refine ⟨v, u, star (psiE ψ s), hv0, hu, huN, ?_, ?_⟩
    · intro h1
      apply hs
      have := congrArg star h1
      rwa [star_star, star_one] at this
    · intro n hn n' hn'
      have huF : u ∈ flagN B.d := huN.1
      rw [psiBes_mul B.d ψ 1 z (mul_mem hn huF) hn', psiBes_mul B.d ψ 1 z hn huF, hval,
        psiBes_mul B.d ψ 1 z hn hn']
      simp only [star_mul']
      ring

theorem fl_eq_flBF (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J)
    (Ψ : WO B.V J.W → ℂ) (hΨ : IsThetaFunO ψ B.V J.W Ψ) :
    fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flBF flatS flatAt
  congr 1
  funext u
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  unfold flFun flatFun evalAt
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact GlobalTheory.Unf.StepFour.integrand_eq hψ B.d J.d _ _ (hf _) b

theorem isTh_and_fl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), IsTh ψ B.d J.W J.d.e (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) ∧ ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flBF s Ψ 0 := by
  intro D ψ ρ B J s
  exact ⟨conjBessel_isTh D ψ s.weil.std ρ B J.W J.d.e (gramQ_e J.d), fun Ψ hΨ => fl_eq_flBF D ψ ρ B J s Ψ hΨ⟩

end GlobalTheory.Asc.FromBes

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (xLast B.d (vecB B.o B.ζ)) = d.qS B.L c (zEll B.L (σ + 1) B.ζ) := by
  first | exact @GlobalTheory.Asc.FBL.basePoint_spec | exact GlobalTheory.Asc.FBL.basePoint_spec | (intros; apply GlobalTheory.Asc.FBL.basePoint_spec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

theorem _root_.GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  first | exact @GlobalTheory.BplusLaws.bplus_add_bound | exact GlobalTheory.BplusLaws.bplus_add_bound | (intros; apply GlobalTheory.BplusLaws.bplus_add_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

theorem _root_.GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  first | exact @GlobalTheory.BplusUnip.bplus_rTr_unip | exact GlobalTheory.BplusUnip.bplus_rTr_unip | (intros; apply GlobalTheory.BplusUnip.bplus_rTr_unip <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

theorem _root_.GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  first | exact @GlobalTheory.BplusShift.bplus_rTr | exact GlobalTheory.BplusShift.bplus_rTr | (intros; apply GlobalTheory.BplusShift.bplus_rTr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

namespace GlobalTheory.SphGlobX

theorem loc_mem_KAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hK : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idem F v) (GlobalTheory.FinDecomp.idem_mul_self v) K ∈ GlobalTheory.InertSph.KAt σ W v := by
  have hfix : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.FinDecomp.idem F v • z = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, y, -, rfl⟩ := hz
      rw [smul_smul, GlobalTheory.FinDecomp.idem_mul_of_at ha]
    | zero => simp
    | add z z' _ _ h h' => rw [smul_add, h, h']
    | neg z _ h => rw [smul_neg, h]
  have hphi : ∀ (M : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idem F v) M *ᵥ z = M *ᵥ z := by
    intro M z hz
    have h1 : (1 - GlobalTheory.FinDecomp.idem F v) • z = 0 := by rw [sub_smul, one_smul, hfix z hz, sub_self]
    rw [GlobalTheory.FinDecomp.phi, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add,
      ← Matrix.mulVec_smul, hfix z hz]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · show u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc _ _ K) - 1) = 0
    rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.phi_sub_one, smul_smul, GlobalTheory.FinDecomp.mul_idem_of_evFin hu, zero_smul]
  · rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.mat_loc_inv, hphi _ z hz, hphi _ z hz]
    exact hK z hz


open scoped Classical in
theorem ev_mem_adm' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, GlobalTheory.WeilM.pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem fixes_pure_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    (∀ v ∉ S, ∀ k ∈ GlobalTheory.InertSph.KAt σ X v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP S hAct k hinf hS hlat f φ hSB hφ
  have hM := hP.good
  have hw := hP.weil
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hM.std, S.finite_toSet.eventually_cofinite_notMem] with w hw hwS
    rw [hφ w hwS, hw]
  set Φ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ with hΦ
  have hloc : ∀ v, v ∉ S → ∀ h ∈ GlobalTheory.InertSph.KAt σ X v, om (h, 1) Φ = Φ := by
    intro v hv h hh
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have e1 : Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r := by rw [hΦ, hrt, Function.update_eq_self]
    have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (φ v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hA := hAct v hv h hh
    rw [← hφ v hv] at hA
    rw [e1, hA r hRest]
  have hcut : ∀ v, v ∉ S → loc (idem F v) (idem_mul_self v) k ∈ GlobalTheory.InertSph.KAt σ X v :=
    fun v hv => loc_mem_KAt' σ X v k (hlat v hv)
  have hcutS : ∀ v ∈ S, loc (idem F v) (idem_mul_self v) k = 1 := by
    intro v hv
    apply ua_ext
    rw [mat_loc, mat_one, ← sub_eq_zero, phi_sub_one]
    exact hS v hv _ fun u hu => by rw [smul_eq_mul, mul_idem_of_evFin hu]
  have hone : ∀ v, om (loc (idem F v) (idem_mul_self v) k, 1) Φ = Φ := by
    intro v
    by_cases hv : v ∈ S
    · rw [hcutS v hv]; show om 1 Φ = Φ; rw [map_one]; rfl
    · exact hloc v hv _ (hcut v hv)
  have hlist : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
      om ((l.map fun v => loc (idem F v) (idem_mul_self v) k).prod, 1) Φ = Φ := by
    intro l
    induction l with
    | nil => show om 1 Φ = Φ; rw [map_one]; rfl
    | cons v t ih =>
      rw [List.map_cons, List.prod_cons]
      have : (loc (idem F v) (idem_mul_self v) k * (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod,
          (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) =
          (loc (idem F v) (idem_mul_self v) k, 1) * ((t.map fun v => loc (idem F v) (idem_mul_self v) k).prod, 1) := by
        simp
      rw [this, map_mul, Module.End.mul_apply, ih, hone]
  have hT : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ = Φ := by
    intro T
    have e : loc (idemS F T) (idemS_mul_self T) k = (T.toList.map fun v => loc (idem F v) (idem_mul_self v) k).prod := by
      apply ua_ext
      rw [mat_prod_loc k _ T.nodup_toList, Finset.toList_toFinset, mat_loc]
    rw [e]; exact hlist _
  have hcont := hw.2.2
  have hΦA : Φ ∈ (GlobalTheory.WeilM.adeleClass F).sp (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  funext x
  have hc := hcont _ (ev_mem_adm' x) Φ hΦA
  have ht : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (loc (idemS F T) (idemS_mul_self T) k, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J))) Filter.atTop (nhds (k, 1)) :=
    (GlobalTheory.T.tendsto_unitaryGroupIdempotentLocalization_finiteSets F E σ n X.J k hinf).prodMk_nhds tendsto_const_nhds
  have hlim : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ))
      Filter.atTop (nhds ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (k, 1) Φ))) :=
    (hc.tendsto _).comp ht
  have hconst : (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ)) =
      fun _ => Φ x := by
    funext T; rw [hT T]; rfl
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end GlobalTheory.SphGlobX
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_admissible_unipotent_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt | exact GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt | (intros; apply GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.FockCompactX

open GlobalTheory.RealLift GlobalTheory.FockCompactW

section Der

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_left {m p q : Type} [Fintype p] {z : Matrix p q (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hz : At (evI F) z)
    (A : Matrix m p (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : At (evI F) (A * z) := by
  intro u hu; rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem sd_intertwine_left {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ Y.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (h, 1)) f g) (hf₁ : Acts (evI F) (om (h, 1)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (mat h * u)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (h, 1) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (h, 1) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((h, 1) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat h * u) := by
    change mat h * (realAd F t • u) * (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

end Der

theorem pol_stable_compact_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ,
          ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hw τ _ _ k hk f hf f₁ hf₁
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hw (k, 1) hk.1 h1
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (FockCompactW.heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (mat k * u)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (FockCompactW.heisLine_zero M ψ _)
      (sd_intertwine_left hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : mat k * mat k⁻¹ = 1 := by
    change mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), mat k * (mat k⁻¹ * u) = u := fun u => by
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hle : M.Pol ψ τ ≤ (M.Pol ψ τ).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_left hu (mat k⁻¹)
      have hv' := at_mul_left hu' (mat k⁻¹)
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          calc _ = (mat k⁻¹).map (piInf (τ w)) * X.θ w *
                ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (τ w)) * (X.θ w * (mat k).map (piInf (τ w))) *
                (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.mul_smul]
        congr 1
        simp only [← Matrix.mul_assoc]
        rw [hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_left hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.FockCompactX

end
end
