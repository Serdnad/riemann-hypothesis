module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle270
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNeg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle208
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaSumGLComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle315
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle091
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle279
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle235
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle243
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c) (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e → (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  first | exact @GlobalTheory.ChainOnto.partPar | exact GlobalTheory.ChainOnto.partPar | (intros; apply GlobalTheory.ChainOnto.partPar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStage_realData_conj_value_mem_cuspForms : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, s.Is c j → ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  first | exact @GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame | exact GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame | (intros; apply GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb


theorem contr_comb_main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S f₁ → IsThetaFunO ψ S B'.V₀ f₂ → IsBiTheta ψ B.A S B'.A (contr l S vL f₁ f₂) ∧ (∀ (c : WO B.A S →₀ ℂ) (c' : WO S B'.A →₀ ℂ), contr l S vL (comb ψ B.V₀ S (extS B.o S c) f₁) (comb ψ S B'.V₀ (extT B'.o S c') f₂) = biComb ψ B.A S B'.A c c' (contr l S vL f₁ f₂)) ∧ ∀ (P : Pl D → Prop) (LA : Lat B.A) (LS : Lat S) (LA' : Lat B'.A) (M : Lat B.V₀) (M' : Lat B'.V₀), IsSelfDualC B.A LA → IsSelfDualC S LS → IsSelfDualC B'.A LA' → IsSelfDualC B.V₀ M → IsSelfDualC B'.V₀ M' → (∀ v, P v → (∃ LL, OrthAt B.o M LA LL v) ∧ ∃ LL, OrthAt B'.o M' LA' LL v) → Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → BiVacAt ψ LA LS LA' P (contr l S vL f₁ f₂) := by
  intro D ψ _ ρ σ B B' l S vL f₁ f₂ h₁ h₂
  obtain ⟨hc, hp⟩ := GlobalTheory.T.theta_contraction_integrand_continuous_periodic D ρ σ B B' l S ψ f₁ f₂ h₁ h₂
  have pc := GlobalTheory.Unf.ParCont.parCont D B'.L.rank S.rank vL (WO B.A S × WO S B'.A)
    (fun w p => f₂ ((B'.o.resT S).symm (p.2, w)) * f₁ ((B.o.resS S).symm (p.1, l.κ S w))) hc
    (fun γ hγ w p => hp γ hγ w p.1 p.2)
  have hint : ∀ (u : WO B.A S) (v : WO S B'.A), IntegrableOn
      (fun w => f₂ ((B'.o.resT S).symm (v, w)) * f₁ ((B.o.resS S).symm (u, l.κ S w))) vL.𝓕 vL.μ :=
    fun u v => pc.1 (u, v)
  have hcont : Continuous fun p : WO B.A S × WO S B'.A => contr l S vL f₁ f₂ p.1 p.2 := pc.2.1
  obtain ⟨hqL, hqR⟩ := GlobalTheory.T.theta_contraction_quasi_periodic_rational D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  have hsm := GlobalTheory.T.theta_contraction_isBiSmooth D ρ σ B B' l S vL ψ f₁ f₂ h₁ h₂
  have hBi : IsBiTheta ψ B.A S B'.A (contr l S vL f₁ f₂) := {
    cont := hcont
    smooth := hsm
    quasiL := hqL
    quasiR := hqR
    levL := by
      obtain ⟨U, hU, hUf⟩ := h₁.level
      refine ⟨U.comap (extL (S := S) B.o), hU.preimage (continuous_extL B.o), fun a ha hai v => ?_⟩
      funext u
      rw [heis_left, ← extL_apply, hUf _ ha (extL_inf B.o a hai)]
    levR := by
      obtain ⟨U, hU, hUf⟩ := h₂.level
      refine ⟨U.comap (extR (S := S) B'.o), hU.preimage (continuous_extR B'.o), fun a ha hai u => ?_⟩
      funext v
      rw [heis_right, ← extR_apply, hUf _ ha (extR_inf B'.o a hai)] }
  refine ⟨hBi, GlobalTheory.T.theta_contraction_extendByZero_double_combination D ρ σ B B' l S vL ψ f₁ f₂ hint, ?_⟩
  intro P LA LS LA' M M' hLA hLS hLA' hM hM' hor hv₁ hv₂
  have hor1 : ∀ v, P v → ∃ LL, OrthAt B.o M LA LL v := fun v hv => (hor v hv).1
  have hor2 : ∀ v, P v → ∃ LL, OrthAt B'.o M' LA' LL v := fun v hv => (hor v hv).2
  have memL : ∀ a ∈ latO B.A S (LA : Set _) (LS : Set _) P, extL (S := S) B.o a ∈ latO B.V₀ S (M : Set _) (LS : Set _) P :=
    fun a ha => GlobalTheory.T.extendByZero_left_mem_core_lattice D B.V₀ B.A B.L S B.o P LA LS M hLA hLS hM hor1 a ha
  have memR : ∀ b ∈ latO S B'.A (LS : Set _) (LA' : Set _) P, extR (S := S) B'.o b ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P :=
    fun b hb => GlobalTheory.T.extendByZero_right_mem_core_lattice D B'.V₀ B'.A B'.L S B'.o P LA' LS M' hLA' hLS hM' hor2 b hb
  refine ⟨fun v => ⟨?_, ?_, ?_⟩, fun u => ⟨?_, ?_, ?_⟩⟩
  · exact {
      quasi := fun γ u => hqL γ u v
      level := by
        obtain ⟨U, hU, h⟩ := hBi.levL
        exact ⟨U, hU, fun a ha hai => h a ha hai v⟩
      cont := by
        have hh : Continuous fun u : WO B.A S => ((u, v) : WO B.A S × WO S B'.A) := continuous_id.prodMk continuous_const
        exact hcont.comp hh
      smooth := fun k L hL hLf w => by
        have := hsm k L 0 hL continuous_zero hLf (fun _ => by simp) w v
        simpa using this }
  · intro a ha
    funext u
    rw [heis_left, ← extL_apply, map_nsmul, hv₁.2.1 _ (memL a ha)]
  · intro e he a ha hh
    funext u
    rw [heis_left, ← extL_apply, hv₁.2.2 e he _ (memL a ha) (extL_half B.o e a hh)]
  · exact {
      quasi := fun γ v => hqR γ u v
      level := by
        obtain ⟨U, hU, h⟩ := hBi.levR
        exact ⟨U, hU, fun a ha hai => h a ha hai u⟩
      cont := by
        have hh : Continuous fun v : WO S B'.A => ((u, v) : WO B.A S × WO S B'.A) := continuous_const.prodMk continuous_id
        exact hcont.comp hh
      smooth := fun k L hL hLf w => by
        have := hsm k 0 L continuous_zero hL (fun _ => by simp) hLf u w
        simpa using this }
  · intro b hb
    funext v
    rw [heis_right, ← extR_apply, map_nsmul, hv₂.2.1 _ (memR b hb)]
  · intro e he b hb hh
    funext v
    rw [heis_right, ← extR_apply, hv₂.2.2 e he _ (memR b hb) (extR_half B'.o e b hh)]

end GlobalTheory.ContrComb
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem delta_isKFinVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ omh : WRep (dblSp A) B, IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → IsKFinVec omh (Khat A a) (delta A B Φ₁ Φ₂) := by
  intro D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ h₁ h₂
  obtain ⟨-, -, -, hθ, -, -, hcA, hcB, -⟩ := hP.setting
  have hc := GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact D θ A sA a hθ hcA hP.maj_eq
  have hb := GlobalTheory.T.doublingSeesawTensorMap_polynomial_fock_vector D ψ θ A B sA sB hP.weil.std hθ Φ₁ Φ₂ h₁ h₂
  exact GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh _ sB homh hθ hc.1 hcB (Khat A a) (isCompact_Khat A a) hc.2 _ hb

end GlobalTheory.Core.Rk.IP
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.exists_conjugate_weilDatum_hermitianSpaceNeg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B), IsWeilDatumO ψ A B χA χB om → (∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → IsThetaFunO ψ (negSp A) B fun x => conj (f (-x))) ∧ ∃ om' : WRep (negSp A) B, IsWeilDatumO ψ (negSp A) B χA⁻¹ χB om' ∧ ∀ (g : GA D (negSp A)) (h : GA D B) (f : WO A B → ℂ), IsThetaFunO ψ A B f → om' (g, h) (fun x => conj (f (-x))) = fun x => (((χB (detA A (negEquiv A g)))⁻¹ : Circle) : ℂ) * conj (om (negEquiv A g, h) f (-x)) := by
  first | exact @GlobalTheory.NegWeil.exists_neg_datum | exact GlobalTheory.NegWeil.exists_neg_datum | (intros; apply GlobalTheory.NegWeil.exists_neg_datum <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Formalism.UG (IsUnifV qV)
open GlobalTheory.LFun (KGL IsSatVecGL eulerFac UnrAt LvTw)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt toCompl locMat IsFrameAt IsSatVecU eulerFac LvTw dv Fam)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.Doubling (ioH_mem_KFin)

namespace GlobalTheory.Core.Rk.IP



theorem localZetaOn_split : GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hP D A L hL χ b hχ hb v hv hU μ hμH hK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  have hJ : IsHermND D.sp.cm.sig A.gram := GlobalTheory.Doubling.isHermND_gram A
  haveI : Submodule.IsFullLattice D.host.E L :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  have hd : IsSelfDualAt D.sp.cm.sig A.gram L v :=
    (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2
      inferInstance).2
      (fun y => hL.2 y) v
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨⟨C, hC⟩, V, _, _, ρ, x, ℓ, hpar, -, hcx⟩ := hc
  obtain ⟨w', hne, hall, hN, hN', -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hcm h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  obtain ⟨e, he, hsat⟩ : ∃ e, IsSplitChart D.sp.cm.sig A.gram L h e ∧
      IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x (par w) := by
    rcases hpar w h with ⟨-, e, he, hsat⟩ | ⟨hw, -⟩
    · exact ⟨e, he, hsat⟩
    · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)
  have hB' : par w' = (par w).map (·⁻¹) :=
    GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd hne (hpar w h) (hpar w' h')
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val h2 ((GlobalTheory.LFun.resEta_iff χ _).1 hb) hne h h' (hU w h) (hU w' h')
  have hfix : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ρ k x = x :=
    GlobalTheory.LGrp.mem_fixed.1 (hpar w h).mem_fixed
  have hz1 : ‖(((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one]
  have hker := GlobalTheory.T.sphericalSection_graph_splitPlace D A L hL χ b hb v hv hU s φ hφ w h e he
  have hbd : ℓ x ≠ 0 → ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) ∧
      ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) := by
    intro h0 β hβ
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, Module.End.one_apply]; exact h0
    have Hb := GlobalTheory.T.sphericalParameterBound_split_place D A L hL v hv par c hc' hc1
    refine ⟨(Hb w h).2 β hβ, ?_⟩
    have H2 := (Hb w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
    have e2 : ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) = (qV D.host.E w : ℝ) := by
      rw [hN', ← hN]; rfl
    rwa [e2] at H2
  have hsum := GlobalTheory.ZetaGL.zeta_sum_GL_complex hP D.host.E w A.rank s (by have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _; linarith)
    (GlobalTheory.LFun.val χ w)⁻¹ (fun g => φ (ioAt A v (e.symm g))) hz1 hker V (ρ.comp e.symm.toMonoidHom) x (par w) hsat ℓ
    ⟨C, fun g => by have := hC (e.symm g); rwa [hcx] at this⟩ hbd
  have hval := GlobalTheory.LocValSplit.LvTw_div_dv_split D.host.F D.host.E par (GlobalTheory.LFun.val χ) v w w' A.rank b s hv
    (GlobalTheory.LFun.isUnram_of_isSplit h2 hv) hne hall hN hN' hB' hm
  have hinv : ∀ y, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v,
      φ (ioAt A v (y * k)) * c (y * k) = φ (ioAt A v y) * c y := by
    intro y k hk
    have e1 : ioAt A v (y * k) = ioAt A v y * ioAt A v k := by
      unfold ioAt
      rw [← map_mul]
      simp
    have hk' : ioAt A v k ∈ KFin D.sp.cm.sig (dblSp A).gram L v :=
      (ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩
    rw [e1, hφ.2.1 _ hk', hcx, hcx, map_mul, Module.End.mul_apply, hfix k hk]
  have hsum' := GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e (stabLoc D.sp.cm.sig A.gram L v) (KGL w (n := A.rank)) he.2
    (fun y => φ (ioAt A v y) * c y) hinv _ (by
      refine hsum.congr_fun ?_
      intro a
      simp [hcx])
  obtain ⟨hI, hE⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v)
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) hK (fun y => φ (ioAt A v y) * c y) _ hinv hsum'
  refine ⟨hI, ?_⟩
  rw [hE, hval, hcx, map_one, Module.End.one_apply]

end GlobalTheory.Core.Rk.IP
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_ip : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ), r ≤ a → r ≤ b → ∀ (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure → GlobalTheory.SplitWeil.ip ν (phiQ (a := a) (b := b) v r mu) (phiQ (a := a) (b := b) v r mu) = (((GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {y | ∀ i j, Valued.v (y i j) ≤ 1}).toReal * (zinv PP 0 r * ((Ideal.absNorm PP.asIdeal : ℝ) ^ (r * (b - r)))⁻¹) : ℝ) : ℂ) ∧ phiQ (a := a) (b := b) v r mu ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin b) (Fin a) (Fv D.host.F v)) := by
  intro D PP v φ hP a b r hra hrb ξ mu hL ν hν
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  refine ⟨?_, GlobalTheory.T.twistPlaceChainStepDatum_mem_schwartzBruhat D PP v φ hP a b r ξ mu hL⟩
  have h1 := GlobalTheory.T.twistPlaceChainStepDatum_mul_conj_eq_indicator D PP v φ hP a b r ξ mu hL
  have h3 := GlobalTheory.T.measurableSet_twistPlaceChainStepDatumMatrixSupport D v a b r
  obtain ⟨e1, e2⟩ := GlobalTheory.T.twistPlaceChainStepDatumSupport_eq_valuative D v a b r
  have h4 := GlobalTheory.T.matrixMeasure_topBlock_integralGL_maxIdeal (Fv D.host.F v) ν hν a b r hra hrb
  rw [← e1, ← e2, (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hP).2] at h4
  unfold GlobalTheory.SplitWeil.ip
  simp_rw [h1]
  rw [integral_indicator_const (μ := GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a)) (1 : ℂ) h3,
    Measure.real, h4, zinv]
  simp

end GlobalTheory.NrmVol
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem lFull_holds : ∀ D : D7, LFull D := by
  intro D c hc B hB k hk
  set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
  have hrt : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast hrt
  have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.Icc 1 k → Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
    intro i
    by_cases hi : i ∈ Finset.Icc 1 k
    · have h1 := (Finset.mem_Icc.1 hi).1
      have h2 := (Finset.mem_Icc.1 hi).2
      obtain ⟨Λ, h⟩ := GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero D c hc i (k + 1) h1 (by omega) (by omega)
      exact ⟨Λ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Λ hΛ using hΛ
  set A := GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ with hA
  have hAb : GlobalTheory.LFun.Bounded T A D.R.r ((D.R.r : ℝ) / 2) :=
    hB.twist fun w _ => by simp [GlobalTheory.LFun.norm_val]
  let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)
  have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
    (GlobalTheory.ChainOnto.bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
  let G : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
    ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l)
  have hEq : ∀ x : ℂ, ((D.R.r : ℝ) + D.R.t + 2) < x.re →
      G x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.chT (k + 1)) (x + 1 / 2) := by
    intro x hx
    have hre : ∀ l : ℕ, l < D.R.t → 1 < (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l).re := by
      intro l hl
      have : (l : ℝ) + 1 ≤ D.R.t := by exact_mod_cast hl
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      simp
      linarith
    show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
      (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹) (x + 1 / 2)
    rw [GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char D c B k, ← hA, GlobalTheory.ChainOnto.eulerProd_add_segFam T A (Finset.Icc 1 k) z D.R.t (x + 1 / 2)
      (hAb.converges (by have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _; simp; linarith))
      (fun i _ l hl => hzc i _ (hre l hl))]
    refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun l hl => ?_)
    exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
  have hU : IsOpen (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
  have hD : DifferentiableOn ℂ G (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := by
    refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
    · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
      simp only [GlobalTheory.Cont.mem_rightOf] at hx
      simp
      linarith
    · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
        (hΛ i hi).1.comp (by fun_prop)
  have hAn := hD.analyticOnNhd hU
  have hmem : ((D.R.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2) := by
    simp only [GlobalTheory.Cont.mem_rightOf]
    simp
    linarith
  have hA0 : GlobalTheory.LFun.Converges T A ((1 + (D.R.t : ℂ)) / 2) := by
    refine hAb.converges ?_
    simp
    linarith
  have hLS : GlobalTheory.LFun.LSD D c.S B (c.μ (k + 1)) ((1 + (D.R.t : ℂ)) / 2) = GlobalTheory.LFun.eulerProd T A ((1 + (D.R.t : ℂ)) / 2) := rfl
  have hreidx : ∀ i, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l) =
      ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n := by
    intro i
    refine Finset.prod_nbij' (fun l => D.R.t - l) (fun n => D.R.t - n) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl ⊢
      omega
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn ⊢
      omega
    · intro l hl
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hl
      omega
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc, Finset.mem_coe] at hn
      omega
    · intro l hl
      have hl' := Finset.mem_range.1 hl
      congr 1
      rw [Nat.cast_sub hl'.le]
      ring
  refine ⟨∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 D.R.t, Λ i n, ?_,
    ⟨Λ, fun i hi => ⟨(hΛ i hi).1, (hΛ i hi).2.1⟩, rfl⟩, hA0, ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun n hn => ?_
    have hn' := Finset.mem_Icc.1 hn
    exact (hΛ i hi).2.2 n hn'.1 hn'.2
  · rw [hLS]
    exact hA0.ne_zero
  · refine ⟨G, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
      (D.R.r : ℝ) + D.R.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, ?_⟩
    show GlobalTheory.LFun.eulerProd T A ((D.R.t : ℂ) / 2 + 1 / 2) *
      ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i ((D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l) = _
    rw [hLS, Finset.prod_congr rfl fun i _ => hreidx i]
    congr 2
    ring

end GlobalTheory.ChainTw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.chainThetaLiftsAdjoint_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdjQ D := by
  first | exact @GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay | exact GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay | (intros; apply GlobalTheory.ChainTw.upAdjQ_of_cuspRapidDecay <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels : ∀ D : D7, ForStageQ D fun c w _ s => MeasurableSet (levSet s) ∧ MeasurableSet (intOff c s) ∧ (∀ g, g ∈ levSet s ↔ g ∈ intOff c s ∧ ∀ v ∈ c.S, gAt s.V (.inl v) g ∈ Lev.levG s.V s.β s.L) ∧ (∀ g ∈ levSet s, ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ (∀ κ ∈ Lev.levG s.V s.β s.L, ‖Lev.levChi s.V s.β s.L κ‖ = 1 ∧ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ ∃ mR, IsLevMeas s mR := by
  first | exact @GlobalTheory.ChainTw.LevLoc.levLoc | exact GlobalTheory.ChainTw.LevLoc.levLoc | (intros; apply GlobalTheory.ChainTw.LevLoc.levLoc <;> assumption)
end
