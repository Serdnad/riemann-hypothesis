module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle530
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle489
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle094
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle061
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)
open GlobalTheory.Core.Rk.IP in
theorem GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.RallisBottom.HeckeFormAniso D := by
  intro hP D
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalTheory.BottomRallis.GlobalFormAniso D :=
    _root_.GlobalTheory.T.theta_tower_compatibility hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
      (_root_.UpperTheory.Lit.Sw47.siegelWeil_fock_anisotropic_unconditional D)
  exact GlobalTheory.BottomRallis.heckeFormAniso_of_global_euler D hG hE
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.rallis_bottom_hecke_form_anisotropic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.RallisBottom.HeckeFormAniso D := by
  first | exact @_root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom | exact _root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom | (intros; apply _root_.GlobalTheory.RallisBottom.hecke_form_anisotropic_of_rallis_bottom <;> assumption)
end
end

section

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
noncomputable section
namespace GlobalTheory.BottomRallis
variable {D : D7}
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
theorem rallis_inner_product_bottom_norm_eq (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A B : HSp D}
    {χA χB : (AE D)ˣ →* Circle} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A} {a : GL (Fin A.rank) (AE D)}
    {om : WRep A B} {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hPair : Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕)
    (hA : wittIndex A = 0) (hB : wittIndex B = 0) {LA : Lat A} {LB : Lat B} {Sf : Finset (FinPl D)}
    {Φ : WO A B → ℂ} (hF : IsFockVec ψ θ A B sA sB Φ) (hU : Unram ψ A B χB LA LB Sf Φ Φ)
    (m : Measure (GA D A)) (mH : Measure (GA D B)) [m.IsHaarMeasure] [mH.IsHaarMeasure]
    (hint : ∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧
      IntegrableOn (integrand om m ν 𝓕 LA a Φ Φ (fun _ => 1) (fun _ => 1) s₁) (openOff A LA Sf) m)
    (l : ℕ → ℂ) (hl : ∀ i < A.rank,
      HolValueAt (LFun.charL χB⁻¹ (Sf : Set (FinPl D))) ((t : ℂ) / 2 + (A.rank : ℂ) / 2 - i) (l i)) :
    petersson B mH (up om m Φ (fun _ => 1)) (up om m Φ (fun _ => 1)) =
      volQ B mH * volQ A m * ((∏ i ∈ Finset.range A.rank, l i) /
        LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
        ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ Φ g ∂m := by
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalFormAniso D := _root_.GlobalTheory.T.theta_tower_compatibility hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
    (_root_.UpperTheory.Lit.Sw47.siegelWeil_fock_anisotropic_unconditional D)
  have hH := heckeFormAniso_of_global_euler D hG hE
  have h1 : (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero hPair.setting hA
  have hpar := GlobalTheory.T.constantFunction_has_trivialRep_satakeParameters A LA Sf hU.sdA hU.two
  have hsph : SphFun A LA Sf (fun _ : GA D A => (1 : ℂ)) := fun _ _ _ _ _ => rfl
  obtain ⟨-, -, -, hfin⟩ := hH ψ θ A B χA χB sA sB t cA a om ν 𝓕 hPair hB LA LB Sf Φ Φ hF hF hU m mH
    inferInstance inferInstance _ h1 _ h1 (trivPar A.rank) hpar hsph hint
  have hL : HolValueAt (fun s => LFun.LSD D Sf (trivPar A.rank) χB (s + 1 / 2)) ((t : ℂ) / 2)
      (∏ i ∈ Finset.range A.rank, l i) := by
    refine HolValueAt.congr (holValueAt_prod (Finset.range A.rank) fun i hi => ?_) (GlobalTheory.T.partial_L_trivial_rep_twist_eq_prod_hecke_L χB Sf A.rank hU.unr)
    have h2 := hl i (Finset.mem_range.1 hi)
    rw [show (t : ℂ) / 2 + (A.rank : ℂ) / 2 - i = (t : ℂ) / 2 + ((A.rank : ℂ) / 2 - i) by ring] at h2
    have h3 := h2.comp_add
    simpa only [add_sub_assoc] using h3
  rw [hfin _ hL]
  simp only [rcoef_one]
  rw [integral_mul_const]
  ring
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
end GlobalTheory.BottomRallis
end
end
end
