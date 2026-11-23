module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Rethread
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.ResCore
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle359
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle078
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle526
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle064
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFinitePlaceThetaMatch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle077
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsMatchingFiniteDataBottomLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IntertwineOfCompatibleMaps
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle501

@[expose] public section

section

section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section
namespace GlobalTheory.Core.Rk.Exh.Top
theorem downNe_k_of_hypotheses' : ResidueKilled.DM → GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ D : D7, EulerRight D → DownNe D :=
  fun hDM hSP => downNe_of_core hDM PositivityTheory.Rg.Rsw.resCore hSP
end GlobalTheory.Core.Rk.Exh.Top
end
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.RegCompare
variable {D : D7}
section Lin
variable {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M))
variable {ω ν 𝓕}
variable (ω ν 𝓕)
variable {ω ν 𝓕}
end Lin
theorem regularisedIntegral_of_const : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ c₀ : ℂ, (∀ Φ' ∈ algF ψ θ false A₁ B, ∃ Φ₀ ∈ algF ψ θ false A₁ B,
        Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) ∧ ModInt θ ωB ν₁ 𝓕₁ Φ₀ ∧
        ∀ Φ ∈ algF ψ θ true A B, p Φ = p' Φ₀ → thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ Φ₀) →
    ∀ ΦB ∈ algF ψ θ false A₁ B, ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧ GlobalTheory.FunObj.zdeg z ≠ 0 ∧
      wop ωB z ΦB ∈ algF ψ θ false A₁ B ∧ ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) ∧
      ∀ Φ ∈ algF ψ θ true A B, p Φ = GlobalTheory.FunObj.zdeg z • p' ΦB →
        thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) := by
  intro hP hK D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm c₀ H ΦB hΦB
  set S := algF ψ θ false A₁ B with hSdef
  have hstab : ∀ g ∈ GfC W₁, ∀ Φ ∈ S, ωB (g, 1) Φ ∈ S := hm.mapB.stabM.1
  have hL : ∀ Φ ∈ S, ∀ γ ∈ GQ W₁, ∀ g h, thetaKO ωB (γ * g) h Φ = thetaKO ωB g h Φ :=
    GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D ψ θ hθ W₁ X A₁ B α (α / β) ωB hm.weilB
  obtain ⟨Φ₀, h0S, hrel, hmod0, hI⟩ := H ΦB hΦB
  have hp : p' ΦB = p' Φ₀ := by
    have h1 : finRel ωB S ≤ LinearMap.ker p' := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
      show p' _ = 0
      rw [map_sub, hm.mapB.invf u hu Ψ hΨ, sub_self]
    have := h1 hrel
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  rw [finRel, Submodule.mem_span_set'] at hrel
  obtain ⟨n, c, g, hsum⟩ := hrel
  choose u hu Ψ hΨ hg using fun i => (g i).2
  obtain ⟨z, hzG, hz0, hz⟩ := _root_.GlobalTheory.T.twist_regulariser_isGood hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hm.weilB (n + 1)
    (Fin.cons ΦB Ψ) (Fin.cons 1 u) (Fin.cases hΦB hΨ) (Fin.cases (one_mem _) hu)
  have hB : ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) := (hz 0).1
  have hX : ∀ i, ModInt θ ωB ν₁ 𝓕₁ (wop ωB z (Ψ i)) ∧
      ∃ u' ∈ GfC W₁, wop ωB z (ωB (u i, 1) (Ψ i)) = ωB (u', 1) (wop ωB z (Ψ i)) := fun i => hz i.succ
  choose u' hu' hcomm using fun i => (hX i).2
  have hXS : ∀ i, wop ωB z (Ψ i) ∈ S := fun i => wop_mem hstab hzG (hΨ i)
  have hXr := fun i => modInt_right hν₁ (hL _ (hXS i)) (hX i).1 (u' i)
  have h0 := thetaInt_wop hν₁ (hL _ h0S) hmod0 z
  have eB : ΦB = Φ₀ + ∑ i, c i • (ωB (u i, 1) (Ψ i) - Ψ i) := by
    have e : ∑ i, c i • (g i : WO W₁ X → ℂ) = ∑ i, c i • (ωB (u i, 1) (Ψ i) - Ψ i) := by simp only [hg]
    rw [← e, hsum]; abel
  have eW : wop ωB z ΦB = wop ωB z Φ₀ + ∑ i, c i • (ωB (u' i, 1) (wop ωB z (Ψ i)) - wop ωB z (Ψ i)) := by

    rw [eB, map_add (f := _), map_sum]
    simp only [map_smul, map_sub, hcomm]
  have hJ : thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) = GlobalTheory.FunObj.zdeg z • thetaInt ωB ν₁ 𝓕₁ Φ₀ := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Intg ωB ν₁ 𝓕₁ (c i • (ωB (u' i, 1) (wop ωB z (Ψ i)) - wop ωB z (Ψ i))) := fun i _ =>
      ((intg_of_modInt (hXr i).1).sub (intg_of_modInt (hX i).1)).smul _
    rw [eW, thetaInt_add h0.1 (Intg.sum _ hi), thetaInt_sum _ hi, h0.2]
    simp only [thetaInt_smul, thetaInt_sub (intg_of_modInt (hXr _).1) (intg_of_modInt (hX _).1), (hXr _).2, sub_self,
      smul_zero, Finset.sum_const_zero, add_zero]
  refine ⟨z, hzG, hz0, wop_mem hstab hzG hΦB, hB, fun Φ hΦ hpΦ => ?_⟩
  have hΦ₁ : (GlobalTheory.FunObj.zdeg z)⁻¹ • Φ ∈ algF ψ θ true A B := Submodule.smul_mem _ _ hΦ
  have hp₁ : p ((GlobalTheory.FunObj.zdeg z)⁻¹ • Φ) = p' Φ₀ := by
    rw [map_smul, hpΦ, smul_smul, inv_mul_cancel₀ hz0, one_smul, hp]
  have e1 := hI _ hΦ₁ hp₁
  have e2 : Φ = GlobalTheory.FunObj.zdeg z • ((GlobalTheory.FunObj.zdeg z)⁻¹ • Φ) := by rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]
  rw [e2, thetaInt_smul, e1, hJ, smul_comm]
theorem regularised_integral_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ ΦB ∈ algF ψ θ false A₁ B, ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧
      GlobalTheory.FunObj.zdeg z ≠ 0 ∧ wop ωB z ΦB ∈ algF ψ θ false A₁ B ∧ ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) ∧
      ∀ Φ ∈ algF ψ θ true A B, p Φ = GlobalTheory.FunObj.zdeg z • p' ΦB →
        thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) := by
  intro hP hK hS D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  obtain ⟨c, hc, H⟩ := hS D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  exact ⟨c, hc, _root_.GlobalTheory.RegCompare.regularisedIntegral_of_const hP hK D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm c H⟩
end GlobalTheory.RegCompare
end
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotAlgI'
theorem twistedClassSums_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨Ω, hΩ, H⟩ := _root_.GlobalTheory.T.bottomClassSum_eq_formula hP hI hL hX
  refine ⟨Ω, hΩ, fun t h hh k => ?_⟩
  obtain ⟨n, c, z, hc, hz, he⟩ := H t h hh k
  rw [he, mul_div_cancel_left₀ _ hΩ]
  have hz' : ∀ l, IsAlgebraic ℚ (z l) := fun l => by
    obtain ⟨δ, t0, Q, P, h', U, e⟩ := hz l
    rw [e]; exact _root_.GlobalTheory.T.normSum_coefficients_isAlgebraic hP hI D δ t0 Q P h' U
  have : ∀ l, (c l * z l) ∈ algebraicClosure ℚ ℂ := fun l =>
    mul_mem (mem_algebraicClosure_iff.2 (hc l)) (mem_algebraicClosure_iff.2 (hz' l))
  exact mem_algebraicClosure_iff.1 (sum_mem fun l _ => this l)
end GlobalTheory.BotAlgI'
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.bottom_twistedClassSums_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @_root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic | exact _root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic | (intros; apply _root_.GlobalTheory.BotAlgI'.twistedClassSums_isAlgebraic <;> assumption)
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
open scoped TensorProduct
namespace GlobalTheory.StageFinMatch
end GlobalTheory.StageFinMatch
namespace GlobalTheory.StageFinMatch
theorem theta_bottom_finite_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      ∃ κ : ℂ, κ ≠ 0 ∧ r (X.f t) = κ • r' (X.f' t) := by
  intro hP hK hL
  refine gBig_two' (_root_.GlobalTheory.T.finite_place_theta_matching hP hK hL) (_root_.GlobalTheory.T.theta_stage_unique hP hK hL) fun {D T Lc sc} G μ₀ C x b₀ hA hB => ?_
  intro W i j a b A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, P, P', κ, hne, heq⟩ := hA W i j a b A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j a b A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have m1 : GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW :=
    Submodule.subset_span ⟨_, P, hf, rfl⟩
  have m2 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
    Submodule.subset_span ⟨_, P', hf', rfl⟩
  have k : p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) =
      (c * κ) • p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') := by
    rw [hE _ m1, hE' _ m2, heq, LinearEquiv.map_smul, smul_smul]
  have kne : p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) ≠ 0 := by
    rw [hE _ m1]
    exact smul_ne_zero hc ((LinearEquiv.map_ne_zero_iff E).mpr hne)
  rw [hp _ hf P, hp' _ hf' P', ← LinearEquiv.map_smul, TensorProduct.smul_tmul'] at k
  rw [hp _ hf P] at kne
  have kne' : q P ⊗ₜ[ℂ] r (X.f t) ≠ 0 := fun h0 => kne (by rw [h0, map_zero])
  exact tmul_right_prop (e.injective k) kne'
end GlobalTheory.StageFinMatch
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
open scoped TensorProduct

theorem _root_.GlobalTheory.T.theta_finiteData_match_each_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      ∃ κ : ℂ, κ ≠ 0 ∧ r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match | exact _root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match | (intros; apply _root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match <;> assumption)
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
open MeasureTheory
open scoped TensorProduct
namespace GlobalTheory.StageFinNonzero
theorem theta_stage_finite_part_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      r' (X.f' t) ≠ 0 := by
  intro hP hK hL
  refine gBig_of_two (_root_.GlobalTheory.T.finite_place_theta_matching hP hK hL) (_root_.GlobalTheory.T.theta_stage_unique hP hK hL) fun {D T Lc sc} G μ₀ C x b₀ hA hB => ?_
  intro W i j a b A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, P, P', κ, hne, heq⟩ := hA W i j a b A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j a b A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have m2 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
    Submodule.subset_span ⟨_, P', hf', rfl⟩
  have n0 : p₀' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at heq
    exact hne heq
  have n1 : p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    rw [hE' _ m2]
    exact (LinearEquiv.map_ne_zero_iff E).mpr n0
  intro h0
  rw [hp' _ hf' P', h0, TensorProduct.tmul_zero, map_zero] at n1
  exact n1 rfl
end GlobalTheory.StageFinNonzero
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
open MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      r' (X.f' t) ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero | exact _root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero | (intros; apply _root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.FlipStart
open GlobalTheory.FlipStart in
theorem GlobalTheory.FlipStart.flipSequence_start_condition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro hP hC
  obtain ⟨a, h⟩ := ((_root_.GlobalTheory.T.flipSequence_column_succ hP hC).and (_root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists hP hC)).and (_root_.GlobalTheory.T.twisted_theta_first_occurrence_finite_swapped_pair hP)
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨x, h⟩ := h ε CF hCF
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨hcol, hrow⟩, hfin⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  obtain ⟨q, hq⟩ := exists_chainPols ch
  refine ⟨Finsupp.single (gPol ch.ρ q) 1, fun t => ?_⟩
  obtain ⟨f, hf⟩ := exists_chainVecs ch t
  obtain ⟨z, hz, hrep⟩ := hfin t f hf
  refine ⟨z, hz, fun Φ => ⟨Finsupp.single (givenFin ch.W t f Φ) (z : ℂ), hrep Φ, fun M hM y => ?_⟩⟩
  obtain ⟨hc1, hc2⟩ := hcol t f q hf hq M hM y
  obtain ⟨hr1, hr2⟩ := hrow t Φ M hM y
  rw [tensE_single]
  refine ⟨fun d hd => ?_, ?_⟩
  · have hd' := Finsupp.support_single_subset hd
    rw [Finset.mem_singleton] at hd'
    subst hd'
    rw [zip_given]
    refine (pathConv_comp ch.W M _ _ _ _ _).2 ⟨hc1, ?_⟩
    rw [hc2]
    exact hr1
  · rw [liftT_single, zip_given]
    unfold givenPath
    rw [pathLift_comp, hc2, ← hr2, smul_smul, inv_mul_cancel₀ (Units.ne_zero z), one_smul]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flipSequence_initial_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_condition | exact _root_.GlobalTheory.FlipStart.flipSequence_start_condition | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_condition <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotFinMatch
theorem theta_bottom_finite_match : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  intro hH hP hK hL
  refine gBig_two (_root_.GlobalTheory.T.theta_bottomLevel_matches_finiteData hH hP hK hL) (_root_.GlobalTheory.T.theta_bottomLevel_uniqueness hH hP hK hL) fun {D T Lc sc} G μ₀ C x b hA hB => ?_
  intro W i j A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, hA'⟩ := hA W i j A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have k1 : ∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p₀ (fockF W.ψ W.θ true FA FW f P) = (e.trans E.symm) (q P ⊗ₜ (c⁻¹ • r) f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ true FA FW f P ∈ algF W.ψ W.θ true FA FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE _ hmem
    rw [hp f hf P] at h1
    rw [LinearEquiv.trans_apply, LinearMap.smul_apply, TensorProduct.tmul_smul, LinearEquiv.map_smul, h1,
      LinearEquiv.map_smul, LinearEquiv.map_smul, LinearEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have k2 : ∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p₀' (fockF W.ψ W.θ false FA' FW f P) = (e.trans E.symm) (q' P ⊗ₜ r' f) := by
    intro f hf P
    have hmem : fockF W.ψ W.θ false FA' FW f P ∈ algF W.ψ W.θ false FA' FW := Submodule.subset_span ⟨f, P, hf, rfl⟩
    have h1 := hE' _ hmem
    rw [hp' f hf P] at h1
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
  obtain ⟨κ, hκ⟩ := hA' Pr Pf q q' (c⁻¹ • r) r' (e.trans E.symm) hq hq' k1 k2
  refine ⟨c * κ, ?_⟩
  rw [LinearMap.smul_apply] at hκ
  rw [mul_smul, ← hκ, smul_smul, mul_inv_cancel₀ hc, one_smul]
end GlobalTheory.BotFinMatch
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_bottom_finite_place_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' → ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi), Function.Surjective q → Function.Surjective q' → (∀ f, IsFinF W.ψ W.θ true FA FW f → ∀ P, p (fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) → (∀ f, IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) → ∃ κ : ℂ, r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match | exact _root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match | (intros; apply _root_.GlobalTheory.BotFinMatch.theta_bottom_finite_match <;> assumption)
end
end
