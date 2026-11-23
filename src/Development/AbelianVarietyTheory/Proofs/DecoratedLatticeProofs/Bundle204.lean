module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle177
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle182
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle183
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle193
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle180
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (u : GA D A → ℂ), GlobalTheory.Grow.RapidDec A u → ∀ N : ℕ, Integrable (fun q : AutQ A => GlobalTheory.Grow.quotHeight A q.out ^ N * ‖u q.out‖) (autMeasure A m) := by
  first | exact @GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec | exact GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec | (intros; apply GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec <;> assumption)
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


theorem _root_.GlobalTheory.T.mem_localLattice_iff_of_finiteAdelic_completion_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)), L.FG → L'.FG → ∀ b : GL (Fin n) (TensorProduct F (Af F) E),
    (∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E))) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E), z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by
  first | exact @GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat | exact GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat | (intros; apply GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat <;> assumption)
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


theorem _root_.GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ u ∈ A0 θ A cA, (fun g => conj (u g)) ∈ A0 θ A cA := by
  first | exact @GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 | exact GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 | (intros; apply GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 <;> assumption)
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


theorem _root_.GlobalTheory.T.rTr_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ k ∈ GfC A, ∀ u ∈ A0 θ A cA, rTr A k u ∈ A0 θ A cA := by
  first | exact @GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite | exact GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite | (intros; apply GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResUnr

open Formalism.L2.Host

theorem exists_int_div {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (k : E)
    (hk : P.valuation E k = 1) :
    ∃ a s : 𝓞 E, a ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ k * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
  obtain ⟨n, d, h | h⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := E) k
  · refine ⟨n, d, ?_, d.2, h⟩
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E), ← h, map_mul, hk, one_mul,
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact d.2
  · refine ⟨d, n, d.2, ?_, h⟩
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, hk, one_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) (r := (d : 𝓞 E)) P).2 d.2] at h2
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).1 h2

theorem loc_eq_of_isRes {D : D7} {H₁ H₂ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {ξ : (kP PP)ˣ →* ℂˣ}
    (h₁ : IsRes H₁ PP ξ) (h₂ : IsRes H₂ PP ξ) (x : (PP.adicCompletion D.host.E)ˣ) (hx : IsUnitAt PP x) :
    H₁.loc PP x = H₂.loc PP x := by
  have hc : IsClopen {x : (PP.adicCompletion D.host.E)ˣ | IsUnitAt PP x} := by
    have := (Valued.isClopen_sphere (PP.adicCompletion D.host.E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := PP.adicCompletion D.host.E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  have hK : ∀ k : D.host.Eˣ, PP.valuation D.host.E (k : D.host.E) = 1 → H₁.locK PP k = H₂.locK PP k := by
    intro k hk
    obtain ⟨a, s, ha, hs, hks⟩ := exists_int_div PP (k : D.host.E) hk
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    have hne : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := fun b hb h0 =>
      hb (by rw [(IsFractionRing.injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)]; exact PP.asIdeal.zero_mem)
    have hq : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun b hb h0 =>
      hb (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let A : D.host.Eˣ := Units.mk0 _ (hne a ha)
    let S : D.host.Eˣ := Units.mk0 _ (hne s hs)
    let ua : (kP PP)ˣ := Units.mk0 _ (hq a ha)
    let us : (kP PP)ˣ := Units.mk0 _ (hq s hs)
    have hkS : k * S = A := Units.ext hks
    have e1 : H₁.locK PP A = H₂.locK PP A := ((h₁ a A ua rfl rfl).symm.trans (h₂ a A ua rfl rfl))
    have e2 : H₁.locK PP S = H₂.locK PP S := ((h₁ s S us rfl rfl).symm.trans (h₂ s S us rfl rfl))
    rw [← hkS, map_mul, map_mul, e2] at e1
    exact mul_right_cancel e1
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin PP).induction_on
    (p := fun x => IsUnitAt PP x → H₁.loc PP x = H₂.loc PP x) x ?_
    (fun k hk => hK k ((PP.valuedAdicCompletion_eq_valuation' _).symm.trans hk)) hx
  exact isClosed_imp hc.2 (isClosed_eq (H₁.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP))
    (H₂.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP)))

theorem unrAt_div_of_isRes : ∀ (D : D7) (c₁ c₂ : (AE D)ˣ →* Circle) (H₁ H₂ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), ChrEq c₁ H₁ → ChrEq c₂ H₂ → IsRes H₁ PP ξ → IsRes H₂ PP ξ → GlobalTheory.LFun.UnrAt (F := D.host.F) (c₁ * c₂⁻¹) PP := by
  intro D c₁ c₂ H₁ H₂ PP ξ hc₁ hc₂ h₁ h₂ x hx
  have e : GlobalTheory.LFun.locChar (c₁ * c₂⁻¹) PP x = GlobalTheory.LFun.locChar c₁ PP x * (GlobalTheory.LFun.locChar c₂ PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq hc₁, GlobalTheory.LFun.locChar_eq_of_chrEq hc₂, loc_eq_of_isRes h₁ h₂ x hx, mul_inv_cancel]

end GlobalTheory.ResUnr
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


theorem _root_.GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c := by
  first | exact @GlobalTheory.Cont.HeightIo.height_io_bound | exact GlobalTheory.Cont.HeightIo.height_io_bound | (intros; apply GlobalTheory.Cont.HeightIo.height_io_bound <;> assumption)
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


theorem _root_.GlobalTheory.T.doubledCompactSubgroup_conj_hermitianSpace : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  first | exact @GlobalTheory.LatMove.mem_KAd_io_conj | exact GlobalTheory.LatMove.mem_KAd_io_conj | (intros; apply GlobalTheory.LatMove.mem_KAd_io_conj <;> assumption)
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


theorem _root_.GlobalTheory.T.iwasawa_doubled_hermitian_space_real_place : ∀ (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ w : InfinitePlace D.host.F, HasIwasawa D.sp.cm.sig (dblSp A).gram (KArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a)) := by
  first | exact @GlobalTheory.Core.Rk.IwArch.hasIwasawa_dblSp_arch | exact GlobalTheory.Core.Rk.IwArch.hasIwasawa_dblSp_arch | (intros; apply GlobalTheory.Core.Rk.IwArch.hasIwasawa_dblSp_arch <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

theorem _root_.GlobalTheory.T.mem_hyperspecialSubgroupAtPlace_iff_local_stabilizer : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ (V : HSp D) (g : GA D V), g ∈ hyp V w ↔ ∃ k ∈ Kv V v, g = embV V v k := by
  first | exact @GlobalTheory.HypDict.mem_hyp_iff_embV | exact GlobalTheory.HypDict.mem_hyp_iff_embV | (intros; apply GlobalTheory.HypDict.mem_hyp_iff_embV <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHecke.StringEig

open GlobalTheory.ChainOnto (esymm_add_C esymm_map_mul_C esymm_string esymm_eq_zero_of_lt sqrt_sq_C natCast_cpow_half)

theorem map_coe_segL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (z : ℂˣ) (t : ℕ) :
    (segL ϖ z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [segL, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  congr 1
  rw [GlobalTheory.MellinPoly.absPow_eq_zpow, ord_eq_one hϖ, zpow_one, ← natCast_cpow_half]
  congr 1
  push_cast
  ring

theorem genVal_add_segL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r N t n₀ : ℕ) (B : Multiset ℂˣ) (zS zT : ℂˣ), B.card = N → n₀ ≤ N + t → genVal (resCard k) r (N + t) (B.map (· * (zS * zT⁻¹)) + segL ϖ zS t) n₀ = (zS : ℂ) ^ n₀ * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n₀ * (r + N)) * ∑ n ∈ Finset.range (N + 1), (if n ≤ n₀ then ((resCard k ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin (resCard k) t (n₀ - n) : ℕ) : ℂ) else 0) * (((zT : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (r + N + t)))⁻¹ * genVal (resCard k) r N B n) := by
  intro k _ _ _ _ ϖ hϖ r N t n₀ B zS zT hB hn₀
  set Q := resCard k with hQdef
  have hsQ := sqrt_sq_C Q
  have hs : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < Q := one_lt_resCard k
    have : ((Q : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : Q ≠ 0) (by exact_mod_cast this)
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  have hA : (B.map (· * (zS * zT⁻¹))).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((zS : ℂ) * (zT : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def, mul_comm]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = N := by simp [hB]
  set F : ℕ → ℂ := fun n => (if n ≤ n₀ then ((Q ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin Q t (n₀ - n) : ℕ) : ℂ) else 0) *
    (((zT : ℂ) ^ n * s ^ (n * (r + N + t)))⁻¹ * genVal Q r N B n) with hF
  have hFa : ∀ j, N < j → F j = 0 := by
    intro j hj
    simp only [hF, genVal, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, n₀ < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ n₀ by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (N + 1), F j = ∑ j ∈ Finset.range (n₀ + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show N + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show n₀ + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, genVal, Multiset.map_add (f := _), esymm_add_C, Finset.mul_sum, Finset.mul_sum, hA, map_coe_segL k ϖ hϖ]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ n₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s zS hs hsQ t]
  simp only [hF, if_pos hjk, genVal]
  by_cases hjN : j ≤ N
  · by_cases hat : n₀ - j ≤ t
    · have hsI : s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ)))) =
          s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j)) := by
        rw [← pow_mul]
        simp only [← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hs]
        congr 1
        push_cast [Nat.cast_sub hjN, Nat.cast_sub hjk, Nat.cast_sub hat, Nat.cast_sub hn₀]
        ring
      have hz : ((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j) = (zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹ := by
        rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk, inv_pow]
      calc _ = (s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ))))) *
            (((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j)) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
        _ = (s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j))) *
            ((zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
        _ = _ := by rw [hsQ]; push_cast; rw [mul_inv]; ring
    · rw [Formalism.L2.Col.gaussBin_eq_zero Q (show t < n₀ - j by omega)]
      simp
  · rw [esymm_eq_zero_of_lt _ (by omega)]
    simp

end GlobalTheory.ParHecke.StringEig

end
end

section


theorem _root_.GlobalTheory.T.pairsAmplitudeBound_of_typeBound : GlobalTheory.Core.Deg.PairsDegOfType := by
  first | exact @GlobalTheory.Core.Deg.pairsDegOfType_holds | exact GlobalTheory.Core.Deg.pairsDegOfType_holds | (intros; apply GlobalTheory.Core.Deg.pairsDegOfType_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal.LatChar

variable {D : D7}

theorem finPart_pair_zero (α : Af D.host.F) (x : D.host.E) :
    finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = α ⊗ₜ[D.host.F] x := rfl

theorem latV_int {S : HSp D} {L : Lat S} (hL : ∀ z ∈ L, z ∈ intVec D S.rank) {P : Pl D → Prop}
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) (i : Fin S.rank) : finPart D (y i) ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    change finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) ∈ intAE D
    rw [finPart_pair_zero, one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => rw [Pi.zero_apply, RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Pi.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [Pi.neg_apply, RingHom.map_neg]; exact neg_mem hx

theorem lat_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
    {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    β.IsLat L Λ → (∀ z, z ∈ L ↔ z ∈ intVec D _) → ∀ x : n → k, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  intro D k _ _ _ _ p S n _ _ β L Λ hΛ hL x
  rw [hΛ x]
  constructor
  · intro h r
    exact (p.int_iff _).2 (latV_int (fun z hz => (hL z).1 hz) h r)
  · intro h
    have h1 : (fun i => p.sec ((β.b *ᵥ x) i)) =
        ∑ r, fun i => p.sec ((β.b *ᵥ x) r) * incA D ((Pi.single r 1 : Fin S.rank → D.host.E) i) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, RingHom.map_one, mul_one]
      · intro r _ hr
        rw [Pi.single_eq_of_ne hr.symm, RingHom.map_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h1]
    refine sum_mem fun r _ => GlobalTheory.FinPl.FrameLat.int_mul_mem (GlobalTheory.FinPl.FrameLat.sec_mem_intAt p _ (h r)) ((hL _).2 fun i => ?_)
    by_cases hi : i = r
    · subst hi; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hi]; exact isIntegral_zero

end GlobalTheory.PhiOneVal.LatChar
end
