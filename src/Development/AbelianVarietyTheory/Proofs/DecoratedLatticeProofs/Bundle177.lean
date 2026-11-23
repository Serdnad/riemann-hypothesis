module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle008
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle173
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle349
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

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

namespace GlobalTheory.Core.Rk.IP

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


theorem _root_.GlobalTheory.T.flatFamilyZeta_convergence_holomorphy : GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.FlatZetaHolomorphic := by
  first | exact @GlobalTheory.FlatFamily.flatZetaHolomorphic | exact GlobalTheory.FlatFamily.flatZetaHolomorphic | (intros; apply GlobalTheory.FlatFamily.flatZetaHolomorphic <;> assumption)
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

noncomputable section

namespace GlobalTheory.ChainOnto.InertValue

theorem npow_eq_zpow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (N : ℕ)
    (hN : Ideal.absNorm w.asIdeal = N ^ 2) (k : ℤ) (z : ℂ) (hz : 2 * z = k) :
    GlobalTheory.LFun.npow w z = (N : ℂ) ^ k := by
  have hlog : (Complex.log (N : ℂ) * ((2 : ℕ) : ℂ)).im = 0 := by
    rw [Complex.mul_im, Complex.log_im, Complex.log_re, ← Complex.ofReal_natCast N,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
    simp
  rw [GlobalTheory.LFun.npow, hN, Nat.cast_pow, ← Complex.cpow_natCast (N : ℂ) 2,
    ← Complex.cpow_mul (x := (N : ℂ)) (y := ((2 : ℕ) : ℂ)) (z := z) (by rw [hlog]; linarith [Real.pi_pos]) (by rw [hlog]; linarith [Real.pi_pos])]
  rw [show ((2 : ℕ) : ℂ) * z = (k : ℂ) by rw [← hz]; norm_num, Complex.cpow_intCast]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

end GlobalTheory.ChainOnto.InertValue


open GlobalTheory.ChainOnto.InertValue in
theorem GlobalTheory.ChainOnto.val_seg_of_isInertAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χ w → val (F := D.host.F) χ w = (-1) ^ n ∧ ∀ (qu z : ℂˣ) (t : ℕ), (qu : ℂ) = qV D.host.F v → seg w z t = (GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu t).map (z * ·) := by
  intro D χ n _ hres v w hwv hw hu
  refine ⟨GlobalTheory.LFun.ResEta.val_of_isInertAt D.sp.cm.deg2 hres hw hu, ?_⟩
  intro qu z t hqu
  have hN : Ideal.absNorm w.asIdeal = qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw
  rw [GlobalTheory.LFun.seg, GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str, Int.toNat_natCast, Multiset.map_map, Finset.range_val]
  conv_lhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply]
  congr 1
  refine Units.ext ?_
  rw [GlobalTheory.LFun.coe_npowU, Units.val_zpow_eq_zpow_val, hqu]
  refine npow_eq_zpow w _ hN _ _ ?_
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
end
end

section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetSB

theorem cosetInd_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  intro k _ _ _ _ n _ _ q L _ f
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  by_cases hex : ∃ F : n → k, Lifts L F f
  · obtain ⟨F, hF⟩ := hex
    have e : cosetInd q L f = fun η => dualInd L (η - q.inv • F) := by
      funext η
      rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF (η - q.inv • F), sub_add_cancel]
    rw [e]
    exact GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.Comm.dualInd_mem L) (s := fun η => η + q.inv • F)
      (by fun_prop) (by fun_prop) fun η => sub_add_cancel η _
  · have e : cosetInd q L f = 0 := by
      classical
      funext η
      unfold cosetInd
      rw [ite_eq_right fun ⟨F, hF, _⟩ => hex ⟨F, hF⟩]
      rfl
    rw [e]
    exact (SB (n → k)).zero_mem

end GlobalTheory.FinPl.CosetSB
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitValueAdelic

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → (∀ τ : D.what₂.Tau, ∃ a : ℚ, a ≠ 0 ∧ HasInfExp D χ τ a) → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.LFun.UnrAt χ w → ¬ IsOfFinOrder (GlobalTheory.LFun.val (F := D.host.F) χ w) := by
  intro D χ hχ ha p hp w hw _
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  choose a ha0 ha using ha
  have h1 := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D χ H a hH).1 ha
  rw [(GlobalTheory.ChrTie.unrAt_iff_and_val_eq D χ H hH w).2]
  exact GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime D H a p h1 ha0 hp w hw

end GlobalTheory.SplitValueAdelic
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def signEquiv {n : ℕ} (ε : Fin n → Bool) {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : Fin n ≃ Fin p ⊕ Fin q :=
  (Equiv.sumCompl fun a => ε a = true).symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; exact hp))
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simpa using hq)))

theorem signEquiv_inl {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin p) : ε ((signEquiv ε hp hq).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl]
  generalize (Fintype.equivFinOfCardEq (α := {a // ε a = true}) _).symm i = x
  exact x.2

theorem signEquiv_inr {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) (i : Fin q) : ε ((signEquiv ε hp hq).symm (Sum.inr i)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.sumCompl_apply_inr]
  generalize (Fintype.equivFinOfCardEq (α := {a // ¬ ε a = true}) _).symm i = x
  simpa using x.2

theorem card_true (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = true).card = (V.sig (tauE D τ)).1 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).1

theorem card_false (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (Finset.univ.filter fun a => M.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  have h1 := GlobalTheory.TowerSplit.hasSignature_of_model M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (M.enum τ)] at h1
  exact (Formalism.UG.P.signature_unique _ _ _ _ _ _ h1 (hV (tauE D τ))).2

def sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Mem.Th.CptF V := fun τ =>
  (M.fr τ).submatrix (signEquiv (M.ε τ) (card_true M hV τ) (card_false M hV τ)).symm id

theorem Jpq_submatrix {n : ℕ} {ε : Fin n → Bool} {p q : ℕ} (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) :
    (Formalism.UG.Jpq p q).submatrix (signEquiv ε hp hq) (signEquiv ε hp hq) = Formalism.REAL.Jm ε := by
  ext a b
  simp only [submatrix_apply, Formalism.REAL.Jm, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rcases h1 : signEquiv ε hp hq a with i | i
    · have := signEquiv_inl hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
    · have := signEquiv_inr hp hq i
      rw [← h1, Equiv.symm_apply_apply] at this
      simp [Formalism.UG.Jpq, this]
  · have hne : signEquiv ε hp hq a ≠ signEquiv ε hp hq b := (signEquiv ε hp hq).injective.ne hab
    rw [if_neg hab]
    rcases h1 : signEquiv ε hp hq a with i | i <;> rcases h2 : signEquiv ε hp hq b with j | j <;> rw [h1, h2] at hne <;>
      simp_all [Formalism.UG.Jpq, Matrix.one_apply]

end GlobalTheory.ChainOnto.RealData

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

namespace GlobalTheory.Core.LocFromGlob

open scoped TensorProduct

theorem mem_latLoc_iff_of_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hL' : L'.FG) (b : GL (Fin n) (TensorProduct F (Af F) E))
    (hb : ∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E)))
    (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E) :
    z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by

  let ext : (Fin n → Fv F v ⊗[F] E) → (Fin n → Af F ⊗[F] E) :=
    fun z i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have hself : ∀ z, GlobalTheory.AdelicU.vecLoc v (ext z) = z := fun z =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have hne : ∀ z u, u ≠ v → GlobalTheory.AdelicU.vecLoc u (ext z) = 0 := fun z u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have hmul : ∀ (g : GL (Fin n) (TensorProduct F (Af F) E)) u y, GlobalTheory.AdelicU.vecLoc u (g.val *ᵥ y) =
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom g).val *ᵥ
        GlobalTheory.AdelicU.vecLoc u y := fun g u y => funext fun i =>
    RingHom.map_mulVec (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom _ y i
  have hext : ∀ (M : Submodule (𝓞 E) (Fin n → E)), M.FG → ∀ z, z ∈ latLoc F M v →
      ext z ∈ Formalism.MainNotions.StandardLattice.latHat F E (M : Set (Fin n → E)) := fun M hM z hz => by
    rw [GlobalTheory.AdelicU.mem_latHat_iff hM]
    intro u
    by_cases e : u = v
    · subst e; rw [hself]; exact hz
    · rw [hne z u e]; exact zero_mem _
  constructor
  · intro hz
    have h1 := (GlobalTheory.AdelicU.mem_latHat_iff hL' _).1 ((hb _).1 (hext L hL z hz)) v
    rwa [hmul, hself] at h1
  · intro hz
    have h1 := hext L' hL' _ hz
    set y := ext ((Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z)
    have h2 : b.val *ᵥ ((b⁻¹).val *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hL _).1 ((hb _).2 (h2 ▸ h1)) v
    rw [hmul, hself, Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.Core.LocFromGlob
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.LStab
section General
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem col_mem_hatL {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ)
    (j : Fin n) : β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  rw [hβ]
  intro k
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem exists_fg_sub {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hβ : IsFrame β Λ) :
    ∃ Λ₁ ≤ Λ, Λ₁.FG ∧ Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ := by
  classical
  have hcol : ∀ j, ∃ T : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ⊆ (fun x : Fin n → E => fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) '' (Λ : Set (Fin n → E)) ∧
      β.1 *ᵥ Pi.single j 1 ∈ Submodule.span (Formalism.L2.Herm.intAf F E) (T : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) := fun j =>
    Submodule.mem_span_finite_of_mem_span (col_mem_hatL hβ j)
  choose T hT hmem using hcol
  let U : Finset (Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := Finset.univ.biUnion T
  have hUsub : ∀ y ∈ U, ∃ x ∈ Λ, (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) = y := fun y hy => by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hy
    obtain ⟨x, hx, e⟩ := hT j hj
    exact ⟨x, hx, e⟩
  choose! pre hpre hpref using hUsub
  have hle : Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))) ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hpre y hy
  refine ⟨Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F))), hle,
    Submodule.fg_def.2 ⟨_, (U.finite_toSet.image pre), rfl⟩, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hle hx, rfl⟩
  · have hcolm : ∀ j, β.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.span (𝓞 E) (pre '' (U : Set (Fin n → E ⊗[F] Formalism.L2.Herm.Af F)))) := by
      intro j
      refine Submodule.span_mono ?_ (hmem j)
      intro y hy
      have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hy⟩
      exact ⟨pre y, Submodule.subset_span ⟨y, hyU, rfl⟩, hpref y hyU⟩
    intro y hy
    have hc := (hβ y).1 hy
    obtain ⟨c, hcdef⟩ : ∃ c, c = (β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ y := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have ey : y = ∑ j, c j • (β.1 *ᵥ Pi.single j 1) := by
      have e1 : y = β.1 *ᵥ c := by
        rw [hcdef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : c = ∑ j, c j • (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply]
      rw [e1]
      conv_lhs => rw [e2]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
    rw [ey]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem _ (⟨c j, hc j⟩ : Formalism.L2.Herm.intAf F E) (hcolm j)

theorem latLoc_eq {Λ₁ Λ : Submodule (𝓞 E) (Fin n → E)} (hle : Λ₁ ≤ Λ) (hfg : Λ₁.FG)
    (heq : Formalism.L2.Herm.hatL (F := F) Λ₁ = Formalism.L2.Herm.hatL (F := F) Λ) (v : HeightOneSpectrum (𝓞 F)) :
    GlobalTheory.AdelicU.latLoc F Λ₁ v = GlobalTheory.AdelicU.latLoc F Λ v := by
  apply le_antisymm
  · intro y hy
    exact GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => GlobalTheory.AdelicU.tmul_mem_latLoc ha (hle hx)) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
  · intro y hy
    refine GlobalTheory.AdelicU.latLoc_induction (fun a ha x hx => ?_) (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    have h1 : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ₁ :=
      heq ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    have h2 : (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (Λ₁ : Set (Fin n → E)) :=
      (GlobalTheory.LevSplit.latHat_iff Λ₁ _).2 h1
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hfg _).1 h2 v
    have h4 : GlobalTheory.AdelicU.vecLoc v (fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x i) = fun i => (1 : Fv F v) ⊗ₜ[F] x i := by
      funext i
      simp [GlobalTheory.AdelicU.vecLoc]
    rw [h4] at h3
    have h5 := (GlobalTheory.AdelicU.latLoc F Λ₁ v).smul_mem
      ⟨a ⊗ₜ[F] ((1 : 𝓞 E) : E), GlobalTheory.AdelicU.tmul_mem_intLoc ha 1⟩ h3
    convert h5 using 1
    funext i
    show _ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp

end General

section Adelic
variable {D : D7}

theorem finE_mem_St_iff_of_fg (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (hfg : Λ.FG) (g : GA D V) :
    Lev.finE V g ∈ Formalism.L2.DIV.St β ↔
      ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  have h1 := GlobalTheory.LevSplit.mem_St_iff β Λ hfr (Lev.finE V g)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff Λ) (finHom V g)
  have h3 := GlobalTheory.AdelicU.mem_levelOpen_iff_latHat D.sp.cm.sig V.gram hfg g
  have h4 := GlobalTheory.AdelicU.mem_levelOpen (σ := D.sp.cm.sig) (J := V.gram) (L := Λ) (g := g)
  exact h1.trans (h2.symm.trans (h3.symm.trans h4))

end Adelic

theorem finE_mem_St_iff_stabLoc : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.DIV.IsFrame β Λ → ∀ g : GA D V, Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := by
  intro D V β Λ hfr g
  obtain ⟨Λ₁, hle, hfg, heq⟩ := exists_fg_sub hfr
  have hfr₁ : Formalism.L2.DIV.IsFrame β Λ₁ := fun x => by
    rw [heq]; exact hfr x
  rw [finE_mem_St_iff_of_fg V β Λ₁ hfr₁ hfg g]
  have hL : ∀ v, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ₁ v = GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v := fun v => by
    unfold GlobalTheory.AdelicU.stabLoc
    rw [latLoc_eq hle hfg heq v]
  simp only [hL]

end GlobalTheory.ChainOnto.LStab
end
end
