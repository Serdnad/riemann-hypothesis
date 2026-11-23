module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle550
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle918
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle543
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShortThetaValueBoundedGoodReduction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle913
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

namespace GlobalTheory.DiffInt

theorem integral_absDet_cpow_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) (S : Set (GA E a)), NullMeasurableSet S μ → μ S < ⊤ → ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) → ∀ F : GA E a → ℂ, Continuous F → ∀ C : ℝ, (∀ g, ‖F g‖ ≤ C) → Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  intro E _ _ _ a μ S hS hμS c hc hδ F hF C hC
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδdef
  have hδc : Continuous δ := GlobalTheory.RSThetaLow.continuous_absDet
  have hae : ∀ᵐ g ∂(μ.restrict S), g ∈ S := ae_restrict_mem₀ hS
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  have key := GlobalTheory.integral_mul_cpow_of_rapid_decay_entire (GA E a) (μ.restrict S) δ F hδc.measurable
    (hae.mono fun g hg => ⟨lt_of_lt_of_le hc (hδ g hg).1, (hδ g hg).2⟩)
    (by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hδc.aestronglyMeasurable ?_
      refine hae.mono fun g hg => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hc.le (hδ g hg).1)]
      exact (hδ g hg).2)
    hF.aestronglyMeasurable
    (by
      intro K
      refine ⟨max C 0 / c ^ K, hae.mono fun g hg => ?_⟩
      have hcK : 0 < c ^ K := pow_pos hc K
      have h1 : c ^ K ≤ δ g ^ K := pow_le_pow_left₀ hc.le (hδ g hg).1 K
      rw [div_mul_eq_mul_div, le_div_iff₀ hcK]
      calc ‖F g‖ * c ^ K ≤ max C 0 * c ^ K :=
            mul_le_mul_of_nonneg_right ((hC g).trans (le_max_left _ _)) hcK.le
        _ ≤ max C 0 * δ g ^ K := mul_le_mul_of_nonneg_left h1 (le_max_right _ _))
  have := key.2.comp (differentiable_id.sub_const (1 : ℂ))
  exact this

end GlobalTheory.DiffInt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct




attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def CopyTw.cm (h : CopyTw D D' ι e) (j : Fin D.R.m) : Fin D'.R.m :=
  Fin.cast (congrArg Ranks.m h.gal.R) j

theorem CopyTw.cm_val (h : CopyTw D D' ι e) (j : Fin D.R.m) : ((h.cm j : Fin D'.R.m) : ℕ) = j := rfl

abbrev SameSetup (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) : Prop := SameData ρ ρ'

def RdRel (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (f : D.nexp.Fm i ((j : ℕ) + 1) b),
    HEq (rd' i' (h.cm j) b (h.fmCast hi ((j : ℕ) + 1) b f)) (rd i j b f)

end GlobalTheory.TwInputs.Move

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move.TieUp

variable {D : D7} (r : Rest D)

theorem placeModel_up {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel D mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel (overD D r) mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeModel_dn {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel (overD D r) mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel D mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    (baseUp r B).F.placeMap ((a)) = (B.F.placeMap a) := by
  have hP : (fun L : (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) →ₗ[ℂ] (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) =>
      IsPlaceModel (baseUp r B).F.ψ (symplO ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))))
        (heisO (baseUp r B).F.ψ ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :)))) ((by with_unfolding_all exact (a :))) (baseUp r B).F.lat 1 (baseUp r B).F.f₀ L) =
      (by with_unfolding_all exact ((fun L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
        IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ L) :)) :=
    funext fun L => propext ⟨fun h => (by with_unfolding_all exact ((placeModel_dn r h) :)), fun h => (by with_unfolding_all exact ((placeModel_up r h) :))⟩
  unfold Frame.placeMap
  exact (by with_unfolding_all exact ((congrArg Classical.epsilon hP) :))

theorem vec_up {S T : HSp D} (B : Base S T) (Q ω) :
    (baseUp r B).F.vec (baseUp r B).G (by with_unfolding_all exact (Q :))
      (by with_unfolding_all exact (ω :)) = (by with_unfolding_all exact (B.F.vec B.G Q ω :)) := by
  have e := placeMap_up r B (halfIdem B.G.Pg Q)
  show (baseUp r B).F.placeMap (by with_unfolding_all exact (halfIdem B.G.Pg Q :))
    (by with_unfolding_all exact (B.F.datumFn B.G Q ω :)) = _
  rw [e]
  with_unfolding_all exact rfl


open Classical in
theorem vecAt_up {S T : HSp D} (B : Base S T) (Q φ) :
    (baseUp r B).vecAt (by with_unfolding_all exact (Q :))
      (by with_unfolding_all exact (φ :)) = (by with_unfolding_all exact (B.vecAt Q φ :)) := by
  show (baseUp r B).F.vec (baseUp r B).G (by with_unfolding_all exact (B.de.Q ∪ Q :))
    (by with_unfolding_all exact (B.locFn Q φ :)) = _
  exact vec_up r B _ _

theorem series_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (Q φ h) :
    series (baseUp r B).F (by with_unfolding_all exact (ω :))
      ((baseUp r B).vecAt (by with_unfolding_all exact (Q :)) (by with_unfolding_all exact (φ :)))
      (by with_unfolding_all exact (h :)) = (by with_unfolding_all exact (series B.F ω (B.vecAt Q φ) h :)) := by
  rw [vecAt_up r B]
  with_unfolding_all exact rfl

theorem theta_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (h : GA D S) :
    (baseUp r B).theta ((ω)) ((h)) = (B.theta ω h) :=
  series_up r B ω ∅ (fun _ _ => 1) h

theorem vecFlat_up {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    (baseUp r B).vecFlat (twistUp r ψ) = (B.vecFlat ψ) :=
  vecAt_up r B ψ.Q _

theorem gen_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) :
    (baseUp r B).gen ((ω)) (twistUp r ψ) = (B.gen ω ψ) := by
  unfold Base.gen
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem genSet_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) (h P) :
    (baseUp r B).genSet (by with_unfolding_all exact (ω :)) (twistUp r ψ)
      (by with_unfolding_all exact (h :)) (by with_unfolding_all exact (P :)) =
        (by with_unfolding_all exact (B.genSet ω ψ h P :)) := by
  unfold Base.genSet
  rw [gen_up]
  with_unfolding_all exact rfl

def univUp {C : Type} [AddCommGroup C] (u : UnivTwist D C) : UnivTwist (overD D r) C := ⟨(by with_unfolding_all exact (u.del :)), (by with_unfolding_all exact (u.kap :))⟩

theorem vecFam_up {S T : HSp D} (B : Base S T) {C : Type} (Q : Finset (Pl D.host.E))
    (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) :
    (baseUp r B).vecFam (C := C) ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (Φ :))) = (by with_unfolding_all exact ((B.vecFam (C := C) Q Φ) :)) :=
  funext fun a => vecAt_up r B Q _

theorem xiCoef_up {S T : HSp D} (B : Base S T) {C : Type} [AddCommGroup C] [Fintype C] (ω : PairRep S T) (u : UnivTwist D C)
    (Q : Finset (Pl D.host.E)) (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) (h : GA D S)
    (P : PolF D T.rank S.rank) :
    (baseUp r B).xiCoef ((ω)) (univUp r u) ((Q)) ((Φ)) ((h)) ((P)) = (B.xiCoef ω u Q Φ h P) := by
  unfold Base.xiCoef Base.xi
  rw [vecFam_up]
  exact (by with_unfolding_all exact (rfl :))

theorem classSum_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) {I : Type} [Fintype I] (h : I → GA D S) :
    (baseUp r B).classSum (I := I) ((by with_unfolding_all exact (ω :))) (twistUp r ψ) ((by with_unfolding_all exact (h :))) = (by with_unfolding_all exact ((B.classSum ω ψ h) :)) := by
  unfold Base.classSum
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem coefLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) : B.coefLat σ emb O = B.coefLat (embLL0 D) (labLL0 D) O := by
  obtain rfl : (embLL0 D).comp e.toRingHom = σ := RingHom.ext hσ
  have h : (fun τ => e.toRingHom.comp (emb τ)) = labLL0 D := funext fun τ => RingHom.ext fun x => (embLL0 D).injective
    ((DFunLike.congr_fun (hemb τ) x).trans (DFunLike.congr_fun (embLL0_labLL0 τ) x).symm)
  funext x
  rw [Base.coefLat, Base.coefLat, harmLat, harmLat, GlobalTheory.CoefLatIso.coefLatFn_ringEquiv, h]

theorem mtLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) (t : Twist D Circle) : B.mtLat σ emb O t = B.mtLat (embLL0 D) (labLL0 D) O t := by
  rw [Base.mtLat, Base.mtLat, coefLat_of_equiv B e σ emb hσ hemb]

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem liftSetupOverExtendedData_theta_eq : (setupUp r ρ).theta ((i)) ((j)) b = (ρ.theta i j b) :=
  (by with_unfolding_all exact ((funext fun h => congrArg DFunLike.coe (theta_up r (ρ.B i j b) (ρ.om i j b 1) h)) :))

theorem liftSetupOverExtendedData_gens_eq : (setupUp r ρ).gens ((i)) ((j)) b = (ρ.gens i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ => funext fun h => funext fun P =>
    genSet_up r (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k Q ψ) h P) :))

theorem liftSetupOverExtendedData_classSum_eq : (setupUp r ρ).sum ((i)) ((j)) b = (ρ.sum i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ =>
    classSum_up r (ρ.B i j b) (ρ.om i j b (ρ.tw i b k Q ψ).chi) (ρ.tw i b k Q ψ) (ρ.rep i j b (ρ.tw i b k Q ψ))) :))

theorem liftSetupOverExtendedData_xi_eq : (setupUp r ρ).xi ((i)) ((j)) b (overD D r).nexp = (ρ.xi i j b D.nexp) :=
  (by with_unfolding_all exact ((funext fun Q => funext fun M => funext fun h => funext fun P =>
    xiCoef_up r (ρ.B i j b) (ρ.om i j b 1) (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc)
      (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) h P) :))

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
include hc

theorem liftSetupOverExtendedData_lat_eq : (setupUp r ρ).lat ((i)) ((j)) b = (ρ.lat i j b) := by
  funext O x
  have := coefLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :))) O
  exact (by with_unfolding_all exact ((congrFun this (finPt _ x)) :))

theorem liftSetupOverExtendedData_integralForms_eq : (setupUp r ρ).mt ((i)) ((j)) b = (ρ.mt i j b) := by
  have H := mtLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :)))
  have H' := fun (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) =>
    H (ρ.eOk i b k).range (ρ.tw i b k Q ψ)
  funext k Q ψ
  exact (by with_unfolding_all exact ((H' k ((Q)) ((ψ))) : _))

theorem liftSetupOverExtendedData_isDatum_eq : (setupUp r ρ).IsDatum ((i)) ((j)) b = (ρ.IsDatum i j b) := by
  funext s x P
  have hl := liftSetupOverExtendedData_lat_eq ρ i j b hc
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · have m := d.mem
    rw [hl] at m
    exact (⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (m :))⟩ : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))))
  · have d' : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))) := d
    refine ⟨(by with_unfolding_all exact (d'.split :)), (by with_unfolding_all exact (d'.off :)), (by with_unfolding_all exact (d'.fin :)), (by with_unfolding_all exact (d'.supp :)), ?_⟩
    rewrite [hl]
    exact (by with_unfolding_all exact (d'.mem :))

end Setup

section Cell

variable {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
  {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool}

def cellUp {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    CellTie hρ' (overD D r).nexp (i := (by with_unfolding_all exact (i :))) (j := (by with_unfolding_all exact (j :))) (b := b) ((by with_unfolding_all exact (rd :))) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.dat :))
  dat_onto := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc, liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.dat_onto :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by rewrite [liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by rewrite [liftSetupOverExtendedData_gens_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_eq :))
  thU_off := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_off :))
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := by rewrite [liftSetupOverExtendedData_integralForms_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.mtLat_iff :))
  thP_eq := by rewrite [liftSetupOverExtendedData_classSum_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thP_eq :))

theorem cellUp_rdV {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    HEq t.rdV (cellUp r hc hρ' t).rdV := HEq.rfl


end Cell

end GlobalTheory.TwInputs.Move.TieUp

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.SBThetaUpper

open GroundTheory.Automorphic.GJMatrix GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GlobalTheory.ShortVecDecay GlobalTheory.RSTheta

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_norm_mul_pow_le {G : (Fin a → Ad E) → ℂ} (hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin a)) (M : ℕ) :
    ∃ B : ℝ, ∀ y, ‖G y‖ * (1 + ‖fun i => pInf E (y i)‖) ^ M ≤ B := by
  classical
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨h1, h2⟩ := (mem_finiteSchwartzBruhatPi E).mp hg
    obtain ⟨B, hB⟩ := h1.continuous.bounded_above_of_compact_support h2
    set S := (toMixedPi E a).symm
    set C := ‖(S : (Fin a → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin a → Cinf E))‖
    have hC : 0 ≤ C := norm_nonneg _
    obtain ⟨A₀, -, hA₀⟩ := φ.decay 0 0
    obtain ⟨A₁, -, hA₁⟩ := φ.decay M 0
    refine ⟨(1 + C) ^ M * 2 ^ M * (A₀ + A₁) * B, fun y => ?_⟩
    rw [GlobalTheory.SchwartzBruhatMoments.pInfPi_eq, schwartzBruhatTensorPi, norm_mul]
    have hBy := hB (finPartPi y)
    generalize finPartPi y = z at hBy
    generalize infPartPi y = u
    have a0 := hA₀ u
    have a1 := hA₁ u
    rw [norm_iteratedFDeriv_zero] at a0 a1
    rw [pow_zero, one_mul] at a0
    have h1 : ‖S u‖ ≤ C * ‖u‖ := (S : (Fin a → mixedEmbedding.mixedSpace E) →L[ℝ] (Fin a → Cinf E)).le_opNorm u
    have h2 : 1 + ‖S u‖ ≤ (1 + C) * (1 + ‖u‖) := by nlinarith [norm_nonneg u, norm_nonneg (S u)]
    have h3 : (1 + ‖S u‖) ^ M ≤ (1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M)) := by
      calc (1 + ‖S u‖) ^ M ≤ ((1 + C) * (1 + ‖u‖)) ^ M := pow_le_pow_left₀ (by positivity) h2 M
        _ = (1 + C) ^ M * (1 + ‖u‖) ^ M := mul_pow _ _ _
        _ ≤ (1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M)) :=
          mul_le_mul_of_nonneg_left (GlobalTheory.SchwartzBruhatMoments.one_add_pow_le (norm_nonneg u) M) (by positivity)
    have h4 : ‖φ u‖ * (1 + ‖S u‖) ^ M ≤ (1 + C) ^ M * 2 ^ M * (A₀ + A₁) := by
      calc ‖φ u‖ * (1 + ‖S u‖) ^ M ≤ ‖φ u‖ * ((1 + C) ^ M * (2 ^ M * (1 + ‖u‖ ^ M))) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = ((1 + C) ^ M * 2 ^ M) * (‖φ u‖ + ‖u‖ ^ M * ‖φ u‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add a0 a1) (by positivity)
    calc ‖φ u‖ * ‖g z‖ * (1 + ‖S u‖) ^ M = ‖φ u‖ * (1 + ‖S u‖) ^ M * ‖g z‖ := by ring
      _ ≤ _ := mul_le_mul h4 hBy (norm_nonneg _) (le_trans (by positivity) h4)
  | zero => exact ⟨0, fun y => by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨B₁, h1⟩ := hG
    obtain ⟨B₂, h2⟩ := hH
    refine ⟨B₁ + B₂, fun y => le_trans ?_ (add_le_add (h1 y) (h2 y))⟩
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  | smul c G _ hG =>
    obtain ⟨B, h⟩ := hG
    refine ⟨‖c‖ * B, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem isSmallKernel_sq_mul {φ : GA E a → ℂ} (h : Decays φ) {G : (Fin a → Ad E) → ℂ}
    (hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin a)) : IsSmallKernel fun g y => φ g ^ 2 * G y := by
  obtain ⟨L, hL, hs⟩ := (GlobalTheory.SchwartzBruhatMoments.compactSupport_and_integrable_moments E a G hG).1
  refine ⟨⟨L, hL, fun g y hy => hs y (right_ne_zero_of_mul hy)⟩, fun L hL N M => ?_⟩
  obtain ⟨C, hC⟩ := h L hL {1} isCompact_singleton N
  obtain ⟨C', hC'⟩ := h L hL {1} isCompact_singleton 0
  obtain ⟨B, hB⟩ := exists_norm_mul_pow_le hG M
  refine ⟨|C| * |C'| * |B|, fun g ξ hξ hm y => ?_⟩
  have hΔ : 0 < (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) :=
    (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have h1 := (hC g 1 rfl ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h2 := (hC' g 1 rfl ξ hξ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
  rw [mul_one] at h1 h2
  have h3 : ‖G y‖ ≤ |B| * (1 + ‖fun i => pInf E (y i)‖) ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact (hB y).trans (le_abs_self B)
  beta_reduce
  rw [norm_mul, sq, norm_mul]
  refine (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)).trans_eq ?_
  ring

set_option synthInstance.maxHeartbeats 400000 in
theorem lintegral_theta_upper_ne_top : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ,
      ∫⁻ g in 𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ' φ' hφ' G hG μ _ 𝓕 h𝓕 x
  have hd : Decays φ' := GlobalTheory.MSpanDecay.Good.decays (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ' hφ')
  obtain ⟨C, hC⟩ := (isSmallKernel_sq_mul hd hG).tsum_le (N := ⌈x⌉₊ + 1) (by omega)
  have hI := ((integrableOn_absDet_rpow_neg (Nat.succ_pos m) μ h𝓕 (s := (⌈x⌉₊ + 1 : ℕ) - x)
      (by push_cast; linarith [Nat.le_ceil x])).const_mul C).lintegral_lt_top
  refine ne_top_of_le_ne_top hI.ne (lintegral_mono fun g => ?_)
  obtain ⟨hs, hle⟩ := hC g
  have h0 := GlobalTheory.RSnm.detAbs_pos g
  change _ ≤ C * GlobalTheory.RSnm.detAbs g ^ _ at hle
  change _ ≤ ENNReal.ofReal (C * GlobalTheory.RSnm.detAbs g ^ _)
  rw [← ENNReal.tsum_mul_left]
  simp only [← eNorm_pow, ← eNorm_mul]
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs,
    ← ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), neg_sub, sub_eq_neg_add, Real.rpow_add h0, ← mul_assoc]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (by positivity))

end GlobalTheory.SBThetaUpper
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a), π.IsUnitary → ∀ φ : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → ∀ l : List (Lie E a),
    ∀ L : Set (Fin a → Af E), IsCompact L → ∀ C₀ : Set (GA E a), IsCompact C₀ → ∀ N : ℕ, ∃ C : ℝ,
      ∀ g : GA E a, ∀ c ∈ C₀, ∀ ξ : Fin a → E, ξ ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)) ∈ L →
          ‖(GlobalTheory.GLFin.word l φ).1 (g * c)‖ ≤
            C * (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) i)‖ ^ (a * Module.finrank ℚ E) /
              (ideleModule E (GeneralLinearGroup.det g) : ℝ)) ^ N := by
  first | exact @GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | exact GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR | (intros; apply GlobalTheory.MSpanDecay.norm_le_of_short_vector_mspanR <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_type_under_supported_lifts : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T), series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  first | exact @GlobalTheory.TypeSupportLift.series_type_supp | exact GlobalTheory.TypeSupportLift.series_type_supp | (intros; apply GlobalTheory.TypeSupportLift.series_type_supp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

theorem _root_.GlobalTheory.T.shortThetaValue_bounded_goodReduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (n d N : ℕ) (La : GenLat E n) (w : (Fin n → LevQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (v : T.Fr), Good y → La.Unimod → La.TrivAt l.M → La.LevOK N l.M → (∀ q, InV T (io (w q))) → P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) → P.IsHomogeneous d → (∀ m, InV T (io (P.coeff m))) → (letI := io.toAlgebra; thLaValAt Xo c nab w La N P y.1 v) → InV T (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l) : ℕ) : T.Fr) * ((2 * NumberField.discr E * N : ℤ) : T.Fr) ^ d * v) := by
  first | exact @GlobalTheory.GoodThetaBound.theta_value_bounded | exact GlobalTheory.GoodThetaBound.theta_value_bounded | (intros; apply GlobalTheory.GoodThetaBound.theta_value_bounded <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  first | exact @GlobalTheory.RawLift.LevelFix.levFix | exact GlobalTheory.RawLift.LevelFix.levFix | (intros; apply GlobalTheory.RawLift.LevelFix.levFix <;> assumption)
end
