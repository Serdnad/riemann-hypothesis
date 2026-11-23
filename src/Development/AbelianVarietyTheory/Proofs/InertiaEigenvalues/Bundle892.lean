module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle868
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle228
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle882
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries MvPolynomial Matrix
open Formalism.IndefR.Links
open scoped TensorProduct




namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Scale

variable {D : D7} {n : ℕ}

theorem coefFn_translate (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n →+* Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) =
      eval₂Hom (RingHom.id ℂ) (fun v => ((u⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_

    simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
    eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => rfl
  have e3 : (RingHom.id ℂ) (detTwK lam (invTrK u)) =
      ((detFam (fun τ => (lam τ).detShift) u⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change (((u τ)⁻¹).valᵀ).det = _
    rw [det_transpose]
    rfl
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

theorem coefFn_map {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  rw [coefFn, coefFn, eval₂Hom_map_hom, RingHom.id_comp]

def coefLin (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
  map_add' F F' := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add (f := _), Pi.add_apply, mul_add]
  map_smul' a F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem coefLin_injective (lam : D.what₂.Tau → DomWeight n) : Function.Injective (coefLin lam) :=
  (injective_iff_map_eq_zero _).2 fun F hF => Subtype.ext (GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily D n lam F (congrFun hF))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {j : Fin D.R.m}
  {B : Base (Vc D j) (Wc D j)}

theorem io_act (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hB : B.Good) (hψ : B.F.ψ = R.ψ) (hθ : B.F.θ = R.θ)
    (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ) (hBT : B.F.BT = onb (R.MW j (sg0 D A)))
    (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta) (x : LowT (R.MW j (sg0 D A))) :
    ∀ u ∈ GinfC (Vc D j), ∀ w, R.ioP j x ((R.cV j).ρ u w) = B.act u (R.ioP j x w) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hf : IsThetaFunO R.ψ (Vc D j) (Wc D j) (R.vP j A.μ0) := by
    have := hth.pt_theta j A.μ0 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D j) τ) 1 (R.BV j τ) (Vc D j).rank := fun τ => hBS τ ▸ hB.frame.onbS τ
  have hinj : Function.Injective (R.ptP j A.μ0) :=
    GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW j (sg0 D A)) (R.BV j) (R.vP j A.μ0) (hth.ωP j A.μ0).std hinf
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hon τ)) hon hf
      (GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βV j))
        (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βW j)) hB.frame.rank_le (hth.vP j A.μ0))
      (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hth.vP j A.μ0) hf)
  have hexp : ∀ τ, HasInfExp D (R.toLevCh.mu A.μ0 ((j : ℕ) + 1)) τ
      ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := fun τ => by
    obtain ⟨k, hk, ho⟩ := hlev.xi_fin A.μ0
    have h1 := hB.inf τ
    rw [hmu] at h1
    have h2 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hinf (hlev.xi A.μ0) hk ho τ)
    rwa [add_zero] at h2
  intro u hu w
  exact hinj (((hth.ioP j A.μ0).1 u hu x w).symm.trans
    (GlobalTheory.T.realisation_definite_realPoint_fockVector_action D G Pl0 T0 A Ks R j A.μ0 B hth hB hψ hθ hsT hBS hBT heta hexp u hu _))

theorem exists_scale (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hc : (R.cV j).Is) (hB : B.Good) (hψ : B.F.ψ = R.ψ)
    (hθ : B.F.θ = R.θ) (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ)
    (hBT : B.F.BT = onb (R.MW j (sg0 D A))) (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta)
    (hap : ∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ)
    (ham : ∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ)
    (c0 : VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (R.cV j).W)
    (ht : Bridge.CoefMapTie (Vc D j) (R.cV j).coef c0 (rhoVr (labLL D) (FWT.lamV D j)))
    (x : LowT (R.MW j (sg0 D A))) (w₀ : (R.cV j).W) (hw : R.ioP j x w₀ = RealDat.Delta j) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ F : VV D.what₂.LL (FWT.lamV D j), harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hT := io_act hlev hth hB hψ hθ hsT hBS hBT hmu heta x
  have hlam : B.w.lam = FWT.lamV D j := GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight D T0 R.toLevCh A.μ0 j B hlev hB hmu hap ham
  have hpq : ∀ τ, B.w.p τ + B.w.q τ ≤ (Wc D j).rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hΔ : B.w.delta (Wc D j).rank = RealDat.Delta j := by
    unfold Weight.delta RealDat.Delta
    rw [show B.w.p = _ from funext fun τ => congrArg Prod.fst (hB.sig τ),
      show B.w.q = _ from funext fun τ => congrArg Prod.snd (hB.sig τ), show B.w.ap = _ from funext hap,
      show B.w.am = _ from funext ham]
  have hirr : ∀ U : Submodule ℂ (R.cV j).W, (∀ h : GinfC (Vc D j), U.map ((R.cV j).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hc.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hc.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
  have hharm : ∀ w, R.ioP j x w ∈ harm (Wc D j).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x))
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D j) R.θ (R.cV j) (FWT.lamV D j) c0 hinf hc ht
  haveI := hc.2.2.2.1
  obtain ⟨c, hcc⟩ := GlobalTheory.T.schur_equivariant_maps_proportional (GinfC (Vc D j)) (R.cV j).W (GLR D (Vc D j).rank → ℂ) (fun h => (R.cV j).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D j) h)⁻¹ * y)
    (harmFn (Wc D j).rank B.w B.F.BS ∘ₗ R.ioP j x) (coefLin (FWT.lamV D j) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x w) ∈
          (harm (Wc D j).rank B.w B.F.BS).map (harmFn (Wc D j).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨F, rfl⟩
      exact ⟨e F, congrArg (coefLin _) (e.symm_apply_apply F)⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP j x ((R.cV j).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP j x w) _
      rw [hT h h.2, ← hθ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV j).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  refine ⟨c, fun h0 => hΔ0 ?_, fun F => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · refine (LinearMap.congr_fun hcc (c0 F)).trans ?_
    change c • coefLin _ (e.symm (c0 F)) = _
    rw [show e.symm (c0 F) = _ from e.symm_apply_eq.2 (he0 F).symm, ← coefFn_map]
    rfl

end Scale

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_isScale (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ)
    (hlev : Rl.toLevCh.Is A3.A.μ0) (hfam : Rl.toRealDat.fam_tie) (hcV : Rl.toRealDat.models_cV) (hth : Rl.toRealDat.IsThP)
    (hio : FWT.IoExt Rl.toRealDat) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) : ∃ c : ℂ, c ≠ 0 ∧ IsScale Rl v₀ (ρ.B i j b) c := by
  obtain ⟨gramR, c0R, c0L, hft⟩ := hfam
  obtain ⟨u, w₀, hu, -, hw⟩ := FWT.IsChosenExtremalVector.io _ hv hio
  obtain ⟨c, hc0, hc⟩ := Scale.exists_scale hlev hth (hcV j) (hρ.base i j b) (hpin.psi i j b) (hpin.inf i j b)
    (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b)
    (c0L j) (hft.mapL j) _ w₀ hw
  exact ⟨c, hc0, gramR, c0R, c0L, hft, u, hu, hc⟩

end GlobalTheory.SeriesTie

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.SeriesTie.ActProof
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem parLev_eq_of {n : ℕ} {LL : Type} [CommRing LL] (hc : CMData D.host.F D.host.E) (J : Matrix (Fin n) (Fin n) D.host.E)
    (β : GL (Fin n) (D.host.E ⊗[D.host.F] Af D.host.F)) (L L' : LevDat D.host.E LL n) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hb : (blkOf L.r L.t : Fin n → ℕ) = blkOf L'.r L'.t) (hb2 : (blk2 L.r : Fin n → ℕ) = blk2 L'.r) :
    parLev hc J β L = parLev hc J β L' := by
  unfold parLev
  rw [hP, hQ, hb, hb2]

theorem blkOf_eq_zero {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem twoBlockSizes_eq_zero_of_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_twoBlockSizes_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) : g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [twoBlockSizes_eq_zero_of_le h] at hik
  exact absurd hik (lt_irrefl _)

variable (Rl : RealDat3 D A3 Ks) (j : Fin D.R.m)

theorem levChi_flagL (κ : GA D (Wc D j)) : levChi (Wc D j) (Rl.βW j) (flagL (Rl.datWp j Rl.triv)) κ = 1 := by
  unfold levChi levFn
  have h1 : (flagL (Rl.datWp j Rl.triv)).P.chi = 1 := rfl
  have hs : (flagL (Rl.datWp j Rl.triv)).s = 0 := rfl
  have hq : (flagL (Rl.datWp j Rl.triv)).Q = ∅ := rfl
  rw [h1, subgroupCharExtension_one_apply, hs, hq]
  simp

theorem hasType_of_mem_wall {σ : D.what₂.LL →+* ℂ} {F : MMap (Rl.MW j σ)} (hF : F ∈ Rl.toRealDat.Wall j σ)
    (v : (Rl.MW j σ).Vec) : HasType (Wc D j) (Rl.βW j) (flag1L (Rl.datWp j Rl.triv)) (F v) := by
  have key : ∀ F' ∈ Rl.toRealDat.Wall j σ, ∀ (v : (Rl.MW j σ).Vec), ∀ κ ∈ levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv),
      ∀ h, F' v (h * κ) = levChi (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) κ * F' v h := by
    intro F' hF'
    induction hF' using Submodule.span_induction with
    | mem x hx => exact fun v κ hκ h => hx.lev v κ hκ h
    | zero => intro v κ _ h; simp only [MultilinearMap.zero_apply, Pi.zero_apply, mul_zero]
    | add x y _ _ hx hy =>
      intro v κ hκ h
      rw [MultilinearMap.add_apply, Pi.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
    | smul a x _ hx =>
      intro v κ hκ h
      rw [MultilinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul, smul_eq_mul, mul_left_comm]
  exact fun κ hκ h => key F hF v κ hκ h

theorem isLift_transfer {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hp : RealPin Rl cG ρ) (i : D.ntw.Tw) (b : Bool)
    (g : G0g D.nd) (κ : GA D (Wc D j))
    (h : IsLevelLift (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).G.levT (ρ.eG i j b g) κ) :
    IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g) κ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hp.frT] at h2 h3
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (ρ.B i j b).G.levT =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    apply parLev_eq_of
    · exact hp.Pg i j b
    · rfl
    · exact (blkOf_eq_zero le_rfl).trans (blkOf_eq_zero hr).symm
    · exact (twoBlockSizes_eq_zero_of_le le_rfl).trans (twoBlockSizes_eq_zero_of_le hr).symm
  refine ⟨h1, hpar ▸ h2, ?_⟩
  funext PP
  apply Units.ext
  ext a c
  have hPP : PP.1 ∈ (ρ.B i j b).G.Pg := (hp.Pg i j b).symm ▸ PP.2
  have hg := hp.grp i j b g PP.1 hPP PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
  rw [← h3] at hg
  have hg2 : Units.val (cG.symm g PP) a c =
      Units.val (rTup (Rl.βW j) (ρ.B i j b).G.levT (finE (Wc D j) κ) ⟨PP.1, hPP⟩)
        (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c) := hg.symm
  rw [hg2]
  unfold rTup
  erw [upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le le_rfl _)]
  rfl

theorem sg0_eq_embLL (Rl : RealDat3 D A3 Ks) : sg0 D A3.A = D.what₂.embLL := by
  ext c
  exact congrArg (fun f : D.what₂.LL →+* ℂ => f c) (Links.sgAt_mk _ Rl.hv0)

theorem evW_rho (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (g' : S.G) (κ : GA D (Wc D j)) (hκ : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm (S.eG g')) κ)
    (z : S.WL ((j : ℕ) + 1)) (x : GA D (Wc D j)) :
    evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ g' z) x =
      D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi g' : D.what₂.LLˣ) : D.what₂.LL) * evW YS v₀ j z (x * κ) := by
  have hgeq : Rl.eG ((YS.fi j).eG g') = cG.symm (S.eG g') := by
    rw [← YS.geq j g', MulEquiv.symm_apply_apply]
  have hκ' : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) κ := hgeq ▸ hκ
  set F := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e z)) with hFdef
  have hmem : F ∈ Rl.toRealDat.Wall j (sg0 D A3.A) := (hW j _).2.1 ▸ LinearMap.mem_range_self _ _
  have hT := hasType_of_mem_wall Rl j hmem (v₀ j _)
  have hs := level_action_spec hT ⟨κ, hκ'⟩ κ hκ' x
  rw [levChi_flagL, inv_one, one_mul] at hs
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ g' z))) (v₀ j _) x = _
  rw [(YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi]
  change sg0 D A3.A _ * (actG0 (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) (F (v₀ j _))) x = _
  rw [hs]
  exact congrArg (· * F (v₀ j _) (x * κ)) (congrArg (fun f : D.what₂.LL →+* ℂ => f _) (sg0_eq_embLL Rl))

end GlobalTheory.SeriesTie.ActProof

namespace GlobalTheory.SeriesTie
open Formalism.IndefR.Lev Formalism.L2.DIV
open scoped TensorProduct

theorem actRead_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → ActRead (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hU hW
  intro g κ hκ f x
  have hκ' := ActProof.isLift_transfer Rl j hp i b g κ hκ
  change (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.actG i _ b g f))) x =
    (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * κ)
  rw [YS.act, Pi.smul_apply, Pi.smul_apply]
  congr 1
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = y
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearEquiv.map_zero, map_zero]; rfl
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, Pi.add_apply, hy, hz, map_add, Pi.add_apply]
  | tmul a f0 =>
    have hg : S.eG (S.eG.symm g) = g := S.eG.apply_symm_apply g
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evK_tmul, evK_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have h2 := ActProof.evW_rho Rl j hU hW YS v₀ (S.eG.symm g) κ (hg.symm ▸ hκ') (Subtype.val f0) x
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    change ρ.e i b _ * evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)) x = _
    rw [h2]
    erw [map_mul, map_inv₀, he]
    field_simp

end GlobalTheory.SeriesTie
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.split_set_inertia_power_trivial : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  first | exact @GlobalTheory.TwistPullTame.good_pull_tame | exact GlobalTheory.TwistPullTame.good_pull_tame | (intros; apply GlobalTheory.TwistPullTame.good_pull_tame <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.fockSubstitution_preserves_harmonicLetterPolynomials : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (lt : LtN Dw n ≃ FVar D m n),
    m = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → IsLetters Dw lt →
    ∀ (u : GlobalTheory.ExportSeries.GLR D n) (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (Q : MvPolynomial (LtN Dw n) ℂ),
      Q ∈ HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) →
      MvPolynomial.rename lt.symm (GlobalTheory.ExportSeries.fockSubst (m := m) (fun _ => Dw.p) u (MvPolynomial.rename lt Q)) ∈
        HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) := by
  first | exact @GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa | exact GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa | (intros; apply GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.vacuum_translate_sum_conjugateHalf_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → ∑ y ∈ Y, heisO ψ V W y f₀ ≠ 0 := by
  first | exact @GlobalTheory.VacTransNe.sum_heisO_conjHalf_ne_zero | exact GlobalTheory.VacTransNe.sum_heisO_conjHalf_ne_zero | (intros; apply GlobalTheory.VacTransNe.sum_heisO_conjHalf_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CellDec
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_unipotentCell_pos_lt_top_continuous : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 E))) (𝓕 : Set (GA E n)), IsFundamentalDomain (NE E n) 𝓕 μ → ∀ B : ℝ → GA E n → ℝ, Continuous (Function.uncurry B) → (∀ x g, 0 ≤ B x g) → (∀ x, 0 < B x 1) → (∀ x, ∀ u ∈ NA E n, ∀ g, B x (u * g) = B x g) → (∃ K : Set (GA E n), IsCompact K ∧ ∀ x g, g ∈ C0 E n S → B x g ≠ 0 → ∃ u ∈ NA E n, u * g ∈ K) → (∀ x, 0 < ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ ∧ ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ < ⊤) ∧ Continuous fun x => (∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ).toReal := by
  first | exact @GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | exact GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous | (intros; apply GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous <;> assumption)
end
