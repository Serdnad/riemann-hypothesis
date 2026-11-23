module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTeichmullerOfFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle166
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle295
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def realLev (R : RealDat D A Ks) (i : Fin D.R.m) : Set (GA D (Wc D i)) :=
  {h | ∃ u ∈ GinfC (Wc D i), ∃ k ∈ levW R i, h = u * k}

def lowCoefSq (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Wc D i)) : ℝ :=
  ‖∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
    (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h)
      ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ‖ ^ 2


variable (A) in
def dimProd (i : Fin D.R.m) : ℂ :=
  ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)

def rallisF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (x y : (R.HW i (sg0 D A)).H) (g : GA D (Wc D i)) : ℂ :=
  thetaIP μ 𝓕 (R.ωP i t (1, g) f) f *
    ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * g) ∂(R.νW i)

theorem two_mul_rank_W_lt (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank < (Vc D i).rank := by
  have h1 := i.2
  rw [D.sp.W_rank _ (by omega) (by omega), D.sp.V_rank _ (by omega) (by omega)]
  have := (D.R.rank_add_five_le : D.R.r + 5 ≤ D.R.t)
  unfold Ranks.nV
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

end GlobalTheory.RawLift

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL PowerSeries

noncomputable section

namespace GlobalTheory.HWL.IoLayer

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem sepRA' (LL : FinExt l) (e : OCb l) (he : ¬ IsUnit (e - 1)) (t : RA LL)
    (ht : (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e = t) (x : RA LL)
    (hx : ∀ k, (t - 1) ^ k ∣ x) : x = 0 := by
  refine sepRA LL e he x ?_
  have h := tmul_sub_one LL (WittVector.teichmuller l e)
  rw [h, ht]
  exact hx

theorem teich_pow (LL : FinExt l) (e : OCb l) :
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (e ^ l) : RA LL) =
      ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l e) ^ l := by
  have h1 : WittVector.teichmuller l (e ^ l) = (WittVector.teichmuller l e : Ainf l) ^ l := map_pow _ _ _
  rw [h1, Algebra.TensorProduct.tmul_pow, one_pow]

theorem γ₀_X_eq {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL} (R : WSer Γ)
    (g : ↥(GK K)) (c : ℤ_[l]) (hc : (c : ℚ_[l]) = (P.χQ g : ℚ_[l])) :
    R.γ₀ (Γ.resΓ g) X = PowerSeries.map (algebraMap ℤ_[l] ↥(OL LL)) (binomialSeries ℤ_[l] c) - 1 := by
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  obtain ⟨_, _, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hlin : (Γ.χΓ (Γ.resΓ g) : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) c := by
    apply Subtype.ext
    have := Γ.χΓ_res g
    rw [P.PD_χ, ← hc] at this
    exact this
  have hact := (GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (R.γ₀ (Γ.resΓ g)) R.φ₀ c h0
    (R.γ₀_comm _) (R.γ₀_X _).1 ((R.γ₀_X _).2.trans hlin)).2
  rw [hact, (GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws l ↥(OL LL)).1, GlobalTheory.Cyc.cyc]



theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ), ∃ I : IoS AI R, IoW I := by
  intro l _ P AI K s LL hG Γ R
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨u, hu, huniq⟩ := GlobalTheory.UnramIdem.exists_prod_hom l P K s LL hG Γ.emb Γ.emb_bij
  have he := εroot_sub_not_unit AI s
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).2.2.2.2 _ he
  obtain ⟨io, hπ, hc⟩ := let_exists
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1) : RA LL) u
  have hπ' := hπ.trans (tmul_sub_one LL _)
  have h0 : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
  have h1 : io.comp (letφ R.φ₀) = (φRA LL).comp io := by
    have ht := teich_pow LL (AI.εroot s)
    have he' : ¬ IsUnit (AI.εroot s ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    refine comm_φ l R.φ₀ h0 io u hc (φRA LL) _ hπ' ((φRA_teich LL _).trans ht) ?_
      (sepRA' LL _ he' _ ht)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := hu (c ^ l) m hm hl
      (by rw [SubmonoidClass.coe_pow, ← pow_mul, mul_comm, pow_mul, hcm, one_pow]) (xb ^ l)
      (tilt_pow hxb l) (shift _ _ o) (fun i => by
        have := DFunLike.congr_fun (Γ.emb_σ (i - 1)) c
        rw [sub_add_cancel, AlgHom.comp_apply, sigma_root K c m hm hl hcm] at this
        rw [this]
        exact ho (i - 1))
    exact e2.trans ((congrArg (φRA LL) e1).trans (φRA_teich LL xb)).symm
  have h2 : ∀ g : ↥(GK K), io.comp (letγ (R.γ₀ (Γ.resΓ g))) = (gRA AI LL (g : GQ l)).comp io := by
    intro g
    obtain ⟨χ, hχ, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
    obtain ⟨⟨io0, hio0, -⟩, -⟩ := GlobalTheory.Cyc.IoMap.main l _ he
    have he' : ¬ IsUnit (AI.actT g (AI.εroot s) - 1) := fun h => he (by
      have := h.map (AI.actT g).symm
      rwa [map_sub, map_one, RingEquiv.symm_apply_apply] at this)
    have e0 := (io_zl LL _ _ he io hπ io0 hio0 (binomialSeries ℤ_[l] (χ g : ℤ_[l]))).trans
      (congrArg (fun w : Ainf l => ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RA LL))
        (io_binomial AI s g _ (hχ g) io0 hio0))
    refine comm_γ _ _ (γ₀_X_eq R g _ (hχ g)) io u hc (gRA AI LL g) _ _ hπ' e0 (gRA_teich AI LL g _) ?_
      (sepRA' LL _ he' _ rfl)
    refine huniq _ _ _ fun c m hm hl hcm o ho => ?_
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hcm
    have e1 := hu c m hm hl hcm xb hxb o ho
    have e2 := actT_tilt AI g c (g.2 ⟨c, c.2.1⟩) m hm hl xb hxb
    have e3 := gRA_teich AI LL g xb
    rw [e2] at e3
    exact e1.trans ((congrArg (gRA AI LL g) e1).trans e3).symm
  obtain ⟨I, hI⟩ := assemble R (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) _
    (φRA LL) (fun g : ↥(GK K) => gRA AI LL (g : GQ l)) (inclR_φRA LL) (fun g => inclR_gRA AI LL g)
    (by rw [P.PD_p]; exact (GlobalTheory.HWL.TensorWitt.main l LL).1) io hπ
    (isUnit_inclR LL _ (εroot_ne_one AI s)) h1 h2
  refine ⟨I, fun c m hm hl hcm xb hxb o ho => ?_⟩
  rw [hI, ← cst_apply, hc]
  exact hu c m hm hl hcm xb hxb o ho

end GlobalTheory.HWL.IoLayer
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open MvPolynomial

namespace GlobalTheory.ExportSeries.Onto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n : ℕ}

def coefLin (lam : D.what₂.Tau → DomWeight n) : Pol ℂ D.what₂.Tau n →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam F
  map_add' F G := by
    funext x
    simp only [coefFn, map_add (f := _), mul_add, Pi.add_apply]
  map_smul' c F := by
    funext x
    simp only [coefFn, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem coefFn_actP (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Pol ℂ D.what₂.Tau n →+* Pol ℂ D.what₂.Tau n) =
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

theorem invTrK_invTrK (g : GLR D n) : invTrK (invTrK g) = g := by
  funext τ
  exact Units.ext rfl

theorem map_harm_eq (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) :
    (harm m w B).map (harmFn m w B) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  obtain ⟨s, hs⟩ := GlobalTheory.T.fockMinorProduct_eq_sign_dualWeylExtremalVector D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have h1 : {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} =
      ((VV ℂ w.lam).map (coefLin w.lam) : Set (GLR D n → ℂ)) := by
    ext φ
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨F, F.2, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact ⟨⟨F, hF⟩, rfl⟩
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  rw [h1, Submodule.span_eq, GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩

end GlobalTheory.ExportSeries.Onto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CoordUnfold




theorem integral_fundamentalDomain_eq_iterated_split : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  intro D r m s t J K L M hLJ hLK hMJ hMK hJLKM μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D s m
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D t m
  obtain ⟨l1, l2, l3, l4, l5, KK, hKK, hKKc⟩ := GlobalTheory.MixModel.lattice_Mx D r m
  haveI : BorelSpace (Mx D s m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r m) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D s m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D t m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D r m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ.1
  haveI := hν.1
  haveI := hη.1
  haveI : IsFiniteMeasure (ν.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓥) := ⟨by rw [Measure.restrict_apply_univ, hη.2.2]; exact ENNReal.one_lt_top⟩
  set rJ : Mx D r s := J.map (incA D) with hrJ
  set rK : Mx D r t := K.map (incA D) with hrK
  set rL : Mx D s r := L.map (incA D) with hrL
  set rM : Mx D t r := M.map (incA D) with hrM
  have hLJ' : rL * rJ = 1 := by rw [hrL, hrJ, ← Matrix.map_mul, hLJ]; exact GlobalTheory.MixModel.rat_one
  have hLK' : rL * rK = 0 := by rw [hrL, hrK, ← Matrix.map_mul, hLK]; exact GlobalTheory.MixModel.rat_zero
  have hMJ' : rM * rJ = 0 := by rw [hrM, hrJ, ← Matrix.map_mul, hMJ]; exact GlobalTheory.MixModel.rat_zero
  have hMK' : rM * rK = 1 := by rw [hrM, hrK, ← Matrix.map_mul, hMK]; exact GlobalTheory.MixModel.rat_one
  have hJLKM' : rJ * rL + rK * rM = 1 := by
    rw [hrJ, hrL, hrK, hrM, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add (f := _), hJLKM]
    · exact GlobalTheory.MixModel.rat_one
    · exact fun a b => map_add (incA D) a b
  let Ec : (Mx D t m × Mx D s m) ≃ₜ+ Mx D r m :=
    { toFun := fun p => rJ * p.2 + rK * p.1
      invFun := fun u => (rM * u, rL * u)
      left_inv := by
        rintro ⟨v, y⟩
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', hMJ', hMK', Matrix.one_mul, Matrix.zero_mul,
          add_zero, zero_add]
      right_inv := by
        intro u
        show rJ * (rL * u) + rK * (rM * u) = u
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hJLKM', Matrix.one_mul]
      map_add' := by
        rintro ⟨v, y⟩ ⟨v', y'⟩
        simp only [Prod.mk_add_mk, Matrix.mul_add]
        abel
      continuous_toFun := ((continuous_const.matrix_mul continuous_snd).add (continuous_const.matrix_mul continuous_fst))
      continuous_invFun := (continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id) }
  have hEapp : ∀ v y, Ec (v, y) = rJ * y + rK * v := fun _ _ => rfl
  let Me : (Mx D t m × Mx D s m) ≃ᵐ Mx D r m := Ec.toHomeomorph.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl
  set lam : Measure (Mx D t m × Mx D s m) := η.prod ν with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set mm : Measure (Mx D r m) := lam.map Me with hm
  haveI : mm.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hμm := Measure.isAddLeftInvariant_eq_smul μ mm
  set c := Measure.addHaarScalarFactor μ mm with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ mm
  set Γ : AddSubgroup (Mx D t m × Mx D s m) :=
    (GlobalTheory.MixModel.ratMx D t m).prod (GlobalTheory.MixModel.ratMx D s m) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ GlobalTheory.MixModel.ratMx D r m := by
    rintro ⟨v, y⟩
    rw [hEapp]
    simp only [Γ, AddSubgroup.mem_prod]
    constructor
    · rintro ⟨hv, hy⟩
      exact add_mem (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem J) hy)
        (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem K) hv)
    · intro h
      have h1 : rM * (rJ * y + rK * v) = v := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hMJ', hMK', Matrix.one_mul, Matrix.zero_mul, zero_add]
      have h2 : rL * (rJ * y + rK * v) = y := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', Matrix.one_mul, Matrix.zero_mul, add_zero]
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h
      · rw [← h2]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem L) h
  have hFDP : IsAddFundamentalDomain Γ (𝓥 ×ˢ 𝓨) lam := isAddFundamentalDomain_prod hη.2.1 hν.2.1
  have hac : lam.map Me ≪ μ := by
    intro A hA
    rw [hμm, Measure.smul_apply] at hA
    exact (smul_eq_zero.1 hA).resolve_left hc.ne'
  have hqmp : Measure.QuasiMeasurePreserving Me lam μ := ⟨Me.measurable.aemeasurable, hac⟩
  let eΓ : GlobalTheory.MixModel.ratMx D r m → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    hμ.2.1.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : Mx D r m) + Me p
      rw [hMe, hMe, map_add (f := _), Ec.apply_symm_apply])
  refine ⟨(c : ℝ), fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hKK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂μ = (c : ℝ) • ∫ u in 𝓕, T u ∂mm := by
    rw [hμm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂mm = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓥 ×ˢ 𝓨, T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add (f := _)]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓥 ×ˢ 𝓨) = (η.restrict 𝓥).prod (ν.restrict 𝓨) := by
    rw [Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  rfl

end GlobalTheory.CoordUnfold

end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

open GlobalTheory.SignedHC

theorem e_add_v_two_pos {R : Ranks} (P : HCParam R) (s ga : ℕ) (c : ℕ → ℤ) (j : Fin R.m) :
    0 < P.e j + ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
  obtain ⟨hv, hb, -⟩ := GridData.ofHCParam_spec P s ga c
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 : (GridData.ofHCParam P s ga c).v (R.k - 2 + 2) < (GridData.ofHCParam P s ga c).v 2 :=
    (GridData.ofHCParam P s ga c).v_anti 2 _ le_rfl (by omega) (show R.k - 2 + 2 ≤ R.k by omega)
  have h2 : (GridData.ofHCParam P s ga c).b (0 + 1) ≤ (GridData.ofHCParam P s ga c).b (j.1 + 1) := by
    rcases Nat.eq_zero_or_pos j.1 with h | h
    · rw [h]
    · exact ((GridData.ofHCParam P s ga c).b_mono _ _ le_rfl (by omega) (show j.1 + 1 ≤ R.m from j.2)).le
  have h1' : P.v ⟨R.k - 2, by omega⟩ < ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
    rw [hv]; exact_mod_cast h1
  have h2' : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rw [hb, hb]; exact_mod_cast h2
  have h3 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h4 := P.u_last_gt (by omega) (by omega)
  have h5 : P.u ⟨R.k - 2 + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ := by
    congr 2; omega
  have h6 := P.gap_be j
  have h7 : (0 : ℚ) ≤ R.t := by positivity
  simp only at h3
  linarith

theorem nFun_eq_bigN (D : D7) : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.Grid.bigN D := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have h : Odd (D.R.r + 6) := by
    rw [Nat.odd_iff]; unfold Ranks.r; omega
  simp only [BlochKatoReduction.Gen.NFun, BlochKatoReduction.Gen.sFun, if_pos h, GlobalTheory.Grid.bigN, GlobalTheory.Grid.sLen]

end GlobalTheory.LamTie
end
