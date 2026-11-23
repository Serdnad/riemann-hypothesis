module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LowVanishFockOfLowVanish
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle320
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemLevelFunOfIsAutFun
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle315
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle321
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle323
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
import Std.Tactic.BVDecide.Normalize.Bool
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size

namespace GlobalTheory.Chain.LiftConv

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}

theorem thetaKO_left (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) f = thetaKO ω g h f := by
  intro γ hγ h

  have hsplit : ((g, γ * h) : GA D V × GA D W) = (1, γ) * (g, h) := by
    ext <;> simp
  have hpres : IsThetaFunO ψ V W (ω (g, h) f) := hω.om_pres _ _ hf
  unfold thetaKO
  rw [hsplit, map_mul, Module.End.mul_apply]
  exact hω.om_aut 1 (one_mem _) γ hγ _ hpres

theorem thetaKO_continuous (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (g : GA D V) :
    Continuous fun h => thetaKO ω g h f := by

  have hpair : Continuous fun h : GA D W => ((g, h) : GA D V × GA D W) := by fun_prop
  unfold thetaKO
  exact (hω.om_cont f hf 0).comp hpair

theorem thetaKO_modGrowth (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hf : IsThetaFunO ψ V W f) (g : GA D V) : ModGrowth W fun h => thetaKO ω g h f := by
  obtain ⟨A, d, hAd⟩ := hG V.rank W.rank
  obtain ⟨U, hUo, hfU⟩ := GlobalTheory.Size.isTheta_iff_level.mp hf
  obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := (hAd V W rfl rfl).real ψ hθ hUo
  obtain ⟨-, hbd⟩ := hC χS χT ω hω μ 𝓕 hcov f hfU

  refine ⟨C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A, A, fun h => ?_⟩
  have key := hbd g h
  unfold thetaKO
  calc ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := key
    _ = C * (sobO ψ θ μ 𝓕 d f).toReal * height V g ^ A * height W h ^ A := by
      rw [mul_pow]; ring

theorem integrableOn_of_rapidDec (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) {F : GA D W → ℂ} (hF : RapidDec W F) (g : GA D V) :
    IntegrableOn (fun h => thetaKO ω g h f * F h) 𝓕 ν := by
  have hcont := thetaKO_continuous hω hf g
  exact hF.integrableOn_modGrowth_mul hν h𝓕 (thetaKO_modGrowth hG hθ hω hf g)
    (thetaKO_left hω hf g) hcont.aestronglyMeasurable

theorem liftInteg_of_growth (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D) :
    LiftInteg D := by
  intro V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕 f F hf hFs hFc g

  have hdec : RapidDec W F := rapidDec_of_cuspForm hP hθ hFs hFc
  exact integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hdec g

end GlobalTheory.Chain.LiftConv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCreaDir

section Mat

variable {m n : ℕ}

theorem eq_sum_unitMap {Bm : Matrix (Fin m) (Fin m) ℂ} {Am : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit Bm.det)
    (hA : IsUnit Am.det) (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, (Bm⁻¹ * z * Am) i j • Formalism.IndefR.Datum.unitMap Am Bm i j := by
  have e : z = Bm * (Bm⁻¹ * z * Am) * Am⁻¹ := by
    rw [← Matrix.mul_assoc Bm, ← Matrix.mul_assoc Bm, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hA]
  have e2 := Matrix.matrix_eq_sum_single (Bm⁻¹ * z * Am)
  calc z = Bm * (∑ i, ∑ j, Matrix.single i j ((Bm⁻¹ * z * Am) i j)) * Am⁻¹ := by rw [← e2, ← e]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h : Matrix.single i j ((Bm⁻¹ * z * Am) i j) = ((Bm⁻¹ * z * Am) i j) • Matrix.single i j (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [h, Matrix.mul_smul, Matrix.smul_mul, Formalism.IndefR.Datum.unitMap]

theorem Jm_single_Jm (ε : Fin m → Bool) (δ : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm ε * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm δ =
      (if (ε i == δ j) then 1 else -1 : ℂ) • Matrix.single i j (1 : ℂ) := by
  ext p q
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h
    cases ε i <;> cases δ j <;> simp
  · simp [h]

end Mat

open GlobalTheory.ChainFr

variable {D : D7} {V W : HSp D}

theorem cplxO_unitMap_fr (A : Fr V) (B : Fr W) (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) :
    cplxO (A.cart τ) (B.cart τ) (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) =
      ((if (B.ε τ i == A.ε τ j) then 1 else -1 : ℂ) * Complex.I) •
        Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := by
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hB := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have h1 : B.cart τ * B.onb τ = B.onb τ * Formalism.REAL.Jm (B.ε τ) := by
    rw [Fr.cart, Fr.onb, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
  have h2 : (A.onb τ)⁻¹ * A.cart τ = Formalism.REAL.Jm (A.ε τ) * (A.onb τ)⁻¹ := by
    rw [Fr.cart, Fr.onb, Matrix.nonsing_inv_nonsing_inv _ hA]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  unfold cplxO Formalism.IndefR.Datum.unitMap
  rw [mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc B.cart τ * (B.onb τ * Matrix.single i j (1 : ℂ) * (A.onb τ)⁻¹) * A.cart τ
      = (B.cart τ * B.onb τ) * Matrix.single i j (1 : ℂ) * ((A.onb τ)⁻¹ * A.cart τ) := by
        simp only [Matrix.mul_assoc]
    _ = B.onb τ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * (A.onb τ)⁻¹ := by
        rw [h1, h2]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Jm_single_Jm, Matrix.mul_smul, Matrix.smul_mul]

theorem fockScale_ne_zero (D : D7) (τ : D.what₂.Tau) : ((fockScale D τ : ℝ) : ℂ) ≠ 0 := by
  have h0 : 0 < ‖tauE D τ D.host.xi0‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := Formalism.L2.Theta.xi_zero_im_pos D τ
    rw [h] at this
    simp at this
  have : 0 < fockScale D τ := by
    unfold fockScale
    have := Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) h0)
    positivity
  exact_mod_cast this.ne'

end GlobalTheory.FockCreaDir


open GlobalTheory.FockCreaDir in
theorem GlobalTheory.FockCreaDir.crea_ptF : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  intro D V W A B θ ψ hψ hθ f hf τ z P
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v
        (pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ V W) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ V W (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ V W) hadd hsm hth hf P
  have hdA : IsUnit (A.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  have hdB : IsUnit (B.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  obtain ⟨c, rfl⟩ : ∃ c : Fin W.rank → Fin V.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := ⟨_, eq_sum_unitMap hdB hdA z⟩
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), ?_⟩
  have h1 : ∀ (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) g,
      crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g := fun y g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : GlobalTheory.ChainFr.ptF ψ θ A B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ))
          (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) (GlobalTheory.ChainFr.ptF ψ θ A B f P) := by
    unfold GlobalTheory.ChainFr.ptF pureTensorO

    simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg (B.ε τ i == A.ε τ j) _ (cplxO_unitMap_fr A B τ i j)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_realFrameElement_le_hsPow : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau), ∃ (C : ℝ) (m : ℕ), ∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), GlobalTheory.Grow.height V (A.elt θ τ g) ≤ C * (1 + Formalism.REAL.hs g) ^ m := by
  first | exact @GlobalTheory.FrameHeight.height_elt_le | exact GlobalTheory.FrameHeight.height_elt_le | (intros; apply GlobalTheory.FrameHeight.height_elt_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SrcHalfOne
open GlobalTheory.EmbChart (tensAt atPlace)
open GlobalTheory.AdelicU (splitProj compFin isCMExt_host)
variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := Formalism.L2.Theta.cA_cA z
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]; rfl

theorem compFin_cA (z : AE D) : compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_cA_idem : piW τ (cA D (idem τ)) = 0 :=
  ((chart_piW τ).2.1 _).2 (GlobalTheory.EmbChart.isSplitIdem_idem τ).2.1

theorem piW_idem : piW τ (idem τ) = 1 := by
  change splitProj τ (compFin _ _ v (idem τ)) = 1
  rw [GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]

theorem piW_alg (a : Fv D.host.F v) : piW τ (algebraMap (AF D.host.F) (AE D) (atPlace v a)) = a := by
  rw [(chart_piW τ).2.2.1]
  exact GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem piW_cA (z : AE D) : piW τ (cA D z) = splitProj (τ.comp D.sp.cm.sig) (compFin D.host.F D.host.E v z) := by
  change splitProj τ (compFin _ _ v (cA D z)) = _
  rw [compFin_cA, GlobalTheory.AdelicU.splitProj_comp]

def plcC (y : Fv D.host.F v) : AE D := cA D (idem τ) * algebraMap (AF D.host.F) (AE D) (atPlace v y)

theorem piW_plcC (y) : piW τ (plcC τ y) = 0 := by rw [plcC, map_mul, piW_cA_idem, zero_mul]
theorem piW_cA_plcC (y) : piW τ (cA D (plcC τ y)) = y := by
  rw [plcC, map_mul, cA_cA', cA_alg, map_mul, piW_idem, piW_alg, one_mul]

theorem idem_mul_self : idem τ * idem τ = idem τ := (GlobalTheory.EmbChart.isSplitIdem_idem τ).1

section Frame

variable (V : HSp D) {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

end Frame

section FJ

variable {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {n : Type} [Fintype n] [DecidableEq n]
  {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)}
  {t : ℕ → Fv D.host.F v}

variable {τ}

open GlobalTheory.RootEx (colE rowE)

variable (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t)
include hβ

end FJ

section Jac

variable {V V₀ L : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E)

end Jac
end GlobalTheory.SrcHalfOne
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tendsto_moderateGrowthSize_translate_near_one : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 1 N φ ≠ ⊤ → Filter.Tendsto (fun u : Matrix (Fin V.rank) (Fin V.rank) ℂ => GlobalTheory.Size.growthSize V N (rTr V (atTau θ V τ u) φ - φ)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (nhds 0) := by
  first | exact @GlobalTheory.Size.NearOne.tendsto_growthSize_translate | exact GlobalTheory.Size.NearOne.tendsto_growthSize_translate | (intros; apply GlobalTheory.Size.NearOne.tendsto_growthSize_translate <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjLiftHecke

variable {D : D7}

theorem theta_form_conj {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {P : Pl D.host.E} (hW : IsWeilDatumO ψ S T χS χT om)
    (hs : S.SigOK) (hp : S.IsPosDef) {Kf : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {ν : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hν : IsMeasDef S Kf ν 𝓕) (hfix : GlobalTheory.Hk3.VacFix ψ om P) {cS cT : List ℤ →₀ ℂ}
    (hM : GlobalTheory.Hk3.Match ψ om P (GlobalTheory.Hk3.dualC cS) cT) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    (hG : ∀ k ∈ GlobalTheory.Hk3.hyp S P, k ∈ GfC S) {f f' : Bridge.Gf S → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (hsph : ∀ k ∈ GlobalTheory.Hk3.hyp S P, ∀ h, f (h * (finHom S).rangeRestrict k) = f h) (hf' : f' = GlobalTheory.Hk3.hkF S P cS f)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ φ, GlobalTheory.Hk3.IsVacAt ψ S T P (pt φ))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {u u' : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f h))) ∂ν)
    (hu' : ∀ g, u' g = ∫ h in 𝓕, thetaKO om h g (pt (io (c.ext f' h))) ∂ν) : u' = GlobalTheory.Hk3.hk T P cT u := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  funext g
  have key := GlobalTheory.DefLiftHecke.theta_comb hW hpos hν.1.1 hν.2 hfix hM (pt ∘ₗ io) (fun w => hpt _) (c.ext f)
    (GlobalTheory.ConjThetaIntegral.ext_continuous c hc β L χ' hχ hf) (GlobalTheory.ThetaIntegrand.ext_invariant c hf)
    (fun k hk h => by
      rw [GlobalTheory.DefLiftHecke.ext_mul c hc f (hG k hk) h, hsph k hk]
      rfl) g
  rw [hu', funext hu, hf']
  simp only [GlobalTheory.DefLiftHecke.ext_hkF c hc]
  exact key

theorem theta_right_hyp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {P : Pl D.host.E} (hfix : GlobalTheory.Hk3.VacFix ψ om P) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)}
    {φ : GA D S → (WO S T → ℂ)} (hφ : ∀ h, GlobalTheory.Hk3.IsVacAt ψ S T P (φ h)) {u : GA D T → ℂ}
    (hu : ∀ g, u g = ∫ h in 𝓕, thetaKO om h g (φ h) ∂ν) : ∀ k ∈ GlobalTheory.Hk3.hyp T P, ∀ g, u (g * k) = u g := by
  intro k hk g
  rw [hu, hu]
  refine congrArg (fun w : GA D S → ℂ => ∫ h in 𝓕, w h ∂ν) (funext fun h => ?_)
  unfold thetaKO
  rw [show ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) by simp, map_mul, Module.End.mul_apply,
    hfix _ (hφ h) 1 (GlobalTheory.DefLiftHecke.one_mem_hyp _ P) k hk]

theorem gaL_hk_of_hyp {G : Type} [Group G] [Fintype G] {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (eG : G ≃* G0 L.Pg L.r) (z : G → ℂ) (c : List ℤ →₀ ℂ) {Φ : GA D V → ℂ}
    (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    gaL V β L eG z (GlobalTheory.Hk3.hk V P c Φ) = GlobalTheory.Hk3.hk V P c (gaL V β L eG z Φ) := by
  obtain ⟨n, hB⟩ := hβ
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.LevOp.level_operators V β Λ _ L hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP
  exact GlobalTheory.DefLiftHecke.gaL_hk eG z fun g0 => h4 c g0 _ hΦ

theorem eq_of_eval {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {Hh : Type} [NormedAddCommGroup Hh]
    [InnerProductSpace ℂ Hh] (e : Hh →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hip : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) {Wa : Submodule ℂ (MMap M)} (hr : LinearMap.range e = Wa)
    (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) {a : Hh} {U : MMap M} (hU : U ∈ Wa) (h : e a v = U v) : e a = U := by
  rw [← hr] at hU
  obtain ⟨b, rfl⟩ := hU
  exact congrArg e (GlobalTheory.EvalAtUnitVector.eval_injective M Hh e d μ 𝓕 hip v hv h)


theorem lift_match : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ω f₀ f B io thP, GlobalTheory.GalLift.LiftData R i σ μ' η' c H ω f₀ f B io thP → GlobalTheory.GalLift.IsProjOf R i σ thP th → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.VacFix R.ψ ω P → ∀ cV cW, GlobalTheory.Hk3.Match R.ψ ω P (GlobalTheory.Hk3.dualC cV) cW → ∀ y y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) → (R.HW i σ).e (th y') = postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L hT i σ c c₁ H j hK hj μ' η' th ω f₀ f B io thP hD hPr P hG hfix cV cW hM y y' hy
  have hW := hD.1
  have hV := hD.2.1
  have hIo := hD.2.2.1
  have hTh := hD.2.2.2
  refine hj.model.elim fun χ' hm => ?_
  have hχ := hm.1
  have hH := hm.2
  have hvac := GlobalTheory.T.conjugateDatum_fockVectors_isVacuum_off_level R hC.lev hC.models.inf i σ f₀ f B hV P hG
  have hform : ∀ x, H.e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).J χ' :=
    fun x => hH.2.1.le (LinearMap.mem_range_self _ x)
  have hχ1 : ∀ k, (levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k = 1 → χ' k = 1 := fun k hk =>
    Units.ext (GlobalTheory.ConjThetaIntegral.conjVal_one (hχ k) (congrArg Units.val hk))
  have hsph := (GlobalTheory.ConjSph.conjForms_spherical R hC.lev i σ c c₁ H j _ hj P hG cV y).1
  refine (hC.lev.βV i).elim fun nV hBV => ?_
  have hlevV := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (R.datVt i A.μ0) hBV P
    (GlobalTheory.DefLiftHecke.one_pow_notMem P nV) hG).1
  have hStep : ∀ w : LowT (R.MW i σ), thP ((c.ext ∘ₗ H.e).rangeRestrict y') w =
      GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w) := fun w => by
    refine theta_form_conj hW (D.sp.V_sig _) (hC.models.vpos i) (hC.models.νV i A.μ0) hfix hM c hj.coef (R.βV i)
      (R.datVt i A.μ0) χ' hχ1 (fun k hk => (hlevV k hk).1.1) (hform y) hsph hy
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) hvac (io w)
      (fun g => hTh.eq _ w g) (fun g => hTh.eq _ w g)
  have hWinv : ∀ (w : LowT (R.MW i σ)), ∀ k ∈ GlobalTheory.Hk3.hyp (Wc D i) P, ∀ g,
      thP ((c.ext ∘ₗ H.e).rangeRestrict y) w (g * k) = thP ((c.ext ∘ₗ H.e).rangeRestrict y) w g := fun w =>
    theta_right_hyp hfix (fun h => hvac _) (fun g => hTh.eq _ w g)
  have hGW : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P :=
    fun PP h => hG PP (h.imp_right fun h => absurd h (Finset.notMem_empty _))
  have hcomm : ∀ w : LowT (R.MW i σ), R.eWf i σ (GlobalTheory.Hk3.hk (Wc D i) P cW (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) =
      GlobalTheory.Hk3.hk (Wc D i) P cW (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict y) w)) := fun w =>
    gaL_hk_of_hyp (hC.lev.βW i) hGW R.eG _ cW (hWinv w)
  have hmod := hC.models.HW i σ
  have hU : (R.HW i σ).e (th y) ∈ R.Wall i σ := hmod.2.1.le (LinearMap.mem_range_self _ _)
  have hU' : postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P cW) ((R.HW i σ).e (th y)) ∈ R.Wall i σ :=
    (GlobalTheory.DefLiftHecke.mult_laws hC.models.inf (R.MW i σ) (hC.lev.βW i) (L := R.datWp i R.triv) hGW R.eG
      (RealDat.eC (A := A) σ) cW hU).1
  refine hIo.2.2.elim fun v hv => hv.elim fun _ hw => ?_
  refine eq_of_eval (R.MW i σ) (R.HW i σ).e _ (R.νW i) (R.fdW i) hmod.2.2 hmod.2.1 (fun ρ => v ρ) hw.1 hU' ?_
  exact (hPr y' v).trans ((congrArg (R.eWf i σ) (hStep _)).trans ((hcomm _).trans
    ((congrArg (GlobalTheory.Hk3.hk (Wc D i) P cW) (hPr y v).symm).trans (postOn_apply _ _ _ _).symm)))

end GlobalTheory.ConjLiftHecke
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.supNormWordSum_sub_le_and_derivative_cost : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → (∀ (G H : WO V W → ℂ) (c : ℂ) (k : ℕ), IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (G - c • H) ≤ GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G + ‖c‖ₑ * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k H) ∧ ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E), ∃ c : ℝ, 0 ≤ c ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ k : ℕ, GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (derAlong ψ θ V W C x G) ≤ ENNReal.ofReal c * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (k + 1) G := by
  first | exact @GlobalTheory.Size.SupWord.wordSum_sup_sub_and_derAlong | exact GlobalTheory.Size.SupWord.wordSum_sup_sub_and_derAlong | (intros; apply GlobalTheory.Size.SupWord.wordSum_sup_sub_and_derAlong <;> assumption)
end
