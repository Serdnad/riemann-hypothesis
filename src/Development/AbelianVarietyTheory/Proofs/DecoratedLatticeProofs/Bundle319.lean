module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle179
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle248
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle311
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle142
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle267
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle041
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem mul_mem_sfin (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) {n : X.B.I.Gf} (hn : n ∈ X.NfinU u)
    {g : X.B.I.Gf} (hg : g ∈ Hfin X u) : n * g ∈ SfinU X u := by
  have hfix : ∀ y ∈ fixSet X u, X.B.I.fmat g *ᵥ incl X.B.I y = incl X.B.I y := hg
  have hm : X.B.I.fmat (n * g) = X.B.I.fmat n * X.B.I.fmat g := by simp [Formalism.MainNotions.S.AutInst.fmat]
  have key : ∀ y ∈ fixSet X u,
      (X.B.I.fmat (n * g) - 1) *ᵥ incl X.B.I y = (X.B.I.fmat n - 1) *ᵥ incl X.B.I y := by
    intro y hy
    rw [hm, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hfix y hy]
  refine ⟨fun a => ?_, ?_⟩
  · rw [key _ (Or.inl (Or.inl ⟨a, rfl⟩))]; exact hn.1 a
  · rw [key _ (Or.inr rfl)]; exact hn.2.1

theorem ph_supp (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (x : X.B.I.GA)
    (hx : Ph X u hK T x ≠ 0) : ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
  unfold Ph at hx
  split_ifs at hx with hd
  · obtain ⟨n, g, k, hdec⟩ := hd
    obtain ⟨hn, hk, he⟩ := hdec
    exact ⟨n * (g : X.B.I.Gf), mul_mem_sfin X u hn g.2, k, hk, he⟩
  · exact absurd rfl hx

end GlobalTheory.Core.MiFold

namespace GlobalTheory.Core.MiFold

open scoped ENNReal

variable {D : D7}

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  simp only [psiBes, psiE]; exact hψ.2.1 _

theorem iota_mul_assoc (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ s : GA D (D.sp.Y 0)) (y : X.B.I.Ginf) (x : X.B.I.Gf) :
    iotaX X h (γ * s) * (y, x) = iotaX X h γ * (iotaX X h s * (y, x)) := by
  rw [map_mul]
  exact mul_assoc _ _ _

end GlobalTheory.Core.MiFold



open GlobalTheory.Core.MiFold in
theorem GlobalTheory.Core.Mi.unfoldedPer : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter), IsStdChar D ψ (-1) → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℂ, ∀ (T : Cu X u hK), IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) ∧ ∀ f : X.B.I.GA → ℂ, RowFun X f → ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u) := by
  intro D X h u ψ A B hK hψ Fs hFs
  obtain ⟨𝓢, h𝓢, h𝓢fin, hI⟩ := (GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D D.R.rS B.lev).2.2.2
  obtain ⟨c, hc, hQ⟩ := GlobalTheory.T.fold_integral_besselQuotient_supportedFunctions D X h u ψ A B 𝓢 h𝓢 Fs hFs
  refine ⟨(c : ℂ), fun T => ?_⟩
  have hPh := Formalism.L2.SG.PoincareInHH.Cut.phProps_closed X u hK (Formalism.L2.SG.Pf.ksetSplit_holds X u)
    (Formalism.L2.SG.Pf.unipotent_in_level X u) (Formalism.L2.SG.Pf.ratLevi_holds X u) (Formalism.L2.SG.Pf.psiProd_holds X u) T
  have hgrp := GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B
  have hph := GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T

  set Φ : X.B.I.Ginf → besGrp B.d B.o → X.B.I.GA := fun y s => iotaX X h s.1 * (y, X.xu u) with hΦdef
  have hι : Continuous fun s : besGrp B.d B.o => iotaX X h s.1 := (iotaX X h).continuous.comp continuous_subtype_val
  have hΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).1 * p.1 :=
      ((continuous_fst.comp hι).measurable.comp measurable_snd).mul measurable_fst
    have h2 : Measurable fun p : X.B.I.Ginf × besGrp B.d B.o => (iotaX X h p.2.1).2 * X.xu u :=
      ((continuous_snd.comp hι).measurable.comp measurable_snd).mul_const _
    exact h1.prodMk h2

  obtain ⟨C, hC⟩ := GlobalTheory.T.bessel_column_scalar_form_norm_bound D X h u ψ A B hK T
  have hbd : ∀ y (s : besGrp B.d B.o), ‖Ph X u hK T (Φ y s)‖ ≤ C * ‖X.Wu u y‖ := by
    intro y s
    obtain ⟨n, hn, a, ha⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s.1).1 s.2
    simp only [hΦdef, ha, hph.2 n hn a y, norm_mul, norm_star, norm_psiBes hψ.1, one_mul]
    exact hC _ _
  have hWu : ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) < ⊤ := (X.Wu_spec u).2.2.2.1
  have hfin : ∀ K : ℝ, 0 ≤ K → ∀ G : X.B.I.GA → ℂ, (∀ x, ‖G x‖ ≤ K * ‖Ph X u hK T x‖) →
      ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u) < ⊤ := by
    intro K hK0 G hG
    have hpt : ∀ y (s : besGrp B.d B.o), ‖G (Φ y s)‖ₑ ≤ ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ := by
      intro y s
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ((hG _).trans ?_)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hbd y s).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))) hK0
    calc ∫⁻ y, ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ∂(X.nuQ u)
        ≤ ∫⁻ y, B.lev.μR 𝓢 * (ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ) ∂(X.nuQ u) := by
          refine lintegral_mono fun y => ?_
          calc ∫⁻ s in 𝓢, ‖G (Φ y s)‖ₑ ∂B.lev.μR ≤ ∫⁻ s in 𝓢, ENNReal.ofReal (K * |C|) * ‖X.Wu u y‖ₑ ∂B.lev.μR :=
                lintegral_mono fun s => hpt y s
            _ = _ := by rw [setLIntegral_const, mul_comm]
      _ = B.lev.μR 𝓢 * ENNReal.ofReal (K * |C|) * ∫⁻ y, ‖X.Wu u y‖ₑ ∂(X.nuQ u) := by
          rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top h𝓢fin.ne ENNReal.ofReal_ne_top)]
          simp only [mul_assoc]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top h𝓢fin ENNReal.ofReal_lt_top) hWu

  set P : (X.B.I.GA → ENNReal) → Prop := fun F => (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) ∧
    (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) ∧
    (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) with hPdef
  have hQ' : ∀ F : X.B.I.GA → ENNReal, Measurable F → P F →
      ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (Φ y s) ∂B.lev.μR ∂(X.nuQ u) :=
    fun F hF hP => hQ F hF hP.1 hP.2.1 hP.2.2
  have hsupp : ∀ G : X.B.I.GA → ℂ, (∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0) → ∀ φ : ℂ → ENNReal, φ 0 = 0 →
      ∀ x, φ (G x) ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k := by
    intro G hG φ hφ x hx
    refine ph_supp X u hK T x (hG x ?_)
    intro h0; rw [h0, hφ] at hx; exact hx rfl
  have hchi : ∀ k ∈ X.K2, ‖X.chi2 k‖ = 1 := hK.2.2.2.2

  have hint : IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) := by
    refine ⟨hPh.1.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hQ' (fun x => ‖Ph X u hK T x‖ₑ) hPh.1.enorm ⟨fun γ hγ x => by dsimp only; rw [hPh.2.1 γ hγ x],
      fun k hk x => by dsimp only; rw [hPh.2.2.1 x k hk, enorm_mul, ← ofReal_norm_eq_enorm (X.chi2 k), hchi k hk,
        ENNReal.ofReal_one, one_mul],
      hsupp (Ph X u hK T) (fun x hx => hx) (fun z => ‖z‖ₑ) enorm_zero⟩]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin 1 zero_le_one _ fun x => by rw [one_mul])
  refine ⟨hint, fun f hf => ?_⟩
  obtain ⟨Cf, hCf⟩ := hf.bdd
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 1)
  have hfm : Measurable f := hf.cont.measurable

  obtain ⟨G, hGdef⟩ : ∃ G : X.B.I.GA → ℂ, G = fun x => f x * Ph X u hK T x := ⟨_, rfl⟩
  have hGl : ∀ γ ∈ Srat X u, ∀ x, G (γ * x) = G x := by
    intro γ hγ x
    simp only [hGdef, hPh.2.1 γ hγ x, hf.left γ (Subgroup.mem_inf.1 hγ).1 x]
  have hGr : ∀ k ∈ X.K2, ∀ x, G (x * (1, k)) = G x := by
    intro k hk x
    have h1 : star (X.chi2 k) * X.chi2 k = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hchi k hk]; norm_num
    simp only [hGdef, hPh.2.2.1 x k hk, hf.right k hk x]
    calc star (X.chi2 k) * f x * (X.chi2 k * Ph X u hK T x) = (star (X.chi2 k) * X.chi2 k) * (f x * Ph X u hK T x) := by ring
      _ = _ := by rw [h1, one_mul]
  have hGs : ∀ x, G x ≠ 0 → Ph X u hK T x ≠ 0 := fun x hx h0 => hx (by simp only [hGdef, h0, mul_zero])
  have hGm : Measurable G := by rw [hGdef]; exact hfm.mul hPh.1
  have hGb : ∀ x, ‖G x‖ ≤ Cf * ‖Ph X u hK T x‖ := fun x => by
    rw [hGdef, norm_mul]; exact mul_le_mul_of_nonneg_right (hCf x) (norm_nonneg _)
  obtain ⟨-, hfold⟩ := GlobalTheory.T.integral_fold_via_lintegral_formula (X.B.I.muA X.B.μf) Fs (X.nuQ u) B.lev.μR 𝓢 h𝓢fin Φ hΦ c hc.le P hQ' G hGm
    (fun φ hφ => ⟨fun γ hγ x => by simp only [hGl γ hγ x], fun k hk x => by simp only [hGr k hk x],
      hsupp G hGs φ hφ⟩) (hfin Cf hCf0 G hGb)
  rw [show (∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf)) = ∫ x in Fs, G x ∂(X.B.I.muA X.B.μf) by rw [hGdef], hfold]
  subst hGdef
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)

  have hcont : ContinuousOn (fun g => f (iotaX X h g * (y, X.xu u)) * Ph X u hK T (iotaX X h g * (y, X.xu u)))
      (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := by
    refine ContinuousOn.mul ?_ (GlobalTheory.T.bessel_column_function_continuousOn_bessel_group D X h u ψ A B hK T y hψ.1)
    exact (hf.cont.comp ((iotaX X h).continuous.mul continuous_const)).continuousOn
  have hinv : ∀ γ ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o,
      f (iotaX X h (γ * s) * (y, X.xu u)) * Ph X u hK T (iotaX X h (γ * s) * (y, X.xu u)) =
        f (iotaX X h s * (y, X.xu u)) * Ph X u hK T (iotaX X h s * (y, X.xu u)) := by
    intro γ hγ s _
    have hγ' := (hgrp.2 γ).1 hγ
    have := hGl _ hγ' (iotaX X h s * (y, X.xu u))
    dsimp only at this
    exact (congrArg (fun z => f z * Ph X u hK T z) (iota_mul_assoc X h γ s y (X.xu u))).trans this
  have hIy := (hI _ hcont hinv).2
  refine hIy.trans ?_
  simp only [BesLev.per, besPer, besFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [hph.2 n.1 n.2 a y]
  ring
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenAvg

theorem exists_central_average_uniform : ∀ (D : D7), BiAct D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A S A' : HSp D)
    (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y →
    k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
    (∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0) →
    ∃ (C₁ : WO A S → WO S A' → ℂ) (χ₁ : GA D A → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ ∧ IsBiSmooth C₁ ∧
      (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) ∧
      ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
        (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) →
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) := by
  intro D hB ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hv hs ⟨φ₀, hφ₀, hc₀, hne⟩
  obtain ⟨χA, χS, ha⟩ := hk₀.weil
  obtain ⟨χS', χA', hb⟩ := hk₀'.weil
  obtain ⟨i1, -, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A
  let Z : Subgroup (GA D A) := GinfC A ⊓ Subgroup.center (GA D A)
  have hcl : IsClosed (Subgroup.center (GA D A) : Set (GA D A)) := by
    have : (Subgroup.center (GA D A) : Set (GA D A)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp ((GlobalTheory.T.isCompact_realPoints_of_definiteHermitianSpaceData D A x hx).inter_right hcl)
  let ν : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hne
  have hh : φ₀ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hc₀ _ b.2.1 b.2.2, hc₀ _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ₀ (h₀ * a) / φ₀ h₀ := by
      funext a
      rw [hc₀ _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ₀.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D A) ∈ GinfC A := fun a => a.2.1
  have hC := GlobalTheory.FrComb.biTheta_of_vac hx.sd hy.sd hz.sd hv hs
  refine ⟨avg k₀.om ν Subtype.val (fun a => χ a) C, fun a => χ a⁻¹,
    isBiVac_avg ν ha hb hB continuous_subtype_val hj hcont hC hv,
    (isBiTheta_avg ν ha hb hB continuous_subtype_val hj hcont hC).smooth, fun a ha1 ha2 v => ?_, ?_⟩
  · funext u
    rw [om_avg ν ha hb hB continuous_subtype_val hj hcont hC]
    let a' : Z := ⟨a, ha1, ha2⟩
    simp only [Pi.smul_apply, smul_eq_mul, avg]
    rw [← integral_const_mul, ← integral_mul_left_eq_self (μ := ν)
      (fun b : Z => χ a⁻¹ * (χ b * k₀.om (b, 1) (fun u' => C u' v) u)) a']
    congr 1
    funext b
    have e : χ a⁻¹ * χ a = 1 := by
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel] at this
      exact this.symm.trans hone
    rw [hmul, ← mul_assoc, ← mul_assoc]
    change _ = χ a⁻¹ * χ a * χ b * k₀.om (a * b, 1) (fun u' => C u' v) u
    rw [e, one_mul]
  intro k k' hk hk' hag φ hφ hcφ
  obtain ⟨χA₁, χS₁, ha₁⟩ := hk.weil
  obtain ⟨χS₁', χA₁', hb₁⟩ := hk'.weil
  have eavg : avg k₀.om ν Subtype.val (fun a => χ a) C = avg k.om ν Subtype.val (fun a => χ a) C := by
    funext u v
    simp only [avg]
    congr 1
    funext a
    rw [hag a a.2.1 1 (GinfC S).one_mem _ (hv.left v).1]
  rw [eavg]
  have hG := GlobalTheory.FrComb.biTheta_combL ha₁.std (GlobalTheory.FrComb.biTheta_combR ha₁.std hC hk'.fin) hk.fin
  rw [biComb_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hC hk.fin hk'.fin]
  change IsBiTheta ψ A S A' (biComb ψ A S A' k.c k'.c C) at hG
  generalize biComb ψ A S A' k.c k'.c C = G at hG
  funext h₂
  unfold biLift
  congr 1
  funext h₁
  have hF : IsContAut A fun h => φ h * k'.om (h₁, h₂) (fun v => k.om (h, h₁) (fun u => G u v) 0) 0 := by
    refine ⟨fun γ hγ g => ?_, hφ.2.mul ?_⟩
    · have : ∀ v, k.om (γ * g, h₁) (fun u => G u v) 0 = k.om (g, h₁) (fun u => G u v) 0 := fun v => by
        rw [← ha₁.om_aut γ hγ 1 (one_mem _) _ (ha₁.om_pres (g, h₁) _ (GlobalTheory.FrComb.slice_left hG v)), ← Module.End.mul_apply,
          ← map_mul, Prod.mk_mul_mk, one_mul]
      simp only [this, hφ.1 γ hγ g]
    · exact (hB ψ A S A' _ _ _ _ _ _ ha₁ hb₁ G hG).2.2.2.comp
        (show Continuous fun h : GA D A => ((h, h₁), (h₁, h₂), (0 : WO A S), (0 : WO S A')) from
          (continuous_id.prodMk continuous_const).prodMk continuous_const)
  rw [← integral_mean ν hx.cpt x.vol continuous_subtype_val hF]
  congr 1
  funext h
  rw [ker_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hG, ← integral_const_mul]
  congr 1
  funext a
  rw [hcφ _ a.2.1 a.2.2]
  ring

end GlobalTheory.CenAvg

namespace GlobalTheory.SeeSaw

theorem fockRed_uniform : ∀ D : D7, BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → k.vac = k₀.vac → k'.vac = k₀'.vac → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → HasCen A χ φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm
  by_cases h0 : ∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0
  · obtain ⟨C₁, χ₁, hC₁, hs₁, he₁, heq₁⟩ :=
      GlobalTheory.CenAvg.exists_central_average_uniform D hBi ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm h0
    obtain ⟨χ₃, h₃⟩ := GlobalTheory.T.realCentre_acts_by_character_on_isotypic_slices D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ C₁ hC₁ he₁
    obtain ⟨C₂, χ₂, hC₂, he₂, hf₂, heq₂⟩ :=
      GlobalTheory.T.exists_uniform_isotypic_average_real_centre D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ hs₁ he₁ h₃
    obtain ⟨n, P, P', hp⟩ := GlobalTheory.T.centralEigen_realDatum_finite_sum_fockProducts D hCF ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₂ C₂ hC₂ he₂ hf₂
    refine ⟨n, P, P', fun k k' hk hk' hv hv' hag hag' φ hφ hcen => ?_⟩
    rw [heq₁ k k' hk hk' hag φ hφ hcen, heq₂ k k' hk hk' hag hag' φ hφ,
      GlobalTheory.T.doubleLift_fockSum_eq_sum_iteratedLifts D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C₂ (by rw [hv, hv']; exact hp) φ hφ]
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k k' _ _ _ _ _ _ φ hφ hcen => ?_⟩
    have e : φ = 0 := by
      by_contra hne
      exact h0 ⟨φ, hφ, hcen, hne⟩
    subst e
    funext h₂
    simp [biLift]

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

namespace GlobalTheory.StabOff



theorem prV_comm_tmul {D : D7} (v : Pl D) (a : Af ↥D.host.F) (e : D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) (a ⊗ₜ e)) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ e)) := by
  rw [Algebra.TensorProduct.comm_tmul]
  simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
  rfl

theorem prV_comm {D : D7} (v : Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e => exact prV_comm_tmul v a e
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_eq_zero {D : D7} (v : Pl D) (y : AE D) (h : FinPl.compAt D v y = 0) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = 0 := by
  unfold FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  refine (prV_comm v z).trans ?_
  rw [h, map_zero]

theorem compAt_mt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (v : Pl D)
    (hv : v ≠ p.v) (i j : Fin S.rank) :
    FinPl.compAt D v (Formalism.L2.Theta.mt S (β.gl g) i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = 0 := by
  have hmem : β.gl g ∈ grpAt S (· = p.v) := ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).1 _).2 ⟨g, rfl⟩
  unfold grpAt congGrp at hmem
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hmem
  have h1 := congrArg (fun u => u.1 i j) hmem
  simp only [GeneralLinearGroup.map_apply, Units.val_one] at h1
  have h2 : Ideal.Quotient.mk (idAt D (· = p.v)) (Formalism.L2.Theta.mt S (β.gl g) i j) =
      Ideal.Quotient.mk (idAt D (· = p.v)) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
    refine h1.trans ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Ideal.Quotient.eq] at h2
  unfold idAt at h2
  rw [Ideal.mem_inf] at h2
  have h3 := h2.2
  rw [Submodule.mem_iInf] at h3
  exact (RingHom.mem_ker).1 (h3 ⟨v, hv⟩)

theorem bc_prV_finM_eq_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k) (m : ℕ) (hm : S.rank = m) (x : GL (Fin m) (EF D)), x.1 = finM S hm (β.gl g) → ∀ v : Pl D, v ≠ p.v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  intro D k _ _ _ _ p S n _ _ β g m hm x hx v hv
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin m) (Fin m) _) i j
  rw [hx]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have h := prV_toEAf_eq_zero v _ (compAt_mt β g v hv ((finCongr hm).symm i) ((finCongr hm).symm j))
  rw [map_sub, map_sub, sub_eq_zero] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply]
  · have hij' : (finCongr hm).symm i ≠ (finCongr hm).symm j := fun e => hij ((finCongr hm).symm.injective e)
    simp [Matrix.one_apply, hij, hij']

end GlobalTheory.StabOff
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem isLattice_of_isLat_selfDual {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p S n) (L : Lat S) (hL : IsSelfDualC S L) (Λ : Submodule 𝒪[k] (n → k)) (h : β.IsLat L Λ) :
    Λ.IsFullLattice k := by
  obtain ⟨Λ₀, h₀, hI, -⟩ := (GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).2.2.2.1 L hL
  have e : Λ = Λ₀ := Submodule.ext fun x => (h x).trans (hI x).symm
  have hlat : Λ.IsLattice k := e ▸ h₀
  refine { toIsLattice := hlat, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
  obtain ⟨m, s, c, hs, hc, -⟩ := GlobalTheory.FinPl.FrameLat.exists_gen (p := p) hL
  have hx := congrArg (β.b' *ᵥ ·) (hc (β.b *ᵥ x))
  simp only [Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec, Matrix.mulVec_sum,
    Matrix.mulVec_smul] at hx
  rw [hx]
  refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  apply (h _).2
  rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
  exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (p := p) (hs l)

theorem latInd_mem_SB_of_selfDual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → latInd ΛS ΛT ∈ SB (Matrix n n' k) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT ΛS ΛT hα hβ
  have := isLattice_of_isLat_selfDual α LS hS ΛS hα
  have := isLattice_of_isLat_selfDual β LT hT ΛT hβ
  exact GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT

end GlobalTheory.FinPl
end
