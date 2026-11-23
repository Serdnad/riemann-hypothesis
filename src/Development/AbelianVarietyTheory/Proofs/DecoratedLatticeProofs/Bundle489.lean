module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PointMapLinearity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle399
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle477
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle448
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle467
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle478
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.WeylFourier

variable {D : D7}

theorem extX_mul_weyl {A B : HSp D} {w : GA D (dblSp A)} {b c : AE D}
    (hX : mt (dblSp A) w ⬝ (dblDec A).jX = -(b • (dblDec A).jY))
    (hY : mt (dblSp A) w ⬝ (dblDec A).jY = c • (dblDec A).jX) (x : Mx D B.rank A.rank) :
    (dblDec A).extX B x ⬝ mt (dblSp A) w = (dblDec A).extY B (c • x) := by
  refine (dblDec A).mat_ext ?_ (Matrix.ext fun _ j => Fin.elim0 j) ?_
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hX, Matrix.mul_neg, Matrix.mul_smul]
    rw [(dblDec A).pX_jY, (dblDec A).pY_jX, Matrix.mul_zero, Matrix.mul_zero, smul_zero, neg_zero]
  · simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, hY, Matrix.mul_smul]
    rw [(dblDec A).pX_jX, (dblDec A).pY_jY, Matrix.mul_one, Matrix.mul_one]

theorem symplO_extX_extY_smul {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : AE D) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T y) (d.extY T (c • x)) =
      trA (incA D D.host.xi0 * cA D c * Matrix.trace (GlobalTheory.StdUnn.inner T x y)) := by
  have h := d.hO_ext T y 0 0 (c • x) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, Matrix.trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS, adj_smul,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc]
  rfl

theorem sch_weyl : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ w : GA D (dblSp A), IsWeyl A w → mt (dblSp A) w ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) → mt (dblSp A) w ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x, sch ψ A B ν 𝓨 (omh (w, 1) f) x = ∫ y, sch ψ A B ν 𝓨 f y * ψ (trA (incA D (-D.host.xi0 / μ) * Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  intro D ψ A B χB omh hW ν 𝓨 hν μ hμ w hw hX hY f hf x
  set u : WO (dblSp A) B := (dblDec A).extY B (incA D μ⁻¹ • x) with hu
  have hact : actO (dblSp A) B w 1 u = (dblDec A).extX B x := by
    rw [actO_eq, mt_one, Matrix.one_mul, hu, ← extX_mul_weyl hX hY x, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]
  have hf₁ : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B u f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hW.std (dblSp A) B).1 u f hf
  have h1 : sch ψ A B ν 𝓨 (omh (w, 1) f) x = swSec A B omh ν 𝓨 (heisO ψ (dblSp A) B u f) w := by
    have h := congrFun (GlobalTheory.MixModel.Check.mixS_heis_extX (ψ := ψ) (dblDec A) ν 𝓨 (omh (w, 1) f) x 0) 0
    rw [zero_add, ← hact, ← hW.om_heis w 1 u f hf, mixS_dblDec_zero] at h
    exact h.symm
  rw [h1, GlobalTheory.T.siegelSection_weylElement_eq_schrodingerIntegral D ψ A B χB omh hW ν 𝓨 hν _ hf₁ w hw]
  refine congrArg _ (funext fun y => ?_)
  have hc : incA D D.host.xi0 * cA D (incA D μ⁻¹) = incA D (-D.host.xi0 / μ) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_inv₀, hμ.2, inv_neg, mul_neg, neg_div, div_eq_mul_inv]
  have h2 := GlobalTheory.MixModel.Check.mixS_heis_extY (dblDec A) hν hf (incA D μ⁻¹ • x) y 0
  rw [symplO_extX_extY_smul, hc, mul_comm] at h2
  exact h2

end GlobalTheory.StdUnn.WeylFourier

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
open GlobalTheory.LiftRows (Given)

noncomputable section
namespace GlobalTheory.ChainTw.UnifFree

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem mu_ratio (t t' : T) (i j : ℕ) :
    (comR R t).μ i * ((comR R t).μ j)⁻¹ = (comR R t').μ i * ((comR R t').μ j)⁻¹ := by
  show R.mu0 i * R.xi t * (R.mu0 j * R.xi t)⁻¹ = R.mu0 i * R.xi t' * (R.mu0 j * R.xi t')⁻¹
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_right_eq_div, mul_div_mul_right_eq_div]

theorem isHval_tuple {t t' : T} {S : Set (HeightOneSpectrum (𝓞 D.host.F))} {k : ℕ} {H : ℂ}
    (h : IsHval (comR R t) S k H) : IsHval (comR R t') S k H := by
  obtain ⟨Λ, h1, h2⟩ := h
  refine ⟨Λ, fun i hi => ⟨(h1 i hi).1, fun z hz => ?_⟩, h2⟩
  rw [(h1 i hi).2 z hz, mu_ratio R t t' i (k + 1)]

theorem ipTh_self {V W : HSp D} (m : Measure (WO V W)) (X : Set (WO V W)) (f : WO V W → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = ((nrm2 m X f : ℝ) : ℂ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  show f w * (starRingEnd ℂ) (f w) = _
  rw [Complex.mul_conj']
  push_cast
  ring

theorem unifY (hL : R.toLevCh.Is A.μ0) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hZ : RealZetaQ D) (hRs : Restore D)
    (h : RangeX R) (hC : RChain R h) (hM : RMeas R) (hV : RVol R) (hN : RNrm R) (k : ℕ) (hk : k + 1 < D.R.m) :
    ∃ (K : ℂ) (φ : PolF D (Yc D (k + 1)).rank (Yc D k).rank) (v : (R.MY k).Vec),
      IsUnif R k (fun t => stY R t k) (fun t => stY R t (k + 1)) (fun t => stepY R t k) K (fun _ => φ) fun _ => v := by
  have hk' : k < D.R.m := by omega
  have hw : ∀ t, (twR R t).Is (comR R t) := fun t => (hC t).1
  have hs : ∀ t, IsStage (comR R t) (twR R t) k (stY R t k) := fun t => (hC t).2.1 k hk'
  have hs' : ∀ t, IsStage (comR R t) (twR R t) (k + 1) (stY R t (k + 1)) := fun t => (hC t).2.1 (k + 1) hk
  have hp : ∀ t, IsStep (twR R t) (k + 1) (stepY R t k) := fun t => (hC t).2.2.2.1 k hk
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne (Yc D k) (Yc D (k + 1))
  obtain ⟨φ, v, hφv⟩ := hZ hG _ _ (hw A.μ0) k hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0) m X hX
  obtain ⟨mR, hmR⟩ := hM k hk'
  obtain ⟨-, ⟨H₀, hH0, hH⟩, hd, -⟩ := hRs hG _ _ (hw A.μ0) k hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0)
  have ev : ∀ t, GlobalTheory.PairLift.IsWeilExp R.ψ (Yc D k) (Yc D (k + 1)) (GlobalTheory.Chain.expS D ⟨k, hk'⟩) (GlobalTheory.Chain.expT D ⟨k, hk'⟩) (R.ωY t k) ∧
      GlobalTheory.Chain.IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k) := fun t =>
    GlobalTheory.ChainTw.StepExpTw.twStepExpVac D hG _ _ (hw t) k hk' _ _ (hs t) (hs' t) _ (hp t) hk'
  have hθ : IsInfFam R.θ := (hw A.μ0).com.inf
  have hn : ∀ t, ((nrm2 m X (R.vY t k) : ℝ) : ℂ) ≠ 0 := fun t => by
    rw [← ipTh_self]
    exact (GlobalTheory.FockProdCoef.ipTh_ptOf_glue D _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ _ _ (R.ωY t k) hθ (hp t).weil
      m X hX _ (ev t).2).1
  have key : ∀ t (g : GinfC (Yc D k)), zReal (stepY R t k) m X φ v g * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
      zReal (stepY R A.μ0 k) m X φ v g * (nrm2 m X (R.vY t k) : ℂ) := fun t g => by
    have e : coefW (stepY R t k).ω m X ((stepY R t k).pt φ) (g : GA D (Yc D k)) * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
        coefW (stepY R A.μ0 k).ω m X ((stepY R A.μ0 k).pt φ) (g : GA D (Yc D k)) * (nrm2 m X (R.vY t k) : ℂ) :=
      GlobalTheory.FockCoefIndep.coef_indep_exponents D ⟨k, hk'⟩ _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ (R.ωY t k) (R.ωY A.μ0 k)
        (R.vY t k) (R.vY A.μ0 k) hθ (ev t).1 (ev A.μ0).1 (ev t).2 (ev A.μ0).2 m X hX φ g g.2
    unfold zReal
    (rw [mul_right_comm, e, mul_right_comm]) <;> rfl
  have hconv : ∀ t, RealConv (stepY R t k) m X φ v mR := fun t => by
    obtain ⟨h1, h2⟩ := (hφv mR (hmR A.μ0).1).2
    refine ⟨h1, fun a ha => ?_⟩
    obtain ⟨s₁, hs₁, hi⟩ := h2 a ha
    refine ⟨s₁, hs₁, (hi.mul_const (((nrm2 m X (R.vY t k) : ℝ) : ℂ) / (nrm2 m X (R.vY A.μ0 k) : ℂ))).congr
      (Filter.Eventually.of_forall fun g => ?_)⟩
    simp only
    (rw [eq_div_of_mul_eq (hn A.μ0) (key t g), mul_div_assoc, mul_right_comm _ (_ / _)]) <;> rfl
  have hint : ∀ t, (∫ g, zReal (stepY R t k) m X φ v g ∂mR) * (nrm2 m X (R.vY A.μ0 k) : ℂ) =
      (∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR) * (nrm2 m X (R.vY t k) : ℂ) := fun t => by
    have e1 := integral_mul_const (μ := mR) ((nrm2 m X (R.vY A.μ0 k) : ℝ) : ℂ) (fun g => zReal (stepY R t k) m X φ v g)
    have e2 := integral_mul_const (μ := mR) ((nrm2 m X (R.vY t k) : ℝ) : ℂ) (fun g => zReal (stepY R A.μ0 k) m X φ v g)
    rw [← e1, ← e2]
    congr 1
    funext g
    exact key t g
  refine ⟨((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D (k + 1)) (R.νY A.μ0 (k + 1)) : ℝ) : ℂ) *
      (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 k) (stY R A.μ0 (k + 1))) * ∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR,
    φ, v, ?_, fun t => ⟨m, X, mR, H₀, hX, hmR t, hconv t, isHval_tuple R hH, ?_⟩⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (div_ne_zero hH0 hd)) (hφv mR (hmR A.μ0).1).1
    exact_mod_cast ((hV A.μ0).1 (k + 1) hk).2.ne'
  · obtain ⟨hv1, hv2⟩ := (hV t).1 (k + 1) hk
    have hPi : (∏ PP ∈ R.Q t, idxQ PP (k + 1)) ≠ 0 := by
      intro h0
      rw [hv1, h0, mul_zero] at hv2
      exact lt_irrefl _ hv2
    have hnr := (hN t).1 k hk m X hX
    have hPv : (∏ PP ∈ R.Q t, volOne PP (k + 1)) ≠ 0 := by
      intro h0
      apply hn t
      rw [hnr, h0, mul_zero, Complex.ofReal_zero]
    have hI : (∫ g, zReal (stepY R t k) m X φ v g ∂mR) =
        (∫ g, zReal (stepY R A.μ0 k) m X φ v g ∂mR) * ((∏ PP ∈ R.Q t, volOne PP (k + 1) : ℝ) : ℂ) := by
      have := hint t
      rw [hnr, Complex.ofReal_mul] at this
      apply mul_right_cancel₀ (hn A.μ0)
      rw [this]
      ring
    show ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D (k + 1)) (R.νY t (k + 1)) / ∏ PP ∈ R.Q t, idxQ PP (k + 1) : ℝ) : ℂ) *
        (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 k) (stY R A.μ0 (k + 1))) *
        ((∫ g, zReal (stepY R t k) m X φ v g ∂mR) / ((∏ PP ∈ R.Q t, volOne PP (k + 1) : ℝ) : ℂ)) = _
    rw [hI, hv1, mul_div_cancel_right₀ _ hPi, mul_div_cancel_right₀ _ (by exact_mod_cast hPv)]

theorem unifX (hL : R.toLevCh.Is A.μ0) (hG : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hZ : RealZetaQ D) (hRs : Restore D)
    (h : RangeX R) (hC : RChain R h) (hM : RMeas R) (hV : RVol R) (hN : RNrm R) :
    ∃ (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec),
      IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K (fun _ => φ)
        fun _ => v := by
  have h2 := D.R.two_le_m
  have hk' : D.R.m - 1 < D.R.m := by omega
  have e1 : D.R.m - 1 + 1 = D.R.m := by omega
  have hw : ∀ t, (twR R t).Is (comR R t) := fun t => (hC t).1
  have hs : ∀ t, IsStage (comR R t) (twR R t) (D.R.m - 1) (stY R t (D.R.m - 1)) := fun t => (hC t).2.1 _ hk'
  have hs' : ∀ t, IsStage (comR R t) (twR R t) (D.R.m - 1 + 1) (stX R t) := fun t => by
    rw [e1]; exact (hC t).2.2.1
  have hp : ∀ t, IsStep (twR R t) (D.R.m - 1 + 1) (stepX R h t) := fun t => by
    rw [e1]; exact (hC t).2.2.2.2
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne (Yc D (D.R.m - 1)) D.sp.X'
  obtain ⟨φ, v, hφv⟩ := hZ hG _ _ (hw A.μ0) _ hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0) m X hX
  obtain ⟨mR, hmR⟩ := hM _ hk'
  obtain ⟨-, ⟨H₀, hH0, hH⟩, hd, -⟩ := hRs hG _ _ (hw A.μ0) _ hk' _ _ (hs A.μ0) (hs' A.μ0) _ (hp A.μ0)
  have ev : ∀ t, GlobalTheory.PairLift.IsWeilExp R.ψ (Yc D (D.R.m - 1)) D.sp.X' (GlobalTheory.Chain.expS D ⟨D.R.m - 1, hk'⟩)
      (GlobalTheory.Chain.expT D ⟨D.R.m - 1, hk'⟩) (R.ωX t) ∧
      GlobalTheory.Chain.IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := fun t =>
    GlobalTheory.ChainTw.StepExpTw.twStepExpVac D hG _ _ (hw t) _ hk' _ _ (hs t) (hs' t) _ (hp t) hk'
  have hθ : IsInfFam R.θ := (hw A.μ0).com.inf
  have hn : ∀ t, ((nrm2 m X (R.vX t) : ℝ) : ℂ) ≠ 0 := fun t => by
    rw [← ipTh_self]
    exact (GlobalTheory.FockProdCoef.ipTh_ptOf_glue D _ _ _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ _ _ (R.ωX t) hθ (hp t).weil
      m X hX _ (ev t).2).1
  have key : ∀ t (g : GinfC (Yc D (D.R.m - 1))), zReal (stepX R h t) m X φ v g * (nrm2 m X (R.vX A.μ0) : ℂ) =
      zReal (stepX R h A.μ0) m X φ v g * (nrm2 m X (R.vX t) : ℂ) := fun t g => by
    have e : coefW (stepX R h t).ω m X ((stepX R h t).pt φ) (g : GA D (Yc D (D.R.m - 1))) *
        (nrm2 m X (R.vX A.μ0) : ℂ) =
        coefW (stepX R h A.μ0).ω m X ((stepX R h A.μ0).pt φ) (g : GA D (Yc D (D.R.m - 1))) *
        (nrm2 m X (R.vX t) : ℂ) :=
      GlobalTheory.FockCoefIndep.coef_indep_exponents D ⟨D.R.m - 1, hk'⟩ _ _ _ _ (R.MY (D.R.m - 1)) R.MX R.θ R.ψ (R.ωX t)
        (R.ωX A.μ0) (R.vX t) (R.vX A.μ0) hθ (ev t).1 (ev A.μ0).1 (ev t).2 (ev A.μ0).2 m X hX φ g g.2
    unfold zReal
    (rw [mul_right_comm, e, mul_right_comm]) <;> rfl
  have hconv : ∀ t, RealConv (stepX R h t) m X φ v mR := fun t => by
    obtain ⟨h1, h2⟩ := (hφv mR (hmR A.μ0).1).2
    refine ⟨h1, fun a ha => ?_⟩
    obtain ⟨s₁, hs₁, hi⟩ := h2 a ha
    refine ⟨s₁, hs₁, (hi.mul_const (((nrm2 m X (R.vX t) : ℝ) : ℂ) / (nrm2 m X (R.vX A.μ0) : ℂ))).congr
      (Filter.Eventually.of_forall fun g => ?_)⟩
    simp only
    (rw [eq_div_of_mul_eq (hn A.μ0) (key t g), mul_div_assoc, mul_right_comm _ (_ / _)]) <;> rfl
  have hint : ∀ t, (∫ g, zReal (stepX R h t) m X φ v g ∂mR) * (nrm2 m X (R.vX A.μ0) : ℂ) =
      (∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR) * (nrm2 m X (R.vX t) : ℂ) := fun t => by
    have e1 := integral_mul_const (μ := mR) ((nrm2 m X (R.vX A.μ0) : ℝ) : ℂ) (fun g => zReal (stepX R h t) m X φ v g)
    have e2 := integral_mul_const (μ := mR) ((nrm2 m X (R.vX t) : ℝ) : ℂ) (fun g => zReal (stepX R h A.μ0) m X φ v g)
    rw [← e1, ← e2]
    congr 1
    funext g
    exact key t g
  refine ⟨((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX A.μ0) : ℝ) : ℂ) *
      (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 (D.R.m - 1)) (stX R A.μ0)) * ∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR,
    φ, v, ?_, fun t => ⟨m, X, mR, H₀, hX, hmR t, hconv t, isHval_tuple R hH, ?_⟩⟩
  · refine mul_ne_zero (mul_ne_zero ?_ (div_ne_zero hH0 hd)) (hφv mR (hmR A.μ0).1).1
    exact_mod_cast (hV A.μ0).2.2.ne'
  · have hv1 := (hV t).2.1
    have hv2 := (hV t).2.2
    have hPi : (∏ PP ∈ R.Q t, idxQ PP D.R.m) ≠ 0 := by
      intro h0
      rw [hv1, h0, mul_zero] at hv2
      exact lt_irrefl _ hv2
    have hnr := (hN t).2 m X hX
    have hPv : (∏ PP ∈ R.Q t, volOne PP D.R.m) ≠ 0 := by
      intro h0
      apply hn t
      rw [hnr, h0, mul_zero, Complex.ofReal_zero]
    have hI : (∫ g, zReal (stepX R h t) m X φ v g ∂mR) =
        (∫ g, zReal (stepX R h A.μ0) m X φ v g ∂mR) * ((∏ PP ∈ R.Q t, volOne PP D.R.m : ℝ) : ℂ) := by
      have := hint t
      rw [hnr, Complex.ofReal_mul] at this
      apply mul_right_cancel₀ (hn A.μ0)
      rw [this]
      ring
    show ((GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ D.sp.X' (R.νX t) / ∏ PP ∈ R.Q t, idxQ PP (D.R.m - 1 + 1) : ℝ) : ℂ) *
        (H₀ / dS (twR R A.μ0).S₀ (stY R A.μ0 (D.R.m - 1)) (stX R A.μ0)) *
        ((∫ g, zReal (stepX R h t) m X φ v g ∂mR) / ((∏ PP ∈ R.Q t, volOne PP (D.R.m - 1 + 1) : ℝ) : ℂ)) = _
    rw [e1, hI, hv1, mul_div_cancel_right₀ _ hPi, mul_div_cancel_right₀ _ (by exact_mod_cast hPv)]

theorem rUnif_of : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → RealZetaQ D → Restore D → ∀ h : RangeX R, RChain R h → RMeas R → RVol R → RNrm R → RUnif R h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hF hG hZ hRs h hC hM hV hN
  exact ⟨fun k hk => unifY R hF.core.lev hG hZ hRs h hC hM hV hN k hk, unifX R hF.core.lev hG hZ hRs h hC hM hV hN⟩

end GlobalTheory.ChainTw.UnifFree
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.GSuppAsm

theorem gsupp_of_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  intro D c v n G hc hv hG h1 h2 _hfl t ht hch j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂
  have hj : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  refine ⟨fun x hx hne => ?_, fun x hx hne => ?_⟩
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1) x hx
    have hb : ∀ i, j + 1 + (2 * σ + 1 + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1) hj (jacGrp (c.jac j (σ + 1) h).d) (fun _ => 2 * σ + 1 + 1) hb xs (fun i => ?_)
    obtain ⟨F, hF, hcomb⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j) := by
      have := (t.sBF j (σ + 1) h).weil
      rw [(ht.sBF j (σ + 1) h).1] at this
      exact this
    obtain ⟨hF', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) j hj _ _ (t.om j) hw F hF y hy
    refine GlobalTheory.T.seesaw_first_flatMap_support_at_level_place hc hv h1 t ht (G i) (hch i) j σ h _ hF' (xs i) (hxs i) ?_
    rw [hprod, hcomb] at hne
    have e : t.om j (1, xs i * y) = t.om j (1, xs i) * t.om j (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1 + 1) x hx
    have hb : ∀ i, j + 1 + 1 + (2 * σ + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1 + 1) (by omega) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
      (fun _ => 2 * σ + 1) hb xs (fun i => ?_)
    obtain ⟨F₁, hF₁, hcomb₁⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨F₂, hF₂, hcomb₂⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG (j + 1) hj2 Ψ₂ hΨ₂ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1 + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) (t.sFB j σ h).χV (t.sFB j σ h).χW (t.om (j + 1)) := by
      have := (t.sFB j σ h).weil
      rw [(ht.sFB j σ h).1] at this
      exact this
    obtain ⟨hF₂', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) (j + 1) hj2 _ _ (t.om (j + 1)) hw F₂ hF₂ y hy
    refine GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place hc hv h2 t ht (G i) (hch i) j σ h F₁ hF₁ _ hF₂' (xs i) (hxs i) ?_
    rw [hprod, hcomb₁, hcomb₂] at hne
    have e : t.om (j + 1) (1, xs i * y) = t.om (j + 1) (1, xs i) * t.om (j + 1) (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne

end GlobalTheory.SeeSaw.GSuppAsm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

theorem idV_props : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v : Pl D, (∀ a, a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v)) ∧ (∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v) ∧ (∀ (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v)) ∧ (∀ n : ℤ, ∀ s, s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v) ∧ (∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ∧ (∀ 𝔞 : FI D, 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v)) ∧ ∀ (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := fun D ψ hψ v =>
  ⟨GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace D v, GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v, GlobalTheory.T.mem_spanSingleton_mul_idealCompletion_iff D v, fun n s => GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff D v n s,
    GlobalTheory.T.inverseDifferentCompletion_iff_characterDual D ψ hψ v, GlobalTheory.T.fractionalIdeal_locallyPrincipal_adelic D v, GlobalTheory.T.mem_scaledLatticeCompletion_iff_polarisationInverse D v⟩

end GlobalTheory.SeeSaw

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftChain_fockVector_levelLaws : ∀ D : D7, LevelLaw D := by
  first | exact @GlobalTheory.ChainOnto.levelLaw | exact GlobalTheory.ChainOnto.levelLaw | (intros; apply GlobalTheory.ChainOnto.levelLaw <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ConvDistinct

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ι : Type) (v : ι → GlobalTheory.FinPl.Pl D) (c : ι → WO S T →₀ ℂ), Function.Injective v → (∀ i, GlobalTheory.FinPl.CombAt (· = v i) (c i)) → ∀ L : List ι, L.Nodup → GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) ∧ ∀ f, comb ψ S T (aconv (L.map c)) f = L.foldr (fun i g => comb ψ S T (c i) g) f := by
  intro D ψ S T ι v c hv hc L
  have hsupp : ∀ L : List ι, GlobalTheory.FinPl.CombAt (fun p => ∃ i ∈ L, v i = p) (aconv (L.map c)) := by
    intro L
    refine GlobalTheory.QFinLaw.combAt_aconv _ (L.map c) (fun e he => ?_)
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
    exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun p hp => ⟨b, hb, hp.symm⟩) (hc b u hu)
  intro hL
  refine ⟨hsupp L, fun f => ?_⟩
  induction L with
  | nil => exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    rw [List.map_cons, GlobalTheory.QFinLaw.comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = v a)) (P' := fun p => ∃ b ∈ L, v b = p) ?_ (hc a x hx) (hsupp L y hy)
    rintro _ rfl ⟨b, hb, hab⟩
    exact (List.nodup_cons.1 hL).1 (hv hab ▸ hb)

end GlobalTheory.ConvDistinct
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


theorem _root_.GlobalTheory.T.unramified_doubling_integral_inert_adelic : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.LocZetaInertAd.localZetaOn_inert | exact GlobalTheory.LocZetaInertAd.localZetaOn_inert | (intros; apply GlobalTheory.LocZetaInertAd.localZetaOn_inert <;> assumption)
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


theorem _root_.GlobalTheory.T.setIntegral_unramified_places_union_eq_local_factors : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ → ∀ s : ℂ, (A.rank : ℝ) < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m → ∀ S₁ S₂ : Finset (FinPl D), Sf ⊆ S₁ → Disjoint S₁ S₂ → ∀ S₃ : Finset (FinPl D), (∀ u, u ∈ S₃ ↔ u ∈ S₁ ∨ u ∈ S₂) → ∫ g in openOff A LA S₃, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m = (∏ v ∈ S₂, GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s) * ∫ g in openOff A LA S₁, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
  first | exact @GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union | exact GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union | (intros; apply GlobalTheory.Core.Rk.EulStep.setIntegral_openOff_union <;> assumption)
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


theorem _root_.GlobalTheory.T.tendsto_setIntegral_unramifiedOutsideOpenSubset : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)) (F : GA D A → ℂ), Integrable F m → Filter.Tendsto (fun S : Finset (FinPl D) => ∫ g in openOff A L S, F g ∂m) Filter.atTop (nhds (∫ g, F g ∂m)) := by
  first | exact @GlobalTheory.Core.Rk.IP.tendsto_setIntegral_openOff | exact GlobalTheory.Core.Rk.IP.tendsto_setIntegral_openOff | (intros; apply GlobalTheory.Core.Rk.IP.tendsto_setIntegral_openOff <;> assumption)
end
