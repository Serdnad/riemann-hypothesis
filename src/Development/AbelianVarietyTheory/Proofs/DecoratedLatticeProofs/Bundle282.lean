module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAverageTranslateEqSmulBranchingMap
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle264
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle265
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle277
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle275
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle268
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle269
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

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


theorem _root_.GlobalTheory.T.doublingClass_offOpenOrbit_fixedByUnipotentRadical : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ¬ (∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ (∀ n ∈ NI V C, ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1) ∧ ∀ δ ∈ GQ V, γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  first | exact @GlobalTheory.Core.Rk.Dich.offOpen | exact GlobalTheory.Core.Rk.Dich.offOpen | (intros; apply GlobalTheory.Core.Rk.Dich.offOpen <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

theorem _root_.GlobalTheory.T.unitaryAverage_translate_eq_smul_branchingMap : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (lam τ) (sg τ)) → ∀ T₀, BrEqv hN G G' lam sg T₀ → (∃ Φ ∈ ValC G lam, T₀ Φ ≠ 0) → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin n) (Fin n) ℂ), OntoUni r → ∀ (y : Frames G) (yk : K → Frames G), (∀ k, ∃ kt, (∀ τ, GlobalTheory.BranchFormula.IsBlock hN (kt τ) (r k τ) 1) ∧ IsTr kt y (yk k)) → ∀ J ∈ ValC G' sg, ∀ Jk : K → Frames G' → ℂ, (∀ k z z', IsTr (r k) z z' → Jk k z' = J z) → ∃ c : ℂ, ∀ Φ ∈ ValC G lam, ∀ ℓ : (Frames G' → ℂ) →ₗ[ℂ] ℂ, ∫ k, ℓ (Jk k) * Φ (yk k) ∂ν = c * ℓ (T₀ Φ) := by
  first | exact @GlobalTheory.KJAvg.avg_eq_mul_branch | exact GlobalTheory.KJAvg.avg_eq_mul_branch | (intros; apply GlobalTheory.KJAvg.avg_eq_mul_branch <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → _root_.GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  first | exact @GlobalTheory.ConjRowCont.conjMap_cont | exact GlobalTheory.ConjRowCont.conjMap_cont | (intros; apply GlobalTheory.ConjRowCont.conjMap_cont <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChain_LValues_nonvanishing : ∀ D : D7, ChainLW D := by
  first | exact @GlobalTheory.ChainOnto.chainLW_holds | exact GlobalTheory.ChainOnto.chainLW_holds | (intros; apply GlobalTheory.ChainOnto.chainLW_holds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.ChartVal

theorem infM_fin' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

end GlobalTheory.AdForm.ChartVal


open GlobalTheory.AdForm.ChartVal in
theorem GlobalTheory.AdForm.rd_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (i : ℕ) (hi : i ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi i, (∀ c, (fun z : FrN (I.rec7 l Z) (B.R.N i) => φ c ⟨z.1, z.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i)) ∧ ∀ β y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ c, ∀ k ∈ GinfC ((I.rec7 l Z).sp.X i), ∀ (κ : A.U i β) (y' : (I.chain l u a).Y i), IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) i hi) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ → A.rd θ i hi β φ y (γ * (A.h i β c * k) * κ.1) = (A.chi i β κ : ℂ) * φ c.1 y' := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ i hi φ hφ
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  refine ⟨?_, ?_⟩
  · intro c
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf i c))
    have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hΨ).2) ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) (Set.mem_univ _)
    have e2 : Ψ ((A.K i hi (A.chOf i c)).y ⟨c, rfl⟩) = fun z => φ c (eY.symm z) := congrFun he ⟨c, rfl⟩
    rw [e2] at hval
    exact hval

  · intro β y γ hγ c k hk κ y' hy
    obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF β)
    have hAd : Ψ ∈ AdFun (A.K i hi β).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
    have hfun : (fun (c : {c // A.chOf i c = β}) (z : Frames (gramC (gramN (I.rec7 l Z) i hi) (embT (I.rec7 l Z)))) =>
        φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K i hi β).y c) := he.symm
    have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
    obtain ⟨hL, hK, hR, -⟩ := laws
    have hκ := (hA.U i hi β κ.1).1 κ.2
    obtain ⟨hκf, κ', hκ'⟩ := hκ
    have hchi := hA.chi i hi β κ κ' hκ'
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
      (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
      (A.K i hi β).y (A.K i hi β).y_bij Ψ hAd ⟨y'.1, y'.2⟩ (A.h i β c)).2.2 ((A.K i hi β).y c) ⟨y'.1, y'.2⟩
      ((hA.h i hi β c).2.symm) (fun τ => by
        have h1 := infM_fin' θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.h i β c) (hA.h i hi β c).1 τ
        show y'.1 τ = infM θ _ _ (A.h i β c) τ * y'.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨y.1, y.2⟩
      (γ * (A.h i β c * k) * κ.1) = _
    have e1 := hL γ hγ (A.h i β c * k * κ.1)
    have e2 := hK κ.1 hκf κ' hκ' (A.h i β c * k)
    have e3 := hR k hk ⟨y'.1, y'.2⟩ hy (A.h i β c)
    have e5 := congrArg (fun F => rdS θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y F
      ⟨y'.1, y'.2⟩ (A.h i β c)) hfun
    have e6 : Ψ ((A.K i hi β).y c) ⟨y'.1, y'.2⟩ = φ c.1 y' := (congrFun (congrFun hfun c) ⟨y'.1, y'.2⟩).symm
    have e4 := e3.trans (e5.trans (hval.trans e6))
    rw [mul_assoc]
    exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e4))
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → (∀ M : ℝ →+ WO A S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ A S M (fun u' => G u' v) u) ∧ ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → IsBiTheta ψ A S A' fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v := by
  first | exact @GlobalTheory.BiDeriv.isBiTheta_dLine | exact GlobalTheory.BiDeriv.isBiTheta_dLine | (intros; apply GlobalTheory.BiDeriv.isBiTheta_dLine <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgMidUnif

open GlobalTheory.AvgMid

theorem exists_isotypic_uniform : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (χ₃ : GA D S → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → IsBiSmooth C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k₀.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v) → ∃ (C₂ : WO A S → WO S A' → ℂ) (χ₂ : GA D S → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₂ ∧ (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₂ u v) = χ₁ a • fun u => C₂ u v) ∧ (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k₀'.om (b, 1) (C₂ u) = χ₂ b • C₂ u) ∧ ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) = biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₂) := by
  intro D _ hF _ ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ _ h1 h3
  obtain ⟨χA, χS, hwa⟩ := hk₀.weil
  obtain ⟨χS', χA', hwb⟩ := hk₀'.weil
  by_cases h0 : ∀ u v, C₁ u v = 0
  · refine ⟨C₁, fun _ => 1, hC₁, h1, fun b _ _ u => ?_, fun _ _ _ _ _ _ _ _ => rfl⟩
    rw [show C₁ u = 0 from funext (h0 u), map_zero, smul_zero]
  push_neg at h0
  obtain ⟨u₀, v₀, h0⟩ := h0
  have hv : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ = χ₃ b.1 * C₁ u₀ v₀ :=
    fun b => congrFun (h3 b.1 b.2.1 b.2.2 v₀) u₀
  have hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1 := by
    have : (fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1) =
        fun b => k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ / C₁ u₀ v₀ := funext fun b => by rw [hv, mul_div_cancel_right₀ _ h0]
    rw [this]
    exact ((hwa.om_cont _ (hC₁.left v₀).1 u₀).comp (continuous_const.prodMk continuous_subtype_val)).div_const _
  have hm : ∀ b b' : ↥(GinfC S ⊓ Subgroup.center (GA D S)), χ₃ (b.1 * b'.1) = χ₃ b.1 * χ₃ b'.1 := fun b b' => by
    have e := hv (b * b')
    have e' : ((1, (b * b').1) : GA D A × GA D S) = (1, b.1) * (1, b'.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, h3 b'.1 b'.2.1 b'.2.2, map_smul, Pi.smul_apply, hv, smul_eq_mul] at e
    refine mul_right_cancel₀ h0 ?_
    rw [← Subgroup.coe_mul, ← e]
    ring
  obtain ⟨hcpt, ν, hν, hν'⟩ := exists_haar hy
  obtain ⟨W, hW, hWf⟩ := hF ψ θ hθ A S x y hx hy k₀ hk₀ χ₁
  let E : Submodule ℂ (WO A S → ℂ) := Submodule.span ℂ (Set.range fun v u => C₁ u v)
  haveI : FiniteDimensional ℂ E := by
    refine Submodule.finiteDimensional_of_le (S₂ := W.map (pureTensorO ψ θ A S x.s y.s x.B y.B k₀.vac))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨v, rfl⟩
    obtain ⟨P, hP, e⟩ := hWf _ (hC₁.left v).1 (hC₁.left v).2 (fun a ha hc => h1 a ha hc v)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  have hEv : E ≤ vacSub ψ A S (latO A S x.L y.L fun _ => True) := Submodule.span_le.2 (by
    rintro _ ⟨v, rfl⟩; exact hC₁.left v)
  have hEe : ∀ (p : GA D A × GA D S) (c : ℂ), (∀ v, k₀.om p (fun u => C₁ u v) = c • fun u => C₁ u v) →
      ∀ f ∈ E, k₀.om p f = c • f := fun p c h f hf => by
    have : E ≤ LinearMap.eqLocus (k₀.om p) (c • LinearMap.id) := Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact h v)
    exact this hf
  obtain ⟨n, e, g, he, hg, hs⟩ := GlobalTheory.SeeSaw.FinRank.sum_prod_of_slices C₁ E
    (vacSub ψ S A' (latO S A' y.L z.L fun _ => True)) (fun v => Submodule.subset_span ⟨v, rfl⟩) hC₁.right
  have hg' : ∀ i, mean k₀'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
    vac_mean hwb hθ hχ (hg i)
  have hl : ∀ v, (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) ∈ E := fun v => by
    have : (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, mean k₀'.om ν χ₃ (g i) v • e i := by
      funext u; simp [Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  have hr : ∀ u, (fun v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, e i u • mean k₀'.om ν χ₃ (g i) := fun u => by
    funext v; simp [Finset.sum_apply]
  refine ⟨fun u v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v, fun b => χ₃ b⁻¹, ⟨?_, fun v => hEv (hl v), fun u => ?_⟩,
    fun a ha hc v => hEe _ _ (h1 a ha hc) _ (hl v), fun b hb hc u => ?_, fun k k' hk hk' hag hag' φ hφ => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hEv (he i)).1.cont.comp continuous_fst).mul
      ((hg' i).1.cont.comp continuous_snd)
  · rw [hr]
    exact (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg' i) :
      _ ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True))
  · simp only []

    rw [hr, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_comm]
    exact congrArg _ (eigen_mean hwb hθ hχ hm (hg i).1 ⟨b, hb, hc⟩)
  · obtain ⟨χA₁, χS₁, hwa₁⟩ := hk.weil
    obtain ⟨χS₁', χA₁', hwb₁⟩ := hk'.weil

    have hmean : ∀ i, mean k₀'.om ν χ₃ (g i) = mean k'.om ν χ₃ (g i) := fun i => by
      funext w
      simp only [mean]
      congr 1
      funext b
      rw [hag' b.1 b.2.1 1 (GinfC A').one_mem (g i) (hg i).1]
    have hEk : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), ∀ f ∈ E, k.om (1, b.1) f = χ₃ b.1 • f :=
      fun b f hf => by
        rw [hag 1 (GinfC A).one_mem b.1 b.2.1 f (hEv hf).1]
        exact hEe _ _ (h3 b.1 b.2.1 b.2.2) f hf
    have hg'' : ∀ i, mean k'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
      vac_mean hwb₁ hθ hχ (hg i)
    simp only [hmean]
    funext h₂
    have hX : ∀ i, IsThetaFunO ψ A S (comb ψ A S k.c (e i)) := fun i => theta_comb hwa₁.std hk.fin (hEv (he i)).1
    rw [show C₁ = fun u v => ∑ i, e i u * g i v from funext fun u => funext (hs u), biComb_sum, biComb_sum,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg i).1) hφ,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg'' i).1) hφ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [comb_mean hwb₁ hχ hk'.fin (hg i).1]
    refine (lift_mean hwb₁ hθ hy.cpt y.vol hχ (theta_comb hwb₁.std hk'.fin (hg i).1)
      (contAut_lift hwa₁ hx.cpt x.vol (hX i) hφ) (fun b h => ?_) h₂).symm
    rw [← integral_const_mul]
    congr 1
    funext a
    have e' : ((a, h * b.1) : GA D A × GA D S) = (a, h) * (1, b.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, GlobalTheory.FrComb.om_comb hwa₁ (GinfC A).one_mem b.2.1 hk.fin (hEv (he i)).1,
      hEk b _ (he i), comb_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.AvgMidUnif

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.schwartzBruhatHalf_adelicHomPairAction_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  first | exact @GlobalTheory.SBMove.isSBHalf_actO_lev | exact GlobalTheory.SBMove.isSBHalf_actO_lev | (intros; apply GlobalTheory.SBMove.isSBHalf_actO_lev <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A S A' : HSp D) (C : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' C → ∀ (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ), IsBiTheta ψ A S A' (biComb ψ A S A' c c' C) := by
  first | exact @GlobalTheory.FrCombAny.biTheta_biComb | exact GlobalTheory.FrCombAny.biTheta_biComb | (intros; apply GlobalTheory.FrCombAny.biTheta_biComb <;> assumption)
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

theorem _root_.GlobalTheory.T.realFormsRangeMultiplicity_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RangeX R := by
  first | exact @GlobalTheory.ChainTw.rangeX_of_given | exact GlobalTheory.ChainTw.rangeX_of_given | (intros; apply GlobalTheory.ChainTw.rangeX_of_given <;> assumption)
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

theorem _root_.GlobalTheory.T.realLastStageNormalized_of_scalarHypotheses : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ h : RangeX R, NormX R h := by
  first | exact @GlobalTheory.ChainTwNorm.normX | exact GlobalTheory.ChainTwNorm.normX | (intros; apply GlobalTheory.ChainTwNorm.normX <;> assumption)
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

theorem _root_.GlobalTheory.T.schurProduct_typings_agree_thetaChain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → IPDict R := by
  first | exact @GlobalTheory.ChainTw.IPDictPf.main | exact GlobalTheory.ChainTw.IPDictPf.main | (intros; apply GlobalTheory.ChainTw.IPDictPf.main <;> assumption)
end
