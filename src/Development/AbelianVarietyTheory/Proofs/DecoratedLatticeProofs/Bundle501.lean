module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle500
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle020
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle271
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle497
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

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

theorem _root_.GlobalTheory.T.doublingMap_span_dense_heisenbergStable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D), IsStdChar D ψ (-1) → let M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂}; (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧ ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := by
  first | exact @GlobalTheory.Core.Rk.DoubleSpan.main | exact GlobalTheory.Core.Rk.DoubleSpan.main | (intros; apply GlobalTheory.Core.Rk.DoubleSpan.main <;> assumption)
end

section

open Formalism.BasicNotions

namespace GlobalTheory.TwArch

theorem archOnRecord_closed : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D :=
  fun hDS hHC D => GlobalTheory.ArchRec.archOnRecord hDS hHC D

end GlobalTheory.TwArch
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.exists_twistRational_levelElements_same_characters : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (k : ℕ), 0 < k → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ (z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E), ∃ (κ₁ : A.U i α) (κ₁' : A.U (i + 1) γ) (x₁ y₁ : (AE (I.rec7 l Z))ˣ) (t : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) κ₁.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ (∀ P ∈ I.Q a, ∃ M : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.host.E, ∀ r s, adAt B.host.F P ((finM _ (rankN (I.rec7 l Z) (i + 1) hi) κ₁'.1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) (Formalism.L2.DIV.AfE B.host.F B.host.E)) r s) = algebraMap B.host.E _ (M r s)) ∧ IsDetRoot _ κ₁.1 x₁ ∧ IsDetRoot _ κ₁'.1 y₁ ∧ A.chr (i + 1) x₁ = A.chr (i + 1) x ∧ A.chr (i + 1) y₁ = A.chr (i + 1) y ∧ A.chi i α κ₁ = A.chi i α κ ∧ A.chi (i + 1) γ κ₁' = A.chi (i + 1) γ κ' ∧ t ∈ stdHom _ _ ∧ IsHalf A.e t ∧ actO _ _ κ₁.1⁻¹ κ₁'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) = actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) + k • t := by
  first | exact @GlobalTheory.AdForm.RatApprox.approx | exact GlobalTheory.AdForm.RatApprox.approx | (intros; apply GlobalTheory.AdForm.RatApprox.approx <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isThetaFunO_annih_of_std {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {A B : HSp D} {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨)
    (τ : D.what₂.Tau)
    (J : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ → Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) :
    IsThetaFunO ψ (dblSp A) B (annih (heisO ψ (dblSp A) B) θ τ J z f) := by
  have h1 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf
  have h2 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf
  have h3 := (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν _ _ h2 h2 Complex.I).2.1
  exact (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν _ _ h1 h3 Complex.I).1

theorem sch_mem_fockA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsFockVec ψ θ (dblSp A) B s' sB f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hS : sch ψ A B ν 𝓨 f ∈ schwartzA θ B.rank A.rank :=
    (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hψ θ hθ A B ν 𝓨 hν).1 f hth
  have key : ∀ L : List (D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ),
      IsThetaFunO ψ (dblSp A) B
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) ∧
      sch ψ A B ν 𝓨
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) =
        L.foldr (fun q g => annS B l sB θ q.1 q.2 g) (sch ψ A B ν 𝓨 f) := by
    intro L
    induction L with
    | nil => exact ⟨hth, rfl⟩
    | cons q L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨isThetaFunO_annih_of_std hψ hθ hν _ _ _ ih1, ?_⟩
      rw [List.foldr_cons, ← ih2]
      exact GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl _ ih1 q.1 q.2
  have hz : sch ψ A B ν 𝓨 0 = 0 := by
    have h := (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν f f hth hth 0).2.2.2
    rwa [zero_smul, zero_smul] at h
  refine GlobalTheory.T.mem_fockSpace_of_polynomial_gaussian_slices D θ hθ B A.rank l sB _ hS
    (GlobalTheory.T.adelicSchwartz_slice_polynomial_gaussian_of_annihilated D θ hθ B A.rank l sB hsB N _ hS ?_)
  intro L hL
  rw [← (key L).2, hN _ (by rw [List.length_map, hL]), hz]

end GlobalTheory.StdUnn
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

theorem _root_.GlobalTheory.T.twistedThetaChain_step_adjoint_scalar : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  first | exact @GlobalTheory.ChainTw.stepLam_of_ns | exact GlobalTheory.ChainTw.stepLam_of_ns | (intros; apply GlobalTheory.ChainTw.stepLam_of_ns <;> assumption)
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.WeylStd

theorem trA_incA_mul (D : D7) (lam : D.host.F) (t : AE D) :
    trA (incA D (algebraMap D.host.F D.host.E lam) * t) = algebraMap D.host.F (AF D.host.F) lam * trA t := by
  have h : incA D (algebraMap D.host.F D.host.E lam) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) lam) := by
    show Algebra.TensorProduct.includeRight (algebraMap D.host.F D.host.E lam) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]
  rw [h, ← Algebra.smul_def]
  show Algebra.trace (AF D.host.F) (AE D) (_ • t) = _
  rw [LinearMap.map_smul, smul_eq_mul]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ g : G D A.rank, mat g = blk4 0 1 (-1) 0 → ∀ Φ x, (omS g Φ).1 x = ∫ y, Φ.1 y * shift ψ lam (trA (Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam g hg Φ x
  obtain ⟨f, hf, hΦ⟩ := (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hW.std θ hθ A B ν 𝓨 hν).2.1 Φ.1 Φ.2
  have hw : mat (κ (κ.symm g)) = blk4 0 1 (-1) 0 := by rw [MulEquiv.apply_symm_apply]; exact hg
  obtain ⟨hW1, h1, h2⟩ := GlobalTheory.T.standardUnitaryChart_weylElement_rational D A μ hμ κ hκ (κ.symm g) hw
  have hg' := hT (κ.symm g) f hf Φ hΦ.symm
  rw [MulEquiv.apply_symm_apply] at hg'
  rw [hg', GlobalTheory.T.weylElement_acts_on_schrodinger_by_fourier D ψ A B χB omh hW ν 𝓨 hν μ hμ (κ.symm g) hW1 h1 h2 f hf x, ← hΦ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [shift, AddChar.mulShift_apply]
  rw [← hlam, trA_incA_mul]

end GlobalTheory.StdUnn.WeylStd
end

section


theorem _root_.GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof : GlobalTheory.AdForm.TwLev' := by
  first | exact @GlobalTheory.AdForm.twLev_prime | exact GlobalTheory.AdForm.twLev_prime | (intros; apply GlobalTheory.AdForm.twLev_prime <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimSplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_sec_mul' (p : SplitPt D k) (a : AE D) (t : k) :
    cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, Formalism.L2.Theta.cA_cA]

theorem colMul_split (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) {a : AE D}
    (ha : a ∈ idAt D (· = q.v)) :
    colMul d.jX i a = (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * q.pr (cA D (incA D (d.e r i)))))) := by
  funext r
  change a * incA D (d.e r i) = _
  conv_lhs => rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q ha]
  rw [add_mul, sec_mul_right, cA_sec_mul' q, Pi.add_apply]

theorem mul_unit_mem_iff {b u : k} (hu : valuation k u = 1) : b * u ∈ 𝒪[k] ↔ b ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]

theorem colMul_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (i : Fin ρ) (y₁ y₂ : Y) (u₁ u₂ : k), IsSelfDualC S L → IntIn q S F L → valuation k u₁ = 1 → valuation k u₂ = 1 → (∀ r, F.β r y₁ = u₁ * q.pr (incA D (d.e r i))) → (∀ l, ∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (d.e t i))) = if l = y₂ then u₂ else 0) → ∀ a : AE D, (GlobalTheory.FinPl.colMul d.jX i a ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S S₀ ρ d L Y _ _ F i y₁ y₂ u₁ u₂ hL hF hu₁ hu₂ hcol₁ hcol₂ a
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hu₁
    exact zero_ne_one hu₁
  have hu₂i : u₂ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu₂.le
  have key : ∀ a ∈ idAt D (· = q.v), (colMul d.jX i a ∈ latV S L (· = q.v) ↔
      q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
    intro a ha
    rw [colMul_split q d i ha, decomp hL]
    refine and_congr ?_ ?_
    · have h1 : (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) =
          fun r => q.sec ((F.β *ᵥ Pi.single y₁ (q.pr a * u₁⁻¹)) r) := by
        funext r
        congr 1
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol₁]
        field_simp
      rw [h1, ← hF]
      constructor
      · intro h
        have := h y₁
        rw [Pi.single_eq_same] at this
        rwa [mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])] at this
      · intro h j
        by_cases hj : j = y₁
        · subst hj
          rw [Pi.single_eq_same, mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])]
          exact h
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
    · rw [csec_mem_iff hL]
      set b := q.pr (cA D a) with hb
      have hsum : ∀ y : Y → k, ∑ r, ∑ t, (F.β *ᵥ y) r * q.pr (cA D (incA D (HSpace.gram S r t))) *
          (b * q.pr (cA D (incA D (d.e t i)))) = b * u₂ * y y₂ := by
        intro y
        have hr : b * u₂ * y y₂ = ∑ l, y l * b * (∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) *
            q.pr (cA D (incA D (d.e t i)))) := by
          simp only [hcol₂, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [hr]
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        symm
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm.trans
          (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun l _ => ?_))
        ring
      constructor
      · intro h
        have h2 := h (F.β *ᵥ Pi.single y₂ 1) ((hF _).1 fun j => by
          by_cases hj : j = y₂
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _)
        rw [hsum, Pi.single_eq_same, mul_one, mul_unit_mem_iff hu₂] at h2
        exact h2
      · intro hb' x hx
        have hx' : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
        rw [hx'] at hx ⊢
        rw [hsum]
        exact mul_mem (mul_mem hb' hu₂i) ((hF _).2 hx y₂)
  constructor
  · intro h
    have ha := GlobalTheory.FinPl.SuppShift.idAt_of_colMul d h
    exact (GlobalTheory.SplitIntComp.mem_intAt_iff q ha).2 ((key a ha).1 h)
  · intro h
    exact (key a h.1).2 ((GlobalTheory.SplitIntComp.mem_intAt_iff q h.1).1 h)

end GlobalTheory.PrimSplitLine

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QProd

open GlobalTheory.FinPl in
theorem at_eq' {D : D7} (V : HSp D) (P : Pl D → Prop) : grpAt V P = GfC V ⊓ grpOff V (fun p => ¬ P p) := by
  rw [(GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.2.1 (fun p => ¬ P p)]
  simp only [not_not]

open GlobalTheory.FinPl in
theorem at_le_off' {D : D7} (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' :=
  (GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.1 P P' h


open GlobalTheory.FinPl in
theorem off_mono {D : D7} {V : HSp D} {R R' : Pl D → Prop} (hR : ∀ p, R' p → R p) {g : GA D V} (h : g ∈ grpOff V R) :
    g ∈ grpOff V R' := by
  unfold grpOff at h ⊢
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h ⊢
  intro a b
  have := h a b
  unfold idOff at this ⊢
  rw [Submodule.mem_iInf] at this ⊢
  intro u
  exact this ⟨u.1, hR u.1 u.2⟩


open GlobalTheory.FinPl in
theorem off_of_each {D : D7} {V : HSp D} {R : Pl D → Prop} {g : GA D V} (h : ∀ p, R p → g ∈ grpOff V (· = p)) :
    g ∈ grpOff V R := by
  unfold grpOff
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro a b
  unfold idOff
  rw [Submodule.mem_iInf]
  intro u
  have hu := h u.1 u.2
  unfold grpOff at hu
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hu
  have := hu a b
  unfold idOff at this
  rw [Submodule.mem_iInf] at this
  exact this ⟨u.1, rfl⟩

theorem prod_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  intro D c v t w F hF j σ h
  have hd : ∀ i : Fin F.r, j + 1 + (2 * σ + 2) = (F.Q i).s + 1 := fun i => by have := (F.Q i).hs; omega
  have key := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1)) ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2))
    ((F.Q i).FY (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl_loc (j + 1) (2 * σ + 2) (hd i))
  let gl := fun i => (F.Q i).gl (j + 1) (2 * σ + 2) (hd i)
  have hoff : ∀ i i', i ≠ i' → ∀ g, gl i' g ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i i' hne g
    have hr : gl i' g ∈ (gl i').range := ⟨g, rfl⟩
    rw [(key i').2.1] at hr
    exact at_le_off' _ (fun p hp hq => hne (hF.inj (hq.symm.trans hp))) hr
  have hcomm : Pairwise fun i i' => ∀ x y, Commute (gl i x) (gl i' y) := by
    intro i i' hne x y
    exact (key i).2.2.2.1 x _ (hoff i i' hne y)
  have hmem : ∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, gl i (y i) ∈ H) →
      MonoidHom.noncommPiCoprod gl hcomm y ∈ H := by
    intro H y hy
    exact Submonoid.noncommProd_mem H.toSubmonoid Finset.univ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => hy i)
  have hat : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) := by
    intro i g
    have hr : gl i g ∈ (gl i).range := ⟨g, rfl⟩
    rw [(key i).2.1] at hr
    rw [at_eq'] at hr ⊢
    refine ⟨hr.1, off_mono (fun p hp hq => hp ((hF.places p).2 ⟨i, hq.symm⟩)) hr.2⟩
  refine ⟨MonoidHom.noncommPiCoprod gl hcomm, hmem, fun y => hmem _ y fun i => hat i (y i), ?_⟩
  intro x hx
  choose y hy _ using fun i => (key i).2.2.1 x
  set P := MonoidHom.noncommPiCoprod gl hcomm
  have hsplit : ∀ i, P y = P (Function.update y i 1) * gl i (y i) := by
    intro i
    have hy' : y = Function.update y i 1 * Pi.mulSingle i (y i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    conv_lhs => rw [hy']
    rw [map_mul, MonoidHom.noncommPiCoprod_mulSingle]
  have hrest : ∀ i, P (Function.update y i 1) ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    refine hmem _ _ fun k => ?_
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]
      exact hoff i k (Ne.symm hk) _
  have hz_i : ∀ i, x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    rw [hsplit i, _root_.mul_inv_rev, ← mul_assoc]
    exact Subgroup.mul_mem _ (hy i) (Subgroup.inv_mem _ (hrest i))
  have hzQ : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hmem _ y fun i => hat i (y i)))
  rw [at_eq'] at hzQ
  have hall : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (fun _ => ¬ False) := by
    refine off_of_each fun p _ => ?_
    by_cases hp : p ∈ w.Q
    · obtain ⟨i, rfl⟩ := (hF.places p).1 hp
      exact hz_i i
    · exact off_mono (fun p' hp' => hp'.symm ▸ hp) hzQ.2
  have hz1 : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (fun _ => False) := by
    rw [at_eq']
    exact ⟨hzQ.1, hall⟩
  have := GlobalTheory.VacFixP.eq_one_of_grpAt (fun _ h => h) hz1
  exact ⟨y, mul_inv_eq_one.1 this, hy⟩

end GlobalTheory.QProd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lineVector_pairing_mem_inverseIdealCompletion : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L : HSp D) (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) (M : Lat S) (𝔠 : FI D) (v : Pl D), IsSelfDualC S M → LineId o ζ M 𝔠 v → 𝔠 ≠ 0 →
      ∀ y ∈ latV S M (· = v), cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v := by
  first | exact @GlobalTheory.LineDual.line_pair_mem_idV | exact GlobalTheory.LineDual.line_pair_mem_idV | (intros; apply GlobalTheory.LineDual.line_pair_mem_idV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.livechart_kernelVectors_realPoints_detPowers : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Real := by
  first | exact @GlobalTheory.KJRealLive.clsKL_real | exact GlobalTheory.KJRealLive.clsKL_real | (intros; apply GlobalTheory.KJRealLive.clsKL_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.vacuum_fixed_by_levelPair_at_selfDualPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  first | exact @GlobalTheory.VacFixP.vac_fix_on | exact GlobalTheory.VacFixP.vac_fix_on | (intros; apply GlobalTheory.VacFixP.vac_fix_on <;> assumption)
end
