module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle491
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjugateWeilDatumHermitianSpaceNeg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle642
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle601
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle494
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle459
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.exists_central_element_homothetic_gluedCores : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M M' : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k) (P : GlobalTheory.LatPair.Pair k n) (a₀ : GA D A), 3 ≤ Fintype.card n → IsSumFrame o ζ β β₀ → IsSelfDualC S M → IsSelfDualC S M' → β₀.IsLat M (GlobalTheory.LatPair.gluedS q 1 P.ker P.vec) → μ ≠ 0 → LineAt (vecB o ζ) μ M' p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → (∀ a ∈ grpAt A (· = p.v), Moves S (o.emb (a, 1)) M M (· = p.v) ↔ Moves S (o.emb (a₀ * a * a₀⁻¹, 1)) M' M' (· = p.v)) → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' p.v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves | exact GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves | (intros; apply GlobalTheory.Core.Mi.LatMatch.CoreHomothety.exists_central_sMoves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem homothetic_of_monomial_primitive_selfDual_cores : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S L → IsSelfDualC S L' → IsSelfDualC S₀ M → z ≠ 0 → MonoAt d L M v → MonoAt d L' M' v → PrimAt ψ d L v → PrimAt ψ d L' v → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → SMoves S c (d.emb0 γ) L L' v := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hL hL' hM hz hmL hmL' hpL hpL' hlL hlL' hc hγ hmv
  have hX : ∀ i : Fin ρ, ∀ a ∈ idAt D (· = v),
      (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
    suffices h : ∀ k : ℕ, ∀ i : Fin ρ, i.1 + k + 1 = ρ → ∀ a ∈ idAt D (· = v),
        (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) by
      intro i
      exact h (ρ - 1 - i.1) i (by omega)
    intro k
    induction k with
    | zero =>
      intro i hi
      exact GlobalTheory.T.lastIsotropicLine_homothety_matches_lattices D ψ S S₀ ρ d z L L' M M' v c γ hM hz hlL hlL' hc hγ hmv i (by omega)
    | succ k ih =>
      intro i hi
      exact GlobalTheory.T.primitive_character_matches_lines_down_flag D ψ S S₀ ρ d L L' v c hL hpL hpL' hc i ⟨i.1 + 1, by omega⟩ rfl
        (ih ⟨i.1 + 1, by omega⟩ (by simp only; omega))
  have hY := GlobalTheory.T.normOne_matchesIsotropicY_of_matchesIsotropicX D S S₀ ρ d L L' M M' v c hL hL' hmL hmL' hc hX
  intro y hy
  have hpX : d.pX *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pX *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have hpY : d.pY *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pY *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have hp0 : d.p0 *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) =
      c • (Formalism.L2.Theta.mt S₀ γ *ᵥ (d.p0 *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding, ← Matrix.mulVec_mulVec]
  rw [hmL y, hmL' _, hpX, hpY, hp0]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) ?_)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hX i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hY i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · exact hmv _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy)

end GlobalTheory.Core.Mi.LatMatch
end

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

noncomputable section

namespace GlobalTheory.Core.Rk.DoubleSpan

variable {D : D7}

theorem span_delta_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A W : HSp D) :
    (Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂} :
      Submodule ℂ (WO (dblSp A) W → ℂ)) =
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨f₁, f₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨f₁, fun x => starRingEnd ℂ (f₂ (-x)), h₁,
      GlobalTheory.CjNeg.theta_negS hψ (GlobalTheory.NegWeil.theta_refl h₂), ?_⟩
    funext x
    exact (GlobalTheory.DoublingTheta.boxS_apply A W f₁ (fun x => starRingEnd ℂ (f₂ (-x))) x).symm
  · refine Submodule.span_le.2 ?_
    rintro φ ⟨g₁, g₂, h₁, h₂, rfl⟩
    refine Submodule.subset_span ⟨g₁, fun x => starRingEnd ℂ (g₂ (-x)), h₁,
      GlobalTheory.NegWeil.theta_refl (GlobalTheory.CjNeg.theta_negS' hψ h₂), ?_⟩
    funext x
    refine ((GlobalTheory.DoublingTheta.boxS_apply A W g₁ g₂ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, neg_neg, Complex.conj_conj]

theorem prodSpan_theta_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S A B : HSp D}
    (o : GlobalTheory.MixModel.OrthDec S A B) (W : HSp D) :
    (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), IsThetaFunO ψ S W g) ∧
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W), ∀ w,
      heisO ψ S W w g ∈ GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS W) (IsThetaFunO ψ A W) (IsThetaFunO ψ B W) := by
  refine ⟨fun g hg => ?_, fun g hg w => ?_⟩
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      exact o.isThetaFunO_boxS hA hB
    | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ S W
    | add a b _ _ ha hb => exact Formalism.IndefR.Fock.CCR.theta_add ha hb
    | smul c a _ ha => exact Formalism.IndefR.Fock.CCR.theta_smul ha c
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hA, hB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hA (o.resS W w).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hB (o.resS W w).2, ?_⟩
      exact o.heisO_boxS ψ W fA fB w
    | zero =>
      have : heisO ψ S W w 0 = 0 := by funext x; simp [heisO]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : heisO ψ S W w (a + b) = heisO ψ S W w a + heisO ψ S W w b := by
        funext x; simp only [heisO, Pi.add_apply]; ring
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : heisO ψ S W w (c • a) = c • heisO ψ S W w a := by
        funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact Submodule.smul_mem _ c ha

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D), IsStdChar D ψ (-1) → let M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂}; (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧ ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := by
  intro D ψ A W hψ M
  have hM : M = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan ((GlobalTheory.DoublingTheta.sumDec A (negSp A)).resS W) (IsThetaFunO ψ A W)
      (IsThetaFunO ψ (negSp A) W) := span_delta_eq hψ A W
  obtain ⟨h1, h2⟩ := prodSpan_theta_heis hψ (GlobalTheory.DoublingTheta.sumDec A (negSp A)) W
  rw [hM]
  exact ⟨h1, h2, fun f hf =>
    GlobalTheory.DenseSum.unifLimit_prodSpan D ψ hψ _ A (negSp A) W (GlobalTheory.DoublingTheta.sumDec A (negSp A)) f hf⟩

end GlobalTheory.Core.Rk.DoubleSpan
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

theorem inputs_of_chosenSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
      GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (X : ProvA), ChosenSeries X → Inputs D X := by
  intro hDS hHC hDec hCW D X hX
  exact
    { chosen := hX
      hc := hHC
      decay := hDec
      bridge := GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
      vacChar := GlobalTheory.VacuumCharacter.vacChar D
      lie := GlobalTheory.LieScalar.lieFockAll D
      cpt := GlobalTheory.CompactFockAction.compactFockAll D
      dense := GlobalTheory.FockDensity.fockDense D
      laws := GlobalTheory.Chain.LiftReg.liftProps_obj hDec D
      const := GlobalTheory.T.constantTermLift_isotropicSubspace D
      ext := GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors hHC hCW D }

end GlobalTheory.PairLift
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


theorem _root_.GlobalTheory.T.doublingBasicIdentity_flatSection_cuspForms : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → ∀ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ → ∀ A : CptF V, ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → GlobalTheory.Eis.BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ := by
  first | exact @GlobalTheory.Core.Rk.IP.basicIdentity_flat | exact GlobalTheory.Core.Rk.IP.basicIdentity_flat | (intros; apply GlobalTheory.Core.Rk.IP.basicIdentity_flat <;> assumption)
end
