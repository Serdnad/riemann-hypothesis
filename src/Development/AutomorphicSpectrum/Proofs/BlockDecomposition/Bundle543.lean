module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicWeightsCoefficient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle493
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddSingle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionDerivativeAtOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle502
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle517
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle504
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle521
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle522
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPushforwardHermitianMeasure
import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.harmonic_weights_coefficient : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ (F : Finset (Fin n → ℤ)), (∀ ν ∈ F, Antitone ν) → ∀ c : (Fin n → ℤ) → ℂ, (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ ν ∈ F, c ν * weylChar ν z = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2)) → ∀ μ ∈ harmZ lam, μ ∈ F ∧ c μ = 2 ^ n := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.coef_harm | exact GlobalTheory.CompanionTheory.CoefId.coef_harm | (intros; apply GlobalTheory.CompanionTheory.CoefId.coef_harm <;> assumption)
end

section

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


open GlobalTheory.CompanionTheory.ModelS.FFin in
theorem GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite (n : ℕ) (lam : Fin n → ℤ) (hl : Antitone lam) (lev : Fin n → ℕ)
    (hlev : IsLev lam lev) (F : GlobalTheory.CompanionTheory.ModelS.SmF n) (hF : F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev) :
    ∃ S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n), FiniteDimensional ℂ S ∧ F ∈ S ∧
      ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S := by
  obtain ⟨m, p, hp⟩ := fRaw_factor lam hl lev hlev
  set e := GlobalTheory.CompanionTheory.ModelS.dif (GlobalTheory.CompanionTheory.ModelS.yZ lam lev) with he
  have hfin : FiniteDimensional ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ p.totalDegree) := inferInstance
  refine ⟨(MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ p.totalDegree).map (wfL e m), inferInstance,
    ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_⟩, ?_⟩
  · apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · show wf e m p g = F.1 g
      rw [hF, hp g hg, wf, Set.indicator_of_mem hg]
    · show wf e m p g = F.1 g
      rw [wf, Set.indicator_of_notMem hg, F.2.2 g hg]
  · rintro a b _ ⟨q, hq, rfl⟩
    refine ⟨(if a = b then (m : ℂ) else 0) • q + Tp a b q,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hq) (Tp_mem a b _ hq), ?_⟩
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · rw [Kf_wf e m q (wfL e m q) rfl a b hg]
      show wf e m _ g = _
      rw [wf, Set.indicator_of_mem hg, evalPoints_add, evalEmbedding_smul]
    · show wf e m _ g = _
      rw [wf, Set.indicator_of_notMem hg, (GlobalTheory.CompanionTheory.ModelS.Kf a b (wfL e m q)).2.2 g hg]
end
end

section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.inducedFunction_derivative_at_one : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → ∀ a b : Fin n, lev b ≤ lev a → (e1 GlobalTheory.CompanionTheory.ModelS.DR a b F).1 1 = (if a = b then (lam a : ℂ) else 0) ∧ (f1 GlobalTheory.CompanionTheory.ModelS.DR a b F).1 1 = (if a = b then (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) else 0) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.FDer.fder | exact GlobalTheory.CompanionTheory.ModelS.FDer.fder | (intros; apply GlobalTheory.CompanionTheory.ModelS.FDer.fder <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

theorem _root_.GlobalTheory.T.standard_compact_frame_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), Dict → DictInf → IsCMExt F E σ → ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (B : Base F E) (K : Subgroup (G2 σ Y)), IsStdK (σ := σ) (Y := Y) B b K → ∀ x : G2 σ Y, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | exact GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ), Integrable P m.μ → ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.integral_fold | exact GlobalTheory.CompanionTheory.FJE.integral_fold | (intros; apply GlobalTheory.CompanionTheory.FJE.integral_fold <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenberg_character_bilinear_laws : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ x x' y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (x + x') y = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x' y) ∧ (∀ x y y' : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (y + y') = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y') ∧ (∀ x y : Mx D ρ p, ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y‖ = 1) ∧ (∀ x y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (-y) = conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y)) ∧ (∀ ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ξ) (GlobalTheory.CompanionTheory.FJE.rt ξ') = 1) ∧ Continuous (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.1 v.2) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.chv_facts | exact GlobalTheory.CompanionTheory.FJE.chv_facts | (intros; apply GlobalTheory.CompanionTheory.FJE.chv_facts <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

theorem _root_.GlobalTheory.T.periodic_partial_fourier_mean : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ), IsPer Φ → IsPer (pm hn m ψ b₀ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.isPer_pm | exact GlobalTheory.CompanionTheory.PcFc.isPer_pm | (intros; apply GlobalTheory.CompanionTheory.PcFc.isPer_pm <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

theorem _root_.GlobalTheory.T.rank_direct_sum_hermitian_lt : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | exact GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | (intros; apply GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

theorem _root_.GlobalTheory.T.hermitian_block_diagonal_normal_form : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n), ρ ≤ β.1.rank → ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | exact GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum | (intros; apply GlobalTheory.CompanionTheory.PcFc.exists_cg_dsum <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.shear_preserves_archimedean_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.coordW_map_shearK <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.shear_pushforward_hermitian_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → ∀ τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n → HeckeCharacterZeroLocus.SiegelWeilU.HermR (Ainf F) σ n, Measurable τ → (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ) (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) * S * GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearM a s) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n).map τ = GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.ShearHaar.coordHerm_map_shear <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.good_set_compact_linearly_independent : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology <;> assumption)
end
