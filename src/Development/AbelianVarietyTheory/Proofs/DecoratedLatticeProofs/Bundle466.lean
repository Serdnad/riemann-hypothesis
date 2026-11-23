module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBox
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle454
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedThetaLiftCommutesSplitPlaceOperators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle429
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle445
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle336
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle446
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SchwartzSch

variable {D : D7}

def volOf {A B : HSp D} (ν : Measure (WO A B)) (𝓨 : Set (WO A B)) (h : IsCovolOne (ratL B A) ν 𝓨) :
    GlobalTheory.Unf.VolM D B.rank A.rank := ⟨ν, 𝓨, h⟩

theorem continuous_finPart' : Continuous (finPart D) := by
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
  rw [this]
  exact continuous_snd.comp hec

variable {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {A B : HSp D} {ν : Measure (WO A B)}
  {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ} (hf : IsThetaFunO ψ (dblSp A) B f)

include hψ hν hf

theorem sch_level : ∃ U : AddSubgroup (Mx D B.rank A.rank), IsOpen (U : Set (Mx D B.rank A.rank)) ∧
    ∀ u ∈ U, u.map (infPart D) = 0 → ∀ x, sch ψ A B ν 𝓨 f (x + u) = sch ψ A B ν 𝓨 f x := by
  obtain ⟨U, hUo, hU⟩ := hf.level
  refine ⟨U.comap ((dblDec A).extX B), ?_, ?_⟩
  · have hX : Continuous ((dblDec A).extX B) := continuous_id.matrix_mul continuous_const
    exact hUo.preimage hX
  · intro u hu h0 x
    have h0' : ((dblDec A).extX B u).map (infPart D) = 0 := by
      rw [HypDec.extX_apply, Matrix.map_mul, h0, Matrix.zero_mul]
    have h := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) f hf).1 x u
    rw [hU _ hu h0'] at h
    exact (congrFun h 0).symm

theorem sch_supp : ∃ K : Set (Matrix (Fin B.rank) (Fin A.rank) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧
    ∀ x, sch ψ A B ν 𝓨 f x ≠ 0 → x.map (finPart D) ∈ K := by
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨K, hK, hsupp⟩ :=
    GlobalTheory.Unf.mixS_support_inBox D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) U hUo
  refine ⟨(fun k : Mx D B.rank A.rank => k.map (finPart D)) '' K,
    hK.image (continuous_id.matrix_map continuous_finPart'), ?_⟩
  intro x hx
  have hmem : f ∈ GlobalTheory.Size.thetaLevel ψ (dblSp A) B U := ⟨hf, hU⟩
  obtain ⟨k, hk, hxk⟩ := hsupp f hmem x 0 hx
  refine ⟨k, hk, ?_⟩
  have hs : (x - k).map (finPart D) = x.map (finPart D) - k.map (finPart D) :=
    Matrix.map_sub _ (fun a b => (finPart D).map_sub a b) x k
  rw [hs, sub_eq_zero] at hxk
  exact hxk.symm

theorem sch_schwartz (k : ℕ) (L : (Fin k → ℝ) →+ Mx D B.rank A.rank) (hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L)
    (hinj : Function.Injective L) (x : Mx D B.rank A.rank) :
    ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = sch ψ A B ν 𝓨 f (x + L t) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let V : Set ((Fin k → ℝ) → ℂ) :=
    {φ | ∃ f', IsThetaFunO ψ (dblSp A) B f' ∧ φ = fun t => sch ψ A B ν 𝓨 f' (x + L t)}
  have hcont : ∀ φ ∈ V, Continuous φ := by
    rintro φ ⟨f', hf', rfl⟩
    exact (GlobalTheory.T.doubledPairSchrodingerFunction_continuous_integrable D ψ hψ A B ν 𝓨 hν f' hf').1.comp (continuous_const.add hL.1)
  have hder : ∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ t : Fin k → ℝ,
      HasDerivAt (fun s : ℝ => φ (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' t) 0 := by
    rintro φ ⟨f', hf', rfl⟩ i
    let M : ℝ →+ Mx D B.rank A.rank :=
      { toFun := fun s => L (s • (Pi.single i (1 : ℝ) : Fin k → ℝ))
        map_zero' := by rw [zero_smul, map_zero]
        map_add' := fun a b => by rw [add_smul, map_add (f := _)] }
    have hMc : Continuous M := hL.1.comp (continuous_id.smul continuous_const)
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hL.2 _
    obtain ⟨f'', hf'', hd⟩ := GlobalTheory.T.schroedingerFunction_hasDerivAt_real_line_doubledPair D ψ hψ A B ν 𝓨 hν f' hf' M hMc hMf
    refine ⟨fun t => sch ψ A B ν 𝓨 f'' (x + L t), ⟨f'', hf'', rfl⟩, fun t => ?_⟩
    have h := hd (x + L t)
    have he : (fun s : ℝ => sch ψ A B ν 𝓨 f' (x + L (t + s • (Pi.single i (1 : ℝ) : Fin k → ℝ)))) =
        fun s : ℝ => sch ψ A B ν 𝓨 f' (x + L t + M s) := by
      funext s
      simp only [map_add (f := _), add_assoc]
      rfl
    simp only at h ⊢
    rw [he]
    exact h
  have hdecay : ∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ t, ‖t‖ ^ N * ‖φ t‖ ≤ C := by
    rintro φ ⟨f', hf', rfl⟩ N
    obtain ⟨C₁, hC₁⟩ := (GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation D θ hθ B.rank A.rank k L hL).2 hinj
    obtain ⟨C₂, hC₂⟩ :=
      GlobalTheory.Unf.mixS_decay D ψ hψ θ hθ (dblSp A) (zeroSp D) B A.rank (dblDec A) (volOf ν 𝓨 hν) N
    have hfin := (GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ (dblSp A) B).1 N f' hf'
    have hne : (C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f' ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
    set c : ℝ := |C₁| * (1 + GlobalTheory.Unf.realSize θ x) with hc
    have hc0 : 0 ≤ c := mul_nonneg (abs_nonneg _) (by linarith [GlobalTheory.Unf.realSize_nonneg θ x])
    clear_value c
    refine ⟨c ^ N * ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal, fun t => ?_⟩
    have hy0 := GlobalTheory.Unf.realSize_nonneg θ (x + L t)
    have hx0 := GlobalTheory.Unf.realSize_nonneg θ x
    have h1 : ‖t‖ ≤ c * (1 + GlobalTheory.Unf.realSize θ (x + L t)) := by
      calc ‖t‖ ≤ C₁ * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) := hC₁ x t
        _ ≤ |C₁| * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
        _ ≤ |C₁| * ((1 + GlobalTheory.Unf.realSize θ x) * (1 + GlobalTheory.Unf.realSize θ (x + L t))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
        _ = c * (1 + GlobalTheory.Unf.realSize θ (x + L t)) := by rw [hc]; ring
    have h2 : ‖sch ψ A B ν 𝓨 f' (x + L t)‖ * (1 + GlobalTheory.Unf.realSize θ (x + L t)) ^ N ≤
        ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal := by
      have h := hC₂ f' hf' (x + L t) 0
      change ‖sch ψ A B ν 𝓨 f' (x + L t)‖ₑ * _ ≤ _ at h
      rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at h
      exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h
    calc ‖t‖ ^ N * ‖sch ψ A B ν 𝓨 f' (x + L t)‖
        ≤ (c * (1 + GlobalTheory.Unf.realSize θ (x + L t))) ^ N * ‖sch ψ A B ν 𝓨 f' (x + L t)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 N) (norm_nonneg _)
      _ = c ^ N * (‖sch ψ A B ν 𝓨 f' (x + L t)‖ * (1 + GlobalTheory.Unf.realSize θ (x + L t)) ^ N) := by
          generalize ‖sch ψ A B ν 𝓨 f' (x + L t)‖ = a
          generalize GlobalTheory.Unf.realSize θ (x + L t) = s
          rw [mul_pow]; ring
      _ ≤ c ^ N * ((C₂ : ℝ≥0∞) * GlobalTheory.Unf.supSob ψ θ N f').toReal :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hc0 N)
  have hS := (GlobalTheory.T.derivativeClosedFunctionClass_smooth_and_schwartz k V hcont hder).2 hdecay _ ⟨f, hf, rfl⟩
  exact hS


omit hψ hν hf in
theorem isSchwartzBruhat_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    ∀ f, IsThetaFunO ψ (dblSp A) B f → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (sch ψ A B ν 𝓨 f) := by
  intro D ψ hψ A B ν 𝓨 hν f hf
  exact ⟨sch_level hψ hν hf, sch_supp hψ hν hf, fun k L hL hinj x => sch_schwartz hψ hν hf k L hL hinj x⟩

end GlobalTheory.SchwartzSch
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing MeasureTheory

noncomputable section

namespace GlobalTheory.FinPl.LiftExactPf

theorem frame_card {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (α : Frame p S n) :
    Fintype.card n = S.rank := by
  have h1 := Matrix.rank_mul_le_left α.b α.b'
  have h2 := Matrix.rank_mul_le_left α.b' α.b
  rw [α.bb', Matrix.rank_one] at h1
  rw [α.b'b, Matrix.rank_one] at h2
  have h3 := Matrix.rank_le_card_width α.b
  have h4 := Matrix.rank_le_card_width α.b'
  simp only [Fintype.card_fin] at h1 h4
  omega

theorem chrPow_mul_neg {D : D7} (χ : (AE D)ˣ →* Circle) (a : (AE D)ˣ) (e : ℤ) :
    chrPow χ a e * chrPow χ a (-e) = 1 := by
  unfold chrPow
  rw [← Circle.coe_mul, ← zpow_add, add_neg_cancel, zpow_zero, Circle.coe_one]

end GlobalTheory.FinPl.LiftExactPf

namespace GlobalTheory.FinPl


open GlobalTheory.FinPl.LiftRam GlobalTheory.FinPl.LiftExactPf in
theorem liftExact : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  intro D k _ _ _ _ p q χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' _ _ _ _ ψ S T hS vS χS χT om hW hχS hχT α β P Q a ha LS LT f₀ f hOv φ₀ hφ₀ ε
  have haq : a = p.idele q.unit := Units.ext (by rw [SplitPt.idele_val, ha]; abel)
  subst haq
  obtain ⟨lS, lT, hlS, hlT, hlSq, hlTq, hlinE⟩ := GlobalTheory.T.linearModel_splitPlace_characterEquivariance D k p q ψ S T χS χT om hW
  obtain ⟨lS₀, lT₀, -, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  have hK := GlobalTheory.T.kernelsCommuteExplicitConstAlt k n n' q χ hχ lS lT (hlS hχT) (hlT hχS) P Q
  have hOv2 := hOv
  obtain ⟨hLS, hLT, hVac, -, -⟩ := hOv2
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n n' ψ hW.std S T α β LS LT hLS hLT f₀ hVac

  let F : SB (Matrix n n' k) → WO S T → ℂ := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose
  have hF : ∀ Ψ : SB (Matrix n n' k), Over ψ α β LS LT f₀ Ψ.1 (F Ψ) := fun Ψ => (hex Ψ.1 Ψ.2).exists.choose_spec
  have hFu : ∀ (Ψ : SB (Matrix n n' k)) g, Over ψ α β LS LT f₀ Ψ.1 g → g = F Ψ :=
    fun Ψ g hg => (hex Ψ.1 Ψ.2).unique hg (hF Ψ)
  have hFth : ∀ Ψ, IsThetaFunO ψ S T (F Ψ) := fun Ψ => (hth _ _ (hF Ψ)).1
  have hFlin : ∀ (a : ℂ) (Ψ Ψ' : SB (Matrix n n' k)), F (a • Ψ + Ψ') = a • F Ψ + F Ψ' := fun a Ψ Ψ' =>
    (hFu (a • Ψ + Ψ') _ ((hlin n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ)).2.2 a Ψ'.1 (F Ψ') (hF Ψ'))).symm
  have hF0 : F 0 = 0 := by
    have h1 := hFlin 1 0 0
    simp only [one_smul, add_zero] at h1
    have h2 : F 0 + F 0 = F 0 + 0 := by rw [← h1, add_zero]
    exact add_left_cancel h2
  have hFadd : ∀ Ψ Ψ' : SB (Matrix n n' k), F (Ψ + Ψ') = F Ψ + F Ψ' := fun Ψ Ψ' => by
    simpa using hFlin 1 Ψ Ψ'
  have hFsmul : ∀ (a : ℂ) (Ψ : SB (Matrix n n' k)), F (a • Ψ) = a • F Ψ := fun a Ψ => by
    simpa [hF0] using hFlin a Ψ 0
  have hint : ∀ (v : contAutSub S) (Ψ : SB (Matrix n n' k)) h,
      IntegrableOn (fun g => om (g, h) (F Ψ) 0 * v.1 g) vS.𝓕 vS.μ :=
    fun v Ψ h => (lift_facts hS vS hW (hFth Ψ) v.2).1 h

  let θ : contAutSub S →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] (GA D T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Ψ => liftT om vS.μ vS.𝓕 v.1 (F Ψ))
      (fun v₁ v₂ Ψ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, Submodule.coe_add, mul_add]
        exact integral_add (hint v₁ Ψ h) (hint v₂ Ψ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_left_comm _ a]
        exact integral_const_mul a _)
      (fun v Ψ₁ Ψ₂ => by
        funext h
        simp only [liftT_apply, Pi.add_apply, hFadd, map_add (f := _), add_mul]
        exact integral_add (hint v Ψ₁ h) (hint v Ψ₂ h))
      (fun a v Ψ => by
        funext h
        simp only [liftT_apply, Pi.smul_apply, hFsmul, map_smul, smul_eq_mul, mul_assoc]
        exact integral_const_mul a _)
  have hθ : ∀ v Ψ, θ v Ψ = liftT om vS.μ vS.𝓕 v.1 (F Ψ) := fun v Ψ => rfl
  have hEq : ∀ (g : GL n' k) (h : GL n k) (v : contAutSub S) (Ψ Ψ' : SB (Matrix n n' k)),
      (∀ x, Ψ'.1 x = (lS (Matrix.GeneralLinearGroup.det g) : ℂ) * (lT (Matrix.GeneralLinearGroup.det h) : ℂ) *
        Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (repAut α g v) Ψ' = β.rep h (θ v Ψ) := by
    intro g h v Ψ Ψ' hΨ
    have e : F Ψ' = om (α.gl g, β.gl h) (F Ψ) := by
      refine (hFu Ψ' _ ?_).symm
      have := hlinE n n' α β LS LT f₀ Ψ.1 (F Ψ) (hF Ψ) g h
      convert this using 1
      funext x
      exact hΨ x
    funext h₁
    rw [hθ, hθ, rep_apply, liftT_apply, liftT_apply, e, repAut_val]
    simp only [rep_apply, LiftRam.om_mul]
    exact setIntegral_mul_right hS vS (fun x => om (x, h₁ * β.gl h) (F Ψ) 0 * v.1 x)
      (fun γ hγ x => by rw [om_left hW (hFth Ψ) hγ, v.2.1 γ hγ x]) (α.gl g)
  obtain ⟨K, hKval, hKdia, hKram⟩ := hK (contAutSub S) (GA D T → ℂ) (repAut α) β.rep θ hEq
  obtain ⟨φ, ⟨hφE, hφM, hφC⟩, rfl⟩ := hφ₀
  let φ' : EqForm (repAut α) := ⟨toAut hφC, fun g P₁ => Subtype.ext (hφE g P₁)⟩
  have hφ'M : φ'.1 ∈ Mram k n' (contAutSub S) := by
    letI := Fintype.ofFinite 𝓀[k]ˣ
    refine (mem_Mram _).2 fun P₁ => Subtype.ext ?_
    have := (mem_Mram _).1 hφM P₁
    simpa [φ', toAut, Submodule.coe_sum] using this
  have hFf : F (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) = f := (hFu _ f hOv).symm
  have hfth : IsThetaFunO ψ S T f := hFf ▸ hFth _
  set φT : Form k n (GA D T → ℂ) := (K φ').1 with hφT
  have hφTQ : φT Q = liftT om vS.μ vS.𝓕 (φ P) f := by
    rw [hφT, hKval φ', hθ, hFf]
    rfl
  have hcQ : IsContAut T (φT Q) := by
    rw [hφTQ]
    exact (lift_facts hS vS hW hfth (hφC P)).2
  have hRam : IsRam β φT := by
    refine ⟨(K φ').2, (hKram φ' hφ'M).1, fun Q' => ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q Q'
    have e : φT (g • Q) = β.rep g (φT Q) := (K φ').2 g Q
    rw [e]
    exact isContAut_mul_right hcQ (β.gl g)
  set c : ℂ := (lS q.unit : ℂ) * (lT q.unit : ℂ) with hc
  have h1 := (hKram φ' hφ'M).2
  have h2 := hKdia ε ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩
  have h3 := hKval ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩
  have key : liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f =
      c • FFStar q (resChar χ hχ q) φT (ε • Q) := by
    calc liftT om vS.μ vS.𝓕 (FFStar q (resChar χ hχ q) φ (ε • P)) f
        = θ (dia ε (FFStar q (resChar χ hχ q) φ'.1) P) (GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOneSB P Q) := by
          rw [hθ, hFf, dia_apply]
          exact congrArg (liftT om vS.μ vS.𝓕 · f) (toAut_FFStar q _ hφC (ε • P)).symm
      _ = (K ⟨dia ε (FFStar q (resChar χ hχ q) φ'.1), dia_mem_EqForm ε (FFStar_mem_EqForm q _ φ'.2)⟩).1 Q := h3.symm
      _ = dia ε (K ⟨FFStar q (resChar χ hχ q) φ'.1, FFStar_mem_EqForm q _ φ'.2⟩).1 Q := by rw [h2]
      _ = c • FFStar q (resChar χ hχ q) φT (ε • Q) := by rw [h1, dia_apply]; rfl

  have hQ : (0 : ℝ) < resCard k := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hnT := frame_card β
  have hnS := frame_card α
  have hR : ((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2)) * ((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2)) *
      ((resCard k : ℝ) ^ ((S.rank : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add hQ, ← Real.rpow_add hQ, hnT, hnS]
    convert Real.rpow_zero (resCard k : ℝ) using 2
    ring
  have hR' : (((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      (((resCard k : ℝ) ^ (-(T.rank : ℝ) / 2) : ℝ) : ℂ) * (((resCard k : ℝ) ^ ((S.rank : ℝ) / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hR
  have eS := chrPow_mul_neg χS (p.idele q.unit) (-1)
  have eT := chrPow_mul_neg χT (p.idele q.unit) 1
  simp only [neg_neg] at eS ⊢
  have hCc : ((((resCard k : ℝ) ^ (((Fintype.card n : ℝ) - Fintype.card n') / 2) : ℝ) : ℂ) *
      chrPow χS (p.idele q.unit) (-1) * chrPow χT (p.idele q.unit) 1) * c = 1 := by
    rw [hc, hlSq, hlTq]
    linear_combination (chrPow χS (p.idele q.unit) (-1) * chrPow χS (p.idele q.unit) 1 *
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1))) * hR' +
      (chrPow χT (p.idele q.unit) 1 * chrPow χT (p.idele q.unit) (-1)) * eS + eT
  rw [← hφTQ]
  unfold sOp
  rw [formAt_eq α hφE P, formAt_eq β hRam.1 Q, dia_apply, dia_apply, key, smul_smul, hCc, one_smul]

end GlobalTheory.FinPl

end
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

open Classical

namespace GlobalTheory.Core.Rk.Exh.SmallSupp

theorem selfDual_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem wcoef_eq_zero_off_prin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  intro D ψ θ A H χA om sA sH _hθ _hη hW _hcA _hcH hrank β Z hP βH f₀ f hβH hvec hthf ν 𝓕 hν g hg hnot
  have sdA := selfDual_frameLat A
  have sdH := selfDual_frameLat H
  obtain ⟨_hvac, e, he, hth⟩ := hvec
  have hQ : (prinDat A Z).Q = ∅ := rfl
  have hPg : (prinDat A Z).Pg = Z := rfl
  have hint : ∀ v, (∀ PP ∈ (prinDat A Z).Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig A.gram (frameLat A) v := by
    intro v hv
    apply hg v
    intro hmem
    simp only [under, Finset.mem_image] at hmem
    obtain ⟨PP, hPP, hPPv⟩ := hmem
    exact hv PP (hPg ▸ hPP) hPPv
  have hsupp := fun x hx => by_contra fun h => hnot
    (GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero D A H (frameLat A) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1) e sdA hP.frame hrank hQ he g hint x hx h)
  have hsb := GlobalTheory.T.thetaChainStep_finiteDatum_isSchwartzBruhat_half D A H (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) (fun _ => 1)
    ((prinDat A Z).Pg ∪ ∅) e sdA sdH hP.frame hβH he
  obtain ⟨n, a, y, -, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D ψ A H hW.std (frameLat A) (frameLat H) sdA sdH
    ((prinDat A Z).Pg ∪ ∅) e he f₀ _ f hsb hth g hsupp
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D ψ A H χA 1 om hW ν 𝓕 hν f hthf g n a y h1 h2

end GlobalTheory.Core.Rk.Exh.SmallSupp
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

theorem _root_.GlobalTheory.T.principalCongruence_fixes_definiteStepVector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f → ∀ κ ∈ prin A β Z, om (κ, 1) f = f := by
  first | exact @GlobalTheory.SmallFix.prin_fixes_stepVec | exact GlobalTheory.SmallFix.prin_fixes_stepVec | (intros; apply GlobalTheory.SmallFix.prin_fixes_stepVec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartLevel_component_fixes_standardPair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ κ ∈ A.U j b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), κ * ((β j i).gl g)⁻¹ ∈ grpOff ((I.rec7 l Z).sp.X j) (· = (p i).v) → g • Q j i = Q j i := by
  first | exact @GlobalTheory.AdForm.comp_fixes_stdPair | exact GlobalTheory.AdForm.comp_fixes_stdPair | (intros; apply GlobalTheory.AdForm.comp_fixes_stdPair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_chartPoint_rightTranslate_stabilizer_splitPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  first | exact @GlobalTheory.AdForm.DiaChart.ptOf_gl_dia | exact GlobalTheory.AdForm.DiaChart.ptOf_gl_dia | (intros; apply GlobalTheory.AdForm.DiaChart.ptOf_gl_dia <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  first | exact @GlobalTheory.AdForm.exists_readsG_of_level | exact GlobalTheory.AdForm.exists_readsG_of_level | (intros; apply GlobalTheory.AdForm.exists_readsG_of_level <;> assumption)
end
