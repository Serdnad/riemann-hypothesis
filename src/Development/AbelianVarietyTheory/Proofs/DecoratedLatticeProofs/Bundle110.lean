module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLoss
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsOther
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle107
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle006

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem hasTypes_of_hasParam_of_group : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar →
    ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ),
      IsParam lam → HasParam R lam → HasTypes R lam := by
  intro hL hK hD p q hpq T R lam hlam hR
  have hn : 0 < p + q := hpq
  obtain ⟨P, e, -, hB, hcase⟩ := isParam_cases hlam
  rcases hcase with rfl | rfl
  · obtain ⟨σ, hf, hds⟩ := (hasParam_iff_factors R hn P hB).1 hR
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering hL hK hD p q (p + q) e P T R σ hB hf hds
  · obtain ⟨σ, hπ, hds⟩ := (hasParam_half_iff R hn P hB).1 hR
    have hf : Factors (Cover.twist R).U e σ := (factors_twist_iff R σ).2 hπ
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist p q T R (blockPar P e)
      (GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering hL hK hD p q (p + q) e P T (Cover.twist R) σ hB hf hds)

end GlobalTheory.CoverDS
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corankSums_bound_with_expLoss : ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ), Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k m f b g v NT 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi → 0 ≤ Gam → Gam ≤ Real.exp ((k : ℝ) / 8) → ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f) ∧ ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi ≤ Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
  first | exact @GlobalTheory.Core.Deg.corankSums_expLoss | exact GlobalTheory.Core.Deg.corankSums_expLoss | (intros; apply GlobalTheory.Core.Deg.corankSums_expLoss <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem diag_abstract_collisions_once :
    ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X one Pg B A₁ A₂ hPg hA hNg hNn hG hO hC hI hB h1 h2
  have hE := Formalism.FourierDecayAlt.P.equal_index
  have hF := Formalism.FourierDecayAlt.P.subfamilyAlt τ Rw I H H₁ X hA
  obtain ⟨_, _, hng⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ X hA hO hC

  have hgen : X.PhiEq X.genSet = X.pairSum (X.big X.genSet) + X.pairSum (X.one X.genSet) := by
    let Y : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁ := { X with scal := fun _ _ => True }
    obtain ⟨_, hg, _⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ Y hA hO hC
    have e1 : Y.nsc Y.genSet = ∅ := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.nsc]
    have e2 : Y.sc Y.genSet = X.one X.genSet := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.sc, Formalism.FourierDecayAlt.PB.Terms.one, Formalism.FourierDecayAlt.PB.Terms.allPairs,
        Formalism.FourierDecayAlt.PB.Terms.genSet]
    have e0 : Y.pairSum ∅ = 0 := by simp [Formalism.FourierDecayAlt.PB.Terms.pairSum]
    rw [e1, e2, e0, add_zero] at hg
    exact hg

  have hS : Summable (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) := by
    have hv := hA.2.1
    have hm : Summable (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) :=
      hv.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_inner_le_norm _ _) hm
  have hdisj : Disjoint (X.big X.genSet) (X.big X.ngSet) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hq.1.1.2 hp.1.1.2
  have hunion : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) =
      X.pairAbs (X.big X.genSet ∪ X.big X.ngSet) := by
    unfold Formalism.FourierDecayAlt.PB.Terms.pairAbs
    rw [Set.indicator_union_of_disjoint hdisj]
    beta_reduce
    rw [Summable.tsum_add (hS.indicator _) (hS.indicator _), mul_add]
  have hsub : X.big X.genSet ∪ X.big X.ngSet ⊆ X.big X.nzSet := by
    rintro p (hp | hp)
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
  have hsum : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) ≤ B := by
    rw [hunion]; exact (hF _ _ hsub).1.trans hB
  have bg : X.pairSum (X.big X.genSet) ≤ X.pairAbs (X.big X.genSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have bn : X.pairSum (X.big X.ngSet) ≤ X.pairAbs (X.big X.ngSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have g1 : ‖X.part X.genSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.genSet) + A₁) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.genSet hNg hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hgen]; linarith
  have g2 : ‖X.part X.ngSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.ngSet) + A₂) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.ngSet hNn hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hng]; linarith
  have hK : X.K0 - one = X.part X.genSet + X.part X.ngSet := by
    unfold Formalism.FourierDecayAlt.PB.Terms.K0
    rw [← hI]
    abel
  rw [hK]
  have hpar : ‖X.part X.genSet + X.part X.ngSet‖ ^ 2 ≤
      2 * ‖X.part X.genSet‖ ^ 2 + 2 * ‖X.part X.ngSet‖ ^ 2 := by
    have := norm_add_le (X.part X.genSet) (X.part X.ngSet)
    have h0 := norm_nonneg (X.part X.genSet + X.part X.ngSet)
    nlinarith [sq_nonneg (‖X.part X.genSet‖ - ‖X.part X.ngSet‖), norm_nonneg (X.part X.genSet),
      norm_nonneg (X.part X.ngSet)]
  have hfin : Pg * (X.pairAbs (X.big X.genSet) + A₁) + Pg * (X.pairAbs (X.big X.ngSet) + A₂) ≤
      Pg * (B + A₁ + A₂) := by
    rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hPg; linarith
  linarith

end GlobalTheory
end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corankSizeHypothesis_explicitConstant_siegelMass : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  first | exact @GlobalTheory.Core.Deg.xiSizes_explicit | exact GlobalTheory.Core.Deg.xiSizes_explicit | (intros; apply GlobalTheory.Core.Deg.xiSizes_explicit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.size_bounds_of_standingHypotheses : ∀ M : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1000 ≤ Cl ∧ M ≤ Cl ∧ M ≤ (D.R.m : ℝ) ∧ M ≤ (D.R.k : ℝ) ∧ D.host.rdE ≤ large₂.sc.b ∧ (D.R.k : ℝ) ^ M ≤ large₂.sc.b ∧ (D.R.r : ℝ) ≤ large₂.sc.b ∧ (D.R.m : ℝ) ^ 2 ≤ D.R.k ∧ M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
  first | exact @GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses | exact GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses | (intros; apply GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.exists_threshold_criticalLevel_lower_bound : ∀ cb Cu : ℝ, 0 < cb → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cT CT C0 : ℝ), thr ≤ Cl → (∀ τ, VV D τ = vand (lamSH D.R (D.hc τ))) → UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.CritLevelSize.tcritLow_sizes | exact GlobalTheory.CritLevelSize.tcritLow_sizes | (intros; apply GlobalTheory.CritLevelSize.tcritLow_sizes <;> assumption)
end

end

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.abstractDiagonalBound_collisions_counted_once : ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  first | exact @GlobalTheory.diag_abstract_collisions_once | exact GlobalTheory.diag_abstract_collisions_once | (intros; apply GlobalTheory.diag_abstract_collisions_once <;> assumption)

end
end
