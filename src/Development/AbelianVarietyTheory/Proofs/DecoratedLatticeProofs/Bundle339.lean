module

public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle024
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SeeSawFourier
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle009
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod GlobalTheory.LocFlat.CFac
open GlobalTheory.FinPl (SplitPt)
open GlobalTheory.IndefiniteRowSideFullHecke.SeeSawLineFourier (atW beta nrm OppLines IsLineFrame ofCol ofRow LineFourier SeeSawFourier)
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastCompare

theorem map_mem_integer {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (φ : k →* k') (hφ : Continuous φ)
    {a : k} (ha : a ∈ 𝒪[k]) : φ a ∈ 𝒪[k'] := by
  by_contra h
  rw [Valuation.mem_integer_iff, not_le] at h
  have hK : IsCompact (φ '' (𝒪[k] : Set k)) := (isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[k])).image hφ
  haveI : MulArchimedean (ValueGroupWithZero k') := ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h0 : valuation k' (φ a) ≠ 0 := (zero_lt_one.trans h).ne'
  have hU : ∀ n : ℕ, IsOpen {y : k' | valuation k' y < valuation k' (φ a) ^ n} := fun n => by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset ((IsValuativeTopology.hasBasis_nhds y).mem_of_mem (i := Units.mk0 _ (pow_ne_zero n h0)) trivial) ?_
    intro z hz
    have := (valuation k').map_add_lt hz hy
    simpa using this
  obtain ⟨n, hn⟩ := hK.elim_directed_cover _ hU (fun y _ => by
      obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k' y) h
      exact Set.mem_iUnion.2 ⟨n + 1, hn.trans_lt (pow_lt_pow_right₀ h n.lt_succ_self)⟩)
    (directed_of_isDirected_le fun m n hmn y hy => lt_of_lt_of_le hy (pow_le_pow_right₀ h.le hmn))
  have := hn ⟨a ^ n, pow_mem ha n, rfl⟩
  simp at this

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' n n' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n']

variable {q : SplitPt D k} {S T : HSp D} {s : k} {σ : Y' ≃ n'} {σ' : Y ≃ n} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
  {α : GlobalTheory.FinPl.Frame q S n'} {β : GlobalTheory.FinPl.Frame q T n}

section Lines

variable {L L'' : HSp D} {ζ₁ : Fin L.rank → D.host.E} {ζ : Fin L''.rank → D.host.E}

end Lines

end GlobalTheory.LastCompare

end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel Filter Topology
open GlobalTheory.LocMod GlobalTheory.LocMod.Witness
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatFBCompare

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem val_lt_one_iff (x : K) : valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ (not_lt.1 hx)
  exact absurd hn (not_lt.2 h2)

end Val

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  [Fintype Z'] [DecidableEq Z'] {S T : HSp D}

section Scal

variable {K : Type} [Field K] {γ t : Kˣ} {s : K} {σ : ℕ}

end Scal

section Frames

variable {q : GlobalTheory.FinPl.SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {σ : ℕ}
  {γ t : kˣ} {s : k} (hγ : (γ : k) = (Place.ofSplitPt q).xi) (ht : (t : k) = s * γ ^ (σ + 1))
include hγ ht

end Frames

section Local

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

variable [MeasurableSpace k] [BorelSpace k] {c : ℕ}

end Local

section Change

variable {q : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {σ : ℕ} {γ γ' t : kˣ}

end Change

section Rename₂

variable {n m A B : Type} [Fintype n] [DecidableEq n] [Unique A] [Unique B] (a : k)

end Rename₂

end GlobalTheory.FlatFBCompare
end
end
