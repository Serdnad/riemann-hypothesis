module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AddPtW
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle003
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle005
public import Formalism.PeriodIntegrals.Bundle008
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle006
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle008
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle012
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
import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh

@[expose] public section

section

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

section

variable {p : ℕ} [Fact p.Prime]

theorem ptW_X {σ : Type} (i : σ) : PtW (Xv i : MvPowerSeries σ ℂ_[p]) := by
  classical
  unfold PtW
  constructor
  · intro n
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp

theorem coefWf_add {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f + g) := (coefWfRing_holds p σ f g hf hg).1

theorem coefWf_sub {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f - g) := (coefWfRing_holds p σ f g hf hg).2.1

theorem coefWf_phAt (g : G1 p) (hph : CoefWf g.ph) {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : PtW a) : CoefWf (g.phAt a) := by
  obtain ⟨ha1, ha2⟩ := ha
  exact substWf_holds p σ g.ph a hph ha1 ha2

theorem coefWf_be (HA : AddPtW) (g : G1 p) (hOk : g.Ok) (hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hph : CoefWf g.ph) {σ : Type} {a b : MvPowerSeries σ ℂ_[p]} (ha : PtW a) (hb : PtW b) : CoefWf (g.be a b) := by
  have hab : PtW (g.add a b) := HA p g hOk hF σ a b ha hb
  show CoefWf (g.phAt (g.add a b) - g.phAt a - g.phAt b)
  exact coefWf_sub (coefWf_sub (coefWf_phAt g hph hab) (coefWf_phAt g hph ha)) (coefWf_phAt g hph hb)

theorem simeqW_of {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) (h : Simeq f g) : SimeqW f g := by

  obtain ⟨h0, hI⟩ := h
  have hr : SimeqW (f - g) 0 :=
    readW_holds p σ (f - g) (coefWf_sub hf hg) (And.intro (by simpa using h0) (by simpa using hI))
  obtain ⟨r0, rI⟩ := hr
  exact And.intro (by simpa using r0) (by simpa using rI)

end

end Formalism.MainNotions.Ext
end

section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

theorem ph0 {p : ℕ} [Fact p.Prime] (g : G1 p) : PowerSeries.constantCoeff g.ph = 0 := by
  unfold G1.ph
  rw [map_neg, neg_eq_zero]
  show logMv _ 0 = 0
  unfold logMv
  simp

theorem fglData {p : ℕ} [Fact p.Prime] (g : G1 p) (h : g.Ok) : PI.FglGram.Data g.l g.ex g.ph :=
  ⟨h.2.2.1, h.2.2.2, ph0 g⟩

theorem cube_of_two_identities_holds : CubeOfTwoIdentities := by
  intro p _ g h
  exact cube_relation_of_parallelogram p g.l g.ex g.ph (fglData g h)

theorem phGramG_holds : PhGramG := by
  first
  | exact phase_gram'
  | (intro p _ g; intros; apply phase_gram' <;> first | exact fglData g ‹_› | assumption)
  | (unfold PhGramG; done)

theorem gramUnitEq_holds : GramUnitEq := by
  first
  | exact gramExpansion_orthonormal
  | (intro p _ g; intros; apply gramExpansion_orthonormal <;> first | exact fglData g ‹_› | assumption)
  | (unfold GramUnitEq; done)

theorem jetsHigh_holds : JetsHigh :=
  fun p _ g hOk => jets_high p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsOne_holds : JetsOne :=
  fun p _ g hOk => jets_one p g.W g.wq g.ex g.ph hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1 hOk.2.2.1
    hOk.2.2.2

theorem jetsTwo_holds : JetsTwo :=
  fun p _ g a b hOk => jets_two p g.W g.wq g.ex g.ph a b hOk.1.1 hOk.1.2.1 hOk.1.2.2.1 hOk.1.2.2.2.1 hOk.1.2.2.2.2.1 hOk.2.1
    hOk.2.2.1 hOk.2.2.2

end Formalism.MainNotions.Ext.CutA
end

section

namespace Formalism.MainNotions.Ext

theorem okpInertG_holds : OkpInertG := integers_inert_prime

theorem inertPrime_holds : InertPrime := isPrime_span_of_jacobi_neg_one

theorem okpInert_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.okpInert D := okpInert_of okpInertG_holds inertPrime_holds D

end Formalism.MainNotions.Ext
end
