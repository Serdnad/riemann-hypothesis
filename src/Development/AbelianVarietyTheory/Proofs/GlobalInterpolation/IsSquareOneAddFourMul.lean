module

import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace GlobalTheory.HenselSquare

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

theorem isAdicComplete_integers (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    IsAdicComplete (maximalIdeal (u.adicCompletionIntegers F)) (u.adicCompletionIntegers F) := by
  first | exact _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers | exact @_root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers | apply _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers <;> assumption

theorem exists_sq_add_eq {O : Type} [CommRing O] [Nontrivial O] (I : Ideal O) [HenselianRing O I]
    (z : O) (hz : z ∈ I) : ∃ s : O, s ^ 2 + s = z := by
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 + X - C z) (by monicity!) 0
    (by simpa using hz) (by simp)
  refine ⟨s, ?_⟩
  have h2 : eval s (X ^ 2 + X - C z) = 0 := hs
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_C] at h2
  linear_combination h2

theorem isSquare_one_add_four_mul : ∀ (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (z : 𝓞 F), z ∈ u.asIdeal → IsSquare (algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F)) := by
  intro F _ _ u z hz
  haveI := isAdicComplete_integers F u
  set z' : u.adicCompletionIntegers F := algebraMap (𝓞 F) (u.adicCompletionIntegers F) z with hz'
  have hcoe : (z' : u.adicCompletion F) = algebraMap F (u.adicCompletion F) (z : F) := by
    rw [hz', algebraMap_adicCompletionIntegers_apply]
    rfl
  have hv : Valued.v (algebraMap F (u.adicCompletion F) (z : F)) < 1 := by
    have h1 : u.valuation F (algebraMap (𝓞 F) F z) < 1 := by
      rw [valuation_of_algebraMap]
      exact (intValuation_lt_one_iff_mem (v := u) z).2 hz
    have h2 : Valued.v (((z : F) : u.adicCompletion F)) = u.valuation F (z : F) :=
      valuedAdicCompletion_eq_valuation' (v := u) (z : F)
    exact (h2.trans_lt h1 :)
  have hzm : z' ∈ maximalIdeal (u.adicCompletionIntegers F) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one]
    rw [show (z'.1 : u.adicCompletion F) = (z' : u.adicCompletion F) from rfl, hcoe]
    exact ne_of_lt hv
  obtain ⟨s, hs⟩ := exists_sq_add_eq (maximalIdeal (u.adicCompletionIntegers F)) z' hzm
  have hsK : (s : u.adicCompletion F) ^ 2 + (s : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (z : F) := by
    rw [← hcoe, ← hs]
    norm_cast
  have hL : algebraMap F (u.adicCompletion F) ((1 + 4 * z : 𝓞 F) : F) =
      1 + 4 * algebraMap F (u.adicCompletion F) (z : F) := by
    have e1 : ((1 + 4 * z : 𝓞 F) : F) = 1 + 4 * (z : F) := by
      rw [show (4 : 𝓞 F) = 1 + 1 + 1 + 1 by norm_num]
      push_cast
      ring
    rw [e1]
    simp only [map_add (f := _), map_one, map_mul, map_ofNat]
  refine ⟨1 + 2 * (s : u.adicCompletion F), ?_⟩
  rw [hL]
  linear_combination (-4 : u.adicCompletion F) * hsK

end GlobalTheory.HenselSquare
