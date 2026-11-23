module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.chirpInf :
    ∀ (K ι : Type) [Field K] [NumberField K] [Fintype ι] (p : MvPolynomial ι (mixedEmbedding.mixedSpace K)) (l : mixedEmbedding.mixedSpace K →L[ℝ] ℝ),
    Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => ((Real.fourierChar (l (MvPolynomial.eval x p)) : Circle) : ℂ) := by
  intro K ι _ _ _ p l
  have hp : Function.HasTemperateGrowth
      fun x : ι → mixedEmbedding.mixedSpace K => MvPolynomial.eval x p := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      simpa using Function.HasTemperateGrowth.const (E := ι → mixedEmbedding.mixedSpace K) a
    | add p q hp hq =>
      simp only [map_add (f := _)]
      exact hp.fun_add hq
    | mul_X p i hp =>
      have hi : Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => x i :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => mixedEmbedding.mixedSpace K)
          i).hasTemperateGrowth
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.fun_mul hi
  exact GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (l.hasTemperateGrowth.comp hp)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma natCast_ne_zero_res {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : v.valuation F (m : F) = 1) :
    ((m : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ 0 := by
  have hval : Valued.v (((m : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    have hc : (((m : v.adicCompletionIntegers F)) : v.adicCompletion F)
        = algebraMap F (v.adicCompletion F) (m : F) := by
      rw [map_natCast]; exact map_natCast (v.adicCompletionIntegers F).subtype m
    rw [hc]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (m : F)).trans hm
  have hu : IsUnit (m : v.adicCompletionIntegers F) :=
    (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one.2 hval
  intro h0
  have h1 : IsLocalRing.residue (v.adicCompletionIntegers F) (m : v.adicCompletionIntegers F) = 0 := by
    simpa using h0
  rw [IsLocalRing.residue_eq_zero_iff] at h1
  exact (IsLocalRing.notMem_maximalIdeal.2 hu) h1

private lemma lt_card_of_inj {k : Type*} (n : ℕ) (f : Fin (n + 1) → k) (hf : Function.Injective f) :
    (n : ℕ∞) < ENat.card k := by
  rcases finite_or_infinite k with h | h
  · have := Nat.card_le_card_of_injective f hf
    rw [ENat.card_eq_coe_natCard]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact_mod_cast this
  · rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top n

theorem UpperTheory.ConvolutionTheory.R2.C.resBig :
    ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (n : ℕ∞) < ENat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  intro F _ _ n
  have hne : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  rw [Filter.eventually_cofinite]
  refine (GlobalTheory.QNorm.finite_valuation_ne_one F (Units.mk0 _ hne)).subset ?_
  intro v hv h1
  apply hv
  have h1' : v.valuation F ((n.factorial : ℕ) : F) = 1 := by simpa using h1
  have hfac := natCast_ne_zero_res v _ h1'
  refine lt_card_of_inj n (fun i => ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F))) ?_
  have key : ∀ i j : ℕ, i < j → j ≤ n →
      ((i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ≠ (j : ℕ) := by
    intro i j hij hj heq
    have hd : ((j - i : ℕ) : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = 0 := by
      rw [Nat.cast_sub hij.le, heq, sub_self]
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hij) ((Nat.sub_le j i).trans hj)
    apply hfac
    rw [hc, Nat.cast_mul, hd, zero_mul]
  intro a b hab
  rcases lt_trichotomy (a : ℕ) b with h | h | h
  · exact absurd hab (key _ _ h (Nat.lt_succ_iff.1 b.2))
  · exact Fin.ext h
  · exact absurd hab.symm (key _ _ h (Nat.lt_succ_iff.1 a.2))
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.genLoc :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (s : Finset (R × R)), (∀ p ∈ s, IsUnit p.1 ∨ IsUnit p.2) →
    (s.card : ℕ∞) < ENat.card (IsLocalRing.ResidueField R) → ∃ t : R, ∀ p ∈ s, IsUnit (p.1 + p.2 * t) := by
  intro R _ _ s hs hcard
  let f : R × R → IsLocalRing.ResidueField R := fun p =>
    -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2)
  have hex : ∃ u : IsLocalRing.ResidueField R, u ∉ s.image f := by
    by_contra hall
    have hall' : ∀ u : IsLocalRing.ResidueField R, u ∈ s.image f := by
      intro u
      by_contra hu
      exact hall ⟨u, hu⟩
    have hsub : (Set.univ : Set (IsLocalRing.ResidueField R)) ⊆ ((s.image f : Finset _) : Set _) :=
      fun u _ => by simpa using hall' u
    have h1 : ENat.card (IsLocalRing.ResidueField R) ≤ ((s.image f).card : ℕ∞) := by
      have h2 := Set.encard_le_encard hsub
      rwa [Set.encard_univ, Set.encard_coe_eq_coe_finsetCard] at h2
    have h3 : ((s.image f).card : ℕ∞) ≤ (s.card : ℕ∞) := by
      exact_mod_cast Finset.card_image_le
    exact absurd (lt_of_le_of_lt (h1.trans h3) hcard) (lt_irrefl _)
  obtain ⟨u, hu⟩ := hex
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective u
  refine ⟨t, fun p hp => ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add (f := _), map_mul]
  intro h0
  by_cases hb : IsLocalRing.residue R p.2 = 0
  · rw [hb, zero_mul, add_zero] at h0
    rcases hs p hp with h | h
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h h0
    · exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 h hb
  · apply hu
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    show -(IsLocalRing.residue R p.1) / (IsLocalRing.residue R p.2) = _
    rw [div_eq_iff hb]
    linear_combination -h0
end
