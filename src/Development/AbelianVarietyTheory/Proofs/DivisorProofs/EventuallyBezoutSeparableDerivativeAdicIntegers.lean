module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT.SepBezout

theorem valuation_le_one_eventually {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, w.valuation E x ≤ 1 := by
  apply _root_.GlobalTheory.CompanionTheory.SW.GoodInt.eventually_le_one <;> assumption

theorem bezout_eventually : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ u v : (w.adicCompletion E)[X],
      (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * P.map (algebraMap E (w.adicCompletion E)) + v * derivative (P.map (algebraMap E (w.adicCompletion E))) = 1 := by
  intro E _ _ P hP
  obtain ⟨u₀, v₀, h⟩ := hP
  have key : ∀ f : E[X], ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      ∀ i, (f.map (algebraMap E (w.adicCompletion E))).coeff i ∈ w.adicCompletionIntegers E := by
    intro f
    filter_upwards [(Filter.eventually_all_finset f.support).2
      (fun i _ => valuation_le_one_eventually (f.coeff i))] with w hw i
    rw [Polynomial.coeff_map]
    by_cases hi : i ∈ f.support
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have := hw i hi
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
      exact this
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
      exact zero_mem _
  filter_upwards [key u₀, key v₀] with w hu hv
  refine ⟨u₀.map (algebraMap E (w.adicCompletion E)), v₀.map (algebraMap E (w.adicCompletion E)), hu, hv, ?_⟩
  rw [Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add (f := _), h,
    Polynomial.map_one]

end GlobalTheory.BCT.SepBezout
