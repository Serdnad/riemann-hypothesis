module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle146
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

def PhiSubOneOntoFilZero {l : ℕ} [Fact l.Prime] (C : Core l) : Prop :=
  ∀ y : Per.Bcris l, ∃ x : Per.Bcris l, C.ι x ∈ Per.FilD l 0 ∧ Per.φB l x - x = y

def FontaineBcris : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (C : Core l),
    C.TensorInj ∧ C.PhiInj ∧ C.IotaInj ∧ C.Fund ∧ PhiSubOneOntoFilZero C ∧ C.FundOnto ∧ C.Regular

namespace FontaineBcris

variable {l : ℕ} [Fact l.Prime]

theorem tensorInj (h : FontaineBcris) (C : Core l) : C.TensorInj := (h l C).1

theorem iotaInj (h : FontaineBcris) (C : Core l) : C.IotaInj := (h l C).2.2.1

theorem ontoFilZero (h : FontaineBcris) (C : Core l) : PhiSubOneOntoFilZero C := (h l C).2.2.2.2.1

theorem fundOnto (h : FontaineBcris) (C : Core l) : C.FundOnto := (h l C).2.2.2.2.2.1

theorem regular (h : FontaineBcris) (C : Core l) : C.Regular := (h l C).2.2.2.2.2.2

theorem oneSubPhiOnto_of_filZero {C : Core l} (h : PhiSubOneOntoFilZero C) : C.OneSubPhiOnto := by
  intro y
  obtain ⟨x, -, hx⟩ := h (-y)
  exact ⟨x, by rw [← neg_sub, hx, neg_neg]⟩

theorem filZero_of_onto {C : Core l} (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : PhiSubOneOntoFilZero C := by
  intro y
  obtain ⟨x, hx⟩ := h1 y
  obtain ⟨b, hb, hF⟩ := h2 (C.ι x)
  refine ⟨b - x, by rwa [map_sub], ?_⟩
  rw [map_sub, hb, ← hx]
  ring

theorem of_rest (h : ∀ (l : ℕ) [Fact l.Prime] (C : Core l),
    C.TensorInj ∧ C.Fund ∧ C.FundOnto ∧ C.Regular) : FontaineBcris := fun l _ C =>
  ⟨(h l C).1, phiB_injective l, (ULaws.u_laws l C).2.2.2.1, (h l C).2.1,
    filZero_of_onto (one_sub_phi_onto l C) (h l C).2.2.1, (h l C).2.2.1, (h l C).2.2.2⟩

end FontaineBcris

end GlobalTheory.Published
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.LFun GlobalTheory.CuspRep GlobalTheory.HeckeGal.Model

namespace GlobalTheory.Published.JacquetShalikaModel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
omit [_root_.NumberField.IsTotallyComplex E] in
theorem _root_.GlobalTheory.Published.JacquetShalikaModel.infinite_places : Infinite (HeightOneSpectrum (𝓞 E)) := by
  classical
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hfin : (Set.range fun P : HeightOneSpectrum (𝓞 E) =>
      Ideal.comap (algebraMap ℤ (𝓞 E)) P.asIdeal).Finite := Set.finite_range _
  apply Nat.infinite_setOf_prime
  have hinj : Set.InjOn (fun p : ℕ => Ideal.span {(p : ℤ)}) {p | p.Prime} := by
    intro p _ q _ hpq
    have := Ideal.span_singleton_eq_span_singleton.mp hpq
    rw [Int.associated_iff_natAbs] at this
    simpa using this
  refine Set.Finite.of_finite_image (hfin.subset ?_) hinj
  rintro _ ⟨p, hp, rfl⟩
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQ, hlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hcomap : Ideal.comap (algebraMap ℤ (𝓞 E)) Q = Ideal.span {(p : ℤ)} :=
    (hlies.over).symm
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hmem : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) :=
      hcomap ▸ Ideal.subset_span rfl
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast, Nat.cast_eq_zero] at hmem
    exact hp.ne_zero hmem
  exact ⟨⟨Q, hQ.isPrime, hne⟩, hcomap⟩

end GlobalTheory.Published.JacquetShalikaModel
end
end
