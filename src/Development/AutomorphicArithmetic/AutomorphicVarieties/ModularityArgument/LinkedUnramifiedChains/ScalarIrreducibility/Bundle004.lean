module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RingHom.Flat
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.BigOperators
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.redCrit :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (q : Ideal A), q.IsPrime → (∀ P ∈ associatedPrimes A A, P ≤ q → P ∈ minimalPrimes A) →
        (∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0) → ∀ a : A, (∀ P : Ideal A, P.IsPrime → P ≤ q → a ∈ P) → ∃ s ∉ q, s * a = 0 := by
  intro A _ _ q hq h1 h2 a ha
  by_contra hcon
  push_neg at hcon
  let N : Submodule A A := Submodule.span A {a}
  have hann : ∀ x, x ∈ Module.annihilator A N ↔ x * a = 0 := by
    intro x
    rw [Module.mem_annihilator]
    constructor
    · intro h
      exact congrArg Subtype.val (h ⟨a, Submodule.mem_span_singleton_self a⟩)
    · intro h m
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp m.2
      apply Subtype.ext
      change x * (m : A) = 0
      rw [← hc, smul_eq_mul, mul_left_comm, h, mul_zero]
  have hle : Module.annihilator A N ≤ q := by
    intro x hx
    by_contra hxq
    exact hcon x hxq ((hann x).mp hx)
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le hle
  have hPass : P ∈ associatedPrimes A N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A N hP
  have hPA : P ∈ associatedPrimes A A :=
    associatedPrimes.subset_of_injective N.injective_subtype hPass
  have hPmin := h1 P hPA hPq
  obtain ⟨s, hsP, hs⟩ := h2 P hPmin hPq a (ha P hPmin.1.1 hPq)
  exact hsP (hP.1.2 ((hann s).mpr hs))
end

section

private theorem flatAss_ann {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) (r : R) (h : a • r = 0) :
    r ∈ P.map (algebraMap A R) := by
  have h1 : ∑ _i : Fin 1, a • r = 0 := by
    rw [Fin.sum_univ_one]
    exact h
  obtain ⟨l, c, y, hy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Fin 1 => a)
      (x := fun _ : Fin 1 => r) h1
  have hr : r = ∑ j, c 0 j • y j := hy 0
  rw [hr]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem _).2 ?_))
  have h2 := hc j
  rw [Fin.sum_univ_one] at h2
  rw [mul_comm]
  exact h2

private theorem flatAss_annih {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) :
    Module.annihilator R (Ideal.span {algebraMap A R a} : Ideal R) = P.map (algebraMap A R) := by
  apply le_antisymm
  · intro r hr
    have h0 : r * algebraMap A R a = 0 :=
      congrArg Subtype.val (Module.mem_annihilator.1 hr
        ⟨algebraMap A R a, Ideal.mem_span_singleton_self _⟩)
    refine flatAss_ann P a hmem r ?_
    rw [Algebra.smul_def, mul_comm]
    exact h0
  · refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
    rw [Ideal.mem_comap, Module.mem_annihilator]
    rintro ⟨n, hn⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hn
    apply Subtype.ext
    change algebraMap A R b * (c * algebraMap A R a) = 0
    rw [mul_left_comm, ← map_mul, (hmem b).1 hb, map_zero, mul_zero]

private theorem flatAss_alg {A R : Type} [CommRing A] [CommRing R] [IsNoetherianRing A]
    [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (Q : Ideal R) (hQ : Q.IsPrime)
    (hmin : ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R)
    (P : Ideal A) (hP : P ∈ associatedPrimes A A) (hPQ : P ≤ Q.comap (algebraMap A R)) :
    P ∈ minimalPrimes A := by
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  obtain ⟨hPp, a, hPa⟩ := isAssociatedPrime_iff.1 hP
  have hmem : ∀ b, b ∈ P ↔ b * a = 0 := fun b => by
    rw [hPa, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  have hmapQ : P.map (algebraMap A R) ≤ Q := Ideal.map_le_iff_le_comap.2 hPQ
  haveI := hQ
  obtain ⟨Q', hQ'min, hQ'Q⟩ := Ideal.exists_minimalPrimes_le hmapQ
  have hQ'ass : Q' ∈ associatedPrimes R R := by
    have h1 := hQ'min
    rw [← flatAss_annih P a hmem] at h1
    exact associatedPrimes.subset_of_injective (Submodule.injective_subtype _)
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ h1)
  have hQ'm := hmin Q' hQ'ass hQ'Q
  haveI hQ'p : Q'.IsPrime := hQ'min.1.1
  refine ⟨⟨hPp, bot_le⟩, fun p hp hpP => ?_⟩
  haveI := hp.1
  have hPc : P ≤ Q'.comap (algebraMap A R) := Ideal.map_le_iff_le_comap.1 hQ'min.1.2
  haveI : Q'.LiesOver (Q'.comap (algebraMap A R)) := ⟨rfl⟩
  obtain ⟨Q'', hle, hQ''p, hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le Q' (hpP.trans hPc)
  have hge := hQ'm.2 ⟨hQ''p, bot_le⟩ hle
  have heq : Q'' = Q' := le_antisymm hle hge
  rw [hlies.over, heq]
  exact hPc

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatAss :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ Q : Ideal R, Q.IsPrime →
        (∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R) → ∀ P ∈ associatedPrimes A A, P ≤ Q.comap ι → P ∈ minimalPrimes A :=
  fun A R _ _ _ _ ι hι Q hQ hmin P hP hPQ =>
    @flatAss_alg A R _ _ _ _ ι.toAlgebra hι Q hQ hmin P hP hPQ
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatHt :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ (q : Ideal A) (Q : Ideal R),
        Q.IsPrime → Q.comap ι = q → Q ∈ (q.map ι).minimalPrimes → Q.height = q.height := by
  intro A R _ _ _ _ ι hι q Q hQ hcomap hmin
  letI : Algebra A R := ι.toAlgebra
  haveI : Module.Flat A R := hι
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : q.IsPrime := hcomap ▸ Ideal.comap_isPrime ι Q
  haveI : Q.LiesOver q := ⟨hcomap.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q]
  suffices h0 : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).height = 0 by
    rw [h0, add_zero]
  have hJQ : q.map (algebraMap A R) ≤ Q := hmin.1.2
  have hker : RingHom.ker (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    rw [Ideal.mk_ker]
    exact hJQ
  haveI : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro K ⟨hK, -⟩ hKQ
  have hle : K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hKQ hx)
    have hd : y - x ∈ q.map (algebraMap A R) := Ideal.Quotient.eq.mp hxy
    have hx' : x = y - (y - x) := by ring
    rw [hx']
    exact Q.sub_mem hy (hJQ hd)
  have hc : Q ≤ K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) := by
    refine hmin.2 ⟨Ideal.comap_isPrime _ K, ?_⟩ hle
    intro x hx
    have hx2 : x ∈ q.map (algebraMap A R) := hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx2]
    exact K.zero_mem
  exact Ideal.map_le_iff_le_comap.mpr hc
end
