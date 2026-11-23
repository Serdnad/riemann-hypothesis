module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.HeightOneIffDimOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

theorem length_quotient_kernel (a b : A) :
    length (A ⧸ Ideal.span {a}) (LinearMap.ker (LinearMap.lsmul (A ⧸ Ideal.span {a})
        (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) := by
  rw [length_quot_restrict a]
  have h : (LinearMap.ker (LinearMap.lsmul (A ⧸ Ideal.span {a})
        (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))).restrictScalars A =
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    ext x
    simp [Algebra.smul_def]
  rw [← h]
  rfl

theorem length_quotient_cokernel (a b : A) :
    length (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (A ⧸ Ideal.span {a, b}) := by
  rw [length_quot_restrict a]
  set N := LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)) with hN
  let f : A →ₗ[A] ((A ⧸ Ideal.span {a}) ⧸ N) :=
    (N.mkQ.restrictScalars A) ∘ₗ (Ideal.span {a} : Ideal A).mkQ
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective N).comp (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker f = Ideal.span {a, b} := by
    ext x
    have h1 : x ∈ LinearMap.ker f ↔ Ideal.Quotient.mk (Ideal.span {a}) x ∈ N := by
      rw [LinearMap.mem_ker]
      exact Submodule.Quotient.mk_eq_zero N
    rw [h1, Ideal.mem_span_pair, hN, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton'] at hy
      obtain ⟨c, hc⟩ := hy
      exact ⟨-c, y, by linear_combination -hc⟩
    · rintro ⟨c, y, h⟩
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton']
      exact ⟨-c, by linear_combination -h⟩
  exact ((f.quotKerEquivOfSurjective hf).symm.trans
    (Submodule.quotEquivOfEq _ _ hk)).length_eq

theorem dimension_eq_one_of_add_one (d : WithBot ℕ∞) (hd : d + 1 = 2) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd hd (by decide)
    | coe m =>
      have e : ((((m + 1 : ℕ) : ℕ∞)) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one]
        exact hd
      have h2 : ((m + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) := WithBot.coe_inj.mp e
      have h3 : m + 1 = 2 := Nat.cast_injective h2
      have h4 : m = 1 := by omega
      subst h4
      rfl

theorem length_quotient_sum_ord (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A) :
    (∑ᶠ (P : PrimeSpectrum (A ⧸ Ideal.span {a}))
        (_ : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1),
        length (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) *
            ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b)) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by
  have hmem : ∀ P : PrimeSpectrum (A ⧸ Ideal.span {a}),
      a ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal := by
    intro P
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)]
    exact zero_mem _
  refine finsum_mem_eq_of_bijOn
    (s := {P : PrimeSpectrum (A ⧸ Ideal.span {a}) |
      ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1})
    (t := {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal})
    (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) ⟨?_, ?_, ?_⟩ ?_
  · intro P hP
    refine ⟨(height_one_iff_dim_one h2 ha _ (hmem P)).2 ?_, hmem P⟩
    rw [← dim_quot_comap]
    exact hP
  · exact (PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).injOn
  · rintro p ⟨hp, hap⟩
    have : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
      exact (Ideal.span_singleton_le_iff_mem _).2 hap
    obtain ⟨P, rfl⟩ := this
    refine ⟨P, ?_, rfl⟩
    change ringKrullDim _ = 1
    rw [dim_quot_comap]
    exact (height_one_iff_dim_one h2 ha _ hap).1 hp
  · intro P _
    rw [length_loc_quot, ordMod_quot]

theorem length_quotient_pair_formula (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A)
    (hfin : length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    length A (A ⧸ Ideal.span {a, b}) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by
  by_cases hu : IsUnit a
  · have h1 : Subsingleton (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hu)
    have h3 : Subsingleton (A ⧸ Ideal.span {a, b}) :=
      Ideal.Quotient.subsingleton_iff.2
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu)
    have h4 : ∀ p : PrimeSpectrum A, a ∉ p.asIdeal := fun p hp =>
      p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    simp [h4]
  · have hm : a ∈ IsLocalRing.maximalIdeal A := hu
    have hnt : Nontrivial (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.nontrivial_iff.2 (fun h => hu (Ideal.span_singleton_eq_top.1 h))
    have hloc : IsLocalRing (A ⧸ Ideal.span {a}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hd := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha) hm
    have hd1 : ringKrullDim (A ⧸ Ideal.span {a}) = 1 := by
      rw [h2] at hd
      exact dimension_eq_one_of_add_one _ hd
    have key := (dimOneFormula (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a})
      (Ideal.Quotient.mk (Ideal.span {a}) b) hd1 (by rw [length_quotient_cokernel]; exact hfin)).2
    rw [length_quotient_cokernel, length_quotient_kernel, length_quotient_sum_ord h2 ha] at key
    exact key

end

theorem length_two_generator_quotient : LocalLengthMultiplicativity := by
  intro A _ _ _ _ a b h2 ha hb hfin
  have hfin' : length A (A ⧸ Ideal.span {b, a}) ≠ ⊤ := by rwa [Set.pair_comm]
  have h1 := length_quotient_pair_formula h2 ha b hfin
  have h1' := length_quotient_pair_formula h2 hb a hfin'
  have hs := length_ker_swap a b ha hb
  have ht := length_ker_ne_top a b ha hb hfin
  refine ⟨h1, ⟨hs, ht⟩, ?_⟩
  rw [Set.pair_comm, h1, ← hs] at h1'
  exact ENat.add_right_injective_of_ne_top ht h1'

end ReciprocityTheory.ChartRestriction.G.AI
end

section

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

section
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]

theorem krullDimLE_one_of_krullDim_eq (h : ringKrullDim A = 1) : Ring.KrullDimLE 1 A := by
  rw [Ring.krullDimLE_iff, h]
  simp

theorem krullDim_quotient_eq_one_iff_eq_bot [Ring.KrullDimLE 1 A] (h : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = 1 ↔ p.asIdeal = ⊥ := by
  constructor
  · intro hq
    by_contra hne
    have hmax : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot p.isPrime hne
    have h0 := ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
    rw [h0] at hq
    exact zero_ne_one hq
  · intro hp
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hp).trans (RingEquiv.quotientBot A)), h]

theorem length_coker_ne_top (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Ring.KrullDimLE 1 A] {x : A} (hx : x ≠ 0) :
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ := by
  have htors : Module.IsTorsionBy A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) x := by
    intro n
    refine Submodule.Quotient.induction_on _ n (fun m => ?_)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, rfl⟩
  have htors' : Module.IsTorsionBySet A (M ⧸ LinearMap.range (LinearMap.lsmul A M x))
      (Ideal.span {x} : Set A) :=
    (Module.isTorsionBySet_span_singleton_iff x).mpr htors
  letI : Module (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) := htors'.module
  haveI : IsScalarTower A (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    htors'.isScalarTower
  haveI : Ring.KrullDimLE 0 (A ⧸ Ideal.span {x}) := by
    rw [Ring.krullDimLE_zero_iff]
    intro P hP
    have hc : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P).IsPrime := Ideal.IsPrime.comap _
    have hne : Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P ≠ ⊥ := by
      intro h0
      have hxm : x ∈ Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)]
        exact P.zero_mem
      rw [h0, Ideal.mem_bot] at hxm
      exact hx hxm
    haveI hm := Ideal.IsPrime.isMaximal_of_ne_bot hc hne
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {x})) := Ideal.Quotient.mk_surjective
    have hmap := Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj
      (m := Ideal.comap (Ideal.Quotient.mk (Ideal.span {x})) P) (by
        intro a ha
        rw [RingHom.mem_ker] at ha
        rw [Ideal.mem_comap, ha]
        exact P.zero_mem)
    rwa [Ideal.map_comap_of_surjective _ hsurj] at hmap
  haveI : IsArtinianRing (A ⧸ Ideal.span {x}) := isArtinianRing_iff_krullDimLE_zero.mpr inferInstance
  haveI : Module.Finite (A ⧸ Ideal.span {x}) (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hs : Function.Surjective (algebraMap A (A ⧸ Ideal.span {x})) := Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hs, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, inferInstance⟩

theorem length_ker_eq_zero_of_torsionFree (M : Type*) [AddCommGroup M] [Module A M] [Module.IsTorsionFree A M]
    {x : A} (hx : x ≠ 0) :
    length A (LinearMap.ker (LinearMap.lsmul A M x)) = 0 := by
  rw [Module.length_eq_zero_iff]
  have hreg : IsSMulRegular M x := IsSMulRegular.of_ne_zero hx
  have hker : LinearMap.ker (LinearMap.lsmul A M x) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun a b hab => hreg (by simpa using hab))
  rw [hker]
  infer_instance

theorem length_localization_bot_eq_finrank (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    length (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) =
      (finrank A M : ℕ∞) := by
  have hfield : IsField (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := hfield.toField
  have hle : (⊥ : Ideal A).primeCompl ≤ nonZeroDivisors A := by
    intro a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => ha (by rw [h0]; exact Submodule.zero_mem _))
  haveI : Module.Finite (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) :=
    Module.Finite.of_isLocalizedModule (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M)
  rw [Module.length_of_free_of_finite, Module.length_eq_one, mul_one]
  rw [IsLocalization.finrank_eq (Localization.AtPrime (⊥ : Ideal A)) (⊥ : Ideal A).primeCompl hle,
    IsLocalizedModule.finrank_eq (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M) hle]

theorem ordQuotient_bot (x : A) :
    ordMod ⟨⊥, Ideal.isPrime_bot⟩ x = Ring.ord A x := by
  unfold ordMod Ring.ord
  dsimp only
  have hs : Function.Surjective (algebraMap A (A ⧸ (⊥ : Ideal A))) := Ideal.Quotient.mk_surjective
  rw [← Module.length_eq_of_surjective hs]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ A (⊥ : Ideal A)) (Ideal.span {x}) =
      Ideal.span {Ideal.Quotient.mk (⊥ : Ideal A) x} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  have e1 := (Ideal.quotientEquivAlgOfEq A h1).symm.trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ A ⊥ (Ideal.span {x})).trans
      (Ideal.quotientEquivAlgOfEq A (bot_sup_eq (Ideal.span {x}))))
  exact e1.toLinearEquiv.length_eq

end

theorem dimOneTorsionFreeFormula : LocalLengthAdditivityTorsionFree := by
  intro A _ _ _ _ M _ _ _ _ x h hx
  haveI : Ring.KrullDimLE 1 A := krullDimLE_one_of_krullDim_eq h
  obtain ⟨-, heq⟩ := dimOneFormula A M x h (length_coker_ne_top M hx)
  rw [heq, length_ker_eq_zero_of_torsionFree M hx, zero_add]
  have hset : {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1} = {⟨⊥, Ideal.isPrime_bot⟩} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [krullDim_quotient_eq_one_iff_eq_bot h p]
    constructor
    · intro hp
      ext1
      exact hp
    · intro hp
      rw [hp]
  change ∑ᶠ p ∈ {p : PrimeSpectrum A | ringKrullDim (A ⧸ p.asIdeal) = 1}, _ = _
  rw [hset, finsum_mem_singleton]
  dsimp only
  rw [length_localization_bot_eq_finrank, ordQuotient_bot]

end ReciprocityTheory.ChartRestriction.G.AI
end
