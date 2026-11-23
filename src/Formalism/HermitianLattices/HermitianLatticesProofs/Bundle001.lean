module

public import Formalism.HermitianLattices.Bundle001
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle056
public import Lemmata.GeneralBFactSecondRest.Imports
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

section

open NumberField Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajBasicAux

variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem majBasic_majAt (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    majAt b X v x y = star (vecAt b v x) ⬝ᵥ ((((X v)⁻¹)ᴴ * (X v)⁻¹) *ᵥ vecAt b v y) := by
  unfold majAt
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

end MajBasicAux

end Formalism.HermitianLatticesTheory
end
end

section

noncomputable section

open nonZeroDivisors

namespace Formalism.HermitianLatticesTheory

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_mem_inv {P : Ideal R} {a : K} :
    a ∈ invIdeal (K := K) P ↔ ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := by
  unfold invIdeal
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.mem_one]
  rfl

theorem neighbourConstruct_mem_span {P : Ideal R} {x z : V} :
    z ∈ Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ↔
      ∃ a ∈ invIdeal (K := K) P, z = a • x := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨b, hb, rfl⟩ := h2
      exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [add_smul]⟩
    | smul r y _ h1 =>
      obtain ⟨a, ha, rfl⟩ := h1
      refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
      rw [smul_assoc]
  · intro hz
    exact Submodule.subset_span hz

end Gen

section DedekindLFunctions

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_one_mem (P : Ideal R) (hP0 : P ≠ ⊥) :
    (1 : K) ∈ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P := by
  have e := FractionalIdeal.coe_ideal_mul_inv (K := K) P hP0
  have e2 : ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) = 1 := by
    rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  have h1 : (1 : K) ∈ ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [e2]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hne : (P : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP0
  refine (mul_le_mul' ?_ ?_ : _ ≤ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P) h1
  · rw [FractionalIdeal.coe_coeIdeal]; exact le_rfl
  · intro a ha
    rw [neighbourConstruct_mem_inv]
    intro p hp
    have := (FractionalIdeal.mem_inv_iff hne).mp ha (algebraMap R K p)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
    rw [mul_comm]
    exact (FractionalIdeal.mem_one_iff _).mp this

theorem neighbourConstruct_key (P : Ideal R) (hP0 : P ≠ ⊥) (L : Submodule R V) (x : V)
    (H : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L) : x ∈ P • L := by
  have h1 := neighbourConstruct_one_mem (K := K) P hP0
  have : ((1 : K) • x) ∈ P • L := by
    refine Submodule.mul_induction_on (C := fun k => k • x ∈ P • L) h1 ?_ ?_
    · intro m hm n hn
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm
      rw [Algebra.linearMap_apply, mul_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul hp (H n hn)
    · intro a b ha hb
      rw [add_smul]; exact Submodule.add_mem _ ha hb
  simpa using this

end DedekindLFunctions

section Avoid

variable {R : Type*} [CommRing R]

end Avoid

section Main

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

end Main

end Formalism.HermitianLatticesTheory
end
end

section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajLatticeAux

variable {K : Type*} [Field K] [NumberField K]

theorem majLattice_common (t : Finset K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ t, IsIntegral ℤ ((d : K) * a) := by
  first | exact UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common .. | (apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› t | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K

end MajLatticeAux

section MajLatticeMain

variable {K V ι : Type*} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem majLattice_exists_c (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ L := by
  first | exact Bl.general_b_fact_second_rest.goal1 .. | (apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL y | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V | exact @Bl.general_b_fact_second_rest.goal1 K

theorem majLattice_exists_d (b : Basis ι K V) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((d : K) * b.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd, ht⟩ := majLattice_common (s.biUnion fun g => Finset.univ.image fun i => b.repr g i)
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    exact ht _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro i
    simp only [map_add (f := _), Finsupp.add_apply, mul_add]
    exact (hx i).add (hy i)
  | smul r x _ hx =>
    intro i
    have : b.repr (r • x) i = algebraMap (𝓞 K) K r * b.repr x i := by
      rw [← algebraMap_smul K r x, map_smul]; rfl
    rw [this, mul_left_comm]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx i)

end MajLatticeMain

end Formalism.HermitianLatticesTheory
end
end
