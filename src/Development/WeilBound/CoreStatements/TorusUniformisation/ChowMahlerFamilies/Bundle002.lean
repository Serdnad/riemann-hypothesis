module

import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
public import Mathlib.FieldTheory.LinearDisjoint
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.Defs
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open TensorProduct

namespace PositivityTheory.Xgn.TensorDomain

open Polynomial
open scoped IntermediateField

theorem natDegree_minpoly_eq {k F A : Type} [Field k] [Field F] [Field A] [Algebra k F]
    [Algebra F A] [Algebra k A] [IsScalarTower k F A]
    (h : ∀ x : F, IsAlgebraic k x → x ∈ (algebraMap k F).range)
    {θ : A} (hθ : IsIntegral k θ) : (minpoly F θ).natDegree = (minpoly k θ).natDegree := by
  apply GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor.natDegree_minpoly_eq_of_closed <;> assumption

theorem linearDisjoint_algebraicClosure {K Ω L : Type} [Field K] [CharZero K] [Field Ω] [Field L]
    [Algebra K Ω] [Algebra Ω L] [Algebra K L] [IsScalarTower K Ω L]
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) :
    (algebraicClosure K L).LinearDisjoint Ω := by
  have : Algebra.IsIntegral K (algebraicClosure K L).toSubalgebra :=
    (algebraicClosure.isAlgebraic K L).isIntegral
  refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left _ _ fun B hB _ => ?_
  have halg : B.IsAlgebraic := fun x hx => (mem_algebraicClosure_iff (F := K)).1 (hB hx)
  let M : IntermediateField K L := halg.toIntermediateField
  haveI : FiniteDimensional K M := ‹Module.Finite K B›
  change M.LinearDisjoint Ω
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K M
  have hi : IsIntegral K (θ : L) := (Algebra.IsIntegral.isIntegral (R := K) θ).map M.val
  have e : K⟮(θ : L)⟯ = M := by
    have := congrArg (IntermediateField.lift (F := M)) hθ
    simpa using this
  rw [← e]
  refine IntermediateField.LinearDisjoint.of_basis_left
    (IntermediateField.adjoin.powerBasis hi).basis ?_
  have hd := natDegree_minpoly_eq (F := Ω) h hi
  have hl := linearIndependent_pow (K := Ω) (θ : L)
  rw [hd] at hl
  have he : (K⟮(θ : L)⟯.val ∘ (IntermediateField.adjoin.powerBasis hi).basis) =
      fun i : Fin (IntermediateField.adjoin.powerBasis hi).dim => (θ : L) ^ (i : ℕ) := by
    funext i
    simp
  rw [he]
  exact hl

theorem exists_point (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] {a : A} (ha : a ≠ 0) : ∃ φ : A →ₐ[k] k, φ a ≠ 0 := by
  let S := Localization.Away a
  haveI : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  haveI : Algebra.FiniteType A S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) S
  haveI : Algebra.FiniteType k S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  let ψ : (S ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(ψ.comp (Ideal.Quotient.mkₐ k m)).comp (IsScalarTower.toAlgHom k A S), ?_⟩
  have hu : IsUnit (algebraMap A S a) := IsLocalization.Away.algebraMap_isUnit a
  exact (hu.map (ψ.comp (Ideal.Quotient.mkₐ k m))).ne_zero

theorem isDomain_tensor_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (F : Type) [Field F] [Algebra k F] :
    IsDomain (F ⊗[k] A) := by
  let b := Module.Basis.ofVectorSpace k F
  let B := Algebra.TensorProduct.basis A b
  haveI : Nontrivial (A ⊗[k] F) :=
    (Algebra.TensorProduct.includeRight_injective (R := k) (A := A) (B := F)
      (algebraMap k A).injective).nontrivial
  haveI : NoZeroDivisors (A ⊗[k] F) := ⟨fun {x y} hxy => by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hx, hy⟩ := hc
    obtain ⟨i, hi⟩ : ∃ i, B.repr x i ≠ 0 := by
      by_contra hn
      exact hx (B.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => not_not.1 fun h => hn ⟨i, h⟩))
    obtain ⟨j, hj⟩ : ∃ i, B.repr y i ≠ 0 := by
      by_contra hn
      exact hy (B.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => not_not.1 fun h => hn ⟨i, h⟩))
    obtain ⟨φ, hφ⟩ := exists_point k A (mul_ne_zero hi hj)
    let Φ : A ⊗[k] F →ₐ[k] F :=
      Algebra.TensorProduct.lift ((Algebra.ofId k F).comp φ) (AlgHom.id k F)
        fun _ _ => Commute.all _ _
    have key : ∀ z i, φ (B.repr z i) = b.repr (Φ z) i := by
      intro z i
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
      | tmul a f =>
        have h1 : Φ (a ⊗ₜ f) = φ a • f := by simp [Φ, Algebra.smul_def]
        rw [h1, map_smul]
        simp [B, Algebra.TensorProduct.basis_repr_tmul]
    have h0 : Φ x * Φ y = 0 := by rw [← map_mul, hxy, map_zero]
    apply hφ
    rw [map_mul, key, key]
    rcases mul_eq_zero.1 h0 with h | h <;> simp [h]⟩
  haveI : IsDomain (A ⊗[k] F) := NoZeroDivisors.to_isDomain _
  exact (Algebra.TensorProduct.comm k F A).toMulEquiv.isDomain

theorem isDomain_tensor_of_closure (k Ω S : Type) [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    [IsDomain (Ω ⊗[k] S)] (F : Type) [Field F] [Algebra k F] : IsDomain (F ⊗[k] S) := by
  let L := AlgebraicClosure F
  let j : Ω →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω L := j.toRingHom.toAlgebra
  haveI : IsScalarTower k Ω L := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI := isDomain_tensor_of_isAlgClosed Ω (Ω ⊗[k] S) L
  haveI : IsDomain (L ⊗[k] S) :=
    (Algebra.TensorProduct.cancelBaseChange k Ω L L S).symm.toMulEquiv.isDomain _
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k F L) (AlgHom.id k S)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S)
      (IsScalarTower.toAlgHom k F L).toLinearMap (algebraMap F L).injective
  exact Function.Injective.isDomain φ.toRingHom hφ

theorem isDomain_tensor {K A Ω : Type} [Field K] [CharZero K] [CommRing A] [Field Ω] [Algebra K A]
    [Algebra K Ω] [Algebra.FiniteType K A] (j : A →ₐ[K] Ω) (hj : Function.Injective j)
    (h : ∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) (F : Type) [Field F]
    [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let N := algebraicClosure K (AlgebraicClosure Ω)
  haveI : IsDomain (N ⊗[K] Ω) := (linearDisjoint_algebraicClosure h).isDomain
  haveI : IsAlgClosed N := IsAlgClosure.isAlgClosed K
  let φ := Algebra.TensorProduct.map (AlgHom.id K N) j
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) j.toLinearMap hj
  haveI : IsDomain (N ⊗[K] A) := Function.Injective.isDomain φ.toRingHom hφ
  exact isDomain_tensor_of_closure K N A F

theorem isDomain_of_algClosed {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L]
    [Algebra K F] [CharZero K] (h : ∀ a : F, IsAlgebraic K a → a ∈ (algebraMap K F).range) :
    IsDomain (L ⊗[K] F) := by
  classical
  haveI : Nontrivial (L ⊗[K] F) :=
    (Algebra.TensorProduct.includeRight_injective (R := K) (A := L) (B := F)
      (algebraMap K L).injective).nontrivial
  haveI : NoZeroDivisors (L ⊗[K] F) := ⟨fun {u v} huv => by
    obtain ⟨Su, rfl⟩ := TensorProduct.exists_finset u
    obtain ⟨Sv, rfl⟩ := TensorProduct.exists_finset v
    let T : Finset F := (Su ∪ Sv).image Prod.snd
    let A := Algebra.adjoin K (T : Set F)
    haveI : Algebra.FiniteType K A :=
      (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset T)
    haveI := isDomain_tensor A.val Subtype.val_injective h L
    let φ := Algebra.TensorProduct.map (AlgHom.id K L) A.val
    have hφ : Function.Injective φ :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := L) A.val.toLinearMap
        Subtype.val_injective
    have hr : ∀ S : Finset (L × F), S ⊆ Su ∪ Sv → (∑ q ∈ S, q.1 ⊗ₜ[K] q.2) ∈ φ.range :=
      fun S hS => sum_mem fun q hq => ⟨q.1 ⊗ₜ ⟨q.2, Algebra.subset_adjoin
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hS hq)))⟩, rfl⟩
    obtain ⟨a, ha⟩ := hr Su Finset.subset_union_left
    obtain ⟨b, hb⟩ := hr Sv Finset.subset_union_right
    have ha' : φ a = _ := ha
    have hb' : φ b = _ := hb
    rw [← ha', ← hb', ← map_mul, map_eq_zero_iff _ hφ] at huv
    rw [← ha', ← hb']
    rcases mul_eq_zero.1 huv with h0 | h0
    · left; rw [h0, map_zero]
    · right; rw [h0, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end PositivityTheory.Xgn.TensorDomain

theorem PositivityTheory.Xgn.tensor_algebraically_closed_domain : ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C], (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) := by
  intro K Ω C _ _ _ _ _ _ h
  haveI : IsDomain (C ⊗[K] Ω) := PositivityTheory.Xgn.TensorDomain.isDomain_of_algClosed h
  exact (Algebra.TensorProduct.comm K Ω C).toMulEquiv.isDomain
end

section

open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.LatticeSectionAlgebra

theorem denom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type)
    (reg : Q → Subring Ω)
    (h3 : ∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q))
    (h4 : ∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R)
    (g : Ω) (hg : g ∈ R) (a : Ω) (ha : ∀ q, g ≠ 0 → g⁻¹ ∈ reg q → a ∈ reg q) :
    ∃ n : ℕ, g ^ n * a ∈ R := by
  let I : Ideal R :=
    { carrier := {s | (s : Ω) * a ∈ R}
      add_mem' := by
        intro x y hx hy
        have := R.add_mem hx hy
        simpa [add_mul] using this
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        have := R.mul_mem c.2 hx
        simpa [mul_assoc] using this }
  have hI : ∀ s : R, s ∈ I ↔ (s : Ω) * a ∈ R := fun s => Iff.rfl
  have hrad : (⟨g, hg⟩ : R) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hIP, hP⟩
    by_contra hgP
    obtain ⟨q, hq⟩ := h3 P hP
    obtain ⟨h0, hu⟩ := (hq _).1 hgP
    obtain ⟨s, hsR, hs0, hsu, hsa⟩ := h4 q a (ha q h0 hu)
    exact (hq ⟨s, hsR⟩).2 ⟨hs0, hsu⟩ (hIP ((hI ⟨s, hsR⟩).2 hsa))
  obtain ⟨n, hn⟩ := hrad
  refine ⟨n, ?_⟩
  have := (hI _).1 hn
  simpa using this

theorem unif {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {ι : Type} [Fintype ι] (g a : ι → Ω) (hg : ∀ i, g i ∈ R)
    (h : ∀ i, ∃ n : ℕ, g i ^ n * a i ∈ R) : ∃ n : ℕ, ∀ i, g i ^ n * a i ∈ R := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ i))
  rw [hd, add_comm, pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem (hg i) d) (hn i)

theorem some_unit {Ω : Type} [Field Ω] (A : Subring Ω) [IsLocalRing A] {k : ℕ} (c g : Fin k → Ω)
    (hc : ∀ l, c l ∈ A) (hg : ∀ l, g l ∈ A) (h : ∑ l, c l * g l = 1) :
    ∃ l, (g l)⁻¹ ∈ A ∧ g l ≠ 0 := by
  by_contra hne
  have hm : ∀ l, (⟨g l, hg l⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    intro l
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : g l * (b : Ω) = 1 := by simpa using congrArg Subtype.val hb
    refine hne ⟨l, ?_, left_ne_zero_of_mul_eq_one hb'⟩
    rw [inv_eq_of_mul_eq_one_right hb']
    exact b.2
  have h1 : (∑ l, (⟨c l, hc l⟩ : A) * ⟨g l, hg l⟩) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hm l)
  have h2 : (∑ l, (⟨c l, hc l⟩ : A) * ⟨g l, hg l⟩) = 1 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa using h
  rw [h2] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem span_top {Ω : Type} [Field Ω] {r : ℕ} (f : Fin r → (Fin r → Ω))
    (hf : LinearIndependent Ω f) : Submodule.span Ω (Set.range f) = ⊤ :=
  hf.span_eq_top_of_card_eq_finrank' (by simp)

theorem coords {Ω : Type} [Field Ω] {r : ℕ} (f : Fin r → (Fin r → Ω))
    (hf : LinearIndependent Ω f) (e : Fin r → Ω) : ∃ a : Fin r → Ω, e = ∑ i, a i • f i := by
  have : e ∈ Submodule.span Ω (Set.range f) := by rw [span_top f hf]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  exact ⟨a, ha.symm⟩

end PositivityTheory.Xgn.LatticeSectionAlgebra

open PositivityTheory.Xgn.LatticeSectionAlgebra in
theorem PositivityTheory.Xgn.lattice_section_algebra : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
  intro o Ω _ _ _ R Q reg r Λ h1 h2 h3 h4 h5
  choose G hGR hG0 hGu F hF hfr using h5
  have hstab : ∀ q, ∀ a ∈ reg q, ∀ e ∈ Λ q, a • e ∈ Λ q := by
    intro q a ha e he
    obtain ⟨b, hb, rfl⟩ := (hfr q q (hGu q) e).1 he
    refine (hfr q q (hGu q) _).2 ⟨fun i => a * b i, fun i => mul_mem ha (hb i), ?_⟩
    simp only [Finset.smul_sum, smul_smul]
  have hcoord : ∀ q q', (G q)⁻¹ ∈ reg q' → ∀ a : Fin r → Ω, (∑ i, a i • F q i) ∈ Λ q' →
      ∀ i, a i ∈ reg q' := by
    intro q q' hq a ha i
    obtain ⟨b, hb, hab⟩ := (hfr q q' hq _).1 ha
    rw [Fintype.linearIndependent_iffₛ.1 (hF q) a b hab i]
    exact hb i
  have htop : Ideal.span (Set.range fun q => (⟨G q, hGR q⟩ : R)) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q, hq⟩ := h3 P hP.isPrime
    exact (hq ⟨G q, hGR q⟩).2 ⟨hG0 q, hGu q⟩ (hle (Ideal.subset_span ⟨q, rfl⟩))
  obtain ⟨k, c, t, hsum⟩ := Submodule.mem_span_set'.1 ((Ideal.eq_top_iff_one _).1 htop)
  choose p hp using fun l => (t l).2
  have hsum' : ∑ l, (c l : Ω) * G (p l) = 1 := by
    have := congrArg Subtype.val hsum
    rw [AddSubmonoidClass.coe_finsetSum] at this
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) this
    rw [← hp l]
    simp
  have hcov : ∀ q, ∃ l, (G (p l))⁻¹ ∈ reg q := by
    intro q
    haveI := h1 q
    obtain ⟨l, hl, -⟩ := some_unit (reg q) (fun l => (c l : Ω)) (fun l => G (p l))
      (fun l => h2 q _ (c l).2) (fun l => h2 q _ (hGR _)) hsum'
    exact ⟨l, hl⟩
  have hsec : ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) →
      ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
    intro g hg e he
    choose a ha using fun l => coords (F (p l)) (hF _) e
    obtain ⟨n, hn⟩ := unif R (ι := Fin k × Fin r) (fun x => g * G (p x.1)) (fun x => a x.1 x.2)
      (fun x => R.mul_mem hg (hGR _)) (by
        rintro ⟨l, i⟩
        refine denom R Q reg h3 h4 _ (R.mul_mem hg (hGR _)) _ ?_
        intro q h0 hu
        have hg0 : g ≠ 0 := left_ne_zero_of_mul h0
        have hl0 := hG0 (p l)
        have e1 : g⁻¹ = G (p l) * (g * G (p l))⁻¹ := by field_simp
        have e2 : (G (p l))⁻¹ = g * (g * G (p l))⁻¹ := by field_simp
        have u1 : g⁻¹ ∈ reg q := by rw [e1]; exact mul_mem (h2 q _ (hGR _)) hu
        have u2 : (G (p l))⁻¹ ∈ reg q := by rw [e2]; exact mul_mem (h2 q _ hg) hu
        exact hcoord (p l) q u2 (a l) (ha l ▸ he q hg0 u1) i)
    refine ⟨n, AddSubgroup.mem_iInf.2 fun q => ?_⟩
    obtain ⟨l, hl⟩ := hcov q
    refine (hfr (p l) q hl _).2 ⟨fun i => g ^ n * a l i, fun i => ?_, ?_⟩
    · have hl0 := hG0 (p l)
      have e1 : g ^ n * a l i = (G (p l))⁻¹ ^ n * ((g * G (p l)) ^ n * a l i) := by
        rw [mul_pow, inv_pow]; field_simp
      show g ^ n * a l i ∈ reg q
      rw [e1]
      exact mul_mem (pow_mem hl n) (h2 q _ (hn (l, i)))
    · conv_lhs => rw [ha l]
      simp only [Finset.smul_sum, smul_smul]
  refine ⟨⟨?_, k, fun l => G (p l), fun l => c l, fun l => hGR _, fun l => (c l).2, hsum', ?_⟩, hsec⟩
  · intro a ha e he
    exact AddSubgroup.mem_iInf.2 fun q => hstab q a (h2 q a ha) e (AddSubgroup.mem_iInf.1 he q)
  · intro l
    have hl0 := hG0 (p l)
    refine ⟨F (p l), hF _, span_top _ (hF _), fun e => ⟨?_, ?_⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨a, rfl⟩ := coords (F (p l)) (hF _) e
      refine ⟨a, fun i => denom R Q reg h3 h4 _ (hGR _) _ ?_, rfl⟩
      intro q _ hu
      refine hcoord (p l) q hu a ?_ i
      have := hstab q _ (pow_mem hu n) _ (AddSubgroup.mem_iInf.1 hn q)
      rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_smul] at this
    · rintro ⟨a, ha, rfl⟩
      refine hsec _ (hGR _) _ fun q _ hu => (hfr (p l) q hu _).2 ⟨a, fun i => ?_, rfl⟩
      obtain ⟨n, hn⟩ := ha i
      have e1 : a i = (G (p l))⁻¹ ^ n * (G (p l) ^ n * a i) := by
        rw [inv_pow]; field_simp
      rw [e1]
      exact mul_mem (pow_mem hu n) (h2 q _ hn)
end

section

open MvPolynomial

namespace PositivityTheory.Xgn.HomogeneousComponentProduct

theorem comp_mul {σ M R : Type*} [CommRing R] [AddCancelCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (b : M)
    (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w (b + bg) (s * g) = weightedHomogeneousComponent w b s * g := by
  conv_lhs => rw [s.as_sum, Finset.sum_mul]
  conv_rhs => rw [s.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hm : IsWeightedHomogeneous w (monomial d (AddMonoidAlgebra.coeff s d)) (Finsupp.weight w d) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  by_cases h : Finsupp.weight w d = b
  · subst h
    rw [(hm.mul hg).weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
  · rw [(hm.mul hg).weightedHomogeneousComponent_ne _ (fun h' => h (add_right_cancel h').symm),
      hm.weightedHomogeneousComponent_ne _ (Ne.symm h), zero_mul]

theorem comp_mul_zero {σ M R : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (c : M)
    (hc : ∀ b, c ≠ b + bg) (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w c (s * g) = 0 := by

  rw [s.as_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  exact ((isWeightedHomogeneous_monomial _ _ _ rfl).mul hg).weightedHomogeneousComponent_ne _ (hc _)

end PositivityTheory.Xgn.HomogeneousComponentProduct

theorem PositivityTheory.Xgn.homogeneous_pair_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P := by
  intro K _ _ ι _ P hP hH f g u₀ v₀ bf bg a hf hg hfP hrel hu
  have h := hH _ hrel (a + bf)
  rw [map_sub, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ f bf hf] at h
  by_cases hb : ∃ b, a + bf = b + bg
  · obtain ⟨b, hb⟩ := hb
    rw [hb, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ g bg hg] at h
    exact ⟨b, _, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hb, h⟩
  · rw [PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul_zero _ g bg hg _
      (fun b hb' => hb ⟨b, hb'⟩), sub_zero] at h
    rcases hP.mem_or_mem h with h | h
    · exact absurd h hu
    · exact absurd h hfP
end

section

open MvPolynomial

theorem PositivityTheory.Xgn.multihomogeneous_eval_scale : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (s : MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ) (c : K → ℂ) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog s a → eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) s) = (∏ k, c k ^ a k) * eval z (MvPolynomial.map (Int.castRingHom ℂ) s) := by
  intro K _ _ ι _ s a c z hs
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m = a :=
    hs (mem_support_iff.mp hm)
  have ha : ∀ k, a k = ∑ i : ι k, m ⟨k, i⟩ := by
    intro k
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
    · intro j _ hj
      simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_apply, hj, hj.symm]
    · simp
  have h1 : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, ← Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, h1]
  ring
end
