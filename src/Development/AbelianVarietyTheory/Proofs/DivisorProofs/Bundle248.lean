module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle008
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.Extension
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem relLen_chain_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ),
    RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  intro C _ v M _ _ X'' X' X r₁ r₂ h₂ h₁
  obtain ⟨n, b, b', A, hA, hrA⟩ := h₁
  obtain ⟨m, c, c', B, hB, hrB⟩ := h₂
  have hnm : n = m := by simpa using Fintype.card_congr (b'.indexEquiv c)
  subst m
  have le_of_basis : ∀ {Y Z : Submodule (Int0 v) M}
      (d : Basis (Fin n) (Int0 v) Y) (e : Basis (Fin n) (Int0 v) Z)
      (D : Matrix (Fin n) (Fin n) (Int0 v)),
      (∀ k, (e k : M) = ∑ i, D i k • (d i : M)) → Z ≤ Y := by
    intro Y Z d e D h x hx
    have hx' : (x : M) = ∑ k, e.repr ⟨x, hx⟩ k • (e k : M) := by
      have hh := congrArg Z.subtype (e.sum_repr ⟨x, hx⟩)
      rw [map_sum] at hh
      exact hh.symm
    rw [hx']
    exact Y.sum_mem fun k _ => Y.smul_mem _ (by
      rw [h k]
      exact Y.sum_mem fun i _ => Y.smul_mem _ (d i).2)
  have hle₁ : X' ≤ X := le_of_basis b b' A hA
  have hle₂ : X'' ≤ X' := le_of_basis c c' B hB
  have key : ∀ {Y Z : Submodule (Int0 v) M} (h : Z ≤ Y)
      (d : Basis (Fin n) (Int0 v) Y) (e : Basis (Fin n) (Int0 v) Z)
      (D : Matrix (Fin n) (Fin n) (Int0 v)),
      (∀ k, (e k : M) = ∑ i, D i k • (d i : M)) →
      LinearMap.toMatrix e d (Submodule.inclusion h) = D := by
    intro Y Z h d e D hD
    ext i k
    have hh : Submodule.inclusion h (e k) = ∑ i, D i k • d i := by
      apply Subtype.ext
      simpa using hD k
    rw [LinearMap.toMatrix_apply, hh]
    simp [Finsupp.single_apply]
  have hmat₁ := key hle₁ b b' A hA
  have hmat₂ := key hle₂ c c' B hB
  let D := LinearMap.toMatrix c' b (Submodule.inclusion (hle₂.trans hle₁))
  have hD : D = A * (b'.toMatrix c) * B := by
    have hc : Submodule.inclusion (hle₂.trans hle₁) =
        (Submodule.inclusion hle₁).comp (Submodule.inclusion hle₂) := by
      ext x; rfl
    dsimp [D]
    rw [hc, LinearMap.toMatrix_comp c' b' b, hmat₁]
    rw [← basis_toMatrix_mul_linearMap_toMatrix c' b' c (Submodule.inclusion hle₂), hmat₂, Matrix.mul_assoc]
  refine ⟨n, b, c', D, ?_, ?_⟩
  · intro k
    have hh := b.sum_repr (Submodule.inclusion (hle₂.trans hle₁) (c' k))
    have hh' := congrArg X.subtype hh
    rw [map_sum] at hh'
    simpa [D, LinearMap.toMatrix_apply] using hh'.symm
  · have hu : IsUnit (b'.toMatrix c).det := by
      letI := b'.invertibleToMatrix c
      exact Matrix.isUnit_det_of_invertible _
    rw [hD, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul,
      v.map_mul, v.map_mul, v_unit v hu, add_zero, hrA, hrB]
    simp

end GlobalTheory
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem finrank_addValuationInteger_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X →
    finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) =>
      (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  intro C _ v N X hX
  let ι : (Fin N → Int0 v) →ₗ[Int0 v] (Fin N → C) := (Algebra.linearMap (Int0 v) C).compLeft (Fin N)
  have hι : Function.Injective ι := by
    intro x y h; funext i; exact Subtype.ext (congrFun h i)
  let L : X →ₗ[Int0 v] (Fin N → C) := ι ∘ₗ X.subtype
  have hL : Function.Injective L := hι.comp Subtype.val_injective
  have hInt : v.toValuation.Integers (Int0 v) := by
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro x
      change 0 ≤ v (x : C)
      exact (mem_addValuationIntegerRing_iff v _).mp x.property
    · intro x hx
      change 0 ≤ v x at hx
      exact ⟨⟨x, (mem_addValuationIntegerRing_iff v x).mpr hx⟩, rfl⟩
  have : ValuationRing (Int0 v) := ValuationRing.of_integers _ hInt
  have : IsFractionRing (Int0 v) C := hInt.isFractionRing
  have : Module.IsTorsionFree (Int0 v) X := inferInstance
  have : Module.Free (Int0 v) X := free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) X
  let b := Module.Free.chooseBasis (Int0 v) X
  have hli : LinearIndependent (Int0 v) (L ∘ b) :=
    b.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)
  have hliC : LinearIndependent C (L ∘ b) := (LinearIndependent.iff_fractionRing (Int0 v) C).mp hli
  have hspan : Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
      (X : Set (Fin N → Int0 v))) = Submodule.span C (Set.range (L ∘ b)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : L ⟨x, hx⟩ ∈ Submodule.span (Int0 v) (L '' Set.range b) :=
        Submodule.apply_mem_span_image_of_mem_span L (by rw [b.span_eq]; trivial)
      rw [← Set.range_comp] at h1
      exact Submodule.span_le_restrictScalars (Int0 v) C _ h1
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(b k : Fin N → Int0 v), (b k).2, rfl⟩
  rw [hspan, finrank_span_eq_card hliC, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.SubLen

theorem exists_relLen_of_smul_le (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M]
    (htf : ∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0)
    (X' X : Submodule (Int0 v) M) (hle : X' ≤ X) (hX : Module.Finite (Int0 v) X)
    (hX' : Module.Finite (Int0 v) X') (c : Int0 v) (hc : c ≠ 0) (hcX : ∀ x ∈ X, c • x ∈ X') :
    ∃ r : ℝ, RelLen v X' X r := by
  haveI tfX : Module.IsTorsionFree (Int0 v) X :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI tfX' : Module.IsTorsionFree (Int0 v) X' :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI := hX
  haveI := hX'
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X')
  let ι : X' →ₗ[Int0 v] X := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  let μ : X →ₗ[Int0 v] X' :=
    { toFun := fun x => ⟨c • (x : M), hcX x x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add c (x : M) y)
      map_smul' := fun r x => Subtype.ext (by
        change c • (r • (x : M)) = r • (c • (x : M))
        exact smul_comm c r (x : M)) }
  have hμ : Function.Injective μ := by
    intro x y hxy
    have : c • ((x : M) - y) = 0 := by
      have h3 : c • (x : M) = c • (y : M) := congrArg Subtype.val hxy
      rw [smul_sub, h3, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (htf c _ hc this))
  have h1 : finrank (Int0 v) X' ≤ finrank (Int0 v) X := LinearMap.finrank_le_finrank_of_injective hι
  have h2 : finrank (Int0 v) X ≤ finrank (Int0 v) X' := LinearMap.finrank_le_finrank_of_injective hμ
  have heq : finrank (Int0 v) X' = finrank (Int0 v) X := le_antisymm h1 h2
  let b := Module.finBasis (Int0 v) X
  let b' := Module.finBasisOfFinrankEq (Int0 v) X' heq
  let A := LinearMap.toMatrix b' b ι
  have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
    intro k
    have e := b.sum_repr (ι (b' k))
    have e2 := congrArg (Submodule.subtype X) e

    rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simpa [A, LinearMap.toMatrix_apply, ι] using e2.symm
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw0
    have : ι (b'.equivFun.symm w) = 0 := by
      have := Matrix.toLin_toMatrix b' b ι
      rw [← this, Matrix.toLin_apply]
      simp only [Basis.equivFun_symm_apply, Basis.repr_sum_self]
      change ∑ x, (A.mulVec w) x • b x = 0
      simp [hw]
    have h4 := hι (this.trans (map_zero ι).symm)
    have h5 := congrArg b'.equivFun h4
    rw [LinearEquiv.apply_symm_apply, map_zero] at h5
    exact h5
  have hv : v (A.det : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact_mod_cast hdet
  exact ⟨(v (A.det : C)).untop hv, _, b, b', A, hA, (WithTop.coe_untop _ hv).symm⟩

end GlobalTheory.SubLen
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.ScalLen

theorem relLen_map_lsmul : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) →
    ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ),
      v (c : C) = r →
      RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  intro C _ v M _ _ htf X hX c r hr
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hr
  have : Module.IsTorsionFree (Int0 v) X := ⟨fun s hs x y hxy => by
    have hs0 : s ≠ 0 := hs.ne_zero
    apply Subtype.ext
    have h1 : s • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      have := congrArg Subtype.val hxy
      simp only [Submodule.coe_smul] at this
      rw [this, sub_self]
    exact sub_eq_zero.1 (htf s _ hs0 h1)⟩
  have : ValuationRing (Int0 v) := by
    have hInt : Int0 v = v.toValuation.integer := by
      ext x
      rw [mem_addValuationIntegerRing_iff]
    rw [hInt]
    infer_instance
  have : Module.Free (Int0 v) X :=
    GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := ↥X)
  set n := finrank (Int0 v) X with hn
  let b : Basis (Fin n) (Int0 v) X := Module.finBasis _ _
  let g : X →ₗ[Int0 v] M := (LinearMap.lsmul (Int0 v) M c).comp X.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have h1 : c • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.lsmul_apply] at hxy
      rw [hxy, sub_self]
    exact sub_eq_zero.1 (htf c _ hc h1)
  have hrange : LinearMap.range g = X.map (LinearMap.lsmul (Int0 v) M c) := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  let e : X ≃ₗ[Int0 v] X.map (LinearMap.lsmul (Int0 v) M c) :=
    (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.RelLen
  refine ⟨n, b, b.map e, Matrix.diagonal (fun _ => c), fun k => ?_, ?_⟩
  · simp only [Basis.map_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Subring.coe_pow, AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]

end GlobalTheory.ScalLen
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.rootSum_map_frobeniusPow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F →+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (k : ℕ) (P : F[X]), _root_.GlobalTheory.CuspGL.rootSum θ k (P.map t) = _root_.GlobalTheory.CuspGL.rootSum θ (k * ringChar F ^ j) P := by
  intro F _ _ θ t j ht k P
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  haveI : CharP (AlgebraicClosure F) (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective (ringChar F)
  haveI : ExpChar (AlgebraicClosure F) (ringChar F) := ExpChar.prime Fact.out
  unfold _root_.GlobalTheory.CuspGL.rootSum
  have hmap : (P.map t).map (algebraMap F (AlgebraicClosure F)) =
      (P.map (algebraMap F (AlgebraicClosure F))).map
        (iterateFrobenius (AlgebraicClosure F) (ringChar F) j) := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [iterateFrobenius_def, ht, map_pow]
  rw [hmap, ← roots_map_of_injective_of_card_eq_natDegree
    (iterateFrobenius (AlgebraicClosure F) (ringChar F) j).injective
    IsAlgClosed.card_roots_eq_natDegree, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  rw [Function.comp_apply, iterateFrobenius_def, map_pow, ← pow_mul, mul_comm]

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem rootSum_minpoly_pow_eq_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ)
    (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 →
    rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) =
      ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  intro F _ _ θ m l α hm hα
  rw [((GlobalTheory.CuspGL.torus_minpoly F θ m hm α hα).2.2 l)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_pow, ← pow_mul, mul_comm]

end GlobalTheory.Shin
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem map_range_mul_of_periodic {β : Type} (g : ℕ → β) (e : ℕ) (hg : ∀ i, g (e + i) = g i) (m : ℕ) :
    (Multiset.range (e * m)).map g = m • (Multiset.range e).map g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, add_comm (e * m), Multiset.range_add, Multiset.map_add (f := _), Multiset.map_map,
      succ_nsmul', ← ih]
    congr 1
    exact Multiset.map_congr rfl fun i _ => hg i

theorem roots_pow_eq_map_range {F : Type} [Field F] [Finite F] (f : F[X]) (m : ℕ) (hf : f.Monic)
    (hi : Irreducible f) (α : AlgebraicClosure F)
    (hα : α ∈ ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots) :
    ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (f ^ m).natDegree).map fun i => α ^ Nat.card F ^ i := by
  rw [Polynomial.map_pow, roots_pow] at hα ⊢
  have h1 := Multiset.mem_of_mem_nsmul hα
  have h2 : aeval α f = 0 := by
    rw [← eval_map_algebraMap]
    exact (mem_roots'.1 h1).2
  have h3 : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi h2 hf
  have hper := (minpoly_natDegree_dvd_iff_pow α _).1 dvd_rfl
  rw [natDegree_pow, mul_comm, h3, roots_minpoly_eq_map_range, map_range_mul_of_periodic]
  intro i
  simp only [pow_add, pow_mul, hper]

theorem natDegree_mul_esymm_roots_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by
  intro F _ _ θ f m k s hf hi
  set R := ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots with hR
  have hcard : R.card = (f ^ m).natDegree := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  have key : ∀ α ∈ R, (R.map fun α => θ α ^ k).esymm s =
      ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro α hα
    have h := roots_pow_eq_map_range f m hf hi α hα
    rw [← hR] at h
    conv_lhs => rw [h]
    rw [Multiset.map_map, ← Finset.range_val, Finset.esymm_map_val]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp, map_pow, ← pow_mul, mul_comm]
  have h2 : (R.map fun _ => (R.map fun α => θ α ^ k).esymm s).sum =
      (R.map fun α => ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i)).sum := by
    rw [Multiset.map_congr rfl key]
  rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at h2
  rw [h2, Multiset.sum_map_sum]
  rfl

end GlobalTheory.CuspGL
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem hasSum_prod_derivWeierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3)
      (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  have h := ((tauPair τ).hasSum_derivWeierstrassP z).mul_left (-(1 / 2))
  let e : ℤ × ℤ ≃ (tauPair τ).lattice :=
    (Equiv.neg (ℤ × ℤ)).trans (tauPair τ).latticeEquivProd.symm.toEquiv
  rw [← e.hasSum_iff] at h
  have key : (fun p : ℤ × ℤ => 1 / (z + p.1 * (τ : ℂ) + p.2) ^ 3) =
      (fun i : (tauPair τ).lattice => -(1 / 2) * (-2 / (z - (i : ℂ)) ^ 3)) ∘ e := ?_
  · rw [key]; exact h
  funext p
  have he : ((e p : (tauPair τ).lattice) : ℂ) = -(p.1 * (τ : ℂ) + p.2) := by
    change ((tauPair τ).latticeEquivProd.symm (-p)).1 = _
    rw [PeriodPair.latticeEquiv_symm_apply]
    simp [tauPair]
    ring
  simp only [Function.comp, he]
  rw [show z - -(p.1 * (τ : ℂ) + p.2) = z + p.1 * (τ : ℂ) + p.2 by ring]
  ring

theorem hasSum_rows_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  intro τ z
  have h := hasSum_prod_derivWeierstrassP τ z
  exact h.prod_fiberwise fun n => (h.summable.prod_factor n).hasSum

end GlobalTheory.WpFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_linear_operations : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  first | exact @GlobalTheory.QFam.hasQ_linear | exact GlobalTheory.QFam.hasQ_linear | (intros; apply GlobalTheory.QFam.hasQ_linear <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ * g τ) (conv a b) := by
  first | exact @GlobalTheory.QFam.hasQ_mul_conv | exact GlobalTheory.QFam.hasQ_mul_conv | (intros; apply GlobalTheory.QFam.hasQ_mul_conv <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), ActBij act → IsFam act w f → ∀ γ : SL(2, ℤ), ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧ ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ = fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  first | exact @GlobalTheory.QFam.sum_esymm_slash | exact GlobalTheory.QFam.sum_esymm_slash | (intros; apply GlobalTheory.QFam.sum_esymm_slash <;> assumption)
end
