module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle001
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle002
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
public import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem rootSum_isAdditive_and_pow_X_sub_one :
    ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ),
      IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  intro F _ θ k
  refine ⟨fun P Q hP hQ => ?_, fun j => ?_⟩
  · unfold rootSum
    rw [Polynomial.map_mul, Polynomial.roots_mul ((hP.map _).mul (hQ.map _)).ne_zero,
      Multiset.map_add, Multiset.sum_add]
  · unfold rootSum
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.sum_nsmul]
    simp

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem pow_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (n : ℕ) :
    (∀ x ∈ A, ((g + h) ^ n) x = (g ^ n) x ∧ (g ^ n) x ∈ A) ∧ ∀ x, ((g + h) ^ n) x - (g ^ n) x ∈ A := by
  induction n with
  | zero => exact ⟨fun x hx => ⟨by simp, by simpa using hx⟩, fun x => by simp⟩
  | succ n ih =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · obtain ⟨h1, h2⟩ := ih.1 x hx
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply, h1, hh.2 _ h2, add_zero, true_and]
      exact hg _ h2
    · have h1 := hg _ (ih.2 x)
      have h2 := hh.1 (((g + h) ^ n) x)
      have := A.add_mem h1 h2
      simp only [pow_succ', Module.End.mul_apply, LinearMap.add_apply]
      rw [map_sub] at this
      convert this using 1
      abel

theorem aeval_add_nilRad {A : Submodule F V} {g h : Module.End F V} (hg : ∀ x ∈ A, g x ∈ A)
    (hh : h ∈ nilRad A) (p : F[X]) :
    (∀ x ∈ A, aeval (g + h) p x = aeval g p x) ∧ ∀ x, aeval (g + h) p x - aeval g p x ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [map_add (f := _), LinearMap.add_apply, hp.1 x hx, hq.1 x hx]
    · have := A.add_mem (hp.2 x) (hq.2 x)
      simp only [map_add (f := _), LinearMap.add_apply]
      convert this using 1
      abel
  | monomial n a =>
    have H := pow_add_nilRad hg hh n
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simp only [aeval_monomial, Module.End.mul_apply, (H.1 x hx).1]
    · simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, ← smul_sub]
      exact A.smul_mem _ (H.2 x)

theorem ker_aeval_add_nilRad :
    ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  intro F _ V _ _ _ g h f hh
  have hg : ∀ x ∈ LinearMap.ker (aeval g f), g x ∈ LinearMap.ker (aeval g f) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have : aeval g f * g = g * aeval g f := by
      have h1 : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using h1
    rw [← Module.End.mul_apply, this, Module.End.mul_apply, hx, map_zero]
  refine ⟨fun x hx => ?_, fun he j => ?_⟩
  · rw [LinearMap.mem_ker, (aeval_add_nilRad hg hh f).1 x hx]
    exact hx
  · have : LinearMap.ker (aeval g (f ^ j)) = LinearMap.ker (aeval (g + h) (f ^ j)) := by
      cases j with
      | zero =>
        ext x
        simp
      | succ j =>
        ext x
        have H := (aeval_add_nilRad hg hh (f ^ j)).2 x
        have e1 : x ∈ LinearMap.ker (aeval g (f ^ (j + 1))) ↔
            aeval g (f ^ j) x ∈ LinearMap.ker (aeval g f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        have e2 : x ∈ LinearMap.ker (aeval (g + h) (f ^ (j + 1))) ↔
            aeval (g + h) (f ^ j) x ∈ LinearMap.ker (aeval (g + h) f) := by
          rw [pow_succ', map_mul, LinearMap.mem_ker, LinearMap.mem_ker, Module.End.mul_apply]
        rw [e1, e2, he]
        constructor
        · intro a
          have := Submodule.add_mem _ H a
          rwa [sub_add_cancel] at this
        · intro a
          have := Submodule.sub_mem _ a H
          rwa [sub_sub_cancel] at this
    rw [this]

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL


open Polynomial in
theorem _root_.GlobalTheory.CuspGL.ipGL_charpoly_eq_finsum_mass (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ) (s : F[X] → ℂ) :
    _root_.GlobalTheory.CuspGL.ipGL φ (fun g => s (LinearMap.charpoly g)) =
      ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0},
        _root_.GlobalTheory.CuspGL.mass φ P * star (s P) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  set S := {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} with hS
  set I := S ∩ Set.range (fun g : Module.End F V => LinearMap.charpoly g) with hI
  have hunit : ∀ g : Module.End F V, IsUnit g ↔ LinearMap.charpoly g ∈ S := by
    intro g
    simp only [hS, Set.mem_setOf_eq, LinearMap.charpoly_monic, LinearMap.charpoly_natDegree,
      true_and]
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff, isUnit_iff_ne_zero]
    simp
  have hset : {g : Module.End F V | IsUnit g} =
      ⋃ P ∈ I, {g : Module.End F V | LinearMap.charpoly g = P} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hI, Set.mem_inter_iff, Set.mem_range,
      exists_prop]
    rw [hunit]
    constructor
    · intro h
      exact ⟨_, ⟨h, g, rfl⟩, rfl⟩
    · rintro ⟨P, ⟨hP, _⟩, rfl⟩
      exact hP
  have hsupp : S ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) =
      I ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) := by
    ext P
    simp only [hI, Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hPS, hne⟩
      refine ⟨⟨hPS, ?_⟩, hne⟩
      by_contra hr
      apply hne
      have hempty : {g : Module.End F V | LinearMap.charpoly g = P} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hr ⟨g, h⟩
      unfold _root_.GlobalTheory.CuspGL.mass
      simp [hempty]
    · rintro ⟨⟨hPS, _⟩, hne⟩
      exact ⟨hPS, hne⟩
  rw [finsum_mem_inter_support_eq _ S I hsupp]
  unfold _root_.GlobalTheory.CuspGL.ipGL _root_.GlobalTheory.CuspGL.mass
  rw [hset, finsum_mem_biUnion ?_ ((Set.finite_range _).subset Set.inter_subset_right)
    (fun _ _ => Set.toFinite _)]
  · refine finsum_mem_congr rfl fun P _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Set.Finite.mem_toFinset] at hg
    show φ g * star (s (LinearMap.charpoly g)) = _
    rw [show LinearMap.charpoly g = P from hg]
  · intro P _ Q _ hPQ
    exact Set.disjoint_left.2 fun g hP hQ => hPQ (hP.symm.trans hQ)

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL Module.Basis

namespace GlobalTheory.CuspGL


open Module Module.Basis in
theorem charpoly_eq_restrict_mul_mapQ {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A) :
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) := by
  classical
  let bA := Module.finBasis F A
  let bQ := Module.finBasis F (V ⧸ A)
  let b := sumQuot bA bQ
  have hmat : LinearMap.toMatrix b b g = Matrix.fromBlocks (LinearMap.toMatrix bA bA (g.restrict hg))
      (Matrix.of fun i j => b.repr (g (b (Sum.inr j))) (Sum.inl i)) 0
      (LinearMap.toMatrix bQ bQ (A.mapQ A g (fun x hx => hg x hx))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁, b, sumQuot_inl]
      rw [sumQuot_repr_inl_of_mem bA bQ _ (hg _ (bA j).2)]
      rfl
    · simp [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, b]
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₁, b, sumQuot_inl,
        Matrix.zero_apply]
      exact sumQuot_repr_inr_of_mem bA bQ _ (hg _ (bA j).2) i
    · simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₂₂, b]
      rw [sumQuot_repr_inr, ← sumQuot_inr bA bQ j, Submodule.mapQ_apply]
      rfl
  rw [← LinearMap.charpoly_toMatrix g b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

theorem charpoly_block : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) *
      LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧
    ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by
  intro F _ V _ _ _ A g hg
  refine ⟨charpoly_eq_restrict_mul_mapQ A g hg, ?_⟩
  rintro h ⟨himg, hker⟩
  have hgh : ∀ x ∈ A, (g + h) x ∈ A := fun x hx => by
    simpa [LinearMap.add_apply, hker x hx] using hg x hx
  have hres : (g + h).restrict hgh = g.restrict hg := by
    ext x
    simp [LinearMap.restrict_apply, hker x x.2]
  have hquot : A.mapQ A (g + h) (fun x hx => hgh x hx) = A.mapQ A g (fun x hx => hg x hx) := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simpa [LinearMap.add_apply] using himg x
  rw [charpoly_eq_restrict_mul_mapQ A (g + h) hgh, charpoly_eq_restrict_mul_mapQ A g hg, hres, hquot]

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] [Finite F]


open Polynomial in
variable {F : Type} [Field F] [Finite F] in
theorem _root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow (α : AlgebraicClosure F) (m : ℕ) :
    (minpoly F α).natDegree ∣ m ↔ α ^ Nat.card F ^ m = α := by
  rw [(minpoly.irreducible (Algebra.IsIntegral.isIntegral α)).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,
    minpoly.dvd_iff]
  simp [sub_eq_zero]


open Polynomial in
variable {F : Type} [Field F] [Finite F] in
theorem _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range (α : AlgebraicClosure F) :
    ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (minpoly F α).natDegree).map fun i => α ^ Nat.card F ^ i := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hσ : ∀ (i : ℕ) (x : AlgebraicClosure F), (σ ^ i) x = x ^ Nat.card F ^ i := fun i x => by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hne : (minpoly F α).map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have key : ∀ i j, i < j → j < (minpoly F α).natDegree →
      α ^ Nat.card F ^ i = α ^ Nat.card F ^ j → False := by
    intro i j hij hj h
    have hfix : α ^ Nat.card F ^ (j - i) = α := by
      apply (σ ^ i).injective
      rw [hσ, hσ, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
      exact h.symm
    have hdvd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α (j - i)).mpr hfix
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnodup : ((Multiset.range (minpoly F α).natDegree).map
      fun i => α ^ Nat.card F ^ i).Nodup := by
    refine (Multiset.nodup_range _).map_on ?_
    intro i hi j hj hij
    rw [Multiset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · rw [Multiset.le_iff_subset hnodup]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    rw [mem_roots hne, IsRoot, eval_map_algebraMap, ← hσ, aeval_algHom_apply, minpoly.aeval,
      map_zero]
  · calc ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots.card
        ≤ ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).natDegree := card_roots' _
      _ = (minpoly F α).natDegree := natDegree_map _
      _ = _ := by simp

open Polynomial in
variable {F : Type} [Field F] [Finite F] in
private theorem sum_range_mul_eq_nsmul_of_periodic {M : Type} [AddCommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ i j, f (d * j + i) = f i) (e : ℕ) :
    ∑ i ∈ Finset.range (d * e), f i = e • ∑ i ∈ Finset.range d, f i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hf i e


open Polynomial in
variable {F : Type} [Field F] [Finite F] in
theorem _root_.GlobalTheory.CuspGL.torus_minpoly : ∀ (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n →
    ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
      (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧
        ∀ k : ℕ, _root_.GlobalTheory.CuspGL.rootSum θ k
            (minpoly F α ^ (n / (minpoly F α).natDegree)) =
          ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  intro F _ _ θ n hn α hα
  rw [Set.mem_setOf_eq] at hα
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqn : 1 < Nat.card F ^ n := Nat.one_lt_pow (by omega) hq
  have hfix : α ^ Nat.card F ^ n = α := by
    calc α ^ Nat.card F ^ n = α ^ (Nat.card F ^ n - 1) * α := by
          rw [← pow_succ, Nat.sub_add_cancel hqn.le]
      _ = α := by rw [hα, one_mul]
  have hd := (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α n).mpr hfix
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hα
    exact zero_ne_one hα
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  refine ⟨hd, minpoly.coeff_zero_ne_zero hint hα0, fun k => ?_⟩
  obtain ⟨e, he⟩ := hd
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
  have hper : ∀ i j, α ^ Nat.card F ^ ((minpoly F α).natDegree * j + i) =
      α ^ Nat.card F ^ i := fun i j => by
    rw [pow_add, pow_mul,
      (_root_.GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow α _).mp (dvd_mul_right _ _)]
  rw [he, Nat.mul_div_cancel_left e hdpos,
    sum_range_mul_eq_nsmul_of_periodic (fun i => θ (α ^ Nat.card F ^ i) ^ k) _
      (fun i j => by simp only [hper]) e]
  unfold _root_.GlobalTheory.CuspGL.rootSum
  rw [Polynomial.map_pow, roots_pow, _root_.GlobalTheory.CuspGL.roots_minpoly_eq_map_range, Multiset.map_nsmul,
    Multiset.sum_nsmul, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

end GlobalTheory.CuspGL
end

section

namespace GlobalTheory

theorem exists_common_eigenvector_of_commute {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V]
    (f : ι → Module.End L V) (hf : ∀ a b, f a * f b = f b * f a) :
    ∃ v : V, v ≠ 0 ∧ ∀ b, ∃ μ : L, f b v = μ • v := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeLemma.main
  | exact _root_.GlobalTheory.UnimodularLatticeLemma.main
  | (apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeLemma.main ..)

theorem exists_character_eigenvector_of_commute :
    ∀ (L : Type) [Field L] [IsAlgClosed L] (B : Type) [Group B] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V] (ρ : Representation L B V), (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∃ (lam : B →* Lˣ) (v : V), v ≠ 0 ∧ ∀ b, ρ b v = (lam b : L) • v := by
  intro L _ _ B _ V _ _ _ _ ρ h
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector_of_commute (fun b => ρ b) h
  choose μ hμ using hv
  have hinj : Function.Injective fun c : L => c • v := smul_left_injective L hv0
  let χ : B →* L :=
    { toFun := μ
      map_one' := hinj (by
        have := hμ 1
        simp only [map_one, Module.End.one_apply] at this
        simpa using this.symm)
      map_mul' := fun a b => hinj (by
        have h1 := hμ (a * b)
        simp only [map_mul, Module.End.mul_apply] at h1
        have h2 := hμ a
        have h3 := hμ b
        simp only at h2 h3 ⊢
        rw [← h1, h3, map_smul, h2, smul_smul, mul_comm]) }
  exact ⟨χ.toHomUnits, v, hv0, fun b => hμ b⟩

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  first | exact @GlobalTheory.exists_coprime_orderOf_pow_prime_pow | exact GlobalTheory.exists_coprime_orderOf_pow_prime_pow | (intros; apply GlobalTheory.exists_coprime_orderOf_pow_prime_pow <;> assumption)
end

section


theorem _root_.GlobalTheory.T.linear_map_short_exact_commute : ∀ (K : Type) [Field K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W), Function.Injective i → Function.Surjective p → LinearMap.range i = LinearMap.ker p → b ∘ₗ i = i ∘ₗ a → p ∘ₗ b = c ∘ₗ p → LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  first | exact @GlobalTheory.trace_eq_add_of_shortExact | exact GlobalTheory.trace_eq_add_of_shortExact | (intros; apply GlobalTheory.trace_eq_add_of_shortExact <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_weight_idempotent_of_eigenvector : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G) (lam : B →* Lˣ) (v : V), B.Normal → v ≠ 0 → (∀ b : B, ρ b v = (lam b : L) • v) → (∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) → ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧ (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  first | exact @GlobalTheory.exists_weight_idempotent | exact GlobalTheory.exists_weight_idempotent | (intros; apply GlobalTheory.exists_weight_idempotent <;> assumption)
end

section


theorem _root_.GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible : ∀ (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V), ρ.IsIrreducible → (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧ (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) → ∀ g, ρ.character g = (lam g : L)) := by
  first | exact @GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | exact GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | (intros; apply GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight <;> assumption)
end
