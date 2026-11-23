module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

section

noncomputable section

namespace PositivityTheory.Rg.Cz

namespace TF

theorem monic_lprod (L : List ℂ) : (L.map fun c => Polynomial.X - Polynomial.C c).prod.Monic := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [List.map_cons, List.prod_cons]
    exact (Polynomial.monic_X_sub_C c).mul ih

theorem fin_adjoin {A : Type*} [Ring A] [Algebra ℂ A] {ι : Type*} [Finite ι] (x : ι → A)
    (hc : ∀ i j, Commute (x i) (x j)) (hL : ∀ i, ∃ L : List ℂ, (L.map fun c => x i - algebraMap ℂ A c).prod = 0) :
    FiniteDimensional ℂ (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range x))) := by
  classical
  have hcomm : (Set.range x).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range x)) := Algebra.isMulCommutative_adjoin ℂ hcomm
  letI : CommRing (Algebra.adjoin ℂ (Set.range x)) := by
    open scoped IsMulCommutative in
      exact inferInstance
  have hint : ∀ i, IsIntegral ℂ (x i) := by
    intro i
    obtain ⟨L, hL⟩ := hL i
    refine ⟨(L.map fun c => Polynomial.X - Polynomial.C c).prod, monic_lprod L, ?_⟩
    rw [← Polynomial.aeval_def, map_list_prod, List.map_map]
    have hf : (⇑(Polynomial.aeval (x i)) ∘ fun c => Polynomial.X - Polynomial.C c) =
        fun c => x i - algebraMap ℂ A c := by
      funext c
      simp [Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hf]
    exact hL
  let y : ι → Algebra.adjoin ℂ (Set.range x) := fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hyint : ∀ z ∈ Set.range y, IsIntegral ℂ z := by
    rintro _ ⟨i, rfl⟩
    exact (isIntegral_algHom_iff (Algebra.adjoin ℂ (Set.range x)).val Subtype.val_injective).1 (hint i)
  have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral (R := ℂ) (Set.finite_range y) hyint
  have hset : Set.range y = Subtype.val ⁻¹' (Set.range x) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have htop : Algebra.adjoin ℂ (Set.range y) = ⊤ := by
    rw [hset]
    exact Algebra.adjoin_adjoin_coe_preimage
  rw [htop] at hfin
  have hS : Module.Finite ℂ (Algebra.adjoin ℂ (Set.range x)) :=
    Module.Finite.equiv Subalgebra.topEquiv.toLinearEquiv
  exact Subalgebra.finiteDimensional_toSubmodule.2 hS

end TF

end PositivityTheory.Rg.Cz
end
end

section

noncomputable section

namespace PositivityTheory.Rg.Cz

namespace TF

theorem pow_mem' {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ k : ℕ, ∀ z ∈ Z, (T ^ k) z ∈ Z := by
  intro k
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih => intro z hz; rw [pow_succ', Module.End.mul_apply]; exact hZ _ (ih z hz)

theorem restrict_pow_coe {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (Z : Submodule ℂ U)
    (hZ : ∀ z ∈ Z, T z ∈ Z) : ∀ (k : ℕ) (w : Z), (((T.restrict hZ) ^ k) w : U) = (T ^ k) (w : U) := by
  intro k
  induction k with
  | zero => intro w; simp
  | succ k ih => intro w; rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, ← Module.End.mul_apply, ← pow_succ']

theorem fit_step {U : Type*} [AddCommGroup U] [Module ℂ U] (T : Module.End ℂ U) (e : U →ₗ[ℂ] ℂ)
    (Z : Submodule ℂ U) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) (he : ∀ z ∈ Z, e (T z) = 0)
    (z0 : U) (hz0 : z0 ∈ Z) (hez : e z0 ≠ 0) : ∃ N : ℕ, ∃ a ∈ Z, (T ^ N) a = 0 ∧ e a ≠ 0 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (LinearMap.eventually_isCompl_ker_pow_range_pow (T.restrict hZ))
  have hc := hN (N + 1) (by omega)
  have hmem : (⟨z0, hz0⟩ : Z) ∈ LinearMap.ker ((T.restrict hZ) ^ (N + 1)) ⊔
      LinearMap.range ((T.restrict hZ) ^ (N + 1)) := by
    rw [hc.codisjoint.eq_top]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨w, rfl⟩ := hb
  refine ⟨N + 1, a, a.2, ?_, ?_⟩
  · rw [← restrict_pow_coe T Z hZ, LinearMap.mem_ker.1 ha]; rfl
  · have h1 : (z0 : U) = (a : U) + (T ^ (N + 1)) (w : U) := by
      rw [← restrict_pow_coe T Z hZ, ← Submodule.coe_add, hab]
    have h2 : e ((T ^ (N + 1)) (w : U)) = 0 := by
      rw [pow_succ', Module.End.mul_apply]
      exact he _ (pow_mem' T Z hZ N _ w.2)
    intro h0
    apply hez
    rw [h1, map_add (f := _), h0, h2, add_zero]

theorem common_ker {U : Type*} [AddCommGroup U] [Module ℂ U] (T : ℕ → Module.End ℂ U)
    (hT : ∀ i j, Commute (T i) (T j)) (e : U →ₗ[ℂ] ℂ) (s : Finset ℕ) :
    ∀ Z : Submodule ℂ U, FiniteDimensional ℂ Z → (∀ i ∈ s, ∀ z ∈ Z, T i z ∈ Z) →
      (∀ i ∈ s, ∀ z ∈ Z, e (T i z) = 0) → (∃ z ∈ Z, e z ≠ 0) → ∃ z ∈ Z, z ≠ 0 ∧ ∀ i ∈ s, T i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro Z - - - ⟨z, hz, hez⟩
    exact ⟨z, hz, fun h => hez (by rw [h, map_zero]), by simp⟩
  | @insert i0 s hi0 ih =>
    rintro Z hfd hZ he ⟨z0, hz0, hez⟩
    have hZ0 := hZ i0 (Finset.mem_insert_self _ _)
    obtain ⟨N, a, haZ, haN, hea⟩ :=
      fit_step (T i0) e Z hZ0 (he i0 (Finset.mem_insert_self _ _)) z0 hz0 hez
    have hfd' : FiniteDimensional ℂ ↥(Z ⊓ LinearMap.ker (T i0 ^ N)) :=
      Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨z1, hz1, hz1ne, hz1s⟩ := ih (Z ⊓ LinearMap.ker (T i0 ^ N)) hfd'
      (fun i hi z hz => by
        refine ⟨hZ i (Finset.mem_insert_of_mem hi) z hz.1, ?_⟩
        have hk : (T i0 ^ N) z = 0 := hz.2
        show (T i0 ^ N) (T i z) = 0
        rw [← Module.End.mul_apply, ((hT i i0).pow_right N).eq.symm,
          Module.End.mul_apply, hk, map_zero])
      (fun i hi z hz => he i (Finset.mem_insert_of_mem hi) z hz.1) ⟨a, ⟨haZ, haN⟩, hea⟩
    have hex : ∃ k, (T i0 ^ k) z1 = 0 := ⟨N, hz1.2⟩
    have hk0 : Nat.find hex ≠ 0 := by
      intro h
      have := Nat.find_spec hex
      rw [h, pow_zero, Module.End.one_apply] at this
      exact hz1ne this
    refine ⟨(T i0 ^ (Nat.find hex - 1)) z1, pow_mem' _ _ hZ0 _ _ hz1.1, Nat.find_min hex (by omega), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      exact Nat.find_spec hex
    · rw [← Module.End.mul_apply, ((hT i i0).pow_right _).eq, Module.End.mul_apply, hz1s i hi, map_zero]

end TF

end PositivityTheory.Rg.Cz
end
end
