module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

section

namespace GlobalTheory

open scoped MonoidAlgebra

theorem asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one :
    ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V), Module.finrank K (Representation.IntertwiningMap τ τ) = 1 → Nontrivial V ∧ Function.Surjective τ.asAlgebraHom := by
  intro K _ _ G _ _ V _ _ _ τ h
  classical
  have : NeZero (Nat.card G : K) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hV : Nontrivial V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : Subsingleton (Representation.IntertwiningMap τ τ) :=
      ⟨fun f g => Representation.IntertwiningMap.ext (Subsingleton.elim _ _)⟩
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, ?_⟩
  have : Nontrivial τ.asModule := hV
  have hE : Module.finrank K (Module.End K[G] τ.asModule) = 1 := by
    rw [← (Representation.IntertwiningMap.equivAlgEnd τ).toLinearEquiv.finrank_eq]
    exact h
  have hscalar : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, c • (1 : Module.End K[G] τ.asModule) = φ :=
    (finrank_eq_one_iff_of_nonzero' _ one_ne_zero).mp hE
  have : IsScalarTower K (Module.End K[G] τ.asModule) τ.asModule := ⟨fun _ _ _ => rfl⟩
  have : Module.Finite (Module.End K[G] τ.asModule) τ.asModule :=
    Module.Finite.of_restrictScalars_finite K _ _
  intro f
  let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
    { toFun := fun m => f m
      map_add' := fun x y => f.map_add x y
      map_smul' := fun φ m => by
        obtain ⟨c, rfl⟩ := hscalar φ
        exact f.map_smul c m }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := K[G]) (M := τ.asModule) F
  refine ⟨a, LinearMap.ext fun v => ?_⟩
  exact congrArg (fun g => g v) ha

end GlobalTheory
end

section

namespace GlobalTheory

theorem sum_conj_idempotent_eq_card_smul (L : Type) [Field L] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (T : Subgroup G)
    (e : Module.End L V) (hirr : ρ.IsIrreducible) (he0 : e ≠ 0) (hee : e * e = e)
    (hT : ∀ t ∈ T, ρ t * e = e * ρ t) (hoff : ∀ g ∉ T, e * ρ g * e = 0) :
    ∑ x : G, ρ x * e * ρ x⁻¹ = (Nat.card T : L) • (1 : Module.End L V) := by
  classical
  set E : Module.End L V := ∑ x : G, ρ x * e * ρ x⁻¹ with hE
  have hcomm : ∀ g : G, ρ g * E = E * ρ g := by
    intro g
    rw [hE, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro x
    have h1 : ρ (g * x)⁻¹ * ρ g = ρ x⁻¹ := by
      rw [← map_mul]; congr 1; group
    simp only [Equiv.coe_mulLeft]
    rw [mul_assoc (ρ (g * x) * e), h1, map_mul]
    simp only [mul_assoc]
  have hEe : E * e = (Nat.card T : L) • e := by
    rw [hE, Finset.sum_mul]
    have h2 : ∀ x : G, ρ x * e * ρ x⁻¹ * e = if x ∈ T then e else 0 := by
      intro x
      split_ifs with hx
      · have h3 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        rw [hT x hx, mul_assoc e, h3, mul_one, hee]
      · have h4 := hoff x⁻¹ (fun h => hx (by simpa using T.inv_mem h))
        calc ρ x * e * ρ x⁻¹ * e = ρ x * (e * ρ x⁻¹ * e) := by simp only [mul_assoc]
          _ = 0 := by rw [h4, mul_zero]
    rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.sum_filter, Finset.sum_const,
      Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set D : Module.End L V := E - (Nat.card T : L) • (1 : Module.End L V) with hD
  have hDc : ∀ g : G, ρ g * D = D * ρ g := by
    intro g
    rw [hD, mul_sub, sub_mul, hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hDe : D * e = 0 := by
    rw [hD, sub_mul, hEe, smul_mul_assoc, one_mul, sub_self]
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker D
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have := congrArg (fun f : Module.End L V => f v) (hDc g)
        simp only [Module.End.mul_apply] at this
        rw [← this, hv, map_zero] }
  have := hirr
  rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
  · exfalso
    apply he0
    ext v
    have hv : e v ∈ K.toSubmodule := by
      change e v ∈ LinearMap.ker D
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, hDe]; rfl
    rw [h] at hv
    exact hv
  · have hk : LinearMap.ker D = ⊤ := by
      change K.toSubmodule = ⊤
      rw [h]; rfl
    exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp hk)

end GlobalTheory
end
