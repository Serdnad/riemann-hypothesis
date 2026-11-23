module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

namespace GlobalTheory

open Matrix Polynomial
open scoped BigOperators

theorem essFiniteType_of_finiteDimensional_subfield_closure {o Om : Type*} [CommRing o]
    [IsDomain o] [Field Om] [Algebra o Om] [FaithfulSMul o Om] {T : Set Om} (hT : T.Finite)
    (h : FiniteDimensional (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) Om) :
    Algebra.EssFiniteType o Om := by
  let K := FractionRing o
  letI : Algebra K Om := FractionRing.liftAlgebra o Om
  haveI : Algebra.EssFiniteType o K := .of_isLocalization K (nonZeroDivisors o)
  let E := IntermediateField.adjoin K T
  haveI : Algebra.EssFiniteType K E :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite hT)
  have hle : Subfield.closure (Set.range (algebraMap o Om) ∪ T) ≤ E.toSubfield := by
    refine Subfield.closure_le.mpr (Set.union_subset ?_ (IntermediateField.subset_adjoin K T))
    rintro _ ⟨x, rfl⟩
    rw [IsScalarTower.algebraMap_apply o K Om]
    exact E.algebraMap_mem _
  letI : Algebra (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E :=
    (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om :=
    .of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E Om :=
    .of_restrictScalars_finite (Subfield.closure (Set.range (algebraMap o Om) ∪ T)) E Om
  haveI : Algebra.EssFiniteType K Om := .comp K E Om
  exact .comp o K Om

end GlobalTheory
end

section

namespace GlobalTheory

theorem one_mem_of_mul_mem_of_forall_prime_not_dvd (X : Type) [Finite X]
    (S : AddSubgroup (X → ℤ)) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hp : ∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) : (1 : X → ℤ) ∈ S := by
  classical
  have h1 : ∀ x : X, ∃ f ∈ S, f x = 1 := by
    intro x
    obtain ⟨d, hd⟩ := Int.subgroup_cyclic (S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x))
    have hd1 : (d : ℤ).natAbs = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p pp hpd
      obtain ⟨f, hf, hnd⟩ := hp x p pp
      apply hnd
      have hmem : f x ∈ AddSubgroup.zmultiples (d : ℤ) := by
        obtain ⟨z, hz⟩ := hd ⟨f x, ⟨f, hf, rfl⟩⟩
        rw [Int.mem_zmultiples_iff]
        refine ⟨z, ?_⟩
        simpa [zsmul_eq_mul, mul_comm] using (congrArg Subtype.val hz).symm
      exact (Int.natCast_dvd.mpr hpd).trans (Int.mem_zmultiples_iff.mp hmem)
    have : (1 : ℤ) ∈ AddSubgroup.zmultiples (d : ℤ) := by
      rw [Int.mem_zmultiples_iff]
      exact isUnit_iff_dvd_one.mp (Int.isUnit_iff_natAbs_eq.mpr hd1)
    have hmap : (1 : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) := by
      obtain ⟨z, hz⟩ := Int.mem_zmultiples_iff.mp this
      have hzmem : z • (d : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) :=
        AddSubgroup.zsmul_mem _ d.property z
      simpa [hz, mul_comm] using hzmem
    obtain ⟨f, hf, hfx⟩ := hmap
    exact ⟨f, hf, hfx⟩
  choose f hfS hf1 using h1
  have key : ∀ s : Finset X, 1 - ∏ x ∈ s, (1 - f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have e : 1 - (1 - f a) * ∏ x ∈ s, (1 - f x)
          = f a + (1 - ∏ x ∈ s, (1 - f x)) - f a * (1 - ∏ x ∈ s, (1 - f x)) := by ring
      rw [e]
      exact S.sub_mem (S.add_mem (hfS a) ih) (hmul _ (hfS a) _ ih)
  haveI := Fintype.ofFinite X
  have h0 : ∏ x : X, (1 - f x) = 0 := by
    funext y
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [hf1])
  simpa [h0] using key Finset.univ

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.UnimodularLatticeExistence

open Representation

theorem main : ∀ {G : Type u_1} [inst : Group G] {V : Type u_2} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have htop : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]
      exact Subsingleton.elim _ _
    · intro U hU
      let σ : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top σ with h1 | h1
      · left
        have := congrArg Subrepresentation.toSubmodule h1
        exact this
      · right
        have := congrArg Subrepresentation.toSubmodule h1
        exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule h
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine ⟨fun σ => ?_⟩
    rcases hU σ.toSubmodule (fun g v hv => σ.apply_mem_toSubmodule g hv) with h1 | h1
    · left
      apply Subrepresentation.toSubmodule_injective
      rw [h1, hbot]
    · right
      apply Subrepresentation.toSubmodule_injective
      rw [h1, htop]

end GlobalTheory.UnimodularLatticeExistence
end

section

namespace GlobalTheory

theorem card_fixedBy_pow_prime_pow_modEq (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End (MulAction.fixedBy X (x ^ p ^ k)) := fun y => ⟨x • (y : X), by
    have hy : (x ^ p ^ k) • (y : X) = y := y.2
    show (x ^ p ^ k) • x • (y : X) = x • (y : X)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩
  have hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X) := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_smul, ← ih y]
      rfl
  have h1 : f ^ p ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hf]
    exact y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1
  have e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x :=
    { toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩
      invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by
          rwa [zpow_natCast] at h⟩, Subtype.ext y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_sylow_over_subgroup (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ)
    (hp : p.Prime) :
    ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧
      (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧
      ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G :=
    { carrier := {g | ∀ c ∈ C, g * c * g⁻¹ ∈ C}
      one_mem' := by intro c hc; simpa using hc
      mul_mem' := by
        intro a b ha hb c hc
        have := ha _ (hb c hc)
        simpa [mul_assoc] using this
      inv_mem' := by
        intro a ha c hc
        have key : ∀ n : ℕ, ∀ c ∈ C, a ^ n * c * (a ^ n)⁻¹ ∈ C := by
          intro n
          induction n with
          | zero => intro c hc; simpa using hc
          | succ n ih =>
            intro c hc
            have := ha _ (ih c hc)
            simpa [pow_succ', mul_assoc] using this
        have h1 : a ^ (orderOf a - 1) = a⁻¹ := by
          have hpos : 0 < orderOf a := orderOf_pos a
          apply eq_inv_of_mul_eq_one_left
          rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        have := key (orderOf a - 1) c hc
        rwa [h1] at this }
  have hN : ∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g => Iff.rfl
  let C' : Subgroup N := C.subgroupOf N
  haveI hC' : C'.Normal := ⟨fun n hn g => by
    simp only [C', Subgroup.mem_subgroupOf] at hn ⊢
    exact (hN g).1 g.2 _ hn⟩
  let P : Sylow p (N ⧸ C') := Classical.arbitrary _
  let H' : Subgroup N := (P : Subgroup (N ⧸ C')).comap (QuotientGroup.mk' C')
  refine ⟨H'.map N.subtype, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hcN : c ∈ N := (hN c).2 fun d hd => C.mul_mem (C.mul_mem hc hd) (C.inv_mem hc)
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    have : QuotientGroup.mk' C' ⟨c, hcN⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    change QuotientGroup.mk' C' ⟨c, hcN⟩ ∈ (P : Subgroup (N ⧸ C'))
    rw [this]
    exact one_mem _
  · rintro _ ⟨h, -, rfl⟩
    exact (hN h).1 h.2
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' C' h, hh⟩
    refine ⟨k, ?_⟩
    have h2 : QuotientGroup.mk' C' (h ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  · intro N' hN'
    obtain rfl : N' = N := by
      ext g
      rw [hN', hN]
    have h1 : (H'.map N.subtype).subgroupOf N = H' :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective H'
    rw [Subgroup.relIndex, h1]
    have h2 : H'.index = (P : Subgroup (N ⧸ C')).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C')
    rw [h2]
    exact P.not_dvd_index

end GlobalTheory
end

section

namespace GlobalTheory.UnimodularLatticeLemma

theorem main {L : Type} [Field L] [IsAlgClosed L] {ι V : Type} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V] (f : ι → Module.End L V)
    (hc : ∀ (a b : ι), f a * f b = f b * f a) :
    ∃ (v : V), v ≠ (0 : V) ∧ ∀ (b : ι), ∃ (μ : L), (f b : V → V) v = μ • v := by
  classical
  let S : Set (Submodule L V) := {W | W ≠ ⊥ ∧ ∀ b, ∀ x ∈ W, f b x ∈ W}
  have hS : (⊤ : Submodule L V) ∈ S := ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  obtain ⟨W, hW, hmin⟩ := (wellFounded_lt (α := Submodule L V)).has_min S ⟨⊤, hS⟩
  have key : ∀ b, ∃ μ : L, ∀ x ∈ W, f b x = μ • x := by
    intro b
    have hWb : ∀ x ∈ W, f b x ∈ W := hW.2 b
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((f b).restrict hWb)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : (f b).restrict hWb w = μ • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    let W' : Submodule L V := W ⊓ LinearMap.ker (f b - μ • 1)
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ f b x = μ • x := by
      intro x
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hW'S : W' ∈ S := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw0
        have : (w : V) ∈ W' := by
          rw [hmem]
          refine ⟨w.2, ?_⟩
          have := congrArg Subtype.val hw1
          simpa using this
        rw [h, Submodule.mem_bot] at this
        exact Subtype.ext this
      · intro c x hx
        rw [hmem] at hx ⊢
        refine ⟨hW.2 c x hx.1, ?_⟩
        have h1 : f b (f c x) = (f b * f c) x := rfl
        rw [h1, hc b c, Module.End.mul_apply, hx.2, map_smul]
    have hle : W' ≤ W := inf_le_left
    have heq : W' = W := by
      by_contra hne
      exact hmin W' hW'S (lt_of_le_of_ne hle hne)
    refine ⟨μ, fun x hx => ?_⟩
    have : x ∈ W' := heq ▸ hx
    exact ((hmem x).1 this).2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
  refine ⟨v, hv0, fun b => ?_⟩
  obtain ⟨μ, hμ⟩ := key b
  exact ⟨μ, hμ v hvW⟩

end GlobalTheory.UnimodularLatticeLemma
end

section

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

def E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

def W8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  0, -1,  0,  0,  0,  0,  0;
       0,  1,  0, -1,  0,  0,  0,  0;
       0,  0,  1, -1,  0,  0,  0,  0;
       0,  0,  0,  1, -1,  0,  0,  0;
       0,  0,  0,  0,  1, -1,  0,  0;
       0,  0,  0,  0,  0,  1, -1,  0;
       0,  0,  0,  0,  0,  0,  1, -1;
       0,  0,  0,  0,  0,  0,  0,  1]

def E8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  7, 10,  8,  6,  4,  2;
       5,  8, 10, 15, 12,  9,  6,  3;
       7, 10, 14, 20, 16, 12,  8,  4;
      10, 15, 20, 30, 24, 18, 12,  6;
       8, 12, 16, 24, 20, 15, 10,  5;
       6,  9, 12, 18, 15, 12,  8,  4;
       4,  6,  8, 12, 10,  8,  6,  3;
       2,  3,  4,  6,  5,  4,  3,  2]

def w8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  3, -2, -2, -2, -2, -2;
       5,  8,  5, -3, -3, -3, -3, -3;
       7, 10,  7, -4, -4, -4, -4, -4;
      10, 15, 10, -5, -6, -6, -6, -6;
       8, 12,  8, -4, -4, -5, -5, -5;
       6,  9,  6, -3, -3, -3, -4, -4;
       4,  6,  4, -2, -2, -2, -2, -3;
       2,  3,  2, -1, -1, -1, -1, -1]

def E8roots : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  2, -2,  0,  0,  0,  0,  0;
      -1,  2,  2, -2,  0,  0,  0,  0;
      -1,  0,  0,  2, -2,  0,  0,  0;
      -1,  0,  0,  0,  2, -2,  0,  0;
      -1,  0,  0,  0,  0,  2, -2,  0;
      -1,  0,  0,  0,  0,  0,  2, -2;
      -1,  0,  0,  0,  0,  0,  0,  2;
       1,  0,  0,  0,  0,  0,  0,  0]

theorem w8_add_transpose_eq_e8 : W8 + W8ᵀ = E8 := by decide

theorem e8_transpose : E8ᵀ = E8 := CartanMatrix.E₈_transpose

theorem e8_det_eq_one : E8.det = 1 := CartanMatrix.E₈_det

theorem e8inv_mul_e8 : E8inv * E8 = 1 := by decide

theorem e8_mul_e8inv : E8 * E8inv = 1 := by decide

theorem E8roots_transpose_mul_self : E8rootsᵀ * E8roots = (4 : ℤ) • E8 := by decide

theorem e8_posDef : (E8.map (fun x : ℤ => (x : ℝ))).PosDef := by
  set f : ℤ →+* ℝ := Int.castRingHom ℝ with hf
  change (E8.map f).PosDef
  have h : E8.map f = ((1 / 2 : ℝ) • E8roots.map f)ᴴ * ((1 / 2 : ℝ) • E8roots.map f) := by
    have h4 : (E8roots.map f)ᵀ * E8roots.map f = (4 : ℝ) • E8.map f := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, E8roots_transpose_mul_self]
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        smul_eq_mul, map_mul]
      simp [hf]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, h4, smul_smul, smul_smul]
    norm_num
  have hs : (E8.map f).PosSemidef := by
    rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _
  rw [hs.posDef_iff_det_ne_zero]
  have : (E8.map f).det = f E8.det := (RingHom.map_det f E8).symm
  rw [this, e8_det_eq_one, map_one]
  exact one_ne_zero

end GlobalTheory
end
