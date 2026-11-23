module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle030
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle033
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle032
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle034
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle019
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle017
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem isChar_of_isIrrChar (K L : Type) [Field K] [Field L]
    [Algebra K L] {G : Type} [Group G] (φ : G → L) (hφ : _root_.GlobalTheory.BI.IsIrrChar K L φ) :
    _root_.GlobalTheory.BI.IsChar K L φ := by
  obtain ⟨n, ρ, _, hρ⟩ := hφ
  exact ⟨n, ρ, hρ⟩

theorem _root_.GlobalTheory.BI.isChar_of_isChar_of_mem_virt (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (χ : G → L) (hχ : _root_.GlobalTheory.BI.IsChar L L χ) (hv : χ ∈ _root_.GlobalTheory.BI.Virt K L G) :
    _root_.GlobalTheory.BI.IsChar K L χ := by
  obtain ⟨a, b, ha, hb, hab⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub K L G χ).1 hv
  obtain ⟨hadd, hnat, hpos, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm K L G
  obtain ⟨-, hnatL, -, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm L L G
  have key : ∀ c : G → L, _root_.GlobalTheory.BI.IsChar K L c →
      ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a = χ + c → _root_.GlobalTheory.BI.IsChar K L χ := by
    refine _root_.GlobalTheory.BI.isChar_induction K L G _ ?_ ?_
    · intro a ha h
      rw [add_zero] at h
      exact h ▸ ha
    · intro φ c hφ hc ih a ha h
      have hφc := isChar_of_isIrrChar K L φ hφ
      obtain ⟨n₁, h₁⟩ := hnatL χ φ hχ (_root_.GlobalTheory.BI.isChar_baseChange K L G φ hφc)
      obtain ⟨n₂, hn₂, h₂⟩ := hpos φ hφ
      obtain ⟨n₃, h₃⟩ := hnat c φ hc hφc
      have hne : _root_.GlobalTheory.BI.pair a φ ≠ 0 := by
        rw [h, hadd, hadd, h₁, h₂, h₃]
        exact_mod_cast (by omega : n₁ + (n₂ + n₃) ≠ 0)
      obtain ⟨a', ha', ha'eq⟩ := _root_.GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero K L G φ a hφ ha hne
      refine ih a' ha' ?_
      have : φ + a' = φ + (χ + c) := by
        rw [← ha'eq, h]
        abel
      exact add_left_cancel this
  exact key b hb a ha (by rw [hab]; abel)

end GlobalTheory.BI
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_induction_irreducible : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (Q : (G → L) → Prop), Q 0 → (∀ φ c : G → L, IsIrrChar K L φ → IsChar K L c → Q c → Q (φ + c)) → ∀ a : G → L, IsChar K L a → Q a := by
  first | exact @GlobalTheory.BI.isChar_induction | exact GlobalTheory.BI.isChar_induction | (intros; apply GlobalTheory.BI.isChar_induction <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) → ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by
  first | exact @GlobalTheory.BI.mem_virt_of_forall_abByP | exact GlobalTheory.BI.mem_virt_of_forall_abByP | (intros; apply GlobalTheory.BI.mem_virt_of_forall_abByP <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_psi | exact GlobalTheory.CuspGL.isPrimitive_psi | (intros; apply GlobalTheory.CuspGL.isPrimitive_psi <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem cyclic_conj {F : Type} [Field F] {V V' : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup V'] [Module F V'] (e : V ≃ₗ[F] V') (g : Module.End F V) (v : V) :
    (∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤) ↔
      (∀ U : Submodule F V', (∀ x ∈ U, (e.conj g) x ∈ U) → e v ∈ U → U = ⊤) := by
  constructor
  · intro h U hU hv
    have h1 : U.comap (e : V →ₗ[F] V') = ⊤ := by
      refine h _ (fun x hx => ?_) hv
      have := hU (e x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e.symm y ∈ U.comap (e : V →ₗ[F] V') := h1 ▸ Submodule.mem_top
    simpa using this
  · intro h U hU hv
    have h1 : U.comap (e.symm : V' →ₗ[F] V) = ⊤ := by
      refine h _ (fun x hx => ?_) (by simpa using hv)
      have := hU (e.symm x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e y ∈ U.comap (e.symm : V' →ₗ[F] V) := h1 ▸ Submodule.mem_top
    simpa using this

theorem glCard_ne_zero_of_finite (F : Type) [Field F] [Finite F] (n : ℕ) : glCard F n ≠ 0 := by
  unfold glCard
  exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'

theorem mass_const {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (c : ℂ) (P : F[X]) :
    mass (fun _ : Module.End F V => c) P = c * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  unfold mass
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective (fun g : Module.End F V => (g : V → V))
    DFunLike.coe_injective
  have hs : {g : Module.End F V | LinearMap.charpoly g = P}.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  simp [mul_comm]

theorem mu_one (F : Type) [Field F] : mu (1 : F[X]) = 1 := by
  unfold mu
  have h : ∀ n : ℕ, n = 0 →
      mass (fun _ : Module.End F (Fin n → F) => (1 : ℂ)) 1 / glCard F n = 1 := by
    rintro n rfl
    have h1 : glCard F 0 = 1 := by
      unfold glCard
      haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      rw [Nat.card_unique]
      simp
    have h2 : {g : Module.End F (Fin 0 → F) | LinearMap.charpoly g = 1} = {0} := by
      ext g
      have hg : g = 0 := Subsingleton.elim _ _
      have hc : LinearMap.charpoly g = 1 := by
        apply (LinearMap.charpoly_monic g).natDegree_eq_zero.1
        rw [LinearMap.charpoly_natDegree]
        simp
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun _ => hg, fun _ => hc⟩
    unfold mass
    rw [h1, h2, finsum_mem_singleton]
    simp
  exact h _ natDegree_one

theorem mu_rec : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic →
    (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  intro F _ _ P hP
  refine ⟨?_, mu_one F⟩
  have key := GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial F (Fin P.natDegree → F)
    (fun V _ _ _ g => (Nat.card {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ))
    (by
      intro V V' _ _ _ _ _ _ e g
      congr 1
      exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun v => cyclic_conj e g v)).symm)
    P hP (by simp)
  simp only [GlobalTheory.T.finsum_card_cyclic_vectors_invariant_subspaces] at key
  rw [mass_const] at key
  have hr : conv (fun D : F[X] => mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D / glCard F D.natDegree) mu P
      = conv (fun _ => 1) mu P := by
    unfold conv
    refine finsum_mem_congr rfl fun x hx => ?_
    beta_reduce
    rw [GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors F x.1 hx.1, div_self (glCard_ne_zero_of_finite F _)]
  rw [← hr, ← key]
  unfold mu
  simp [mul_div_assoc]

end GlobalTheory.CuspGL
end
