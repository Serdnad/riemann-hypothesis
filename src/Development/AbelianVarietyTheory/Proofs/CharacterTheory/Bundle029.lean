module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle026
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle004
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_irreducible_subrepresentation {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, S.toSubmodule ≠ ⊥ ∧
      Module.finrank K S.toSubmodule = m :=
    ⟨_, ⟨⊤, fun _ _ _ => Submodule.mem_top⟩, top_ne_bot, rfl⟩
  obtain ⟨S, hS, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, T.toSubmodule ≠ ⊥ →
      Module.finrank K S.toSubmodule ≤ Module.finrank K T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  have : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hS
  refine ⟨S, ?_⟩
  have : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule K S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'⟩
  refine ⟨fun T => ?_⟩
  by_cases hT : T.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hT)
  · right
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hT' : T'.toSubmodule ≠ ⊥ := by
      intro h
      apply hT
      have h2 : T.toSubmodule.map S.toSubmodule.subtype = ⊥ := h
      rwa [← Submodule.map_bot S.toSubmodule.subtype,
        (Submodule.map_injective_of_injective S.toSubmodule.injective_subtype).eq_iff] at h2
    have h1 := hmin T' hT'
    have h2 : Module.finrank K T'.toSubmodule = Module.finrank K T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 : T.toSubmodule = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h2 ▸ h1))
    exact Subrepresentation.toSubmodule_injective h3

theorem exists_irrChar_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (a : G → L), IsChar K L a → a ≠ 0 → ∃ φ c : G → L, IsIrrChar K L φ ∧ IsChar K L c ∧ a = φ + c := by
  intro K L _ _ _ G _ a ha h0
  obtain ⟨n, ρ, hρ⟩ := ha
  have hn : Nontrivial (Fin n → K) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply h0
    funext g
    have : ρ g = 0 := Subsingleton.elim _ _
    simp [hρ, Representation.character, this]
  obtain ⟨S, hS⟩ := exists_irreducible_subrepresentation ρ
  let f : Representation.IntertwiningMap S.toRepresentation ρ :=
    ⟨S.toSubmodule.subtype, fun g => by ext v; rfl⟩
  obtain ⟨c, hc, hcg⟩ := GlobalTheory.T.exists_character_quotient_of_injective_intertwining K L G _ _ ρ S.toRepresentation f
    S.toSubmodule.injective_subtype
  refine ⟨_, c, (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ S.toRepresentation).2 hS, hc, ?_⟩
  funext g
  rw [hρ, hcg]
  rfl

end GlobalTheory.BI
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (ind H ψ) := by
  first | exact @GlobalTheory.BI.isChar_ind | exact GlobalTheory.BI.isChar_ind | (intros; apply GlobalTheory.BI.isChar_ind <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_mem_virt_complex {G : Type} [Group G] {χ : G → ℂ}
    (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) : χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G :=
  AddSubgroup.subset_closure h

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_mul_complex {G : Type} [Group G] {a b : G → ℂ}
    (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) (hb : _root_.GlobalTheory.BI.IsChar ℂ ℂ b) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (a * b) := by
  obtain ⟨n, ρ, hρ⟩ := ha
  obtain ⟨m, σ, hσ⟩ := hb
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (Representation.tprod ρ σ)).1
  convert key using 1
  funext g
  simp [Representation.char_tensor, hρ, hσ]

open Polynomial in
private lemma trace_mulLeft_complex_lemma (z : ℂ) :
    LinearMap.trace ℂ ℂ (Algebra.lmul ℂ ℂ z) = z := by
  have hz : (Algebra.lmul ℂ ℂ z : ℂ →ₗ[ℂ] ℂ) = z • LinearMap.id := by
    ext x
    simp
  rw [hz, map_smul, LinearMap.trace_id]
  simp

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_monoidHom_complex {G : Type} [Group G] (lam : G →* ℂˣ) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun g => (lam g : ℂ)) := by
  let ρ : Representation ℂ G ℂ :=
    (Algebra.lmul ℂ ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp lam)
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G ℂ ρ).1
  convert key using 1
  funext g
  simpa [ρ, Representation.character] using (trace_mulLeft_complex_lemma (lam g : ℂ)).symm

open Polynomial in
theorem _root_.GlobalTheory.BI.subgroupFunctionExtendByZero_add {G : Type} [Group G] (H : Subgroup G) (a b : H → ℂ)
    (g : G) :
    _root_.GlobalTheory.BI.ext0 H (a + b) g =
      _root_.GlobalTheory.BI.ext0 H a g + _root_.GlobalTheory.BI.ext0 H b g := by
  unfold _root_.GlobalTheory.BI.ext0
  split_ifs <;> simp

noncomputable def indAddHomComplex {G : Type} [Group G] [Finite G] (H : Subgroup G) : (H → ℂ) →+ (G → ℂ) :=
  AddMonoidHom.mk' (ind H) (fun a b => by
    funext g
    haveI := Fintype.ofFinite G
    simp only [ind, Pi.add_apply, subgroupFunctionExtendByZero_add, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, mul_add])


open Polynomial in
theorem _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear : ∀ (G : Type) [Group G] [Finite G],
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G,
      a * b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G),
      (fun h => a (f h)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧
    (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H →
      _root_.GlobalTheory.BI.ind H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by
  intro G _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      induction hb using AddSubgroup.closure_induction with
      | mem b hb' => exact AddSubgroup.subset_closure (_root_.GlobalTheory.BI.isChar_mul_complex ha' hb')
      | zero => simpa using zero_mem _
      | add b c _ _ hb hc => simpa [mul_add] using add_mem hb hc
      | neg b _ hb => simpa [mul_neg] using neg_mem hb
    | zero => simpa using zero_mem _
    | add a c _ _ ha hc => simpa [add_mul] using add_mem ha hc
    | neg a _ ha => simpa [neg_mul] using neg_mem ha
  · intro a ha H _ f
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      exact AddSubgroup.subset_closure
        ((_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').1 H f)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | neg a _ ha => exact neg_mem ha
  · intro a ha g x
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' => exact (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').2.1 g x
    | zero => rfl
    | add a c _ _ ha hc => simp [ha, hc]
    | neg a _ ha => simp [ha]
  · intro H ψ hψ
    change _root_.GlobalTheory.BI.indAddHomComplex H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G
    induction hψ using AddSubgroup.closure_induction with
    | mem ψ hψ' =>
      exact AddSubgroup.subset_closure
        (_root_.GlobalTheory.BI.isChar_ind ℂ ℂ G H ψ hψ')
    | zero => simpa using zero_mem _
    | add ψ φ _ _ hψ hφ => simpa [map_add (f := _)] using add_mem hψ hφ
    | neg ψ _ hψ => simpa [map_neg] using neg_mem hψ
  · intro lam
    exact _root_.GlobalTheory.BI.isChar_mem_virt_complex (_root_.GlobalTheory.BI.isChar_monoidHom_complex lam)

end GlobalTheory.BI
end
