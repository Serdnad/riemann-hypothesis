module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle023
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle024
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyTransversalSubspaces
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent | exact GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent | (intros; apply GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent <;> assumption)
end

section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_ind : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L),
    IsChar K L ψ → IsChar K L (ind H ψ) := by
  intro K L _ _ _ _ _ G _ _ H ψ h
  have hcl : ∀ a x : H, ψ (x⁻¹ * a * x) = ψ a := (GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one K L H ψ h).2.1
  have e : ind H ψ = fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) :=
    funext (GlobalTheory.T.inducedClassFunctionFromSubgroup_eq_finsum_cosets L G H ψ hcl)
  rw [e]
  exact GlobalTheory.T.isCharacter_finsum_conj_subgroupFunctionExtendByZero K L G H ψ h
end GlobalTheory.BI
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.character_eq_induced_of_imprimitivity_system : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  first | exact @GlobalTheory.BI.character_eq_ind_of_imprimitive | exact GlobalTheory.BI.character_eq_ind_of_imprimitive | (intros; apply GlobalTheory.BI.character_eq_ind_of_imprimitive <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_character_quotient_of_injective_intertwining : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  first | exact @GlobalTheory.BI.exists_isChar_eq_add_of_injective | exact GlobalTheory.BI.exists_isChar_eq_add_of_injective | (intros; apply GlobalTheory.BI.exists_isChar_eq_add_of_injective <;> assumption)
end

section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.mem_virtualCharacters_iff_sub_characters : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L), f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  first | exact @GlobalTheory.BI.mem_virt_iff_sub | exact GlobalTheory.BI.mem_virt_iff_sub | (intros; apply GlobalTheory.BI.mem_virt_iff_sub <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * (Nat.card F : ℂ) ^ (a * (Module.finrank F V - a)) * glCard F a * glCard F (Module.finrank F V - a) = glCard F (Module.finrank F V) := by
  first | exact @GlobalTheory.CuspGL.card_subspaces_mul_glCard | exact GlobalTheory.CuspGL.card_subspaces_mul_glCard | (intros; apply GlobalTheory.CuspGL.card_subspaces_mul_glCard <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), (∀ j : ℕ, s ((X - C 1) ^ j) = j) → 0 < Module.finrank F V → psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.psi_one | exact GlobalTheory.CuspGL.psi_one | (intros; apply GlobalTheory.CuspGL.psi_one <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_psi_le (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V)
    (hg : ∀ x ∈ A, g x ∈ A) :
    ∑ᶠ W : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2.2)
      = s (LinearMap.charpoly (g.restrict hg)) := by
  rw [GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F A s (g.restrict hg)]
  let e : {W : Submodule F V // W ≤ A ∧ ∀ x ∈ W, g x ∈ W} ≃
      {W' : Submodule F A // ∀ x ∈ W', g.restrict hg x ∈ W'} :=
    { toFun := fun W => ⟨W.1.comap A.subtype, fun x hx => by
        simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply] at hx ⊢
        exact W.2.2 _ hx⟩
      invFun := fun W' => ⟨W'.1.map A.subtype, Submodule.map_subtype_le _ _, fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
        exact Submodule.mem_map.2 ⟨_, W'.2 y hy, rfl⟩⟩
      left_inv := fun W => Subtype.ext (by
        change (W.1.comap A.subtype).map A.subtype = W.1
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.2 W.2.1)
      right_inv := fun W' => Subtype.ext (Submodule.comap_map_eq_of_injective A.injective_subtype _) }
  rw [← finsum_comp_equiv e]
  congr 1
  funext W
  have hc : (Submodule.comapSubtypeEquivOfLe W.2.1).conj
      ((g.restrict hg).restrict (e W).2) = g.restrict W.2.2 := by
    ext x
    simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe]
  rw [← hc, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]
  rfl

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution : ∀ (F : Type) [Field F] (q : ℕ), 2 ≤ q → ∀ (s m : F[X] → ℂ), IsAdditive s → m 1 = 1 → (∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P) → ∀ P : F[X], P.Monic → s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by
  first | exact @GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv | exact GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv | (intros; apply GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ x : {x : Module.End F V × Submodule F V // x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}, psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) = (Nat.card (nilRad A) : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
  first | exact @GlobalTheory.CuspGL.finsum_psi_transversal | exact GlobalTheory.CuspGL.finsum_psi_transversal | (intros; apply GlobalTheory.CuspGL.finsum_psi_transversal <;> assumption)
end
