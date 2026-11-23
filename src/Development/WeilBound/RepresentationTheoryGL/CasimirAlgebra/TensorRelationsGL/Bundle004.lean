module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle002
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

def TensorGl : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (P : Type) [Fintype P] [DecidableEq P]
  (E : Fin n → Fin n → Module.End ℂ M), GlRel E → ∀ S : Finset P, GlRel (tE S E) ∧
    (∀ p ∈ S, ∀ a b, Commute (Om E p) (tE S E a b)) ∧
    (∀ σ : Equiv.Perm P, (∀ p, σ p ∈ S ↔ p ∈ S) → ∀ a b, Commute (pm σ) (tE S E a b)) ∧
    ∀ (σ : Equiv.Perm P) (p : P), pm σ * Om E p = (Om E (σ p) * pm σ : Module.End ℂ (TV n M P))

def JMComm : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ m : ℕ, (∀ i j : Fin m, Commute (xJ E i) (xJ E j)) ∧
    (∀ i j : Fin m, (i : ℕ) + 1 = j → xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j))) ∧
    ∀ (u : ℂ) (σ : Equiv.Perm (Fin m)), Commute (PiJ m E u) (pm σ)

def PiQdet : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ u : ℂ, PiJ n E u * alt Finset.univ = lift (qdet E u) * alt Finset.univ

def StepFormula : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (m : ℕ) (u : ℂ),
    PiJ m E u * qdet (tE (Finset.univ : Finset (Fin m)) E) u = lift (qdet E u) * PiJ m E (u + 1)

def Spectrum : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℂ) (s : ℂ), HasChar E l → (∀ k, ∃ r : ℕ, l k = s + r) → ∀ m : ℕ,
    (∀ k ≤ m, ∃ L : List ℕ, (L.map fun r : ℕ => (∑ j ∈ Finset.univ.filter fun j : Fin m => (j : ℕ) < k, xJ E j) -
      algebraMap ℂ _ ((k : ℂ) * s + r)).prod = 0) ∧
    ∀ j : Fin m, ∃ L : List ℕ, (L.map fun r : ℕ => xJ E j - algebraMap ℂ _ (s + r)).prod = 0

def Trans : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℤ), HasChar E (fun k => (l k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → IsWh E ℓ →
  ∀ (P : Type) [Fintype P] [DecidableEq P] (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n), IsTab col b →
    (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun _ : Unit => tE (Finset.univ : Finset P) E), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ u : ℂ,
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (Finset.univ : Finset P) E) u =
        (∏ k, (u + l k + ((Finset.univ.filter fun p => co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)

def TransAll : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (E : ι → Fin n → Fin n → Module.End ℂ M), (∀ τ, GlRel (E τ)) →
  (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) →
  ∀ (P : Type) [Fintype P] [DecidableEq P] (lab : P → ι) (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n),
    (∀ p q, col p = col q → lab p = lab q) → IsTab col b → (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)

def WallAlg : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E₁ E₂ : Fin n → Fin n → Module.End ℂ M),
  GlRel E₁ → GlRel E₂ → (∀ a b c d, Commute (E₁ a b) (E₂ c d)) → ∀ s₁ s₂ c : ℂ,
  HasChar E₁ (fun _ => s₁) → HasChar E₂ (fun _ => s₂) → ∀ (m : ℕ) (X : Submodule ℂ (TV n M (Fin m))), X ≠ ⊥ →
    (∀ σ, ∀ ξ ∈ X, pm σ ξ ∈ X) → (∀ j, ∀ ξ ∈ X, Om E₁ j ξ ∈ X) →
    (∀ a b, ∀ ξ ∈ X, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a b ξ = if a = b then c • ξ else 0) →
    (n : ℂ) * (s₁ + s₂) + n * (n - 1) + m = n * c ∧ (0 < m → n ≤ m ∧ ∃ ξ ∈ X, alt (firstG m n) ξ ≠ 0)

def TensorGK : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (P : Type) [Fintype P] [DecidableEq P] (lab : P → ι),
    IsGK bar κ (fun τ => tE (fib lab τ) (E τ)) (actT lab κ ρ) ∧
    ∀ σ : Equiv.Perm P, (∀ p, lab (σ p) = lab p) → ∀ γ, Commute (pm σ) (actT lab κ ρ γ)

def SphAll : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
  (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (s : ℂ) (φ : M →ₗ[ℂ] ℂ), φ ≠ 0 → (∀ τ (u : ℂ), φ ∘ₗ qdet (E τ) u = ((u + s) ^ n) • φ) →
    ∃ ξ : M, (∀ γ, ρ γ ξ = ξ) ∧ ∃ w ∈ envAlg E, φ (w ξ) ≠ 0

def Young : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [DecidableEq ι]
  (Q : Type) [Fintype Q] [DecidableEq Q] (N : ℕ) (tl : Fin N → ι) (C : Type) [DecidableEq C]
  (col : Q ⊕ (Fin N ⊕ Fin N) → C) (b : Q ⊕ (Fin N ⊕ Fin N) → Fin n), IsTab col b →
    (∀ p k, col (.inl p) ≠ col (.inr k)) → (∀ k k', col (.inr (.inl k)) ≠ col (.inr (.inr k'))) →
    (∀ k k', col (.inr (.inl k)) = col (.inr (.inl k')) ↔ tl k = tl k' ∧ b (.inr (.inr k)) = b (.inr (.inr k'))) →
    (∀ k k', col (.inr (.inr k)) = col (.inr (.inr k')) ↔ tl k = tl k' ∧ b (.inr (.inl k)) = b (.inr (.inl k'))) →
    ∀ ξ : TV n M (Q ⊕ (Fin N ⊕ Fin N)), altPair tl (alt (colG col) ξ) = 0 → cA col b ξ = 0

def KType : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
  (bar : ι → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
  (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M), IsKD bar κ → IsGK bar κ E ρ →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, Function.Injective (l τ)) → (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) →
  ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) → ∃ s : ℤ, KTypeData bar κ ρ l s

def CasBound : Prop := ∀ (n : ℕ) (Q : Type) [Fintype Q] [DecidableEq Q] (C : Type) [DecidableEq C] (col : Q → C)
  (b : Q → Fin n) (S : Finset Q), IsTab col b → (∀ p q, col p = col q → (p ∈ S ↔ q ∈ S)) →
  ∀ f : TV n ℂ Q, (∀ p q, col p = col q → p ≠ q → pm (Equiv.swap p q) f = -f) →
    (star f ⬝ᵥ (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a :
      Module.End ℂ (TV n ℂ Q)) f).re ≤
      (∑ i : Fin n, ((S.filter fun p => b p = i).card : ℝ) *
        (((S.filter fun p => b p = i).card : ℝ) + 2 * (i : ℕ) + 1 - n)) * (star f ⬝ᵥ f).re

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  (q : P → Prop) [DecidablePred q]

def merge (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) : P → Fin n :=
  fun p => if h : q p then J ⟨p, h⟩ else I ⟨p, h⟩

omit [Fintype P] [DecidableEq P] in
theorem merge_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) :
    merge q J I x.1 = J x := by simp [merge, x.2]

omit [Fintype P] [DecidableEq P] in
theorem merge_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) :
    merge q J I x.1 = I x := by simp [merge, x.2]

omit [Fintype P] in
theorem merge_upd_left (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // q p}) (c : Fin n) :
    merge q (Function.update J x c) I = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]
  · have hp : p ≠ x.1 := fun e => h (e ▸ x.2)
    simp [merge, h, hp]

omit [Fintype P] in
theorem merge_upd_right (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) (x : {p // ¬ q p}) (c : Fin n) :
    merge q J (Function.update I x c) = Function.update (merge q J I) x.1 c := by
  funext p
  by_cases h : q p
  · have hp : p ≠ x.1 := fun e => x.2 (e ▸ h)
    simp [merge, h, hp]
  · by_cases hp : p = x.1
    · subst hp
      simp [merge, h]
    · have hx : (⟨p, h⟩ : {p // ¬ q p}) ≠ x := fun e => hp (congrArg Subtype.val e)
      simp [merge, h, hp, Function.update_of_ne hx]

def spl : TV n M P ≃ₗ[ℂ] TV n (TV n M {p // ¬ q p}) {p // q p} where
  toFun F J I := F (merge q J I)
  invFun G K := G (fun x => K x.1) (fun x => K x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by
    funext K
    show F (merge q _ _) = F K
    congr 1
    funext p
    by_cases h : q p <;> simp [merge, h]
  right_inv G := by
    funext J I
    show G (fun x => merge q J I x.1) (fun x => merge q J I x.1) = G J I
    congr 1 <;> funext x
    · exact merge_left q J I x
    · exact merge_right q J I x

omit [Fintype P] [DecidableEq P] in
theorem spl_apply (F : TV n M P) (J : {p // q p} → Fin n) (I : {p // ¬ q p} → Fin n) :
    spl q F J I = F (merge q J I) := rfl

omit [Fintype P] in
theorem spl_tE (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : TV n M P) :
    spl q (tE S F a b f) =
      tE (S.subtype q) (fun a b => tE (S.subtype fun p => ¬ q p) F a b) a b (spl q f) := by
  funext J I
  simp only [spl_apply, tE, lift, eAt, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.add_apply]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not S q, add_comm]
  congr 1
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : I x = a
    · simp [h, merge_right, spl_apply, merge_upd_right]
    · simp [h, merge_right]
  · rw [← Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : J x = a
    · simp [h, merge_left, spl_apply, merge_upd_left]
    · simp [h, merge_left]

omit [DecidableEq P] in
theorem card_sub (r : P → Prop) [DecidablePred r] :
    (Finset.univ.filter fun x : {p // q p} => r x.1).card = (Finset.univ.filter fun p => q p ∧ r p).card := by
  rw [← Finset.card_map (Function.Embedding.subtype q)]
  congr 1
  ext p
  simp [and_comm]

private theorem subtypePerm_subtypeCongr_eq {q : P → Prop} [DecidablePred q] (σ : Equiv.Perm P)
    (h0 : ∀ x, q (σ x) ↔ q x) (h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x) :
    (σ.subtypePerm h0).subtypeCongr (σ.subtypePerm (p := fun x => ¬ q x) h1) = σ := by
  ext x
  by_cases hx : q x
  · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
    rfl
  · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
    rfl

theorem cA_split {C : Type} [DecidableEq C] (col : P → C) (hq : ∀ p p', col p = col p' → (q p ↔ q p'))
    (b : P → Fin n) (F : TV n M P) :
    cA col b F = cA (fun x : {p // ¬ q p} => col x.1) (fun x => b x.1)
      (cA (fun x : {p // q p} => col x.1) (fun x => b x.1) (spl q F)) := by

  simp only [cA, alt, colG, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, map_sum, map_smul, pm, LinearMap.pi_apply]
  simp_rw [Finset.smul_sum, smul_smul, spl_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun τ _ => τ.1.subtypeCongr τ.2) ?_ ?_ ?_ ?_
  · rintro ⟨σ0, σ1⟩ hτ
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    intro x
    by_cases hx : q x
    · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      exact hτ.1 ⟨x, hx⟩
    · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hx]
      exact hτ.2 ⟨x, hx⟩
  · rintro ⟨σ0, σ1⟩ _ ⟨σ0', σ1'⟩ _ he
    simp only at he
    have e0 : σ0 = σ0' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.left_apply _ _ x.2] at this
      exact this
    have e1 : σ1 = σ1' := by
      ext x
      have := congrArg (fun σ : Equiv.Perm P => σ x.1) he
      simp only [Equiv.Perm.subtypeCongr.right_apply _ _ x.2] at this
      exact this
    rw [e0, e1]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have h0 : ∀ x, q (σ x) ↔ q x := fun x => hq _ _ (hσ x)
    have h1 : ∀ x, ¬ q (σ x) ↔ ¬ q x := fun x => not_congr (h0 x)
    refine ⟨(σ.subtypePerm h0, σ.subtypePerm (p := fun x => ¬ q x) h1), ?_, subtypePerm_subtypeCongr_eq σ h0 h1⟩
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun x => hσ x.1, fun x => hσ x.1⟩
  · rintro ⟨σ0, σ1⟩ _
    simp only
    rw [Equiv.Perm.sign_subtypeCongr]
    congr 1
    · push_cast
      ring
    · congr 1
      funext x
      by_cases hx : q x
      · simp [merge, hx, Equiv.Perm.subtypeCongr.left_apply _ _ hx]
      · simp [merge, hx, Equiv.Perm.subtypeCongr.right_apply _ _ hx]

end PositivityTheory.Rg.Cz.TA

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]

def mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Γ → ℂ :=
  fun k => (∏ τ, (κ τ k).det ^ c τ) * ∏ p, κ (lab p) k (I p) (K p)

def Mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (H : Set ι) : Set (Γ → ℂ) :=
  {g | ∃ (m : ℕ) (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n), (∀ p, lab p ∈ H) ∧ g = mono κ lab c I K}

theorem exists_half (bar : ι → ι) (h1 : ∀ τ, bar (bar τ) = τ) (h2 : ∀ τ, bar τ ≠ τ) :
    ∃ H : Set ι, ∀ τ, τ ∈ H ↔ bar τ ∉ H := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨{τ | e τ < e (bar τ)}, fun τ => ?_⟩
  simp only [Set.mem_setOf_eq, h1, not_lt]
  have hne : e τ ≠ e (bar τ) := fun h => h2 τ (e.injective h).symm
  constructor
  · intro h
    exact h.le
  · intro h
    exact lt_of_le_of_ne h hne

variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem det_ne (hK : IsKD bar κ) (τ : ι) (γ : Γ) : (κ τ γ).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (hK.unit τ γ)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem mono_cont (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Continuous (mono κ lab c I K) := by
  have hent : ∀ τ, Continuous fun k => κ τ k :=
    fun τ => continuous_pi fun i => continuous_pi fun j => hK.cont τ i j
  unfold mono
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun τ _ => ?_
    exact ((hent τ).matrix_det).zpow₀ (c τ) fun k => Or.inl (det_ne hK τ k)
  · exact continuous_finsetProd _ fun p _ => hK.cont (lab p) (I p) (K p)

theorem one_mem_Mono (H : Set ι) : (1 : Γ → ℂ) ∈ Mono κ H := by
  refine ⟨0, Fin.elim0, 0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
  funext k
  simp [mono]

theorem mul_mem_Mono (hK : IsKD bar κ) (H : Set ι) {g g' : Γ → ℂ} (hg : g ∈ Mono κ H) (hg' : g' ∈ Mono κ H) :
    g * g' ∈ Mono κ H := by
  obtain ⟨m1, l1, c1, I1, K1, hl1, rfl⟩ := hg
  obtain ⟨m2, l2, c2, I2, K2, hl2, rfl⟩ := hg'
  refine ⟨m1 + m2, Fin.append l1 l2, c1 + c2, Fin.append I1 I2, Fin.append K1 K2, ?_, ?_⟩
  · intro p
    refine Fin.addCases (fun i => ?_) (fun i => ?_) p
    · simpa [Fin.append_left] using hl1 i
    · simpa [Fin.append_right] using hl2 i
  · funext k
    simp only [mono, Pi.mul_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]
    rw [show (∏ τ, (κ τ k).det ^ (c1 τ + c2 τ)) =
        (∏ τ, (κ τ k).det ^ c1 τ) * ∏ τ, (κ τ k).det ^ c2 τ by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun τ _ => zpow_add₀ (det_ne hK τ k) _ _]
    ring

def monoAlg (hK : IsKD bar κ) (H : Set ι) : Subalgebra ℂ (Γ → ℂ) :=
  (Submodule.span ℂ (Mono κ H)).toSubalgebra (Submodule.subset_span (one_mem_Mono H)) (by
    intro x y hx hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Submodule.subset_span (mul_mem_Mono hK H ha hb))

theorem integrable_of_cont [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : MeasureTheory.Measure Γ)
    [MeasureTheory.IsFiniteMeasure μ] {f : Γ → ℂ} (hf : Continuous f) : MeasureTheory.Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem entry_mem (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i j : Fin n) :
    (fun k => κ τ k i j) ∈ Submodule.span ℂ (Mono κ H) := by
  classical
  change (fun k => κ τ k i j) ∈ monoAlg hK H
  have hent : ∀ σ ∈ H, ∀ a b : Fin n, (fun k => κ σ k a b) ∈ monoAlg hK H := by
    intro σ hσ a b
    apply Submodule.subset_span
    refine ⟨1, fun _ => σ, 0, fun _ => a, fun _ => b, fun _ => hσ, ?_⟩
    funext k
    simp [mono]
  by_cases hτ : τ ∈ H
  · exact hent τ hτ i j
  · have hσ : bar τ ∈ H := by
      by_contra h
      exact hτ ((hH τ).2 h)
    have hinv : ∀ z : ℤ, (fun k => (κ (bar τ) k).det ^ z) ∈ monoAlg hK H := by
      intro z
      apply Submodule.subset_span
      refine ⟨0, Fin.elim0, Pi.single (bar τ) z, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
      funext k
      symm
      simp only [mono, Fin.prod_univ_zero, mul_one]
      rw [Finset.prod_eq_single (bar τ)]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hadj : (fun k => (κ (bar τ) k).adjugate j i) ∈ monoAlg hK H := by
      have hfun : (fun k => (κ (bar τ) k).adjugate j i) = ∑ p : Equiv.Perm (Fin n),
          (Equiv.Perm.sign p : ℤ) • ∏ r, (fun k => ((κ (bar τ) k).updateRow i (Pi.single j 1)) (p r) r) := by
        funext k
        simp [Matrix.adjugate_apply, Matrix.det_apply, Finset.sum_apply, Finset.prod_apply, Units.smul_def]
      rw [hfun]
      refine Subalgebra.sum_mem _ fun p _ => zsmul_mem (Subalgebra.prod_mem _ fun r _ => ?_) _
      by_cases h : p r = i
      · simp only [h, Matrix.updateRow_self]
        exact Subalgebra.algebraMap_mem (monoAlg hK H) ((Pi.single j (1 : ℂ) : Fin n → ℂ) r)
      · simp only [Matrix.updateRow_ne h]
        exact hent _ hσ _ _
    have hkey : (fun k => κ τ k i j) =
        (fun k => (κ (bar τ) k).det ^ (-1 : ℤ)) * (fun k => (κ (bar τ) k).adjugate j i) := by
      funext k
      have hinvM : (κ (bar τ) k)⁻¹ = (κ (bar τ) k)ᴴ := Matrix.inv_eq_right_inv (hK.unit (bar τ) k)
      have e1 : κ τ k i j = star (κ (bar τ) k i j) := by
        have := hK.conj (bar τ) k i j
        rwa [hK.invol] at this
      have e2 : star (κ (bar τ) k i j) = ((κ (bar τ) k)ᴴ) j i := by
        simp [Matrix.conjTranspose_apply]
      rw [Pi.mul_apply, e1, e2, ← hinvM]
      simp [Matrix.inv_def, Ring.inverse_eq_inv', _root_.zpow_neg_one]
    rw [hkey]
    exact Subalgebra.mul_mem _ (hinv (-1)) hadj

end SWS

end PositivityTheory.Rg.Cz

end
end
