module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle502
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KerTensor

theorem exists_factor {O σ A M : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module O M]
    (ev : MvPowerSeries σ O →ₐ[O] A) (hs : Function.Surjective ev)
    (ℓ : MvPowerSeries σ O →ₗ[O] M) (h : ∀ f, ev f = 0 → ℓ f = 0) :
    ∃ l : A →ₗ[O] M, ∀ f, l (ev f) = ℓ f := by
  have hle : LinearMap.ker ev.toLinearMap ≤ LinearMap.ker ℓ := fun f hf => h f hf
  have hs' : Function.Surjective ev.toLinearMap := hs
  refine ⟨(LinearMap.ker ev.toLinearMap).liftQ ℓ hle ∘ₗ
    (ev.toLinearMap.quotKerEquivOfSurjective hs').symm.toLinearMap, fun f => ?_⟩
  have : (ev.toLinearMap.quotKerEquivOfSurjective hs').symm (ev f) = Submodule.Quotient.mk f := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]; rfl
  simp [this]

theorem eval_coe {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (P : MvPolynomial σ O) :
    ev (P : MvPowerSeries σ O) = MvPolynomial.aeval x P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.coe_C, MvPolynomial.aeval_C, ← ev.commutes a]
    rfl
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p i hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, hx,
      MvPolynomial.aeval_X]

theorem eval_monomial {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype σ]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (γ : σ →₀ ℕ) (c : O) :
    ev ((MvPolynomial.monomial γ c : MvPolynomial σ O) : MvPowerSeries σ O) =
      c • ∏ i, x i ^ γ i := by
  rw [eval_coe ev x hx, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Algebra.smul_def]

theorem le_degree {σ : Type} [Fintype σ] (γ : σ →₀ ℕ) (k : σ) : γ k ≤ γ.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (f := fun i => γ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem degree_sum {σ τ : Type} [Fintype σ] [Fintype τ] (γ : σ ⊕ τ →₀ ℕ) :
    γ.degree = (Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) : σ →₀ ℕ).degree +
      (Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) : τ →₀ ℕ).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.coe_equivFunOnFinite_symm]

end GlobalTheory.KerTensor

namespace GlobalTheory.KerTensor

theorem ker_tensor : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B) (m N : ℕ), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → (∀ f, evA f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, evB f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ f, E f = 0 → ∀ α : σ ⊕ τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p O A B σ τ _ _ _ _ _ _ _ x y evA evB E m N hA hB hE sA sB kA kB f hf α hα
  classical
  set I : Ideal O := Ideal.span {(p : O) ^ m} with hI
  have fact : ∀ {ρ R : Type} [CommRing R] [Algebra O R] (ev : MvPowerSeries ρ O →ₐ[O] R),
      Function.Surjective ev → (∀ f, ev f = 0 → ∀ α : ρ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
      ∀ β : ρ →₀ ℕ, β.degree < N → ∃ l : R →ₗ[O] O ⧸ I, ∀ g, l (ev g) = Ideal.Quotient.mk I (coeff β g) := by
    intro ρ R _ _ ev hs hk β hβ
    obtain ⟨l, hl⟩ := exists_factor ev hs ((Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ coeff β) (fun g hg => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hI]
      exact Ideal.mem_span_singleton.2 (hk g hg β hβ))
    exact ⟨l, fun g => by rw [hl]; rfl⟩
  have hdeg := degree_sum α
  set α₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => α (Sum.inl i) with hα₁
  set α₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => α (Sum.inr j) with hα₂
  obtain ⟨l1, hl1⟩ := fact evA sA kA α₁ (by omega)
  obtain ⟨l2, hl2⟩ := fact evB sB kB α₂ (by omega)
  let Λ : A ⊗[O] B →ₗ[O] O ⧸ I := TensorProduct.lift ((LinearMap.mul O (O ⧸ I)).compl₁₂ l1 l2)
  have hΛ : ∀ a b, Λ (a ⊗ₜ b) = l1 a * l2 b := fun a b => by simp [Λ]

  have hmono : ∀ (γ : σ ⊕ τ →₀ ℕ) (c : O),
      Λ (E ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) =
        Ideal.Quotient.mk I (coeff α ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) := by
    intro γ c
    set γ₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) with hγ₁
    set γ₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) with hγ₂
    have e1 := eval_monomial evA x hA.1 γ₁ 1
    have e2 := eval_monomial evB y hB.1 γ₂ 1
    have eE := eval_monomial E _ hE.1 γ c
    have split : (∏ k, (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) k ^ γ k) =
        (∏ i, x i ^ γ₁ i) ⊗ₜ[O] (∏ j, y j ^ γ₂ j) := by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hγ₁, hγ₂, Finsupp.coe_equivFunOnFinite_symm]
      have h1 : (∏ i, (x i ⊗ₜ[O] (1 : B)) ^ γ (Sum.inl i)) = (∏ i, x i ^ γ (Sum.inl i)) ⊗ₜ[O] (1 : B) := by
        rw [← Algebra.TensorProduct.includeLeft_apply (S := O), map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeLeft_apply]
      have h2 : (∏ j, ((1 : A) ⊗ₜ[O] y j) ^ γ (Sum.inr j)) = (1 : A) ⊗ₜ[O] (∏ j, y j ^ γ (Sum.inr j)) := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeRight_apply]
      rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [eE, split, map_smul, hΛ, ← one_smul O (∏ i, x i ^ γ₁ i), ← e1, ← one_smul O (∏ j, y j ^ γ₂ j),
      ← e2, hl1, hl2]
    simp only [MvPolynomial.coe_monomial, coeff_monomial]
    have hiff : α = γ ↔ α₁ = γ₁ ∧ α₂ = γ₂ := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        ext k
        cases k with
        | inl i => simpa [hα₁, hγ₁] using congrArg (fun g => g i) h1
        | inr j => simpa [hα₂, hγ₂] using congrArg (fun g => g j) h2
    by_cases h : α = γ
    · rw [if_pos h, if_pos (hiff.1 h).1, if_pos (hiff.1 h).2]
      simp [Algebra.smul_def]
    · rw [if_neg h]
      by_cases h1 : α₁ = γ₁
      · rw [if_neg (fun h2 => h (hiff.2 ⟨h1, h2⟩))]; simp
      · rw [if_neg h1]; simp
  have hpoly : ∀ P : MvPolynomial (σ ⊕ τ) O,
      Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = Ideal.Quotient.mk I (coeff α (P : MvPowerSeries (σ ⊕ τ) O)) := by
    intro P
    induction P using MvPolynomial.induction_on' with
    | monomial γ c => exact hmono γ c
    | add P Q hP hQ => rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), hP, hQ, map_add (f := _), map_add (f := _)]

  obtain ⟨N', hN'⟩ := hE.2 m
  set K := max N' N with hK
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => K) f with hP
  have hrest : ∀ γ : σ ⊕ τ →₀ ℕ, γ.degree < K → coeff γ (f - (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    intro γ hγ
    have hle : γ ≤ Finsupp.equivFunOnFinite.symm fun _ => K := by
      intro k
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact le_of_lt (lt_of_le_of_lt (le_degree γ k) hγ)
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨c, hc⟩ := hN' (f - (P : MvPowerSeries (σ ⊕ τ) O))
    (fun γ hγ => hrest γ (lt_of_lt_of_le hγ (le_max_left _ _)))
  have hzero : Λ (E (f - (P : MvPowerSeries (σ ⊕ τ) O))) = 0 := by
    rw [hc]
    have : (p : A ⊗[O] B) ^ m * c = ((p : O) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [this, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul]
  have hsplit : E f = E (P : MvPowerSeries (σ ⊕ τ) O) + E (f - (P : MvPowerSeries (σ ⊕ τ) O)) := by
    rw [← map_add (f := _), add_sub_cancel]
  have hPval : Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    have := congrArg Λ hsplit
    rw [hf, map_zero, map_add (f := _), hzero, add_zero] at this
    exact this.symm
  have hcoeff : coeff α f = coeff α (P : MvPowerSeries (σ ⊕ τ) O) := by
    have := hrest α (lt_of_lt_of_le hα (le_max_right _ _))
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hmk : Ideal.Quotient.mk I (coeff α f) = 0 := by rw [hcoeff, ← hpoly, hPval]
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)

end GlobalTheory.KerTensor
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SurjTens

variable {O σ ι : Type} [CommRing O]


open Classical in
def pushVars (j : σ → ι) (f : MvPowerSeries σ O) : MvPowerSeries ι O :=
  fun β => if h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β then coeff h.choose f else 0

theorem coeff_pushVars_mapDomain {j : σ → ι} (hj : Function.Injective j) (f : MvPowerSeries σ O)
    (α : σ →₀ ℕ) : coeff (Finsupp.mapDomain j α) (pushVars j f) = coeff α f := by
  have h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = Finsupp.mapDomain j α := ⟨α, rfl⟩
  rw [coeff_apply]
  unfold pushVars
  rw [dite_eq_left h, Finsupp.mapDomain_injective hj h.choose_spec]

theorem coeff_pushVars_of_not {j : σ → ι} (f : MvPowerSeries σ O) (β : ι →₀ ℕ)
    (h : ¬∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β) : coeff β (pushVars j f) = 0 := by
  rw [coeff_apply]
  unfold pushVars
  rw [dite_eq_right h]

theorem pushVars_add {j : σ → ι} (hj : Function.Injective j) (f g : MvPowerSeries σ O) :
    pushVars j (f + g) = pushVars j f + pushVars j g := by
  ext β
  by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
  · obtain ⟨α, rfl⟩ := h
    simp only [map_add (f := _), coeff_pushVars_mapDomain hj]
  · simp only [map_add (f := _), coeff_pushVars_of_not _ _ h, add_zero]

theorem pushVars_monomial {j : σ → ι} (hj : Function.Injective j) (α : σ →₀ ℕ) (c : O) :
    pushVars j (monomial α c) = monomial (Finsupp.mapDomain j α) c := by
  classical
  ext β
  by_cases h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = β
  · obtain ⟨α', rfl⟩ := h
    rw [coeff_pushVars_mapDomain hj, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff]
  · rw [coeff_pushVars_of_not _ _ h, coeff_monomial, if_neg]
    rintro rfl
    exact h ⟨α, rfl⟩

theorem pushVars_coe {j : σ → ι} (hj : Function.Injective j) (P : MvPolynomial σ O) :
    pushVars j (P : MvPowerSeries σ O) = ((MvPolynomial.rename j P : MvPolynomial ι O) : MvPowerSeries ι O) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [MvPolynomial.coe_monomial, MvPolynomial.rename_monomial, MvPolynomial.coe_monomial,
      pushVars_monomial hj]
  | add P Q hP hQ =>
    rw [MvPolynomial.coe_add, pushVars_add hj, hP, hQ, map_add (f := _), MvPolynomial.coe_add]

theorem eval_coe {R A κ : Type} [CommRing R] [CommRing A] [Algebra R A] (z : κ → A)
    (E : MvPowerSeries κ R →ₐ[R] A) (hE : ∀ i, E (X i) = z i) (P : MvPolynomial κ R) :
    E (P : MvPowerSeries κ R) = MvPolynomial.aeval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom R) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem exists_eval_pushVars (p : ℕ) {A C : Type} [CommRing A] [CommRing C] [Algebra O A] [Algebra O C]
    [Fintype σ] [IsHausdorff (Ideal.span {(p : C)}) C] (j : σ → ι) (hj : Function.Injective j)
    (x : σ → A) (z : ι → C) (φ : A →ₐ[O] C) (evA : MvPowerSeries σ O →ₐ[O] A)
    (E : MvPowerSeries ι O →ₐ[O] C) (hA : IsEval p x evA) (hE : IsEval p z E)
    (hz : ∀ i, z (j i) = φ (x i)) (f : MvPowerSeries σ O) :
    E (pushVars j f) = φ (evA f) := by
  classical
  have hpoly : ∀ P : MvPolynomial σ O, E (pushVars j (P : MvPowerSeries σ O)) = φ (evA P) := by
    intro P
    rw [pushVars_coe hj, eval_coe z E hE.1, eval_coe x evA hA.1, MvPolynomial.aeval_rename]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hzj : z ∘ j = fun i => φ (x i) := funext hz
    rw [hzj]
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : C)}) inferInstance _ fun m => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨N1, hN1⟩ := hE.2 m
  obtain ⟨N2, hN2⟩ := hA.2 m
  set N := max N1 N2
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  set P : MvPolynomial σ O := trunc' O n f
  set g : MvPowerSeries σ O := f - (P : MvPowerSeries σ O)
  have hg : ∀ α : σ →₀ ℕ, α.degree < N → coeff α g = 0 := by
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  have hgA : (p : A) ^ m ∣ evA g := hN2 g fun α hα => hg α (lt_of_lt_of_le hα (le_max_right _ _))
  have hgE : (p : C) ^ m ∣ E (pushVars j g) := by
    apply hN1
    intro β hβ
    by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
    · obtain ⟨α, rfl⟩ := h
      rw [coeff_pushVars_mapDomain hj]
      apply hg
      rw [Finsupp.degree_mapDomain] at hβ
      exact lt_of_lt_of_le hβ (le_max_left _ _)
    · exact coeff_pushVars_of_not _ _ h
  have hgφ : (p : C) ^ m ∣ φ (evA g) := by
    have := map_dvd φ hgA
    simpa only [map_pow, map_natCast] using this
  have hf : f = g + (P : MvPowerSeries σ O) := by simp [g]
  have key : E (pushVars j f) - φ (evA f) = E (pushVars j g) - φ (evA g) := by
    rw [hf, pushVars_add hj, map_add (f := _), map_add (f := _), map_add (f := _), hpoly P]
    ring
  rw [key]
  exact dvd_sub hgE hgφ

theorem surjective_eval_tmul : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  intro p O A B σ τ _ _ _ _ _ _ _ _ x y evA evB E hA hB hE sA sB
  have hl : ∀ a : A, a ⊗ₜ[O] (1 : B) ∈ E.range := by
    intro a
    obtain ⟨f, rfl⟩ := sA a
    refine ⟨pushVars Sum.inl f, ?_⟩
    have := exists_eval_pushVars p Sum.inl Sum.inl_injective x _ Algebra.TensorProduct.includeLeft
      evA E hA hE (fun i => by simp) f
    simpa using this
  have hr : ∀ b : B, (1 : A) ⊗ₜ[O] b ∈ E.range := by
    intro b
    obtain ⟨g, rfl⟩ := sB b
    refine ⟨pushVars Sum.inr g, ?_⟩
    have := exists_eval_pushVars p Sum.inr Sum.inr_injective y _ Algebra.TensorProduct.includeRight
      evB E hB hE (fun i => by simp) g
    simpa using this
  intro t
  have : t ∈ E.range := by
    induction t using TensorProduct.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | tmul a b =>
      have h := Subalgebra.mul_mem _ (hl a) (hr b)
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
    | add s t hs ht => exact Subalgebra.add_mem _ hs ht
  exact this

end GlobalTheory.SurjTens
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.LieAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zero_of_constantCoeff {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) f = 0 := by
  have ha : HasSubst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
  by_cases h : a = 0
  · subst h
    rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h
    have : (a.prod fun _ k => (0 : MvPowerSeries (Fin d) R) ^ k) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 (by simpa using hs))
        (zero_pow (by simpa using hs))
    rw [this, map_zero, smul_zero]

theorem constantCoeff_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem subst_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf0 : constantCoeff f = 0)
    (hf : cob1 μ f = 0) (n : ℕ) : subst (nmul μ n) f = (n : R) • f := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul]
    exact subst_zero_of_constantCoeff hf0
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    have hb := hasSubst_of_constantCoeff_zero hs
    have hm : nmul μ (n + 1) = fun i => subst (Sum.elim (nmul μ n) fun i => X i) (μ i) := by
      rw [nmul, Function.iterate_succ_apply', ← nmul]; rfl
    have hc : subst μ f = inL f + inR f := by
      rw [cob1, sub_sub, sub_eq_zero] at hf; exact hf
    have hl0 : ∀ i, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    have hr0 : ∀ i, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    rw [hm, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hb, hc,
      subst_add hb, inL, inR,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hl0) hb,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr0) hb]
    simp only [subst_X hb, Sum.elim_inl, Sum.elim_inr]
    rw [ih, subst_self, id, Nat.cast_succ, add_smul, one_smul]

theorem nmul_succ {S : Type} [CommRing S] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  rw [nmul, Function.iterate_succ_apply', ← nmul]

theorem up_nmul {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ n) = nmul (up Q μ) n := by
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    funext i
    rw [nmul_succ, nmul_succ, ← ih]
    simp only [up, op, at2]
    rw [map_subst (hasSubst_of_constantCoeff_zero hs)]
    congr 1
    funext j
    rcases j with j | j <;> simp [map_X, up]

end GlobalTheory.QLog.LieAdd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem Chart.isLie_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C),
    constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c f hf0 hf
  have hμ := c.isLaw.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    rw [up, constantCoeff_map, hμ, map_zero]
  refine (c.isLie_iff hv.hom_inj f 0).2 fun n => ⟨0, ?_, fun w φ _ => by simp⟩
  rw [map_zero, defect, LieAdd.up_nmul hμ, LieAdd.subst_nmul hμC hf0 hf, sub_self]

end GlobalTheory.QLog
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.coeffsInIdealOfPowerSeries_iff_image : ∀ (B Q σ : Type) [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) (f : MvPowerSeries σ Q), (In N f ↔ ∃ s : MvPowerSeries σ B, (∀ α, coeff α s ∈ N) ∧ map (algebraMap B Q) s = f) ∧ ∀ g : MvPowerSeries σ Q, In N f → In N g → ∀ a : B, In N (f + algebraMap B Q a • g) ∧ In N (f - g) := by
  first | exact @GlobalTheory.series_in_ideal_iff_image | exact GlobalTheory.series_in_ideal_iff_image | (intros; apply GlobalTheory.series_in_ideal_iff_image <;> assumption)
end

section

open GlobalTheory.QLog

theorem _root_.GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (d : ℕ) (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A), IsEval p x E → ∀ (n N : ℕ) (f : MvPowerSeries (Fin d) O), E f = 0 → ∃ P : MvPolynomial (Fin d) O, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) ∧ (∀ α : Fin d →₀ ℕ, α.degree < N → AddMonoidAlgebra.coeff P α = MvPowerSeries.coeff α f) ∧ MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) ^ N ⊔ Ideal.span {(p : A) ^ n} := by
  first | exact @GlobalTheory.trunc_dec | exact GlobalTheory.trunc_dec | (intros; apply GlobalTheory.trunc_dec <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  first | exact @GlobalTheory.isLaw_map_nmul | exact GlobalTheory.isLaw_map_nmul | (intros; apply GlobalTheory.isLaw_map_nmul <;> assumption)
end
