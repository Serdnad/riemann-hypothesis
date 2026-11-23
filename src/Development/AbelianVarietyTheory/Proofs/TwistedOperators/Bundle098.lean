module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.PairingTensor

open TensorProduct

variable {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

noncomputable def contrR (l : B →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A l

noncomputable def contrL (l : A →ₗ[ℂ] ℂ) : TensorProduct ℂ A B →ₗ[ℂ] B :=
  (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B l

@[simp] theorem contrR_tmul (l : B →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrR l (a ⊗ₜ[ℂ] b) = l b • a := by
  simp [contrR]

@[simp] theorem contrL_tmul (l : A →ₗ[ℂ] ℂ) (a : A) (b : B) :
    contrL l (a ⊗ₜ[ℂ] b) = l a • b := by
  simp [contrL]

theorem apply_contrR (l : A →ₗ[ℂ] ℂ) (m : B →ₗ[ℂ] ℂ) (z : TensorProduct ℂ A B) :
    l (contrR m z) = m (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem contrR_map (m : B →ₗ[ℂ] ℂ) (a : Module.End ℂ A) (z : TensorProduct ℂ A B) :
    contrR m (TensorProduct.map a LinearMap.id z) = a (contrR m z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

theorem contrL_map (l : A →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : TensorProduct ℂ A B) :
    contrL l (TensorProduct.map LinearMap.id b z) = b (contrL l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

theorem eq_zero_of_contrR {ι : Type} (m : ι → B →ₗ[ℂ] ℂ) (hm : ∀ b, (∀ y, m y b = 0) → b = 0)
    (z : TensorProduct ℂ A B) (hz : ∀ y, contrR (m y) z = 0) : z = 0 := by
  classical
  let bA := Module.Basis.ofVectorSpace ℂ A
  have key : ∀ (w : TensorProduct ℂ A B) i,
      TensorProduct.equivFinsuppOfBasisLeft bA w i = contrL (bA.coord i) w := by
    intro w i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft bA).injective
  ext i
  rw [key, map_zero, Finsupp.zero_apply]
  apply hm
  intro y
  rw [← apply_contrR, hz, map_zero]

theorem inner_separates {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (i : A →ₗ[ℂ] H) (hi : Function.Injective i) (a : A) (h : ∀ x, inner ℂ x (i a) = 0) :
    a = 0 := by
  apply hi
  rw [map_zero]
  exact inner_self_eq_zero.mp (h (i a))

theorem exists_linearMap_tensor :
    ∀ (V A B H₁ H₂ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (i₁ : A →ₗ[ℂ] H₁) (i₂ : B →ₗ[ℂ] H₂), Function.Injective i₁ → Function.Injective i₂ → ∀ (φ : H₂ → V →ₗ[ℂ] A) (ψ : H₁ → V →ₗ[ℂ] B), (∀ x y P, inner ℂ x (i₁ (φ y P)) = inner ℂ y (i₂ (ψ x P))) → (∀ P, ∃ E : Submodule ℂ A, FiniteDimensional ℂ E ∧ ∀ y, φ y P ∈ E) → ∃ f : V →ₗ[ℂ] TensorProduct ℂ A B, (∀ P, f P = 0 → ∀ y, φ y P = 0) ∧ (∀ (c : Module.End ℂ V) (a : Module.End ℂ A), (∀ y P, φ y (c P) = a (φ y P)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f) ∧ (∀ (c : Module.End ℂ V) (b : Module.End ℂ B), (∀ x P, ψ x (c P) = b (ψ x P)) → f ∘ₗ c = TensorProduct.map LinearMap.id b ∘ₗ f) := by
  intro V A B H₁ H₂ _ _ _ _ _ _ _ _ _ _ i₁ i₂ h₁ h₂ φ ψ hφψ hE
  let m : H₂ → B →ₗ[ℂ] ℂ := fun y => (innerₛₗ ℂ y) ∘ₗ i₂
  let l : H₁ → A →ₗ[ℂ] ℂ := fun x => (innerₛₗ ℂ x) ∘ₗ i₁
  have hm : ∀ y b, m y b = inner ℂ y (i₂ b) := fun _ _ => rfl
  have hl : ∀ x a, l x a = inner ℂ x (i₁ a) := fun _ _ => rfl
  have sepm : ∀ b, (∀ y, m y b = 0) → b = 0 := fun b h => inner_separates i₂ h₂ b h
  have sepl : ∀ a, (∀ x, l x a = 0) → a = 0 := fun a h => inner_separates i₁ h₁ a h
  have sepR : ∀ z w : TensorProduct ℂ A B, (∀ y, contrR (m y) z = contrR (m y) w) → z = w := by
    intro z w h
    rw [← sub_eq_zero]
    exact eq_zero_of_contrR m sepm _ (fun y => by rw [map_sub, h, sub_self])
  have sepL : ∀ z w : TensorProduct ℂ A B, (∀ x, contrL (l x) z = contrL (l x) w) → z = w := by
    intro z w h
    apply sepR
    intro y
    rw [← sub_eq_zero]
    apply sepl
    intro x
    rw [map_sub, apply_contrR, apply_contrR, h, sub_self]
  have ex : ∀ P, ∃ z : TensorProduct ℂ A B, ∀ y, contrR (m y) z = φ y P := by
    intro P
    obtain ⟨E, hfin, hmem⟩ := hE P
    let e := stdOrthonormalBasis ℂ (E.map i₁)
    have ha : ∀ j, ∃ a : A, i₁ a = (e j : H₁) := fun j => by
      obtain ⟨a, -, ha⟩ := (e j).2
      exact ⟨a, ha⟩
    choose a ha using ha
    refine ⟨∑ j, a j ⊗ₜ[ℂ] ψ (e j) P, fun y => ?_⟩
    apply h₁
    have := congrArg (fun v : E.map i₁ => (v : H₁))
      (e.sum_repr' ⟨i₁ (φ y P), Submodule.mem_map_of_mem (hmem y)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this

    rw [← this, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [contrR_tmul, map_smul, ha, hm, ← hφψ]
  choose g hg using ex
  let f : V →ₗ[ℂ] TensorProduct ℂ A B :=
    { toFun := g
      map_add' := fun P Q => sepR _ _ fun y => by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]
      map_smul' := fun s P => sepR _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply] }
  have hf : ∀ P y, contrR (m y) (f P) = φ y P := hg
  have hf' : ∀ P x, contrL (l x) (f P) = ψ x P := by
    intro P x
    rw [← sub_eq_zero]
    apply sepm
    intro y
    rw [map_sub, ← apply_contrR, hf, hl, hm, hφψ, sub_self]
  refine ⟨f, fun P hP y => by rw [← hf, hP, map_zero], fun c a h => ?_, fun c b h => ?_⟩
  · ext P
    refine sepR _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrR_map, hf, hf, h]
  · ext P
    refine sepL _ _ fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, contrL_map, hf', hf', h]

end GlobalTheory.PairingTensor
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FactorialJet

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0) (n : ℕ) :
    ∀ k t, t0 ≤ t →
      ‖g k t‖ ≤ C * ρ ^ (k + n) * ((k + n).factorial : ℝ) * ((t - t0) ^ n / (n.factorial : ℝ)) := by
  induction n with
  | zero => intro k t _; simpa using hb k t
  | succ n ih =>
    intro k t ht
    set A : ℝ := C * ρ ^ (k + (n + 1)) * ((k + (n + 1)).factorial : ℝ) with hA
    have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => A * ((s - t0) ^ (n + 1) / ((n + 1).factorial : ℝ)))
        (A * ((x - t0) ^ n / (n.factorial : ℝ))) x := by
      intro x
      have h1 : HasDerivAt (fun s : ℝ => (s - t0) ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * (x - t0) ^ n * 1) x := by
        exact ((hasDerivAt_id x).sub_const t0).pow (n + 1)
      have h2 := (h1.div_const ((n + 1).factorial : ℝ)).const_mul A
      refine h2.congr_deriv ?_
      congr 1
      rw [Nat.factorial_succ]
      have : (n.factorial : ℝ) ≠ 0 := by positivity
      have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast at *
      field_simp
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g k) (f' := g (k + 1))
      (a := t0) (b := t) (fun x _ => (hd k x).continuousAt.continuousWithinAt)
      (fun x _ => (hd k x).hasDerivWithinAt) (by simp [h0 k]) hB
      (fun x hx => by
        have h := ih (k + 1) x hx.1
        have e : k + 1 + n = k + (n + 1) := by ring
        rwa [e] at h) (x := t) ⟨ht, le_rfl⟩
    exact this

theorem eq_zero_near_right (g : ℕ → ℝ → E) (C ρ t0 : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k t0 = 0)
    (k : ℕ) (t : ℝ) (ht : t0 ≤ t) (ht' : ρ * (t - t0) < 1) : g k t = 0 := by
  have hr : ‖ρ * (t - t0)‖ < 1 := by
    rw [Real.norm_of_nonneg (mul_nonneg hρ.le (sub_nonneg.2 ht))]; exact ht'
  have hs := (summable_choose_mul_geometric_of_norm_lt_one k hr).tendsto_atTop_zero
  have hs2 := hs.const_mul (C * ρ ^ k * (k.factorial : ℝ))
  rw [mul_zero] at hs2
  have hle : ‖g k t‖ ≤ 0 := by
    refine ge_of_tendsto' hs2 fun n => ?_
    have h := norm_le_right g C ρ t0 hd hb h0 n k t ht
    refine h.trans (le_of_eq ?_)
    have e : ((k + n).factorial : ℝ) = ((n + k).choose k : ℝ) * n.factorial * k.factorial := by
      rw [add_comm k n]; exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial n k).symm
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [e, mul_pow, pow_add]
    field_simp
  exact norm_le_zero_iff.1 hle

theorem eq_zero_right (g : ℕ → ℝ → E) (C ρ : ℝ) (hρ : 0 < ρ)
    (hd : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t)
    (hb : ∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) (h0 : ∀ k, g k 0 = 0)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) : g k t = 0 := by
  have key : ∀ m : ℕ, ∀ k (t : ℝ), 0 ≤ t → 2 * ρ * t ≤ m → g k t = 0 := by
    intro m
    induction m with
    | zero =>
      intro k t ht h
      have : t = 0 := by
        have : t ≤ 0 := by
          by_contra hc
          push_neg at hc
          have := mul_pos hρ hc
          simp at h
          nlinarith
        linarith
      rw [this, h0]
    | succ m ih =>
      intro k t ht h
      by_cases hm : 2 * ρ * t ≤ m
      · exact ih k t ht hm
      · push_neg at hm
        have e : 2 * ρ * ((m : ℝ) / (2 * ρ)) = m := by field_simp
        have h1 : (m : ℝ) / (2 * ρ) ≤ t := by
          rw [div_le_iff₀ (by positivity)]; linarith
        refine eq_zero_near_right g C ρ ((m : ℝ) / (2 * ρ)) hρ hd hb
          (fun j => ih j _ (by positivity) e.le) k t h1 ?_
        push_cast at h
        linarith
  exact key ⌈2 * ρ * t⌉₊ k t ht (Nat.le_ceil _)

theorem eq_zero_of_factorial_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → ℝ → E) (C ρ : ℝ), 0 ≤ C → 0 < ρ → (∀ k t, HasDerivAt (g k) (g (k + 1) t) t) → (∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → (∀ k, g k 0 = 0) → ∀ k t, g k t = 0 := by
  intro E _ _ g C ρ _ hρ hd hb h0 k t
  rcases le_total 0 t with ht | ht
  · exact eq_zero_right g C ρ hρ hd hb h0 k t ht
  · have h := eq_zero_right (fun j s => ((-1 : ℝ) ^ j) • g j (-s)) C ρ hρ
      (fun j s => by
        have h1 := ((hd j (-s)).scomp s (hasDerivAt_neg s)).const_smul ((-1 : ℝ) ^ j)
        refine h1.congr_deriv ?_
        rw [smul_smul, pow_succ])
      (fun j s => by simpa [norm_smul] using hb j (-s))
      (fun j => by simp [h0 j]) k (-t) (by linarith)
    simpa using h

end GlobalTheory.FactorialJet
end
