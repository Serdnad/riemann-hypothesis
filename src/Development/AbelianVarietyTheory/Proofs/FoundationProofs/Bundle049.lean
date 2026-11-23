module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle176
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle020
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

section

open Polynomial

set_option linter.deprecated false

namespace GlobalTheory.DeformZeros

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

lemma iter_eq (f : PowerSeries k) (l : ℕ) :
    (PowerSeries.derivativeFun)^[l] f = (PowerSeries.derivative (R := k))^[l] f := by
  induction l generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

lemma cc_subst (φ a : PowerSeries k) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ :=
  (GlobalTheory.T.powerSeries_taylor_subst_first_order k φ a 0 1 le_rfl ha).1

end GlobalTheory.DeformZeros

namespace GlobalTheory.DeformZeros

variable {k : Type} [Field k]

lemma dvd_step {m : ℕ} (hm : 1 ≤ m) (y g S S' : PowerSeries k) (y0 c A : k)
    (hy : PowerSeries.constantCoeff y = y0) (hS : PowerSeries.constantCoeff S = A)
    (hT : (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      S' - S - PowerSeries.X ^ m * PowerSeries.C c) :
    (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      (y + PowerSeries.X ^ m * g) * S' - y * S
        - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c) := by
  apply GlobalTheory.PicDiv.DeformZerosHasse.dvd_step <;> assumption

end GlobalTheory.DeformZeros

namespace GlobalTheory.DeformZeros

theorem deform : ∀ (k J I : Type) [Field k] [CharZero k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * (((PowerSeries.derivativeFun)^[l] (s i j)).subst (a i) : PowerSeries k) = 0 := by
  intro k J I _ _ _ _ N ξ s y₀ hN h0 hlow hN' hsurj

  have hA : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l] f)
      = (l.factorial : k) * PowerSeries.coeff l f := by
    intro f l; rw [iter_eq]; exact PowerSeries.constantCoeff_iterate_derivative f l
  have hB : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l] f)
      = ((2 : ℕ).ascFactorial l : k) * PowerSeries.coeff (1 + l) f := by
    intro f l; rw [iter_eq]; exact PowerSeries.coeff_iterate_derivative f l 1
  have hsur : Function.Surjective (lin N ξ s y₀) := by

    intro w
    have hfac : ∀ l : ℕ, (l.factorial : k) ≠ 0 := fun l => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
    obtain ⟨hv, hv0, hvl⟩ := hsurj (w none)
      (fun i l => if hl : l < N then w (some (i, ⟨l, hl⟩)) / (l.factorial : k) else 0)
    have hN1 : N - 1 < N := by omega
    have hS : ∀ i, ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[N - 1] (s i j)) ≠ 0 := by
      intro i
      simp only [hB]
      have e1 : 1 + (N - 1) = N := by omega
      rw [e1]
      have hasc : ((Nat.ascFactorial 2 (N - 1) : ℕ) : k) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ascFactorial_pos 1 (N - 1)).ne'
      calc ∑ j, y₀ j * (((Nat.ascFactorial 2 (N - 1) : ℕ) : k) * PowerSeries.coeff N (s i j))
          = ((Nat.ascFactorial 2 (N - 1) : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff N (s i j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≠ 0 := mul_ne_zero hasc (hN' i)
    refine ⟨Sum.elim hv (fun i => (w (some (i, ⟨N - 1, hN1⟩)) - ∑ j, hv j *
        PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[N - 1] (s i j))) /
        ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[N - 1] (s i j))), ?_⟩
    funext e
    rcases e with _ | ⟨i, l⟩
    · simpa [lin, linFun] using hv0
    · simp only [lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
      rcases Nat.lt_or_ge (l.1 + 1) N with hl | hl
      · have h1 : ∑ j, hv j * PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
            = w (some (i, l)) := by
          simp only [hA]
          have := hvl i l.1 hl
          rw [dite_eq_left l.2] at this
          calc ∑ j, hv j * ((l.1.factorial : k) * PowerSeries.coeff l.1 (s i j))
              = (l.1.factorial : k) * ∑ j, hv j * PowerSeries.coeff l.1 (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = w (some (i, l)) := by rw [this, mul_div_assoc', mul_div_cancel_left₀ _ (hfac _)]
        have h2 : ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)) = 0 := by
          simp only [hB]
          calc ∑ j, y₀ j * (((Nat.ascFactorial 2 l.1 : ℕ) : k) * PowerSeries.coeff (1 + l.1) (s i j))
              = ((Nat.ascFactorial 2 l.1 : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff (1 + l.1) (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hlow i (1 + l.1) (by omega), mul_zero]
        rw [h1, h2, mul_zero, add_zero]
      · have hl' : l = ⟨N - 1, hN1⟩ := Fin.ext (by simp; omega)
        subst hl'
        rw [div_mul_cancel₀ _ (hS i)]
        ring
  have hbase : ∀ e, PowerSeries.constantCoeff
      (sys N ξ s (fun i => PowerSeries.C (Sum.elim y₀ 0 i)) e) = 0 := by

    intro e
    rcases e with _ | ⟨i, l⟩

    · simp [sys, map_sum, h0]
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [sys, map_sum, map_mul, PowerSeries.constantCoeff_C, Sum.elim_inl, Sum.elim_inr]
      have h' : ∀ j, PowerSeries.constantCoeff (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst
          (PowerSeries.C ((0 : I → k) i)) : PowerSeries k) = (l.1.factorial : k) * PowerSeries.coeff l.1 (s i j) := by
        intro j; rw [cc_subst _ _ (by simp), hA]
      simp only [h']
      calc ∑ j, y₀ j * ((l.1.factorial : k) * PowerSeries.coeff l.1 (s i j))
          = (l.1.factorial : k) * ∑ j, y₀ j * PowerSeries.coeff l.1 (s i j) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hlow i l.1 l.2, mul_zero]
  have htay : ∀ (x h : J ⊕ I → PowerSeries k) (m : ℕ), 1 ≤ m →
      (∀ i, PowerSeries.constantCoeff (x i) = Sum.elim y₀ 0 i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ sys N ξ s (fun i => x i + PowerSeries.X ^ m * h i) e
        - sys N ξ s x e - PowerSeries.X ^ m *
          PowerSeries.C (lin N ξ s y₀ (fun i => PowerSeries.constantCoeff (h i)) e) := by

    intro x h m hm hx0 e
    rcases e with _ | ⟨i, l⟩
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) * ξ j - ∑ j, x (Sum.inl j) * ξ j
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))
          = PowerSeries.X ^ m * (∑ j, h (Sum.inl j) * ξ j - PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))) := by
        rw [mul_sub, Finset.mul_sum]; simp only [add_mul, Finset.sum_add_distrib, mul_assoc]; ring
      rw [heq, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]

      simp [map_sum]
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk]
      set a := x (Sum.inr i)
      set b := h (Sum.inr i)
      have ha : PowerSeries.constantCoeff a = 0 := by simpa using hx0 (Sum.inr i)
      have key : ∀ j, (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
          (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)))) := by
        intro j
        have T := GlobalTheory.T.powerSeries_taylor_subst_first_order k ((PowerSeries.derivativeFun)^[l.1] (s i j)) a b m hm ha
        exact dvd_step hm _ _ _ _ _ _ _ (by simpa using hx0 (Sum.inl j)) T.1 T.2
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - ∑ j, x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + PowerSeries.constantCoeff b * ∑ j, y₀ j * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j)))
          = ∑ j, ((x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * (((PowerSeries.derivativeFun)^[l.1] (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff ((PowerSeries.derivativeFun)^[l.1] (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 ((PowerSeries.derivativeFun)^[l.1] (s i j))))) := by

        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum,
        Finset.sum_add_distrib, Finset.mul_sum (a := PowerSeries.constantCoeff b)]
        congr 4
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact Finset.dvd_sum fun j _ => key j
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.newton_powerSeries_surjective_linearization_solution k (J ⊕ I) (Option (I × Fin N)) (sys N ξ s) (Sum.elim y₀ 0)
    (lin N ξ s y₀) hsur hbase htay
  refine ⟨fun j => x (Sum.inl j), fun i => x (Sum.inr i), fun j => by simpa using hx0 (Sum.inl j),
    fun i => by simpa using hx0 (Sum.inr i), hx none, ?_⟩
  intro i l hl
  exact hx (some (i, ⟨l, hl⟩))

end GlobalTheory.DeformZeros
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem conj_mem_lev {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ lev N l) : σ * γ * σ⁻¹ ∈ lev N l := by
  apply GlobalTheory.Hk.dia_conj_mem <;> assumption

end GlobalTheory.Hk

namespace GlobalTheory.Hk


open scoped Pointwise in
theorem dia_cuspForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  have hle : ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ) •
      (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤ (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv] at hy
    obtain ⟨γ, hγ, hγe⟩ := hy
    refine ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, ?_⟩
    change Matrix.SpecialLinearGroup.mapGL ℝ (σ * γ * σ⁻¹) = y
    rw [map_mul, map_mul, map_inv, hγe]
    group
  refine ⟨{ toFun := dia k σ f
            slash_action_eq' := fun A hA => ?_
            holo' := ?_
            zero_at_cusps' := fun {x} hx => ?_ }, rfl⟩
  · obtain ⟨γ, hγ, rfl⟩ := hA
    have h : (f : ℍ → ℂ) ∣[k] (σ * γ * σ⁻¹) = f :=
      f.slash_action_eq' _ ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, rfl⟩
    show ((f : ℍ → ℂ) ∣[k] σ) ∣[k] γ = (f : ℍ → ℂ) ∣[k] σ
    rw [← SlashAction.slash_mul]
    have e : σ * γ = (σ * γ * σ⁻¹) * σ := by group
    rw [e, SlashAction.slash_mul, h]
  · exact MDifferentiable.slash f.holo' _ _
  · have h3 : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ σ • x) (lev N l : Subgroup (GL (Fin 2) ℝ)) :=
      (hx.smul _).mono hle
    show x.IsZeroAt ((f : ℍ → ℂ) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ) k
    exact OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3)

end GlobalTheory.Hk
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem diam_conj_mem (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) (hσ : IsDiam N l d σ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Lev N l) : σ * γ * σ⁻¹ ∈ Lev N l := by
  apply GlobalTheory.HeckeFamilyMatrices.CosetReps.diam_conj <;> assumption

theorem diam_normalises_lev : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  intro N l d σ hσ γ
  refine ⟨⟨σ * (γ : SL(2, ℤ)) * σ⁻¹, diam_conj_mem N l d σ hσ γ γ.2⟩, ?_⟩
  simp only [mat, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

end GlobalTheory.HeckeFamilyMatrices
end

section

namespace GlobalTheory.TraceFormNondegenerate

theorem eq_zero_of_trace_mul {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (h : ∀ Y : Matrix (Fin n) (Fin n) K, Matrix.trace (X * Y) = 0) : X = 0 := by
  ext i j
  have hij := h (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at hij
  simpa using hij

theorem span_eq_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K)
    (htr : ∀ g : Γ, Matrix.trace (M g) = Matrix.trace (N g))
    (hN : Submodule.span K (Set.range (⇑N : Γ → Matrix (Fin n) (Fin n) K)) = ⊤) :
    Submodule.span K (Set.range (⇑M : Γ → Matrix (Fin n) (Fin n) K)) = ⊤ := by
  apply GlobalTheory.TraceConj.span_top_of_trace_eq <;> assumption

end GlobalTheory.TraceFormNondegenerate
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.mul_powerSeries {N : ℕ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
    (hf : HasQ N f (fun n => PowerSeries.coeff n φ)) (hg : HasQ N g (fun n => PowerSeries.coeff n ψ)) :
    HasQ N (fun τ => f τ * g τ) (fun n => PowerSeries.coeff n (φ * ψ)) := by
  have h := hf.mul_conv hg
  have e : conv (fun n => PowerSeries.coeff n φ) (fun n => PowerSeries.coeff n ψ) =
      fun n => PowerSeries.coeff n (φ * ψ) := by
    funext n; rw [conv, PowerSeries.coeff_mul]
  rwa [e] at h

theorem HasQ.pow_powerSeries {N : ℕ} {f : ℍ → ℂ} {b : ℕ → ℂ} (hf : HasQ N f b) (i : ℕ) :
    HasQ N (fun τ => f τ ^ i) (fun n => PowerSeries.coeff n (PowerSeries.mk b ^ i)) := by
  induction i with
  | zero =>
    have h := HasQ.const N (1 : ℂ)
    convert h using 2 <;> simp [PowerSeries.coeff_one]
  | succ i ih =>
    have hb : HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk b)) := by
      simpa only [PowerSeries.coeff_mk] using hf
    have h := ih.mul_powerSeries hb
    simpa only [pow_succ] using h

theorem polyRel_qSeries : ∀ (N n : ℕ) (f : ℍ → ℂ) (b : ℕ → ℂ) (p : ℕ → ℍ → ℂ) (c : ℕ → ℕ → ℂ), 0 < N → HasQ N f b → (∀ i, HasQ N (p i) (c i)) → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i = 0) → (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i))).eval (PowerSeries.mk b) = 0 := by
  intro N n f b p c hN hf hp hrel
  have hterm : ∀ i ∈ Finset.range (n + 1), HasQ N (fun τ => p i τ * f τ ^ i)
      (fun m => PowerSeries.coeff m (PowerSeries.mk (c i) * PowerSeries.mk b ^ i)) := by
    intro i _
    have hpi : HasQ N (p i) (fun m => PowerSeries.coeff m (PowerSeries.mk (c i))) := by
      simpa only [PowerSeries.coeff_mk] using hp i
    exact hpi.mul_powerSeries (hf.pow_powerSeries i)
  have hsum := HasQ.sum (Finset.range (n + 1)) hterm
  have hzero : HasQ N (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) (fun _ => 0) := by
    have h0 := HasQ.const N (0 : ℂ)
    have e : (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) = fun _ => (0 : ℂ) :=
      funext hrel
    rw [e]
    simpa using h0
  have hc := HasQ.coeff_unique hN hsum hzero
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  ext m
  have := congrFun hc m

  simpa [map_sum] using this

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCong

theorem cong_iff_dg : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ),
    Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  intro N d u hu γ γ'
  have key : (dg u * redGL N γ' = redGL N γ * dg u) ↔
      ((dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) * (redGL N γ' : Matrix (Fin 2) (Fin 2) (ZMod N)) =
        (redGL N γ : Matrix (Fin 2) (Fin 2) (ZMod N)) * (dg u : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
    constructor
    · intro h; rw [← Units.val_mul, h, Units.val_mul]
    · intro h; ext1; simpa using h
  rw [key]
  have hM : ∀ δ : SL(2, ℤ), (redGL N δ : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      !![(en δ 0 0 : ZMod N), en δ 0 1; en δ 1 0, en δ 1 1] := by
    intro δ
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hD : (dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![1, 0; 0, (d : ZMod N)] := by
    show !![1, 0; 0, (u : ZMod N)] = _
    rw [hu]
  rw [hM, hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [Cong, ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, one_mul, zero_mul, add_zero,
    zero_add, mul_one, mul_zero]
  have hdu : IsUnit (d : ZMod N) := hu ▸ u.isUnit
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, ?_, ?_⟩
    · rw [h2, mul_comm]
    · rw [h3]
    · rw [h4, mul_comm]
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · rw [h2, mul_comm]
    · rw [mul_comm] at h4
      exact hdu.mul_right_cancel h4

end GlobalTheory.FNCong
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.diamond_diag_mul_eq_mul_of_dvd_lowerLeft_gamma1InterGamma0 : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, mat σ * dg q 1 * mat γ = mat γ' * (mat σ * dg q 1) := by
  first | exact @GlobalTheory.Hk.dia_diag_mul_of_dvd_lowerLeft | exact GlobalTheory.Hk.dia_diag_mul_of_dvd_lowerLeft | (intros; apply GlobalTheory.Hk.dia_diag_mul_of_dvd_lowerLeft <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

theorem _root_.GlobalTheory.T.upperTriangular_mul_eq_mul_upperTriangular_gamma1InterGamma0 : ∀ (N l q j : ℕ) (γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → j < q → γ ∈ GlobalTheory.Hk.lev N l → ¬ (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  first | exact @GlobalTheory.Hk.tinv_fin_fin | exact GlobalTheory.Hk.tinv_fin_fin | (intros; apply GlobalTheory.Hk.tinv_fin_fin <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix : ∀ (N l q : ℕ) (k d : ℤ) (ρ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.uOp q (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.uOp q ⇑f) := by
  first | exact @GlobalTheory.Hk.uOp_dia_comm | exact GlobalTheory.Hk.uOp_dia_comm | (intros; apply GlobalTheory.Hk.uOp_dia_comm <;> assumption)
end
