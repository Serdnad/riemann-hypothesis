module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle063
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle064
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle066
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle081
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle080
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle065
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal


theorem _root_.GlobalTheory.T.exists_lintegral_norm_pow_mul_le_sqrt_weighted_sq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] [NormedAddCommGroup F], ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (H : E → F), Continuous H → ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ k * ‖H z‖) ∂μ ≤ C * (∫⁻ z, ENNReal.ofReal ((‖z‖ ^ k * ‖H z‖) ^ 2) ∂μ + ∫⁻ z, ENNReal.ofReal ((‖z‖ ^ (k + finrank ℝ E + 1) * ‖H z‖) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  first | exact @GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | exact GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq | (intros; apply GlobalTheory.lintegral_norm_pow_mul_le_sqrt_weighted_sq <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eventually_rpow_log_inequalities : ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop, x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧ 11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧ 2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧ 44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  first | exact @GlobalTheory.five_elementary_inequalities_eventually | exact GlobalTheory.five_elementary_inequalities_eventually | (intros; apply GlobalTheory.five_elementary_inequalities_eventually <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eq_of_forall_cexp_neg_two_pi_I_mul_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  first | exact @GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq | exact GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq | (intros; apply GlobalTheory.real_eq_of_exp_neg_two_pi_I_div_eq <;> assumption)
end

section

open Matrix

namespace GlobalTheory

def piMatUnit {I : Type} [DecidableEq I] (m : ℕ) (τ : I) (i j : Fin m) :
    I → Matrix (Fin m) (Fin m) ℂ :=
  Pi.single τ (Matrix.single i j 1)

lemma piMatUnit_mul {I : Type} [DecidableEq I] (m : ℕ) (τ τ' : I) (i j k l : Fin m) :
    piMatUnit m τ i j * piMatUnit m τ' k l =
      if τ = τ' ∧ j = k then piMatUnit m τ i l else 0 := by
  funext ρ
  simp only [piMatUnit, Pi.mul_apply]
  by_cases h1 : τ = τ'
  · subst h1
    by_cases h2 : j = k
    · subst h2
      by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_same]
      · simp [Pi.single_apply, h3]
    · by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_of_ne, h2]
      · simp [Pi.single_apply, h3, h2]
  · by_cases h3 : ρ = τ
    · subst h3
      have : ρ ≠ τ' := h1
      simp [Pi.single_apply, this, h1]
    · simp [Pi.single_apply, h3, h1]

lemma piMatUnit_decomp {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (x : I → Matrix (Fin m) (Fin m) ℂ) :
    x = ∑ τ, ∑ i, ∑ j, x τ i j • piMatUnit m τ i j := by
  funext ρ
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, piMatUnit,
    Pi.single_apply]
  simp only [show ∀ (c : Prop) [Decidable c] (M : Matrix (Fin m) (Fin m) ℂ),
      (if c then M else 0) a b = if c then M a b else 0 from fun c _ M => by split_ifs <;> rfl]
  simp [Matrix.zero_apply, Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

lemma sum_piMatUnit_diag {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (τ : I) :
    ∑ i, piMatUnit m τ i i = Pi.single τ 1 := by
  funext ρ
  ext a b
  by_cases h : ρ = τ
  · subst h
    simp only [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_eq_same, Matrix.single_apply,
      Matrix.one_apply]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab]
  · simp [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_apply, h]

lemma exists_mul_idem_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P') (ht : P.trace = P'.trace) :
    ∃ X Y : Matrix (Fin g) (Fin g) ℂ, Y * P' * X = P := by
  first
  | exact @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | (apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq ..)

theorem conj_of_trace_central_idem_eq :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m →
      ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ),
        (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) →
          ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  intro I _ _ m g hm σ σ' htr
  set z : Fin m := ⟨0, hm⟩

  have hdiag : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      (ρ (Pi.single τ 1)).trace = (m : ℂ) * (ρ (piMatUnit m τ z z)).trace := by
    intro ρ τ
    have hi : ∀ i, (ρ (piMatUnit m τ i i)).trace = (ρ (piMatUnit m τ z z)).trace := by
      intro i
      have e1 : piMatUnit m τ i i = piMatUnit m τ i z * piMatUnit m τ z i := by
        rw [piMatUnit_mul]; simp
      have e2 : piMatUnit m τ z z = piMatUnit m τ z i * piMatUnit m τ i z := by
        rw [piMatUnit_mul]; simp
      rw [e1, e2, map_mul, map_mul, Matrix.trace_mul_comm]

    rw [← sum_piMatUnit_diag, map_sum, Matrix.trace_sum, Finset.sum_congr rfl (fun i _ => hi i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hidem : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      IsIdempotentElem (ρ (piMatUnit m τ z z)) := by
    intro ρ τ
    unfold IsIdempotentElem
    rw [← map_mul, piMatUnit_mul]; simp
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have htr' : ∀ τ, (σ (piMatUnit m τ z z)).trace = (σ' (piMatUnit m τ z z)).trace := by
    intro τ
    have := htr τ
    rw [hdiag σ, hdiag σ'] at this
    exact mul_left_cancel₀ hm' this
  choose X Y hYX using fun τ => exists_mul_idem_mul_eq_of_trace_eq _ _ (hidem σ τ) (hidem σ' τ) (htr' τ)
  set h : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ' (piMatUnit m τ i z) * X τ * σ (piMatUnit m τ z i) with hh
  set h' : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) with hh'

  have hE : ∀ τ k l, σ' (piMatUnit m τ k l) * h = h * σ (piMatUnit m τ k l) := by
    intro τ k l
    have hL : ∀ τ' i, σ' (piMatUnit m τ k l) * (σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i))
        = if τ = τ' ∧ l = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [← mul_assoc, ← mul_assoc, ← map_mul, piMatUnit_mul]
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; rfl
      · simp
    have hR : ∀ τ' i, σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i) * σ (piMatUnit m τ k l)
        = if τ = τ' ∧ k = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [mul_assoc _ (σ _), ← map_mul, piMatUnit_mul]
      by_cases hc : τ' = τ ∧ i = k
      · obtain ⟨rfl, rfl⟩ := hc; simp
      · have hc' : ¬ (τ = τ' ∧ k = i) := fun h => hc ⟨h.1.symm, h.2.symm⟩
        simp [hc, hc']
    rw [hh, Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul, hL, hR]
    simp [ite_and, Finset.sum_ite_eq]
  have hint : ∀ x, σ' x * h = h * σ x := by
    intro x
    rw [piMatUnit_decomp m x]

    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hE]

  have hprod : ∀ τ i τ' j, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
      (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j))
        = if τ = τ' ∧ i = j then σ (piMatUnit m τ i i) else 0 := by
    intro τ i τ' j
    have e : σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
        (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j)) =
        σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i * piMatUnit m τ' j z) * X τ' *
          σ (piMatUnit m τ' z j) := by
      rw [map_mul]; simp only [mul_assoc]
    rw [e, piMatUnit_mul]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      rw [show σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z z) * X τ * σ (piMatUnit m τ z i) =
          σ (piMatUnit m τ i z) * (Y τ * σ' (piMatUnit m τ z z) * X τ) * σ (piMatUnit m τ z i) by
            simp only [mul_assoc], hYX τ, ← map_mul, ← map_mul]
      simp [piMatUnit_mul]
    · simp
  have hrow : ∀ τ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) * h =
      σ (piMatUnit m τ i i) := by
    intro τ i
    rw [hh]
    simp only [Finset.mul_sum, hprod]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hinv : h' * h = 1 := by
    rw [hh', Finset.sum_mul]
    simp only [Finset.sum_mul, hrow]

    rw [← map_one σ, ← Finset.univ_sum_single (1 : I → Matrix (Fin m) (Fin m) ℂ), map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_

    rw [Pi.one_apply, ← sum_piMatUnit_diag, map_sum]
  exact ⟨h, (Matrix.isUnit_iff_isUnit_det h).mpr (Matrix.isUnit_det_of_left_inverse hinv), hint⟩

end GlobalTheory
end

section

namespace GlobalTheory.CMModel

theorem mem_of_forall_ringEquiv_fixed :
    ∀ (F : IntermediateField ℚ ℂ) (x : ℂ),
      (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := fun F x hx ↦ by
  obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := F) x
    fun σ ↦ hx σ.toRingEquiv fun y hy ↦ σ.commutes ⟨y, hy⟩
  exact y.2

end GlobalTheory.CMModel
end

section

namespace GlobalTheory.CompanionTheory.Burnside

theorem mem_of_irred {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  first
  | exact @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | (apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible ..)

theorem burnside_surj_of_irred {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  intro f
  have h := mem_of_irred ρ.range (fun N hN => hirr N fun a w hw => hN (ρ a) ⟨a, rfl⟩ w hw) f
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.Burnside
end

section

open Polynomial
namespace GlobalTheory

theorem exists_ringHom_extension_algClosed_of_isIntegral_injective {R S K : Type*} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (ψ : R →+* K) : ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
  | (apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq ..)

theorem isRoot_map_minpoly_iff_exists_ringHom : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B], Function.Injective (algebraMap A B) → ∀ (g : B) (φ : A →+* ℂ) (z : ℂ), ((minpoly A g).map φ).IsRoot z ↔ ∃ x : B →+* ℂ, x.comp (algebraMap A B) = φ ∧ x g = z := by
  intro A B _ _ _ _ _ _ _ hinj g φ z
  constructor
  · intro h
    haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    have hg : IsIntegral A g := Algebra.IsIntegral.isIntegral g
    have h' : (minpoly A g).eval₂ φ z = 0 := by rwa [IsRoot, eval_map] at h
    let e := minpoly.equivAdjoin hg
    let ψ : Algebra.adjoin A {g} →+* ℂ := (AdjoinRoot.lift φ z h').comp (e.symm : _ →+* _)
    haveI : Algebra.IsIntegral (Algebra.adjoin A {g}) B := Algebra.IsIntegral.tower_top A
    obtain ⟨x, hx⟩ := exists_ringHom_extension_algClosed_of_isIntegral_injective (S := B) Subtype.val_injective ψ
    have hx' : ∀ r : Algebra.adjoin A {g}, x r = ψ r := fun r => RingHom.congr_fun hx r
    refine ⟨x, ?_, ?_⟩
    · ext a
      have := hx' (algebraMap A _ a)
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of] at this
      exact this
    · have h1 : (e (AdjoinRoot.root _) : B) = g := by
        change ((AdjoinRoot.Minpoly.toAdjoin A g (AdjoinRoot.root _) : Algebra.adjoin A {g}) : B) = g
        simp [AdjoinRoot.Minpoly.toAdjoin]
      have := hx' (e (AdjoinRoot.root _))
      simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_root] at this
      rwa [h1] at this
  · rintro ⟨x, rfl, rfl⟩
    rw [IsRoot, eval_map, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

end GlobalTheory
end

section

open scoped Pointwise

theorem _root_.GlobalTheory.T.doubleCoset_card_div_card_inf_commutative_subgroup : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by
  first | exact @GlobalTheory.DCIndex.index_identity | exact GlobalTheory.DCIndex.index_identity | (intros; apply GlobalTheory.DCIndex.index_identity <;> assumption)
end

section


theorem _root_.GlobalTheory.T.orbit_mass_formula_finiteIndex_subgroup : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  first | exact @GlobalTheory.OrbitMass.mass_formula | exact GlobalTheory.OrbitMass.mass_formula | (intros; apply GlobalTheory.OrbitMass.mass_formula <;> assumption)
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem span_image_inf_of_linearIndependent {K V W ι : Type} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W)
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun k => j (b k)))
    (U U' : Submodule K V) :
    Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) =
      Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V)) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := Fintype.ofFinite ι
  let B := Algebra.TensorProduct.basis ℂ b
  let J : ℂ ⊗[K] V →ₗ[ℂ] W := B.constr ℂ (fun k => j (b k))
  have hJb : ∀ k, J (1 ⊗ₜ b k) = j (b k) := fun k => by
    have := B.constr_basis ℂ (fun k => j (b k)) k
    rwa [Algebra.TensorProduct.basis_apply] at this
  have hJ : ∀ v, J (1 ⊗ₜ v) = j v := fun v => by

    rw [← b.sum_repr v, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_smulₛₗ j, ← hJb, ← map_smul,
      ← algebraMap_smul ℂ (b.repr v k)]
    rfl
  have hinj : Function.Injective J := by
    apply Module.Basis.injective_constr_of_linearIndependent
    exact hb
  have key : ∀ A : Submodule K V,
      Submodule.span ℂ (j '' (A : Set V)) = (A.baseChange ℂ).map J := fun A => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => (hJ v).symm
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ hinj]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V * V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h : B, (∀ f ∈ V, h * rd f ∈ Submodule.span ℂ (rd '' (V' : Set A))) → (∃ f ∈ V, h * rd f ≠ 0) → ∃ T : V →ₗ[K] V', T ≠ 0 ∧ ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A) := by
  first | exact @GlobalTheory.exists_rational_multiplier_of_complex | exact GlobalTheory.exists_rational_multiplier_of_complex | (intros; apply GlobalTheory.exists_rational_multiplier_of_complex <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B), Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O → ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  first | exact @GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | exact GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | (intros; apply GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq <;> assumption)
end
