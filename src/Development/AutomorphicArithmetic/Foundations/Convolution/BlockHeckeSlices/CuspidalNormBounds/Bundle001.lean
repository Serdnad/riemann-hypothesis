module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapPoly
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField

namespace UpperTheory.ConvolutionTheory.BW

private theorem finite_span_of_killed {K X : Type} {d : ℕ} (ρ : K → Matrix (Fin d) (Fin d) ℂ) (ψ : K → X → ℂ)
    (h : ∀ x : K →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ g : X, (x.sum fun k c => c * ψ k g) = 0) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) := by
  let A : (K →₀ ℂ) →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ := Finsupp.linearCombination ℂ ρ
  let B : (K →₀ ℂ) →ₗ[ℂ] (X → ℂ) := Finsupp.linearCombination ℂ ψ
  have hAB : LinearMap.ker A ≤ LinearMap.ker B := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    funext g
    have := h x (by simpa [A, Finsupp.linearCombination_apply] using hx) g
    simpa [B, Finsupp.linearCombination_apply, Finsupp.sum_apply'] using this
  haveI : FiniteDimensional ℂ ((K →₀ ℂ) ⧸ LinearMap.ker A) :=
    Module.Finite.equiv A.quotKerEquivRange.symm
  have hr : LinearMap.range ((LinearMap.ker A).liftQ B hAB) = Submodule.span ℂ (Set.range ψ) := by
    rw [Submodule.range_liftQ]
    exact Finsupp.range_linearCombination ℂ
  rw [← hr]
  infer_instance

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW GlobalTheory.CuspRep in
theorem UpperTheory.ConvolutionTheory.BW.killedOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.KilledOps E := by
  intro E _ _ _ n ρ φ hφ
  refine ⟨fun k x hx g => ?_, ?_⟩
  · have h0 : ((x.mapDomain fun k' => k' * k).sum fun k' c => c • ρ.ρ k') = 0 := by
      rw [Finsupp.sum_mapDomain_index (h := fun k' c => c • ρ.ρ k') (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
      have : (x.sum fun k' c => c • ρ.ρ (k' * k)) = (x.sum fun k' c => c • ρ.ρ k') * ρ.ρ k := by
        rw [Finsupp.sum_mul]
        simp only [map_mul, smul_mul_assoc]
      rw [this, hx, zero_mul]
    have h1 := hφ _ h0 g
    rw [Finsupp.sum_mapDomain_index (h := fun (k' : KA E n) c => c * φ.1 (g * (k' : GA E n))) (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)] at h1
    simp only [Subgroup.coe_mul, ← mul_assoc] at h1
    exact h1
  · unfold GroundTheory.Automorphic.AutomorphicForm.IsKFinite
    exact finite_span_of_killed ρ.ρ _ (fun x hx g => hφ x hx g)
end

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

theorem UpperTheory.ConvolutionTheory.BW.cuspUmg :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.CuspUmg E := by
  intro E _ _ _ n f hf
  refine ⟨⟨hf.1.isLeftInvariant, level_of hf.1.isSmooth hf.1.isKFinite, ?_⟩, hf.2⟩
  obtain ⟨C₀, N, hC₀⟩ := hf.1.hasModerateGrowth
  refine ⟨N, fun u => ?_⟩
  show HasGrowth (uC E n u f).1 N
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, fun g => by simp⟩
  | tmul c x =>
    obtain ⟨C, hC⟩ := hasGrowth_uAction x hf.1.isSmoothKZ ⟨C₀, hC₀⟩
    refine ⟨‖c‖ * C, fun g => ?_⟩
    rw [uC_tmul, mul_assoc]
    exact (norm_mul c _).le.trans (mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c))
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy
end
end

section

open NumberField

theorem UpperTheory.ConvolutionTheory.BW.zSpec :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.ZSpec E := by
  intro E _ _ _ n τ
  have key : ∀ ℓ : UpperTheory.V.Cm.UC E n →ₗ[ℂ] ℂ, ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ p.coeff n = ℓ 1 ∧
      (∀ u, p.eval u = ℓ (UpperTheory.V.Cm.capC τ u)) ∧ ∀ i, ℓ (zC E n τ i) = p.coeff (n - i) := fun ℓ => by
    obtain ⟨p, h1, h2, -, h4⟩ := exists_capPoly (UpperTheory.V.Cm.genC (a := n) τ) ℓ
    refine ⟨p, h1, h2, h4, fun i => ?_⟩
    have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1))) :=
      fun a _ b _ h => Fin.ext (Nat.cast_injective h)
    have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h1)
    conv_rhs => rw [Lagrange.eq_interpolate hinj hd]

    rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, zC, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, h4, map_smul, smul_eq_mul, mul_comm]
    rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, -, h2, -, h4⟩ := key ℓ
    rw [map_sub, h4, Nat.sub_zero, h2, sub_self]
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, h1, -, h3, h4⟩ := key ℓ

    rw [map_sub, sub_eq_zero, ← h3, map_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
    ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, h4, smul_eq_mul, mul_comm]
    simp
end
