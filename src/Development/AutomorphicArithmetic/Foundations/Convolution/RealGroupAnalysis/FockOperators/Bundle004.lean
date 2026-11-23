module

public import Formalism.RealPlaceAnalysis.Bundle003
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.Algebra.BigOperators.Fin
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem qdet_fin_two {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V) (u : ℂ) :
    Formalism.REAL.qdet X u = (algebraMap ℂ (Module.End ℂ V) u + X 0 0) * (algebraMap ℂ (Module.End ℂ V) (u - 1) + X 1 1) - X 1 0 * X 0 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, hp, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem four_qdet {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V)
    (hX : Formalism.REAL.GlRel X) (u : ℂ) (w : V) :
    (4 : ℂ) • Formalism.REAL.qdet X u w = ((2 * u - 1) ^ 2 - 1) • w + (2 * (2 * u - 1)) • (X 0 0 + X 1 1) w
      + (X 0 0 + X 1 1) ((X 0 0 + X 1 1) w)
      - ((X 0 0 - X 1 1) ((X 0 0 - X 1 1) w) + (2 : ℂ) • (X 0 1 (X 1 0 w) + X 1 0 (X 0 1 w))) := by
  have r1 : X 0 0 (X 1 1 w) - X 1 1 (X 0 0 w) = 0 := by
    simpa using LinearMap.congr_fun (hX 0 0 1 1) w
  have r2 : X 0 1 (X 1 0 w) - X 1 0 (X 0 1 w) = X 0 0 w - X 1 1 w := by
    simpa using LinearMap.congr_fun (hX 0 1 1 0) w
  rw [qdet_fin_two]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add (f := _),
    map_sub, map_smul]
  linear_combination (norm := module) (2 : ℂ) • r1 + (2 : ℂ) • r2

theorem UpperTheory.ConvolutionTheory.R2.Fo.capAbs :
    ∀ (V S T : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
    (V₀ : Submodule ℂ V) (S₀ : Submodule ℂ S) (Λ : V →ₗ[ℂ] S →ₗ[ℂ] T) (E : Fin 2 → Fin 2 → Module.End ℂ V) (P : Fin 2 → Fin 2 → Module.End ℂ T)
    (a : Fin 2 → Fin 2 → Module.End ℂ S) (e f h : Module.End ℂ S), Formalism.REAL.GlRel E → Formalism.REAL.GlRel P →
    (∀ i j, ∀ v ∈ V₀, E i j v ∈ V₀) → (∀ i j, ∀ s ∈ S₀, a i j s ∈ S₀) → (∀ s ∈ S₀, e s ∈ S₀) → (∀ s ∈ S₀, f s ∈ S₀) →
    (∀ i j, ∀ v ∈ V₀, ∀ s ∈ S₀, P i j (Λ v s) = Λ v (a i j s) + if i = j then Λ (E 1 1 v) s else 0) →
    (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e s) = -Λ (E 0 1 v) s) → (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f s) = -Λ (E 1 0 v) s) →
    e * f - f * e = h → a 0 0 + a 1 1 = -h →
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h + 2 * (e * f + f * e) →
    ∀ u, ∀ v ∈ V₀, ∀ s ∈ S₀, Formalism.REAL.qdet P u (Λ v s) = Λ (Formalism.REAL.qdet E u v) s := by
  intro V S T _ _ _ _ _ _ V₀ S₀ Λ E P a e f h hE hP hEV haS heS hfS hPΛ heΛ hfΛ hh hz hb u v hv s hs
  have hH : ∀ w, E 0 1 (E 1 0 w) - E 1 0 (E 0 1 w) = (E 0 0 - E 1 1) w := fun w => by
    simpa using LinearMap.congr_fun (hE 0 1 1 0) w
  have hef : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e (f s)) = Λ (E 1 0 (E 0 1 v)) s := fun v hv s hs => by
    rw [heΛ v hv _ (hfS s hs), hfΛ _ (hEV 0 1 v hv) s hs, neg_neg]
  have hfe : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f (e s)) = Λ (E 0 1 (E 1 0 v)) s := fun v hv s hs => by
    rw [hfΛ v hv _ (heS s hs), heΛ _ (hEV 1 0 v hv) s hs, neg_neg]
  have hhS : ∀ s ∈ S₀, h s ∈ S₀ := fun s hs => by
    rw [← hh]
    exact S₀.sub_mem (heS _ (hfS s hs)) (hfS _ (heS s hs))
  have hHV : ∀ v ∈ V₀, (E 0 0 - E 1 1) v ∈ V₀ := fun v hv =>
    V₀.sub_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hZV : ∀ v ∈ V₀, (E 0 0 + E 1 1) v ∈ V₀ := fun v hv =>
    V₀.add_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hhΛ : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (h s) = -Λ ((E 0 0 - E 1 1) v) s := fun v hv s hs => by
    rw [← hh, ← hH v, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, map_sub, hef v hv s hs,
      hfe v hv s hs, map_sub, LinearMap.sub_apply, neg_sub]
  have hZ : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 + P 1 1) (Λ v s) = Λ ((E 0 0 + E 1 1) v) s := fun v hv s hs => by
    have h1 : a 0 0 s + a 1 1 s = -h s := by simpa using LinearMap.congr_fun hz s
    have h2 : Λ v (a 0 0 s) + Λ v (a 1 1 s) = Λ ((E 0 0 - E 1 1) v) s := by
      rw [← map_add (f := _), h1, map_neg, hhΛ v hv s hs, neg_neg]
    simp only [LinearMap.add_apply, hPΛ _ _ v hv s hs, if_true, map_add (f := _)]
    simp only [LinearMap.sub_apply, map_sub] at h2
    linear_combination (norm := module) h2
  have hHP : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 - P 1 1) (Λ v s) = Λ v ((a 0 0 - a 1 1) s) := fun v hv s hs => by
    simp only [LinearMap.sub_apply, hPΛ _ _ v hv s hs, if_true, map_sub]
    abel
  have hA : ∀ s ∈ S₀, (a 0 0 - a 1 1) s ∈ S₀ := fun s hs => S₀.sub_mem (haS 0 0 s hs) (haS 1 1 s hs)
  have hBr : (P 0 0 - P 1 1) ((P 0 0 - P 1 1) (Λ v s)) + (2 : ℂ) • (P 0 1 (P 1 0 (Λ v s)) + P 1 0 (P 0 1 (Λ v s)))
      = Λ ((E 0 0 - E 1 1) ((E 0 0 - E 1 1) v) + (2 : ℂ) • (E 0 1 (E 1 0 v) + E 1 0 (E 0 1 v))) s := by
    have p10 : P 1 0 (Λ v s) = Λ v (a 1 0 s) := by simpa using hPΛ 1 0 v hv s hs
    have p01 : P 0 1 (Λ v s) = Λ v (a 0 1 s) := by simpa using hPΛ 0 1 v hv s hs
    have p01' : P 0 1 (Λ v (a 1 0 s)) = Λ v (a 0 1 (a 1 0 s)) := by
      simpa using hPΛ 0 1 v hv _ (haS 1 0 s hs)
    have p10' : P 1 0 (Λ v (a 0 1 s)) = Λ v (a 1 0 (a 0 1 s)) := by
      simpa using hPΛ 1 0 v hv _ (haS 0 1 s hs)
    have hb' : (a 0 0 - a 1 1) ((a 0 0 - a 1 1) s) + (2 : ℂ) • (a 0 1 (a 1 0 s) + a 1 0 (a 0 1 s))
        = h (h s) + (2 : ℂ) • (e (f s) + f (e s)) := by
      have := LinearMap.congr_fun hb s
      simp only [two_mul, LinearMap.add_apply, Module.End.mul_apply] at this
      rw [two_smul, two_smul]
      exact this
    rw [hHP v hv s hs, hHP v hv _ (hA s hs), p10, p01, p01', p10', ← map_add (f := _), ← map_smul, ← map_add (f := _), hb', map_add (f := _), map_smul,
      map_add, hef v hv s hs, hfe v hv s hs, hhΛ v hv _ (hhS s hs), hhΛ _ (hHV v hv) s hs, neg_neg,
      map_add, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.add_apply, add_comm (Λ (E 1 0 _) s)]
  have key : (4 : ℂ) • Formalism.REAL.qdet P u (Λ v s) = (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s := by
    have k2 : (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s = Λ ((4 : ℂ) • Formalism.REAL.qdet E u v) s := by
      rw [map_smul, LinearMap.smul_apply]
    rw [k2, four_qdet P hP u, four_qdet E hE u v, hBr, hZ v hv s hs, hZ _ (hZV v hv) s hs]
    simp only [map_add (f := _), map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  exact smul_right_injective T (by norm_num : (4 : ℂ) ≠ 0) key
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capelli :
    ∀ (A : Type) [Ring A] (X D a : Fin 2 → Fin 2 → A) (q Δ h : A), (∀ i j k l, X i j * X k l = X k l * X i j) → (∀ i j k l, D i j * D k l = D k l * D i j) →
    (∀ i j k l, D i j * X k l = X k l * D i j + if i = k ∧ j = l then 1 else 0) →
    (∀ i j, a i j = -(if i = j then 1 else 0) - ∑ b, X j b * D i b) → q = X 0 1 * X 1 0 - X 0 0 * X 1 1 → Δ = D 0 1 * D 1 0 - D 0 0 * D 1 1 →
    h = (∑ i, ∑ j, X i j * D i j) + 2 →
    Δ * q - q * Δ = h ∧ a 0 0 + a 1 1 = -h ∧
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h - 2 * (q * Δ + Δ * q) := by
  intro A _ X D a q Δ h hX hD hDX ha hq hΔ hh
  have hDX' : ∀ i j k l z, D i j * (X k l * z) = X k l * (D i j * z) + if i = k ∧ j = l then z else 0 := by
    intro i j k l z
    rw [← mul_assoc, hDX, add_mul, mul_assoc]
    split_ifs <;> simp
  have hX' : ∀ i j k l z, X i j * (X k l * z) = X k l * (X i j * z) := by
    intro i j k l z
    rw [← mul_assoc, hX, mul_assoc]
  have h2 : (2 : A) = 1 + 1 := by norm_num
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  subst hq hΔ hh
  simp only [ha, Fin.sum_univ_two, h2, h01, h10, if_true, if_false]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    try simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_zero, zero_sub, neg_neg, mul_one, one_mul, mul_assoc, hDX, hDX', h01, h10, and_self, and_true, true_and, and_false, false_and, if_true, if_false, add_zero,
      hX 1 1 0 0, hX 1 1 0 1, hX 1 1 1 0, hX 1 0 0 0, hX 1 0 0 1, hX 0 1 0 0,
      hX' 1 1 0 0, hX' 1 1 0 1, hX' 1 1 1 0, hX' 1 0 0 0, hX' 1 0 0 1, hX' 0 1 0 0,
      hD 1 1 0 0, hD 1 1 0 1, hD 1 1 1 0, hD 1 0 0 0, hD 1 0 0 1, hD 0 1 0 0]
  all_goals abel
end
