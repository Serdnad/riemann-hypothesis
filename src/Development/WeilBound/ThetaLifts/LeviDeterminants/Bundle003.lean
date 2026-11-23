module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle002
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

theorem evI_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

theorem mem_latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → F)
    (hy : ∀ i, IsIntegral ℤ (y i)) : (fun i => mixedEmbedding F (y i)) ∈ latPi F κ := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro ji
  rw [Pi.basis_repr]
  have h1 : mixedEmbedding F (y ji.1) ∈ mixedEmbedding.integerLattice F := by
    exact ⟨⟨y ji.1, hy ji.1⟩, rfl⟩
  have h2 := (mem_span_latticeBasis F).mpr h1
  exact (Module.Basis.mem_span_iff_repr_mem ℤ _ _).mp h2 ji.2

theorem summable_inv_one_add_pow (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Summable fun z : latPi F κ =>
      ((1 + ‖(z : κ → mixedSpace F)‖) ^ (Module.finrank ℤ (latPi F κ) + 1))⁻¹ := by
  set N : ℕ := Module.finrank ℤ (latPi F κ) + 1 with hN
  have h0 := ZLattice.summable_norm_rpow (latPi F κ) (-(N : ℝ)) (by rw [hN]; push_cast; linarith)
  have h1 : Summable fun z : latPi F κ => (if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro z hz
    have : z ≠ 0 := by simpa using hz
    simp [this]
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add h1)
  have hr : 0 ≤ ‖z‖ ^ (-(N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, if_false, add_zero]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    have : ‖z‖ = ‖(z : κ → mixedSpace F)‖ := rfl
    rw [← this]
    gcongr
    linarith

end PositivityTheory.ThKF0.LatSum

namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  apply GlobalTheory.LatScaleSum.thetaSum_norm_le_pow <;> assumption

end PositivityTheory.ThKF0.LatSum

namespace PositivityTheory.ThKF0

theorem theta_sum_norm_bound_denominator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k :=
  LatSum.thetaSum_norm_le_pow

end PositivityTheory.ThKF0
end

section

open Complex GlobalTheory.CompanionTheory.OM.SchDiff
open scoped ContDiff

namespace PositivityTheory.ThKF0

theorem schwartzDq : SchwartzDq := by
  intro V _ _ _ a L f G hG T
  let ph : ℝ × V → ℝ := fun q => -(2 * Real.pi) * (q.1 * L q.2 + q.1 * q.1 * (L a / 2))
  let l : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight a
  have h1 := (ContinuousLinearMap.fst ℝ ℝ V).hasTemperateGrowth
  have h2 := (L ∘L ContinuousLinearMap.snd ℝ ℝ V).hasTemperateGrowth
  have hph : Function.HasTemperateGrowth ph :=
    (Function.HasTemperateGrowth.const _).fun_mul ((h1.fun_mul h2).fun_add
      ((h1.fun_mul h1).fun_mul (Function.HasTemperateGrowth.const _)))
  have hA := temperate_exp.comp hph
  let F : ℝ × V → ℂ := fun q => cexp (I * (ph q : ℝ)) * f (q.2 + l q.1)
  have hF : ContDiff ℝ ∞ F := hA.1.mul ((f.smooth ⊤).comp (contDiff_snd.add (l.contDiff.comp contDiff_fst)))
  have hR : ∀ t, ⇑(G t) = fun x => F (t, x) := fun t => by
    funext x
    rw [hG, Lib.hl]
    simp only [F, ph, l, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    congr 2
    push_cast
    ring
  have hd : ∀ x, HasDerivAt (fun t => F (t, x)) (Lib.dop a L f x) 0 := fun x => by
    have e1 : HasDerivAt (fun t : ℝ => ph (t, x)) (-(2 * Real.pi) * L x) 0 := by
      have := ((((hasDerivAt_id (0 : ℝ)).mul_const (L x)).add
        (((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (L a / 2))).const_mul (-(2 * Real.pi)))
      exact this.congr_deriv (by simp)
    have e2 := (e1.ofReal_comp.const_mul I).cexp
    have e3 : HasDerivAt (fun t : ℝ => f (x + l t)) (fderiv ℝ f x a) 0 := by
      have := (f.differentiable (x + l 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (l.hasDerivAt.const_add x)
      exact this.congr_deriv (by simp [l])
    refine (e2.mul e3).congr_deriv ?_
    rw [Lib.dop_apply]
    simp [ph, l]
    ring
  have hD : ∀ v : ℝ, ⇑((v : ℂ) • Lib.dop a L f) = fun x => fderiv ℝ F (0, x) (v, 0) := fun v => by
    funext x
    have e := (hF.differentiable (by simp) (0, x)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))
    have e' : fderiv ℝ F (0, x) (1, 0) = Lib.dop a L f x := e.unique (hd x)
    rw [show ((v, 0) : ℝ × V) = v • (1, 0) by simp, map_smul, e', SchwartzMap.smul_apply, smul_eq_mul, Complex.real_smul]
  have key := hasFDerivAt_family hF 0 (fun k n => bound_mul_translate hA f l 0 k n) G (fun v => (v : ℂ) • Lib.dop a L f) hR hD T
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (T (Lib.dop a L f))) fun v => by simp
  exact key.hasDerivAt.congr_deriv (by simp)

end PositivityTheory.ThKF0
end
