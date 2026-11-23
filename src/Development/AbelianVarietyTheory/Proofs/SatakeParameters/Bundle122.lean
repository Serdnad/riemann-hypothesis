module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.IsPairFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle124
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle114
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle004
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem pair_value_eq {D : D7} {p : ℕ} [Fact p.Prime] {ι : ℂ ≃+* ℂ_[p]} {th : ℂ_[p]} (hth : th ≠ 0)
    {z₁ z₂ : Bool × HH D} {s₁ s₂ : D.host.E} (h₁ : ‖rho D ι z₁ s₁‖ = 1) (h₂ : ‖rho D ι z₂ s₂‖ = 1)
    (hc : ‖rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂‖ ≤ ‖th‖) {N : ℕ} {a b : Fin N} {X : D.host.E}
    (hX : X = s₁ * D.host.conj s₂ * (if a = b then 1 else 0)) :
    ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ (rho D ι z₁ s₁)⁻¹ * rho D ι z₁ X * (rho D ι z₂ s₂)⁻¹ =
      (if a = b then 1 else 0) + th * e := by
  have n₁ : rho D ι z₁ s₁ ≠ 0 := fun h => by simp [h] at h₁
  have n₂ : rho D ι z₂ s₂ ≠ 0 := fun h => by simp [h] at h₂
  by_cases hab : a = b
  · refine ⟨(rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂) / (rho D ι z₂ s₂ * th), ?_, ?_⟩
    · rw [norm_div, norm_mul, h₂, one_mul]
      exact div_le_one_of_le₀ hc (norm_nonneg _)
    · subst hX
      simp only [hab, if_true, mul_one, map_mul]
      field_simp
      ring
  · refine ⟨0, by simp, ?_⟩
    subst hX
    simp [hab]

theorem sum_pc_pc {D : D7} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ}
    (σ : Bool × HH D → 𝓞 D.host.E) (z₁ z₂ : Bool × HH D) (a₁ a₂ : Fin N)
    (F : (Bool × HH D) × Fin N → (Bool × HH D) × Fin N → ℂ_[p]) :
    ∑ l, ∑ l₂, pc D ι σ z₁ l a₁ * F l l₂ * pc D ι σ z₂ l₂ a₂ =
      (rho D ι z₁ (σ z₁ : D.host.E))⁻¹ * F (z₁, a₁) (z₂, a₂) * (rho D ι z₂ (σ z₂ : D.host.E))⁻¹ := by
  rw [Finset.sum_eq_single (z₁, a₁), Finset.sum_eq_single (z₂, a₂)]
  · simp [pc]
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem dual_local_bases_pair : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  intro D p _ ι th hth h2 N P σ hσ hP
  have key : ∀ t : HH D, (P (tauPl D (false, t)))⁻¹ = ((P (tauPl D (true, t))).map D.host.conj).transpose ∧
      (P (tauPl D (true, t)))⁻¹ * P (tauPl D (true, t)) = 1 := by
    intro t
    have h := hP t
    refine ⟨Matrix.inv_eq_left_inv h, ?_⟩
    apply Matrix.nonsing_inv_mul
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hd' : (P (tauPl D (true, t))).det ≠ 0 := by
      intro h0
      have : ((P (tauPl D (true, t))).map D.host.conj).det = D.host.conj (P (tauPl D (true, t))).det := by
        simpa using (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) (P (tauPl D (true, t)))).symm
      rw [this, h0] at hd
      simp at hd
    exact isUnit_iff_ne_zero.mpr hd'
  refine ⟨fun t a₁ a₂ => ?_, fun t b₁ b₂ => ?_⟩
  · rw [sum_pc_pc ι σ (false, t) (true, t) a₁ a₂
      (fun l l₂ => rho D ι (false, t) (∑ j, rowL D P σ l j * D.host.conj (rowL D P σ l₂ j)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    obtain ⟨k₁, k₂⟩ := key t
    have e := congrFun (congrFun k₂ a₂) a₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have e' := congrArg D.host.conj e

    simp only [rowL, k₁, map_mul, map_sum, Matrix.transpose_apply, Matrix.map_apply] at e' ⊢
    have e'' : D.host.conj (if a₂ = a₁ then 1 else 0) = if a₁ = a₂ then 1 else 0 := by
      by_cases h : a₁ = a₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e', Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [sum_pc_pc ι σ (false, t) (true, t) b₁ b₂
      (fun l l₂ => rho D ι (false, t) (∑ i, colR D P σ l i * D.host.conj (colR D P σ l₂ i)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    have e := congrFun (congrFun (hP t) b₂) b₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e
    simp only [colR, map_mul]
    have e'' : (if b₂ = b₁ then (1 : D.host.E) else 0) = if b₁ = b₂ then 1 else 0 := by
      by_cases h : b₁ = b₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.DFrame
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem frameM_coef_eq_chgB : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), (∀ (τ : D.what₂.Tau) (y : D.host.E), TaylorLogMetric.tauEmb D lm τ y = ι (TaylorLogMetric.embT D τ y)) → ∀ (X : Fields) (s : Seam D X) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (r : ∀ z, Fin (n z) → ℂ_[p]) (cκ c0 : Bool × HH D → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E), (∀ z, GlobalTheory.DFrame.rho D ι z (σ z : D.host.E) ≠ 0) → (∀ z, GlobalTheory.DFrame.rho D ι z (σ' z : D.host.E) ≠ 0) → (∀ z, (P (tauPl D z)).det ≠ 0) → (∀ z (τ' : D.what₂.Tau), ∑ k, r z k * TaylorLogMetric.tauEmb D lm τ' (a z k) = if τ' = tauPl D z then c0 z else 0) → ∀ (i : DVar X.Tau N N') (x : (Bool × HH D) × Fin N × Fin N'), frameM (ι : ℂ →+* ℂ_[p]) (fun j => GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.coef D ι cκ r σ σ') i x = cκ x.1 * c0 x.1 * TaylorLogMetric.chgB D lm P P' (s.iT i.1, i.2) ((0 : ZMod 1), (tauPl D x.1, x.2)) := by
  intro D p _ lm ι hι X s n N N' a r cκ c0 P P' σ σ' hσ hσ' hdet hsum i x
  unfold frameM
  have hJ : ∀ f : GlobalTheory.DFrame.JJ D n N N' → ℂ_[p], ∑ j, f j = ∑ α, ∑ l, ∑ l', f (α, l, l') := by
    intro f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hJ, Fintype.sum_sigma]
  simp only [GlobalTheory.DFrame.coef, GlobalTheory.DFrame.gc, GlobalTheory.DFrame.pc]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]
  rw [Finset.sum_eq_single x.1 (fun z _ hz => by simp [hz]) (by simp)]
  simp only [if_true, GlobalTheory.DFrame.vecF, GlobalTheory.DFrame.mat, GlobalTheory.DFrame.colR, GlobalTheory.DFrame.rowL, Matrix.of_apply, map_mul, RingEquiv.coe_toRingHom]
  have hsum' := hsum x.1 (s.iT i.1)
  simp only [hι] at hsum'
  have e : ∀ k, ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k)) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (cκ x.1 * r x.1 k * (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) =
      (cκ x.1 * (ι (TaylorLogMetric.embT D (s.iT i.1) (σ' x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) (P' (tauPl D x.1) i.2.1 x.2.2))) *
      (ι (TaylorLogMetric.embT D (s.iT i.1) (σ x.1 : D.host.E)) * ι (TaylorLogMetric.embT D (s.iT i.1) ((P (tauPl D x.1))⁻¹ x.2.1 i.2.2))) *
      (GlobalTheory.DFrame.rho D ι x.1 (σ x.1 : D.host.E))⁻¹ * (GlobalTheory.DFrame.rho D ι x.1 (σ' x.1 : D.host.E))⁻¹) *
      (r x.1 k * ι (TaylorLogMetric.embT D (s.iT i.1) (a x.1 k))) := fun k => by ring
  rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, hsum']
  by_cases h : s.iT i.1 = tauPl D x.1
  · rw [if_pos h, TaylorLogMetric.chgB, if_pos h.symm]
    simp only [h]
    set tp := tauPl D x.1 with htp
    have hm : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin m) D.host.E),
        Q.map (TaylorLogMetric.tauEmb D lm tp) = Q.map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      intro m Q; ext u v; simp [hι]
    have hinv : ((P tp).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)))⁻¹ =
        ((P tp)⁻¹).map ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D tp)) := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x.1)), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hm, hm, hinv]
    clear e hsum' hJ hsum hm hinv
    have h1 := hσ x.1
    have h2 := hσ' x.1
    simp only [GlobalTheory.DFrame.rho, RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1 h2 ⊢
    simp only [Matrix.map_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← htp] at h1 h2 ⊢
    field_simp
    try ring
  · rw [if_neg h, TaylorLogMetric.chgB, if_neg (fun e => h e.symm)]
    simp

end GlobalTheory.DFrame
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

open GlobalTheory.SmGL.EmptyBlocks GlobalTheory.SmGL.Exponents

namespace GlobalTheory.EigenSupport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jac_mk {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (e : (a : α) × m a ≃ n) (π : Representation ℂ (GL n k) V) (g : Levi k m) (v : V) :
    GlobalTheory.SmGL.jac e π g (Submodule.Quotient.mk v) =
      (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk (π (leviEmb k e g) v) : Jacquet π (unipRad k e)) := rfl

theorem jacB_mk {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (t : n → kˣ) (v : V) :
    jacB π t (Submodule.Quotient.mk v) =
      (((deltaHalf k (fun _ : n => Unit) (leviTorus k n t))⁻¹ : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (π (leviEmb k (points n) (leviTorus k n t)) v) : Jacquet π (unipB k n)) := rfl

theorem leviTorus_eq {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] (t : n → kˣ) :
    leviTorus k n t = torusToLevi k (points n) t := by
  funext j; ext a b
  rw [val_torusToLevi]
  simp [leviTorus, points, Matrix.diagonal]

theorem eq_torusToLevi (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    g = torusToLevi k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) (fun j => Matrix.GeneralLinearGroup.det (g j)) := by
  funext j; ext a b
  rw [val_torusToLevi]
  fin_cases a; fin_cases b
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

theorem deltaHalf_eq (n : ℕ) (g : Levi k (fun _ : Fin n => Fin 1)) :
    deltaHalf k (fun _ : Fin n => Fin 1) g =
      deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (fun j => Matrix.GeneralLinearGroup.det (g j))) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => by simp), modExp_fin (fun _ : Fin n => Unit) (fun _ => by simp)]
  exact congrArg _ (congrFun ((leviTorus k (Fin n)).symm_apply_apply (fun j => Matrix.GeneralLinearGroup.det (g j))) a).symm

theorem inSupport_of_eigenform (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ)
    (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t y, l (jacB π t y) = (GlobalTheory.SmGL.torusChar ψ t : ℂ) * l y) (i : Fin n) : InSupport π (ψ i) := by
  let f := Equiv.sigmaUnique (Fin n) fun _ : Fin n => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h : unipRad k f = unipB k (Fin n) := unipRad_eq k f hmono
  let l' : Jacquet π (unipRad k f) →ₗ[ℂ] ℂ :=
    (twKer π (unipRad k f) 1).liftQ (l ∘ₗ (twKer π (unipB k (Fin n)) 1).mkQ) (by
      rw [h]; intro x hx
      simp [(Submodule.Quotient.mk_eq_zero _).mpr hx])
  have hl' : ∀ v : V, l' (Submodule.Quotient.mk v) = l (Submodule.Quotient.mk v) := fun v => rfl
  let χ : Levi k (fun _ : Fin n => Fin 1) →* ℂˣ := leviChar _ ψ
  have key : ∀ (g : Levi k (fun _ : Fin n => Fin 1)) (v : V),
      l' (GlobalTheory.SmGL.jac f π g (Submodule.Quotient.mk v)) = (χ g : ℂ) * l' (Submodule.Quotient.mk v) := by
    intro g v
    set t : Fin n → kˣ := fun j => Matrix.GeneralLinearGroup.det (g j) with ht
    have h1 := hl t (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n)))
    rw [jacB_mk, map_smul, leviTorus_eq, leviEmb_torusToLevi, ← leviTorus_eq] at h1
    have hEmb : leviEmb k f g = diagT k (Fin n) t := by
      conv_lhs => rw [eq_torusToLevi n g]
      exact leviEmb_torusToLevi k f t
    rw [jac_mk, map_smul, hl', hl', deltaHalf_eq n g, hEmb, ← ht]
    have hc : (χ g : ℂ) = (GlobalTheory.SmGL.torusChar ψ t : ℂ) := by
      simp [χ, leviChar_apply, GlobalTheory.SmGL.torusChar_apply, t]
    rw [hc, ← h1]
  refine ⟨n, fun _ => 1, f, i, rfl, ℂ, inferInstance, inferInstance, ofChar χ, isIrreducible_ofChar χ, ?_, ?_⟩
  · refine IsSubquotient.of_surjective ⟨l', fun g => ?_⟩ ?_
    · apply Submodule.linearMap_qext
      ext v
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [key, ofChar_apply]
    · obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
        by_contra hc; push_neg at hc; exact hl0 (LinearMap.ext hc)
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      intro c
      refine ⟨(c / l (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, ?_⟩
      show l' _ = c
      rw [map_smul, hl', smul_eq_mul, div_mul_cancel₀ _ hx]
  · intro g y
    rw [ofChar_apply]
    simp [χ, leviChar_apply, Pi.mulSingle_apply, apply_ite, Finset.prod_ite_eq']

end GlobalTheory.EigenSupport

theorem GlobalTheory.EigenSupport.inSupport_of_torus_eigenform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 → (∀ t y, l (jacB π t y) = (GlobalTheory.SmGL.torusChar ψ t : ℂ) * l y) → ∀ i, InSupport π (ψ i) := by
  intro k _ _ _ _ n V _ _ π ψ l hl0 hl i
  exact GlobalTheory.EigenSupport.inSupport_of_eigenform n V π ψ l hl0 hl i
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (Formalism.ConjugateSelfDual.G F Ω)), IsOpen (U : Set (Formalism.ConjugateSelfDual.G F Ω)) → ∃ N : Subgroup (Formalism.ConjugateSelfDual.G F Ω), N.Normal ∧ IsOpen (N : Set (Formalism.ConjugateSelfDual.G F Ω)) ∧ N.FiniteIndex ∧ N ≤ U := by
  first | exact @GlobalTheory.OpenNormal.exists_open_normal_le | exact GlobalTheory.OpenNormal.exists_open_normal_le | (intros; apply GlobalTheory.OpenNormal.exists_open_normal_le <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), Formalism.ConjugateSelfDual.IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  first | exact @GlobalTheory.AboveL.exists_isPlaceOver_of_tower | exact GlobalTheory.AboveL.exists_isPlaceOver_of_tower | (intros; apply GlobalTheory.AboveL.exists_isPlaceOver_of_tower <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_open_galoisSubgroup_trace_ne_zero : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a → ∀ r : Formalism.ConjugateSelfDual.G K Ω →* GL (Fin a) (Qbar l), Continuous r → ∃ N : Subgroup (Formalism.ConjugateSelfDual.G K Ω), IsOpen (N : Set (Formalism.ConjugateSelfDual.G K Ω)) ∧ ∀ n ∈ N, (r n).val.trace ≠ 0 := by
  first | exact @GlobalTheory.AboveL.exists_open_trace_ne_zero | exact GlobalTheory.AboveL.exists_open_trace_ne_zero | (intros; apply GlobalTheory.AboveL.exists_open_trace_ne_zero <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.InertCompare

section Emb

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom

def rhoH (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem rhoH_apply (τ : D.what₂.Tau) (x : D.host.E) : rhoH D lam τ x = lamC lam (embT D τ x) := by
  unfold lamC
  rw [dite_eq_left (embT_mem D τ x)]
  rfl

theorem coe_rhoH (τ : D.what₂.Tau) : (rhoH D lam τ : D.host.E → ℂ_[l]) = tauEmb D lam τ :=
  funext fun x => rhoH_apply D lam τ x

def rhoC (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] := (rhoH D lam τ).comp (D.host.conj : D.host.E →+* D.host.E)

end Emb

def SamePrime {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ ρ' : E →+* ℂ_[l]) : Prop :=
  ∀ a : 𝓞 E, ‖ρ (a : E)‖ < 1 ↔ ‖ρ' (a : E)‖ < 1

theorem tauPl_bijective (D : D7) : Function.Bijective (tauPl D) := by
  have hinj := D.R.toFrame.iota_bijective.1
  have hP := factPlaces D.R.toFrame
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have h1 : plGG D (b, t) = plGG D (b', t') := congrArg Subtype.val (D.eTau.symm.injective h)
    cases b <;> cases b' <;> simp only [plGG, if_true, if_false, Bool.false_eq_true] at h1
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
    · exact absurd h1 (hP.2 _ _)
    · exact absurd h1.symm (hP.2 _ _)
    · rw [show t = t' from hinj (congrArg Prod.snd h1)]
  · intro τ
    rcases (hP.1 _).1 (D.eTau τ).2 with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨(false, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])
    · refine ⟨(true, t), ?_⟩
      unfold tauPl
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext (by simp [plGG, ht])

def plEquiv (D : D7) : (Bool × HH D) ≃ D.what₂.Tau := Equiv.ofBijective _ (tauPl_bijective D)

end GlobalTheory.InertCompare
end
end

section

noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Mem

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]

def unramOff (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (Chr F E L) :=
  ⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)

def IsTwist (S : Set ℕ) (x : Chr F E L) : Prop :=
  x ∈ finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ∧
    x ∈ ⨅ v : HeightOneSpectrum (𝓞 F), unramOff F E L S v

end Mem

end GlobalTheory.ColPeriodCompare
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.columnField_ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok → ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  first | exact @GlobalTheory.ColumnField.ramificationIdxIn_eq_one | exact GlobalTheory.ColumnField.ramificationIdxIn_eq_one | (intros; apply GlobalTheory.ColumnField.ramificationIdxIn_eq_one <;> assumption)
end
