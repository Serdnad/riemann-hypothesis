module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem CotangentBasisInPrime.proof : CotangentBasisInPrime.Statement := by
  intro T _ _ P _

  let g : P → maximalIdeal (Localization.AtPrime P) := fun x =>
    ⟨algebraMap T _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P (x : T)).2 x.2⟩
  let v : P → CotangentSpace (Localization.AtPrime P) := fun x => (maximalIdeal _).toCotangent (g x)
  have hspan : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range v) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := (maximalIdeal (Localization.AtPrime P)).toCotangent_surjective z
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective P.primeCompl (y : Localization.AtPrime P)
    simp only at hxs
    have hx : x ∈ P :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P x s).1 (hxs ▸ y.2)
    have hy : y = IsLocalization.mk' (Localization.AtPrime P) (1 : T) s • g ⟨x, hx⟩ := by
      ext
      simp only [g, Submodule.coe_smul, smul_eq_mul, ← hxs]
      rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
    rw [hy, map_smul, ← algebraMap_smul (ResidueField (Localization.AtPrime P))]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField (Localization.AtPrime P)) v
  have : Finite κ := hli.finite_of_isNoetherian
  let e := Finite.equivFin κ
  let w := (v ∘ a) ∘ e.symm
  have hliw : LinearIndependent (ResidueField (Localization.AtPrime P)) w :=
    hli.comp e.symm e.symm.injective
  have hspw : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) = ⊤ := by
    rw [show Set.range w = Set.range (v ∘ a) from e.symm.surjective.range_comp _, hsp, hspan]
  let G : Fin (Nat.card κ) → maximalIdeal (Localization.AtPrime P) := fun i => g (a (e.symm i))
  have hsum : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      (maximalIdeal _).toCotangent (∑ i, c i • G i) = ∑ i, residue _ (c i) • w i := by
    intro c

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rfl
  have hcoe : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      ((∑ i, c i • G i : maximalIdeal (Localization.AtPrime P)) : Localization.AtPrime P) =
        ∑ i, c i * algebraMap T _ (a (e.symm i) : T) := by
    intro c
    simp [G, g]
  refine ⟨Nat.card κ, fun i => (a (e.symm i) : T), fun i => (a (e.symm i)).2, ?_, ?_⟩
  · intro y hy
    have hz : (maximalIdeal _).toCotangent ⟨y, hy⟩ ∈
        Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) := by
      rw [hspw]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    choose c' hc' using fun i => residue_surjective (R := Localization.AtPrime P) (c i)
    have hdiff : (maximalIdeal _).toCotangent (⟨y, hy⟩ - ∑ i, c' i • G i) = 0 := by
      rw [map_sub, hsum, ← hc]
      simp [hc']
    rw [Ideal.toCotangent_eq_zero, Submodule.coe_sub, hcoe] at hdiff
    rw [show y = (y - ∑ i, c' i * algebraMap T _ (a (e.symm i) : T)) +
        ∑ i, c' i * algebraMap T _ (a (e.symm i) : T) by ring]
    refine add_mem (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left (Ideal.sum_mem _ fun i _ => ?_))
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro c hc i
    have h0 : (maximalIdeal _).toCotangent (∑ i, c i • G i) = 0 := by
      rw [Ideal.toCotangent_eq_zero, hcoe]; exact hc
    rw [hsum] at h0
    exact (residue_eq_zero_iff _).1 (Fintype.linearIndependent_iff.1 hliw _ h0 i)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

theorem LengthLocalizedLocalized.isLocalization_atPrime_map (B : Type u) [CommRing B] (P Q : Ideal B)
    [hP : P.IsPrime] [Q.IsPrime] [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime] (hPQ : P ≤ Q) :
    IsLocalization P.primeCompl (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) := by
  have h : Ideal.under B (P.map (algebraMap B (Localization.AtPrime Q))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hP
      (Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP))
  have key : IsLocalization ((P.map (algebraMap B (Localization.AtPrime Q))).comap
        (algebraMap B (Localization.AtPrime Q))).primeCompl
      (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime Q.primeCompl _
  rw [Ideal.under] at h
  have e : P.primeCompl = ((P.map (algebraMap B (Localization.AtPrime Q))).comap
      (algebraMap B (Localization.AtPrime Q))).primeCompl :=
    Submonoid.ext fun x => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, h]
  rw [e]
  exact key

theorem LengthLocalizedLocalized.proof : LengthLocalizedLocalized.Statement.{u, v} := by
  intro B _ P Q _ _ _ M _ _ hPQ
  have hloc := LengthLocalizedLocalized.isLocalization_atPrime_map B P Q hPQ

  let σ : Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))) ≃ₐ[B]
      Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl _ _
  let : Algebra (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) := σ.toRingHom.toAlgebra
  let : Module (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    Module.compHom _ (algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P))
  have : IsScalarTower (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    ⟨fun r l x => by
      show (r • l) • x = algebraMap _ (Localization.AtPrime P) r • (l • x)
      rw [Algebra.smul_def, mul_smul]⟩
  have : IsScalarTower B (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule P.primeCompl M) :=
    ⟨fun b r x => by
      show algebraMap _ (Localization.AtPrime P) (b • r) • x =
        b • (algebraMap _ (Localization.AtPrime P) r • x)
      rw [Algebra.smul_def, map_mul, mul_smul]
      rw [show algebraMap (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
          (Localization.AtPrime P) (algebraMap B _ b) = algebraMap B (Localization.AtPrime P) b from
          σ.commutes b, algebraMap_smul]⟩

  have hf : IsBaseChange (Localization.AtPrime Q) (LocalizedModule.mkLinearMap Q.primeCompl M) :=
    IsLocalizedModule.isBaseChange Q.primeCompl _ _
  have hg : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl
        (LocalizedModule Q.primeCompl M)) :=
    IsLocalizedModule.isBaseChange (P.map (algebraMap B (Localization.AtPrime Q))).primeCompl _ _
  have hfg := hf.comp hg
  have h0 : IsBaseChange (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q))))
      (LocalizedModule.mkLinearMap P.primeCompl M) :=
    IsLocalizedModule.isBaseChange P.primeCompl _ _
  rw [← (h0.equiv.symm.trans hfg.equiv).length_eq]
  exact Module.length_eq_of_surjective σ.surjective

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

open scoped ContDiff
open Metric

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem BrouwerFixedPoint.smooth_of_changeOfVariablesDegree
    (hL : ChangeOfVariablesDegree.Statement) (n : ℕ) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgb : ∀ x, ‖g x‖ ≤ 1) : ∃ x, g x = x := by
  by_contra hne
  push Not at hne
  have hcont : ContinuousOn (fun x => ‖x - g x‖) (closedBall (0 : Fin n → ℝ) 2) :=
    (continuous_id.sub hg.continuous).norm.continuousOn
  obtain ⟨x₀, -, hmin⟩ := (isCompact_closedBall (0 : Fin n → ℝ) 2).exists_isMinOn
    (nonempty_closedBall.2 zero_le_two) hcont
  have hε : 0 < ‖x₀ - g x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀).symm)
  set δ := min ‖x₀ - g x₀‖ 1 with hδ_def
  have hδ : 0 < δ := lt_min hε one_pos

  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨2, 3, two_pos, by norm_num⟩
  let φ : (Fin n → ℝ) → Fin n → ℝ := fun x => x - χ x • g x
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.sub (χ.contDiff.smul hg)
  have hφc : HasCompactSupport (fun x => φ x - x) := by
    have h : (fun x => φ x - x) = -((fun x => χ x) • g) := by
      funext x; simp [φ]
    rw [h]
    exact χ.hasCompactSupport.smul_right.neg
  have hφδ : ∀ x, δ ≤ ‖φ x‖ := by
    intro x
    by_cases hx : ‖x‖ ≤ 2
    · have hχ : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)
      have h2 : ‖x₀ - g x₀‖ ≤ ‖x - g x‖ :=
        isMinOn_iff.1 hmin x (mem_closedBall_zero_iff.2 hx)
      simp only [φ, hχ, one_smul]
      exact (min_le_left _ _).trans h2
    · push Not at hx
      have h1 : ‖χ x • g x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
        exact mul_le_one₀ χ.le_one (norm_nonneg _) (hgb x)
      have h3 : ‖x‖ - ‖χ x • g x‖ ≤ ‖φ x‖ := norm_sub_norm_le _ _
      have h4 : δ ≤ 1 := min_le_right _ _
      linarith

  let ψ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hzero : ∀ x, ψ (φ x) = 0 := by
    intro x
    by_contra h
    have hmem : φ x ∈ ball (0 : Fin n → ℝ) δ := by
      rw [← ψ.support_eq]; exact h
    rw [mem_ball_zero_iff] at hmem
    exact absurd (hφδ x) (not_le.2 hmem)
  have hL' := hL n φ hφ hφc ψ ψ.contDiff ψ.hasCompactSupport
  simp only [hzero, zero_mul, MeasureTheory.integral_zero] at hL'
  exact (ψ.integral_pos (μ := MeasureTheory.volume)).ne hL'

theorem BrouwerFixedPoint.proof (hL : ChangeOfVariablesDegree.Statement) :
    BrouwerFixedPoint.Statement := by
  intro n f hf hmaps
  by_contra hne
  push Not at hne
  set B := closedBall (0 : Fin n → ℝ) 1 with hB_def
  have hB : IsCompact B := isCompact_closedBall _ _
  have hcont : ContinuousOn (fun x => ‖f x - x‖) B := (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hB.exists_isMinOn (nonempty_closedBall.2 zero_le_one) hcont
  have hε : 0 < ‖f x₀ - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀ hx₀))

  let P : (Fin n → ℝ) → Fin n → ℝ := fun x i => max (min (x i) 1) (-1)
  have hPB : ∀ x, P x ∈ B := by
    intro x
    rw [hB_def, mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩
  have hPid : ∀ x ∈ B, P x = x := by
    intro x hx
    funext i
    have hi : |x i| ≤ 1 := by
      have h := (norm_le_pi_norm x i).trans (mem_closedBall_zero_iff.1 hx)
      rwa [Real.norm_eq_abs] at h
    rw [abs_le] at hi
    simp only [P, min_eq_left hi.2, max_eq_left hi.1]
  have hPlip : ∀ x y, dist (P x) (P y) ≤ dist x y := by
    intro x y
    refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
    calc dist (P x i) (P y i) = |max (min (x i) 1) (-1) - max (min (y i) 1) (-1)| :=
          Real.dist_eq _ _
      _ ≤ |min (x i) 1 - min (y i) 1| := abs_max_sub_max_le_abs _ _ _
      _ ≤ max |x i - y i| |1 - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = dist (x i) (y i) := by simp [Real.dist_eq]
      _ ≤ dist x y := dist_le_pi_dist x y i

  let F : (Fin n → ℝ) → Fin n → ℝ := fun x => f (P x)
  have hFu : UniformContinuous F := by
    have hfu : UniformContinuousOn f B := hB.uniformContinuousOn_of_continuous hf
    rw [Metric.uniformContinuous_iff]
    intro η hη
    obtain ⟨d, hd, hfd⟩ := Metric.uniformContinuousOn_iff.1 hfu η hη
    exact ⟨d, hd, fun {a b} hab => hfd _ (hPB a) _ (hPB b) ((hPlip a b).trans_lt hab)⟩
  have hFB : ∀ x, ‖F x‖ ≤ 1 := fun x => mem_closedBall_zero_iff.1 (hmaps (hPB x))

  set a := ‖f x₀ - x₀‖ / 3 with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨G, hG, hGF⟩ := hFu.exists_contDiff_dist_le ha
  set c := (1 + a)⁻¹ with hc_def
  have hc : c * (1 + a) = 1 := inv_mul_cancel₀ (by positivity)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hGb : ∀ x, ‖G x‖ ≤ 1 + a := by
    intro x
    have h1 : ‖G x‖ ≤ ‖F x‖ + ‖G x - F x‖ := norm_le_norm_add_norm_sub' _ _
    have h2 : ‖G x - F x‖ < a := by rw [← dist_eq_norm]; exact hGF x
    linarith [hFB x]
  have hgb : ∀ x, ‖c • G x‖ ≤ 1 := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg hc0.le]
    calc c * ‖G x‖ ≤ c * (1 + a) := mul_le_mul_of_nonneg_left (hGb x) hc0.le
      _ = 1 := hc
  obtain ⟨x, hx⟩ := BrouwerFixedPoint.smooth_of_changeOfVariablesDegree hL n (fun x => c • G x)
    (hG.const_smul c) hgb
  have hx' : c • G x = x := hx
  have hxB : x ∈ B := by
    rw [hB_def, mem_closedBall_zero_iff, ← hx']
    exact hgb x
  have hFx : F x = f x := by simp only [F, hPid x hxB]
  have h1 : ‖f x - G x‖ < a := by
    rw [← hFx, ← dist_eq_norm, dist_comm]; exact hGF x
  have h2 : ‖G x - x‖ ≤ a := by
    have h : G x - x = (1 - c) • G x := by
      rw [sub_smul, one_smul, hx']
    rw [h, norm_smul, Real.norm_of_nonneg (by linarith)]
    have := hGb x
    nlinarith
  have h3 : ‖f x - x‖ ≤ ‖f x - G x‖ + ‖G x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : ‖f x₀ - x₀‖ ≤ ‖f x - x‖ := isMinOn_iff.1 hmin x hxB
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter

noncomputable section

variable {n d : ℕ}

theorem lift_eval_comp_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) :
    (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq).comp
        (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom =
      MvPolynomial.eval (A.mulVec x) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback]
  · intro i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
      GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem fibre_finite {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A) (y : Fin d → ℂ) :
    (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := by
  classical
  have hint : ∀ j : Fin n, (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.IsIntegralElem
      (Ideal.Quotient.mk J (X j)) := fun j => hA.finite.to_isIntegral _
  choose p hpm hp using hint
  refine (Set.Finite.pi (t := fun j => {z : ℂ | ((p j).map (MvPolynomial.eval y)).IsRoot z})
    fun j => Polynomial.finite_setOfPred_isRoot ((hpm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxy⟩ j -
  have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) (hp j)
  rw [Polynomial.hom_eval₂, lift_eval_comp_projHom J A hx, hxy, map_zero] at h
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using h

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def DominantFibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) →
    Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)) →
    ∃ (e : ℕ) (Δ : MvPolynomial (Fin d) ℂ), Δ ≠ 0 ∧ ∀ w : Fin d → ℂ, eval w Δ ≠ 0 →
      {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i}.encard ≤ e

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def FiniteProjectionsContainOpen.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      ∃ W : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen W ∧ W.Nonempty ∧
        W ⊆ {A | IsFiniteProjection J A}

def FiniteProjectionsGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      (∃ W : Set (Matrix (Fin d) (Fin n) ℂ), IsZariskiOpen W ∧ W.Nonempty ∧
        W ⊆ {A | IsFiniteProjection J A}) ∧
      (∀ D : Set (Matrix (Fin d) (Fin n) ℂ), D ⊆ orthoRows d n → orthoRows d n ⊆ closure D →
        ∃ A ∈ D, IsFiniteProjection J A) ∧
      (∀ (m : ℕ) (F : Fin m → Matrix.unitaryGroup (Fin n) ℂ),
        ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (k : Fin m) (s : Fin d ↪ Fin n),
          IsFiniteProjection J (((F k : Matrix (Fin n) (Fin n) ℂ) * U).submatrix s id))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def IsolatedFibreOpenPoly.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) → x ∈ zeroSet P →
    (∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x) →
    ∀ W' ∈ 𝓝 x, (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ W') ∈
      𝓝 (fun i => eval x (p i))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

def isolatedFibrePts {n m : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (z : Fin m → ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ (∀ i, eval x (Q i) = z i) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, (∀ i, eval x' (Q i) = z i) → x' = x}

def IsolatedPointsCount.Statement : Prop :=
  ∀ (n m : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (Q : Fin m → MvPolynomial (Fin n) ℂ),
    ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts J Q z).encard ≤ N

end

end GroundTheory.Heights₂.Heights
end
