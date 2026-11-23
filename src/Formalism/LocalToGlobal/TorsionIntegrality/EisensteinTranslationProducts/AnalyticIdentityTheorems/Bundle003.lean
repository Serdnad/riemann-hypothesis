module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

section

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

theorem elliptic_entire_const : EllipticEntire := by
  intro L f hf hper z
  have key : ∀ x : ℂ, ∃ ω ∈ L.lattice, ‖x - ω‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := by
    intro x
    have hx := L.basis.sum_repr x
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hx
    refine ⟨(⌊L.basis.repr x 0⌋ : ℂ) * L.ω₁ + (⌊L.basis.repr x 1⌋ : ℂ) * L.ω₂,
      PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, ?_⟩
    generalize L.basis.repr x 0 = a at hx ⊢
    generalize L.basis.repr x 1 = b at hx ⊢
    subst hx
    have e : a • L.ω₁ + b • L.ω₂ - ((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂)
        = ((Int.fract a : ℝ) : ℂ) * L.ω₁ + ((Int.fract b : ℝ) : ℂ) * L.ω₂ := by
      simp only [Complex.real_smul, Int.fract]; push_cast; ring
    rw [e]
    have hfr : ∀ (r : ℝ) (v : ℂ), ‖((Int.fract r : ℝ) : ℂ) * v‖ ≤ ‖v‖ := by
      intro r v
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    exact (norm_add_le _ _).trans (add_le_add (hfr a _) (hfr b _))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (‖L.ω₁‖ + ‖L.ω₂‖)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hb : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨ω, hω, hxω⟩ := key x
    have : f x = f (x - ω) := by
      have := hper ω hω (x - ω)
      rwa [sub_add_cancel] at this
    rw [this]
    exact hC _ (by simpa using hxω)
  exact hf.apply_eq_apply_of_bounded hb z 0

namespace Elliptic

lemma eq_of_eventuallyEq_nhdsNE {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z :=
  tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

lemma tendsto_add_nhdsNE (z ω : ℂ) : Tendsto (fun w : ℂ => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_add_const ω).tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun h => hw (add_right_cancel h)

end Elliptic

theorem elliptic_no_pole_const : EllipticNoPole := by
  intro L f hmer hper hord
  have hM : MeromorphicOn f Set.univ := fun z _ => hmer z
  set g := toMeromorphicNFOn f Set.univ with hg_def
  have heq : ∀ z, g =ᶠ[𝓝[≠] z] f := fun z =>
    hM.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han : ∀ z, AnalyticAt ℂ g z := fun z => by
    have hnf := meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ z)
    rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_congr (heq z)]
    exact hord z
  have hcont : ∀ z, ContinuousAt g z := fun z => (han z).continuousAt
  have hdiff : Differentiable ℂ g := fun z => (han z).differentiableAt
  have hpg : IsPeriodic L g := by
    intro ω hω z
    have hc1 : ContinuousAt (fun w => g (w + ω)) z :=
      show ContinuousAt (g ∘ fun w => w + ω) z from
        (hcont (z + ω)).comp_of_eq (continuous_add_const ω).continuousAt rfl
    have h1 : ∀ᶠ w in 𝓝[≠] z, g (w + ω) = f (w + ω) :=
      (Elliptic.tendsto_add_nhdsNE z ω).eventually (heq (z + ω))
    have h2 : (fun w => g (w + ω)) =ᶠ[𝓝[≠] z] g := by
      filter_upwards [h1, heq z] with w hw1 hw2
      rw [hw1, hper ω hω w, hw2]
    exact Elliptic.eq_of_eventuallyEq_nhdsNE hc1 (hcont z) h2
  refine ⟨g 0, fun z hz => ?_⟩
  rw [← elliptic_entire_const L g hdiff hpg z]
  exact Elliptic.eq_of_eventuallyEq_nhdsNE hz (hcont z) (heq z).symm

end Formalism.L2.Th1.F
end
end

section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace SigmaLog

lemma hasDerivAt_wFactor (l z : ℂ) :
    HasDerivAt (wFactor l)
      (-(1 / l) * Complex.exp (z / l + z ^ 2 / (2 * l ^ 2))
        + (1 - z / l) * (Complex.exp (z / l + z ^ 2 / (2 * l ^ 2)) * (1 / l + 2 * z / (2 * l ^ 2)))) z := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z / l) (-(1 / l)) z := by
    simpa using ((hasDerivAt_id z).div_const l).const_sub 1
  have h2 : HasDerivAt (fun z : ℂ => z / l + z ^ 2 / (2 * l ^ 2)) (1 / l + 2 * z / (2 * l ^ 2)) z := by
    have := ((hasDerivAt_id z).div_const l).fun_add ((hasDerivAt_pow 2 z).div_const (2 * l ^ 2))
    simpa using this
  exact h1.mul h2.cexp

lemma differentiable_wFactor (l : ℂ) : Differentiable ℂ (wFactor l) :=
  fun z => (hasDerivAt_wFactor l z).differentiableAt

lemma wFactor_ne_zero {l z : ℂ} (h : z ≠ l) : wFactor l z ≠ 0 := by
  unfold wFactor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : l = 0
  · simp [hl]
  · intro h0
    apply h
    field_simp at h0
    linear_combination -h0

lemma logDeriv_wFactor {l z : ℂ} (h : z ≠ l) :
    logDeriv (wFactor l) z
      = (1 / (z - l) + 1 / l + z / l ^ 2) - (if l = 0 then 1 / z else 0) := by
  rw [logDeriv_apply, (hasDerivAt_wFactor l z).deriv]
  by_cases hl : l = 0
  · simp [hl, wFactor]
  · have h1 : z - l ≠ 0 := sub_ne_zero.mpr h
    have h2 : 1 - z / l ≠ 0 := by
      intro h0
      apply h
      field_simp at h0
      linear_combination -h0
    have h3 : l - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have he := Complex.exp_ne_zero (z / l + z ^ 2 / (2 * l ^ 2))
    rw [if_neg hl, wFactor, sub_zero, div_eq_iff (mul_ne_zero h2 he)]
    field_simp
    ring

end SigmaLog

open SigmaLog in
theorem sigmaLogDeriv_of (h1 : SigmaProdLU) (h2 : SigmaSummable) (h3 : ZetaSummable) :
    SigmaLogDeriv := by
  intro L z hz
  have hne : ∀ l : L.lattice, z ≠ (l : ℂ) := fun l h => hz (h ▸ l.2)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ L.lattice.zero_mem)
  set P : ℂ → ℂ := fun z => ∏' l : L.lattice, wFactor (l : ℂ) z with hP

  have hPne : P z ≠ 0 := by
    have := tprod_one_add_ne_zero_of_summable (f := fun l : L.lattice => wFactor (l : ℂ) z - 1)
      (fun l => by simpa using wFactor_ne_zero (hne l)) (h2 L z)
    simpa [hP] using this

  have hPd : DifferentiableOn ℂ P Set.univ := by
    have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp (h1 L)
    refine ht.differentiableOn (.of_forall fun s => ?_) isOpen_univ
    exact DifferentiableOn.fun_finsetProd fun i _ => (differentiable_wFactor _).differentiableOn
  have hPdz : DifferentiableAt ℂ P z := (hPd z (Set.mem_univ z)).differentiableAt Filter.univ_mem

  have hc : HasSum (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0) (1 / z) := by
    have : (fun l : L.lattice => if (l : ℂ) = 0 then 1 / z else 0)
        = fun l : L.lattice => if l = 0 then 1 / z else 0 := by
      funext l; simp
    rw [this]
    exact hasSum_ite_eq 0 (1 / z)
  have hs : HasSum (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z) (wZeta L z - 1 / z) := by
    have := (h3 L z).hasSum.sub hc
    have he : (fun l : L.lattice => logDeriv (wFactor (l : ℂ)) z)
        = fun l : L.lattice => (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
            - (if (l : ℂ) = 0 then 1 / z else 0) := by
      funext l
      exact logDeriv_wFactor (hne l)
    rw [he]
    exact this
  have hlog : logDeriv P z = wZeta L z - 1 / z := by
    have := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ z)
      (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z) (fun l => wFactor_ne_zero (hne l))
      (fun l => (differentiable_wFactor _).differentiableOn) hs.summable
      (h1 L).multipliableLocallyUniformlyOn hPne
    rw [hs.tsum_eq] at this
    exact this
  have hPderiv : HasDerivAt P ((wZeta L z - 1 / z) * P z) z := by
    have := hPdz.hasDerivAt
    rw [← hlog, logDeriv_apply, div_mul_cancel₀ _ hPne]
    exact this
  have := (hasDerivAt_id z).mul hPderiv
  have he : wZeta L z * wSigma L z = 1 * P z + id z * ((wZeta L z - 1 / z) * P z) := by
    simp only [wSigma, id, hP]
    field_simp
    ring
  rw [he]
  exact this

end Formalism.L2.Th1.F
end
end

section

noncomputable section

namespace Formalism.L2.Th1.F

theorem sigmaOrder_of (he : SigmaEntire) (hz : SigmaZero) (hs : SigmaSimple) : SigmaOrder := by
  intro L a b z ha
  classical
  set f : ℂ → ℂ := fun w => wSigma L (a * w + b) with hfdef
  have hlin : Differentiable ℂ (fun w : ℂ => a * w + b) :=
    (differentiable_id.const_mul a).add_const b
  have hfd : Differentiable ℂ f := (he L).comp hlin
  have hfa : AnalyticAt ℂ f z := hfd.analyticAt z
  have hder : HasDerivAt f (deriv (wSigma L) (a * z + b) * (a * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => a * w + b) (a * 1) z :=
      ((hasDerivAt_id z).const_mul a).add_const b
    exact ((he L) (a * z + b)).hasDerivAt.comp z h1
  rw [hfa.meromorphicOrderAt_eq]
  split_ifs with hmem
  · have h0 : f z = 0 := (hz L (a * z + b)).2 hmem
    have hord : analyticOrderAt f z = ((1 : ℕ) : ℕ∞) := by
      rw [hfa.analyticOrderAt_eq_natCast]
      refine ⟨dslope f z, ?_, ?_, ?_⟩
      · have hon : DifferentiableOn ℂ (dslope f z) Set.univ :=
          (Complex.differentiableOn_dslope Filter.univ_mem).2 hfd.differentiableOn
        exact (differentiableOn_univ.1 hon).analyticAt z
      · rw [dslope_same, hder.deriv]
        exact mul_ne_zero ((hs L).2 _ hmem) (by simpa using ha)
      · filter_upwards with w
        rw [pow_one, sub_smul_dslope, h0, sub_zero]
    rw [hord]
    rfl
  · have hne : f z ≠ 0 := fun h => hmem ((hz L (a * z + b)).1 h)
    have hord : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.2 (Or.inr hne)
    rw [hord]
    rfl

end Formalism.L2.Th1.F
end
end
