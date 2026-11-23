module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZeroWindow.RightHalfWith
public import Formalism.PeriodIntegrals.Bundle002
public import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.ZW

open DirichletCharacter

lemma finsum_mem_le_of_subset' {s t : Set ℂ} (g : ℂ → ℝ) (hg : ∀ x, 0 ≤ g x) (ht : t.Finite)
    (hst : s ⊆ t) : ∑ᶠ x ∈ s, g x ≤ ∑ᶠ x ∈ t, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (ht.subset hst), finsum_mem_eq_finite_toFinset_sum _ ht]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.mpr hst) fun x _ _ => hg x

lemma finsum_mem_le_finsum_mem' {s : Set ℂ} (f g : ℂ → ℝ) (hs : s.Finite) (h : ∀ x ∈ s, f x ≤ g x) :
    ∑ᶠ x ∈ s, f x ≤ ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  exact Finset.sum_le_sum fun x hx => h x (hs.mem_toFinset.mp hx)

lemma ne_one_or_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    χ ≠ 1 ∨ N = 1 := by
  by_cases h : χ = 1
  · right
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hχ
    exact hχ.symm
  · exact Or.inl h

lemma log_mul_abs_add_two_nonneg (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Real.log (N * (|t| + 2)) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  apply Real.log_nonneg
  nlinarith [abs_nonneg t]

theorem zerosWindowWith_of (C : ℝ) (hR : RightHalfWith C) (hT : Transfer) :
    PI.ZerosWindowWith (2 * C) := by
  intro N _ χ hχ t
  have hχ' : χ ≠ 1 ∨ N = 1 := ne_one_or_of_isPrimitive hχ
  have hχi : χ⁻¹ ≠ 1 ∨ N = 1 := hχ'.imp (fun h h' => h (inv_eq_one.mp h')) id
  obtain ⟨hA, hAs⟩ := hR N χ hχ' t
  obtain ⟨hB, hBs⟩ := hR N χ⁻¹ hχi (-t)
  rw [abs_neg] at hBs
  have hZrA : ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re} ⊆ RightNear χ t :=
    fun ρ ⟨⟨_, h1, h2, h3⟩, h4⟩ => ⟨h4, h1, h2, h3⟩
  have hZl : ∀ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}, 1 - ρ ∈ RightNear χ⁻¹ (-t) := by
    rintro ρ ⟨⟨h0, h1, h2, h3⟩, h4⟩
    simp only [Set.mem_setOf_eq] at h4
    refine ⟨by simp; linarith, by simp; linarith, ?_, (hT N χ hχ ρ h0 h1 h3).1⟩
    simp only [Complex.sub_im, Complex.one_im, zero_sub]
    rw [show -ρ.im - -t = -(ρ.im - t) by ring, abs_neg]
    exact h2
  have hsplit : ZerosNear χ t = (ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re}) ∪ (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}) :=
    Set.ext fun ρ => ⟨fun h => (le_or_gt (1 / 2) ρ.re).imp (fun h' => ⟨h, h'⟩) (fun h' => ⟨h, h'⟩),
      fun h => h.elim (·.1) (·.1)⟩
  have hBimg : ((fun σ : ℂ => 1 - σ) '' RightNear χ⁻¹ (-t)).Finite := hB.image _
  have hZfin : (ZerosNear χ t).Finite := by
    rw [hsplit]
    refine (hA.subset hZrA).union (hBimg.subset fun ρ hρ => ⟨1 - ρ, hZl ρ hρ, by ring⟩)
  refine ⟨hZfin, ?_⟩
  have hdisj : Disjoint (ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re}) (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}) :=
    Set.disjoint_left.mpr fun ρ h1 h2 => absurd (show (1 / 2 : ℝ) ≤ ρ.re from h1.2) (not_le.mpr (show ρ.re < 1 / 2 from h2.2))
  have hfl : (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}).Finite := hZfin.subset Set.inter_subset_left
  rw [hsplit, finsum_mem_union hdisj (hZfin.subset Set.inter_subset_left) hfl]
  have e1 := finsum_mem_le_of_subset' (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
    (fun _ => Nat.cast_nonneg _) hA hZrA
  have e2 : ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      ∑ᶠ σ ∈ RightNear χ⁻¹ (-t), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) := by
    calc ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
        ≤ ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) : ℝ) :=
          finsum_mem_le_finsum_mem' _ _ hfl fun ρ hρ => by
            exact_mod_cast (hT N χ hχ ρ hρ.1.1 hρ.1.2.1 hρ.1.2.2.2).2
      _ = ∑ᶠ σ ∈ (fun σ : ℂ => 1 - σ) '' (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) :=
          (finsum_mem_image (f := fun σ => (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ))
            (g := fun σ : ℂ => 1 - σ) (s := ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2})
            (fun a _ b _ h => by simpa using h)).symm
      _ ≤ ∑ᶠ σ ∈ RightNear χ⁻¹ (-t), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) :=
          finsum_mem_le_of_subset' _ (fun _ => Nat.cast_nonneg _) hB (by
            rintro _ ⟨ρ, hρ, rfl⟩
            exact hZl ρ hρ)
  linarith

theorem rightHalf_of (C₁ C₂ : ℝ) (h₁ : RightChiWith C₁) (h₂ : RightOneWith C₂) :
    RightHalfWith (max C₁ C₂) := by
  intro N _ χ hχ t
  have hl := log_mul_abs_add_two_nonneg N t
  rcases hχ with h | h
  · obtain ⟨hf, hs⟩ := h₁ N χ h t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)⟩
  · obtain ⟨hf, hs⟩ := h₂ N χ h t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hl)⟩

end PI.ZW
end
end

section

noncomputable section

open Metric

namespace PI.ZW

lemma order_ne_top_of_ball {f : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hz : z ∈ closedBall c R) : analyticOrderAt f z ≠ ⊤ := by
  have hR : 0 ≤ R := dist_nonneg.trans (Metric.mem_closedBall.1 hz)
  refine hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
    (Metric.mem_closedBall_self hR) hz ?_
  rw [analyticOrderAt_eq_zero.2 (Or.inr hfc)]
  exact ENat.zero_ne_top

lemma divisor_eq_order {f : ℂ → ℂ} {c z : ℂ} {r R : ℝ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hfc : f c ≠ 0) (hrR : r ≤ R) (hz : z ∈ closedBall c r) :
    MeromorphicOn.divisor f (closedBall c r) z = (analyticOrderNatAt f z : ℤ) := by
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR hz
  have hm : MeromorphicOn f (closedBall c r) := (hf.mono (closedBall_subset_closedBall hrR)).meromorphicOn
  have hne := order_ne_top_of_ball hf hfc hzR
  rw [MeromorphicOn.divisor_apply hm hz, (hf z hzR).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hne]
  simp

theorem jensenCount : JensenCount := by
  intro f c M hf hfc hM1 hbd S hS
  have hR : |(19 / 10 : ℝ)| = 19 / 10 := abs_of_pos (by norm_num)
  have hf' : AnalyticOnNhd ℂ f (closedBall c |(19 / 10 : ℝ)|) := by rw [hR]; exact hf
  have hDnn : 0 ≤ MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf'
  have hfin : (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support.Finite :=
    (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).finiteSupport (isCompact_closedBall _ _)
  have hSD : ∀ u ∈ S, MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u =
      (analyticOrderNatAt f u : ℤ) ∧ 1 ≤ analyticOrderNatAt f u ∧ 0 < ‖c - u‖ ∧ ‖c - u‖ ≤ 37 / 20 := by
    intro u hu
    obtain ⟨hub, hfu⟩ := hS hu
    have hub' : u ∈ closedBall c (19 / 10) := closedBall_subset_closedBall (by norm_num) hub
    have hdiv := divisor_eq_order hf hfc le_rfl hub'
    have hne := order_ne_top_of_ball hf hfc hub'
    refine ⟨by rw [hR]; exact hdiv, ?_, ?_, ?_⟩
    · by_contra h0
      push_neg at h0
      have h00 : analyticOrderNatAt f u = 0 := by omega
      have hord : analyticOrderAt f u = 0 := by rw [← Nat.cast_analyticOrderNatAt hne, h00]; rfl
      rcases analyticOrderAt_eq_zero.1 hord with h | h
      · exact h (hf u hub')
      · exact h hfu
    · have : u ≠ c := by rintro rfl; exact hfc hfu
      exact norm_pos_iff.2 (sub_ne_zero.2 this.symm)
    · rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hub
  have hSsub : S ⊆ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support := by
    intro u hu
    obtain ⟨h1, h2, -, -⟩ := hSD u hu
    simp only [Function.mem_support, h1]
    exact_mod_cast (by omega : analyticOrderNatAt f u ≠ 0)
  have hSfin : S.Finite := hfin.subset hSsub
  refine ⟨hSfin, ?_⟩
  have hJ := AnalyticOnNhd.circleAverage_log_norm (R := 19 / 10) hf' hfc
  have hup : Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) ≤ Real.log M := by
    apply Real.circleAverage_mono_on_of_le_circle
    · exact MeromorphicOn.circleIntegrable_log_norm (hf'.mono sphere_subset_closedBall).meromorphicOn
    · intro x hx
      rw [hR] at hx
      by_cases h0 : f x = 0
      · rw [h0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM1
      · exact Real.log_le_log (norm_pos_iff.2 h0) (hbd x hx)
  set g : ℂ → ℝ := fun u => (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) *
    Real.log (19 / 10 * ‖c - u‖⁻¹) with hg
  have hgnn : ∀ u, 0 ≤ g u := by
    intro u
    by_cases hu : u ∈ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).support
    · have hdu : (0 : ℝ) ≤ (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|) u : ℝ) := by
        exact_mod_cast hDnn u
      have hin := (MeromorphicOn.divisor f (closedBall c |(19 / 10 : ℝ)|)).supportWithinDomain hu
      rw [hR] at hin
      have hcu : ‖c - u‖ ≤ 19 / 10 := by rw [norm_sub_rev, ← dist_eq_norm]; exact mem_closedBall.1 hin
      apply mul_nonneg hdu
      rcases (norm_nonneg (c - u)).eq_or_lt with h0 | h0
      · rw [← h0, inv_zero, mul_zero, Real.log_zero]
      · apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ h0]; linarith
    · simp only [Function.mem_support, not_not] at hu
      simp [hg, hu]
  have hgsupp : Function.support g ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    apply hu
    simp [hg, h0]
  have hfs : ∑ᶠ u, g u = ∑ u ∈ hfin.toFinset, g u := finsum_eq_sum_of_support_subset g hgsupp
  have hsub2 : hSfin.toFinset ⊆ hfin.toFinset := by
    intro u hu
    simp only [Set.Finite.mem_toFinset] at hu ⊢
    exact hSsub hu
  have hlow : ∑ u ∈ hSfin.toFinset, g u ≤ ∑ u ∈ hfin.toFinset, g u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun u _ _ => hgnn u
  have hLpos : 0 < Real.log ((19 / 10) / (37 / 20)) := Real.log_pos (by norm_num)
  have hterm : ∀ u ∈ hSfin.toFinset, (analyticOrderNatAt f u : ℝ) * Real.log ((19 / 10) / (37 / 20)) ≤ g u := by
    intro u hu
    rw [Set.Finite.mem_toFinset] at hu
    obtain ⟨h1, h2, h3, h4⟩ := hSD u hu
    simp only [hg, h1]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by norm_num)
    rw [← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) h3 h4
  have hfc0 : 0 < ‖f c‖ := norm_pos_iff.2 hfc
  have hM0 : 0 < M := by linarith
  rw [finsum_mem_eq_finite_toFinset_sum _ hSfin, le_div_iff₀ hLpos, Finset.sum_mul,
    Real.log_div hM0.ne' hfc0.ne']
  have hsum := Finset.sum_le_sum hterm
  have hJ' : ∑ᶠ u, g u = Real.circleAverage (fun x => Real.log ‖f x‖) c (19 / 10) - Real.log ‖f c‖ := by
    rw [hJ]; simp only [hg]; ring
  linarith

end PI.ZW
end
end
