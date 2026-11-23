module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.WeilBound.CoreStatements.FlagImmersions.IsPotentialSumPot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle004
public import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionConstantMetricLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology GlobalTheory.CompanionTheory.Ar.PB

theorem scale_le {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) : Real.exp (-(s ^ 2)⁻¹) ≤ s := by
  have h := Real.one_sub_inv_le_log_of_pos hs
  have hu : 0 < s⁻¹ := inv_pos.2 hs
  have e : (s ^ 2)⁻¹ = s⁻¹ ^ 2 := by rw [inv_pow]
  have hl : -(s ^ 2)⁻¹ ≤ Real.log s := by
    rw [e]
    nlinarith [sq_nonneg (s⁻¹ - 1 / 2)]
  calc Real.exp (-(s ^ 2)⁻¹) ≤ Real.exp (Real.log s) := Real.exp_le_exp.2 hl
    _ = s := Real.exp_log hs

theorem epsT_scale (C : ℝ) {s : ℝ} (hs : 0 < s) :
    epsT C (Real.exp (-(s ^ 2)⁻¹)) = -(2 * C) * (s * Real.log s) * s := by
  have h1 : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have h2 : Real.log ((s ^ 2)⁻¹) = -(2 * Real.log s) := by
    rw [Real.log_inv, Real.log_pow]
    push_cast
    ring
  unfold epsT
  rw [h1, h2]
  have hs2 : s ^ 2 ≠ 0 := by positivity
  field_simp

theorem epsT_small (C ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → |epsT C (Real.exp (-(s ^ 2)⁻¹))| ≤ ε * s := by
  have hc : ContinuousAt (fun x : ℝ => -(2 * C) * (x * Real.log x)) 0 :=
    (continuous_const.mul Real.continuous_mul_log).continuousAt
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc ε hε
  refine ⟨δ / 2, by positivity, fun s hs hsδ => ?_⟩
  have := h (x := s) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; linarith)
  simp only [Real.dist_eq, zero_mul, mul_zero, sub_zero] at this
  rw [epsT_scale C hs, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_right this.le hs.le

theorem potT_potential {e : ℕ} {σ : Type} (S : AnSys e σ) (a : σ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    IsPotential S.A (S.potT a t) :=
  isPotentialAdd _ _ _ (S.sing a).1 (isPotential_ofFun _ _ ((S.reg a).2.2 t h0 h1).1)

theorem psh_sum_potentials_small_parameter : ∀ (e : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (Fl : Set σ) (a' : σ) (c₀ abelian₂ : ℝ), 0 < c₀ → (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → (∀ t, IsPsh S.A (S.potT a' t + S.Θ.rsmul (-c₀))) → a' ∉ Fl → ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, c a' = s → ∑ a, |c a| ≤ abelian₂ → (∀ a ∉ Fl, 0 ≤ c a) → IsPsh S.A (sumPot c (fun a => S.potT a (Real.exp (-(s ^ 2)⁻¹))) + S.Θ.rsmul (-(s * c₀ / 2))) := by
  classical
  intro e σ _ S Fl a' c₀ abelian₂ hc₀ hFl ha' hna'
  have ht0 : 0 < S.t₀ := (S.reg a').1
  have hεp : 0 < c₀ / (2 * (|abelian₂| + 1)) := by positivity
  obtain ⟨s₁, hs₁, heps⟩ := epsT_small S.C (c₀ / (2 * (|abelian₂| + 1))) hεp
  refine ⟨min s₁ (min 1 S.t₀), lt_min hs₁ (lt_min one_pos ht0), fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := le_trans hss (le_trans (min_le_right _ _) (min_le_left _ _))
  have hst : s ≤ S.t₀ := le_trans hss (le_trans (min_le_right _ _) (min_le_right _ _))
  have hss₁ : s ≤ s₁ := le_trans hss (min_le_left _ _)
  have htt : Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ := (scale_le hs hs1).trans hst
  refine ⟨htt, fun c hca' hsum hpos => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹) with ht
  have htp : 0 < t := Real.exp_pos _
  have hpot : ∀ a, IsPotential S.A (S.potT a t) := fun a => potT_potential S a htp htt
  have hE : |epsT S.C t| ≤ c₀ / (2 * (|abelian₂| + 1)) * s := heps s hs hss₁
  rw [isPsh_iff (isPotentialAdd S.A _ _ (isPotential_sumPot c hpot)
    (isPotentialRsmul S.A _ S.Θ S.potΘ))]
  intro j y hy w
  rw [dl_add_rsmul (isPotential_sumPot c hpot) S.potΘ _ j hy w, dl_sumPot c hpot j hy w]
  have hθ : 0 ≤ dl S.A S.Θ j y w := dl_nonneg_of_pos S.posΘ j hy w
  set θ := dl S.A S.Θ j y w with hθdef
  set E := |epsT S.C t| with hEdef
  have hE0 : 0 ≤ E := abs_nonneg _
  have hterm : ∀ a, -(|c a| * E * θ) ≤ c a * dl S.A (S.potT a t) j y w := by
    intro a
    by_cases hF : a ∈ Fl
    · have hp := hFl a hF t
      have n1 := dl_nonneg hp.1 j hy w
      rw [dl_rsmul (hpot a) (-1) j hy w] at n1
      have n2 := dl_nonneg hp.2 j hy w
      have hz : dl S.A (S.potT a t) j y w = 0 := by linarith
      rw [hz, mul_zero]
      have := mul_nonneg (mul_nonneg (abs_nonneg (c a)) hE0) hθ
      linarith
    · have hca : 0 ≤ c a := hpos a hF
      have hr : IsPsh S.A (S.potT a t + LocPot.rsmul (epsT S.C t) S.Θ) :=
        ((S.reg a).2.2 t htp htt).2.2.2.2.1
      have n1 := dl_nonneg hr j hy w
      rw [dl_add_rsmul (hpot a) S.potΘ _ j hy w] at n1
      have n3 : epsT S.C t * θ ≤ E * θ := mul_le_mul_of_nonneg_right (le_abs_self _) hθ
      have n4 : -(E * θ) ≤ dl S.A (S.potT a t) j y w := by linarith
      rw [abs_of_nonneg hca]
      have := mul_le_mul_of_nonneg_left n4 hca
      linarith
  have ha'l : c₀ * θ ≤ dl S.A (S.potT a' t) j y w := by
    have n1 := dl_nonneg (ha' t) j hy w
    rw [dl_add_rsmul (hpot a') S.potΘ _ j hy w] at n1
    linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a')]
  have hrest : -(∑ a, |c a|) * E * θ ≤
      ∑ a ∈ Finset.univ.erase a', c a * dl S.A (S.potT a t) j y w := by
    calc -(∑ a, |c a|) * E * θ = -(∑ a, |c a| * E * θ) := by
          rw [neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ -(∑ a ∈ Finset.univ.erase a', |c a| * E * θ) := by
          refine neg_le_neg (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
          intro a _ _
          exact mul_nonneg (mul_nonneg (abs_nonneg _) hE0) hθ
      _ = ∑ a ∈ Finset.univ.erase a', -(|c a| * E * θ) := by rw [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun a _ => hterm a
  have hA : c a' * dl S.A (S.potT a' t) j y w ≥ s * (c₀ * θ) := by
    rw [hca']
    exact mul_le_mul_of_nonneg_left ha'l hs.le
  have hLE : (∑ a, |c a|) * E ≤ s * c₀ / 2 := by
    have hL0 : 0 ≤ ∑ a, |c a| := Finset.sum_nonneg fun a _ => abs_nonneg _
    have h1 : (∑ a, |c a|) * E ≤ |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) :=
      mul_le_mul (hsum.trans (le_abs_self _)) hE hE0 (abs_nonneg _)
    have h2 : |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) ≤ s * c₀ / 2 := by
      have hL1 : 0 < |abelian₂| + 1 := by positivity
      rw [show |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) = (s * c₀ / 2) * (|abelian₂| / (|abelian₂| + 1)) by
        field_simp]
      have hq : |abelian₂| / (|abelian₂| + 1) ≤ 1 := by
        rw [div_le_one hL1]; linarith
      have : 0 ≤ s * c₀ / 2 := by positivity
      nlinarith
    linarith
  have hfin : 0 ≤ ((s * c₀ / 2) - (∑ a, |c a|) * E) * θ := mul_nonneg (by linarith) hθ
  nlinarith

end RootFieldNumerics.A1
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in
theorem hermLine_ext {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp only at ha hh
  subst ha hh
  rfl


open Classical in
noncomputable def indLine (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι where
  a := 0
  h z := if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then 1 else 0
  pos z hz := by rw [if_pos hz]; exact one_pos
  smul c z hc := by
    have : (∀ k, ∃ i, c k * z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
      simp [hc]
    simp only [this]
    simp

theorem indLine_smooth : IsSmoothHerm (indLine ι) :=
  (contDiffOn_const (c := (1 : ℝ))).congr fun _ hz => if_pos hz

theorem tensor_indLine {A B : HermLine ι} (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) :
    A.tensor (indLine ι) = B.tensor (indLine ι) := by
  refine hermLine_ext (by simp [HermLine.tensor, ha]) (funext fun z => ?_)
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · show A.h z * _ = B.h z * _
    rw [hh z hz]
  · have : (indLine ι).h z = 0 := if_neg hz
    show A.h z * _ = B.h z * _
    rw [this, mul_zero, mul_zero]

theorem additive_congr (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (ha : A.a = B.a)
    (hh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A.h z = B.h z) : φ A = φ B := by
  have h1 := hφ A _ hA indLine_smooth
  have h2 := hφ B _ hB indLine_smooth
  rw [tensor_indLine ha hh] at h1
  linarith

theorem combLine_single {J : Type} [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (j : J) :
    combLine ℓ (Pi.single j 1) = ℓ j := by
  refine hermLine_ext ?_ (funext fun z => ?_)
  · show ∑ i, (Pi.single j 1 : J → ℤ) i • (ℓ i).a = _
    rw [Finset.sum_eq_single j] <;> simp +contextual
  · show ∏ i, (ℓ i).h z ^ (Pi.single j 1 : J → ℤ) i = _
    rw [Finset.prod_eq_single j] <;> simp +contextual

theorem tensor_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hB

theorem additive_comb (φ : HermLine ι → ℝ)
    (hφ : ∀ A B, IsSmoothHerm A → IsSmoothHerm B → φ (A.tensor B) = φ A + φ B)
    {J : Type} [Fintype J] (ℓ : J → HermLine ι) (hℓ : ∀ j, IsSmoothHerm (ℓ j)) (n : J → ℤ) :
    φ (combLine ℓ n) = ∑ j, (n j : ℝ) * φ (ℓ j) := by
  classical
  have hs : ∀ m, IsSmoothHerm (combLine ℓ m) := fun m => (combLine_smooth_conj_invariant K ι J ℓ m).1 hℓ
  let ψ : (J → ℤ) →+ ℝ := AddMonoidHom.mk' (fun m => φ (combLine ℓ m)) (fun m m' => by
    show φ _ = φ _ + φ _
    rw [← hφ _ _ (hs m) (hs m')]
    refine additive_congr φ hφ (hs _) (tensor_smooth (hs m) (hs m')) ?_ fun z hz => ?_
    · show ∑ i, (m + m') i • (ℓ i).a = ∑ i, m i • (ℓ i).a + ∑ i, m' i • (ℓ i).a
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    · show ∏ i, (ℓ i).h z ^ (m + m') i = (∏ i, (ℓ i).h z ^ m i) * ∏ i, (ℓ i).h z ^ m' i
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => zpow_add₀ ((ℓ i).pos z hz).ne' _ _)
  have hn : n = ∑ j, n j • (Pi.single j 1 : J → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  show ψ n = _
  conv_lhs => rw [hn]

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  show _ * φ (combLine ℓ (Pi.single j 1)) = _
  rw [combLine_single]

end

end Ii

open Ii in
theorem intersection_multilinear_one_position : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (L : Fin d → HermLine ι) (k : Fin d) (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), IsArithVar P d → (∀ i, IsSmoothHerm (L i)) → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (Function.update L k (combLine ℓ n)) = ∑ j, (n j : ℝ) * II K ι P d (Function.update L k (ℓ j)) := by
  intro II hII K _ ι _ P d L k J _ ℓ n hP hL hℓ
  exact additive_comb (fun A => II K ι P d (Function.update L k A))
    (fun A B hA hB => hII.2.1 K ι P d L k A B hP hL hA hB) ℓ hℓ n

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics

theorem mixedDisc_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (hk : A k = 0) : mixedDisc A = 0 := by
  unfold mixedDisc
  have h : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ j ∈ S, A j).det = 0 := by
    rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ k),
      Finset.sum_powerset_insert (Finset.notMem_erase k _), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun S hS => ?_
    have hkS : k ∉ S := fun h => Finset.notMem_erase k _ (Finset.mem_powerset.mp hS h)
    have hc : (insert k S).card ≤ D := by simpa using Finset.card_le_univ (insert k S)
    rw [Finset.card_insert_of_notMem hkS] at hc
    rw [Finset.sum_insert hkS, hk, zero_add, Finset.card_insert_of_notMem hkS,
      show D - S.card = D - (S.card + 1) + 1 by omega, pow_succ]
    ring
  rw [h, mul_zero]

theorem maDensity_eq_zero {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (k : Fin D) (c : ℝ)
    (hk : φ k = fun _ => c) (z : Fin D → ℂ) : maDensity φ z = 0 := by
  have h : cxHessian (φ k) z = 0 := by
    rw [hk]
    funext i j
    simp [cxHessian]
  unfold maDensity
  rw [mixedDisc_eq_zero _ k h]
  simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsIntegral_eq_zero (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (k : Fin e) (c : ℝ) (hk : φ k = fun _ => c) :
    ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hs : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs
      · rw [maDensity_eq_zero _ k c (by rw [hk]), mul_zero]
      · rfl
    simp [hs]
  · rfl

theorem geoNum_last_zero (n : ℕ) (V : Ideal (MRing ι)) (a : Fin (n + 1) → K → ℤ)
    (ha : a (Fin.last n) = 0) : geoNum (n + 1) V a = 0 := by
  rw [geoNum.eq_2]
  simp [ha]

theorem snoc_snoc_swap {α : Type*} {e : ℕ} (L : Fin e → α) (A B : α) :
    (Fin.snoc (Fin.snoc L A : Fin (e + 1) → α) B : Fin (e + 2) → α) =
      (Fin.snoc (Fin.snoc L B : Fin (e + 1) → α) A : Fin (e + 2) → α) ∘
        Equiv.swap (Fin.last (e + 1)) (Fin.last e).castSucc := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · simp
    · have h1 : k.castSucc.castSucc ≠ Fin.last (e + 1) := (Fin.castSucc_lt_last _).ne
      have h2 : k.castSucc.castSucc ≠ (Fin.last e).castSucc := fun h =>
        (Fin.castSucc_lt_last k).ne (Fin.castSucc_injective _ h)
      simp [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem smooth_snoc {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (j : Fin (e + 1)) :
    IsSmoothHerm ((Fin.snoc L A : Fin (e + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa using hA
  · simpa using hL k

theorem points_integral_section_snoc : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → ptsIntegral P (fun j z => Real.log (((Fin.snoc L A : Fin (e + 1) → HermLine ι) j).h z)) (fun _ => 1) = ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  classical
  intro II hII hDS K _ ι _ P e L A s hP hL hA hs
  obtain ⟨hIS, -, -, -⟩ := hII
  obtain ⟨hperm, -, hrec⟩ := hIS K ι
  set O : HermLine ι := HermLine.ofWeight (K := K) (ι := ι) (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl) with hO
  have hOs : IsSmoothHerm O := by
    show ContDiffOn ℝ _ (fun _ => Real.exp (-(-1 : ℝ))) _
    exact contDiffOn_const
  have hsnL := smooth_snoc hL hA
  have hsnO := smooth_snoc hL hOs
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have h1 := intersection_constant_metric_line II hIS K ι P (e + 1) (Fin.snoc L A) (-1) hP hsnL
  have h2 := hrec P (e + 1) (Fin.snoc L O) A s a hP hsnO hA ha hsa hsP
  have h3 : II K ι P (e + 1 + 1) (Fin.snoc (Fin.snoc L A) O) =
      II K ι P (e + 1 + 1) (Fin.snoc (Fin.snoc L O) A) := by
    rw [snoc_snoc_swap L A O]
    exact hperm P (e + 1 + 1) _ _ hP (smooth_snoc hsnO hA)
  have h4 := h1.symm.trans (h3.trans h2)
  rw [neg_neg, one_mul] at h4
  rw [h4]
  unfold recR
  have hz : arInt P s A (Fin.snoc L O) = 0 :=
    ptsIntegral_eq_zero P _ _ (Fin.last e) 1 (by funext z; simp [hO, HermLine.ofWeight])
  rw [hz, sub_zero]
  refine finsum_congr fun W => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hW : W ∈ divSupp P s
  · have hW' : W ∈ divSupp P s ↔ True := iff_true_intro hW
    by_cases hh : IsHorizontal W
    · have hWa := (hDS K ι P (e + 1) A s W hP ⟨a, ha, hsa, hsP⟩ hW).1 hh
      have hh' : IsHorizontal W ↔ True := iff_true_intro hh
      simp only [hW', hh', and_self, if_true]
      rw [intersection_constant_metric_line II hIS K ι W e L (-1) hWa hL]
      ring
    · have hh' : IsHorizontal W ↔ False := iff_false_intro hh
      simp only [hW', hh', and_false, if_true, if_false]
      rw [geoNum_last_zero e W _ (by simp [hO, HermLine.ofWeight])]
      simp
  · have hW' : W ∈ divSupp P s ↔ False := iff_false_intro hW
    simp only [hW', false_and, if_false]

end RootFieldNumerics
end
end
