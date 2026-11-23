module

public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem log_inv_bounds {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    Real.exp 1 ≤ Real.log (1 / t) ∧ 1 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : Real.exp 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  refine ⟨h1, ?_⟩
  have := Real.log_le_log (Real.exp_pos 1) h1
  rwa [Real.log_exp] at this

theorem loglog_quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_bounds ht hte
  exact div_nonneg (by linarith) (by linarith [Real.exp_pos 1])

theorem epsT_eq_mul (C t : ℝ) :
    epsT C t = C * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) := by
  rw [epsT, mul_div_assoc]

theorem epsT_le_epsT {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C' t := by
  rw [epsT_eq_mul, epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (loglog_quot_nonneg ht hte)

theorem mul_epsT_le {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t)
    (hte : t ≤ Real.exp (-Real.exp 1)) : C * epsT C t ≤ C' * epsT C' t := by
  have hx := loglog_quot_nonneg ht hte
  rw [epsT_eq_mul, epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem isPsh_rsmul_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) {ε ε' : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (hε : ε ≤ ε')
    (h : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε') := by
  intro x j y hy w
  obtain ⟨hyt, hyU⟩ := hy
  have hU : (A.chart j).symm y ∈ (th.U x ∩ Set.univ) ∩ Θ.U x := hyU
  have hO1 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' th.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (th.isOpen_U x)
  have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
  have hO3 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (Set.univ : Set X)) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target isOpen_univ
  have hth2 : ContDiffAt ℝ 2 (th.φ x ∘ (A.chart j).symm) y :=
    ((hth.1 x j).contDiffAt (hO1.mem_nhds ⟨hyt, hU.1.1⟩)).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
    ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
  have hu2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (hO3.mem_nhds ⟨hyt, Set.mem_univ _⟩)).of_le (by norm_cast)
  have hP2 : ContDiffAt ℝ 2
      ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hth2.add hu2).add (contDiffAt_const.mul hΘ2)
  have hfun : (th + LocPot.ofFun u + Θ.rsmul ε').φ x ∘ (A.chart j).symm =
      fun z => ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) z +
        (ε' - ε) * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show th.φ x _ + u _ + ε' * Θ.φ x _ = th.φ x _ + u _ + ε * Θ.φ x _ + (ε' - ε) * Θ.φ x _
    ring
  rw [hfun, levi_add_smul (ε' - ε) hP2 hΘ2 w]
  exact add_nonneg (h x j y ⟨hyt, hyU⟩ w)
    (mul_nonneg (sub_nonneg.2 hε) (hΘp x j y ⟨hyt, hU.2⟩ w))

theorem isRegFamily_mono {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ C' t₁ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th)
    (hs : ∀ y, logNormSec L s y ≤ 0) (hF : IsRegFamily A Θ L s th ph phT C t₀)
    (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀) (hte : t₁ ≤ Real.exp (-Real.exp 1)) :
    IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y => by
    have := hs y
    have := Real.exp_pos 1
    unfold rW
    linarith
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-Real.exp 1) := htt.trans hte
  have hε := epsT_le_epsT hCC ht hte'
  have hll := (log_inv_bounds ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_, fun y hy => ?_,
    fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_le hC (ht.trans_le htt') (ht'.trans hte)
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PshAdd

open ReciprocityTheory.AnForm.M.LocPot

theorem isPshOn_add_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X)
    (P : LocPot X) (f : X → ℝ) (Θ : LocPot X) (hU : IsOpen U) (hP : IsPotential A P)
    (hΘ : IsPotential A Θ) (hf : A.SmoothOn U f) (hPf : IsPshOn A U (P + LocPot.ofFun f))
    (hΘp : IsPsh A Θ) : IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  intro x j y hy w
  obtain ⟨hyt, ⟨⟨hyP, -⟩, hyΘ⟩, hyU⟩ := hy
  have hP2 : ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)).mem_nhds ⟨hyt, hyP⟩
    exact ((hP.1 x j).contDiffAt hmem).of_le (by norm_cast)
  have hf2 : ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' U ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ⟨hyt, hyU⟩
    exact ((hf j).contDiffAt hmem).of_le (by norm_cast)
  have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x ∈ 𝓝 y :=
      ((A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U x)).mem_nhds ⟨hyt, hyΘ⟩
    exact ((hΘ.1 x j).contDiffAt hmem).of_le (by norm_cast)
  have hPf2 : ContDiffAt ℝ 2 (fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) y :=
    hP2.add hf2
  have h1 := hPf x j y ⟨hyt, ⟨hyP, Set.mem_univ _⟩, hyU⟩ w
  have h2 := hΘp x j y ⟨hyt, hyΘ⟩ w
  have hsum := ReciprocityTheory.AnForm.levi_add_smul (f := fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z))
    (g := Θ.φ x ∘ (A.chart j).symm) 1 hPf2 hΘ2 w
  have heq : ((P + LocPot.ofFun f + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) +
        1 * (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z; simp [Function.comp, HAdd.hAdd, Add.add, LocPot.ofFun]
  rw [heq, hsum, one_mul]
  exact add_nonneg h1 h2

end GlobalTheory.CompanionTheory.Ar.PshAdd
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem bdry_snc_chart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
      (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsSection A L s → IsSNC A L s m W → ∀ x,
        ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
          ∃ S : Finset (Fin e), ∀ y ∈ ψ.source, (y ∈ bdry s ↔ ∃ i ∈ S, ψ y i = 0) := by
  classical
  intro e X _ A L s nb m W hs hsnc x
  obtain ⟨ψ, hψ, hx, hsub, σ, -, -, u, -, hu, hfac⟩ := hsnc x
  refine ⟨ψ, hψ, hx, Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ m k ≠ 0), ?_⟩
  intro y hy
  have hglue := hs.2 x y y ⟨hsub hy, L.mem_U y⟩
  have hzero : s y y = 0 ↔ s x y = 0 := by
    have e1 : Real.exp (-L.φ x y) ≠ 0 := (Real.exp_pos _).ne'
    have e2 : Real.exp (-L.φ y y) ≠ 0 := (Real.exp_pos _).ne'
    constructor
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue).resolve_right e1)
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue.symm).resolve_right e2)
  have hmem : y ∈ bdry s ↔ s y y = 0 := Iff.rfl
  rw [hmem, hzero, hfac y hy, mul_eq_zero, or_iff_right (hu y hy), Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    cases hσ : σ k with
    | none => simp [hσ] at hk
    | some i =>
      simp only [hσ] at hk
      have hm : m k ≠ 0 := by
        intro h
        rw [h, pow_zero] at hk
        exact one_ne_zero hk
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, k, hσ, hm⟩, pow_eq_zero_iff hm |>.mp hk⟩
  · rintro ⟨i, hi, h0⟩
    obtain ⟨k, hk, hm⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨k, Finset.mem_univ k, ?_⟩
    simp only [hk]
    rw [h0, zero_pow hm]

end GlobalTheory.CompanionTheory.Metric
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_nonneg_of_compat_fixedBase : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B →
    IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) →
    (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    ∀ w : Fin e → ℂ,
    0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  intro e X _ A B th ph U x₀ j hAB hth hU hph hpsh hsrc y hy w
  have hp : (B.chart j).symm y ∈ (B.chart j).source := (B.chart j).map_target hy.1
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hτ : AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y := hAB.2 j k y ⟨hy.1, hk⟩
  have hsymm : (A.chart k).symm ((A.chart k ∘ (B.chart j).symm) y) = (B.chart j).symm y :=
    (A.chart k).left_inv hk
  have htgt : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target := (A.chart k).map_source hk
  have hthU : (B.chart j).symm y ∈ th.U x₀ := hsrc hp
  have hO1 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀) :=
    (A.chart k).isOpen_inter_preimage_symm (th.isOpen_U x₀)
  have hO2 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have hm1 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀ :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hthU⟩
  have hm2 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' U :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hy.2⟩
  have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hC1 : ContDiffAt ℝ 2 (th.φ x₀ ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hth.1 x₀ k).contDiffAt (hO1.mem_nhds hm1)).of_le h2
  have hC2 : ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hph k).contDiffAt (hO2.mem_nhds hm2)).of_le h2
  have hC : ContDiffAt ℝ 2 (fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z))
      ((A.chart k ∘ (B.chart j).symm) y) := hC1.add hC2
  have hev : (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) =ᶠ[𝓝 y]
      ((fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ∘
        (A.chart k ∘ (B.chart j).symm)) := by
    have h1 : ∀ᶠ z in 𝓝 y, (B.chart j).symm z ∈ (A.chart k).source :=
      ((B.chart j).continuousAt_symm hy.1).eventually ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  rw [levi_congr hev w, levi_comp w hτ hC]
  exact hpsh x₀ k _ ⟨htgt, ⟨hm1.2, Set.mem_univ _⟩, hm2.2⟩ _

end GlobalTheory.CompanionTheory.LeviChart
end

section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.AnForm

theorem isPsh_of_dense_compl : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (B : Set X) (Q Q' : LocPot X), IsClosed B → Dense Bᶜ → (∀ x, Q'.U x = Q.U x) → (∀ x, A.SmoothOn (Q'.U x) (Q'.φ x)) → (∀ x, ∀ y ∈ Q.U x, y ∉ B → Q'.φ x y = Q.φ x y) → IsPshOn A Bᶜ Q → IsPsh A Q' := by
  intro e X _ A B Q Q' hB hD hU hS hE hP x j y hy w
  by_contra hneg
  have hneg' : levi (Q'.φ x ∘ (A.chart j).symm) y w < 0 := not_le.mp hneg
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q'.isOpen_U x)
  have hf : ContDiffOn ℝ 2 (Q'.φ x ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    (hS x j).of_le ENat.LEInfty.out
  have hc := continuousOn_levi hO hf
  have hc' : ContinuousOn (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) :=
    hc.comp (f := fun y' => (y', w)) (by fun_prop) (fun y' hy' => ⟨hy', Set.mem_univ _⟩)
  have hV := hc'.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  set V := ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q'.U x) ∩
    (fun y' => levi (Q'.φ x ∘ (A.chart j).symm) y' w) ⁻¹' Set.Iio 0 with hVdef
  have hVt : V ⊆ (A.chart j).target := fun z hz => hz.1.1
  have hVi : IsOpen ((A.chart j).symm '' V) :=
    (A.chart j).symm.isOpen_image_of_subset_source hV hVt
  have hne : ((A.chart j).symm '' V).Nonempty := ⟨_, y, ⟨hy, hneg'⟩, rfl⟩
  obtain ⟨z, ⟨y', hy'V, rfl⟩, hzB⟩ := hD.inter_open_nonempty _ hVi hne
  have hW : IsOpen (V ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
    have h1 := (A.chart j).isOpen_inter_preimage_symm hB.isOpen_compl
    have : V ∩ (A.chart j).symm ⁻¹' Bᶜ =
        V ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Bᶜ) := by
      ext u
      exact ⟨fun h => ⟨h.1, hVt h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact hV.inter h1
  have hev : (Q'.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y'] (Q.φ x ∘ (A.chart j).symm) := by
    filter_upwards [hW.mem_nhds ⟨hy'V, hzB⟩] with u hu
    have huU : (A.chart j).symm u ∈ Q.U x := hU x ▸ hu.1.1.2
    exact hE x _ huU hu.2
  have h0 := hP x j y' ⟨hy'V.1.1, (hU x ▸ hy'V.1.2 : (A.chart j).symm y' ∈ Q.U x), hzB⟩ w
  rw [← levi_congr hev w] at h0
  exact absurd h0 (not_le.mpr hy'V.2)

end GlobalTheory.CompanionTheory.AnForm
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos

theorem isPsh_add_zero_add (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ) :
    IsPsh A (Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ) := by
  unfold ReciprocityTheory.AnForm.M.IsPsh
  intro x j y hy w
  have hy' : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x := ⟨hy.1, hy.2.2⟩
  have hfun : ((Θ + LocPot.ofFun (fun _ => (0 : ℝ)) + Θ).φ x ∘ (A.chart j).symm) =
      fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z := by
    funext z
    show Θ.φ x _ + 0 + Θ.φ x _ = (2 : ℝ) • Θ.φ x _
    rw [smul_eq_mul]
    ring
  have hlevi : ∀ z v, ReciprocityTheory.AnForm.levi (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) z v =
      2 * ReciprocityTheory.AnForm.levi (Θ.φ x ∘ (A.chart j).symm) z v := by
    intro z v
    unfold ReciprocityTheory.AnForm.levi
    have h1 : fderiv ℝ (fun z => (2 : ℝ) • (Θ.φ x ∘ (A.chart j).symm) z) =
        (2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm) := fderiv_const_smul_field (2 : ℝ)
    have h2 : fderiv ℝ ((2 : ℝ) • fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) =
        (2 : ℝ) • fderiv ℝ (fderiv ℝ (Θ.φ x ∘ (A.chart j).symm)) := fderiv_const_smul_field (2 : ℝ)
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun, hlevi]
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi]
  · exact mul_nonneg (by norm_num) (hpos x j y hy' w hw).le

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.TwicePos
end
