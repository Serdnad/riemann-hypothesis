module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem icyc_mem {R : Type*} [CommRing R] {P W : Ideal R} (hW : W.IsPrime) (hP : P ≤ W) {f g u v : R}
    (hu : u ∉ W) (h : u * f - v * g ∈ P) (hg : g ∈ W) : f ∈ W := by
  have : u * f ∈ W := by simpa using W.add_mem (hP h) (W.mul_mem_left v hg)
  exact (hW.mem_or_mem this).resolve_left hu

theorem icyc_sub {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι)
    (h : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    (h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P) : divSupp P f ⊆ divSupp P g := by
  rintro W ⟨⟨⟨hWp, hle⟩, hmin⟩, hr⟩
  have hPW : P ≤ W := le_sup_left.trans hle
  have hf : f ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  refine ⟨⟨⟨hWp, sup_le hPW ?_⟩, ?_⟩, hr⟩
  · obtain ⟨u, v, hu, -, huv⟩ := h' W hWp hPW hr
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hWp hPW hu huv hf
  · rintro W' ⟨hW'p, hle'⟩ hWW
    have hPW' : P ≤ W' := le_sup_left.trans hle'
    have hr' : IsRelevant W' := fun k => (hr k).imp fun i hi hi' => hi (hWW hi')
    obtain ⟨u, v, hu, -, huv⟩ := h W' hW'p hPW' hr'
    refine hmin ⟨hW'p, sup_le hPW' ?_⟩ hWW
    rw [Ideal.span_singleton_le_iff_mem]
    exact icyc_mem hW'p hPW' hu huv (hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)))

theorem icyc_map {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (P : Ideal R) (f g u v : R)
    (hu : u ∉ W) (h : u * f - v * g ∈ P) :
    Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) ≤
      Ideal.map (algebraMap R (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) := by
  rw [Ideal.map_le_iff_le_comap]
  refine sup_le (le_sup_left.trans Ideal.le_comap_map) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  have hU : IsUnit (algebraMap R (Localization.AtPrime W) u) :=
    IsLocalization.map_units (Localization.AtPrime W) (⟨u, hu⟩ : W.primeCompl)
  rw [← Ideal.unit_mul_mem_iff_mem _ hU, ← map_mul]
  apply Ideal.mem_map_of_mem
  have := (P ⊔ Ideal.span {g}).add_mem (Ideal.mem_sup_left h)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ v (Ideal.mem_span_singleton_self g)))
  simpa using this

theorem icyc_len {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] (J : Ideal R) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ Ideal.map (algebraMap R (Localization.AtPrime W)) J) := by
  refine LinearEquiv.length_eq ?_
  exact ((LocalizedModule.equivTensorProduct W.primeCompl (R ⧸ J)).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime W) J).toLinearEquiv.symm)

theorem i_cycle : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  intro K _ ι _ P f g h
  obtain ⟨-, -, h⟩ := h
  have h' : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * g - v * f ∈ P := by
    intro W hW hP hr
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hP hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  refine ⟨Set.Subset.antisymm (icyc_sub P f g h h') (icyc_sub P g f h' h), fun W hW => ?_⟩
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  obtain ⟨u, v, hu, hv, huv⟩ := h W hWp hPW hW.2
  unfold multAt
  rw [dite_eq_left hWp, dite_eq_left hWp]
  congr 1
  rw [icyc_len, icyc_len]
  have e : Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {f}) =
      Ideal.map (algebraMap (MRing ι) (Localization.AtPrime W)) (P ⊔ Ideal.span {g}) :=
    le_antisymm (icyc_map W P f g u v hu huv) (icyc_map W P g f v u hv (by simpa using P.neg_mem huv))
  rw [e]

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

namespace IDef

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

def wt : (Σ k, ι k) → K → ℤ := fun p => Pi.single p.1 1

theorem weight_wt (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (wt (ι := ι)) m k = ((∑ i, m ⟨k, i⟩ : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [wt]
  · intro b _ hb
    simp [wt, Pi.single_eq_of_ne hb.symm]
  · simp

theorem mem_of_homog {s : MRing ι} {a : K → ℕ} (h : IsMultiHomog s a) :
    s ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) (fun k => (a k : ℤ)) := by
  rw [mem_weightedHomogeneousSubmodule]
  intro d hd
  funext k
  rw [weight_wt, h d (mem_support_iff.mpr hd) k]

theorem evC_smul {s : MRing ι} {d : K → ℤ} (h : s ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) d) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : evC (fun p => c p.1 * z p) s = (∏ k, c k ^ d k) * evC z s := by
  rw [mem_weightedHomogeneousSubmodule] at h
  by_cases hs : s = 0
  · simp [hs, evC]
  obtain ⟨m₀, hm₀⟩ := ne_zero_iff.mp hs
  have h1 : ∀ k, d k = ((∑ i, m₀ ⟨k, i⟩ : ℕ) : ℤ) := fun k => by rw [← h hm₀, weight_wt]
  have h2 : IsMultiHomog s fun k => ∑ i, m₀ ⟨k, i⟩ := by
    intro m hm k
    have := weight_wt m k
    rw [h (mem_support_iff.mp hm), h1] at this
    exact_mod_cast this.symm
  simp only [h1, zpow_natCast]
  exact eval_smul_homog s _ h2 c z

theorem homog_ideal {P : Ideal (MRing ι)} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨_, mem_of_homog ha⟩

theorem exists_homog_pair {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {f g u v : MRing ι} {α γ : K → ℕ}
    (hf : IsMultiHomog f α) (hg : IsMultiHomog g γ) (h : u * f - v * g ∈ P) {z : (Σ k, ι k) → ℂ}
    (hu : evC z u ≠ 0) : ∃ (u' v' : MRing ι) (d : K → ℤ), u' ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) d ∧
      v' ∈ weightedHomogeneousSubmodule ℤ (wt (ι := ι)) (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ)) ∧
      u' * f - v' * g ∈ P ∧ evC z u' ≠ 0 := by
  classical
  set 𝒜 := weightedHomogeneousSubmodule ℤ (wt (ι := ι)) with h𝒜
  have h1 : ∃ d, evC z (DirectSum.decompose 𝒜 u d : MRing ι) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hu
    rw [← DirectSum.sum_support_decompose 𝒜 u]
    unfold evC at hc ⊢

    rw [map_sum, map_sum]
    exact Finset.sum_eq_zero fun d _ => hc d
  obtain ⟨d, hd⟩ := h1
  refine ⟨_, _, d, (DirectSum.decompose 𝒜 u d).2,
    (DirectSum.decompose 𝒜 v (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ))).2, ?_, hd⟩
  have h2 := homog_ideal hP (d + fun k => (α k : ℤ)) h
  rw [← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (mem_of_homog hf),
    ← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (mem_of_homog hg), sub_add_cancel]
  rw [DirectSum.decompose_sub] at h2
  exact h2

omit [DecidableEq K] in
theorem exists_pair {P : Ideal (MRing ι)} {f g : MRing ι} (h : UnitRatio P f g) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : ∃ u v : MRing ι, evC z u ≠ 0 ∧ evC z v ≠ 0 ∧ u * f - v * g ∈ P := by
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  exact h.2.2 (RingHom.ker φ) (RingHom.ker_isPrime φ) (fun s hs => hz.2 s hs) fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa [φ, RingHom.mem_ker] using hi⟩

omit [DecidableEq K] in
theorem ratio_eq {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g u v u' v' : MRing ι} (hg : g ∉ P)
    (h : u * f - v * g ∈ P) (h' : u' * f - v' * g ∈ P) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hu : evC z u ≠ 0) (hu' : evC z u' ≠ 0) : ‖evC z v‖ / ‖evC z u‖ = ‖evC z v'‖ / ‖evC z u'‖ := by
  have h1 : (u * v' - u' * v) * g ∈ P := by
    have := P.sub_mem (P.mul_mem_left u' h) (P.mul_mem_left u h')
    convert this using 1
    ring
  have h2 := hz.2 _ ((hP.mem_or_mem h1).resolve_right hg)
  rw [← norm_div, ← norm_div]
  congr 1
  unfold evC at *
  simp only [map_sub, map_mul] at h2
  field_simp
  linear_combination -h2

end IDef

open IDef HolomorphicMinorCharts in
theorem i_defect : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) := by
  intro K _ ι _ P J e R A B f g hP hI hA hB
  classical
  obtain ⟨⟨α, γ, hf, hg, hdeg⟩, hU⟩ := hI
  let w : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ q : MRing ι × MRing ι, q.1 * f - q.2 * g ∈ P ∧ evC z q.1 ≠ 0 then
      Real.log (‖evC z h.choose.2‖ / ‖evC z h.choose.1‖ * B.h z / A.h z) else 0
  have hw : IsDefectOn P (mcPts P) f g A B w := by
    intro z hz u v h hu
    have hex : ∃ q : MRing ι × MRing ι, q.1 * f - q.2 * g ∈ P ∧ evC z q.1 ≠ 0 := ⟨(u, v), h, hu⟩
    simp only [w, dif_pos hex]
    rw [ratio_eq hP.1 hU.2.1 hex.choose_spec.1 h hz hex.choose_spec.2 hu]
  have hinv : ∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z' := by
    intro z hz z' hzz
    have hz' : z' ∈ mcPts P := mem_mcPts_of_sameOrbit hP.2.1 (so_symm hzz) hz
    obtain ⟨u₀, v₀, hu₀, -, h₀⟩ := exists_pair hU hz'
    obtain ⟨u, v, d, hu, hv, h, hu'⟩ := exists_homog_pair hP.2.1 hf hg h₀ hu₀
    obtain ⟨c, hc, rfl⟩ := hzz
    have hn : ∀ n : K → ℤ, (∏ k, c k ^ n k) ≠ 0 := fun n => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hn' : ∀ n : K → ℤ, (∏ k, ‖c k‖ ^ n k) ≠ 0 := fun n =>
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [hw _ hz u v h (by rw [evC_smul hu]; exact mul_ne_zero (hn d) hu'), hw _ hz' u v h hu', evC_smul hu, evC_smul hv,
      A.smul c z' hc, B.smul c z' hc]
    congr 1
    simp only [norm_mul, norm_prod, norm_zpow]
    have key : (∏ k, ‖c k‖ ^ (d + (fun k => (α k : ℤ)) - fun k => (γ k : ℤ)) k) * ∏ k, ‖c k‖ ^ B.a k =
        (∏ k, ‖c k‖ ^ d k) * ∏ k, ‖c k‖ ^ A.a k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (norm_ne_zero_iff.mpr (hc k)), ← zpow_add₀ (norm_ne_zero_iff.mpr (hc k))]
      congr 1
      have := hdeg k
      simp only [Pi.sub_apply, Pi.add_apply]
      linarith
    have h1 := hn' d
    have h2 := hn' A.a
    have h3 := (A.pos z' hz'.1).ne'
    have h4 := norm_ne_zero_iff.mpr hu'
    field_simp
    linear_combination ‖evC z' v‖ * B.h z' * key
  refine ⟨w, hw, hinv, fun j y hy => ContDiffAt.contDiffWithinAt ?_⟩
  set x := (R.A.chart j).symm y with hx
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds ⟨hy.1, R.mem_U x⟩
  have hz := R.mem x x (R.mem_U x)
  obtain ⟨u, v, hu, hv, h⟩ := exists_pair hU hz
  have hl : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => R.lift x ((R.A.chart j).symm y)) y :=
    (contDiffOn_lift R x j).contDiffAt hO
  have hev : ∀ s : MRing ι, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => evC (R.lift x ((R.A.chart j).symm y)) s) y := fun s =>
    ContDiffAt.comp (g := fun z => evC z s) y
      (((AnalyticOnNhd.eval_mvPolynomial (map (Int.castRingHom ℂ) s)) _ trivial).contDiffAt.restrict_scalars ℝ) hl
  have hNZ : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun k => ?_
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const
  have hh : ∀ C : HermLine ι, IsSmoothHerm C → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => C.h (R.lift x ((R.A.chart j).symm y))) y := fun C hC =>
    ContDiffAt.comp (g := C.h) y (ContDiffOn.contDiffAt hC (hNZ.mem_nhds hz.1)) hl
  have hA0 := (A.pos _ hz.1).ne'
  have hB0 := (B.pos _ hz.1).ne'
  have hu0 := norm_ne_zero_iff.mpr hu
  have hv0 := norm_ne_zero_iff.mpr hv
  refine ContDiffAt.congr_of_eventuallyEq
    ((((((hev v).norm ℂ hv).div ((hev u).norm ℂ hu) hu0).mul (hh B hB)).div (hh A hA) hA0).log
      (div_ne_zero (mul_ne_zero (div_ne_zero hv0 hu0) hB0) hA0)) ?_
  filter_upwards [hO, (hev u).continuousAt.eventually_ne hu] with y' h1 h2
  simp only [Function.comp_apply]
  rw [hinv _ (R.mem _ _ (R.mem_U _)) _ (R.compat _ x _ ⟨R.mem_U _, h1.2⟩)]
  exact hw _ (R.mem x _ h1.2) u v h h2

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : TateIso D k Q act e), ∃ J : TateIso D k Q (fun c y => act (g.s c) y) e, J.ζ = I.ζ ∧ ∀ n x, J.ev n x = I.ev n (a.a n x) := by
  intro E _ _ _ H D g a k _ Q _ act e I
  have ev_nsmul : ∀ (n : ℕ), 0 < n → ∀ y : D.La, I.ev n (n • y) = 1 := fun n hn y =>
    (I.ker n hn (n • y)).mpr ⟨y, rfl⟩
  have ev_split : ∀ (n : ℕ), 0 < n → ∀ (c : D.La) (f : TwMod g.s D.La),
      I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) := by
    intro n hn c f
    have h1 : I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) * I.ev n (n • (f : D.La)) :=
      I.add n _ _
    have h0 : I.ev n (n • (f : D.La)) = 1 := ev_nsmul n hn f
    exact h1.trans ((congrArg (fun q => I.ev n (a.a n c) * q) h0).trans (_root_.mul_one _))
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n x => I.ev n (a.a n x),
            add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, fun _ _ => rfl⟩
  · intro n x y
    rw [map_add (f := _)]
    exact I.add n _ _
  · intro n c x
    rw [map_smul]
    exact I.lin n (g.s c) (a.a n x)
  · intro n hn x
    exact (I.ker n hn (a.a n x)).trans (a.inj n hn x)
  · intro n hn x
    refine (I.onto n hn x).trans ⟨?_, ?_⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨c, f, hb⟩ := a.surj n hn b
      refine ⟨c, ?_⟩
      have h3 : I.ev n b = I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) := by
        rw [hb]
      exact (ev_split n hn c f).symm.trans h3.symm
    · rintro ⟨c, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    obtain ⟨f, hf⟩ := a.compat n m hn hm x
    have h4 : I.ev (n * m) (a.a (n * m) x) ^ m = I.ev n (a.a (n * m) x) := I.tower n m hn hm _
    have h5 : I.ev n (a.a (n * m) x) = I.ev n (((a.a n x + n • f : TwMod g.s D.La)) : D.La) := by
      rw [hf]
    exact h4.trans (h5.trans (ev_split n hn x f))
  · intro n hn x y
    have h := I.isom n hn (a.a n x) (a.a n y)
    obtain ⟨t, ht⟩ := a.isom n hn x y
    have hpow : I.ζ n ^ n = 1 := (I.ζ_prim n hn).pow_eq_one
    have heq : I.ζ n ^ (D.EF (a.a n x : D.La)) (a.a n y : D.La) = I.ζ n ^ (D.EF x) y := by
      have h2 : (D.EF (a.a n x : D.La)) (a.a n y : D.La) = (D.EF x) y + (n : ℤ) * t := by
        have : (twForm D g ((a.a n) x)) ((a.a n) y) = (D.EF (a.a n x : D.La)) (a.a n y : D.La) := rfl
        rw [← this]
        linarith
      rw [h2, zpow_add, zpow_mul, zpow_natCast, hpow, one_zpow, _root_.mul_one]
    show e n (I.ev n (a.a n x)) (I.ev n (a.a n y)) (I.ζ n ^ (D.EF x) y)
    rw [← heq]
    exact h

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

private theorem fix_rt_lemma {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.rt = H.rt := by
  apply RingOfIntegers.ext
  rw [HostAut.s, RingOfIntegers.mapRingEquiv_apply]
  exact g.fix

private theorem fix_gen_lemma_2 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) : g.s H.w0 = H.w0 ∧ g.s (H.bar H.w0) = H.bar H.w0 := by
  have hr := fix_rt_lemma g
  have hbr : g.s (H.bar H.rt) = H.bar H.rt := by
    have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by
      rw [← map_pow, H.rt_sq, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h, hr]
    · rw [h, map_neg, hr]
  have two_ne : (2 : 𝓞 E) ≠ 0 := two_ne_zero
  constructor
  · apply mul_left_cancel₀ two_ne
    have h := congrArg g.s H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add (f := _), map_one, hr] at h
    rw [h, H.two_weight_eq_one_add_root]
  · apply mul_left_cancel₀ two_ne
    have h := congrArg (fun x => g.s (H.bar x)) H.two_weight_eq_one_add_root
    simp only [map_mul, map_ofNat, map_add (f := _), map_one] at h
    rw [h, hbr]
    have h2 := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_ofNat, map_add (f := _), map_one] at h2
    exact h2.symm

private theorem fix_adj_lemma_3 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (g : HostAut H) (a : 𝓞 E) (ha : a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))) : g.s a = a ∧ g.s (H.bar a) = H.bar a := by
  obtain ⟨h1, h2⟩ := fix_gen_lemma_2 g
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨h1, h2⟩
  | algebraMap r =>
    simp
  | add x y _ _ hx hy =>
    simp only [map_add (f := _), hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩
  | mul x y _ _ hx hy =>
    simp only [map_mul, hx.1, hy.1, hx.2, hy.2]
    exact ⟨trivial, trivial⟩

theorem tw_mb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (g : HostAut H), l.Mb.map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb ∧ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)).map (g.s : 𝓞 E →+* 𝓞 E) = l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  intro E _ _ _ H l g
  set S : Set (𝓞 E) := {a : 𝓞 E | a ∈ l.Mb ∧ a ∈ Algebra.adjoin ℤ ({H.w0} : Set (𝓞 E))} with hSdef
  have hS : l.Mb = Ideal.span S := l.fromK
  constructor
  · rw [hS, Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [RingEquiv.coe_toRingHom]
      rw [(fix_adj_lemma_3 g y hy.2).1]
      exact hy
    · intro hx
      exact ⟨x, hx, by simp only [RingEquiv.coe_toRingHom]; exact (fix_adj_lemma_3 g x hx.2).1⟩
  · rw [hS, Ideal.map_span, Ideal.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact ((fix_adj_lemma_3 g y hy.2).2).symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp only [RingEquiv.coe_toRingHom]
      exact (fix_adj_lemma_3 g y hy.2).2

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

private theorem isLieEigen_twistAct_iff {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (s : O ≃+* O) {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (v : epsPt t ⟶ G) :
    IsLieEigen (twistAct act s) t (τ.comp s.toRingHom) v ↔ IsLieEigen act t τ v := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    have := h1 (s.symm a)
    simpa [twistAct] using this
  · rintro ⟨h0, h1⟩
    refine ⟨h0, fun a => ?_⟩
    simpa [twistAct] using h1 (s a)

theorem tw_liemult : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (G : Over S) [GrpObj G] (act : OAct O G) (s : O ≃+* O) (k : Type) [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult (twistAct act s) t (τ.comp s.toRingHom) n ↔ LieMult act t τ n := by
  intro O _ S G _ act s k _ t τ n
  simp only [LieMult, isLieEigen_twistAct_iff]

end PositivityTheory.UnitarySelfGeneration
end
