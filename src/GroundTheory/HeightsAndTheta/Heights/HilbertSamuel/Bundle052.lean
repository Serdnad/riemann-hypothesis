module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle043
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle042
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.LocalSubring
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace ResolutionSupBound

theorem eval_smul_homog {ι : Type*} {f : MvPolynomial ι ℂ} {n : ℕ} (hf : f.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) f = c ^ n * eval z f := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = n := by
    by_contra h
    exact (mem_support_iff.mp he) (hf.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : e.degree = ∑ i ∈ e.support, e i := rfl
  rw [← hdeg, hs]
  ring

theorem ptNorm_smul {ι : Type*} (m : ConeMetric ℂ ι) {n : ℕ} {f : MvPolynomial ι ℂ} (hf : f.IsHomogeneous n)
    {c : ℂ} (hc : c ≠ 0) (z : ι → ℂ) :
    ptNorm m (RingHom.id ℂ) n f (c • z) = ptNorm m (RingHom.id ℂ) n f z := by
  have hc' : (0 : ℝ) < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc) n
  simp only [ptNorm, MvPolynomial.map_id, eval_smul_homog hf, m.smul, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ hc'.ne'

theorem proof (hI : ResolutionImageSup.Statement) (hND : NonvanishingDense.Statement) :
    ResolutionSupBound.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := hI D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set B := C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧ eval w (map (Int.castRingHom ℂ) g) ≠ 0}
  have hzm : z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    refine ⟨fun _ => ?_, hz.2⟩
    by_contra h
    simp only [not_exists, not_not] at h
    exact hz.1 (funext fun q => h q.2)
  have hzS : z ∈ closure S := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hzm
  have key : ∀ w ∈ S, ptNorm d.m (RingHom.id ℂ) n f w ≤ B := by
    rintro w ⟨hw, hwg⟩
    obtain ⟨y, c, hc, hyc⟩ := d.R.surj w hw fun h => hwg (h.2 g hgJ)
    have hy : resPt d y = c () • w := by
      rw [resPt, hyc]
      rfl
    rw [← ptNorm_smul d.m hf (hc ()), ← hy]
    exact hC n hn f hf y
  have hρ : ContinuousAt d.m.ρ z :=
    (d.smooth.continuousOn).continuousAt (isOpen_ne.mem_nhds hz.1)
  have hcont : ContinuousAt (ptNorm d.m (RingHom.id ℂ) n f) z := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact ((MvPolynomial.continuous_eval f).norm.continuousAt).div (hρ.pow n)
      (pow_pos (d.m.pos z hz.1) n).ne'
  have := mem_closure_iff_nhdsWithin_neBot.1 hzS
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall key)

end ResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem FibreNormPrimeBound.block_ne_zero {y : (Σ k, ι k) → Ω} {e : K → ℕ} {f : MRing ι}
    (he : ∀ k, 1 ≤ e k) (hf : IsMultiHomog f e) (hy : aeval y f ≠ 0) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  by_contra h
  push Not at h
  apply hy
  rw [aeval_def, eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have hsum : ∑ i, m ⟨k, i⟩ ≠ 0 := by rw [hf m hm k]; exact (Nat.one_le_iff_ne_zero.mp (he k))
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, i⟩) ?_)
  rw [h i, zero_pow hi]


omit [Fintype K] in
theorem FibreNormPrimeBound.exists_chart (V : ValuationSubring Ω) {y : (Σ k, ι k) → Ω}
    (hblk : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ ∀ q : Σ k, ι k, y q / y ⟨q.1, c q.1⟩ ∈ V := by
  classical
  have hmax : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 ∧ ∀ i', V.valuation (y ⟨k, i'⟩) ≤ V.valuation (y ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hm⟩ := Finset.exists_max_image (Finset.univ.filter fun i => y ⟨k, i⟩ ≠ 0)
      (fun i => V.valuation (y ⟨k, i⟩)) (by obtain ⟨i0, h0⟩ := hblk k; exact ⟨i0, by simp [h0]⟩)
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun i' => ?_⟩
    by_cases h : y ⟨k, i'⟩ = 0
    · rw [h, map_zero]; exact zero_le
    · exact hm i' (by simp [h])
  choose c hc0 hcm using hmax
  refine ⟨c, hc0, fun ⟨k, i⟩ => ?_⟩
  have hv : V.valuation (y ⟨k, c k⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc0 k)
  rw [← V.valuation_le_one_iff, div_eq_mul_inv, map_mul, map_inv₀]
  calc V.valuation (y ⟨k, i⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹
      ≤ V.valuation (y ⟨k, c k⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹ := mul_le_mul_left (hcm k i) _
    _ = 1 := mul_inv_cancel₀ hv

theorem FibreNormPrimeBound.mem_of_isIntegral (V : ValuationSubring Ω) {S : Subalgebra ℤ Ω} (hS : ∀ s ∈ S, s ∈ V)
    {u : Ω} (hu : IsIntegral S u) : u ∈ V := by
  let φ : S →+* V :=
    { toFun := fun r => ⟨r, hS r r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  obtain ⟨f, hf, hfu⟩ := hu
  have hint : IsIntegral V u := ⟨f.map φ, hf.map φ, by rw [Polynomial.eval₂_map]; exact hfu⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  exact hv ▸ v.2

theorem FibreNormPrimeBound.proof (hG : PullFormsGeneric.Statement) (hN : NormFormGaussBound.Statement)
    (hC : ChartPrimePowerInverse.Statement) : FibreNormPrimeBound.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hAr hBir he hhomL hnz p hp
  have hM : ∀ j, ∃ M : ℕ, aeval y (L j) ≠ 0 → ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro j
    by_cases hj : aeval y (L j) = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨M, hM⟩ := hC K ι Ω y D e L hhomL hnz p hp j hj
      exact ⟨M, fun _ => hM⟩
  choose M hM using hM
  refine ⟨Module.finrank (pullField y L) Ω * (∑ j, M j) * q, ?_⟩
  intro τ s hs j c hc μ
  obtain ⟨hLj, hfd, -, hhom, hcp⟩ := hc
  have := hfd
  set S := ∑ j, M j with hS
  set Sset : Set Ω := {z | ∃ i k, z = aeval y (L i) / aeval y (L k)} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}
  have key : ∀ V : ValuationSubring Ω, Sset ⊆ V.toSubring →
      (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈ V := by
    intro V hSV
    obtain ⟨c, hc0, hcV⟩ :=
      FibreNormPrimeBound.exists_chart V (FibreNormPrimeBound.block_ne_zero he (hhomL j) hLj)
    set Z := ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) with hZ
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hY
    have hu : s * Z ∈ V := by
      refine FibreNormPrimeBound.mem_of_isIntegral V (S := chartRingZ y c) ?_ (hs c hc0)
      intro t ht
      rw [chartRingZ, Algebra.adjoin_int] at ht
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ ht
      rintro _ ⟨q', rfl⟩
      exact hcV q'
    have hw : (p : Ω) ^ M j * Y / aeval y (L j) ∈ V := by
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ (hM j hLj c hc0)
      rintro z ((⟨q', rfl⟩ | ⟨i, rfl⟩) | hz)
      · exact hcV q'
      · exact hSV (Or.inl ⟨i, j, rfl⟩)
      · exact hSV (Or.inr hz)
    have hpV : (p : Ω) ∈ V := natCast_mem V p
    obtain ⟨r, hr⟩ : ∃ r, S = M j + r :=
      ⟨S - M j, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))).symm⟩
    have hZY : Z * Y ^ (q * τ) = 1 := by
      rw [hZ, hY, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← pow_mul, ← zpow_natCast (y _) (e k * (q * τ)), ← zpow_add₀ (hc0 k)]
      have h0 : -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) + ((e k * (q * τ) : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [h0, zpow_zero]
    have heq : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) =
        (s * Z) * ((p : Ω) ^ r) ^ (q * τ) * ((p : Ω) ^ M j * Y / aeval y (L j)) ^ (q * τ) := by
      rw [hr]
      calc (p : Ω) ^ ((M j + r) * (q * τ)) * (s / aeval y (L j) ^ (q * τ))
          = s * (Z * Y ^ (q * τ)) * (p : Ω) ^ ((M j + r) * (q * τ)) / aeval y (L j) ^ (q * τ) := by
            rw [hZY]; ring
        _ = _ := by ring
    rw [heq]
    exact mul_mem (mul_mem hu (pow_mem (pow_mem hpV _) _)) (pow_mem hw _)
  have hint : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
      integralClosure (Subring.closure Sset) Ω := by
    have hmem : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
        (integralClosure (Subring.closure Sset) Ω).toSubring := by
      rw [← iInf_valuationSubring_superset]
      exact Subring.mem_iInf.mpr fun V => key V.1 V.2
    exact hmem
  have h := hN Ω D (fun i => aeval y (L i)) (pullField y L) rfl
    (hG K ι Ω y D e L hAr hBir he hhomL hnz) p hp j (S * (q * τ))
    (Module.finrank (pullField y L) Ω * (q * τ)) (s / aeval y (L j) ^ (q * τ)) c
    (hhom _ le_rfl) hcp hint μ
  have hn : Module.finrank (pullField y L) Ω * (S * (q * τ)) =
      Module.finrank (pullField y L) Ω * S * q * τ := by ring
  rw [hn] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

namespace FibreNormDehomIntegral

theorem den_eq_one_of_padicValRat_nonneg {a : ℚ} (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p a) : a.den = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ a.num := by
    intro hn
    have h1 : p ∣ Nat.gcd a.num.natAbs a.den := Nat.dvd_gcd (Int.ofNat_dvd_left.mp hn) hpd
    rw [a.reduced.gcd_eq_one] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have h0 := h p hp
  rw [padicValRat, padicValInt.eq_zero_of_not_dvd hnum] at h0
  have h2 : 1 ≤ multiplicity p a.den := one_le_multiplicity_of_dvd a.den_ne_zero hpd
  omega

end FibreNormDehomIntegral


open FibreNormDehomIntegral in
theorem FibreNormDehomIntegral.proof (hF : FibreNormBadPrimesFinite.Statement)
    (hG : FibreNormGoodPrimeIntegral.Statement) (hB : FibreNormPrimeBound.Statement) :
    FibreNormDehomIntegral.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hV hBir he hL hz
  have hSf := hF K ι Ω y D e L hV hBir he hL hz
  set T := hSf.toFinset with hT
  choose! C hC using hB K ι Ω y D e L q hV hBir he hL hz
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => ((Set.Finite.mem_toFinset hSf).mp hp).1
  set M₀ : ℕ := ∏ p ∈ T, p ^ C p with hM
  have hM0 : M₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hTp p hp).ne_zero
  refine ⟨M₀, Nat.one_le_iff_ne_zero.mpr hM0, ?_⟩
  intro τ s hs j c hc

  have hcoef : ∀ m, (((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).den = 1 := by
    intro m
    by_cases ha : (c (Module.finrank (pullField y L) Ω)).coeff m = 0
    · rw [ha, mul_zero]; rfl
    refine den_eq_one_of_padicValRat_nonneg fun p hp => ?_
    have := Fact.mk hp
    have hMq : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM0)
    rw [padicValRat.mul hMq ha, padicValRat.pow, padicValRat.of_nat]
    by_cases hpT : p ∈ T
    · have hle : C p ≤ multiplicity p M₀ :=
        (multiplicity_dvd_iff_le hM0).mp (Finset.dvd_prod_of_mem (fun p => p ^ C p) hpT)
      have hb := hC p hp τ s hs j c hc m
      have hle' : ((C p * τ : ℕ) : ℤ) ≤ (τ : ℤ) * (multiplicity p M₀ : ℤ) := by
        push_cast
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by positivity)
      linarith
    · have hgood : ¬ HasCommonZeroModP y L p hp := fun h =>
        hpT ((Set.Finite.mem_toFinset hSf).mpr ⟨hp, h⟩)
      have hg := hG K ι Ω y D e L q hV hBir he hL hz p hp hgood τ s hs j c hc m
      have : (0 : ℤ) ≤ (τ : ℤ) * (multiplicity p M₀ : ℤ) := by positivity
      linarith

  have hmem : ((M₀ : ℚ) ^ τ) • c (Module.finrank (pullField y L) Ω) ∈
      Set.range (map (Int.castRingHom ℚ) : MvPolynomial (Fin (D + 1)) ℤ → MvPolynomial (Fin (D + 1)) ℚ) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp ha
    refine ⟨(((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).num, ?_⟩
    rw [MvPolynomial.coeff_smul, smul_eq_mul, eq_intCast]
    exact Rat.coe_int_num_of_den_eq_one (hcoef m)
  obtain ⟨F, hF'⟩ := hmem
  exact ⟨F, hF'⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem top_sub_top_mixPot (I : AllFam) (hI : I.IsFamily) {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type}
    [Fintype κ] {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (hP : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) (hs₀ : IsSmoothMetric m₀)
    (hs₁ : IsSmoothMetric m₁) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  classical
  have hB := tele_smooth_ratio hs₀ hs₁
  have hsymm := (hI Unit (GlobalTheory κ)).1
  have hadd := (hI Unit (GlobalTheory κ)).2.1
  have htel := Finset.sum_range_sub
    (fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i)) (D + 1)
  have hT0 : tele_fam m₀ m₁ (D + 1) 0 = fun _ => HermLine.ofCone m₀ := by
    funext j
    simp [tele_fam]
  have hT1 : tele_fam m₀ m₁ (D + 1) (D + 1) = fun _ => HermLine.ofCone m₁ := by
    funext j
    simp [tele_fam, j.isLt]
  simp only [hT0, hT1] at htel
  unfold top
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e1 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (i + 1)) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₁)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl)]
    have : HermLine.ofCone m₁ = tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  have e0 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₀)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have : HermLine.ofCone m₀ = tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  rw [e1, e0, tele_ofCone_tensor m₀ m₁,
    hadd _ _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _) (tele_smooth_ofCone hs₀) hB,
    add_sub_cancel_left, fam_degZero I hI hP _ (tele_fam_smooth hs₀ hs₁ _ _) _ hB rfl]
  have hpot : pot (tele_fam m₀ m₁ D i) = mixPot m₀ m₁ D i := by
    funext j z
    simp only [pot, mixPot, tele_fam]
    split_ifs <;> rfl
  rw [hpot]
  rfl

theorem DefectMetricChange.proof (hR : RealGramComparison.Statement)
    (hC : ComplexGramMetricChange.Statement) (hM : ResolutionMixedIntegral.Statement) :
    DefectMetricChange.Statement := by
  intro D Ω _ _ κ _ I d m₁ P0₁ hs hc hle hp e hI he
  have h₁ := hR D Ω κ (d.withMetric m₁ P0₁ hs hc hle hp) e he
  have h₀ := hR D Ω κ d e he
  have hc₁ := hC D Ω κ d m₁ P0₁ hs hc hle hp e he
  have htop : top I d.x m₁ D = top I d.x d.m D + ((D : ℝ) + 1) * resMetricInt d m₁ := by
    rw [← hM D Ω κ d m₁ hs, ← top_sub_top_mixPot I hI d.arith d.smooth hs]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def ChangeOfLatticeNested.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    (fun n : ℕ => latLogIndex x (matAct B x) n -
        (top I (matAct B x) m' D - top I x m D) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D

namespace ChangeOfLatticeNested

theorem matAct_one {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] [DecidableEq J] (x : J → Ω) :
    matAct (1 : Matrix J J ℚ) x = x := by
  funext i
  simp only [matAct, Matrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

end ChangeOfLatticeNested

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def HSMBlockDatum.withMetric (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A') : HSMBlockDatum D K ι Ω :=
  { d with A := A', P0 := P0', deg := hdeg, conjInv := hc, normalForm_baseLattice_le_dualSpan_sup_line := hle, semipos := hp }

def BlockDefectMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A'),
    I.IsFamily →
    (fun n => hsDefect D (blockChi (d.withMetric A' P0' hdeg hc hle hp))
          (I K ι (mCoordIdeal d.y) (D + 1) fun _ => A') n -
        hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
