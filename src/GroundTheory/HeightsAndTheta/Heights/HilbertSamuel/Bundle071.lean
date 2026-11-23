module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import Mathlib.Algebra.Group.ForwardDiff
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle007

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionInterpIntegral

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem locDens_interp (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA' : IsSmoothHerm A')
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
          else AnResBridge.potOf d.R d.A) j y := by
  set x0 := (d.R.A.chart j).symm y with hx0
  set a : (Fin D → ℂ) → ℝ := fun y' => Real.log (d.A.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with ha
  set b : (Fin D → ℂ) → ℝ := fun y' => Real.log (A'.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with hb
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hyV : y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0 := ⟨hy, d.R.mem_U x0⟩
  have hsm : ∀ {L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}, IsSmoothHerm L → ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ 2 (fun y'' => Real.log (L.h (d.R.lift x0 ((d.R.A.chart j).symm y'')))) y' := by
    intro L hL
    filter_upwards [hV.mem_nhds hyV] with y' hy'
    exact_mod_cast contDiffAt_infty.mp
      ((AnResBridge.contDiffOn_potOf d.R hL x0 j).contDiffAt (hV.mem_nhds hy')) 2
  have hH := gaamix_cxHessian_comb (ψ := fun y' => (1 - t) * a y' + t * b y') (1 - t) t
    (hsm d.semipos.1) (hsm hA') (Filter.EventuallyEq.refl _ _)
  set H₀ := cxHessian a y
  set H₁ := cxHessian b y
  have hL : locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ReciprocityTheory.AnForm.maDens (fun _ y' => (1 - t) * a y' + t * b y') y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
      else AnResBridge.potOf d.R d.A) j y =
      ReciprocityTheory.AnForm.maDens (fun k => if k.val < i then b else a) y := by
    intro i
    show ReciprocityTheory.AnForm.maDens _ y = _
    congr 1
    funext k y'
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  have hpure : (fun _ : Fin D => ReciprocityTheory.AnForm.hessC (fun y' => (1 - t) * a y' + t * b y') y) =
      fun _ => (t : ℂ) • H₁ + (1 - (t : ℂ)) • H₀ := by
    funext k
    show cxHessian _ y = _
    rw [hH, add_comm]
    push_cast
    rfl
  have hmix : ∀ i, (fun k : Fin D => ReciprocityTheory.AnForm.hessC (if k.val < i then b else a) y) =
      fun k : Fin D => if k.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  rw [hL]
  simp only [hR]
  unfold ReciprocityTheory.AnForm.maDens
  rw [hpure, ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem continuous_logRatio (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀)
    (hA' : IsSmoothHerm A') :
    Continuous fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)) := by
  have hA : IsSmoothHerm d.A := d.semipos.1
  have hE : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
      ext z; simp
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hΦ : ContinuousOn (fun z : (Σ k, ι k) → ℂ => Real.log (A'.h z / d.A.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA'.continuousOn.div hA.continuousOn fun z hz => (d.A.pos z hz).ne').log fun z hz =>
      (div_pos (A'.pos z hz) (d.A.pos z hz)).ne'
  have hdeg' : A'.a = d.A.a := hdeg.trans d.deg.symm
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (d.R.isOpen_U x₀).mem_nhds (d.R.mem_U x₀)
  have hl : ContinuousAt (d.R.lift x₀) x₀ :=
    (continuousOn_pi.2 fun p => AnResBridge.continuousOn_lift d.R x₀ p).continuousAt hU
  have h0 : d.R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (d.R.mem x₀ x₀ (d.R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Real.log (A'.h (d.R.lift x₀ x) / d.A.h (d.R.lift x₀ x))) x₀ :=
    (hΦ.continuousAt (hE.mem_nhds h0)).comp hl
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := d.R.compat x x₀ x ⟨d.R.mem_U x, hx⟩
  show _ = Real.log (A'.h (d.R.lift x x) / d.A.h (d.R.lift x x))
  have hp : (∏ k, ‖c k‖ ^ d.A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc0 k))
  rw [he, A'.smul c _ hc0, d.A.smul c _ hc0, hdeg', mul_div_mul_left _ _ hp]

theorem mInt_interp (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀)
    (hA' : IsSmoothHerm A') (t : ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
        (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
            else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) := by
  have hg := continuous_logRatio d hdeg hA'
  have hΦ : ∀ (i : ℕ) (k : Fin D), IsPotential d.R.A
      (if k.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A) := by
    intro i k
    split_ifs
    · exact AnResBridge.isPotential_potOf d.R hA'
    · exact AnResBridge.isPotential_potOf d.R d.semipos.1
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) *
            Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) / d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
            locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
              else AnResBridge.potOf d.R d.A) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) /
                d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
              locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
                else AnResBridge.potOf d.R d.A) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_interp d hA' t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

theorem proof : BlockResolutionInterpIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  unfold blockMetricInt
  simp only [mInt_interp d hdeg hA']
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end BlockResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem exists_nat_mul_mem_adjoin_int {Ω : Type} [Field Ω] [CharZero Ω] (S : Set Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ S) : ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ Algebra.adjoin ℤ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_pos, ?_⟩
    have h : ((r.den : ℕ) : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : ((r.den : ℕ) : Ω) ≠ 0 := by exact_mod_cast r.den_pos.ne'
      rw [eq_ratCast (algebraMap ℚ Ω) r, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [h]
    exact intCast_mem _ _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x + y) = (m : ℤ) • ((n : Ω) * x) + (n : ℤ) • ((m : Ω) * y) := by
      simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
    rw [h]
    exact add_mem (zsmul_mem hnx _) (zsmul_mem hmy _)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
    have h : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [h]
    exact mul_mem hnx hmy

theorem ChartDenominator.proof : ChartDenominator.Statement := by
  intro K _ ι _ Ω _ _ y b τ s hs
  classical
  have key : ∀ c : ∀ k, ι k, ∃ n : ℕ, 1 ≤ n ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose N hN1 hN using key
  refine ⟨∏ c, N c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => by
    have := hN1 c; omega), ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have h : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)) =
      (m : ℤ) • ((N c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)))) := by
    rw [hm]; simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
  rw [h]
  exact zsmul_mem (hN c hc) _

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageGenDeg

open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff diffStep eventualValue intNum)
open fwdDiff

theorem mixedDiff_line {K : Type*} (b m₀ : K → ℤ) (h : (K → ℤ) → ℤ) (D : ℕ) (t : ℤ) :
    mixedDiff (fun _ : Fin D => b) h (m₀ + t • b) = ((fwdDiff 1)^[D] fun s : ℤ => h (m₀ + s • b)) (t - D) := by
  induction D generalizing t with
  | zero => simp [mixedDiff]
  | succ D ih =>
    have hs : mixedDiff (fun _ : Fin (D + 1) => b) h = diffStep b (mixedDiff (fun _ : Fin D => b) h) := by
      simp [mixedDiff, List.ofFn_succ]
    have h1 : m₀ + t • b - b = m₀ + (t - 1) • b := by rw [sub_smul, one_smul, add_sub_assoc]
    have e1 : t - ((D + 1 : ℕ) : ℤ) + 1 = t - D := by push_cast; ring
    have e2 : t - ((D + 1 : ℕ) : ℤ) = t - 1 - D := by push_cast; ring
    rw [hs, diffStep, h1, ih, ih, Function.iterate_succ_apply', fwdDiff, e1, e2]

theorem fwdDiff_iter_eq_poly (φ : ℤ → ℤ) (q : Polynomial ℚ) (D : ℕ) (s : ℤ)
    (h : ∀ j ≤ D, (φ (s + j) : ℚ) = q.eval ((s : ℚ) + j)) :
    (((fwdDiff 1)^[D] φ) s : ℚ) = ((fwdDiff 1)^[D] q.eval) (s : ℚ) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  rw [h j hj']

theorem fwdDiff_iter_poly (q : Polynomial ℚ) {D : ℕ} (hq : q.natDegree ≤ D) (x : ℚ) :
    ((fwdDiff 1)^[D] q.eval) x = q.coeff D * D.factorial := by
  rcases hq.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [q.fwdDiff_iter_degree_eq_factorial]
    rw [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rfl

def lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) : Polynomial ℚ :=
  MvPolynomial.aeval (fun k => if k = k₀ then Polynomial.X else Polynomial.C (m k)) p

theorem eval_lineRestr {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) (t : ℚ) :
    (lineRestr p k₀ m).eval t = MvPolynomial.eval (fun k => if k = k₀ then t else m k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [lineRestr]
  | add p q hp hq => simp only [lineRestr, map_add (f := _), Polynomial.eval_add] at *; rw [hp, hq]
  | mul_X p k hp =>
    simp only [lineRestr, map_mul, Polynomial.eval_mul] at *
    rw [hp]
    by_cases hk : k = k₀ <;> simp [hk]

theorem natDegree_lineRestr_le {K : Type*} [DecidableEq K] (p : MvPolynomial K ℚ) (k₀ : K) (m : K → ℚ) :
    (lineRestr p k₀ m).natDegree ≤ p.totalDegree := by
  rw [lineRestr]
  conv_lhs => rw [p.as_sum]

  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  refine Finset.sum_le_sum fun k _ => (Polynomial.natDegree_pow_le).trans ?_
  have : (if k = k₀ then (Polynomial.X : Polynomial ℚ) else Polynomial.C (m k)).natDegree ≤ 1 := by
    split_ifs <;> simp
  simpa using Nat.mul_le_mul_left (s k) this

theorem eventualValue_eq {K : Type*} (f : (K → ℤ) → ℤ) (e : ℚ) (h : ∀ᶠ m in Filter.atTop, (f m : ℚ) = e) :
    (eventualValue f : ℚ) = e := by
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := by
    obtain ⟨m, hm⟩ := h.exists
    exact ⟨f m, h.mono fun m' hm' => by exact_mod_cast hm'.trans hm.symm⟩
  unfold eventualValue
  rw [dite_eq_left hex]
  obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
  rw [← hm1]
  exact hm2

end BlockImageGenDeg


open GroundTheory.Heights₂.Heights.NumbersDVR (hilbFn mixedDiff eventualValue) in
open BlockImageGenDeg in
theorem BlockImageGenDeg.proof (hMHP : MultigradedHilbertPolynomial.Statement.{0})
    (hGFV : GenericFibreVar.Statement) (hHEP : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement.{0})
    (hHom : GenFibreHomog.Statement) (hImg : BlockImageHilb.Statement) (hBir : BlockBirationalHilbert.Statement)
    (hSand : PolySandwich.Statement) : BlockImageGenDeg.Statement := by
  intro D K _ _ ι _ Ω _ _ κ _ y k₀ M N x hA hB hI
  set PY := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPY
  set PX := (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) with hPX

  obtain ⟨⟨hprime, -, hrel⟩, hdim⟩ := hGFV K ι Ω y D hA
  obtain ⟨pY, a₀, hdeg, hpY⟩ := hMHP ℚ K ι PY D ⟨hprime, hHom K ι Ω y, hrel⟩ hdim

  have hXhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal (ι := GlobalTheory κ) PX := by
    rw [hPX, coordIdeal_eq_mCoordIdeal]; exact hHom Unit (GlobalTheory κ) Ω x
  obtain ⟨pX, hpX⟩ := hHEP ℚ Unit (GlobalTheory κ) PX hXhom
  obtain ⟨aX, haX⟩ := Filter.eventually_atTop.mp hpX
  set p₁ := lineRestr pX () 0 with hp₁
  have hX1 : ∀ n : ℕ, (aX ()).toNat ≤ n → (hilbFn PX (fun _ => (n : ℤ)) : ℚ) = p₁.eval (n : ℚ) := by
    intro n hn
    rw [haX (fun _ => (n : ℤ)) (fun u => by cases u; show aX () ≤ (n : ℤ); omega), hp₁, eval_lineRestr]
    simp

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]

  have hY1 : ∀ (m : K → ℕ) (s : ℕ), (∀ k, k ≠ k₀ → a₀ ≤ m k) → a₀ ≤ s →
      (hilbFn PY (fun k => if k = k₀ then (s : ℤ) else m k) : ℚ) =
        (lineRestr pY k₀ fun k => (m k : ℚ)).eval (s : ℚ) := by
    intro m s hm hs
    have := hpY (fun k => if k = k₀ then s else m k) fun k => by
      by_cases hk : k = k₀ <;> simp [hk, hs, hm k]
    rw [eval_lineRestr]
    convert this using 3 <;> (funext k; by_cases hk : k = k₀ <;> simp [hk])

  have hsand : ∀ m : K → ℕ, (∀ k, k ≠ k₀ → a₀ ≤ m k) →
      p₁.natDegree ≤ D ∧ p₁.coeff D = (lineRestr pY k₀ fun k => (m k : ℚ)).coeff D := by
    intro m hm
    obtain ⟨c, hc⟩ := hBir K ι Ω y k₀ hnz hB m
    refine hSand D c _ _ ((natDegree_lineRestr_le _ _ _).trans hdeg) ?_
    filter_upwards [Filter.eventually_ge_atTop (max a₀ (aX ()).toNat)] with n hn
    have h1 := hX1 n (le_of_max_le_right hn)
    have h2 := hX1 (n + c) ((le_of_max_le_right hn).trans (Nat.le_add_right _ _))
    rw [hImg K ι Ω κ y k₀ M N x hI] at h1 h2
    rw [← hY1 m n hm (le_of_max_le_left hn)]
    push_cast at h2
    rw [← h1, ← h2]
    exact ⟨by exact_mod_cast (hc n).1, by exact_mod_cast (hc n).2⟩
  have hdegX : p₁.natDegree ≤ D := (hsand (fun _ => a₀) fun _ _ => le_rfl).1

  have key : (eventualValue (mixedDiff (fun _ : Fin D => (1 : Unit → ℤ)) (hilbFn PX)) : ℚ) =
      eventualValue (mixedDiff (fun _ : Fin D => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) (hilbFn PY)) := by
    rw [eventualValue_eq (e := p₁.coeff D * D.factorial), eventualValue_eq (e := p₁.coeff D * D.factorial)]
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((a₀ : ℤ) + D), fun m hm => ?_⟩
      have hm' : ∀ k, (a₀ : ℤ) + D ≤ m k := hm
      have hline : m = (fun k => if k = k₀ then 0 else m k) + m k₀ • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ := by
        funext k; by_cases hk : k = k₀ <;> simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ (lineRestr pY k₀ fun k => ((m k).toNat : ℚ)) D,
        fwdDiff_iter_poly _ ((natDegree_lineRestr_le _ _ _).trans hdeg),
        (hsand (fun k => (m k).toNat) fun k _ => by have := hm' k; omega).2]
      intro j hj
      have hs : 0 ≤ m k₀ - D + j := by have := hm' k₀; omega
      have hkey : (fun k => if k = k₀ then 0 else m k) + (m k₀ - D + j) • ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ =
          fun k => if k = k₀ then (((m k₀ - D + j).toNat : ℕ) : ℤ) else (((m k).toNat : ℕ) : ℤ) := by
        funext k
        by_cases hk : k = k₀
        · simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg, Int.toNat_of_nonneg hs]
        · have := hm' k
          simp [hk, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg]
          omega
      rw [hkey, hY1 (fun k => (m k).toNat) _ (fun k _ => by have := hm' k; omega) (by have := hm' k₀; omega)]
      congr 1
      rw [show (((m k₀ - D + j).toNat : ℕ) : ℚ) = ((m k₀ - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring
    · rw [Filter.eventually_atTop]
      refine ⟨fun _ => ((aX ()).toNat + D : ℤ), fun m hm => ?_⟩
      have hm' : ((aX ()).toNat + D : ℤ) ≤ m () := hm ()
      have hline : m = 0 + m () • (1 : Unit → ℤ) := by funext u; cases u; simp
      rw [hline, mixedDiff_line, fwdDiff_iter_eq_poly _ p₁ D, fwdDiff_iter_poly _ hdegX]
      intro j hj
      have hs : 0 ≤ m () - D + j := by omega
      have hkey : (0 : Unit → ℤ) + (m () - D + j) • (1 : Unit → ℤ) = fun _ => (((m () - D + j).toNat : ℕ) : ℤ) := by
        funext u; simp [Int.toNat_of_nonneg hs]
      rw [hkey, hX1 _ (by omega)]
      congr 1
      rw [show (((m () - D + j).toNat : ℕ) : ℚ) = ((m () - D + j : ℤ) : ℚ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hs]]
      push_cast; ring

  apply Int.cast_injective (α := ℚ)
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  convert key using 6 <;> rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
