module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Set Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace PointsAbsMeasurable

section PushForward

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem integrable_absPushSum [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, |g x * pushDens A Φ q x|) := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set Pt := hne.some with hPt
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    |Pt.χ j ((A.chart j).symm u) * g ((A.chart j).symm u) * locDens A Φ j u| with hhj
  set Qj : Fin A.n → (Fin e → ℂ) → (Fin e → ℂ) := fun j => q ∘ (A.chart j).symm with hQj
  set N : Fin A.n → Set (Fin e → ℂ) :=
    fun j => Qj j '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S) with hNdef
  have hN : ∀ j, volume (N j) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null (inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j)
  have hfib : ∀ j, ∀ y ∉ N j, goodT A q j ∩ Qj j ⁻¹' {y} =
      (A.chart j) '' ((A.chart j).source ∩ (q ⁻¹' {y} \ S)) :=
    fun j y hy => goodT_fibre_eq A q S hq j hy
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ Qj j ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [hfib j y hy]
    exact ((hfin y).subset inter_subset_right).image _
  have hint : ∀ j, Integrable (fibSum (goodT A q j) (Qj j) (hj j)) := fun j =>
    (area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((show IntegrableOn (hj j) (A.chart j).target volume from
        (integrableOn_chart A Pt Φ g hg j).abs).mono_set fun u hu => hu.1) (hfinj j)).1
  refine (integrable_finsetSum Finset.univ fun j _ => hint j).congr ?_
  have hNall : ∀ᵐ y, ∀ j, y ∉ N j :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp (hN j)
  filter_upwards [hNall] with y hy
  have hterm : ∀ j, fibSum (goodT A q j) (Qj j) (hj j) y =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, Pt.χ j x * |g x * pushDens A Φ q x| := by
    intro j
    unfold fibSum
    rw [hfib j y (hy j), finsum_mem_image ((A.chart j).injOn.mono inter_subset_left)]
    refine (finsum_mem_congr (g := fun x => Pt.χ j x * |g x * pushDens A Φ q x|) rfl
      fun x hx => ?_).trans ?_
    · have hJ : 0 ≤ jacN (Qj j) (A.chart j x) := by unfold jacN; positivity
      calc hj j (A.chart j x) / jacN (Qj j) (A.chart j x)
          = |Pt.χ j ((A.chart j).symm (A.chart j x)) * g ((A.chart j).symm (A.chart j x)) *
              locDens A Φ j (A.chart j x) / jacN (Qj j) (A.chart j x)| := by
            rw [abs_div, abs_of_nonneg hJ]
        _ = |Pt.χ j x * (g x * pushDens A Φ q x)| := by
            rw [fib_term A Φ hΦ q S hq Pt g j hx.1 hx.2.2]
        _ = Pt.χ j x * |g x * pushDens A Φ q x| := by
            rw [abs_mul, abs_of_nonneg (Pt.nonneg j x)]
    · refine finsum_mem_inter_support_eq' _ _ _ fun x hx => ?_
      have hχ : Pt.χ j x ≠ 0 := left_ne_zero_of_mul hx
      have hxs : x ∈ (A.chart j).source := Pt.tsupport_subset j (subset_tsupport _ hχ)
      exact ⟨fun h => h.2, fun h => ⟨hxs, h⟩⟩
  simp_rw [hterm]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, Pt.sum_eq_one x, one_mul]

end PushForward

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem absFibreSum_ae (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        |logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x| := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    measure_eq_zero_iff_ae_notMem.mp hN
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono (by exact fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩))]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dite_eq_left ⟨γ, hγ⟩]
  exact congrArg abs
    ((hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval)

end Res

end PointsAbsMeasurable


open PointsAbsMeasurable in
theorem PtsAbsMeasurable.proof (hE : ResExistsStatement) : PtsAbsMeasurable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  have hI := integrable_absPushSum R.A (fun j => potOf R (L j))
    (fun j => potOf_isPotential R (L j) (hL j)) (brQ R Ψ) (brBad R Ψ) (brBad_null R Ψ hP hΨ)
    (brGood R Ψ) (brFib_finite R Ψ hP hΨ) _ (brIntegrable R L A s hP hL hA hs)
  exact hI.aestronglyMeasurable.congr
    ((absFibreSum_ae R Ψ L A s hP hΨ hL hA hs).mono fun y hy => hy.symm)

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsRegLimit.abs_half_log_le {x ε : ℝ} (hx : x ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (x ^ 2 + ε) / 2| ≤ |Real.log x| + |Real.log (x ^ 2 + 1) / 2| := by
  have h2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))
  have hlo : Real.log x ≤ Real.log (x ^ 2 + ε) / 2 := by
    have : Real.log x = Real.log (x ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
    rw [this]
    exact div_le_div_of_nonneg_right (Real.log_le_log h2 (by linarith)) (by norm_num)
  have hhi : Real.log (x ^ 2 + ε) / 2 ≤ Real.log (x ^ 2 + 1) / 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log x), abs_nonneg (Real.log (x ^ 2 + 1) / 2)]
  · linarith [le_abs_self (Real.log (x ^ 2 + 1) / 2), abs_nonneg (Real.log x)]

theorem PtsRegLimit.tendsto_half_log {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) (𝓝[>] 0) (𝓝 (Real.log x)) := by
  have h2 : x ^ 2 + 0 ≠ 0 := by rw [add_zero]; exact pow_ne_zero 2 hx
  have hc : ContinuousAt (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) 0 :=
    ((continuousAt_const.add continuousAt_id).log h2).div_const 2
  have hv : Real.log (x ^ 2 + 0) / 2 = Real.log x := by
    rw [add_zero, Real.log_pow]; push_cast; ring
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem PtsRegLimit.proof (hInt : PtsIntegrableStatement) (hAbs : PtsAbsIntegrable.Statement) :
    PtsRegLimit.Statement := by
  intro K _ ι _ Q e M E t ht hQ hM hE htQ
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · simp only [dif_neg hΨ]
    exact tendsto_const_nhds
  simp only [dif_pos hΨ]
  have hgood := hΨ.choose_spec
  generalize hΨ.choose = Ψ at hgood ⊢
  unfold ptsIntegralAt
  obtain ⟨a, haE, hta⟩ := id ht
  have hfin : ∀ y, (fibre Q Ψ y).Finite := fibreFinite K ι Q e Ψ hQ hgood
  have h1 : (1 : MRing ι) ∉ Q := fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  have hone : ∀ ε, IsSectionOn Q (regLine E t ht ε) 1 := fun ε =>
    ⟨fun _ => 0, fun k => by rw [regLine_a]; simp, fun m hm k => by
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp, h1⟩

  have hsdlog : ∀ (B : HermLine ι) y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (B.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm B 1) y w := by
    intro B y w
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, logNorm, map_one, norm_one, one_div, Real.log_inv]
      ring
    · simp only [sheetDensity, dif_neg hγ, neg_zero]
  have hFint : ∀ ε, 0 < ε → Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht ε).h z)) y w) := by
    intro ε hε
    refine (hInt K ι Q e Ψ M (regLine E t ht ε) 1 hQ hgood hM (isSmoothHerm_regLine hE hε)
      (hone ε)).neg.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w _ => (hsdlog _ y w).symm

  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJP : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hN : ∀ᵐ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ := compl_mem_ae_iff.mpr (projB_null Ψ hQ hgood hJ hJP)
  have hpt : ∀ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ → ∀ w (hγ : ∃ γ, IsSheet Q Ψ y w γ), secNorm E t (hγ.choose y) ≠ 0 := by
    intro y hy w hγ h0
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hev0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact norm_eq_zero.mp h
      · exact absurd h (E.pos _ hmem.1).ne'
    refine hy ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hev0, mul_zero]
  have hB1 : ∀ z, |Real.log ((regLine E t ht 1).h z)| = |Real.log (secNorm E t z ^ 2 + 1) / 2| := fun z => by
    rw [log_regLine_h]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => ∑ᶠ w ∈ fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (logNorm E t) y w| +
      ∑ᶠ w ∈ fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht 1).h z)) y w|)
    (eventually_mem_nhdsWithin.mono fun ε hε => (hFint ε hε).aestronglyMeasurable) ?_ ?_ ?_
  ·
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hN] with y hy
    rw [Real.norm_eq_abs, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [hB1, log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.abs_half_log_le (hpt y hy w hγ) hε.1 hε.2.le
    · simp only [sheetDensity, dif_neg hγ, abs_zero, add_zero, le_refl]
  ·
    have hts : IsSectionOn Q E t := ⟨a, haE, hta, htQ⟩
    refine (hAbs K ι Q e Ψ M E t hQ hgood hM hE hts).add ((hAbs K ι Q e Ψ M (regLine E t ht 1) 1 hQ hgood hM
      (isSmoothHerm_regLine hE one_pos) (hone 1)).congr (Eventually.of_forall fun y => ?_))
    exact finsum_mem_congr rfl fun w _ => by rw [hsdlog, abs_neg]
  ·
    filter_upwards [hN] with y hy
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun w _ => ?_
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ]
      refine Tendsto.mul_const _ ?_
      simp only [log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.tendsto_half_log (hpt y hy w hγ)
    · simp only [sheetDensity, dif_neg hγ]
      exact tendsto_const_nhds

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem mem_mcPts_span_singleton {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hs : eval z (map (Int.castRingHom ℂ) s) = 0) : z ∈ mcPts (Ideal.span {s}) := by
  refine ⟨hz.1, fun f hf => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rw [map_mul, map_mul, hs, mul_zero]

theorem ZeroSetNull.proof : ZeroSetNull.Statement := by
  intro K _ ι _ P e s a φ g₁ g₂ hP hs hsP hg
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  · rw [dite_eq_left hΨ, dite_eq_left hΨ]
    set Ψ := hΨ.choose with hΨdef
    have hJ : IsMultiHomogIdeal (Ideal.span {s}) :=
      ⟨{s}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hs⟩, rfl⟩
    have hJP : ¬ Ideal.span {s} ≤ P := fun h => hsP (h (Ideal.subset_span rfl))
    have hnull := projB_null Ψ hP hΨ.choose_spec hJ hJP
    unfold ptsIntegralAt
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun y hy => ?_) hnull
    by_contra hyB
    apply hy
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · rw [dite_eq_left hγ, dite_eq_left hγ]
      obtain ⟨-, hev⟩ := hγ.choose_spec
      obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
      have hs0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) s) ≠ 0 := fun h0 =>
        hyB ⟨hγ.choose y, hmem, mem_mcPts_span_singleton hmem h0, hproj⟩
      rw [hg _ hmem hs0]
    · rw [dite_eq_right hγ, dite_eq_right hγ]
  · rw [dite_eq_right hΨ, dite_eq_right hΨ]

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityLocalize.exists_prime_over {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hW : IsClosedPt W) :
    ∃ p : ℤ, Prime p ∧ ∀ k : ℤ, C k ∈ W ↔ p ∣ k := by
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  have : W.IsPrime := hW.1.1
  have : (W.comap (C : ℤ →+* MRing ι)).IsPrime := Ideal.IsPrime.comap _
  refine ⟨_, Submodule.IsPrincipal.prime_generator_of_isPrime _ hvert, fun k => ?_⟩
  rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap]

theorem RegularityLocalize.proof (h₁ : RegularityLocalPrime.Statement) : RegularityLocalize.Statement := by
  classical
  intro K _ ι _ P W y hP hW hPW hy
  have hPp : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1
  have hφ : ∀ f : MRing ι, f ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ≠ 0 :=
    fun f hf => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hf
  obtain ⟨p, hp, hpW⟩ := RegularityLocalize.exists_prime_over hP hW
  have hCpP : (C p : MRing ι) ∉ P := fun h => hp.ne_zero (by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rwa [hP.2.2.1, Ideal.mem_bot] at h')

  set S : Set (Ideal (MRing ι)) := {W' | IsClosedPt W' ∧ P ≤ W' ∧ C p ∈ W'} with hS
  have hSfin : S.Finite := (divSupp_finite P (C p)).subset fun W' hW' =>
    (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W' hP (RegularityDenominator.isMultiHomog_C p) hCpP).2 hW'
  have hWS : W ∈ S := ⟨hW, hPW, (hpW p).2 dvd_rfl⟩
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid S hSfin fun W' hW' => hW'.1.1

  obtain ⟨u₀, v₀, a, hu₀, hv₀, hv₀W, hyv₀⟩ := LocRingFrac.proof K ι P W hPp hWp hPW y hy
  choose c hc using hW.1.2.2
  obtain ⟨t, ht, htW⟩ : ∃ t : MRing ι, IsMultiHomog t 1 ∧ t ∉ W :=
    ⟨_, AvoidRing.isMultiHomog_coordProd c 1, AvoidRing.coordProd_not_mem hWp c hc 1⟩
  obtain ⟨u, v, hu, hv, hvW, hyv⟩ : ∃ u v : MRing ι, IsMultiHomog u (a + 1) ∧ IsMultiHomog v (a + 1) ∧ v ∉ W ∧
      y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) :=
    ⟨u₀ * t, v₀ * t, AvoidRing.isMultiHomog_mul hu₀ ht, AvoidRing.isMultiHomog_mul hv₀ ht,
      fun h => (hWp.mem_or_mem h).elim hv₀W htW, by simp only [map_mul, ← mul_assoc, hyv₀]⟩

  set m := ∑ k, d₀ k
  obtain ⟨h, hh, hhS⟩ := hd₀ ((m + 1) • (a + 1)) fun k => by
    have h1 : d₀ k ≤ m := Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    nlinarith
  have hhW : h ∉ W := hhS W hWS
  have hhP : h ∉ P := fun e => hhW (hPW e)
  have hvm : IsMultiHomog (v ^ (m + 1)) ((m + 1) • (a + 1)) := AvoidRing.isMultiHomog_pow hv _
  have hxm : IsMultiHomog (v ^ m * u) ((m + 1) • (a + 1)) := by
    rw [succ_nsmul]; exact AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_pow hv _) hu
  obtain ⟨s₀, hs₀⟩ := exists_funField_mul_eq hvm hh hhP
  obtain ⟨x₀, hx₀⟩ := exists_funField_mul_eq hxm hh hhP
  have hys : y * (s₀ : FractionRing (MRing ι ⧸ P)) = x₀ := by
    refine mul_right_cancel₀ (hφ h hhP) ?_
    rw [mul_assoc, hs₀, hx₀]
    simp only [map_pow, map_mul]
    rw [pow_succ, ← hyv]
    ring

  have hover : ∀ z : funField P, (∃ g : MRing ι, IsMultiHomog g ((m + 1) • (a + 1)) ∧
      (z : FractionRing (MRing ι ⧸ P)) * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P h) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
      ∀ W', IsClosedPt W' → P ≤ W' → C p ∈ W' → (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W' :=
    fun z ⟨g, hg, hz⟩ W' h1 h2 h3 => frac_mem_locRing h2 hg hh (hhS W' ⟨h1, h2, h3⟩) hz
  obtain ⟨n₁, hn₁, hs⟩ := h₁ K ι P p s₀ hP hp (hover s₀ ⟨_, hvm, hs₀⟩)
  obtain ⟨n₂, hn₂, hx⟩ := h₁ K ι P p x₀ hP hp (hover x₀ ⟨_, hxm, hx₀⟩)
  have hsc : (((n₂ : regRing P) * ⟨_, hs⟩ : regRing P) : funField P) = (n₂ : funField P) * ((n₁ : funField P) * s₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  have hxc : (((n₁ : regRing P) * ⟨_, hx⟩ : regRing P) : funField P) = (n₁ : funField P) * ((n₂ : funField P) * x₀) := by
    rw [Subring.coe_mul, Subring.coe_intCast, Subtype.coe_mk]
  refine ⟨(n₂ : regRing P) * ⟨_, hs⟩, (n₁ : regRing P) * ⟨_, hx⟩, ?_, ?_⟩
  ·
    have hnW : (C (n₁ * n₂) : MRing ι) ∉ W := fun e => by
      rcases hp.dvd_or_dvd ((hpW _).1 e) with h' | h'
      exacts [hn₁ h', hn₂ h']
    have hden : IsMultiHomog (C (n₁ * n₂) * v ^ (m + 1)) ((m + 1) • (a + 1)) := by
      simpa using AvoidRing.isMultiHomog_mul (RegularityDenominator.isMultiHomog_C (n₁ * n₂)) hvm
    have hdenW : C (n₁ * n₂) * v ^ (m + 1) ∉ W := fun e =>
      (hWp.mem_or_mem e).elim hnW fun e' => hvW (hWp.mem_of_pow_mem _ e')
    have hden0 := hφ _ fun e => hdenW (hPW e)
    refine ⟨_, frac_mem_locRing hPW hh hden hdenW (div_mul_cancel₀ _ hden0), ?_⟩
    rw [hsc, mul_div_assoc', div_eq_one_iff_eq hden0]
    simp only [map_mul, eq_intCast C, map_intCast, Int.cast_mul, Subring.coe_mul, Subring.coe_intCast, ← hs₀]
    ring
  · rw [hsc, hxc]
    simp only [Subring.coe_mul, Subring.coe_intCast, ← hys]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end
