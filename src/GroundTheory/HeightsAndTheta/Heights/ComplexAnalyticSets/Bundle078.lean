module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Analytic.Polynomial
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set ComplexSets

open scoped ENNReal

noncomputable section

theorem IsSheetAt.eventuallyEq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {γ s : (Fin d → ℂ) → Fin n → ℂ}
    (hγ : IsSheetAt J A x γ) (hs : IsSheetAt J A x s) : γ =ᶠ[𝓝 (A *ᵥ x)] s := by
  obtain ⟨U, hU, hxU, hγd, hγx, hγZ, -⟩ := hγ
  obtain ⟨U', hU', hxU', -, -, -, V, hV, hsV⟩ := hs
  have hc : ContinuousAt γ (A *ᵥ x) := (hγd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hV' : ∀ᶠ y in 𝓝 (A *ᵥ x), γ y ∈ V := hc.preimage_mem_nhds (by rwa [hγx])
  filter_upwards [hU.mem_nhds hxU, hU'.mem_nhds hxU', hV'] with y hy hy' hyV
  obtain ⟨hAy, hZy⟩ := hγZ y hy
  have h := hsV (γ y) ⟨hZy, hyV⟩ (by rwa [hAy])
  rwa [hAy] at h

theorem ConeSheetGramLintegral.proof (hPar : ConeSliceSheetParam.Statement)
    (hArea : ConeMapArea.Statement) : ConeSheetGramLintegral.Statement := by
  classical
  intro n e h J ℓ A F hJ hdim hℓ hA hF
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hinj, hsub, hcov⟩ := hPar n e h J ℓ A hJ hdim hℓ hA

  set v : (Σ k, Fin (N k)) → (Fin e → ℂ) → (Fin n → ℂ) :=
    fun i y => (h.matᵀ)⁻¹ *ᵥ s i.1 i.2 y with hv_def
  have hvd : ∀ i : Σ k, Fin (N k), DifferentiableOn ℂ (v i) (U i.1) := fun i =>
    (Matrix.mulVecLin (h.matᵀ)⁻¹).toContinuousLinearMap.differentiable.comp_differentiableOn
      ((hUD i.1).2.2.2 i.2)

  set H : (Σ k, Fin (N k)) → (Fin e → ℂ) → ℝ≥0∞ := fun i y =>
    ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i y)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) y)
    with hH_def
  have hHm : ∀ i : Σ k, Fin (N k), AEMeasurable (H i) (volume.restrict (D i.1)) := fun i =>
    aemeasurable_coneTerm (hUD i.1).1 (hUD i.1).2.2.1 (hvd i) hF

  set G : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      F (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y)) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (fun y' =>
          (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y) with hG_def

  have hGD : ∀ k, ∀ y ∈ D k, G y = ∑ j : Fin (N k), H ⟨k, j⟩ y := by
    intro k y hy
    obtain ⟨hfe, hinjy, hsh⟩ := hfib k y ((hUD k).2.2.1 hy)
    simp only [hG_def, hfe]
    rw [finsum_mem_range hinjy, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hAy : A *ᵥ s k j y = y := by
      have hmem : s k j y ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y := hfe ▸ ⟨j, rfl⟩
      exact hmem.2
    have hex : ∃ γ, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) γ := ⟨s k j, hsh j⟩
    have hch : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) =ᶠ[𝓝 y] s k j := by
      have h1 : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) = hex.choose := by
        simp only [sheetThrough, dif_pos hex]
      have h2 := hex.choose_spec.eventuallyEq (hsh j)
      rw [hAy] at h2
      rw [h1]
      exact h2
    have hval : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y = s k j y :=
      hch.eq_of_nhds
    have hgram : gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) y') y =
        gramVol (v ⟨k, j⟩) y :=
      gramVol_congr (hch.fun_comp fun f => (h.matᵀ)⁻¹ *ᵥ f)
    simp only [hH_def, hv_def, hval, hgram]

  set G' : (Fin e → ℂ) → ℝ≥0∞ := fun y =>
    ∑' k, (D k).indicator (fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) y with hG'_def
  have hGG' : G =ᵐ[volume] G' := by
    have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ ⋃ k, D k := by
      rw [ae_iff]
      simpa [compl_def] using hnull
    filter_upwards [hae] with y hy
    obtain ⟨k, hk⟩ := mem_iUnion.1 hy
    simp only [hG'_def]
    rw [tsum_eq_single k, indicator_of_mem hk, hGD k y hk]
    intro k' hk'
    exact indicator_of_notMem (fun h' => (hdisj hk').le_bot ⟨h', hk⟩) _
  have hG'm : ∀ k, AEMeasurable ((D k).indicator fun y => ∑ j : Fin (N k), H ⟨k, j⟩ y) volume :=
    fun k => (aemeasurable_indicator_iff (hUD k).2.1).2
      (Finset.aemeasurable_fun_sum _ fun j _ => hHm ⟨k, j⟩)
  refine ⟨(AEMeasurable.tsum hG'm).congr hGG'.symm, ?_⟩

  have hRHS : ∫⁻ y, G y = ∑' i : Σ k, Fin (N k), ∫⁻ y in D i.1, H i y := by
    rw [lintegral_congr_ae hGG', lintegral_tsum hG'm, ENNReal.tsum_sigma']
    refine tsum_congr fun k => ?_
    rw [lintegral_indicator (hUD k).2.1, lintegral_finsetSum' _ fun j _ => hHm ⟨k, j⟩,
      tsum_fintype]

  have hLHS : ∫⁻ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      ∫⁻ z in (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}, F z
        ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
    refine setLIntegral_congr (ae_eq_set.2 ⟨hcov, ?_⟩)
    rw [sdiff_eq_empty.2 hsub, measure_empty]
  have hMap := hArea n e (Σ k, Fin (N k)) (fun i => U i.1) (fun i => D i.1) v F
    (fun i => ⟨(hUD i.1).1, (hUD i.1).2.1, (hUD i.1).2.2.1, hvd i⟩) hinj hF
  rw [hLHS, hMap]
  exact congrArg _ hRHS.symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem NormalModelGoodPointChart.proof : NormalModelGoodPointChart.Statement := by
  classical
  intro n d J u M w hgood
  obtain ⟨hw, c, f, h, g, a, b, k, hc, hfJ, hh, hsat, hg, hli, hk, ha, hb, hrel, himm⟩ := hgood

  let Φ : ((Fin n ⊕ Fin M.m → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (Fin n ⊕ Fin M.m → ℂ) :=
    { toFun := fun L s => L (Pi.single s 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let D : Fin (c + 1) → (Fin n ⊕ Fin M.m → ℂ) →L[ℂ] ℂ :=
    Fin.cons (fderiv ℂ (fun z => eval z g) w) (fun j => fderiv ℂ (fun z => eval z (f j)) w)
  have hDli : LinearIndependent ℂ D := by
    refine LinearIndependent.of_comp Φ ?_
    convert hli using 1
    funext i s
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [D, Φ, NormalModelGoodPointChart.fderiv_eval_apply, Pi.single_apply]
    · simp [D, Φ, NormalModelGoodPointChart.fderiv_eval_apply, Pi.single_apply]
  obtain ⟨A, hA⟩ := NormalModelGoodPointChart.exists_clm_ker_inf
    (LinearMap.pi fun i => (D i : (Fin n ⊕ Fin M.m → ℂ) →ₗ[ℂ] ℂ))
    (IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.pi_surjective_of_linearIndependent hDli) d
    (by simp [Module.finrank_fintype_fun_eq_card]; omega)

  let q : Fin (d + 1) ⊕ Fin c → (Fin n ⊕ Fin M.m → ℂ) → ℂ :=
    Sum.elim (Fin.cons (fun z => eval z g) (fun i z => A (z - w) i)) (fun j z => eval z (f j))
  have hq0 : q (Sum.inl 0) = fun z => eval z g := by simp [q]
  have hqs : ∀ i : Fin d, q (Sum.inl i.succ) = fun z => A (z - w) i := fun i => by simp [q]
  have hAd : ∀ (i : Fin d) x, HasFDerivAt (fun z => A (z - w) i)
      ((ContinuousLinearMap.proj i).comp A) x := fun i x => by
    have e : (fun z => A (z - w) i) = fun z => ((ContinuousLinearMap.proj i).comp A) z - A w i := by
      funext z; simp [map_sub]
    rw [e]
    exact ((ContinuousLinearMap.proj i).comp A).hasFDerivAt.sub_const _
  have hqan : ∀ k x, AnalyticAt ℂ (q k) x := by
    intro k x
    rcases k with i | j
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [hq0]; exact AnalyticOnNhd.eval_mvPolynomial g x trivial
      · rw [hqs]
        have e : (fun z => A (z - w) i) = fun z => ((ContinuousLinearMap.proj i).comp A) z - A w i := by
          funext z; simp [map_sub]
        rw [e]
        exact (((ContinuousLinearMap.proj i).comp A).analyticAt x).sub analyticAt_const
    · exact AnalyticOnNhd.eval_mvPolynomial (f j) x trivial
  set W : Set (Fin n ⊕ Fin M.m → ℂ) := {z | eval z h ≠ 0 ∧ eval z a ≠ 0 ∧ eval z b ≠ 0} with hWdef
  have hWo : IsOpen W :=
    (isOpen_ne_fun (continuous_eval h) continuous_const).inter
      ((isOpen_ne_fun (continuous_eval a) continuous_const).inter
        (isOpen_ne_fun (continuous_eval b) continuous_const))
  obtain ⟨V, O, φ, hVo, hwV, hVW, hOo, hφan, hφV, hφl, hφr, hback, hder⟩ :=
    NormalModelGoodPointChart.exists_coordChart q w W (fun k => hqan k w) (by
      intro v hv
      refine hA v ?_ ?_
      · funext i
        have := hv (Sum.inl i.succ)
        rw [hqs, (hAd i w).fderiv] at this
        simpa using this
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have := hv (Sum.inl 0)
          rw [hq0] at this
          simpa [D] using this
        · have := hv (Sum.inr j)
          change fderiv ℂ (fun z => eval z (f j)) w v = 0 at this
          simpa [D] using this)
      (by simp; omega) (hWo.mem_nhds ⟨hh, ha, hb⟩)

  have hZf : ∀ z ∈ V, (∀ j, eval z (f j) = 0) → z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := by
    intro z hz hfz p hp
    obtain ⟨e, he⟩ := hsat p hp
    have hker : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) :=
      Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact RingHom.mem_ker.2 (hfz j))
    have h0 := RingHom.mem_ker.1 (hker he)
    rw [map_mul, map_pow] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (hVW hz).1)
  have hφZ : ∀ t ∈ O, φ t ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := fun t ht => hZf _ (hφV t ht) (hφr t ht)

  have hp0 : (fun i => q (Sum.inl i) w) = 0 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [hq0] using hg
    · simp [hqs]
  obtain ⟨hO0, hφ0⟩ := hback w hwV (fun j => hw _ (hfJ j))
  rw [hp0] at hO0 hφ0
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo 0 hO0
  have hpc : Continuous fun z i => q (Sum.inl i) z :=
    continuous_pi fun i => continuous_iff_continuousAt.2 fun x => (hqan _ x).continuousAt
  refine ⟨r, φ, k, hr, fun t ht => (hφan t (hrO ht)).differentiableAt.differentiableWithinAt,
    fun x hx y hy hxy => funext fun i => by rw [← hφl x (hrO hx) i, ← hφl y (hrO hy) i, hxy],
    hφ0, fun t ht => hφZ t (hrO ht), ?_, ?_, ?_⟩
  ·
    intro s hs
    refine ⟨V ∩ (fun z i => q (Sum.inl i) z) ⁻¹' Metric.ball 0 s,
      Filter.inter_mem (hVo.mem_nhds hwV) (hpc.continuousAt.preimage_mem_nhds (by
        rw [hp0]; exact Metric.ball_mem_nhds 0 hs)), ?_⟩
    rintro z ⟨hzZ, hzV, hzs⟩
    exact ⟨_, hzs, (hback z hzV fun j => hzZ _ (hfJ j)).2⟩
  ·
    refine ⟨fun t => eval (φ t) a / eval (φ t) b, ?_, ?_, ?_⟩
    · intro t ht
      have hφt := (hφan t (hrO ht)).differentiableAt
      have h1 : DifferentiableAt ℂ (fun t => eval (φ t) a) t :=
        (AnalyticOnNhd.eval_mvPolynomial a (φ t) trivial).differentiableAt.comp t hφt
      have h2 : DifferentiableAt ℂ (fun t => eval (φ t) b) t :=
        (AnalyticOnNhd.eval_mvPolynomial b (φ t) trivial).differentiableAt.comp t hφt
      have h3 : DifferentiableAt ℂ (fun t => eval (φ t) a * (eval (φ t) b)⁻¹) t :=
        h1.mul (h2.inv (hVW (hφV t (hrO ht))).2.2)
      simpa only [div_eq_mul_inv] using h3.differentiableWithinAt
    · intro t ht
      have hW' := hVW (hφV t (hrO ht))
      exact div_ne_zero hW'.2.1 hW'.2.2
    · intro t ht
      have hW' := hVW (hφV t (hrO ht))
      have hz := hφZ t (hrO ht) _ hrel
      have hgt : eval (φ t) g = t 0 := by simpa [hq0] using hφl t (hrO ht) 0
      have hl : eval (φ t) (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)) =
          linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) := by

        simp [linForm, linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords, map_sum]
      simp only [map_sub, map_mul, map_pow, hl, hgt] at hz
      field_simp [hW'.2.2]
      linear_combination hz
  ·
    intro v hv0 hν
    have hDd := hder 0 hO0 v
    rw [hφ0] at hDd
    set x := fderiv ℂ φ 0 v with hx
    let πL : (Fin n ⊕ Fin M.m → ℂ) →L[ℂ] (Fin n → ℂ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ⊕ Fin M.m => ℂ) (Sum.inl i)
    have hπ : HasFDerivAt (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) (πL.comp (fderiv ℂ φ 0)) 0 :=
      πL.hasFDerivAt.comp 0 (hφan 0 hO0).differentiableAt.hasFDerivAt
    rw [hπ.fderiv] at hν
    have hx0 : x = 0 := by
      refine himm x (fun i => by simpa [πL, hx] using congrFun hν i) ?_ ?_
      · have := hDd.1 0
        rw [hq0, NormalModelGoodPointChart.fderiv_eval_apply] at this
        rw [this, hv0]
      · intro j
        have := hDd.2 j
        rwa [show q (Sum.inr j) = fun z => eval z (f j) from rfl,
          NormalModelGoodPointChart.fderiv_eval_apply] at this
    funext i
    have := hDd.1 i
    rw [hx0, map_zero] at this
    simpa using this.symm

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem hadamard_decomposition {σ : Type} [Fintype σ] {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f w) :
    ∃ g : σ → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) w) ∧
      ∀ᶠ z in 𝓝 w, f z = f w + ∑ i, (z i - w i) * g i z := by
  classical
  obtain ⟨p, r, hp⟩ := hf
  have hrad : p.shift.radius = p.radius := FormalMultilinearSeries.radius_shift p
  have hq : 0 < p.shift.radius := by rw [hrad]; exact lt_of_lt_of_le hp.r_pos hp.r_le
  have hG : HasFPowerSeriesOnBall p.shift.sum p.shift 0 p.shift.radius :=
    p.shift.hasFPowerSeriesOnBall hq
  refine ⟨fun i z => p.shift.sum (z - w) (Pi.single i 1), fun i => ?_, ?_⟩
  · have h2 : AnalyticAt ℂ (fun z : σ → ℂ => z - w) w := analyticAt_id.sub analyticAt_const
    have h3 : AnalyticAt ℂ p.shift.sum ((fun z : σ → ℂ => z - w) w) := by
      simpa using hG.analyticAt
    exact ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ))).analyticAt _).comp
      (AnalyticAt.comp (g := p.shift.sum) (f := fun z : σ → ℂ => z - w) h3 h2)
  · filter_upwards [Metric.eball_mem_nhds w hp.r_pos] with z hz
    set y := z - w with hy
    have hy0 : y ∈ Metric.eball (0 : σ → ℂ) r := by
      rw [Metric.mem_eball] at hz ⊢
      rwa [edist_zero_right, hy, ← edist_eq_enorm_sub]
    have hy1 : y ∈ Metric.eball (0 : σ → ℂ) p.shift.radius :=
      Metric.eball_subset_eball (hrad ▸ hp.r_le) hy0
    have h1 := hp.hasSum hy0
    have h2 := hG.hasSum hy1
    rw [zero_add] at h2
    have h3 := (ContinuousLinearMap.apply ℂ ℂ y).hasSum h2
    have h4 : ∀ n, (ContinuousLinearMap.apply ℂ ℂ y) (p.shift n fun _ => y) =
        p (n + 1) fun _ => y := by
      intro n
      simp only [ContinuousLinearMap.apply_apply, FormalMultilinearSeries.shift,
        ContinuousMultilinearMap.curryRight_apply]
      congr 1
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp
    simp only [h4, ContinuousLinearMap.apply_apply] at h3
    have h5 := (hasSum_nat_add_iff' 1).mpr h1
    simp only [Finset.range_one, Finset.sum_singleton, hp.coeff_zero] at h5
    have e := h5.unique h3
    have hwz : w + y = z := by rw [hy]; abel
    rw [hwz] at e
    have e2 : p.shift.sum y y = ∑ i, (z i - w i) * p.shift.sum y (Pi.single i 1) := by
      have hyy : p.shift.sum y y = p.shift.sum y (∑ i, Pi.single i (y i)) := by
        rw [Finset.univ_sum_single]

      rw [hyy, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (y i) : σ → ℂ) = y i • Pi.single i 1 by
        ext j; by_cases h : j = i
        · subst h; simp
        · simp [h], map_smul, smul_eq_mul, hy, Pi.sub_apply]
    rw [← e2, ← e]
    ring

theorem HolGermPointIdealSpan.proof : HolGermPointIdealSpan.Statement := by
  intro σ _ w
  apply le_antisymm
  · rintro ⟨_, f, hf, rfl⟩ hφ
    have hfw : f w = 0 := hφ
    obtain ⟨g, hg, hfg⟩ := hadamard_decomposition hf
    have key : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) =
        ∑ i, polyGerm w (X i - C (w i)) * ⟨(g i : Germ (𝓝 w) ℂ), g i, hg i, rfl⟩ := by
      apply Subtype.ext
      change (f : Germ (𝓝 w) ℂ) = (holGerms w).subtype (∑ i, _)

      rw [map_sum]
      simp only [map_mul, Subring.coe_subtype]
      have hsum : ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) =
          ∑ i, ((fun z : σ → ℂ => z i - w i : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) * (g i : Germ (𝓝 w) ℂ) := by
        change Germ.coeRingHom (𝓝 w) (fun z => ∑ i, (z i - w i) * g i z) = _

        rw [show (fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) =
          ∑ i, (fun z : σ → ℂ => z i - w i) * g i by
        funext z; simp [Finset.sum_apply], map_sum]
        rfl
      have hfe : (f : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, (z i - w i) * g i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) :=
        Germ.coe_eq.mpr (hfg.mono fun z hz => by rw [hz, hfw, zero_add])
      rw [hfe, hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      change _ = ((fun z : σ → ℂ => eval z (X i - C (w i)) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
      simp
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change holGermValue w (polyGerm w (X i - C (w i))) = 0
    rw [holGermValue_polyGerm]
    simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimeGermFiniteProjection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
      (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → IsGermCombination w p (fun z => h (A z)) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
          IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def VarLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y ≤
        r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y

end

end GroundTheory.Heights₂.Heights
end
