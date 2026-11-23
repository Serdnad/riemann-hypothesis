module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle006
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle001
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem localMult_ker_eval_eq_zero {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∈ J) (hgq : eval q g ≠ 0) :
    localMult J (RingHom.ker (eval q)) = 0 := by
  have htop : J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
      (IsLocalization.map_units _ (⟨g, fun h ↦ hgq (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl))
  have hs := Ideal.Quotient.subsingleton_iff.2 htop
  rw [localMult, dite_eq_left (isPrime_ker_eval q), Module.length_eq_zero_iff.2 hs]
  rfl

theorem CurveBranchLength.proof (hN : CurveNormalisationLength.Statement)
    (hB : BranchNormalisation.Statement) : CurveBranchLength.Statement := by
  intro n I u q m c ord hrad hcov hdisj hord
  have hlin : ∀ x, eval x (linForm u) = linEval u x := fun x ↦ by simp [linForm, linEval]
  have hq0 : ∀ b, linEval u q = 0 ↔ 0 < ord b := by
    intro b
    obtain ⟨H, -, hH, hF⟩ := hord b
    have h0 := hF 0 (Metric.mem_ball_self (c b).radius_pos)
    simp only [(c b).map_zero] at h0
    rw [h0]
    simp [hH 0 (Metric.mem_ball_self (c b).radius_pos), Nat.pos_iff_ne_zero]
  by_cases hmain : linEval u q = 0 ∧ 0 < m
  swap
  · have hsum : ∑ b, ord b = 0 := Finset.sum_eq_zero fun b _ ↦ by
      by_contra hb
      exact hmain ⟨(hq0 b).2 (Nat.pos_of_ne_zero hb), Fin.pos_iff_nonempty.2 ⟨b⟩⟩
    rw [hsum]
    by_cases hu : linEval u q = 0
    · have hm : m = 0 := by by_contra hm; exact hmain ⟨hu, Nat.pos_of_ne_zero hm⟩
      subst hm
      obtain ⟨N, hNq, hsub⟩ := hcov
      have hq : q ∉ zeroSet I := fun hq ↦ by simpa using hsub ⟨hq, mem_of_mem_nhds hNq⟩
      obtain ⟨g, hg, hgq⟩ : ∃ g ∈ I, eval q g ≠ 0 := by
        by_contra h
        push Not at h
        exact hq h
      exact localMult_ker_eval_eq_zero (Ideal.mem_sup_left hg) hgq
    · exact localMult_ker_eval_eq_zero (Ideal.mem_sup_right (Ideal.subset_span rfl)) (by rwa [hlin])
  obtain ⟨hu0, hm⟩ := hmain
  have hpt : ∀ b, ∀ x ∈ (c b).image, linEval u x = 0 → x = q := by
    rintro b _ ⟨t, ht, rfl⟩ hx
    obtain ⟨H, -, hH, hF⟩ := hord b
    rw [show linEval u ((c b).toFun t) = t 0 ^ ord b * H t from hF t ht, mul_eq_zero] at hx
    have ht0 : t 0 = 0 := hx.elim eq_zero_of_pow_eq_zero fun h ↦ absurd h (hH t ht)
    have ht' : t = 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]; exact ht0
    rw [ht', (c b).map_zero]
  obtain ⟨hdim, hnzd, e, he⟩ := hB n I q m c hrad hm hcov
    fun b b' hbb x hx ↦ hpt b x hx.1 (hdisj b b' hbb hx)
  have hordb : ∀ b, branchOrder (c b) (linForm u) = ord b := fun b ↦
    branchOrder_eq_of_vanishesToOrder (c b) _ _ (by simpa only [hlin] using hord b)
  have hL := hN n I q (linForm u) hrad hdim (hnzd _ fun b ↦ by rw [hordb b]; exact ENat.natCast_ne_top _)
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype] at hL
  simp only [(he _).1, mul_one, (he _).2, hordb] at hL
  exact_mod_cast hL

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace CutOffDominated

variable {n d : ℕ}

theorem chartDens_congr_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f g : (Fin n → ℂ) → ℝ} (h : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    chartDens J A f φ = chartDens J A g φ := by
  funext y
  unfold chartDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]


open Classical in
theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0 :=
  finsum_mem_eq_finite_toFinset_sum _ hfin

theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

end CutOffDominated

theorem CutOffDominated.proof : CutOffDominated.Statement := by
  classical
  intro n d J A P χ f ψ hJ hdim hA hP hχm hχ01 hlim hf hψ hint
  have hfin : ∀ y, (fibre J A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
  set g : (Fin n → ℂ) → ℝ := (zeroSet J).piecewise f 0 with hgdef
  have hg : Measurable g :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : ∀ k, Measurable (chartDens J A (fun x => χ k x * f x) ψ) := fun k => by
    rw [CutOffDominated.chartDens_congr_zeroSet (g := fun x => χ k x * g x)
      (fun x hx => by rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hx])]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA ((hχm k).mul hg) hψ).1
  refine tendsto_integral_of_dominated_convergence (chartAbsDens J A f ψ)
    (fun k => (hmeas k).aestronglyMeasurable) hint (fun k => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with h
    · rw [mul_assoc, abs_mul, abs_of_nonneg (hχ01 k x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 k x).2
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    have hxl := hlim x hx.1 (by rw [show A *ᵥ x = y from hx.2]; exact hy)
    split_ifs with h
    · simpa using (hxl.mul_const (f x)).mul_const
        (ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ h.choose) y)
    · exact tendsto_const_nhds

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace SheetOnlyNull

variable {n d : ℕ}

theorem injective_iff_det_ne_zero (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) :
    Function.Injective L ↔ LinearMap.det (L : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  rfl

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem differentiableOn_mulVec {m : ℕ} (B : Matrix (Fin m) (Fin n) ℂ) {U : Set (Fin d → ℂ)}
    {s : (Fin d → ℂ) → Fin n → ℂ} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (fun w => B *ᵥ s w) U :=
  (LinearMap.toContinuousLinearMap B.mulVecLin).differentiable.comp_differentiableOn hs

theorem analyticOnNhd_of_differentiableOn {m : ℕ} {U : Set (Fin d → ℂ)}
    {F : (Fin d → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := fun w hw =>
  AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood d U (fun z => F z i) hU
    (differentiableOn_pi.1 hF i) w hw

theorem analyticOnNhd_det_jacC {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → Fin d → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) U := by
  intro w hw
  have hF' := (analyticOnNhd_of_differentiableOn hU hF).fderiv w hw
  have hent : ∀ a k, AnalyticAt ℂ (fun z => ReciprocityTheory.AnForm.A.jacC F z a k) w := fun a k => by
    show AnalyticAt ℂ (fun z => fderiv ℂ F z (Pi.single k 1) a) w
    exact (((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.apply ℂ (Fin d → ℂ) (Pi.single k (1 : ℂ)))).analyticAt _).comp hF'
  simp only [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ fun i _ => hent _ _)

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩

theorem exists_sheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hs : IsSheetAt J A x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) (A *ᵥ x)).det ≠ 0) :
    ∃ s', IsSheetAt J A' x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  have hFa := analyticOnNhd_of_differentiableOn hU (differentiableOn_mulVec A' hsd)
  set G : Set (Fin d → ℂ) := U ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G := (analyticOnNhd_det_jacC hU (differentiableOn_mulVec A' hsd)).continuousOn
    |>.isOpen_inter_preimage hU isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyU, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : A *ᵥ x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (A *ᵥ x) = A' *ᵥ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A' *ᵥ x) = A *ᵥ x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyU, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨?_, (hsec _ hz.2.1).2⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ (fun z => A *ᵥ z) ⁻¹' (φ.source ∩ U), inter_mem hV
      (((φ.open_source.inter hU).preimage (by fun_prop)).mem_nhds ⟨hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''src, hx''U⟩ -
    have hx'' : x'' = s (A *ᵥ x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''U
    have hA' : A' *ᵥ x'' = φ (A *ᵥ x'') := by rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hA', φ.left_inv hx''src]
    exact hx''

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A A' : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hA' : IsFiniteProjection J A')
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : A *ᵥ x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A' *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A' *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (differentiableOn_mulVec A' hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).2
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hnhds := h₁ n d J (linPoly A') hJ hA'.injective hA'.finite x hxZ
    (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))
    (inter_mem hV (((hW₀.inter hU).preimage hAc).mem_nhds ⟨hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A' i)) = A' *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A' *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ (fun z => A *ᵥ z) ⁻¹' (W₀ ∩ U))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzW⟩, rfl⟩
    refine ⟨A *ᵥ z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end SheetOnlyNull

theorem SheetOnlyNull.proof (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) : SheetOnlyNull.Statement := by
  intro n d J A A' hJ _ _ hA'
  set B := {x | x ∈ zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧ ¬ ∃ s', IsSheetAt J A' x s'} with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => SheetOnlyNull.exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume ((fun x => A *ᵥ x) '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hAx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hAx
    refine ⟨Metric.ball (A *ᵥ x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A' *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A' (hσd i))).mono hball,
      SheetOnlyNull.exists_det_ne_zero h₁ h₂ hJ hA' hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (SheetOnlyNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

namespace IntegralIndep

variable {n d : ℕ}

theorem chartDens_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) :
    chartAbsDens J A f φ y = chartPosDens J A f φ y + chartPosDens J A (-f) φ y ∧
      chartDens J A f φ y = chartPosDens J A f φ y - chartPosDens J A (-f) φ y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartAbsDens chartDens chartPosDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_congr rfl fun x _ => ?_, Finset.sum_congr rfl fun x _ => ?_⟩ <;>
    split_ifs <;> simp only [Pi.neg_apply, neg_mul, max_zero_add_max_neg_zero_eq_abs_self,
      max_zero_sub_max_neg_zero_eq_self, add_zero, sub_zero]

theorem chartPosDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (y : Fin d → ℂ) : 0 ≤ chartPosDens J A f φ y := by
  unfold chartPosDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y)]
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp

theorem measurable_chartPosDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (chartPosDens J A f φ) :=
  SheetSumMeasurable.measurable_sheetSum hA (fun a b => max (a * b) 0)
    ((continuous_fst.mul continuous_snd).max continuous_const).measurable hf φ

theorem chartInt_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (chartAbsDens J A f φ) ↔
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) < ⊤) ∧
    (Integrable (chartAbsDens J A f φ) → chartInt J A f φ =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y)).toReal) := by
  have h0 := chartPosDens_nonneg J A hA f φ
  have h1 := chartPosDens_nonneg J A hA (-f) φ
  have m0 := measurable_chartPosDens hA hf φ
  have m1 := measurable_chartPosDens hA hf.neg φ
  have habs : chartAbsDens J A f φ = fun y => chartPosDens J A f φ y + chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).1
  have hlin : ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) =
      (∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y)) +
        ∫⁻ y, ENNReal.ofReal (chartPosDens J A (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (chartAbsDens J A f φ) ↔
      ∫⁻ y, ENNReal.ofReal (chartAbsDens J A f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (chartPosDens J A f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (chartPosDens J A (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : chartDens J A f φ = fun y => chartPosDens J A f φ y - chartPosDens J A (-f) φ y :=
    funext fun y => (chartDens_eq_posParts hA f φ y).2
  rw [chartInt, hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]

end IntegralIndep

theorem IntegralIndep.proof (h : PosPartIndep.Statement) : IntegralIndep.Statement := by
  intro n d J A A' f φ hP hd hA hA' hf hφ hi
  have e0 := h n d J A A' f φ hP hd hA hA' hf hφ
  have e1 := h n d J A A' (-f) φ hP hd hA hA' hf.neg hφ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  obtain ⟨iA', cA'⟩ := IntegralIndep.chartInt_eq_posParts hA' hf φ
  have hi' : Integrable (chartAbsDens J A' f φ) := iA'.2 (by rw [← e0, ← e1]; exact iA.1 hi)
  exact ⟨hi', by rw [cA hi, cA' hi', e0, e1]⟩

end

end GroundTheory.Heights₂.Heights
end
