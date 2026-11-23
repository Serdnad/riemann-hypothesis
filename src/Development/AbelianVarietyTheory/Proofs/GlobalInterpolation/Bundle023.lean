module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.MomN

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq_zcHom {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) : zc x = zcHom q x := rfl

theorem zc_continuous' {q : ℕ} [Fact q.Prime] : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def linZ {q : ℕ} [Fact q.Prime] {κ κ' : Type} [Fintype κ] (a : κ' → κ → ℤ_[q]) :
    C(κ → ℤ_[q], κ' → ℤ_[q]) :=
  ⟨fun x i => ∑ j, a i j * x j, by fun_prop⟩

def pullCLM {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : C(Y, ℂ_[q]) →L[ℂ_[q]] C(X, ℂ_[q]) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp A
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } 1 (fun f => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
        exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => f.norm_coe_le_norm (A x))

theorem pullCLM_norm_le {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : ‖(pullCLM (q := q) A)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem pullCLM_apply {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) (f : C(Y, ℂ_[q])) : pullCLM A f = f.comp A := rfl

def monoC {q : ℕ} [Fact q.Prime] {κ : Type} {k : ℕ} (σ : Fin k → κ) : C(κ → ℤ_[q], ℂ_[q]) :=
  ⟨fun x => ∏ l, zc (x (σ l)), by
    exact continuous_finsetProd _ fun l _ => zc_continuous'.comp (continuous_apply (σ l))⟩

theorem momInt_push (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q])
    (G : V → ℂ) (hc : ∀ i j, ι (c i j) = zc (a i j)) (hw : ∀ i, w i = ∑ j, c i j • v j) (h : MomInt ι v G) :
    MomInt ι w G := by
  classical
  obtain ⟨μ, hμ, hm⟩ := h
  refine ⟨μ.comp (pullCLM (linZ a)), ?_, ?_⟩
  · calc ‖μ.comp (pullCLM (linZ a))‖ ≤ ‖μ‖ * ‖pullCLM (q := q) (linZ a)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hμ (pullCLM_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro k j f hf
    have hfe : pullCLM (linZ a) f = ∑ σ : Fin k → κ, (∏ l, zc (a (j l) (σ l))) • monoC σ := by
      ext x
      rw [pullCLM_apply, ContinuousMap.comp_apply, hf]
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        monoC, ContinuousMap.coe_mk, linZ]

      simp only [zc_eq_zcHom, map_sum, map_mul]
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]
    have hd : iteratedFDeriv ℂ k G 0 (fun l => w (j l)) =
        ∑ σ : Fin k → κ, (∏ l, c (j l) (σ l)) • iteratedFDeriv ℂ k G 0 (fun l => v (σ l)) := by
      simp only [hw]

      rw [ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact ContinuousMultilinearMap.map_smul_univ _ _ _

    rw [ContinuousLinearMap.comp_apply, hfe, hd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_eq_mul, map_mul, map_prod, map_smul, smul_eq_mul, ← hm k σ (monoC σ) (fun _ => rfl)]
    simp only [hc]

end GlobalTheory.MomN
end
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin


open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
theorem _root_.GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
      (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧
        _root_.GlobalTheory.Lin.ord χ s = _root_.GlobalTheory.Lin.ord χ.primitiveCharacter s := by
  intro q _ χ s hs hχs
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set E : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))
    with hE
  have hform : ∀ z, (χ.primitiveCharacter ≠ 1 ∨ z ≠ 1) →
      LFunction χ z = LFunction χ.primitiveCharacter z * E z := by
    intro z hz
    have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hz
    rwa [changeLevel_primitiveCharacter] at h
  have hprim : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with h | h
    · left
      intro h1
      apply h
      calc χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
            (changeLevel_primitiveCharacter χ).symm
        _ = 1 := by rw [h1, map_one]
    · exact Or.inr h
  have hEne : E s ≠ 0 := by
    rw [hE]
    refine Finset.prod_ne_zero_iff.2 (fun p hp => ?_)
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have hlt : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      calc _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (norm_le_one _ _) (by positivity)
        _ < 1 := by
            rw [one_mul]
            exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
    intro h0
    rw [sub_eq_zero] at h0
    rw [← h0, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hEd : Differentiable ℂ E := by
    have h : Differentiable ℂ (∏ p ∈ q.primeFactors,
        fun z : ℂ => 1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z)) :=
      Differentiable.finsetProd (fun p hp => by
        have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        fun_prop (disch := exact Or.inl hp0))
    rw [hE]
    convert h using 1
    ext z
    simp [Finset.prod_apply]
  have hEa : AnalyticAt ℂ E s := hEd.analyticAt s
  have hLa : AnalyticAt ℂ (LFunction χ.primitiveCharacter) s := by
    by_cases h1 : χ.primitiveCharacter = 1
    · have hs1 : s ≠ 1 := hprim.resolve_left (not_not.2 h1)
      exact DifferentiableOn.analyticAt (s := {z | z ≠ 1})
        (fun z hz => (differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt)
        (isOpen_ne.mem_nhds hs1)
    · exact (differentiable_LFunction h1).analyticAt s
  have hev : LFunction χ =ᶠ[𝓝 s] LFunction χ.primitiveCharacter * E := by
    rcases hprim with h1 | h1
    · exact Eventually.of_forall (fun z => hform z (Or.inl h1))
    · filter_upwards [isOpen_ne.mem_nhds h1] with z hz using hform z (Or.inr hz)
  refine ⟨?_, ?_⟩
  · rw [hform s hprim, mul_eq_zero]
    simp [hEne]
  · show (analyticOrderAt _ s).toNat = (analyticOrderAt _ s).toNat
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hLa hEa,
      analyticOrderAt_eq_zero.2 (Or.inr hEne), add_zero]

end GlobalTheory.Lin
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem mem_primesIoc_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {p : ℕ} (hp : p ∈ primesIoc x y) :
    x < p ∧ (p : ℝ) ≤ y := by
  simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  exact ⟨(Nat.floor_lt hx).mp hp.1.1, (Nat.le_floor_iff (hx.trans hxy)).mp hp.1.2⟩

theorem sum_primesIoc_eq_sum_indicator (a : ℕ → ℂ) {x y t : ℝ} (ht : 0 ≤ t) (hty : t ≤ y) :
    ∑ p ∈ primesIoc x t, a p
      = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t := by
  have hs : primesIoc x t = (primesIoc x y).filter (fun p : ℕ => (p : ℝ) ≤ t) := by
    ext p
    simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨h1, h2.trans (Nat.floor_mono hty)⟩, hp⟩, (Nat.le_floor_iff ht).mp h2⟩
    · rintro ⟨⟨⟨h1, _⟩, hp⟩, h3⟩
      exact ⟨⟨h1, (Nat.le_floor_iff ht).mpr h3⟩, hp⟩
  rw [hs, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : (p : ℝ) ≤ t <;> simp [h]

private lemma intervalIntegrable_indicator_Ici_of_intervalIntegrable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {x y p : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume x y) :
    IntervalIntegrable ((Set.Ici p).indicator f) MeasureTheory.volume x y := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.indicator measurableSet_Ici

private lemma integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt {J J' : ℝ → ℝ} {x y p : ℝ} (hxp : x < p) (hpy : p ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y)) :
    ∫ t in x..y, (Set.Ici p).indicator (fun t => (J' t : ℂ)) t = (J y : ℂ) - J p := by
  have hxy : x ≤ y := hxp.le.trans hpy
  rw [intervalIntegral.integral_of_le hxy, MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioc x y ∩ Set.Ici p = Set.Icc p y := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hxp.trans_le h1, h2⟩, h1⟩
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpy]
  have hsub : Set.uIcc p y ⊆ Set.Icc x y := by
    rw [Set.uIcc_of_le hpy]
    exact Set.Icc_subset_Icc hxp.le le_rfl
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hJ t (hsub ht)).ofReal_comp)
    ((hc'.mono hsub).intervalIntegrable)

theorem abel_primesIoc_weight (a : ℕ → ℂ) (J J' : ℝ → ℝ) (x y r : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y))
    (hb : ∀ t ∈ Set.Icc x y, |J' t| ≤ r / t) :
    ‖∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ)‖
      ≤ r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  have hx0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℂ, S = fun t => ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t :=
    ⟨_, rfl⟩
  have hIcc : Set.uIcc x y = Set.Icc x y := Set.uIcc_of_le hxy
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  have hJi : IntervalIntegrable (fun t => (J' t : ℂ)) MeasureTheory.volume x y :=
    (hc'.mono hIcc.subset).intervalIntegrable
  have hterm : ∀ p ∈ primesIoc x y, IntervalIntegrable
      (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) MeasureTheory.volume x y :=
    fun p _ => (intervalIntegrable_indicator_Ici_of_intervalIntegrable hJi).const_mul (a p)
  have hpt : ∀ t, (J' t : ℂ) * S t
      = ∑ p ∈ primesIoc x y, a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t := by
    intro t
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : t ∈ Set.Ici (p : ℝ)
    · simp only [Set.indicator_of_mem h]
      ring
    · simp [Set.indicator_of_notMem h]
  have hL : ∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ) = -∫ t in x..y, (J' t : ℂ) * S t := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum hterm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hb := mem_primesIoc_bounds hx0 hxy hp
    rw [intervalIntegral.integral_const_mul, integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt hb.1 hb.2 hJ hc]
    push_cast
    ring
  have hSi : IntervalIntegrable S MeasureTheory.volume x y := by
    have hS' : S = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) := by
      rw [hS]
      funext t
      simp [Finset.sum_apply]
    rw [hS']
    exact IntervalIntegrable.sum _ (fun p _ => intervalIntegrable_indicator_Ici_of_intervalIntegrable intervalIntegrable_const)
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc x y) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [hIcc] at ht
    exact (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)).ne'
  have hg : IntervalIntegrable (fun t => r * (‖S t‖ / t)) MeasureTheory.volume x y := by
    have := (hSi.norm.mul_continuousOn hinv).const_mul r
    simpa [div_eq_mul_inv] using this
  have hf : IntervalIntegrable (fun t => ‖(J' t : ℂ) * S t‖) MeasureTheory.volume x y := by
    have hsum := IntervalIntegrable.sum _ hterm
    have he : (fun t => (J' t : ℂ) * S t)
        = ∑ p ∈ primesIoc x y, (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) := by
      funext t
      rw [hpt, Finset.sum_apply]
    rw [← he] at hsum
    exact hsum.norm
  have hA : ∀ t ∈ Set.uIcc x y, ‖∑ p ∈ primesIoc x t, a p‖ / t = ‖S t‖ / t := by
    intro t ht
    rw [hIcc] at ht
    rw [sum_primesIoc_eq_sum_indicator a (hx0.trans ht.1) ht.2, hS]
  rw [hL, norm_neg, intervalIntegral.integral_congr hA, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm hxy).trans ?_
  refine intervalIntegral.integral_mono_on hxy hf hg (fun t ht => ?_)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |J' t| * ‖S t‖ ≤ r / t * ‖S t‖ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
    _ = r * (‖S t‖ / t) := by ring

end GlobalTheory.Lin
end

section

open GlobalTheory.MomN
open scoped ContDiff

noncomputable section

namespace GlobalTheory.MomEmbed

open MvPolynomial

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem monoJet_eq_listJet {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (m : κ →₀ ℕ) :
    monoJet v G m = ReciprocityTheory.ChartRestriction.G.PullbackSections.lD G 0 (m.toMultiset.toList.map v) := by
  unfold monoJet
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq G 0 _ (List.length_map _)]
  congr 1
  funext i
  simp [List.get_eq_getElem]

theorem monoJet_mapDomain {κ ι' : Type} [Fintype κ] [Fintype ι'] (e : κ ↪ ι') (w : κ → V) (u : ι' → V)
    (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (hw : ∀ i, u (e i) = w i) (m : κ →₀ ℕ) :
    monoJet u G (Finsupp.mapDomain e m) = monoJet w G m := by
  rw [monoJet_eq_listJet, monoJet_eq_listJet]
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm (hG.contDiffAt)
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, ← Multiset.map_coe, Multiset.coe_toList,
    Multiset.coe_toList, ← Finsupp.toMultiset_map m e, Multiset.map_map]
  congr 1
  funext i
  exact hw i

theorem mahler_embed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ i, u (e i) = w i) →
    (∀ p, p ∉ Set.range e → u p = 0) →
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → GlobalTheory.MomN.mahler u G k = GlobalTheory.MomN.mahler w G (fun i => k (e i))) := by
  intro V _ _ κ ι' _ _ e w u G hG hw hu
  classical
  constructor
  · rintro k ⟨p, hp, hkp⟩
    simp only [GlobalTheory.MomN.mahler]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hkp
    have hP : (∏ i, C (((k i).factorial : ℂ)⁻¹) * Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) =
        X p * (C (((k p).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X p : MvPolynomial ι' ℂ) ((descPochhammer ℂ n).comp (Polynomial.X - 1)) *
          ∏ i ∈ Finset.univ.erase p, C (((k i).factorial : ℂ)⁻¹) *
            Polynomial.aeval (X i : MvPolynomial ι' ℂ) (descPochhammer ℂ (k i))) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p)]
      simp only [hn, descPochhammer_succ_left, map_mul, Polynomial.aeval_X]
      ring
    rw [hP]
    apply Finset.sum_eq_zero
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul'] at hm
    have hpm : p ∈ m.support := by
      by_contra h
      exact hm (if_neg h)
    have hmem : p ∈ m.toMultiset.toList := by
      rw [Multiset.mem_toList]
      simpa using hpm
    obtain ⟨idx, hidx⟩ := List.get_of_mem hmem
    have hz : monoJet u G m = 0 := by
      unfold monoJet
      exact ContinuousMultilinearMap.map_coord_zero _ idx (by
        show u ((Finsupp.toMultiset m).toList.get idx) = 0
        rw [hidx]
        exact hu p hp)
    rw [hz, mul_zero]
  · intro k hk
    simp only [GlobalTheory.MomN.mahler]
    have hprod : (∏ p : ι', C (((k p).factorial : ℂ)⁻¹) *
        Polynomial.aeval (X p : MvPolynomial ι' ℂ) (descPochhammer ℂ (k p))) =
        rename e (∏ i : κ, C (((k (e i)).factorial : ℂ)⁻¹) *
          Polynomial.aeval (X i : MvPolynomial κ ℂ) (descPochhammer ℂ (k (e i)))) := by
      rw [map_prod]
      symm
      apply Fintype.prod_of_injective e e.injective
      · intro b hb
        simp [hk b hb]
      · intro a
        simp [← Polynomial.aeval_algHom_apply, rename_X]
    rw [hprod, MvPolynomial.support_rename_of_injective e.injective,
      Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective e.injective h)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_rename_mapDomain _ e.injective, monoJet_mapDomain e w u G hG hw]

end GlobalTheory.MomEmbed
end
end

section

open Complex
open scoped Real

theorem _root_.GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  first | exact @GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | exact GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | (intros; apply GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite <;> assumption)
end

section

open Complex

theorem _root_.GlobalTheory.T.gaussianOddJacobiTheta_eq_deriv_mul_sgStar : Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by
  first | exact @GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar | exact GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar | (intros; apply GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.contDensity_eq_fibre_measure_of_compact_open : ∀ (K V : Type) [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → ∀ (fib : K → Measure V), IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib → ∀ (L : Set V), IsCompact L → IsOpen L → ∀ g : K → ℂ, IsContDensityOn μ q id ν {t | t ≠ 0} (L.indicator 1) g → ∀ t : K, t ≠ 0 → g t = (((fib t L).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.contDensityOn_eq_fibre_mass | exact GlobalTheory.contDensityOn_eq_fibre_mass | (intros; apply GlobalTheory.contDensityOn_eq_fibre_mass <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.isFibreFamily_univ_of_null_cone' : ∀ (K V : Type) [NormedField K] [IsUltrametricDist K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) (q : V → K), Continuous q → μ {x | q x = 0} = 0 → ∀ (U : Set V) (B : Set K) (fib : K → Measure V), {x | q x ≠ 0} ⊆ U → {t | t ≠ 0} ⊆ B → IsFibreFamily μ q id U ν B fib → IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  first | exact @GlobalTheory.isFibreFamily_univ_of_null_cone | exact GlobalTheory.isFibreFamily_univ_of_null_cone | (intros; apply GlobalTheory.isFibreFamily_univ_of_null_cone <;> assumption)
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.hermitian_form_finite_zeros_on_line_cmExt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | qR K σ J (x + t • y) = 0}.Finite := by
  first | exact @GlobalTheory.HermLineZeros.finite_zeros_on_line | exact GlobalTheory.HermLineZeros.finite_zeros_on_line | (intros; apply GlobalTheory.HermLineZeros.finite_zeros_on_line <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.isFibreFamily_eq_at_continuity_point : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ) (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ), Measurable f → IsOpen O → O ⊆ U → O ⊆ U' → f ⁻¹' {β} ⊆ O → IsOpen B → IsOpen B' → β ∈ B → β ∈ B' → IsFibreFamily μ f id U (volume : Measure ℝ) B fib → IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib' → fib β = fib' β := by
  first | exact @GlobalTheory.IsFibreFamily_eq_at | exact GlobalTheory.IsFibreFamily_eq_at | (intros; apply GlobalTheory.IsFibreFamily_eq_at <;> assumption)
end
