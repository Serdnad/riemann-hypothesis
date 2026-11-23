module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

private theorem coe_symm_apply_of_isChart_val {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (y : M) (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    e'.symm =ᶠ[𝓝 (z y)] e.symm := by

  have hzy : z y = e' y := he' hy'
  have hzy2 : z y = e y := he hy
  have hopen : IsOpen (e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source)) :=
    e.open_target.inter (e'.isOpen_inter_preimage_symm e.open_source)
  have hmem : z y ∈ e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source) := by
    refine ⟨by rw [hzy2]; exact e.map_source hy, by rw [hzy]; exact e'.map_source hy', ?_⟩
    show e'.symm (z y) ∈ e.source
    rw [hzy, e'.left_inv hy']
    exact hy
  filter_upwards [hopen.mem_nhds hmem] with w hw
  obtain ⟨_, hw2, hw3⟩ := hw
  have ha : e'.symm w ∈ e'.source := e'.map_target hw2
  have hea : e (e'.symm w) = w := by
    rw [← he hw3, he' ha, e'.right_inv hw2]
  calc e'.symm w = e.symm (e (e'.symm w)) := (e.left_inv hw3).symm
    _ = e.symm w := by rw [hea]

private theorem wdb_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wdb n k F p = wdb n k G p := by
  unfold wdb
  rw [h.fderiv_eq]

private theorem wd_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wd n k F p = wd n k G p := by
  unfold wd
  rw [h.fderiv_eq]

private theorem db_apply_eq_wdb_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : db n z k f y = wdb n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold db
  rw [dite_eq_left hex]
  apply wdb_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

private theorem d_apply_eq_wd_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : d n z k f y = wd n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold d
  rw [dite_eq_left hex]
  apply wd_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

theorem leviZ_coord_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (l : Fin n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    EqOn ((fun y => z y l) ∘ e.symm) (fun w : V n => w l) e.target := by
  intro w hw
  simp only [Function.comp_apply]
  rw [he (e.map_target hw), e.right_inv hw]

theorem leviZ_wd_coord (n : ℕ) (j l : Fin n) (y : V n) :
    wd n j (fun w : V n => w l) y = if j = l then 1 else 0 := by
  have hL : fderiv ℝ (fun w : V n => w l) y =
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) :=
    ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ).fderiv
  unfold wd
  rw [hL]
  by_cases h : j = l
  · subst h
    simp [bas, PiLp.single_apply, Complex.I_mul_I]
  · simp [bas, PiLp.single_apply, h, Ne.symm h]

theorem leviZ_d_coord {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j l : Fin n) (x : M) :
    d n z j (fun y => z y l) x = if j = l then 1 else 0 := by
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => congrFun hze y
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  rw [d_apply_eq_wd_of_mem_source n z j _ e he x hx,
    wd_apply_congr_of_eventuallyEq n j (G := fun w : V n => w l) (by
      filter_upwards [e.open_target.mem_nhds hzx] with w hw
      exact leviZ_coord_chart n z l e he hw)]
  exact leviZ_wd_coord n j l (z x)

private theorem wdb_sum_mul_conj_eq_coord (n : ℕ) (k : Fin n) (p : V n) :
    wdb n k (fun w : V n => ∑ l, w l * conj (w l)) p = p k := by
  have hP : ∀ l, HasFDerivAt (fun w : V n => w l)
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) p :=
    fun l => (EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ
  have hC : ∀ l, HasFDerivAt (fun w : V n => conj (w l))
      (Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    fun l => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p (hP l)
  have hF : HasFDerivAt (fun w : V n => ∑ l, w l * conj (w l))
      (∑ l, (p l • Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) +
        conj (p l) • (EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    HasFDerivAt.fun_sum (fun l _ => (hP l).mul (hC l))
  unfold wdb
  rw [hF.fderiv]
  simp [bas, PiLp.single_apply]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Complex.conj_I,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linear_combination ((starRingEnd ℂ (p.ofLp k) - p.ofLp k) / 2) * Complex.I_sq

theorem leviNormSq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LeviNormSqStatement n M := by
  intro z hz
  have hchart : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
    intro x
    obtain ⟨e, hx, hze⟩ := hz x
    exact ⟨e, fun y _ => congrFun hze y, hx⟩

  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      EqOn ((fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) ∘ e.symm) (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ))
        e.target := by
    intro e he w hw
    simp only [Function.comp_apply]
    rw [he (e.map_target hw), e.right_inv hw]
  have hsq : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ l, w l * conj (w l) := by
    funext w
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨fun e he => ?_, fun x ξ => ?_⟩
  · have hsm : ContDiffOn ℝ ∞ (fun w : V n => ∑ l, w l * conj (w l)) e.target := by
      refine ContDiffOn.sum (fun l _ => ?_)
      have hPc : ContDiff ℝ ∞ (fun w : V n => w l) :=
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ).contDiff
      have hCc : ContDiff ℝ ∞ (fun w : V n => conj (w l)) :=
        (Complex.conjCLE.toContinuousLinearMap.comp
          ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)).contDiff
      exact (hPc.mul hCc).contDiffOn
    rw [← hsq] at hsm
    exact hsm.congr (hloc e he)
  ·
    have hdb : ∀ k, db n z k (fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) = fun y => z y k := by
      intro k
      funext y
      obtain ⟨e, he, hy⟩ := hchart y
      have hzy : z y ∈ e.target := by rw [he hy]; exact e.map_source hy
      rw [db_apply_eq_wdb_of_mem_source n z k _ e he y hy,
        wdb_apply_congr_of_eventuallyEq n k (G := fun w : V n => ∑ l, w l * conj (w l)) (by
          rw [← hsq]
          filter_upwards [e.open_target.mem_nhds hzy] with w hw
          exact hloc e he hw)]
      exact wdb_sum_mul_conj_eq_coord n k (z y)
    simp only [Levi, hdb, leviZ_d_coord n z hz]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

private lemma d_apply_eq_zero_of_eventuallyEq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (x : M) (hf : f =ᶠ[𝓝 x] 0) : d n z j f x = 0 := by
  unfold d
  split_ifs with h
  · set e := Classical.choose h
    have he := Classical.choose_spec h
    have hzx : z x = e x := he.1 he.2
    have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have hc := e.continuousAt_symm (e.map_source he.2)
      rw [ContinuousAt, e.left_inv he.2] at hc
      exact hc
    have hg : (f ∘ e.symm) =ᶠ[𝓝 (e x)] fun _ => (0 : ℂ) :=
      (ht.eventually hf).mono fun y hy => by simpa using hy
    rw [hzx]
    unfold wd
    rw [hg.fderiv_eq]
    simp
  · rfl

theorem locality (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LocalityStatement n M := by
  intro z _ ph ph' ψ U f _ _ hsupp hph
  have hfz : ∀ x, x ∉ U → f x = 0 := by
    intro x hx
    by_contra h
    exact hx (hsupp (subset_tsupport _ h))
  have hfun : ∀ j, (fun y => (Real.exp (-(w2 ph' ψ y)) : ℂ) * f y j) =
      fun y => (Real.exp (-ph y) : ℂ) * f y j := by
    intro j
    funext y
    by_cases hy : y ∈ U
    · simp [w2, (hph y hy).1, (hph y hy).2]
    · simp [hfz y hy]
  refine ⟨?_, ?_⟩
  · intro v
    unfold ipV
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp [w2, (hph x hx).1, (hph x hx).2]
    · simp [hfz x hx]
  · unfold wint
    apply lintegral_congr
    intro x
    unfold tstar
    simp_rw [hfun]
    by_cases hx : x ∈ U
    · have h1 : w1 ph' ψ x = ph x := by simp [w1, (hph x hx).1, (hph x hx).2]
      rw [h1]
    · have hx' : x ∉ tsupport f := fun h => hx (hsupp h)
      have hev : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx'
      have hS : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x = 0 := fun j =>
        d_apply_eq_zero_of_eventuallyEq_zero n z j _ x (hev.mono fun y hy => by simp [hy])
      rw [Finset.sum_eq_zero (fun j _ => hS j)]
      simp

end

end ReciprocityTheory.L2DbarEstimates.F
end

section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

lemma shell_mem (a t : ℝ) (ht : a + 1 < t) :
    a + 1 + (⌈t - a - 2⌉₊ : ℝ) < t ∧ t ≤ a + 2 + (⌈t - a - 2⌉₊ : ℝ) := by
  constructor
  · rcases le_or_gt 0 (t - a - 2) with h | h
    · have := Nat.ceil_lt_add_one h
      linarith
    · rw [Nat.ceil_eq_zero.mpr h.le]
      simp only [CharP.cast_eq_zero, add_zero]
      linarith
  · have := Nat.le_ceil (t - a - 2)
    linarith

lemma shell_coef (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-(Real.log (1 + C) + k))) * ENNReal.ofReal C ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by linarith)]
  have h1 : 0 < 1 + C := by linarith
  have h2 := Real.exp_pos (-(k : ℝ))
  have h3 : (1 + C)⁻¹ * C ≤ 1 := by
    rw [inv_mul_le_iff₀ h1]
    linarith
  have h4 : 0 ≤ (1 + C)⁻¹ := inv_nonneg.mpr h1.le
  nlinarith [mul_le_mul_of_nonneg_left h3 h2.le]

private lemma vol_lt_infty_of_compact {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) {K : Set M} (hK : IsCompact K) :
    vol n z K < ⊤ := by
  classical
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold vol
  split_ifs with h
  · rw [Measure.ofMeasurable_apply K hKm]
    unfold volFun
    have hz' : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source ∧ z = e :=
      fun x => (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hz) x (Set.mem_univ x)
    choose e he hze using hz'
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => (e x).source) (fun x => (e x).open_source)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, he x⟩)
    have hbound : ∀ y : V n, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤
        (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ z '' K
      · rw [Set.indicator_of_mem hy]
        have hidx : ∀ p ∈ K ∩ z ⁻¹' {y}, ∃ i ∈ t, p ∈ (e i).source := by
          intro p hp
          have := ht hp.1
          simp only [Set.mem_iUnion] at this
          obtain ⟨i, hi, hpi⟩ := this
          exact ⟨i, hi, hpi⟩
        choose! f hf1 hf2 using hidx
        have h1 : (K ∩ z ⁻¹' {y}).encard ≤ ((t : Set M)).encard := by
          refine Set.encard_le_encard_of_injOn (fun p hp => hf1 p hp) ?_
          intro p hp q hq hpq
          have hp' := hf2 p hp
          have hq' := hf2 q hq
          rw [hpq] at hp'
          apply (e (f q)).injOn hp' hq'
          have h3 := congrFun (hze (f q))
          rw [← h3 p, ← h3 q, Set.mem_singleton_iff.mp hp.2, Set.mem_singleton_iff.mp hq.2]
        rw [Set.encard_coe_eq_coe_finsetCard] at h1
        calc ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ((t.card : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr h1
          _ = t.card := by simp
      · rw [Set.indicator_of_notMem hy]
        have : K ∩ z ⁻¹' {y} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hp hzp
          exact hy ⟨p, hp, hzp⟩
        rw [this, Set.encard_empty]
        simp
    calc ∫⁻ y, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ∫⁻ y, (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y :=
          lintegral_mono hbound
      _ = t.card * volume (z '' K) :=
          lintegral_indicator_const (hK.image hz.continuous).isClosed.measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (hK.image hz.continuous).measure_lt_top
  · simp

theorem shell (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ShellStatement n M := by
  classical
  intro z hz e ph ψ v a he hK hph hψ hv
  set g : M → ℝ := fun x => ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hgm : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hgc.measurable
  have hfin : ∀ b : ℝ, ∫⁻ x in {x | e x ≤ b}, ENNReal.ofReal (g x) ∂vol n z < ⊤ := by
    intro b
    exact setLIntegral_lt_top_of_isCompact (vol_lt_infty_of_compact z hz (hK b)).ne (hK b)
      (f := fun x => (g x).toNNReal) (continuous_real_toNNReal.comp hgc)
  set C : ℕ → ℝ := fun k => (∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z).toReal with hC
  have hC0 : ∀ k : ℕ, 0 ≤ C k := fun k => ENNReal.toReal_nonneg
  have hCeq : ∀ k : ℕ, ∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z = ENNReal.ofReal (C k) :=
    fun k => (ENNReal.ofReal_toReal (hfin _).ne).symm
  set R : ℝ → ℝ := fun t => if a + 1 < t then Real.log (1 + C ⌈t - a - 2⌉₊) + ⌈t - a - 2⌉₊ else 0 with hR
  have hterm0 : ∀ k : ℕ, 0 ≤ Real.log (1 + C k) + k :=
    fun k => add_nonneg (Real.log_nonneg (by linarith [hC0 k])) (Nat.cast_nonneg k)
  refine ⟨R, ?_, ?_⟩
  · intro b
    refine ⟨∑ k ∈ Finset.range (⌈b - a - 2⌉₊ + 1), (Real.log (1 + C k) + k), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_Iic] at ht
    simp only [hR]
    split_ifs with h
    · exact Finset.single_le_sum (f := fun k : ℕ => Real.log (1 + C k) + k) (fun k _ => hterm0 k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono (by linarith))))
    · exact Finset.sum_nonneg fun k _ => hterm0 k
  · intro χ hχ0 hχR
    unfold nV
    set S : ℕ → Set M := fun k => {x | a + 1 + k < e x ∧ e x ≤ a + 2 + k} with hS
    have hSm : ∀ k, MeasurableSet (S k) := fun k =>
      (measurableSet_lt measurable_const he.measurable).inter (measurableSet_le he.measurable measurable_const)
    have hLm : MeasurableSet {x | e x ≤ a + 1} := measurableSet_le he.measurable measurable_const
    have hpt : ∀ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ≤
        {x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
        ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
          ENNReal.ofReal (g x)) x := by
      intro x
      by_cases hx : e x ≤ a + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | e x ≤ a + 1} from hx)]
        refine le_trans ?_ le_self_add
        apply ENNReal.ofReal_le_ofReal
        simp only [hg]
        gcongr
        linarith [hχ0 (e x)]
      · push_neg at hx
        have hxS : x ∈ S ⌈e x - a - 2⌉₊ := shell_mem a (e x) hx
        refine le_trans ?_ (le_add_left (ENNReal.le_tsum ⌈e x - a - 2⌉₊))
        rw [Set.indicator_of_mem hxS, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have hRx : Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊ ≤ χ (e x) := by
          have := hχR (e x) hx.le
          simp only [hR, if_pos hx] at this
          exact this
        simp only [hg]
        rw [show -(ph x + χ (e x) - ψ x) = -(χ (e x)) + (-ph x + ψ x) by ring, Real.exp_add]
        have h1 : Real.exp (-(χ (e x))) ≤ Real.exp (-(Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : 0 ≤ ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    calc ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ∂vol n z
        ≤ ∫⁻ x, ({x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
          ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ENNReal.ofReal (g x)) x) ∂vol n z := lintegral_mono hpt
      _ = ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k, ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z := by
        rw [lintegral_add_left (hgm.indicator hLm), lintegral_indicator hLm,
          lintegral_tsum (fun k => ((hgm.const_mul _).indicator (hSm k)).aemeasurable)]
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator (hSm k), lintegral_const_mul _ hgm]
      _ ≤ ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        calc ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z
            ≤ ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ENNReal.ofReal (C k) := by
              gcongr
              rw [← hCeq k]
              exact lintegral_mono_set (fun x hx => hx.2)
          _ ≤ _ := shell_coef (C k) (hC0 k) k
      _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨hfin (a + 1), ?_⟩
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) Real.summable_exp_neg_nat]
        exact ENNReal.ofReal_lt_top

end

end ReciprocityTheory.L2DbarEstimates.F
end
