module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGroupIntegrability.InstCompactUG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle001
import GroundTheory.AutomorphicForms.RealIwasawaIntegration
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle010
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle004
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.UniformSpace.Uniformizable
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSpaceR

@[expose] public section

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem simp_int {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (ν : Measure X) [IsFiniteMeasure ν]
    (s : SimpleFunc X X) (F : X → E) : ∫ k, F (s k) ∂ν = ∑ x ∈ s.range, ν.real (s ⁻¹' {x}) • F x := by
  have h : (fun k => F (s k)) = fun k => ∑ x ∈ s.range, (s ⁻¹' {x}).indicator (fun _ => F x) k := by
    funext k
    rw [Finset.sum_eq_single (s k)]
    · simp
    · intro b _ hb
      exact Set.indicator_of_notMem (by simpa using fun h => hb h.symm) _
    · intro h
      exact absurd (s.mem_range_self k) h
  rw [h, integral_finsetSum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_indicator_const _ (s.measurableSet_preimage _)]
  · intro x _
    exact (integrable_const (F x)).indicator (s.measurableSet_preimage _)

private theorem simp_lim {X E : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure X) [IsFiniteMeasure ν] (s : ℕ → SimpleFunc X X) (hs : ∀ k, Tendsto (fun i => s i k) atTop (𝓝 k)) (G : X → E) (hG : Continuous G) :
    Tendsto (fun i => ∫ k, G (s i k) ∂ν) atTop (𝓝 (∫ k, G k ∂ν)) := by
  obtain ⟨C, hC⟩ := (isCompact_range hG).isBounded.exists_norm_le
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun i => ?_) (integrable_const C) (fun i => Eventually.of_forall fun k => hC _ ⟨_, rfl⟩)
    (Eventually.of_forall fun k => (hG.tendsto k).comp (hs k))
  exact ((s i).map G).aestronglyMeasurable

private theorem cont_int {X Y : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (ν : Measure X) [IsFiniteMeasure ν] (f : Y → X → ℂ) (hf : Continuous fun p : Y × X => f p.1 p.2) :
    Continuous fun y => ∫ k, f y k ∂ν := by
  let c : C(Y, C(X, ℂ)) := ContinuousMap.curry ⟨fun p : Y × X => f p.1 p.2, hf⟩
  have hI : Continuous fun g : C(X, ℂ) => ∫ k, g k ∂ν := by
    refine Metric.continuous_iff.2 fun g ε hε => ?_
    refine ⟨ε / (ν.real Set.univ + 1), by positivity, fun h hh => ?_⟩
    rw [dist_eq_norm, ← integral_sub (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hb : ∀ k, ‖h k - g k‖ ≤ dist h g := fun k => by
      rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist k
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hb)).trans_lt ?_
    have hp : 0 < ν.real Set.univ + 1 := by positivity
    calc dist h g * ν.real Set.univ ≤ dist h g * (ν.real Set.univ + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) dist_nonneg
      _ < ε := (lt_div_iff₀ hp).1 hh
  exact hI.comp c.continuous

variable {μ : Measure (G1 K n)} [μ.IsHaarMeasure]

private theorem reps_ext' {v w : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w φ) : v = w := by
  refine Lp.ext ?_
  have hm := map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K n) μ)
  refine Measure.ae_le_iff_absolutelyContinuous.2 (hm ▸ Measure.AbsolutelyContinuous.rfl :
    quotientMeasure (Gam K n) μ ≪ Measure.map (mk (Gam K n)) (μ.restrict (fundamentalDomain (Gam K n)))) ?_
  refine (ae_map_iff (measurable_mk _).aemeasurable
    ((Lp.stronglyMeasurable v).measurableSet_eq_fun (Lp.stronglyMeasurable w))).2 (ae_restrict_of_ae ?_)
  filter_upwards [hv, hw] with y h1 h2
  rw [h1, h2]

private theorem reps_sum' {ι : Type} (s : Finset ι) (c : ι → ℂ) {v : ι → L2 μ} {φ : ι → G1 K n → ℂ} (h : ∀ i ∈ s, Reps μ (v i) (φ i)) :
    Reps μ (∑ i ∈ s, c i • v i) fun y => ∑ i ∈ s, c i * φ i y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa only [Finset.sum_empty, Pi.zero_apply] using hy
  | insert a s ha ih =>
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_add (c a • v a) (∑ i ∈ s, c i • v i)),
      MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_smul (c a) (v a)), h a (Finset.mem_insert_self _ _),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)] with y h1 h2 h3 h4
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, smul_eq_mul]

private theorem reps_right' {v : L2 μ} {φ : G1 K n → ℂ} (hv : Reps μ v φ) (g : G1 K n) :
    Reps μ (rightRegularRep (Gam K n) μ g v) fun y => φ (y * g) := by
  filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (coeFn_rightRegularRep (Gam K n) μ g v),
    MeasureTheory.QuasiMeasurePreserving.ae (measurePreserving_mul_right μ g).quasiMeasurePreserving hv] with y h1 h2
  rw [h1, rightMul_mk, h2]

private theorem reps_int {X : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (a : X → ℂ) (ha : Continuous a) (u : X → G1 K n) (hu : Continuous u)
    {v : LL μ} {φ : G1 K n → ℂ} (hφ : Continuous φ) (hv : Reps μ v φ) :
    Reps μ (∫ k, a k • rightRegularRep (Gam K n) μ (u k) v ∂ν) fun y => ∫ k, a k * φ (y * u k) ∂ν := by
  letI := TopologicalSpace.metrizableSpaceMetric X
  haveI : TopologicalSpace.SeparableSpace (Set.univ : Set X) := inferInstance
  let s : ℕ → SimpleFunc X X := fun i => SimpleFunc.approxOn id measurable_id Set.univ (Classical.arbitrary X) (Set.mem_univ _) i
  have hs : ∀ k, Tendsto (fun i => s i k) atTop (𝓝 k) := fun k =>
    SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ _) (by simp)
  let G : X → LL μ := fun k => a k • rightRegularRep (Gam K n) μ (u k) v
  have hG : Continuous G := ha.smul (((rightRegularRep (Gam K n) μ).continuous_orbit v).comp hu)
  let W : ℕ → LL μ := fun i => ∫ k, G (s i k) ∂ν
  let P : ℕ → G1 K n → ℂ := fun i y => ∫ k, a (s i k) * φ (y * u (s i k)) ∂ν
  have hW : ∀ i, Reps μ (W i) (P i) := fun i => by
    have e1 : W i = ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) • rightRegularRep (Gam K n) μ (u x) v := by
      show ∫ k, G (s i k) ∂ν = _
      rw [simp_int]
      refine Finset.sum_congr rfl fun x _ => ?_
      show ν.real (s i ⁻¹' {x}) • (a x • rightRegularRep (Gam K n) μ (u x) v) = _
      rw [mul_smul, Complex.coe_smul]
      rfl
    have e2 : P i = fun y => ∑ x ∈ (s i).range, ((ν.real (s i ⁻¹' {x}) : ℂ) * a x) * φ (y * u x) := by
      funext y
      refine (simp_int ν (s i) (fun x => a x * φ (y * u x))).trans (Finset.sum_congr rfl fun x _ => ?_)
      rw [Complex.real_smul, mul_assoc]
    rw [e1, e2]
    exact reps_sum' _ _ fun x _ => reps_right' hv (u x)
  have hWl : Tendsto W atTop (𝓝 (∫ k, G k ∂ν)) := simp_lim ν s hs G hG
  have hPl : ∀ y, Tendsto (fun i => P i y) atTop (𝓝 (∫ k, a k * φ (y * u k) ∂ν)) := fun y =>
    simp_lim ν s hs (fun k => a k * φ (y * u k)) (ha.mul (hφ.comp (continuous_const.mul hu)))
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hWl).exists_seq_tendsto_ae
  have h1 := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) hns
  have h2 : ∀ᵐ y ∂μ, ∀ i, (W i : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) = P i y := ae_all_iff.2 hW
  filter_upwards [h1, h2] with y hy1 hy2
  simp only [hy2] at hy1
  exact tendsto_nhds_unique hy1 ((hPl y).comp hmono.tendsto_atTop)

private theorem cont_ae_eq {f g : G1 K n → ℂ} (hf : Continuous f) (hg : Continuous g) (h : f =ᵐ[μ] g) : f = g :=
  Continuous.ae_eq_iff_eq μ hf hg |>.1 h
end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.ptPi :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (v : LL μ) (φ : G1 K 2 → ℂ), Continuous φ → Reps μ v φ →
      (∀ i n q, C.Pi μ i n q v = 0 → ∀ x, ∫ m, conj (KT.psi n q n m) * φ (x * C.un i m) ∂μK = 0) ∧
      ∀ (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), IdemA κ p → (pOp μ κ p v = v ↔ FixA κ p φ) := by
  intro K _ _ _ ι _ C μ _ v φ hφ hv
  haveI : TopologicalSpace.MetrizableSpace U2 := inferInstance
  haveI : CompactSpace U2 := inferInstance
  have hcu : ∀ i, Continuous (C.un i) := fun i => by
    have hm : Continuous (fun x : U2 => (Pi.mulSingle i x : ι → U2)) := by
      refine continuous_pi fun j => ?_
      by_cases h : j = i
      · subst h
        simpa using continuous_id'
      · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
    unfold Co.un arc1
    exact continuous_archP.comp (continuous_subtype_val.comp ((C.Φ 2).symm.continuous.comp hm))
  have hca : Continuous (arc1 : archCompact K 2 → G1 K 2) := continuous_archP.comp continuous_subtype_val
  haveI : TopologicalSpace.MetrizableSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.isEmbedding.metrizableSpace
  haveI : CompactSpace (archCompact K 2) := (C.Φ 2).toHomeomorph.symm.compactSpace
  refine ⟨fun i n q h0 x => ?_, fun κ p hp => ?_⟩
  · have hT : Continuous (T n q) := continuous_const.mul (Complex.continuous_conj.comp (KT.continuous_psi n q n))
    have hr := reps_int μK (T n q) hT (C.un i) (hcu i) hφ hv
    have hc : Continuous fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK :=
      cont_int μK _ (hT.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul ((hcu i).comp continuous_snd))))
    have h0' : (∫ m, T n q m • rightRegularRep (Gam K 2) μ (C.un i m) v ∂μK) = 0 := h0
    rw [h0'] at hr
    have hz : Reps μ (0 : LL μ) fun _ => 0 := by
      filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K 2) μ) (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K 2) μ))] with y hy
      simpa only [Pi.zero_apply] using hy
    have he : (fun y => ∫ m, T n q m * φ (y * C.un i m) ∂μK) = fun _ => 0 := by
      refine cont_ae_eq (μ := μ) hc continuous_const ?_
      filter_upwards [hr, hz] with y h1 h2
      rw [← h1, h2]
    have hx := congrFun he x
    have hN : ((KT.normSqInt n q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (KT.normSqInt_pos n q).ne'
    simp only [T, mul_assoc] at hx
    rw [integral_const_mul] at hx
    exact (mul_eq_zero.1 hx).resolve_left (inv_ne_zero hN)
  · haveI := hp.haar.prob
    have hr : Reps μ (pOp μ κ p v) fun y => ∫ k, p k * φ (y * arc1 k) ∂κ := reps_int κ p hp.cont arc1 hca hφ hv
    have hc : Continuous fun y => ∫ k, p k * φ (y * arc1 k) ∂κ :=
      cont_int κ _ (hp.cont.comp continuous_snd |>.mul (hφ.comp (continuous_fst.mul (hca.comp continuous_snd))))
    constructor
    · intro h
      rw [h] at hr
      have he : (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ := by
        refine cont_ae_eq (μ := μ) hc hφ ?_
        filter_upwards [hr, hv] with y h1 h2
        rw [← h1, h2]
      exact fun g => congrFun he g
    · intro h
      have : (fun y => ∫ k, p k * φ (y * arc1 k) ∂κ) = φ := funext h
      rw [this] at hr
      exact reps_ext' hr hv
end

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma sq_sum_le_of_dom (π : Equiv.Perm (Fin (2 + 2))) (μ ν : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν i ^ 2 ≤ ∑ i, μ i ^ 2 := by
  have hm : Monotone ((fun i => -ν i) ∘ Tuple.sort (fun i => -ν i)) := Tuple.monotone_sort _
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (2 + 2)), Monotone ((fun i => -ν i) ∘ τ) := ⟨_, hm⟩
  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin (2 + 2)), s = τ * π⁻¹ := ⟨_, rfl⟩
  have hanti : Antitone ((fun i => ν (s i)) ∘ π) := by
    intro a b hab
    have := hτ hab
    simp only [Function.comp, neg_le_neg_iff] at this
    simpa [hs, Equiv.Perm.mul_apply] using this
  have h1 := h s⁻¹ (fun i => ν (s i)) hanti
  have h2 : ∑ i, ν i * ν (s (s⁻¹ i)) = ∑ i, ν i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  rw [h2] at h1
  have h3 : ∑ i, ν (s i) ^ 2 = ∑ i, ν i ^ 2 := Equiv.sum_comp s fun i => ν i ^ 2
  have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ μ fun i => ν (s i)
  rw [h3] at h4
  have hA : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, μ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨A, hAe⟩ : ∃ A, A = ∑ i, ν i ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hBe⟩ : ∃ B, B = ∑ i, μ i ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hCe⟩ : ∃ C, C = ∑ i, μ i * ν (s i) := ⟨_, rfl⟩
  rw [← hAe, ← hCe] at h1
  rw [← hAe, ← hBe, ← hCe] at h4
  rw [← hAe] at hA
  rw [← hBe] at hB
  rw [← hAe, ← hBe]
  rcases hA.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · have h5 : A * A ≤ B * A := by nlinarith
    exact le_of_mul_le_mul_right h5 h0

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expNorm :
    ∀ π ψ μ, OExp π ψ μ → WExp ψ μ := by
  intro π ψ μ h
  obtain ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩ := h
  refine ⟨J, hJ, j₀, a, b, ν, hc, he, ha, hb, hν, hw, fun j => sq_sum_le_of_dom π μ (ν j) (hg j), ?_⟩
  intro j hj hEq
  have := hg' j hj
  rw [hEq] at this
  exact lt_irrefl _ this
end

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private lemma chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) :
    chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add, add_mul]

private lemma weak (π : Equiv.Perm (Fin (2 + 2))) (ν μ : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν (π i) * (-((i : ℕ) : ℤ)) ≤ ∑ i, μ (π i) * (-((i : ℕ) : ℤ)) := by
  have h1 := h 1 (fun i => -(((π.symm i : Fin (2 + 2)) : ℕ) : ℤ)) (by
    intro a b hab
    simp only [Function.comp_apply, Equiv.symm_apply_apply, neg_le_neg_iff, Nat.cast_le]
    exact hab)
  rw [← Equiv.sum_comp π, ← Equiv.sum_comp π (fun i => μ i * _)] at h1
  simpa only [Equiv.Perm.one_apply, Equiv.symm_apply_apply] using h1

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expMul :
    ∀ π ψ ψ' μ μ', OExp π ψ μ → OExp π ψ' μ' → OExp π (fun k => ψ k * ψ' k) (μ + μ') := by
  rintro π ψ ψ' μ μ' ⟨J, _, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩
    ⟨J', _, j₀', a', b', ν', hc', he', ha', hb', hν', hw', hf, hf'⟩
  refine ⟨J × J', inferInstance, (j₀, j₀'), fun j h => a j.1 h * a' j.2 h, fun j h => b j.1 h * b' j.2 h,
    fun j => ν j.1 + ν' j.2, fun j => ⟨(hc j.1).1.mul (hc' j.2).1, (hc j.1).2.mul (hc' j.2).2⟩,
    fun h k => ?_, ?_, ?_, ?_, fun j θ h => ?_, fun j w y hy => ?_, fun j hj => ?_⟩
  · simp only [he, he', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [ha, ha']
  · simp only [hb, hb']
  · simp only [hν, hν']
  · obtain ⟨h1, h2, h3⟩ := hw j.1 θ h
    obtain ⟨h1', h2', h3'⟩ := hw' j.2 θ h
    simp only [h1, h2, h3, h1', h2', h3', chi_add]
    refine ⟨by ring, by ring, by ring⟩
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_le_add (hg j.1 w y hy) (hf j.2 w y hy)
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    by_cases h1 : j.1 = j₀
    · have h2 : j.2 ≠ j₀' := fun h2 => hj (Prod.ext h1 h2)
      exact add_lt_add_of_le_of_lt (weak π _ _ (hg j.1)) (hf' j.2 h2)
    · exact add_lt_add_of_lt_of_le (hg' j.1 h1) (weak π _ _ (hf j.2))
end

section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section

open PositivityTheory.Rg.Tf.Geo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem gal_infEmb (σ : E ≃ₐ[F] E) (n : ℕ) (a : archGroup E n) :
    Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a) =
      infEmb E n (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) := by
  apply (AdelicGLn.prodEquiv E n).injective
  rw [prodEquiv_infEmb, ContinuousMulEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · have h1 : UpperTheory.ConvolutionTheory.T4.pI E n (infEmb E n a) = (archEquiv E n).symm a := congrArg Prod.fst (prodEquiv_infEmb a)
    rw [← UpperTheory.ConvolutionTheory.K.galAdEq F E σ, ← h1]
    exact (UpperTheory.adele_galois_action_baseChange_compat F E σ n).1 _
  · have h2 : (AdelicGLn.prodEquiv E n (infEmb E n a)).2 = 1 := congrArg Prod.snd (prodEquiv_infEmb a)
    have h3 : (AdelicGLn.prodEquiv E n
        (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.toRingEquiv) (infEmb E n a))).2 =
        mapGL n (Formalism.L2.Host.CT.finMap σ.toRingEquiv) (AdelicGLn.prodEquiv E n (infEmb E n a)).2 :=
      Units.ext (Matrix.ext fun _ _ => rfl)
    rw [h3, h2, map_one]

private theorem compA_shift {σ : E ≃ₐ[F] E} {m : ℕ} (D : InfD σ m) (n : ℕ) (a : archGroup E n) (i : Fin (m + 1)) :
    compA D n i (archEquiv E n (mapGL n (galInf σ) ((archEquiv E n).symm a))) = compA D n (i + 1) a := by
  have e : ∀ j x, compA D n j x = archEquiv F n (D.comp n j ((archEquiv E n).symm x)) := fun _ _ => rfl
  rw [e, e, ContinuousMulEquiv.symm_apply_apply]
  congr 1
  exact Units.ext (Matrix.ext fun p q => D.map_shift _ i)

private theorem single_shift {ι G : Type} [One G] (s i : Fin 2) (u v : ι) (m : G) :
    (Pi.mulSingle (s, u) m : Fin 2 × ι → G) (i + 1, v) = (Pi.mulSingle (s + 1, u) m : Fin 2 × ι → G) (i, v) := by
  have h : i + 1 = s ↔ i = s + 1 := by revert i s; decide
  simp only [Pi.mulSingle_apply, Prod.mk.injEq, h]

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coTw :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1) (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      (∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u) →
      ∀ (μ : Measure (G1 E 2)) [μ.IsHaarMeasure] (θ : Twist μ), UpperTheory.ConvolutionTheory.K.IsGal σ.toRingEquiv θ → ∀ s u m, θ.e (CE.un (s, u) m) = CE.un (s + 1, u) m := by
  intro F E _ _ _ _ _ _ _ σ D CF CE hC μ _ θ hθ s u m
  apply Subtype.ext
  rw [hθ]
  simp only [Co.un, arc1, archimedeanProjection_maximalCompact]
  rw [gal_infEmb]
  congr 1
  apply (CE.Ψ 2).injective
  funext ⟨i, v⟩
  rw [hC, compA_shift, ← hC]
  apply Units.ext
  rw [← CE.Φ_val, ← CE.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  congr 1
  convert single_shift s i u v m
end
