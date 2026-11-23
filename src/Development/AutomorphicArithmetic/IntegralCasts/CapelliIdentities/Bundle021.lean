module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

namespace OneParameterGroupMulIntegral
open intervalIntegral

private lemma mul_integral {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (c : A) (f : ℝ → A) (a b : ℝ) (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    c * (∫ s in a..b, f s) = ∫ s in a..b, c * f s := by
  have := (ContinuousLinearMap.mul ℝ A c).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    (a := a) (b := b) (f := f)
  simpa using (this hf).symm

end OneParameterGroupMulIntegral

open OneParameterGroupMulIntegral in
theorem UpperTheory.Reformulated.B.OneParameterGroupDifferentiableAtZero.main.{u_1} :
    ∀ {W : Type u_1} [inst : NormedAddCommGroup W]
    [inst_1 : NormedSpace ℂ W] [CompleteSpace W] (φ : ℝ → W →L[ℂ] W),
    Continuous φ → φ (0 : ℝ) = (1 : W →L[ℂ] W) → (∀ (s t : ℝ), φ (s + t) = φ s * φ t) → DifferentiableAt ℝ φ (0 : ℝ) := by
  intro W _ _ _ φ hc h0 hmul

  obtain ⟨ε, εpos, hε⟩ := Metric.continuous_iff.mp hc 0 (1/2) (by norm_num)
  set δ : ℝ := ε / 2 with hδ
  have δpos : 0 < δ := by positivity
  set A : W →L[ℂ] W := ∫ s in (0:ℝ)..δ, φ s with hA
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hest : ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ 1/2 * δ := by
    have e1 : A - δ • (1 : W →L[ℂ] W) = ∫ s in (0:ℝ)..δ, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 δ) intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp <;> rfl
    rw [e1]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := 1/2)
      (f := fun s => φ s - 1) (by
        intro x hx
        rw [Set.uIoc_of_le δpos.le] at hx
        have hxd : dist x 0 < ε := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2]
        have := hε x hxd
        rw [dist_eq_norm, h0] at this
        exact this.le)
    simpa [abs_of_pos δpos] using this
  have hsmall : ‖1 - δ⁻¹ • A‖ < 1 := by
    have : 1 - δ⁻¹ • A = -(δ⁻¹ • (A - δ • (1 : W →L[ℂ] W))) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ δpos.ne']; simp
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr δpos)]
    calc δ⁻¹ * ‖A - δ • (1 : W →L[ℂ] W)‖ ≤ δ⁻¹ * (1/2 * δ) :=
          mul_le_mul_of_nonneg_left hest (inv_pos.mpr δpos).le
      _ = 1/2 := by field_simp
      _ < 1 := by norm_num
  set u := Units.oneSub (1 - δ⁻¹ • A) hsmall
  have hu : (u : W →L[ℂ] W) = δ⁻¹ • A := by simp [u, Units.val_oneSub]
  set B : W →L[ℂ] W := δ⁻¹ • ((u⁻¹ : (W →L[ℂ] W)ˣ) : W →L[ℂ] W)
  have hAB : A * B = 1 := by
    simp only [B, mul_smul_comm, ← smul_mul_assoc, ← hu]
    exact u.mul_inv
  set F : ℝ → W →L[ℂ] W := fun u => ∫ s in (0:ℝ)..u, φ s
  have key : ∀ t, φ t = (F (t + δ) - F t) * B := by
    intro t
    have h1 : φ t * A = F (t + δ) - F t := by
      rw [hA, mul_integral _ _ _ _ (hint 0 δ)]
      have : (fun s => φ t * φ s) = fun s => φ (t + s) := by
        funext s; rw [hmul]
      rw [this, intervalIntegral.integral_comp_add_left (fun s => φ s) t]
      simp only [add_zero, F]
      rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + δ)) (hint 0 t)]
    calc φ t = φ t * A * B := by rw [mul_assoc, hAB, mul_one]
      _ = _ := by rw [h1]
  have hF : ∀ x, HasDerivAt F (φ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * B) ((φ (0 + δ) - φ 0) * B) 0 := by
    apply HasDerivAt.mul_const
    apply HasDerivAt.sub
    · exact (hF (0 + δ)).comp_add_const 0 δ
    · exact hF 0
  have : φ = fun t => (F (t + δ) - F t) * B := funext key
  rw [this]
  exact hd.differentiableAt
end

section

open scoped ContDiff

namespace UpperTheory.Reformulated.B.weightedSumBis

theorem exists_eq_exp (f : ℝ → ℂ) (hc : Continuous f) (h0 : f 0 = 1) (hm : ∀ x y, f (x + y) = f x * f y) :
    ∃ c : ℂ, ∀ x : ℝ, f x = Complex.exp (c * x) := by
  set F : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, f t with hF
  have hFd : ∀ u, HasDerivAt F (f u) u := fun u =>
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  obtain ⟨a, ha⟩ : ∃ a, F a ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : F = fun _ => 0 := funext h
    have h2 := hFd 0
    rw [h1, h0] at h2
    exact one_ne_zero (h2.unique (hasDerivAt_const _ _))
  have key : ∀ x, f x = (F (x + a) - F x) / F a := by
    intro x
    rw [eq_div_iff ha]
    have h1 : F (x + a) - F x = ∫ t in x..(x + a), f t :=
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
    have h2 : ∫ t in (0 : ℝ)..a, f (x + t) = ∫ t in x..(x + a), f t := by
      simp
    rw [h1, ← h2]
    simp only [hm, hF]
    rw [intervalIntegral.integral_const_mul]
  set c : ℂ := (f a - 1) / F a with hcdef
  have hfd : ∀ x, HasDerivAt f (c * f x) x := by
    intro x
    have h1 : HasDerivAt (fun y => (F (y + a) - F y) / F a) ((f (x + a) - f x) / F a) x :=
      (((hFd (x + a)).comp_add_const x a).sub (hFd x)).div_const _
    rw [← funext key] at h1
    convert h1 using 1
    rw [hm, hcdef]
    ring
  have hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f y * Complex.exp (-c * y)) 0 x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (-c * y)) (Complex.exp (-c * x) * (-c * 1)) x :=
      ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-c)).cexp
    have h2 := (hfd x).mul h1
    have h3 : c * f x * Complex.exp (-c * x) + f x * (Complex.exp (-c * x) * (-c * 1)) = 0 := by
      ring
    rw [h3] at h2
    exact h2
  refine ⟨c, fun x => ?_⟩
  have h := is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
    (fun y => (hg y).deriv) x 0
  simp only [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  rw [neg_mul, Complex.exp_neg] at h
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp h

end UpperTheory.Reformulated.B.weightedSumBis
end

section

open MeasureTheory in
theorem UpperTheory.Reformulated.B.Qo7.eq_zero_of_orth :
    ∀ {K : Type} [inst : TopologicalSpace K] [CompactSpace K]
    [inst_2 : MeasurableSpace K] [BorelSpace K] (μ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (S : Set C(K, ℂ)),
    (1 : C(K, ℂ)) ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) →
        (∀ a ∈ S, Star.star a ∈ S) →
          (∀ (x y : K), x ≠ y → ∃ a ∈ S, (a : K → ℂ) x ≠ (a : K → ℂ) y) →
            ∀ (f : C(K, ℂ)), (∀ a ∈ S, ∫ (x : K), (a : K → ℂ) x * (f : K → ℂ) x ∂μ = (0 : ℂ)) → f = (0 : C(K, ℂ)) := by
  intro K _ _ _ _ μ _ _ S h1 hmul hstar hsep f hf
  have hint : ∀ g : C(K, ℂ), Integrable (fun x => g x) μ := fun g =>
    (BoundedContinuousFunction.mkOfCompact g).integrable μ
  have hint' : ∀ a : C(K, ℂ), Integrable (fun x => a x * f x) μ := fun a => hint (a * f)
  let L0 : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ x, a x * f x ∂μ
      map_add' := fun a b => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint' a) (hint' b)
      map_smul' := fun c a => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hL : Continuous L0 := by
    refine (L0.mkContinuous (‖f‖ * μ.real Set.univ) fun a => ?_).continuous
    have : ‖∫ x, a x * f x ∂μ‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      exact mul_le_mul (a.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
    calc ‖L0 a‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := this
      _ = _ := by ring
  have hspan : ∀ a ∈ StarAlgebra.adjoin ℂ S, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using StarAlgebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨u, hu, v, hv, rfl⟩
      exact hmul u hu v hv
    | star x _ hx =>
      clear * - hx hstar
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hstar y hy)
      | zero => simp
      | add y z _ _ hy hz => rw [star_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy
  have hker : Submodule.span ℂ S ≤ LinearMap.ker L0 :=
    Submodule.span_le.2 fun a ha => hf a ha
  have hsp : (StarAlgebra.adjoin ℂ S).SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, ha, hne⟩ := hsep x y hxy
    exact ⟨a, ⟨a, StarAlgebra.subset_adjoin ℂ S ha, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsp
  have hall : ∀ a : C(K, ℂ), L0 a = 0 := by
    intro a
    have ha : a ∈ closure (StarAlgebra.adjoin ℂ S : Set C(K, ℂ)) := by
      have : a ∈ (StarAlgebra.adjoin ℂ S).topologicalClosure := by
        rw [htop]; exact StarSubalgebra.mem_top
      exact this
    exact closure_minimal (t := {b | L0 b = 0}) (fun b hb => hker (hspan b hb))
      (isClosed_eq hL continuous_const) ha
  have h0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by
    have h := hall (star f)
    change ∫ x, (star f) x * f x ∂μ = 0 at h
    have e : (fun x => (star f) x * f x) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      simp only [ContinuousMap.star_apply, RCLike.star_def]
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [e, integral_complex_ofReal] at h
    exact_mod_cast h
  have hc : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable μ
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).1 h0
  have heq := (hc.ae_eq_iff_eq μ continuous_zero).1 hae
  ext x
  simpa using congrFun heq x
end

section

theorem UpperTheory.Reformulated.B.Qf11.expSq :
    ∀ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ),
    N * N = (0 : Matrix (Fin n) (Fin n) ℂ) → NormedSpace.exp N = (1 : Matrix (Fin n) (Fin n) ℂ) + N := by
  intro n N h
  have hz : ∀ k : ℕ, k ∉ Finset.range 2 → ((k.factorial : ℂ)⁻¹) • N ^ k = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by
      rw [Finset.mem_range] at hk
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    rw [pow_add, pow_two, h, zero_mul, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ]
end

section

open MeasureTheory

theorem UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le {X : Type*} (c : X → ℝ) (hb : ∀ x, |c x| ≤ 1)
    (x : X) (z : ℂ) : ‖(c x : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb x)

theorem UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (c : X → ℝ) (hc : Measurable c) (hb : ∀ x, |c x| ≤ 1) (f : Lp ℂ 2 ν) :
    MemLp (fun x => (c x : ℂ) * f x) 2 ν :=
  (Lp.memLp f).of_le
    ((Complex.measurable_ofReal.comp hc).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le c hb x (f x))

noncomputable def UpperTheory.Reformulated.B.MultiplicationNormBound.mulL.{u_1} :
    {X : Type u_1} →
      [inst : MeasurableSpace X] →
        {ν : MeasureTheory.Measure X} →
          (c : X → ℝ) →
            Measurable c →
              (∀ (x : X), |c x| ≤ (1 : ℝ)) →
                ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) →L[ℂ] ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν) :=
  fun {X} _ {ν} c hc hb =>
    LinearMap.mkContinuous
      { toFun := fun f => (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp (fun x => (c x : ℂ) * f x)
        map_add' := fun f g => by
          apply Lp.ext
          filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb (f + g)).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb g).coeFn_toLp, Lp.coeFn_add f g,
            Lp.coeFn_add ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp _)
              ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb g).toLp _)] with x h1 h2 h3 h4 h5
          rw [h1, h5, h4, Pi.add_apply, Pi.add_apply, h2, h3, mul_add]
        map_smul' := fun a f => by
          apply Lp.ext
          filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb (a • f)).coeFn_toLp,
            (UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp, Lp.coeFn_smul a f,
            Lp.coeFn_smul a ((UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).toLp _)] with x h1 h2 h3 h4
          rw [RingHom.id_apply, h1, h4, h3, Pi.smul_apply, Pi.smul_apply, h2, smul_eq_mul,
            smul_eq_mul, mul_left_comm] }
      1
      (fun f => by
        rw [one_mul]
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(UpperTheory.Reformulated.B.MultiplicationNormBound.memLp_mul c hc hb f).coeFn_toLp] with x h
        exact h ▸ UpperTheory.Reformulated.B.MultiplicationNormBound.norm_mul_le c hb x (f x))
end

section

theorem UpperTheory.Reformulated.B.Yxa1.main :
    ∀ {α : Type} [inst : MeasurableSpace α] {ν : MeasureTheory.Measure α} {ι : Type} (s : Finset ι)
      (g : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑(∑ j ∈ s, g j) : α →ₘ[ν] ℂ) : α → ℂ) =ᵐ[ν] fun (x : α) ↦ ∑ j ∈ s, (↑(↑(g j) : α →ₘ[ν] ℂ) : α → ℂ) x := by
  intro α _ ν ι s g
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 ν
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [MeasureTheory.Lp.coeFn_add (g a) (∑ j ∈ s, g j), ih] with x hx hx'
    rw [hx, Pi.add_apply, hx']
end

section

open Filter Topology NumberField IsDedekindDomain

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero {K : Type*} [NormedField K]
    (h1 : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (N : ℕ) (hN : 0 < N) (hlt : ‖(N : K)‖ < 1) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : K)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (norm_nonneg _),
    fun a ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ha hlt
  filter_upwards [eventually_ge_atTop (N ^ k)] with n hn
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hN k) hn
  rw [hm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (by positivity) (h1 m)).trans_lt hk

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  refine UpperTheory.Reformulated.B.AdelicCharacterNormOne.factorial_tendsto_zero (K := v.adicCompletion F) (fun n => ?_)
    (Ideal.absNorm v.asIdeal) (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)) ?_
  · have := FinitePlace.norm_le_one F v (n : 𝓞 F)
    rwa [map_natCast, map_natCast] at this
  · have := (FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
    rwa [map_natCast, map_natCast] at this

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto {F : Type} [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h : Tendsto (fun (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_subtype_rng]
    simpa using UpperTheory.Reformulated.B.AdelicCharacterNormOne.local_tendsto v
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous
  exact (hc.tendsto _).comp h

private lemma UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto {r : ℝ} (hr : 0 ≤ r)
    (h : Tendsto (fun n : ℕ => r ^ n.factorial) atTop (𝓝 1)) : r = 1 := by
  have hf : Tendsto Nat.factorial atTop atTop :=
    tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · exact absurd (tendsto_nhds_unique ((tendsto_pow_atTop_nhds_zero_of_lt_one hr hlt).comp hf) h)
      zero_ne_one
  · exact heq
  · exact absurd h (not_tendsto_nhds_of_tendsto_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt hgt).comp hf) 1)

theorem UpperTheory.Reformulated.B.AdelicCharacterNormOne.norm_eq_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ℂ),
    Continuous (⇑ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) →
      (∀ (a : F),
          (ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ)
              ((Algebra.algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
                  F → NumberField.AdeleRing (NumberField.RingOfIntegers F) F)
                a) =
            (1 : ℂ)) →
        ∀ (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F),
          ‖(ψ : NumberField.AdeleRing (NumberField.RingOfIntegers F) F → ℂ) x‖ = (1 : ℝ) := by
  intro F _ _ ψ hψ htriv
  let i : InfiniteAdeleRing F → AdeleRing (𝓞 F) F := fun x => (x, 0)
  let j : FiniteAdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F := fun y => (0, y)
  have hi : Continuous i := continuous_id.prodMk continuous_const
  have hj : Continuous j := continuous_const.prodMk continuous_id
  have hsplit : ∀ x : AdeleRing (𝓞 F) F, x = i x.1 + j x.2 := fun x =>
    Prod.ext (add_zero x.1).symm (zero_add x.2).symm
  have hfin : ∀ y, ‖ψ (j y)‖ = 1 := by
    intro y
    apply UpperTheory.Reformulated.B.AdelicCharacterNormOne.eq_one_of_tendsto (norm_nonneg _)
    have h1 := (UpperTheory.Reformulated.B.AdelicCharacterNormOne.finite_tendsto (F := F)).mul_const y
    rw [zero_mul] at h1
    have h2 := (((hψ.comp hj).norm).tendsto 0).comp h1
    have h0 : j 0 = 0 := rfl
    have hs : ∀ n : ℕ, j ((n : FiniteAdeleRing (𝓞 F) F) * y) = n • j y := fun n =>
      Prod.ext (nsmul_zero n).symm (nsmul_eq_mul n y).symm
    simp only [Function.comp_def, h0, hs, AddChar.map_zero_eq_one, norm_one,
      AddChar.map_nsmul_eq_pow, norm_pow] at h2
    exact h2
  have hinf : ∀ x, ‖ψ (i x)‖ = 1 := by
    intro x
    refine (InfiniteAdeleRing.denseRange_algebraMap F).induction_on x
      (isClosed_eq (hψ.comp hi).norm continuous_const) fun a => ?_
    have h := congrArg norm (htriv a)
    rw [hsplit (algebraMap F _ a), AddChar.map_add_eq_mul, norm_mul, hfin, mul_one, norm_one] at h
    exact h
  intro x
  rw [hsplit x, AddChar.map_add_eq_mul, norm_mul, hfin, hinf, mul_one]
end

section

theorem UpperTheory.Reformulated.B.TraceMixedEmbedding.trace_mixedEmbedding :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
    (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
        ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
      (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by
  intro F _ _ y
  classical
  rw [Algebra.trace_eq_matrix_trace (NumberField.mixedEmbedding.latticeBasis F),
    Algebra.trace_eq_matrix_trace (NumberField.integralBasis F)]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [NumberField.mixedEmbedding.latticeBasis_apply, ← map_mul,
    NumberField.mixedEmbedding.latticeBasis_repr_apply]
end
