module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory

theorem summable_norm_coset_out (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (hμ : μ K = 1) (F : G → ℂ)
    (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hint : Integrable F μ) :
    Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  classical
  set C : G ⧸ K → Set G := fun x => (fun y => x.out⁻¹ * y) ⁻¹' (K : Set G) with hCdef
  have hCmeas : ∀ x, MeasurableSet (C x) := fun x =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCμ : ∀ x, μ (C x) = 1 := by
    intro x
    simp only [C]
    rw [measure_preimage_mul]; exact hμ
  have hconst : ∀ x, ∀ y ∈ C x, F y = F x.out := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have := hF x.out _ hy'
    simpa using this
  have hmk : ∀ x, ∀ y ∈ C x, (QuotientGroup.mk y : G ⧸ K) = x := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have h1 : (QuotientGroup.mk y : G ⧸ K) = QuotientGroup.mk x.out :=
      (QuotientGroup.eq.mpr hy').symm
    rw [h1]; exact Quotient.out_eq x
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    exact hxy ((hmk x z hzx).symm.trans (hmk y z hzy))
  have hnorm : Integrable (fun y => ‖F y‖) μ := hint.norm
  have hterm : ∀ x, ∫ y in C x, ‖F y‖ ∂μ = ‖F x.out‖ := by
    intro x
    rw [setIntegral_congr_fun (hCmeas x) (g := fun _ => ‖F x.out‖) (fun y hy => by
      simp only; rw [hconst x y hy])]
    rw [setIntegral_const]
    simp [Measure.real, hCμ x]
  refine summable_of_sum_le (c := ∫ y, ‖F y‖ ∂μ) (fun x => norm_nonneg _) ?_
  intro S
  calc ∑ x ∈ S, ‖F x.out‖ = ∑ x ∈ S, ∫ y in C x, ‖F y‖ ∂μ := by
        simp only [hterm]
    _ = ∫ y in ⋃ x ∈ S, C x, ‖F y‖ ∂μ := by
        rw [integral_biUnion_finset S (fun x _ => hCmeas x) (hdisj.set_pairwise _)
          (fun x _ => hnorm.integrableOn)]
    _ ≤ ∫ y, ‖F y‖ ∂μ :=
        setIntegral_le_integral hnorm (Filter.Eventually.of_forall (fun y => norm_nonneg _))

end GlobalTheory
end

section

open MeasureTheory Pointwise

namespace GlobalTheory

theorem eq_zero_of_ae_fundamentalDomain_of_leftInvariant
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsHaarMeasure] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : G → ℂ)
    (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x)
    (hae : ∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) : ∀ x, F x = 0 := by
  set U : Set G := {x | F x ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hF continuous_const
  have hUinv : ∀ g : Γ, g • U = U := by
    intro g
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, hUdef, Set.mem_setOf_eq, Subgroup.smul_def,
      smul_eq_mul]
    rw [hinv _ (Γ.inv_mem g.2)]
  have hU𝓕 : μ (U ∩ 𝓕) = 0 := by
    rw [ae_iff, Measure.restrict_apply hUo.measurableSet] at hae
    simpa [hUdef] using hae
  have hU0 : μ U = 0 := h𝓕.measure_zero_of_invariant U hUinv hU𝓕
  have hUe : U = ∅ := by
    by_contra hne
    exact (hUo.measure_pos μ (Set.nonempty_iff_ne_empty.mpr hne)).ne' hU0
  intro x
  by_contra hx
  have : x ∈ U := hx
  rw [hUe] at this
  exact this

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem integrable_of_tsum_translate_norm_le
    (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [Countable Γ] (μ : Measure G) (hμ : μ.IsAddLeftInvariant) (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h𝓕μ : μ 𝓕 < ⊤) (c : G → ℂ) (hc : Continuous c)
    (C : ℝ) (hC : ∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧
      ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) : Integrable c μ := by
  haveI : VAddInvariantMeasure Γ G μ := ⟨fun g s _ => measure_preimage_add μ (g : G) s⟩
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [h𝓕.lintegral_eq_tsum'' (fun x => ‖c x‖ₑ)]
  rw [← lintegral_tsum (f := fun (γ : Γ) x => ‖c (γ +ᵥ x)‖ₑ) fun γ : Γ =>
    ((hc.comp (continuous_const_vadd (γ : G))).measurable.enorm).aemeasurable]
  have hpt : ∀ x, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ≤ ENNReal.ofReal C := by
    intro x
    have h1 : ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ = ENNReal.ofReal (∑' γ : Γ, ‖c ((γ : G) + x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hC x).1]
      refine tsum_congr fun γ => ?_
      rw [ofReal_norm_eq_enorm]
      rfl
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hC x).2
  calc ∫⁻ x in 𝓕, ∑' γ : Γ, ‖c (γ +ᵥ x)‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, ENNReal.ofReal C ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal C * μ 𝓕 := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h𝓕μ

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.GaussLine

open Complex NumberField

def heisFun {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p)

def dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : V → ℂ)
    (x : V) : ℂ :=
  fderiv ℝ f x w.1 - 2 * Real.pi * Complex.I * (β x w.2 : ℂ) * f x

variable (F : Type) [Field F] [NumberField F]

def pairInf (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [smul_mul_assoc, ← Finset.smul_sum])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp [mul_smul_comm, ← Finset.smul_sum])

theorem pairInf_apply (κ : Type) [Fintype κ] (x y : κ → mixedEmbedding.mixedSpace F) :
    pairInf F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

theorem heisFun_apply {V : Type} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (p q : V) (f : V → ℂ) (x : V) :
    heisFun β p q f x = Complex.exp (-(2 * Real.pi * Complex.I) * ((β x q + β p q / 2 : ℝ) : ℂ)) * f (x + p) := rfl

end GlobalTheory.GaussLine

end
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff

namespace GlobalTheory


open Filter MeasureTheory Topology in
open MeasureTheory Filter Topology in
theorem contDiff_of_continuous_of_map_add_eq_mul {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℂ) (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 ≠ 0) : ContDiff ℝ ∞ f := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let b : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hb hf 0
  obtain ⟨n, hn⟩ := (ht.eventually_ne h0).exists
  have hs : ContDiff ℝ ∞
      (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ) :=
    HasCompactSupport.contDiff_convolution_left _ (b n).hasCompactSupport_normed
      (b n).contDiff_normed hf.locallyIntegrable
  have key : ∀ x, convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      = f x * convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0 := by
    intro x
    rw [convolution_def, convolution_def, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have : x - t = x + (0 - t) := by abel
    simp only [ContinuousLinearMap.lsmul_apply]
    rw [this, hadd, mul_smul_comm]
  have : f = fun x => convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      * (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0)⁻¹ := by
    funext x
    rw [key x, mul_inv_cancel_right₀ hn]
  rw [this]
  exact hs.mul contDiff_const

noncomputable def mixedExpUnit (K : Type) [Field K] (y : mixedSpace K) : (mixedSpace K)ˣ :=
  ⟨(fun w => Real.exp (y.1 w), fun w => Complex.exp (y.2 w)),
    (fun w => Real.exp (-y.1 w), fun w => Complex.exp (-y.2 w)),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add]),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add])⟩

theorem mixedExpUnit_add (K : Type) [Field K] (x y : mixedSpace K) :
    mixedExpUnit K (x + y) = mixedExpUnit K x * mixedExpUnit K y :=
  Units.ext (Prod.ext (funext fun w => Real.exp_add (x.1 w) (y.1 w))
    (funext fun w => Complex.exp_add (x.2 w) (y.2 w)))

theorem continuous_mixedExpUnit (K : Type) [Field K] : Continuous (mixedExpUnit K) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun y : mixedSpace K =>
      (((fun w => Real.exp (y.1 w), fun w => Complex.exp (y.2 w))) : mixedSpace K)
    fun_prop
  · show Continuous fun y : mixedSpace K =>
      (((fun w => Real.exp (-y.1 w), fun w => Complex.exp (-y.2 w))) : mixedSpace K)
    fun_prop

noncomputable def mixedLog (K : Type) [Field K] (x : mixedSpace K) : mixedSpace K :=
  (fun w => Real.log (x.1 w), fun w => Complex.log (x.2 w))

theorem contDiffAt_mixedLog_one (K : Type) [Field K] [NumberField K] :
    ContDiffAt ℝ ∞ (mixedLog K) 1 := by
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun w => ?_) (contDiffAt_pi.mpr fun w => ?_)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.1 w) :=
      (contDiff_apply ℝ (fun _ => ℝ) w).comp contDiff_fst
    exact h1.contDiffAt.log (by simp)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.2 w) :=
      (contDiff_apply ℝ (fun _ => ℂ) w).comp contDiff_snd
    have h2 : ContDiffAt ℝ ∞ Complex.log ((1 : mixedSpace K).2 w) :=
      (Complex.contDiffAt_log (by simp)).restrict_scalars ℝ
    exact h2.comp 1 h1.contDiffAt

open Filter Topology in
theorem eventually_mixedExpUnit_mixedLog (K : Type) [Field K] [NumberField K] :
    ∀ᶠ x in 𝓝 (1 : mixedSpace K), (mixedExpUnit K (mixedLog K x) : mixedSpace K) = x := by
  have h1 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, 0 < x.1 w := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.1 w) := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simp))
  have h2 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, x.2 w ≠ 0 := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.2 w) := by fun_prop
    exact hc.continuousAt.eventually_ne (by simp)
  filter_upwards [h1, h2] with x hx1 hx2
  exact Prod.ext (funext fun w => Real.exp_log (hx1 w)) (funext fun w => Complex.exp_log (hx2 w))

theorem mixedSpace_norm_ne_zero_iff_isUnit (K : Type) [Field K] [NumberField K]
    (x : mixedSpace K) : mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by
  rw [mixedEmbedding.norm_ne_zero_iff, Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  constructor
  · intro h
    refine ⟨fun w => ?_, fun w => ?_⟩
    · have := h w.1
      rw [normAtPlace_apply_of_isReal w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
    · have := h w.1
      rw [normAtPlace_apply_of_isComplex w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
  · rintro ⟨h1, h2⟩ w
    rcases w.isReal_or_isComplex with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]
      exact norm_ne_zero_iff.mpr (h1 _).ne_zero
    · rw [normAtPlace_apply_of_isComplex hw]
      exact norm_ne_zero_iff.mpr (h2 _).ne_zero

theorem exists_smooth_mul_extension_of_continuous_char :
    ∀ (K : Type) [Field K] [NumberField K] (ψ : (mixedSpace K)ˣ →* ℂˣ), Continuous ψ → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ u : (mixedSpace K)ˣ, φ u = (ψ u : ℂ)) ∧ ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by
  intro K _ _ ψ hψ
  let φ : mixedSpace K → ℂ := fun x => if h : IsUnit x then (ψ h.unit : ℂ) else 0
  have hu : ∀ u : (mixedSpace K)ˣ, φ u = (ψ u : ℂ) := by
    intro u
    simp only [φ, dif_pos u.isUnit, IsUnit.unit_of_val_units]
  have hn : ∀ x, ¬ IsUnit x → φ x = 0 := fun x hx => dif_neg hx
  have hmul : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [← Units.val_mul, hu, hu, hu, map_mul, Units.val_mul]
      · rw [hn y hy, hn _ (fun h => hy (isUnit_of_mul_isUnit_right h)), mul_zero]
    · rw [hn x hx, hn _ (fun h => hx (isUnit_of_mul_isUnit_left h)), zero_mul]
  have hf : ContDiff ℝ ∞ (fun y => (ψ (mixedExpUnit K y) : ℂ)) :=
    contDiff_of_continuous_of_map_add_eq_mul _
      (Units.continuous_val.comp (hψ.comp (continuous_mixedExpUnit K)))
      (fun x y => by rw [mixedExpUnit_add, map_mul, Units.val_mul]) (Units.ne_zero _)
  have h1 : ContDiffAt ℝ ∞ φ 1 := by
    refine (hf.contDiffAt.comp 1 (contDiffAt_mixedLog_one K)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_mixedExpUnit_mixedLog K] with x hx
    rw [Function.comp_apply, ← hu, hx]
  refine ⟨φ, hmul, fun x hx => ?_, hu, mixedSpace_norm_ne_zero_iff_isUnit K⟩
  obtain ⟨u, rfl⟩ := (mixedSpace_norm_ne_zero_iff_isUnit K x).mp hx
  have h2 : φ = fun z => φ u * φ ((u⁻¹ : (mixedSpace K)ˣ) * z) := by
    funext z
    rw [← hmul, Units.mul_inv_cancel_left]
  have h3 : ContDiffAt ℝ ∞ φ (((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * u) := by
    rw [Units.inv_mul]
    exact h1
  have h4 : ContDiffAt ℝ ∞
      (fun z : mixedSpace K => φ u * φ ((u⁻¹ : (mixedSpace K)ˣ) * z)) (u : mixedSpace K) :=
    contDiffAt_const.mul (h3.comp (u : mixedSpace K)
      (f := fun z : mixedSpace K => ((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * z)
      (contDiffAt_const.mul contDiffAt_id))
  rw [← h2] at h4
  exact h4.contDiffWithinAt

end GlobalTheory
end

section

open scoped InnerProductSpace
open Filter Topology

namespace GlobalTheory

theorem dense_span_tensor_of_dense_subspaces {ι : Type} [Fintype ι] {H : ι → Type}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type}
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs)
    (W : ∀ i, Submodule ℂ (H i)) (hu : ∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs))
    (hW : ∀ i, Dense (W i : Set (H i))) :
    Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) :
      Set Hs) := by
  have hnorm : ∀ x y, ‖u y - u x‖ = Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
      - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) := by
    intro x y
    rw [← hu, ← hu, ← hu, inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← norm_sub_sq,
      Real.sqrt_sq (norm_nonneg _)]
  have hcont : Continuous u := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hc : Continuous (fun y : (∀ i, H i) => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
        - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ))) := by
      fun_prop
    have key : Tendsto (fun y => ‖u y - u x‖) (𝓝 x) (𝓝 ‖u x - u x‖) := by
      have e : (fun y => ‖u y - u x‖) = fun y => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
          - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) :=
        funext fun y => hnorm x y
      rw [e, hnorm x x]
      exact hc.tendsto x
    simpa using key
  set S := Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i))))
    with hS
  have hpi : Dense (Set.pi Set.univ (fun i => (W i : Set (H i)))) :=
    dense_pi Set.univ (fun i _ => hW i)
  have hsub : Set.range u ⊆ closure (S : Set Hs) := by
    rintro _ ⟨x, rfl⟩
    refine map_mem_closure hcont (hpi x) ?_
    intro y hy
    apply Submodule.subset_span
    exact ⟨fun i => ⟨y i, hy i (Set.mem_univ i)⟩, rfl⟩
  have hle : Submodule.span ℂ (Set.range u) ≤ S.topologicalClosure := by
    rw [Submodule.span_le, Submodule.topologicalClosure_coe]
    exact hsub
  have h2 : Dense (S.topologicalClosure : Set Hs) := hd.mono hle
  rwa [Submodule.topologicalClosure_coe, dense_closure] at h2

end GlobalTheory
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem continuousMultilinearMap_ext_hilbertBasis (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F)
    (h : ∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) : f = g := by
  have key : ∀ s : Finset ι, ∀ y : ∀ i, Hs i,
      (∀ i, i ∉ s → y i ∈ Set.range (e i)) → f y = g y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy
      choose j hj using fun i => hy i (by simp)
      have hy' : y = fun i => e i (j i) := funext fun i => (hj i).symm
      rw [hy']
      exact h j
    | insert a s ha ih =>
      intro y hy
      let L : Hs a →L[ℂ] F := (f - g).toContinuousLinearMap y a
      have hL : Set.EqOn (L : Hs a → F) (0 : Hs a →L[ℂ] F) (Set.range (e a)) := by
        intro z hz
        simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
          ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero]
        apply ih
        intro i hi
        by_cases hia : i = a
        · subst hia
          simpa using hz
        · rw [Function.update_of_ne hia]
          exact hy i (by simp [hia, hi])
      have hdense : Dense (Submodule.span ℂ (Set.range (e a)) : Set (Hs a)) := by
        exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (e a).dense_span
      have hL0 : L = 0 := ContinuousLinearMap.ext_on hdense hL
      have hya := congrArg (fun M : Hs a →L[ℂ] F => M (y a)) hL0
      simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
        ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero,
        Function.update_eq_self] at hya
      exact hya
  ext y
  exact key Finset.univ y (by simp)

end GlobalTheory
end
