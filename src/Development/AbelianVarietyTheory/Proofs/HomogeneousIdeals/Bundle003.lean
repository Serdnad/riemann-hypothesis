module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

universe u_1

namespace GlobalTheory.ExpOfFrechetDerivative

theorem eq_exp_fderiv {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    (hd : DifferentiableAt ℂ f (0 : E)) (h0 : f (0 : E) ≠ (0 : ℂ))
    (hmul : ∀ x y : E, f (x + y) = f x * f y) (z : E) :
    f z = Complex.exp ((fderiv ℂ f (0 : E) : E → ℂ) z) := by
  set L := fderiv ℂ f (0 : E) with hL

  have hf0 : f 0 = 1 := by
    have h00 := hmul 0 0
    rw [add_zero] at h00
    have hfac : f 0 * (f 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h00, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h

  have hD : ∀ x : E, HasFDerivAt f (f x • L) x := by
    intro x
    have h1 : HasFDerivAt f L (x - x) := by
      rw [sub_self]
      exact hd.hasFDerivAt
    have h2 : HasFDerivAt (fun y : E => f (y - x)) L x := by
      have h := h1.comp (f := fun y : E => y - x) x ((hasFDerivAt_id x).sub_const x)
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    refine (h2.const_mul (f x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    show f y = f x * f (y - x)
    rw [← hmul, add_sub_cancel]

  have hE : ∀ y : E, HasFDerivAt (fun y => f y * Complex.exp (-(L y)))
      (f y • (Complex.exp (-(L y)) • -L) + Complex.exp (-(L y)) • (f y • L)) y :=
    fun y => (hD y).mul (L.hasFDerivAt.neg.cexp)
  have hzero : ∀ y, fderiv ℂ (fun y => f y * Complex.exp (-(L y))) y = 0 := by
    intro y
    rw [(hE y).fderiv]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hc := is_const_of_fderiv_eq_zero (fun y => (hE y).differentiableAt) hzero z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one, hf0] at hc
  calc f z = f z * Complex.exp (-(L z)) * Complex.exp (L z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (L z) := by rw [hc, one_mul]

end GlobalTheory.ExpOfFrechetDerivative
end

section

open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real

local notation "𝕢" => Periodic.qParam

noncomputable section

namespace GlobalTheory

def HasQExpansion (h : ℝ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m ↦ coeff m φ * 𝕢 h τ ^ m) (f τ)

namespace HasQExpansion

variable {h : ℝ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}

lemma one_le_radius (hh : 0 < h) (hf : HasQExpansion h f φ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ coeff m φ)).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  rcases eq_or_ne r 0 with rfl | hr'
  · simp
  · lift r to NNReal using hr.ne_top
    apply FormalMultilinearSeries.le_radius_of_summable
    have hq : ‖((r : ℝ) : ℂ)‖ < 1 := by simpa using hr
    have hq1 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr'
    have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
    have := (hf ⟨_, h1⟩).summable.norm
    simp only [Periodic.qParam_right_inv hh.ne' hq1] at this
    simpa [norm_mul] using this

lemma exists_analytic (hh : 0 < h) (hf : HasQExpansion h f φ) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 1) ∧ F 0 = coeff 0 φ ∧
      ∀ τ : ℍ, f τ = F (𝕢 h τ) := by
  set p := FormalMultilinearSeries.ofScalars ℂ (fun m ↦ coeff m φ) with hp
  have h1 : 1 ≤ p.radius := hf.one_le_radius hh
  have h2 : HasFPowerSeriesOnBall p.sum p 0 1 :=
    (p.hasFPowerSeriesOnBall (zero_lt_one.trans_le h1)).mono zero_lt_one h1
  refine ⟨p.sum, ?_, ?_, fun τ ↦ ?_⟩
  · have := h2.analyticOnNhd
    rwa [← ENNReal.coe_one, Metric.eball_coe] at this
  · rw [← h2.coeff_zero (fun _ ↦ 0)]
    simp [hp, FormalMultilinearSeries.ofScalars_apply_eq']
  · rw [FormalMultilinearSeries.sum, ← (hf τ).tsum_eq]
    simp [hp, FormalMultilinearSeries.ofScalars_apply_eq', mul_comm]

lemma tendsto (hh : 0 < h) (hf : HasQExpansion h f φ) :
    Tendsto f atImInfty (𝓝 (coeff 0 φ)) := by
  obtain ⟨F, hF, h0, hfF⟩ := hf.exists_analytic hh
  rw [show f = F ∘ fun τ : ℍ ↦ 𝕢 h τ from funext hfF, ← h0]
  exact (hF 0 (by simp)).continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)

lemma isBoundedAtImInfty (hh : 0 < h) (hf : HasQExpansion h f φ) : IsBoundedAtImInfty f :=
  (hf.tendsto hh).isBigO_one ℝ

lemma mdifferentiable (hh : 0 < h) (hf : HasQExpansion h f φ) : MDiff f := by
  obtain ⟨F, hF, -, hfF⟩ := hf.exists_analytic hh
  rw [UpperHalfPlane.mdifferentiable_iff]
  have : DifferentiableOn ℂ (fun z ↦ F (𝕢 h z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have h1 : DifferentiableAt ℂ F (𝕢 h z) :=
      (hF _ (by simpa using Periodic.norm_qParam_lt_one hh hz)).differentiableAt
    exact (h1.comp z (Periodic.differentiable_qParam z)).differentiableWithinAt
  refine this.congr fun z hz ↦ ?_
  simp [ofComplex_apply_of_im_pos hz, hfF]

lemma congr (hf : HasQExpansion h f φ) (hfg : ∀ τ, g τ = f τ) : HasQExpansion h g φ :=
  fun τ ↦ hfg τ ▸ hf τ

lemma sub (hf : HasQExpansion h f φ) (hg : HasQExpansion h g ψ) :
    HasQExpansion h (fun τ ↦ f τ - g τ) (φ - ψ) := fun τ ↦ by
  simpa [sub_mul] using (hf τ).sub (hg τ)

lemma mul (hf : HasQExpansion h f φ) (hg : HasQExpansion h g ψ) :
    HasQExpansion h (fun τ ↦ f τ * g τ) (φ * ψ) := fun τ ↦ by
  have h1 := (hf τ).summable.norm
  have h2 := (hg τ).summable.norm
  have h3 := (summable_norm_sum_mul_antidiagonal_of_summable_norm h1 h2).of_norm.hasSum
  rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h1 h2, (hf τ).tsum_eq,
    (hg τ).tsum_eq] at h3
  convert! h3 using 2 with m
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx]
  ring

lemma const (h : ℝ) (c : ℂ) : HasQExpansion h (fun _ ↦ c) (C c) := fun τ ↦ by
  have := hasSum_single (f := fun m ↦ coeff m (C c) * 𝕢 h τ ^ m) 0
    (fun m hm ↦ by simp [coeff_C, hm])
  simpa using this

lemma qParam (h : ℝ) : HasQExpansion h (fun τ ↦ 𝕢 h τ) X := fun τ ↦ by
  have := hasSum_single (f := fun m ↦ coeff m (X : PowerSeries ℂ) * 𝕢 h τ ^ m) 1
    (fun m hm ↦ by simp [coeff_X, hm])
  simpa using this

lemma pow (hf : HasQExpansion h f φ) (n : ℕ) : HasQExpansion h (fun τ ↦ f τ ^ n) (φ ^ n) := by
  induction n with
  | zero => simpa using const h 1
  | succ n ih => simpa [pow_succ] using ih.mul hf

lemma of_qParam_mul (hf : HasQExpansion h (fun τ ↦ 𝕢 h τ * f τ) (X * φ)) :
    HasQExpansion h f φ := fun τ ↦ by
  have h1 := (hasSum_nat_add_iff' 1).mpr (hf τ)
  have hq : 𝕢 h τ ≠ 0 := Periodic.qParam_ne_zero _
  have h2 := h1.mul_left (𝕢 h τ)⁻¹
  simp only [coeff_succ_X_mul, Finset.range_one, Finset.sum_singleton, coeff_zero_X_mul,
    zero_mul, sub_zero, inv_mul_cancel_left₀ hq] at h2
  convert! h2 using 2 with m
  field_simp
  ring

lemma eq_zero (hh : 0 < h) (hf : HasQExpansion h (fun _ ↦ 0) φ) : φ = 0 := by
  ext m
  induction m generalizing φ with
  | zero => exact (tendsto_nhds_unique tendsto_const_nhds (hf.tendsto hh)).symm
  | succ m ih =>
    have h0 : coeff 0 φ = 0 := (tendsto_nhds_unique tendsto_const_nhds (hf.tendsto hh)).symm
    obtain ⟨ψ, rfl⟩ : X ∣ φ := X_dvd_iff.mpr (by simpa using h0)
    have := ih (φ := ψ) (of_qParam_mul (by simpa using hf))
    simpa [coeff_succ_X_mul] using this

lemma unique (hh : 0 < h) (hf : HasQExpansion h f φ) (hg : HasQExpansion h f ψ) : φ = ψ :=
  sub_eq_zero.mp (eq_zero hh (by simpa using hf.sub hg))

lemma of_hasSum_pow {c : ℕ → ℂ} {e : ℕ} (he : e ≠ 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m * (𝕢 h τ ^ e) ^ m) (f τ)) :
    HasQExpansion h f (PowerSeries.mk fun k ↦ if e ∣ k then c (k / e) else 0) := fun τ ↦ by
  have hinj : Injective (fun m : ℕ ↦ e * m) := mul_right_injective₀ he
  rw [← hinj.hasSum_iff]
  · convert hf τ using 2 with m
    simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he), pow_mul]
  · intro k hk
    have : ¬ e ∣ k := fun ⟨m, hm⟩ ↦ hk ⟨m, hm.symm⟩
    simp [this]

lemma of_periodic (hh : 0 < h) (hper : Periodic (f ∘ ofComplex) h) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) : HasQExpansion h f (qExpansion h f) := fun τ ↦ by
  simpa using UpperHalfPlane.hasSum_qExpansion hh hper hhol hbdd τ

end HasQExpansion

lemma hasQExpansion_modularForm {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    HasQExpansion 1 f (qExpansion 1 f) := fun τ ↦
  ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_SL τ

end GlobalTheory
end
end

section

open MvPolynomial Cardinal

namespace GlobalTheory.GaloisDescent


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis {F F' L L' ι κ : Type*} [Field F] [Field F']
    [Field L] [Field L'] [Algebra F L] [Algebra F' L'] [IsAlgClosed L] [IsAlgClosed L']
    {v : ι → L} {w : κ → L'} (hv : IsTranscendenceBasis F v) (hw : IsTranscendenceBasis F' w)
    (e : MvPolynomial ι F ≃+* MvPolynomial κ F') :
    ∃ σ : L ≃+* L', ∀ p, σ (aeval v p) = aeval w (e p) := by
  letI : Algebra (MvPolynomial ι F) L := (aeval v).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial κ F') L' := (aeval w).toRingHom.toAlgebra
  have : Module.IsTorsionFree (MvPolynomial ι F) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hv.1
  have : Module.IsTorsionFree (MvPolynomial κ F') L' :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hw.1
  have : IsAlgClosure (MvPolynomial ι F) L := by
    refine ⟨inferInstance, ?_⟩
    have := hv.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hv.1.aevalEquiv.symm (RingHom.id L)
      hv.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval v (hv.1.aevalEquiv.symm a) = algebraMap _ L a
    rw [← hv.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  have : IsAlgClosure (MvPolynomial κ F') L' := by
    refine ⟨inferInstance, ?_⟩
    have := hw.isAlgebraic
    refine Algebra.IsAlgebraic.ringHom_of_comp_eq hw.1.aevalEquiv.symm (RingHom.id L')
      hw.1.aevalEquiv.symm.injective Function.surjective_id ?_
    ext a
    change aeval w (hw.1.aevalEquiv.symm a) = algebraMap _ L' a
    rw [← hw.1.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  exact ⟨IsAlgClosure.equivOfEquiv L L' e, fun p => IsAlgClosure.equivOfEquiv_algebraMap L L' e p⟩

theorem exists_ringEquiv_extend {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    (τ : F ≃+* F) : ∃ σ : L ≃+* L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs (mapEquiv s τ)
  refine ⟨σ, fun a => ?_⟩
  simpa using hσ (C a)

theorem exists_algEquiv_extend {K F L : Type*} [Field K] [Field F] [Field L] [Algebra K F]
    [Algebra F L] [Algebra K L] [IsScalarTower K F L] [IsAlgClosed L]
    (τ : F ≃ₐ[K] F) : ∃ σ : L ≃ₐ[K] L, ∀ a, σ (algebraMap F L a) = algebraMap F L (τ a) := by
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend (L := L) τ.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, hσ⟩
  rw [IsScalarTower.algebraMap_apply K F L, hσ]
  congr 1
  exact τ.commutes k

theorem exists_algEquiv_apply_eq_add_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] {x : L} (hx : Transcendental K x) : ∃ σ : L ≃ₐ[K] L, σ x = x + 1 := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (aeval fun i => X i + 1) (aeval fun i => X i - 1)
      (by ext i : 1; simp) (by ext i : 1; simp)
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun k => ?_, ?_⟩
  · simpa [e] using hσ (C k)
  · simpa [e] using hσ (X ⟨x, hxs rfl⟩)


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    [PerfectField K] [IsAlgClosed L] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    x ∈ Set.range (algebraMap K L) := by
  by_cases halg : IsAlgebraic K x
  · have hxA : x ∈ algebraicClosure K L := mem_algebraicClosure_iff.2 halg
    have hfix : ∀ f : Gal(algebraicClosure K L/K), f ⟨x, hxA⟩ = ⟨x, hxA⟩ := by
      intro f
      obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (algebraicClosure K L) L
      obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs
        (MvPolynomial.mapEquiv s (f : algebraicClosure K L ≃+* algebraicClosure K L))
      have hτA : ∀ a : algebraicClosure K L, τ (a : L) = (f a : L) := fun a => by
        simpa using hτ (MvPolynomial.C a)
      let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by
        simpa using hτA (algebraMap K (algebraicClosure K L) k))
      apply Subtype.ext
      rw [← hτA]
      exact hx σ
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
    exact ⟨k, congrArg Subtype.val hk⟩
  · classical
    have hind : AlgebraicIndepOn K id {x} :=
      (algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set L))).2 halg
    obtain ⟨t, hxt, ht⟩ := exists_isTranscendenceBasis_superset hind
    let i : t := ⟨x, hxt rfl⟩
    let φ : MvPolynomial t K ≃ₐ[K] MvPolynomial t K := AlgEquiv.ofAlgHom
      (aeval fun j => if j = i then X j + 1 else X j) (aeval fun j => if j = i then X j - 1 else X j)
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
      (MvPolynomial.algHom_ext fun j => by by_cases h : j = i <;> simp [h])
    obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis ht ht φ.toRingEquiv
    have hτx : τ x = x + 1 := by simpa [φ, i] using hτ (X i)
    let σ : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := τ) (fun k => by simpa [φ] using hτ (C k))
    have h1 := hx σ
    have h2 : τ x = x := h1
    rw [hτx] at h2
    simp at h2


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv {K : Type*} [Field K] [Algebra K ℂ] (x : ℂ)
    (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ Set.range (algebraMap K ℂ) := by
  haveI : CharZero K := RingHom.charZero (algebraMap K ℂ)
  exact _root_.GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv x hx


open MvPolynomial Cardinal in
theorem _root_.GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq {K : Type} [Field K] [Countable K] (f g : K →+* ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ a, σ (f a) = g a := by
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  letI Af : Algebra K ℂ := f.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  have hsc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hK hC
  letI Ag : Algebra K ℂ := g.toAlgebra
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have htc := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK hC
  obtain ⟨eqv⟩ := Cardinal.eq.1 (hsc.symm.trans htc)
  obtain ⟨σ, hσ⟩ := @_root_.GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis K K ℂ ℂ s t _ _ _ _ Af Ag _ _ _ _
    hs ht (MvPolynomial.renameEquiv K eqv).toRingEquiv
  refine ⟨σ, fun a => ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using hσ (MvPolynomial.C a)

end GlobalTheory.GaloisDescent
end

section

universe u_1 u_2

namespace GlobalTheory.PowerExtensionEvaluation

theorem pow_le_comap_map_pow {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) (n : ℕ) : I ^ n ≤ ((I.map f) ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (Ideal.map_pow f I n))

theorem factorPow_evalₐ {A : Type u_1} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (s.val n) = Ideal.Quotient.mk (I ^ m) (s.val m)
  rw [Ideal.Quotient.eq]
  have h := s.property hle
  rw [SModEq.sub_mem] at h
  have h2 : s.val m - s.val n ∈ I ^ m := by simpa [smul_eq_mul, Ideal.mul_top] using h
  have h3 := (I ^ m).neg_mem h2
  rwa [neg_sub] at h3

theorem exists_extension {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) [IsAdicComplete (Ideal.map f I) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A (AdicCompletion I A)) = f := by
  let F : (n : ℕ) → AdicCompletion I A →+* B ⧸ (Ideal.map f I) ^ n := fun n =>
    (Ideal.quotientMap ((Ideal.map f I) ^ n) f (pow_le_comap_map_pow I f n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.map f I) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hm : AdicCompletion.evalₐ I m x = Ideal.Quotient.mk (I ^ m) a := by
      rw [← factorPow_evalₐ I hle x, ← ha]
      rfl
    change Ideal.Quotient.factorPow (Ideal.map f I) hle
        (Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n x)) =
      Ideal.quotientMap _ f (pow_le_comap_map_pow I f m) (AdicCompletion.evalₐ I m x)
    rw [← ha, hm, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    rfl
  refine ⟨IsAdicComplete.liftRingHom (Ideal.map f I) F hF, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (Ideal.map f I)
  intro n a
  rw [RingHom.coe_comp, Function.comp_apply, IsAdicComplete.mk_liftRingHom]
  change Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A a)) = _
  rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

end GlobalTheory.PowerExtensionEvaluation
end
