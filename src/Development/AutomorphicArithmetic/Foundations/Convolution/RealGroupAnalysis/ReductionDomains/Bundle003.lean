module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
public import GroundTheory.AutomorphicForms.ReductionCore
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem oneVar {F : Type} [Field F] [NumberField F] (f w : A F → ℝ≥0∞) (hf : Measurable f) (hw : Measurable w)
    (hinv : ∀ (ξ : F) b, f (rt ξ + b) = f b) (hsum : ∀ b, ∑' ξ : F, w (rt ξ + b) = 1) :
    ∫⁻ b, f b * w b ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, f b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  let φ : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := hφ.2.countable
  rw [hD.lintegral_eq_tsum'' (fun b => f b * w b), ← lintegral_tsum]
  · refine lintegral_congr fun x => ?_
    rw [← (Equiv.ofBijective φ hφ).tsum_eq]
    have h1 : ∀ ξ : F, f ((Equiv.ofBijective φ hφ ξ) +ᵥ x) * w ((Equiv.ofBijective φ hφ ξ) +ᵥ x) = f x * w (rt ξ + x) := by
      intro ξ
      change f (rt ξ + x) * w (rt ξ + x) = _
      rw [hinv]
    simp only [h1]
    rw [ENNReal.tsum_mul_left, hsum, mul_one]
  · intro γ
    exact ((hf.mul hw).comp (measurable_const_add (γ : A F))).aemeasurable

theorem UpperTheory.ConvolutionTheory.R2.M.wtInt :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞), M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ β u hβ hu hinv
  haveI := M₀.prob
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  have hmD : Measurable (mD : IdeleGroup F → G1 F) := M.continuous_mD.measurable
  have hy : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    (hmD.comp measurable_fst).mul measurable_snd
  have hI : Measurable fun p : IdeleGroup F × G1 F =>
      ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : (IdeleGroup F × G1 F) × A F => u (nU q.2 * (mD q.1.1 * q.1.2)))
      (hu.comp ((hnU.comp measurable_snd).mul (hy.comp measurable_fst)))
  have hJ : Measurable fun p : IdeleGroup F × G1 F =>
      M.wt p.1 * ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    (M.measurable_wt.comp measurable_fst).mul hI
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ.1), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable]
  refine lintegral_congr fun k => lintegral_congr fun a => ?_
  have hsh : ∀ (ξ : F) (b : A F) (y : G1 F), nU (rt ξ + b) * y = nU (rt ξ) * (nU b * y) := by
    intro ξ b y
    rw [M.nU_add, mul_assoc]
  have hmy : ∀ v : G1 F → ℝ≥0∞, Measurable v → Measurable fun b : A F => v (nU b * (mD a * k)) :=
    fun v hv => hv.comp (hnU.mul_const _)
  have key := oneVar (fun b => u (nU b * (mD a * k))) (fun b => β (nU b * (mD a * k)))
    (hmy u hu) (hmy β hβ.1) (fun ξ b => by simp only [hsh, hinv])
    (fun b => by simp only [hsh]; exact hβ.2 _)
  simp only [mul_assoc (nU _) (mD a) k]
  rw [lintegral_mul_const (f := fun b => u (nU b * (mD a * k)) * β (nU b * (mD a * k))) _
    ((hmy u hu).mul (hmy β hβ.1)), key, mul_comm]
  rfl
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtOne :
    ∀ (F : Type) [Field F] [NumberField F] (β : G1 F → ℝ≥0∞), M.NWt β → ∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = 1 := by
  intro F _ _ β hβ g
  obtain ⟨hm, hs⟩ := hβ
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let e : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := he.surjective.countable
  have hfd := isAddFundamentalDomain_fundamentalSet F
  have hf : Measurable fun b : A F => β (nU b * g) :=
    hm.comp (M.continuous_nU.mul continuous_const).measurable
  rw [hfd.lintegral_eq_tsum'' (fun b => β (nU b * g)), ← lintegral_tsum]
  · have hone : ∀ x : A F,
        ∑' k : AdeleRing.principalSubgroup (𝓞 F) F, β (nU (k +ᵥ x) * g) = 1 := by
      intro x
      rw [← (Equiv.ofBijective e he).tsum_eq, ← hs (nU x * g)]
      refine tsum_congr fun ξ => ?_
      change β (nU (rt ξ + x) * g) = _
      rw [M.nU_add, mul_assoc]
    simp only [hone, lintegral_const, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter,
      adeleMeasure_fundamentalSet, one_mul]
  · intro k
    exact (hf.comp (measurable_const_vadd k)).aemeasurable
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem lintegral_mul_left_adele {F : Type} [Field F] [NumberField F] (c : (A F)ˣ) (g : A F → ℝ≥0∞) :
    ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) = ENNReal.ofReal (ab c)⁻¹ * ∫⁻ s, g s ∂(adeleMeasure F) := by
  have he : MeasurableEmbedding (fun x : A F => c • x) := (Homeomorph.smul c).measurableEmbedding
  have h1 : ∫⁻ s, g ((c : A F) * s) ∂(adeleMeasure F) =
      ∫⁻ s, g s ∂((adeleMeasure F).map (fun x : A F => c • x)) :=
    (he.lintegral_map g).symm
  rw [h1, map_smul_adeleMeasure, lintegral_smul_measure]
  rfl

private theorem wt_mul {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : M.wt (s * t) = M.wt s * M.wt t := by
  have hs : 0 ≤ ((ab s)⁻¹ ^ 2 : ℝ) := by positivity
  simp only [M.wt]
  rw [← ENNReal.ofReal_mul hs, M.ab_mul, mul_inv, mul_pow]

theorem UpperTheory.ConvolutionTheory.R2.M.borLeft :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (f : G1 F → ℝ≥0∞), Measurable f → ∀ (b₀ : A F) (a₀ : (A F)ˣ), ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) = ∫⁻ a : IdeleGroup F, ∫⁻ b, f (nU b * mD a) * M.wt a ∂(adeleMeasure F) ∂(ideleMeasure F) := by
  intro F _ _ f _ b₀ a₀
  have key : ∀ (a : (A F)ˣ) (b : A F), nU b₀ * mD a₀ * (nU b * mD a) =
      nU (b₀ + ((a₀ * a₀ : (A F)ˣ) : A F) * b) * mD (a₀ * a) := by
    intro a b
    rw [M.nU_add, M.mD_mul, mul_assoc (nU b₀), ← mul_assoc (mD a₀), M.mD_mul_nU]
    simp [pow_two, mul_assoc]
  have hc : ENNReal.ofReal (ab (a₀ * a₀))⁻¹ = M.wt a₀ := by
    simp only [M.wt]
    rw [M.ab_mul, mul_inv, pow_two]
  have inner : ∀ a : IdeleGroup F,
      ∫⁻ b, f (nU b₀ * mD a₀ * (nU b * mD a)) * M.wt a ∂(adeleMeasure F) =
        ∫⁻ b, f (nU b * mD (a₀ * a)) * M.wt (a₀ * a) ∂(adeleMeasure F) := by
    intro a
    have hwa : M.wt a ≠ ∞ := ENNReal.ofReal_ne_top
    have hwb : M.wt (a₀ * a) ≠ ∞ := ENNReal.ofReal_ne_top
    simp only [key]
    rw [lintegral_mul_const' _ _ hwa, lintegral_mul_const' _ _ hwb,
      lintegral_mul_left_adele (a₀ * a₀) (fun s => f (nU (b₀ + s) * mD (a₀ * a))),
      lintegral_add_left_eq_self (fun s => f (nU s * mD (a₀ * a))) b₀, hc, wt_mul]
    ring
  simp only [inner]
  exact lintegral_mul_left_eq_self
    (fun x : IdeleGroup F => ∫⁻ b, f (nU b * mD x) * M.wt x ∂(adeleMeasure F)) a₀
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private def upS {F : Type} [Field F] (ξ : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, ξ; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem upS_val {F : Type} [Field F] (ξ : F) : (upS ξ).1 = !![1, ξ; 0, 1] := rfl

private theorem ratS_upS {F : Type} [Field F] [NumberField F] (ξ : F) : ratS F (upS ξ) = nU (rt ξ) :=
  M.ratS_up ξ

private theorem specialLinear_upper_unipotent {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (h0 : g.1 1 0 = 0) (h1 : g.1 1 1 = 1) : g = upS (g.1 0 1) := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two, h0, h1] at hd
  have hd' : g.1 0 0 = 1 := by simpa using hd
  refine Subtype.ext ?_
  change g.1 = (upS (g.1 0 1)).1
  rw [upS_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, hd']

private theorem ratS_inj {F : Type} [Field F] [NumberField F] :
    Function.Injective (ratS F) := by
  intro a b h
  have hinj : Function.Injective (algebraMap F (A F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  refine Subtype.ext ?_
  ext i j
  apply hinj
  have h2 := congrArg (fun g : G1 F => g.1 i j) h
  simpa [M.val_ratS] using h2

private theorem row_up {F : Type} [Field F] (ξ : F) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (upS ξ * g).1 1 = g.1 1 := by
  ext j
  change ((upS ξ).1 * g.1) 1 j = _
  rw [upS_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.ConvolutionTheory.R2.M.rowCosets :
    ∀ (F : Type) [Field F] [NumberField F], (∃ σ, M.RowSec (F := F) σ) ∧ ∀ σ, M.RowSec (F := F) σ → ∀ γ : Gam F, ∃! p : {r : Fin 2 → F // r ≠ 0} × F, (γ : G1 F) = nU (rt p.2) * ratS F (σ p.1) := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have hex : ∀ r : {r : Fin 2 → F // r ≠ 0}, ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g.1 1 = r.1 := by
      rintro ⟨r, hr⟩
      by_cases hc : r 0 = 0
      · have hd : r 1 ≠ 0 := fun hd => hr (by ext i; fin_cases i <;> simp [hc, hd])
        refine ⟨⟨!![(r 1)⁻¹, 0; r 0, r 1], by simp [Matrix.det_fin_two, hd]⟩, ?_⟩
        ext i; fin_cases i <;> simp
      · refine ⟨⟨!![0, -(r 0)⁻¹; r 0, r 1], by simp [Matrix.det_fin_two, hc]⟩, ?_⟩
        ext i; fin_cases i <;> simp
    choose σ hσ using hex
    exact ⟨σ, hσ⟩
  · rintro σ hσ ⟨_, γ0, rfl⟩
    have hr : γ0.1 1 ≠ 0 := by
      intro h
      have hd := γ0.det_coe
      rw [Matrix.det_fin_two] at hd
      have h0 : γ0.1 1 0 = 0 := congrFun h 0
      have h1 : γ0.1 1 1 = 0 := congrFun h 1
      simp [h0, h1] at hd
    obtain ⟨r, hrdef⟩ : ∃ r : {r : Fin 2 → F // r ≠ 0}, r = ⟨γ0.1 1, hr⟩ := ⟨_, rfl⟩
    have hs : (σ r).1 1 = γ0.1 1 := by rw [hσ r, hrdef]
    have hs0 : (σ r).1 1 0 = γ0.1 1 0 := congrFun hs 0
    have hs1 : (σ r).1 1 1 = γ0.1 1 1 := congrFun hs 1
    have hdet : (σ r).1 0 0 * (σ r).1 1 1 - (σ r).1 0 1 * (σ r).1 1 0 = 1 := by
      have hd := (σ r).det_coe
      rwa [Matrix.det_fin_two] at hd
    have e0 : (γ0 * (σ r)⁻¹).1 1 0 = 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp [hs0, hs1]
      ring
    have e1 : (γ0 * (σ r)⁻¹).1 1 1 = 1 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp
      linear_combination hdet - (σ r).1 0 0 * hs1 + (σ r).1 0 1 * hs0
    obtain ⟨ξ, hξ⟩ : ∃ ξ : F, γ0 * (σ r)⁻¹ = upS ξ := ⟨_, specialLinear_upper_unipotent _ e0 e1⟩
    have hγ : γ0 = upS ξ * σ r := by
      rw [← hξ, inv_mul_cancel_right]
    refine ⟨(r, ξ), ?_, ?_⟩
    · show ratS F γ0 = nU (rt ξ) * ratS F (σ r)
      conv_lhs => rw [hγ]
      rw [map_mul, ratS_upS]
    · rintro ⟨r', ξ'⟩ heq
      have heq' : ratS F γ0 = nU (rt ξ') * ratS F (σ r') := heq
      rw [← ratS_upS, ← map_mul] at heq'
      have hγ' := ratS_inj heq'
      have hrr : r' = r := by
        refine Subtype.ext ?_
        rw [← hσ r', ← row_up ξ' (σ r'), ← hγ', hrdef]
      subst hrr
      have hU : upS ξ = upS ξ' := mul_right_cancel (hγ.symm.trans hγ')
      have hξξ : ξ = ξ' := by
        have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.1 0 1) hU
        simpa [upS_val] using h2
      rw [hξξ]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.iwDens :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F), ∃ ρ : Measure (IdeleGroup F × G1 F), SFinite ρ ∧ (∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ p, u (mD p.1 * p.2) ∂ρ = M.J0 M₀ u) ∧ ∀ u : IdeleGroup F × G1 F → ℂ, (Integrable u ρ ↔ Integrable (fun p => (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p) M₀.ν) ∧ ∫ p, u p ∂ρ = ∫ p, (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p ∂M₀.ν := by
  intro F _ _ M₀
  have hfm : Measurable (fun p : IdeleGroup F × G1 F => Real.toNNReal ((ab p.1)⁻¹ ^ 2)) :=
    (((M.continuous_ab.measurable.comp measurable_fst).inv).pow_const 2).real_toNNReal
  have hwm : Measurable (fun p : IdeleGroup F × G1 F => M.wt p.1) :=
    M.measurable_wt.comp measurable_fst
  have hsm : ∀ (u : IdeleGroup F × G1 F → ℂ) (p : IdeleGroup F × G1 F),
      Real.toNNReal ((ab p.1)⁻¹ ^ 2) • u p = (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p := by
    intro u p
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.real_smul]
  haveI : IsProbabilityMeasure M₀.κ := M₀.prob
  haveI : SFinite M₀.ν := by unfold Meas.ν; infer_instance
  refine ⟨M₀.ν.withDensity fun p => (Real.toNNReal ((ab p.1)⁻¹ ^ 2) : ℝ≥0∞), inferInstance, ?_, ?_⟩
  · intro u _
    have h := lintegral_withDensity_eq_lintegral_mul_non_measurable M₀.ν hwm
      (Eventually.of_forall fun p => ENNReal.ofReal_lt_top) (fun p => u (mD p.1 * p.2))
    exact h
  · intro u
    refine ⟨?_, ?_⟩
    · rw [integrable_withDensity_iff_integrable_smul hfm]
      simp only [hsm]
    · rw [integral_withDensity_eq_integral_smul hfm]
      simp only [hsm]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtA :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞) (c : ℝ≥0∞), Measurable β → (∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = c) → Measurable u → (∀ b g, u (nU b * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = c * M.J0 M₀ u := by
  intro F _ _ M₀ β u c hβ hc hu hinv
  haveI := M₀.prob
  have hm : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    ((M.continuous_mD.comp continuous_fst).mul continuous_snd).measurable
  have hJ : Measurable fun p : IdeleGroup F × G1 F => M.wt p.1 * u (mD p.1 * p.2) :=
    (M.measurable_wt.comp measurable_fst).mul (hu.comp hm)
  have hin : ∀ (a : IdeleGroup F) (k : G1 F),
      ∫⁻ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2) ∂(adeleMeasure F)
        = c * (M.wt a * u (mD a * k)) := by
    intro a k
    have h1 : ∀ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2)
        = (M.wt a * u (mD a * k)) * β (nU b * (mD a * k)) := fun b => by
      rw [mul_assoc (nU b), hinv, M.wt]; ring
    simp_rw [h1]
    have hb : Measurable fun b : A F => β (nU b * (mD a * k)) :=
      hβ.comp ((M.continuous_nU.mul continuous_const).measurable)
    rw [lintegral_const_mul _ hb, hc, mul_comm]
  have hk : Measurable fun k : G1 F => ∫⁻ a, M.wt a * u (mD a * k) ∂(ideleMeasure F) :=
    hJ.lintegral_prod_left'
  have hsec : ∀ k : G1 F, Measurable fun a : IdeleGroup F => M.wt a * u (mD a * k) :=
    fun k => M.measurable_wt.mul (hu.comp ((M.continuous_mD.mul continuous_const).measurable))
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable,
    ← lintegral_const_mul _ hk]
  refine lintegral_congr fun k => ?_
  rw [← lintegral_const_mul _ (hsec k)]
  exact lintegral_congr fun a => hin a k
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem mem_bor_iff {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g ∈ M.Bor F ↔ g 1 0 = 0 := by
  constructor
  · intro h
    exact h (show (id (0 : Fin 2)) < id (1 : Fin 2) by decide)
  · intro h i j hij
    have hij' : j < i := hij
    have hi : i = 1 := by omega
    have hj : j = 0 := by omega
    subst hi hj
    exact h

private theorem nm_val {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (b : A F) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [M.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperTriangular_diagonal_product {F : Type} [Field F] [NumberField F] (g : G1 F) (h : g 1 0 = 0) :
    g 0 0 * g 1 1 = 1 := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  have h' : g.1 1 0 = 0 := h
  rw [h', mul_zero, sub_zero] at hd
  exact hd

private def dg {F : Type} [Field F] [NumberField F] (g : M.Bor F) : IdeleGroup F :=
  ⟨g.1 0 0, g.1 1 1, upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2),
    (mul_comm _ _).trans (upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2))⟩

theorem UpperTheory.ConvolutionTheory.R2.M.borHomeo :
    ∀ (F : Type) [Field F] [NumberField F], IsClosed (M.Bor F : Set (G1 F)) ∧ ∃ e : IdeleGroup F × A F ≃ₜ M.Bor F, ∀ p, (e p : G1 F) = nU p.2 * mD p.1 := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have : (M.Bor F : Set (G1 F)) = {g | g 1 0 = 0} := Set.ext mem_bor_iff
    rw [this]
    exact isClosed_eq (M.continuous_entry 1 0) continuous_const
  · have hmem : ∀ p : IdeleGroup F × A F, nU p.2 * mD p.1 ∈ M.Bor F := fun p => by
      rw [mem_bor_iff]
      show (nU p.2 * mD p.1).1 1 0 = 0
      rw [nm_val]
      simp
    refine ⟨{ toFun := fun p => ⟨nU p.2 * mD p.1, hmem p⟩
              invFun := fun g => (dg g, g.1 0 1 * g.1 0 0)
              left_inv := ?_
              right_inv := ?_
              continuous_toFun := ?_
              continuous_invFun := ?_ }, fun p => rfl⟩
    · rintro ⟨a, b⟩
      have e00 : (nU b * mD a) 0 0 = (a : A F) := by
        show (nU b * mD a).1 0 0 = _
        rw [nm_val]; simp
      have e01 : (nU b * mD a) 0 1 = b * ((a⁻¹ : (A F)ˣ) : A F) := by
        show (nU b * mD a).1 0 1 = _
        rw [nm_val]; simp
      refine Prod.ext (Units.ext e00) ?_
      show (nU b * mD a) 0 1 * (nU b * mD a) 0 0 = b
      rw [e00, e01, mul_assoc, Units.inv_mul, mul_one]
    · rintro ⟨g, hg⟩
      have h10 := (mem_bor_iff g).1 hg
      have hd := upperTriangular_diagonal_product g h10
      refine Subtype.ext (Subtype.ext ?_)
      show (nU (g 0 1 * g 0 0) * mD (dg ⟨g, hg⟩)).1 = g.1
      rw [nm_val]
      have hinv : (((dg ⟨g, hg⟩)⁻¹ : (A F)ˣ) : A F) = g 1 1 := rfl
      have hval : ((dg ⟨g, hg⟩ : (A F)ˣ) : A F) = g 0 0 := rfl
      rw [hinv, hval]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · show g 0 1 * g 0 0 * g 1 1 = g 0 1
        rw [mul_assoc, hd, mul_one]
      · exact h10.symm
      · rfl
    · exact Continuous.subtype_mk
        ((M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)) _
    · have c : ∀ i j, Continuous fun g : M.Bor F => g.1 i j := fun i j =>
        (M.continuous_entry i j).comp continuous_subtype_val
      exact (Units.continuous_iff.2 ⟨c 0 0, c 1 1⟩).prodMk ((c 0 1).mul (c 0 0))
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.redDet :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (g : G1 F) (γ : GL (Fin 2) F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k : GL (Fin 2) (A F), AdelicGLn.diagonal F 2 γ * gl g = b * k → ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) F, ∃ b' ∈ Reduction.adelicBorel (K := F) (n := 2), gl (ratS F γ' * g) = b' * k ∧ b'.val 0 0 = b.val 0 0 ∧ Reduction.adeleAbs (b'.val 1 1) = Reduction.adeleAbs (b.val 1 1) := by
  intro F _ _ g γ b hb k h
  set d : Fˣ := Matrix.GeneralLinearGroup.det γ with hd
  have hdet : γ.val.det = (d : F) := rfl
  set t : (A F)ˣ := (IdeleGroup.diagonal F d)⁻¹ with ht
  have htv : ((t : (A F)ˣ) : A F) = algebraMap F (A F) ((d⁻¹ : Fˣ) : F) := by
    simp [ht, IdeleGroup.diagonal, ← map_inv]
  let γ' : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1, 0; 0, ((d⁻¹ : Fˣ) : F)] * γ.val, by
      rw [Matrix.det_mul, hdet, Matrix.det_fin_two_of]; simp⟩
  have hg : gl (ratS F γ') = dM t * AdelicGLn.diagonal F 2 γ := by
    refine Units.ext ?_
    rw [Units.val_mul, val_gl, val_ratS]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ', dM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, htv, map_mul]
  obtain ⟨u, hu⟩ := Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1
  have hlow : b.val 1 0 = 0 := Reduction.mem_adelicBorel.1 hb (by decide)
  refine ⟨γ', dM t * b, ?_, ?_, ?_, ?_⟩
  · refine mul_mem (Reduction.mem_adelicBorel.2 ?_) hb
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (simp [dM]; done) | (simp at hij)
  · have hm : gl (ratS F γ' * g) = gl (ratS F γ') * gl g := map_mul _ _ _
    rw [hm, hg, mul_assoc, h, mul_assoc]
  · simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  · have e : (dM t * b).val 1 1 = ((t * u : (A F)ˣ) : A F) := by
      simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hu]
    rw [e, ← hu, Reduction.adeleAbs_units, Reduction.adeleAbs_units]
    have := ab_mul t u
    have h1 : ab t = 1 := by rw [ht, ab_inv, ab_diag, inv_one]
    rw [h1, one_mul] at this
    exact this
end
