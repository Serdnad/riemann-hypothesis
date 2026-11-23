module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle051
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

theorem sq_intervalIntegral_unit_le (h : ℝ → ℝ) (hc : Continuous h) :
    (∫ s in (0:ℝ)..1, h s) ^ 2 ≤ ∫ s in (0:ℝ)..1, h s ^ 2 := by
  set c := ∫ s in (0:ℝ)..1, h s with hcdef
  have hnn : 0 ≤ ∫ s in (0:ℝ)..1, (h s - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)
  have hexp : ∫ s in (0:ℝ)..1, (h s - c) ^ 2 = (∫ s in (0:ℝ)..1, h s ^ 2) - 2 * c * c + c ^ 2 := by
    have e1 : (fun s => (h s - c) ^ 2) = fun s => (h s ^ 2 - (2 * c) * h s) + c ^ 2 := by
      funext s; ring
    rw [e1, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    · simp
      exact Or.inl rfl
    · exact (hc.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hc).intervalIntegrable _ _
    · exact ((hc.pow 2).sub (continuous_const.mul hc)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  nlinarith

theorem norm_sub_expK_sq_le : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ Y : Mx n, inK ε Y → ∫ x, ‖φ x - φ (x * expK ε Y 1)‖ ^ 2 ∂(muK ε) ≤ ∫ x, ‖rder ε [Y] φ x‖ ^ 2 ∂(muK ε) := by
  intro n ε d φ hφ Y hY
  obtain ⟨hRmem, hRder⟩ := rder_mem_and_hasDerivAt ε d φ hφ Y hY
  set R := rder ε [Y] φ with hRdef
  have hRc : Continuous R := continuous_of_mem hRmem
  have hφc : Continuous φ := continuous_of_mem hφ
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hEG := group_exponential_facts n ε Y hY.1
  have hEK := hEG.2.2.2 hY
  let e : ℝ → KG ε := fun t => expK ε Y t
  have he_add : ∀ s t, e (s + t) = e s * e t := fun s t => by
    apply Subtype.ext
    show ((expK ε Y (s + t) : KG ε) : UJ ε) = (expK ε Y s : UJ ε) * (expK ε Y t : UJ ε)
    rw [hEK.1, hEK.1, hEK.1]
    exact hEG.2.1 s t
  have he0 : e 0 = 1 := by
    apply Subtype.ext
    show ((expK ε Y 0 : KG ε) : UJ ε) = 1
    rw [hEK.1]; exact hEG.1
  have he_cont : Continuous e := hEK.2
  have hder' : ∀ k s, HasDerivAt (fun t => φ (k * e t)) (R (k * e s)) s := by
    intro k s
    have h1 := hRder (k * e s)
    have h2 : HasDerivAt (fun t => φ (k * e s * expK ε Y (t - s))) (R (k * e s)) s :=
      HasDerivAt.comp_sub_const (f := fun t => φ (k * e s * expK ε Y t)) s s (by rw [sub_self]; exact h1)
    have hfun : (fun t => φ (k * e s * expK ε Y (t - s))) = fun t => φ (k * e t) := by
      funext t
      show φ (k * e s * e (t - s)) = φ (k * e t)
      rw [mul_assoc, ← he_add, add_sub_cancel]
    rw [hfun] at h2
    exact h2
  have hgc : ∀ k, Continuous (fun s => R (k * e s)) := fun k =>
    hRc.comp (continuous_const.mul he_cont)
  have hftc : ∀ k, ∫ s in (0:ℝ)..1, R (k * e s) = φ (k * e 1) - φ k := by
    intro k
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder' k s)
      ((hgc k).intervalIntegrable 0 1), he0, mul_one]
  have hpt : ∀ k, ‖φ k - φ (k * e 1)‖ ^ 2 ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ ^ 2 := by
    intro k
    have h1 : ‖φ k - φ (k * e 1)‖ ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ := by
      rw [norm_sub_rev, ← hftc k]
      exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    have h2 := sq_intervalIntegral_unit_le (fun s => ‖R (k * e s)‖) ((hgc k).norm)
    calc ‖φ k - φ (k * e 1)‖ ^ 2 ≤ (∫ s in (0:ℝ)..1, ‖R (k * e s)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hRsc : Continuous (fun x => ‖R x‖ ^ 2) := hRc.norm.pow 2
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hRsc.continuousOn
  have hcont2 : Continuous (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2) :=
    hRsc.comp (continuous_fst.mul (he_cont.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2)
      ((muK ε).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      rw [isFiniteMeasure_restrict]; simp
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
    have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
      (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    haveI : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (KG ε × ℝ) := inferInstance
    exact Integrable.of_bound hcont2.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _ (Set.mem_univ _))
  have hswap := integral_integral_swap hI
  have hrhs : ∫ x, (∫ s in (0:ℝ)..1, ‖R (x * e s)‖ ^ 2) ∂(muK ε) = ∫ x, ‖R x‖ ^ 2 ∂(muK ε) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    rw [hswap]
    simp_rw [integral_mul_right_eq_self (μ := muK ε) (fun x => ‖R x‖ ^ 2)]
    rw [setIntegral_const]
    simp
  rw [← hrhs]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x => by positivity
  · have := hI.integral_prod_left
    simp only [Function.uncurry_apply_pair] at this
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [intervalIntegral.integral_of_le zero_le_one]
  · exact Filter.Eventually.of_forall fun x => hpt x

end GlobalTheory.KFourier

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

theorem inK_zero' (ε : Fin n → Bool) : inK ε (0 : Mx n) := by
  refine ⟨?_, ?_⟩
  · show (0 : Mx n)ᴴ * Jm ε + Jm ε * 0 = 0
    simp
  · simp

theorem inK_add'' {ε : Fin n → Bool} {X Y : Mx n} (hX : inK ε X) (hY : inK ε Y) : inK ε (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · have h1' : Xᴴ * Jm ε + Jm ε * X = 0 := h1
    have h3' : Yᴴ * Jm ε + Jm ε * Y = 0 := h3
    show (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
        = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
      _ = 0 := by rw [h1', h3', add_zero]
  · rw [Matrix.add_mul, Matrix.mul_add, h2, h4]

theorem inK_sum_real {ε : Fin n → Bool} {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    inK ε (∑ j, (c j : ℂ) • X j) := by
  classical
  refine Finset.sum_induction _ (inK ε) (fun _ _ ha hb => inK_add'' ha hb) (inK_zero' ε) ?_
  intro j _
  exact inK_smul_real ε (hX j) (c j)

def entryDer (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := ∑ l, toMK k a l * Y l b
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Complex.real_smul]
    ring

def entryDerStar (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := star (∑ l, toMK k a l * Y l b)
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, star_add]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
    simp only [star_sum, Finset.mul_sum, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem hasDerivAt_coord_lin {ε : Fin n → Bool} (c : Fin n × Fin n × Bool) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε Y t)) (D k Y) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ (k : KG ε) (Y : Mx n), inK ε Y → HasDerivAt (fun t : ℝ => (toMK (k * expK ε Y t)) a b)
      (∑ l, toMK k a l * Y l b) 0 := by
    intro k Y hY
    have e : (fun t : ℝ => (toMK (k * expK ε Y t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • Y)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hY, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real Y l b).const_mul _
  cases f
  · refine ⟨fun k => entryDerStar ε k a b, fun k Y hY => ?_⟩
    have h := (hent k Y hY).star
    have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε Y t)) =
        fun t => star ((toMK (k * expK ε Y t)) a b) := by
      funext t; simp [coord]
    rw [e1]; exact h
  · refine ⟨fun k => entryDer ε k a b, fun k Y hY => ?_⟩
    have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε Y t)) =
        fun t => (toMK (k * expK ε Y t)) a b := by
      funext t; simp [coord]
    rw [e1]; exact hent k Y hY

theorem hasDerivAt_mono_lin {ε : Fin n → Bool} (s : List (Fin n × Fin n × Bool)) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε Y t)) (D k Y) 0 := by
  induction s with
  | nil =>
    refine ⟨0, fun k Y _ => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    obtain ⟨Dc, hc⟩ := hasDerivAt_coord_lin (ε := ε) c
    obtain ⟨Ds, hs⟩ := ih
    refine ⟨fun k => mono ε s k • Dc k + coord ε c k • Ds k, fun k Y hY => ?_⟩
    have h := (hc k Y hY).mul (hs k Y hY)
    have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε Y t)) =
        fun t => coord ε c (k * expK ε Y t) * mono ε s (k * expK ε Y t) := by
      funext t; simp [mono]
    rw [e]
    rw [coord_mul_expK_zero hY, mono_mul_expK_zero hY] at h
    refine h.congr_deriv ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring

theorem hasDerivAt_lin_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => φ (k * expK ε Y t)) (D k Y) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, -, rfl⟩ := hx
    exact hasDerivAt_mono_lin s
  | zero =>
    exact ⟨0, fun k Y _ => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, d₁⟩ := hx
    obtain ⟨D₂, d₂⟩ := hy
    exact ⟨D₁ + D₂, fun k Y hY => (d₁ k Y hY).add (d₂ k Y hY)⟩
  | smul a x _ hx =>
    obtain ⟨D, dD⟩ := hx
    exact ⟨a • D, fun k Y hY => by simpa using (dD k Y hY).const_mul a⟩

theorem rder_real_linear {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    rder ε [∑ j, (c j : ℂ) • X j] φ = ∑ j, (c j : ℂ) • rder ε [X j] φ := by
  obtain ⟨D, hD⟩ := hasDerivAt_lin_of_mem hφ
  have hr : ∀ (Y : Mx n), inK ε Y → ∀ k, rder ε [Y] φ k = D k Y := by
    intro Y hY k
    rw [rder_cons, rder_nil]
    exact (hD k Y hY).deriv
  funext k
  rw [hr _ (inK_sum_real X c hX) k, Finset.sum_apply]
  have e : (∑ j, (c j : ℂ) • X j) = ∑ j, c j • X j :=
    Finset.sum_congr rfl fun j _ => Complex.coe_smul (c j) (X j)

  rw [e, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, hr _ (hX j) k, Complex.real_smul, smul_eq_mul]

end GlobalTheory.KFourier

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

variable {n : ℕ}

theorem continuous_integral_paramK {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : KG ε → KG ε → E} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => ∫ k, F x k ∂(muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  have h := continuous_parametric_integral_of_continuous (μ := muK ε) hF (isCompact_univ (X := KG ε))
  simpa only [Measure.restrict_univ] using h

theorem integrable_prod_of_continuousK {ε : Fin n → Bool} {F : KG ε × KG ε → ℂ} (hF : Continuous F) :
    Integrable F ((muK ε).prod (muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem norm_integral_star_mul_le_sqrtK {ε : Fin n → Bool} {f g : KG ε → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    ‖∫ x, star (f x) * g x ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(muK ε)) := by
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re1 : ∀ h : KG ε → ℂ, (∫ x, star (h x) * h x ∂(muK ε)).re = ∫ x, ‖h x‖ ^ 2 ∂(muK ε) := by
    intro h; simp_rw [hsq]; rw [integral_complex_ofReal, Complex.ofReal_re]
  have H := GlobalTheory.norm_integral_star_mul_sq_le (muK ε) f g hf.aestronglyMeasurable hg.aestronglyMeasurable
    (integrable_of_continuousK (by fun_prop)) (integrable_of_continuousK (by fun_prop))
  rw [re1 f, re1 g] at H
  rw [← Real.sqrt_mul (integral_nonneg fun x => by positivity)]
  have := Real.abs_le_sqrt H
  rwa [abs_of_nonneg (norm_nonneg _)] at this



theorem sqrt_integral_normSq_le_integral_kernel_mul_translate :
    ∀ {n : ℕ} (ε : Fin n → Bool) (p : KG ε → ℂ) (κ : KG ε → ℝ), Continuous p → Continuous κ →
      (∀ k, 0 ≤ κ k) → ∫ k, κ k ∂(muK ε) = 1 →
      (∀ k, ∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε) = 0) →
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) ≤
        ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
  intro n ε p κ hp hκ hκ0 hκ1 horth
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have hA0 : 0 ≤ ∫ x, ‖p x‖ ^ 2 ∂(muK ε) := integral_nonneg fun x => by positivity
  have hAc : ∫ x, star (p x) * p x ∂(muK ε) = ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
    simp_rw [hsq]; exact integral_complex_ofReal
  have htr : ∀ x, ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) = ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) := by
    intro x
    have := integral_mul_left_eq_self (μ := muK ε) (fun k => (κ (x⁻¹ * k) : ℂ) * p k) x
    simpa only [inv_mul_cancel_left] using this
  have hzero : ∫ x, star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) ∂(muK ε) = 0 := by
    simp_rw [htr]
    have e1 : ∀ x, star (p x) * ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) =
        ∫ k, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) := fun x => (integral_const_mul _ _).symm
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK (F := fun z : KG ε × KG ε => star (p z.1) * ((κ (z.1⁻¹ * z.2) : ℂ) * p z.2))
        (by fun_prop)
    rw [integral_integral_swap hint]
    have e2 : ∀ k, ∫ x, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) =
        (∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε)) * p k := by
      intro k; rw [← integral_mul_const]; congr 1; funext x; ring
    simp_rw [e2, horth, zero_mul, integral_zero]
  have hκ1c : ∫ k, (κ k : ℂ) ∂(muK ε) = 1 := by rw [integral_complex_ofReal, hκ1, Complex.ofReal_one]
  have hinner : ∀ x, ∫ k, (κ k : ℂ) * (p x - p (x * k)) ∂(muK ε) =
      p x - ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
    intro x
    have i1 : Integrable (fun k => (κ k : ℂ) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have i2 : Integrable (fun k => (κ k : ℂ) * p (x * k)) (muK ε) := integrable_of_continuousK (by fun_prop)
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hκ1c, one_mul]
  have hcontT : Continuous (fun x => ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun x k => (κ k : ℂ) * p (x * k)) (by fun_prop)
  have hkey : ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) =
      ∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε) := by
    have e1 : ∀ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) =
        ∫ x, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) := by
      intro k; rw [← integral_const_mul]; congr 1; funext x; ring
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ k : ℂ) * (p x - p (x * k))))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK
        (F := fun z : KG ε × KG ε => star (p z.1) * ((κ z.2 : ℂ) * (p z.1 - p (z.1 * z.2)))) (by fun_prop)
    rw [← integral_integral_swap hint]
    have e2 : ∀ x, ∫ k, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) =
        star (p x) * p x - star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
      intro x; rw [integral_const_mul, hinner, mul_sub]
    simp_rw [e2]
    have iA : Integrable (fun x => star (p x) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have iB : Integrable (fun x => star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) (muK ε) :=
      integrable_of_continuousK ((continuous_star.comp hp).mul hcontT)
    rw [integral_sub iA iB, hzero, sub_zero, hAc]
  have hCS : ∀ k, ‖∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    fun k => norm_integral_star_mul_le_sqrtK (g := fun x => p x - p (x * k)) hp (by fun_prop)
  have hIc : Continuous (fun k => ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => star (p x) * (p x - p (x * k))) (by fun_prop)
  have hDc : Continuous (fun k => ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => ‖p x - p (x * k)‖ ^ 2) (by fun_prop)
  have hmain : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) ≤ Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
      ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
    have e : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) =
        (∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)).re := by
      rw [← hkey, Complex.ofReal_re]
    have hl : Continuous (fun k => ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖) := by
      fun_prop
    have hr : Continuous (fun k => κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
        Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)))) := by fun_prop
    calc ∫ x, ‖p x‖ ^ 2 ∂(muK ε)
        ≤ ‖∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)‖ := by
          rw [e]; exact Complex.re_le_norm _
      _ ≤ ∫ k, ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ∂(muK ε) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ k, κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
            Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε))) ∂(muK ε) := by
          refine integral_mono (hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (hr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun k => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 k)]
          exact mul_le_mul_of_nonneg_left (hCS k) (hκ0 k)
      _ = _ := by rw [← integral_const_mul]; congr 1; funext k; ring
  rcases hA0.lt_or_eq with hpos | hz
  · have hs : 0 < Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) := Real.sqrt_pos.2 hpos
    refine le_of_mul_le_mul_left ?_ hs
    rw [Real.mul_self_sqrt hA0]
    exact hmain
  · rw [← hz, Real.sqrt_zero]
    exact integral_nonneg fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _)

end GlobalTheory.KFourier

end
end
