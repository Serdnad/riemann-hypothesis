module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle021
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelCount

theorem cnt_ne_top (X : Ctx) (Ω : Set X.G) (hΩ : IsCompact Ω) (x : X.G) : cnt X.Γ Ω x ≠ ⊤ := by
  have hC : IsCompact ((fun z => x * z * x⁻¹) '' Ω) :=
    hΩ.image (by fun_prop)
  have hfin := X.proper _ hC
  have hsupp : (Function.support fun γ : X.Γ =>
      Ω.indicator (1 : X.G → ℝ≥0∞) (x⁻¹ * (γ : X.G) * x)) ⊆ (hfin.toFinset : Set X.Γ) := by
    intro γ hγ
    have hmem : x⁻¹ * (γ : X.G) * x ∈ Ω := by
      by_contra h
      exact hγ (Set.indicator_of_notMem h _)
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    exact ⟨_, hmem, by group⟩
  unfold cnt
  rw [tsum_eq_sum (s := hfin.toFinset) (fun γ hγ => by
    by_contra h
    exact hγ (by simpa using hsupp h))]
  refine (ENNReal.sum_lt_top.2 fun γ _ => ?_).ne
  refine lt_of_le_of_lt (Set.indicator_le_self' (fun _ _ => zero_le) _) ?_
  simp

theorem cnt_mul_left (X : Ctx) (Ω : Set X.G) (γ : X.G) (hγ : γ ∈ X.Γ) (x : X.G) :
    cnt X.Γ Ω (γ * x) = cnt X.Γ Ω x := by
  unfold cnt
  rw [← Equiv.tsum_eq (MulAut.conj (⟨γ, hγ⟩ : X.Γ)).toEquiv]
  refine tsum_congr fun δ => ?_
  have : (γ * x)⁻¹ * (((MulAut.conj (⟨γ, hγ⟩ : X.Γ)).toEquiv δ : X.Γ) : X.G) * (γ * x)
      = x⁻¹ * (δ : X.G) * x := by
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, Subgroup.coe_mul,
      InvMemClass.coe_inv]
    group
  rw [this]

theorem cnt_mono (X : Ctx) {Ω Ω' : Set X.G} (h : Ω ⊆ Ω') (x : X.G) :
    cnt X.Γ Ω x ≤ cnt X.Γ Ω' x :=
  ENNReal.tsum_le_tsum fun _ => Set.indicator_le_indicator_of_subset h (fun _ => zero_le) _

theorem enorm_le_indicator {G : Type} [TopologicalSpace G] (φ : G → ℂ) (B : ℝ)
    (hB : ∀ z, ‖φ z‖ ≤ B) (z : G) :
    ‖φ z‖ₑ ≤ ENNReal.ofReal B * (tsupport φ).indicator (1 : G → ℝ≥0∞) z := by
  by_cases hz : z ∈ tsupport φ
  · rw [Set.indicator_of_mem hz, Pi.one_apply, mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB z)
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp

theorem cntBasic_of_kerBasic (h : KerBasic) : CntBasic := by
  intro X
  refine ⟨fun Ω hΩ x => cnt_ne_top X Ω hΩ x, fun Ω γ hγ x => cnt_mul_left X Ω γ hγ x,
    fun Ω Ω' hs x => cnt_mono X hs x, fun φ B hφ hB x => ?_⟩
  obtain ⟨-, -, -, -, -, hk⟩ := h X φ hφ
  refine (hk x x).trans ?_
  unfold cnt
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun γ => enorm_le_indicator φ B hB _

end GlobalTheory.CompanionTheory.KernelCount

end
end

section

noncomputable section

open MeasureTheory
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.ConvTest

variable (X : Ctx)

theorem support_cv_subset (φ ψ : X.G → ℂ) :
    Function.support (cv X.μ φ ψ) ⊆ tsupport φ * tsupport ψ := by
  intro y hy
  by_contra hmem
  apply hy
  have hz : ∀ z : X.G, φ z * ψ (z⁻¹ * y) = 0 := by
    intro z
    by_contra hne
    have h1 : φ z ≠ 0 := left_ne_zero_of_mul hne
    have h2 : ψ (z⁻¹ * y) ≠ 0 := right_ne_zero_of_mul hne
    apply hmem
    refine Set.mem_mul.2 ⟨z, subset_tsupport _ h1, z⁻¹ * y, subset_tsupport _ h2, ?_⟩
    group
  simp [cv, hz]

theorem continuous_cv {φ ψ : X.G → ℂ} (hφ : Tst φ) (hψ : Tst ψ) : Continuous (cv X.μ φ ψ) := by
  have hK : IsCompact (tsupport φ) := hφ.2
  have hEq : cv X.μ φ ψ = fun y => ∫ z in tsupport φ, φ z * ψ (z⁻¹ * y) ∂X.μ := by
    funext y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hEq]
  refine continuous_parametric_integral_of_continuous
    (f := fun (y z : X.G) => φ z * ψ (z⁻¹ * y)) ?_ hK
  have h1 : Continuous fun p : X.G × X.G => φ p.2 := hφ.1.comp continuous_snd
  have h2 : Continuous fun p : X.G × X.G => ψ (p.2⁻¹ * p.1) :=
    hψ.1.comp (continuous_snd.inv.mul continuous_fst)
  exact h1.mul h2

theorem integrable_reflect {ψ : X.G → ℂ} (hψ : Tst ψ) (y : X.G) :
    Integrable (fun z => ‖ψ (z⁻¹ * y)‖) X.μ := by
  have hc : Continuous fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.1.comp (continuous_inv.mul continuous_const)
  have hs : HasCompactSupport fun z : X.G => ψ (z⁻¹ * y) :=
    hψ.2.comp_homeomorph ((Homeomorph.inv X.G).trans (Homeomorph.mulRight y))
  exact (hc.integrable_of_hasCompactSupport hs).norm

theorem norm_cv_le {φ ψ : X.G → ℂ} (hψ : Tst ψ) (B : ℝ) (hB : ∀ z, ‖φ z‖ ≤ B) (y : X.G) :
    ‖cv X.μ φ ψ y‖ ≤ B * ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  have hshift : ∫ z, ‖ψ (z⁻¹ * y)‖ ∂X.μ = ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
    have h := integral_mul_left_eq_self (μ := X.μ) (fun z => ‖ψ z⁻¹‖) y⁻¹
    simpa [mul_inv_rev] using h
  have hle : ‖cv X.μ φ ψ y‖ ≤ ∫ z, B * ‖ψ (z⁻¹ * y)‖ ∂X.μ := by
    refine norm_integral_le_of_norm_le ((integrable_reflect X hψ y).const_mul B) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
  rw [integral_const_mul, hshift] at hle
  exact hle

theorem cvTest : CvTest := by
  intro X φ ψ hφ hψ
  have hsupp := support_cv_subset X φ ψ
  refine ⟨⟨continuous_cv X hφ hψ, ?_⟩, hsupp, fun B hB y => norm_cv_le X hψ B hB y⟩
  have hK : IsCompact (tsupport φ * tsupport ψ) := IsCompact.mul hφ.2 hψ.2
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  exact hy (hsupp hne)

end GlobalTheory.CompanionTheory.ConvTest

end
end

section

noncomputable section

open MeasureTheory
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem colOp : KerBasic → CvTest → KernelL2RowsColumns → KerMul → ColOp := by
  intro hB hC hL hM X ι _ ψ hψ
  classical
  refine ⟨?_, ?_⟩
  · intro y j
    have hm : MemLp (fun x => ker X.Γ ψ x y) 2 X.ν := (hL X ψ hψ).1 y
    refine ⟨WithLp.toLp 2 (Pi.single j (hm.toLp _)), ?_, ?_⟩
    · have e : (WithLp.toLp 2 (Pi.single j (hm.toLp _)) : X.Hs ι) j = hm.toLp _ := by
        simp
      rw [e]
      exact hm.coeFn_toLp
    · intro l hl
      ext1
      simp [Pi.single_eq_of_ne hl]
  · intro Φ T hΦ hT y j u hu
    have key : ∀ i, (T u i : X.G → ℂ) =ᵐ[X.ν] fun x => ker X.Γ (cv X.μ (Φ i j) ψ) x y := by
      intro i
      filter_upwards [hT u i] with x hx
      rw [hx, Finset.sum_eq_single j]
      · rw [← hM X (Φ i j) ψ (hΦ i j) hψ x y]
        apply integral_congr_ae
        filter_upwards [hu.1] with z hz
        rw [hz]
      · intro l _ hl
        have h0 : (u l : X.G → ℂ) =ᵐ[X.ν] 0 := by
          rw [hu.2 l hl]
          exact Lp.coeFn_zero _ _ _
        have : (fun z => ker X.Γ (Φ i l) x z * (u l : X.G → ℂ) z) =ᵐ[X.ν] fun _ => 0 := by
          filter_upwards [h0] with z hz
          rw [hz]
          simp
        rw [integral_congr_ae this]
        simp
      · intro h
        exact absurd (Finset.mem_univ j) h
    refine ⟨key, ?_⟩
    intro x i v hv
    have hc := hC X (Φ i j) ψ (hΦ i j) hψ
    have ha := (hB X ψ hψ).2.2.2.1
    have hadj := (hB X ψ hψ).2.2.2.2.1
    rw [PiLp.inner_apply, Finset.sum_eq_single i]
    · rw [L2.inner_def, ← hM X (adj ψ) (cv X.μ (Φ i j) ψ) ha hc.1 x y]
      apply integral_congr_ae
      filter_upwards [hv.1, key i] with z hz1 hz2
      rw [hz1, hz2, RCLike.inner_apply, hadj x z, mul_comm]
    · intro l _ hl
      rw [hv.2 l hl]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h

end GlobalTheory.CompanionTheory.KernelColumns

end
end

section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.SchurKernel

theorem lintegral_enorm_rpow_two_ne_top {α : Type} [MeasurableSpace α] {ν : Measure α} {g : α → ℂ}
    (hg : MemLp g 2 ν) : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num) (by norm_num)
    hg.eLpNorm_lt_top
  simpa using h.ne

theorem schurInt_of_schurL : SchurL → SchurInt := by
  intro hS α _ ν _ k A hk hA hrow hcol g f hg hf
  have hkm : AEStronglyMeasurable (fun p : α × α => k p.1 p.2) (ν.prod ν) :=
    hk.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun p : α × α => g p.1) (ν.prod ν) := hg.aestronglyMeasurable.comp_fst
  have hfm : AEStronglyMeasurable (fun p : α × α => f p.2) (ν.prod ν) := hf.aestronglyMeasurable.comp_snd
  have hm : AEStronglyMeasurable (fun p : α × α => g p.1 * k p.1 p.2 * f p.2) (ν.prod ν) :=
    (hgm.mul hkm).mul hfm
  refine ⟨hm, ?_⟩
  set K : α → α → ℝ≥0∞ := fun x y => ‖k x y‖ₑ with hK
  have hKm : Measurable (Function.uncurry K) := hk.enorm
  have hFm : AEMeasurable (fun y => ‖f y‖ₑ) ν := hf.aestronglyMeasurable.aemeasurable.enorm
  set h : α → ℝ≥0∞ := fun x => ∫⁻ y, K x y * ‖f y‖ₑ ∂ν with hh
  have hprod : AEMeasurable (fun p : α × α => K p.1 p.2 * ‖f p.2‖ₑ) (ν.prod ν) :=
    hKm.aemeasurable.mul hfm.enorm
  have hhm : AEMeasurable h ν := hprod.lintegral_prod_right'
  have hsch : ∫⁻ x, h x ^ 2 ∂ν ≤ A ^ 2 * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν :=
    hS α ν K A (fun y => ‖f y‖ₑ) hKm hFm hrow hcol
  have heq : ∫⁻ p, ‖g p.1 * k p.1 p.2 * f p.2‖ₑ ∂(ν.prod ν) = ∫⁻ x, ‖g x‖ₑ * h x ∂ν := by
    rw [lintegral_prod _ hm.enorm]
    refine lintegral_congr fun x => ?_
    simp only [hh, hK]
    rw [← lintegral_const_mul' _ _ enorm_ne_top]
    refine lintegral_congr fun y => ?_
    simp only [enorm_mul, mul_assoc]
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (Real.HolderConjugate.two_two)
    hg.aestronglyMeasurable.aemeasurable.enorm hhm
  have hG : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := lintegral_enorm_rpow_two_ne_top hg
  have hF : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν ≠ ⊤ := lintegral_enorm_rpow_two_ne_top hf
  have hH : ∫⁻ x, h x ^ (2 : ℝ) ∂ν ≠ ⊤ := by
    simp only [ENNReal.rpow_two] at hF ⊢
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hA) hF) hsch
  rw [HasFiniteIntegral, heq]
  refine lt_of_le_of_lt hhold (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hG
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hH

end GlobalTheory.CompanionTheory.SchurKernel
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Schur

open PositivityTheory.Rg.BcB.E1

variable {α : Type} [MeasurableSpace α] {ν : Measure α}

theorem eLpNorm_two_sq (f : α → ℂ) : eLpNorm' f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  simpa [ENNReal.rpow_ofNat] using
    (lintegral_rpow_eNorm_eq_rpow_eLpNorm' (f := f) (μ := ν) (q := 2) (by norm_num)).symm

theorem schur_memLp (hS : SchurL) [SFinite ν] (k : α → α → ℂ) (A : ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) (hA : A ≠ ⊤)
    (hr : ∀ x, ∫⁻ y, ‖k x y‖ₑ ∂ν ≤ A) (hc : ∀ y, ∫⁻ x, ‖k x y‖ₑ ∂ν ≤ A)
    (g : α → ℂ) (hg : MemLp g 2 ν) :
    MemLp (fun x => ∫ y, k x y * g y ∂ν) 2 ν ∧
      eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν ∧
      ∀ᵐ x ∂ν, Integrable (fun y => k x y * g y) ν := by
  have norm_sq (f : α → ℂ) (hf : AEStronglyMeasurable f ν) :
      eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
    simpa [ENNReal.rpow_ofNat] using eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hf
  have hkK : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.eNorm
  have hgSm := hg.aestronglyMeasurable
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) ν := hgSm.eNorm
  have key := hS α ν (fun x y => ‖k x y‖ₑ) A (fun y => ‖g y‖ₑ) hkK hgm hr hc
  have hgfin : eLpNorm g 2 ν ≠ ⊤ := hg.ne
  have hsq : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν = eLpNorm g 2 ν ^ 2 := (norm_sq g hgSm).symm
  have hbound : ∫⁻ x, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂ν ≤ (A * eLpNorm g 2 ν) ^ 2 := by
    rw [mul_pow, ← hsq]; exact key
  have hfin : (A * eLpNorm g 2 ν) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top hA hgfin)
  have hprod : AEStronglyMeasurable (fun p : α × α => k p.1 p.2 * g p.2) (ν.prod ν) :=
    hk.stronglyMeasurable.aestronglyMeasurable.mul hgSm.comp_snd
  have hSm : AEStronglyMeasurable (fun x => ∫ y, k x y * g y ∂ν) ν :=
    hprod.integral_prod_right'
  have hhm : AEMeasurable (fun x => ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ν := by
    have : AEMeasurable (fun p : α × α => ‖k p.1 p.2‖ₑ * ‖g p.2‖ₑ) (ν.prod ν) := by
      simpa [eNorm_mul] using hprod.eNorm
    exact this.lintegral_prod_right'
  have hle : eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν := by
    refine (ENNReal.pow_right_strictMono two_ne_zero).le_iff_le.1 ?_
    rw [norm_sq _ hSm]
    refine le_trans (lintegral_mono fun x => ?_) hbound
    refine pow_le_pow_left' ?_ 2
    refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
    simp [eNorm_mul]
  refine ⟨hle.trans_lt (ENNReal.mul_ne_top hA hgfin).lt_top, hle, ?_⟩
  have hae : ∀ᵐ x ∂ν, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 < ⊤ :=
    ae_lt_top' (hhm.pow_const 2) (ne_top_of_le_ne_top hfin hbound)
  filter_upwards [hae] with x hx
  have hxf : ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hcon => ?_
    simp [hcon] at hx
  have hkx : Measurable (k x) := hk.of_uncurry_left
  refine ⟨hkx.aestronglyMeasurable.mul hgSm, ?_⟩
  simpa [HasFiniteIntegral, eNorm_mul] using hxf

theorem schurOp_of_schurL (hS : SchurL) : SchurOp := by
  intro α _ ν _ k A hk hA hr hc
  have H := fun f : Lp ℂ 2 ν => schur_memLp hS k A hk hA hr hc (f : α → ℂ) (Lp.memLp f)
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f => (H f).1.toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        have h1 := (H (f + g)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h3 := (H g).1.coeFn_toLp
        have h4 := Lp.coeFn_add ((H f).1.toLp _) ((H g).1.toLp _)
        filter_upwards [h1, h2, h3, h4, (H f).2.2, (H g).2.2] with x e1 e2 e3 e4 i1 i2
        rw [e1, e4, Pi.add_apply, e2, e3, ← integral_add i1 i2]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        have h1 := (H (c • f)).1.coeFn_toLp
        have h2 := (H f).1.coeFn_toLp
        have h4 := Lp.coeFn_smul c ((H f).1.toLp _)
        filter_upwards [h1, h2, h4] with x e1 e2 e4
        rw [e1, RingHom.id_apply, e4, Pi.smul_apply, e2, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul]
        ring }
  refine ⟨L.mkContinuous A.toReal ?_, fun f => (H f).1.coeFn_toLp⟩
  intro f
  change ‖(H f).1.toLp _‖ ≤ A.toReal * ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.memLp f).ne) (H f).2.1

end GlobalTheory.CompanionTheory.Schur

end
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OpEx

open PositivityTheory.Rg.BcB.E1

theorem coeFn_sum_ae {α : Type} [MeasurableSpace α] {ν : Measure α} {ι : Type} (s : Finset ι)
    (g : ι → Lp ℂ 2 ν) :
    ((∑ j ∈ s, g j : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] fun x => ∑ j ∈ s, (g j : α → ℂ) x :=
  _root_.UpperTheory.Reformulated.B.Yxa1.main s g

theorem opExA : KerBasic → RowInt → SchurOp → OpExA := by
  intro hK hR hS X ι _ Φ hΦ
  classical
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hex : ∀ i j, ∃ T : Lp ℂ 2 X.ν →L[ℂ] Lp ℂ 2 X.ν, ∀ f, (T f : X.G → ℂ) =ᵐ[X.ν]
      fun x => ∫ y, ker X.Γ (Φ i j) x y * (f : X.G → ℂ) y ∂X.ν := by
    intro i j
    obtain ⟨A, hA, h1, h2⟩ := hR X (Φ i j) (hΦ i j)
    have hc := (hK X (Φ i j) (hΦ i j)).2.1
    exact hS X.G X.ν (ker X.Γ (Φ i j)) A hc.measurable hA h1 h2
  choose S hSop using hex
  let T : X.Hs ι →L[ℂ] X.Hs ι :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 X.ν)).symm :
        (ι → Lp ℂ 2 X.ν) →L[ℂ] X.Hs ι) ∘L
      ContinuousLinearMap.pi fun i => ∑ j, (S i j).comp (PiLp.proj 2 (fun _ : ι => Lp ℂ 2 X.ν) j)
  have hT : ∀ f i, T f i = ∑ j, S i j (f j) := by
    intro f i
    simp [T, ContinuousLinearMap.sum_apply]
  have hIs : X.IsOp Φ T := by
    intro f i
    rw [hT]
    have hall : ∀ᵐ x ∂X.ν, ∀ j, (S i j (f j) : X.G → ℂ) x =
        ∫ y, ker X.Γ (Φ i j) x y * (f j : X.G → ℂ) y ∂X.ν :=
      ae_all_iff.2 fun j => hSop i j (f j)
    filter_upwards [coeFn_sum_ae Finset.univ (fun j => S i j (f j)), hall] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => h2 j
  refine ⟨T, hIs, ?_⟩
  intro T' hT'
  ext f : 1
  refine PiLp.ext fun i => Lp.ext ?_
  exact (hT' f i).trans (hIs f i).symm

end GlobalTheory.CompanionTheory.OpEx
end

section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.Kabs

theorem kD_kDel_apply {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]
    (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {n : ℕ}
    (θ : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (Y : Fin (n + 1) → P) :
    kD T (kDel T' b θ) Y = ∑ s, ∑ i, T (Y s) (T' (b i) (θ (Function.update Y s (b i)))) := by
  rw [kD_apply]
  refine Finset.sum_congr rfl fun s _ => ?_

  rw [kDel_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.insertNth_removeNth, θ.map_insertNth, map_zsmul, map_zsmul]

end GlobalTheory.CompanionTheory.Kabs
end
