module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.lamGen :
    (∀ (G H : Type) [Add G] [Add H] [MeasurableSpace G] [MeasurableSpace H] (μ : Measure G) (ν : Measure H) [SFinite μ] [SFinite ν] (γ φ : G → ℂ) (γ' φ' : H → ℂ),
      abelian₂ (μ.prod ν) (fun p => γ p.1 * γ' p.2) (fun p => φ p.1 * φ' p.2) = abelian₂ μ γ φ * abelian₂ ν γ' φ') ∧
    (∀ (ι G : Type) [Fintype ι] [Add G] [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ] (γ φ : ι → G → ℂ),
      abelian₂ (Measure.pi fun _ : ι => μ) (fun v => ∏ i, γ i (v i)) (fun v => ∏ i, φ i (v i)) = ∏ i, abelian₂ μ (γ i) (φ i)) ∧
    ∀ (G H : Type) [Add G] [Add H] [MeasurableSpace G] [MeasurableSpace H] (μ : Measure G) (ν : Measure H) (e : G ≃ᵐ H) (c : ENNReal),
      (∀ x y, e (x + y) = e x + e y) → μ.map e = c • ν → ∀ γ φ : H → ℂ,
      abelian₂ μ (fun x => γ (e x)) (fun x => φ (e x)) = ((c.toReal : ℝ) : ℂ) ^ 2 * abelian₂ ν γ φ ∧ ∫ x, φ (e x) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, φ x ∂ν := by
  refine ⟨fun G H _ _ _ _ μ ν _ _ γ φ γ' φ' => ?_, fun ι G _ _ _ μ _ γ φ => ?_, fun G H _ _ _ _ μ ν e c he hm γ φ => ?_⟩
  · simp only [abelian₂]
    rw [← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · simp only [abelian₂]
    rw [← integral_fintype_prod_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_fintype_prod_eq_prod (fun i x => φ i x * γ i (x + y i))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Finset.prod_mul_distrib]
  · have key : ∀ u : H → ℂ, ∫ x, u (e x) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, u x ∂ν := fun u => by
      rw [← integral_map_equiv e u, hm, integral_smul_measure, Complex.real_smul]
    refine ⟨?_, key φ⟩
    simp only [abelian₂, he]
    have h1 : ∀ y, ∫ x, φ (e x) * γ (e x + e y) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, φ x * γ (x + e y) ∂ν := fun y =>
      key fun x => φ x * γ (x + e y)
    simp only [h1]
    rw [integral_const_mul, key fun y => ∫ x, φ x * γ (x + y) ∂ν]
    ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma half_root (a : ℂ) (ha : 0 < a.re) :
    (a ^ (1 / 2 : ℂ)) ^ 2 = a ∧ 0 < (a ^ (1 / 2 : ℂ)).re ∧
      |(a ^ (1 / 2 : ℂ)).im| < (a ^ (1 / 2 : ℂ)).re := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h2 : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by
    have := Complex.cpow_nat_inv_pow a (n := 2) two_ne_zero
    simpa [one_div] using this
  have hpos : 0 < (a ^ (1 / 2 : ℂ)).re := by
    have harg : |a.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl ha)
    have harg' := abs_lt.1 harg
    rw [Complex.cpow_def_of_ne_zero ha0, Complex.exp_re]
    have him : (Complex.log a * (1 / 2 : ℂ)).im = a.arg / 2 := by
      simp [Complex.log_im]
      ring
    rw [him]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;> linarith [Real.pi_pos]
  refine ⟨h2, hpos, ?_⟩
  generalize a ^ (1 / 2 : ℂ) = w at h2 hpos
  have hre : a.re = w.re ^ 2 - w.im ^ 2 := by
    rw [← h2, pow_two, Complex.mul_re]
    ring
  apply abs_lt_of_sq_lt_sq _ hpos.le
  linarith

private lemma lamR_props (β : ℝ) (hβ : β ≠ 0) :
    lamR β ^ 2 = 1 / (2 * Complex.I * (β : ℂ)) ∧ 0 < (lamR β).re := by
  have hr : 0 < √|β| := Real.sqrt_pos.2 (abs_pos.2 hβ)
  have hrc : ((√|β| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hsq : ((√|β| : ℝ) : ℂ) ^ 2 = ((|β| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (abs_nonneg β)]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rcases lt_or_gt_of_ne hβ with h | h
  · have hs : ((SignType.sign β : SignType) : ℂ) = -1 := by simp [sign_neg h]
    have hab : ((|β| : ℝ) : ℂ) = -(β : ℂ) := by
      rw [abs_of_neg h]; push_cast; ring
    constructor
    · simp only [lamR, hs]
      push_cast
      rw [div_pow, mul_pow, hsq, hab]
      field_simp
      linear_combination (-(2 + Complex.I)) * hI
    · simp only [lamR, hs]
      rw [Complex.div_ofReal_re]
      simp
      positivity
  · have hs : ((SignType.sign β : SignType) : ℂ) = 1 := by simp [sign_pos h]
    have hab : ((|β| : ℝ) : ℂ) = (β : ℂ) := by
      rw [abs_of_pos h]
    constructor
    · simp only [lamR, hs]
      push_cast
      rw [div_pow, mul_pow, hsq, hab]
      field_simp
      linear_combination (Complex.I - 2) * hI
    · simp only [lamR, hs]
      rw [Complex.div_ofReal_re]
      simp
      positivity

theorem UpperTheory.ConvolutionTheory.R2.C.lamReal :
    ∀ β : ℝ, β ≠ 0 → abelian₂ (volume : Measure ℝ) (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * (x : ℂ) ^ 2)) (fun x => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) = lamR β := by
  intro β hβ
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hbc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = 1 + 2 * Complex.I * (β : ℂ) := ⟨_, rfl⟩
  have hDre : D.re = 1 := by simp [hDdef]
  have hDim : D.im = 2 * β := by simp [hDdef]
  have hD : D ≠ 0 := by
    intro h
    rw [h] at hDre
    simp at hDre
  have hnsq : 0 < Complex.normSq D := Complex.normSq_pos.2 hD
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = 2 * Complex.I * (β : ℂ) / D := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by
    rw [hsdef]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hI0) hbc) hD
  have hsre : 0 < s.re := by
    rw [hsdef, Complex.div_re]
    have e1 : (2 * Complex.I * (β : ℂ)).re = 0 := by simp
    have e2 : (2 * Complex.I * (β : ℂ)).im = 2 * β := by simp
    rw [e1, e2, hDim, zero_mul, zero_div, zero_add]
    have : 0 < 2 * β * (2 * β) := by
      have := mul_self_pos.2 (mul_ne_zero two_ne_zero hβ)
      simpa using this
    exact div_pos this hnsq
  have hinvD : 0 < (1 / D).re := by
    rw [one_div, Complex.inv_re, hDre]
    exact div_pos one_pos hnsq
  have hinvs : 0 < (1 / s).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos hsre (Complex.normSq_pos.2 hs0)
  have hb : (-(Real.pi : ℂ) * D).re < 0 := by
    simp [hDre, hDim, Real.pi_pos]
  have hinner : ∀ y : ℝ,
      (∫ x : ℝ, Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) =
      (1 / D) ^ (1 / 2 : ℂ) * Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2) := by
    intro y
    have hfun : (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (β : ℂ) * ((x + y : ℝ) : ℂ) ^ 2)) =
        fun x : ℝ => Complex.exp ((-(Real.pi : ℂ) * D) * (x : ℂ) ^ 2 +
          (-(4 * Real.pi * Complex.I * (β : ℂ) * (y : ℂ))) * (x : ℂ) +
          (-(2 * Real.pi * Complex.I) * (β : ℂ) * (y : ℂ) ^ 2)) := by
      funext x
      rw [← Complex.exp_add, hDdef]
      congr 1
      push_cast
      ring
    rw [hfun, integral_cexp_quadratic hb]
    congr 1
    · congr 1
      field_simp
    · congr 1
      rw [hsdef, hDdef]
      have hD' : (1 + 2 * Complex.I * (β : ℂ)) ≠ 0 := hDdef ▸ hD
      field_simp
      ring
  unfold abelian₂
  simp only [hinner]
  rw [integral_const_mul]
  have houter : (∫ y : ℝ, Complex.exp (-((Real.pi : ℂ) * s) * (y : ℂ) ^ 2)) = (1 / s) ^ (1 / 2 : ℂ) := by
    have hre : 0 < ((Real.pi : ℂ) * s).re := by
      simpa using mul_pos Real.pi_pos hsre
    rw [integral_gaussian_complex hre]
    congr 1
    field_simp
  rw [houter]
  obtain ⟨hA2, hApos, hAim⟩ := half_root _ hinvD
  obtain ⟨hB2, hBpos, hBim⟩ := half_root _ hinvs
  obtain ⟨hL2, hLpos⟩ := lamR_props β hβ
  generalize (1 / D) ^ (1 / 2 : ℂ) = A at hA2 hApos hAim
  generalize (1 / s) ^ (1 / 2 : ℂ) = B at hB2 hBpos hBim
  have hsq : (A * B) ^ 2 = lamR β ^ 2 := by
    rw [mul_pow, hA2, hB2, hL2, hsdef]
    field_simp
  have hzre : 0 < (A * B).re := by
    rw [Complex.mul_re]
    have h1 : A.im * B.im ≤ |A.im| * |B.im| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |A.im| * |B.im| < A.re * B.re :=
      mul_lt_mul'' hAim hBim (abs_nonneg _) (abs_nonneg _)
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · exfalso
    rw [h, Complex.neg_re] at hzre
    linarith
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

section
variable {F : Type} [Field F] [NumberField F]

private lemma nU_val (b : A F) : (nU b).1 = !![1, b; 0, 1] := rfl
private lemma mD_val (a : (A F)ˣ) : (mD a).1 = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl
private lemma wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

private lemma sl_ext {g h : G1 F} (e : g.1 = h.1) : g = h := Subtype.ext e

private lemma sl_of {g h : G1 F} {p q r s : A F} (e : h.1 = !![p, q; r, s])
    (h00 : g.1 0 0 = p) (h01 : g.1 0 1 = q) (h10 : g.1 1 0 = r) (h11 : g.1 1 1 = s) : g = h := by
  apply sl_ext
  rw [e, Matrix.eta_fin_two g.1, h00, h01, h10, h11]

private lemma det_eq (g : G1 F) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma nm_val (b : A F) (a : (A F)ˣ) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, mD_val, Matrix.mul_fin_two]
  simp

private lemma cell_val (b b' : A F) (a : (A F)ˣ) :
    (nU b * mD a * wW F * nU b').1 =
      !![-(b * ((a⁻¹ : (A F)ˣ) : A F)), (a : A F) - b * ((a⁻¹ : (A F)ˣ) : A F) * b';
        -((a⁻¹ : (A F)ˣ) : A F), -(((a⁻¹ : (A F)ˣ) : A F) * b')] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, nm_val, wW_val, nU_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  simp
  ring_nf

private lemma rel_part : Rel (nU (F := F)) mD (wW F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Group.isUnit _⟩
  · apply sl_ext
    simp [nU_val, Matrix.one_fin_two]
  · intro b c
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, nU_val, nU_val, Matrix.mul_fin_two]
    simp [add_comm]
  · apply sl_ext
    simp [mD_val, Matrix.one_fin_two]
  · intro a a'
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, mD_val, mD_val, mD_val, Matrix.mul_fin_two]
    simp [mul_comm]
  · intro a b
    apply sl_ext
    have he : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
    rw [Matrix.SpecialLinearGroup.coe_mul, nm_val, mD_val, nU_val, Matrix.mul_fin_two]
    have hq : (a : A F) ^ 2 * b * ((a⁻¹ : (A F)ˣ) : A F) = (a : A F) * b := by
      linear_combination ((a : A F) * b) * he
    simp [hq]
  · intro a
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, mD_val, mD_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp

private lemma gauss_part : Gauss (nU (F := F)) mD (wW F) := by
  intro t
  apply sl_ext
  have he : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := t.mul_inv
  rw [cell_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, nU_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [he]

private lemma tri_part (g : G1 F) : g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a := by
  constructor
  · intro h
    have h' : g.1 1 0 = 0 := h
    have hd := det_eq g
    rw [h', mul_zero, sub_zero] at hd
    have hd' : g.1 1 1 * g.1 0 0 = 1 := by rw [mul_comm]; exact hd
    refine ⟨g.1 0 1 * g.1 0 0, ⟨g.1 0 0, g.1 1 1, hd, hd'⟩, ?_⟩
    refine sl_of (nm_val _ _) rfl ?_ h' rfl
    show g.1 0 1 = g.1 0 1 * g.1 0 0 * g.1 1 1
    linear_combination (-g.1 0 1) * hd
  · rintro ⟨b, a, rfl⟩
    show (nU b * mD a).1 1 0 = 0
    rw [nm_val]
    simp

private lemma tri_uniq (b b' : A F) (a a' : (A F)ˣ) (e : nU b * mD a = nU b' * mD a') : b = b' ∧ a = a' := by
  have h := congrArg Subtype.val e
  rw [nm_val, nm_val] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  have ha : a = a' := Units.ext h00
  subst ha
  exact ⟨(Units.mul_left_inj _).1 h01, rfl⟩

private lemma cell_part (g : G1 F) : IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  constructor
  · rintro ⟨c, hc⟩
    have hc' : g.1 1 0 = (c : A F) := hc.symm
    have he : (c : A F) * ((c⁻¹ : (A F)ˣ) : A F) = 1 := c.mul_inv
    have hd := det_eq g
    rw [hc'] at hd
    refine ⟨g.1 0 0 * ((c⁻¹ : (A F)ˣ) : A F), -c⁻¹, g.1 1 1 * ((c⁻¹ : (A F)ˣ) : A F), ?_⟩
    refine sl_of (cell_val _ _ _) ?_ ?_ ?_ ?_
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 0 0) * he
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) ^ 2)) * hd +
        (-((c⁻¹ : (A F)ˣ) : A F) - g.1 0 1 * ((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) + 1)) * he
    · simp only [inv_neg, inv_inv, Units.val_neg, neg_neg]
      exact hc'
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 1 1) * he
  · rintro ⟨b, a, b', rfl⟩
    show IsUnit ((nU b * mD a * wW F * nU b').1 1 0)
    rw [cell_val]
    simp
end

theorem UpperTheory.ConvolutionTheory.R2.C.grpRel :
    ∀ (F : Type) [Field F] [NumberField F], Rel (nU (F := F)) mD (wW F) ∧ Gauss (nU (F := F)) mD (wW F) ∧
    (∀ g : G1 F, g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a) ∧ (∀ (b b' : A F) a a', nU b * mD a = nU b' * mD a' → b = b' ∧ a = a') ∧
    ∀ g : G1 F, IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  intro F _ _
  exact ⟨rel_part, gauss_part, tri_part, tri_uniq, cell_part⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem one_side {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] (μ : Measure G) [SFinite μ]
    [μ.IsAddLeftInvariant] (γ φ₁ φ₂ : G → ℂ) (h2 : Integrable φ₂ μ) (hP : Integrable (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) μ) :
    (∫ y, ∫ x, φ₁ x * γ (x + y) ∂μ ∂μ) * ∫ x, φ₂ x ∂μ = ∫ y, ∫ z, ∫ x, φ₂ z * (φ₁ x * γ (x + (z + y))) ∂μ ∂μ ∂μ := by
  have h3 := ((measurePreserving_prod_add μ μ).integrable_comp_of_integrable (h2.mul_prod hP))
  have h4 := integral_integral_swap (f := fun z y => φ₂ z * ∫ x, φ₁ x * γ (x + (z + y)) ∂μ) h3
  simp only [integral_const_mul] at h4 ⊢
  rw [← h4, mul_comm, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_add_left_eq_self (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) z]

theorem UpperTheory.ConvolutionTheory.R2.C.symm :
    ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G) [SFinite μ] [μ.IsAddLeftInvariant] (γ φ₁ φ₂ : G → ℂ),
    Measurable γ → (∀ x, ‖γ x‖ ≤ 1) → Integrable φ₁ μ → Integrable φ₂ μ → Integrable (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) μ →
    Integrable (fun y => ∫ x, φ₂ x * γ (x + y) ∂μ) μ → abelian₂ μ γ φ₁ * ∫ x, φ₂ x ∂μ = abelian₂ μ γ φ₂ * ∫ x, φ₁ x ∂μ := by
  intro G _ _ _ _ μ _ _ γ φ₁ φ₂ hγ hb h1 h2 hP1 hP2
  refine (one_side μ γ φ₁ φ₂ h2 hP1).trans (Eq.trans ?_ (one_side μ γ φ₂ φ₁ h1 hP2).symm)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hm : Measurable fun p : G × G => γ (p.2 + (p.1 + y)) := hγ.comp (by fun_prop)
  have h3 := (h2.mul_prod h1).mul_bdd (c := 1) hm.aestronglyMeasurable (Eventually.of_forall fun p => hb _)
  have h4 := integral_integral_swap (f := fun z x => φ₂ z * φ₁ x * γ (x + (z + y))) h3
  simp only [mul_assoc] at h4
  refine h4.trans (integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun z => ?_)))
  simp only
  rw [add_left_comm]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.sgnEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ a : (A F)ˣ, IsSgn a ∧ a * a = 1 ∧ ab a = 1 := by
  intro F _ _ _
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set s : TR.Rinf F := fun w => if w = w₀ then -1 else 1 with hs
  have hss : s * s = 1 := by
    funext w
    by_cases h : w = w₀ <;> simp [hs, h]
  have hx : ((TR.infEq F s, 1) : A F) * (TR.infEq F s, 1) = 1 := by
    have h1 : TR.infEq F s * TR.infEq F s = 1 := by rw [← map_mul, hss, map_one]
    exact Prod.ext h1 (mul_one _)
  let a : (A F)ˣ := ⟨(TR.infEq F s, 1), (TR.infEq F s, 1), hx, hx⟩
  have haa : a * a = 1 := Units.ext hx
  refine ⟨a, ⟨rfl, w₀, fun w => ?_⟩, haa, ?_⟩
  · change (TR.infEq F).symm (TR.infEq F s) w = _
    rw [RingEquiv.symm_apply_apply]
  · have h1 : IdeleGroup.ideleModule F (a * a) = 1 := by rw [haa, map_one]
    rw [map_mul] at h1
    have h2 : ab a * ab a = 1 := by
      have := congrArg (fun r : {r : ℝ // 0 < r} => (r : ℝ)) h1
      simpa [ab] using this
    have h3 : 0 < ab a := (IdeleGroup.ideleModule F a).2
    nlinarith
end
