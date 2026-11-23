module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem sq_le_qInf {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ e : F →+* ℝ, e δ < 0) (v : V4 F) : ∑ w, TR.pInf F (v 1) w ^ 2 ≤ qInf δ v := by
  rw [qInf]
  refine Finset.sum_le_sum fun w _ => ?_
  have hd : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
    congrFun (GlobalTheory.HilbertThetaSeries.RatPts.pInf_algebraMap F δ) w
  have hneg := hδ (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  simp only [map_add (f := _), map_mul, map_pow, map_sub, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, map_ofNat, Pi.ofNat_apply, hd]
  have h3 : 0 ≤ -(InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ) * TR.pInf F (v 3) w ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [sq_nonneg (TR.pInf F (v 0) w), sq_nonneg (TR.pInf F (v 2) w)]

private theorem exp_le_gauss {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ e : F →+* ℝ, e δ < 0) (R : ℝ) (v : V4 F) :
    Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * Real.exp (-(Real.pi / 2) * qInf δ v) ≤
      Real.exp (∑ _w : InfinitePlace F, R ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hq := sq_le_qInf δ hδ v
  have hs : 0 ≤ ∑ w, TR.pInf F (v 1) w ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have h1 : ∑ w, TR.pInf F (v 1) w ^ 2 ≤ Real.pi / 2 * qInf δ v := by nlinarith
  have h2 : R * ∑ w, |TR.pInf F (v 1) w| ≤ ∑ w, TR.pInf F (v 1) w ^ 2 + ∑ _w : InfinitePlace F, R ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    have h := sq_abs (TR.pInf F (v 1) w)
    nlinarith [sq_nonneg (|TR.pInf F (v 1) w| - R), sq_nonneg R, sq_nonneg (|TR.pInf F (v 1) w|)]
  linarith

theorem UpperTheory.ConvolutionTheory.R2.G.fockGauss :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ e : F →+* ℝ, e δ < 0) → ∀ χ ∈ FockFn δ, ∀ (R : ℝ) (N : ℕ), ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧
    ∀ v, Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖χ v‖ ≤ B * wt4 L N v := by
  intro F _ _ _ δ hδ χ hχ
  induction hχ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨p, hp, g, hg, rfl⟩ := h
    intro R N
    have hmem := UpperTheory.ConvolutionTheory.R2.G.pgMem F δ hδ (Real.pi / 2) (by positivity) p hp g hg
    obtain ⟨M, L, hM, hb⟩ := GlobalTheory.CompanionTheory.EpConvB.exists_majorant hmem (C := {1}) isCompact_singleton N
    refine ⟨Real.exp (∑ _w : InfinitePlace F, R ^ 2) * M, L, mul_nonneg (Real.exp_pos _).le hM, fun v => ?_⟩
    have h1 := hb 1 rfl v
    rw [Units.val_one, Matrix.one_mulVec] at h1
    have hsplit : ‖p v * gauss δ v * g (finPartPi v)‖ =
        Real.exp (-(Real.pi / 2) * qInf δ v) *
          ‖p v * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ)) * g (finPartPi v)‖ := by
      have hg2 : ‖gauss δ v‖ = Real.exp (-(Real.pi / 2) * qInf δ v) * Real.exp (-(Real.pi / 2) * qInf δ v) := by
        rw [gauss_eq, ← Real.exp_add, Complex.norm_exp]
        congr 1
        simp
        ring
      have hg3 : ‖Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ))‖ = Real.exp (-(Real.pi / 2) * qInf δ v) := by
        rw [Complex.norm_exp]
        congr 1
        simp
      simp only [norm_mul, hg2, hg3]
      ring
    rw [hsplit, ← mul_assoc]
    calc _ ≤ Real.exp (∑ _w : InfinitePlace F, R ^ 2) *
          ‖p v * Complex.exp (-((Real.pi / 2 : ℝ) : ℂ) * (qInf δ v : ℝ)) * g (finPartPi v)‖ :=
          mul_le_mul_of_nonneg_right (exp_le_gauss δ hδ R v) (norm_nonneg _)
      _ ≤ Real.exp (∑ _w : InfinitePlace F, R ^ 2) * (M * wt4 L N v) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = _ := by ring
  | zero =>
    intro R N
    exact ⟨0, 1, le_rfl, fun v => by simp⟩
  | add f g _ _ hf hg =>
    intro R N
    obtain ⟨B₁, L₁, h₁, hb₁⟩ := hf R N
    obtain ⟨B₂, L₂, h₂, hb₂⟩ := hg R N
    have hmono : ∀ {L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ},
        (L' : FractionalIdeal (𝓞 F)⁰ F) ≤ (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂ : (FractionalIdeal (𝓞 F)⁰ F)ˣ) →
        ∀ v : V4 F, wt4 L' N v ≤ wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v := fun h v =>
      Finset.prod_le_prod₀ (fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _)
        fun i _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_mono h N _
    refine ⟨B₁ + B₂, GroundTheory.Global.fractionalIdealSupUnit L₁ L₂, add_nonneg h₁ h₂, fun v => ?_⟩
    have he := (Real.exp_pos (R * ∑ w, |TR.pInf F (v 1) w|)).le
    calc Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖(f + g) v‖
        ≤ Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * (‖f v‖ + ‖g v‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) he
      _ = Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖f v‖ + Real.exp (R * ∑ w, |TR.pInf F (v 1) w|) * ‖g v‖ := by ring
      _ ≤ B₁ * wt4 L₁ N v + B₂ * wt4 L₂ N v := add_le_add (hb₁ v) (hb₂ v)
      _ ≤ B₁ * wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v + B₂ * wt4 (GroundTheory.Global.fractionalIdealSupUnit L₁ L₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (hmono le_sup_left v) h₁)
            (mul_le_mul_of_nonneg_left (hmono le_sup_right v) h₂)
      _ = _ := by ring
  | smul r f _ hf =>
    intro R N
    obtain ⟨B, L, hB, hb⟩ := hf R N
    refine ⟨‖r‖ * B, L, by positivity, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_left_comm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v) (norm_nonneg r)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem hat_n {D : Dat F E} (W : Weil D) (Ψ : S4 F) (ξ : Fin 2 → F) (b : A F) (g : G1 F) :
    hat (W.Om (nU b * g) Ψ).1 (pt ξ) = ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) * hat (W.Om g Ψ).1 (pt ξ) := by
  have hH := (_root_.UpperTheory.ConvolutionTheory.R2.hatSt F E D W).n b (W.Om g Ψ) (pt ξ)
  have e : W.Om (nU b * g) Ψ = W.Om (nU b) (W.Om g Ψ) := by rw [map_mul]; rfl
  have e1 : pt ξ 1 + b * pt ξ 0 = pt ξ 1 := by simp [pt]
  have e3 : b * (pt ξ 2 ^ 2 - rt D.δ * pt ξ 3 ^ 2) = rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b := by
    simp only [pt, rt, map_sub, map_mul, map_pow]
    simp
    ring
  rw [e, hH, e1, Function.update_eq_self, e3]

private theorem hat_meas {D : Dat F E} (W : Weil D) (Ψ : S4 F) (v : V4 F) :
    Measurable fun g : G1 F => hat (W.Om g Ψ).1 v := by
  have hc : Continuous fun p : G1 F × A F =>
      (W.Om p.1 Ψ).1 (Function.update v 1 p.2) * ψ (-(p.2 * v 1)) := by
    have h2 : Continuous fun s : A F => Function.update v 1 s := continuous_const.update 1 continuous_id
    have h1 : Continuous fun p : G1 F × A F => (p.1, Function.update v 1 p.2) :=
      continuous_fst.prodMk (h2.comp continuous_snd)
    have h3 : Continuous fun s : A F => ψ (-(s * v 1)) :=
      Pp.cont_ψ.comp ((continuous_id.mul continuous_const).neg)
    exact ((W.cont Ψ).comp h1).mul (h3.comp continuous_snd)
  exact (hc.stronglyMeasurable.integral_prod_right (ν := adeleMeasure F)).measurable

end UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

open UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage in
theorem UpperTheory.ConvolutionTheory.R2.G.uxAv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (f : GL (Fin 2) (A F) → ℂ), Pp.Lf f → ∀ φ h ξ, NInv (ux W f φ h ξ) ∧ av (ux W f φ h ξ) = wx W f φ h ξ ∧
    ∀ b g, ‖ux W f φ h ξ (nU b * g)‖ = ‖f (gl (nU b * g) * dM (nu F h))‖ * ‖hat (W.Om g (W.L h φ)).1 (pt ξ)‖ := by
  intro F E _ _ _ _ _ _ _ D W f hf φ h ξ
  have hgl : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
  have hux : ∀ b g, ux W f φ h ξ (nU b * g) =
      f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) *
        hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    intro b g
    simp only [ux]
    rw [hat_n, hgl, mul_assoc (gl (nU b)), mul_assoc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have h1 : Continuous fun g : G1 F => f (gl g * dM (nu F h)) :=
      hf.1.comp (_root_.UpperTheory.ConvolutionTheory.R2.M.continuous_gl.mul continuous_const)
    exact h1.measurable.mul (hat_meas W _ _)
  · intro c g
    rw [hux]
    have e : rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * rt c = rt ((ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * c) := (map_mul _ _ _).symm
    have e2 : f (gl (nU (rt c)) * (gl g * dM (nu F h))) = f (gl g * dM (nu F h)) := by
      obtain ⟨γ, hγ⟩ := Pp.rat_n c
      rw [← hγ, hf.2]
    rw [e, Pp.ψ_rt, mul_one, e2]
    rfl
  · funext g
    simp only [av, wx]
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun b => hux b g)
  · intro b g
    simp only [ux]
    rw [hat_n, norm_mul, norm_mul, Pp.norm_ψ, one_mul]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem conj_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    {ξ : Fin 2 → F} (hξ : ξ ≠ 0) : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0 := by
  intro h
  have hl := Fintype.linearIndependent_iff.1 D.b.linearIndependent ![ξ 0, -ξ 1] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, D.b0, D.b1, Algebra.smul_def, map_neg]
    simp only [Matrix.cons_val_fin_one, mul_one, map_neg]
    linear_combination h)
  apply hξ
  ext i
  fin_cases i
  · simpa using hl 0
  · simpa using hl 1

private theorem coe_al {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    (ξ : Fin 2 → F) (h : algebraMap F E (ξ 0) - algebraMap F E (ξ 1) * D.θ ≠ 0) :
    ((al D ξ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (-rt (ξ 1)) := by
  have e := D.mkE_rt (ξ 0) (-ξ 1)
  have e' : -rt (ξ 1) = (rt (-ξ 1) : A F) := (map_neg _ _).symm
  rw [e', e, al, dite_eq_right h, IdeleGroup.coe_diagonal]
  simp [sub_eq_add_neg]

private theorem vcD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    (gl (cD t x)).val = !![x 0 0, x 0 1 * ((t⁻¹ : (A F)ˣ) : A F); (t : A F) * x 1 0, x 1 1] := rfl

private theorem vgl {F : Type} [Field F] [NumberField F] (x : G1 F) : (gl x).val = x.1 := rfl

private theorem vmD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) :
    (gl (mD t)).val = !![(t : A F), 0; 0, ((t⁻¹ : (A F)ˣ) : A F)] := rfl

private theorem cD_dM {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) (x : G1 F) :
    gl (cD t x) * dM t = dM t * gl x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, vcD, vgl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] <;> ring

private theorem dM_mD {F : Type} [Field F] [NumberField F] (t : (A F)ˣ) : dM t * gl (mD t) = aE t := by
  refine Units.ext ?_
  rw [Units.val_mul, vmD]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, aE, Matrix.mul_apply, Fin.sum_univ_two]

private theorem pt_move {F : Type} [Field F] [NumberField F] (t n : (A F)ˣ) (g : G1 F) :
    gl (cD t (mD t * g)) * dM (t * n) = aE t * (gl g * dM n) := by
  rw [UpperTheory.ConvolutionTheory.R2.dM_mul, ← mul_assoc, cD_dM, gl_mul, ← mul_assoc (dM t), dM_mD, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.G.wxPt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (ξ : Fin 2 → F), ξ ≠ 0 → ∃ t : Fˣ, ∀ f : GL (Fin 2) (A F) → ℂ, Pp.Lf f → ∀ φ h g,
    w1 W f φ (aE (al D ξ) * h) (cD (IdeleGroup.diagonal F t) (mD (IdeleGroup.diagonal F t) * g)) = wx W f φ h ξ g := by
  intro F E _ _ _ _ _ _ _ D W ξ hξ
  have hz := conj_ne D hξ
  have hα := coe_al D ξ hz
  set α := al D ξ with hαdef
  let t : Fˣ := Units.map (Algebra.norm F : E →* F) (Units.mk0 _ hz)
  have hT : ideleNorm F E α = IdeleGroup.diagonal F t := by
    rw [hαdef, al, dite_eq_right hz, ideleNorm_diagonal]
  have hco : D.co (α : A E) = ![rt (ξ 0), -rt (ξ 1)] := by rw [hα, D.co_mkE]
  have ht : (t : F) = ξ 0 ^ 2 - D.δ * ξ 1 ^ 2 := by
    haveI := AdeleBaseChange.nontrivial_adeleRing F
    apply (algebraMap F (A F)).injective
    have h1 := D.coe_ideleNorm α
    rw [hT, IdeleGroup.coe_diagonal, hco] at h1
    simpa using h1
  refine ⟨t, fun f hf φ h g => ?_⟩
  set T := IdeleGroup.diagonal F t with hTdef
  have hnu : nu F (aE α * h) = T * nu F h := by rw [nu_mul, nu_aE, hT]
  have hpoint : ![T * (0 : A F), ((T⁻¹ : (A F)ˣ) : A F) * ((ideleNorm F E α : (A F)ˣ) * 1),
      T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 0, T * D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE 1 0) 1] = pt ξ := by
    have hb : am E (T : A F) * ((α⁻¹ : (A E)ˣ) : A E) = D.mkE (rt (ξ 0)) (rt (ξ 1)) := by
      rw [← hT, D.am_ideleNorm, mul_comm (α : A E), mul_assoc, Units.mul_inv, mul_one, hα, D.bar_mkE, neg_neg]
    have hc := D.co_am_mul (T : A F) ((α⁻¹ : (A E)ˣ) : A E)
    rw [hb, D.co_mkE] at hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    rw [D.mkE_one, mul_one, hT]
    simp [pt, ← h0, ← h1]
  have hhat : hat (W.Om (cD T (mD T * g)) (W.L (aE α * h) φ)).1 ![0, 1, 1, 0] = hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    have hcm : W.Om (cD T (mD T * g)) (W.L (aE α) (W.L h φ)) = W.L (aE α) (W.Om (mD T * g) (W.L h φ)) := by
      have := W.comm (aE α) (mD T * g)
      rw [nu_aE, hT] at this
      exact (LinearMap.congr_fun this (W.L h φ)).symm
    rw [map_mul, Module.End.mul_apply, hcm]
    have hS := hatSt F E D W
    have e1 := hS.aE α (W.Om (mD T * g) (W.L h φ)) 0 1 1 0
    have e2 := hS.m T (W.Om g (W.L h φ))
    have e3 : ((W.η.1 T : ℂˣ) : ℂ) = 1 := by rw [← hT, W.η_norm]; rfl
    have e4 : ab T = 1 := ab_diagonal t
    rw [e1, map_mul, Module.End.mul_apply, e2, e3, e4]
    have hv := hpoint
    rw [← hv]
    simp
  have hw : ∫ b in fundamentalSet F, f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) ∂(adeleMeasure F) =
      Wf f (aE T * (gl g * dM (nu F h))) := by
    rw [← ht]
    exact Pp.wfT F f hf t _
  simp only [w1, wx]
  rw [hhat, hnu, pt_move, hw]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem nu_nE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) :
    nu F (nE D u * h) = nu F h := by
  have hd : Matrix.GeneralLinearGroup.det (nE D u) = 1 := by
    exact Units.ext (nU (D.mkE (u 0) (u 1))).2
  simp only [nu, map_mul, hd, one_mul]

private theorem cD_unit {F : Type} [Field F] [NumberField F] (g : G1 F) : cD (1 : (A F)ˣ) g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem om_L {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (u : Fin 2 → A F) (h : GL (Fin 2) (A E)) (φ : S4 F) (g : G1 F) :
    W.Om g (W.L (nE D u * h) φ) = W.L (nE D u) (W.Om g (W.L h φ)) := by
  have hn : nu F (nE D u) = 1 := by
    have := nu_nE D u 1
    rw [mul_one] at this
    rw [this]
    simp [nu]
  have hc := W.comm (nE D u) g
  rw [hn, cD_unit] at hc
  rw [map_mul, Module.End.mul_apply]
  exact (LinearMap.congr_fun hc (W.L h φ)).symm

theorem UpperTheory.ConvolutionTheory.R2.G.transN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)) (u : Fin 2 → A F), T0 W M f φ (nE D u * h) = T0 W M f φ h ∧
    ∀ ξ, Wx W M f φ (nE D u * h) ξ = chi D.δ ξ u * Wx W M f φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M f φ h u
  have hH : St.Hat W := hatSt F E D W
  have hnu := nu_nE D u h
  constructor
  · unfold T0
    refine setIntegral_congr_fun M.meas fun g _ => ?_
    have hrow : ThRow 0 0 (W.Om g (W.L (nE D u * h) φ)).1 = ThRow 0 0 (W.Om g (W.L h φ)).1 := by
      rw [om_L]
      unfold ThRow
      refine tsum_congr fun ξ => ?_
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 0 (rt (ξ 0)) (rt (ξ 1))
      simpa [nE, zero_mul, neg_zero, ψ] using this
    simp only [hnu, hrow]
  · intro ξ
    have hpt : ∀ g, wx W f φ (nE D u * h) ξ g = chi D.δ ξ u * wx W f φ h ξ g := by
      intro g
      unfold wx
      rw [hnu, om_L]
      have := hH.nE (u 0) (u 1) (W.Om g (W.L h φ)) 1 (rt (ξ 0)) (rt (ξ 1))
      have e : hat (W.L (nE D u) (W.Om g (W.L h φ))).1 (pt ξ) =
          chi D.δ ξ u * hat (W.Om g (W.L h φ)).1 (pt ξ) := by
        simpa only [one_mul, chi, pt, nE] using this
      rw [e]
      ring
    unfold Wx Meas.I0
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [iw, hpt]
    ring
end
