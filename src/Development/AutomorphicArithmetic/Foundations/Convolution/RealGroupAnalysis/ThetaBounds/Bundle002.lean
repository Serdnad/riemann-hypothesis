module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle003
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private theorem infPart_add (a b : V4 F) : infPartPi (a + b) = infPartPi a + infPartPi b := by
  funext i
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _

variable [IsTotallyReal F]

private noncomputable def ell : (Fin 4 → TR.Rinf F) →L[ℝ] (Fin 4 → mixedEmbedding.mixedSpace F) :=
  AddMonoidHom.toRealLinearMap
    { toFun := fun x => infPartPi fun i => TR.sInf F (x i)
      map_zero' := by
        funext i
        simp only [infPartPi, map_zero, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun x y => by
        have : (fun i => TR.sInf F ((x + y) i)) = (fun i => TR.sInf F (x i)) + fun i => TR.sInf F (y i) := by
          funext i
          simp only [Pi.add_apply, map_add (f := _)]
        rw [this, infPart_add] }
    (continuous_pi fun i => (homeomorphMixedSpace F).continuous.comp
      ((TR.continuous_infEq F).comp (continuous_apply i)))

private theorem differentiable_schwartz_translate (v : V4 F) {Φ : V4 F → ℂ} (h : Φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    Differentiable ℝ fun x : Fin 4 → TR.Rinf F => Φ fun i => v i + TR.sInf F (x i) := by
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : ∀ x : Fin 4 → TR.Rinf F, schwartzBruhatTensorPi f g (fun i => v i + TR.sInf F (x i)) =
        f (infPartPi v + ell x) * g (finPartPi v) := by
      intro x
      have h1 : infPartPi (fun i => v i + TR.sInf F (x i)) = infPartPi v + ell x :=
        infPart_add v fun i => TR.sInf F (x i)
      have h2 : finPartPi (fun i => v i + TR.sInf F (x i)) = finPartPi v := by
        funext i
        exact add_zero (v i).2
      simp only [schwartzBruhatTensorPi, h1, h2]
    simp_rw [e]
    exact (f.differentiable.comp ((differentiable_const _).add ell.differentiable)).mul_const _
  | zero => exact differentiable_const _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.sDiff :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Fo.Ops F), SDiff O := by
  intro F _ _ _ O φ v x x' h0 hx
  set G : (Fin 4 → TR.Rinf F) → ℂ := fun y => φ.1 fun i => v i + TR.sInf F (y i) with hG
  have hd : DifferentiableAt ℝ G 0 := differentiable_schwartz_translate v φ.2 0
  have hF : HasFDerivAt G (fderiv ℝ G 0) (x 0) := by
    rw [h0]
    exact hd.hasFDerivAt
  have hc : HasDerivAt (fun t => G (x t)) (fderiv ℝ G 0 x') 0 := hF.comp_hasDerivAt 0 hx
  have hb : ∀ i w, fderiv ℝ G 0 (Pi.single i (Pi.single w 1)) = (O.d w i φ).1 v := by
    intro i w
    set e : Fin 4 → TR.Rinf F := Pi.single i (Pi.single w 1) with he
    have hl : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const e
    have hF0 : HasFDerivAt G (fderiv ℝ G 0) ((0 : ℝ) • e) := by
      rw [zero_smul]
      exact hd.hasFDerivAt
    have h1 := hF0.comp_hasDerivAt (0 : ℝ) hl
    have h2 := O.d_spec w i φ v
    have hfun : (fun t : ℝ => G (t • e)) = fun t : ℝ => φ.1 (v + Pi.single i (Fo.at1 w t)) := by
      funext t
      refine congrArg φ.1 ?_
      funext j
      by_cases hj : j = i
      · subst hj
        have : (t • e) j = Pi.single w t := by
          funext u
          by_cases hu : u = w
          · subst hu
            simp [he]
          · simp [he, hu]
        simp [this, Fo.at1]
      · have : (t • e) j = 0 := by simp [he, hj]
        simp [this, hj]
    exact (HasDerivAt.unique (by simpa [Function.comp_def, hfun] using h1) h2)
  have hs : x' = ∑ i, ∑ w, x' i w • (Pi.single i (Pi.single w 1) : Fin 4 → TR.Rinf F) := by
    funext i w
    have h1 : ∀ c, c ≠ i → (∑ u, x' c u • (Pi.single c (Pi.single u 1) : Fin 4 → TR.Rinf F)) i = 0 := by
      intro c hc
      simp [Finset.sum_apply, Pi.single_eq_of_ne hc.symm]
    have h2 : (∑ u, x' i u • (Pi.single i (Pi.single u 1) : Fin 4 → TR.Rinf F)) i w = x' i w := by
      simp [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun c _ hc => h1 c hc) (by simp), h2]
  have key : fderiv ℝ G 0 x' = ∑ i, ∑ w, ((x' i w : ℝ) : ℂ) * (O.d w i φ).1 v := by
    conv_lhs => rw [hs]

    simp only [map_sum, map_smul, hb, Complex.real_smul]
  rw [← key]
  exact hc
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieSplit {E : Type} [Field E] [NumberField E] (X : Lie E 2) :
    ∃ (Y : Lie E 2) (s : Cinf E), (Matrix.of Y).trace = 0 ∧ X = Y + zE s ∧ X 0 0 + X 1 1 = s + s := by
  have h : X 0 0 + X 1 1 = (2⁻¹ : ℝ) • (X 0 0 + X 1 1) + (2⁻¹ : ℝ) • (X 0 0 + X 1 1) := by
    rw [← add_smul]; norm_num
  refine ⟨X - zE ((2⁻¹ : ℝ) • (X 0 0 + X 1 1)), _, ?_, (sub_add_cancel _ _).symm, h⟩
  rw [Matrix.trace_fin_two]
  change (X 0 0 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) + (X 1 1 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) = 0
  linear_combination h
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem abs_le_of_continuous_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →+ ℝ) (hf : Continuous f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |f z| ≤ B * ‖z‖ := by
  refine ⟨‖f.toRealLinearMap hf‖, norm_nonneg _, fun z => ?_⟩
  have h := (f.toRealLinearMap hf).le_opNorm z
  simpa using h

private noncomputable def eU {E : Type} [Field E] [NumberField E] (z : InfinitePlace E → ℂ) : (Cinf E)ˣ where
  val := fun w => Complex.exp (z w)
  inv := fun w => Complex.exp (-z w)
  val_inv := by
    funext w
    change Complex.exp (z w) * Complex.exp (-z w) = 1
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by
    funext w
    change Complex.exp (-z w) * Complex.exp (z w) = 1
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

private theorem continuous_eU {E : Type} [Field E] [NumberField E] :
    Continuous (eU (E := E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w)
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w).neg

private theorem eU_add {E : Type} [Field E] [NumberField E] (z z' : InfinitePlace E → ℂ) :
    eU (z + z') = eU z * eU z' := by
  refine Units.ext ?_
  funext w
  change Complex.exp (z w + z' w) = Complex.exp (z w) * Complex.exp (z' w)
  rw [Complex.exp_add]

private theorem eU_log {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) :
    eU (fun w => Complex.log (s.val w)) = s := by
  refine Units.ext ?_
  funext w
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  change Complex.exp (Complex.log (s.val w)) = s.val w
  exact Complex.exp_log h0

private theorem norm_log_le {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) (w : InfinitePlace E) :
    ‖Complex.log (s.val w)‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) + Real.pi := by
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  have h1 : s⁻¹.val w ≠ 0 := right_ne_zero_of_mul_eq_one h
  have p0 : 0 < ‖s.val w‖ := norm_pos_iff.2 h0
  have p1 : 0 < ‖s⁻¹.val w‖ := norm_pos_iff.2 h1
  have hprod : ‖s.val w‖ * ‖s⁻¹.val w‖ = 1 := by rw [← norm_mul, h, norm_one]
  have b0 : ‖s.val w‖ ≤ ‖s.val‖ := norm_le_pi_norm s.val w
  have b1 : ‖s⁻¹.val w‖ ≤ ‖s⁻¹.val‖ := norm_le_pi_norm s⁻¹.val w
  have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
  have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
  have l0 : Real.log ‖s.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p0 (by linarith)
  have l1 : Real.log ‖s⁻¹.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p1 (by linarith)
  have hs : Real.log ‖s.val w‖ + Real.log ‖s⁻¹.val w‖ = 0 := by
    rw [← Real.log_mul p0.ne' p1.ne', hprod, Real.log_one]
  have hre : |(Complex.log (s.val w)).re| ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) := by
    rw [Complex.log_re, abs_le]
    constructor <;> linarith
  have him : |(Complex.log (s.val w)).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

theorem UpperTheory.ConvolutionTheory.R2.Ff.omGrowth :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), OmGrowth F E := by
  intro F E _ _ _ _ _ _ _ _D
  have hN : Continuous (fun s : (Cinf E)ˣ => ideleNorm F E (infId E s)) :=
    continuous_ideleNorm.comp (continuous_infId E)
  refine ⟨hN, fun ω hω => ?_⟩
  let c : (Cinf E)ˣ → ℝ := fun s => ‖((ω (ideleNorm F E (infId E s)) : ℂˣ) : ℂ)‖
  have hc : Continuous c := (Units.continuous_val.comp (hω.comp hN)).norm
  have hpos : ∀ s, 0 < c s := fun s => norm_pos_iff.2 (Units.ne_zero _)
  have hmul : ∀ s s', c (s * s') = c s * c s' := by
    intro s s'
    simp only [c, map_mul, Units.val_mul, norm_mul]
  let f : (InfinitePlace E → ℂ) →+ ℝ :=
    { toFun := fun z => Real.log (c (eU z))
      map_zero' := by
        have h1 : eU (0 : InfinitePlace E → ℂ) = 1 := by
          have := eU_add (0 : InfinitePlace E → ℂ) 0
          rw [add_zero] at this
          exact left_eq_mul.1 this
        have h2 : c 1 = 1 := by simp [c]
        change Real.log (c (eU 0)) = 0
        rw [h1, h2, Real.log_one]
      map_add' := fun z z' => by
        change Real.log (c (eU (z + z'))) = Real.log (c (eU z)) + Real.log (c (eU z'))
        rw [eU_add, hmul, Real.log_mul (hpos _).ne' (hpos _).ne'] }
  have hf : Continuous f :=
    (hc.comp continuous_eU).log fun z => (hpos _).ne'
  obtain ⟨B, hB0, hB⟩ := abs_le_of_continuous_add f hf
  refine ⟨Real.exp (B * Real.pi), ⌈B⌉₊, fun s => ?_⟩
  change c s ≤ _
  set H : ℝ := 1 + ‖s.val‖ + ‖s⁻¹.val‖ with hH
  have hH1 : 1 ≤ H := by
    have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
    have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
    linarith
  have hH0 : 0 < H := by linarith
  have hL : 0 ≤ Real.log H := Real.log_nonneg hH1
  let z : InfinitePlace E → ℂ := fun w => Complex.log (s.val w)
  have hz : ‖z‖ ≤ Real.log H + Real.pi :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => norm_log_le s w
  have hfz : f z = Real.log (c s) := by
    change Real.log (c (eU z)) = _
    rw [eU_log]
  have h1 : Real.log (c s) ≤ B * (Real.log H + Real.pi) := by
    rw [← hfz]
    exact (le_abs_self _).trans ((hB z).trans (mul_le_mul_of_nonneg_left hz hB0))
  have h2 : B * (Real.log H + Real.pi) ≤ B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H := by
    have : B * Real.log H ≤ (⌈B⌉₊ : ℝ) * Real.log H :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil B) hL
    linarith
  calc c s = Real.exp (Real.log (c s)) := (Real.exp_log (hpos s)).symm
    _ ≤ Real.exp (B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H) := Real.exp_le_exp.2 (h1.trans h2)
    _ = Real.exp (B * Real.pi) * H ^ ⌈B⌉₊ := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hH0]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem parCont_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Continuous (TR.infGL F 2) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((TR.continuous_infEq F).prodMk continuous_const :
    Continuous fun x : TR.Rinf F => ((TR.infEq F x, 0) : InfiniteAdeleRing F × Af F))))

private theorem parCont_val {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    {c : ℝ → GL (Fin 2) (TR.Rinf F)} {Y : TR.Lie F 2} (h : Par c Y) :
    Continuous fun t => (c t).val := by
  have h0 : ContinuousAt (fun t => (c t).val) 0 := h.2.continuousAt
  refine continuous_iff_continuousAt.2 fun t => ?_
  have e : (fun s => (c s).val) = fun s => (c t).val * (c (s - t)).val := by
    funext s
    rw [← Units.val_mul, ← h.1, add_sub_cancel]
  rw [e]
  have hs : ContinuousAt (fun s : ℝ => s - t) t := (continuous_id.sub continuous_const).continuousAt
  have h0' : ContinuousAt (fun t => (c t).val) ((fun s : ℝ => s - t) t) := by
    simpa using h0
  exact continuousAt_const.mul (ContinuousAt.comp (f := fun s : ℝ => s - t) h0' hs)

theorem UpperTheory.ConvolutionTheory.R2.Ff.parCont :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ParCont F := by
  intro F _ _ _
  refine ⟨parCont_infGL F, fun c Y h => ?_⟩
  have h1 : c 0 = 1 := by
    have := h.1 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← h.1, add_neg_cancel, h1])
  have hv := parCont_val h
  refine ⟨h1, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, ?_⟩
  · have : (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val) = fun t => (c (-t)).val := by
      funext t; rw [hinv]
    change Continuous (fun t => ((c t)⁻¹ : GL (Fin 2) (TR.Rinf F)).val)
    rw [this]
    exact hv.comp continuous_neg
  · intro s t
    change c (-(s + t)) = c (-s) * c (-t)
    rw [neg_add, h.1]
  · have h2 : HasDerivAt (fun t => TR.toL (c t).val) Y (-(0 : ℝ)) := by simpa using h.2
    have := HasDerivAt.scomp (0 : ℝ) h2 (hasDerivAt_neg 0)
    simpa [Function.comp_def] using this
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem wt_mono' {F : Type} [Field F] [NumberField F]
    {K K' : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (h : K ⊆ K') (N : ℕ) (v : V4 F) :
    wt K N v ≤ wt K' N v := by
  unfold wt
  by_cases hv : finPartPi v ∈ K
  · rw [if_pos hv, if_pos (h hv)]
  · rw [if_neg hv]
    split_ifs
    · positivity
    · exact le_rfl

private theorem majorant {F : Type} [Field F] [NumberField F] {G : V4 F → ℂ}
    (hG : G ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    ∃ K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ v, ‖G v‖ ≤ B * wt K N v := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have hgc : Continuous g := ((mem_finiteSchwartzBruhatPi F).mp hg).1.continuous
    have hgs : HasCompactSupport g := ((mem_finiteSchwartzBruhatPi F).mp hg).2
    obtain ⟨C₂, h₂⟩ := hgc.bounded_above_of_compact_support hgs
    refine ⟨tsupport g, hgs.isCompact, fun N => ?_⟩
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_le_inv_one_add_pow φ N
    refine ⟨C₁ * max C₂ 0, mul_nonneg hC₁ (le_max_right _ _), fun v => ?_⟩
    simp only [schwartzBruhatTensorPi, norm_mul]
    by_cases hx : finPartPi v ∈ tsupport g
    · rw [wt, if_pos hx]
      calc ‖φ (infPartPi v)‖ * ‖g (finPartPi v)‖
          ≤ (C₁ * ((1 + ‖infPartPi v‖) ^ N)⁻¹) * max C₂ 0 :=
            mul_le_mul (h₁ _) ((h₂ _).trans (le_max_left _ _)) (norm_nonneg _)
              (mul_nonneg hC₁ (inv_nonneg.2 (by positivity)))
        _ = C₁ * max C₂ 0 * ((1 + ‖infPartPi v‖) ^ N)⁻¹ := by ring
    · rw [wt, if_neg hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  | zero =>
    exact ⟨∅, isCompact_empty, fun N => ⟨0, le_rfl, fun v => by simp⟩⟩
  | add G H _ _ hG hH =>
    obtain ⟨K₁, hK₁, h₁⟩ := hG
    obtain ⟨K₂, hK₂, h₂⟩ := hH
    refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun N => ?_⟩
    obtain ⟨B₁, hB₁, b₁⟩ := h₁ N
    obtain ⟨B₂, hB₂, b₂⟩ := h₂ N
    refine ⟨B₁ + B₂, add_nonneg hB₁ hB₂, fun v => ?_⟩
    calc ‖(G + H) v‖ ≤ ‖G v‖ + ‖H v‖ := norm_add_le _ _
      _ ≤ B₁ * wt K₁ N v + B₂ * wt K₂ N v := add_le_add (b₁ v) (b₂ v)
      _ ≤ B₁ * wt (K₁ ∪ K₂) N v + B₂ * wt (K₁ ∪ K₂) N v :=
          add_le_add (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_left N v) hB₁)
            (mul_le_mul_of_nonneg_left (wt_mono' Set.subset_union_right N v) hB₂)
      _ = (B₁ + B₂) * wt (K₁ ∪ K₂) N v := by ring
  | smul c G _ hG =>
    obtain ⟨K, hK, h⟩ := hG
    refine ⟨K, hK, fun N => ?_⟩
    obtain ⟨B, hB, b⟩ := h N
    refine ⟨‖c‖ * B, mul_nonneg (norm_nonneg c) hB, fun v => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b v) (norm_nonneg c)

theorem UpperTheory.ConvolutionTheory.R2.Ff.wtBound :
    ∀ (F : Type) [Field F] [NumberField F], WtBound F := by
  intro F _ _ φ
  refine ⟨continuous_of_mem_schwartzBruhatPi φ.2, ?_⟩
  obtain ⟨K, hK, h⟩ := majorant φ.2
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨B, _, b⟩ := h N
  exact ⟨B, fun _ _ v => b v⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), LCen W := by
  intro F E _ _ _ _ _ _ _ D W z
  refine ⟨LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_), nu_scalar z⟩
  have hη : W.η.1 (ideleNorm F E z)⁻¹ = 1 := by rw [map_inv, W.η_norm, inv_one]
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ :=
    (map_inv _ _).symm
  have hv : D.act (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ v =
      fun i => (((ideleNorm F E z)⁻¹ : (A F)ˣ) : A F) * v i := by
    rw [hs, D.act_scalar, map_inv]; rfl
  rw [W.L_apply, W.Om_m, nu_scalar, hv, hη, ab_inv, ab_pow]
  simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem fst_finGL' {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) k

private theorem det_fst {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    ((Matrix.GeneralLinearGroup.det (finGL E 2 k) : (A E)ˣ) : A E).1 = 1 := by
  have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)
  rw [fst_finGL'] at h
  exact h.symm.trans (by simp)

private theorem norm_fst {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : (A E)ˣ) (hx : (x : A E).1 = 1) : ((ideleNorm F E x : (A F)ˣ) : A F).1 = 1 := by
  funext v
  rw [ideleNorm_fst, hx]
  exact Finset.prod_eq_one fun w _ => map_one _

private theorem dM_of_fst {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (t : (A F)ˣ) (ht : (t : A F).1 = 1) :
    finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t := by
  have h := TR.infGL_mul_finGL (dM t)
  have h1 : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1 := by
    have ht' : TR.pInf F (t : A F) = 1 := by
      change (TR.infEq F).symm (t : A F).1 = 1
      rw [ht]; exact map_one _
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht']
  rw [h1, map_one, one_mul] at h
  exact h

theorem UpperTheory.ConvolutionTheory.R2.Ff.finTr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), FinTr F E := by
  intro F E _ _ _ _ _ _ _ _
  let κ : GL (Fin 2) (Af E) →* GL (Fin 2) (Af F) :=
    { toFun := fun k => Matrix.GeneralLinearGroup.map (pFin F) (dM (nu F (finGL E 2 k)))
      map_one' := by simp [nu]
      map_mul' := fun a b => by simp [nu, dM_mul] }
  refine ⟨κ, ?_, fun k => (dM_of_fst _ (norm_fst _ (det_fst k))).symm⟩
  have hp : Continuous (pFin F) := continuous_snd
  have hm : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (pFin F)) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id hp)
  have hf : Continuous (finGL E 2) := Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  exact hm.comp (continuous_dM.comp (continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp hf)))
end
