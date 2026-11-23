module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer
import GroundTheory.AutomorphicForms.Bundle012
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle008
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem infGL_scalarE {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (u : (Cinf E)ˣ) :
    infGL E 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (infId E u) := by
  have h1 : pInf E (infId E u).val = u.val := by
    change pInf E (1 - sInf E 1 + sInf E _) = _
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    simp [h]
  have h2 : pFin E (infId E u).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem det_mul_inv (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    y.val.det w * (y⁻¹).val.det w = 1 := by
  have h : y.val.det * (y⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  exact congrFun h w

private theorem det_ne (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : y.val.det w ≠ 0 := fun h => by
  have := det_mul_inv y w
  rw [h, zero_mul] at this
  exact zero_ne_one this

private noncomputable def nd (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : ℝ := Real.sqrt ‖y.val.det w‖

private theorem nd_pos (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : 0 < nd y w :=
  Real.sqrt_pos.2 (norm_pos_iff.2 (det_ne y w))

private theorem nd_sq (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : nd y w ^ 2 = ‖y.val.det w‖ :=
  Real.sq_sqrt (norm_nonneg _)

private theorem nd_inv (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) : (nd y w)⁻¹ = nd y⁻¹ w := by
  have h : ‖y.val.det w‖ * ‖(y⁻¹).val.det w‖ = 1 := by
    rw [← norm_mul, det_mul_inv, norm_one]
  have h' : nd y w * nd y⁻¹ w = 1 := by
    rw [nd, nd, ← Real.sqrt_mul (norm_nonneg _), h, Real.sqrt_one]
  exact (eq_inv_of_mul_eq_one_right h').symm

private theorem entry_le (x : Matrix (Fin 2) (Fin 2) (Cinf E)) (i j : Fin 2) (w : InfinitePlace E) :
    ‖x i j w‖ ≤ ‖toL x‖ :=
  (norm_le_pi_norm (x i j) w).trans ((norm_le_pi_norm (toL x i) j).trans (norm_le_pi_norm (toL x) i))

private theorem det_le (x : Matrix (Fin 2) (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    ‖x.det w‖ ≤ 2 * ‖toL x‖ ^ 2 := by
  have e := entry_le x
  have n0 : 0 ≤ ‖toL x‖ := norm_nonneg _
  rw [Matrix.det_fin_two, Pi.sub_apply, Pi.mul_apply, Pi.mul_apply]
  calc _ ≤ ‖x 0 0 w * x 1 1 w‖ + ‖x 0 1 w * x 1 0 w‖ := norm_sub_le _ _
    _ = ‖x 0 0 w‖ * ‖x 1 1 w‖ + ‖x 0 1 w‖ * ‖x 1 0 w‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖toL x‖ * ‖toL x‖ + ‖toL x‖ * ‖toL x‖ := by
      gcongr <;> apply e
    _ = _ := by ring

private theorem nd_le (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    nd y w ≤ 2 * ‖toL y.val‖ := by
  have n0 : 0 ≤ ‖toL y.val‖ := norm_nonneg _
  refine Real.sqrt_le_iff.2 ⟨by positivity, (det_le y.val w).trans ?_⟩
  nlinarith [sq_nonneg ‖toL y.val‖]

private noncomputable def sg (y : GL (Fin 2) (Cinf E)) : (Cinf E)ˣ where
  val := fun w => ((nd y w : ℝ) : ℂ)
  inv := fun w => (((nd y w)⁻¹ : ℝ) : ℂ)
  val_inv := by
    funext w
    change ((nd y w : ℝ) : ℂ) * (((nd y w)⁻¹ : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (nd_pos y w).ne', Complex.ofReal_one]
  inv_val := by
    funext w
    change (((nd y w)⁻¹ : ℝ) : ℂ) * ((nd y w : ℝ) : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (nd_pos y w).ne', Complex.ofReal_one]

private theorem continuous_nd (w : InfinitePlace E) : Continuous fun y : GL (Fin 2) (Cinf E) => nd y w :=
  Real.continuous_sqrt.comp (continuous_norm.comp
    ((continuous_apply w).comp (Continuous.matrix_det Units.continuous_val)))

private theorem continuous_sg : Continuous (sg (E := E)) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun w => ?_, continuous_pi fun w => ?_⟩
  · exact Complex.continuous_ofReal.comp (continuous_nd w)
  · exact Complex.continuous_ofReal.comp ((continuous_nd w).inv₀ fun y => (nd_pos y w).ne')

private theorem sg_le (y : GL (Fin 2) (Cinf E)) : ‖(sg y).val‖ ≤ 2 * ‖toL y.val‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => by
    change ‖((nd y w : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (nd_pos y w).le]
    exact nd_le y w

private theorem sg_inv_le (y : GL (Fin 2) (Cinf E)) : ‖(sg y)⁻¹.val‖ ≤ 2 * ‖toL (y⁻¹).val‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => by
    change ‖(((nd y w)⁻¹ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, nd_inv, Real.norm_of_nonneg (nd_pos y⁻¹ w).le]
    exact nd_le y⁻¹ w

private theorem sc_entry (s : (Cinf E)ˣ) (y : GL (Fin 2) (Cinf E)) (i j : Fin 2) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) s * y).val i j = s.val * y.val i j := by
  rw [Units.val_mul]
  change ((Matrix.diagonal (fun _ => s.val) : Matrix (Fin 2) (Fin 2) (Cinf E)) * y.val) i j = _
  rw [Matrix.diagonal_mul]

private theorem sc_le (s : (Cinf E)ˣ) (y : GL (Fin 2) (Cinf E)) :
    ‖toL (Matrix.GeneralLinearGroup.scalar (Fin 2) s * y).val‖ ≤ ‖s.val‖ * ‖toL y.val‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => by
    change ‖(Matrix.GeneralLinearGroup.scalar (Fin 2) s * y).val i j‖ ≤ _
    rw [sc_entry]
    refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact (norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)

private theorem tau_det (y : GL (Fin 2) (Cinf E)) (w : InfinitePlace E) :
    ‖(Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y).val.det w‖ = 1 := by
  have h : (Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹).val.det w = (((nd y w)⁻¹ : ℝ) : ℂ) ^ 2 := by
    change (Matrix.diagonal fun _ => (sg y)⁻¹.val).det w = _
    rw [Matrix.det_diagonal, Fin.prod_univ_two, Pi.mul_apply, sq]
    rfl
  rw [Units.val_mul, Matrix.det_mul, Pi.mul_apply, h, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (nd_pos y w).le), ← nd_sq, inv_pow,
    inv_mul_cancel₀ (pow_pos (nd_pos y w) 2).ne']

private theorem continuous_sc :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) : (Cinf E)ˣ → GL (Fin 2) (Cinf E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val)
  · have e : (fun x : (Cinf E)ˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) x)⁻¹ : GL (Fin 2) (Cinf E)) :
        Matrix (Fin 2) (Fin 2) (Cinf E))) = fun x => Matrix.diagonal fun _ => (x⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [e]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => Units.continuous_val.comp continuous_inv)

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.dec :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), Dec F E := by
  intro F E _ _ _ _ _ _ _ D
  refine ⟨sg, fun y => Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y, continuous_sg,
    (continuous_sc.comp continuous_sg.inv).mul continuous_id, fun y => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← infGL_scalarE, ← map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · exact UpperTheory.ConvolutionTheory.R2.Ff.oneOf F E D _ fun w => tau_det y w
  · have hA := (sc_le (sg y)⁻¹ y).trans (mul_le_mul_of_nonneg_right (sg_inv_le y) (norm_nonneg _))
    have hB : ‖toL ((Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y)⁻¹).val‖ ≤
        2 * ‖toL y.val‖ * ‖toL (y⁻¹).val‖ := by
      have e : (Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y)⁻¹ * y)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (sg y) * y⁻¹ := by
        rw [_root_.mul_inv_rev, ← map_inv, inv_inv]
        exact (Matrix.GeneralLinearGroup.scalar_commute _ _).symm
      rw [e]
      exact (sc_le (sg y) y⁻¹).trans (mul_le_mul_of_nonneg_right (sg_le y) (norm_nonneg _))
    have a0 : 0 ≤ ‖toL y.val‖ := norm_nonneg _
    have b0 : 0 ≤ ‖toL (y⁻¹).val‖ := norm_nonneg _
    unfold Ht
    nlinarith [mul_nonneg a0 b0, sq_nonneg ‖toL y.val‖, sq_nonneg ‖toL (y⁻¹).val‖]
  · have hs := sg_le y
    have hi := sg_inv_le y
    unfold Ht
    linarith
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.vol :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Vol F := by
  intro F _ _ _ M₀
  exact UpperTheory.ConvolutionTheory.R2.M.volD F M₀
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem der_nU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (b : A F) :
    Der (fun s => W.Om (nU b) (Ψ s)) (fun s => W.Om (nU b) (Ψ' s)) := by
  intro t v
  simp only [W.Om_n]
  exact (h t v).const_mul _

private theorem integrable_mul_char {F : Type} [Field F] [NumberField F] (φ : S4 F)
    {c : V4 F → ℂ} (hc : Continuous c) (hn : ∀ y, ‖c y‖ = 1) :
    Integrable (fun y => φ.1 y * c y) (adeleMeasurePi F) := by
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨hφ, K, hK, hB⟩ := wtBound F φ
  obtain ⟨B, hB⟩ := hB N
  refine Integrable.mono' ((hN K hK).const_mul B) (hφ.mul hc).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, hn, mul_one]
  exact hB () (Set.mem_univ _) y

private theorem der_wW {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D) {Ψ Ψ' : ℝ → S4 F}
    (h : Der Ψ Ψ') (hd : ∀ t, Dom (Metric.ball t 1) fun s => (Ψ' s).1) :
    Der (fun s => W.Om (wW F) (Ψ s)) (fun s => W.Om (wW F) (Ψ' s)) := by
  intro t v
  simp only [W.Om_w, ft4]
  obtain ⟨N, hN⟩ := wtInt F
  obtain ⟨K, hK, hB⟩ := hd t
  obtain ⟨B, hB⟩ := hB N
  have e : ∀ i, Continuous fun y : V4 F => y i := fun i => continuous_apply i
  have cB : Continuous fun y : V4 F => B4 D.δ y v :=
    ((continuous_const.mul (((e 2).mul continuous_const).sub
      (continuous_const.mul ((e 3).mul continuous_const)))).sub
      ((e 1).mul continuous_const)).sub ((e 0).mul continuous_const)
  have cψ : Continuous fun y : V4 F => ψ (B4 D.δ y v) := continuous_ψ.comp cB
  have cont : ∀ φ : S4 F, Continuous fun y => φ.1 y * ψ (B4 D.δ y v) :=
    fun φ => (wtBound F φ).1.mul cψ
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => (Ψ s).1 y * ψ (B4 D.δ y v)) (F' := fun s y => (Ψ' s).1 y * ψ (B4 D.δ y v))
    (bound := fun y => B * wt K N y) (μ := adeleMeasurePi F)
    (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s => (cont (Ψ s)).aestronglyMeasurable)
    (integrable_mul_char (Ψ t) cψ fun y => norm_ψ _)
    (cont (Ψ' t)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs => by
      rw [norm_mul, norm_ψ, mul_one]
      exact hB s hs y)
    ((hN K hK).const_mul B)
    (Eventually.of_forall fun y s _ => (h s y).mul_const _)).2

theorem UpperTheory.ConvolutionTheory.R2.Ff.omDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmDer W := by
  intro F E _ _ _ _ _ _ _ D W Ψ Ψ' h hd g
  have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
    rw [(gen F).1]
    trivial
  have wstep : ∀ y, Der (fun s => W.Om y (Ψ s)) (fun s => W.Om y (Ψ' s)) →
      Der (fun s => W.Om (wW F * y) (Ψ s)) (fun s => W.Om (wW F * y) (Ψ' s)) := by
    intro y hy
    simp only [map_mul, Module.End.mul_apply]
    exact der_wW W hy (hd y)
  induction hg using Subgroup.closure_induction_left with
  | one => simpa using h
  | mul_left x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih b
    · rw [Set.mem_singleton_iff.1 hx]
      exact wstep y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with ⟨b, rfl⟩ | hx
    · rw [← nU_neg]
      simp only [map_mul, Module.End.mul_apply]
      exact der_nU W ih (-b)
    · rw [Set.mem_singleton_iff.1 hx, wW_inv, ← wW_mul_wW, mul_assoc, mul_assoc]
      exact wstep _ (wstep _ (wstep y ih))
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.dLDer :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), DLDer O W := by
  intro F E _ _ _ _ _ _ _ D O W Y hY
  have hOne : ∀ t, One F (ex Y t) := by
    intro t
    refine oneOf F E D (ex Y t) fun w => ?_
    rw [(exPar E Y).2.2.2.1 hY t]
    simp
  have hL : ∀ (s : ℝ) (ψ : S4 F) (u : V4 F),
      (W.L (infGL E 2 (ex Y s)) ψ).1 u = ψ.1 (D.act (infGL E 2 (ex Y s))⁻¹ u) := by
    intro s ψ u
    have h1 : nu F (infGL E 2 (ex Y s)) = 1 := hOne s
    rw [W.L_apply, h1]
    have h2 : ab (1 : (A F)ˣ) = 1 := by simp [ab]
    rw [h2]
    simp
  refine ⟨hOne, fun φ t v => ?_⟩
  set v' : V4 F := D.act (infGL E 2 (ex Y t))⁻¹ v with hv'
  obtain ⟨x, x', hx0, hx, hact, hH⟩ := vfDer F E D Y v'
  have h0 : HasDerivAt (fun s => φ.1 fun i => v' i + TR.sInf F (x s i))
      ((O.dL D Y φ).1 v') 0 := by
    have h := sDiff F O φ v' x x' hx0 hx
    rwa [vfOps F E D O Y hY v' x' hH φ] at h
  have hshift : ∀ s, (W.L (infGL E 2 (ex Y (t + s))) φ).1 v =
      φ.1 fun i => v' i + TR.sInf F (x s i) := by
    intro s
    rw [(exPar E Y).1 t s, map_mul, map_mul]
    change (W.L (infGL E 2 (ex Y t)) (W.L (infGL E 2 (ex Y s)) φ)).1 v = _
    rw [hL t, hL s, hact s]
  have h1 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + s))) φ).1 v)
      ((O.dL D Y φ).1 v') 0 := by
    simpa only [hshift] using h0
  have h2 : HasDerivAt (fun s => (W.L (infGL E 2 (ex Y (t + (s - t)))) φ).1 v)
      ((O.dL D Y φ).1 v') t :=
    HasDerivAt.comp_sub_const t t (by simpa using h1)
  rw [hL t (O.dL D Y φ) v]
  simpa only [add_sub_cancel] using h2
end
