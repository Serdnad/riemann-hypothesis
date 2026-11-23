module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.TateThesis.Bundle006
public import GroundTheory.GlobalFields.TateThesis.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import GroundTheory.GlobalFields.Adele.Bundle002

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem ev_comp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    (fun g => ev m g j) = (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d) m j).1 := by
  induction m using TensorProduct.induction_on with
  | zero =>
    rw [(ev (E := E) (a := a) (d := d)).map_zero,
      (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).map_zero]
    rfl
  | tmul φ v =>
    funext g
    simp [mul_comm]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), Pi.add_apply, Submodule.coe_add, ← hx, ← hy]
    rfl

theorem evFacts : EvFacts := by
  intro E _ _ _ a d
  refine ⟨fun m m' h => ?_, fun m j => ?_, fun f hf => ?_⟩
  · apply (TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).injective
    funext j
    apply Subtype.ext
    rw [← ev_comp, ← ev_comp, h]
  · rw [ev_comp]
    exact Subtype.property _
  · refine ⟨(TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩, ?_⟩
    funext g j
    have := congrFun (ev_comp ((TensorProduct.piScalarRight ℂ ℂ (Sm E a) (Fin d)).symm fun j => ⟨_, hf j⟩) j) g
    rw [LinearEquiv.apply_symm_apply] at this
    exact this

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def detProd (p : HV E a) : ℝ := ∏ w : InfinitePlace E, ((Matrix.of p.1).det w).re

private theorem detProd_sand (g : GL (Fin a) (Cinf E)) (p : HV E a) :
    detProd (sand g p) = (∏ w : InfinitePlace E, ‖g.val.det w‖ ^ 2) * detProd p := by
  unfold detProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [sand_val, det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_right_comm]
  have h : (g.val.det * star g.val.det * (Matrix.of p.1).det) w =
      ((‖g.val.det w‖ ^ 2 : ℝ) : ℂ) * (Matrix.of p.1).det w := by
    rw [Pi.mul_apply, Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.re_ofReal_mul]

private theorem contDiff_detProd : ContDiff ℝ ∞ (detProd (E := E) (a := a)) := by
  unfold detProd
  refine contDiff_prod fun w _ => Complex.reCLM.contDiff.comp (f := fun p : HV E a => (Matrix.of p.1).det w) ?_
  simp only [det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  have h : ContDiff ℝ ∞ (fun p : HV E a => p.1) := (HV E a).subtypeL.contDiff
  exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 h _) _) _

private theorem detProd_smul (t : ℝ) (p : HV E a) :
    detProd (t • p) = t ^ (a * Fintype.card (InfinitePlace E)) * detProd p := by
  unfold detProd
  have h : ∀ w : InfinitePlace E, ((Matrix.of (t • p).1).det w).re = t ^ a * ((Matrix.of p.1).det w).re := by
    intro w
    have h1 : Matrix.of (t • p).1 = (algebraMap ℝ (Cinf E) t) • Matrix.of p.1 := by
      rw [algebraMap_smul]; rfl
    rw [h1, det_smul, Fintype.card_fin, ← map_pow, ← Algebra.smul_def, Pi.smul_apply, Complex.smul_re, smul_eq_mul]
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_mul]

theorem normInf : NormInf := by
  intro E _ _ _ a
  refine ⟨detProd, contDiff_detProd, ?_, detProd_smul, ?_⟩
  · rintro p ⟨g, rfl⟩
    rw [detProd_sand]
    have h1 : detProd (hOne E a) = 1 := by
      unfold detProd
      rw [hOne_val, det_one]
      simp
    rw [h1, mul_one]
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2
    have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact (hu.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero
  · intro γ p
    rw [detProd_sand]
    congr 1
    have hd : (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val.det = pInf E (algebraMap E (Ad E) γ.val.det) := by
      rw [RingHom.map_det, RingHom.map_det]
      rfl
    rw [hd, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq, IsTotallyComplex.mult_eq]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped ComplexOrder MatrixOrder

namespace UpperTheory.V.Lit.Dr

private theorem posDef_iff_mul_star {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    M.PosDef ↔ ∃ B : Matrix n n ℂ, IsUnit B ∧ M = B * star B := by
  open scoped Matrix.Norms.L2Operator in
  rw [← Matrix.isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self]

private theorem pi_iff {n ι : Type} [Fintype n] [DecidableEq n] (M : Matrix n n (ι → ℂ)) :
    (∃ g : GL n (ι → ℂ), g.val * 1 * star g.val = M) ↔ ∀ w, (Matrix.of fun i j => M i j w).PosDef := by
  simp only [posDef_iff_mul_star, mul_one]
  constructor
  · rintro ⟨g, rfl⟩ w
    refine ⟨g.val.map (Pi.evalRingHom (fun _ => ℂ) w), ?_, ?_⟩
    · exact g.isUnit.map (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix
    · ext i j
      simp [Matrix.mul_apply, Finset.sum_apply]
  · intro h
    choose B hB hM using h
    have hu : IsUnit (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
      intro w
      have := RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) (Matrix.of fun i j w => B w i j : Matrix n n (ι → ℂ))
      rw [Pi.evalRingHom_apply] at this
      rw [this, ← Matrix.isUnit_iff_isUnit_det]
      exact hB w
    refine ⟨hu.unit, ?_⟩
    ext i j w
    have := congrFun (congrFun (hM w) i) j
    simp only [Matrix.of_apply] at this
    rw [this]
    simp [Matrix.mul_apply, Finset.sum_apply]

theorem conePos : ConePos := by
  intro E _ _ a p
  refine Iff.trans ?_ (pi_iff (Matrix.of p.1))
  exact exists_congr fun g => Subtype.ext_iff

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem hasDerivAt_evaluation_lie {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a)
    (X : Lie E a) (c : ℝ → GL (Fin a) (Cinf E)) (h0 : c 0 = 1) (hX : HasDerivAt (fun t => toL (c t).val) X 0)
    (h : GA E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    HasDerivAt (fun t => Ξ.mat (c t) *ᵥ ev m (h * infGL E a (c t))) (ev (smLie Ξ X m) h) 0 := by
  induction m using TensorProduct.induction_on with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : Fin Ξ.d → ℂ)
  | add x y hx hy =>
    simpa only [map_add (f := _), Pi.add_apply, Matrix.mulVec_add] using hx.fun_add hy
  | tmul φ v =>
    have h1 := GlobalTheory.CuspRep.hasDerivAt_curve φ h c X h0 hX
    have h2 : HasDerivAt (fun t => Ξ.mat (c t) *ᵥ v) (Ξ.dmat X *ᵥ v) 0 :=
      hasDerivAt_pi.2 fun j => HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        (Ξ.hasDerivAt_curve c X h0 hX j i).mul_const (v i)
    have h3 := h1.fun_smul h2
    simp only [h0, map_one, mul_one, Matrix.one_mulVec] at h3
    have h4 : ev (smLie Ξ X (φ ⊗ₜ[ℂ] v)) h = φ.1 h • Ξ.dmat X *ᵥ v + lieD X φ.1 h • v := by
      change ev ((lie E a X φ) ⊗ₜ[ℂ] v + φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v)) h = _
      rw [map_add (f := _), Pi.add_apply, ev_tmul, ev_tmul, add_comm]
      rfl
    rw [h4]
    simpa only [ev_tmul, Matrix.mulVec_smul] using h3

theorem evDeriv : EvDeriv := by
  intro E _ _ _ a Ξ m g x c X h0 hX
  have h1 := (mulVecL (Ξ.mat g)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_evaluation_lie Ξ X c h0 hX (infGL E a g * finGL E a x) m)
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : infGL E a (g * c t) * finGL E a x = infGL E a g * finGL E a x * infGL E a (c t) := by
    rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
  simp only [Function.comp, mulVecL_apply, e, map_mul (Ξ.mat), Matrix.mulVec_mulVec]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af Filter Topology
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def jor (X Y : HV E a) : HV E a :=
  ⟨toL (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1), by
    have hX : star (Matrix.of X.1) = Matrix.of X.1 := X.2
    have hY : star (Matrix.of Y.1) = Matrix.of Y.1 := Y.2
    change star (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) =
      Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1
    rw [star_add, star_mul, star_mul, hX, hY, add_comm]⟩

private def jorL : HV E a →ₗ[ℝ] HV E a →ₗ[ℝ] HV E a :=
  LinearMap.mk₂ ℝ jor
    (fun X X' Y => Subtype.ext (by
      change (Matrix.of X.1 + Matrix.of X'.1) * Matrix.of Y.1 + Matrix.of Y.1 * (Matrix.of X.1 + Matrix.of X'.1) =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X'.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X'.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change (c • Matrix.of X.1) * Matrix.of Y.1 + Matrix.of Y.1 * (c • Matrix.of X.1) =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))
    (fun X Y Y' => Subtype.ext (by
      change Matrix.of X.1 * (Matrix.of Y.1 + Matrix.of Y'.1) + (Matrix.of Y.1 + Matrix.of Y'.1) * Matrix.of X.1 =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X.1 * Matrix.of Y'.1 + Matrix.of Y'.1 * Matrix.of X.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change Matrix.of X.1 * (c • Matrix.of Y.1) + (c • Matrix.of Y.1) * Matrix.of X.1 =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))

private def jorC : HV E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := HV E a) (F' := HV E a)).toLinearMap ∘ₗ jorL)

private theorem jorC_val (X Y : HV E a) :
    Matrix.of (jorC X Y).1 = Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1 := rfl

private def sq2 (X : HV E a) : HV E a := (1 / 2 : ℝ) • jorC X X

private theorem square_map_val (X : HV E a) : Matrix.of (sq2 X).1 = Matrix.of X.1 * Matrix.of X.1 := by
  change (1 / 2 : ℝ) • Matrix.of (jorC X X).1 = _
  rw [jorC_val, ← two_smul ℝ, smul_smul]; norm_num

private theorem square_map_one : sq2 (hOne E a) = hOne E a := by
  apply Subtype.ext
  change Matrix.of (sq2 (hOne E a)).1 = Matrix.of (hOne E a).1
  rw [square_map_val, hOne_val, mul_one]

private theorem square_map_contDiff : ContDiff ℝ ∞ (sq2 (E := E) (a := a)) :=
  ((jorC (E := E) (a := a)).contDiff.clm_apply contDiff_id).const_smul _

private def dbl : HV E a ≃L[ℝ] HV E a :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := HV E a) (Units.mk0 (2 : ℝ) two_ne_zero)

private theorem square_map_hasFDerivAt : HasFDerivAt (sq2 (E := E) (a := a)) (dbl (E := E) (a := a) : HV E a →L[ℝ] HV E a) (hOne E a) := by
  have h := (((jorC (E := E) (a := a)).hasFDerivAt (x := hOne E a)).clm_apply (hasFDerivAt_id (hOne E a))).const_smul (1 / 2 : ℝ)
  refine HasFDerivAt.congr_fderiv h ?_
  refine ContinuousLinearMap.ext fun H => Subtype.ext ?_
  change (1 / 2 : ℝ) • (Matrix.of (jorC (hOne E a) H).1 + Matrix.of (jorC H (hOne E a)).1) = (2 : ℝ) • Matrix.of H.1
  rw [jorC_val, jorC_val, hOne_val, mul_one, one_mul]
  module

private theorem exists_sqrt : ∃ σ : HV E a → HV E a, ContDiffAt ℝ ∞ σ (hOne E a) ∧ σ (hOne E a) = hOne E a ∧
    ∀ᶠ p in 𝓝 (hOne E a), sq2 (σ p) = p := by
  have hc : ContDiffAt ℝ ∞ (sq2 (E := E) (a := a)) (hOne E a) := square_map_contDiff.contDiffAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse square_map_hasFDerivAt hn, ?_, ?_, ?_⟩
  · have := hc.to_localInverse square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := hc.localInverse_apply_image square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := (hc.hasStrictFDerivAt' square_map_hasFDerivAt hn).eventually_right_inverse
    rwa [square_map_one] at this

private theorem ev_unit : ∀ᶠ X in 𝓝 (hOne E a), IsUnit (Matrix.of X.1) := by
  have hc : Continuous fun X : HV E a => (Matrix.of X.1).det :=
    Continuous.matrix_det (A := fun X : HV E a => Matrix.of X.1) continuous_subtype_val
  have h1 : (Matrix.of (hOne E a).1).det ∈ {x : Cinf E | IsUnit x} := by
    rw [hOne_val, det_one]; exact isUnit_one
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds h1)] with X hX
  exact (Matrix.isUnit_iff_isUnit_det _).2 hX

private def lmul (g : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (g * Matrix.of X.1)
      map_add' := fun X Y => by
        change g * (Matrix.of X.1 + Matrix.of Y.1) = g * Matrix.of X.1 + g * Matrix.of Y.1
        rw [mul_add]
      map_smul' := fun c X => by
        change g * (c • Matrix.of X.1) = c • (g * Matrix.of X.1)
        rw [mul_smul_comm] }

open Classical in
theorem locSec : LocSec := by
  rintro E _ _ a p₀ ⟨g, rfl⟩
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := exists_sqrt (E := E) (a := a)
  have h0 : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hq : Tendsto (sand g⁻¹) (𝓝 (sand g (hOne E a))) (𝓝 (hOne E a)) := by
    have := (sand g⁻¹).continuous.tendsto (sand g (hOne E a))
    rwa [h0] at this
  have hs : Tendsto σ (𝓝 (hOne E a)) (𝓝 (hOne E a)) := by
    have := hσ.continuousAt.tendsto
    rwa [hσ1] at this
  have hu := (hs.comp hq).eventually ev_unit
  let u : HV E a → GL (Fin a) (Cinf E) := fun X => if h : IsUnit (Matrix.of X.1) then h.unit else 1
  have hval : ∀ X : HV E a, IsUnit (Matrix.of X.1) → (u X).val = Matrix.of X.1 := fun X h => by
    simp only [u, dif_pos h, IsUnit.unit_spec]
  refine ⟨fun p => g * u (σ (sand g⁻¹ p)), ?_, ?_⟩
  · have h1 : ContDiffAt ℝ ∞ (fun p => σ (sand g⁻¹ p)) (sand g (hOne E a)) :=
      ContDiffAt.comp (g := σ) _ (h0.symm ▸ hσ) (sand g⁻¹).contDiff.contDiffAt
    refine ((lmul g.val).contDiff.contDiffAt.comp _ h1).congr_of_eventuallyEq ?_
    filter_upwards [hu] with p hp
    rw [Units.val_mul, hval (σ (sand g⁻¹ p)) hp]; rfl
  · filter_upwards [hu, hq.eventually hσ2] with p hp hp2
    have h2 : sand (u (σ (sand g⁻¹ p))) (hOne E a) = sand g⁻¹ p := by
      rw [← hp2]
      apply Subtype.ext
      change Matrix.of (sand _ _).1 = Matrix.of (sq2 _).1
      have hX : star (Matrix.of (σ (sand g⁻¹ p)).1) = Matrix.of (σ (sand g⁻¹ p)).1 := (σ (sand g⁻¹ p)).2
      rw [sand_val, square_map_val, hOne_val, mul_one, hp2, hval (σ (sand g⁻¹ p)) hp, hX]
    rw [map_mul, ContinuousLinearMap.mul_apply, h2, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end UpperTheory.V.Lit.Dr
end
end

section

open UpperTheory.V.Lit.Dr

private theorem one_of_compact {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) (hU : IsCompact (U : Set G))
    (φ : G → ℝ) (hc : Continuous φ) (hp : ∀ g, 0 < φ g) (hm : ∀ g h, φ (g * h) = φ g * φ h) :
    ∀ u ∈ U, φ u = 1 := by
  obtain ⟨m, hmU, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn
  have hle : ∀ u ∈ U, φ u ≤ 1 := fun u hu => by
    have h : φ (u * m) ≤ φ m := hmax (U.mul_mem hu hmU)
    rw [hm] at h
    have := hp m
    nlinarith
  intro u hu
  have h1 : φ 1 = 1 := by
    have h := hm 1 1
    rw [mul_one] at h
    have := hp 1
    nlinarith
  have h2 := hm u u⁻¹
  rw [mul_inv_cancel, h1] at h2
  have h3 := hle u hu
  have h4 := hle _ (U.inv_mem hu)
  have h5 := hp u
  nlinarith

open NumberField Matrix GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CuspRep in
theorem UpperTheory.V.Lit.Dr.normFin :
    NormFin := by
  intro E _ _ a U hU
  let φ : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) → ℝ :=
    fun g => finiteModule (ofFinite (K := E) (GeneralLinearGroup.det g))
  have hc : Continuous φ :=
    continuous_finiteModule.comp (continuous_ofFinite.comp GeneralLinearGroup.continuous_det)
  have hp : ∀ g, 0 < φ g := fun g => finiteModule_pos _
  have hm : ∀ g h, φ (g * h) = φ g * φ h := fun g h => by
    simp only [φ, map_mul, finiteModule_mul]
  have h1 := one_of_compact U hU φ hc hp hm
  have hγ : ∀ γ : GL (Fin a) E, φ (GeneralLinearGroup.map (algebraMap E _) γ) =
      |((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)|⁻¹ := fun γ => by
    have e : φ (GeneralLinearGroup.map (algebraMap E _) γ) =
        finiteModule (IdeleGroup.diagonal E (GeneralLinearGroup.det γ)) := by
      have hd : ((GeneralLinearGroup.det (GeneralLinearGroup.map
          (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ)) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) =
          algebraMap E _ γ.val.det := by
        rw [RingHom.map_det]; rfl
      have h2 : ((ofFinite (K := E) (GeneralLinearGroup.det (GeneralLinearGroup.map
          (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ))).val).2 = algebraMap E _ γ.val.det :=
        (congrArg Units.val (toFinite_ofFinite _)).trans hd
      simp only [φ, finiteModule, h2]
      rfl
    rw [e, finiteModule_diagonal, FinitePlace.prod_eq_inv_abs_norm (GeneralLinearGroup.det γ).ne_zero]
    simp
  refine ⟨Quotient.lift φ fun g h hgh => ?_, fun s => ?_, fun γ s => ?_⟩
  · have h2 := h1 _ (QuotientGroup.leftRel_apply.1 hgh)
    have h3 := hm g (g⁻¹ * h)
    rw [mul_inv_cancel_left, h2, mul_one] at h3
    exact h3.symm
  · induction s using QuotientGroup.induction_on with
    | H g => exact hp g
  · induction s using QuotientGroup.induction_on with
    | H g => exact (hm _ g).trans (by rw [hγ]; rfl)
end

section

open NumberField IsDedekindDomain

theorem UpperTheory.V.Lit.Dr.finField : UpperTheory.V.Lit.Dr.FinField := by
  intro E _ _ C T hT
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact (K := E) hT
  have hdE : algebraMap (𝓞 E) E d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ
    ((∑ w : InfinitePlace E, w (algebraMap (𝓞 E) E d)) * C)
  refine Set.Finite.of_finite_image (f := fun x => algebraMap (𝓞 E) E d * x) (hfin.subset ?_)
    (mul_right_injective₀ hdE).injOn
  rintro _ ⟨x, ⟨hx, hxT⟩, rfl⟩
  refine ⟨?_, fun φ => ?_⟩
  · have h := hd _ hxT
    rw [← map_mul] at h
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (algebraMap (𝓞 E) E d * x) fun v => by
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v]
        exact GroundTheory.Global.mem_integralFiniteAdeles.1 h v
    beta_reduce
    rw [← hz]
    exact RingOfIntegers.isIntegral_coe _
  · beta_reduce
    rw [← InfinitePlace.apply, map_mul]
    exact mul_le_mul
      (Finset.single_le_sum (f := fun w : InfinitePlace E => w (algebraMap (𝓞 E) E d))
        (fun w _ => apply_nonneg w _) (Finset.mem_univ _))
      (hx _) (apply_nonneg _ _) (Finset.sum_nonneg fun w _ => apply_nonneg w _)
end
