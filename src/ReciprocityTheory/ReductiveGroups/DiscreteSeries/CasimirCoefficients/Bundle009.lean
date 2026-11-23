module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle006
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def upPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a < b then B a b else 0

def lowPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if b < a then B a b else 0

def diagPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => B a a

lemma decomp_up (B : Matrix (Fin n) (Fin n) ℂ) :
    B = lowMinusUp B + (2 : ℂ) • upPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, lowMinusUp, upPart, diagPart, Matrix.of_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_neg (lt_asymm h), if_neg h.ne']
    ring

lemma decomp_low (B : Matrix (Fin n) (Fin n) ℂ) :
    B = -lowMinusUp B + (2 : ℂ) • lowPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, lowMinusUp, lowPart, diagPart,
    Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_pos h, if_neg h.ne']
    ring

lemma single_eq_smul (a b : Fin n) (c : ℂ) :
    Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma dtau_upPart_w (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    T.dτ (upPart B) T.w = 0 := by

  rw [Matrix.matrix_eq_sum_single (upPart B), map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun a _ => ?_)

  rw [map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
  simp only [upPart, Matrix.of_apply]
  split_ifs with h
  · by_cases he : ε a = ε b
    · rw [T.w_hw a b h he, smul_zero]
    · rw [hB a b he, zero_smul]
  · rw [zero_smul]

lemma dtau_diagPart_w (T : KType ε Λ) (B : Matrix (Fin n) (Fin n) ℂ) :
    T.dτ (diagPart B) T.w = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • T.w := by

  rw [Matrix.matrix_eq_sum_single (diagPart B), map_sum, _root_.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)

  rw [map_sum, _root_.sum_apply, Finset.sum_eq_single a]
  · rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply, T.w_wt, smul_smul]
    simp only [diagPart, Matrix.diagonal_apply_eq]
    rw [mul_comm]
  · intro b _ hb
    rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
    simp only [diagPart, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    rw [zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma isBlock_lowPart {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) : IsBlock ε (lowPart B) := by
  intro a b h
  simp only [lowPart, Matrix.of_apply]
  split_ifs
  · exact hB a b h
  · rfl

lemma isBlock_diagPart (B : Matrix (Fin n) (Fin n) ℂ) : IsBlock ε (diagPart B) := by
  intro a b h
  have hab : a ≠ b := by
    rintro rfl
    exact h rfl
  simp only [diagPart]
  exact Matrix.diagonal_apply_ne _ hab

lemma lowPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (lowPart B)ᴴ = upPart B := by
  ext a b
  simp only [Matrix.conjTranspose_apply, lowPart, upPart, Matrix.of_apply]
  split_ifs
  · have h := congrFun (congrFun hBh a) b
    rw [Matrix.conjTranspose_apply] at h
    exact h
  · exact star_zero _

lemma diagPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (diagPart B)ᴴ = diagPart B := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [diagPart]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    have h' := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h'
    exact h'
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, star_zero]

theorem tau_part {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : IsBlock ε B) (hBh : Bᴴ = B) :
    T.dτ B * projW T + projW T * T.dτ B =
      (T.dτ (lowMinusUp B) * projW T - projW T * T.dτ (lowMinusUp B)) +
        (2 * ∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
  have hP : ∀ v, projW T v = inner ℂ T.w v • T.w := fun v => by
    simp only [projW, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hBaa : ∀ a, (starRingEnd ℂ) (B a a) = B a a := fun a => by
    have h := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h
    exact h
  have hc : (starRingEnd ℂ) (∑ a, ((Λ a : ℝ) : ℂ) * B a a) = ∑ a, ((Λ a : ℝ) : ℂ) * B a a := by

    simp only [map_sum, map_mul, Complex.conj_ofReal, hBaa]
  have h1 : T.dτ (upPart B) * projW T = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_upPart_w T hB, smul_zero,
      ContinuousLinearMap.zero_apply]
  have h2 : T.dτ (diagPart B) * projW T = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_diagPart_w, ContinuousLinearMap.smul_apply,
      hP, smul_comm]
  have h3 : projW T * T.dτ (lowPart B) = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_lowPart hB), lowPart_conjTranspose hBh, dtau_upPart_w T hB, inner_zero_left,
      zero_smul, ContinuousLinearMap.zero_apply]
  have h4 : projW T * T.dτ (diagPart B) = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_diagPart B), diagPart_conjTranspose hBh, dtau_diagPart_w, inner_smul_left, hc,
      ContinuousLinearMap.smul_apply, hP, mul_smul]
  have eB1 : T.dτ B = T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (upPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_up B]
    rw [map_add (f := _), map_add (f := _), map_smul]
  have eB2 : T.dτ B = -T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (lowPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_low B]
    rw [map_add (f := _), map_add (f := _), map_smul, map_neg]
  have hL : T.dτ B * projW T =
      T.dτ (lowMinusUp B) * projW T + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB1, add_mul, add_mul, smul_mul_assoc, h1, smul_zero, add_zero, h2]
  have hR : projW T * T.dτ B =
      -(projW T * T.dτ (lowMinusUp B)) + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB2, mul_add, mul_add, mul_smul_comm, h3, smul_zero, add_zero, h4, mul_neg]
  rw [hL, hR, two_mul, add_smul]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private abbrev dpP (T : KType ε Λ) (k : KG ε) : T.V →L[ℂ] T.V := T.op k * projW T * T.op k⁻¹

private lemma dp_op_inv (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  exact op_inv_eq_adjoint T k

private lemma dpP_apply (T : KType ε Λ) (k : KG ε) (v : T.V) :
    dpP T k v = ⟪T.op k T.w, v⟫_ℂ • T.op k T.w := by
  show T.op k (projW T (T.op k⁻¹ v)) = _
  unfold projW
  rw [ContinuousLinearMap.smulRight_apply, map_smul, dp_op_inv]
  congr 1
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

private lemma dp_inner_P (T : KType ε Λ) (k : KG ε) (v : T.V) :
    ⟪v, dpP T k v⟫_ℂ = ((‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [dpP_apply, inner_smul_right, ← inner_conj_symm v (T.op k T.w)]
  first
  | (rw [RCLike.mul_conj]; rfl)
  | (rw [RCLike.mul_conj]; norm_cast)
  | (rw [RCLike.mul_conj]; push_cast; ring)
  | (rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
  | simp [RCLike.mul_conj]

private lemma dp_cont_P (T : KType ε Λ) : Continuous (dpP T) := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hinv : Continuous fun k : KG ε => T.op k⁻¹ := hop.comp continuous_inv
  exact (hop.mul continuous_const).mul hinv

private lemma dp_integrable (T : KType ε Λ) {g : KG ε → ℝ} (hg : Continuous g) :
    Integrable (fun k => ((g k : ℝ) : ℂ) • dpP T k) (muK ε) := by
  haveI := compactSpace_KG ε
  have hf : Continuous (fun k => ((g k : ℝ) : ℂ) • dpP T k) :=
    (Complex.continuous_ofReal.comp hg).smul (dp_cont_P T)
  exact integrableOn_univ.mp (ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn)

private lemma dp_isPositive (T : KType ε Λ) {c : ℝ} (hc : 0 ≤ c) {g : KG ε → ℝ} (hg : Continuous g)
    (hg0 : ∀ k, 0 ≤ g k) :
    ((c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)).IsPositive := by
  have hI := dp_integrable T hg

  have key : ∀ u v : T.V, ⟪u, (∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ =
      ∫ k, ((g k : ℝ) : ℂ) * ⟪u, dpP T k v⟫_ℂ ∂(muK ε) := by
    intro u v
    have hIv : Integrable (fun k => (((g k : ℝ) : ℂ) • dpP T k) v) (muK ε) :=
      (ContinuousLinearMap.apply ℂ T.V v).integrable_comp hI
    rw [ContinuousLinearMap.integral_apply hI, ← integral_inner hIv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

  have hsym : ∀ k (u v : T.V), ⟪dpP T k u, v⟫_ℂ = ⟪u, dpP T k v⟫_ℂ := by
    intro k u v
    rw [dpP_apply, dpP_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  refine ⟨?_, ?_⟩
  · intro u v
    change ⟪(((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) u, v⟫_ℂ =
      ⟪u, (((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ
    rw [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      ← inner_conj_symm _ v, key, key, ← integral_conj, Complex.conj_ofReal]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [map_mul, Complex.conj_ofReal, inner_conj_symm, hsym]
  · intro v
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm, ContinuousLinearMap.smul_apply,
      inner_smul_right, key]
    have e : ∫ k, ((g k : ℝ) : ℂ) * ⟪v, dpP T k v⟫_ℂ ∂(muK ε) =
        ((∫ k, g k * ‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
      first
      | rw [← integral_complex_ofReal]
      | rw [← integral_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [dp_inner_P]
      push_cast
      ring
    rw [e, ← Complex.ofReal_mul]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact mul_nonneg hc (integral_nonneg fun k => mul_nonneg (hg0 k) (sq_nonneg _))

private lemma dp_posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  have hinj : Function.Injective (toMK k).mulVec := by
    intro a b h
    have h2 := congrArg ((toMK k)ᴴ).mulVec h
    simpa [Matrix.mulVec_mulVec, (toMK_facts k).1] using h2
  rw [toMK_inv]
  exact hx.conjTranspose_mul_mul_same hinj

private lemma dp_cont_phi (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (fun k : KG ε => (PhiM μ (toMK k⁻¹ * x * toMK k)).re) := by
  have htoMK : Continuous (toMK : KG ε → Matrix (Fin n) (Fin n) ℂ) := by
    unfold toMK toM
    first
    | fun_prop
    | continuity
    | exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcont : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    ((htoMK.comp continuous_inv).mul continuous_const).mul htoMK
  have hmem : ∀ k : KG ε, toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
    intro k
    first
    | exact posSet_subset_omega (dp_posDef_conj k hx)
    | exact posSet_subset_omega (by simpa [posSet] using dp_posDef_conj k hx)
  exact Complex.continuous_re.comp
    ((phiM_differentiableOn μ).continuousOn.comp_continuous hcont hmem)

theorem psM_norm_le (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {B : ℝ}
    (hB : ∀ k : KG ε, (PhiM μ (toMK k⁻¹ * x * toMK k)).re ≤ B) : ‖psM T μ x‖ ≤ B := by
  set c : ℝ := (Module.finrank ℂ T.V : ℝ) / (muK ε Set.univ).toReal with hc_def
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (muK_univ_pos ε).le
  set g : KG ε → ℝ := fun k => (PhiM μ (toMK k⁻¹ * x * toMK k)).re with hg_def
  have hgc : Continuous g := dp_cont_phi μ hx
  have hg0 : ∀ k, 0 ≤ g k := fun k => (phiM_posDef μ (dp_posDef_conj k hx)).1.le
  have hPhi : ∀ k, PhiM μ (toMK k⁻¹ * x * toMK k) = ((g k : ℝ) : ℂ) := by
    intro k
    apply Complex.ext
    · simp [hg_def]
    · simp [(phiM_posDef μ (dp_posDef_conj k hx)).2]
  have hA : psM T μ x = ((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hPhi, dpP]
  have hone : (1 : T.V →L[ℂ] T.V) = ((c : ℝ) : ℂ) • ∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [← psM_one T μ]
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have h1 : toMK k⁻¹ * 1 * toMK k = 1 := by rw [Matrix.mul_one, toMK_inv, (toMK_facts k).1]
    simp only [h1, phiM_one, one_smul, dpP]
  have i1 := dp_integrable T (g := fun _ => (1 : ℝ)) continuous_const
  have i2 := dp_integrable T hgc
  have hlin : ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) =
      (B : ℂ) • (∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε)) -
        ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    have i1' : Integrable (fun k => (B : ℂ) • ((((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k)) (muK ε) :=
      i1.smul (B : ℂ)
    have e1 := integral_sub i1' i2
    rw [integral_smul] at e1
    refine (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)).trans e1
    beta_reduce
    rw [smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring
  have hdiff : (B : ℂ) • (1 : T.V →L[ℂ] T.V) - psM T μ x =
      ((c : ℝ) : ℂ) • ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [hlin, smul_sub, smul_comm ((c : ℝ) : ℂ) (B : ℂ), ← hone, ← hA]
  have hpos1 := dp_isPositive T hc hgc hg0
  have hpos2 := dp_isPositive T hc (g := fun k => B - g k) (continuous_const.sub hgc)
    (fun k => sub_nonneg.mpr (hB k))
  have h0 : 0 ≤ psM T μ x := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, hA]
    exact hpos1
  have hle : psM T μ x ≤ (B : ℂ) • (1 : T.V →L[ℂ] T.V) := by
    rw [ContinuousLinearMap.le_def, hdiff]
    exact hpos2
  have hB0 : 0 ≤ B := (hg0 1).trans (hB 1)
  calc ‖psM T μ x‖ ≤ ‖(B : ℂ) • (1 : T.V →L[ℂ] T.V)‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0
    _ ≤ ‖(B : ℂ)‖ * ‖(1 : T.V →L[ℂ] T.V)‖ := norm_smul_le _ _
    _ ≤ B * 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hB0]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hB0
    _ = B := mul_one B

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
