module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle035
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
public import Formalism.HermitianCurvature.Bundle005
public import Mathlib.CategoryTheory.Category.Basic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
public import Formalism.HermitianCurvature.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section



namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

section Alg

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem inner_self_cast (a : Wp) : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) a
  · rw [Complex.ofReal_im]
    exact inner_self_im (𝕜 := ℂ) a

theorem l2_norm_scaling {νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (T F : Mx k r → Wp) (a : Wp) (U D : ℝ) (hU : 0 ≤ U)
    (hN : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (U * (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re / D))
    (hae : ∀ᵐ x ∂νq, T (Matrix.of x) = ⟪a, a⟫_ℂ • F (Matrix.of x)) :
    ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F =
      ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
  have hinner : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := inner_self_cast a
  have hnq : ‖⟪a, a⟫_ℂ‖ = ‖a‖ ^ 2 := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : (‖⟪a, a⟫_ℂ‖₊ : ENNReal) = ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [← hnq]
    exact (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).symm
  have hT : PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq T =
      ENNReal.ofReal (‖a‖ ^ 2) ^ 2 * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' (ENNReal.ofReal (‖a‖ ^ 2) ^ 2) _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_congr_ae (hae.mono fun x hx => ?_)
    dsimp only
    rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, hc]
  have hre : (⟪a, ⟪a, a⟫_ℂ • a⟫_ℂ).re = ‖a‖ ^ 4 := by
    rw [inner_smul_right, hinner, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hT, hre] at hN
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hp : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) 2
  have key : ENNReal.ofReal (‖a‖ ^ 2) * (ENNReal.ofReal (‖a‖ ^ 2) * PI.BesselPeriodGGP.l2SG (k := k) (r := r) νq F) =
      ENNReal.ofReal (‖a‖ ^ 2) * ENNReal.ofReal (U * ‖a‖ ^ 2 / D) := by
    rw [← mul_assoc, ← pow_two, hN, ← ENNReal.ofReal_mul hp.le]
    congr 1
    ring
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp key

end Alg

theorem shape_of (hPsi : PsiConst) (hSch : SchurH) (hBC : BeConv) (hNI : NormIdSm) (hBB : BeBessel) : Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hnz
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨x0, hx0, y0, hy0, hne⟩ := hnz
  obtain ⟨ξ0, hξ0⟩ : ∃ ξ, be z c π σ μW μN x0 y0 ξ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne (ContinuousLinearMap.ext hcon)
  have hB0 := hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS y0 (Or.inl hy0) ξ0
  set B0 : H → Wp := fun x => be z c π σ μW μN x y0 ξ0 with hB0def
  have hB0x : B0 x0 ≠ 0 := hξ0
  have hcoef : ∀ v ∈ DDsp σ w0, ∀ ξ : Wp, ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      be z c π σ μW μN x v ξ = κ • B0 x := fun v hv ξ =>
    jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hB0
      (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inl hv) ξ) (hsm x0 hx0) hB0x
  choose! cf hcf using hcoef
  have herm : ∀ x ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, ∀ η ξ : Wp,
      cf v ξ * ⟪η, B0 x⟫_ℂ = conj (cf x η) * ⟪B0 v, ξ⟫_ℂ := by
    intro x hx v hv η ξ
    have hadj := (hBC4 x hx v (Or.inl hv)).2
    have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x v) ξ η
    rw [hadj, hcf v hv ξ x (hsm x hx), hcf x hx η v (hsm v hv), inner_smul_left, inner_smul_right] at e
    exact e.symm
  have hη : ⟪B0 x0, B0 x0⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hB0x
  set κ : ℂ := conj (cf x0 (B0 x0)) / ⟪B0 x0, B0 x0⟫_ℂ with hκdef
  have hcf' : ∀ v ∈ DDsp σ w0, ∀ ξ, cf v ξ = κ * ⟪B0 v, ξ⟫_ℂ := by
    intro v hv ξ
    have e := herm x0 hx0 v hv (B0 x0) ξ
    rw [hκdef, div_mul_eq_mul_div, eq_div_iff hη]
    linear_combination e
  have hform : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ DDsp σ w0, ∀ ξ,
      be z c π σ μW μN x v ξ = (κ * ⟪B0 v, ξ⟫_ℂ) • B0 x := fun x hx v hv ξ => by
    rw [hcf v hv ξ x hx, hcf' v hv ξ]
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply hξ0
    show be z c π σ μW μN x0 y0 ξ0 = 0
    rw [hform x0 (hsm x0 hx0) y0 hy0 ξ0, h0, zero_mul, zero_smul]
  have hpos := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x0 (hsm x0 hx0) x0 (Or.inl hx0)
    (B0 x0)).2
  rw [hform x0 (hsm x0 hx0) x0 hx0, inner_smul_right, inner_self_cast] at hpos
  set N2 : ℝ := ‖B0 x0‖ ^ 2 with hN2
  have hN2pos : 0 < N2 := by rw [hN2]; have := norm_pos_iff.mpr hB0x; positivity
  have hexp : κ * (N2 : ℂ) * (N2 : ℂ) = κ * ((N2 * N2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hpos
  simp only [mul_zero, zero_add, sub_zero] at hpos
  have hNN : 0 < N2 * N2 := mul_pos hN2pos hN2pos
  have him : κ.im = 0 := by
    rcases mul_eq_zero.mp hpos.1 with h1 | h1
    · exact h1
    · exact absurd h1 hNN.ne'
  have hre0 : 0 ≤ κ.re := by
    by_contra hneg; push_neg at hneg
    have : κ.re * (N2 * N2) < 0 := mul_neg_of_neg_of_pos hneg hNN
    linarith [hpos.2]
  have hre : 0 < κ.re := by
    rcases hre0.lt_or_eq with h1 | h1
    · exact h1
    · exact absurd (Complex.ext (by simp [← h1]) (by simp [him])) hκ0
  set s : ℝ := Real.sqrt κ.re with hs
  have hss : (s : ℂ) * (s : ℂ) = κ := by
    rw [← Complex.ofReal_mul, hs, Real.mul_self_sqrt hre.le]
    exact Complex.ext (by simp) (by simp [him])
  have hspos : 0 < s := Real.sqrt_pos.mpr hre
  refine ⟨fun x => (s : ℂ) • B0 x, bessel_smul hB0 _, ⟨x0, hx0, ?_⟩, ?_⟩
  · exact smul_ne_zero (by exact_mod_cast hspos.ne') hB0x
  · intro x hx v hv
    ext ξ
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hform x hx v hv ξ, inner_smul_left, Complex.conj_ofReal, smul_smul]
    congr 1
    rw [← hss]; ring

theorem kFinForm_of (hPsi : PsiConst) (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl hx1e hid v hv x hx
  obtain ⟨x1, hx1, hlx1⟩ := hx1e
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, hz, hT, hc, hπ, -, -, -, -⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  obtain ⟨κ, hκ⟩ := jsz_line hIn.2.2.2 hPsi hlam hσ hz hT hc hπ hl
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ) (hsm x1 hx1) hlx1
  have hadj := (hBC4 x1 hx1 v (Or.inr hv)).2
  have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN x1 v) ξ (l x1)
  rw [hadj, hκ x1 (hsm x1 hx1), hid v hvs x1 hx1] at e
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, inner_smul_right,
    inner_conj_symm] at e
  have hn : ⟪l x1, l x1⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hlx1
  have hκv : κ = ⟪l v, ξ⟫_ℂ := by
    apply mul_left_cancel₀ hn
    linear_combination -e
  rw [hκ x hx, hκv]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

theorem discrete_form_one_side : DDFormOneOfSteps := by
  intro hPsi hSch _ _ _ _ hBC hNI hBB hSh hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, -, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), hid x (hsm x hx) v hv⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x (hsm x hx) v (Or.inl hv) (l v)).1
    rw [hid v (hsm v hv) v hv] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hid _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x (hsm x hx) _ hg) v hv]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [hnz x hx v hv]
    ext ξ; simp

end Formalism.FourierDecayAlt.P.DDSmoothness
end
end

section

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Split

variable {r : ℕ}

def coordinateRestEquiv (l : Fin r) :
    {j : {j : Fin r // l.castSucc.val ≤ j.val} // ¬ (j.1 = l)} ≃ {j : Fin r // l.succ.val ≤ j.val} where
  toFun j := ⟨j.1.1, by
    have h1 := j.1.2; have h2 := j.2
    simp only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢
    rcases Nat.lt_or_ge l.val j.1.1.val with h | h
    · omega
    · exact absurd (Fin.ext (by omega)) h2⟩
  invFun j := ⟨⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩, by
    intro h; have := j.2; rw [h] at this; simp at this⟩
  left_inv j := rfl
  right_inv j := rfl

instance uniqueCoordinateAtLevel (l : Fin r) : Unique {j : {j : Fin r // l.castSucc.val ≤ j.val} // j.1 = l} where
  default := ⟨⟨l, by simp⟩, rfl⟩
  uniq j := Subtype.ext (Subtype.ext j.2)

def coordinateSplit (l : Fin r) : Cf r l.castSucc ≃ᵐ ℂ × Cf r l.succ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {j : Fin r // l.castSucc.val ≤ j.val} => ℂ)
      (fun j => j.1 = l)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique _)
      (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l)))

theorem coordinate_split_measurePreserving (l : Fin r) : MeasurePreserving (coordinateSplit l) volume volume := by
  unfold coordinateSplit
  refine MeasurePreserving.trans (volume_preserving_piEquivPiSubtypeProd _ _) ?_
  exact MeasurePreserving.prod (measurePreserving_piUnique _)
    (volume_measurePreserving_piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l))

theorem coordinate_split_fst (l : Fin r) (a : Cf r l.castSucc) : (coordinateSplit l a).1 = a ⟨l, by simp⟩ := by
  rfl

theorem coordinate_split_snd (l : Fin r) (a : Cf r l.castSucc) (j : {j : Fin r // l.succ.val ≤ j.val}) :
    (coordinateSplit l a).2 j = a ⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩ := by
  rfl

theorem glue_coordinate_split (l : Fin r) (c : Fin r → ℂ) (a : Cf r l.castSucc) :
    glue l.castSucc c a = glue l.succ (Function.update c l (coordinateSplit l a).1) (coordinateSplit l a).2 := by
  funext j
  rw [coordinate_split_fst]
  unfold glue
  rcases lt_trichotomy j.val l.val with h | h | h
  · have h1 : ¬ (l.castSucc.val ≤ j.val) := by simp only [Fin.val_castSucc]; omega
    have h2 : ¬ (l.succ.val ≤ j.val) := by simp only [Fin.val_succ]; omega
    have h3 : j ≠ l := fun e => by rw [e] at h; omega
    rw [dif_neg h1, dif_neg h2, Function.update_of_ne h3]
  · have hj : j = l := Fin.ext h
    subst hj
    have h2 : ¬ (j.succ.val ≤ j.val) := by simp
    rw [dif_pos (by simp), dif_neg h2, Function.update_self]
  · have h1 : l.castSucc.val ≤ j.val := by simp only [Fin.val_castSucc]; omega
    have h2 : l.succ.val ≤ j.val := by simp only [Fin.val_succ]; omega
    rw [dif_pos h1, dif_pos h2, coordinate_split_snd]

theorem weight_coordinate_split (l : Fin r) (a : Cf r l.castSucc) :
    (∏ j, ‖a j‖ ^ (-2 : ℤ)) = ‖(coordinateSplit l a).1‖ ^ (-2 : ℤ) * ∏ j, ‖(coordinateSplit l a).2 j‖ ^ (-2 : ℤ) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : {j : Fin r // l.castSucc.val ≤ j.val} => j.1 = l)]
  congr 1
  · rw [Fintype.prod_unique, coordinate_split_fst]; rfl
  · rw [← (coordinateRestEquiv l).prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [coordinate_split_snd]; rfl

def coordinateExtension (i : Fin (r + 1)) (c : Fin r → ℂ) (a : Cf r i) : Cf r 0 := fun j => glue i c a j.1

theorem coordinate_extension_glue (i : Fin (r + 1)) (c : Fin r → ℂ) (a : Cf r i) : glue 0 c (coordinateExtension i c a) = glue i c a := by
  funext j
  simp [glue, coordinateExtension]

theorem coordinate_extension_measurable (i : Fin (r + 1)) (c : Fin r → ℂ) : Measurable (coordinateExtension i c) := by
  refine Measurable.of_eval fun j => ?_
  by_cases h : i.val ≤ j.1.val
  · simp only [coordinateExtension, glue, dif_pos h]; exact measurable_pi_apply _
  · simp only [coordinateExtension, glue, dif_neg h]; exact measurable_const

theorem level_weight_measurable {β : Type} [MeasurableSpace β] (i : Fin (r + 1)) :
    Measurable (fun q : Cf r i × β => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ)) := by
  fun_prop

end Split

section Top

variable {r : ℕ}

instance isEmptyCoordinatesFromLastLevel : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun j => by have h1 := j.2; have h2 := j.1.isLt; simp only [Fin.val_last] at h1; omega⟩

def lastLevelPoint (r : ℕ) : Cf r (Fin.last r) := isEmptyElim

theorem integral_top_level_point {β E : Type} [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure β) [SFinite ν]
    (f : Cf r (Fin.last r) × β → E) :
    (Integrable f (volume.prod ν) ↔ Integrable (fun g => f (lastLevelPoint r, g)) ν) ∧
      ∫ q, f q ∂(volume.prod ν) = ∫ g, f (lastLevelPoint r, g) ∂ν := by
  have hv : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (lastLevelPoint r) := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  rw [hv, Measure.dirac_prod]
  exact ⟨(measurableEmbedding_prodMk_left _).integrable_map_iff,
    (measurableEmbedding_prodMk_left _).integral_map _⟩

theorem glue_last_level (c : Fin r → ℂ) (a : Cf r (Fin.last r)) : glue (Fin.last r) c a = c := by
  funext j; have := j.isLt; simp only [glue, Fin.val_last]; rw [dif_neg (by omega)]

end Top

section Dens

theorem sesquilinear_polarization {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    4 * β x y = β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) + Complex.I * β (x + Complex.I • y) (x + Complex.I • y)
      - β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) - Complex.I * β (x + (-Complex.I) • y) (x + (-Complex.I) • y) := by
  simp only [hl, hr, map_one, map_neg, Complex.conj_I, neg_neg]
  linear_combination (2 * β x y - 2 * β y x) * Complex.I_mul_I

theorem sesquilinear_polarization_norm {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    ‖β x y‖ ≤ (‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖) / 4 := by
  have h := sesquilinear_polarization β hl hr x y
  have h4 : ‖(4 : ℂ) * β x y‖ = 4 * ‖β x y‖ := by simp
  have : ‖(4 : ℂ) * β x y‖ ≤ ‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖ := by
    rw [h]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) le_rfl)) ?_
    · simp
    · simp
  linarith

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
  (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
  (w : List (Letter ℂ S))

theorem top_density_add_left (x x' y : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w (x + a • x') y c g = topDens L st w x y c g + a * topDens L st w x' y c g := by
  simp only [topDens, act_add_smul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hsInner_add_smul_left, Finset.sum_add_distrib, Finset.mul_sum]

theorem top_density_add_right (x y y' : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w x (y + a • y') c g = topDens L st w x y c g + conj a * topDens L st w x y' c g := by
  simp only [topDens, act_add_smul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hsInner_add_smul_right, Finset.sum_add_distrib, Finset.mul_sum]

theorem act_one_hermitian_curvature (x : Ix S → RadSp k r z z' π π') : act (1 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) x = x := by
  funext a
  simp only [act, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp; rfl
  · intro b _ hb; rw [if_neg (Ne.symm hb)]; rfl
  · simp

end Dens

section Meas

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem level_integrand_aestronglyMeasurable (hM : TopDensMeas S P z z' π π' μ L st K) (w : List (Letter ℂ S))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K (Fin.last P.r)) x) (hy : InK (K (Fin.last P.r)) y)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) :
    AEStronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w x y (glue i c q.1) (Matrix.of q.2)) (volume.prod μ) := by
  have h0 := hM w x y hx hy c
  have e : (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) =
      (fun q : Cf P.r 0 × Mt P.k P.r => topDens L st w x y (glue 0 c q.1) (Matrix.of q.2)) ∘
        Prod.map (coordinateExtension i c) id := by
    funext q; simp only [Function.comp, Prod.map, coordinate_extension_glue]; rfl
  have h1 : StronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) := by
    rw [e]; exact h0.comp_measurable ((coordinate_extension_measurable i c).prodMap measurable_id)
  exact (level_weight_measurable i).aestronglyMeasurable.mul h1.aestronglyMeasurable

end Meas

end Formalism.FourierDecayAlt.P5
end
end

section

namespace Formalism.FourierDecayAlt.TL

open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

open Classical

theorem act_e1Vec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (e : Wd.Ix S) :
    P5.act M (Top.firstStateVector Φ) e = (M e e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp only [if_true]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end Formalism.FourierDecayAlt.TL
end
