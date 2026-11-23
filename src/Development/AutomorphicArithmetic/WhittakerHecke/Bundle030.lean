module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle002
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle002
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle016
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle022
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle013
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle023
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle026
public import Development.AutomorphicArithmetic.WhittakerHecke.HasSumWhittakerDiagTorusRatEqUnipotentConstantTe
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle018
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle024
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle017
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle027
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.IdeleNormEmbeddingNegOneReal
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle003
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
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) (z : (A E)ˣ)
    (h : (z : A E) = AdeleBaseChange.adeleMap ℚ E (y : A ℚ)) : em E (aE y) = aE z := by
  apply Units.ext
  ext i j
  rw [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [aE, h]

theorem UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
          CenN P ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ) φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∀ v : H.P ℚ, ¬ Bad N v → ∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Inert D v w →
          ∃ m : ℕ → ℂ, m 0 = 1 ∧
            (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧
            ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) =
              PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := by
  intro E _ _ _ D P ω χ _ _ L N φ hA hG a hIs v hv w hw hI
  obtain ⟨-, B, hsat, hEig⟩ := hG.fix w (by rw [hw]; exact hv)
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w B).1 hsat))
  obtain ⟨-, -, hleft, -⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hA
  have hEw := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w _ hA.cont hEig
  obtain ⟨χw, hχ, hχe⟩ := UpperTheory.exists_good_character_of_inert_CMDatum E D v w (hG.pl v hv) hI
  have hnl : ∀ b h, Wo D φ (H.lc w (H.nL b) * h) = χw b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [(H.lcLaws E w).1, e1, ← e2]
    exact hleft ![u, t] h
  obtain ⟨ϖ', hϖ', hz, -⟩ := hI.unif (atFin v (unif v)) (unif_spec v)
  have hem : ∀ k : ℕ, em E (aE (pv v ^ k)) = aE (H.idl w ϖ' ^ k) := fun k => by
    refine em_aE _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, hz, Dat.mkE, map_zero, zero_mul, add_zero]
    rfl
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hqw : H.q w = (normV v : ℂ) ^ 2 := by
    have : H.q w = (normV w : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hI.norm]
    push_cast
    rfl
  have hqv : (normV v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsq : H.q w ^ (1 / 2 : ℂ) = (normV v : ℂ) := by
    rw [hqw]
    have e : ((normV v : ℂ) ^ 2) = ((((normV v : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    simp
  refine ⟨fun k => ((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i), by simp,
    fun k g hg => ?_, fun _ => ?_⟩
  · have h := UpperTheory.eigenform_shintani_formula_at_place E w ϖ' hϖ' χw hχ α β _ hEw hnl g (hg w hw) k
    rw [hsq] at h
    rw [hem, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hqv), one_mul]
  · have h1 := hIs.inert v hv w hw hI.norm α β hsat
    have h2 := UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one ((α * χ.val v : ℂˣ) : ℂ) ((β * χ.val v : ℂˣ) : ℂ)
    have h3 : (PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k *
        (((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i))) =
        PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i) := by
      congr 1
      funext k
      rw [Nat.cast_pow, mul_comm ((normV v : ℂ) ^ k), mul_assoc, ← mul_assoc ((normV v : ℂ) ^ k),
        mul_inv_cancel₀ (pow_ne_zero k hqv), one_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
      rw [Nat.add_sub_cancel_left, Units.val_mul, Units.val_mul]
      ring
    rw [h3]
    linear_combination (PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i)) * h1 -
      (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) * h2
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem row_nU (b : A ℚ) (g : G1 ℚ) (u : (A ℚ)ˣ) (j : Fin 2) :
    (gl (nU b * g) * dM u).val 1 j = (gl g * dM u).val 1 j := by
  rw [Units.val_mul, Units.val_mul, M.val_gl, M.val_gl, M.val_mul]
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem row_mD (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a * cD u k) * dM u).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * G.row k j := by
  have h : gl (mD a * cD u k) = gl (mD a) * gl (cD u k) := map_mul _ _ _
  rw [h, mul_assoc, M.gl_cD, Units.val_mul, Units.val_mul, M.val_gl, M.val_gl]
  simp [mD, dM, G.row, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, Matrix.vecMul, dotProduct]

theorem UpperTheory.maximalCompact_integral_unipotent_norm_finite :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (M₀ : Meas ℚ), ∀ Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2), ∀ (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        (_root_.UpperTheory.ConvolutionTheory.R2.M.J0 M₀ fun g => ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ)) ≠ ⊤ := by
  intro E _ _ D ω φ hA M₀ Φ hΦ t u hu
  obtain ⟨B, hB⟩ := hA.bdd
  obtain ⟨hmp, hme⟩ := UpperTheory.measurePreserving_idele_scale_and_conj_on_maximalCompact M₀ t u hu
  obtain ⟨C, hC⟩ := UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded Φ hΦ 2 (by norm_num)
  obtain ⟨-, hiy, -, hU⟩ := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one
  haveI := M₀.prob
  have hw : ∀ g : G1 ℚ, ∫⁻ b in fundamentalSet ℚ, ‖Un.Uu φ Φ t u (nU b * g)‖ₑ ∂(adeleMeasure ℚ) ≤
      ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ := by
    intro g
    refine (lintegral_mono (g := fun _ => ENNReal.ofReal B * ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (gl g * dM u).val 1 j‖ₑ)
      fun b => ?_).trans ?_
    · simp only [Un.Uu, row_nU, enorm_mul]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one]
  let F : IdeleGroup ℚ × G1 ℚ → ℝ≥0∞ := fun p =>
    ‖Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j‖ₑ * ENNReal.ofReal (ab p.1 ^ (2 : ℝ))
  have hF : Measurable F := by
    have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j :=
      (continuous_of_mem_schwartzBruhatPi hΦ).comp (continuous_pi fun j =>
        (Units.continuous_val.comp continuous_fst).mul ((M.continuous_entry 1 j).comp continuous_snd))
    have h2 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => ab p.1 ^ (2 : ℝ) :=
      (M.continuous_ab.comp continuous_fst).rpow_const fun _ => Or.inr (by norm_num)
    exact h1.measurable.enorm.mul h2.measurable.ennreal_ofReal
  have hI : ∫⁻ p, F p ∂M₀.ν ≤ C := by
    rw [Meas.ν, lintegral_prod_symm _ hF.aemeasurable]
    have hae : ∀ᵐ k ∂M₀.κ, k ∈ KK ℚ := by
      rw [ae_iff]
      exact M₀.supp
    refine (lintegral_mono_ae (g := fun _ => (C : ℝ≥0∞)) (hae.mono fun k hk => hC k hk)).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  unfold M.J0
  rw [← hmp.lintegral_comp_emb hme]
  have hK : ENNReal.ofReal B * ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hK (ENNReal.coe_ne_top (r := C))) ?_
  refine le_trans ?_ (mul_le_mul_right hI _)
  rw [← lintegral_const_mul _ hF]
  refine lintegral_mono fun p => ?_
  refine (mul_le_mul_right (hw _) _).trans (le_of_eq ?_)
  have e1 : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u p.1) * cD u p.2) * dM u).val 1 j) =
      fun j => ((p.1 : (A ℚ)ˣ) : A ℚ) * G.row p.2 j := by
    funext j
    rw [row_mD, ← mul_assoc, ← Units.val_mul]
    have : (iy (Real.exp t) * ((Un.aa t u p.1)⁻¹ * u) : (A ℚ)ˣ) = p.1 := by
      have h : ∀ x y z : (A ℚ)ˣ, x * ((x * y * z⁻¹)⁻¹ * y) = z := fun x y z => by
        rw [mul_left_comm, ← mul_assoc, mul_right_comm, mul_comm x y, mul_assoc _ y x, mul_comm y x, mul_inv, inv_inv,
          mul_right_comm, inv_mul_cancel, one_mul]
      exact h _ _ _
    rw [this]
  have e2 : M.wt (Un.aa t u p.1) = ENNReal.ofReal ((Real.exp t)⁻¹ ^ 2) * ENNReal.ofReal (ab p.1 ^ (2 : ℝ)) := by
    have h : ab (Un.aa t u p.1) = Real.exp t * (ab p.1)⁻¹ := by
      have h0 : ab (Un.aa t u p.1) = ab (iy (Real.exp t)) * ab u * ab (p.1⁻¹ : (A ℚ)ˣ) := by
        rw [← M.ab_mul, ← M.ab_mul]
        rfl
      rw [h0, hiy _ (Real.exp_ne_zero t), hU u hu, M.ab_inv, abs_of_pos (Real.exp_pos t), mul_one]
    rw [M.wt, h, ← ENNReal.ofReal_mul (by positivity), Real.rpow_two, mul_inv, inv_inv, mul_pow]
  simp only [e1, e2, F]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem ab_mul' (a b : (A ℚ)ˣ) : ab (a * b) = ab a * ab b := by simp [ab, map_mul]

private theorem ab_pos' (a : (A ℚ)ˣ) : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2

private theorem ab_inv' (a : (A ℚ)ˣ) : ab a⁻¹ = (ab a)⁻¹ := by simp [ab, map_inv]

private theorem ab_diag' (α : ℚˣ) : ab (IdeleGroup.diagonal ℚ α) = 1 := by
  simp [ab, IdeleGroup.ideleModule_diagonal]

private theorem cpow_exp (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp ((x : ℂ) * w) := by
  have h : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [Complex.cpow_def_of_ne_zero h, ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem modid (t r : ℝ) (hr : 0 < r) (s : ℂ) :
    Complex.exp (2 * s * t) * ((((Real.exp t * r⁻¹)⁻¹ ^ 2 : ℝ)) : ℂ) =
      ((Real.exp t * Real.exp t * (r⁻¹ * r⁻¹) : ℝ) : ℂ) ^ (s - 1) * (r : ℂ) ^ (2 * s) := by
  obtain ⟨L, rfl⟩ : ∃ L, r = Real.exp L := ⟨Real.log r, (Real.exp_log hr).symm⟩
  have h1 : (Real.exp t * (Real.exp L)⁻¹)⁻¹ ^ 2 = Real.exp (2 * L - 2 * t) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : Real.exp t * Real.exp t * ((Real.exp L)⁻¹ * (Real.exp L)⁻¹) = Real.exp (2 * t - 2 * L) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h1, h2, cpow_exp, cpow_exp, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cpow_ne {r : ℝ} (hr : 0 < r) (w : ℂ) : (r : ℂ) ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne')]
  exact Complex.exp_ne_zero _

private theorem cg1 {G : Type} [CommGroup G] (e u z : G) :
    e * e * u * (z * z)⁻¹ = (e * u * z⁻¹) * (e * u * z⁻¹) * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg2 {G : Type} [CommGroup G] (e u z : G) :
    e * ((e * u * z⁻¹)⁻¹ * u) = z := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg3 {G : Type} [CommGroup G] (a u : G) :
    a * a * u⁻¹ = u * (u * a⁻¹)⁻¹ * (u * a⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg4 {G : Type} [CommGroup G] (a b u : G) :
    (u * a⁻¹) * (b * (a * a * u⁻¹)) = b * a := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem gl_mD (a : (A ℚ)ˣ) : (gl (mD a)).val = !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl

private theorem mat_id (b a u : (A ℚ)ˣ) :
    aE b * gl (mD a) * dM u = Matrix.GeneralLinearGroup.scalar (Fin 2) (u * a⁻¹) * aE (b * (a * a * u⁻¹)) := by
  have h4 : ((u : A ℚ) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) * ((b : A ℚ) * ((a : A ℚ) * (a : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ))) = (b : A ℚ) * (a : A ℚ) := by
    have := congrArg Units.val (cg4 a b u)
    simpa only [Units.val_mul] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aE, gl_mD, dM, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two, h4, mul_comm]

private theorem row_id (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a) * dM u * gl k).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * row k j := by
  simp [gl_mD, dM, UpperTheory.ConvolutionTheory.R2.G.row, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.tsum_unfoldedIntegrand_ideleCovering_eq_exp_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        ∀ p : IdeleGroup ℚ × G1 ℚ, (Summable fun α : ℚˣ => Un.Hh D χ φ Φ s (Un.cov t u α * (p.1 * p.1)⁻¹, p)) →
        Complex.exp (2 * s * t) * (((χ.1 u : ℂˣ) : ℂ) * Un.Tt φ Φ t u p) = ∑' α : ℚˣ, Un.Hh D χ φ Φ s (Un.cov t u α * (p.1 * p.1)⁻¹, p) := by
  intro E _ _ D ω χ φ hA hχω Φ s t u hu p hS
  obtain ⟨z, k⟩ := p
  obtain ⟨e, he⟩ : ∃ e : (A ℚ)ˣ, e = iy (Real.exp t) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (A ℚ)ˣ, a = e * u * z⁻¹ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (A ℚ)ˣ, c = u * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (A ℚ)ˣ, y = a * a * u⁻¹ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : GL (Fin 2) (A E), x = em E (gl (mD a) * dM u * gl k) := ⟨_, rfl⟩
  obtain ⟨Φz, hΦz⟩ : ∃ w : ℂ, w = Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j := ⟨_, rfl⟩
  have haa : Un.aa t u z = a := by rw [ha, he]; rfl
  have hcov : ∀ α : ℚˣ, Un.cov t u α * (z * z)⁻¹ = IdeleGroup.diagonal ℚ α * y := fun α => by
    have h := cg1 e u z
    rw [← ha, ← hy] at h
    rw [← h, he]
    simp only [Un.cov, mul_assoc]
  have hrow : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD a) * dM u * gl k).val 1 j) =
      fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j := by
    funext j
    rw [row_id, ← he, ← mul_assoc, ← Units.val_mul, ha, cg2]
  have hTt : Un.Tt φ Φ t u (z, k) = (((ab a)⁻¹ ^ 2 : ℝ) : ℂ) * Un.Fb φ x * Φz := by
    show (((ab (Un.aa t u z))⁻¹ ^ 2 : ℝ) : ℂ) * Un.Fb φ (em E (gl (mD (Un.aa t u z)) * dM u * gl k)) *
      (Φ fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u z)) * dM u * gl k).val 1 j) = _
    rw [haa, hrow, ← hx, ← hΦz]
  obtain ⟨W, hWd⟩ : ∃ W : ℚˣ → ℂ, W = fun α => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α * y) * gl k)) := ⟨_, rfl⟩
  have hW : ∀ α : ℚˣ, Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x) = ((ω.1 c : ℂˣ) : ℂ) ^ 2 * W α := fun α => by
    have h : aE (IdeleGroup.diagonal ℚ α) * (gl (mD a) * dM u * gl k) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * (aE (IdeleGroup.diagonal ℚ α * y) * gl k) := by
      calc _ = aE (IdeleGroup.diagonal ℚ α) * gl (mD a) * dM u * gl k := by simp only [mul_assoc]
        _ = _ := by rw [mat_id, mul_assoc, ← hc, ← hy]
    rw [hx, ← map_mul, h, map_mul, UpperTheory.whittaker_scalar_mul_eq_centralChar_sq_mul E D ω φ hA, hWd]
  obtain ⟨C, hC⟩ : ∃ C : ℂ, C = ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) * (Φz * ((ab z : ℝ) : ℂ) ^ (2 * s)) := ⟨_, rfl⟩
  have habd : ∀ α : ℚˣ, ab (IdeleGroup.diagonal ℚ α * y) = ab y := fun α => by
    rw [ab_mul', ab_diag', one_mul]
  have hχd : ∀ α : ℚˣ, χ.1 (IdeleGroup.diagonal ℚ α * y) = χ.1 y := fun α => by
    have h : χ.1 (IdeleGroup.diagonal ℚ α) = 1 := χ.2.2 α
    rw [map_mul, h, one_mul]
  have hH : ∀ α : ℚˣ, Un.Hh D χ φ Φ s (Un.cov t u α * (z * z)⁻¹, (z, k)) = W α * C := fun α => by
    rw [hcov α]
    show Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α * y) * gl k)) * ((χ.1 (IdeleGroup.diagonal ℚ α * y) : ℂˣ) : ℂ) *
      ((ab (IdeleGroup.diagonal ℚ α * y) : ℝ) : ℂ) ^ (s - 1) *
      ((Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)) = _
    rw [hχd, habd, ← hΦz, hC, hWd]
    ring
  have hS' : Summable fun α : ℚˣ => W α * C := by
    simpa only [hH] using hS
  simp only [hH]
  rw [hTt]
  by_cases h0 : Φz = 0
  · have hC0 : C = 0 := by rw [hC, h0]; ring
    simp [h0, hC0]
  have hCne : C ≠ 0 := by
    rw [hC]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (cpow_ne (ab_pos' y) _)) (mul_ne_zero h0 (cpow_ne (ab_pos' z) _))
  have hsW : Summable W := (summable_mul_right_iff hCne).1 hS'
  have hsum : Summable fun α : ℚˣ => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x) := by
    simp only [hW]
    exact hsW.mul_left _
  have hFb : Un.Fb φ x = ((ω.1 c : ℂˣ) : ℂ) ^ 2 * ∑' α, W α := by
    have h := (UpperTheory.hasSum_whittaker_diagTorus_rat_eq_unipotentConstantTerm E D ω φ hA x hsum).tsum_eq
    simp only [hW] at h
    rw [← h, tsum_mul_left]
  have hchar : ((χ.1 u : ℂˣ) : ℂ) * ((ω.1 c : ℂˣ) : ℂ) ^ 2 = ((χ.1 y : ℂˣ) : ℂ) := by
    have h2 : ω.1 c ^ 2 = (χ.1 c)⁻¹ * (χ.1 c)⁻¹ := by
      have h := hχω c
      rw [mul_pow] at h
      rw [← mul_inv, ← sq]
      exact eq_inv_of_mul_eq_one_right h
    have h3 : χ.1 y = χ.1 u * ω.1 c ^ 2 := by
      rw [hy, cg3, ← hc, map_mul, map_mul, map_inv, h2, mul_assoc]
    rw [h3]
    push_cast
    rfl
  have hiy : ab e = Real.exp t := by
    rw [he, (UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one).2.1 _ (Real.exp_ne_zero t), abs_of_pos (Real.exp_pos t)]
  have hau : ab u = 1 := (UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one).2.2.2 u hu
  have hab : ab a = Real.exp t * (ab z)⁻¹ := by
    rw [ha, ab_mul', ab_mul', hiy, hau, ab_inv', mul_one]
  have haby : ab y = Real.exp t * Real.exp t * ((ab z)⁻¹ * (ab z)⁻¹) := by
    rw [hy, ab_mul', ab_mul', ab_inv', hab, hau]
    ring
  have hmod := modid t (ab z) (ab_pos' z) s
  rw [← hab, ← haby] at hmod
  rw [tsum_mul_right, hFb, hC, ← hchar]
  linear_combination (((χ.1 u : ℂˣ) : ℂ) * ((ω.1 c : ℂˣ) : ℂ) ^ 2 * (∑' α, W α) * Φz) * hmod
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_archIdele_natIdele_congruenceUnit_factorization :
    ∀ N : ℕ, 0 < N → ∀ y : (A ℚ)ˣ, ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT N ∧ y = iy r * pin n * τ := by
  intro N hN y h
  exact UpperTheory.exists_factorization_of_ideleCongruence_divisor_level N N hN dvd_rfl (fun _ h => h) y h.1 fun v _ => h.2 v
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem val_nat (n : ℕ) (v : H.P ℚ) : Valued.v (n : H.Kv v) = v.intValuation (n : 𝓞 ℚ) := by
  have e : (n : H.Kv v) = FinitePlace.embedding v (algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ)) := by simp
  rw [e, ← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ))

private theorem val_le (N : ℕ) (v : H.P ℚ) : Valued.v (N : H.Kv v) ≤ 1 := by
  rw [val_nat]
  exact HeightOneSpectrum.intValuation_le_one v _

private theorem cp_iy {y : ℝ} (h : y ≠ 0) (v : H.P ℚ) : H.cp v ((iy y : (A ℚ)ˣ) : A ℚ) = 1 := by
  have : ((iy y : (A ℚ)ˣ) : A ℚ).2 = 1 := by
    unfold iy
    rw [dite_eq_right h]
    show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
    simp
  exact (congrArg (pLoc ℚ v) this).trans (map_one _)

theorem UpperTheory.ideleCongruence_archIdele_mul_finiteNatIdele :
    ∀ N : ℕ, 0 < N → ∀ (n : ℕ) (r : ℝ), 0 < n → n.Coprime N → r ≠ 0 → ((∀ v, Bad N v → Dv N v (((iy r * pin n : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((iy r * pin n : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N _ n r hn hc hr
  obtain ⟨-, h2, h3⟩ := UpperTheory.finiteNatIdele_arch_valuation_support n hn
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hb : ¬ Bad n v := fun hb => by
      have h1 : IsCoprime (n : 𝓞 ℚ) (N : 𝓞 ℚ) := Nat.Coprime.cast hc
      obtain ⟨a, b, e⟩ := h1
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (e ▸ add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_left _ _ hv)))
    unfold Dv
    rw [map_sub, Units.val_mul, map_mul, cp_iy hr, h3 v hb, map_one]
    simp
  · rw [Units.val_mul, map_mul, cp_iy hr, one_mul, h2]
    exact val_le n v
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem kInf_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ)
    (i j : Fin 2) (w : InfinitePlace E) :
    (kInf (em E (rot t))).val i j w = (((Nz.X t).val i j (Fo.pl ℚ w.embedding) : ℝ) : ℂ) := by
  have h1 := (UpperTheory.ConvolutionTheory.R2.Fo.coordMk ℚ E D).1 w.embedding ((rot t).val i j) 0
  rw [FieldIso.coord_embedding] at h1
  have h2 : D.mkE ((rot t).val i j) 0 = AdeleBaseChange.adeleMap ℚ E ((rot t).val i j) := by
    simp [Dat.mkE]
  have h3 : TR.pInf ℚ ((rot t).val i j) = (Nz.X t).val i j := by
    have h := congrArg (fun g : GL (Fin 2) (TR.Rinf ℚ) => g.val i j) (TR.pInf_infGL (Nz.X t))
    rw [← Nz.rot_eq] at h
    exact h
  change pInf E (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)) w = _
  rw [← h2, h1]
  simp [Fo.cw, h3]

private theorem kInf_rot {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ) :
    (kInf (em E (rot t))).val =
      !![fun _ => (Real.cos t : ℂ), fun _ => -(Real.sin t : ℂ); fun _ => (Real.sin t : ℂ), fun _ => (Real.cos t : ℂ)] := by
  ext i j w
  rw [kInf_val D]
  fin_cases i <;> fin_cases j <;> simp [Nz.X]

theorem UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (t : ℝ), XB D (em E (rot t)) = !![(Real.cos t * Real.sin t) • thInf D, (Real.cos t ^ 2) • thInf D; -((Real.sin t ^ 2) • thInf D), -((Real.cos t * Real.sin t) • thInf D)] := by
  intro E _ _ _ D t
  have hinv : (kInf (em E (rot t)))⁻¹ = kInf (em E (rot (-t))) := by
    rw [Nz.rot_neg, map_inv]
    simp [kInf, map_inv]
  rw [XB, hinv, kInf_rot D, kInf_rot D]
  ext i j w
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;> ring
end
