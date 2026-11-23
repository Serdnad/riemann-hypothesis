module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ThetaDecayingFunction

theorem key {x C1 D : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D) :
    ((D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * x = C1 * D ^ (-(a : ℝ) / k) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hD.le, Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha,
    show -(a : ℝ) / k = -((k : ℝ)⁻¹ * a) by ring, Real.rpow_neg hD.le]
  have : 0 < D ^ ((k : ℝ)⁻¹ * a) := Real.rpow_pos_of_pos hD _
  field_simp

theorem le_height {x C1 D h : ℝ} {a k : ℕ} (ha : a ≠ 0) (hx : 0 < x) (hC : 0 < C1) (hD : 0 < D)
    (ht : 0 < h / D ^ ((k : ℝ)⁻¹)) (hb : x ≤ C1 * (h / D ^ ((k : ℝ)⁻¹)) ^ a) :
    D ^ ((k : ℝ)⁻¹) * (x / C1) ^ ((a : ℝ)⁻¹) ≤ h := by
  have hDk : 0 < D ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hD _
  have h1 : (x / C1) ^ ((a : ℝ)⁻¹) ≤ h / D ^ ((k : ℝ)⁻¹) := by
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (div_nonneg hx.le hC.le) _) ht.le ha,
      Real.rpow_inv_natCast_pow (div_nonneg hx.le hC.le) ha, div_le_iff₀' hC]
    exact hb
  calc _ ≤ D ^ ((k : ℝ)⁻¹) * (h / D ^ ((k : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h1 hDk.le
    _ = h := by field_simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem part1 (hD : D0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (Cf : Set (Fin k → Af E)) (hCf : IsCompact Cf) (a : ℕ) (hka : k ≤ a) :
    ∃ (M : ℕ) (C : ℝ), ∀ g : GA E k, (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  obtain ⟨M, C, hMC⟩ := hG E k Cf hCf a hka
  obtain ⟨C1, hC1⟩ := hφ a
  refine ⟨M, C * C1, fun g => ?_⟩
  have hDg : 0 < Dt g := (hD E k).1 g
  by_cases h0 : φ g = 0
  · simp [h0]
  have hx : 0 < ‖φ g‖ := norm_pos_iff.2 h0
  have hne : (fun _ : Fin k => (1 : E)) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hk⟩
    simp at this
  have hC1p : 0 < C1 := by
    have h1 := hC1 g _ hne
    have h2 := (hH E k).1 g _ hne
    by_contra hc
    replace hc := not_lt.1 hc
    have : C1 * ht g (fun _ => 1) ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg h2.le _)
    linarith
  have ha : a ≠ 0 := by omega
  have hr : 0 < Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹) :=
    mul_pos (Real.rpow_pos_of_pos hDg _) (Real.rpow_pos_of_pos (div_pos hx hC1p) _)
  have hbound := hMC g _ hr fun ξ hξ => le_height ha hx hC1p hDg ((hH E k).1 g ξ hξ) (hC1 g ξ hξ)
  calc _ ≤ ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹) * ‖φ g‖ₑ := by
        gcongr
    _ = ENNReal.ofReal (C * ((Dt g ^ ((k : ℝ)⁻¹) * (‖φ g‖ / C1) ^ ((a : ℝ)⁻¹)) ^ a)⁻¹ * ‖φ g‖) := by
        rw [ENNReal.ofReal_mul' (norm_nonneg _), ofReal_norm]
    _ = _ := by rw [mul_assoc, key ha hx hC1p hDg, mul_assoc]

theorem ind_le {C₀ : Set (Fin k → Ad E)} {R : ℝ} (hR : ∀ y ∈ C₀, ‖fun i => pInf E (y i)‖ ≤ R) (M : ℕ)
    (y : Fin k → Ad E) :
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal ((1 + max R 0) ^ M) *
      ENNReal.ofReal (((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy),
      ← ENNReal.ofReal_mul (by positivity), ENNReal.one_le_ofReal, ← div_eq_mul_inv,
      one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by linarith [hR y hy, le_max_left R 0]) M
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem part2 (hD : D0) (hN : N0) (hH : H0) (hG : ThetaSeriesBound) (hk : 1 ≤ k) (φ : GA E k → ℂ) (hφ : Dec φ)
    (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (hka : k ≤ a) :
    ∃ C : ℝ, ∀ g : GA E k,
      (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) * ‖φ g‖ₑ ≤
        ENNReal.ofReal (C * Dt g ^ (-(a : ℝ) / k)) := by
  have hcF : Continuous fun y : Fin k → Ad E => fun i => pFin E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pFin E).comp (continuous_apply i)
  have hcI : Continuous fun y : Fin k → Ad E => fun i => pInf E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.ContAut.continuous_pInf E).comp (continuous_apply i)
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn hcI.continuousOn
  obtain ⟨M, C', hC'⟩ := part1 hD hH hG hk φ hφ _ (hC₀.image hcF) a hka
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hN E k k hk le_rfl
  let e : {ξ : Fin k → E // ξ ≠ 0} ≃ RowT E k k :=
    { toFun := fun ξ => ⟨ξ.1, ξ.2, fun i hi => absurd i.2 (by omega)⟩
      invFun := fun ξ => ⟨ξ.1, ξ.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hK : (0 : ℝ) ≤ (1 + max R 0) ^ M := by positivity
  refine ⟨(1 + max R 0) ^ M * C', fun g => ?_⟩
  rw [← e.tsum_eq]
  calc _ = (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, C₀.indicator (fun _ => (1 : ℝ≥0∞))
          ((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val)) * ‖φ g‖ₑ := by
        congr 1
        exact tsum_congr fun ξ => by rw [hlast]; rfl
    _ ≤ (∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ :=
        by
        gcongr with ξ
        exact ind_le hR M _
    _ = ENNReal.ofReal ((1 + max R 0) ^ M) * ((∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (
          ((fun y : Fin k → Ad E => fun i => pFin E (y i)) '' C₀).indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))) * ‖φ g‖ₑ) := by
        rw [ENNReal.tsum_mul_left, mul_assoc]
    _ ≤ ENNReal.ofReal ((1 + max R 0) ^ M) * ENNReal.ofReal (C' * Dt g ^ (-(a : ℝ) / k)) :=
        by
        gcongr
        exact hC' g
    _ = _ := by rw [← ENNReal.ofReal_mul hK, mul_assoc]

end ThetaDecayingFunction

theorem theta_decaying_of_bound : D0 → N0 → H0 → ThetaSeriesBound → ThetaDecaying := by
  intro hD hN hH hG E _ _ _ k hk φ hφ
  exact ⟨fun Cf hCf a hka => ThetaDecayingFunction.part1 hD hH hG hk φ hφ Cf hCf a hka,
    fun C₀ hC₀ a hka => ThetaDecayingFunction.part2 hD hN hH hG hk φ hφ C₀ hC₀ a hka⟩

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace MeasureInverseInduction

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countGL : Countable (GL (Fin k) E) := by
  haveI : Countable E := GroundTheory.Global.countable_numberField E
  haveI : Countable (Matrix (Fin k) (Fin k) E) := inferInstanceAs (Countable (Fin k → Fin k → E))
  exact Units.val_injective.countable

theorem blk_ratGL {j : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory j γ) : GlobalTheory j (ratGL E k γ) := by
  intro i c hic
  change algebraMap E (Ad E) (γ.val i c) = _
  rw [h i c hic, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  exact tsum_congr fun γ => lintegral_map hF (measurable_const_mul _)

theorem inv_step (ν : Measure (GA E k)) (hinvν : Measure.map (fun h => h⁻¹) ν = ν) (g : GA E k)
    (hc : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F (g * h * g⁻¹) ∂ν = ∫⁻ h, F h ∂ν)
    (f : GA E k → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * h) ∂ν := by
  have hG : Measurable fun x : GA E k => f (g⁻¹ * (g * x * g⁻¹)) :=
    hf.comp ((measurable_const_mul _).comp ((measurable_mul_const _).comp (measurable_const_mul _)))
  calc ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * (g * h⁻¹ * g⁻¹)) ∂ν :=
        lintegral_congr fun h => by congr 1; group
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂Measure.map (fun h => h⁻¹) ν := (lintegral_map hG measurable_inv).symm
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂ν := by rw [hinvν]
    _ = ∫⁻ x, f (g⁻¹ * x) ∂ν := hc (fun y => f (g⁻¹ * y)) (hf.comp (measurable_const_mul _))

def invE (Γ : Set (GL (Fin k) E)) (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) : Γ ≃ Γ where
  toFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  invFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  left_inv γ := Subtype.ext (inv_inv γ.1)
  right_inv γ := Subtype.ext (inv_inv γ.1)

theorem inv_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ)
    (hinvν : Measure.map (fun h => h⁻¹) (nuD E k d) = nuD E k d)
    (hconj : ∀ γ ∈ Γ, ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ h, F (ratGL E k γ * h * (ratGL E k γ)⁻¹) ∂nuD E k d = ∫⁻ h, F h ∂nuD E k d)
    (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) :
    Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc ∫⁻ h, f h ∂Measure.map (fun h => h⁻¹) (nuG Γ d) = ∫⁻ h, f h⁻¹ ∂nuG Γ d :=
        lintegral_map hf measurable_inv
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h)⁻¹ ∂nuD E k d := lint_nuG Γ d _ (hf.comp measurable_inv)
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ.1⁻¹ * h) ∂nuD E k d := tsum_congr fun γ => by
        rw [inv_step _ hinvν _ (hconj γ.1 γ.2) f hf, map_inv (ratGL E k) γ.1]
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d :=
        (invE Γ hΓ).tsum_eq (fun γ : Γ => ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d)
    _ = ∫⁻ h, f h ∂nuG Γ d := (lint_nuG Γ d f hf).symm

theorem sf_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) [SFinite (nuD E k d)] : SFinite (nuG Γ d) := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [nuG]; infer_instance

theorem ae_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (hae : ∀ᵐ u ∂nuD E k d, UU (k - d) u) :
    ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [ae_iff] at hae ⊢
  rw [nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
  intro γ
  rw [(measurableEmbedding_mulLeft (ratGL E k γ)).map_apply]
  exact measure_mono_null (t := {u | ¬ UU (k - d) u})
    (fun u hu hUU => hu ⟨γ.1, u, γ.2, hUU, rfl⟩) hae

theorem nuD_ne_zero (hsf : ∀ d ≤ k, SFinite (nuD E k d)) : ∀ d ≤ k, nuD E k d ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro _ h
    have h1 := congrArg (fun μ : Measure (GA E k) => μ Set.univ) h
    simp [nuD] at h1
  | succ d ih =>
    intro hd h
    haveI := hsf d (by omega)
    have hm : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => blkU p.1 * p.2 :=
      (((continuous_posU (isNil_blk k _ _)).comp continuous_fst).mul continuous_snd).measurable
    have h3 := (Measure.map_eq_zero_iff hm.aemeasurable).mp h
    have h2 := congrArg (fun μ => μ (vecDomain E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) ×ˢ Set.univ)) h3
    simp only [Measure.prod_prod, vecMeasure_vecDomain, one_mul, Measure.coe_zero, Pi.zero_apply] at h2
    exact ih (by omega) (Measure.measure_univ_eq_zero.mp h2)

variable [_root_.NumberField.IsTotallyComplex E]

theorem main_nuG (hD0 : D0) (hN1 : N1) (Γ : Set (GL (Fin k) E)) (d : ℕ) (hd : d ≤ k)
    (hinv : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hblk : ∀ γ ∈ Γ, GlobalTheory (k - d) γ) :
    SFinite (nuG Γ d) ∧ Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d ∧
      ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  obtain ⟨hsf, hae, hinvν, -, hconj⟩ := hN1 E k d hd
  haveI := hsf
  refine ⟨sf_nuG Γ d, inv_nuG Γ d hinvν (fun γ hγ F hF => ?_) hinv, ae_nuG Γ d hae⟩
  rw [hconj _ (blk_ratGL (hblk γ hγ)) F hF, (hD0 E k).2.2.2.1 γ, inv_one, ENNReal.ofReal_one, one_pow, one_mul]

end MeasureInverseInduction

open MeasureInverseInduction in
set_option synthInstance.maxHeartbeats 400000 in
theorem galois_fixed_adelic_matrices_descend : D0 → N0 → N1 → N3 := by
  intro hD0 hN0 hN1 E _ _ _ k
  have hP : ∀ m < k, SFinite (nuP E k m) ∧ Measure.map (fun h => h⁻¹) (nuP E k m) = nuP E k m ∧
      ∀ᵐ h ∂nuP E k m, ∃ γ u, IsMir m γ ∧ UU (m + 1) u ∧ h = ratGL E k γ * u := by
    intro m hm
    have hN := hN0 E k (m + 1) (by omega) (by omega)
    have h6 : ∀ γ : GL (Fin k) E, IsMir m γ → IsMir m γ⁻¹ ∧ GlobalTheory (m + 1) γ := by
      simpa only [Nat.add_sub_cancel] using hN.2.2.2.2.2.1
    have e : k - (k - (m + 1)) = m + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | IsMir m γ} (k - (m + 1)) (by omega)
      (fun γ hγ => (h6 γ hγ).1) (fun γ hγ => by rw [e]; exact (h6 γ hγ).2)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hB : ∀ j ≤ k, SFinite (nuB E k j) ∧ Measure.map (fun h => h⁻¹) (nuB E k j) = nuB E k j ∧
      ∀ᵐ h ∂nuB E k j, ∃ γ u, GlobalTheory j γ ∧ UU j u ∧ h = ratGL E k γ * u := by
    intro j hj
    have hinv : ∀ γ : GL (Fin k) E, GlobalTheory j γ → GlobalTheory j γ⁻¹ := by
      intro γ hγ
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
        subst this
        rw [inv_one]
        exact hγ
      · exact (hN0 E k j hpos hj).2.2.2.1 γ hγ
    have e : k - (k - j) = j := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | GlobalTheory j γ} (k - j) (by omega)
      (fun γ hγ => hinv γ hγ) (fun γ hγ => by rw [e]; exact hγ)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hall : ∀ γ : GL (Fin k) E, γ ∈ {γ : GL (Fin k) E | GlobalTheory k γ} := fun γ i c h =>
    absurd h (not_or.mpr ⟨not_le.mpr i.isLt, not_le.mpr c.isLt⟩)
  have hK : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F h ∂nuB E k k = ∑' γ : GL (Fin k) E, F (ratGL E k γ) := by
    intro F hF
    rw [nuB, lint_nuG _ _ F hF, Nat.sub_self]
    simp only [nuD, lintegral_dirac, mul_one]
    exact (Equiv.subtypeUnivEquiv hall).tsum_eq (fun γ => F (ratGL E k γ))
  have h4 : 1 ≤ k → (∀ᵐ h ∂nuP E k 0, UU 0 h) ∧ nuP E k 0 ≠ 0 := by
    intro hk
    obtain ⟨-, -, hae⟩ := hP 0 (by omega)
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
      have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
      rw [hh, this, map_one, one_mul]
      exact ⟨hu.1, hu.2.1, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
    · intro h0
      haveI : Countable (GL (Fin k) E) := countGL
      have h1 : nuP E k 0 Set.univ = 0 := by simp [h0]
      rw [nuP, nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero] at h1
      have h2 := h1 ⟨1, show IsMir 0 (1 : GL (Fin k) E) from fun i c _ => rfl⟩
      rw [(measurableEmbedding_mulLeft _).map_apply, Set.preimage_univ, Measure.measure_univ_eq_zero] at h2
      exact nuD_ne_zero (fun d hd => (hN1 E k d hd).1) _ (by omega) h2
  exact ⟨hP, hB, hK, h4⟩

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace AdmissibleVectors

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem map_wd (μ : Measure (GA E k)) [μ.IsHaarMeasure] (β : GA E k → ℝ≥0∞) (t : GA E k) :
    Measure.map (MeasurableEquiv.mulLeft t⁻¹) (μ.withDensity β) = μ.withDensity fun g => β (t * g) := by
  ext s hs
  rw [Measure.map_apply (MeasurableEquiv.mulLeft t⁻¹).measurable hs,
    withDensity_apply _ ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator ((MeasurableEquiv.mulLeft t⁻¹).measurable hs), ← lintegral_indicator hs]
  rw [← lintegral_mul_left_eq_self (μ := μ) _ t]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

end AdmissibleVectors

open AdmissibleVectors in
set_option synthInstance.maxHeartbeats 400000 in
theorem sum_wt_mul_massS_le_inv_pow_mul_total_mass : Q1 → Q2 → N2 → N3 → C1 := by
  intro _ hQ2 hN2 hN3 E _ _ _ k μ _ hk β hβ w l Φ hΦ hΦu hint
  set t := fl k w (Iwasawa.torusPow (w.adicCompletion E) k l) with ht
  obtain ⟨hsf, hinv, -⟩ := (hN3 E k).1 0 (by omega)
  have := hsf
  obtain ⟨hUU, -⟩ := (hN3 E k).2.2.2 hk
  have hq0 : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set c : ℝ≥0∞ := ENNReal.ofReal ((Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l) with hc
  have hcpos : 0 < (Ideal.absNorm w.asIdeal : ℝ) ^ rhoPair l :=
    zpow_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hq0)) _
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hcpos).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hβ0m : Measurable fun g => β (t * g) := hβ.1.comp (measurable_const_mul t)
  set β' : GA E k → ℝ≥0∞ := fun g => c⁻¹ * β (t * g) with hβ'
  have hβ'm : Measurable β' := hβ0m.const_mul _
  have hwt : IsWt (nuP E k 0) β' := by
    refine ⟨hβ'm, fun g => ?_⟩
    simp only [hβ']
    rw [lintegral_const_mul c⁻¹ (f := fun h => β (t * (h * g))) (hβ0m.comp (measurable_mul_const g))]
    have := hN2 E k w l (fun h => β (h * (t * g))) (hβ.1.comp (measurable_mul_const _))
    rw [← ht] at this
    simp only [mul_assoc, inv_mul_cancel_left] at this
    rw [this, hβ.2 (t * g), mul_one, ENNReal.inv_mul_cancel hc0 hctop]

  have hH : ∀ᵐ h ∂nuP E k 0, h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)} := by
    set A := {h : GA E k | ¬ UU 0 h}
    have hA : nuP E k 0 A = 0 := ae_iff.1 hUU
    set S := toMeasurable (nuP E k 0) A
    have hS : MeasurableSet S := measurableSet_toMeasurable _ _
    have hS0 : nuP E k 0 S = 0 := by rw [measure_toMeasurable]; exact hA
    have hcm : Measurable fun h : GA E k => t * h * t⁻¹ := (measurable_const_mul t).mul_const _
    have := hN2 E k w l (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS, hS0, mul_zero] at this
    have h2 := (lintegral_eq_zero_iff ((measurable_one.indicator hS).comp hcm)).1 this
    filter_upwards [h2] with h hh
    by_contra hn
    have : t * h * t⁻¹ ∈ S := subset_toMeasurable _ _ hn
    simp [Set.indicator_of_mem this] at hh
  have hone : ∀ g, ∫⁻ r, ∫⁻ h, β (r⁻¹ * h * g) ∂nuP E k 0 ∂Measure.dirac (1 : GA E k) = 1 := fun g => by
    rw [lintegral_dirac]; simpa using hβ.2 g
  have hΦ'm : Measurable fun g => Φ (t * g) := hΦ.comp (measurable_const_mul t)
  have hΦ'H : ∀ h ∈ {h : GA E k | UU 0 (t * h * t⁻¹)}, ∀ g, Φ (t * (h * g)) = Φ (t * g) := by
    intro h hh g
    have := hΦu _ hh (t * g)
    simpa [mul_assoc] using this
  have hmap := map_wd μ β t
  have hsm : μ.withDensity (fun g => β (t * g)) = c • μ.withDensity β' := by
    rw [← withDensity_smul _ hβ'm]
    congr 1
    funext g
    simp [hβ', ← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop]
  have hint0 : Integrable (fun g => Φ (t * g)) (μ.withDensity fun g => β (t * g)) := by
    rw [← hmap, integrable_map_equiv]
    simpa [Function.comp_def] using hint
  have hint' : Integrable (fun g => Φ (t * g)) (μ.withDensity β') := by
    have h1 : μ.withDensity β' = c⁻¹ • μ.withDensity (fun g => β (t * g)) := by
      rw [hsm, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
    rw [h1]
    exact hint0.smul_measure (ENNReal.inv_ne_top.2 hc0)
  have hQ := hQ2 (GA E k) μ (nuP E k 0) (Measure.dirac 1) _ β' β hinv hH hwt hβ.1 hone
    (fun g => Φ (t * g)) hΦ'm hΦ'H hint'
  simp only [integral_dirac, one_mul] at hQ
  refine ⟨hQ.1, ?_⟩
  have e1 : ∫ g, Φ g ∂μ.withDensity β = ∫ g, Φ (t * g) ∂μ.withDensity fun g => β (t * g) := by
    rw [← hmap, integral_map_equiv]
    simp [MeasurableEquiv.coe_mulLeft]
  rw [e1, hsm, integral_smul_measure, hQ.2, hc, ENNReal.toReal_ofReal hcpos.le, Complex.real_smul]
  push_cast
  rfl

end PositivityTheory.AdelicQuotientData

end
end
