module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
public import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
public import GroundTheory.AutomorphicForms.GL2.GJGlobalMean
public import GroundTheory.AutomorphicForms.GL2.GJGlobalMellin
public import GroundTheory.AutomorphicForms.GL2.Bundle001
public import GroundTheory.AutomorphicForms.GL2.GJGlobalUnfold
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLatticeBounds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Set Filter NumberField ComplexConjugate
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne (K := K) (n := n)

theorem isLeftInvariant_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsLeftInvariant ψ) :
    IsLeftInvariant (fun g => conj (ψ g)) := fun γ g => by
  simp only [h γ g]

theorem isCuspidal_conj {ψ : AdelicGLn.AdelicGL K n → ℂ} (h : IsCuspidal ψ) :
    IsCuspidal (fun g => conj (ψ g)) := by
  intro r hr hrn g
  have := h r hr hrn g
  unfold constantTerm at this ⊢
  rw [integral_conj, this, map_zero]

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

theorem integrableOn_mul_tsum_comp {ψ : AdelicGLn.AdelicGL K n → ℂ} (hψc : Continuous ψ)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    {C : ℝ} (hC : ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C)
    {ι : Type*} [Countable ι] (e : ι → Matrix (Fin n) (Fin n) K) (he : Function.Injective e) :
    IntegrableOn (fun g : normOneGL (K := K) (n := n) => ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' i, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (e i) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])))
      (fundamentalDomain Γ₁) μ := by
  have hF : μ (fundamentalDomain Γ₁) < ⊤ := measure_fundamentalDomain_rationalGLOne_lt_top μ
  refine Measure.integrableOn_of_bounded (M := C) hF.ne ?_ ?_
  · refine ((hψc.comp continuous_subtype_val).measurable.mul ?_).aestronglyMeasurable
    refine UnfoldGL.measurable_tsum_of_summable (fun i => ?_) fun g => ?_
    · exact (hΦ.comp (continuous_const.mul (Units.continuous_val.comp
        continuous_subtype_val))).measurable
    · exact ((hsum g).comp_injective he).of_norm
  · refine Eventually.of_forall fun g => ?_
    rw [norm_mul]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hC g g.2)
    refine (norm_tsum_le_tsum_norm ((hsum g).comp_injective he)).trans ?_
    exact Summable.tsum_le_tsum_of_inj e he (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
      ((hsum g).comp_injective he) (hsum g)



theorem setIntegral_mul_tsum_det_eq_zero (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ = 0 := by
  obtain ⟨C, hC⟩ := hbd
  have hsplit : ∀ g : normOneGL (K := K) (n := n),
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
        ∑ r : Fin n, ψ (g : AdelicGLn.AdelicGL K n) *
          ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
            Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
              ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_det_eq_zero_eq_sum_rank (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, Finset.mul_sum]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_finsetSum _ fun r _ =>
      integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : (r : ℕ) = 0
  ·
    have hmem : (0 : Matrix (Fin n) (Fin n) K).rank = r := by rw [Matrix.rank_zero, hr]
    have h0 : ∀ g : normOneGL (K := K) (n := n),
        ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r},
          Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
            ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) = Φ 0 := by
      intro g
      have hu : ∀ ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r}, ξ = ⟨0, hmem⟩ := by
        intro ξ
        refine Subtype.ext ?_
        have h1 : (ξ : Matrix (Fin n) (Fin n) K).rank = 0 := ξ.2.trans hr
        exact (rank_eq_zero_iff (K := K) (n := n)).1 h1
      rw [tsum_eq_single (⟨0, hmem⟩ : {ξ : Matrix (Fin n) (Fin n) K // ξ.rank = r})
        fun ξ hξ => absurd (hu ξ) hξ]
      have hz : ratMat (0 : Matrix (Fin n) (Fin n) K) = 0 := by
        unfold ratMat
        exact Matrix.map_zero _ (map_zero _)
      rw [hz, mul_zero, zero_mul]
    have hm := setIntegral_fundamentalDomain_eq_zero μ hn hψc hψl hψ hψb
    rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => by rw [h0 g],
      integral_mul_const, hm, zero_mul]
  ·
    have hk : 0 < n - (r : ℕ) := Nat.sub_pos_of_lt r.2
    have hkn : n - (r : ℕ) < n := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero hr)
    have e : n - (n - (r : ℕ)) = r := Nat.sub_sub_self r.2.le
    have := UnfoldGL.setIntegral_mul_tsum_rank_eq_zero μ hψc hψl hψ hΦ y hsum ⟨C, hC⟩ hk hkn
    rw [e] at this
    exact this



theorem setIntegral_mul_tsum_eq_tsum_GL (hn : 2 ≤ n) {ψ : AdelicGLn.AdelicGL K n → ℂ}
    (hψc : Continuous ψ) (hψl : IsLeftInvariant ψ) (hψ : IsCuspidal ψ)
    (hψb : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ ≤ C)
    {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Continuous Φ) (y : AdelicGLn.AdelicGL K n)
    (hsum : ∀ g : AdelicGLn.AdelicGL K n, Summable fun ξ : Matrix (Fin n) (Fin n) K =>
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖)
    (hbd : ∃ C, ∀ g ∈ normOneGL (K := K) (n := n), ‖ψ g‖ * ∑' ξ : Matrix (Fin n) (Fin n) K,
      ‖Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (g : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ C) :
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ =
    ∫ g in fundamentalDomain Γ₁, ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' γ : GL (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) *
        ratMat (γ : Matrix (Fin n) (Fin n) K) *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) ∂μ := by
  obtain ⟨C, hC⟩ := hbd
  have hsing := setIntegral_mul_tsum_det_eq_zero μ hn hψc hψl hψ hψb hΦ y hsum ⟨C, hC⟩
  have hsplit : ∀ g : normOneGL (K := K) (n := n), ψ (g : AdelicGLn.AdelicGL K n) *
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) =
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' γ : GL (Fin n) K,
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) +
      ψ (g : AdelicGLn.AdelicGL K n) * ∑' ξ : {ξ : Matrix (Fin n) (Fin n) K // ξ.det = 0},
        Φ ((y : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (ξ : Matrix (Fin n) (Fin n) K) *
          ((g : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
    intro g
    rw [tsum_eq_tsum_GL_add (hsum (g : AdelicGLn.AdelicGL K n)).of_norm, mul_add]
  rw [setIntegral_congr_fun (measurableSet_fundamentalDomain Γ₁) fun g _ => hsplit g,
    integral_add (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Units.val_injective)
      (integrableOn_mul_tsum_comp μ hψc hΦ y hsum hC _ Subtype.val_injective), hsing, add_zero]

end GJGlobal

end

end GroundTheory.Automorphic
end

section

open MeasureTheory NumberField Topology Filter Set
open scoped NumberField.AdeleRing Classical nonZeroDivisors

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open GroundTheory.Global GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem continuous_of_mem_matrixSchwartzBruhat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) : Continuous Φ := by
  have hF := continuous_of_mem_schwartzBruhatPi (mem_matrixSchwartzBruhat.mp hΦ)
  have h : Φ = (fun z : Fin n × Fin n → 𝔸[K] => Φ (Matrix.of fun i j => z (i, j))) ∘
      (fun X : Matrix (Fin n) (Fin n) 𝔸[K] => fun p : Fin n × Fin n => X p.1 p.2) := rfl
  rw [h]
  exact hF.comp (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

theorem continuous_infNorm_coe_inv : Continuous fun g : AdelicGLn.AdelicGL K n =>
    infNorm ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  have hc : Continuous fun g : AdelicGLn.AdelicGL K n =>
      ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
    Units.continuous_val.comp continuous_inv
  unfold infNorm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun w _ => continuous_norm.comp ?_
  exact (continuous_apply w).comp (continuous_fst.comp (hc.matrix_elem i j))

theorem centralScale_mono {s t : {r : ℝ // 0 < r}} (h : (s : ℝ) ≤ t) :
    centralScale (K := K) n s ≤ centralScale (K := K) n t :=
  Real.rpow_le_rpow s.2.le h (inv_nonneg.2 (by positivity))

theorem exists_summable_bound {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (t₁ : {r : ℝ // 0 < r})
    {A B : Set (AdelicGLn.AdelicGL K n)} (hA : IsCompact A) (hB : IsCompact B) :
    ∃ u : Matrix (Fin n) (Fin n) K → ℝ, Summable u ∧ ∀ t : {r : ℝ // 0 < r}, (t₁ : ℝ) ≤ t →
      ∀ a ∈ A, ∀ b ∈ B, ∀ ξ, ‖Φ (((Reduction.centralSection K n t * a : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖ ≤ u ξ := by
  set M : ℕ := Module.finrank ℝ (Fin n × Fin n → mixedEmbedding.mixedSpace K) + 1 with hM
  obtain ⟨C₁, hC₁, I, hmaj⟩ := exists_majorant hΦ M
  set Q : Set (Matrix (Fin n) (Fin n) 𝔸ᶠ[K]) := (fun g : AdelicGLn.AdelicGL K n =>
    finMat ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) '' (A ∪ B) with hQ
  have hQc : IsCompact Q := (hA.union hB).image (continuous_finMat_coe.comp continuous_inv)
  obtain ⟨J, hJ⟩ := exists_ideal_mul_mul hQc I
  obtain ⟨R, hR⟩ := (hA.union hB).exists_bound_of_continuousOn
    (continuous_infNorm_coe_inv (K := K) (n := n)).continuousOn
  set m : ℝ := (max 1 (centralScale (K := K) n t₁)⁻¹) ^ M with hm
  have hm0 : 0 ≤ m := pow_nonneg (zero_le_one.trans (le_max_left _ _)) M
  set R' : ℝ := 1 + max R 0 with hR'
  refine ⟨fun ξ => C₁ * m * (R' * R') ^ M * latticeWeight J M ξ,
    (summable_latticeWeight J (by omega)).mul_left _, fun t ht a ha b hb ξ => ?_⟩
  have hpt := norm_le_twistedWeight hC₁ hmaj t a⁻¹ b ξ
  rw [inv_inv] at hpt
  have hxQ : finMat ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q :=
    ⟨a, Or.inl ha, rfl⟩
  have hyQ : finMat ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ∈ Q :=
    ⟨b, Or.inr hb, rfl⟩
  have htw := twistedWeight_le hJ M hxQ hyQ ξ
  have hRa : infNorm ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ≤ max R 0 := by
    have := hR a (Or.inl ha)
    rw [Real.norm_of_nonneg (infNorm_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have hRb : infNorm ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) ≤ max R 0 := by
    have := hR b (Or.inr hb)
    rw [Real.norm_of_nonneg (infNorm_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  have hmt : (max 1 (centralScale (K := K) n t)⁻¹) ^ M ≤ m := by
    refine pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_le_max le_rfl ?_) M
    exact inv_anti₀ (centralScale_pos n t₁) (centralScale_mono ht)
  have hlw := latticeWeight_nonneg J M ξ
  have hcomb : ((1 + infNorm ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) *
      (1 + infNorm ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]))) ^ M ≤
      (R' * R') ^ M := by
    refine pow_le_pow_left₀ (mul_nonneg (by linarith [infNorm_nonneg ((a⁻¹ :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])]) (by linarith [infNorm_nonneg ((b⁻¹ :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])])) ?_ M
    exact mul_le_mul (by linarith) (by linarith)
      (by linarith [infNorm_nonneg ((b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])])
      (by linarith [le_max_right R 0])
  calc ‖Φ (((Reduction.centralSection K n t * a : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ * (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖
      ≤ C₁ * (max 1 (centralScale (K := K) n t)⁻¹) ^ M * twistedWeight I M a⁻¹ b ξ := hpt
    _ ≤ C₁ * m * ((R' * R') ^ M * latticeWeight J M ξ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmt hC₁)
          (htw.trans (mul_le_mul_of_nonneg_right hcomb hlw))
          (twistedWeight_nonneg I M a⁻¹ b ξ) (mul_nonneg hC₁ hm0)
    _ = C₁ * m * (R' * R') ^ M * latticeWeight J M ξ := by ring

theorem continuous_centralSection_mul_coe : Continuous fun p : {r : ℝ // 0 < r} ×
    AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ((Reduction.centralSection K n p.1 * p.2.1 : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) := by
  have h : Continuous fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      (Reduction.centralSection K n p.1 * p.2.1 : AdelicGLn.AdelicGL K n) :=
    (Reduction.continuous_centralSection.comp continuous_fst).mul
      (continuous_fst.comp continuous_snd)
  exact Units.continuous_val.comp h

theorem continuous_snd_snd_coe : Continuous fun p : {r : ℝ // 0 < r} ×
    AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ((p.2.2 : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) :=
  Units.continuous_val.comp (continuous_snd.comp continuous_snd)

theorem exists_nhds_compact (p₀ : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n ×
    AdelicGLn.AdelicGL K n) :
    ∃ A B : Set (AdelicGLn.AdelicGL K n), IsCompact A ∧ IsCompact B ∧
      {p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n |
        (p₀.1 : ℝ) / 2 < p.1 ∧ p.2.1 ∈ A ∧ p.2.2 ∈ B} ∈ 𝓝 p₀ := by
  have := AdelicGLn.locallyCompactSpace K n
  obtain ⟨A, hA, hAn⟩ := exists_compact_mem_nhds p₀.2.1
  obtain ⟨B, hB, hBn⟩ := exists_compact_mem_nhds p₀.2.2
  refine ⟨A, B, hA, hB, ?_⟩
  have h1 : {p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n |
      (p₀.1 : ℝ) / 2 < p.1} ∈ 𝓝 p₀ :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_fst)).mem_nhds
      (half_lt_self p₀.1.2)
  have h2 : (Prod.snd ⁻¹' (A ×ˢ B) : Set ({r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n ×
      AdelicGLn.AdelicGL K n)) ∈ 𝓝 p₀ :=
    continuous_snd.continuousAt.preimage_mem_nhds (prod_mem_nhds hAn hBn)
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2.1, hp2.2⟩

theorem continuous_tsum_ratMat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Continuous (fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ (((Reduction.centralSection K n p.1 * p.2.1 :
        AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
          (p.2.2 : Matrix (Fin n) (Fin n) 𝔸[K]))) := by
  have hΦc := continuous_of_mem_matrixSchwartzBruhat hΦ
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨A, B, hA, hB, hU⟩ := exists_nhds_compact (K := K) (n := n) p₀
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound hΦ ⟨(p₀.1 : ℝ) / 2, half_pos p₀.1.2⟩ hA hB
  refine (continuousOn_tsum (s := {p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n ×
      AdelicGLn.AdelicGL K n | (p₀.1 : ℝ) / 2 < p.1 ∧ p.2.1 ∈ A ∧ p.2.2 ∈ B})
    (fun ξ => ?_) hu (fun ξ p hp => hbd p.1 hp.1.le p.2.1 hp.2.1 p.2.2
    hp.2.2 ξ)).continuousAt hU
  exact (hΦc.comp ((continuous_centralSection_mul_coe.matrix_mul continuous_const).matrix_mul
    continuous_snd_snd_coe)).continuousOn

theorem continuous_tsum_GL {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Continuous (fun p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ∑' γ : GL (Fin n) K, Φ ((Reduction.centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ *
        p.2.2 : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  have hΦc := continuous_of_mem_matrixSchwartzBruhat hΦ
  have heq : ∀ (p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n)
      (γ : GL (Fin n) K), ((Reduction.centralSection K n p.1 * p.2.1 * AdelicGLn.diagonal K n γ *
        p.2.2 : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      ((Reduction.centralSection K n p.1 * p.2.1 : AdelicGLn.AdelicGL K n) :
        Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat (γ : Matrix (Fin n) (Fin n) K) *
          (p.2.2 : Matrix (Fin n) (Fin n) 𝔸[K]) := fun p γ => by
    simp only [Units.val_mul, coe_diagonal]
  simp_rw [heq]
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨A, B, hA, hB, hU⟩ := exists_nhds_compact (K := K) (n := n) p₀
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound hΦ ⟨(p₀.1 : ℝ) / 2, half_pos p₀.1.2⟩ hA hB
  refine (continuousOn_tsum (s := {p : {r : ℝ // 0 < r} × AdelicGLn.AdelicGL K n ×
      AdelicGLn.AdelicGL K n | (p₀.1 : ℝ) / 2 < p.1 ∧ p.2.1 ∈ A ∧ p.2.2 ∈ B})
    (u := fun γ : GL (Fin n) K => u (γ : Matrix (Fin n) (Fin n) K))
    (fun γ => ?_) (hu.comp_injective (fun _ _ h => Units.ext h))
    (fun γ p hp => hbd p.1 hp.1.le p.2.1 hp.2.1 p.2.2 hp.2.2 _)).continuousAt hU
  exact (hΦc.comp ((continuous_centralSection_mul_coe.matrix_mul continuous_const).matrix_mul
    continuous_snd_snd_coe)).continuousOn

end GJGlobal

end

end GroundTheory.Automorphic
end
