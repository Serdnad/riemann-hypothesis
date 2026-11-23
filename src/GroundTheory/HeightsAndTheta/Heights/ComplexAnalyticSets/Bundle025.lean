module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory Set Relation
open scoped NNReal ENNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radial_lipschitzOnWith (x : E) (ℓ : E →L[ℝ] ℝ) {β δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun c => x + ((ℓ c - ℓ x) / β)⁻¹ • (c - x))
      {c | δ ≤ (ℓ c - ℓ x) / β ∧ ‖c - x‖ ≤ R} := by
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) ?_⟩
  rintro a ⟨ha, -⟩ b ⟨hb, hbR⟩
  set ta := (ℓ a - ℓ x) / β with hta_def
  set tb := (ℓ b - ℓ x) / β with htb_def
  have hta : 0 < ta := hδ.trans_le ha
  have htb : 0 < tb := hδ.trans_le hb
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [hta_def, div_zero] at hta
    exact lt_irrefl _ hta
  have hkey : x + ta⁻¹ • (a - x) - (x + tb⁻¹ • (b - x)) =
      ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x) := by
    simp only [smul_sub, sub_smul]; abel
  have hdiff : tb - ta = ℓ (b - a) / β := by
    rw [hta_def, htb_def, map_sub]; ring
  have hinv : |ta⁻¹ - tb⁻¹| ≤ ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) := by
    rw [inv_sub_inv hta.ne' htb.ne', hdiff, abs_div, abs_div, abs_of_pos (mul_pos hta htb), div_div]
    apply div_le_div₀ (by positivity)
    · rw [← Real.norm_eq_abs, norm_sub_rev a b]
      exact ℓ.le_opNorm _
    · exact mul_pos (abs_pos.2 hβ) (mul_pos hδ hδ)
    · exact mul_le_mul_of_nonneg_left (mul_le_mul ha hb hδ.le hta.le) (abs_nonneg _)
  rw [dist_eq_norm, dist_eq_norm, hkey]
  calc ‖ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x)‖
      ≤ ‖ta⁻¹ • (a - b)‖ + ‖(ta⁻¹ - tb⁻¹) • (b - x)‖ := norm_add_le _ _
    _ = ta⁻¹ * ‖a - b‖ + |ta⁻¹ - tb⁻¹| * ‖b - x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hta)]
    _ ≤ δ⁻¹ * ‖a - b‖ + ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) * R := by
        gcongr
    _ = (δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) * ‖a - b‖ := by ring

variable [MeasurableSpace E] [BorelSpace E]

theorem segment_hits_image_null {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {C : Set E} {x : E} (hx : x ∉ C) (ℓ : E →L[ℝ] ℝ) {α : ℝ}
    (hα : α ≠ ℓ x) (g : E →L[ℝ] F) {d : ℝ} (hd : 0 ≤ d) (hC : μH[d] C = 0) :
    μH[d] (g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty}) = 0 := by
  have hβ : α - ℓ x ≠ 0 := sub_ne_zero.2 hα
  have hsub : g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty} ⊆
      ⋃ j : ℕ, (g ∘ fun c => x + ((ℓ c - ℓ x) / (α - ℓ x))⁻¹ • (c - x)) ''
        (C ∩ {c | ((j : ℝ) + 1)⁻¹ ≤ (ℓ c - ℓ x) / (α - ℓ x) ∧ ‖c - x‖ ≤ (j : ℝ) + 1}) := by
    rintro _ ⟨m, ⟨hm, c, hcs, hcC⟩, rfl⟩
    rw [segment_eq_image'] at hcs
    obtain ⟨s, ⟨hs0, -⟩, rfl⟩ := hcs
    have hs : s ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hcC
      exact hx hcC
    have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hτ : (ℓ (x + s • (m - x)) - ℓ x) / (α - ℓ x) = s := by
      rw [map_add (f := _), map_smul, map_sub, hm, smul_eq_mul, add_sub_cancel_left, mul_div_assoc,
        div_self hβ, mul_one]
    obtain ⟨j, hj⟩ := exists_nat_gt (max s⁻¹ ‖s • (m - x)‖)
    refine mem_iUnion.2 ⟨j, x + s • (m - x), ⟨hcC, ?_, ?_⟩, ?_⟩
    · rw [hτ]
      have h1 : s⁻¹ < (j : ℝ) + 1 := by linarith [le_max_left s⁻¹ ‖s • (m - x)‖]
      calc ((j : ℝ) + 1)⁻¹ ≤ (s⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hspos) h1.le
        _ = s := inv_inv s
    · rw [add_sub_cancel_left]
      linarith [le_max_right s⁻¹ ‖s • (m - x)‖]
    · simp only [Function.comp_apply, hτ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs,
        one_smul, add_sub_cancel]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  obtain ⟨K, hK⟩ := radial_lipschitzOnWith x ℓ (β := α - ℓ x) (R := (j : ℝ) + 1)
    (show (0 : ℝ) < ((j : ℝ) + 1)⁻¹ by positivity)
  have hL := g.lipschitz.comp_lipschitzOnWith (hK.mono (inter_subset_right (s := C)))
  refine le_antisymm ?_ zero_le
  calc _ ≤ _ := hL.hausdorffMeasure_image_le hd
    _ = 0 := by rw [measure_mono_null inter_subset_left hC, mul_zero]

theorem diff_nonempty_of_hausdorffMeasure_null [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) : (U \ C).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
  obtain ⟨z, hz⟩ := hne
  have hlt : ((k : ℝ≥0) : ℝ≥0∞) < dimH U := by
    rw [Real.dimH_of_mem_nhds (hU.mem_nhds hz), hk]
    exact_mod_cast Nat.lt_succ_self k
  have htop := hausdorffMeasure_of_lt_dimH hlt
  rw [NNReal.coe_natCast, measure_mono_null h hC] at htop
  exact ENNReal.zero_ne_top htop

theorem convex_diff_isPreconnected [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {B : Set E}
    (hBo : IsOpen B) (hBc : Convex ℝ B) : IsPreconnected (B \ C) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  by_cases hxy : x = y
  · subst hxy
    exact ⟨{x}, singleton_subset_iff.2 hx, rfl, rfl, isPreconnected_singleton⟩
  let φ : E ≃L[ℝ] (Fin (k + 1) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hk, Module.finrank_fin_fun])
  obtain ⟨i, hi⟩ : ∃ i, φ x i ≠ φ y i := by
    by_contra h
    push Not at h
    exact hxy (φ.injective (funext h))
  let ℓ : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  let g : E →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (i.succAbove j)).comp
      (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  have hℓ : ∀ z, ℓ z = φ z i := fun z => rfl
  have hg : ∀ z, g z = Fin.removeNth i (φ z) := fun z => rfl
  have hαx : (φ x i + φ y i) / 2 ≠ ℓ x := by rw [hℓ]; intro h; apply hi; linarith
  have hαy : (φ x i + φ y i) / 2 ≠ ℓ y := by rw [hℓ]; intro h; apply hi; linarith
  have hvol : (volume : Measure (Fin k → ℝ)) = μH[(k : ℝ)] := by
    have := hausdorffMeasure_pi_real (ι := Fin k)
    rw [Fintype.card_fin] at this
    exact this.symm
  have hS0 : volume (g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ x m ∩ C).Nonempty} ∪
      g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ y m ∩ C).Nonempty}) = 0 := by
    rw [hvol]
    exact measure_union_null (segment_hits_image_null hx.2 ℓ hαx g (Nat.cast_nonneg k) hC)
      (segment_hits_image_null hy.2 ℓ hαy g (Nat.cast_nonneg k) hC)
  let ψ : (Fin k → ℝ) → E := fun w => φ.symm (Fin.insertNth i ((φ x i + φ y i) / 2) w)
  have hψc : Continuous ψ :=
    φ.symm.continuous.comp (continuous_const.finInsertNth i continuous_id)
  have hz₀ : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ B :=
    hBc hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  have hψz₀ : ψ (g ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by
    have h1 : φ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) i = (φ x i + φ y i) / 2 := by
      simp only [map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    simp only [ψ, hg]
    rw [← h1, Fin.insertNth_self_removeNth, ContinuousLinearEquiv.symm_apply_apply]
  have hWpos : 0 < volume (ψ ⁻¹' B) :=
    (hBo.preimage hψc).measure_pos volume ⟨_, show ψ _ ∈ B from hψz₀ ▸ hz₀⟩
  obtain ⟨w, hwB, hwS⟩ := nonempty_of_measure_ne_zero
    ((measure_sdiff_null hS0).symm ▸ hWpos.ne' : volume (ψ ⁻¹' B \ _) ≠ 0)
  have hφm : φ (ψ w) = Fin.insertNth i ((φ x i + φ y i) / 2) w := by
    simp only [ψ, ContinuousLinearEquiv.apply_symm_apply]
  have hℓm : ℓ (ψ w) = (φ x i + φ y i) / 2 := by rw [hℓ, hφm, Fin.insertNth_apply_same]
  have hgm : g (ψ w) = w := by rw [hg, hφm, Fin.removeNth_insertNth]
  have hxm : segment ℝ x (ψ w) ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hx.1 hwB hc, fun hcC => hwS (Or.inl ⟨ψ w, ⟨hℓm, c, hc, hcC⟩, hgm⟩)⟩
  have hmy : segment ℝ (ψ w) y ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hwB hy.1 hc, fun hcC =>
      hwS (Or.inr ⟨ψ w, ⟨hℓm, c, segment_symm ℝ (ψ w) y ▸ hc, hcC⟩, hgm⟩)⟩
  exact ⟨segment ℝ x (ψ w) ∪ segment ℝ (ψ w) y, union_subset hxm hmy,
    Or.inl (left_mem_segment ℝ x (ψ w)), Or.inr (right_mem_segment ℝ (ψ w) y),
    (convex_segment x (ψ w)).isPreconnected.union (ψ w) (right_mem_segment ℝ x (ψ w))
      (left_mem_segment ℝ (ψ w) y) (convex_segment (ψ w) y).isPreconnected⟩

theorem HausdorffNullComplementConnected.proof : HausdorffNullComplementConnected.Statement := by
  intro E _ _ _ _ _ D C hDo hDc hC
  by_cases h0 : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    exact Set.subsingleton_of_subsingleton.isPreconnected
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h0
  have hC' : μH[(k : ℝ)] C = 0 := by
    rw [hk, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hC
    exact hC
  choose! r hr0 hrD using Metric.isOpen_iff.1 hDo
  have hU : D \ C = ⋃ z ∈ D, ball z (r z) \ C := by
    ext z
    simp only [mem_sdiff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz, hzC⟩
      exact ⟨z, hz, mem_ball_self (hr0 z hz), hzC⟩
    · rintro ⟨w, hw, hzb, hzC⟩
      exact ⟨hrD w hw hzb, hzC⟩
  rw [hU]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun z _ => convex_diff_isPreconnected hk hC' isOpen_ball (convex_ball z (r z))) ?_
  intro z hz w hw
  refine hDc.induction₂' (fun a b => ReflTransGen
      (fun i j => ((ball i (r i) \ C) ∩ (ball j (r j) \ C)).Nonempty ∧ i ∈ D) a b) ?_
    (fun a b c _ _ _ h1 h2 => h1.trans h2) hz hw
  intro a ha
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a (hr0 a ha)), self_mem_nhdsWithin]
    with b hb hbD
  obtain ⟨p, ⟨hpa, hpb⟩, hpC⟩ := diff_nonempty_of_hausdorffMeasure_null hk hC'
    (isOpen_ball.inter isOpen_ball) ⟨b, hb, mem_ball_self (hr0 b hbD)⟩
  exact ⟨ReflTransGen.single ⟨⟨p, ⟨hpa, hpC⟩, hpb, hpC⟩, ha⟩,
    ReflTransGen.single ⟨⟨p, ⟨hpb, hpC⟩, hpa, hpC⟩, hbD⟩⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing Matrix

theorem derivation_mem_of_mem_sq {T : Type} [CommRing T] (P : Ideal T) (D : Derivation ℤ T T)
    {x : T} (hx : x ∈ P ^ 2) : D x ∈ P := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ ha) (P.mul_mem_right _ hb)
  · rw [map_add (f := _)]; exact P.add_mem ha hb

theorem mem_of_derivation_det_not_mem {T : Type} [CommRing T] (P : Ideal T) [P.IsPrime] {h : ℕ}
    (D : Fin h → Derivation ℤ T T) (f : Fin h → T) (hf : ∀ i, f i ∈ P)
    (hdet : (Matrix.of fun i j => D j (f i)).det ∉ P) (b : Fin h → T) (t : T) (ht : t ∉ P)
    (hsum : t * ∑ i, b i * f i ∈ P ^ 2) (i : Fin h) : b i ∈ P := by
  set A : Matrix (Fin h) (Fin h) T := Matrix.of fun i j => D j (f i) with hA

  have hv : ∀ j, (b ᵥ* A) j ∈ P := by
    intro j
    have h1 := derivation_mem_of_mem_sq P (D j) hsum

    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_sum] at h1
    have h2 : (∑ i, b i * f i) * D j t ∈ P :=
      P.mul_mem_right _ (P.sum_mem fun i _ => P.mul_mem_left _ (hf i))
    have h3 : t * ∑ i, D j (b i * f i) ∈ P := by
      have := P.sub_mem h1 h2; simpa using this
    have h4 : ∑ i, D j (b i * f i) ∈ P :=
      ((Ideal.IsPrime.mem_or_mem inferInstance h3).resolve_left ht)
    have h5 : ∑ i, D j (b i * f i) - ∑ i, f i * D j (b i) = (b ᵥ* A) j := by
      rw [← Finset.sum_sub_distrib]
      simp only [Matrix.vecMul, dotProduct, hA, Matrix.of_apply, Derivation.leibniz, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [← h5]
    exact P.sub_mem h4 (P.sum_mem fun i _ => P.mul_mem_right _ (hf i))

  have hw : (b ᵥ* A ᵥ* A.adjugate) i = A.det * b i := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
      Pi.smul_apply, smul_eq_mul]
  have hmem : (b ᵥ* A ᵥ* A.adjugate) i ∈ P := by
    simp only [Matrix.vecMul, dotProduct]
    exact P.sum_mem fun j _ => P.mul_mem_right _ (hv j)
  rw [hw] at hmem
  exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left hdet

theorem DerivationCotangentIndependent.proof : DerivationCotangentIndependent.Statement := by
  intro T _ P _ h D f hf hdet a hsum i

  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl (Finset.univ : Finset (Fin h)) a
  choose b hb using fun k => hs k (Finset.mem_univ k)

  have hmax : maximalIdeal (Localization.AtPrime P) = P.map (algebraMap T (Localization.AtPrime P)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hsq : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) ∈ (P ^ 2).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_pow, ← hmax]
    have : algebraMap T (Localization.AtPrime P) (∑ k, b k * f k) =
        algebraMap T (Localization.AtPrime P) (s : T) * ∑ k, a k * algebraMap T (Localization.AtPrime P) (f k) := by

      simp only [map_sum, map_mul, Finset.mul_sum, hb, Algebra.smul_def]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hsum
  obtain ⟨⟨⟨y, hy⟩, u⟩, hyu⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)).1 hsq
  rw [← map_mul] at hyu
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).1 hyu
  have hbi : b i ∈ P := by
    refine mem_of_derivation_det_not_mem P D f hf hdet b ((c : T) * (u : T)) ?_ ?_ i
    · exact (P.primeCompl.mul_mem c.2 u.2 : _)
    · have : (c : T) * (u : T) * ∑ k, b k * f k = (c : T) * y := by rw [← hc]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hy

  have hsa : algebraMap T (Localization.AtPrime P) (s : T) * a i ∈ maximalIdeal (Localization.AtPrime P) := by
    rw [← Algebra.smul_def, ← hb i]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hbi
  have hs' : algebraMap T (Localization.AtPrime P) (s : T) ∉ maximalIdeal (Localization.AtPrime P) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P]; exact s.2
  exact ((maximalIdeal.isMaximal (Localization.AtPrime P)).isPrime.mem_or_mem hsa).resolve_left hs'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open AdicCompletion Polynomial

section

variable {R : Type} [CommRing R] (J : Ideal R)

theorem CompletionNormalDescent.evalₐ_algebraMap (n : ℕ) (x : R) :
    evalₐ J n (algebraMap R (AdicCompletion J R) x) = Ideal.Quotient.mk (J ^ n) x := by
  rw [(evalₐ J n).commutes]
  rfl

variable [IsNoetherianRing R]

theorem CompletionNormalDescent.algebraMap_injective (hJ : J ≤ (⊥ : Ideal R).jacobson) :
    Function.Injective (algebraMap R (AdicCompletion J R)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have H : IsHausdorff J R := IsHausdorff.of_le_jacobson J R (by simpa only [Ideal.jacobson_bot] using hJ)
  refine H.haus a fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have := CompletionNormalDescent.evalₐ_algebraMap J n a
  rw [ha, _root_.map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

theorem CompletionNormalDescent.dvd_of_dvd_completion (hJ : J ≤ (⊥ : Ideal R).jacobson) (a b : R)
    (x : AdicCompletion J R)
    (h : algebraMap R (AdicCompletion J R) a = algebraMap R (AdicCompletion J R) b * x) : b ∣ a := by
  have H : IsHausdorff J (R ⧸ Ideal.span {b}) := IsHausdorff.of_le_jacobson J _ (by simpa only [Ideal.jacobson_bot] using hJ)
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
  have h1 := congrArg (evalₐ J n) h
  rw [map_mul, CompletionNormalDescent.evalₐ_algebraMap, CompletionNormalDescent.evalₐ_algebraMap, ← hr,
    ← map_mul, Ideal.Quotient.eq] at h1
  have h2 : Ideal.Quotient.mk (Ideal.span {b}) a = Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) := by
    rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b), zero_mul,
      sub_zero]
  have h3 : Ideal.Quotient.mk (Ideal.span {b}) (a - b * r) =
      (a - b * r) • (Ideal.Quotient.mk (Ideal.span {b}) 1) := by
    rw [Algebra.smul_def, _root_.map_one, mul_one]
    rfl
  rw [h2, h3]
  exact Submodule.smul_mem_smul h1 Submodule.mem_top

end

theorem CompletionNormalDescent.proof : CompletionNormalDescent.Statement := by
  intro R _ J _ hJ hD hIC
  have hinj := CompletionNormalDescent.algebraMap_injective J hJ
  have : IsDomain R := hinj.isDomain (algebraMap R (AdicCompletion J R))
  refine ⟨inferInstance, ?_⟩
  set f := algebraMap R (AdicCompletion J R) with hf
  let L := FractionRing (AdicCompletion J R)
  let g : R →+* L := (algebraMap (AdicCompletion J R) L).comp f
  have hg : Function.Injective g := (IsFractionRing.injective (AdicCompletion J R) L).comp hinj
  let φ : FractionRing R →+* L := IsFractionRing.lift hg
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap (AdicCompletion J R) L (f r) :=
    fun r => IsFractionRing.lift_algebraMap hg r
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro z hz
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R (FractionRing R) b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
    exact hb0

  have hint : IsIntegral (AdicCompletion J R) (φ (algebraMap R (FractionRing R) a /
      algebraMap R (FractionRing R) b)) := by
    obtain ⟨p, hp, hpz⟩ := hz
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [eval₂_map]
    have : (algebraMap (AdicCompletion J R) L).comp f = φ.comp (algebraMap R (FractionRing R)) := by
      ext r; exact (hφ r).symm
    rw [this, ← hom_eval₂, hpz, _root_.map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hay : f a = f b * y := by
    apply IsFractionRing.injective (AdicCompletion J R) L
    rw [map_mul, hy, map_div₀, hφ, hφ]
    have hfb : algebraMap (AdicCompletion J R) L (f b) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (AdicCompletion J R) L),
        map_eq_zero_iff _ hinj]
      exact hb0
    exact (mul_div_cancel₀ _ hfb).symm
  obtain ⟨r, rfl⟩ := CompletionNormalDescent.dvd_of_dvd_completion J hJ a b y hay
  refine ⟨r, ?_⟩
  rw [map_mul]
  exact (mul_div_cancel_left₀ _ hbK).symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem FlatDimFormula.proof : FlatDimFormula.Statement := by
  intro A B _ _ _ _ _ hA hB hloc hflat
  set I : Ideal B := (maximalIdeal A).map (algebraMap A B) with hI

  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩

  have hIle : I ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le (algebraMap A B)
  have : Nontrivial (B ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hIle)
  have : IsLocalRing (B ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  rw [← hI, hmap] at key
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B ⧸ I), key, WithBot.coe_add]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibresRegular.Statement : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A], Algebra.FiniteType k A →
    ∀ (m : Ideal A), m.IsMaximal → ∀ (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      IsRegularLocalRing (primeFibreLocalRing A P)

noncomputable def polyOriginIdeal : Ideal (MvPolynomial (Fin 1) ℂ) :=
  RingHom.ker (MvPolynomial.eval (0 : Fin 1 → ℂ))

theorem polyOriginIdeal_isMaximal : polyOriginIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun z => ⟨MvPolynomial.C z, by simp⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
