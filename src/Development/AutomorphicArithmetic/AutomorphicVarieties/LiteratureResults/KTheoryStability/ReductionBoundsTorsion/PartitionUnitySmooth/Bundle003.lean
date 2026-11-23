module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Chebyshev
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem re_nonneg {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    0 ≤ (star x ⬝ᵥ (mat h w *ᵥ x)).re :=
  (Complex.le_def.1 ((hh w).posSemidef.dotProduct_mulVec_nonneg x)).1

private theorem qR_nonneg {h : HS L N} (hh : h ∈ Pos L N) (z : VR L N) : 0 ≤ qR h z :=
  Finset.sum_nonneg fun w _ => re_nonneg hh w _

private theorem qR_para (h : HS L N) (a b : VR L N) : qR h (a - b) + qR h (a + b) = 2 * qR h a + 2 * qR h b := by
  simp only [qR, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, star_sub, star_add, mulVec_sub, mulVec_add, sub_dotProduct, add_dotProduct,
    dotProduct_sub, dotProduct_add, Complex.sub_re, Complex.add_re]
  ring

private theorem toR_add (u v : Lat L N) : toR (u + v) = toR u + toR v := by
  funext w a; simp [toR]

private def bb (h : HS L N) (u v : Lat L N) : ℝ := ∑ w, (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)).re

private theorem bb_add (h : HS L N) (u v : Lat L N) : bb h u (v + u) = bb h u v + q h u := by
  simp only [bb, q, qR, toR_add, Pi.add_apply, mulVec_add, dotProduct_add, Complex.add_re, Finset.sum_add_distrib]

private theorem bb_sq (h : HS L N) (u v : Lat L N) :
    0 ≤ qR (rk h v) (toR u) ∧ bb h u v ^ 2 ≤ Fintype.card (InfinitePlace L) * qR (rk h v) (toR u) := by
  have e : ∀ w, (star (toR u w) ⬝ᵥ (mat (rk h v) w *ᵥ toR u w)).re =
      Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)) := by
    intro w
    have e1 : mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w)) := rfl
    rw [e1, dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
      star_dotProduct (mat h w *ᵥ toR v w), Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have e2 : qR (rk h v) (toR u) = ∑ w, Complex.normSq (star (toR u w) ⬝ᵥ (mat h w *ᵥ toR v w)) :=
    Finset.sum_congr rfl fun w _ => e w
  rw [e2]
  refine ⟨Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _, sq_sum_le_card_mul_sum_sq.trans ?_⟩
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (Nat.cast_nonneg _)
  rw [sq]; exact Complex.re_sq_le_normSq _

private theorem rho_mem (x : ℝ) : 0 ≤ rho x ∧ rho x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem rho_one {x : ℝ} (hx : x ≤ 1) : rho x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

private theorem rho_zero {x : ℝ} (hx : 4 ≤ x) : rho x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem num1 {r B a F G : ℝ} (h1 : B ^ 2 ≤ r * F) (h2 : (B + a) ^ 2 ≤ r * G) : a ^ 2 / 2 ≤ r * (F + G) := by
  nlinarith [sq_nonneg (2 * B + a)]

private theorem num2 {r a s C n Z W : ℝ} (hr : 0 < r) (ha : 0 < a) (hs : 0 < s) (hC : 0 < C) (hZ : 1 ≤ Z) (hW : 0 ≤ W)
    (h1 : s ≤ 16 * a) (h2 : Z ≤ C * n) (h3 : n * (a ^ 2 / 2) ≤ r * (W + W)) : 1 / (1024 * r * C) ≤ (s ^ 2 * Z)⁻¹ * W := by
  rw [← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (s ^ 2 * Z) ≤ 1 * ((16 * a) ^ 2 * (C * n)) := by gcongr
    _ = 512 * C * (n * (a ^ 2 / 2)) := by ring
    _ ≤ 512 * C * (r * (W + W)) := by gcongr
    _ = _ := by ring

private theorem term_low {C : ℝ} (hC : 0 < C) {h : HS L N} (hh : h ∈ Pos L N)
    (hfin : ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite) {s : ℝ} (hs : 0 < s)
    (hcnt : (({v : Lat L N | q h v ≤ 16 * (s / 4)}.ncard : ℕ) : ℝ) ≤ C * ({v : Lat L N | q h v ≤ s / 4}.ncard : ℕ))
    (u : Lat L N) (ha : 0 < q h u) (h1 : s ≤ 16 * q h u) (h2 : 4 * q h u ≤ s) :
    1 / (1024 * (Fintype.card (InfinitePlace L) : ℝ) * C) ≤ qR (term s h) (toR u) := by
  classical
  have hz : ∀ v, v ∉ (hfin (16 * (s / 4))).toFinset → rho (q h v / s) = 0 := fun v hv => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hv
    exact rho_zero (by rw [le_div_iff₀ hs]; linarith)
  have hone : ∀ v, q h v ≤ s → v ∈ (hfin (16 * (s / 4))).toFinset ∧ rho (q h v / s) = 1 := fun v hv =>
    ⟨by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; linarith, rho_one ((div_le_one hs).2 hv)⟩
  rw [Set.ncard_eq_toFinset_card _ (hfin _), Set.ncard_eq_toFinset_card _ (hfin _)] at hcnt
  have hS : ∀ v ∈ (hfin (s / 4)).toFinset, q h v ≤ s / 4 := fun v hv => by
    rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  generalize (hfin (16 * (s / 4))).toFinset = T at hz hone hcnt
  generalize (hfin (s / 4)).toFinset = S at hS hcnt
  have eZ : zed s h = ∑ v ∈ T, rho (q h v / s) :=
    finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (hz v hn)
  have eW : (∑ᶠ v : Lat L N, rho (q h v / s) • rk h v) = ∑ v ∈ T, rho (q h v / s) • rk h v :=
    finsum_eq_sum_of_support_subset _ fun v hv => by_contra fun hn => hv (by simp only [hz v hn, zero_smul])
  have eT : qR (term s h) (toR u) = (s ^ 2 * zed s h)⁻¹ * ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u) := by

    rw [← evR_apply, term, eW, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul, evR_apply]
  have hq0 : q h 0 ≤ s := by
    have : toR (0 : Lat L N) = 0 := by funext w a; simp [toR]
    simp [q, qR, this, hs.le]
  have hZ1 : 1 ≤ zed s h := by
    rw [eZ, ← (hone 0 hq0).2]
    exact Finset.single_le_sum (f := fun v => rho (q h v / s)) (fun v _ => (rho_mem _).1) (hone 0 hq0).1
  have hZ2 : zed s h ≤ C * S.card := by
    refine le_trans ?_ hcnt
    rw [eZ]
    exact (Finset.sum_le_card_nsmul _ _ 1 fun v _ => (rho_mem _).2).trans (by simp)
  have hnn : ∀ v, 0 ≤ rho (q h v / s) * qR (rk h v) (toR u) := fun v => mul_nonneg (rho_mem _).1 (bb_sq h u v).1
  have hsub : ∀ S' : Finset (Lat L N), (∀ v ∈ S', q h v ≤ s) →
      ∑ v ∈ S', qR (rk h v) (toR u) ≤ ∑ v ∈ T, rho (q h v / s) * qR (rk h v) (toR u) := by
    intro S' hS'
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (hone v (hS' v hv)).1) fun v _ _ => hnn v)
    rw [(hone v (hS' v hv)).2, one_mul]
  have a1 := hsub S fun v hv => (hS v hv).trans (by linarith)
  have a2 := hsub (S.image (· + u)) fun v' hv' => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hv'
    have k1 := qR_para h (toR v) (toR u)
    have k2 := qR_nonneg hh (toR v - toR u)
    have k3 := hS v hv
    rw [← toR_add] at k1
    unfold q at k3 h2 ⊢
    linarith
  rw [Finset.sum_image fun a _ b _ e => add_right_cancel e] at a2
  have hr : (0 : ℝ) < Fintype.card (InfinitePlace L) := Nat.cast_pos.2 Fintype.card_pos
  rw [eT]
  refine num2 hr ha hs hC hZ1 (Finset.sum_nonneg fun v _ => hnn v) h1 hZ2 ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (add_le_add a1 a2) hr.le)
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← nsmul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun v _ => num1 (bb_sq h u v).2 ?_
  rw [← bb_add]; exact (bb_sq h u _).2

theorem pf_GRLow : GRLow := by
  intro hB hCt hE hTL L _ _ N hN μ hμ
  obtain ⟨C, hC, hcnt⟩ := hCt L N 16
  obtain ⟨_, hT⟩ := hTL L N hN
  obtain ⟨c, C2, hc, hcmp⟩ := hμ.cmp
  have hr : (0 : ℝ) < Fintype.card (InfinitePlace L) := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨min (1 / 16) (1 / (1024 * (Fintype.card (InfinitePlace L) : ℝ) * C)),
    lt_min (by norm_num) (one_div_pos.2 (mul_pos (mul_pos (by norm_num) hr) hC)), fun h hh => ?_⟩
  obtain ⟨-, hRP, hge⟩ := hE L N hN μ hμ h hh
  obtain ⟨u, hu, e⟩ := ((hB L N hN).1 _ hRP).2.2.1
  obtain ⟨hl, hlq, -, hdP, hfin⟩ := (hB L N hN).1 h hh
  have hμ0 : 0 < μ h := (mul_pos hc ((hB L N hN).1 _ hdP).1).trans_le (hcmp h hh).1
  have ha : 0 < q h u := hl.trans_le (hlq u hu)
  rw [← e]
  by_cases hcase : 1 / 16 ≤ μ h * q h u
  · exact (min_le_left _ _).trans (hcase.trans (hge (toR u)))
  refine (min_le_right _ _).trans ?_
  obtain ⟨k, hk0, hk1⟩ := exists_mem_Ico_zpow (mul_pos (show (0 : ℝ) < 16 by norm_num) ha) (show (1 : ℝ) < 4 by norm_num)
  have hp : ∀ j : ℤ, (0 : ℝ) < 4 ^ j := fun j => zpow_pos (by norm_num) _
  rw [zpow_add_one₀ (by norm_num)] at hk1
  refine (term_low hC hh hfin (hp k) (hcnt h hh _ (div_pos (hp k) (by norm_num)).le) u ha hk0 (by linarith)).trans ?_
  obtain ⟨k1, -, hk1'⟩ := exists_mem_Ico_zpow (div_pos (show (0 : ℝ) < 4 by norm_num) hμ0) (show (1 : ℝ) < 4 by norm_num)
  obtain ⟨k2, hk2, -⟩ := exists_mem_Ico_zpow hl (show (1 : ℝ) < 4 by norm_num)
  have hsupp : (Function.support fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) • term ((4 : ℝ) ^ j) h) ⊆
      (insert k (Finset.Icc k2 k1) : Finset ℤ) := by
    intro j hj
    by_contra hn
    have hn' : j < k2 ∨ k1 < j := by
      simp only [Finset.coe_insert, Finset.coe_Icc, Set.mem_insert_iff, Set.mem_Icc] at hn
      omega
    refine hj ?_
    rcases hn' with h1 | h1
    · have : 4 * (4 : ℝ) ^ j ≤ lam h := by
        refine le_trans ?_ hk2
        rw [mul_comm, ← zpow_add_one₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      simp only [(hT _ (hp j) h hh 0).2.1 this, smul_zero]
    · have : 4 ≤ (4 : ℝ) ^ j * μ h := by
        rw [← div_le_iff₀ hμ0]
        exact hk1'.le.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
      simp only [rho_zero this, zero_smul]
  have h1 : rho ((4 : ℝ) ^ k * μ h) = 1 := by
    refine rho_one ((mul_le_mul_of_nonneg_right hk0 hμ0.le).trans ?_)
    have := not_le.1 hcase
    linarith [mul_comm (μ h) (q h u), mul_assoc 16 (q h u) (μ h)]
  change _ ≤ evR (toR u) (ret μ h)

  rw [ret, finsum_eq_sum_of_support_subset _ hsupp, map_add (f := _), map_sum]
  simp only [map_smul, smul_eq_mul, evR_apply]
  refine le_add_of_nonneg_of_le (mul_nonneg hμ0.le (qR_nonneg hh _)) ?_
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j : ℤ => rho ((4 : ℝ) ^ j * μ h) * qR (term ((4 : ℝ) ^ j) h) (toR u))
    (fun j _ => mul_nonneg (rho_mem _).1 (hT _ (hp j) h hh _).1.1) (Finset.mem_insert_self k _))
  simp only [h1, one_mul]

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem qR_smul_VR {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) (c : ℝ)
    (z : VR L N) : qR h (c • z) = c ^ 2 * qR h z := by
  show ∑ w, (star ((c • z) w) ⬝ᵥ mat h w *ᵥ (c • z) w).re =
    c ^ 2 * ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : (c • z) w = (c : ℂ) • z w := by
    ext i; simp [Complex.real_smul]
  rw [e, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul, Complex.conj_ofReal]
  ring

private theorem qR_pos_of_mem_Pos_of_VR_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) (z : VR L N) (hz : z ≠ 0) : 0 < qR h z := by
  obtain ⟨w0, hw0⟩ : ∃ w, z w ≠ 0 := by
    by_contra hc; push_neg at hc; exact hz (funext hc)
  show 0 < ∑ w, (star (z w) ⬝ᵥ mat h w *ᵥ z w).re
  have hnn : ∀ w, 0 ≤ (star (z w) ⬝ᵥ mat h w *ᵥ z w).re := fun w => by
    have := (hp w).posSemidef.dotProduct_mulVec_nonneg (z w)
    exact (Complex.nonneg_iff.mp this).1
  have hpos : 0 < (star (z w0) ⬝ᵥ mat h w0 *ᵥ z w0).re := (hp w0).re_dotProduct_pos hw0
  exact Finset.sum_pos' (fun w _ => hnn w) ⟨w0, Finset.mem_univ _, hpos⟩

private theorem continuous_qR_comp {L : Type} [Field L] [NumberField L] {N : ℕ} {X : Type*}
    [TopologicalSpace X] {f : X → HS L N} {g : X → VR L N} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => qR (f x) (g x) := by
  show Continuous fun x => ∑ w, (star (g x w) ⬝ᵥ mat (f x) w *ᵥ g x w).re
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  have h1 : Continuous fun x => g x w := (continuous_apply w).comp hg
  have h2 : Continuous fun x => mat (f x) w :=
    (continuous_apply w).comp (continuous_subtype_val.comp hf)
  exact h1.star.dotProduct (h2.matrix_mulVec h1)

private theorem qR_zero_right {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N) :
    qR h 0 = 0 := by
  simpa using qR_smul_VR h 0 0

private theorem exists_pos_smul_unit_sphere_eq_of_ne_zero {L : Type} [Field L] [NumberField L] {N : ℕ} (z : VR L N)
    (hz : z ≠ 0) : ∃ r : ℝ, 0 < r ∧ ∃ u ∈ Metric.sphere (0 : VR L N) 1, z = r • u := by
  refine ⟨‖z‖, norm_pos_iff.mpr hz, ‖z‖⁻¹ • z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

private theorem ne_zero_of_mem_unit_sphere_VR {L : Type} [Field L] [NumberField L] {N : ℕ}
    (u : VR L N) (hu : u ∈ Metric.sphere (0 : VR L N) 1) : u ≠ 0 := by
  rintro rfl
  simp at hu

private theorem exists_qR_le_mul_qR_on_compact_subset_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (K : Set (HS L N))
    (hK : IsCompact K) (hKP : K ⊆ Pos L N) (h0 : HS L N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ z, qR h0 z ≤ C * qR h z := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hc : ContinuousOn (fun p : HS L N × VR L N => qR h0 p.2 / qR p.1 p.2)
      (K ×ˢ Metric.sphere (0 : VR L N) 1) := by
    refine ContinuousOn.div ?_ (continuous_qR_comp continuous_fst continuous_snd).continuousOn ?_
    · exact (continuous_qR_comp continuous_const continuous_snd).continuousOn
    · rintro ⟨h, z⟩ ⟨hh, hz⟩
      exact (qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) z (ne_zero_of_mem_unit_sphere_VR z hz)).ne'
  obtain ⟨C, hC⟩ := (hK.prod hS).bddAbove_image hc
  refine ⟨max C 0, le_max_right _ _, fun h hh z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp [qR_zero_right]
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h (hKP hh) u (ne_zero_of_mem_unit_sphere_VR u hu)
  have hb : qR h0 u / qR h u ≤ C := hC ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  have h1 : qR h0 u ≤ max C 0 * qR h u := by
    rw [div_le_iff₀ hpu] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpu.le)
  rw [qR_smul_VR, qR_smul_VR]
  calc r ^ 2 * qR h0 u ≤ r ^ 2 * (max C 0 * qR h u) := mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = max C 0 * (r ^ 2 * qR h u) := by ring

private theorem eventually_nhds_unit_sphere_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ u ∈ Metric.sphere (0 : VR L N) 1,
      |qR k u - qR h u| - 1 / 2 * qR h u < 0 := by
  have hS : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have c1 : Continuous fun p : HS L N × VR L N => qR p.1 p.2 :=
    continuous_qR_comp continuous_fst continuous_snd
  have c2 : Continuous fun p : HS L N × VR L N => qR h p.2 :=
    continuous_qR_comp continuous_const continuous_snd
  refine hS.eventually_forall_of_forall_eventually fun u hu => ?_
  have hpu : 0 < qR h u := qR_pos_of_mem_Pos_of_VR_ne_zero h hp u (ne_zero_of_mem_unit_sphere_VR u hu)
  set f : HS L N × VR L N → ℝ := fun p => |qR p.1 p.2 - qR h p.2| - 1 / 2 * qR h p.2 with hf
  have hcont : Continuous f :=
    ((c1.sub c2).abs).sub (continuous_const.mul c2)
  have hv : f (h, u) < 0 := by
    show |qR h u - qR h u| - 1 / 2 * qR h u < 0
    rw [sub_self, abs_zero, zero_sub, neg_lt_zero]
    linarith
  have h2 : ∀ᶠ p in nhds (h, u), f p < 0 := hcont.continuousAt.eventually (Iio_mem_nhds hv)
  filter_upwards [h2] with p hp'
  exact hp'

private theorem eventually_nhds_abs_qR_sub_le_half_of_mem_Pos {L : Type} [Field L] [NumberField L] {N : ℕ} (h : HS L N)
    (hp : h ∈ Pos L N) :
    ∀ᶠ k in nhds h, ∀ z : VR L N, |qR k z - qR h z| ≤ 1 / 2 * qR h z := by
  filter_upwards [eventually_nhds_unit_sphere_of_mem_Pos h hp] with k hk z
  rcases eq_or_ne z 0 with rfl | hz
  · rw [qR_zero_right, qR_zero_right]
    norm_num
  obtain ⟨r, -, u, hu, rfl⟩ := exists_pos_smul_unit_sphere_eq_of_ne_zero z hz
  rw [qR_smul_VR, qR_smul_VR, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
  have h1 : |qR k u - qR h u| ≤ 1 / 2 * qR h u := by linarith [hk u hu]
  calc r ^ 2 * |qR k u - qR h u| ≤ r ^ 2 * (1 / 2 * qR h u) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = 1 / 2 * (r ^ 2 * qR h u) := by ring

theorem pf_GProper : GProper := by
  intro hB L _ _ N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨?_, ?_⟩
    · have hu : Pos L 0 = Set.univ := by
        ext h
        simp only [Set.mem_univ, iff_true]
        intro w
        refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => absurd (Subsingleton.elim x 0) hx
        exact h.2 w
      rw [hu]
      exact isOpen_univ
    · intro K _ _
      apply Set.Subsingleton.finite
      intro a _ b _
      exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨hPos, hEq, -, hCl, -, -⟩ := hB L N hN
  refine ⟨?_, ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun h hh => ?_
    filter_upwards [eventually_nhds_abs_qR_sub_le_half_of_mem_Pos h hh] with k hk
    exact (hCl (1 / 2) (by norm_num) le_rfl h hh k hk).1
  intro K hK hKP
  rcases K.eq_empty_or_nonempty with rfl | ⟨h0, hh0⟩
  · simp
  obtain ⟨C, hC0, hC⟩ := exists_qR_le_mul_qR_on_compact_subset_Pos K hK hKP h0
  have hbd : ∀ i : Fin N, ∃ B : ℝ, ∀ h ∈ K, q h (Pi.single i 1 : UpperTheory.V.KT.Lat L N) ≤ B := by
    intro i
    have hc : Continuous fun h : HS L N => qR h (toR (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) :=
      continuous_qR_comp continuous_id continuous_const
    obtain ⟨B, hB'⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨B, fun h hh => hB' ⟨h, hh, rfl⟩⟩
  choose B hBd using hbd
  have hF : (⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}).Finite :=
    Set.finite_iUnion fun i => (hPos h0 (hKP hh0)).2.2.2.2 _
  have hmaps : ∀ γ ∈ {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K},
      (fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ∈
        Set.pi Set.univ (fun _ => ⋃ i, {v : UpperTheory.V.KT.Lat L N | q h0 v ≤ C * B i}) := by
    rintro γ ⟨h, hh, hγ⟩ i -
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) ≤ C * B i
    calc q h0 (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
        ≤ C * q h (γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N)) := hC h hh _
      _ = C * q (ac γ h) (Pi.single i 1 : UpperTheory.V.KT.Lat L N) := by rw [hEq]
      _ ≤ C * B i := mul_le_mul_of_nonneg_left (hBd i _ hγ) hC0
  have hinj : Set.InjOn (fun γ : Gm L N => fun i : Fin N => γ⁻¹ • (Pi.single i 1 : UpperTheory.V.KT.Lat L N))
      {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K} := by
    intro a _ b _ hab
    have hinv : (a⁻¹ : Gm L N) = b⁻¹ := by
      apply Units.ext
      ext j i
      have e := congrFun (congrFun hab i) j
      change ((↑(a⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j =
        ((↑(b⁻¹ : GL (Fin N) (𝓞 L)) : Matrix (Fin N) (Fin N) (𝓞 L)) *ᵥ Pi.single i 1) j at e
      simpa [Matrix.mulVec_single_one] using e
    exact inv_injective hinv
  exact Set.Finite.of_finite_image ((Set.Finite.pi fun _ => hF).subset (Set.image_subset_iff.mpr hmaps)) hinj

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds Filter Topology

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem d_rel {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gp L N) (h : HS L N)
    (z : VR L N) (w : InfinitePlace L) :
    star (z w) ⬝ᵥ (mat (actL g h) w *ᵥ z w) =
      star ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w) ⬝ᵥ
        (mat h w *ᵥ ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w)) := by
  rw [mat_actL, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

private theorem d_key {L : Type} [Field L] [NumberField L] {N : ℕ} (x : Gp L N) (v : HS L N) (z : VR L N) :
    |qR (actL x v) z| ≤ N * ‖v‖ * qR (actL x (one L N).1) z := by
  unfold qR
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [d_rel, d_rel]
  have h1 : mat (one L N).1 w = 1 := rfl
  rw [h1, one_mulVec]
  refine quad_bd N (mat v w) ‖v‖ (norm_nonneg _) (fun a b => ?_) _
  exact ((norm_le_pi_norm (v.1 w a) b).trans (norm_le_pi_norm (v.1 w) a)).trans
    ((norm_le_pi_norm v.1 w).trans le_rfl)

theorem pf_DerB : DerB := by
  intro L _ _ N φ x B ε hB hε hd hl
  set p := actL x (one L N).1 with hp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.comp_apply]
  set u := actL x v with hu
  have hline : HasDerivAt (fun t : ℝ => φ (p + t • u)) ((fderiv ℝ φ p) u) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
    have hD : HasFDerivAt φ (fderiv ℝ φ p) (p + (0 : ℝ) • u) := by
      simpa using hd.hasFDerivAt
    exact hD.comp_hasDerivAt (0 : ℝ) h1
  have hlim := hline.tendsto_slope_zero_right.norm
  set K : ℝ := N * ‖v‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine le_of_tendsto hlim ?_
  have hmem : Set.Ioo (0 : ℝ) (ε / (K + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hδε : K * t ≤ ε := by
    have : (K + 1) * t < ε := by rwa [lt_div_iff₀ (by positivity), mul_comm] at ht1
    nlinarith
  have hcl : Cl (K * t) p (p + t • u) := by
    intro z
    have e : qR (p + t • u) z = qR p z + t * qR u z := by
      rw [← evR_apply, map_add (f := _), map_smul, evR_apply, evR_apply, smul_eq_mul]
    rw [e, add_sub_cancel_left, abs_mul, abs_of_pos ht0]
    have := d_key x v z
    rw [← hu, ← hp] at this
    nlinarith
  have hb := hl (K * t) (by positivity) hδε _ hcl
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, norm_mul, norm_inv, Real.norm_eq_abs,
    abs_of_pos ht0]
  rw [inv_mul_le_iff₀ ht0]
  nlinarith

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end
