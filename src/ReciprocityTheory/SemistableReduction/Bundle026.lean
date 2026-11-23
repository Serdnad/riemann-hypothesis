module

public import ReciprocityTheory.SemistableReduction.Bundle017
public import ReciprocityTheory.SemistableReduction.SemiDegCE
public import ReciprocityTheory.SemistableReduction.Bundle021
public import ReciprocityTheory.SemistableReduction.SJCoreA
public import ReciprocityTheory.SemistableReduction.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.SemistableReduction.Bundle011
public import ReciprocityTheory.SemistableReduction.Bundle023

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : Fin r → K) (w : ι → Fin r → K) :
    S.h u (∑ i ∈ s, w i) = ∑ i ∈ s, S.h u (w i) := by
  classical
  refine Finset.induction_on s (by simp [HermForm.h]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h u (a • w) = a * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def coordForm {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : HermForm K k where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hGram S b
  G_herm i j := hermForm_conj S (b i) (b j)

def combMap {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) :
    (Fin k → K) →ₗ[K] (Fin r → K) where
  toFun t := ∑ i, t i • b i
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [Finset.smul_sum, smul_smul]

theorem combMap_apply {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    combMap b t = ∑ i, t i • b i := rfl

theorem coordForm_h {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (s t : Fin k → K) :
    S.h (combMap b s) (combMap b t) = (coordForm S b).h s t := by
  have key : ∀ j, S.h (combMap b s) (b j) = ∑ i, S.c (s i) * S.h (b i) (b j) := by
    intro j

    rw [← hermForm_conj S (b j), combMap_apply, hermForm_sum_right, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermForm_smul_right, map_mul, hermForm_conj]
  show _ = ∑ i, ∑ j, S.c (s i) * S.h (b i) (b j) * t j
  rw [combMap_apply b t, hermForm_sum_right]
  simp only [hermForm_smul_right, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem combMap_injective {K : Type} [Field K] {r k : ℕ} {b : Fin k → Fin r → K}
    (hb : LinearIndependent K b) : Function.Injective (combMap b) := by
  rw [Fintype.linearIndependent_iff] at hb
  refine (injective_iff_map_eq_zero (combMap b)).2 fun t ht => funext fun i => ?_
  exact hb t (by simpa only [combMap_apply] using ht) i

def coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin k → K) := B.comap ((combMap b).restrictScalars (𝓞 K))

theorem mem_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {t : Fin k → K} : t ∈ coordLat B b ↔ combMap b t ∈ B := Iff.rfl

theorem exists_coord {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) {y : Fin r → K} (hy : y ∈ B) :
    ∃ t ∈ coordLat B b, combMap b t = y := by
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hb.2.2 y hy)
  exact ⟨t, mem_coordLat.2 (by rw [combMap_apply, ht]; exact hy), by rw [combMap_apply, ht]⟩

theorem map_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) :
    (coordLat B b).map ((combMap b).restrictScalars (𝓞 K)) = B := by
  ext y
  refine ⟨fun h => ?_, fun hy => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 h
    exact mem_coordLat.1 ht
  · obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
    exact Submodule.mem_map.2 ⟨t, ht, rfl⟩

theorem coordLat_fg {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hB : B.FG) (hb : IsKBasisIn B b) : (coordLat B b).FG := Submodule.fg_of_fg_map_injective ((combMap b).restrictScalars (𝓞 K)) (combMap_injective hb.2.1) (by rw [map_coordLat hb]; exact hB)

theorem combMap_intVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    {b : Fin k → Fin r → K} {t : Fin k → K} (ht : t ∈ intVec K k)
    (P : Submodule (𝓞 K) (Fin r → K)) (hP : ∀ i, b i ∈ P) : combMap b t ∈ P := by
  rw [combMap_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx⟩ := Submodule.mem_one.1 ((Submodule.mem_pi).1 ht i (Set.mem_univ i))
  rw [← hx, algebraMap_smul]
  exact P.smul_mem x (hP i)

theorem intVec_le_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : intVec K k ≤ coordLat B b := fun t ht => mem_coordLat.2 (combMap_intVec ht B hb.1)

theorem spanIdx_eq_vecIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : spanIdx B b = vecIdx (coordLat B b) := by
  have hinj := combMap_injective hb.2.1
  have hspan : (intVec K k).map ((combMap b).restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range b) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨t, ht, rfl⟩
      exact combMap_intVec ht _ fun i => Submodule.subset_span ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, (Submodule.mem_pi).2 fun j _ => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Pi.single_apply, if_pos rfl]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
        · rw [Pi.single_apply, if_neg hj]; exact zero_mem _
      · show combMap b (Pi.single i 1) = b i
        simp [combMap_apply, Pi.single_apply, ite_smul]
  have e1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup =
      (intVec K k).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    rw [← hspan]; exact AddSubgroup.ext fun _ => Iff.rfl
  have e2 : B.toAddSubgroup =
      (coordLat B b).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    conv_lhs => rw [← map_coordLat hb]
    exact AddSubgroup.ext fun _ => Iff.rfl
  unfold spanIdx vecIdx
  rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

theorem coordLat_integral {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hint : IsIntegralOn S B) :
    IsIntegralOn (coordForm S b) (coordLat B b) := by
  intro s hs t ht
  rw [← coordForm_h]
  exact hint _ (mem_coordLat.1 hs) _ (mem_coordLat.1 ht)

theorem coordLat_selfDual {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hb : IsKBasisIn B b)
    (hsd : IsSelfDual S B) : IsSelfDual (coordForm S b) (coordLat B b) := by
  refine ⟨coordLat_integral hsd.1, fun s hs => mem_coordLat.2 (hsd.2 _ fun y hy => ?_)⟩
  obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
  rw [coordForm_h]
  exact hs t ht

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

namespace ReciprocityTheory.MultiplicativeHeights

open SemiDegIdx

theorem integralIndex_holds : IntegralIndexStatement := by
  intro K _ _ r k S B b hB hb hint hdet
  have key : ((vecIdx (coordLat B b) : ℕ) : ℚ) ^ 2 ≤ |Algebra.norm ℚ (hGram S b).det| :=
    vec_integral_bound (coordForm S b) _ (coordLat_fg hB hb) (intVec_le_coordLat hb)
      (coordLat_integral hint) hdet
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

theorem selfDualIndex_holds : SelfDualIndexStatement := by
  intro K _ _ r S L b hL hsd hb
  have key : |Algebra.norm ℚ (hGram S b).det| ≤ ((vecIdx (coordLat L b) : ℕ) : ℚ) ^ 2 :=
    vec_selfDual_bound (coordForm S b) _ (coordLat_fg hL.1 hb) (intVec_le_coordLat hb)
      (coordLat_selfDual hb hsd)
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix Module
open scoped ComplexOrder

theorem sb_re_dot_comm {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re = (star w ⬝ᵥ v).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem sb_normSq_split (p : ℕ) {r : ℕ} (v : Fin r → ℂ) : normSq v = posSq p v + negSq p v := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_normSq_nonneg {r : ℕ} (v : Fin r → ℂ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem sb_setup {r p : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} {s : ℝ} (hH : H.PosDef)
    (hJ : H * signMat p r * H = signMat p r)
    (hP : ∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) :
    ∀ w : Fin r → ℂ, ∃ x, signMat p r *ᵥ (H *ᵥ x) = x ∧ sbDp p r *ᵥ x = sbDp p r *ᵥ w := by
  intro w
  have hJJ : signMat p r * signMat p r = 1 := sb_J_mul_J p r
  have hA2 : signMat p r * H * (signMat p r * H) = 1 := by
    calc signMat p r * H * (signMat p r * H) = signMat p r * (H * signMat p r * H) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have hHx : ∀ x : Fin r → ℂ, H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
    intro x; rw [mulVec_mulVec, hJJ, one_mulVec]
  have hre : ∀ x : Fin r → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
    intro x hx
    have := hH.re_dotProduct_pos hx
    simpa using this
  have hplus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = x → sbDp p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, sb_re_dot_J, sb_posSq_eq, hDx, sb_negSq_eq] at h1
    have h2 := sb_normSq_nonneg (sbDn p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  have hminus : ∀ x : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ x) = -x → sbDn p r *ᵥ x = 0 → x = 0 := by
    intro x hAx hDx
    by_contra hx
    have h1 := hre x hx
    rw [hHx x, hAx, mulVec_neg, dotProduct_neg, Complex.neg_re, sb_re_dot_J, sb_posSq_eq,
      sb_negSq_eq, hDx] at h1
    have h2 := sb_normSq_nonneg (sbDp p r *ᵥ x)
    have h3 : normSq (0 : Fin r → ℂ) = 0 := by simp [normSq]
    linarith
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r) (Fin r) ℂ, P = (1 / 2 : ℂ) • (1 + signMat p r * H) :=
    ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin r) (Fin r) ℂ, N = (1 / 2 : ℂ) • (1 - signMat p r * H) :=
    ⟨_, rfl⟩
  have hAP : signMat p r * H * P = P := by
    rw [hP, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hA2, add_comm]
  have hAN : signMat p r * H * N = -N := by
    rw [hN, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hA2, ← smul_neg, neg_sub]
  have hPN : P + N = 1 := by
    rw [hP, hN]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hPv : ∀ x, signMat p r *ᵥ (H *ᵥ (P *ᵥ x)) = P *ᵥ x := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAP]
  have hNv : ∀ x, signMat p r *ᵥ (H *ᵥ (N *ᵥ x)) = -(N *ᵥ x) := by
    intro x; rw [mulVec_mulVec, mulVec_mulVec, hAN, neg_mulVec]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin r) (Fin r) ℂ, F = sbDp p r * P + sbDn p r * N := ⟨_, rfl⟩
  have hFp : ∀ x, sbDp p r *ᵥ (F *ᵥ x) = sbDp p r *ᵥ (P *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dp_mul_Dp,
      sb_Dp_mul_Dn, zero_mul, zero_mulVec, add_zero]
  have hFn : ∀ x, sbDn p r *ᵥ (F *ᵥ x) = sbDn p r *ᵥ (N *ᵥ x) := by
    intro x
    simp only [hF, add_mulVec, mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, sb_Dn_mul_Dn,
      sb_Dn_mul_Dp, zero_mul, zero_mulVec, zero_add]
  have hinj : Function.Injective F.mulVec := by
    intro x y hxy
    have h0 : F *ᵥ (x - y) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hxy
    have hp : P *ᵥ (x - y) = 0 := hplus _ (hPv _) (by rw [← hFp, h0, mulVec_zero])
    have hn : N *ᵥ (x - y) = 0 := hminus _ (hNv _) (by rw [← hFn, h0, mulVec_zero])
    have : x - y = 0 := by
      rw [← one_mulVec (x - y), ← hPN, add_mulVec, hp, hn, add_zero]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective F.mulVec :=
    mulVec_surjective_iff_isUnit.mpr (mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨x, hx⟩ := hsurj (sbDp p r *ᵥ w)
  refine ⟨P *ᵥ x, hPv x, ?_⟩
  rw [← hFp, hx, mulVec_mulVec, sb_Dp_mul_Dp]

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Set Real

theorem gaussLogC_div {a : ℝ} (ha : 0 < a) :
    gaussLogC a / gaussOneC = log a + radK 1 / radJ 1 := by
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h1 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => exp (-r ^ 2))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => log (a * r) * exp (-r ^ 2))
  rw [hdim] at h1 h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h1 h2
  set C : ℝ := (volume : Measure ℂ).real (Metric.ball 0 1) with hCdef
  have hC : 0 < C :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ℂ) one_pos).ne' measure_ball_lt_top.ne
  have hG : gaussOneC = 2 * C * radJ 1 := by
    unfold gaussOneC radJ
    rw [h1]
    simp only [pow_one]
    ring
  have hsplit : ∫ y in Ioi (0 : ℝ), y * (log (a * y) * exp (-y ^ 2)) =
      log a * radJ 1 + radK 1 := by
    have heq : EqOn (fun y : ℝ => y * (log (a * y) * exp (-y ^ 2)))
        (fun y : ℝ => log a * (y ^ 1 * exp (-y ^ 2)) + y ^ 1 * log y * exp (-y ^ 2)) (Ioi 0) := by
      intro y hy
      simp only
      rw [log_mul ha.ne' (ne_of_gt hy)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      integral_add ((integrableOn_radJ 1).const_mul (log a)) (integrableOn_radK le_rfl),
      integral_const_mul]
    rfl
  have hL : gaussLogC a = 2 * C * (log a * radJ 1 + radK 1) := by
    unfold gaussLogC
    rw [h2, hsplit]
    ring
  have hM := radJ_pos 1
  rw [hL, hG]
  field_simp

theorem sjCore_holds : SphereLinLogStatement := by
  intro n c hc
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim c 0) hc
    · exact h
  obtain ⟨hi, he⟩ := polar_mean hn c hc
  refine ⟨hi, ?_⟩
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [he, gaussLogC_div hcn, h2, radRatio_odd]
  ring

end ReciprocityTheory.MultiplicativeHeights
end
end
