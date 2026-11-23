module

public import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import GroundTheory.GlobalFields.TateThesis.Bundle003
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import GroundTheory.GlobalFields.Adele.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField InfinitePlace InfinitePlace.Completion Complex
open scoped Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem eq_of_forall_exp_mul_I {a b : ℝ}
    (h : ∀ t : ℝ, Complex.exp (a * t * I) = Complex.exp (b * t * I)) : a = b := by
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.2 hab
  set t : ℝ := π / (a - b)
  have ht : (a - b) * t = π := by simp only [t]; field_simp
  have h1 : Complex.exp ((((a - b) * t : ℝ) : ℂ) * I) = 1 := by
    have e : ((((a - b) * t : ℝ) : ℂ) * I) = (a : ℂ) * t * I - (b : ℂ) * t * I := by
      push_cast; ring
    rw [e, Complex.exp_sub, h t, div_self (Complex.exp_ne_zero _)]
  rw [ht, Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have h2 : (π : ℂ) = ((n * (2 * π) : ℝ) : ℂ) := by
    refine mul_right_cancel₀ I_ne_zero (hn.trans ?_)
    push_cast; ring
  have h3 : π = n * (2 * π) := by exact_mod_cast h2
  have h4 : (1 : ℝ) = 2 * n := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp at h3
    linarith
  have h5 : (1 : ℤ) = 2 * n := by exact_mod_cast h4
  omega


omit [NumberField K] in
theorem exists_extensionEmbedding_eq_ofReal (w : InfinitePlace K) (r : ℝ) :
    ∃ a : w.Completion, extensionEmbedding w a = r := by
  by_cases hw : w.IsReal
  · obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hw r
    exact ⟨a, by rw [← extensionEmbeddingOfIsReal_apply hw, ha]⟩
  · exact surjective_extensionEmbedding_of_isComplex (not_isReal_iff_isComplex.1 hw) (r : ℂ)

omit [NumberField K] in
theorem norm_extensionEmbedding' (w : InfinitePlace K) (a : w.Completion) :
    ‖extensionEmbedding w a‖ = ‖a‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a

theorem ofReal_exp_cpow (t : ℝ) (c : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ c = Complex.exp (t * c) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'), ← ofReal_log
    (Real.exp_pos t).le, Real.log_exp]

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem infiniteParams_unique (w : InfinitePlace K) {p : ℤ × ℝ}
    (hp1 : w.IsReal → 0 ≤ p.1 ∧ p.1 < 2)
    (hp2 : ∀ a : (w.Completion)ˣ, (χ.infiniteComponent w a : ℂ) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I)) :
    p = χ.infiniteParams w := by
  set q := χ.infiniteParams w
  have hq1 : w.IsReal → 0 ≤ q.1 ∧ q.1 < 2 := (χ.exists_infiniteParams w).choose_spec.1
  have hq2 := (χ.exists_infiniteParams w).choose_spec.2
  have heq : ∀ a : (w.Completion)ˣ,
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1 *
        ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((q.2 : ℂ) * I) :=
    fun a ↦ (hp2 a).symm.trans (hq2 a)
  have hM : (1 : ℝ) ≤ w.mult := by exact_mod_cast InfinitePlace.one_le_mult

  have hτ : p.2 = q.2 := by
    have key : ∀ t : ℝ, Complex.exp ((w.mult * p.2 : ℝ) * t * I) =
        Complex.exp ((w.mult * q.2 : ℝ) * t * I) := by
      intro t
      obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal w (Real.exp t)
      have ha0 : a ≠ 0 := fun h0 ↦ by
        rw [h0, map_zero] at ha
        exact (Real.exp_pos t).ne' (by exact_mod_cast ha.symm)
      have hn : ‖a‖ = Real.exp t := by
        rw [← norm_extensionEmbedding', ha, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos t)]
      have h := heq (Units.mk0 a ha0)
      simp only [Units.val_mk0, ha, hn, div_self (by exact_mod_cast (Real.exp_pos t).ne' :
        ((Real.exp t : ℝ) : ℂ) ≠ 0), one_zpow, one_mul, ← Real.exp_nat_mul,
        ofReal_exp_cpow] at h
      convert h using 2 <;> push_cast <;> ring
    have := eq_of_forall_exp_mul_I key
    have hM0 : (w.mult : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hM0 this

  have hm : ∀ a : (w.Completion)ˣ,
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 =
      (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ q.1 := by
    intro a
    have h := heq a
    rw [hτ] at h
    have hpos : (0 : ℝ) < ‖(a : w.Completion)‖ ^ w.mult := pow_pos (norm_pos_iff.2 a.ne_zero) _
    have hne : ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((q.2 : ℂ) * I) ≠ 0 := by
      rw [cpow_def_of_ne_zero (by exact_mod_cast hpos.ne')]
      exact Complex.exp_ne_zero _
    exact mul_right_cancel₀ hne h
  refine Prod.ext ?_ hτ
  by_cases hw : w.IsReal
  · obtain ⟨hp0, hp2'⟩ := hp1 hw
    obtain ⟨hq0, hq2'⟩ := hq1 hw
    obtain ⟨a, ha⟩ := exists_extensionEmbedding_eq_ofReal w (-1)
    have ha0 : a ≠ 0 := fun h0 ↦ by rw [h0, map_zero] at ha; norm_num at ha
    have hn : ‖a‖ = 1 := by rw [← norm_extensionEmbedding', ha]; simp
    have h := hm (Units.mk0 a ha0)
    simp only [Units.val_mk0, ha, hn, ofReal_one, div_one, ofReal_neg] at h
    rcases (show p.1 = 0 ∨ p.1 = 1 by omega) with h1 | h1 <;>
      rcases (show q.1 = 0 ∨ q.1 = 1 by omega) with h2 | h2 <;> rw [h1, h2] at h ⊢ <;>
      norm_num at h
  · have hc := not_isReal_iff_isComplex.1 hw
    have key : ∀ θ : ℝ, Complex.exp ((p.1 : ℝ) * θ * I) = Complex.exp ((q.1 : ℝ) * θ * I) := by
      intro θ
      obtain ⟨a, ha⟩ := surjective_extensionEmbedding_of_isComplex hc (Complex.exp (θ * I))
      have ha0 : a ≠ 0 := fun h0 ↦ by
        rw [h0, map_zero] at ha
        exact Complex.exp_ne_zero _ ha.symm
      have hn : ‖a‖ = 1 := by
        rw [← norm_extensionEmbedding', ha, Complex.norm_exp_ofReal_mul_I]
      have h := hm (Units.mk0 a ha0)
      simp only [Units.val_mk0, ha, hn, ofReal_one, div_one, ← Complex.exp_int_mul] at h
      convert h using 2 <;> push_cast <;> ring
    exact_mod_cast eq_of_forall_exp_mul_I key

theorem inv_toIdele (x : IdeleGroup K) : (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ := rfl

theorem localComponent_inv (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : (χ⁻¹).localComponent v a = (χ.localComponent v a)⁻¹ := rfl

theorem infiniteComponent_inv (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    (χ⁻¹).infiniteComponent w a = (χ.infiniteComponent w a)⁻¹ := rfl

theorem conductor_inv : χ⁻¹.conductor = χ.conductor := by
  have hker : (χ⁻¹).toIdele.ker = χ.toIdele.ker := by
    ext x
    simp only [MonoidHom.mem_ker, inv_toIdele, inv_eq_one]
  have h1 : χ⁻¹.conductor ∣ χ.conductor := by
    rw [← (χ⁻¹).map_idealLevel_le_ker_iff χ.conductor_ne_bot, hker]
    exact χ.map_idealLevel_conductor_le_ker
  have h2 : χ.conductor ∣ χ⁻¹.conductor := by
    rw [← χ.map_idealLevel_le_ker_iff (χ⁻¹).conductor_ne_bot, ← hker]
    exact (χ⁻¹).map_idealLevel_conductor_le_ker
  exact le_antisymm (Ideal.le_of_dvd h2) (Ideal.le_of_dvd h1)


open Classical in
theorem infiniteParams_inv (w : InfinitePlace K) :
    (χ⁻¹).infiniteParams w =
      (if w.IsReal then χ.infiniteWeight w else -χ.infiniteWeight w, -χ.infiniteTau w) := by
  symm
  refine (χ⁻¹).infiniteParams_unique w ?_ fun a ↦ ?_
  · intro hw
    rw [if_pos hw]
    exact χ.infiniteWeight_of_isReal hw
  · rw [infiniteComponent_inv, Circle.coe_inv, χ.infiniteComponent_eq]
    simp only
    rw [mul_inv, ofReal_neg, neg_mul, cpow_neg]
    congr 1
    split_ifs with hw
    ·
      have hι : extensionEmbedding w (a : w.Completion) =
          ((extensionEmbeddingOfIsReal hw (a : w.Completion) : ℝ) : ℂ) :=
        (extensionEmbeddingOfIsReal_apply hw _).symm
      have hn : ‖(a : w.Completion)‖ = |extensionEmbeddingOfIsReal hw (a : w.Completion)| := by
        rw [← Real.norm_eq_abs]
        exact ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm
      have hx0 : extensionEmbeddingOfIsReal hw (a : w.Completion) ≠ 0 :=
        (map_ne_zero_iff _ (extensionEmbeddingOfIsReal hw).injective).2 a.ne_zero
      rw [hι, hn, ofReal_div_abs_eq_sign hx0, ← zpow_neg, ← inv_zpow']
      congr 1
      rcases lt_or_gt_of_ne hx0 with h | h
      · rw [Real.sign_of_neg h]; push_cast; norm_num
      · rw [Real.sign_of_pos h]; push_cast; norm_num
    · rw [zpow_neg]

theorem infiniteWeight_inv_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    (χ⁻¹).infiniteWeight w = χ.infiniteWeight w := by
  rw [infiniteWeight, infiniteParams_inv, if_pos hw]

theorem infiniteWeight_inv_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) :
    (χ⁻¹).infiniteWeight w = -χ.infiniteWeight w := by
  rw [infiniteWeight, infiniteParams_inv, if_neg (not_isReal_iff_isComplex.2 hw)]

end HeckeCharacter

end

end GroundTheory.Global
end

section

open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace

namespace GroundTheory.Global

noncomputable section

theorem hasTemperateGrowth_finsetProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (s : Finset ι) {f : ι → E → ℂ} (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact HasTemperateGrowth.const (1 : ℂ)
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem ofReal_finsetProd_cpow {ι : Type*} (t : Finset ι) {r : ι → ℝ} (hr : ∀ i ∈ t, 0 ≤ r i)
    (s : ℂ) : ((∏ i ∈ t, r i : ℝ) : ℂ) ^ s = ∏ i ∈ t, ((r i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr a (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hr i (Finset.mem_insert_of_mem hi)]

variable {K : Type*} [Field K] [NumberField K]

theorem norm_mixedToEuclidean_sq (x : mixedSpace K) :
    ‖mixedToEuclidean K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change ⟪(euclidean.toMixed K).symm (mapComplexCoord K sqrtTwoSMulComplex x),
    (euclidean.toMixed K).symm (mapComplexCoord K sqrtTwoSMulComplex x)⟫ = _
  rw [inner_toMixed_symm, mapComplexCoord_apply, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun w _ ↦ by ring
  · refine Finset.sum_congr rfl fun w _ ↦ ?_
    dsimp only
    rw [sqrtTwoSMulComplex_apply, Complex.real_smul, map_mul, conj_ofReal,
      show ((√2 : ℝ) : ℂ) * conj (x.2 w) * (((√2 : ℝ) : ℂ) * x.2 w) =
        (((√2 : ℝ) ^ 2 : ℝ) : ℂ) * (conj (x.2 w) * x.2 w) by push_cast; ring,
      Real.sq_sqrt (by norm_num), Complex.conj_mul']
    norm_cast

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def infinitePoly (x : mixedSpace K) : ℂ :=
  (∏ w : {w // IsReal w}, ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs) *
    ∏ w : {w // IsComplex w},
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^ (χ.infiniteWeight w).natAbs

theorem hasTemperateGrowth_infinitePoly : χ.infinitePoly.HasTemperateGrowth := by
  have h1 : ∀ w : {w // IsReal w}, (fun x : mixedSpace K ↦
      ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs).HasTemperateGrowth := fun w ↦ by
    have h := (((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
    exact h
  have h2 : ∀ w : {w // IsComplex w}, (fun x : mixedSpace K ↦
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^
        (χ.infiniteWeight w).natAbs).HasTemperateGrowth := by
    intro w
    by_cases hw : 0 < χ.infiniteWeight w
    · simp only [ite_eq_left hw]
      have h := (((Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj w :
        ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
    · simp only [ite_eq_right hw]
      have h := ((((ContinuousLinearMap.proj w : ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ)) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
  exact (hasTemperateGrowth_finsetProd _ fun w _ ↦ h1 w).mul
    (hasTemperateGrowth_finsetProd _ fun w _ ↦ h2 w)

def infiniteSchwartz : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ χ.infinitePoly
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K)
      (gaussianSchwartz (euclidean.mixedSpace K)))

theorem infiniteSchwartz_apply (x : mixedSpace K) :
    χ.infiniteSchwartz x = χ.infinitePoly x *
      ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [infiniteSchwartz, SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth_infinitePoly,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

theorem infiniteSchwartz_homeomorphMixedSpace (x : InfiniteAdeleRing K) :
    χ.infiniteSchwartz (homeomorphMixedSpace K x) = ∏ w, χ.infiniteTest w (x w) := by
  rw [infiniteSchwartz_apply, prod_eq_prod_mul_prod, homeomorphMixedSpace_apply,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [infinitePoly, infiniteTest, Finset.prod_mul_distrib]
  have hr : ∀ w : {w // IsReal w}, (if 0 < χ.infiniteWeight w.1 then
      conj (extensionEmbedding w.1 (x w.1)) else extensionEmbedding w.1 (x w.1)) =
        ((extensionEmbeddingOfIsReal w.2 (x w.1) : ℝ) : ℂ) := fun w ↦ by
    rw [extensionEmbeddingOfIsReal_apply]
    split_ifs
    · rw [← extensionEmbeddingOfIsReal_apply w.2, conj_ofReal]
    · rfl
  have hnr : ∀ w : {w // IsReal w}, (extensionEmbeddingOfIsReal w.2 (x w.1)) ^ 2 = ‖x w.1‖ ^ 2 :=
    fun w ↦ by
      rw [← (isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _),
        Real.norm_eq_abs, sq_abs]
  have hnc : ∀ w : {w // IsComplex w}, ‖extensionEmbedding w.1 (x w.1)‖ = ‖x w.1‖ := fun w ↦
    (isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _
  simp only [hr, hnr, hnc, mult_isReal, mult_isComplex]
  have hexp : ((Real.exp (-π * (∑ w : {w // IsReal w}, ‖x w.1‖ ^ 2 +
      2 * ∑ w : {w // IsComplex w}, ‖x w.1‖ ^ 2)) : ℝ) : ℂ) =
      (∏ w : {w // IsReal w}, ((Real.exp (-(π * ((1 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ)) *
        ∏ w : {w // IsComplex w}, ((Real.exp (-(π * ((2 : ℕ) : ℝ) * ‖x w.1‖ ^ 2)) : ℝ) : ℂ) := by
    rw [← ofReal_prod, ← ofReal_prod, ← ofReal_mul, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
    congr 2
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun w _ ↦ by push_cast; ring
  rw [hexp]
  ring

theorem toIdele_ofInfinite (a : (InfiniteAdeleRing K)ˣ) :
    χ.toIdele (IdeleGroup.ofInfinite a) =
      ∏ w, χ.infiniteComponent w (IdeleGroup.infiniteComponent w a) := by
  have ha : a = ∏ w, Units.map (IdeleGroup.infiniteAdeleSingle w) (IdeleGroup.infiniteComponent w a) := by
    ext1
    rw [Units.coe_prod]
    simp only [Units.coe_map, IdeleGroup.coe_infiniteComponent]
    exact (Finset.univ_prod_mulSingle (fun w ↦ (a : InfiniteAdeleRing K) w)).symm
  conv_lhs => rw [ha]
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ ↦ by
    rw [IdeleGroup.ofInfinite_map_infiniteAdeleSingle]
    rfl

theorem integral_infiniteSchwartz {s : ℂ} (hs : 0 < s.re) :
    ∫ a : (InfiniteAdeleRing K)ˣ, χ.infiniteSchwartz (homeomorphMixedSpace K a) *
      (χ.toIdele (IdeleGroup.ofInfinite a) : ℂ) *
        ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      ∏ w, infiniteConst w * χ.infiniteGamma w s := by
  have he : MeasurableEmbedding (infiniteUnitsEquiv K).symm :=
    (infiniteUnitsEquiv K).symm.toHomeomorph.measurableEmbedding
  rw [infiniteIdeleMeasure, he.integral_map]
  have hpt : ∀ y : Π w : InfinitePlace K, (w.Completion)ˣ,
      χ.infiniteSchwartz (homeomorphMixedSpace K ((infiniteUnitsEquiv K).symm y)) *
        (χ.toIdele (IdeleGroup.ofInfinite ((infiniteUnitsEquiv K).symm y)) : ℂ) *
        ((∏ w, ‖(((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
          InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s =
      ∏ w, χ.infiniteTest w (y w) * χ.infiniteComponent w (y w) *
        ((‖(y w : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s := by
    intro y
    have hy : ∀ w, (((infiniteUnitsEquiv K).symm y : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) w = (y w : w.Completion) := fun w ↦ rfl
    have hc : ∀ w, IdeleGroup.infiniteComponent w ((infiniteUnitsEquiv K).symm y) = y w :=
      fun w ↦ Units.ext rfl
    rw [infiniteSchwartz_homeomorphMixedSpace, toIdele_ofInfinite,
      ofReal_finsetProd_cpow _ (fun w _ ↦ by positivity)]
    have hcp : ((∏ w, χ.infiniteComponent w (y w) : Circle) : ℂ) =
        ∏ w, (χ.infiniteComponent w (y w) : ℂ) :=
      map_prod Circle.coeHom (fun w ↦ χ.infiniteComponent w (y w)) Finset.univ
    simp only [hy, hc, hcp, Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hfub := integral_fintype_prod_eq_prod (μ := fun w : InfinitePlace K ↦ infinitePlaceUnitsMeasure w)
    (fun w (u : (w.Completion)ˣ) ↦ χ.infiniteTest w u * (χ.infiniteComponent w u : ℂ) *
      ((‖(u : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s)
  exact hfub.trans (Finset.prod_congr rfl fun w _ ↦ χ.integral_infiniteTest w hs)

end HeckeCharacter

end

end GroundTheory.Global
end

section

set_option maxSynthPendingDepth 1

open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

open IdeleGroup

variable (χ : HeckeCharacter K)

theorem exists_toIdele_pow_eq_one (h : IsOfFinOrder χ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : IdeleGroup K, χ.toIdele x ^ n = 1 := by
  obtain ⟨n, hn, hχ⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine ⟨n, hn, fun x ↦ ?_⟩
  rw [toIdele_apply, ← ContinuousMonoidHom.pow_apply, hχ]
  rfl

theorem realComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsReal) {x : ℝˣ} (hx : 0 < (x : ℝ)) : χ.realComponent hw x = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  have hr : 0 < (x : ℝ) ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos hx _
  have hy : Units.mk0 _ hr.ne' ^ n = x := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Real.rpow_inv_natCast_pow hx.le hn.ne'])
  rw [← hy, map_pow]
  exact hpow (infiniteEmbedding w (realUnitsHom hw (Units.mk0 _ hr.ne')))

theorem complexComponent_eq_one_of_isOfFinOrder (h : IsOfFinOrder χ) {w : InfinitePlace K}
    (hw : w.IsComplex) (z : ℂˣ) : χ.complexComponent hw z = 1 := by
  obtain ⟨n, hn, hpow⟩ := χ.exists_toIdele_pow_eq_one h
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) hn
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hy
    exact z.ne_zero hy.symm
  have hyz : Units.mk0 y hy0 ^ n = z := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hy])
  rw [← hyz, map_pow]
  exact hpow (infiniteEmbedding w (complexUnitsHom hw (Units.mk0 y hy0)))

end HeckeCharacter

end

end GroundTheory.Global
end
