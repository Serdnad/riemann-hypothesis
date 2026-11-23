module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Aesop.Main
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkMulVecMulVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergMapContinuous
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ProdIicCastLE
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def EInt (k r' : ℕ) (A : ℝ) (c : ℂ) (g : Mat k r') : ℝ≥0∞ :=
  ∫⁻ x : HPar k r', ENNReal.ofReal (gN (w0 k r' c * ιLev k 1 r' g * heis0 k r' x) ^ (-A))

theorem eInt_bound (hGL : GNLower) (hHA : HeisAct) (hHC : HeisClosed) (hCL : HeisConjLev) (hCM : HeisConjLevMeas)
    (k r' : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A) :
    ∃ C : ℝ, ∀ c : ℂ, c ≠ 0 → ∀ g ∈ GV k r',
      EInt k r' A c g ≤ ENNReal.ofReal (C * min (‖c‖ ^ (-((4 * r' + 2 * k + 3 : ℕ) : ℝ))) ‖c‖⁻¹ *
        gN g ^ (((4 * r' + 2 * k + 3 : ℕ) : ℝ) - A)) := by
  exact ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.eInt_bound' hGL hHA hCL hCM k r' A hA

theorem cInt_fin (n : ℕ) (σ : ℝ) (h1 : 1 < σ) (h2 : σ < 2 * (n : ℝ) + 1) :
    (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
      ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹)) < ∞ := by
  have hF0 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioc 0 1) := by
    refine Integrable.mono'
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 * (n : ℝ) - σ)
        (by linarith)).1 ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := hy.1
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_right _ _) hA) hy0.le
        _ = y ^ (2 * (n : ℝ) - σ) := by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hy0.ne', mul_one]
  have hF1 : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 1) := by
    refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -σ) (by linarith) zero_lt_one) ?_ ?_
    · first
        | exact (by measurability : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
        | exact (by fun_prop : Measurable fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy => ?_)
      have hy0 : 0 < y := zero_lt_one.trans hy
      have hA : 0 ≤ y ^ (2 * (n : ℝ) - σ) := Real.rpow_nonneg hy0.le _
      have hmin : 0 ≤ min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹ := le_min (Real.rpow_nonneg hy0.le _) (inv_nonneg.2 hy0.le)
      rw [Real.norm_of_nonneg (mul_nonneg hy0.le (mul_nonneg hA hmin))]
      calc y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹) ≤ y * (y ^ (2 * (n : ℝ) - σ) * y ^ (-((2 * n + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (min_le_left _ _) hA) hy0.le
        _ = y ^ (-σ) := by
          rw [← mul_assoc, mul_comm y, ← Real.rpow_add_one hy0.ne', ← Real.rpow_add hy0]
          congr 1
          push_cast
          ring
  have hY : IntegrableOn (fun y : ℝ => y * (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹)) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hF0.union hF1
  have hI : Integrable (fun c : ℂ => ‖c‖ ^ (2 * (n : ℝ) - σ) *
      min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) volume := by
    first
      | exact (integrable_fun_norm_addHaar volume
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
      | exact (integrable_fun_norm_addHaar (μ := volume)
          (f := fun y : ℝ => (y ^ (2 * (n : ℝ) - σ) * min (y ^ (-((2 * n + 1 : ℕ) : ℝ))) y⁻¹))).2 (hY.congr_fun (fun y _ => by simp) measurableSet_Ioi)
  calc (∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ)) *
        ENNReal.ofReal (min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹))
      = ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (n : ℝ) - σ) *
          min (‖c‖ ^ (-((2 * n + 1 : ℕ) : ℝ))) ‖c‖⁻¹) :=
        lintegral_congr fun c => (ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)).symm
    _ < ∞ := hI.lintegral_lt_top

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem H_es (k r : ℕ) (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  have ha := a.isLt
  funext i
  have hi := i.isLt
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem row_fix {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : h (eI k r a) j = if j = eI k r a then 1 else 0 := by
  obtain ⟨hU, hfix, -⟩ := hm
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have h1 : hᴴ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
    have := congrArg (fun M => M *ᵥ bvec (esI k r a)) hU'
    simp only [← Matrix.mulVec_mulVec, (hfix a).2, H_es] at this
    exact this
  have h2 := congrFun h1 j
  simp only [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  have h3 := congrArg star h2
  rw [star_star] at h3
  rw [h3]
  split_ifs <;> simp

theorem row_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (v : Fin (2 * r + k + 1) → ℂ) : (h *ᵥ v) (eI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, row_fix hm a, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem inv_fix {k r : ℕ} {h : Mat k r} (hu : IsUnit h.det) {v : Fin (2 * r + k + 1) → ℂ} (hv : h *ᵥ v = v) :
    h⁻¹ *ᵥ v = v := by
  calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem conj_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (n : Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : h⁻¹ *ᵥ v = v) (a : Fin r) :
    ((h * n * h⁻¹) *ᵥ v) (eI k r a) = (n *ᵥ v) (eI k r a) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, row_apply hm a]

theorem lam_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z)
    (hu : IsUnit h.det) (n : Mat k r) : lam k r z (h * n * h⁻¹) = lam k r z n := by
  have hent : ∀ (g : Mat k r) (i j : Fin (2 * r + k + 1)), g i j = (g *ᵥ bvec j) i := by
    intro g i j
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hz : h⁻¹ *ᵥ z = z := inv_fix hu hm.2.2
  have hell : ell k r z (h * n * h⁻¹) = ell k r z n := by
    unfold ell
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with hlt
    · rw [hent (h * n * h⁻¹), hent n]
      exact conj_apply hm n _ (inv_fix hu (hm.2.1 _).1) a
    · exact conj_apply hm n z hz a
  simp only [lam, hell]

end ReciprocityTheory.ChartRestriction.DS.Xi.XI

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB

theorem ga_nonneg (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : 0 ≤ Ga k r l Y := by
  unfold Ga
  let M : Matrix (Fin (2 * r + k + 1)) (Fin (l.val + 1)) ℂ := fun i b => Y (Fin.castLE (by omega) b) i
  have key : 0 ≤ ((Mᴴ * M).det).re := by
    open scoped ComplexOrder in
    have h0 := Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self M).det_nonneg
    rw [Complex.zero_re] at h0
    exact h0.1
  convert key using 3
  ext a b
  first
    | rfl
    | (simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply, M]; rfl)

theorem rpow_bd (a b K s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 1 ≤ K) (hs : 0 ≤ s) (h1 : b ≤ K * a)
    (h2 : a ≤ K * b) : a ^ (-s) ≤ K ^ s * b ^ (-s) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have hb0 : b = 0 := le_antisymm (by simpa using h1) hb
    subst hb0
    have h3 : 1 ≤ K ^ s := Real.one_le_rpow hK hs
    have h4 : 0 ≤ (0:ℝ) ^ (-s) := Real.rpow_nonneg le_rfl _
    nlinarith
  · have hbpos : 0 < b := by
      by_contra hc
      push_neg at hc
      nlinarith
    rw [Real.rpow_neg ha, Real.rpow_neg hb]
    have hbs : b ^ s ≤ K ^ s * a ^ s := by
      rw [← Real.mul_rpow (by linarith) ha]
      exact Real.rpow_le_rpow hb h1 hs
    have hapos : 0 < a ^ s := Real.rpow_pos_of_pos hpos s
    have hbpos' : 0 < b ^ s := Real.rpow_pos_of_pos hbpos s
    rw [← div_eq_mul_inv, inv_eq_one_div]
    first
      | (rw [div_le_div_iff_of_pos hapos hbpos']; linarith)
      | (rw [div_le_div_iff₀ hapos hbpos']; linarith)

theorem gN_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ gN g := Real.sqrt_nonneg _

theorem ga_two {k r : ℕ} (A : Mat k r) (K : ℝ) (hA : gN A ≤ K) (l : Fin (r + 1))
    (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (K ^ (l.val + 1)) ^ 2 * Ga k r l Y := by
  refine (ga_mul_le k r A l Y).trans (mul_le_mul_of_nonneg_right ?_ (ga_nonneg k r l Y))
  rw [← pow_mul, ← pow_mul, mul_comm]
  exact pow_le_pow_left₀ (gN_nonneg A) hA _

theorem xi_bd {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (h : Mat k r) (hu : IsUnit h.det) (K : ℝ)
    (hK : 1 ≤ K) (h1 : gN h ≤ K) (h2 : gN h⁻¹ ≤ K) (m : Mat k r) :
    xiR k r s (h * m) ≤ (∏ l, (K ^ (l.val + 1)) ^ s l) * xiR k r s m := by
  unfold xiR
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro l _
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  · intro l _
    have hK0 : 0 ≤ K ^ (l.val + 1) := pow_nonneg (by linarith) _
    have hK' : 1 ≤ K ^ (l.val + 1) := one_le_pow₀ hK
    have e1 : Ga k r l (fun a => (h * m) *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => m *ᵥ phiV k r a) := by
      have := ga_two h K h1 l (fun a => m *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec] at this
      exact this
    have e2 : Ga k r l (fun a => m *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => (h * m) *ᵥ phiV k r a) := by
      have := ga_two h⁻¹ K h2 l (fun a => (h * m) *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec, ← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul] at this
      exact this
    have d1 : Del k r l (h * m) ≤ K ^ (l.val + 1) * Del k r l m := by
      have := Real.sqrt_le_sqrt e1
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    have d2 : Del k r l m ≤ K ^ (l.val + 1) * Del k r l (h * m) := by
      have := Real.sqrt_le_sqrt e2
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    exact rpow_bd _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hK' (hs l) d2 d1

theorem cont_gN {k r : ℕ} : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  refine Continuous.sqrt ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)

theorem cont_ga {k r : ℕ} (l : Fin (r + 1)) :
    Continuous fun x : Mt k r => Ga k r l (fun a => Matrix.of x *ᵥ phiV k r a) := by
  unfold Ga
  refine Complex.continuous_re.comp ?_
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.of_apply]
  have hx : Continuous fun x : Mt k r => Matrix.of x := continuous_id
  first
    | exact ((hx.matrix_mulVec continuous_const).star).dotProduct (hx.matrix_mulVec continuous_const)
    | (simp only [dotProduct]; exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (hx.matrix_mulVec continuous_const).star).mul ((continuous_apply i).comp (hx.matrix_mulVec continuous_const)))
    | (simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]; fun_prop)

theorem meas_xi (k r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable fun x : Mt k r => xiN k r s (Matrix.of x) := by
  unfold xiN xiR
  refine Measurable.real_toNNReal ?_
  refine Finset.measurable_prod _ fun l _ => ?_
  refine Measurable.pow_const ?_ _
  exact ((cont_ga l).sqrt).measurable

end ReciprocityTheory.ChartRestriction.DS.Xi.XI
end
end

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section fs
variable {k r : ℕ}

theorem iic_eq (l : Fin (r + 1)) :
    Finset.Iic l = Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)) := by
  ext c
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and, Fin.le_def]
  constructor
  · intro hc; exact ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩
  · rintro ⟨a, rfl⟩
    have := a.isLt
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    omega

theorem ofReal_fsR (s : Fin (r + 1) → ℝ) (x : Mat k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hGa : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l (fun a => x *ᵥ phiV' k r a))
    (hpos : ∀ l, 0 < Ga k r l (fun a => x *ᵥ phiV' k r a)) :
    ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  unfold fsR
  rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hpos l).le _)]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ht : Ga k r l (fun a => x *ᵥ phiV' k r a) = ((cl τ l : ℝ)) ^ 2 := by
    rw [← hGa l, iic_eq, Finset.prod_map, Finset.prod_pow, cl, NNReal.coe_prod]
    rfl
  have hc : 0 < (cl τ l : ℝ) := by
    have h0 := hpos l
    rw [ht] at h0
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (fun he => by rw [← he] at h0; simp at h0)
  rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← ENNReal.ofReal_rpow_of_pos hc,
    ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  ring

theorem xphi_linInd (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    LinearIndependent ℂ (fun a => x *ᵥ phiV' k r a) := by
  have hinj : Function.Injective (Matrix.mulVecLin x) := fun u v huv => by
    have h2 := congrArg (fun w => x⁻¹ *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, uh_inv_mul hx] using h2
  exact (phiV'_linInd k r hk).map' (Matrix.mulVecLin x) (LinearMap.ker_eq_bot.2 hinj)

theorem iw_at (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ s, ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hGa⟩ := hIW k r (fun a => x *ᵥ phiV' k r a) hk (xphi_linInd hk hx)
    (fun a b => by rw [herm_UH' _ hx]; exact phiV'_iso k r hk a b)
  exact ⟨κ, hκ, τ, hτ, hY, fun s => ofReal_fsR s x τ hGa (fun l => GS.ga_pos k r _ (xphi_linInd hk hx) l)⟩

theorem fsE_left (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (x⁻¹ * g) = ENNReal.ofReal (fsR k r s x) * FsE k r s (κ⁻¹ * g) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hx
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_left hx hκ.1 τ hτ hY g)

theorem fsE_right (hIW : IW) (hk : 1 ≤ k) {y : Mat k r} (hy : y ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (g * y) = ENNReal.ofReal (fsR k r s y) * FsE k r s (g * κ) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hy
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_right τ hτ hY g)

theorem fsR_nonneg {k r : ℕ} (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) (s : Fin (r + 1) → ℝ) :
    0 ≤ fsR k r s x :=
  Finset.prod_nonneg fun l _ => Real.rpow_nonneg (GS.ga_pos k r _ (xphi_linInd hk hx) l).le _

end fs

section meas
variable {k r : ℕ}

theorem cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) :=
  Continuous.matrix_mul continuous_const continuous_id

theorem cont_rmul (a : Mat k r) : Continuous (rmulF a : Mt k r → Mt k r) :=
  Continuous.matrix_mul continuous_id continuous_const

def lmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv g := by
    show a⁻¹ * (a * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_inv_mul ha, Matrix.one_mul]; rfl
  right_inv g := by
    show a * (a⁻¹ * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_mul_inv ha, Matrix.one_mul]; rfl
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable

def rmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv g := by
    show Matrix.of g * a * a⁻¹ = g
    rw [Matrix.mul_assoc, uh_mul_inv ha, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of g * a⁻¹ * a = g
    rw [Matrix.mul_assoc, uh_inv_mul ha, Matrix.mul_one]; rfl
  measurable_toFun := (cont_rmul a).measurable
  measurable_invFun := (cont_rmul a⁻¹).measurable

theorem lmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (lmulM a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (lmulE ha) (μ := μ)
  rw [show ⇑(lmulE ha) = lmulM a from rfl, hμ.left a ha] at h
  exact h.symm

theorem rmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (rmulF a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (rmulE ha) (μ := μ)
  rw [show ⇑(rmulE ha) = rmulF a from rfl, hμ.right a ha] at h
  exact h.symm

end meas

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
end
end
