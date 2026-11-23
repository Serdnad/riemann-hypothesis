module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SpanStepHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (m r : ℕ) (t : Fin r → Ω), (∀ l, t l ∈ chartLat y a m) ∧
      ∀ (n : ℕ), ∀ s ∈ chartLat y a n, ∀ j, w j ≠ 0 →
        ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w (fun _ => m) t (n + D)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric

noncomputable section

theorem ChartSupBound.proof : ChartSupBound.Statement := by
  intro D V K ψ ν hV hK hKV hψ hν hν0
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, fun n _ F _ w hw => by simp [hKe] at hw⟩
  obtain ⟨r, hr0, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  set S := cthickening r K with hS
  have hSc : IsCompact S := hK.cthickening
  have hSne : S.Nonempty := hKne.mono (self_subset_cthickening K)

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ M := by
    have h1 := hψ.fderiv_of_isOpen hV (m := 1) (by norm_num)
    exact hSc.exists_bound_of_continuousOn ((h1.continuousOn_fderiv_of_isOpen hV le_rfl).mono hrV)
  set M' := |M| with hM'

  obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hSne (hν.mono hrV)
  set ν₀ := ν x₀ with hν₀
  have hν₀pos : 0 < ν₀ := hν0 x₀ (hrV hx₀)
  set P : ℝ := (Real.pi * r ^ 2) ^ D with hP
  have hPpos : 0 < P := by positivity
  have hprod : ∏ _j : Fin D, gaussDiscMass 0 r = P := by
    rw [hP, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [gaussDiscMass]
  refine ⟨Real.exp (M' * r ^ 2) / (ν₀ * P), fun n hn F hF w hw => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set s := r / Real.sqrt n with hs
  have hs2 : (n : ℝ) * s ^ 2 = r ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hnpos.le]
    field_simp
  have hsr : s ≤ r := by
    rw [hs]
    refine div_le_self hr0.le ?_
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  set B := closedBall (0 : Fin D → ℂ) s with hB
  have hzS : ∀ z ∈ B, closedBall w ‖z‖ ⊆ S := fun z hz =>
    (closedBall_subset_closedBall ((mem_closedBall_zero_iff.1 hz).trans hsr)).trans
      (closedBall_subset_cthickening hw r)
  have hwzS : ∀ z ∈ B, w + z ∈ S := fun z hz => hzS z hz (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])

  set ℓ := fderiv ℝ ψ w with hℓ
  set lam : (Fin D → ℂ) →L[ℂ] ℂ := StrongDual.extendRCLike (𝕜 := ℂ) ℓ with hlam
  have hre : ∀ z, (lam z).re = ℓ z := fun z => by
    rw [hlam, StrongDual.extendRCLike_apply]
    simp
  set G : (Fin D → ℂ) → ℂ := fun z => F (w + z) * Complex.exp (((-(n : ℝ) / 2 : ℝ) : ℂ) * lam z)
    with hGdef
  have hG0 : G 0 = F w := by simp [hGdef]
  have hGan : AnalyticOnNhd ℂ G B := by
    intro z hz
    have haff : AnalyticAt ℂ (fun z : Fin D → ℂ => w + z) z := analyticAt_const.add analyticAt_id
    exact ((hF _ (hrV (hwzS z hz))).comp_of_eq haff rfl).mul
      ((analyticAt_const.mul (lam.analyticAt z)).cexp)
  have hPn := PolydiscSubmean.proof D n (fun _ => 0) r G (by omega) hr0 (fun _ => le_rfl) hGan
  simp only [zero_mul, Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at hPn
  rw [hG0, hprod] at hPn
  set k : ℝ := ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) with hk
  have hk0 : 0 ≤ k := by positivity

  have hpt : ∀ z ∈ B, ENNReal.ofReal (k * ‖G z‖ ^ 2) ≤
      ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z)) := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have hGz : ‖G z‖ ^ 2 = ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z) := by
      simp only [hGdef]
      rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre, mul_pow, sq (Real.exp _),
        ← Real.exp_add]
      congr 2
      ring
    have hT := ChartTaylorCover.taylor_le hV hψ ((hzS z hz).trans hrV)
      (fun x hx => (hM x (hzS z hz hx)).trans (le_abs_self M))
    have hz' : ‖z‖ ≤ s := mem_closedBall_zero_iff.1 hz
    have hnz : (n : ℝ) * (M' * ‖z‖ ^ 2) ≤ M' * r ^ 2 := by
      calc (n : ℝ) * (M' * ‖z‖ ^ 2) = M' * ((n : ℝ) * ‖z‖ ^ 2) := by ring
        _ ≤ M' * ((n : ℝ) * s ^ 2) := by gcongr
        _ = M' * r ^ 2 := by rw [hs2]
    have hexp : Real.exp (-(M' * r ^ 2)) * (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z)) ≤
        Real.exp (-(n : ℝ) * ψ (w + z)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hT hnpos.le
      nlinarith
    have hνz : ν₀ ≤ ν (w + z) := isMinOn_iff.1 hmin _ (hwzS z hz)
    rw [hGz, hk]
    have hF0 : 0 ≤ ‖F (w + z)‖ ^ 2 := by positivity
    calc ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
          (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z))
        = ‖F (w + z)‖ ^ 2 * (Real.exp (-(M' * r ^ 2)) *
            (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z))) * ν₀ := by ring
      _ ≤ ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hF0) hνz hν₀pos.le (by positivity)

  have hΦ : MeasurePreserving (fun z : Fin D → ℂ => w + z) volume volume :=
    measurePreserving_add_left volume w
  have hemb : MeasurableEmbedding (fun z : Fin D → ℂ => w + z) :=
    (Homeomorph.addLeft w).isClosedEmbedding.measurableEmbedding
  have hint : ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) ≤ ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by
    calc _ ≤ ‖∫ z in B, ‖G z‖ ^ 2‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ z in B, ‖‖G z‖ ^ 2‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = _ := lintegral_congr fun z => Real.enorm_eq_ofReal (by positivity)
  have hmain : ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) ≤
      ∫⁻ z in V, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(n : ℝ) * ψ z) * ν z) := by
    calc _ ≤ ENNReal.ofReal (k * ∫ z in B, ‖G z‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hPn hk0)
      _ = ENNReal.ofReal k * ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) := ENNReal.ofReal_mul hk0
      _ ≤ ENNReal.ofReal k * ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by gcongr
      _ = ∫⁻ z in B, ENNReal.ofReal k * ENNReal.ofReal (‖G z‖ ^ 2) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ z in B, ENNReal.ofReal (k * ‖G z‖ ^ 2) :=
          lintegral_congr fun z => (ENNReal.ofReal_mul hk0).symm
      _ ≤ ∫⁻ z in B, ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) *
            ν (w + z)) :=
          setLIntegral_mono' isClosed_closedBall.measurableSet hpt
      _ = ∫⁻ y in (fun z : Fin D → ℂ => w + z) '' B,
            ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y) :=
          hΦ.setLIntegral_comp_emb hemb
            (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y)) B
      _ ≤ _ := lintegral_mono_set (image_subset_iff.2 fun z hz => hrV (hwzS z hz))
  have hC0 : 0 ≤ Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D := by positivity
  have heq : Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D *
      (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
    have hnD : (n : ℝ) ^ D ≠ 0 := by positivity
    have he : Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hνP : ν₀ * P ≠ 0 := by positivity
    rw [hk, div_eq_mul_inv]
    calc Real.exp (M' * r ^ 2) * (ν₀ * P)⁻¹ * (n : ℝ) ^ D *
          (ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
            (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P))
        = (Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2))) * ((n : ℝ) ^ D * ((n : ℝ) ^ D)⁻¹) *
            ((ν₀ * P) * (ν₀ * P)⁻¹) * (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w)) := by ring
      _ = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
        rw [he, mul_inv_cancel₀ hnD, mul_inv_cancel₀ hνP]; ring
  calc ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w))
      = ENNReal.ofReal (Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D) *
          ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) := by
        rw [← ENNReal.ofReal_mul hC0, heq]
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbertIncrement

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem weight_intWeight (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (intWeight (ι := ι)) e =
      fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) := by
  funext k
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_sum, Nat.cast_mul, intWeight, unitDeg, blockWeight]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : k = v.1 <;> simp [h]

theorem isWeightedHomogeneous_intWeight_iff {f : MRing ι F} {a : K → ℕ} :
    IsWeightedHomogeneous (intWeight (ι := ι)) f (fun k => (a k : ℤ)) ↔
      IsWeightedHomogeneous (blockWeight ι) f a := by
  constructor
  · intro h e he
    funext k
    have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = (a k : ℤ) := by
      have := congrFun (h he) k
      rw [weight_intWeight] at this
      exact this
    exact_mod_cast e1
  · intro h e he
    rw [weight_intWeight, h he]

theorem ringPiece_natCast (a : K → ℕ) :
    ringPiece (F := F) (ι := ι) (fun k => (a k : ℤ)) =
      weightedHomogeneousSubmodule F (blockWeight ι) a := by
  ext f
  simp only [ringPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_intWeight_iff

theorem component_intWeight_mem {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    {f : MRing ι F} (hf : f ∈ J) (m : K → ℤ) :
    weightedHomogeneousComponent (intWeight (ι := ι)) m f ∈ J := by
  classical
  by_cases hm : ∀ k, 0 ≤ m k
  · have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f =
        weightedHomogeneousComponent (blockWeight ι) (fun k => (m k).toNat) f := by
      ext e
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_intWeight]
      have hiff : ((fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ)) = m) ↔
          Finsupp.weight (blockWeight ι) e = fun k => (m k).toNat := by
        constructor
        · intro h
          funext k
          have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
          have := hm k
          show _ = (m k).toNat
          omega
        · intro h
          funext k
          have e1 : Finsupp.weight (blockWeight ι) e k = (m k).toNat := congrFun h k
          have := hm k
          show ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k
          omega
      simp only [hiff]
    rw [e]
    exact hJ f hf _
  · push Not at hm
    obtain ⟨k, hk⟩ := hm
    have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f = 0 := by
      ext e
      rw [coeff_weightedHomogeneousComponent, weight_intWeight]
      split_ifs with h
      · have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
        omega
      · rfl
    rw [e]
    exact J.zero_mem

theorem isMultiHomogIdeal_sup_X {q : Ideal (MRing ι F)} (hq : IsMultiHomogIdeal q)
    (v : Σ k, ι k) : IsMultiHomogIdeal (q ⊔ Ideal.span {(X v : MRing ι F)}) := by
  classical
  intro f hf n
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hX : IsMultiHomog (X v : MRing ι F) (blockWeight ι v) :=
    isWeightedHomogeneous_X F (blockWeight ι) v
  rw [map_add (f := _), GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide.component_mul_form hX t n]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hq p hp n)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩)
  · exact zero_mem _

def quotPiece (J : Ideal (MRing ι F)) (m : K → ℤ) : Submodule F (MRing ι F ⧸ J) :=
  (ringPiece m).map (Ideal.Quotient.mkₐ F J).toLinearMap

theorem quotPiece_natCast (J : Ideal (MRing ι F)) (a : K → ℕ) :
    quotPiece J (fun k => (a k : ℤ)) = gradedPiece J a := by
  rw [quotPiece, gradedPiece, ringPiece_natCast]

theorem isMultigrading_quotPiece [Fintype K] {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) :
    IsMultigrading ι (MRing ι F ⧸ J) (quotPiece J) := by
  refine ⟨?_, ?_⟩
  · classical
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum m hm
      have hex : ∀ i ∈ s, ∃ y ∈ ringPiece (F := F) (ι := ι) i,
          (Ideal.Quotient.mkₐ F J).toLinearMap y = v i := fun i hi => Submodule.mem_map.mp (hv i hi)
      choose! x hx hxv using hex
      have hy : (∑ i ∈ s, x i) ∈ J := by

        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        rw [← hsum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hxv i hi]
        rfl
      have hc := component_intWeight_mem hJ hy m

      rw [map_sum] at hc
      have hcs : (∑ i ∈ s, weightedHomogeneousComponent (intWeight (ι := ι)) m (x i)) = x m := by
        rw [Finset.sum_eq_single m]
        · rw [weightedHomogeneousComponent_of_mem (hx m hm), ite_eq_left rfl]
        · intro j hj hjm
          rw [weightedHomogeneousComponent_of_mem (hx j hj), ite_eq_right (Ne.symm hjm)]
        · intro h
          exact absurd hm h
      rw [hcs] at hc
      rw [← hxv m hm]
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
    · show (⨆ m, (ringPiece (F := F) (ι := ι) m).map (Ideal.Quotient.mkₐ F J).toLinearMap) = ⊤
      rw [← Submodule.map_iSup]
      show Submodule.map _ (⨆ i, weightedHomogeneousSubmodule F (intWeight (ι := ι)) i) = ⊤
      rw [(weightedDecomposition F (intWeight (ι := ι))).isInternal.submodule_iSup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective F J
  · intro v m x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have hmul : (X v : MRing ι F) * y ∈ ringPiece (m + unitDeg v.1) := by
      change IsWeightedHomogeneous (intWeight (ι := ι)) y m at hy
      change IsWeightedHomogeneous (intWeight (ι := ι)) (X v * y) (m + unitDeg v.1)
      rw [add_comm m (unitDeg v.1)]
      exact (isWeightedHomogeneous_X F (intWeight (ι := ι)) v).mul hy
    exact Submodule.mem_map.mpr ⟨_, hmul, rfl⟩

theorem proof (hrec : IntersectionRecursion.Statement.{u}) : HilbertIncrement.Statement.{u} := by
  intro d hmod F _ K _ _ ι _ q hq hdim b
  obtain ⟨i, hi⟩ := hq.relevant b
  have hJ : IsMultiHomogIdeal (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) :=
    isMultiHomogIdeal_sup_X hq.multiHomog ⟨b, i⟩
  obtain ⟨hstep, hsupp⟩ :=
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.HilbertIncrement.closed.{u} F K ι (d + 1) q b i hq
      hdim (by omega) hi
  obtain ⟨a₀, C, hbd⟩ := hmod F K ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}))
    (quotPiece _) (isMultigrading_quotPiece hJ) (fun W hW hann => by
      rw [Ideal.annihilator_quotient] at hann
      simpa using hsupp W hW hann)
  refine ⟨a₀, C, fun a ha => ?_⟩
  have h1 : hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) =
      (Module.finrank F (quotPiece (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})
        fun k => (a k : ℤ)) : ℤ) := by
    rw [show unitDeg b = Pi.single b 1 from rfl, hstep, hilbFn,
      ite_eq_left (fun k => Nat.cast_nonneg _), quotPiece_natCast]
    have ha' : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => by omega
    rw [ha']
  have h2 : intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) =
      topCycleNum F ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) d
        (fun _ => fun k => (a k : ℤ)) := by
    rw [hrec F K ι q d hq hdim b i hi]
    unfold topCycleNum
    refine finsum_congr fun W => ?_
    have hann : Module.annihilator (MRing ι F)
        (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) =
        q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} := Ideal.annihilator_quotient
    by_cases hc : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dite_eq_left hc, dite_eq_left (by rw [hann]; exact hc)]
      rfl
    · rw [dite_eq_right hc, dite_eq_right (by rw [hann]; exact hc)]
  rw [h1, h2]
  simpa using hbd a ha

end HilbertIncrement

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleiman.atDim_of_steps (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    ∀ d, MixedKleiman.AtDim d := by
  intro d
  induction d with
  | zero => exact MixedKleiman.atDim_zero
  | succ n ih =>
    have ih' : MixedKleiman.AtDim (n + 1 - 1) := by simpa using ih
    have hLow : MixedKleiman.LowAt (n + 1) := hL (n + 1) ih'
    intro K _ ι _ P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hLow K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    · have hlist : (fun i : Fin (n + 1) => if (i : ℕ) < n + 1 then M else A) = fun _ => M :=
        funext fun i => if_pos i.isLt
      rw [hlist]
      rcases Nat.lt_or_ge n 1 with hn | hn
      · obtain rfl : n = 0 := by omega
        have hW := hhM P hP le_rfl
        have e : (fun _ : Fin 1 => M) = ![M] := by
          funext i
          fin_cases i
          rfl
        simpa [e] using hW
      · exact hT (n + 1) (by omega) ih' hLow K ι P P0 M II hII h1 hP h0 hsM hnM hcM hhM

theorem MixedKleiman.proof (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    MixedKleiman.Statement := by
  intro K _ ι _ P P0 d M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
  exact MixedKleiman.atDim_of_steps hL hT d K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
