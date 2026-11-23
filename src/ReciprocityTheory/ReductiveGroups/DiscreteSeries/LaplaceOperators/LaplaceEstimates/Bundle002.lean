module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ExistsOrthogonalProjectionInner
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

theorem convolution_integral_fubini {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (f : L2 ε)
    (hFc : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)))
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hγ : MemLp (fGam ε f) 2 (Formalism.REAL.muG ε)) {N : Set (Formalism.REAL.UJ ε)}
    (hNf : Formalism.REAL.muG ε N ≠ ∞) (x : Formalism.REAL.UJ ε) :
    ∫ z in N, fPhi ε F f (z * x) ∂(Formalism.REAL.muG ε) =
      ∫ y, (∫ z in N, F (Formalism.MainNotions.S.umat (z * y)) ∂(Formalism.REAL.muG ε)) * fGam ε f (y⁻¹ * x)
        ∂(Formalism.REAL.muG ε) := by
  set μ := Formalism.REAL.muG ε with hμ
  have e1 : (fun z => fPhi ε F f (z * x)) =
      fun z => ∫ y, F (Formalism.MainNotions.S.umat (z * y)) * fGam ε f (y⁻¹ * x) ∂μ := by
    funext z
    unfold fPhi
    rw [← integral_mul_left_eq_self (fun y => F (Formalism.MainNotions.S.umat y) * fGam ε f (y⁻¹ * (z * x))) z]
    congr 1
    funext y
    congr 2
    group
  rw [e1]
  set G2 : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε → ℂ :=
    fun z y => F (Formalism.MainNotions.S.umat (z * y)) * fGam ε f (y⁻¹ * x) with hG2
  have hcont : Continuous (Function.uncurry G2) := by
    show Continuous fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat (p.1 * p.2)) * fGam ε f (p.2⁻¹ * x)
    exact (hFc.comp continuous_mul).mul ((matrix_coefficient_continuous ε f).comp (continuous_snd.inv.mul continuous_const))
  have hB : MemLp (fun y => fGam ε f (y⁻¹ * x)) 2 μ :=
    hγ.comp_measurePreserving ((measurePreserving_mul_right ε x).comp (Measure.measurePreserving_inv μ))
  have hA : ∀ z, MemLp (fun y => F (Formalism.MainNotions.S.umat (z * y))) 2 μ :=
    fun z => hF2.comp_measurePreserving (measurePreserving_mul_left μ z)
  have hint : Integrable (Function.uncurry G2) ((μ.restrict N).prod μ) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun z => (hA z).integrable_mul hB, ?_⟩
    have : IsFiniteMeasure (μ.restrict N) := isFiniteMeasure_restrict.2 hNf
    refine Integrable.of_bound hcont.aestronglyMeasurable.norm.integral_prod_right'
      ((∫ y, ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ y, ‖fGam ε f (y⁻¹ * x)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hH := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun y => F (Formalism.MainNotions.S.umat (z * y))) (g := fun y => fGam ε f (y⁻¹ * x))
      (by rw [ENNReal.ofReal_ofNat]; exact hA z) (by rw [ENNReal.ofReal_ofNat]; exact hB)
    have ht : ∫ y, ‖F (Formalism.MainNotions.S.umat (z * y))‖ ^ (2 : ℝ) ∂μ = ∫ y, ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ) ∂μ :=
      integral_mul_left_eq_self (fun y => ‖F (Formalism.MainNotions.S.umat y)‖ ^ (2 : ℝ)) z
    rw [ht] at hH
    refine le_of_eq_of_le ?_ hH
    simp only [Function.uncurry_apply_pair, hG2, norm_mul]
  rw [integral_integral_swap hint]
  congr 1
  funext y
  exact integral_mul_const _ _

theorem reproducing_formula_closed_invariant {K : Submodule ℂ (L2 ε)} {d : ℝ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hFc : ContinuousOn F (UJset ε))
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (hKc : IsClosed (K : Set (L2 ε))) (hfK : toL2 ε F ∈ K)
    (hKs : ∀ g ∈ UJset ε, ∀ u ∈ K, rreg ε g u ∈ K)
    (hS : ∀ a ∈ K, ∀ b ∈ K, ∀ a' ∈ K, ∀ b' ∈ K,
      Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
        star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
      ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
        ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ)) :
    ∀ x ∈ UJset ε, ∫ y, F (Formalism.MainNotions.S.umat y) *
        ⟪toL2 ε F, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * x) (toL2 ε F)⟫_ℂ ∂(Formalism.REAL.muG ε) =
      ⟪toL2 ε F, toL2 ε F⟫_ℂ / (d : ℂ) * F x := by
  intro x hx
  obtain ⟨x, rfl⟩ := exists_unitary_preimage ε hx
  set f := toL2 ε F with hfdef
  set μ := Formalism.REAL.muG ε with hμ
  set c : ℂ := ⟪f, f⟫_ℂ / (d : ℂ) with hc
  have hL : ∫ y, F (Formalism.MainNotions.S.umat y) * ⟪f, rreg ε ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat x) f⟫_ℂ ∂μ =
      fPhi ε F f x := by
    unfold fPhi fGam
    congr 1
    funext y
    rw [unitary_matrix_mul, unitary_matrix_inv_alt]
  rw [hL]
  have hFc' : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) :=
    hFc.comp_continuous (continuous_unitary_matrix ε) (fun g => unitary_matrix_mem_set ε g)
  have hγ : MemLp (fGam ε f) 2 μ := matrix_coefficient_memLp ε hS hfK hfK
  set D : Formalism.REAL.UJ ε → ℂ := fun w => fPhi ε F f w - c * F (Formalism.MainNotions.S.umat w) with hD
  have hDc : Continuous D := (convolution_coefficient_continuous hS hF2 hfK).sub (continuous_const.mul hFc')
  by_contra hne
  have hδ : D x ≠ 0 := fun h0 => hne (sub_eq_zero.1 h0)
  have hδp : 0 < ‖D x‖ := norm_pos_iff.2 hδ
  have hDz : Continuous fun z : Formalism.REAL.UJ ε => D (z * x) := hDc.comp (continuous_id.mul continuous_const)
  have hev : ∀ᶠ z in 𝓝 (1 : Formalism.REAL.UJ ε), ‖D (z * x) - D x‖ < ‖D x‖ / 2 := by
    have ht := hDz.tendsto 1
    simp only [one_mul] at ht
    have := (Metric.tendsto_nhds.1 ht) (‖D x‖ / 2) (by linarith)
    simpa [dist_eq_norm] using this
  obtain ⟨C₀, hC₀c, hC₀n⟩ := exists_compact_mem_nhds (1 : Formalism.REAL.UJ ε)
  set N := interior ({z | ‖D (z * x) - D x‖ < ‖D x‖ / 2} ∩ C₀) with hN
  have hNo : IsOpen N := isOpen_interior
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ N := mem_interior_iff_mem_nhds.2 (Filter.inter_mem hev hC₀n)
  have hNC : N ⊆ C₀ := interior_subset.trans Set.inter_subset_right
  have hNP : ∀ z ∈ N, ‖D (z * x) - D x‖ < ‖D x‖ / 2 := fun z hz => (interior_subset hz).1
  have hNlt : μ N < ∞ := lt_of_le_of_lt (measure_mono hNC) hC₀c.measure_lt_top
  have hNf : μ N ≠ ∞ := hNlt.ne
  have hNpos : 0 < μ N := hNo.measure_pos μ ⟨1, h1N⟩
  have hNr : 0 < (μ N).toReal := ENNReal.toReal_pos hNpos.ne' hNf
  have hNm : MeasurableSet N := hNo.measurableSet
  have hIphi : IntegrableOn (fun z => fPhi ε F f (z * x)) N μ :=
    (((convolution_coefficient_continuous hS hF2 hfK).comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact
      hC₀c).mono_set hNC
  have hIF : IntegrableOn (fun z => F (Formalism.MainNotions.S.umat (z * x))) N μ :=
    ((hFc'.comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact hC₀c).mono_set hNC
  have hkey : ∫ z in N, fPhi ε F f (z * x) ∂μ = c * ∫ z in N, F (Formalism.MainNotions.S.umat (z * x)) ∂μ := by
    rw [convolution_integral_fubini f hFc' hF2 hγ hNf x]
    have e2 : (fun y => (∫ z in N, F (Formalism.MainNotions.S.umat (z * y)) ∂μ) * fGam ε f (y⁻¹ * x)) =
        fun y => ⟪(indicatorConstLp 2 hNm hNf (1 : ℂ) : L2 ε), rreg ε (Formalism.MainNotions.S.umat y) f⟫_ℂ *
          fGam ε f (y⁻¹ * x) := by
      funext y
      rw [inner_indicator_right_regular ε hF2 hNm hNf y]
      rfl
    rw [e2, schur_orthogonality_integral hKc hKs hS hfK, inner_indicator_right_regular ε hF2 hNm hNf x, hc]
    simp only [unitary_matrix_mul]
    ring
  have hzero : ∫ z in N, D (z * x) ∂μ = 0 := by
    simp only [hD]
    rw [integral_sub hIphi (hIF.const_mul c), integral_const_mul, hkey, sub_self]
  have hID : IntegrableOn (fun z => D (z * x)) N μ := hIphi.sub (hIF.const_mul c)
  have hIc : IntegrableOn (fun _ : Formalism.REAL.UJ ε => D x) N μ :=
    (continuous_const.continuousOn.integrableOn_compact hC₀c).mono_set hNC
  have hNr' : 0 < μ.real N := hNr
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun z => D (z * x) - D x) hNlt
    (fun z hz => (hNP z hz).le)
  rw [integral_sub hID hIc, hzero, setIntegral_const,
    zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hNr'.le] at hbound
  nlinarith [mul_pos hNr' hδp]

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem gapNeed : GapNeedStatement := by
  intro k r ε h hp hq hg
  unfold StepGap at hg
  unfold hNeed S7.q0
  obtain ⟨h1, h2⟩ := hg
  rw [← Nat.cast_min] at h2 ⊢
  have hqr : ((qOf ε : ℕ) : ℝ) - 1 = (r : ℝ) := by rw [hq]; push_cast; ring
  rw [hqr]
  have hm : 1 ≤ min (pOf ε) (qOf ε) := by
    by_contra hc
    have h0 : min (pOf ε) (qOf ε) = 0 := by omega
    rw [h0] at h2
    simp at h2
    linarith [le_max_left (0 : ℝ) (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2)]
  refine ⟨hm, ?_⟩
  set m := min (pOf ε) (qOf ε) with hmdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; norm_cast; omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsq : 1 ≤ Real.sqrt (2 * (m : ℝ)) := Real.one_le_sqrt.mpr (by linarith)
  set s := 8 * Real.sqrt (2 * (m : ℝ)) with hs
  have hs8 : 8 ≤ s := by rw [hs]; linarith
  have hspos : 0 < s := by linarith
  set X := max (2 * N * (m : ℝ)) (2 * (r : ℝ) * N ^ 2) with hX
  have hX1 : 2 * N * m ≤ X := le_max_left _ _
  have hNm : 1 ≤ N * m := by nlinarith
  have hC : s * (4 * X + 1) < h := by
    have h4 := h2
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hspos] at h4
    linarith
  have hsX : 8 * X ≤ s * X := by nlinarith
  refine max_lt (by linarith) (max_lt ?_ hC)
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.Lap
end

section

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem finB_umat_inv {n : ℕ} {ε : Fin n → Bool} (y : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat y⁻¹ = (Formalism.MainNotions.S.umat y)⁻¹ := by
  show ((y⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = _
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem finB_umat_mul {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl

theorem finB_intJ_shift {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) (b : ℝ)
    (hI : Integrable (fun y : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y) ^ (-b)) (Formalism.REAL.muG ε))
    (γ : Formalism.REAL.UJ ε) :
    Integrable (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) (Formalism.REAL.muG ε) ∧
    ∫ y, frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b) ∂(Formalism.REAL.muG ε) =
      ∫ y, frob (Formalism.MainNotions.S.umat y) ^ (-b) ∂(Formalism.REAL.muG ε) := by
  have e : (fun y : Formalism.REAL.UJ ε => frob ((Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ) ^ (-b)) =
      fun y => (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) (γ⁻¹ * y) := by
    funext y
    have h1 : (Formalism.MainNotions.S.umat y)⁻¹ * Formalism.MainNotions.S.umat γ = (Formalism.MainNotions.S.umat (γ⁻¹ * y))⁻¹ := by
      rw [← finB_umat_inv, ← finB_umat_inv, ← finB_umat_mul, _root_.mul_inv_rev, inv_inv]
    simp only
    rw [h1, finB_frob_inv (unitary_matrix_mem_set ε _)]
  rw [e]
  exact ⟨hI.comp_mul_left γ⁻¹,
    integral_mul_left_eq_self (μ := Formalism.REAL.muG ε) (fun y' : Formalism.REAL.UJ ε => frob (Formalism.MainNotions.S.umat y') ^ (-b)) γ⁻¹⟩

theorem finB_pair {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (β : ℝ) (hβ : 0 ≤ β) {Y g : Mat k r}
    (hY : Y ∈ UJset ε) (hg : g ∈ UJset ε) (hYg : Y⁻¹ * g ∈ UJset ε) :
    frob Y ^ (-β) * frob (Y⁻¹ * g) ^ (-β) ≤
      frob g ^ (-(β / 4)) * (frob Y ^ (-(β / 2)) + frob (Y⁻¹ * g) ^ (-(β / 2))) := by
  have hA := finB_one_le hY
  have hB := finB_one_le hYg
  have hG := finB_one_le hg
  have hle := finB_le_mul hY g
  have hAh : 0 ≤ frob Y ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hBh : 0 ≤ frob (Y⁻¹ * g) ^ (-(β / 2)) := Real.rpow_nonneg (by linarith) _
  have hGq : 0 ≤ frob g ^ (-(β / 4)) := Real.rpow_nonneg (by linarith) _
  rcases le_total (frob Y) (frob (Y⁻¹ * g)) with h | h
  · calc _ ≤ frob g ^ (-(β / 4)) * frob (Y⁻¹ * g) ^ (-(β / 2)) :=
          S0.DecA.pb_real β _ _ _ hβ hA hB (by linarith) (le_of_le_of_eq hle (mul_comm _ _)) h
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAh) hGq
  · have := S0.DecA.pb_real β (frob (Y⁻¹ * g)) (frob Y) (frob g) hβ hB hA (by linarith) hle h
    rw [mul_comm] at this
    calc _ ≤ frob g ^ (-(β / 4)) * frob Y ^ (-(β / 2)) := this
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBh) hGq

theorem finB_one_UH (k r : ℕ) : (1 : Mat k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem finB_frob_conj_ge {k r : ℕ} {P : Mat k r} (hP : IsUnit P.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : Mat k r, c * Formalism.FourierDecayAlt.B.gN g ≤ frob (P * g * P⁻¹) := by
  letI : NormedAddCommGroup (Mat k r) := Matrix.frobeniusNormedAddCommGroup
  have hg : ∀ A : Mat k r, Formalism.FourierDecayAlt.B.gN A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_eq_norm_sq, Real.rpow_two]
  have hf : ∀ A : Mat k r, frob A = ‖A‖ := by
    intro A
    rw [Matrix.frobenius_norm_def, frob, Real.sqrt_eq_rpow]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Real.rpow_two]
  refine ⟨1 / (‖P⁻¹‖ * ‖P‖ + 1), by positivity, fun g => ?_⟩
  have e : g = P⁻¹ * (P * g * P⁻¹) * P := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hP, Matrix.nonsing_inv_mul _ hP,
      Matrix.mul_one]
  have h1 : ‖g‖ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ := by
    conv_lhs => rw [e]
    calc ‖P⁻¹ * (P * g * P⁻¹) * P‖ ≤ ‖P⁻¹ * (P * g * P⁻¹)‖ * ‖P‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖P⁻¹‖ * ‖P * g * P⁻¹‖ * ‖P‖ :=
        mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
  rw [hg, hf, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (P * g * P⁻¹), norm_nonneg P⁻¹, norm_nonneg P,
    mul_nonneg (norm_nonneg P⁻¹) (norm_nonneg P)]

theorem finB_intS (hIS : S0.IntSStatement) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (x : Mat k r) (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (b : ℝ) (hb : S0.bS k r < b) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)) (μW.prod μN) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hb0 : 0 ≤ b := by
    have : 0 ≤ S0.bS k r := by unfold S0.bS S0.nS; positivity
    linarith
  obtain ⟨c0, hc0, hcg⟩ := finB_frob_conj_ge hd
  have h1 := hIS k r z μW μN hz hT hW hN 1 (finB_one_UH k r) x hx b hb
  simp only [inv_one, Matrix.one_mul] at h1
  have hae := ae_mem_unitary_nilpotent_product z μW μN hW hN
  have hof : Continuous (fun g : Formalism.QuantumDeterminants.Mt k r => (Matrix.of g : Mat k r)) := S0.Dec.of_cont k r
  have hfc : Continuous (fun M : Mat k r => frob M) := by
    have : (fun M : Mat k r => frob M) = fun M => Formalism.FourierDecayAlt.B.gN M := funext finB_frob_eq
    rw [this]; exact S0.Dec.gN_cont k r
  have hgc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) :=
    (continuous_const.matrix_mul (((hof.comp continuous_fst).matrix_mul (hof.comp continuous_snd)).matrix_mul
      continuous_const)).matrix_mul continuous_const
  refine Integrable.mono' (h1.const_mul (c0 ^ (-b))) ((hfc.comp hgc).measurable.pow_const _).aestronglyMeasurable ?_
  filter_upwards [hae] with p hp
  have hM : Matrix.of p.1 * Matrix.of p.2 * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    unitary_hermitian_form_mul_mem (unitary_hermitian_form_mul_mem hp.1.1 hp.2.1) hx
  have hg1 := S0.DecA.one_le_gN' hM
  have hge := hcg (Matrix.of p.1 * Matrix.of p.2 * x)
  have hpos : 0 < c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  calc frob (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) ^ (-b)
      ≤ (c0 * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hpos hge (by linarith)
    _ = c0 ^ (-b) * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2 * x) ^ (-b) :=
        Real.mul_rpow hc0.le (by linarith)

theorem finB_UJ_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {a b : Mat k r} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := (mir_inUJ_iff ε a).2 ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := (mir_inUJ_iff ε b).2 hb
  show inUJ ε (a * b)
  rw [← mir_inUJ_iff]
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem finB_UJ_closed {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) : IsClosed (UJset ε : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem finB_gap {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hgap : StepGap ε r h) :
    1 ≤ S7.q0 ε ∧ 0 < h ∧
      4 * max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) <
        aExp ε h - 1 := by
  obtain ⟨h1, h2⟩ := hgap
  have e : min (pOf ε : ℝ) (qOf ε : ℝ) = (S7.q0 ε : ℝ) := by unfold S7.q0; push_cast; rfl
  rw [e] at h2
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmax0 : 0 ≤ max (2 * ((2 * r + k + 1 : ℕ) : ℝ) * (S7.q0 ε : ℝ)) (2 * (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) :=
    le_max_of_le_left (by positivity)
  refine ⟨?_, ?_, h2⟩
  · by_contra hq
    have hq0 : S7.q0 ε = 0 := by omega
    rw [hq0] at h2
    simp at h2
    have : (0 : ℝ) ≤ max 0 (2 * (r : ℝ) * (2 * (r : ℝ) + (k : ℝ) + 1) ^ 2) := le_max_left _ _
    linarith
  · have : 0 ≤ 3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2 := by positivity
    have := le_max_left (3 * ((2 * r + k + 1 : ℕ) : ℝ) / 2) (1 + ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorMembership

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem list_prod_mem_of_forall {S : Submodule ℂ M} :
    ∀ (l : List (Module.End ℂ M)), (∀ f ∈ l, ∀ x ∈ S, f x ∈ S) → ∀ x ∈ S, l.prod x ∈ S
  | [], _, x, hx => by simpa using hx
  | f :: l, h, x, hx => by
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f List.mem_cons_self _
      (list_prod_mem_of_forall l (fun g hg => h g (List.mem_cons_of_mem _ hg)) x hx)

theorem capEntry_mem {n : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (t : ℂ) (a b : Fin n) :
    ∀ x ∈ S, Capelli.capEntry E t a b x ∈ S := by
  intro x hx
  unfold Capelli.capEntry
  rw [LinearMap.add_apply]
  refine S.add_mem (hS a b x hx) ?_
  split_ifs
  · simpa using S.smul_mem t hx
  · simp

theorem cminor_mem {n p : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (R C : Fin p → Fin n) (t : ℂ) :
    ∀ x ∈ S, Capelli.cminor E R C t x ∈ S := by
  intro x hx
  unfold Capelli.cminor
  rw [LinearMap.sum_apply]
  refine S.sum_mem fun σ _ => ?_
  rw [LinearMap.smul_apply]
  refine S.smul_of_tower_mem _ ?_
  refine list_prod_mem_of_forall _ ?_ x hx
  intro f hf
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact capEntry_mem hS _ _ _

end CapelliMinorMembership

open CapelliMinorMembership

theorem eig : EigStatement := by
  intro M _ _ m E S ω y β v hE hS hC hv
  have h0 : Capelli.capelliC E (ω : ℂ) v = 0 := hC v hv
  have eV : Capelli.eeV E = LemK.eeV E := by
    ext f d; simp [Capelli.eeV, LemK.eeV, LemK.prj]
  have eVd : Capelli.eeVd E = LemK.eeVd E := by
    ext f d; simp [Capelli.eeVd, LemK.eeVd, LemK.prj]
  constructor
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnPlus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eV,
        Capelli.capelliAPlus M m E y (ω : ℂ) v hE h0]
      simp
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnMinus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eVd,
        Capelli.capelliAMinus M m E β (ω : ℂ) v hE h0]
      simp

end ReciprocityTheory.ChartRestriction.DS.Lap
end
