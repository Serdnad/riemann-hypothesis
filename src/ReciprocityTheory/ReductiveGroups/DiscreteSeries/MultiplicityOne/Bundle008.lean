module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.MeasurableSpace
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInfA

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

theorem stPairs (h : UnitaryGroupStructuralFacts) : StPairs := by
  have h' := h
  unfold UnitaryGroupStructuralFacts ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at h'
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -⟩, -⟩ := h'
  intro k r Wp _ _ _ D X _ _ d hd a₁ a₂ u hu v hv
  set a := min a₁ a₂ with ha_def
  set b := AG k r + 1 with hb_def
  have hone : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have hlow : ∀ x ∈ GV k r, 1 ≤ gN x := fun x hx => hLow k r x hx
  have hb0 : 0 ≤ b := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  by_cases hab : b ≤ a
  swap
  · refine ⟨‖u‖ * ‖v‖, fun x hx => ?_⟩
    have h1 : ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := by
      calc ‖mc X u v x‖ = ‖⟪v, X.σ x u⟫_ℂ‖ := rfl
        _ ≤ ‖v‖ * ‖X.σ x u‖ := norm_inner_le_norm _ _
        _ = ‖u‖ * ‖v‖ := by rw [X.rep.2.1 x hx u]; ring
    have h2 : 1 ≤ gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by
      apply Real.one_le_rpow (hlow x hx)
      rw [← ha_def]
      linarith
    calc ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := h1
      _ = ‖u‖ * ‖v‖ * 1 := by ring
      _ ≤ ‖u‖ * ‖v‖ * gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by gcongr
  obtain ⟨C₁, hC₁⟩ := hu
  obtain ⟨C₂, hC₂⟩ := hv
  have hpos : ∀ x ∈ GV k r, 0 < gN x := fun x hx => lt_of_lt_of_le one_pos (hlow x hx)
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := hC₁ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₁)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₁ * gN (1 : Mat k r) ^ (-a₁) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X u X.w 1)]
  have hC₂0 : 0 ≤ C₂ := by
    have h1 := hC₂ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₂)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₂ * gN (1 : Mat k r) ^ (-a₂) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X v X.w 1)]
  set c := gN (Hpk k r) ^ 2 with hc_def
  have hc : 0 < c := by
    have h1 : gN (1 : Mat k r) ≤ gN (Hpk k r) * gN (Hpk k r) := by
      have := gN_mul_le (Hpk k r) (Hpk k r)
      rwa [Hpk_sq] at this
    have h2 := hlow 1 hone
    rw [hc_def]
    nlinarith
  have hmeas : Measurable (fun g : Mt k r => gN (Matrix.of g)) := by
    unfold gN
    fun_prop
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r := by
    rw [ae_iff]
    exact D.haarG.conc
  have hAB : AB k r ≤ b := AB_le_AG k r
  have hfin := hInt k r D.μG b D.haarG hAB
  have hI : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-b)) D.μG := by
    refine ⟨(hmeas.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hfin
    · exact Filter.Eventually.of_forall fun g => Real.rpow_nonneg (by unfold gN; positivity) _
  set I := ∫ g : Mt k r, gN (Matrix.of g) ^ (-b) ∂D.μG with hI_def
  refine ⟨d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))), fun x hx => ?_⟩
  have hd0 : 0 < d := hd.1
  obtain ⟨-, hEq⟩ := hd.2 (X.σ x u) X.w v X.w
  have hww : ⟪X.w, X.w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hww, mul_one] at hEq
  set F : Mt k r → ℂ := fun g => mc X (X.σ x u) X.w (Matrix.of g) * star (mc X v X.w (Matrix.of g)) with hF_def
  have hmc : mc X u v x = (d : ℂ) * ∫ g, F g ∂D.μG := by
    rw [hEq]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    change ⟪v, X.σ x u⟫_ℂ = (d : ℂ) * (⟪v, X.σ x u⟫_ℂ / (d : ℂ))
    field_simp
  set G : Mt k r → ℝ := fun g => C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) with hG_def
  have hGi : Integrable G D.μG := hI.const_mul _
  have hpt : ∀ᵐ g ∂D.μG, ‖F g‖ ≤ G g := by
    filter_upwards [hae] with g hg
    have hgx : Matrix.of g * x ∈ GV k r := GV_mul k r hg hx
    have hFg : ‖F g‖ = ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖ := by
      rw [hF_def]
      simp only [norm_mul, norm_star]
      congr 1
      show ‖⟪X.w, X.σ (Matrix.of g) (X.σ x u)⟫_ℂ‖ = ‖⟪X.w, X.σ (Matrix.of g * x) u⟫_ℂ‖
      rw [X.rep.1.2 _ hg _ hx]
      rfl
    have hA1 := hlow _ hgx
    have hB1 := hlow _ hg
    have e1 : ‖mc X u X.w (Matrix.of g * x)‖ ≤ C₁ * gN (Matrix.of g * x) ^ (-a) := by
      refine (hC₁ _ hgx).trans ?_
      gcongr
      exact min_le_left a₁ a₂
    have e2 : ‖mc X v X.w (Matrix.of g)‖ ≤ C₂ * gN (Matrix.of g) ^ (-a) := by
      refine (hC₂ _ hg).trans ?_
      gcongr
      exact min_le_right a₁ a₂
    have key := real_key hA1 hB1 (hpos x hx) hc hb0 hab (gN_le_mul hg x)
    rw [hFg, hG_def]
    calc ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖
        ≤ (C₁ * gN (Matrix.of g * x) ^ (-a)) * (C₂ * gN (Matrix.of g) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg hC₁0 (Real.rpow_nonneg (hpos _ hgx).le _))
      _ = C₁ * C₂ * (gN (Matrix.of g * x) ^ (-a) * gN (Matrix.of g) ^ (-a)) := by ring
      _ ≤ C₁ * C₂ * ((gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b)) := by
          gcongr
      _ = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) := by ring
  have hbound : ‖∫ g, F g ∂D.μG‖ ≤ ∫ g, G g ∂D.μG :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hGi hpt)
  have hGint : ∫ g, G g ∂D.μG = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I := by
    rw [hG_def, integral_const_mul]
  have hsplit : (gN x * c⁻¹) ^ (-(a - b)) = gN x ^ (-(a - b)) * (c⁻¹) ^ (-(a - b)) :=
    Real.mul_rpow (hpos x hx).le (inv_nonneg.mpr hc.le)
  have hexp : -(min a₁ a₂ - AG k r - 1) = -(a - b) := by
    rw [ha_def, hb_def]; ring
  rw [hmc, norm_mul, hexp]
  have hdn : ‖(d : ℂ)‖ = d := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
  rw [hdn]
  calc d * ‖∫ g, F g ∂D.μG‖ ≤ d * (C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I) := by
        rw [← hGint]; exact mul_le_mul_of_nonneg_left hbound hd0.le
    _ = d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))) * gN x ^ (-(a - b)) := by
        rw [hsplit]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem isHaarOn_smul_of {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) : IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, hμ.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM (k := k) (r := r) a) :=
      continuous_const.matrix_mul continuous_id
    rw [Measure.map_smul c hcont.measurable.aemeasurable, hμ.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a) := continuous_id.matrix_mul continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, hμ.right a ha]
  · intro K hK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hct) (hμ.finite_compact K hK)
  · intro h0
    apply hμ.ne_zero
    ext s _
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν s) h0
    simp only [smul_apply, smul_eq_mul, FunLike.coe_zero, Pi.zero_apply, mul_eq_zero] at h1
    simpa [hc0] using h1

theorem stDiagExists (h : UnitaryGroupStructuralFacts) : StDiagExists := by
  unfold StDiagExists
  intro k r Wp _ _ _ z π hk hz hT hrep hun hcont hirr
  unfold UnitaryGroupStructuralFacts at h
  obtain ⟨hB2, hBS, -⟩ := h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -⟩ := hB2
  obtain ⟨D, hDz, hDz', hDπ, hDπ', -⟩ :=
    hBS k r Wp Wp z z π π hk hz hz hT hT hrep hrep hun hun hcont hcont
  have hcomp : IsCompact (UWset k r z) := hCW k r z hz hT
  have hW : IsHaarOn (UWset k r z) D.μW := by
    have h0 := D.haarW
    rw [hDz] at h0
    exact h0
  have hm0 : D.μW Set.univ ≠ 0 := by
    intro h0
    exact hW.ne_zero (Measure.measure_univ_eq_zero.mp h0)
  have hmt : D.μW Set.univ ≠ ∞ := by
    have h1 : D.μW Set.univ ≤ D.μW (UWset k r z) + D.μW (UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    rw [hW.conc, add_zero] at h1
    exact ne_top_of_le_ne_top (hW.finite_compact _ hcomp).ne h1
  have hc0 : (D.μW Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmt
  have hct : (D.μW Set.univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm0
  have hH : IsHaarOn (UWset k r D.z) ((D.μW Set.univ)⁻¹ • D.μW) :=
    isHaarOn_smul_of D.haarW hc0 hct
  have hH' : IsHaarOn (UWset k r D.z') ((D.μW Set.univ)⁻¹ • D.μW) := by
    rw [hDz', ← hDz]
    exact hH
  let D' : RealPlaceData k r Wp Wp :=
    { D with
      μW := (D.μW Set.univ)⁻¹ • D.μW
      μW' := (D.μW Set.univ)⁻¹ • D.μW
      haarW := hH
      haarW' := hH' }
  refine ⟨D', hDz, hDπ, ?_⟩
  refine ⟨hDz'.trans hDz.symm, hDπ'.trans hDπ.symm, rfl, ?_, ?_⟩
  · show ((D.μW Set.univ)⁻¹ • D.μW) Set.univ = 1
    rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm0 hmt]
  · show Formalism.MainNotions.S.IsIrredOn (UWset k r D.z) D.π
    rw [hDz, hDπ]
    exact hirr

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stBetaInf (h : UnitaryGroupStructuralFacts) : StBetaInf := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRB, hRA, -, hAe, hDJ⟩ := h
  have hDJ' : DilJacAll := by first | exact hDJ | exact hDJ.1
  intro k r Wp Wq _ _ _ _ _ _ D A hXi hA F F' hF hF' hP
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  exact BetaInfA.betaInf_eq_of D A hAe (hRB k r Wp Wq D Ξ A hA hCB hXI)
    (hRA k r Wp Wq D Ξ A hA hCB hXI (hDJ' k r Wp Wq D)) (BetaInfA.inCC_five_four hF)
    (BetaInfA.inCC_five_four hF') hP

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
