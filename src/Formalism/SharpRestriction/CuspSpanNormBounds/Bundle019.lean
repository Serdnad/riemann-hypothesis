module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle018
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrameFactorGe
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle002
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle010
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.OnePlaceExpansion

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BesselShellMomentBounds

section OnePl

variable (D : D7)

variable {D}

end OnePl

section ThmB

variable {D : D7}

end ThmB

section Frames


open Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.OnePlaceEstimates in
theorem frame_bound_of_bessel_torus (D : D7) (Cgf Cf : ℝ) (hCf : 2 ≤ Cf) (hOB : OneBesselTor D Cgf) :
    Formalism.MainNotions.OnePlaceEstimates.FrameBesselBound D Cgf Cf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  obtain ⟨f₁, C, hC, hf₁, hJ, hO⟩ := hOB L f κ₀ κ τ hκ₀ hκ hτ hc hκN hκNt hε hgap hf
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hCpos : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have e1 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z = τ ^ 2 * Tz D.R.k D.R.rS L.z := Tz_smul _ _
  have e2 : Tz D.R.k D.R.rS (trDat L κ τ hκ hτ).z' = τ ^ 2 * Tz D.R.k D.R.rS L.z' := Tz_smul _ _
  refine ⟨trDat L κ τ hκ hτ, f₁, rfl, rfl, rfl, rfl, ?_, ?_, ?_, e1, e2, hf₁, ?_⟩
  · show (κ : ℂ) * L.c = _
    rw [hc]; unfold cOfDpsi; push_cast; ring
  · show 0 < L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ)
    exact ENNReal.mul_pos hκN.ne' (ENNReal.ofReal_pos.mpr (deltaN_pos hκ hτ)).ne'
  · show L.κN * ENNReal.ofReal (deltaN D.R.k D.R.rS κ τ) ≠ ⊤
    exact ENNReal.mul_ne_top hκNt ENNReal.ofReal_ne_top
  intro μsec hsec
  refine ⟨secTr τ μsec, isSection_tr hτ hsec, jacBig D.R.rS κ τ * wBig D.R.k D.R.rS κ τ * ‖C‖ ^ 2,
    mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2), ?_, ?_⟩
  · refine jNorm2_tr hκ hτ L (trDat L κ τ hκ hτ) e1 e2 f f₁ μsec (secTr τ μsec) C hk2 fun p hp hζ => ?_
    rw [secTr_sBig hτ]
    have hb : bigCell D.R.k D.R.rS (sBig D.R.rS κ τ p).1 (μsec p.2) =
        cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)) := by
      rw [bigCell_cj hκ hτ]; rfl
    rw [hb]
    show @hsNormSq L.Wp L.Wq _ _ _ _ _
      ((trDat L κ τ hκ hτ).J f₁ (cj D.R.k D.R.rS κ τ (bigCell D.R.k D.R.rS p.1 (μsec p.2)))) = _
    rw [J_trD hκ hτ L, hJ p.1 (μsec p.2) hp (hsec.2 p.2 hζ).1, Formalism.MainNotions.FrameBoundFromBesselTorus.hsNormSq_smul]
  · intro γ hG
    refine ⟨ptTr κ τ hκ hτ γ, rfl, ?_, ?_⟩
    · rw [e1, e2, GPoint_ptTr]
    · rw [e1, e2, orbSq_trDat hκ hτ L f f₁ γ C fun g μR ν h1 h2 h3 h4 => hO γ g μR ν hG h1 h2 h3 h4]
      have hα := alphaPt_pos hκ hτ γ
      have hw := ptWeight_ptTr hk1 hκ hτ (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ
      have hcard := card_rootPat_le γ
      refine frames_ineqs (orbSq L f γ) (by positivity)
        (mul_pos (mul_pos (jacBig_pos hκ hτ) (wBig_pos hκ hτ)) (pow_pos hCpos 2)).le (inv_pos.mpr (by positivity))
        (ratio_le_frameFactor hκ hτ hCf hcard) (by rw [inv_inv]; exact ratio_inv_le_frameFactor hκ hτ hCf hcard) ?_
      have hP : 0 < κ ^ (2 * (rootPat γ).card) := pow_pos hκ _
      have hpw : ptWeight D.R.k D.R.rS (τ ^ 2 * Tz D.R.k D.R.rS L.z) (τ ^ 2 * Tz D.R.k D.R.rS L.z')
          (ptTr κ τ hκ hτ γ) = Wbig D.R.k D.R.rS κ τ * alphaPt κ τ γ ^ 2 *
            ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ / κ ^ (2 * (rootPat γ).card) := by
        rw [eq_div_iff hP.ne']; exact hw
      rw [hpw, wBig_eq_Wbig hk1, jacBig_eq, pow_add]
      field_simp

end Frames

end Formalism.MainNotions.OnePlaceExpansion
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem NE_pow (D : D7) : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) = (gS D : ℝ) ^ (D.R.m * D.R.f) := by
  unfold NE
  rw [j_finrank D, ← pow_mul]
  congr 1
  have h2 := D.R.two_le_m
  obtain ⟨k, hk⟩ := D.R.m_even
  have hm : 2 * (D.R.rS + 1) = D.R.m := by
    unfold Ranks.rS
    omega
  rw [← hm]
  ring

end Formalism.MainNotions.GramProductBounds

end
end

section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants

section Fdeg

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem integral_normSq_coef {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} :
    ∫ g, f g * star (f g) ∂μ = ((∫ g, ‖f g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  congr 1
  funext g
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem inner_self_C {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) :
    ⟪v, v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  simp

theorem fdegOf_eq {μ : Measure (Formalism.REAL.UJ ε)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (h : IsFdeg μ σ d) {v : H} (hv : v ≠ 0) : fdegOf μ σ v = d := by
  obtain ⟨hd, hF⟩ := h
  have e := (hF v v v v).2
  rw [integral_normSq_coef, inner_self_C] at e
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have e' : (∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ) = ‖v‖ ^ 4 / d := by
    have : (((∫ g, ‖coefOn σ v v g‖ ^ 2 ∂μ : ℝ)) : ℂ) = ((‖v‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [e]; push_cast; ring_nf
    exact_mod_cast this
  unfold fdegOf
  rw [e']
  field_simp

end Fdeg

section SchurH

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end SchurH

section P90P

open Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem ds_one (hσ : IsDSHpk k r ε lam σ) : σ 1 = 1 := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h := hDS.2.2.1.1.1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  simpa [Matrix.nonsing_inv_mul _ hu] using h

theorem ds_inv_adj (hσ : IsDSHpk k r ε lam σ) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (y z : H) : ⟪σ a⁻¹ y, z⟫_ℂ = ⟪y, σ a z⟫_ℂ := by
  have h1 := Formalism.MainNotions.LeviCoordinates.discrete_series_inner hσ ha (σ a⁻¹ y) z
  have h2 : σ a (σ a⁻¹ y) = y := by
    have e : σ (a * a⁻¹) = (σ a).comp (σ a⁻¹) := Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha (uh_inv ha)
    rw [Matrix.mul_nonsing_inv _ (isUnit_of_uh ha), ds_one hσ] at e
    have := congrArg (fun T : H →L[ℂ] H => T y) e
    simpa using this.symm
  rw [h2] at h1
  exact h1.symm

end P90P

section Named

open Formalism.QuantumDeterminants.WeylGroupFacts

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end Named

end Formalism.MainNotions.DiscreteSeriesInnerProducts
end
end
