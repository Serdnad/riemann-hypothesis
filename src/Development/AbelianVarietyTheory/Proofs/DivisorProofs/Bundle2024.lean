module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle056
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle104
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle081
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle385
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LamSpread


open Classical in
def sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) : ℕ := ∑ i : Fin (Dw.mult b), a (b, i)

theorem le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (b : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult b) : a (b, i) ≤ sumA Dw a b :=
  Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => a (b, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨i, hi⟩ : Fin (Dw.mult b)))

theorem spread_le_sumA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hr : 0 < r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (k : U.Comp) (τ : (U.X k).Ψ) :
    (U.X k).spread (laU U a n k) τ ≤ (sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1)) + n := by
  have hsurj : Function.Surjective (relab (E := E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  obtain ⟨hp0, hΨ⟩ := hU.2.1 k
  have hrr := hU.1
  obtain ⟨ρ, hρ⟩ := hsurj τ.1
  have hρΨ : ρ (H.rt : E) = H.rt0 := by
    by_contra hn
    have h3 : relab c σ (conjEmb ρ) (H.rt : E) = H.rt0 := by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext (GlobalTheory.AllWt.conj_mem hn))).trans hσ0
    rw [GlobalTheory.AllWt.relab_conj, hρ] at h3
    exact GlobalTheory.AllWt.conj_not_mem ⟨τ.1, (hΨ _).1 τ.2⟩ h3
  have e1 : Function.invFun (relab c σ) τ.1 = ρ := by
    rw [← hρ]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) ρ
  have e2 : Function.invFun (relab c σ) (conjEmb τ.1) = conjEmb ρ := by
    rw [← hρ, ← GlobalTheory.AllWt.relab_conj]; exact Function.leftInverse_invFun (GlobalTheory.AllWt.relab_injective σ) _
  have m1 : Dw.mult ρ = Dw.p := by rw [Datum.mult, if_pos hρΨ]
  have m2 : Dw.mult (conjEmb ρ) = Dw.q := by rw [Datum.mult, if_neg (GlobalTheory.AllWt.conj_not_mem ⟨ρ, hρΨ⟩)]
  rw [e1, e2]
  have hn : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ n := by
    have : n / 2 + n / 2 ≤ n := by omega
    exact_mod_cast this
  have key : ∀ i : Fin r, -((sumA Dw a (conjEmb ρ) : ℤ) + ((n / 2 : ℕ) : ℤ)) ≤ laU U a n k τ i ∧
      laU U a n k τ i ≤ (sumA Dw a ρ : ℤ) + ((n / 2 : ℕ) : ℤ) := by
    intro i
    have hi' := i.isLt
    unfold laU
    rw [e1, e2]
    split_ifs with hi
    · have := le_sumA Dw a ρ ((i : ℕ) - (U.X k).p0) (by rw [m1]; omega)
      constructor <;> omega
    · have := le_sumA Dw a (conjEmb ρ) ((U.X k).p0 - 1 - (i : ℕ)) (by rw [m2]; omega)
      constructor <;> omega
  refine (GlobalTheory.WtSizes.spread_le hr _ ((sumA Dw a ρ : ℝ) + ((n / 2 : ℕ) : ℝ))
    ((sumA Dw a (conjEmb ρ) : ℝ) + ((n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_spread_laU_le : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : (U σ).Comp), (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
  intro D j H Dw l Xo c U dict hL σ hσ a n k
  have hU := hL.unf σ hσ
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hsurj : Function.Surjective (relab (E := D.host.E) c σ) :=
    Finite.injective_iff_surjective.1 (GlobalTheory.AllWt.relab_injective σ)
  have hgb : Function.Bijective (Function.invFun (relab c σ)) :=
    Finite.injective_iff_bijective.1 (Function.LeftInverse.injective (Function.rightInverse_invFun hsurj))
  refine (Finset.sum_le_sum fun τ _ => spread_le_sumA (U σ) hσ hU hr a n k τ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (U σ).X k),
    nsmul_eq_mul]
  have h1 : ∑ τ : ((U σ).X k).Ψ, ((sumA Dw a (Function.invFun (relab c σ) τ.1) : ℝ) +
      sumA Dw a (Function.invFun (relab c σ) (conjEmb τ.1))) ≤ absA Dw a := by
    have := GlobalTheory.WtSizes.sum_cm_le ((U σ).X k) (fun b => sumA Dw a (Function.invFun (relab c σ) b))
    rw [hgb.sum_comp (fun b => sumA Dw a b)] at this
    show _ ≤ ((∑ b, sumA Dw a b : ℕ) : ℝ)
    exact_mod_cast this
  have h2 : (fdeg D.host.E : ℝ) * n ≤ ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) := by
    have : fdeg D.host.E * n ≤ fdeg D.host.E * D.R.r * n :=
      Nat.mul_le_mul_right n (Nat.le_mul_of_pos_right _ hr)
    exact_mod_cast this
  linarith

end GlobalTheory.LamSpread
end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LamSize

theorem one_le_fdeg_of_cm (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ fdeg E := by
  have h : Module.finrank ℚ E = 2 * fdeg E := by rw [fdeg, IsTotallyComplex.finrank E]; omega
  have := Module.finrank_pos (R := ℚ) (M := E)
  omega

theorem one_le_dE_field (E : Type) [Field E] [NumberField E] : 1 ≤ dE E := by
  unfold dE
  have h := Int.one_le_abs (NumberField.discr_ne_zero E)
  rw [← Int.cast_abs]
  exact_mod_cast h

theorem neg_log_epStar_le (f M d w : ℝ) (hf : 1 ≤ f) (hM : 1 ≤ M) (hd : 1 ≤ d) (hw : 1 ≤ w) :
    0 < epStar (2 * M * Real.sqrt d) f w 1 ∧ epStar (2 * M * Real.sqrt d) f w 1 ≤ 1 ∧
      -Real.log (epStar (2 * M * Real.sqrt d) f w 1) ≤
        Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hpi := Real.pi_gt_three
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hfw : 1 ≤ f * w := one_le_mul_of_one_le_of_one_le hf hw
  set A := 2 * M * Real.sqrt d * f * w with hA
  have hA1 : 1 ≤ A := by
    have h1 : 1 ≤ M * Real.sqrt d := one_le_mul_of_one_le_of_one_le hM hsd
    have : A = 2 * (M * Real.sqrt d) * (f * w) := by rw [hA]; ring
    rw [this]; nlinarith
  have hA0 : 0 < A := by linarith
  have hB : 0 < 2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2 := by positivity
  have hlow : 1 / A ≤ epStar (2 * M * Real.sqrt d) f w 1 := by
    unfold epStar
    refine le_min ((div_le_one hA0).2 hA1) ?_
    rw [div_le_div_iff₀ hA0 hB]
    have hMd : 0 < 2 * M * Real.sqrt d := by positivity
    have key : (f * w + 2) * Real.log 2 ≤ Real.pi * (f * w) := by nlinarith
    have : 1 * (2 * M * Real.sqrt d * (f * w + 2) * 1 * Real.log 2) = (2 * M * Real.sqrt d) * ((f * w + 2) * Real.log 2) := by ring
    rw [this]
    have : Real.pi * A = (2 * M * Real.sqrt d) * (Real.pi * (f * w)) := by rw [hA]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left key hMd.le
  have he0 : 0 < epStar (2 * M * Real.sqrt d) f w 1 := lt_of_lt_of_le (by positivity) hlow
  refine ⟨he0, min_le_left _ _, ?_⟩
  have h1 : Real.log (1 / A) ≤ Real.log (epStar (2 * M * Real.sqrt d) f w 1) :=
    Real.log_le_log (by positivity) hlow
  rw [one_div, Real.log_inv] at h1
  have hlA : Real.log A = Real.log 2 + Real.log M + 1 / 2 * Real.log d + Real.log f + Real.log w := by
    rw [hA, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt (by linarith)]
    ring
  linarith

theorem log_radius_le (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ)
    (hr : 1 ≤ r) (hd : 1 ≤ d) (hM : 1 ≤ M) (hL : 1 ≤ L) (hw : 1 ≤ w)
    (hfr : Real.log (fdeg E * r) ≤ L) (hlM : Real.log M ≤ 30 * L) (hdE : Real.log (dE E) ≤ 4 * fdeg E * L)
    (hld : Real.log d ≤ 4 * L) (hlw : Real.log w ≤ 2 * L) :
    1 ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
      (3 * frameRadius w r / 5)) ≤ (4 * fdeg E + 32) * L := by
  have hf1 := one_le_fdeg_of_cm E
  have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast hf1
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hdE1 := one_le_dE_field E
  obtain ⟨he0, he1, hne⟩ := neg_log_epStar_le (fdeg E) M d w hf' hM' hd' hw
  have hepsdef : epsLev E d M w = epStar (2 * M * Real.sqrt d) (fdeg E) w 1 := rfl
  rw [← hepsdef] at he0 he1 hne
  obtain ⟨hX0, hX⟩ := GlobalTheory.room_log_radius (fdeg E) r (dE E) (epsLev E d M w) w hf1 hr hdE1 he0 hw
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E) (Real.sqrt (epsLev E d M w) / Real.sqrt (fdeg E)))
    (3 * frameRadius w r / 5) with hXdef
  clear_value X
  have hle : Real.log (epsLev E d M w) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (fdeg E : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have a1 : 0 ≤ Real.log (dE E) := Real.log_nonneg hdE1
  have a2 : 0 ≤ Real.log w := Real.log_nonneg hw
  have a3 : 0 ≤ Real.log (fdeg E : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((fdeg E : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have a7 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hM'
  have a8 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd'
  have hmul : Real.log ((fdeg E : ℝ) * r) = Real.log (fdeg E : ℝ) + Real.log r :=
    Real.log_mul (by positivity) (by positivity)
  have hc : Real.log (1600 / 3 : ℝ) ≤ 7 := by
    have h1 : Real.log (1600 / 3 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1
    linarith
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hfdL : 0 ≤ (fdeg E : ℝ) * L := by positivity
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  refine ⟨?_, ?_⟩
  · by_contra hc'
    have := Real.log_neg hX0 (not_le.1 hc')
    linarith
  · rw [hX]
    have : (4 * (fdeg E : ℝ) + 32) * L = 4 * ((fdeg E : ℝ) * L) + 32 * L := by ring
    rw [this]
    linarith

theorem lamSup_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  intro E _ _ _ r q d M Om s t L hr hd hM hL hs ht hfr hlM hdE hld hlw
  have hw : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨hX1, hXle⟩ := log_radius_le E r d M (s + t + 1) L hr hd hM hL hw hfr hlM hdE hld hlw
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hcm : cmLen E r q d M (s + t + 1) = (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5)) ^ (2 * q + 1) := rfl
  unfold lamSup
  rw [hcm]
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu (fdeg E) r (dE E)
      (Real.sqrt (epsLev E d M (s + t + 1)) / Real.sqrt (fdeg E))) (3 * frameRadius (s + t + 1) r / 5) with hXdef
  clear_value X
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  unfold Formalism.L2.LamCM.pDeg
  push_cast
  set K : ℝ := 2 * (q : ℝ) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set Y := K * Real.log X with hY
  have hY0 : 0 ≤ Y := mul_nonneg hK0 hlX
  have hYle : Y ≤ K * ((4 * fdeg E + 32) * L) := mul_le_mul_of_nonneg_left hXle hK0
  have hlr : Real.log r ≤ L := by
    have hf' : (1 : ℝ) ≤ fdeg E := by exact_mod_cast one_le_fdeg_of_cm E
    have : Real.log (r : ℝ) ≤ Real.log ((fdeg E : ℝ) * r) :=
      Real.log_le_log (by positivity) (le_mul_of_one_le_left (by positivity) hf')
    linarith
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have hst : 0 ≤ s + t := by linarith
  have c1 : s * (Real.log r + Y) ≤ (s + t) * (L + Y) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hst
  have c2 : (3 / 2 * Y) * (s + t) ≤ (K * (6 * fdeg E + 48) * L) * (s + t) := by
    refine mul_le_mul_of_nonneg_right ?_ hst
    have : K * (6 * (fdeg E : ℝ) + 48) * L = 3 / 2 * (K * ((4 * fdeg E + 32) * L)) := by ring
    rw [this]; linarith
  nlinarith

end GlobalTheory.LamSize
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem latEmb_model_of_eq (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ) (hj : InR D j)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD)
    (hp : Dw.p = (D.R.sigW j).1) (hq : Dw.q = (D.R.sigW j).2) (V : HSp D) (hV : V = D.sp.W j) (r : ℕ)
    (hr : V.rank = r) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hL : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (hI : LatIsom V Dw.EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀)) :
    Function.Injective ι₀ ∧ Submodule.span D.host.E (Set.range ι₀) = ⊤ ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
        herm (GlobalTheory.RecDict.gmW V hr) (ι₀ x) (ι₀ y)) := by
  subst hV
  subst hr
  have hL' : LatEmb (D.sp.W j) ι₀ := hL
  obtain ⟨ε, hε⟩ : LatIsom (D.sp.W j) Dw.EF ι₀ := hI
  have hsp : Submodule.span D.host.E (Set.range ι₀) = ⊤ := by
    rw [← LinearMap.coe_range, hL'.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D (D.sp.W j) 1).2.1
  let f := ((D.sp.W j).frame.equivFun.symm.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hsp' : Submodule.span D.host.E (Set.range (f ∘ₗ ι₀)) = ⊤ := by
    have : Set.range (f ∘ₗ ι₀) = (D.sp.W j).frame.equivFun.symm.toLinearMap '' Set.range ι₀ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  have h1 : ε = 1 := GlobalTheory.Member.sign_eq_one D H Dw j hj hrt hrt0 hp hq (f ∘ₗ ι₀) ε
    ((D.sp.W j).frame.equivFun.symm.injective.comp hL'.1) hsp' hε
  subst h1
  refine ⟨hL'.1, hsp, (GlobalTheory.Member.isom_iff_model Dw (D.sp.W j) rfl ι₀).1 fun x y => ?_⟩
  rw [hε x y, Units.val_one, Int.cast_one, _root_.one_mul]



theorem model_space_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∀ τ : D.host.E →+* ℂ, τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 → (τ ((T.U j σ).X k).ξ0).im < 0) ∧ ∃ φD : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), Function.Injective φD ∧ Submodule.span D.host.E (Set.range φD) = ⊤ ∧ ∀ x y, (((T.Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm (φD x) (φD y)) := by
  intro D T h j hj σ hσ k
  obtain ⟨hr, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨-, hrt, hrt0, -⟩ := h.pins.1
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨hr', -, -, -, -, -, -, hL, hI, -⟩ := h.adPin j hj σ hσ
  refine ⟨fun τ hτ => ?_, T.iota j, ?_⟩
  · rw [(hW k).2]
    exact GlobalTheory.Member.hostCMType_neg_constant_im_neg D τ (by rw [← hrt0, ← hrt, hτ])
  · rw [(hW k).1, (hW k).2]
    exact latEmb_model_of_eq D T.Q.H (T.Q.Dw j) j hj hrt hrt0 hp hq (T.V j σ) (h.spaceW j hj σ hσ) D.R.r hr
      (T.iota j) hL hI

end GlobalTheory.GeoLevel
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.RuleIntegral

theorem vLa_int_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K}
    (hr : (r : K) ≠ 0) : 0 ≤ vLa w (r : K) := by
  unfold vLa
  have h1 := w.valuation_le_one (K := K) r
  have h2 : (w.valuation K) (r : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

theorem nonneg_of_four {x : EReal} (hx : x ≠ ⊥) (h : 0 ≤ x + x + x + x) : 0 ≤ x := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe r =>
    have : (0 : EReal) ≤ ((r + r + r + r : ℝ) : EReal) := by simpa [EReal.coe_add] using h
    have h' : (0 : ℝ) ≤ r + r + r + r := EReal.coe_nonneg.1 this
    exact EReal.coe_nonneg.2 (by linarith)

theorem eq_zero_or_top_of_double {x : EReal} (hx : x ≠ ⊥) (h : x = x + x) : x = 0 ∨ x = ⊤ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact Or.inr rfl
  | coe r =>
    left
    have h' : r = r + r := by exact_mod_cast h
    have : r = 0 := by linarith
    simp [this]

theorem exists_common_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (a : ι → K) :
    ∃ s : 𝓞 K, (s : K) ≠ 0 ∧ ∀ i, ∃ r : 𝓞 K, (r : K) = (s : K) * a i := by
  classical
  have h := fun i => IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) (a i)
  choose d hd using h
  refine ⟨∏ i, (d i : 𝓞 K), ?_, fun i => ?_⟩
  · have hm : (∏ i, (d i : 𝓞 K)) ∈ nonZeroDivisors (𝓞 K) :=
      Submonoid.prod_mem _ fun i _ => (d i).2
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
  · obtain ⟨r, hr⟩ := hd i
    refine ⟨(∏ j ∈ Finset.univ.erase i, (d j : 𝓞 K)) * r, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (d j : 𝓞 K)) (Finset.mem_univ i)]
    have e1 : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
    rw [e1, e1, map_mul, map_mul, hr, Algebra.smul_def]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_idem_zero {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : v ∈ valSet Xo c (algCls Xo c) w) : ∃ Z, v (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨y, rfl⟩ := hv
  have h1 : vAtV y 1 = 0 := by
    rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
    show nval T.V e (evI y 1) = 0
    have h1 : evI y 1 = 1 := by
      letI := io.toAlgebra
      exact evalAt_one _ _ y.1 y.2.1
    rw [h1, nval_of_ne one_ne_zero]
    simp [vV]
  by_contra hne
  push_neg at hne
  have htop : ∀ Z, vAtV y (GlobalTheory.FlatLine.idem Z) = ⊤ := fun Z => by
    have hd := vAtV_mul y (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)
    rw [GlobalTheory.FlatLine.idem_mul_idem] at hd
    exact (eq_zero_or_top_of_double (vAtV_ne_bot y _) hd).resolve_left (hne Z)
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  classical
  have hs : ∀ s : Finset (Comp Xo c), vAtV y (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z) = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using vAtV_zero y
    | insert Z s hZ ih =>
      rw [Finset.sum_insert hZ]
      have := vAtV_add y (GlobalTheory.FlatLine.idem Z) (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z)
      rw [htop Z, ih, min_self] at this
      exact top_le_iff.1 this
  have h2 := hs Finset.univ
  rw [GlobalTheory.FlatLine.sum_idem] at h2
  rw [h2] at h1
  exact EReal.top_ne_zero h1

theorem exists_smul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  intro E _ _ _ H Dw l Xo c K ρ a ha hρ hK
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  obtain ⟨s, hs0, hsa⟩ := exists_common_denom a
  refine ⟨(s : c.F), hs0, fun w v hv => ?_⟩
  have hKv := hK w v hv
  obtain ⟨Z, hZ⟩ := exists_idem_zero hv
  obtain ⟨y, rfl⟩ := hv
  obtain ⟨r, hr⟩ := hsa Z
  have hb : (((s ^ 3 * r : 𝓞 c.F)) : c.F) = (s : c.F) ^ 4 * a Z := by
    have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F s * a Z := hr
    show algebraMap (𝓞 c.F) c.F (s ^ 3 * r) = (algebraMap (𝓞 c.F) c.F s) ^ 4 * a Z
    rw [map_mul, map_pow, hr']; ring
  have hb0 : (((s ^ 3 * r : 𝓞 c.F)) : c.F) ≠ 0 := by
    rw [hb]; exact mul_ne_zero (pow_ne_zero _ hs0) (ha Z)
  have hid : GlobalTheory.FlatLine.idem Z * ((s : c.F) • ρ) ^ 4 =
      (((s ^ 3 * r : 𝓞 c.F)) : c.F) • (GlobalTheory.FlatLine.idem Z * K) := by
    rw [smul_pow, mul_smul_comm, hρ Z, smul_smul, hb]
  have h4 : ∀ x : Rul Xo c, x ^ 4 = x * x * x * x := fun x => by ring
  have e := congrArg (vAtV y) hid
  rw [h4, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_smul _ _ _ hb0, vAtV_mul, hZ, zero_add, zero_add] at e
  refine nonneg_of_four (vAtV_ne_bot _ _) ?_
  rw [e]
  refine add_nonneg ?_ hKv
  exact EReal.coe_nonneg.2 (by exact_mod_cast vLa_int_nonneg w hb0)

end GlobalTheory.RuleIntegral
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Good SchurAll TwoSided IsLab)

theorem _root_.GlobalTheory.T.inertValues_iff_inertLabels_carriedEigensystems : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ (i : Fin D.R.m) (p p' : A3.fam3.base3.Ix) c c', R.Carries p c → R.Carries p' c' → ((∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → _root_.Formalism.DivisionValues.conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d)) := by
  first | exact @GlobalTheory.InertValLab.inert_vals_iff_labels | exact GlobalTheory.InertValLab.inert_vals_iff_labels | (intros; apply GlobalTheory.InertValLab.inert_vals_iff_labels <;> assumption)
end
