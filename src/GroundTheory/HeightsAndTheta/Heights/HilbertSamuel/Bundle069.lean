module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle060
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedProductNonneg

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem le_of_mem_support_ratDiv {V : Ideal (MRingOver F ι)} {f g : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (hW : W ∈ (ratDiv V f g).support) : V ≤ W := by
  have key : ∀ s : MRingOver F ι, ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → V ≤ W := by
    intro s hs
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hs
    rw [Finsupp.ofSupportFinite_coe] at hs
    split_ifs at hs with h
    · exact le_sup_left.trans h.1.1.2
    · exact absurd rfl hs
  rw [Finsupp.mem_support_iff, ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hf : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g fun h => hW ?_
    rw [hf, h]
    simp
  · exact key f hf

end GeneratedProductNonneg

theorem GeneratedProductNonneg.proof (hR : GeneratedRestrict.Statement)
    (hE : GeneratedEffectiveSection.Statement) : GeneratedProductNonneg.Statement := by
  classical
  intro F _ K _ _ ι _ _ I V m β hI hV hgen
  induction m generalizing V with
  | zero =>
    choose i hi using hV.1.2.2
    rw [hI.1 V β i hV hi]
    exact Int.natCast_nonneg _
  | succ m ih =>
    obtain ⟨f, g, hs, heff⟩ := hE F K ι V (β (Fin.last m)) hV.1 (hgen (Fin.last m))
    have e := hI.2 V m (Fin.init β) (β (Fin.last m)) f g hV hs
    rw [Fin.snoc_init_self] at e
    rw [e, cycEval]
    refine Finsupp.sum_nonneg fun W hW => mul_nonneg (heff W) ?_
    obtain ⟨α, γ, hf, hg, hfV, hgV, -⟩ := hs
    have hWm : IsProjVarF W m := KleimanNefF.isProjVarF_of_mem_support hV
      ((NumbersDVR.VocabMultiHomog.proof F K ι f α).1 hf) ((NumbersDVR.VocabMultiHomog.proof F K ι g γ).1 hg)
      hfV hgV hW
    have hle : V ≤ W := GeneratedProductNonneg.le_of_mem_support_ratDiv hW
    exact ih W (Fin.init β) hWm fun j => hR F K ι V W _ hle (hgen _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem ReductionToProjectiveBlock.proof (hRP : ReductionToProjective.Statement)
    (hMC : BlockMetricChange.Statement) (hIm : BlockImageDatum.Statement) (hTop : BlockImageTop.Statement)
    (hGD : BlockImageGenDeg.Statement) : ReductionToProjectiveBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  obtain ⟨d₀, r, M, N, d', hy, hk, hB, hmet, hchi⟩ := hIm D K ι Ω d

  have h1 := hMC D K ι Ω I d d₀ hI hy hk

  have h2 := (hRP D Ω (Fin r) I d' hI).2

  have hdeg : d₀.A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ := hk ▸ d₀.deg
  have htop : I K ι (mCoordIdeal d₀.y) (D + 1) (fun _ => d₀.A) = top I d'.x d'.m D := by
    rw [hy]
    exact hTop D K ι Ω (Fin r) I d.y d.k₀ d₀.A M N d'.x d'.m hI d.arith d.birat d'.arith hB hdeg
      d₀.semipos.1 d'.smooth hmet

  have hg : genDeg (ι := GlobalTheory (Fin r)) (coordIdeal ℤ d'.x) D 1 = genDeg (mCoordIdeal d.y) D d.A.a := by
    rw [d.deg]
    exact hGD D K ι Ω (Fin r) d.y d.k₀ M N d'.x d.arith d.birat hB
  rw [hg] at h2
  refine (h2.sub h1).congr_left fun n => ?_
  simp only [hsDefect, hchi n, htop]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ArithmeticVolumeDimensionOne.proof (hG6 : ArithmeticVolumeBigDimensionOne.Statement) : ArithmeticVolumeDimensionOne.Statement := by
  intro K _ ι _ Ω _ _ y M P0 II hII har hb hM hpos
  set T := II K ι (mCoordIdeal y) 1 (fun _ => M)
  set g := geomDeg (mCoordIdeal y) M 0
  have hden : 0 < 2 * (|g| + 1) := by positivity
  set η := T / (2 * (|g| + 1))
  have hη0 : 0 < η := div_pos hpos hden
  have he : η * (2 * (|g| + 1)) = T := div_mul_cancel₀ T hden.ne'
  have hηlt : η * g < T := by
    have h1 : η * g ≤ η * |g| := mul_le_mul_of_nonneg_left (le_abs_self g) hη0.le
    nlinarith
  have hshift := ConstantShift.proof K ι (II K ι) (mCoordIdeal y) 0 M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) := by
    have e : II K ι (mCoordIdeal y) 1 (fun _ => HermLine.constShift M η) = T - ((0 : ℕ) + 1 : ℝ) * η * g :=
      hshift
    rw [e]
    push_cast
    linarith
  have hvol := hG6 K ι Ω y (HermLine.constShift M η) P0 II hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g' h z hg hh hdeg heq hz
    have hle := hsmall dg dh g' h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSupBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartPiece (c : ∀ k, ι k) : Set ((Σ k, ι k) → ℂ) :=
  Metric.closedBall 0 1 ∩ {w | ∀ k, w ⟨k, c k⟩ = 1}

theorem isCompact_chartPiece (c : ∀ k, ι k) : IsCompact (chartPiece c) := by
  refine (isCompact_closedBall _ _).inter_right ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_eq (continuous_apply _) continuous_const

theorem exists_lower (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (c : ∀ k, ι k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hsub : chartPiece c ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun w hw k =>
    ⟨c k, by rw [hw.2 k]; exact one_ne_zero⟩
  have hcont : ContinuousOn (fun w => (A.h w)⁻¹) (chartPiece c) :=
    (hA.mono hsub).inv₀ fun w hw => (A.pos w (hsub hw)).ne'
  obtain ⟨M, hM⟩ := (isCompact_chartPiece c).exists_bound_of_continuousOn hcont
  refine ⟨|M|, abs_nonneg M, fun z hmax hz0 => ?_⟩
  have hr : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => norm_pos_iff.mpr (hz0 k)
  set s : K → ℂ := fun k => (z ⟨k, c k⟩)⁻¹ with hs
  have hs0 : ∀ k, s k ≠ 0 := fun k => inv_ne_zero (hz0 k)
  set w : (Σ k, ι k) → ℂ := fun p => s p.1 * z p with hw
  have hwS : w ∈ chartPiece c := by
    refine ⟨?_, fun k => inv_mul_cancel₀ (hz0 k)⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro p
    obtain ⟨k, i⟩ := p
    show ‖(z ⟨k, c k⟩)⁻¹ * z ⟨k, i⟩‖ ≤ 1
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (hr k), mul_one]
    exact hmax k i
  have hwpos : 0 < A.h w := A.pos w (hsub hwS)
  have h1 : 1 ≤ |M| * A.h w := by
    have := (hM w hwS).trans (le_abs_self M)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hwpos] at this
    rw [inv_le_iff_one_le_mul₀ hwpos] at this
    exact this
  have hAw : A.h w = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z := by
    rw [hw, A.smul s z hs0, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hs, norm_inv, inv_zpow]
  have hR : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hr k) _
  rw [hAw] at h1
  calc ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * 1 := (mul_one _).symm
    _ ≤ (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * (|M| * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z)) :=
        mul_le_mul_of_nonneg_left h1 hR.le
    _ = |M| * A.h z := by field_simp

end SectionSupBound


open SectionBounded SectionSupBound in
theorem SectionSupBound.proof : SectionSupBound.Statement := by
  intro K _ ι _ Ω _ y A τ e hA he
  classical
  choose M hM0 hM using fun c => SectionSupBound.exists_lower A hA c
  choose B hB0 hB using fun c hc => SectionBounded.exists_upper y A.a τ he c hc
  set S : ℝ := ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c' _ => by
    split_ifs with hc'
    · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
    · exact le_rfl
  refine ⟨Real.log (1 + S), Real.log_nonneg (by linarith), ?_⟩
  rw [Real.exp_log (by linarith)]
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM c z hcmax hz0
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) ≤ M c ^ τ * A.h z ^ τ := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 τ
  have hCge : B c hyc * M c ^ τ ≤ 1 + S := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
        · exact le_rfl) (Finset.mem_univ c)
    simp only [dif_pos hyc] at this
    linarith
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M c ^ τ * A.h z ^ τ) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M c ^ τ) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by ring
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

theorem leviForm_comp_clm {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (L : (J → ℂ) →L[ℝ] (J → ℂ))
    (hL : ∀ w, L (Complex.I • w) = Complex.I • L w) (z : J → ℂ)
    (hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ φ (L y))
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (L z)) (w : J → ℂ) :
    leviForm (φ ∘ L) z w = leviForm φ (L z) (L w) := by
  set R := (ContinuousLinearMap.compL ℝ (J → ℂ) (J → ℂ) ℝ).flip L with hR
  have hev : fderiv ℝ (φ ∘ L) =ᶠ[𝓝 z] fun y => R (fderiv ℝ φ (L y)) := by
    filter_upwards [hφ] with y hy
    rw [fderiv_comp y hy L.differentiableAt, L.fderiv]
    rfl
  have hd : HasFDerivAt (fun y => R (fderiv ℝ φ (L y))) (R.comp ((fderiv ℝ (fderiv ℝ φ) (L z)).comp L)) z :=
    R.hasFDerivAt.comp z (hφ2.hasFDerivAt.comp z L.hasFDerivAt)
  have key : ∀ v, fderiv ℝ (fderiv ℝ (φ ∘ L)) z v v = fderiv ℝ (fderiv ℝ φ) (L z) (L v) (L v) := by
    intro v
    rw [hev.fderiv_eq, hd.fderiv]
    rfl
  unfold leviForm
  rw [key, key, hL]

theorem contDiffAt_log_fs {J : Type} [Fintype J] {y : J → ℂ} (hy : y ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.log ((fsMetric (ι := J)).ρ y)) y :=
  ((ProjLine.isSmoothMetric_fs (J := J) y hy).contDiffAt (isOpen_ne.mem_nhds hy)).log
    ((fsMetric (ι := J)).pos y hy).ne'

namespace Veronese

def scaleLin (D : ℕ) : (Ix (Idx D) → ℂ) →ₗ[ℂ] (Ix (Idx D) → ℂ) where
  toFun := scale D
  map_add' z z' := by
    funext q
    simp only [scale, Pi.add_apply]
    ring
  map_smul' c z := by
    funext q
    simp only [scale, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def scaleL (D : ℕ) : (Ix (Idx D) → ℂ) →L[ℝ] (Ix (Idx D) → ℂ) :=
  (LinearMap.toContinuousLinearMap (scaleLin D)).restrictScalars ℝ

theorem scaleL_I (D : ℕ) (w : Ix (Idx D) → ℂ) : scaleL D (Complex.I • w) = Complex.I • scaleL D w :=
  (scaleLin D).map_smul Complex.I w

end Veronese

open Veronese

theorem VeroneseSemipos.proof : VeroneseSemipos.Statement := by
  intro D
  refine ⟨(isSmoothMetric_metric D).mono fun z hz h0 => ?_, fun z hz w _ => ?_⟩
  · obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  · have hz0 : z ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := hz.1 ()
      exact hi (congrFun h0 _)
    have e : (fun z => Real.log ((HermLine.ofCone (metric D)).h z)) =
        (fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) ∘ scaleL D := rfl
    have hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ (fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) (scaleL D y) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact (contDiffAt_log_fs (scale_ne_zero hy)).differentiableAt (by simp)
    have hφ2 : DifferentiableAt ℝ (fderiv ℝ fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) (scaleL D z) :=
      ((contDiffAt_log_fs (scale_ne_zero hz0)).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt
        one_ne_zero
    rw [e, leviForm_comp_clm _ _ (scaleL_I D) z hφ hφ2 w]
    exact ProjLine.leviForm_log_fs_nonneg (scale_ne_zero hz0) (scaleL D w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

theorem BlockResolutionDegree.proof (hRank : BlockSectionsRank.Statement)
    (hInt : BlockResolutionDegreeIntegral.Statement) : BlockResolutionDegree.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h₀ h₁ s₀ s₁ t ht
  obtain ⟨C, hC⟩ := hRank D K ι Ω d.y d.k₀ d.one_le d.arith d.birat
  refine ⟨C, fun n => ?_⟩
  rw [hInt D K ι Ω d A₀ A₁ h₀ h₁ s₀ s₁ t ht]
  exact hC n

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace BlockResolutionMixedIntegral

theorem proof (hB : BlockResolutionMixedBridge.Statement) (hI : BlockResolutionInterpIntegral.Statement) :
    BlockResolutionMixedIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  rw [hI D K ι Ω d A' hdeg hA']
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : ∀ j : Fin D, IsSmoothHerm (if j.val < i then A' else d.A) := fun j => by
    split_ifs
    · exact hA'
    · exact d.semipos.1
  have hpot : blockMixPot d.A A' D i = fun j z => Real.log ((if j.val < i then A' else d.A).h z) := by
    funext j z
    unfold blockMixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => AnResBridge.potOf d.R (if j.val < i then A' else d.A)) =
      fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D K ι Ω d (fun j => if j.val < i then A' else d.A) A' hL hdeg hA', hres]

end BlockResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreSectionLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 1) →
    ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch (y := y) (S := ZMod p) s a = z

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
