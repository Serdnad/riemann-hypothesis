module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle066
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle168
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle176
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle162
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SesquilinearLevelZeroPairing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open MeasureTheory Topology Filter
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_isClosed (k r : ℕ) : IsClosed (B.GV k r) := by
  show IsClosed {g : B.Mat k r | Matrix.conjTranspose g * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem sgs_continuousAt_oneP {k r : ℕ} (g : B.Mat k r) :
    ContinuousAt (fun p : B.SS k r => B.sgs p g) oneP := by
  have hinv : ContinuousAt (fun A : B.Mat k r => A⁻¹) 1 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Matrix.det_one]
    exact NormedRing.inverse_continuousAt (1 : ℂˣ)
  have c11 : Continuous fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r) := continuous_fst.comp continuous_fst
  have c12 : Continuous fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r) := continuous_snd.comp continuous_fst
  have c21 : Continuous fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r) := continuous_fst.comp continuous_snd
  have c22 : Continuous fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r) := continuous_snd.comp continuous_snd
  have i1 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c11.continuousAt rfl
  have i2 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c12.continuousAt rfl
  show ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * g *
    (Matrix.of p.2.2 : B.Mat k r) * (Matrix.of p.2.1 : B.Mat k r)) oneP
  exact (((i1.mul i2).mul continuousAt_const).mul c22.continuousAt).mul c21.continuousAt

theorem avgCutoff_of_parts (hB : ACBump) (hI : ACInv) (hN : ACInt) (hP : ACHaarPos) (hS : ACSmooth) :
    Formalism.FourierDecayAlt.P.JFxI.AvgCutoff := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  obtain ⟨φ₀, hφ₀s, hφ₀n, hφ₀c, hφ₀O, hφ₀K⟩ := hB k r Wp Wq D K hK hKQ
  have hφ₀cont : Continuous φ₀ := hφ₀s.continuous
  set I : B.Mat k r → ℝ := fun g => ∫ p, φ₀ (B.sgs p g) ∂D.μSS with hIdef
  have hgqOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ JF.Om k r D.z D.z' := fun q hq =>
    Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q hq

  have hposI : ∀ g ∈ JF.Om k r D.z D.z', 0 < φ₀ g → 0 < I g := by
    intro g hg hφg
    have hint := hN k r Wp Wq D φ₀ hφ₀cont hφ₀c g hg
    rw [hIdef]
    refine (integral_pos_iff_support_of_nonneg (fun p => hφ₀n _) hint).2 ?_
    have hca : ContinuousAt (fun p : B.SS k r => φ₀ (B.sgs p g)) oneP :=
      hφ₀cont.continuousAt.comp (sgs_continuousAt_oneP g)
    have hev : ∀ᶠ p in 𝓝 (oneP : B.SS k r), 0 < φ₀ (B.sgs p g) := by
      refine hca.eventually (lt_mem_nhds ?_)
      show 0 < φ₀ (B.sgs oneP g)
      rw [sgs_oneP]; exact hφg
    obtain ⟨O, hOsub, hOo, hO1⟩ := mem_nhds_iff.1 hev
    exact lt_of_lt_of_le (hP k r Wp Wq D O hOo hO1)
      (measure_mono fun p hp => (ne_of_gt (hOsub hp)))

  have hcont : ContinuousOn (fun q => I (B.gq D q)) K := by
    intro q₀ hq₀
    have hq₀D := hKQ hq₀
    obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O _ (hgqOm q₀ hq₀D)
    have hgqc : ContinuousAt (fun q => B.gq D q) q₀ :=
      ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn).continuousAt
        ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D)
    have hev : (fun q => I (B.gq D q)) =ᶠ[𝓝 q₀] fun q => I' (B.gq D q) := by
      have h1 : ∀ᶠ q in 𝓝 q₀, B.gq D q ∈ U := hgqc.preimage_mem_nhds (hUo.mem_nhds hgU)
      have h2 : ∀ᶠ q in 𝓝 q₀, q ∈ JF.QDom k r D.z D.z' := (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D
      filter_upwards [h1, h2] with q hq1 hq2
      exact hII' _ hq1 (hgqOm q hq2).1
    have hI'c : ContinuousAt I' (B.gq D q₀) := (hI'U.continuousOn).continuousAt (hUo.mem_nhds hgU)
    exact ((ContinuousAt.comp_of_eq hI'c hgqc rfl).congr hev.symm).continuousWithinAt

  obtain ⟨c₀, hc₀, hc₀K⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q ∈ K, c₀ ≤ I (B.gq D q) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun q hq => by simp [hKe] at hq⟩
    · obtain ⟨q₁, hq₁, hmin⟩ := hK.exists_isMinOn hKne hcont
      exact ⟨I (B.gq D q₁), hposI _ (hgqOm q₁ (hKQ hq₁)) (hφ₀K q₁ hq₁), fun q hq => hmin hq⟩

  set s : ℝ → ℝ := fun t => Real.smoothTransition ((t - c₀ / 2) / (c₀ / 2)) with hsdef
  set σ : ℝ → ℝ := fun t => s t * t + (1 - s t) * (c₀ / 2) with hσdef
  have hc2 : 0 < c₀ / 2 := by linarith
  have hσlb : ∀ t, c₀ / 2 ≤ σ t := by
    intro t
    have h0 : 0 ≤ s t := Real.smoothTransition.nonneg _
    by_cases ht : c₀ / 2 ≤ t
    · show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      nlinarith
    · have hz : s t = 0 := Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hc2.le)
      show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      rw [hz]; simp
  have hσpos : ∀ t, σ t ≠ 0 := fun t => (lt_of_lt_of_le hc2 (hσlb t)).ne'
  have hσid : ∀ t, c₀ ≤ t → σ t = t := by
    intro t ht
    have h1 : s t = 1 := Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc2]; linarith)
    show s t * t + (1 - s t) * (c₀ / 2) = t
    rw [h1]; ring
  have hσs : ContDiff ℝ ∞ σ := by
    have hs : ContDiff ℝ ∞ s :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact (hs.mul contDiff_id).add ((contDiff_const.sub hs).mul contDiff_const)

  classical
  let φ : B.Mat k r → ℂ := fun g => if g ∈ B.GV k r then ((φ₀ g * (σ (I g))⁻¹ : ℝ) : ℂ) else 0
  have hφ0 : ∀ g, g ∉ tsupport φ₀ → φ g = 0 := by
    intro g hg
    have : φ₀ g = 0 := image_eq_zero_of_notMem_tsupport hg
    simp [φ, this]
  refine ⟨φ, ?_, ⟨tsupport φ₀ ∩ B.GV k r, hφ₀c.isCompact.inter_right (gv_isClosed k r),
    fun g hg => ⟨hg.2, hφ₀O hg.1⟩, fun g hg => ?_⟩, ?_⟩
  ·
    intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O g₀ ⟨hg₀, hO⟩
      refine ⟨U, fun g => ((φ₀ g * (σ (I' g))⁻¹ : ℝ) : ℂ), hUo, hgU, ?_, ?_⟩
      · have h1 : ContDiffOn ℝ ∞ (fun g => φ₀ g * (σ (I' g))⁻¹) U :=
          hφ₀s.contDiffOn.mul ((hσs.comp_contDiffOn hI'U).inv fun g _ => hσpos _)
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
      · intro g hg hgG
        show (if g ∈ B.GV k r then ((φ₀ g * (σ (∫ p, φ₀ (B.sgs p g) ∂D.μSS))⁻¹ : ℝ) : ℂ) else 0) = _
        rw [if_pos hgG, hII' g hg hgG]
    · refine ⟨(tsupport φ₀)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, fun h => hO (hφ₀O h),
        contDiffOn_const, fun g hg _ => hφ0 g hg⟩
  ·
    by_cases hgG : g ∈ B.GV k r
    · exact hφ0 g fun h => hg ⟨h, hgG⟩
    · simp [φ, hgG]
  ·
    intro p₀ hp₀ q hq
    have hgq := hgqOm q (hKQ hq)
    have hg := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D hp₀ hgq
    have hIg : I (B.sgs p₀ (B.gq D q)) = I (B.gq D q) := hI k r Wp Wq D φ₀ hφ₀cont p₀ hp₀ _
    have hIpos : 0 < I (B.gq D q) := lt_of_lt_of_le hc₀ (hc₀K q hq)
    have hae : ∀ᵐ p ∂D.μSS, φ (B.sgs p (B.sgs p₀ (B.gq D q))) =
        ((φ₀ (B.sgs p (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hG : B.sgs p (B.sgs p₀ (B.gq D q)) ∈ B.GV k r := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV D hp hg.1
      have hIp : I (B.sgs p (B.sgs p₀ (B.gq D q))) = I (B.gq D q) := by
        rw [← hIg]; exact hI k r Wp Wq D φ₀ hφ₀cont p hp _
      simp only [φ, if_pos hG, hIp, hσid _ (hc₀K q hq)]
    rw [integral_congr_ae hae, integral_complex_ofReal, integral_mul_const]
    change (((I (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) = 1
    rw [hIg, mul_inv_cancel₀ hIpos.ne', Complex.ofReal_one]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open MeasureTheory Topology
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_bump_holds : ACBump := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  have : LocallyCompactSpace (B.Mat k r) :=
    (inferInstance : LocallyCompactSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  have hcont : ContinuousOn (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn
  have hgK : IsCompact ((fun q => B.gq D q) '' K) := hK.image_of_continuousOn (hcont.mono hKQ)
  have hsub : (fun q => B.gq D q) '' K ⊆ Q.OmPlus k r D.z D.z' := by
    rintro _ ⟨q, hq, rfl⟩
    exact (Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q (hKQ hq)).2
  obtain ⟨L, hLc, hKL, hLO⟩ := exists_compact_between hgK (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z') hsub
  obtain ⟨φ₀, hsupp, hsmooth, hrange⟩ :=
    (isOpen_interior : IsOpen (interior L)).exists_contDiff_support_eq (n := ⊤)
  have hts : tsupport φ₀ ⊆ L := by
    unfold tsupport
    rw [hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  refine ⟨φ₀, hsmooth, fun g => (hrange ⟨g, rfl⟩).1, hLc.of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hLO, fun q hq => ?_⟩
  have hin : B.gq D q ∈ Function.support φ₀ := by
    rw [hsupp]; exact hKL ⟨q, hq, rfl⟩
  exact lt_of_le_of_ne (hrange ⟨_, rfl⟩).1 (Ne.symm hin)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def TopDMeasCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → KB.CutWord P p.l0 w →
      AEStronglyMeasurable (topD p X w) volume

section iter

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem normC_one (w : List C.Letter) : TBB.normC (fun _ => 1) w = 1 := by
  unfold TBB.normC
  induction w with
  | nil => rfl
  | cons a w ih => simp

end iter

section iter2

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end iter2

section assembly

theorem nfHyp_monoC {Cb C c : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ : ℝ → ℝ} {N : ℕ}
    (hH : NFHyp Cb C p f A₀ p₀ χ N) (hc : c ≤ C) : NFHyp Cb c p f A₀ p₀ χ N := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
      x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
    fun x => by ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hc hX

end assembly

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

theorem vtop_rows (k r : ℕ) (s : Fin (k + 1)) : rowsNv k r (Fin.last r) s = rowsN k r (Fin.last r) s := by
  funext j
  apply Fin.ext
  simp [rowsNv, rowsN]

theorem mirror_residue_top_holds : JDRvTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  simp only [FNv, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NLv
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, vtop_rows, vtop_rows]
  congr 1
  have ez : Q.wCell k r (Fin.last r) c *ᵥ z = z := top_wlist_wb c _ z hz
  have eh : herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec (wI k r s)) z =
      herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z := by
    rw [← Matrix.mulVec_mulVec]
    conv_lhs => rw [← ez]
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hW.1 _ _
  have es : Q.posL k r (Fin.last r) (Fin.cast hm.symm s) = wI k r s := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  have et : Q.posL k r (Fin.last r) (Fin.cast hm.symm t) = wI k r t := by
    apply Fin.ext; simp [Q.posL, wI]; omega
  rw [eh]
  simp only [Q.ybv, Q.xv, fvec, es, et]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section TowerC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

theorem transportC {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
    {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
    {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
    {l0 : ℕ} (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef (T.bs j) ε F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) (Y : ℝ) (a b : Fin 2) {R : ℝ} (hRF : BSR R F) :
    ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j ((QQi L st 0 (Y : ℂ) a b).1 Φ) F' := by
  let w : List C.Letter := [(true, Y)]
  let Fv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := Pi.single (eS 0 b) F
  have hFv : ∀ e, JC.NiceCoef (T.bs j) ε (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let xv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun e => B.JF (T.bs j) (Fv e)
  let Φv : Ix (Fin w.length) →
      RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' :=
    Pi.single (eS 0 b) Φ
  have hx : ∀ e, xv e ∈ FFl (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' 0
      (OmPlus (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z') := fun e =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (Fv e) ε hε (hFv e)
  have hΦv : ∀ e, ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φv e : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (xv e) y.1 y.2 := by
    intro e y hy
    by_cases h : e = eS 0 b
    · subst h
      have := hΦ y hy
      simp only [Φv, xv, Fv, Pi.single_eq_same]
      exact this
    · simp only [Φv, xv, Fv, Pi.single_eq_of_ne h]
      have h0 := congrFun (congrFun (resG_JF_zero (T.bs j) (Fin.last (JC.parLev P0 j).r)) y.1) y.2
      exact h0.symm
  have hRv : ∀ e, BSR R (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hRF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact fun g _ h0 => absurd rfl h0
  refine ⟨D.actOp (D.RRlev T (M.sgn P0 l0) j w) Fv (eS 0 a),
    Formalism.FourierDecayAlt.P.module_regularity Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a),
    (actOp_nice_bsr P0 T (M.sgn P0 l0) j w Fv hFv hRv (eS 0 a)).2, fun y hy => ?_⟩
  have hact := Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w xv Φv hx hΦv (eS 0 a) y hy
  have hbes := Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a) y hy
  have e : P5.act (RRi L st 0 (D.positionted w)) Φv (eS 0 a) = (QQi L st 0 (Y : ℂ) a b).1 Φ := by
    show actP (RRw (QQi L st 0) [(⟨true, 0, (Y : ℂ)⟩ : Letter ℂ (Fin 1))]) (Pi.single (eS 0 b) Φ) (eS 0 a) = _
    exact blockMulVec_one_letter _ _ _ _ _ _
  have e' := congrArg (fun Ψ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
    (T.bs j).π' => (Ψ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2) e
  exact e'.symm.trans (hact.trans hbes.symm)

end TowerC

section ClsC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

def PicsInBS (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (K0 : Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) :
    Prop :=
  ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε R : ℝ), 0 < ε → JC.NiceCoef (T.bs j) ε F → BSR R F →
    ∃ Φ ∈ K0, ∀ x ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) x.1 x.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last (JC.parLev P0 j).r) (B.JF (T.bs j) F) x.1 x.2

theorem pic_mem_K0C (hJ : PicsInBS T j (K 0)) {ε R : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F) (hRF : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ K 0 := by
  obtain ⟨Φ', hK, hΦ'⟩ := hJ F ε R hε hF hRF
  have e : Φ = Φ' := radSp_ext Φ Φ' (fun y hy => (hΦ y hy).trans (hΦ' y hy).symm)
  rw [e]; exact hK

theorem pic_mem_UclsC (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    (hJ : PicsInBS T j (K 0)) (Pts : Set ℝ) {ε R : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F) (hRF : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ Ucls (K 0) (Gen L st Pts) := by
  intro m hm
  have key : ∀ m ∈ Submonoid.closure (Gen L st Pts), ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      JC.NiceCoef (T.bs j) ε F → BSR R F → IsPic T j Φ F →
      ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j (m.1 Φ) F' := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem a ha =>
      intro F Φ hF hRF hΦ
      obtain ⟨Y, _, i, i', rfl⟩ := ha
      exact transportC hD hε hF Φ hΦ Y i i' hRF
    | one => intro F Φ hF hRF hΦ; exact ⟨F, hF, hRF, hΦ⟩
    | mul a b _ _ iha ihb =>
      intro F Φ hF hRF hΦ
      obtain ⟨F1, h1, hr1, h1'⟩ := ihb F Φ hF hRF hΦ
      obtain ⟨F2, h2, hr2, h2'⟩ := iha F1 _ h1 hr1 h1'
      exact ⟨F2, h2, hr2, h2'⟩
  obtain ⟨F', hF', hRF', hΦ'⟩ := key m hm F Φ hF hRF hΦ
  exact pic_mem_K0C hJ hε hF' hRF' _ hΦ'

end ClsC

end

end Formalism.FourierDecayAlt.P.PBF
end
