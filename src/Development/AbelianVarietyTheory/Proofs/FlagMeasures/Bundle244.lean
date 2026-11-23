module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle022
public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle235
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle236
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualFamilyInSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeImageFrameQuotient
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryFrameDual
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
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField Finset Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FarTerms

private lemma indicator_eq_indicator_inter_support {α : Type} (S : Set α) (F : α → ℝ) :
    S.indicator F = ({a | a ∈ S ∧ F a ≠ 0} : Set α).indicator F := by
  funext a
  by_cases hS : a ∈ S <;> by_cases hF : F a = 0 <;> simp [Set.indicator, hS, hF]

theorem summable_of_support {α : Type} (S : Set α) (F : α → ℝ) (C : ℝ)
    (h : Summable (fun γ : {a // a ∈ S ∧ F a ≠ 0} => F γ.1) ∧
      ∑' γ : {a // a ∈ S ∧ F a ≠ 0}, F γ.1 ≤ C) :
    Summable (fun γ : S => F γ.1) ∧ ∑' γ : S, F γ.1 ≤ C := by
  obtain ⟨hs, hle⟩ := h
  have key := indicator_eq_indicator_inter_support S F
  have hT : Summable (({a | a ∈ S ∧ F a ≠ 0} : Set α).indicator F) :=
    (summable_subtype_iff_indicator (s := {a | a ∈ S ∧ F a ≠ 0}) (f := F)).1 hs
  rw [← key] at hT
  refine ⟨(summable_subtype_iff_indicator (s := S) (f := F)).2 hT, ?_⟩
  rw [tsum_subtype S F, key, ← tsum_subtype {a | a ∈ S ∧ F a ≠ 0} F]
  exact hle

private lemma one_le_n_of_sigIs_of_one_le_q (B : RowsAut) (p q : ℕ) (hS : SigIs B p q) (hq : 1 ≤ q) :
    1 ≤ B.I.n := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace B.I.F))
  have h1 : B.I.qAt v = q := (hS v).2
  have h2 : B.I.qAt v ≤ B.I.n := by
    show (Finset.univ.filter fun a => B.I.ε v a = false).card ≤ B.I.n
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

theorem farBound_of_ptBound : GlobalTheory.Deep.PtBound → GlobalTheory.Deep.FarBound := by
  intro hP B d p q h ep hDS hSig hqm hq1 hGap hep0 hepc hlog hhep hhep2 h120 x
  have hn : 1 ≤ B.I.n := one_le_n_of_sigIs_of_one_le_q B p q hSig hq1
  have h120' : 120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [← hqm]; exact h120
  obtain ⟨hdec, hbd, -, -, -, hK, -⟩ := hP B d p q h hDS hSig hGap h120'
  rw [← hqm] at hdec
  have hdec' := hdec hq1
  have hne : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, phe B d (x⁻¹ * γ.1 * x) ≠ 0 := by
    intro γ h0
    exact γ.2.2 (by simp [h0])
  have hM0 : 0 ≤ (∏ v, d v) * (B.e 1).re := (norm_nonneg _).trans (hbd 1)
  rcases eq_or_lt_of_le hM0 with hM | hM
  · haveI : IsEmpty {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} :=
      ⟨fun γ => hne γ (norm_eq_zero.1 (le_antisymm ((hbd _).trans_eq hM.symm) (norm_nonneg _)))⟩
    refine summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x)
      (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨summable_empty, ?_⟩
    rw [tsum_empty, ← hM]
    simp
  · have hMne : (∏ v, d v) * (B.e 1).re ≠ 0 := hM.ne'
    have hA : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor; positivity
    have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hc : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    have hdist : ∀ (γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}) (v : InfinitePlace B.I.F),
        0 ≤ GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) := by
      intro γ v; unfold GlobalTheory.Count.dHS; exact Real.sqrt_nonneg _
    have hcount : ∀ r : InfinitePlace B.I.F → ℝ, (∀ v, 0 ≤ r v) →
        {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}.Finite ∧
        (({γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
          GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x * Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) := by
      intro r hr
      obtain ⟨hfin, hcard⟩ := GlobalTheory.AutBall.autBallCount B.I hn x r hr
      have hmaps : ∀ γ ∈ {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v},
          (γ.1 : B.I.GA) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet B.I x r := by
        intro γ hγ
        have hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1 := γ.2.1
        show γ.1 ∈ B.I.GFset ∧ (x⁻¹ * γ.1 * x).2 ∈ B.I.Kset ∧
          ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v
        exact ⟨hm.1, hK _ (hne γ), hγ⟩
      have hinj : Set.InjOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1)
          {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v} :=
        fun a _ b _ hab => Subtype.ext hab
      refine ⟨(hfin.preimage Subtype.val_injective.injOn).subset hmaps, ?_⟩
      have hle := Set.ncard_le_ncard_of_injOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1) hmaps hinj hfin
      have hAB : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x = GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA B.I x := rfl
      rw [hAB]
      exact (Nat.cast_le.2 hle).trans hcard
    have hfar : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ∃ v, ep < GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) := by
      intro γ
      have hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1 := γ.2.1
      by_contra hcon
      push_neg at hcon
      exact hm.2 (by unfold GlobalTheory.Count.IsNear; exact ⟨hm.1, hne γ, hcon⟩)
    have hw : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, 0 ≤ ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ∧
        ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ≤
          ∏ v, Real.exp (-(h / 8) * min (GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ^ 2)
            (GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) / Real.sqrt (2 * (q : ℝ)))) := by
      intro γ
      refine ⟨div_nonneg (norm_nonneg _) hM.le, ?_⟩
      rw [div_le_iff₀ hM]
      exact le_of_le_of_eq (hdec' (x⁻¹ * γ.1 * x)) (mul_comm _ _)
    obtain ⟨hsum, hle⟩ := GlobalTheory.sum_over_dyadic_shells {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} (InfinitePlace B.I.F)
      (fun γ v => GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)))
      (fun γ => ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re))
      (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x) (2 * (B.I.n : ℝ) ^ 2) h ep (Real.sqrt (2 * (q : ℝ)))
      hA (by positivity) hep0 hc hepc hlog (by linarith) hhep2 hdist hcount hfar hw
    have hfun : (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖) =
        fun γ => (∏ v, d v) * (B.e 1).re * (‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re)) := by
      funext γ
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hMne, mul_one]
    have hs' : Summable (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [hfun]; exact hsum.mul_left _
    have hle' : ∑' γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤
        (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
          (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * ep ^ 2 / 16))) := by
      rw [hfun, tsum_mul_left]
      calc _ ≤ (∏ v, d v) * (B.e 1).re * (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
              (2 * (Fintype.card (InfinitePlace B.I.F) : ℝ) * 3 ^ Fintype.card (InfinitePlace B.I.F) *
                Real.exp (-(h * ep ^ 2 / 16)))) := mul_le_mul_of_nonneg_left hle hM.le
        _ = _ := by rw [GlobalTheory.Count.FrameMajorant.card_places B.I]; ring
    exact summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x)
      (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨hs', hle'⟩

end GlobalTheory.FarTerms
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
open scoped ENNReal

namespace GlobalTheory.ThA

private lemma measurable_lmulM_flag_measures {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.measurable_sum _ fun l _ => measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply l))

private lemma measurable_rmulF' {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Measurable (B.rmulF a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [B.rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

private lemma measurableSet_lmulM_pair_mem {k r : ℕ} {A : Set (Mt k r)} (hA : MeasurableSet A) :
    MeasurableSet {p : Mt k r × Mt k r | lmulM (Matrix.of p.2) p.1 ∈ A} := by
  have hm : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  exact hm hA

theorem measure_eq_smul_of_left_right {k r : ℕ} {U : Set (B.Mat k r)} {μ ν : Measure (Mt k r)}
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ U) (hν : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ U)
    (hl : ∀ a ∈ U, Measure.map (lmulM a) μ = μ) (hr : ∀ a ∈ U, Measure.map (B.rmulF a) ν = ν) :
    ν = ν Set.univ • μ := by
  ext A hA
  set S : Set (Mt k r × Mt k r) := {p | lmulM (Matrix.of p.2) p.1 ∈ A} with hSdef
  have hS : MeasurableSet S := measurableSet_lmulM_pair_mem hA

  have hx : (μ.prod ν) S = ν A := by
    rw [Measure.prod_apply hS]
    have hslice : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' S) = ν A := by
      filter_upwards [hμ] with x hx
      have hpre : Prod.mk x ⁻¹' S = B.rmulF (Matrix.of x) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_rmulF' _) hA, hr _ hx]
    rw [lintegral_congr_ae hslice, lintegral_const, measure_univ, mul_one]

  have hy : (μ.prod ν) S = μ A * ν Set.univ := by
    rw [Measure.prod_apply_symm hS]
    have hslice : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' S) = μ A := by
      filter_upwards [hν] with y hy
      have hpre : (fun x => (x, y)) ⁻¹' S = lmulM (Matrix.of y) ⁻¹' A := rfl
      rw [hpre, ← Measure.map_apply (measurable_lmulM_flag_measures _) hA, hl _ hy]
    rw [lintegral_congr_ae hslice, lintegral_const]
  rw [Measure.smul_apply, smul_eq_mul, ← hx, hy, mul_comm]

theorem haarW_twoSided_of_left : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  intro k r z μ _ _ hH h1
  obtain ⟨_, hne, hconc, hleft⟩ := hH
  haveI : IsProbabilityMeasure μ := ⟨h1⟩
  have hinvU : ∀ g ∈ UWset k r z, g⁻¹ ∈ UWset k r z ∧ g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 :=
    fun g hg => Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hg
  have hUm : MeasurableSet {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} :=
    (show IsClosed {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ UWset k r z} from
      Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r z).measurableSet
  have hμU : ∀ᵐ x ∂μ, (Matrix.of x : B.Mat k r) ∈ UWset k r z := ae_iff.mpr hconc

  have hinvm : Measurable (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := Formalism.FourierDecayAlt.P.HermitianFormFactor.invF_meas
  obtain ⟨ν, hνdef⟩ : ∃ ν : Measure (Mt k r), ν = μ.map (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) := ⟨_, rfl⟩
  have hmass : ν Set.univ = 1 := by
    rw [hνdef, Measure.map_apply hinvm MeasurableSet.univ, Set.preimage_univ, h1]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hνU : ∀ᵐ x ∂ν, (Matrix.of x : B.Mat k r) ∈ UWset k r z := by
    rw [hνdef]
    refine (ae_map_iff hinvm.aemeasurable hUm).2 ?_
    filter_upwards [hμU] with x hx using (hinvU _ hx).1

  have hνr : ∀ a ∈ UWset k r z, Measure.map (B.rmulF a) ν = ν := by
    intro a ha
    obtain ⟨hai, haa, -⟩ := hinvU a ha
    rw [hνdef, Measure.map_map (measurable_rmulF' a) hinvm]
    have hcomp : (B.rmulF a ∘ (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1)))) = (Formalism.FourierDecayAlt.P.HermitianFormFactor.invF (m := Fin (2 * r + k + 1))) ∘ lmulM a⁻¹ := by
      funext x
      show ((Matrix.of x)⁻¹ * a : B.Mat k r) = (a⁻¹ * Matrix.of x)⁻¹
      rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv haa]
    rw [hcomp]
    exact (Measure.map_map hinvm (measurable_lmulM_flag_measures a⁻¹)).symm.trans (congrArg (Measure.map _) (hleft _ hai))
  have hkey := measure_eq_smul_of_left_right (μ := μ) (ν := ν) hμU hνU hleft hνr
  rw [hmass, one_smul] at hkey
  refine ⟨hconc, hleft, fun a ha => ?_, fun K _ => measure_lt_top μ K, hne⟩
  have h := hνr a ha
  rwa [hkey] at h

end GlobalTheory.ThA
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

theorem _root_.GlobalTheory.T.span_different_eq_localGenerator : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  first | exact @GlobalTheory.LocDiffGen.span_different_eq | exact GlobalTheory.LocDiffGen.span_different_eq | (intros; apply GlobalTheory.LocDiffGen.span_different_eq <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cntPrim_latticeImage_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ (L : Submodule (𝓞 K) V) (j de : ℕ), cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  first | exact @GlobalTheory.LoopC.cntPrim_gmap_isom | exact GlobalTheory.LoopC.cntPrim_gmap_isom | (intros; apply GlobalTheory.LoopC.cntPrim_gmap_isom <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc MeasureTheory
open scoped Pointwise ENNReal Classical NNReal

namespace GlobalTheory.ModuleUnits

theorem modK_units : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → (∀ x y : E, IsUnit x → IsUnit y → M.modK (x * y) = M.modK x * M.modK y) ∧ (∀ x : E, IsUnit x → 0 < M.modK x ∧ M.modK (M.L.cj x) = M.modK x) ∧ ∀ x : E, x ∈ M.L.O → (∃ y ∈ M.L.O, x * y = 1) → M.modK x = 1 := by
  intro F _ _ _ E _ _ _ _ M hM
  obtain ⟨h1, h2, h3, h4, h5, hRc, hRo, hOc, hOo, -⟩ := GlobalTheory.SgLoc.Top.model_topology M hM
  have := hM.borel
  have := hM.loc
  have := hM.char0
  have := hM.haar.haar
  have hreg : M.mu.Regular := inferInstance
  have hO0 : M.mu (M.L.O : Set E) ≠ 0 := hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩
  have hOt : M.mu (M.L.O : Set E) ≠ ∞ := hOc.measure_lt_top.ne
  have hmodK : ∀ u : Eˣ, M.modK u = (distribHaarChar E u : ℝ) := by
    intro u
    have h := distribHaarChar_mul M.mu u (M.R : Set E)
    rw [hM.haar.volR, mul_one] at h
    change (M.mu (u • (M.R : Set E))).toReal = _
    rw [← h]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    rw [← Units.val_mul, hmodK, hmodK, hmodK, map_mul, NNReal.coe_mul]
  · intro x hx
    obtain ⟨u, rfl⟩ := hx
    refine ⟨by rw [hmodK]; exact NNReal.coe_pos.mpr distribHaarChar_pos, ?_⟩
    have hcjO : ∀ z, z ∈ M.L.O → M.L.cj z ∈ M.L.O := by
      intro z hz
      rw [M.L.O_def] at hz ⊢
      exact hz.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
    have hcjO' : ∀ z, M.L.cj z ∈ M.L.O ↔ z ∈ M.L.O := fun z =>
      ⟨fun h => by simpa [M.L.cj_cj] using hcjO _ h, hcjO z⟩
    have : IsModuleTopology F E := M.L.top
    have hc1 : Continuous M.L.cj := IsModuleTopology.continuous_of_linearMap M.L.cj.toLinearMap
    have hc2 : Continuous M.L.cj.symm :=
      IsModuleTopology.continuous_of_linearMap M.L.cj.symm.toLinearMap
    let φ : E ≃ₜ+ E := { M.L.cj.toAddEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }
    have hpre : ∀ X : Set E, addEquivAddHaarChar φ • M.mu (φ ⁻¹' X) = M.mu X := fun X =>
      addEquivAddHaarChar_smul_preimage M.mu φ
    have hφO : φ ⁻¹' (M.L.O : Set E) = M.L.O := by
      ext z
      exact hcjO' z
    have hc : (addEquivAddHaarChar φ : ℝ≥0∞) = 1 := by
      have h := hpre M.L.O
      rw [hφO] at h
      simp only [ENNReal.smul_def, smul_eq_mul] at h
      calc _ = (addEquivAddHaarChar φ : ℝ≥0∞) * M.mu M.L.O / M.mu M.L.O :=
            (ENNReal.mul_div_cancel_right hO0 hOt).symm
        _ = 1 := by rw [h, ENNReal.div_self hO0 hOt]
    let w : Eˣ := Units.map (M.L.cj : E →* E) u
    have hw : φ ⁻¹' (u • (M.L.O : Set E)) = w • (M.L.O : Set E) := by
      ext z
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
      change ((u⁻¹ : Eˣ) : E) * M.L.cj z ∈ M.L.O ↔ ((w⁻¹ : Eˣ) : E) * z ∈ M.L.O
      rw [← hcjO' (((w⁻¹ : Eˣ) : E) * z), map_mul]
      simp [w, M.L.cj_cj]
    have hχ : distribHaarChar E w = distribHaarChar E u := by
      apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt
      rw [← hw, distribHaarChar_mul M.mu u]
      have h := hpre (u • (M.L.O : Set E))
      simp only [ENNReal.smul_def, smul_eq_mul, hc, one_mul] at h
      exact h
    rw [show M.L.cj (u : E) = (w : E) from rfl, hmodK, hmodK, hχ]
  · rintro x hx ⟨y, hy, hxy⟩
    let u : Eˣ := ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩
    have hset : u • (M.L.O : Set E) = M.L.O := by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change y * z ∈ M.L.O ↔ z ∈ M.L.O
      constructor
      · intro h
        have h' := M.L.O.mul_mem hx h
        rwa [← mul_assoc, hxy, one_mul] at h'
      · intro h
        exact M.L.O.mul_mem hy h
    have h1 : distribHaarChar E u = 1 :=
      distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt (by rw [hset]; simp)
    rw [show x = (u : E) from rfl, hmodK, h1]
    simp

end GlobalTheory.ModuleUnits
end

section

open Formalism.MainNotions.S

namespace GlobalTheory

theorem locStd_exists_flag_coef_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r), ∃ v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L), v ∈ Fr.Fj (a.val + 1) ∧ H.h v (Fr.es a) = 1 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn L a

  have hiso : ∀ b c : Fin r, H.h (Fr.e b) (Fr.e c) = 0 := fun b c =>
    Fr.h_iso b.castSucc c.castSucc (Or.inl (Fin.castSucc_lt_last b).ne)
  have hes : ∀ b c : Fin r, H.h (Fr.e b) (Fr.es c) = if b = c then 1 else 0 := fun b c =>
    Fr.h_es b c

  have hlam : Fr.e a ∈ Fr.LamStd L := by
    refine Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩
    · rw [hes]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · rw [hiso]
      exact zero_mem _
    · simp only [Formalism.MainNotions.S.LocNG.FrameD.prF, hes, hiso, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, sub_self,
        ZeroMemClass.coe_zero]
    · rw [map_zero]
      exact L.zero_mem

  have hperp : ∀ w ∈ Fr.Fj a.val, H.h w (Fr.es a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      rw [hes, if_neg (Fin.ne_of_val_ne (Nat.ne_of_lt hb))]
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

  have hmem : Fr.e a ∈ Fr.Fj (a.val + 1) :=
    Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩
  have hle : a.val + 1 ≤ r := a.isLt
  have hdiff : n (Fr.e a) - Fr.e a ∈ Fr.Fj a.val := by
    have := (T.unipotentRadical_isotropicFlag_moves_step_into_prev Fr n hn (a.val + 1) hle (Fr.e a) hmem).1
    simpa using this
  have hmono : Fr.Fj a.val ≤ Fr.Fj (a.val + 1) :=
    Submodule.span_mono (Set.image_mono fun b (hb : b.val < a.val) => Nat.lt_succ_of_lt hb)
  refine ⟨n (Fr.e a), Submodule.mem_map.mpr ⟨Fr.e a, hlam, rfl⟩, ?_, ?_⟩
  · have := (Fr.Fj (a.val + 1)).add_mem (hmono hdiff) hmem
    simpa using this
  · have hsplit : n (Fr.e a) = (n (Fr.e a) - Fr.e a) + Fr.e a := by abel
    rw [hsplit, H.h_add_left, hperp _ hdiff, hes, if_pos rfl, zero_add]

end GlobalTheory
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.unitary_image_standardLattice_eq_selfDual_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → (∀ a : Fin r, Fr.f a.castSucc ∈ Λ) → ∀ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f → ∀ n : V ≃ₗ[E] V, IsUnitary H n → (∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) → (∀ a, n (Fr.es a) ∈ Λ) → (∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) → Λ = img n (Fr.LamStd L) := by
  first | exact @GlobalTheory.StdLatImg.eq_img_lamStd | exact GlobalTheory.StdLatImg.eq_img_lamStd | (intros; apply GlobalTheory.StdLatImg.eq_img_lamStd <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_totallyIsotropic_dual_family_in_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ y' : Fin r → V, (∀ a, y' a ∈ Λ) ∧ (∀ a b, H.h (y' a) (Fr.f b) = if b = a.castSucc then 1 else 0) ∧ ∀ a b, H.h (y' a) (y' b) = 0 := by
  first | exact @GlobalTheory.IsotropicDual.isotropic_dual | exact GlobalTheory.IsotropicDual.isotropic_dual | (intros; apply GlobalTheory.IsotropicDual.isotropic_dual <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_dual_family_in_selfDual_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ y : Fin (r + 1) → V, (∀ b, y b ∈ Λ) ∧ ∀ a b, H.h (y b) (Fr.f a) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.SelfDualFrame.exists_dual_family | exact GlobalTheory.SelfDualFrame.exists_dual_family | (intros; apply GlobalTheory.SelfDualFrame.exists_dual_family <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_innerLattice_image_frame_quotient : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ Fr.IsInner L := by
  first | exact @GlobalTheory.StdLatInner.exists_inner | exact GlobalTheory.StdLatInner.exists_inner | (intros; apply GlobalTheory.StdLatInner.exists_inner <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_unitary_frame_dual' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (y : Fin r → V), (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → (∀ a b, H.h (y a) (y b) = 0) → ∃ n : V ≃ₗ[E] V, IsUnitary H n ∧ (∀ b, n (Fr.f b) = Fr.f b) ∧ (∀ a, n (Fr.es a) = y a) ∧ ∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f := by
  first | exact @GlobalTheory.UnipFrame.exists_unitary_frame_dual | exact GlobalTheory.UnipFrame.exists_unitary_frame_dual | (intros; apply GlobalTheory.UnipFrame.exists_unitary_frame_dual <;> assumption)
end
