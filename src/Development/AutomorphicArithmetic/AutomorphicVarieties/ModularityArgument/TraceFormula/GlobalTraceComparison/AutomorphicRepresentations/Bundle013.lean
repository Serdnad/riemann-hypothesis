module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle006
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
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
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ac_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ac E n 0 = 1 := by
  unfold ac
  rw [zero_div, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  rfl

private theorem test_trM {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]
    {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    Continuous (trM Φ M) ∧ HasCompactSupport (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  constructor
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hΦ i j).1.mul continuous_const
  · rw [e]
    exact HasCompactSupport.finset_sum fun i _ => HasCompactSupport.finset_sum fun j _ => (hΦ i j).2.mul_right

private theorem ldet_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : H E n 0 → ℂ}
    (hc : HasCompactSupport φ) : ∃ N : ℕ, ∀ z, φ z ≠ 0 → |ldet z| ≤ N := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image (continuous_abs.comp (continuous_ldet (E := E) (n := n)))).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨N, fun z hz => (hR ⟨z, subset_tsupport _ hz, rfl⟩).trans hN⟩

private theorem cut_cont (N : ℕ) : Continuous fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (Dcy.continuous_chi N)

private theorem cut_supp (N : ℕ) : HasCompactSupport fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun t ht => by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
    rw [Dcy.chi_eq_zero ht.le, Complex.ofReal_zero]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rangeW_pf :
    Rep → RangeW := by
  intro hR E _ _ _ n ι _ s p hF m ψ hψ x₀ h₀
  obtain ⟨N, hN⟩ := ldet_bound (test_trM m.t s.M).2
  set u : ℝ → ℂ := fun t => ((Dcy.chi N t : ℝ) : ℂ) with hu
  have rep := fun y => hR E n ι s m ψ hψ u (cut_cont N) (cut_supp N) y
  have key : ∀ y : H E n 0, ldet y = 0 →
      ∫ x, ψ.1 x.1 * m.G y x * u (ldet x) ∂s.D.ν = ∫ z, m.φ z * ψ.1 (thetaA E n (y.1 * z.1)) ∂s.D.μ := by
    intro y hy
    rw [(rep y).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : m.φ z = 0
    · simp [hz]
    · have h1 : |(-(ldet y + ldet z))| ≤ N := by
        rw [hy, zero_add, abs_neg]
        exact hN z hz
      simp only [hu, Dcy.chi_eq_one h1, Complex.ofReal_one, mul_one]
  rw [← key x₀ h₀]
  have hG : ∀ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) =
      ∑ b, (p.w b).1 x₀.1 * (ψ.1 x.1 * m.G (p.x b) x * u (ldet x)) := by
    intro x
    rw [hF m x₀ x, h₀, ac_zero, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [one_mul]
    ring
  simp_rw [hG]
  rw [integral_finsetSum _ fun b _ => ((rep (p.x b)).1).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, key (p.x b) (p.zero b)]

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem test_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    IsTestH (trM Φ M) := by
  have h := (kerLin (ctx ratProper_holds D) (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  exact h

private theorem measurable_cnt (D : Dom E n 0) {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI : T2Space (H E n 0) := (ctx ratProper_holds D).t2
  haveI : IsTopologicalGroup (H E n 0) := (ctx ratProper_holds D).tg
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : Countable (ratH E n 0) := Dcy.countable_ratH'
  unfold cnt
  refine Measurable.tsum fun γ => ?_
  have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  exact (measurable_one.indicator hΩ.isClosed.measurableSet).comp hc.measurable

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.halfTerm_pf :
    Basic → GBound → Supp → Rep → Flip → DomInt → HalfTerm := by
  intro hB hGB hSu hRep hFl hDI E _ _ _ n ι _ s m ψ hψ x₀ hx₀
  classical
  haveI : T2Space (H E n 0) := (ctx ratProper_holds s.D).t2
  haveI : SecondCountableTopology (H E n 0) := (ctx ratProper_holds s.D).sc
  haveI : IsTopologicalGroup (H E n 0) := (ctx ratProper_holds s.D).tg
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure s.D.μ := s.D.haar.2.2.2
  haveI : SFinite s.D.ν := by unfold Dom.ν; infer_instance
  obtain ⟨hlac, hlmul, -, -, -, hacc, -, -, -, -, hlc, hthc⟩ := hB E n s.pos
  have hφ : IsTestH m.φ := test_trM s.D m.t s.M
  have hψc : Continuous ψ.1 := continuous_of_mem s.π hψ
  obtain ⟨R₀, hR₀⟩ := (hφ.2.isCompact).exists_bound_of_continuousOn hlc.continuousOn
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ R := fun z hz =>
    (hR₀ z (subset_tsupport _ hz)).trans (le_max_left _ _)
  obtain ⟨Ω, hΩ, hG⟩ := hGB E n ι s
  obtain ⟨C, hC0, hCb⟩ := hG x₀
  obtain ⟨N, hN⟩ := hDI E n s.pos s.D s.π s.fix ψ hψ Ω hΩ
  obtain ⟨C', hC', hb⟩ := hN 0 le_rfl
  have hb' := hb (R + 1) 0 (by positivity)
  have hcf : ∀ x, cnt (ratH E n 0) Ω x ≠ ⊤ := (cntBasic (ctx ratProper_holds s.D)).1 Ω hΩ
  have hcm := measurable_cnt s.D hΩ
  have hA : 0 ≤ C * ‖m.U‖ := mul_nonneg hC0 (norm_nonneg _)
  set S : Set (H E n 0) := {x | |ldet x| ≤ R + 1} with hS
  have hSm : MeasurableSet S := (isClosed_le (continuous_abs.comp hlc) continuous_const).measurableSet
  let F : ℝ → H E n 0 → ℂ := fun t x => ψ.1 x.1 * m.G (ac E n t * x₀) x
  let mm : H E n 0 → ℂ := fun z => m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1))
  let d : H E n 0 → ℝ := S.indicator fun x => ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal
  have hlm : Measurable (ldet : H E n 0 → ℝ) := hlc.measurable

  have hFj : Continuous (Function.uncurry F) := by
    refine (hψc.comp (continuous_fst.comp continuous_snd)).mul ?_
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.inner ?_ ?_
    · exact (s.vecs.cont i).1.comp ((hacc.comp continuous_fst).mul continuous_const)
    · exact m.Uπ.continuous.comp ((s.vecs.cont i).2.comp continuous_snd)
  have hFs : ∀ x, Continuous fun t => F t x := fun x =>
    hFj.comp (continuous_id.prodMk continuous_const)

  have hmm : Integrable mm s.D.μ := by
    haveI : IsFiniteMeasureOnCompacts s.D.μ :=
      ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ => s.D.μ.finiteAt_nhdsWithin x K⟩
    refine Continuous.integrable_of_hasCompactSupport ?_ hφ.2.mul_right
    refine hφ.1.mul (hψc.comp ?_)
    have : Continuous fun z : H E n 0 => (th (x₀ * z)).1 :=
      continuous_fst.comp (hthc.comp (continuous_const.mul continuous_id))
    exact this

  have hdm : Measurable d := by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ hcm.ennreal_toReal
    exact ((hψc.comp continuous_fst).norm.mul continuous_const).measurable
  have hdI : Integrable d s.D.ν := by
    refine ⟨hdm.aestronglyMeasurable, ?_⟩
    set f : H E n 0 → ℝ≥0∞ := {x | |ldet x| ≤ R + 1 ∧ (0 : ℝ) ≤ r0 x}.indicator
      (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
    have hpt : ∀ x, ‖d x‖ₑ ≤ ENNReal.ofReal (C * ‖m.U‖) * f x := by
      intro x
      by_cases hx : x ∈ S
      · have hx' : x ∈ {x | |ldet x| ≤ R + 1 ∧ (0 : ℝ) ≤ r0 x} := ⟨hx, Dcy.redSize_nonneg _⟩
        have e1 : d x = ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal :=
          Set.indicator_of_mem hx _
        rw [e1, hf, Set.indicator_of_mem hx', Real.enorm_eq_ofReal (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ENNReal.ofReal_toReal (hcf x)]
        exact le_of_eq (by ring)
      · have e1 : d x = 0 := Set.indicator_of_notMem hx _
        simp [e1]
    calc ∫⁻ x, ‖d x‖ₑ ∂s.D.ν ≤ ∫⁻ x, ENNReal.ofReal (C * ‖m.U‖) * f x ∂s.D.ν := lintegral_mono hpt
      _ = ENNReal.ofReal (C * ‖m.U‖) * ∫⁻ x, f x ∂s.D.ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hb' ENNReal.ofReal_lt_top)

  have hlx : ∀ t, ldet (ac E n t * x₀) = t := fun t => by rw [hlmul, hlac, hx₀, add_zero]
  have hbd : ∀ t x, |t - ldet x| ≤ 1 → ‖F t x‖ ≤ d x := by
    intro t x htx
    by_cases hx : x ∈ S
    · have e1 : d x = ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal :=
        Set.indicator_of_mem hx _
      rw [e1, mul_assoc]
      show ‖ψ.1 x.1 * m.G (ac E n t * x₀) x‖ ≤ _
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcf x)) (hCb m t x)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at h1
      simpa using h1
    · have e1 : d x = 0 := Set.indicator_of_notMem hx _
      have hx2 : R + 1 < |ldet x| := not_le.1 hx
      have hg : m.G (ac E n t * x₀) x = 0 := by
        refine hSu E n ι s m R hR _ _ ?_
        rw [hlx]
        by_contra hc
        have h1 := abs_le.1 (not_lt.1 hc)
        have h2 := abs_le.1 htx
        have h3 : |ldet x| ≤ R + 1 := abs_le.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2, hR0], by linarith [h1.1, h1.2, h2.1, h2.2, hR0]⟩
        exact hx h3
      rw [e1]
      show ‖ψ.1 x.1 * m.G (ac E n t * x₀) x‖ ≤ 0
      simp [hg]

  obtain ⟨ψ', hψ', hθ⟩ := s.fix.2 ψ hψ
  have hrep : ∀ (t : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u →
      ∫ x, F t x * u (ldet x) ∂s.D.ν = ∫ z, mm z * u (-(t + ldet z)) ∂s.D.μ := by
    intro t u hu hu'
    have h := (hRep E n ι s m ψ hψ u hu hu' (ac E n t * x₀)).2
    refine h.trans (integral_congr_ae (Eventually.of_forall fun z => ?_))
    show m.φ z * ψ.1 (thetaA E n ((ac E n t * x₀).1 * z.1)) * u (-(ldet (ac E n t * x₀) + ldet z)) =
      m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(t + ldet z))
    have e : (ac E n t * x₀).1 * z.1 = splitCentre E n (t / (n * Module.finrank ℚ E)) * (x₀.1 * z.1) := by
      simp only [ac, Prod.fst_mul, mul_assoc]
    rw [hlx, e, ← hθ, ← hθ, s.fix.1 ψ' hψ']
  exact hFl (H E n 0) (H E n 0) s.D.ν s.D.μ ldet ldet F mm d hlm hlm hFj.measurable hFs hmm hdI hbd hrep
end
