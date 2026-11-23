module

public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PairZero
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import GroundTheory.AutomorphicForms.ReductionIwasawa
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
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
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import Mathlib.Topology.UniformSpace.Uniformizable
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

@[expose] public section

section

noncomputable section

open NumberField MeasureTheory
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal InnerProductSpace

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

theorem memLp_rt (X : PositivityTheory.Rg.BcB.E1.Ctx) (hr : X.μ.IsMulRightInvariant) {f : X.G → ℂ}
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (z : X.G) :
    MemLp (fun x => f (x * z)) 2 X.ν := by
  haveI := hr
  have hνμ : X.ν ≪ X.μ := Measure.absolutelyContinuous_of_le (Measure.restrict_le_self : X.μ.restrict X.F ≤ X.μ)
  have hm : AEStronglyMeasurable (fun x => f (x * z)) X.ν :=
    ((aesm_of_inv X hinv hf.aestronglyMeasurable).comp_measurePreserving (measurePreserving_mul_right X.μ z)).mono_ac hνμ
  change eLpNorm (fun x => f (x * z)) 2 X.ν < ∞
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm,
    lint_rt X hr (g := fun y => ‖f y‖ₑ ^ (2 : ℝ≥0∞).toReal) (fun γ y => by simp only [hinv γ y]) z,
    ← eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf.aestronglyMeasurable]
  exact hf

theorem piInv_of (hC : PiClosureInv) : PiInv := by
  intro E _ _ _ n hn D π hθ ι _ Φ T hΦ hT
  classical
  let X := PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D
  have hr : X.μ.IsMulRightInvariant := D.haar.2.1
  have hdet : ∀ g : GA E n, IsUnit (g : Matrix (Fin n) (Fin n) (Ad E)).det := fun g => by
    simp
  have hldet : ∀ (γ : ratH E n 0) (y : H E n 0), ldet ((γ : H E n 0) * y) = ldet y := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    have hb := PositivityTheory.Rg.BcB.D1.logAbsBasic E
    have hd : ((ratGL E n γ₁ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)).det =
        algebraMap E (Ad E) (γ₁ : Matrix (Fin n) (Fin n) E).det := by
      simp [ratGL, RingHom.map_det]
    have hne : (γ₁ : Matrix (Fin n) (Fin n) E).det ≠ 0 := by
      simpa using (Matrix.GeneralLinearGroup.det γ₁).ne_zero
    simp only [ldet, Prod.fst_mul, h1]
    rw [Units.val_mul, Matrix.det_mul, hb.2.1 _ _ (hdet _) (hdet _), hd, hb.2.2 _ hne, zero_add]
  have hpsi0 : True := trivial
  have hpsi : ∀ ψ ∈ π.V, ∀ (γ : ratH E n 0) (y : H E n 0), ψ.1 ((γ : H E n 0) * y).1 = ψ.1 y.1 := by
    intro ψ hψ γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (π.cusp ψ hψ).1.left γ₁ y.1
  have key : ∀ g : Hs (ι := ι) D, IsPiVec D π g → T g ∈ piSp D π ι := by
    intro g hg
    choose ψ hψ u hu hu' hgu using hg
    set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
    have hinv : ∀ j, ∀ γ : ratH E n 0, ∀ y : H E n 0, Ft j ((γ : H E n 0) * y) = Ft j y := fun j γ y => by
      show (ψ j).1 ((γ : H E n 0) * y).1 * u j (ldet ((γ : H E n 0) * y)) = (ψ j).1 y.1 * u j (ldet y)
      rw [hpsi _ (hψ j) γ y, hldet γ y]
    have hmem : ∀ j, MemLp (Ft j) 2 X.ν := fun j => (Lp.memLp (g j)).ae_eq (hgu j)
    rw [← Submodule.orthogonal_orthogonal (piSp D π ι), Submodule.mem_orthogonal]
    intro h hh
    have hz : ∀ i j (z : H E n 0),
        ∫ x, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) * Ft j (x * z) ∂D.ν = 0 := by
      intro i j z
      have hw := memLp_rt X hr (hinv j) (hmem j) z
      let w : Lp ℂ 2 D.ν := hw.toLp _
      let v : Hs (ι := ι) D := WithLp.toLp 2 (Pi.single i w)
      have hvl : ∀ l, v l = (Pi.single i w : ι → Lp ℂ 2 D.ν) l := fun l => rfl
      have hv : v ∈ piSp D π ι := by
        refine hC E n hn D π hθ ι (fun l => if l = i then ψ j else 0) (fun l => if l = i then u j else 0) z v ?_ ?_
        · intro l
          split_ifs
          · exact ⟨hψ j, hu j, hu' j⟩
          · exact ⟨Submodule.zero_mem _, continuous_zero, HasCompactSupport.zero⟩
        · intro l
          rw [hvl]
          by_cases hl : l = i
          · subst hl
            rw [Pi.single_eq_same]
            filter_upwards [hw.coeFn_toLp] with x hx
            simp only [if_pos rfl]
            exact (show (w : H E n 0 → ℂ) x = Ft j (x * z) from hx)
          · rw [Pi.single_eq_of_ne hl]
            filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := D.ν)] with x hx
            rw [hx]
            simp only [if_neg hl, Submodule.coe_zero, ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul]
      have h0 : ⟪h, v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hv hh
      rw [PiLp.inner_apply, Finset.sum_eq_single i (fun l _ hl => by rw [hvl, Pi.single_eq_of_ne hl, inner_zero_right])
        (fun hi => absurd (Finset.mem_univ i) hi), hvl, Pi.single_eq_same, MeasureTheory.L2.inner_def] at h0
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [hw.coeFn_toLp] with x hx
      rw [show (w : H E n 0 → ℂ) x = Ft j (x * z) from hx, RCLike.inner_apply, mul_comm]
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MeasureTheory.L2.inner_def]
    have hP := fun j => pair_zero X hr PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (hΦ i j) (hinv j) (hmem j)
      (Lp.memLp (h i)) (hz i j)
    calc ∫ x, ⟪(h i : H E n 0 → ℂ) x, (T g i : H E n 0 → ℂ) x⟫_ℂ ∂D.ν
        = ∫ x, ∑ j, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) *
            ∫ y, kerH (Φ i j) x y * Ft j y ∂D.ν ∂D.ν := by
          refine integral_congr_ae ?_
          filter_upwards [hT g i] with x hx
          rw [hx, RCLike.inner_apply, mul_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          exact integral_congr_ae ((hgu j).mono fun y hy => by simp only [hy, hFt])
      _ = ∑ j, ∫ x, starRingEnd ℂ ((h i : H E n 0 → ℂ) x) * ∫ y, kerH (Φ i j) x y * Ft j y ∂D.ν ∂D.ν :=
          integral_finsetSum _ fun j _ => (hP j).1
      _ = 0 := Finset.sum_eq_zero fun j _ => (hP j).2
  intro f hf
  have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π ι).comap (T : Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D) :=
    Submodule.span_le.2 fun g hg => key g hg
  have hcl : IsClosed (((piSp D π ι).comap (T : Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D)) : Set (Hs (ι := ι) D)) :=
    (show IsClosed (piSp D π ι : Set (Hs (ι := ι) D)) from Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact Submodule.topologicalClosure_minimal _ hle hcl hf

end DiscreteGroups.T1.G

end
end

section

set_option linter.all false

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.BcB PositivityTheory.Rg.Rs.JInitBnd

namespace DiscreteGroups.T1.G.CP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem lAbs_mul (x y : GA E n) : logAbs (x * y).val.det = logAbs x.val.det + logAbs y.val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  exact (D1.logAbsBasic E).2.1 _ _ (Matrix.isUnits_det_units x) (Matrix.isUnits_det_units y)

theorem lAbs_one : logAbs (1 : GA E n).val.det = 0 := by
  have h := lAbs_mul (E := E) (n := n) 1 1
  rw [mul_one] at h
  linarith

theorem lAbs_pow (k : GA E n) (m : ℕ) : logAbs (k ^ m).val.det = m * logAbs k.val.det := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact lAbs_one
  | succ m ih => rw [pow_succ, lAbs_mul, ih]; push_cast; ring

theorem eq_zero_of_nat_mul_le {a C : ℝ} (h : ∀ m : ℕ, (m : ℝ) * |a| ≤ C) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.2 ha
  obtain ⟨m, hm⟩ := exists_nat_gt (C / |a|)
  have h1 := h m
  have h2 : C / |a| * |a| < m * |a| := mul_lt_mul_of_pos_right hm hpos
  rw [div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

theorem lAbs_maxCompact {k : GA E n} (hk : k ∈ maxCompact (K := E) (n := n)) : logAbs k.val.det = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_maxCompact (K := E) (n := n)).exists_bound_of_continuousOn
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).continuousOn
  refine eq_zero_of_nat_mul_le (C := C) fun m => ?_
  have h := hC (k ^ m) (pow_mem hk m)
  rw [Real.norm_eq_abs, lAbs_pow, abs_mul, Nat.abs_cast] at h
  exact h

end DiscreteGroups.T1.G.CP

end
end

section

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal Pointwise

namespace DiscreteGroups.T1.G.CP

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def bump (R : ℝ) (s : ℝ) : ℂ := ((max 0 (min 1 (R + 1 - |s|)) : ℝ) : ℂ)

theorem continuous_bump (R : ℝ) : Continuous (bump R) :=
  Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs)))

theorem hasCompactSupport_bump (R : ℝ) : HasCompactSupport (bump R) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun s hs => ?_
  have h : R + 1 < |s| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with h | h
    · have := neg_abs_le s; linarith
    · have := le_abs_self s; linarith
  simp only [bump]
  rw [max_eq_left (min_le_of_right_le (by linarith)), Complex.ofReal_zero]

theorem norm_bump_eq_one {R s : ℝ} (hs : |s| ≤ R) : ‖bump R s‖ = 1 := by
  simp only [bump]
  rw [min_eq_left (by linarith), max_eq_right zero_le_one, Complex.ofReal_one, norm_one]

theorem cp_vol (hn : 1 ≤ n) (D : Dom E n 0) (R : ℝ) : D.ν {x | |ldet x| ≤ R} < ⊤ := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E n (muG D)
  obtain ⟨K, hK, hKs⟩ := tsum_shift_le (bump R) (continuous_bump R) (hasCompactSupport_bump R) _
    (lg_e_pos (E := E) hn)
  have hS : MeasurableSet {x : H E n 0 | |ldet x| ≤ R} := by
    haveI := borelSpace_H (E := E) (n := n)
    exact (isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet
  have h1 : D.ν {x | |ldet x| ≤ R} ≤ ∫⁻ x, ‖bump R (lg x.1)‖ₑ ^ (2 : ℝ) ∂D.ν := by
    rw [← lintegral_indicator_one hS]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x : H E n 0 | |ldet x| ≤ R}
    · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm_eq_enorm, norm_bump_eq_one (s := lg x.1) hx,
        ENNReal.ofReal_one, ENNReal.one_rpow]
    · rw [indicator_of_notMem hx]
      exact zero_le
  have h2 : ∫⁻ x, ‖bump R (lg x.1)‖ₑ ^ (2 : ℝ) ∂D.ν =
      ∫⁻ g in stdDom (ratGL E n).range, ‖bump R (lg g)‖ₑ ^ (2 : ℝ) ∂muG D :=
    lintegral_nu D (fun g => ‖bump R (lg g)‖ₑ ^ (2 : ℝ)) fun γ hγ g => by rw [lg_rat_mul γ hγ g]
  have h3 : ∫⁻ g in stdDom (ratGL E n).range, ‖bump R (lg g)‖ₑ ^ (2 : ℝ) ∂muG D =
      ∫⁻ q, ∑' m : ℤ, ‖bump R (lg q.out + m * lg (splitCentre E n 1))‖ₑ ^ (2 : ℝ)
        ∂quotMeasure (latticeGL E n) (muG D) := by
    have h := lintegral_unfold (muG D) hn (fun _ => 1) (by intro _ _ _; rfl) aemeasurable_const
      (fun s => ‖bump R s‖ₑ ^ (2 : ℝ)) ((continuous_bump R).measurable.enorm.pow_const _)
    simpa only [one_mul] using h
  calc D.ν {x | |ldet x| ≤ R} ≤ _ := h1
    _ = _ := h2
    _ = _ := h3
    _ ≤ ∫⁻ _q, K ∂quotMeasure (latticeGL E n) (muG D) := lintegral_mono fun q => hKs _
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top hK.lt_top (measure_lt_top _ _)

end DiscreteGroups.T1.G.CP

end
end
