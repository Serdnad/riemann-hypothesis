module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import GroundTheory.AutomorphicForms.Bundle017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle414
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle412
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle415
import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle416
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.ChiGamGlobal

theorem twConj_cent_mul {G : Type} [Group G] (θ : Monoid.End G) {t δ : G} (x : G) (ht : twConj θ t δ = δ) :
    twConj θ (t * x) δ = twConj θ x δ := by
  have h : t⁻¹ * δ * θ t = δ := ht
  calc twConj θ (t * x) δ = x⁻¹ * (t⁻¹ * δ * θ t) * θ x := by
        simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    _ = twConj θ x δ := by rw [h]; rfl

theorem logSize_nonneg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (g : GA E n) :
    0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
      (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

theorem chiGam_of (hI : OnlyIsotropic) (hP : PosY) (hC : ChainSum) : ChiGam := by
  classical
  intro E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hI E n
  obtain ⟨C₂, h₂⟩ := hP E n
  refine ⟨max C₁ C₂, fun d m Wof a hiso huniq h0 hmeet hle hreg hdeg τ x hτ t ht => ?_⟩
  have hs : 0 ≤ 1 + logSize (twConj (thetaA E n) x (ratGL E n d)) := by
    have := logSize_nonneg (twConj (thetaA E n) x (ratGL E n d))
    linarith
  have b₁ := (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hs).trans hτ
  have b₂ := (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hs).trans hτ
  have hconj : twConj (thetaA E n) (t * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) :=
    twConj_cent_mul _ x ht
  have hind := (hC m).1 _ (a t) (h₂ d m Wof hiso huniq h0 hmeet hle hreg τ x b₂)
  have hiff : t * x ∈ cutSet E n τ ↔
      ∀ e, sdot e (a t) ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e) := by
    rw [h₁ τ (t * x) d (by rw [hconj]; exact b₁)]
    constructor
    · intro h e
      have := h (Wof e) (hiso e).1 (hiso e).2
      rw [hdeg t ht x e] at this
      linarith
    · intro h W hW₁ hW₂
      obtain ⟨e, rfl, _⟩ := huniq W ⟨hW₁, hW₂⟩
      have := h e
      rw [hdeg t ht x e]
      linarith
  rw [hind]
  by_cases hx : t * x ∈ cutSet E n τ
  · have ha : a t ∈ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      hiff.1 hx
    rw [Set.indicator_of_mem ha, chiT, Set.indicator_of_mem hx]
    simp
  · have ha : a t ∉ {b : Fin m → ℝ | ∀ e, sdot e b ≤ prof n τ (Module.finrank E (Wof e)) - deg x (Wof e)} :=
      fun h => hx (hiff.2 h)
    rw [Set.indicator_of_notMem ha, chiT, Set.indicator_of_notMem hx]
    simp

end GlobalTheory.CompanionTheory.ChiGamGlobal

end
end

section

noncomputable section

open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LatticeSum

theorem tsum_prod_eq_pow (g : ℤ → ℝ≥0∞) (n : ℕ) :
    ∑' m : Fin n → ℤ, ∏ i, g (m i) = (∑' k, g k) ^ n :=
  _root_.UpperTheory.Reformulated.B.Yvb3.main g n

def wt (k : ℤ) : ℝ := ((1 + |(k : ℝ)|) ^ 2)⁻¹

theorem wt_nonneg (k : ℤ) : 0 ≤ wt k := by
  unfold wt; positivity

theorem summable_nat_wt : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have h : Summable fun k : ℕ => ((k : ℝ) ^ 2)⁻¹ := by
    simpa [one_div] using (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have h1 := (summable_nat_add_iff 1).2 h
  simpa using h1

theorem summable_wt : Summable wt := by
  apply Summable.of_nat_of_neg
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]
  · refine summable_nat_wt.congr fun k => ?_
    simp [wt, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) k), add_comm]

theorem pointwise_le (n M : ℕ) (h : 2 * n ≤ M) (m : Fin n → ℤ) :
    (1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ)) ≤ ∏ i, wt (m i) := by
  set N : ℝ := 1 + ‖fun i => (m i : ℝ)‖ with hN
  have hN1 : 1 ≤ N := by
    have := norm_nonneg (fun i => (m i : ℝ))
    linarith
  have hN0 : 0 < N := by linarith
  have hle : ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ N ^ M := by
    calc ∏ i, (1 + |(m i : ℝ)|) ^ 2 ≤ ∏ _i : Fin n, N ^ 2 := by
          apply Finset.prod_le_prod₀
          · intro i _; positivity
          · intro i _
            have h1 : |(m i : ℝ)| ≤ ‖fun i => (m i : ℝ)‖ := by
              simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun i => (m i : ℝ)) i
            have h2 : 1 + |(m i : ℝ)| ≤ N := by rw [hN]; linarith
            exact pow_le_pow_left₀ (by positivity) h2 2
      _ = N ^ (2 * n) := by simp [Finset.prod_const, pow_mul]
      _ ≤ N ^ M := pow_le_pow_right₀ hN1 h
  have hpos : 0 < ∏ i, (1 + |(m i : ℝ)|) ^ 2 := Finset.prod_pos fun i _ => by positivity
  have hw : ∏ i, wt (m i) = (∏ i, (1 + |(m i : ℝ)|) ^ 2)⁻¹ := by
    simp only [wt, Finset.prod_inv_distrib]
  rw [hw, zpow_neg, zpow_natCast]
  exact inv_anti₀ hpos hle

theorem latSum : PositivityTheory.Rg.BcB.E1.LatSum := by
  intro n M h
  have hS : ∑' k, ENNReal.ofReal (wt k) ≠ ⊤ := summable_wt.tsum_ofReal_ne_top
  have hle : ∑' m : Fin n → ℤ, ENNReal.ofReal ((1 + ‖fun i => (m i : ℝ)‖) ^ (-(M : ℤ))) ≤
      ∑' m : Fin n → ℤ, ∏ i, ENNReal.ofReal (wt (m i)) := by
    refine ENNReal.tsum_le_tsum fun m => ?_
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => wt_nonneg (m i)]
    exact ENNReal.ofReal_le_ofReal (pointwise_le n M h m)
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top hS)
    (hle.trans_eq (tsum_prod_eq_pow (fun k => ENNReal.ofReal (wt k)) n))

end GlobalTheory.CompanionTheory.LatticeSum

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.TorNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem norm_cV (v : InfinitePlace E) (u : Ad E) : ‖cV v u‖ = ‖u.1 v‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v))) _

theorem cW_posIdele (w : HeightOneSpectrum (𝓞 E)) (ρ : ℝ) (hρ : 0 < ρ) :
    cW w ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E) = 1 :=
  posIdele_finite ρ hρ w

theorem norm_cV_posIdele (v : InfinitePlace E) (ρ : ℝ) (hρ : 0 < ρ) :
    ‖cV v ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E)‖ = ρ := by
  rw [norm_cV]; exact norm_posIdele_infinite ρ hρ v

theorem two_card : 2 * (Fintype.card (InfinitePlace E) : ℝ) = Module.finrank ℚ E := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero]
  push_cast; ring

theorem logAbs_of (u : Ad E) (t : ℝ) (h1 : ∀ v, ‖cV v u‖ = Real.exp t) (h2 : ∀ w, ‖cW w u‖ = 1) :
    logAbs u = Module.finrank ℚ E * t := by
  have : ∀ v : InfinitePlace E, Real.log (‖cV v u‖ ^ 2) = 2 * t := fun v => by
    rw [h1, Real.log_pow, Real.log_exp]; norm_num
  simp only [logAbs, this, h2, Real.log_one, finsum_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_zero]
  rw [← two_card]; ring

theorem tor_neg {n : ℕ} (x : Fin n → ℝ) : (An.tor E x : GA E n)⁻¹ = An.tor E (-x) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  have : ∀ i, posIdele (K := E) (Real.exp ((-x) i)) (Real.exp_pos _) * posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) = 1 := fun i => by
    have h : (⟨Real.exp ((-x) i), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) *
        ⟨Real.exp (x i), Real.exp_pos _⟩ = 1 := by
      apply Subtype.ext
      simp [← Real.exp_add]
    have := congrArg (posIdeleHom E) h
    simpa only [map_mul, map_one, posIdeleHom_apply] using this
  change diagUnits n _ * diagUnits n _ = 1
  rw [← map_mul]
  convert map_one (diagUnits n (R := Ad E))
  exact funext this

theorem logSizeM_tor {n : ℕ} (x : Fin n → ℝ) :
    logSizeM (An.tor E x : GA E n).val ≤ Module.finrank ℚ E * ‖x‖ := by
  have entry : ∀ i j, (An.tor E x : GA E n).val i j =
      if i = j then ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) else 0 := fun i j => by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val i j = _
    rw [coe_diagUnits, Matrix.diagonal_apply]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have inf : ∀ v : InfinitePlace E,
      Real.posLog (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ 2 * ‖x‖ := fun v => by
    have hle : (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ Real.exp (2 * ‖x‖) := by
      refine Real.iSup_le (fun p => ?_) (Real.exp_pos _).le
      rw [entry]
      split_ifs
      · rw [norm_cV_posIdele, ← Real.exp_nat_mul]
        have : x p.1 ≤ ‖x‖ := (le_abs_self _).trans (norm_le_pi_norm x p.1)
        exact Real.exp_le_exp.2 (by push_cast; linarith)
      · simp [(Real.exp_pos _).le]
    calc _ ≤ Real.posLog (Real.exp (2 * ‖x‖)) :=
          Real.posLog_le_posLog (le_trans (by norm_num) (Real.iSup_nonneg fun _ => by positivity)) hle
      _ = 2 * ‖x‖ := by
          rw [Real.posLog, Real.log_exp]
          exact max_eq_right (by positivity)
  have fin : ∀ w : HeightOneSpectrum (𝓞 E),
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w ((An.tor E x : GA E n).val p.1 p.2)‖) = 0 := fun w => by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)]
    refine Real.iSup_le (fun p => ?_) zero_le_one
    rw [entry]
    split_ifs
    · rw [cW_posIdele, norm_one]
    · simp
  unfold logSizeM
  simp only [fin, finsum_zero, add_zero]
  calc _ ≤ ∑ _v : InfinitePlace E, 2 * ‖x‖ := Finset.sum_le_sum fun v _ => inf v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← two_card]; ring

theorem logAbs_det_tor {n : ℕ} (x : Fin n → ℝ) :
    logAbs (An.tor E x : GA E n).val.det = Module.finrank ℚ E * ∑ i, x i := by
  have d : (An.tor E x : GA E n).val.det =
      ∏ i, ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) := by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val.det = _
    rw [coe_diagUnits, det_diagonal]
  rw [d]
  refine logAbs_of _ _ (fun v => ?_) (fun w => ?_)
  · rw [map_prod, norm_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => norm_cV_posIdele v _ _
  · rw [map_prod, norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [cW_posIdele, norm_one]

theorem torNorm : LogAbsBasic → TorNorm := fun _ E _ _ _ =>
  ⟨fun t => logAbs_of _ t (fun v => norm_cV_posIdele v _ _) (fun w => by rw [cW_posIdele, norm_one]),
    fun n x => ⟨logAbs_det_tor x, by
      have h1 := logSizeM_tor (E := E) x
      have h2 := logSizeM_tor (E := E) (-x)
      rw [norm_neg] at h2
      rw [logSize, tor_neg]
      linarith⟩⟩

end GlobalTheory.CompanionTheory.TorNorm
end
end

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_inG : InG (JJ n) := by
  have hc : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  show (JJ n)ᴴ * JJ n * JJ n = JJ n
  rw [hc, Matrix.mul_assoc, JJ_mul_JJ]
  simp

def JG : GR n :=
  ⟨⟨JJ n, -JJ n, by simp [JJ_mul_JJ], by simp [JJ_mul_JJ]⟩, JJ_inG⟩

theorem lower_mul_JG (y : GR n) :
    (mR (y * JG)).toBlocks₂₁ = -(mR y).toBlocks₂₂ := by
  have h : mR (y * JG) = mR y * JJ n := rfl
  rw [h, ← Matrix.fromBlocks_toBlocks (mR y)]
  unfold JJ
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

theorem dense_bigCell₂₂ : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} := by
  intro n
  have hset : {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} =
      (fun y => y * (JG (n := n))) ⁻¹' {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, lower_mul_JG, Matrix.det_neg]
    constructor
    · intro h
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
    · intro h h0
      exact h (by rw [h0, mul_zero])
  rw [hset]
  exact (dense_bigCell n).preimage (isOpenMap_mul_right _)

end GlobalTheory.CompanionTheory.BigCell
end
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.bruhat_cell_parabolic_unipotent_factorization : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  first | exact @GlobalTheory.CompanionTheory.DCell.main | exact GlobalTheory.CompanionTheory.DCell.main | (intros; apply GlobalTheory.CompanionTheory.DCell.main <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

theorem _root_.GlobalTheory.T.hecke_operator_coset_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (g : GL (Fin N) k) (T : Module.End ℂ (fixed π J)), IsHeckeOp π J g T → ∀ (r : ℕ) (x : Fin r → GL (Fin N) k), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((T v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average | exact GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average | (intros; apply GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.EisTerm

theorem flat_norm_le_height_rpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} (K : Subgroup (G2 σ Y))
    (a : G2 σ Y → ℝ) (hK : IsCompact (K : Set (G2 σ Y))) (hH : IsHgt K a) (ha : ∀ x, 0 < a x)
    (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ C : ℝ, ∀ (s : ℂ) (x : G2 σ Y), ‖flat a f s₁ s x‖ ≤ C * a x ^ (s.re + (n : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun s x => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := hH.iwa x
  have hpos := ha (p * k)
  have hval := hH.val p t hp k hk
  have hlaw := hf.law p t k hp
  have hfk : ‖f (p * k)‖ = a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖ := by
    have h1 : ‖(χ (Matrix.GeneralLinearGroup.det t) : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
        | exact mem_sphere_zero_iff_norm.mp (χ (Matrix.GeneralLinearGroup.det t)).2
    rw [hlaw, ← hval, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, h1, one_mul]
    congr 2
    simp
  have e1 : a (p * k) ^ (s.re + (n : ℝ) / 2) =
      a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add hpos]
    congr 1
    rw [Complex.sub_re]
    ring
  show ‖((a (p * k) : ℝ) : ℂ) ^ (s - s₁) * f (p * k)‖ ≤ _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, hfk, e1]
  have h0 : 0 ≤ a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hpos.le _) (Real.rpow_nonneg hpos.le _)
  calc a (p * k) ^ ((s - s₁).re) * (a (p * k) ^ (s₁.re + (n : ℝ) / 2) * ‖f k‖)
      = (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * ‖f k‖ := by ring
    _ ≤ (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) * C :=
      mul_le_mul_of_nonneg_left (hC k hk) h0
    _ = C * (a (p * k) ^ ((s - s₁).re) * a (p * k) ^ (s₁.re + (n : ℝ) / 2)) := by ring

end GlobalTheory.CompanionTheory.EisTerm
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix


theorem _root_.GlobalTheory.T.compact_adelic_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (C : Set (Af F ⊗[F] E)), IsCompact C → ∃ d : ℕ, 0 < d ∧ ∀ x : E, (1 : Af F) ⊗ₜ[F] x ∈ C → ∃ y : 𝓞 E, (d : E) * x = y := by
  first | exact @GlobalTheory.CompanionTheory.AdelicDenom.exists_denominator_of_isCompact | exact GlobalTheory.CompanionTheory.AdelicDenom.exists_denominator_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.AdelicDenom.exists_denominator_of_isCompact <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.integers_bounded_embeddings_count : ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
    {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R}.Finite ∧
    (Set.ncard {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} : ℝ) ≤ C * R ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.IntegerCount.card_bounded_conjugates_le | exact GlobalTheory.CompanionTheory.IntegerCount.card_bounded_conjugates_le | (intros; apply GlobalTheory.CompanionTheory.IntegerCount.card_bounded_conjugates_le <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

theorem _root_.GlobalTheory.T.summable_height_pow_of_polynomial_count : ∀ (Q : Type) (h : Q → ℝ), (∀ q, 1 ≤ h q) → ∀ (C : ℝ) (c : ℕ),
    (∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C * T ^ c) → ∀ s : ℝ, (c : ℝ) < s →
    Summable fun q => h q ^ (-s) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.summable_rpow_neg_of_polynomial_count | exact GlobalTheory.CompanionTheory.GodementH.summable_rpow_neg_of_polynomial_count | (intros; apply GlobalTheory.CompanionTheory.GodementH.summable_rpow_neg_of_polynomial_count <;> assumption)
end
