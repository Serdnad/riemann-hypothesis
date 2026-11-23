module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle175
import Aesop.Main
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle180
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle172
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle178
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Topology Matrix
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def linM {k r : ℕ} (A Bb : B.Mat k r) : Mt k r →ₗ[ℝ] Mt k r :=
  ((LinearMap.mulLeft ℝ A).comp (LinearMap.mulRight ℝ Bb) : B.Mat k r →ₗ[ℝ] B.Mat k r)

theorem linM_apply {k r : ℕ} (A Bb : B.Mat k r) (v : Mt k r) :
    (Matrix.of (linM A Bb v) : B.Mat k r) = A * Matrix.of v * Bb := by
  show A * ((Matrix.of v : B.Mat k r) * Bb) = _
  rw [Matrix.mul_assoc]

theorem aCSmooth_of_proper (hP : ACProper) : ACSmooth := by
  intro k r Wp Wq _ _ _ _ D φ₀ hφ hφc hφs g₀ hg₀

  obtain ⟨ε₀, hε₀, hball⟩ :=
    Metric.mem_nhds_iff.1 ((Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open D.z D.z').mem_nhds hg₀.2)
  have hε : 0 < ε₀ / 2 := by positivity
  have hCb : Metric.closedBall g₀ (ε₀ / 2) ⊆ Q.OmPlus k r D.z D.z' := fun x hx =>
    hball (Metric.closedBall_subset_ball (by linarith) hx)
  have hC'c : IsCompact (Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r) :=
    (isCompact_closedBall g₀ (ε₀ / 2)).inter_right Formalism.FourierDecayAlt.P.B5.GV_closed
  have hC'O : Metric.closedBall g₀ (ε₀ / 2) ∩ B.GV k r ⊆ JF.Om k r D.z D.z' := fun x hx => ⟨hx.2, hCb hx.1⟩
  obtain ⟨P, hPc, hPp⟩ := hP k r Wp Wq D (tsupport φ₀) _ hφc hC'c hC'O

  set Am : B.SS k r → B.Mat k r := fun p =>
    (Hpk k r * (Matrix.of p.1.1 : B.Mat k r)ᴴ * Hpk k r) * (Hpk k r * (Matrix.of p.1.2 : B.Mat k r)ᴴ * Hpk k r)
    with hAm
  set Bm : B.SS k r → B.Mat k r := fun p => (Matrix.of p.2.2 : B.Mat k r) * Matrix.of p.2.1 with hBm
  have hsgs : ∀ p, D.inSS p → ∀ g, B.sgs p g = Am p * g * Bm p := by
    intro p hp g
    show (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1 = _
    rw [Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.1.1, Formalism.FourierDecayAlt.P.Qx3.uh_inv_eq hp.2.1.1]
    simp only [hAm, hBm, Matrix.mul_assoc]
  have hof : Continuous (fun ν : Mt k r => (Matrix.of ν : B.Mat k r)) := continuous_id
  have hAc : Continuous Am := by
    have h1 : Continuous (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)) := hof.comp continuous_fst.fst
    have h2 : Continuous (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)) := hof.comp continuous_fst.snd
    exact ((continuous_const.mul h1.matrix_conjTranspose).mul continuous_const).mul
      ((continuous_const.mul h2.matrix_conjTranspose).mul continuous_const)
  have hBc : Continuous Bm := by
    have h3 : Continuous (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) := hof.comp continuous_snd.snd
    have h4 : Continuous (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) := hof.comp continuous_snd.fst
    exact h3.mul h4
  have hcont : Continuous (fun p : B.SS k r => B.gN (Am p) * B.gN (Bm p)) :=
    (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hAc).mul (Formalism.FourierDecayAlt.P.B6.gN_continuous.comp hBc)
  obtain ⟨M₁, hM₁⟩ := hPc.exists_bound_of_continuousOn hcont.continuousOn
  set L : B.SS k r → (Mt k r →L[ℝ] Mt k r) := fun p => LinearMap.toContinuousLinearMap (linM (Am p) (Bm p))
    with hLdef
  have hL : ∀ p (v : Mt k r), (Matrix.of (L p v) : B.Mat k r) = Am p * Matrix.of v * Bm p := fun p v =>
    linM_apply (Am p) (Bm p) v
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := by positivity
  set ML : ℝ := nn * max M₁ 0 with hML
  have hML0 : 0 ≤ ML := mul_nonneg hnn0 (le_max_right _ _)
  have hLn : ∀ p ∈ P, ‖L p‖ ≤ ML := by
    intro p hp
    apply ContinuousLinearMap.opNorm_le_bound _ hML0
    intro v
    have e1 : ‖L p v‖ = ‖(Matrix.of (L p v) : B.Mat k r)‖ := rfl
    have e2 : ‖v‖ = ‖(Matrix.of v : B.Mat k r)‖ := rfl
    rw [e1, e2, hL]
    set g : B.Mat k r := Matrix.of v
    have hgA := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Am p)
    have hgB := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg (Bm p)
    have hgg := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_nonneg g
    have hgn : B.gN g ≤ nn * ‖g‖ :=
      Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.gN_le_of_ent g ‖g‖ (norm_nonneg _) (fun i j => Matrix.norm_entry_le_entrywise_sup_norm g)
    have hAB : B.gN (Am p) * B.gN (Bm p) ≤ max M₁ 0 := by
      have := hM₁ p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hgA hgB)] at this
      exact this.trans (le_max_left _ _)
    calc ‖Am p * g * Bm p‖ ≤ B.gN (Am p * g * Bm p) := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN _
      _ ≤ B.gN (Am p * g) * B.gN (Bm p) := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ (B.gN (Am p) * B.gN g) * B.gN (Bm p) :=
          mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) hgB
      _ = (B.gN (Am p) * B.gN (Bm p)) * B.gN g := by ring
      _ ≤ max M₁ 0 * (nn * ‖g‖) := mul_le_mul hAB hgn hgg (le_max_right _ _)
      _ = ML * ‖g‖ := by rw [hML]; ring

  set φ₁ : Mt k r → ℝ := fun v => φ₀ (Matrix.of v) with hφ₁def
  have hφ₁ : ContDiff ℝ ∞ φ₁ := hφ
  have hφ₁c : HasCompactSupport φ₁ := hφc
  have hK : ∀ i : ℕ, ∃ K : ℝ, ∀ x, ‖iteratedFDeriv ℝ i φ₁ x‖ ≤ K := fun i =>
    (hφ₁.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support (hφ₁c.iteratedFDeriv i)
  choose K hKb using hK

  set F : B.SS k r → Mt k r → ℝ := fun p y => P.indicator (fun p => φ₁ (L p y)) p with hF
  have hFin : ∀ p ∈ P, F p = φ₁ ∘ (L p) := fun p hp => by
    funext y; simp [hF, hp]
  have hFout : ∀ p ∉ P, F p = fun _ => 0 := fun p hp => by
    funext y; simp [hF, hp]

  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  have : IsFiniteMeasureOnCompacts D.μW := ⟨D.haarW.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨D.haarN.finite_compact⟩
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨D.haarW'.finite_compact⟩
  have : IsFiniteMeasureOnCompacts (D.μW.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts (D.μW'.prod D.μN) := inferInstance
  have : IsFiniteMeasureOnCompacts D.μSS := by
    show IsFiniteMeasureOnCompacts ((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
    infer_instance
  have hPfin : D.μSS P ≠ ⊤ := (hPc.measure_lt_top (μ := D.μSS)).ne
  have hPm : MeasurableSet P := hPc.isClosed.measurableSet
  have hFm : ∀ y, AEStronglyMeasurable (fun p => F p y) D.μSS := by
    intro y
    have hc : Continuous (fun p => φ₁ (L p y)) := by
      have : (fun p => φ₁ (L p y)) = fun p => φ₀ (Am p * Matrix.of y * Bm p) := by
        funext p; simp only [hφ₁def]; rw [hL]
      rw [this]
      exact hφ.continuous.comp ((hAc.mul continuous_const).mul hBc)
    exact (hc.measurable.indicator hPm).aestronglyMeasurable
  have hsm : ContDiffOn ℝ ∞ (fun y => ∫ p, F p y ∂D.μSS) (Metric.ball (Matrix.of.symm g₀ : Mt k r) (ε₀ / 2)) := by
    rw [contDiffOn_infty]
    intro N
    set Kt : ℝ := (∑ i ∈ Finset.range (N + 1), |K i|) * (max ML 1) ^ N with hKt
    have hb : Integrable (P.indicator fun _ => Kt) D.μSS :=
      (integrableOn_const hPfin).integrable_indicator hPm
    refine (Formalism.FourierDecayAlt.P.Ux10.pint Metric.isOpen_ball (P.indicator fun _ => Kt) hb N ℝ F ?_ (fun y _ => hFm y) ?_).1
    · intro p
      by_cases hp : p ∈ P
      · rw [hFin p hp]
        exact (hφ₁.comp (L p).contDiff).contDiffOn.of_le (mod_cast le_top)
      · rw [hFout p hp]; exact contDiffOn_const
    · intro i hi y _ p
      by_cases hp : p ∈ P
      · rw [hFin p hp, ContinuousLinearMap.iteratedFDeriv_comp_right (L p) hφ₁ y (mod_cast le_top)]
        simp only [Set.indicator_of_mem hp]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have h1 : ‖iteratedFDeriv ℝ i φ₁ (L p y)‖ ≤ ∑ j ∈ Finset.range (N + 1), |K j| :=
          (hKb i _).trans ((le_abs_self _).trans
            (Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
        have h2 : ‖L p‖ ^ i ≤ (max ML 1) ^ N :=
          (pow_le_pow_left₀ (norm_nonneg _) ((hLn p hp).trans (le_max_left _ _)) i).trans
            (pow_le_pow_right₀ (le_max_right _ _) hi)
        exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _)
          (Finset.sum_nonneg fun j _ => abs_nonneg _)
      · rw [hFout p hp, iteratedFDeriv_fun_zero]
        simp [Set.indicator_of_notMem hp]
  refine ⟨Metric.ball g₀ (ε₀ / 2), fun g => ∫ p, F p (Matrix.of.symm g) ∂D.μSS, Metric.isOpen_ball,
    Metric.mem_ball_self hε, hsm, ?_⟩
  intro g hg hgG
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
  by_cases hpP : p ∈ P
  · have e : φ₁ (L p (Matrix.of.symm g)) = φ₀ (Am p * g * Bm p) := by
      simp only [hφ₁def]; rw [hL]; rfl
    simp only [hF, Set.indicator_of_mem hpP, e, hsgs p hp g]
  · have h0 : φ₀ (B.sgs p g) = 0 := by
      by_contra hne
      exact hpP (hPp p hp g ⟨Metric.ball_subset_closedBall hg, hgG⟩ (subset_tsupport _ hne))
    simp [hF, hpP, h0]

theorem averaging_smoothness_holds : ACSmooth := aCSmooth_of_proper averaging_properness_holds

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem asm_omLong_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (β : ℂ) (Φ : G.Mat 1 → V) (z : ℂ) :
    G.OmLong β 0 Φ z = Φ (fun _ _ => z) := by
  unfold G.OmLong
  have : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  have hμ : G.muPi β (G.UT (0 + 1)) = Measure.dirac (fun q => isEmptyElim q) := Measure.pi_of_empty _ _
  rw [hμ, integral_dirac]
  have h1 : G.superSum (G.upper (fun q : G.UT (0 + 1) => isEmptyElim q)) = 0 := by
    simp [G.superSum]
  have h2 : (G.ptLong (0 + 1) z * G.upper (fun q : G.UT (0 + 1) => isEmptyElim q) : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.of fun _ _ => z := by
    ext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.ptLong, G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  rw [h1, h2]
  simp [G.psi]
  rfl

theorem asm_psi_cast {a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) (cc : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h z) cc (D.castM h g) = psi k a z cc g := by
  subst h; rw [P.JCTx5.castV_rfl, P.JCTx5.castM_rfl]

theorem asm_castM_mul {a b : ℕ} (h : a = b) (g g' : B.Mat k a) : D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_inv {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_castM {a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem asm_castM_symm {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h.symm (D.castM h g) = g := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_lowV_lift (a ρ m r : ℕ) (hm : 1 + ρ = m) (h1 : a + m = r) (h5 : a + 1 + ρ = a + (1 + ρ))
    (er : r = a + 1 + ρ) (zj : Fin (2 * m + k + 1) → ℂ) :
    U.lowV k a (1 + ρ) (D.castV h5 (D.castV er (D.castV h1 (liftVec k a m zj)))) = D.castV hm.symm zj := by
  subst hm; subst h1
  funext i
  simp only [U.lowV, D.castV, liftVec, Fin.val_cast]
  rw [dite_eq_left (by omega)]
  congr 1; ext; simp

theorem asm_phiFun_lev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {a r ρa ρb : ℕ} (e : ρa = ρb)
    (ha : r = a + 0 + ρa) (hb : r = a + 0 + ρb) (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (z0 z0' : Fin (2 * r + k + 1) → ℂ) (F0 : B.Mat k r → E) (g : B.Mat k ρa) :
    U.PhiFun (s := 0) k ρa σ d (D.castV ha z0) (D.castV ha z0') (D.castF ha.symm F0) (fun q => q.elim0) g =
      U.PhiFun (s := 0) k ρb σ d (D.castV hb z0) (D.castV hb z0') (D.castF hb.symm F0) (fun q => q.elim0)
        (D.castM e g) := by
  subst e; rw [P.JCTx5.castM_rfl]

theorem asm_bridge {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a ρ1 ρ2 m r : ℕ) (e12 : ρ1 = ρ2) (e : ρ2 + 1 = m) (er : r = a + 1 + ρ1)
    (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (zb zb' : Fin (2 * r + k + 1) → ℂ) (zj zj' : Fin (2 * m + k + 1) → ℂ)
    (hzj : D.castV (show a + m = r by omega) (liftVec k a m zj) = zb)
    (hzj' : D.castV (show a + m = r by omega) (liftVec k a m zj') = zb')
    (Fb : B.Mat k r → E) (c : ℂ) (γ : B.Mat k ρ2)
    (zA zA' : Fin (2 * (a + 1 + ρ1) + k + 1) → ℂ) (hzA : zA = D.castV er zb) (hzA' : zA' = D.castV er zb')
    (FA : B.Mat k (a + 1 + ρ1) → E) (hFA : FA = D.castF er.symm Fb) (γ1 : B.Mat k ρ1)
    (hγ1 : γ1 = D.castM e12.symm γ) :
    ∫ yy : U.RC k 1 ρ1 × U.RC k 1 ρ1,
        (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)) cStd
            (U.Rn k 1 ρ1 yy.1) *
          star (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA')) cStd
            (U.Rn k 1 ρ1 yy.2))) •
        U.PhiFun (p := a) (s := 0) k (1 + ρ1) σ d (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)
          (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA') (D.castF (by omega : a + (1 + ρ1) = a + 1 + ρ1) FA)
          (fun q => q.elim0)
          ((U.Rn k 1 ρ1 yy.1)⁻¹ * U.mMap k 1 ρ1 (Matrix.of fun _ _ => c) γ1 * U.Rn k 1 ρ1 yy.2)
        ∂((U.muRC k 1 ρ1).prod (U.muRC k 1 ρ1)) =
      ∫ xx : U.RC k 1 ρ2 × U.RC k 1 ρ2,
        (psi k m zj cStd (rn1 e xx.1) * star (psi k m zj' cStd (rn1 e xx.2))) •
          U.PhiFun (p := a) (s := 0) k (r - a) σ d (D.castV (by omega : r = a + 0 + (r - a)) zb)
            (D.castV (by omega : r = a + 0 + (r - a)) zb') (D.castF (by omega : a + 0 + (r - a) = r) Fb)
            (fun q => q.elim0)
            (D.castM (by omega : m = r - a) ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2))
        ∂((U.muRC k 1 ρ2).prod (U.muRC k 1 ρ2)) := by
  subst e12; subst e; subst hzA; subst hzA'; subst hFA; subst hγ1; subst er
  rw [P.JCTx5.castM_rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  simp only [rn1, mc, P.JCTx5.castM_rfl]
  have hl := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj
  have hl' := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj'
  subst hzj; subst hzj'
  rw [hl, hl', ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.1),
    ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.2)]
  congr 1
  rw [← asm_castM_inv, ← asm_castM_mul, ← asm_castM_mul, asm_castM_castM]
  exact asm_phiFun_lev (by omega) _ _ σ d _ _ _ _

theorem asm_pointStepT (hPS : PointStep) : PointStepT := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ
  obtain ⟨hhb, rfl⟩ := hh
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hP' : D.ptSize (h ++ [(1, c)]) = D.ptSize h + 1 := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h 1 c
  have hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])) := ⟨hc.1, rfl⟩
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨hhb, rfl⟩
  have hle : D.ptSize (h ++ [(1, c)]) ≤ P.r := by omega
  have e2 : D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])) = P.r := by omega
  have hFs : B.CkOn ⊤ (B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])))) (D.castF e2 F) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hF.1
  obtain ⟨R, hR⟩ := hF.2.1
  have hRs : ∀ g ∈ B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)]))), D.castF e2 F g ≠ 0 →
      B.gN g ≤ R := fun g hg hne => by
    have := hR _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne
    rwa [Formalism.FourierDecayAlt.P.PBE.gN_castM] at this
  have hγ' : D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ ∈
      B.GV P.k (P.r - D.ptSize (h ++ [(1, c)])) := Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  have hI := asm_gInt_int (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c hd0 hc0
    (D.castV e2.symm p.T.base.z) (D.castV e2.symm p.T.base.z') (D.castF e2 F) hFs R hRs _ hγ'
  have hS := Formalism.FourierDecayAlt.P.slice_measure_identity P.k P.r (Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' F h (h ++ [(1, c)]) 0 c rfl hle
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) hloc
    (integrable_slice_append_single p.T.base.z p.T.base.z' F h c hle hloc _ hI)
  rw [asm_omLong_zero] at hS
  have hPS' := hPS P.k (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) hd0 c hc0
    (D.castV (by omega) p.T.base.z) (D.castV (by omega) p.T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z'_mem)
    (Wq →L[ℂ] Wp) (D.castF (by omega) F)
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ)
    (integrable_unipotent_rank_one (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c _ _ _ _ hI)
  have hB := asm_bridge (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (P.r - (D.ptSize h + 1))
    (P.r - D.ptSize h) P.r (by omega) (by omega) (by omega) (D.ptPerm h) (D.ptDiag h) p.T.base.z p.T.base.z'
    (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' (p.T.z_lev _ (by omega)) (p.T.z'_lev _ (by omega)) F c γ
    _ _ rfl rfl _ rfl _ rfl
  have hπ : ((Real.pi ^ ((0 + 1) * 0 / 2) : ℝ) : ℂ) = 1 := by norm_num
  rw [hπ, one_smul] at hS
  refine ((show KB.slv p.T F (D.ptSize h + 1) hj [] (h ++ [(1, c)]) hc.2 (fun a => a.elim0) γ =
      D.sliceAt P.k P.r p.T.base.z p.T.base.z' F (h ++ [(1, c)])
        (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) from rfl).trans
    (hS.trans (hPS'.trans (hB.trans ?_))))
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  dsimp only
  congr 1
  show _ = D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h (D.castM _ _)
  unfold D.sliceAt
  rw [dite_eq_left (by omega)]

end Formalism.FourierDecayAlt.P.PBH
end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem firstSt_inj {w : List C.Letter} : ∀ ys : List ℝ, Function.Injective (KB.firstSt (w := w) ys)
  | [] => fun _ _ h => h
  | _ :: ys => fun e e' h => firstSt_inj ys (Fin.cons_right_injective (α := fun _ => Fin 2) (0 : Fin 2) h)

theorem lam_sum_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.abs_prod _ _

theorem lam_sum_pos {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    0 < ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| := by
  rw [lam_sum_eq]
  refine Finset.prod_pos fun b _ => ?_
  exact lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) 0))
    (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ 0))

theorem thGrid_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (n : Fin K → Fin (d + 1)) :
    F7.thGrid grid n = |∏ b, F7.lagCo (grid b) (n b)| / ∑ m : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (m b)| := by
  unfold F7.thGrid
  rw [Finset.prod_div_distrib, lam_sum_eq, Finset.abs_prod]

theorem lam_sum_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (B : ℝ)
    (hb : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ B) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| ≤ B ^ K := by
  rw [lam_sum_eq]
  calc ∏ b, ∑ i, |F7.lagCo (grid b) i| ≤ ∏ _b : Fin K, B :=
        Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hb b
    _ = B ^ K := by simp

theorem zpow_sq_eq (x : ℝ) (hx : 0 < x) (ν : ℤ) : (x ^ ν) ^ 2 = x⁻¹ ^ (-(2 * ν)) := by
  rw [inv_zpow', neg_neg, ← zpow_natCast, ← zpow_mul, mul_comm]
  norm_num

section psd

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_dsum {Ea R : Type} [Fintype Ea] [Fintype R] (Y : Finset α) (d : Ea → R → ℝ) (hd : ∀ e ρ, 0 ≤ d e ρ)
    (V : Ea → R → α → H) : TB.PSDOn Y (fun P Q => ∑ e, ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) := by
  have h := loe_sum (Finset.univ : Finset Ea) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun e P Q => ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) fun e _ => by
      have := loe_sum (Finset.univ : Finset R) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
        (B := fun ρ P Q => (d e ρ : ℂ) * gramH (V e ρ) P Q) fun ρ _ => by
          have := loe_smul (d e ρ) (hd e ρ) (loe_zero_of_psd (psd_gramH Y (V e ρ)))
          exact loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem psd_mixω {N : Type} [Fintype N] (Y : Finset α) (ω : α → ℝ) (θ κ : N → ℝ) (hθ : ∀ n, 0 ≤ θ n)
    (hκ : ∀ n, 0 ≤ κ n) (Kn : N → α → α → ℂ) (hK : ∀ n, TB.PSDOn Y (Kn n)) :
    TB.PSDOn Y (fun P Q => ∑ n, (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) := by
  have h := loe_sum (Finset.univ : Finset N) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun n P Q => (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) fun n _ => by
      have h1 := loe_diag ω (loe_smul (θ n * κ n) (mul_nonneg (hθ n) (hκ n)) (loe_zero_of_psd (hK n)))
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => by push_cast; ring) h1
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

end psd

theorem mix_alg {N : Type} [Fintype N] (ω1 ω2 ka X L : ℝ) (lam Pn : N → ℝ) (Kn : N → ℂ) (hL : L ≠ 0)
    (hP : ∀ n, Pn n ≠ 0) :
    (ω1 : ℂ) * (ω2 : ℂ) * ((ka : ℂ) * ((X : ℂ) * ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * Kn n)) =
      ((X * L : ℝ) : ℂ) * ∑ n, ((|lam n| / L : ℝ) : ℂ) * ((ω1 : ℂ) * (ω2 : ℂ) * (((ka / Pn n : ℝ) : ℂ) * Kn n)) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := hP n
  push_cast
  field_simp

end

end Formalism.FourierDecayAlt.P.PBL
end
