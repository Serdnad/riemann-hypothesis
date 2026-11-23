module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

namespace GlobalTheory.BetaIntegrand

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end GlobalTheory.BetaIntegrand

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem exists_CCle_four_of_inCC_five {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ}
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) : ∃ c, _root_.Formalism.FourierDecayAlt.B.CCle A 4 G c := by
  unfold _root_.Formalism.FourierDecayAlt.B.InCC _root_.Formalism.FourierDecayAlt.B.CCle at hG
  obtain ⟨c, h1, h2⟩ := hG
  exact ⟨c, _root_.Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) h1, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem measurableSet_Qset' (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : MeasurableSet (_root_.Formalism.FourierDecayAlt.B.Qset Bs) :=
  measurableSet_lt measurable_const (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem aestronglyMeasurable_indicator_hsVec_JF (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      volume := by
  refine (aestronglyMeasurable_indicator_iff (measurableSet_Qset' Bs)).2 ?_
  have h := _root_.Formalism.FourierDecayAlt.P.B7.jc_aesm_J Bs hG (1, 1)
  simp only [_root_.Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs G] at h
  exact _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_cont'.comp_aestronglyMeasurable h

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem mem_Qset_iff_zero_lt_bcWeight (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) :
    q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs ↔ 0 < _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q := Iff.rfl

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem bcWeight_mul_eq_bcWeight_mul_indicator (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {β : Type} [Zero β] (Φ : β → ℝ)
    (hΦ : Φ 0 = 0) (u : (Fin r → ℂ) × ℂ → β) (q : (Fin r → ℂ) × ℂ) :
    _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q * Φ (u q) =
      _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q * Φ ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator u q) := by
  by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
  · rw [Set.indicator_of_mem hq]
  · have hw : _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (_root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q)
    rw [hw, zero_mul, zero_mul]


open Filter Topology MeasureTheory in
theorem _root_.GlobalTheory.betaIntegrand_integrable_of_xiExists (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (A : ℝ) (X F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → _root_.Formalism.FourierDecayAlt.B.InCC A 5 X → _root_.Formalism.FourierDecayAlt.B.InCC A 5 F → Integrable (fun q : (Fin r → ℂ) × ℂ => (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) * inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs A X F hA hX hF
  obtain ⟨-, -, -, ⟨C, hC⟩, -⟩ := _root_.Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq Bs A hA
  obtain ⟨cF, hcF⟩ := exists_CCle_four_of_inCC_five hF
  obtain ⟨cX, hcX⟩ := exists_CCle_four_of_inCC_five hX
  obtain ⟨hFF, hFX, -⟩ := hC F X cF cX hF hX hcF hcX
  unfold _root_.Formalism.FourierDecayAlt.B.normSq _root_.Formalism.QuantumDeterminants.jNormSq at hFF hFX
  set w := fun q => _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q with hw
  set uF := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huF
  set uX := (_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)) with huX
  have hmF : AEStronglyMeasurable uF volume :=
    aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cF, hcF⟩))
  have hmX : AEStronglyMeasurable uX volume :=
    aestronglyMeasurable_indicator_hsVec_JF Bs (_root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cX, hcX⟩))
  have hw0 : ∀ q, 0 ≤ w q := fun q => _root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q
  have hfun : (fun q : (Fin r → ℂ) × ℂ => (w q : ℂ) * inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) = fun q => (w q : ℂ) * inner ℂ (uF q) (uX q) := by
    funext q
    by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
    · rw [huF, huX, Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    · have hwq : w q = 0 :=
        le_antisymm (not_lt.1 ((mem_Qset_iff_zero_lt_bcWeight Bs q).not.1 hq)) (hw0 q)
      rw [hwq, Complex.ofReal_zero, zero_mul, zero_mul]
  have hFF' : ∫⁻ q, ENNReal.ofReal (w q * ‖uF q‖ ^ 2) ≠ ⊤ := by
    refine ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFF
    exact congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm
  have hFX' : ∫⁻ q, ENNReal.ofReal (w q * ‖uX q‖ ^ 2) ≠ ⊤ := by
    refine ne_of_eq_of_ne (lintegral_congr fun q => ?_) hFX
    exact congrArg ENNReal.ofReal (bcWeight_mul_eq_bcWeight_mul_indicator Bs (fun x => ‖x‖ ^ 2) (by simp) _ q).symm
  have hbound : ∀ q, ‖(w q : ℂ) * inner ℂ (uF q) (uX q)‖ₑ ≤
      ENNReal.ofReal (w q * ‖uF q‖ ^ 2) + ENNReal.ofReal (w q * ‖uX q‖ ^ 2) := by
    intro q
    rw [← ENNReal.ofReal_add (mul_nonneg (hw0 q) (sq_nonneg _)) (mul_nonneg (hw0 q) (sq_nonneg _)),
      ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 q)]
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (uF q) (uX q)
    have h2 : ‖uF q‖ * ‖uX q‖ ≤ ‖uF q‖ ^ 2 + ‖uX q‖ ^ 2 := by
      nlinarith [sq_nonneg (‖uF q‖ - ‖uX q‖), norm_nonneg (uF q), norm_nonneg (uX q)]
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (hw0 q)]
  have haeF : AEMeasurable (fun q => ENNReal.ofReal (w q * ‖uF q‖ ^ 2)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aemeasurable.mul (hmF.norm.aemeasurable.pow_const 2))
  rw [hfun]
  refine ⟨(Complex.continuous_ofReal.measurable.comp (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable.mul
    (hmF.inner hmX), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ q, ‖(w q : ℂ) * inner ℂ (uF q) (uX q)‖ₑ
      ≤ ∫⁻ q, (ENNReal.ofReal (w q * ‖uF q‖ ^ 2) + ENNReal.ofReal (w q * ‖uX q‖ ^ 2)) :=
        lintegral_mono hbound
    _ = (∫⁻ q, ENNReal.ofReal (w q * ‖uF q‖ ^ 2)) + ∫⁻ q, ENNReal.ofReal (w q * ‖uX q‖ ^ 2) :=
        lintegral_add_left' haeF _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hFF', lt_top_iff_ne_top.2 hFX'⟩
end
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.CapelliFoldBound

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

variable {k r : ℕ} (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

variable {Wp Wq}

end GlobalTheory.CapelliFoldBound

namespace GlobalTheory

open Filter Topology MeasureTheory in
private theorem ckOn_sum_smul_Rw {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (L : List (ℂ × List (_root_.Formalism.FourierDecayAlt.B.Mat k r))) (hL : ∀ cw ∈ L, ∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X)
    {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)} (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) :
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g => (L.map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum) := by
  induction L with
  | nil => exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_zero'
  | cons cw L ih =>
    have hw : ∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.inLie k r X := by
      intro X hX
      have := hL cw (List.mem_cons_self ..) X hX
      unfold _root_.Formalism.FourierDecayAlt.B.unitLie at this
      unfold _root_.Formalism.FourierDecayAlt.B.inLie
      exact this.1
    exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_add' (_root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' cw.1 (_root_.Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hF cw.2 hw)) (ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h))

open Filter Topology MeasureTheory in
private theorem capelli_eq_foldT_signed_sum {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (y : ℂ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.Q.CV k r y F g = ∑ σ : Equiv.Perm (Fin (2 * (r - 0) + k + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
        (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j)) F g := by
  unfold _root_.Formalism.FourierDecayAlt.Q.CV _root_.Formalism.FourierDecayAlt.Q.capL _root_.Formalism.QuantumDeterminants.qminorOp _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT
  simp only [Finset.sum_apply, List.map_ofFn, Pi.smul_apply, Function.comp_def]
  rfl

open Filter Topology MeasureTheory in
private theorem capelli_eq_wordSum_lemma_3 {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (y : ℂ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E) (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) :
    ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, _root_.Formalism.FourierDecayAlt.Q.CV k r y F g =
      ∑ σ : Equiv.Perm (Fin (2 * (r - 0) + k + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
          (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j))).map
            fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum := by
  intro g hg
  rw [capelli_eq_foldT_signed_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hloc : _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc (⊤ : ℕ∞) F g := by
    unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hF
    exact hF g hg
  rw [_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq _ F g hg (_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top hloc)]

open Filter Topology MeasureTheory in
private theorem CCle_sum_smul_Rw {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (N : ℕ) (L : List (ℂ × List (_root_.Formalism.FourierDecayAlt.B.Mat k r)))
    (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ N) {A : ℝ} {m : ℕ}
    {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} {c : ℝ} (hF : _root_.Formalism.FourierDecayAlt.B.CCle A (m + N) F c) :
    _root_.Formalism.FourierDecayAlt.B.CCle A m (fun g => (L.map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      ((L.map fun cw => ‖cw.1‖).sum * c) := by
  induction L with
  | nil => simpa using (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))
  | cons cw L ih =>
    have hcw := hL cw (List.mem_cons_self ..)
    have h1 : _root_.Formalism.FourierDecayAlt.B.CCle A m (_root_.Formalism.FourierDecayAlt.B.Rw cw.2 F) c :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hcw.1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by omega) hF)
    have h2 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 h1) (ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact h2

open Filter Topology MeasureTheory in
private theorem norm_sign_perm_complex_eq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

open Filter Topology MeasureTheory in
private theorem capelli_smooth_and_bound_lemma {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (y : ℂ) :
    (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (_root_.Formalism.FourierDecayAlt.Q.CV k r y F)) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (m : ℕ) (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ),
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → _root_.Formalism.FourierDecayAlt.B.CCle A (m + (2 * r + k + 1)) F c →
        _root_.Formalism.FourierDecayAlt.B.CCle A m (_root_.Formalism.FourierDecayAlt.Q.CV k r y F) (K * c) := by
  set ts : Equiv.Perm (Fin (2 * (r - 0) + k + 1)) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin (2 * (r - 0) + k + 1) =>
      (_root_.Formalism.FourierDecayAlt.Q.uC k r 0 y - (j : ℂ), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 (σ j), _root_.Formalism.FourierDecayAlt.Q.posL k r 0 j) with hts
  have hwords : ∀ σ, ∀ cw ∈ _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ),
      (∀ X ∈ cw.2, _root_.Formalism.FourierDecayAlt.B.unitLie k r X) ∧ cw.2.length ≤ 2 * r + k + 1 := by
    intro σ cw hcw
    obtain ⟨h1, h2⟩ := _root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (ts σ) cw hcw
    refine ⟨h1, h2.trans ?_⟩
    simp [hts]
  refine ⟨fun F hF => ?_, ?_⟩
  · have hG := _root_.Formalism.FourierDecayAlt.P.JCx2.sq_ckOn_sum (Finset.univ : Finset (Equiv.Perm (Fin (2 * (r - 0) + k + 1))))
      (fun σ g => ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      (fun σ _ => _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ (ckOn_sum_smul_Rw _ (fun cw h => (hwords σ cw h).1) hF))
    have heq := capelli_eq_wordSum_lemma_3 y F hF
    unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hG ⊢
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hagree⟩ := hG g₀ hg₀
    exact ⟨U, f', hU, hgU, hf', fun x hx hxG => (heq x hxG).trans (hagree x hx hxG)⟩
  · refine ⟨∑ σ, ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => ‖cw.1‖).sum,
      Finset.sum_nonneg fun σ _ => List.sum_nonneg fun a ha => by
        obtain ⟨cw, -, rfl⟩ := List.mem_map.1 ha
        exact norm_nonneg _, ?_⟩
    intro A m F c hF hc
    have hc0 : 0 ≤ c := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
    have hsum := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_sum (Finset.univ : Finset (Equiv.Perm (Fin (2 * (r - 0) + k + 1))))
      (fun σ g => ((Equiv.Perm.sign σ : ℤ) : ℂ) •
        ((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => cw.1 • _root_.Formalism.FourierDecayAlt.B.Rw cw.2 F g).sum)
      (fun σ => ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ * (((_root_.Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map fun cw => ‖cw.1‖).sum * c))
      (fun σ _ => _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ (CCle_sum_smul_Rw _ _ (hwords σ) hc))
    simp only [norm_sign_perm_complex_eq_one, one_mul] at hsum
    rw [Finset.sum_mul]
    exact _root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => (capelli_eq_wordSum_lemma_3 y F hF g hg).symm) hsum


open Filter Topology MeasureTheory in
theorem _root_.GlobalTheory.capelli_fold_ccle : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (s : ℂ) (w : List (Bool × ℝ)) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (A c : ℝ) (X : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) X → _root_.Formalism.FourierDecayAlt.B.CCle A (m + w.length * (2 * r + k + 1)) X c → _root_.Formalism.FourierDecayAlt.B.CCle A m (List.foldr (fun (a : Bool × ℝ) G => s • _root_.Formalism.FourierDecayAlt.Q.CV k r (a.2 : ℂ) G) (X) w) (K * c) := by
  intro k r Wp Wq _ _ _ _ _ _ s w
  have hsmooth : ∀ (w : List (Bool × ℝ)) (X : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) X →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (List.foldr (fun (a : Bool × ℝ) G => s • _root_.Formalism.FourierDecayAlt.Q.CV k r (a.2 : ℂ) G) X w) := by
    intro w X hX
    induction w with
    | nil => exact hX
    | cons a w ih => exact _root_.Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' s ((capelli_smooth_and_bound_lemma (a.2 : ℂ)).1 _ ih)
  induction w with
  | nil => exact fun m => ⟨1, zero_le_one, fun A c X _ hX => by simpa using hX⟩
  | cons a w ih =>
    intro m
    obtain ⟨K, hK, hbound⟩ := ih (m + (2 * r + k + 1))
    obtain ⟨Ky, hKy, hy⟩ := (capelli_smooth_and_bound_lemma (Wp := Wp) (Wq := Wq) (a.2 : ℂ)).2
    refine ⟨‖s‖ * (Ky * K), by positivity, fun A c X hX hXc => ?_⟩
    have h1 := hbound A c X hX (by
      have : m + (2 * r + k + 1) + w.length * (2 * r + k + 1) = m + (a :: w).length * (2 * r + k + 1) := by
        simp only [List.length_cons]; ring
      rw [this]; exact hXc)
    have h2 := hy A m _ (K * c) (hsmooth w X hX) h1
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul s h2
    simp only [List.foldr_cons]
    rw [show ‖s‖ * (Ky * K) * c = ‖s‖ * (Ky * (K * c)) by ring]
    exact h3

end GlobalTheory
end
