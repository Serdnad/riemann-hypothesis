module

import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle107
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle113
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle109
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle069
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle110
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselConv

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

section

variable {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem ae_mem_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := hW.1; have := hN.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)

theorem pi_inv_contOn [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ContinuousOn (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} := by
  apply Gp91.GlobalTheory.BesselConv.pi_inv_contOn <;> assumption

theorem beInt_aesm [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (w v : H) :
    AEStronglyMeasurable (beInt z c π σ w v) (μW.prod μN) := by
  apply Gp91.GlobalTheory.BesselConv.beInt_aesm <;> assumption

theorem norm_beInt_le (σ : Mx k r → (H →L[ℂ] H)) {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (w v : H) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z) :
    ‖beInt z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ := by
  have h1 : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
      rw [piW_unitary hT hπ _ (uw_inv hp).1 ξ, one_mul]
  unfold beInt
  rw [norm_smul, norm_mul, norm_star, psi_norm, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end

theorem be_conv_of_growth (hG : GrowthS) : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) := by
  intro Hy k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hR hgap hok hS v hv
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -, hW, hN, hGh, hq⟩ := hS
  obtain ⟨C, Ws, hWs, hb⟩ := GlobalTheory.BesselDecay.decay_TK Hy k r ε mu h R hR hgap hok v hv
  have hA : AG k r < aOf r h - 1 := by
    have h4 := hok.2.2.2
    have : 0 ≤ AG k r := by unfold AG; positivity
    have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have hI := hG k r z μW μN μG νq _ hz hT hW hN hGh hq hA
  rw [neg_sub] at hI
  have hbd : ∀ w ∈ R.sm, ∀ᵐ p ∂(μW.prod μN), ‖beInt z Formalism.QuantumDeterminants.cStd π R.σ w v p‖ ≤
      C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum *
        B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) := by
    intro w hw
    filter_upwards [ae_mem_prod hW hN] with p hp
    exact (norm_beInt_le R.σ _ hT hπ w v p hp.1).trans
      (hb w hw _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hp.1.1 hp.2.1))
  refine ⟨fun w hw => ?_, C * ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (1 - aOf r h) ∂(μW.prod μN), Ws, hWs, fun w hw => ?_⟩
  · exact Integrable.mono' (hI.const_mul _) (beInt_aesm hR.2 _ hT hπ hW hN w v) (hbd w hw)
  · refine (norm_integral_le_of_norm_le (hI.const_mul _) (hbd w hw)).trans (le_of_eq ?_)
    rw [integral_const_mul]; ring

theorem be_conv : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, (∀ w ∈ R.sm, Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN)) ∧ PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v) :=
  be_conv_of_growth GlobalTheory.T.besselGrowth_stabilizer_unipotent

end GlobalTheory.BesselConv
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgContr

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

private lemma star_eval_eq_eval₂_starRingEnd {σ : Type*} (x : σ → ℂ) (q : MvPolynomial σ ℂ) :
    star (MvPolynomial.eval x q) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun v => star (x v)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p v hp => simp [hp]

theorem isPolyDeg_star {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (le_trans (by
        unfold MvPolynomial.totalDegree
        exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)) hq)
  · intro g
    show star (P g) = _
    rw [hP g, MvPolynomial.eval_rename, MvPolynomial.eval_map, star_eval_eq_eval₂_starRingEnd]
    congr 1
    funext v
    cases v <;> simp

theorem isPolyDeg_pow {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (n : ℕ) :
    U.IsPolyDeg (n * a) (fun g => P g ^ n) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨q ^ n, (MvPolynomial.totalDegree_pow q n).trans (Nat.mul_le_mul_left n hq), ?_⟩
  intro g
  simp [hP g]

theorem isPolyDeg_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i, U.IsPolyDeg (d i) (P i)) : U.IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by
  choose q hq hP using h
  refine ⟨∏ i ∈ s, q i, (MvPolynomial.totalDegree_finsetProd s q).trans (Finset.sum_le_sum fun i _ => hq i), ?_⟩
  intro g
  simp [hP]

private lemma isPolyDeg_const (c : ℂ) (a : ℕ) : U.IsPolyDeg (N := N) a (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun g => by simp⟩

private lemma exists_pow_mul_mul_mem_subring {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P)
    (hQ : U.IsPolyDeg b Q) : U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hPe⟩ := hP
  obtain ⟨q, hq, hQe⟩ := hQ
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => by simp [hPe, hQe]⟩

private lemma exists_pow_mul_finset_sum_mem_subring {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolyDeg_const (N := N) 0 a
  | insert j s hj ih =>
    have hj' := h j (Finset.mem_insert_self j s)
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨p, hp, hPe⟩ := hj'
    obtain ⟨q, hq, hQe⟩ := hs
    refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
    have e := hQe g
    simp only at e
    show ∑ i ∈ insert j s, P i g = _
    rw [Finset.sum_insert hj, MvPolynomial.eval_add, ← hPe g, ← e]

private lemma mono_lemma {a b : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (hab : a ≤ b) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem isPolyDeg_eval {σ : Type*} {a d : ℕ} (f : Matrix (Fin N) (Fin N) ℂ → σ → ℂ)
    (hf : ∀ i, U.IsPolyDeg a (fun g => f g i)) (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ d) :
    U.IsPolyDeg (d * a) (fun g => MvPolynomial.eval (f g) q) := by
  classical
  have expand : (fun g => MvPolynomial.eval (f g) q) =
      fun g => ∑ m ∈ q.support, q.coeff m * ∏ i ∈ m.support, f g i ^ m i := by
    funext g
    rw [MvPolynomial.eval_eq]
  rw [expand]
  refine exists_pow_mul_finset_sum_mem_subring _ fun m hm => ?_
  have hdeg : (∑ i ∈ m.support, m i) * a ≤ d * a := by
    apply Nat.mul_le_mul_right
    exact (MvPolynomial.le_totalDegree hm).trans hq
  refine mono_lemma ?_ hdeg
  have hprod : U.IsPolyDeg (∑ i ∈ m.support, m i * a) (fun g => ∏ i ∈ m.support, f g i ^ m i) :=
    isPolyDeg_prod m.support (fun i => m i * a) (fun i => isPolyDeg_pow (hf i) (m i))
  rw [Finset.sum_mul]
  simpa using exists_pow_mul_mul_mem_subring (isPolyDeg_const (q.coeff m) 0) hprod

end GlobalTheory.WigSh.OmgContr

namespace GlobalTheory.WigSh

open OmgContr

theorem wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (π'' : Mx k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → (∃ (t : ℕ) (c : Fin t → Mx k r → ℂ) (L : Fin t → (Wq' →L[ℂ] Wq)), (∀ i, Formalism.FourierDecayAlt.U.IsPolyDeg (d * (r + 1)) (c i)) ∧ ∀ g, A (GlobalTheory.WigSh.omg k r z z' g) = ∑ i, c i g • L i) ∧ ∀ g ∈ UH (Hpk k r), ∀ p : Formalism.FourierDecayAlt.B.SS k r, Matrix.of p.1.1 ∈ UWset k r z → Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r → Matrix.of p.2.1 ∈ UWset k r z' → Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r → (A (GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g))).comp (π'' (Matrix.of p.2.1)⁻¹) = (π' (Matrix.of p.2.1)⁻¹).comp (A (GlobalTheory.WigSh.omg k r z z' g)) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hTz hz' hTz' hA
  obtain ⟨⟨t, q, Lm, hq, hAe⟩, hAeq, -, -⟩ := hA
  refine ⟨⟨t, fun i g => MvPolynomial.eval
      (Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) (q i), Lm, ?_, ?_⟩, ?_⟩
  · intro i
    refine isPolyDeg_eval (N := 2 * r + k + 1)
      (fun g => Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) ?_ (q i) (hq i)
    rintro (j | j)
    · exact GlobalTheory.WigSh.omg_isPolyDeg k r z z' j
    · exact isPolyDeg_star (GlobalTheory.WigSh.omg_isPolyDeg k r z z' j)
  · intro g
    exact hAe _
  · intro g hg p h1 h2 h3 h4
    have hn : (Matrix.of p.1.2)⁻¹ * g ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hg
    have hG : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hn h4.1
    have hs : Formalism.FourierDecayAlt.B.sgs p g =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
      simp only [Formalism.FourierDecayAlt.B.sgs, Matrix.mul_assoc]
    have hom : GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g) =
        (Matrix.of p.2.1)⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' g := by
      rw [hs, GlobalTheory.WigSh.omg_equivariant k r z z' _ _ _ hz hTz hz' hTz' hG h1 h3,
        GlobalTheory.WigSh.omg_mul_N k r z z' _ _ hz hz' hn h4, GlobalTheory.WigSh.OmLeftN.omg_left_N k r z z' g _ hz hz' hg h2]
    rw [hom]
    exact hAeq _ (GlobalTheory.WigSh.OmgEquiv.inv_mem h3) _

end GlobalTheory.WigSh
end
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh.ContrPlus

theorem herm_sum_smul_left {ι κ : Type} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (l : κ → ℂ) (B : κ → ι → ℂ)
    (w : ι → ℂ) : herm H (∑ c, l c • B c) w = ∑ c, l c * herm H (B c) w := by
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_conj {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (v w : ι → ℂ) :
    herm H w v = star (herm H v w) := by
  unfold herm
  rw [← star_dotProduct_star, star_star, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem herm_real_smul_right {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (t : ℝ) (v w : ι → ℂ) :
    herm H v ((t : ℂ) • w) = (t : ℂ) * herm H v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  simp

theorem opNorm_sum_smul_sq_le {V V₂ κ : Type} [Fintype κ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (a : κ → (V₂ →L[ℂ] V)) (l : κ → ℂ)
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) : ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have hS : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans ?_
    have h4 := Real.le_sqrt_of_sq_le h3
    rwa [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg y)] at h4
  calc _ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := Real.sq_sqrt hS

theorem contraction_wigMap :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) (B c) ω • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c) (B c₀) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha hequi
  obtain ⟨hcomp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  have hH : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((Hpk k r *ᵥ B c) j) * MvPolynomial.X (Sum.inr j), a, ?_, ?_⟩,
    ?_, ?_, ?_⟩, ?_⟩
  · intro c
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · intro ω
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [herm, dotProduct, mul_comm]
  · intro h hh ω
    obtain ⟨hW, hiso, -⟩ := hU h hh
    ext y
    have key : ∀ d, ∑ c, herm (Hpk k r) (h *ᵥ B d) (B c) * herm (Hpk k r) (B c) (h *ᵥ ω)
        = herm (Hpk k r) (B d) ω := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2, hiso]

    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sum, map_smul, hequi h hh, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul, ← key d]
    simp only [mul_comm]
  · intro t ω
    simp only [herm_real_smul_right, pow_one, Finset.smul_sum, smul_smul]
  · intro ω h1 h2
    rw [pow_one]
    refine (opNorm_sum_smul_sq_le a _ ha).trans (le_of_eq ?_)
    have h3 : herm (Hpk k r) ω ω = ∑ c, herm (Hpk k r) ω (B c) * herm (Hpk k r) (B c) ω := by
      rw [← herm_sum_smul_left, ← hcomp _ h1 h2]
    rw [h3, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [herm_conj _ hH (B c) ω, Complex.star_def, Complex.conj_mul']
    norm_cast
  · intro c₀
    simp [hB.2.1]

end GlobalTheory.WigSh.ContrPlus
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.ContractLinear

open Formalism.FourierDecayAlt.P

theorem norm_sq_contract_le {V V₂ : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] {k : ℕ} (a : Fin k → (V₂ →L[ℂ] V))
    (ha : ∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) (l : Fin k → ℂ) :
    ‖∑ c, l c • a c‖ ^ 2 ≤ ∑ c, ‖l c‖ ^ 2 := by
  have h0 : 0 ≤ ∑ c, ‖l c‖ ^ 2 := Finset.sum_nonneg fun c _ => by positivity
  have h1 : ‖∑ c, l c • a c‖ ≤ Real.sqrt (∑ c, ‖l c‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    have h2 : ‖(∑ c, l c • a c) y‖ ≤ ∑ c, ‖l c‖ * ‖a c y‖ := by
      rw [ContinuousLinearMap.sum_apply]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun c => ‖l c‖) (fun c => ‖a c y‖)
    rw [ha y] at h3
    refine h2.trans (le_of_sq_le_sq ?_ (by positivity))
    rw [mul_pow, Real.sq_sqrt h0]
    exact h3
  calc ‖∑ c, l c • a c‖ ^ 2 ≤ (Real.sqrt (∑ c, ‖l c‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt h0

theorem wigMap_contract : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (V₂ : Type) [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [FiniteDimensional ℂ V₂] (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (a : Fin k → (V₂ →L[ℂ] V)), inWb k r z → 0 < Tz k r z → IsFrameOf k r [z] B → (∀ y, ∑ c, ‖a c y‖ ^ 2 = ‖y‖ ^ 2) → (∀ h ∈ UWset k r z, ∀ y c, a c (π₂ h y) = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (a d y)) → GlobalTheory.WigSh.WigMap k r z π₂ π 1 (fun ω => ∑ c, herm (Hpk k r) ω (B c) • a c) ∧ ∀ c₀, (∑ c, herm (Hpk k r) (B c₀) (B c) • a c) = a c₀ := by
  intro V _ _ _ k r z π B V₂ _ _ _ π₂ a hz hT hB ha heq
  obtain ⟨hexp, hU⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB
  refine ⟨⟨⟨k, fun c => ∑ j, MvPolynomial.C ((star (B c) ᵥ* Hpk k r) j) * MvPolynomial.X (Sum.inl j), a,
    fun c => ?_, fun ω => ?_⟩, fun h hh ω => ?_, fun t ω => ?_, fun ω hω hωz => ?_⟩, fun c₀ => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  · refine Finset.sum_congr rfl fun c _ => ?_
    congr 1

    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl]
    rw [herm, Matrix.dotProduct_mulVec]
    rfl
  · obtain ⟨hW, hpres, -⟩ := hU h hh
    ext y
    have key : ∀ d, herm (Hpk k r) ω (B d) =
        ∑ c, star (herm (Hpk k r) (h *ᵥ B d) (B c)) * herm (Hpk k r) (h *ᵥ ω) (B c) := by
      intro d
      obtain ⟨h1, h2⟩ := hW (B d) (hB.1 d) (hB.2.2 d z (by simp))
      rw [← HermitianFormSums.herm_rsum, ← hexp _ h1 h2, hpres]

    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    heq h hh, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [key d, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
  · simp only [Qx8.herm_smul_left', pow_one, Finset.smul_sum, smul_smul]
  · refine (norm_sq_contract_le a ha _).trans (le_of_eq ?_)
    have h1 := HermitianFormSums.herm_comb hB (fun c => herm (Hpk k r) ω (B c)) (fun c => herm (Hpk k r) ω (B c))
    rw [← hexp ω hω hωz] at h1
    rw [pow_one, h1, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · simp [hB.2.1]

end GlobalTheory.ContractLinear
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ q, (∀ l, X.op l 0 * W q = W q * X.op l 0 + W (q + 1) ∧ X.op l 3 * W q = W q * X.op l 3 + W (q + 1) ∧ Commute (X.op l 1) (W q) ∧ Commute (X.op l 2) (W q) ∧ Commute (X.op l 4) (W q) ∧ Commute (X.op l 5) (W q)) ∧ ∀ j, Commute (X.fn j) (W q) := by
  first | exact @GlobalTheory.HatNF.MulCoord.mul_coord | exact GlobalTheory.HatNF.MulCoord.mul_coord | (intros; apply GlobalTheory.HatNF.MulCoord.mul_coord <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.rightOperatorDual_mem_of_infinite : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) (K : Submodule ℂ A) (S : Set ℂ), S.Infinite → (∀ y ∈ S, rhv d y ∈ K) → ∀ y : ℂ, rhv d y ∈ K := by
  first | exact @GlobalTheory.RhvPoly.rhv_mem_of_infinite | exact GlobalTheory.RhvPoly.rhv_mem_of_infinite | (intros; apply GlobalTheory.RhvPoly.rhv_mem_of_infinite <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  first | exact @GlobalTheory.HatNF.TaylorMinus.taylor_minus | exact GlobalTheory.HatNF.TaylorMinus.taylor_minus | (intros; apply GlobalTheory.HatNF.TaylorMinus.taylor_minus <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.plusHats_taylorCoeff_leibniz_rule : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahat (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0 (Y + s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahat Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0 Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  first | exact @GlobalTheory.HatTaylorPlus.taylor_plus | exact GlobalTheory.HatTaylorPlus.taylor_plus | (intros; apply GlobalTheory.HatTaylorPlus.taylor_plus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.exists_mulEquiv_uniformisedPoints_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  first | exact @GlobalTheory.PtTie.exists_mulEquiv_ptTieF | exact GlobalTheory.PtTie.exists_mulEquiv_ptTieF | (intros; apply GlobalTheory.PtTie.exists_mulEquiv_ptTieF <;> assumption)
end
