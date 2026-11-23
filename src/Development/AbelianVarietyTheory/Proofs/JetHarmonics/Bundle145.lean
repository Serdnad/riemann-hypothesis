module

public import Formalism.HermitianCurvature.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle012
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

namespace GlobalTheory.HatNF.EmptyWordL2

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem integrable_weight_normSq (hXi : B.XiExists) {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ)
    (hF : ∀ m : ℕ, B.InCC A m F) (hAB : B.AB k r ≤ A) (hT : JF.TransportedAlt k r A 0) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := Formalism.FourierDecayAlt.P.BXiAsm.any_of hXi k r Wp Wq D A hAB
  obtain ⟨c4, hc4⟩ := hF 4
  have hfin := (hB1 F F c4 c4 (hF 5) (hF 5) hc4 hc4).1
  have h := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates k r Wp Wq D A 0 F hT (hF 0)
  have h2 : ContinuousOn (fun q => B.JF D F (B.gq D q)) (Formalism.FourierDecayAlt.P.B7.Q0 D) := h.continuousOn
  have h3 : ContinuousOn (fun q => B.hsVec (B.JF D F (B.gq D q))) (Formalism.FourierDecayAlt.P.B7.Q0 D) :=
    (LinearMap.continuous_of_finiteDimensional
      (⟨⟨B.hsVec, fun X Y => by ext; simp [B.hsVec]⟩, fun a X => by ext; simp [B.hsVec]⟩ :
        (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp))).comp_continuousOn h2
  have hmeas : AEStronglyMeasurable
      (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) volume :=
    Formalism.FourierDecayAlt.P.JCx2.rb_aesm D _ ((Formalism.FourierDecayAlt.P.JCx2.rb_contOn_bcW D).mul (h3.norm.pow 2)) fun q h => by simp [h]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
    mul_nonneg (Formalism.FourierDecayAlt.P.JCx2.rb_bcWeight_nonneg _ _ q) (sq_nonneg _))]
  exact lt_of_le_of_ne le_top hfin

theorem Ew_bigPt_eq_indicator {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      (Formalism.FourierDecayAlt.P.B7.Q0 p.T.base).indicator
        (fun q => bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q *
          ‖B.hsVec (B.JF p.T.base F (B.gq p.T.base q))‖ ^ 2)
        ((fun j => c j.castSucc), c (Fin.last P.r)) := by
  by_cases hq : ((fun j : Fin P.r => c j.castSucc), c (Fin.last P.r)) ∈ Formalism.FourierDecayAlt.P.B7.Q0 p.T.base
  · rw [Set.indicator_of_mem hq]
    obtain ⟨hc, hlt⟩ := hq
    dsimp only at hc hlt
    have hTT : 0 < Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := mul_pos p.T.base.T_pos p.T.base.T'_pos
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p F hl, Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := Formalism.FourierDecayAlt.P.CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    rw [hn, Real.mul_self_sqrt (Formalism.FourierDecayAlt.P.CutBP.bcWeight_nonneg0 _ _ _ _ _)]
    rfl
  · rw [Set.indicator_of_notMem hq]
    refine Formalism.FourierDecayAlt.P.TBBx4.ew_zero_of p F fun h => hq ⟨fun a => ?_, ?_⟩
    · exact (h.1.1 (1, c a.castSucc) (by
        unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a.castSucc, rfl⟩)).2
    · exact Formalism.FourierDecayAlt.P.PBM.zeta_big _ c h.2

end

theorem integrable_density_nil_of_xiExists (hXi : B.XiExists) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) := by
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p H A _ hCC hA
  have ha : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  set x : ℝ := (P.r : ℝ) + 1 with hx
  set n : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn
  have hx1 : 1 ≤ x := by linarith
  have hn1 : 1 ≤ n := by linarith
  have h1 : x ≤ x ^ 4 := le_self_pow₀ hx1 (by norm_num)
  have h2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have h3 : x * n ^ 2 ≤ x ^ 4 * n ^ 3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : 10 * (x * n ^ 2) ≤ A := by nlinarith
  have h5 : n ≤ n ^ 2 := le_self_pow₀ hn1 (by norm_num)
  have h6 : x * n ≤ x * n ^ 2 := mul_le_mul_of_nonneg_left h5 (by linarith)
  have h7 : 1 ≤ x * n := by nlinarith
  have hAB : B.AB P.k P.r ≤ A := by
    unfold B.AB
    rw [← hx]
    have : ((P.k : ℝ) + P.r) * x ≤ n * x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    rw [← hx, ← hn]
    nlinarith
  have hint := (integrable_weight_normSq hXi p.T.base H A hCC hAB hT).indicator
    (Formalism.FourierDecayAlt.P.B7.isOpen_good_set p.T.base).measurableSet
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  have h8 := (hmp.integrable_comp_emb e.measurableEmbedding).2 hint
  refine h8.congr (Filter.Eventually.of_forall fun c => ?_)
  simp only [Function.comp]
  rw [he c]
  exact (Ew_bigPt_eq_indicator p H c).symm

theorem integrable_density_nil : GlobalTheory.HCXi.BesselXiIntegrable → ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) H → (∀ m : ℕ, B.InCC A m H) → Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A → Integrable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)) :=
  fun h => integrable_density_nil_of_xiExists (GlobalTheory.HCXi.xiExists_of_besselXiIntegrable h)

end GlobalTheory.HatNF.EmptyWordL2
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_regularRep_besselBigCellVector_eq_bessel : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ γ ∈ JF.Om P.k P.r p.T.base.z p.T.base.z', Formalism.QuantumDeterminants.Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) ∧ ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), p.V F (TBB.bigPt P.r c) = B.JF p.T.base F γ := by
  first | exact @GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel | exact GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel | (intros; apply GlobalTheory.exists_regular_rep_vec_bigPt_eq_bessel <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.jN2_eq_normSq_base

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem good_of_weight_ne_zero (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ)
    (hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) ≠ 0) :
    (∀ a, c a ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
  set T := Tz P.k P.r p.T.base.z with hT
  set T' := Tz P.k P.r p.T.base.z' with hT'
  have hk : 2 ≤ P.k := p.hl.2.2
  have hTT : 0 < T * T' := mul_pos p.T.base.T_pos p.T.base.T'_pos
  have hw' := hw
  unfold bcWeight at hw'
  split_ifs at hw' with hle
  · have hprod := left_ne_zero_of_mul hw'
    have hgg := right_ne_zero_of_mul hw'
    have hlt : T * T' < Complex.normSq (c (Fin.last P.r)) := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso; apply hgg; rw [← h, sub_self, zero_pow (by omega)]
    have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := by
      intro a ha
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      dsimp only
      rw [ha, norm_zero, zero_pow]
      unfold Mdim; have := a.isLt; omega
    have hlast : c (Fin.last P.r) ≠ 0 := by
      intro h0; rw [h0, Complex.normSq_zero] at hlt; linarith
    have hd : ∀ a, c a ≠ 0 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact hlast
      | cast i => exact hc i
    refine ⟨hd, ?_⟩
    show 0 < D.ptG (T * T') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
      Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
    nlinarith [mul_lt_mul_of_pos_left hlt hp]
  · exact absurd rfl hw'

theorem pt_eq (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
    bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) *
      ‖B.hsVec (B.JF p.T.base F (bigCell P.k P.r (fun j => c j.castSucc)
        (p.T.base.μsec (c (Fin.last P.r)))))‖ ^ 2 := by
  by_cases h : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  · obtain ⟨hl, hG⟩ := h
    have hd : ∀ a, c a ≠ 0 := fun a =>
      (hl.1 (1, c a) (by unfold TBB.bigPt; exact (List.mem_ofFn' _ _).2 ⟨a, rfl⟩)).2
    have hG' : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) := hG
    have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
      Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG'
    rw [TBBx2.Tri.Ew_top p F hl, hsVec_norm_V_bigPt p F c hd hG]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := nPt_bigPt P.k P.r _ _ c hζ.le
    rw [hn, Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]
  · have hw : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
        ((fun j => c j.castSucc), c (Fin.last P.r)) = 0 := by
      by_contra hw
      obtain ⟨hd, hG⟩ := good_of_weight_ne_zero p c hw
      exact h ⟨Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd, hG⟩
    rw [TBBx4.ew_zero_of p F h, hw, zero_mul]

theorem besselNormSq_eq_bigCellNormSq : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F := by
  intro P Wp Wq _ _ _ _ _ _ p F
  let e : (Fin (P.r + 1) → ℂ) ≃ᵐ (Fin P.r → ℂ) × ℂ :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last P.r)).trans MeasurableEquiv.prodComm
  have hmp : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (P.r + 1) => ℂ) (Fin.last P.r))
  have he : ∀ c, e c = ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    intro c
    simp [e, MeasurableEquiv.piFinSuccAbove]
    rfl
  unfold B.normSq jNormSq
  rw [← hmp.lintegral_comp_emb e.measurableEmbedding]
  unfold TBB.jN2
  refine lintegral_congr fun c => ?_
  rw [he c, pt_eq p F c]
  rfl

end GlobalTheory.jN2_eq_normSq_base
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory


open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in
theorem bigCell_density_eq {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) (hd : ∀ a, c a ≠ 0) :
    TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c) =
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hd
  have hc : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hd _
  rw [TBBx2.Tri.Ew_top p F hl]
  split_ifs with hlt
  · have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      show 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
      unfold D.ptG
      rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
        Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
      have hp : 0 < Complex.normSq (∏ i : Fin P.r, c i.castSucc) :=
        Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hc a)
      nlinarith [mul_lt_mul_of_pos_left hlt hp]
    have hn : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
          ((fun j => c j.castSucc), c (Fin.last P.r)) := CutBP.nPt_bigPt P.k P.r _ _ c hlt.le
    have hq : ((fun j => c j.castSucc), c (Fin.last P.r)) ∈ B7.Q0 p.T.base := ⟨hc, hlt⟩
    rw [CutBP.hsVec_norm_V_bigPt p F c hd hG, hn, Real.mul_self_sqrt (CutBP.bcWeight_nonneg0 _ _ _ _ _),
      B7.JM_eq p.T.base F (1, 1) hq, bessel_function_trivial_index P.k P.r Wp Wq p.T.base F, B7.hsL_apply]
    rfl
  · have hV : p.V F (TBB.bigPt P.r c) = 0 := by
      show D.vecV p.T.base p.ν' p.m₀ F (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = 0
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨-, hG⟩
      exact hlt (Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG)
    rw [hV, TBBx2.Tri.hsVec_zero]
    simp


open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P in
theorem bigCell_density_aemeasurable :
    ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn F (B.GV P.k P.r) →
      AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro P Wp Wq _ _ _ _ _ _ p F hF
  have hq : Measurable fun c : Fin (P.r + 1) → ℂ =>
      (((fun j => c j.castSucc), c (Fin.last P.r)) : (Fin P.r → ℂ) × ℂ) := by fun_prop
  have hJ : StronglyMeasurable fun q : (Fin P.r → ℂ) × ℂ => B7.JM p.T.base F (1, 1) q :=
    (B7.sm_JM p.T.base hF).comp_measurable measurable_prodMk_left
  have hN : Measurable fun q : (Fin P.r → ℂ) × ℂ => ‖B7.hsL (B7.JM p.T.base F (1, 1) q)‖ :=
    ((B7.hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable hJ).norm.measurable
  have hm : Measurable fun c : Fin (P.r + 1) → ℂ =>
      if Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) then
        bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z')
            ((fun j => c j.castSucc), c (Fin.last P.r)) *
          ‖B7.hsL (B7.JM p.T.base F (1, 1) ((fun j => c j.castSucc), c (Fin.last P.r)))‖ ^ 2
      else 0 := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const
        (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))
    · exact ((B7.measurable_bcWeight _ _).comp hq).mul ((hN.comp hq).pow_const 2)
  have hae : ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ a, c a ≠ 0 := by
    rw [ae_all_iff]
    intro a
    exact Measure.ae_eval_ne (fun _ => (volume : Measure ℂ)) a 0
  refine (ENNReal.measurable_ofReal.comp hm).aemeasurable.congr ?_
  filter_upwards [hae] with c hc
  rw [bigCell_density_eq p F c hc]
  rfl

end GlobalTheory
end
