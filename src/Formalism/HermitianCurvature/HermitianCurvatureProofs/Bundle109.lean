module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.StatementHeads
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section hs

variable {Wp Wq Wq' Wq'' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  [NormedAddCommGroup Wq''] [InnerProductSpace ℂ Wq''] [FiniteDimensional ℂ Wq'']

lemma hs_le_of_adj_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) (A' : Wq'' →L[ℂ] Wq) (K : ℝ)
    (h : ∀ v : Wq, ‖v‖ ^ 2 ≤
      K * (‖(ContinuousLinearMap.adjoint A) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint A') v‖ ^ 2)) :
    ‖B.hsVec X‖ ^ 2 ≤ K * (‖B.hsVec (X.comp A)‖ ^ 2 + ‖B.hsVec (X.comp A')‖ ^ 2) := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A'), ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  exact h _

lemma hs_comp_le_sh (X : Wq →L[ℂ] Wp) (A : Wq' →L[ℂ] Wq) :
    ‖B.hsVec (X.comp A)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj (X.comp A), Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj X, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  have h1 := (ContinuousLinearMap.adjoint A).le_opNorm
    ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))
  rw [LinearIsometryEquiv.norm_map] at h1
  calc ‖(ContinuousLinearMap.adjoint A) ((ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j))‖ ^ 2
      ≤ (‖A‖ * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖) ^ 2 := by gcongr
    _ = ‖A‖ ^ 2 * ‖(ContinuousLinearMap.adjoint X) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by ring

end hs

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

lemma ttp_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold TTp
  rw [hz, hz']
  rfl

lemma ew_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) :
    Ew q (fun _ => 1) F (P.r + 1) [] γ =
      (Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)) * ‖B.hsVec (q.V F γ)‖ ^ 2 := by
  have h := Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top q F hγ
  rw [ttp_sh p q hz hz'] at h
  exact h

lemma V_fpmSh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z') {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ)
    (hA : q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ)) :
    q.V (fpmSh (P := P) q f A p₀) γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (APt γ) := by
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  have h := Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow q (fun g => (f g).comp (A g)) p₀ hγ (hGq ▸ hG)
  rw [hA, hGq] at h
  exact h

lemma big_sh (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (APt : C.LPt → (Wq' →L[ℂ] Wq)) (n₀ p₀ : ℕ)
    (hz : q.T.base.z = p.T.base.z) (hz' : q.T.base.z' = p.T.base.z')
    (hA : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (APt γ))
    (hn : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖APt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (c : Fin (P.r + 1) → ℂ) :
    Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c) := by
  set γ := bigPt P.r c with hγdef
  by_cases hloc : D.IsLocPt γ (P.r + 1)
  swap
  · have h0q : Ew q (fun _ => 1) (fpmSh (P := P) q f A p₀) (P.r + 1) [] γ = 0 :=
      Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc q _ hloc
    rw [h0q, Formalism.FourierDecayAlt.P.TBBx4.ew_not_loc p _ hloc, mul_zero]
  have hGq : Gp q γ = Gp p γ := by
    unfold Gp
    rw [ttp_sh p q hz hz']
    rfl
  rw [ew_sh p q hz hz' _ hloc, Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hloc]
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  have hnn : 0 ≤ nn := mul_self_nonneg _
  by_cases hG : 0 < Gp p γ
  · rw [V_fpmSh p q f A APt p₀ hz hz' hloc hG (hA γ hloc hG), Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
    have h1 := hs_comp_le_sh (p.V f γ) (APt γ)
    have h2 := hn γ hloc hG
    set X2 := ‖B.hsVec (p.V f γ)‖ ^ 2 with hX2_def
    have hX2 : 0 ≤ X2 := sq_nonneg _
    have hTT : 0 ≤ TTp p := Formalism.FourierDecayAlt.P.Qx5.place_alt_alt p.hP
    have hGd : Gp p γ ≤ ‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2 := by
      show D.ptG (TTp p) P.r γ ≤ _
      unfold D.ptG
      rw [Complex.normSq_eq_norm_sq]
      have := Complex.normSq_nonneg (D.ptMatN γ P.r).det
      nlinarith
    have hTq : 0 ≤ (Tq p)⁻¹ ^ n₀ := by
      have h3 : 0 ≤ (Gp p γ / Tq p) ^ n₀ := le_trans (sq_nonneg _) h2
      rw [div_pow, div_eq_mul_inv, ← inv_pow] at h3
      exact (mul_nonneg_iff_of_pos_left (pow_pos hG n₀)).mp h3
    calc nn * ((Gp p γ ^ p₀) ^ 2 * ‖B.hsVec ((p.V f γ).comp (APt γ))‖ ^ 2)
        ≤ nn * ((Gp p γ ^ p₀) ^ 2 * (‖APt γ‖ ^ 2 * X2)) := by gcongr
      _ ≤ nn * ((Gp p γ ^ p₀) ^ 2 * ((Gp p γ / Tq p) ^ n₀ * X2)) := by gcongr
      _ = (Gp p γ) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) := by
        rw [div_pow]
        ring
      _ ≤ (‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2) ^ (2 * p₀ + n₀) * (Tq p)⁻¹ ^ n₀ * (nn * X2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hG.le hGd _) hTq)
          (mul_nonneg hnn hX2)
      _ = _ := by rw [← pow_mul]
  · have hq0 : q.V (fpmSh (P := P) q f A p₀) γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right]
      rintro ⟨-, h⟩
      apply hG
      rw [← hGq]
      exact h
    have hp0 : p.V f γ = 0 := by
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right]
      rintro ⟨-, h⟩
      exact hG h
    have e1 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq' →L[ℂ] Wp)
    have e2 := Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq 0 (0 : Wq →L[ℂ] Wp)
    simp only [Complex.ofReal_zero, zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_mul] at e1 e2
    rw [hq0, hp0, e1, e2, mul_zero, mul_zero]

end sh

theorem normaliser_across_places : NormAtShOfAmaps := by
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hz hz' hzm hzm' hA
  obtain ⟨hAp, hAm, hadj, hnp, hnm⟩ := hA
  refine ⟨fun γ hγ hG => ?_, fun c => big_sh p pp f Ap ApPt n₀ p₀ hz hz' hAp hnp c,
    fun c => big_sh p pm f Am AmPt n₀ p₀ hzm hzm' hAm hnm c⟩
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.Ew_top p f hγ, ew_sh p pp hz hz' _ hγ, ew_sh p pm hzm hzm' _ hγ,
    V_fpmSh p pp f Ap ApPt p₀ hz hz' hγ hG (hAp γ hγ hG),
    V_fpmSh p pm f Am AmPt p₀ hzm hzm' hγ hG (hAm γ hγ hG),
    Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  have hX := hs_le_of_adj_sh (p.V f γ) (ApPt γ) (AmPt γ)
    ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀) (hadj γ hγ hG)
  set nn := Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) with hnn_def
  set a1 := ‖B.hsVec ((p.V f γ).comp (ApPt γ))‖ ^ 2 with ha1
  set a2 := ‖B.hsVec ((p.V f γ).comp (AmPt γ))‖ ^ 2 with ha2
  have hnn : 0 ≤ nn := mul_self_nonneg _
  have hcanc : (Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm p₀ 2, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hG.ne')]
  have e : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
      (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
      nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) := by
    rw [show (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
        (nn * ((Gp p γ ^ p₀) ^ 2 * a1) + nn * ((Gp p γ ^ p₀) ^ 2 * a2)) =
        nn * ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (a1 + a2)) *
          ((Gp p γ)⁻¹ ^ (2 * p₀) * (Gp p γ ^ p₀) ^ 2) by ring, hcanc, mul_one]
  rw [e]
  exact mul_le_mul_of_nonneg_left hX hnn

end

end Formalism.FourierDecayAlt.P.CutBP2
end

section

noncomputable section

open Finset Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.NFRO

open Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.NFx4

def JetR {M : Type*} [AddCommGroup M] [Module ℝ M] (U : Set ℂ) (ζ0 : ℂ) (Λ : (ℂ → ℂ) → M) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → List Bool) (L : ι → ℂ →ₗ[ℝ] M),
    ∀ f, ContDiffOn ℝ ∞ f U → Λ f = ∑ i, L i (wd (w i) f ζ0)

theorem wn_cmono (ζ0 c : ℂ) (j l a b : ℕ) :
    wn a b (fun x => c * mono ζ0 j l x) ζ0 = c * wn a b (mono ζ0 j l) ζ0 := by
  have e : mono ζ0 j l = fun x => 1 * mono ζ0 j l x := by funext x; ring
  have h1 : wn a b (fun x => c * mono ζ0 j l x) ζ0 =
      (c * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, iter_dZb_cmono, iter_dZ_cmono]
  have h2 : wn a b (mono ζ0 j l) ζ0 =
      (1 * (l.descFactorial b : ℂ) * (j.descFactorial a : ℂ)) * mono ζ0 (j - a) (l - b) ζ0 := by
    rw [wn, e, iter_dZb_cmono, iter_dZ_cmono]
  rw [h1, h2]
  ring

section Zero

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_zero (hU : IsOpen U) (h0 : ζ0 ∈ U) {Λ : (ℂ → ℂ) → M} (hΛ : JetR U ζ0 Λ)
    (hP : ∀ (c : ℂ) (j l : ℕ), Λ (fun x => c * mono ζ0 j l x) = 0) : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = 0 := by
  classical
  obtain ⟨ι, _, w, L, h⟩ := hΛ
  let cnt : ι → ℕ × ℕ := fun i => ((w i).count false, (w i).count true)
  have hS : ∀ (c : ℕ × ℕ) (x : ℂ), ∑ i ∈ univ.filter (fun i => cnt i = c), L i x = 0 := by
    intro c x
    have hne : ((c.1.factorial * c.2.factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
    obtain ⟨y, hy⟩ : ∃ y : ℂ, y * ((c.1.factorial * c.2.factorial : ℕ) : ℂ) = x :=
      ⟨x / _, div_mul_cancel₀ x hne⟩
    have hsm : ContDiffOn ℝ ∞ (fun t => y * mono ζ0 c.1 c.2 t) U :=
      contDiffOn_const.mul (contDiff_mono ζ0 c.1 c.2).contDiffOn
    have hc := h _ hsm
    rw [hP] at hc
    have e1 : ∀ i, L i (wd (w i) (fun t => y * mono ζ0 c.1 c.2 t) ζ0) =
        if cnt i = c then L i x else 0 := by
      intro i
      rw [wd_eq hU hsm (w i) h0, wn_cmono, wn_mono]
      by_cases hi : cnt i = c
      · rw [if_pos hi, if_pos (by rw [← hi]), hy]
      · rw [if_neg hi, if_neg (by intro h'; exact hi (by rw [h'])), mul_zero, map_zero]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_filter] at hc
    exact hc.symm
  intro f hf
  rw [h f hf, Finset.sum_congr rfl (fun i _ => by rw [wd_eq hU hf (w i) h0]),
    ← Finset.sum_fiberwise_of_maps_to (g := cnt) (t := univ.image cnt)
      (fun i _ => Finset.mem_image_of_mem cnt (Finset.mem_univ i))]
  refine Finset.sum_eq_zero fun c _ => ?_
  have e2 : ∀ i ∈ univ.filter (fun i => cnt i = c),
      L i (wn ((w i).count false) ((w i).count true) f ζ0) = L i (wn c.1 c.2 f ζ0) := by
    intro i hi
    have hi' : cnt i = c := (Finset.mem_filter.1 hi).2
    rw [← hi']
  rw [Finset.sum_congr rfl e2, hS c]

end Zero

section Deriv

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def smulR {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) : E →L[ℝ] (X →L[ℝ] E) :=
  ((ContinuousLinearMap.compL ℝ X ℂ E).flip c).comp (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).flip

theorem smulR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : X →L[ℝ] ℂ) (e : E) (v : X) : smulR c e v = c v • e := by
  first
  | rfl
  | simp [smulR]

theorem jetR_iter (p : X →L[ℝ] ℂ) {U : Set ℂ} {V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : ∀ x ∈ V, p x ∈ U) {q : X} (hq : q ∈ V) (j : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (φ : X → E),
      ContDiffOn ℝ ∞ φ V → JetR U (p q) (fun f => iteratedFDeriv ℝ j (fun x => f (p x) • φ x) q) := by
  induction j with
  | zero =>
    intro E _ _ _ _ φ _
    let L0 : ℂ →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 0 => X) E :=
      { toFun := fun c => (continuousMultilinearCurryFin0 ℝ X E).symm (c • φ q)
        map_add' := fun a b => by rw [add_smul, map_add (f := _)]
        map_smul' := fun s a => by
          rw [RingHom.id_apply, smul_assoc, LinearIsometryEquiv.map_smul] }
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => L0, fun f _ => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rfl
  | succ j ih =>
    intro E _ _ _ _ φ hφ
    let c2 : X →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp p
    have hφ' : ContDiffOn ℝ ∞ (fun y => fderiv ℝ φ y) V := hφ.fderiv_of_isOpen hV (by simp)
    have hM1 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) p (φ y)) V :=
      (smulR (E := E) p).contDiff.comp_contDiffOn hφ
    have hM2 : ContDiffOn ℝ ∞ (fun y => smulR (E := E) c2 (φ y)) V :=
      (smulR (E := E) c2).contDiff.comp_contDiffOn hφ
    obtain ⟨ι1, _, w1, L1, e1⟩ := ih (X →L[ℝ] E) _ hφ'
    obtain ⟨ι2, _, w2, L2, e2⟩ := ih (X →L[ℝ] E) _ hM1
    obtain ⟨ι3, _, w3, L3, e3⟩ := ih (X →L[ℝ] E) _ hM2
    let K : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) (X →L[ℝ] E) →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => X) E :=
      (continuousMultilinearCurryRightEquiv' ℝ j X E).symm.toLinearEquiv.toLinearMap
    refine ⟨ι1 ⊕ ι2 ⊕ ι3, inferInstance,
      Sum.elim w1 (Sum.elim (fun i => w2 i ++ [false]) (fun i => w3 i ++ [true])),
      Sum.elim (fun i => K ∘ₗ L1 i) (Sum.elim (fun i => K ∘ₗ L2 i) (fun i => K ∘ₗ L3 i)), fun f hf => ?_⟩
    have hsm : ∀ {g : ℂ → ℂ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
        [IsScalarTower ℝ ℂ F] {ψ : X → F}, ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ ψ V →
        ContDiffAt ℝ j (fun y => g (p y) • ψ y) q := by
      intro g F _ _ _ _ ψ hg hψ
      exact (((hg.comp p.contDiff.contDiffOn hVU).smul hψ).contDiffAt (hV.mem_nhds hq)).of_le (inf_ge j)
    have hD : ∀ y ∈ V, fderiv ℝ (fun x => f (p x) • φ x) y =
        (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y) := by
      intro y hy
      have hfd : HasFDerivAt f (fderiv ℝ f (p y)) (p y) :=
        ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hVU y hy))).hasFDerivAt
      have hφd : HasFDerivAt φ (fderiv ℝ φ y) y :=
        ((hφ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hy)).hasFDerivAt
      have hc : HasFDerivAt (fun x => f (p x)) ((fderiv ℝ f (p y)).comp p) y := hfd.comp y p.hasFDerivAt
      rw [(hc.fun_smul hφd).fderiv]
      ext v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smulR_apply, fderiv_wirt, add_smul,
        mul_smul, c2]
      simp [add_assoc]
    have hev : (fun y => fderiv ℝ (fun x => f (p x) • φ x) y) =ᶠ[𝓝 q]
        (fun y => (f (p y) • fderiv ℝ φ y + dZ f (p y) • smulR p (φ y)) + dZb f (p y) • smulR c2 (φ y)) :=
      Filter.eventually_of_mem (hV.mem_nhds hq) hD
    beta_reduce at e1 e2 e3 ⊢
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, (hev.iteratedFDeriv ℝ j).eq_of_nhds,
      fun_iteratedFDeriv_add_apply ((hsm hf hφ').add (hsm (contDiffOn_dZ hU hf) hM1))
        (hsm (contDiffOn_dZb hU hf) hM2),
      fun_iteratedFDeriv_add_apply (hsm hf hφ') (hsm (contDiffOn_dZ hU hf) hM1),
      e1 f hf, e2 _ (contDiffOn_dZ hU hf), e3 _ (contDiffOn_dZb hU hf)]

    simp only [map_add (f := _), map_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, wd_append]
    simp only [wd, Bool.false_eq_true, ↓reduceIte, add_assoc]
    rfl

end Deriv

section Closure

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N] {U : Set ℂ} {ζ0 : ℂ}

theorem jetR_congr {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (e : ∀ f, ContDiffOn ℝ ∞ f U → Λ f = Λ' f) :
    JetR U ζ0 Λ' := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, L, fun f hf => (e f hf).symm.trans (hL f hf)⟩

theorem jetR_map (Lm : M →ₗ[ℝ] N) {Λ : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) : JetR U ζ0 (fun f => Lm (Λ f)) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  exact ⟨ι, hι, w, fun i => Lm ∘ₗ L i, fun f hf => by simp only [hL f hf, map_sum, LinearMap.comp_apply]⟩

theorem jetR_add {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f + Λ' f) := by
  obtain ⟨ι, hι, w, L, hL⟩ := h
  obtain ⟨ι', hι', w', L', hL'⟩ := h'
  exact ⟨ι ⊕ ι', inferInstance, Sum.elim w w', Sum.elim L L', fun f hf => by
    simp only [hL f hf, hL' f hf, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]⟩

theorem jetR_sub {Λ Λ' : (ℂ → ℂ) → M} (h : JetR U ζ0 Λ) (h' : JetR U ζ0 Λ') :
    JetR U ζ0 (fun f => Λ f - Λ' f) := by
  refine jetR_congr (jetR_add h (jetR_map (-LinearMap.id) h')) fun f _ => ?_
  simp [sub_eq_add_neg]

theorem jetR_sum {κ : Type*} (s : Finset κ) {Λ : κ → (ℂ → ℂ) → M} (h : ∀ j ∈ s, JetR U ζ0 (Λ j)) :
    JetR U ζ0 (fun f => ∑ j ∈ s, Λ j f) := by
  have h0 : JetR U ζ0 (fun _ : ℂ → ℂ => (0 : M)) :=
    ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun f _ => by simp⟩
  have hs := Finset.sum_induction Λ (JetR U ζ0) (fun a b ha hb => jetR_add ha hb) h0 h
  refine jetR_congr hs fun f _ => ?_
  simp [Finset.sum_apply]

theorem jetR_word (w : List Bool) (L : ℂ →ₗ[ℝ] M) : JetR U ζ0 (fun f => L (wd w f ζ0)) := by
  exact ⟨Unit, inferInstance, fun _ => w, fun _ => L, fun f _ => by simp⟩

def cl {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E) :
    ℂ →ₗ[ℝ] E where
  toFun c := (α * c) • e
  map_add' x y := by rw [mul_add, add_smul]
  map_smul' s c := by rw [RingHom.id_apply, mul_smul_comm, smul_assoc]

theorem cl_apply {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E] (α : ℂ) (e : E)
    (c : ℂ) : cl α e c = (α * c) • e := rfl

end Closure

end Formalism.FourierDecayAlt.P.NFRO
end
end

section

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def JAAop : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (u : ℂ), KB.CptCoef Bs F → ∀ g ∈ JF.Om k r Bs.z Bs.z',
    B.JF Bs (C3.AAop k r r le_rfl u F) g = C3.AAop k r r le_rfl u (B.JF Bs F) g

def AACell : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (u : ℂ) (c : Fin r → ℂ)
    (g : B.Mat k r), g ∈ Q.Glev k r (Fin.last r) →
    C3.AAop k r r le_rfl u f (Q.wCell k r (Fin.last r) c * g) =
      (∏ a, c a) • qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl) u f
        (Q.wCell k r (Fin.last r) c * g)

def MinorCell : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℂ), KB.CptCoef Bs F → ∀ x ∈ Q.DomR k r Bs.z Bs.z',
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) (B.JF Bs F)) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2

def RadSideA : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (X : Q.ActualOps k r z z' π π')
    (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r) (y : ℂ), Q.IsActualLevel X L →
    ∀ (Ψ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      (((L.Ar y).1 Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.crd (Q.vAB r y r).1 (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

def AACpt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℝ),
    KB.CptCoef Bs F → KB.CptCoef Bs (aaTop Bs y F)

def RadAATopOfParts : Prop := JAAop → AACell → MinorCell → RadSideA → AACpt → RadAATop

end Formalism.FourierDecayAlt.P.PBN
end
end
