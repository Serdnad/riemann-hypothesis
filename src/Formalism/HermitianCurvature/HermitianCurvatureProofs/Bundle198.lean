module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbSplitPt
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section what₂

variable {k p ρ : ℕ}

theorem block_three_mul_apply_last (A11 : Matrix (Fin p) (Fin p) ℂ) (A12 : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin p) (Fin p) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (g : B.Mat k (p + ρ)) (a : Fin p) (c : Fin (2 * (p + ρ) + k + 1)) :
    (U.blk3 A11 A12 A13 A21 A22 A23 0 0 1 * g) (U.eB k p ρ (Sum.inr a)) c = g (U.eB k p ρ (Sum.inr a)) c := by
  rw [Matrix.mul_apply, ← (U.eB k p ρ).sum_comp]
  rw [Finset.sum_eq_single (Sum.inr a)]
  · rw [Ux3.block3_apply]; simp
  · intro q _ hq
    rw [Ux3.block3_apply]
    rcases q with (q | q) | q
    · simp
    · simp
    · have : q ≠ a := fun h => hq (by rw [h])
      simp [Matrix.one_apply, this.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zh_row (a : Fin p) : (⟨2 * (p + ρ) + k - a.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1)) =
    U.eB k p ρ (Sum.inr ⟨p - 1 - a.val, by omega⟩) := by
  ext; rw [Ux3.block_index_last_val]; simp; omega

theorem corner_matrix_block_three_mul (A11 : Matrix (Fin p) (Fin p) ℂ) (A12 : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin p) (Fin p) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (g : B.Mat k (p + ρ)) :
    U.Zh k p ρ (U.blk3 A11 A12 A13 A21 A22 A23 0 0 1 * g) = U.Zh k p ρ g := by
  ext a b
  simp only [U.Zh]
  rw [zh_row, block_three_mul_apply_last]

theorem zh_rn_mul (x : U.RC k p ρ) (g : B.Mat k (p + ρ)) : U.Zh k p ρ (U.Rn k p ρ x * g) = U.Zh k p ρ g := by
  rw [Ux3.rn_eq]; exact corner_matrix_block_three_mul _ _ _ _ _ _ g

theorem zh_embG_mul (y : B.Mat k ρ) (g : B.Mat k (p + ρ)) : U.Zh k p ρ (U.embG k p ρ y * g) = U.Zh k p ρ g := by
  unfold U.embG; exact corner_matrix_block_three_mul _ _ _ _ _ _ g

end what₂

section zh

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zh_sP_mul (Bj : B.RealPlaceData k ρ Wp Wq) (x : XP k p ρ) (g : B.Mat k (p + ρ)) :
    U.Zh k p ρ (sP Bj x * g) = U.Zh k p ρ g := by
  unfold sP
  split_ifs
  · rw [Matrix.mul_assoc, zh_rn_mul, zh_embG_mul]
  · rw [Matrix.one_mul]

theorem zh_mul_UW (z : Fin (2 * (p + ρ) + k + 1) → ℂ) (g h : B.Mat k (p + ρ)) (hh : h ∈ UWset k (p + ρ) z) :
    U.Zh k p ρ (g * h) = U.Zh k p ρ g := by
  ext a b
  simp only [U.Zh, Matrix.mul_apply]
  have hcol : ∀ c : Fin (2 * (p + ρ) + k + 1), h c ⟨b.val, by omega⟩ = if c.val = b.val then 1 else 0 := by
    intro c
    have h1 := congrFun (hh.2.1 ⟨b.val, by omega⟩).1 c
    have e : eI k (p + ρ) ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := rfl
    rw [e] at h1
    rw [← Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply h ⟨b.val, by omega⟩ c, h1]
    unfold bvec
    by_cases hcb : c.val = b.val
    · rw [if_pos hcb, Pi.single_apply, if_pos (Fin.ext hcb)]
    · rw [if_neg hcb, Pi.single_apply, if_neg (fun h' => hcb (congrArg Fin.val h'))]
  rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
  · rw [hcol, if_pos rfl, mul_one]
  · intro c _ hc
    rw [hcol, if_neg (fun h' => hc (Fin.ext h')), mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem nblk_upper (nn : B.Mat k (p + ρ)) (hn : nn ∈ Nset k (p + ρ)) :
    Matrix.of (fun c b : Fin p => nn ⟨c.val, by omega⟩ ⟨b.val, by omega⟩) =
      G.upper (fun q : G.UT p => nn ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
  ext c b
  simp only [Matrix.of_apply, G.upper, G.strictUpper, Matrix.add_apply, Matrix.one_apply]
  rcases lt_trichotomy c b with hcb | rfl | hcb
  · rw [if_neg (ne_of_lt hcb), dite_eq_left hcb, zero_add]
  · rw [LeftFubiniLemmas.n_col nn hn c _ le_rfl, if_pos rfl, if_pos rfl, dite_eq_right (lt_irrefl _), add_zero]
  · rw [LeftFubiniLemmas.n_col nn hn b _ (le_of_lt hcb), if_neg (by simp only; omega), if_neg (ne_of_gt hcb),
      dite_eq_right (not_lt.mpr (le_of_lt hcb)), add_zero]

end zh

section support

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pb_head_support (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)) (hCs : IsCompact Cs)
    (hH : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) :
    ∃ R : ℝ, ∀ v : U.LW σ → ℂ, R < ‖v‖ → ∀ g ∈ B.GV k n,
      U.Zh k p ρ (D.castM e.symm g) = LeftFubiniLemmas.lhOf σ v * U.hMat σ d → pbF Bj B0 e H g = 0 := by
  subst e
  obtain ⟨C2, hC2⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 p 0 σ d hd
  have hcont : Continuous (fun c : B.Mat k (p + ρ) => U.mx (U.Zh k p ρ c)) := by
    have e1 : (fun c : B.Mat k (p + ρ) => U.mx (U.Zh k p ρ c)) =
        fun c => ‖(fun a b => c ⟨2 * (p + ρ) + k - a.val, by omega⟩ ⟨b.val, by omega⟩ : Fin p → Fin p → ℂ)‖ := rfl
    rw [e1]
    refine continuous_norm.comp ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply (⟨b.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1))).comp
      (continuous_apply (⟨2 * (p + ρ) + k - a.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1)))
  obtain ⟨M, hM⟩ := hCs.exists_bound_of_continuousOn hcont.continuousOn
  set M0 : ℝ := max M 0 with hM0
  set C0 : ℝ := max C2 0 with hC0
  refine ⟨C0 * M0 ^ p, fun v hv g hg hZ => ?_⟩
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hZ
  unfold pbF
  rw [← integral_zero (XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [ae_goodP Bj] with x hx
  show pbI Bj B0 rfl H g x = 0
  unfold pbI
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hK : PBG.Kr B0 H (sP Bj x * g) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k (p + ρ) × Mt k (p + ρ)) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    have hc : sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs := by
      intro hcC
      have hZc : U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1) =
          U.headH σ d v (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
        rw [zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, zh_sP_mul, hZ, nblk_upper _ hξ.2,
          (LeftFubiniLemmas.head_hermitian_eq p σ d v _).1]
      set η : U.XiH p 0 σ := ((fun i => i.elim0, fun _ i => i.elim0),
        (v, fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩)) with hη
      have hZj : U.ZjH σ d η (fun i => i.elim0) = U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1) := by
        rw [hZc, LeftFubiniLemmas.lower_corner_hermitian_zero]
      have hb := (hC2 η (fun i => i.elim0)).2.2.1
      rw [hZj] at hb
      have hm := hM _ hcC
      rw [Real.norm_eq_abs, abs_le] at hm
      have hmx0 : 0 ≤ U.mx (U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1)) := norm_nonneg _
      have h1 : U.mx (U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1)) ≤ M0 := hm.2.trans (le_max_left _ _)
      have h2 : ‖v‖ ≤ C0 * M0 ^ p := by
        refine hb.trans ?_
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hmx0 h1 p) (pow_nonneg hmx0 _) (le_max_right _ _)
      exact absurd hv (not_lt.mpr h2)
    have hGV : sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k (p + ρ) := by
      have hs : sP Bj x ∈ B.GV k (p + ρ) := by
        unfold sP
        rw [if_pos hx]
        refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (LeftFubiniLemmas.rn_nset _).1 ?_
        rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
        exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_GV p ρ _
          (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.1.1) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.2.1))
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hg) hξ.2.1) hξ.1.1
    rw [hH _ hGV hc, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

end support

end Formalism.FourierDecayAlt.P.PBQ
end
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_split [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    (h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q)
    (h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ) :
    ∃ θL : Mt k r × Mt k r → ℝ, ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs F →
      Integrable (lint Bs h'.choose θL F) (Bs.μW.prod Bs.μN) ∧
        D.vecV Bs ν' m₀ F q = ∫ x, lint Bs h'.choose θL F x ∂(Bs.μW.prod Bs.μN) := by
  obtain ⟨c₃, hc₃⟩ := orbJ_domL
  set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef
  have hγ := h'.choose_spec.1
  have hZ := h'.choose_spec.2.1
  have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
  have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
  obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
  have hZm := hZ.trans hmono
  obtain ⟨θ, maj, hθ, hθL, hθp, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
    ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  refine ⟨fun x => θ (x, 0), fun F hF => ?_⟩
  obtain ⟨cF, hcF0, hb⟩ := Formalism.FourierDecayAlt.P.PBN.gN_bound Bs hF A (le_max_left _ _)
  have hbnd : ∀ᵐ p ∂Bs.μSS, θ p * ‖F (B.sgs p h'.choose)‖ ≤ cF * maj p :=
    hdom F cF hcF0 (fun p hp => hb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))
  have hFc : ContinuousOn F (B.GV k r) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose F) Bs.μSS :=
    Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs (U := B.GV k r) (fun p hp => Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hFc
  have hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := by
    refine Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbnd, Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS Bs] with p hp hs
    rw [norm_smul, Real.norm_of_nonneg (hθ.2.1 p)]
    unfold D.orbIntegrand
    rw [norm_smul, Formalism.FourierDecayAlt.P.B7.norm_xi, one_mul]
    exact (mul_le_mul_of_nonneg_left (Formalism.FourierDecayAlt.P.B7.norm_rho_le Bs hs F h'.choose) (hθ.2.1 p)).trans hp
  have hR' := inner_int Bs h'.choose hγ θ hθL hθp maj hmaj cF hFc hbnd
  obtain ⟨hint, heq⟩ := fub Bs h'.choose θ hθL F hi hR'
  refine ⟨hint, ?_⟩
  unfold D.vecV
  rw [dite_eq_left h, dite_eq_left h']
  have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := ⟨θ, hθ, hi⟩
  unfold D.orbJ
  rw [dite_eq_left hex]
  refine (Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR F _ θ hex.choose_spec.1 hθ
    hex.choose_spec.2 hi).trans heq

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end

section

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem letter_level_zero_eq {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hj : 0 ≤ r) (l : C.Letter) (e : Fin 2) (G : B.Mat k r → E) :
    D.vLet k r z z' 0 hj l e G = if e = 0 then G else fun _ => 0 := by
  funext g
  by_cases he : e = 0
  · subst he
    have hD0 : Dmin k r z z' g 0 = 1 := by simp [Dmin]
    rcases l with ⟨b, Y⟩
    cases b <;>
      simp [D.vLet, C3.AAop, C3.AAvop, qminorOp, Matrix.det_isEmpty, Finset.univ_unique] <;>
      rw [if_pos (show StrictMono _ from fun a => a.elim0)] <;> simp [hD0]
  · have he1 : e = 1 := by omega
    subst he1
    simp [D.vLet]

theorem slicePolyAll : SlicePolyAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j hj h hh w' b δ e
  by_cases hj0 : j = 0
  · subst hj0
    refine ⟨fun _ => if e = 0 then KB.slv p.T F 0 hj w' h hh.2 else 0, rfl, fun l => ?_, fun t => ?_⟩
    · by_cases he : e = 0
      · simp only [he, if_true]
        exact nice_vec_of_cpt (p.T.bs 0) (fun a => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 hj w' h hh hF a)
      · simp only [he, if_false]
        exact ⟨0, fun a => Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero⟩
    · intro a g hg
      show D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
        (D.vLet P.k P.r p.T.base.z p.T.base.z' 0 hj (b, t + δ) e
          (D.uwG P.k P.r p.T.base.z p.T.base.z' F 0 hj w' a)) h) g = _
      rw [letter_level_zero_eq]
      by_cases he : e = 0
      · simp [he, Finset.sum_apply, Fin.sum_univ_succ, KB.slv]
      · simp [he, sliceAt_zero, Finset.sum_apply, D.castF]
  · refine slicePoly_of_pt p.T F hF j hj (by omega) h hh w' b δ e (fun a g hg hD => ?_)
    obtain ⟨c, hcl, hc⟩ := uwG_letter_poly p.T.base.z p.T.base.z' j hj hF.1 w' a g hg hD b e
    obtain ⟨c', hc'l, hsh⟩ := poly_shift j c (δ : ℂ)
    refine ⟨c', hc'l.trans hcl, fun t => ?_⟩
    show D.vLet P.k P.r p.T.base.z p.T.base.z' j hj (b, t + δ) e (D.uwG P.k P.r p.T.base.z p.T.base.z' F j hj w' a) g = _
    rw [hc (t + δ), ← hsh (t : ℂ)]
    push_cast
    rfl

theorem _root_.Formalism.FourierDecayAlt.P.degree_of_plane_wave : KB.DegWave := degWave_of slicePolyAll

end Formalism.FourierDecayAlt.P.PBG
end
end
