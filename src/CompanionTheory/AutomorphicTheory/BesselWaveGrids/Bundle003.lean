module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.Assemble
public import CompanionTheory.AutomorphicTheory.BesselSmoothness.BesselSmoothOf
public import Formalism.HermitianCurvature.Bundle004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle176
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.FourLeOfFive
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.PStarTie
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace CompanionTheory.WaveGrid.Coef

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP PI.UpqRep CompanionTheory.LimBd.Main
open scoped InnerProductSpace

section coef

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wp]
  {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ} {f : B.Mat k r → (Wq →L[ℂ] Wp)}

theorem kfin_wsp (hf : KFinDSCoef ε μ f) : ∃ F ∈ Wsp k r Wp Wq ε μ, ∀ g ∈ B.GV k r, F g = f g := by
  classical
  obtain ⟨H, i1, i2, i3, σ, Pm, Qm, hlam, hσ, hQ, hP, hfG⟩ := hf
  let ea := stdOrthonormalBasis ℂ Wp
  let eb := stdOrthonormalBasis ℂ Wq
  let φ : Fin (Module.finrank ℂ Wp) → Fin (Module.finrank ℂ Wq) → B.Mat k r → ℂ :=
    fun a b g => ⟪ContinuousLinearMap.adjoint Pm (ea a), σ g (Qm (eb b))⟫_ℂ
  have hφ : ∀ a b, IsCoef k r ε μ (φ a b) := fun a b =>
    ⟨H, i1, i2, i3, σ, Qm (eb b), ContinuousLinearMap.adjoint Pm (ea a), hlam, hσ, hQ _, hP _, fun _ _ => rfl⟩
  refine ⟨∑ a, ∑ b, fun g => φ a b g • (innerSL ℂ (eb b)).smulRight (ea a),
    Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.subset_span ⟨φ a b, _, hφ a b, rfl⟩, fun g hg => ?_⟩
  rw [op_expand (f g), hfG g hg]
  simp only [Finset.sum_apply, φ, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply, ea, eb]

theorem kfin_inCC (hK : PI.KFinSmooth) (hC : CoefCC) {A h : ℝ} (hD : KDecay k r ε A h)
    (hg : PI.ZuckTensor.GapAtLeast ε μ h) (hf : KFinDSCoef ε μ f) (m : ℕ) : B.InCC A m f := by
  obtain ⟨F, hF, he⟩ := kfin_wsp hf
  have hFm : B.InCC A m F := by
    clear he
    induction hF using Submodule.span_induction with
    | mem F h' =>
      obtain ⟨φ, T, hφ, rfl⟩ := h'
      exact hC hK k r ε A h hD μ φ _ T m hφ hg
    | zero => exact JCx2.sq_inCC_zero
    | add F F' _ _ h h' => exact JCx2.sq_inCC_add h h'
    | smul c F _ h => exact JCx2.sq_inCC_smul c h
  obtain ⟨c, hc⟩ := hFm
  exact ⟨c, JCx2.mn_ccle_congr he hc⟩

end coef

def SmoothKB : Prop :=
  ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), (∀ m, m ≤ CompanionTheory.JfS.NN P.k P.r → JF.TransportedAlt P.k P.r A m) →
    B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) f g = c • f g) →
    Q.SmoothLev P.k P.r 0 (Q.OmPlus P.k P.r p.T.base.z p.T.base.z') (B.JF p.T.base f)

def thrX (k r : ℕ) : ℝ :=
  ((r : ℝ) + 1) ^ 4 * (((3 * (r + 1) : ℕ) : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3)

theorem sq_le_thrX (k r : ℕ) : ((r : ℝ) + 1) ^ 2 * (2 * (r : ℝ) + k + 1) ^ 2 ≤ thrX k r := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 : ((r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) + 1) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h2 : (2 * (r : ℝ) + k + 1) ^ 2 ≤ (2 * (r : ℝ) + k + 1) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h3 : (0 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
  exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)

theorem thrX_nonneg (k r : ℕ) : 0 ≤ thrX k r := le_trans (by positivity) (sq_le_thrX k r)

theorem thr_main {c C A : ℝ} (k r : ℕ) (hc : c ≤ C) (h : C * thrX k r ≤ A) :
    c * ((r : ℝ) + 1) ^ 4 * (((3 * (r + 1) : ℕ) : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A := by
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_right hc (thrX_nonneg k r)).trans h

theorem thr_conv {c C A : ℝ} (k r : ℕ) (hc : c ≤ C) (hC : 0 ≤ C) (h : C * thrX k r ≤ A) :
    c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 : (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1 ≤ (2 * (r : ℝ) + k + 1) ^ 2 := by push_cast; nlinarith
  have h2 : ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ thrX k r :=
    (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (sq_le_thrX k r)
  rw [mul_assoc]
  calc _ ≤ C * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ C * thrX k r := mul_le_mul_of_nonneg_left h2 hC
    _ ≤ A := h

theorem thr_AB {C A : ℝ} (k r : ℕ) (hC : 46 ≤ C) (h : C * thrX k r ≤ A) : B.AB k r ≤ A := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 := sq_le_thrX k r
  have h2 := mul_le_mul_of_nonneg_right hC (thrX_nonneg k r)
  have h3 : (2 * (r : ℝ) + k + 1) ^ 2 ≤ ((r : ℝ) + 1) ^ 2 * (2 * (r : ℝ) + k + 1) ^ 2 :=
    le_mul_of_one_le_left (by positivity) (by nlinarith)
  unfold B.AB
  nlinarith [mul_nonneg hk hr, sq_nonneg (k : ℝ), sq_nonneg (r : ℝ)]

theorem thr_JF {C A : ℝ} (k r m : ℕ) (hm : m ≤ CompanionTheory.JfS.NN k r) (hC : 46 ≤ C) (h : C * thrX k r ≤ A) :
    JF.TransportedAlt k r A m := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 := sq_le_thrX k r
  have h2 := mul_le_mul_of_nonneg_right hC (thrX_nonneg k r)
  have hmR : (m : ℝ) ≤ 2 * (2 * (r : ℝ) + k + 1) * (2 * r * (2 * (r : ℝ) + k + 1) + 1) := by
    have : (m : ℝ) ≤ (CompanionTheory.JfS.NN k r : ℝ) := by exact_mod_cast hm
    unfold CompanionTheory.JfS.NN at this
    push_cast at this
    exact this
  unfold JF.TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  push_cast
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hn1 : 1 ≤ n := by linarith
  have h4 : 6 * (r : ℝ) * m ≤ 6 * r * (2 * n * (2 * r * n + 1)) := mul_le_mul_of_nonneg_left hmR (by positivity)
  have h5 : (r : ℝ) * n ≤ r * n ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hr
  have h6 : 0 < n ^ 2 := by positivity
  have h7 : 0 ≤ (r : ℝ) * n ^ 2 := by positivity
  have h8 : 0 ≤ (r : ℝ) ^ 2 * n ^ 2 := by positivity
  nlinarith

end CompanionTheory.WaveGrid.Coef
end
end

section

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq

section shift

variable {P : M.Par} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {c g b : ℝ} {l n₀ : ℕ}

theorem pairData_plus (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hl1 : 1 ≤ l)
    (hlk : l < P.k) (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) :
    PairData (shP P P.u (uPlus P.u l n₀)) (l + 1) (lamN lam) c g b := by
  open GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid in
  have movedData_of_hyp {Q : M.Par} {lamLocal : Fin (2 * Q.r + Q.k + 1) → ℝ} {c g b : ℝ}
      (h : HypLam Q.k Q.r lamLocal c g b) (hu : HypType Q.k Q.r lamLocal Q.u b) {j : ℕ}
      (hj1 : 1 ≤ j) (hjk : j ≤ Q.k) (hmv : ∀ i, i ≠ j → Q.u' i = Q.u i)
      (hj : |Q.u' j| ≤ b) : PairData Q j (lamN lamLocal) c g b := by
    exact { c_pos := by linarith [h.c_ge]
            g_ge := by linarith [h.c_ge, h.g_ge]
            b_ge_three := h.b_ge_three
            b_ge_k := h.k_le
            b_ge_c := h.b_ge_c
            lam_le := h.lamN_le
            gap := h.lamN_gap
            ul_le := ⟨hu.u_le j hj1 hjk, hj⟩
            pair := fun Y hY =>
              ⟨⟨0, pairOK_of_interlace Q.k (lamN lamLocal) Q.u 0 (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2)⟩,
                pairOK_of_moved Q.k j (lamN lamLocal) Q.u Q.u' (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2) hmv (by
                  rcases hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact Or.inl ⟨by linarith, by linarith⟩
                  · exact Or.inr ⟨by linarith, by linarith⟩)⟩ }
  refine (movedData_of_hyp (Q := shP P P.u (uPlus P.u l n₀)) h hu (by omega) hlk (fun i hi => ?_) ?_)
  · show uPlus P.u l n₀ i = P.u i
    simp only [uPlus, if_neg hi]
  · show |uPlus P.u l n₀ (l + 1)| ≤ b
    have h1 := abs_le.1 (hu.u_le l hl1 hlk.le)
    have h2 := abs_le.1 (hu.u_le (l + 1) (by omega) hlk)
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    simp only [uPlus, if_true]
    rw [abs_le]
    constructor <;> linarith

theorem pairData_minus (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hl1 : 1 ≤ l)
    (hlk : l < P.k) (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) :
    PairData (shP P P.u (uMinus P.u l n₀)) l (lamN lam) c g b := by
  open GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid in
  have movedData_of_hyp {Q : M.Par} {lamLocal : Fin (2 * Q.r + Q.k + 1) → ℝ} {c g b : ℝ}
      (h : HypLam Q.k Q.r lamLocal c g b) (hu : HypType Q.k Q.r lamLocal Q.u b) {j : ℕ}
      (hj1 : 1 ≤ j) (hjk : j ≤ Q.k) (hmv : ∀ i, i ≠ j → Q.u' i = Q.u i)
      (hj : |Q.u' j| ≤ b) : PairData Q j (lamN lamLocal) c g b := by
    exact { c_pos := by linarith [h.c_ge]
            g_ge := by linarith [h.c_ge, h.g_ge]
            b_ge_three := h.b_ge_three
            b_ge_k := h.k_le
            b_ge_c := h.b_ge_c
            lam_le := h.lamN_le
            gap := h.lamN_gap
            ul_le := ⟨hu.u_le j hj1 hjk, hj⟩
            pair := fun Y hY =>
              ⟨⟨0, pairOK_of_interlace Q.k (lamN lamLocal) Q.u 0 (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2)⟩,
                pairOK_of_moved Q.k j (lamN lamLocal) Q.u Q.u' (-Y) (fun s h1 h2 => inter_half h.hc hu s h1 h2) hmv (by
                  rcases hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact Or.inl ⟨by linarith, by linarith⟩
                  · exact Or.inr ⟨by linarith, by linarith⟩)⟩ }
  refine (movedData_of_hyp (Q := shP P P.u (uMinus P.u l n₀)) h hu hl1 hlk.le (fun i hi => ?_) ?_)
  · show uMinus P.u l n₀ i = P.u i
    simp only [uMinus, if_neg hi]
  · show |uMinus P.u l n₀ l| ≤ b
    have h1 := abs_le.1 (hu.u_le l hl1 hlk.le)
    have h2 := abs_le.1 (hu.u_le (l + 1) (by omega) hlk)
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    simp only [uMinus, if_true]
    rw [abs_le]
    constructor <;> linarith

theorem len_le (r : ℕ) : 15 * ((r : ℝ) + 1) * (2 * r + 1) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by
  have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  nlinarith

end shift

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem grids_PStar (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ)
    (hL : PairData P p.l0 (lamN lam) c g b)
    (hlen : 15 * ((P.r : ℝ) + 1) * (2 * P.r + 1) ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3 (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  have e : GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r (lamN lam) c = PStar lam c :=
    funext fun y => Pst_lamN P.k P.r lam c y
  rw [← e]
  refine grids_text p 3 (3 * (P.r + 1)) (by omega) (lamN lam) c g b hL (le_trans (le_of_eq ?_) hlen)
  push_cast
  ring

theorem gridΛ_bounds (p : KB.Pl P Wp Wq) (b CT : ℝ) (hb : 3 ≤ b) (hCT : 0 ≤ CT)
    (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    1 ≤ gridΛ P b (3 * (P.r + 1)) ∧ gridΛ P b (3 * (P.r + 1)) ≤ b ^ ((6 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) :=
  ⟨one_le_gridΛ _ _ _, gridΛ_le P b CT _ le_rfl hb hCT (mul_pos p.hP.1.T_pos p.hP.1.T'_pos) hTT⟩

theorem grids_diff (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (c g b : ℝ)
    (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b) (hu' : HypType P.k P.r lam P.u' b)
    (hlen : 30 * ((P.r : ℝ) + 1) ^ 2 + 6 ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3 (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid p (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  have data : LamData P (lamN lam) c g b := {
    c_pos := by linarith [h.c_ge]
    g_ge := by linarith [h.c_ge, h.g_ge]
    b_ge_three := h.b_ge_three
    b_ge_k := h.k_le
    b_ge_c := h.b_ge_c
    lam_le := h.lamN_le
    gap := h.lamN_gap
    inter := fun s h1 h2 => ⟨inter_half h.hc hu s h1 h2, inter_half h.hc hu' s h1 h2⟩
    u_le := fun i h1 h2 => ⟨hu.u_le i h1 h2, hu'.u_le i h1 h2⟩ }
  have pair : PairData P p.l0 (lamN lam) c g b := {
    c_pos := data.c_pos
    g_ge := data.g_ge
    b_ge_three := data.b_ge_three
    b_ge_k := data.b_ge_k
    b_ge_c := data.b_ge_c
    lam_le := data.lam_le
    gap := data.gap
    ul_le := data.u_le p.l0 p.hl.1 p.hl.2.1
    pair := fun Y _ =>
      ⟨⟨0, GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_of_interlace P.k (lamN lam) P.u 0 (-Y) (fun s h1 h2 => (data.inter s h1 h2).1)⟩,
       ⟨0, GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.pairOK_of_interlace P.k (lamN lam) P.u' 0 (-Y) (fun s h1 h2 => (data.inter s h1 h2).2)⟩⟩ }
  exact grids_PStar p lam c g b pair ((len_le P.r).trans hlen)

theorem grids_plus {up up' : ℕ → ℝ} (q : KB.Pl (shP P up up') Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (c g b : ℝ) (l n₀ : ℕ) (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hn₀ : n₀ = 30 * (P.r + 1) ^ 2 + 6) (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) (e1 : up = P.u) (e2 : up' = uPlus P.u l n₀)
    (e3 : q.l0 = l + 1) :
    TBBx5.WaveGrid q (PStar lam c) (gridY (shP P up up') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid q (PStar lam c) (gridY (shP P up up') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  subst e1 e2
  have hn₀R : (n₀ : ℝ) = 30 * ((P.r : ℝ) + 1) ^ 2 + 6 := by rw [hn₀]; push_cast; ring
  refine grids_PStar q lam c g b (by rw [e3]; exact pairData_plus h hu hl1 hlk hposition) ?_
  rw [e3]
  show _ ≤ |P.u (l + 1) - uPlus P.u l n₀ (l + 1)|
  simp only [uPlus, if_true]
  rw [show P.u (l + 1) - (P.u (l + 1) + n₀) = -(n₀ : ℝ) by ring, abs_neg, abs_of_nonneg (Nat.cast_nonneg _), hn₀R]
  exact len_le P.r

theorem grids_minus {um um' : ℕ → ℝ} (q : KB.Pl (shP P um um') Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ)
    (c g b : ℝ) (l n₀ : ℕ) (h : HypLam P.k P.r lam c g b) (hu : HypType P.k P.r lam P.u b)
    (hn₀ : n₀ = 30 * (P.r + 1) ^ 2 + 6) (hl1 : 1 ≤ l) (hlk : l < P.k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1)) (e1 : um = P.u) (e2 : um' = uMinus P.u l n₀)
    (e3 : q.l0 = l) :
    TBBx5.WaveGrid q (PStar lam c) (gridY (shP P um um') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) ∧
      TBBx5.LiftGrid q (PStar lam c) (gridY (shP P um um') q.l0 (3 * (P.r + 1))) (gridΛ P b (3 * (P.r + 1))) 3
        (3 * (P.r + 1)) := by
  subst e1 e2
  have hn₀R : (n₀ : ℝ) = 30 * ((P.r : ℝ) + 1) ^ 2 + 6 := by rw [hn₀]; push_cast; ring
  refine grids_PStar q lam c g b (by rw [e3]; exact pairData_minus h hu hl1 hlk hposition) ?_
  rw [e3]
  show _ ≤ |P.u l - uMinus P.u l n₀ l|
  simp only [uMinus, if_true]
  rw [show P.u l - (P.u l - n₀) = (n₀ : ℝ) by ring, abs_of_nonneg (Nat.cast_nonneg _), hn₀R]
  exact len_le P.r

end grid

end CompanionTheory.WaveGrid
end
