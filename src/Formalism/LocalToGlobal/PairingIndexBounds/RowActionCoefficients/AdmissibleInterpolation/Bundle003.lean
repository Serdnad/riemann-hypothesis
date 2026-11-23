module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bundle001
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.XFacts
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.Bundle002
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.WeylComplementDetCoeffSpan
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.YVMapRowAct
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem mF_mul (j : ℕ) (b : BX X) (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b A * mF X j b B = mF X j b (A * B) := by
  simp only [mF]
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  ext i k

  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

theorem mF_one (j : ℕ) (b : BX X) : mF X j b 1 = 1 := by
  ext i k
  by_cases h : i = k <;> simp [mF, Matrix.one_apply, h]

theorem mF_inv_mul (j : ℕ) (b : BX X) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    mF X j b ((g⁻¹ : GL _ _) : Matrix _ _ (X.G.P.Qq b.1)) * mF X j b (g : Matrix _ _ (X.G.P.Qq b.1)) = 1 := by
  rw [mF_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mF_one]

theorem mF_det_ne (j : ℕ) (b : BX X) (g : GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq b.1)) :
    (mF X j b (g : Matrix _ _ (X.G.P.Qq b.1))).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (mF_inv_mul X j b g)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def PhiX (j : ℕ) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) :
    (X.Pj j).Xsp →ₗ[X.G.Kf] Kc :=
  ((LinearMap.mulLeft Kc a).restrictScalars X.G.Kf) ∘ₗ (l.restrictScalars X.G.Kf) ∘ₗ ((delF X Kc j).flip f)

theorem PhiX_apply (j : ℕ) (l : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] Kc) (a : Kc) (f : MvPowerSeries (X.ZA j) Kc) (G : (X.Pj j).Xsp) :
    PhiX X Kc j l a f G = a * l (delF X Kc j G f) := rfl

def WT (j : ℕ) : Submodule Kc (XspC (X.Pj (j + 1)) Kc) :=
  Submodule.span Kc {z | ∃ F : BX X → MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) X.G.Kf,
    (∀ b, F b ∈ dualWeyl X.G.Kf (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b)) ∧
      z = map (algebraMap X.G.Kf Kc) (∏ b, rename (emX X (j + 1) b) (F b))}

private theorem prod_rowAct_lemma {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (d : K) :
    rowAct K M (C d : MvPolynomial (Fin n × Fin n) K) = C d := by
  simp [rowAct]

private theorem prod_rowAct_lemma_2 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (yV K n).map (rowAct K M) = M.map C * yV K n := by
  ext a t
  simp [yV, BidetPairing.rowAct_X', Matrix.mul_apply]

private theorem prod_rowAct_lemma_3 {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) : mulC A (mulC B y) = mulC (A * B) y := by
  funext a i
  simp only [mulC, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

private theorem prod_rowAct_lemma_4 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) :
    mulC (M.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) (fun a i => C (y a i)) =
      fun a i => C (mulC M y a i) := by
  funext a i

  simp [mulC, map_sum, map_mul]

private theorem prod_rowAct_lemma_5 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M.det ≠ 0) (y : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) :
    rowAct K M (hvO (fun a i => C (y a i)) (yV K n) c h) =
      C (M.det ^ c) * hvO (fun a i => C (mulC M⁻¹ y a i)) (yV K n) c h := by
  show (rowAct K M).toRingHom _ = _
  rw [map_hvO]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, prod_rowAct_lemma]
  rw [prod_rowAct_lemma_2]
  have hy : (fun a i => (C (y a i) : MvPolynomial (Fin n × Fin n) K)) =
      mulC (M.map (C : K →+* MvPolynomial (Fin n × Fin n) K)) (fun a i => C (mulC M⁻¹ y a i)) := by
    rw [prod_rowAct_lemma_4, prod_rowAct_lemma_3, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),
      mulC_one']
  rw [hy, hvO_mul]
  congr 1
  rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply]

private theorem prod_rowAct_lemma_6 {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (y : Fin n → ℕ → K) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k : Fin c, h k ≤ n) :
    rowAct K M (hvE (fun a i => C (y a i)) (yV K n) c h hh) =
      hvE (fun a i => C (mulC M.transpose y a i)) (yV K n) c h hh := by
  show (rowAct K M).toRingHom _ = _
  rw [map_hvE]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, prod_rowAct_lemma]
  rw [prod_rowAct_lemma_2, hvE_mul, ← Matrix.transpose_map, prod_rowAct_lemma_4]

private theorem prod_rowAct_lemma_7 (j : ℕ) (b : BX X) (M : Matrix (Fin (NJ X j)) (Fin (NJ X j)) X.G.Kf)
    (hM : M.det ≠ 0) (y : Fin (NJ X j) → ℕ → X.G.Kf) :
    ∃ (c : X.G.Kf) (y'' : Fin (NJ X j) → ℕ → X.G.Kf),
      rowAct X.G.Kf M (srcN X j b y) = c • srcN X j b y'' := by
  unfold srcN
  split_ifs with hb
  · exact ⟨M.det ^ cX X j b, mulC M⁻¹ y, by rw [prod_rowAct_lemma_5 M hM, MvPolynomial.smul_eq_C_mul]⟩
  · refine ⟨(M.det ^ eX X j b)⁻¹, mulC M.transpose y, ?_⟩
    rw [map_mul, prod_rowAct_lemma, prod_rowAct_lemma_6, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    congr 2
    have hd : (Matrix.of fun (a i : Fin (NJ X j)) => mulC M.transpose y a ↑i) =
        M.transpose * Matrix.of fun (a i : Fin (NJ X j)) => y a ↑i := by
      ext a i
      simp [mulC, Matrix.mul_apply]
    rw [hd, Matrix.det_mul, Matrix.det_transpose, mul_pow, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hM), one_mul]

theorem prod_rowAct (j : ℕ) (g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (x : X.FrI j → X.G.Kf) :
    ∃ (a : X.G.Kf) (x'' : ∀ b : BX X, Fin (NJ X j) → ℕ → X.G.Kf),
      ∏ b, rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
        (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b))) = a • ∏ b, rename (emX X j b) (srcN X j b (x'' b)) := by
  have key : ∀ b : BX X, ∃ (c : X.G.Kf) (y'' : Fin (NJ X j) → ℕ → X.G.Kf),
      rename (emX X j b) (rowAct X.G.Kf (mF X j b ((g b.1)⁻¹ : GL _ _))
        (evX (fun s => x (xmX X j b s)) (HgX X X.G.Kf j b))) =
        c • rename (emX X j b) (srcN X j b y'') := by
    intro b
    rw [evX_HgX]
    obtain ⟨c, y'', hc⟩ := prod_rowAct_lemma_7 X j b _ (mF_det_ne X j b (g b.1)⁻¹) _
    exact ⟨c, y'', by rw [hc, MvPolynomial.smul_eq_C_mul, map_mul, rename_C, MvPolynomial.smul_eq_C_mul]⟩
  choose c y'' hc using key
  refine ⟨∏ b, c b, y'', ?_⟩
  rw [Finset.prod_congr rfl (fun b _ => hc b)]
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

end Formalism.L2.PairingIndexBounds.Ent
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def dgQ (K : Type) [Field K] (p k r : ℕ) : Matrix (Fin k) (Fin k) K := Matrix.diagonal fun c => if c.val < r then (p : K)⁻¹ else 1

theorem dgQ_det_ne (K : Type) [Field K] (p k r : ℕ) (hp : (p : K) ≠ 0) : (dgQ K p k r).det ≠ 0 := by
  unfold dgQ
  rw [Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
  split_ifs
  · exact inv_ne_zero hp
  · exact one_ne_zero

theorem mF_dgQ (j : ℕ) (b : BX X) (i0 : X.Pl → ℕ) :
    mF X (j + 1) b (dgQ (X.G.P.Qq b.1) p _ (i0 b.1)) = DgX X X.G.Kf j i0 b.1 := by
  unfold mF dgQ DgX
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, if_pos rfl]
    have : ((finCongr (rank_eq X (j + 1)).symm) a).val = a.val := rfl
    rw [this]
    split_ifs
    · rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
    · rw [map_one, map_one]
  · rw [if_neg hac, if_neg (fun h => hac ((finCongr (rank_eq X (j + 1)).symm).injective h)), map_zero, map_zero]

theorem frame_edge_identity_holds : XEdge := by
  intro p _ X j L' L'' i0 h2 h4
  have key : ∀ v : X.Pl, ∃ g' h' : GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v),
      X.latAt v (j + 1) L'' = colSpan (X.G.P.W v) (g' : Matrix _ _ (X.G.P.Qq v)) ∧
      X.latAt v (j + 1) L' = colSpan (X.G.P.W v) (h' : Matrix _ _ (X.G.P.Qq v)) ∧
      (h' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) =
        (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)) *
          dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) := by
    intro v
    have hS := X.G.P.setting v
    have := hS.frac_alt
    have hp0 : (p : X.G.P.Qq v) ≠ 0 := pQ_ne hS.p_unif
    rcases h4 v with ⟨h0, hL⟩ | ⟨_, he⟩
    · obtain ⟨g, hg, hgL⟩ := h2 v
      have h0' : i0 v = 0 := h0
      refine ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit g hg, ?_, hgL, ?_⟩
      · show L'' v = _
        rw [hL]; exact hgL
      · have : dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v) = 1 := by
          unfold dgQ
          rw [h0']
          simp
        rw [this, mul_one]
    · obtain ⟨g, hg, hsrc, htgt⟩ := Formalism.L2.G.Model.edgeBasis hS _ _ _ he
      have hd : IsUnit (g * dgQ (X.G.P.Qq v) p ((X.Pj (j + 1)).m + 1) (i0 v)).det := by
        rw [Matrix.det_mul]
        exact hg.mul (isUnit_iff_ne_zero.2 (dgQ_det_ne _ _ _ _ hp0))
      exact ⟨Matrix.nonsingInvUnit g hg, Matrix.nonsingInvUnit _ hd, hsrc, htgt, rfl⟩
  choose g' h' h1 h2' h3 using key
  refine ⟨g', h', h1, h2', fun b => ?_⟩
  rw [h3 b.1, ← mF_dgQ X j b i0]
  unfold mF
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  exact Matrix.map_mul (f := (X.G.P.ι b.1).comp (X.G.P.σ b.1 ^ b.2.val : X.G.P.Qq b.1 ≃+* X.G.P.Qq b.1).toRingHom)

end Formalism.L2.PairingIndexBounds.Ent
end
end
