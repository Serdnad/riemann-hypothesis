module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle194
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

lemma nf_norm_sum_sq_le {E : Type*} [SeminormedAddCommGroup E] {n : ℕ} (x : Fin n → E) :
    ‖∑ i, x i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  have h1 : ‖∑ i, x i‖ ≤ ∑ i, ‖x i‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun i => ‖x i‖)
  calc ‖∑ i, x i‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa using h2

lemma nf_globCoef_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {Θ : B.DiffOp k r Wp Wq} {d d' : ℝ}
    (h : CutMP.GlobCoef Θ d) (hd : d ≤ d') : CutMP.GlobCoef Θ d' := by
  intro Tm hTm
  obtain ⟨h1, h2, h3⟩ := h Tm hTm
  refine ⟨h1, h2, fun m => ?_⟩
  obtain ⟨Cb, hCb⟩ := h3 m
  refine ⟨max Cb 0, fun u w hu hw hl g hg => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hp : B.gN g ^ d ≤ B.gN g ^ d' := Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hp0 : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (by linarith) _
  obtain ⟨a1, a2⟩ := hCb u w hu hw hl g hg
  constructor
  · calc _ ≤ Cb * B.gN g ^ d := a1
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ d' := mul_le_mul_of_nonneg_left hp (le_max_right _ _)
  · calc _ ≤ Cb * B.gN g ^ d := a2
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ d' := mul_le_mul_of_nonneg_left hp (le_max_right _ _)

lemma nfOpOK_mono {C C' : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {N : ℕ} {Th : B.DiffOp P.k P.r Wp Wq} (h : NFOpOK C p N Th) (hC : C ≤ C') :
    NFOpOK C' p N Th := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hn : 0 ≤ CutMP.nDim P.k P.r := by unfold CutMP.nDim; positivity
  refine ⟨h1, h2, nf_globCoef_mono h3 ?_, le_trans h4 ?_⟩
  · have : 0 ≤ ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
    have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1) =
        x * (((P.r : ℝ) + 1) * CutMP.nDim P.k P.r * ((N : ℝ) + 1)) := fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hC this
  · have : 0 ≤ CutMP.nDim P.k P.r * ((N : ℝ) + 1) := by positivity
    have e : ∀ x : ℝ, x * CutMP.nDim P.k P.r * ((N : ℝ) + 1) = x * (CutMP.nDim P.k P.r * ((N : ℝ) + 1)) :=
      fun x => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hC this

lemma nf_empty_bound (hV : NFVMul) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ N : ℕ) (hNp : N ≤ 2 * p₀) (χ : ℝ → ℝ) (K : ℝ)
    (Th₀ Th₁ : B.DiffOp P.k P.r Wp Wq)
    (hap : ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
        B.opApply Th₀ F g = F g ∧ B.opApply Th₁ F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • F g)
    (ε : ℝ) (c : Fin (P.r + 1) → ℂ) (hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1))
    (hG : 0 < TBB.Gp p (TBB.bigPt P.r c)) (hK : |χ (TBB.Gp p (TBB.bigPt P.r c) / ε)| ≤ K) :
    ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) [] c‖ ≤
      K ^ 2 * ∑ t : Fin 2, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (B.opApply (![Th₀, Th₁] t) f) (P.r + 1) [] (TBB.bigPt P.r c) := by
  set γ := TBB.bigPt P.r c with hγ
  have hH : D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε =
      fun g => (((fun y => χ (y / ε) * y ^ p₀) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • f g := by
    funext g
    simp only [D.cutF, TBBx4.fpm, ContinuousLinearMap.comp_id, smul_smul, Complex.ofReal_mul, Complex.ofReal_pow]
  have h0 : B.opApply Th₀ f = f := funext fun g => (hap f g).1
  have h1 : B.opApply Th₁ f = fun g => (((fun y : ℝ => y ^ N) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • f g :=
    funext fun g => (hap f g).2
  show ‖TBB.Ew p (fun _ => 1) _ (P.r + 1) [] γ‖ ≤ _
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hH, h0, h1, TBBx2.Tri.Ew_top p _ hl, TBBx2.Tri.Ew_top p _ hl, TBBx2.Tri.Ew_top p _ hl,
    hV Wp Wq P p (fun y => χ (y / ε) * y ^ p₀) f γ hl hG, hV Wp Wq P p (fun y : ℝ => y ^ N) f γ hl hG, TBBx4.hsVec_real_smul_sq, TBBx4.hsVec_real_smul_sq]
  set G := TBB.Gp p γ
  set S := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ)
  set v := ‖B.hsVec (p.V f γ)‖ ^ 2
  set x := χ (G / ε)
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hv : 0 ≤ v := sq_nonneg _
  have hG0 : 0 ≤ G := hG.le
  have hx2 : x ^ 2 ≤ K ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hK 2
  have hGa : G ^ (2 * p₀) = G ^ (2 * p₀ - N) * G ^ N := by rw [← pow_add, Nat.sub_add_cancel hNp]
  have hGN : G ^ N ≤ 1 + (G ^ N) ^ 2 := by nlinarith [sq_nonneg (G ^ N - 1), pow_nonneg hG0 N]
  have hLHS : 0 ≤ S * ((x * G ^ p₀) ^ 2 * v) := by positivity
  rw [Real.norm_of_nonneg hLHS, Real.norm_of_nonneg hG0]
  have e1 : S * ((x * G ^ p₀) ^ 2 * v) = (S * v * G ^ (2 * p₀ - N)) * (x ^ 2 * G ^ N) := by
    rw [mul_pow, ← pow_mul, mul_comm p₀ 2, hGa]; ring
  have e2 : K ^ 2 * (G ^ (2 * p₀ - N) * (S * v) + G ^ (2 * p₀ - N) * (S * ((G ^ N) ^ 2 * v))) =
      (S * v * G ^ (2 * p₀ - N)) * (K ^ 2 * (1 + (G ^ N) ^ 2)) := by ring
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul hx2 hGN (pow_nonneg hG0 N) (sq_nonneg K)

lemma nf_comp_sum {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {n : ℕ} (E : Wp →L[ℂ] Wp) (a : Fin n → ℂ) (W : Fin n → (Wq →L[ℂ] Wp)) :
    E.comp (∑ q, a q • W q) = ∑ q, a q • E.comp (W q) := by
  ext v

  simp [map_sum, map_smul]

lemma nf_block {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ} (E : Wp →L[ℂ] Wp) (a : Fin n → ℝ) (Kt : ℝ)
    (ha : ∀ q, |a q| ≤ Kt) (W : Fin n → (Wq →L[ℂ] Wp)) (d : ℝ) :
    d ^ 2 * ‖B.hsVec (E.comp (∑ q, ((a q : ℝ) : ℂ) • W q))‖ ^ 2 ≤
      (n : ℝ) * Kt ^ 2 * ∑ q, d ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
  rw [nf_comp_sum, TBBx2.Tri.hsVec_sum]
  simp only [TBBx2.Tri.hsVec_smul]
  have h1 := nf_norm_sum_sq_le (fun q => ((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q)))
  have h2 : ∀ q, ‖((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2 ≤ Kt ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
    intro q
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have : |a q| ^ 2 ≤ Kt ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (ha q) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h3 : ∑ q, ‖((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2 ≤ Kt ^ 2 * ∑ q, ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun q _ => h2 q
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc d ^ 2 * ‖∑ q, ((a q : ℝ) : ℂ) • B.hsVec (E.comp (W q))‖ ^ 2
      ≤ d ^ 2 * ((n : ℝ) * (Kt ^ 2 * ∑ q, ‖B.hsVec (E.comp (W q))‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h3 hn)) (sq_nonneg d)
    _ = (n : ℝ) * Kt ^ 2 * ∑ q, d ^ 2 * ‖B.hsVec (E.comp (W q))‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => by ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem vector_multiplication_holds : NFVMul := by
  intro Wp Wq _ _ _ _ _ _ P p φ F γ _hγ hG
  by_cases hc : ((φ (TBB.Gp p γ) : ℝ) : ℂ) = 0
  · rw [hc, zero_smul]
    unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · have hae : ∀ᵐ q ∂p.T.base.μSS,
          D.orbIntegrand p.T.base h2.choose
            (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) q =
          (1 : ℂ) • D.orbIntegrand p.T.base h2.choose (fun _ => (0 : Wq →L[ℂ] Wp)) q := by
        filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
        have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
          rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
          rfl
        unfold D.orbIntegrand B.rho
        simp [hGq, hc]
      rw [TBBx4.orbJ_smul_ae _ _ _ _ _ _ one_ne_zero hae, one_smul]
      have h0 := TBBx4.orbJ_smul_ae p.T.base h2.choose
        (D.muR p.T.base h2.choose (h1.1.2 ▸ D.ptPerm γ)) (fun _ => (0 : Wq →L[ℂ] Wp))
        (fun _ => (0 : Wq →L[ℂ] Wp)) (2 : ℂ) two_ne_zero
        (ae_of_all _ fun q => by unfold D.orbIntegrand B.rho; simp)
      rw [two_smul] at h0
      simpa using h0
    · simp
    · simp
  · unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · apply TBBx4.orbJ_smul_ae _ _ _ _ _ _ hc
      filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
      have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
        rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
        rfl
      unfold D.orbIntegrand B.rho
      simp only [hGq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [smul_comm]
    · simp
    · simp

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieBasisConstruction

def lieSubR (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := by
    intro X Y hX hY
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * _ + _ * X) + (Yᴴ * _ + _ * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by
    unfold B.inLie
    simp
  smul_mem' := by
    intro c X hX
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

end LieBasisConstruction

theorem lie_basis_holds : LieBasis := by
  intro k r
  let S := LieBasisConstruction.lieSubR k r
  let b := Module.finBasis ℝ S
  let L0 : (Fin (Module.finrank ℝ S) → ℝ) →ₗ[ℝ] B.Mat k r := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hinj : LinearMap.ker L0 = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact S.injective_subtype.comp b.equivFun.symm.injective
  obtain ⟨M0, hM0⟩ := L0.exists_leftInverse_of_injective hinj
  have hML : ∀ y, M0 (L0 y) = y := fun y => LinearMap.congr_fun hM0 y
  refine ⟨Module.finrank ℝ S, LinearMap.toContinuousLinearMap L0, LinearMap.toContinuousLinearMap M0,
    fun x => (b.equivFun.symm x).2, fun x => hML x, fun X hX => ?_⟩
  have e : L0 (b.equivFun ⟨X, hX⟩) = X := by simp [L0]
  show L0 (M0 X) = X
  calc L0 (M0 X) = L0 (M0 (L0 (b.equivFun ⟨X, hX⟩))) := by rw [e]
    _ = X := by rw [hML, e]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def MC (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

noncomputable instance instNRMC (m : ℕ) : NormedRing (MC m) := Matrix.linftyOpNormedRing

noncomputable instance instNAMC (m : ℕ) : NormedAlgebra ℝ (MC m) := Matrix.linftyOpNormedAlgebra

instance instFDMC (m : ℕ) : FiniteDimensional ℝ (MC m) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin m) (Fin m) ℂ))

instance instCSMC (m : ℕ) : CompleteSpace (MC m) := FiniteDimensional.complete ℝ (MC m)

def toMC (m : ℕ) : Matrix (Fin m) (Fin m) ℂ ≃L[ℝ] MC m :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.refl ℝ (Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℝ] MC m)

def cayMC {m : ℕ} (g₀ X : MC m) : MC m := g₀ * ((1 + X) * Ring.inverse (1 - X))

def cinvMC {m : ℕ} (a Y : MC m) : MC m := (a * Y - 1) * Ring.inverse (a * Y + 1)

theorem cay_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun X : B.Mat k r => g₀ * cay X) = fun X => (toMC _).symm (cayMC (toMC _ g₀) (toMC _ X)) := by
  funext X
  show g₀ * ((1 + X) * (1 - X)⁻¹) = g₀ * ((1 + X) * Ring.inverse (1 - X))
  rw [Matrix.nonsing_inv_eq_ringInverse]

theorem cayInv_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) = fun m => (toMC _).symm (cinvMC (toMC _ g₀⁻¹) (toMC _ m)) := by
  funext m
  show (g₀⁻¹ * m - 1) * (g₀⁻¹ * m + 1)⁻¹ = (g₀⁻¹ * m - 1) * Ring.inverse (g₀⁻¹ * m + 1)
  rw [Matrix.nonsing_inv_eq_ringInverse (g₀⁻¹ * m + 1)]

theorem cayMC_contDiffAt {m : ℕ} (g₀ X : MC m) (hX : IsUnit (1 - X)) : ContDiffAt ℝ ∞ (cayMC g₀) X := by
  obtain ⟨u, hu⟩ := hX
  have h1 : ContDiffAt ℝ ∞ (fun Y : MC m => Ring.inverse (1 - Y)) X := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp X (contDiffAt_const.sub contDiffAt_id)
  exact contDiffAt_const.mul ((contDiffAt_const.add contDiffAt_id).mul h1)

theorem cinvMC_contDiffAt {m : ℕ} (a Y : MC m) (hY : IsUnit (a * Y + 1)) : ContDiffAt ℝ ∞ (cinvMC a) Y := by
  obtain ⟨u, hu⟩ := hY
  have h1 : ContDiffAt ℝ ∞ (fun Z : MC m => Ring.inverse (a * Z + 1)) Y := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp Y ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  exact ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const).mul h1

theorem cayley_smoothness_holds : CaySmooth := by
  intro k r g₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      (continuous_const.sub continuous_id)).preimage (toMC _).continuous
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      ((continuous_const.mul continuous_id).add continuous_const)).preimage (toMC _).continuous
  · rw [cay_eq_MC g₀]
    intro X hX
    have hX' : IsUnit (1 - toMC _ X) := hX
    exact ((toMC _).symm.contDiff.contDiffAt.comp X
      ((cayMC_contDiffAt (toMC _ g₀) _ hX').comp X (toMC _).contDiff.contDiffAt)).contDiffWithinAt
  · rw [cayInv_eq_MC g₀]
    intro m hm
    have hm' : IsUnit (toMC _ g₀⁻¹ * toMC _ m + 1) := hm
    exact ((toMC _).symm.contDiff.contDiffAt.comp m
      ((cinvMC_contDiffAt (toMC _ g₀⁻¹) _ hm').comp m (toMC _).contDiff.contDiffAt)).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace UnitInverseArithmetic

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mul_inv_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem inv_mul_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem isUnit_of_mul_one {A B : Matrix n n ℂ} (h : A * B = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse h)

theorem half_two : ((2 : ℂ)⁻¹) • ((1 : Matrix n n ℂ) + 1) = 1 := by
  rw [← two_smul ℂ (1 : Matrix n n ℂ), smul_smul]; norm_num

theorem half_double (A : Matrix n n ℂ) : ((2 : ℂ)⁻¹) • (A + A) = A := by
  rw [← two_smul ℂ A, smul_smul]; norm_num

theorem fwd {H X : Matrix n n ℂ} (hX : Xᴴ * H + H * X = 0) (hu : IsUnit (1 - X)) :
    ((1 + X) * (1 - X)⁻¹)ᴴ * H * ((1 + X) * (1 - X)⁻¹) = H ∧ IsUnit ((1 + X) * (1 - X)⁻¹ + 1) ∧
      ((1 + X) * (1 - X)⁻¹ - 1) * ((1 + X) * (1 - X)⁻¹ + 1)⁻¹ = X := by
  set V := (1 - X)⁻¹ with hV
  have h1 : (1 - X) * V = 1 := mul_inv_of_isUnit hu
  have h2 : V * (1 - X) = 1 := inv_mul_of_isUnit hu
  have hXV : X * V = V - 1 := by
    have e := h1
    rw [Matrix.sub_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hg1 : (1 + X) * V + 1 = V + V := by
    rw [Matrix.add_mul, Matrix.one_mul, hXV]; abel
  have hq : (V + V) * ((2⁻¹ : ℂ) • (1 - X)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  refine ⟨?_, ?_, ?_⟩
  · have ha : (1 + Xᴴ) * H = H * (1 - X) := by
      have e : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
      rw [Matrix.add_mul, Matrix.one_mul, e, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    have hb : H * (1 + X) = (1 - Xᴴ) * H := by
      have e : H * X = -(Xᴴ * H) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hX)
      rw [Matrix.mul_add, Matrix.mul_one, e, Matrix.sub_mul, Matrix.one_mul, sub_eq_add_neg]
    have hc : (1 - X) * (1 + X) = (1 + X) * (1 - X) := by noncomm_ring
    have hW : Vᴴ * (1 - Xᴴ) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one] at e
    calc ((1 + X) * V)ᴴ * H * ((1 + X) * V)
        = Vᴴ * (((1 + Xᴴ) * H) * ((1 + X) * V)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * (((1 - X) * (1 + X)) * V)) := by rw [ha]; simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * ((1 + X) * ((1 - X) * V))) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = (Vᴴ * (1 - Xᴴ)) * H := by
          rw [h1, Matrix.mul_one, hb]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hW, Matrix.one_mul]
  · rw [hg1]; exact isUnit_of_mul_one hq
  · rw [hg1, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : ((1 + X) * V - 1) * (1 - X) = X + X := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, Matrix.one_mul]; abel
    rw [e, half_double]

theorem bwd {H g : Matrix n n ℂ} (hg : gᴴ * H * g = H) (hu : IsUnit (g + 1)) :
    ((g - 1) * (g + 1)⁻¹)ᴴ * H + H * ((g - 1) * (g + 1)⁻¹) = 0 ∧ IsUnit (1 - (g - 1) * (g + 1)⁻¹) ∧
      (1 + (g - 1) * (g + 1)⁻¹) * (1 - (g - 1) * (g + 1)⁻¹)⁻¹ = g := by
  set P := (g + 1)⁻¹ with hP
  have h1 : (g + 1) * P = 1 := mul_inv_of_isUnit hu
  have h2 : P * (g + 1) = 1 := inv_mul_of_isUnit hu
  have hgP : g * P = 1 - P := by
    have e := h1
    rw [Matrix.add_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hX : (g - 1) * P = 1 - P - P := by rw [Matrix.sub_mul, Matrix.one_mul, hgP]
  have hOne : (1 : Matrix n n ℂ) - (1 - P - P) = P + P := by abel
  have hq : (P + P) * ((2⁻¹ : ℂ) • (g + 1)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · have hQ : Pᴴ * (gᴴ + 1) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one] at e
    have hm : H * (g + 1) + (gᴴ + 1) * H = (gᴴ + 1) * H * (g + 1) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hg]; abel
    have key : Pᴴ * H + H * P = H := by
      calc Pᴴ * H + H * P = Pᴴ * (H * ((g + 1) * P)) + (Pᴴ * (gᴴ + 1)) * (H * P) := by
            rw [h1, hQ, Matrix.mul_one, Matrix.one_mul]
        _ = Pᴴ * ((H * (g + 1) + (gᴴ + 1) * H) * P) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (Pᴴ * (gᴴ + 1)) * H * ((g + 1) * P) := by rw [hm]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hQ, h1, Matrix.one_mul, Matrix.mul_one]
    have key' : Pᴴ * H = H - H * P := eq_sub_of_add_eq key
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, key']
    abel
  · rw [hOne]; exact isUnit_of_mul_one hq
  · rw [hOne, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : (1 + (1 - P - P)) * (g + 1) = g + g := by
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [e, half_double]

end UnitInverseArithmetic

theorem cayley_algebraic_holds : CayAlg := by
  intro k r
  refine ⟨fun X hX hu => ?_, fun g hg hu => ?_⟩
  · exact UnitInverseArithmetic.fwd hX hu
  · exact UnitInverseArithmetic.bwd hg hu

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
