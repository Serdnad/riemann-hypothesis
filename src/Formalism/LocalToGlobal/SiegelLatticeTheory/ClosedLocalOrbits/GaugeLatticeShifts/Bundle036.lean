module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle033
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle008
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

private theorem crd_toLin_map_eq_mulVec_crd {D : D7} (X : HidaSetting D) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (y : (VS D).V) : X.crd (Matrix.toLin X.bas X.bas (M.map X.ιE) y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i

  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, ← h, Matrix.mulVec, dotProduct,
  Matrix.map_apply, map_sum, map_mul, RingEquiv.symm_apply_apply]

theorem memIsomOf_holds : MemIsomOf := by
  intro D X g hg
  let A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E := (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  let B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
    ((g⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hinj : ∀ y y' : (VS D).V, X.crd y = X.crd y' → y = y' := by
    intro y y' h
    apply X.bas.repr.injective
    ext i
    have := congrFun h i
    simpa [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] using this
  let n : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas (A.map X.ιE)) (Matrix.toLin X.bas X.bas (B.map X.ιE))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
  have hn : ∀ y, X.crd (n y) = A *ᵥ X.crd y := fun y => crd_toLin_map_eq_mulVec_crd X A y
  refine ⟨n, ?_, hn⟩
  intro x y
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X (n x) (n y), ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y,
    hn, hn, Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hg]

end Formalism.L2.SG.TermOp.Vanish
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def coordSc (r : ℕ) (sc : ℝ) (q : (Fin r → ℂ) × ℂ) : Fin (r + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) (fun a : Fin r => (((sc : ℂ) ^ (r - a.1))⁻¹) ^ 2 * q.1 a) q.2

def psiP {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (u : Formalism.REAL.UJ ε) : Formalism.QuantumDeterminants.Mt k r :=
  fun i j => (P⁻¹ * uMat u * P) i j

def PFrame : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' →
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r ∧ IsUnit P.det ∧
      (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) ∧
      ∃ zH zH' : Fin (2 * r + k + 1) → ℂ, Formalism.QuantumDeterminants.inWb k r zH ∧ Formalism.QuantumDeterminants.inWb k r zH' ∧
        P *ᵥ zH = z ∧ P *ᵥ zH' = z' ∧ Formalism.QuantumDeterminants.Tz k r zH = T ∧ Formalism.QuantumDeterminants.Tz k r zH' = T'

def SetCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH →
    ∀ u : Formalism.REAL.UJ ε, u ∈ SLoc ε e z ↔ P⁻¹ * uMat u * P ∈ Formalism.QuantumDeterminants.Sset k r zH

def HaarCorr : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z zH : Fin (2 * r + k + 1) → ℂ)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r →
    IsUnit P.det →
    (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) → Formalism.QuantumDeterminants.inWb k r zH → P *ᵥ zH = z →
    0 < Formalism.QuantumDeterminants.Tz k r zH → 1 ≤ k →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ((Formalism.REAL.muG ε).map (psiP P)) ∧
    ∀ μW μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r zH) μW →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
      ∀ μS : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS →
        ∃ c : ℝ, 0 < c ∧ μS.map (psiP P) = ENNReal.ofReal c • Formalism.MainNotions.S.muS μW μN

def ZBig : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ)
    (z z' zH zH' : Fin (2 * r + k + 1) → ℂ) (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (sc : ℝ),
    Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r → IsUnit P.det → (∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) →
    Formalism.QuantumDeterminants.inWb k r zH → Formalism.QuantumDeterminants.inWb k r zH' → P *ᵥ zH = z → P *ᵥ zH' = z' → 0 < sc →
    ∀ μsec, Formalism.QuantumDeterminants.IsSection k r zH zH' μsec →
    ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) → Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq q.2 →
      Formalism.REAL.inUJ ε (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) ∧
      Zhat ε (famSc sc e z) (famSc sc e z') (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) =
        Matrix.diagonal (coordSc r sc q)

def BigMem : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)

def CoordW : Prop :=
  ∀ (r k : ℕ) (T T' sc : ℝ), 1 ≤ k → 0 < T → 0 < T' → 0 < sc →
    ∃ κ : ℝ, 0 < κ ∧ ∀ F : (Fin (r + 1) → ℂ) → ℝ≥0∞,
      ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
        ENNReal.ofReal κ * ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))

def SecWb : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' → ∃ μsec, Formalism.QuantumDeterminants.IsSection k r z z' μsec

def JacExGoodN : Prop :=
  ∀ (r k : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e : Fin r → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (T T' sc : ℝ), FrameLoc ε k e z z' T T' → GoodPos ε e z z' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

theorem jacExGood_of_N (H : JacExGoodN) : JacExGood := by
  intro n r k ε e z z' T T' sc hF hG hsc
  have hn : n = 2 * r + k + 1 := by have := hF.dim; omega
  subst hn
  exact H r k ε e z z' T T' sc hF hG hsc

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

section MemConj

variable {D : D7} (X : HidaSetting D)

theorem mc_gr_mul_inv (M : GL (Fin X.B.I.n) X.B.I.E) :
    Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := by
  unfold Gr
  have h1 := Bm_mul_Bm' X
  have h2 : Bm' X * Bm X = 1 := Bm'_mul_Bm X
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul]
  have h3 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *
      (((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X) = Bm X := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h3, h2]

theorem mc_gr_unitary (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (Gr X (M : Matrix _ _ _))ᴴ * JB X * Gr X (M : Matrix _ _ _) = JB X := by
  have hc : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ := by
    ext i j
    unfold Formalism.UG.cT
    simp [Matrix.conjTranspose_apply, starRingEnd_apply]
  have hMJ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := by
    rw [← hc]
    exact hM
  have hJB : JB X = (Bm X)ᴴ * X.B.I.J * Bm X := by
    ext k k'
    unfold JB hE Formalism.UG.hform Bm
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, starRingEnd_apply]
    rw [Finset.sum_comm]
  have h1 := Bm_mul_Bm' X
  have h5 : ∀ Z : Matrix (Fin X.B.I.n) (Kap X) X.B.I.E, (Bm' X)ᴴ * ((Bm X)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
  rw [hJB]
  unfold Gr
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul, h5]
  have h4 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * (X.B.I.J *
      ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X)) = X.B.I.J * Bm X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMJ]
  rw [h4]

theorem memConjOf_holds : MemConjOf := by
  intro D X M hM
  letI : Invertible (2 : X.B.I.E) := invertibleOfNonzero two_ne_zero
  have h1 : Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := mc_gr_mul_inv X M
  have h2 : Gr X (↑M⁻¹ : Matrix _ _ _) * Gr X (M : Matrix _ _ _) = 1 := by
    have := mc_gr_mul_inv X M⁻¹
    rwa [inv_inv] at this
  have hU := mc_gr_unitary X M hM
  refine ⟨fun Z => ?_, fun Z hZ => ?_, ?_⟩
  ·
    have hBB : ∀ Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, Bm X * (Bm' X * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, Bm_mul_Bm', Matrix.one_mul]
    unfold Formalism.L2.SG.Pf.UnipB.gE
    rw [← conj_cay h1]
    unfold Gr
    simp only [Matrix.mul_assoc, hBB, Bm_mul_Bm', Matrix.mul_one]
  ·
    set G := Gr X (M : Matrix _ _ _) with hG
    set G' := Gr X (↑M⁻¹ : Matrix _ _ _) with hG'
    have hA : Gᴴ * JB X = JB X * G' := by
      calc Gᴴ * JB X = Gᴴ * JB X * (G * G') := by rw [h1, Matrix.mul_one]
        _ = Gᴴ * JB X * G * G' := by simp only [Matrix.mul_assoc]
        _ = JB X * G' := by rw [hU]
    have hB : G'ᴴ * JB X = JB X * G := by
      calc G'ᴴ * JB X = G'ᴴ * (Gᴴ * JB X * G) := by rw [hU]
        _ = (G * G')ᴴ * JB X * G := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = JB X * G := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
    calc (G' * Z * G)ᴴ * JB X = Gᴴ * Zᴴ * (G'ᴴ * JB X) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Gᴴ * (Zᴴ * JB X) * G := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = Gᴴ * (-(JB X * Z)) * G := by rw [hZ]
      _ = -(Gᴴ * JB X * Z * G) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(JB X * (G' * Z * G)) := by rw [hA]; simp only [Matrix.mul_assoc]
  ·
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
      ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2))
    have hint : ∀ z ∈ ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2)),
        (y.natAbs : X.B.I.E) * z ∈ integralClosure ℤ X.B.I.E := by
      intro z hz
      rw [mem_integralClosure_iff]
      have h := hy z hz
      rw [zsmul_eq_mul] at h
      rcases Int.natAbs_eq y with e | e
      · rw [e] at h
        simpa using h
      · rw [e] at h
        have h' := h.neg
        simpa [neg_mul] using h'
    have hP : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (↑M⁻¹ : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    have hQ : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (M : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    let P1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hP i j⟩
    let Q1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hQ i j⟩
    have hP1 : P1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (↑M⁻¹ : Matrix _ _ _) := by
      ext i j
      rfl
    have hQ1 : Q1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (M : Matrix _ _ _) := by
      ext i j
      rfl
    have hmap : ∀ U V : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
        (U * V).map (fun a => (a : X.B.I.E)) =
          U.map (fun a => (a : X.B.I.E)) * V.map (fun a => (a : X.B.I.E)) :=
      fun U V => Matrix.map_mul (f := algebraMap (𝓞 X.B.I.E) X.B.I.E)
    refine ⟨y.natAbs * y.natAbs, Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Int.natAbs_ne_zero.mpr hy0) (Int.natAbs_ne_zero.mpr hy0)), fun d A => ⟨P1 * A * Q1, ?_⟩⟩
    rw [hmap, hmap, hP1, hQ1]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul]
    congr 1
    ring

end MemConj

end Formalism.L2.SG.TermOp.Vanish
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

theorem memPtOf_holds : MemPtOf := by
  intro D X Z n hni hn
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hni
  refine ⟨x, hx, fun v => ?_⟩
  obtain ⟨M', -, h1, -, h3⟩ := hx
  have hM : (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = gE X Z := by
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨y, hy⟩ := Formalism.L2.SG.Pf.crd_surj X (Pi.single i 1)
    rw [← hy, ← h3, hn]
  unfold Mv
  rw [h1 v, hM, gE_real]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one, cay_map]

end Formalism.L2.SG.TermOp.Vanish
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.Pf.FlagCoordinates

variable {D : D7} (X : HidaSetting D)

theorem gE_sub_one (Z : Matrix (Kap X) (Kap X) X.B.I.E) :
    Formalism.L2.SG.Pf.UnipB.gE X Z - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X := by
  unfold Formalism.L2.SG.Pf.UnipB.gE
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bm_mul_Bm']

theorem Bm_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → X.B.I.E) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bm X *ᵥ c ∈ Submodule.span X.B.I.E (X.eR '' S) := by
  rw [Bm_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem flag_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (a : Fin D.R.rS) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.eR a ∈ Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hB : Bm' X *ᵥ X.eR a = Pi.single (Sum.inl a) 1 := by
    rw [Bm'_mulVec]
    funext k
    rw [show X.eR a = bv X (Sum.inl a) from rfl, cE_bv]
    simp [Pi.single_apply]
  rw [hB]
  refine Bm_mulVec_mem X _ _ fun k hk => ?_
  rw [mulVec_single_one]
  refine cay_sub_one _ hZ k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem orth_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (x : Fin X.B.I.n → X.B.I.E)
    (hx : ∀ a, hE X (X.eR a) x = 0) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ x ∈ Submodule.span X.B.I.E (X.eR '' Set.univ) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Bm'_mulVec]
  refine Bm_mulVec_mem X Set.univ _ fun k hk => ?_
  have hk' : ∀ b, k ≠ Sum.inl b := by
    rintro b rfl
    exact hk ⟨b, Set.mem_univ _, rfl⟩
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hlk := lvk_notinl X k hk'
  rcases j with b | i | b
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_w]; omega), zero_mul]
  · rw [show cE X x (Sum.inr (Sum.inr b)) = hE X (X.eR b) x from rfl, hx b, mul_zero]

theorem crd_desc (S : Set (Fin D.R.rS)) (v : (VS D).V)
    (hv : X.crd v ∈ Submodule.span X.B.I.E (X.eR '' S)) :
    v ∈ Submodule.span D.host.E (X.eX '' S) := by
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun X.B.I.E).1 hv
  have e : v = ∑ i : S, X.ιE (c i) • X.eX i := by
    rw [← Formalism.L2.SG.Pf.Level.toV_crd X v, ← hc, Formalism.L2.SG.Pf.Level.toV_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.L2.SG.Pf.Level.toV_smul, show X.eR i = X.crd (X.eX i) from rfl, Formalism.L2.SG.Pf.Level.toV_crd]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩)

end Formalism.L2.SG.Pf.FlagCoordinates

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.FlagCoordinates

theorem memFlagOf_holds : MemFlagOf := by
  intro D X u Z n hZ hn
  have hm : ∀ v, (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.crd v = X.crd (n v - v) := fun v => Formalism.L2.SG.Pf.Vanish2.mcrd X hn v
  have hXf : ∀ k, Xflag (lf D (X.Fu u)) k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k
    show Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < k}) = _
    rw [X.Fu_e]
  have hXs : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (X.eX '' Set.univ) := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e, Set.image_univ]
  have he : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
    intro a
    have hd := flag_coord X hZ a
    rw [show X.eR a = X.crd (X.eX a) from rfl, hm] at hd
    exact crd_desc X _ _ hd
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [hXf] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨b, lt_of_lt_of_le hb (Nat.lt_succ_iff.1 ha), rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_sub_add_comm]
      exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  · have hx0 : ∀ a, hE X (X.eR a) (X.crd x) = 0 := by
      intro a
      have hmem : X.eX a ∈ Xsp (lf D (X.Fu u)) := by
        rw [hXs]
        exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩
      have h0 : (VS D).hT (X.eX a) x = 0 := (Formalism.L2.SG.Pf.mem_orth_iff _ _).1 hx _ hmem
      rw [show X.eR a = X.crd (X.eX a) from rfl, hE_crd, h0, map_zero]
    have hd := orth_coord X hZ _ hx0
    rw [hm] at hd
    rw [hXs]
    exact crd_desc X _ _ hd

end Formalism.L2.SG.TermOp.Vanish
end
end
