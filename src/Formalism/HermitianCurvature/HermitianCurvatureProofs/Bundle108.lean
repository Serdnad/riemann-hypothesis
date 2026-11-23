module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle102
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle103
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictUpperNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem tc_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem tc_hsVec_eq_zero {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => by
    have := congrArg (fun w => w i) h
    simpa [B.hsVec] using this
  have hl : A.toLinearMap = (0 : Wq →ₗ[ℂ] Wp) :=
    (stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => by simpa using h' i
  ext v
  exact LinearMap.congr_fun hl v

end hs

theorem tc_up_unique {P : M.Par} {l : ℕ} {π ρ ρ' : M.Ty P} (h : M.Up P l π ρ) (h' : M.Up P l π ρ') : ρ = ρ' := by
  funext i
  apply Fin.ext
  rw [h i, h' i]

theorem theta_constancy_assembly : ThConstOfCut := by
  intro hPR hMC hLN hPF
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw'
  have main : ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c : ℂ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          c • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf) := by
    intro π ρ hup
    obtain ⟨n, q, hq⟩ := hPR Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    obtain ⟨c₁, c₂, hc⟩ := hMC Wp Wq P Bs hk X d hAct l hl S hS Pr hPr Bw Bw' hBw hBw' π ρ hup
    have hGG : ∀ ζ ∈ Gauge.GC.Ann P, (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) ≠ 0 := by
      intro ζ hζ
      have : (0 : ℝ) < Complex.normSq ζ - P.TT := by
        have := hζ; simp only [Gauge.GC.Ann, Set.mem_ofPred_eq] at this; linarith
      exact pow_ne_zero _ (by exact_mod_cast this.ne')
    by_cases hc2 : c₂ = 0
    · refine ⟨0, fun ζ hζ Xf hXf hfix => ?_⟩
      have hB0 := (hc ζ hζ Xf hXf hfix).2
      rw [hc2, zero_mul, sq_eq_zero_iff, norm_eq_zero] at hB0
      have hB0' := tc_hsVec_eq_zero hB0
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hB0', smul_zero] at h1
      rw [zero_smul]
      exact (smul_eq_zero.1 h1).resolve_left (hGG ζ hζ)
    ·
      have hTT : 0 ≤ P.TT := by
        have := hAct.1.1
        exact mul_nonneg this.T_pos.le this.T'_pos.le
      have hmod : ∀ x : ℝ, P.TT < x → Complex.normSq (q.eval (x : ℂ)) = (c₁ / c₂) * (x - P.TT) ^ (2 * n) := by
        intro x hx
        have hx0 : 0 ≤ x := le_trans hTT hx.le
        set ζ : ℂ := ((Real.sqrt x : ℝ) : ℂ) with hζdef
        have hnz : Complex.normSq ζ = x := by
          rw [hζdef, Complex.normSq_ofReal, ← sq, Real.sq_sqrt hx0]
        have hζ : ζ ∈ Gauge.GC.Ann P := by
          show P.TT < Complex.normSq ζ
          rw [hnz]; exact hx
        obtain ⟨Xf, hXf, hfix, hne⟩ := hLN Wp Wq P Bs hAct.1 hk Pr hPr π ζ hζ
        obtain ⟨hS1, hB1⟩ := hc ζ hζ Xf hXf hfix
        have h1 := congrArg (fun w => ‖B.hsVec w‖ ^ 2) (hq ζ hζ Xf hXf hfix)
        simp only [tc_hsVec_smul, norm_smul, mul_pow] at h1
        rw [hS1, hB1, hnz] at h1
        have hX : 0 < ‖B.hsVec Xf‖ ^ 2 := by
          have : B.hsVec Xf ≠ 0 := fun h0 => hne (tc_hsVec_eq_zero h0)
          positivity
        have hnq : ‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 = Complex.normSq (q.eval (x : ℂ)) := by
          rw [Complex.normSq_eq_norm_sq]
        have hng : ‖((x - P.TT : ℝ) : ℂ) ^ n‖ ^ 2 = (x - P.TT) ^ (2 * n) := by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < x - P.TT), ← pow_mul,
            mul_comm]
        rw [hng] at h1
        have h2 : (‖q.eval ((x : ℝ) : ℂ)‖ ^ 2 * c₂ - (x - P.TT) ^ (2 * n) * c₁) * ‖B.hsVec Xf‖ ^ 2 = 0 := by
          linear_combination (-1 : ℝ) * h1
        have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hX.ne')
        rw [← hnq, div_mul_eq_mul_div, eq_div_iff hc2]
        linarith [h3]
      obtain ⟨c, hcq⟩ := hPF q n P.TT (c₁ / c₂) hmod
      refine ⟨c, fun ζ hζ Xf hXf hfix => ?_⟩
      have h1 := hq ζ hζ Xf hXf hfix
      rw [hcq] at h1
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X] at h1
      have he : ((Complex.normSq ζ : ℝ) : ℂ) - (P.TT : ℂ) = (((Complex.normSq ζ - P.TT : ℝ)) : ℂ) := by push_cast; ring
      rw [he, mul_comm, mul_smul] at h1
      exact smul_right_injective _ (hGG ζ hζ) h1
  classical
  refine ⟨fun π => if h : ∃ ρ, M.Up P l π ρ then (main π h.choose h.choose_spec).choose else 0, ?_⟩
  intro ζ hζ π ρ hup Xf hXf hfix
  have hex : ∃ ρ, M.Up P l π ρ := ⟨ρ, hup⟩
  have hρ : hex.choose = ρ := tc_up_unique hex.choose_spec hup
  simp only [dif_pos hex]
  have := (main π hex.choose hex.choose_spec).choose_spec ζ hζ Xf hXf hfix
  subst hρ
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

def Line {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) (π : M.Ty P) (ζ : ℂ) : Set (Wq →L[ℂ] Wp) :=
  {X | X ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ ∧ (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp X = X}

def LineAtMost : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ (π : M.Ty P), ∀ ζ ∈ Gauge.GC.Ann P, ∀ X ∈ Line P Bs Pr π ζ, ∀ Y ∈ Line P Bs Pr π ζ, X ≠ 0 → ∃ c : ℂ, Y = c • X

def DatumTransit : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ ∧
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ ∧
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂ ∧
      ∀ p ∈ NF.Stab k r z z' μsec ζ₂, (h⁻¹ * p.1 * h, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μsec ζ₁

def SRaise : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π ρ : M.Ty P, M.Up P l π ρ →
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ Line P Bs Pr π ζ, S ζ Xf ∈ Line P Bs Pr ρ ζ

def SNorm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr → ∀ π : M.Ty P,
    ∀ ζ ∈ Gauge.GC.Ann P, ∀ Xf ∈ Line P Bs Pr π ζ, ‖B.hsVec (S ζ Xf)‖ ^ 2 = M.Nrm P l π * ‖B.hsVec Xf‖ ^ 2

def ModConstOfCut : Prop :=
  LineNonzero → LineAtMost → DatumTransit → SRaise → SNorm → SSn.Rep.ThtFacts → ModConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

theorem embedding_map_embedded_group : MMapEmbG := by
  intro k p ρ Z γ y₁ y₂
  simp only [U.mMap, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

theorem embedded_group_measure_preserving : EmbGMuP := by
  intro k p ρ y q
  simp only [U.muP, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem wMat_mul_self_eq_one (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext i j
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  split_ifs <;> simp_all

private theorem wMat_mul_wMat_mul' (d : ℕ) {m : Type*} (X : Matrix (Fin d) m ℂ) : G.wMat d * (G.wMat d * X) = X := by
  rw [← Matrix.mul_assoc, wMat_mul_self_eq_one, Matrix.one_mul]

theorem embedding_map_lower_unipotent : MMapLZU := by
  intro k p ρ l Z u γ hl
  simp only [U.mMap, U.muP, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_nonsing_inv l hl,
    Matrix.mul_assoc, wMat_mul_wMat_mul']

theorem embedded_group_right_action : EmbGRn := by
  intro k p ρ y x hy
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have h2 : (rcAct y x).2 = x.2 := rfl
  have h3 : yᴴ * (Hpk k ρ * y) = Hpk k ρ := by rw [← Matrix.mul_assoc, hy]
  have h4 : ∀ M : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ, yᴴ * (Hpk k ρ * (y * M)) = Hpk k ρ * M := by
    intro M
    rw [← Matrix.mul_assoc (Hpk k ρ), ← Matrix.mul_assoc, h3]
  simp only [U.Rn, U.embG, Ux5.block3_mul_blocks, h1, h2, Matrix.conjTranspose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3, h4,
    neg_zero, smul_zero]

private theorem wP_inv_mul_wP_eq_one {p : ℕ} (σ : Equiv.Perm (Fin p)) : U.wP σ⁻¹ * U.wP σ = 1 := by
  ext a c
  have h : σ (σ⁻¹ a) = a := σ.apply_symm_apply a
  simp only [U.wP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h]

private theorem isUnit_det_wP {p : ℕ} (σ : Equiv.Perm (Fin p)) : IsUnit (U.wP σ).det :=
  Matrix.isUnit_det_of_left_inverse (wP_inv_mul_wP_eq_one σ)

theorem lh_lower {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : G.IsLowerUni (lhOf σ v) := by
  have hinv : (U.wP σ)⁻¹ = U.wP σ⁻¹ := Matrix.inv_eq_left_inv (wP_inv_mul_wP_eq_one σ)
  have hentry : ∀ a b, lhOf σ v a b = U.lowW σ v (σ a) (σ b) := by
    intro a b
    rw [lhOf, hinv]
    simp only [Matrix.mul_apply, U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.Perm.inv_eq_iff_eq, Finset.sum_ite_eq']
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Matrix.transpose_apply, hentry]
    simp [U.lowW]
  · simp only [Matrix.transpose_apply, hentry]
    have h1 : σ j ≠ σ i := fun h => (ne_of_lt hij) (σ.injective h)
    have h2 : ¬ (i < j) := not_lt.mpr hij.le
    simp [U.lowW, Matrix.one_apply, h1, h2]

theorem head_hermitian_eq : HeadHEq := by
  intro p σ d v u
  refine ⟨?_, lh_lower σ v⟩
  simp only [U.headH, lhOf, U.hMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP σ)⁻¹ (U.wP σ), Matrix.nonsing_inv_mul _ (isUnit_det_wP σ), Matrix.one_mul]

private theorem blk2_fin_zero_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 0) ℂ)
    (C : Matrix (Fin 0) (Fin p) ℂ) (D : Matrix (Fin 0) (Fin 0) ℂ) : U.blk2 A B' C D = A := by
  ext i j
  have hi : finSumFinEquiv.symm i = Sum.inl i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  have hj : finSumFinEquiv.symm j = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  simp [U.blk2, Matrix.reindex_apply, hi, hj]

theorem lower_corner_hermitian_zero : ZjHZero := by
  intro p σ d η Z
  simp only [U.ZjH, U.Zj, blk2_fin_zero_eq, Matrix.one_mul, Matrix.mul_one]

theorem lh_unit {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : IsUnit (lhOf σ v).det := by
  have hL : (U.lowW σ v).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ?_]
    · simp [U.lowW]
    · intro i j hij
      have h1 : i < j := OrderDual.toDual_lt_toDual.mp hij
      have h2 : ¬ j < i := not_lt.mpr h1.le
      simp [U.lowW, Matrix.one_apply, ne_of_lt h1, h2]
  simp only [lhOf, Matrix.det_mul, hL, mul_one]
  exact (isUnit_det_wP σ).mul (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_wP σ))

theorem gamma_xi_split : GaXiSplit := by
  intro k p ρ σ d ξ Z h ν h' ν' g hh hν hh'
  have hZ : U.ZjH σ d ξ.2 Z = lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2 := by
    rw [lower_corner_hermitian_zero p σ d ξ.2 Z]
    exact (head_hermitian_eq p σ d ξ.2.2.1 ξ.2.2.2).1
  have hγ : h⁻¹ * ν⁻¹ * g * ν' * h' = (h⁻¹ * ν⁻¹) * g * (ν' * h') := by
    simp only [Matrix.mul_assoc]
  have hE : U.embG k p ρ (ν' * h') = U.embG k p ρ ν' * U.embG k p ρ h' := by
    simp only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  simp only [U.gaXi]
  rw [PBM.rn_inv, hZ]
  show U.Rn k p ρ (-ξ.1.1) * U.mMap k p ρ (lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2) (h⁻¹ * ν⁻¹ * g * ν' * h') *
      U.Rn k p ρ ξ.1.2 = _
  rw [embedding_map_lower_unipotent k p ρ _ _ _ _ (lh_unit σ ξ.2.2.1), hγ, embedding_map_embedded_group, hE]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.embG k p ρ h') (U.muP k p ρ (G.upper ξ.2.2.2)),
    embedded_group_measure_preserving k p ρ h' (G.upper ξ.2.2.2), Matrix.mul_assoc, embedded_group_right_action k p ρ h' ξ.1.2 hh']

theorem embG_nset {k p ρ : ℕ} {y : B.Mat k ρ} (hy : y ∈ QuantumDeterminants.Nset k ρ) : U.embG k p ρ y ∈ QuantumDeterminants.Nset k (p + ρ) := by
  rw [WeylGroupFacts.nset_iff] at hy ⊢
  refine ⟨?_, ?_⟩
  · show (U.embG k p ρ y)ᴴ * Hpk k (p + ρ) * U.embG k p ρ y = Hpk k (p + ρ)
    have hy1 : yᴴ * Hpk k ρ * y = Hpk k ρ := hy.1
    rw [Formalism.FourierDecayAlt.P.hermitian_group_blocks k p ρ, U.embG, Ux3.block3_conjTranspose, Ux3.block3_mul, Ux3.block3_mul]
    congr 1 <;> simp [hy1]
  · intro i c hc hi
    obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
    obtain ⟨w, rfl⟩ := (U.eB k p ρ).surjective c
    rw [U.embG, Ux3.block3_apply]
    simp only [(U.eB k p ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases w with ((w | w) | w) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc hi <;>
      first
      | (simp [Matrix.one_apply]; done)
      | (exfalso; have := x.isLt; have := w.isLt; omega)
      | skip
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq]
    exact hy.2 x w (by omega) (by omega)

theorem left_factor_mem : LeftMem := by
  intro k p ρ z x l h ν hz hl hh hν
  have hH := Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ
  have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have hclN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)

  have hlH : G.IsUpperUni lᴴ := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.conjTranspose_apply, show l i i = lᵀ i i from rfl, hl.1 i, star_one]
    · rw [Matrix.conjTranspose_apply, show l j i = lᵀ i j from rfl, hl.2 i j hij, star_zero]
  have hlu : IsUnit (lᴴ).det := by rw [Formalism.FourierDecayAlt.P.G4.upperUni_det hlH]; exact isUnit_one
  have hmu : U.muP k p ρ (lᴴ)⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) := by
    rw [← Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hlu]
    refine hclN.inv_mem _ (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ ⟨fun i j hij => hlH.2 i j hij, hlH.1⟩)
  have hRn : U.Rn k p ρ (rcAct h x) ∈ QuantumDeterminants.Nset k (p + ρ) :=
    (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨rcAct h x, rfl⟩)
  have hνN : U.embG k p ρ ν⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) :=
    embG_nset ((Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).inv_mem ν hν)
  have hW : U.embG k p ρ h⁻¹ ∈ UWset k (p + ρ) (liftVec k p ρ z) := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]; exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW p ρ z _ (WeylGroupFacts.uw_inv hh)
  refine ⟨U.embG k p ρ h⁻¹, hW, U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ ν⁻¹,
    hclN.mul_mem _ (hclN.mul_mem _ hRn _ hmu) _ hνN, ?_⟩
  have e1 : U.embG k p ρ h * U.Rn k p ρ x = U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := embedded_group_right_action k p ρ h x hh.1
  have e2 : U.embG k p ρ h⁻¹ * U.embG k p ρ h = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, Matrix.nonsing_inv_mul _ hhu, Formalism.FourierDecayAlt.P.PBM.embG_one]
  have e3 : U.Rn k p ρ x = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  have e4 : U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹) = U.embG k p ρ ν⁻¹ := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  have e5 : U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹ = U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ h := embedded_group_measure_preserving k p ρ h _
  calc U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)
      = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * (U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹) *
          U.embG k p ρ (h⁻¹ * ν⁻¹) := by rw [e3]; simp only [Matrix.mul_assoc]
    _ = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ *
          (U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹)) := by rw [e5]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [e4]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

def CoefG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)

def OpCCg : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (d Bg A η : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    0 < η → 0 ≤ Bg → B.SmoothCoef (B.GPos Bs) Θ → CoefG Bs Θ d Bg →
    B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC (A - Bg * m) m F) →
    (∀ g ∈ B.GV k r, Gf k r Bs.z Bs.z' g < η → F g = 0) →
    (B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opApply Θ F)) ∧
    (B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opAdj Θ F))

def AgreeOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ℝ),
    J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} →
    (∀ q ∈ JF.QDom k r Bs.z Bs.z', Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', Gf k r Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g

def ThetaJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (UU : Set (B.Mat k r)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    UU ⊆ JF.Om k r Bs.z Bs.z' → B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF Bs F) →
    (∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g) ∧
      ∀ g ∈ UU, B.opAdj Θ (B.JF Bs F) g = B.JF Bs (B.opAdj Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

def ThetaJApply : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end
