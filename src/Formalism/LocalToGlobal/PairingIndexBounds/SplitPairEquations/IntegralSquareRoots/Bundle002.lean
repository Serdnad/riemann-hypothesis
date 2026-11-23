module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.Bundle001
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Bundle001
public import Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Bundle003
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Bundle002
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.ReductionOf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def J1at (B : Ker.Base D cc δ) (N N' : ℕ)
    (γ : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N) D.host.E) : Prop :=
  letI := D.host.cmStar
  TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
    (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
      B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

def J2at (B : Ker.Base D cc δ) (N N' : ℕ)
    (γ' : letI := D.host.cmStar; Matrix.unitaryGroup (Fin N') D.host.E) : Prop :=
  letI := D.host.cmStar
  TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
    (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')))
        (B.thZero N N')

theorem pull_mul_left {N N' : ℕ} (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (1 : Matrix (Fin N') (Fin N') D.host.E) G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ₁ 1 (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ₂ 1 G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.map_mul]
  exact (Matrix.mul_assoc _ _ _).symm

theorem pull_mul_right {N N' : ℕ} (γ₁ γ₂ : Matrix (Fin N') (Fin N') D.host.E) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E) (γ₁ * γ₂) G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ₁ (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ₂ G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.map_mul, Matrix.mul_assoc, Matrix.conjTranspose_mul]
  rfl

variable {B : Ker.Base D cc δ}

theorem J1at_mul (hL : B.LatAll) (hTL : Tr0L D B.tor) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ γ₁ γ₂ : Matrix.unitaryGroup (Fin N) D.host.E, J1at B N N' γ₁ → J1at B N N' γ₂ → J1at B N N' (γ₁ * γ₂) := by
  letI := D.host.cmStar
  intro γ₁ γ₂ j1 j2
  have e1 : ((1 : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) = 1 := rfl
  have em : ((γ₁ * γ₂ : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) =
      (γ₁ : Matrix (Fin N) (Fin N) D.host.E) * (γ₂ : Matrix (Fin N) (Fin N) D.host.E) := rfl
  have s1 := smulSD D N (StandardLatticesGL3.stdL D N) γ₁ (sd0 N)
  have s2 := smulSD D N (StandardLatticesGL3.stdL D N) γ₂ (sd0 N)
  have s12 := smulSD D N _ γ₁ s2
  have p := (pullIop_of hL N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ₂ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
    (StandardLatticesGL3.stdL D N') (StandardLatticesGL3.stdL D N') γ₁ 1 hN hN' (sd0 N) s2 (sd0 N') (sd0 N') (B.thZero N N')
    (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p
  have t := hTL N N' _ _ hN hN' s1 s12 _ (mem_ThSp_of' _ _ _ _ h0)
  unfold J1at at j1 j2 ⊢
  rw [em, pull_mul_left, j2, pull_smul]
  show _ • TaylorLogMetric.pull D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
  rw [p, j1, Iop_smulF]
  show _ • _ • TaylorLogMetric.Iop D B.tor _ _ (TaylorLogMetric.Iop D B.tor _ _ (B.thZero N N')) = _
  rw [t, smul_smul, Formalism.BasicNotions.Examples₂.smulLat_mul, Matrix.det_mul, star_mul']
  simp only [map_mul, Finset.prod_mul_distrib, mul_pow]
  rw [mul_comm]
  rfl

theorem J2at_mul (hL : B.LatAll) (hTR : Tr0R D B.tor) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') :
    letI := D.host.cmStar
    ∀ γ₁ γ₂ : Matrix.unitaryGroup (Fin N') D.host.E, J2at B N N' γ₁ → J2at B N N' γ₂ → J2at B N N' (γ₁ * γ₂) := by
  letI := D.host.cmStar
  intro γ₁ γ₂ j1 j2
  have e1 : ((1 : Matrix.unitaryGroup (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) = 1 := rfl
  have em : ((γ₁ * γ₂ : Matrix.unitaryGroup (Fin N') D.host.E) : Matrix (Fin N') (Fin N') D.host.E) =
      (γ₁ : Matrix (Fin N') (Fin N') D.host.E) * (γ₂ : Matrix (Fin N') (Fin N') D.host.E) := rfl
  have s1 := smulSD D N' (StandardLatticesGL3.stdL D N') γ₁ (sd0 N')
  have s2 := smulSD D N' (StandardLatticesGL3.stdL D N') γ₂ (sd0 N')
  have s12 := smulSD D N' _ γ₁ s2
  have p := (pullIop_of hL N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')
    (SDLat.smulLat (γ₂ : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) 1 γ₁ hN hN' (sd0 N) (sd0 N) (sd0 N') s2
    (B.thZero N N') (mem_ThSp_of' _ _ _ _ h0)).2
  rw [e1, Formalism.BasicNotions.Examples₂.smulLat_one] at p
  have t := hTR N N' _ _ hN hN' s1 s12 _ (mem_ThSp_of' _ _ _ _ h0)
  unfold J2at at j1 j2 ⊢
  rw [em, pull_mul_right, j2, pull_smul, p, j1, Iop_smulF, t, smul_smul, Formalism.BasicNotions.Examples₂.smulLat_mul, Matrix.det_mul]
  simp only [map_mul, Finset.prod_mul_distrib, mul_pow]
  rw [mul_comm]

end Formalism.L2.PairingIndexBounds.Eq.J
end
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phiU {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) :
    TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  phiL (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (Matrix.mem_unitaryGroup_iff'.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ.2)
    (Matrix.mem_unitaryGroup_iff'.mp γ'.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)

def cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix.unitaryGroup (Fin n) D.host.E :=
  ⟨(star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ) = (γ : Matrix (Fin n) (Fin n) D.host.E)ᵀ := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    rw [h, ← Matrix.transpose_mul, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.transpose_one]⟩

theorem map_row {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) (x : TaylorLogMetric.VC D N N') (i : Fin N') :
    rowE D N N' (phiU γ 1 x) i = phiU γ 1 (rowE D N N' x i) := by
  funext τ a j
  show (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (rowE D N N' x i τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_apply, Matrix.mul_apply]
  rfl

theorem map_col {N N' : ℕ} (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') (j : Fin N) :
    colE D N N' (phiU 1 γ' x) j = phiU (cjU γ') 1 (colE D N N' x j) := by
  funext τ a i
  show (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) * (gM (1 : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (colE D N N' x j τ) *
      (gM ((star (γ' : Matrix (Fin N') (Fin N') D.host.E))ᵀ) τ)ᴴ) a i
  rw [gM_one, gM_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  show TaylorLogMetric.embT D τ ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k) * x τ k j =
    x τ k j * star (TaylorLogMetric.embT D τ (star ((γ' : Matrix (Fin N') (Fin N') D.host.E) i k)))
  rw [embT_star', star_star, mul_comm]

theorem det_gM {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : (gM M τ).det = TaylorLogMetric.embT D τ M.det :=
  ((TaylorLogMetric.embT D τ).map_det M).symm

theorem gM_sub {n : ℕ} (A C : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) : gM (A - C) τ = gM A τ - gM C τ := by
  ext i j
  simp [gM]

theorem nofix {N N' : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) (y : TaylorLogMetric.VC D N N') (h : (phiU γ 1).symm y = y) : y = 0 := by
  funext τ
  have h1 : (gM (1 : Matrix (Fin N') (Fin N') D.host.E) τ)ᴴ * Matrix.of (y τ) * gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ =
      Matrix.of (y τ) := congrFun h τ
  rw [gM_one, Matrix.conjTranspose_one, Matrix.one_mul] at h1
  have h2 : Matrix.of (y τ) * gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ = 0 := by
    rw [gM_sub, gM_one, Matrix.mul_sub, Matrix.mul_one, h1, sub_self]
  have hu : IsUnit (gM (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)) τ).det := by
    rw [det_gM]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero _).mpr hγ)
  have h3 := Matrix.mul_nonsing_inv_cancel_right _ (Matrix.of (y τ)) hu
  rw [h2, Matrix.zero_mul] at h3
  exact h3.symm

theorem det_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E) :
    ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).det =
      star (γ : Matrix (Fin n) (Fin n) D.host.E).det := by
  show ((star (γ : Matrix (Fin n) (Fin n) D.host.E))ᵀ).det = _
  rw [Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]

theorem ne_cjU {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0) :
    (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  have h : (1 - ((cjU γ : Matrix.unitaryGroup (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) =
      (star (1 - (γ : Matrix (Fin n) (Fin n) D.host.E)))ᵀ := by
    rw [star_sub, star_one, Matrix.transpose_sub, Matrix.transpose_one]
    rfl
  rw [h, Matrix.det_transpose, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]
  exact star_ne_zero.mpr hγ

theorem det_row {N : ℕ} (γ : Matrix.unitaryGroup (Fin N) D.host.E) :
    LinearMap.det ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) := by
  let g : D.what₂.Tau → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun τ =>
    Matrix.toLin' (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ)
  let f : D.what₂.Tau → (Fin 1 → Fin N → ℂ) →ₗ[ℂ] (Fin 1 → Fin N → ℂ) := fun τ =>
    LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)
  have e : ((phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) : TaylorLogMetric.VC D N 1 →ₗ[ℂ] TaylorLogMetric.VC D N 1) =
      LinearMap.pi fun τ => (f τ).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => ?_
    funext τ a j
    show (gM (1 : Matrix (Fin 1) (Fin 1) D.host.E) τ * Matrix.of (x τ) * (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) a j =
      (((gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ)ᵀ *ᵥ (x τ a)) j
    rw [gM_one, Matrix.one_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [e, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun τ _ => ?_
  show LinearMap.det (LinearMap.pi fun a => (g τ).comp (LinearMap.proj a)) = _
  rw [LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one, LinearMap.det_toLin',
    Matrix.det_transpose, Matrix.det_conjTranspose, det_gM, embT_star']

theorem finrank_row (N : ℕ) : Module.finrank ℂ (TaylorLogMetric.VC D N 1) = Fintype.card D.what₂.Tau * N := by
  simp [Module.finrank_pi_fintype]

end Formalism.L2.PairingIndexBounds.Eq.J
end
end
