module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle119
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle121
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionUnitary
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConnectionRaisingConstantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

def cW (k r : ℕ) (θ : ℝ) : Q.Mx k r :=
  B2.embWb k r (Complex.exp ((θ : ℂ) * Complex.I) • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ))

def PhaseSec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ θ : ℝ, ∃ h h' : Q.Mx k r, h ∈ UWset k r z ∧ h' ∈ UWset k r z' ∧
      (∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
        h *ᵥ (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = Complex.exp (-((θ : ℂ) * Complex.I)) • (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) ∧
        (∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (SSn.nu0 k r z z' (TheSec.theSection k r z z') ζ) = 0 → h *ᵥ v = v) ∧
        CP.mu0 k r z z' (rot θ ζ) = h * cW k r θ * CP.mu0 k r z z' ζ * h') ∧
      ∀ v, inWb k r v → herm (Hpk k r) v z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v

def LowerUnipotentRotation : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (θ : ℝ) (Y : ℂ) (f : Q.Mx k r → E), ∀ g ∈ Q.Glev k r (Fin.last r),
      Q.tL k r z z' (Fin.last r) Y 1 0 f (cW k r θ * g) =
        Complex.exp (-((θ : ℂ) * Complex.I)) • Q.tL k r z z' (Fin.last r) Y 1 0 (fun x => f (cW k r θ * x)) g

def RotRadSp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ (θ : ℝ) (Φ : Q.Fn k r (Wq →L[ℂ] Wp)), Φ ∈ Q.RadSp k r z z' π π' →
      (fun c g => Φ c (cW k r θ * g)) ∈ Q.RadSp k r z z' π π'

def ThtRot : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ (θ : ℝ) (h h' : Q.Mx P.k P.r), h ∈ UWset P.k P.r Bs.z → h' ∈ UWset P.k P.r Bs.z' →
    ∀ ζ ∈ Gauge.GC.Ann P,
      h *ᵥ SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = Complex.exp (-((θ : ℂ) * Complex.I)) • SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z = 0 → herm (Hpk P.k P.r) v (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) = 0 →
        h *ᵥ v = v) →
      (∀ v, inWb P.k P.r v → herm (Hpk P.k P.r) v Bs.z' = 0 → h' *ᵥ v = Complex.exp (-((θ : ℂ) * Complex.I)) • v) →
      ∀ Xf : Wq →L[ℂ] Wp,
        (Bs.π h).comp (((tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) Xf).comp (Bs.π' h')) =
          Complex.exp ((θ : ℂ) * Complex.I) • (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
            (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)) ((Bs.π h).comp (Xf.comp (Bs.π' h')))

def PhaseInvOfCut : Prop :=
  PhaseSec → LowerUnipotentRotation → RotRadSp → ThtRot → KapLine → AlgSS → DatumConst → FibStable → PhaseInv

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
end

section

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)}

theorem lie_rsmul {X : Q.Mx k r} (hX : Q.inLieLev k r i X) (x : ℝ) : Q.inLieLev k r i (x • X) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX ⊢
  obtain ⟨h1, h2⟩ := hX
  have hs : ∀ v : Fin (2 * r + k + 1) → ℂ, (x • X) *ᵥ v = x • (X *ᵥ v) := fun v => by
    ext j
    simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc, mul_assoc]
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [hs, (h2 a ha).1, smul_zero]
  · rw [hs, (h2 a ha).2, smul_zero]

private theorem inLieLev_add {X Y : Q.Mx k r} (hX : Q.inLieLev k r i X) (hY : Q.inLieLev k r i Y) :
    Q.inLieLev k r i (X + Y) := by
  unfold Formalism.FourierDecayAlt.Q.inLieLev at hX hY ⊢
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
        (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX.1, hY.1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).1, (hY.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).2, (hY.2 a ha).2, add_zero]

theorem glc_lin {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) : GLc k r (a • Z + Z') := by
  unfold GLc at *
  obtain ⟨h1, h2⟩ := hZ
  obtain ⟨h1', h2'⟩ := hZ'
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  have e1 : hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    first | ring | (ring_nf; simp only [Complex.I_sq]; ring)
  have e2 : hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq
  rw [e1, e2]
  exact ⟨inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    inLieLev_add (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2'⟩

private theorem hermitian_halves_smul_add (Z Z' : Q.Mx k r) (a : ℂ) :
    hpart1 (Hpk k r) (a • Z + Z') =
      a.re • hpart1 (Hpk k r) Z + (-a.im) • hpart2 (Hpk k r) Z + hpart1 (Hpk k r) Z' ∧
    hpart2 (Hpk k r) (a • Z + Z') =
      a.im • hpart1 (Hpk k r) Z + a.re • hpart2 (Hpk k r) Z + hpart2 (Hpk k r) Z' := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hsa : star a = (a.re : ℂ) - (a.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have ha : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  constructor
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · unfold Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hsa, hI,
      show a • Z = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • Z by rw [← ha]]
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(a.im : ℂ) * Z i j / 2 + (a.im : ℂ) * ((Hpk k r)⁻¹ * Zᴴ * Hpk k r) i j / 2) * Complex.I_sq

private theorem rdV_real_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E)
    (X g : Q.Mx k r) (s : ℝ) : RdV (s • X) f g = (s : ℂ) • RdV X f g := by
  have hx : ∀ t : ℝ, (t : ℂ) • (s • X) = ((s * t : ℝ) : ℂ) • X := fun t => by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
    ring
  unfold Formalism.REAL.RdV
  simp only [hx]
  have key := deriv_comp_mul_left s (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) 0
  simp only [mul_zero] at key
  rw [key, Complex.coe_smul]

private theorem gLc_zero : GLc k r (0 : Q.Mx k r) := by
  unfold GLc Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2 Formalism.FourierDecayAlt.Q.inLieLev
  simp

private theorem rc_zero_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Rc (0 : Q.Mx k r) f g = 0 := by
  unfold Rc Formalism.REAL.RdV Formalism.QuantumDeterminants.hpart1 Formalism.QuantumDeterminants.hpart2
  simp

private theorem rc_smul_add_of_smoothLev_of_gLc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
    {f : Q.Mx k r → E} (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r}
    (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {Z Z' : Q.Mx k r} (hZ : GLc k r Z) (hZ' : GLc k r Z') (a : ℂ) :
    Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g := by
  obtain ⟨e1, e2⟩ := hermitian_halves_smul_add Z Z' a
  have hz := hZ
  have hz' := hZ'
  unfold GLc at hz hz'
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h1', h2'⟩ := hz'
  unfold Rc
  rw [e1, e2,
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h1',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _),
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (inLieLev_add (lie_rsmul h1 _) (lie_rsmul h2 _)) h2',
    Formalism.FourierDecayAlt.P.Qx5.rd_addX hf hg (lie_rsmul h1 _) (lie_rsmul h2 _)]
  simp only [rdV_real_smul, Complex.ofReal_neg]
  have haI : a * Complex.I = (a.re : ℂ) * Complex.I - a.im := by
    apply Complex.ext <;> simp
  rw [smul_add a, smul_smul a Complex.I, haI,
    show a • RdV (hpart1 (Hpk k r) Z) f g = ((a.re : ℂ) + (a.im : ℂ) * Complex.I) • RdV (hpart1 (Hpk k r) Z) f g by
      rw [Complex.re_add_im]]
  module

theorem rc_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)} {f : Q.Mx k r → E}
    (hf : Q.SmoothLev k r (Fin.last r) D f) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) :
    ∃ L : Q.Mx k r →ₗ[ℂ] E, ∀ Z, GLc k r Z → Rc Z f g = L Z := by
  let S : Submodule ℂ (Q.Mx k r) :=
    { carrier := {Z | GLc k r Z}
      add_mem' := fun {Z Z'} hZ hZ' => by simpa using glc_lin hZ hZ' 1
      zero_mem' := gLc_zero
      smul_mem' := fun c Z hZ => by simpa using glc_lin hZ gLc_zero c }
  let f0 : S →ₗ[ℂ] E :=
    { toFun := fun Z => Rc (Z : Q.Mx k r) f g
      map_add' := fun Z Z' => by simpa using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 Z'.2 1
      map_smul' := fun c Z => by simpa [rc_zero_left] using rc_smul_add_of_smoothLev_of_gLc hf hg Z.2 gLc_zero c }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend f0
  exact ⟨L, fun Z hZ => (LinearMap.congr_fun hL ⟨Z, hZ⟩).symm⟩

theorem radial_coefficient_linearity : RcLin := by
  unfold RcLin
  intro k r E _ _ D f _ hf g hg a Z Z' hZ hZ'
  obtain ⟨L, hL⟩ := rc_linear hf hg
  rw [hL _ (glc_lin hZ hZ' a), hL Z hZ, hL Z' hZ', map_add (f := _), map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.RadicalReductionOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

def MxOp (k r : ℕ) : Type := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

instance (k r : ℕ) : NormedRing (MxOp k r) := Matrix.linftyOpNormedRing

instance (k r : ℕ) : NormedAlgebra ℂ (MxOp k r) := Matrix.linftyOpNormedAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toOp (k r : ℕ) : Q.Mx k r ≃ₗ[ℝ] MxOp k r where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    change (c • x : Q.Mx k r) = (c • (@id (MxOp k r) x))
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c x, RCLike.real_smul_eq_coe_smul (K := ℂ) c (@id (MxOp k r) x)]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem locLog : NFRadRedR.LocLog := by
  intro k r z _ _
  obtain ⟨O, hO, h1, Λ, hΛ, hΛg⟩ := RadicalReductionUnitary.locLogOp (k := k) (r := r) z
  have hΛ' : ContDiffOn ℝ ∞ (fun x : MxOp k r => @id (MxOp k r) (Λ x)) (@id (Set (MxOp k r)) O) := hΛ
  have hO' : IsOpen (O : Set (Q.Mx k r)) := hO
  refine ⟨O, hO', h1, Λ, ?_, hΛg⟩
  have hL1 := (toOp k r).toContinuousLinearEquiv.toContinuousLinearMap.contDiff (n := ∞)
  have hL2 := (toOp k r).toContinuousLinearEquiv.symm.toContinuousLinearMap.contDiff (n := ∞)
  have h := hL2.comp_contDiffOn (hΛ'.comp (s := (O : Set (Q.Mx k r))) hL1.contDiffOn (fun x hx => hx))
  exact h.congr (fun x _ => rfl)

end Formalism.FourierDecayAlt.P.RadicalReductionOperator

namespace Formalism.FourierDecayAlt.P

theorem local_logarithm_unitary : NFRadRedR.LocLog := RadicalReductionOperator.locLog

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

def Vp (P : M.Par) (Y : ℂ) (i : ℕ) : Wd.M2 (MA.A P (MA.DQ P)) :=
  (((List.finRange P.r).take i).reverse.map fun l => Wd.Ts (MA.siteA P (MA.DQ P) l) Y).prod

theorem Vp_zero (P : M.Par) (Y : ℂ) : Vp P Y 0 = 1 := by
  simp [Vp]

theorem Vp_succ (P : M.Par) (Y : ℂ) (i : ℕ) (h : i < P.r) :
    Vp P Y (i + 1) = Wd.Ts (MA.siteA P (MA.DQ P) ⟨i, h⟩) Y * Vp P Y i := by
  simp [Vp, List.take_add_one, h]

theorem sitesCommonSpace_v0_eq_Vp (P : M.Par) (Y : ℂ) : Wd.v0 (MA.sites P (MA.DQ P)) Y = fun b => Vp P Y P.r b 0 := by
  funext b
  simp [Wd.v0, MA.sites, Vp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le, Function.comp_def]

theorem Ts_mul_0 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 0 0 = (algebraMap ℂ (MA.A P (MA.DQ P)) Y + σ.p) * V 0 0 + -σ.c * V 1 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Ts_mul_1 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    (Wd.Ts σ Y * V) 1 0 = σ.ci * V 0 0 := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two]

section ind

theorem actA_p (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).p f = fun ρ => MA.eulerQ (TT := P.TT) (M.vc l) (f ρ) :=
  actA_sc P _ f

theorem actA_c (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).c f = fun ρ => MA.coordQ (TT := P.TT) (M.vc l) * f ρ :=
  actA_sc P _ f

theorem actA_ci (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.siteA P (MA.DQ P) l).ci f = fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc l)) * f ρ :=
  actA_sc P _ f

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem vab_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℝ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ) =
          MA.actA P (Vp P Y i 0 0) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ) =
          MA.actA P (Vp P Y i 1 0) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    obtain ⟨⟨hA, tA⟩, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc Φ hΦ
    set ΦA := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 0) Φ with hΦA
    set ΦB := Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) i) 1) Φ with hΦB
    have hv : Q.vAB (E := Wq →L[ℂ] Wp) P.r (Y : ℂ) (i + 1) =
        (fun f => (Y : ℂ) • (Q.vAB P.r (Y : ℂ) i).1 f + pOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f) -
          cOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).2 f), fun f => ciOp ⟨i, h⟩ ((Q.vAB P.r (Y : ℂ) i).1 f)) := by
      simp only [Q.vAB, dif_pos h]
    have e0 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 0) Φ =
        (Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA - Q.crd (cOp ⟨i, h⟩) ΦB := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) (i + 1)) 1) Φ = Q.crd (ciOp ⟨i, h⟩) ΦA := by
      rw [hv]; rfl
    have hpA : FamR P Bs Dc (Q.crd (pOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 0
    have hcB : FamR P Bs Dc (Q.crd (cOp ⟨i, h⟩) ΦB) := famR_opL hB ⟨i, h⟩ 1
    have hciA : FamR P Bs Dc (Q.crd (ciOp ⟨i, h⟩) ΦA) := famR_opL hA ⟨i, h⟩ 2
    have hsum : FamR P Bs Dc ((Y : ℂ) • ΦA + Q.crd (pOp ⟨i, h⟩) ΦA) := famR_add (famR_smul hA _) hpA
    have tc : trR P Bs.μsec e (Q.crd (cOp ⟨i, h⟩) ΦB) =
        fun ρ => MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩) * trR P Bs.μsec e ΦB ρ :=
      trR_mul hpl hk he hB _ hcB (fun c => c ⟨i, h⟩) (fun _ _ => rfl) _ (fun q => coordE_vc _ _)
    have tci : trR P Bs.μsec e (Q.crd (ciOp ⟨i, h⟩) ΦA) =
        fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vc ⟨i, h⟩)) * trR P Bs.μsec e ΦA ρ :=
      trR_mul hpl hk he hA _ hciA (fun c => (c ⟨i, h⟩)⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vc]; exact hx.1 _), coordE_vc])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hsum hcB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hsum ρ) (fun ρ => smR hpl hk he hcB ρ),
        trR_add _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hA _) ρ) (fun ρ => smR hpl hk he hpA ρ), trR_smul,
        trR_p hpl hk he hA, tc, tA, tB, Vp_succ P Y i h, Ts_mul_0, actA_add, actA_mul, actA_mul,
        actA_neg, actA_add, actA_algebraMap, actA_p, actA_c, sub_eq_add_neg]
    · rw [e1]; exact hciA
    · rw [e1, tci, tA, Vp_succ P Y i h, Ts_mul_1, actA_mul, actA_ci]

end ind

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

open VLem

theorem gauge_vector_transition_holds : GVTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y b
  have h := vab_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
  rw [sitesCommonSpace_v0_eq_Vp]
  fin_cases b
  · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
  · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge
end

section

namespace Formalism.FourierDecayAlt.P

theorem normalFormFromModule_statement : Formalism.FourierDecayAlt.Q.NormalFormFromModule :=
  normal_form_from_module theorem_S_ring actual_pre_level actual_hypotheses_of_parts
    level_coordinates_commute types_complete

theorem normal_form_actual : Formalism.FourierDecayAlt.Q.NormalFormActual :=
  JacquetIntegral.normalFormActual_of_fromModule normalFormFromModule_statement

theorem level_start_actual : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  JacquetIntegral.levelStartActual_of_fromModule normalFormFromModule_statement

end Formalism.FourierDecayAlt.P
end
