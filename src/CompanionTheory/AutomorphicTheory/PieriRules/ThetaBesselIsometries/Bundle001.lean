module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
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

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  show 0 ≤ max 1 T * b ^ (20 * (r + 1))
  have h1 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  have h2 : 0 ≤ b ^ (20 * (r + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (by positivity) _
  exact mul_nonneg h1 h2

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have he0 : e ≠ 0 := ne_of_gt he
  have hsq : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  have hprod : (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by
    field_simp <;> ring
  have key : (a' * a * d / e) ^ 2 ≤ (Real.sqrt (A * A') ^ n) ^ 2 := by
    rw [hprod, hsq]
    exact mul_le_mul h h' (by positivity) (pow_nonneg hA n)
  have hl : 0 ≤ a' * a * d / e := by positivity
  have hr : 0 ≤ Real.sqrt (A * A') ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  calc a' * a * d / e = Real.sqrt ((a' * a * d / e) ^ 2) := (Real.sqrt_sq hl).symm
    _ ≤ Real.sqrt ((Real.sqrt (A * A') ^ n) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (A * A') ^ n := Real.sqrt_sq hr

end GlobalTheory.SupTau
end Gp91
end

section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

section gap

variable {k r : ℕ}

structure Rep.IsDG (R : Rep k r) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) : Prop where
  hc : Formalism.QuantumDeterminants.IsHCParam mu
  ds : PI.UpqRep.IsDSHpk k r ε mu R.σ
  gap : ∃ h, Formalism.QuantumDeterminants.GapAtLeast ε mu h ∧ GapOK k r h

theorem _root_.GlobalTheory.isDS_of_isDG {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDG ε mu) : R.IsDS ε mu := ⟨h.1, h.2⟩

def IsFamG (lam : Fin (2 * r + k + 1) → ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) : Prop :=
  ∀ ν, ∑ a, (ν a).natAbs ≤ q0 → (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))

end gap

def RankOneG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (R : Rep k r)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)),
    R.IsDG ε lam → Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsHCTypeW k r z u π →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    ∃ L : R.H → Wp, ∀ w ∈ R.sm, ∀ v ∈ R.sm,
      Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN) ∧
      be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (L v)).smulRight (L w)

def InputsG : Prop := DecLow ∧ DecInf ∧ PI.KFinSmooth ∧ RankOneG

def InfCharG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)), (∃ Q, PI.UpqRep.IsCayleyU k r ε Q) →
    (∃ h, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ GapOK k r h) → Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl (2 * r + k + 1))
          (Y + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

def DSExistG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam mu →
    (∃ P, PI.UpqRep.IsCayleyU k r ε P) → (∃ h, Formalism.QuantumDeterminants.GapAtLeast ε mu h ∧ GapOK k r h) →
    ∃ R : Rep k r, R.IsDG ε mu

def ZuckG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r),
    (∀ ν, n1 ν ≤ q0 → (R ν).IsDG ε (fun a => lam a + (ν a : ℝ))) → ∀ ν,
    (∀ l, n1 ν + l ≤ q0 →
      ∃ io pr, TensRaw (cmp l) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr) ∧
    (n1 ν + 1 ≤ q0 → ∃ io pr, TensRaw dualM (R ν) (fun s => R (ν - Pi.single s 1)) io pr)

def PoulsenG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r),
    R.IsDG ε mu → R'.IsDG ε mu' →
    (∀ Bf : R.H → R.H → ℂ, IsInvForm R R Bf → ∃ c : ℂ, ∀ x ∈ R.sm, ∀ y ∈ R.sm, Bf x y = c * ⟪y, x⟫_ℂ) ∧
    ∀ Bf : R.H → R'.H → ℂ, IsInvForm R R' Bf → (∀ x ∈ R.sm, ∀ y ∈ R'.sm, Bf x y = 0) ∨
      ∃ U : R.H ≃ₗᵢ[ℂ] R'.H, ∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)

def HCFdegG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool), (∃ Q, PI.UpqRep.IsCayleyU k r ε Q) → ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Mx k r → (H →L[ℂ] H)), (∃ h, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ GapOK k r h) →
      PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
      PI.UpqRep.IsFdeg (PI.UpqRep.muG ε) σ (c * PI.UpqRep.fdegHC lam)

def HypsG : Prop :=
  InputsG ∧ PI.SmoothCyc ∧ InfCharG ∧ DSExistG ∧ ZuckG ∧ PoulsenG ∧ HCFdegG

section side

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def SetupG {k r : ℕ} [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) : Prop :=
  Num k r lam u b bv ga h q0 ∧ IsFamG lam q0 R ∧ SideG k r z π u μW μN μG νq ∧ SideFam z π μW μN μG q0 R l dg

end side

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end BranchingSupport
end
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SuppliedPieri

theorem n1_add_eZ_le {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : I.card = ∑ i : Fin n, (if i ∈ I then 1 else 0) := by
    rw [Finset.sum_boole]; simp
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, eZ]
  split_ifs <;> omega

theorem JF_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (g : B.Mat k r) :
    B.JF D 0 g = 0 := by
  simp [B.JF, Formalism.QuantumDeterminants.besselJ]

end GlobalTheory.SuppliedPieri
end Gp91
end
