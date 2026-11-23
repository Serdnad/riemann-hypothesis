module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle044
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle045
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
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

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem tsum_mix {ι W : Type} (Wd : Finset W) (m : ι → ℝ) (hm0 : ∀ i, 0 ≤ m i) (hms : Summable m)
    (hM : 0 < ∑' i, m i) (q : ι → W → ℝ) (hq : ∀ i, TB.IsProb Wd (q i)) :
    ∃ θ : W → ℝ, TB.IsProb Wd θ ∧ ∀ N : W → ℝ,
      Summable (fun i => m i * ∑ u ∈ Wd, q i u * N u) ∧
      ∑' i, m i * ∑ u ∈ Wd, q i u * N u = (∑' i, m i) * ∑ u ∈ Wd, θ u * N u := by
  set M := ∑' i, m i with hMdef
  have hq1 : ∀ i u, q i u ≤ 1 := by
    intro i u
    by_cases hu : u ∈ Wd
    · rw [← (hq i).2.2]
      exact Finset.single_le_sum (fun a _ => (hq i).1 a) hu
    · rw [(hq i).2.1 u hu]
      exact zero_le_one
  have hsu : ∀ u, Summable (fun i => m i * q i u) := fun u =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm0 i) ((hq i).1 u))
      (fun i => mul_le_of_le_one_right (hm0 i) (hq1 i u)) hms
  refine ⟨fun u => (∑' i, m i * q i u) / M, ⟨fun u => div_nonneg (tsum_nonneg fun i =>
    mul_nonneg (hm0 i) ((hq i).1 u)) hM.le, fun u hu => ?_, ?_⟩, fun N => ⟨?_, ?_⟩⟩
  · simp [(hq _).2.1 u hu]
  · rw [← Finset.sum_div, div_eq_one_iff_eq hM.ne', ← Summable.tsum_finsetSum (fun u _ => hsu u)]
    refine tsum_congr fun i => ?_
    rw [← Finset.mul_sum, (hq i).2.2, mul_one]
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    exact summable_sum fun u _ => (hsu u).mul_right (N u)
  · simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Summable.tsum_finsetSum (fun u _ => (hsu u).mul_right (N u))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tsum_mul_right]
    field_simp

theorem mL_pat {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L σ * ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K = ∏ v ∈ crystallineComparison.pat L σ, L v ^ K := by
  have h1 : ∀ v ∈ crystallineComparison.pat L σ, crystallineComparison.mfac K (L v) ‖σ v‖ * ‖σ v‖ ^ K = L v ^ K := by
    intro v hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have ha : 0 < ‖σ v‖ := lt_of_le_of_lt (hL v) hv
    have hle : (L v / ‖σ v‖) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg (hL v) ha.le) ((div_le_one ha).mpr hv.le)
    unfold crystallineComparison.mfac
    rw [if_neg ha.ne', min_eq_right hle, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ ha.ne'
  have h2 : ∀ v ∈ (Finset.univ : Finset (Fin f)), v ∉ crystallineComparison.pat L σ → crystallineComparison.mfac K (L v) ‖σ v‖ = 1 := by
    intro v _ hv
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hv
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rfl
    · have ha : 0 < ‖σ v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact min_eq_left (one_le_pow₀ ((one_le_div ha).mpr hv))
  unfold crystallineComparison.mL
  rw [← Finset.prod_subset (Finset.subset_univ _) h2, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl h1

theorem bound_mL {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) (X Y : ℝ)
    (h : (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X ≤ (∏ v ∈ crystallineComparison.pat L σ, L v ^ K) * Y) : X ≤ crystallineComparison.mL K L σ * Y := by
  have hP : 0 < ∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K := by
    refine Finset.prod_pos fun v hv => pow_pos ?_ _
    simp only [crystallineComparison.pat, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact lt_of_le_of_lt (hL v) hv
  rw [← mL_pat K L hL σ] at h
  refine le_of_mul_le_mul_left ?_ hP
  calc (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * X
      ≤ crystallineComparison.mL K L σ * (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * Y := h
    _ = (∏ v ∈ crystallineComparison.pat L σ, ‖σ v‖ ^ K) * (crystallineComparison.mL K L σ * Y) := by ring

theorem mL_nonneg {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (σ : crystallineComparison.V f) : 0 ≤ crystallineComparison.mL K L σ := Finset.prod_nonneg fun v _ => by
    unfold crystallineComparison.mfac
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (pow_nonneg (div_nonneg (hL v) (norm_nonneg _)) _)

theorem mL_zero {f : ℕ} (K : ℕ) (L : Fin f → ℝ) : crystallineComparison.mL K L 0 = 1 := by
  unfold crystallineComparison.mL crystallineComparison.mfac
  simp

section setting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem prod_gN (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (p q : Fin S.f → C.LPt) :
    ∏ v, KB.gN S v ε i (w.1 v) (p v) (q v) =
      (∏ v, S.gramLoc v ε i (w.1 v) (p v) (q v)) / (C.Word.size S.P w.1 : ℂ) := by
  unfold KB.gN C.Word.size
  rw [Finset.prod_div_distrib]
  congr 1
  push_cast
  rfl

theorem nstV_eq (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : Fin S.f → ℂ) :
    KB.NstV S ε i s w Y κ t t' = ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' *
      ∏ v, KB.gN S v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)]) (C.loc (S.σ v) h' ++ [(s, t' v)]) := by
  unfold KB.NstV
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun h' _ => ?_
  have e := prod_gN S ε i w (fun v => C.loc (S.σ v) h ++ [(s, t v)]) (fun v => C.loc (S.σ v) h' ++ [(s, t' v)])
  rw [e, mul_div_assoc]

end setting

end

end Formalism.FourierDecayAlt.P.PBC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def KapPt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (Qr : M.Ty P → (Wq →L[ℂ] Wq)) : Prop :=
  (∀ ρ σ, (Qr ρ).comp (Qr σ) = if ρ = σ then Qr ρ else 0) ∧ (∑ ρ, Qr ρ = 1) ∧
  (∀ ρ (v w : Wq), inner ℂ (Qr ρ v) w = inner ℂ v (Qr ρ w)) ∧
  ∀ (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT),
    (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (∑ ρ, f ρ • Qr ρ)

end preds

def GTKPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr

def GTKLine : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qr : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qr →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ ρ : M.Ty P,
      ∃ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, E.comp (Qr ρ) = E ∧
        inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) ∧
        ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Z.comp (Qr ρ) = Z →
          Z = inner ℂ (B.hsVec E) (B.hsVec Z) • E

def GTKapOfCut : Prop := GTKPt → GTKLine → GTKap

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def Ann (P : M.Par) : Set ℂ := {ζ : ℂ | P.TT < Complex.normSq ζ}

def fnZ (P : M.Par) (f : ℂ → ℂ) : MA.SmQ P.r P.TT := MA.toSm P (fun q => f q.1.2)

def dzQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzP).1 f

def dzbQ (P : M.Par) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := ((MA.DQ P).dzbP).1 f

def modA (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * star ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))

def modB (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : ℂ :=
  (M.aC P ρ : ℂ) * ζ / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ))

def ConnF (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P),
    trR P Bs e (d.L.nab.1 Φ) ρ = dzQ P (trR P Bs e Φ ρ) + fnZ P (A ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e (d.L.nabs.1 Φ) ρ = -dzbQ P (trR P Bs e Φ ρ) + fnZ P (B ρ) * trR P Bs e Φ ρ

def SmAB (P : M.Par) (A B : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A ρ) (Ann P) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B ρ) (Ann P)

def PhaseEq (P : M.Par) (A B u : M.Ty P → ℂ → ℂ) : Prop :=
  ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 ∧
    A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ = modA P ρ ζ ∧ B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ = modB P ρ ζ

end preds

def GTCLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ A B : M.Ty P → ℂ → ℂ, SmAB P A B ∧ ConnF P Bs d e A B

def GTCReal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)

def GTCCurv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0

def GTCHol : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B →
        ∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A ρ w) 0 R).im = Real.pi * n

def GTCAnnulus : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ), 0 ≤ TT → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (NF.dZb α ζ).re = 0) →
    (∀ R : ℝ, 0 < R → TT < R ^ 2 → ∃ n : ℤ, (circleIntegral α 0 R).im = Real.pi * n) →
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = α ζ ∧ star (u ζ) * NF.dZb u ζ = -star (α ζ)

def GTCGauge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B u : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → PhaseEq P A B u →
        IsFrameB P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) ∧ KapF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) ∧
          NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ)

def GTCTT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → 0 ≤ P.TT

def GTCPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → ∃ u, PhaseEq P A B u

theorem modA_smooth (P : M.Par) (ρ : M.Ty P) (hTT : 0 ≤ P.TT) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'

theorem star_modA (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : star (modA P ρ ζ) = modB P ρ ζ := by
  simp only [modA, modB]
  first
  | (rw [star_div₀, star_mul', star_sub, star_star]; simp [Complex.conj_ofReal]; done)
  | (simp [map_div₀, Complex.conj_ofReal]; done)
  | (rw [star_div₀, star_mul', star_sub, star_star]
     simp only [Complex.star_def, Complex.conj_ofReal]; done)

def GTCPhaseOfCut : Prop := GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTCTT → GTCPhase

theorem gTCPhase_of_cut : GTCPhaseOfCut := by
  intro hR hC hH hA hT Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn
  have hTT := hT Wp Wq P Bs X d hyp
  have hex : ∀ ρ : M.Ty P, ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | P.TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = modA P ρ ζ - A ρ ζ ∧
          star (u ζ) * NF.dZb u ζ = -star (modA P ρ ζ - A ρ ζ) := by
    intro ρ
    refine hA P.TT (fun w => modA P ρ w - A ρ w) hTT ((modA_smooth P ρ hTT).sub (hAB ρ).1) ?_ ?_
    · intro ζ hζ
      exact hC Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
    · intro R hR0 hR2
      exact hH Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR2
  choose u hu using hex
  refine ⟨u, fun ρ => ⟨(hu ρ).1, fun ζ hζ => ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := (hu ρ).2 ζ hζ
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]; ring
  · rw [h3, hR Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ, star_sub, star_modA]; ring

def GTConnOfCut : Prop := GTCLocal → GTCPhase → GTCGauge → GTConn

theorem gTConn_of_cut : GTConnOfCut := by
  intro hL hP hG Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk
  obtain ⟨A, B', hAB, hC⟩ := hL Wp Wq P Bs X d hH e he hk
  obtain ⟨u, hu⟩ := hP Wp Wq P Bs X d hH e he hk A B' hAB hC
  exact ⟨_, hG Wp Wq P Bs X d hH e he hk A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

def pairLev (μ : Measure (Mt k r)) (i : Fin (r + 1)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * pairAt μ Φ Ψ (glue i c c')

variable {μ : Measure (Mt k r)} {i : Fin (r + 1)} {U : Submodule ℂ (RadSp k r z z' π π')}

theorem pairLev_swap (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairLev μ i Ψ Φ c = conj (pairLev μ i Φ Ψ c) := by
  unfold pairLev
  rw [← integral_conj]
  congr 1
  funext c'
  rw [pairAt_swap, map_mul, Complex.conj_ofReal]

theorem pairLev_smul_left (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (a : ℂ) :
    pairLev μ i (a • Φ) Ψ c = a * pairLev μ i Φ Ψ c := by
  unfold pairLev
  rw [← integral_const_mul]
  congr 1
  funext c'
  rw [pairAt_smul_left]
  ring

theorem pairLev_zero_left (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : pairLev μ i 0 Ψ c = 0 := by
  unfold pairLev
  have h0 : ∀ c', pairAt μ (0 : RadSp k r z z' π π') Ψ c' = 0 := fun c' => by
    have := pairAt_smul_left μ (0 : RadSp k r z z' π π') Ψ c' 0
    rwa [zero_smul, zero_mul] at this
  simp [h0]

theorem act_mem_pres (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (hM : ∀ a b, M a b ∈ presAlg U)
    (x : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ U) (a : Ix S) : act M x a ∈ U := U.sum_mem fun b _ => (hM a b).1 _ (hx b)

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt

theorem admissible_in_truncation_holds : AdmInCut := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG v a ha x hx
  obtain ⟨w, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := w.2.1.1 v j hj
  have hnode := (hG v).2.2.2.2.2
  have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    intro Y hY
    simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
    simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hY.1, hY.2]
  by_cases hp : ((w.1 v)[j]'hj).1
  · rw [if_pos hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact hcut _ (hnode _ hy).1
  · rw [if_neg hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := hcut _ (hnode _ hy).2.1
    simpa using this

end Formalism.FourierDecayAlt.P.CutMP
end
