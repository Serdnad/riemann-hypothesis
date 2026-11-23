module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Length
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section

open IsDedekindDomain NumberField Module

namespace Formalism.MainNotions.Gaps.HeightData

def lN (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal : ℝ) / (finrank ℚ K : ℝ)

structure HtData where

  K : Type
  [fK : Field K]
  [nfK : NumberField K]

  D : ℕ
  δ : ℕ
  i : ℕ

  g0 : ℝ
  L : ℝ
  G : ℝ
  PH : ℝ
  Prw : ℝ
  Pet : ℝ

  S : Fin δ → ℝ

  etaPart : Prop

  Op : HeightOneSpectrum (𝓞 K) → Type
  [rOp : ∀ la, CommRing (Op la)]

  SectionSheafQuotient : HeightOneSpectrum (𝓞 K) → Type
  [gA : ∀ la, AddCommGroup (SectionSheafQuotient la)]
  [mA : ∀ la, Module (Op la) (SectionSheafQuotient la)]
  A0 : ∀ la, Submodule (Op la) (SectionSheafQuotient la)
  t : ∀ la, Fin δ → SectionSheafQuotient la

  Pts : HeightOneSpectrum (𝓞 K) → Type
  ep : ∀ la, Pts la → ℕ
  f : ∀ la, Pts la → ℕ
  vEt : ∀ la, Pts la → ℝ

attribute [instance] HtData.fK HtData.nfK HtData.rOp HtData.gA HtData.mA

namespace HtData

variable (H : HtData)

def Ila (la : HeightOneSpectrum (𝓞 H.K)) : ℕ∞ :=
  Module.length (H.Op la) (↥(H.A0 la) ⧸ (Submodule.span (H.Op la) (Set.range (H.t la))).comap (H.A0 la).subtype)

def Net (la : HeightOneSpectrum (𝓞 H.K)) : ℝ :=
  ∑ᶠ ζ, (H.ep la ζ : ℝ) * (H.f la ζ : ℝ) * H.vEt la ζ

end HtData

def HtConcl (H : HtData) : Prop :=
  (∀ la, H.Ila la ≠ ⊤) ∧ Summable (fun la => ((H.Ila la).toNat : ℝ) * lN H.K la) ∧
  2 * (∑' la, ((H.Ila la).toNat : ℝ) * lN H.K la) ≤
    (H.δ : ℝ) * Real.log H.δ + 2 * ∑ k, H.S k +
      8 / 3 * (H.D : ℝ) * ((H.D : ℝ) + 4) * H.δ * H.Prw * H.L +
      2 * ((H.D : ℝ) + 4) * ((H.D : ℝ) + 1) * H.δ * (2 * H.G + 6 * H.PH) * H.L ∧
  (H.etaPart → Summable (fun la => H.Net la * lN H.K la) ∧
    (∑' la, H.Net la * lN H.K la) / (H.i : ℝ) ≤
      H.g0 * (((H.D : ℝ) + 1) * H.δ * (2 * H.G + 6 * H.PH) * H.L + 4 / 3 * (H.D : ℝ) * H.δ * H.Prw * H.L) +
        H.δ * H.Pet)

end Formalism.MainNotions.Gaps.HeightData
end
end

section

noncomputable section

namespace Formalism.MainNotions.Gaps.T0

theorem levels_real (A B R δ d D T cg c w G PH Pη L F' fr aδ aF HF Hδ SS Λ' lδ : ℝ)
    (hR : 0 ≤ R) (hRδ : R * δ ≤ d) (hδ : 0 ≤ δ) (hlδ : 0 ≤ lδ) (hD : 0 ≤ D) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hcg0 : 0 ≤ cg) (hcg1 : cg ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ PH * L) (hG : 0 ≤ G) (hPH : 0 ≤ PH)
    (hPη : 0 ≤ Pη) (hL : 0 ≤ L) (hfr : 0 ≤ fr)
    (h1 : 2 * A ≤ δ * lδ + 2 * SS + 2 * D * aF * w + 2 * HF)
    (h2 : B ≤ cg * (Hδ + D * aδ * w) + T * c * δ * Pη)
    (hSS : SS ≤ δ * Λ') (hΛ : Λ' ≤ G * F') (hF : F' ≤ (D + 2) * L + 5 * fr * T)
    (haδ : aδ ≤ 4 / 3 * δ) (haF : aF ≤ 4 / 3 * (D + 4) * δ)
    (hHF : HF ≤ (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L)
    (hHδ : Hδ ≤ (D + 1) * δ * (2 * G + 6 * PH) * L) :
    R * (A + 1 / 2 * B) ≤
      d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
  have hSS' : SS ≤ δ * (G * ((D + 2) * L + 5 * fr * T)) :=
    hSS.trans (mul_le_mul_of_nonneg_left (hΛ.trans (mul_le_mul_of_nonneg_left hF hG)) hδ)
  have haFw : aF * w ≤ 4 / 3 * (D + 4) * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haF hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haFw' : D * (aF * w) ≤ D * (4 / 3 * (D + 4) * δ * (PH * L)) := mul_le_mul_of_nonneg_left haFw hD
  have haδw : aδ * w ≤ 4 / 3 * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haδ hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haδw' : D * (aδ * w) ≤ D * (4 / 3 * δ * (PH * L)) := mul_le_mul_of_nonneg_left haδw hD
  have hXb0 : 0 ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by positivity
  have hin : Hδ + D * aδ * w ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by
    have e : D * aδ * w = D * (aδ * w) := by ring
    linarith
  have hB' : B ≤ ((D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L))) + T * c * δ * Pη := by
    have e2 := mul_le_mul_of_nonneg_left hin hcg0
    have e3 := mul_le_of_le_one_left hXb0 hcg1
    linarith
  have hAB : A + 1 / 2 * B ≤ δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
    have p1 : 0 ≤ δ * G * L * D ^ 2 := by positivity
    have p2 : 0 ≤ δ * G * L * D := by positivity
    have p3 : 0 ≤ δ * G * L := by positivity
    have p4 : 0 ≤ δ * PH * L * D ^ 2 := by positivity
    have p5 : 0 ≤ δ * PH * L * D := by positivity
    have p6 : 0 ≤ δ * PH * L := by positivity
    have p7 : 0 ≤ δ * lδ := by positivity
    have e : D * aF * w = D * (aF * w) := by ring
    linarith
  have hT0 : 0 ≤ ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by positivity
  calc R * (A + 1 / 2 * B) ≤ R * (δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)) := mul_le_mul_of_nonneg_left hAB hR
    _ = (R * δ) * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by ring
    _ ≤ d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := mul_le_mul_of_nonneg_right hRδ hT0

theorem total_named_real (d D T c G PH Pη Pd PD PQ DivisibilityWeightConstant RR γ L κ fr lδ ρ ρ' : ℝ)
    (hd : 0 ≤ d) (hD : 1 ≤ D) (hT : 1 ≤ T) (hG : 0 ≤ G) (hPH : 0 ≤ PH) (hPD : 0 ≤ PD) (hPQ : 0 ≤ PQ)
    (hκ : 0 ≤ κ) (hS2 : T * L ≤ 2 * κ) (hlδ0 : 0 ≤ lδ) (hlδ : lδ ≤ Pd)
    (hρ : ρ ≤ ρ' + 22 * D ^ 2 * d / T) (hρ' : ρ' ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ)) :
    d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)
        + ρ * PD * κ + ρ' * PQ * κ ≤
      d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) := by
  have hT0 : 0 < T := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hLT : L ≤ 2 * κ / T := by
    rw [le_div_iff₀ hT0]
    linarith
  have hDD : (D + 4) * (D + 1) ≤ 10 * D ^ 2 := by nlinarith
  have hk : 0 ≤ 2 * κ / T := by positivity
  have hGP : 0 ≤ 3 * G + 9 * PH := by positivity
  have e1 : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L ≤ (60 * G + 180 * PH) * D ^ 2 * κ / T := by
    calc (D + 4) * (D + 1) * (3 * G + 9 * PH) * L
        ≤ (D + 4) * (D + 1) * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_left hLT (by positivity)
      _ ≤ 10 * D ^ 2 * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD hGP) hk
      _ = (60 * G + 180 * PH) * D ^ 2 * κ / T := by ring
  have hPd0 : 0 ≤ Pd := le_trans hlδ0 hlδ
  have e2 : lδ ≤ Pd * T := hlδ.trans (le_mul_of_one_le_right hPd0 hT)
  have hX : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη ≤ ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) := by
    have ea : (5 * G * fr + Pd) * T = 5 * G * fr * T + Pd * T := by ring
    have eb : Pη / 2 * T * c = 1 / 2 * T * c * Pη := by ring
    linarith
  have g1 := mul_le_mul_of_nonneg_left hX hd
  have f1 : ρ * (PD * κ) ≤ (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) :=
    mul_le_mul_of_nonneg_right hρ (mul_nonneg hPD hκ)
  have f2 : ρ' * ((PD + PQ) * κ) ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) :=
    mul_le_mul_of_nonneg_right hρ' (mul_nonneg (add_nonneg hPD hPQ) hκ)
  have e5 : 22 * D ^ 2 * d / T * (PD * κ) ≤ d * (40 * PD * D ^ 2 * κ / T) := by
    have h0 : 0 ≤ d * PD * D ^ 2 * κ / T := by positivity
    have ea : 22 * D ^ 2 * d / T * (PD * κ) = 22 * (d * PD * D ^ 2 * κ / T) := by ring
    have eb : d * (40 * PD * D ^ 2 * κ / T) = 40 * (d * PD * D ^ 2 * κ / T) := by ring
    rw [ea, eb]
    linarith
  have eq1 : d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) =
      d * ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) + d * (40 * PD * D ^ 2 * κ / T) +
        d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) := by ring
  have eq2 : ρ * PD * κ + ρ' * PQ * κ = ρ * (PD * κ) + ρ' * ((PD + PQ) * κ) - ρ' * (PD * κ) := by ring
  have eq3 : (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) = ρ' * (PD * κ) + 22 * D ^ 2 * d / T * (PD * κ) := by
    ring
  rw [eq1]
  linarith

theorem total_le_of_bounds (d D T c RR γ κ P1 P2 P3 P4 PP : ℝ)
    (hd : 0 ≤ d) (hT : 0 < T) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (h1 : P1 * D ^ 2 ≤ PP ^ 2 * D ^ 3) (h2 : P2 ≤ PP ^ 3) (h3 : P3 ≤ PP ^ 2) (h4 : P4 ≤ PP ^ 2) :
    d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ) ≤
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by
  have a1 : P1 * D ^ 2 * (κ / T) ≤ PP ^ 2 * D ^ 3 * (κ / T) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have a2 : P2 * T ≤ PP ^ 3 * T := mul_le_mul_of_nonneg_right h2 hT.le
  have a3 : P3 * (T * c) ≤ PP ^ 2 * (T * c) := mul_le_mul_of_nonneg_right h3 (by positivity)
  have a4 : P4 * ((1 / T + RR ^ 2 * c) * κ / γ) ≤ PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have hsum : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ ≤
      PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T := by
    have e : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ =
        P1 * D ^ 2 * (κ / T) + P2 * T + P3 * (T * c) + P4 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    have e' : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T =
        PP ^ 2 * D ^ 3 * (κ / T) + PP ^ 3 * T + PP ^ 2 * (T * c) + PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    rw [e, e']
    linarith
  calc d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ)
      ≤ d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T) :=
        mul_le_mul_of_nonneg_left hsum hd
    _ = d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by ring

structure SumDat (ι : Type*) where

  s : Finset ι

  l : ι → ℝ

  I : ι → ℝ

  N : ι → ℝ

  cD : ι → ℝ

  vQ : ι → ℝ

  be : ι → ℝ

  (R δ d D T c i g₀ rw : ℝ)

  (G PH Prw Pη Pd PD PQ DivisibilityWeightConstant RR γ₀ : ℝ)

  (L κ F' f r : ℝ)

  (aδ aF HF Hδ SS Λ' : ℝ)

  (ρ ρ' : ℝ)

namespace SumDat

variable {ι : Type*} (X : SumDat ι)

def rr (la : ι) : ℝ :=
  X.R * (X.I la + X.T * (X.c / (2 * X.i)) * X.N la) + X.cD la + (X.vQ la + X.ρ' * X.be la)

def P1 : ℝ := 60 * X.G + 180 * X.PH + 40 * X.PD

def P2 : ℝ := 5 * X.G * (X.f * X.r ^ 2) + X.Pd

def P3 : ℝ := X.Pη / 2

def P4 : ℝ := X.DivisibilityWeightConstant * (X.PD + X.PQ)

variable {X}

end SumDat

end Formalism.MainNotions.Gaps.T0
end
end

section

noncomputable section

namespace Formalism.MainNotions.Gaps.CC.Fib

open MulAction

variable {G : Type*} [Group G]

def Gam (Γ K : Subgroup G) (g : G) : Subgroup G :=
  Γ ⊓ K.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_Gam {Γ K : Subgroup G} {g x : G} : x ∈ Gam Γ K g ↔ x ∈ Γ ∧ g⁻¹ * x * g ∈ K := by
  simp [Gam, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem Gam_eq_map (Γ K : Subgroup G) (g : G) :
    Gam Γ K g = Γ ⊓ K.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_Gam, Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hx, hk⟩
    refine ⟨hx, _, hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨hx, k, hk, rfl⟩
    refine ⟨hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert hk using 1
    group

def GamEquivSet (Γ K : Subgroup G) (g : G) : Gam Γ K g ≃ {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} where
  toFun x := ⟨⟨x.1, (mem_Gam.1 x.2).1⟩, (mem_Gam.1 x.2).2⟩
  invFun y := ⟨y.1.1, mem_Gam.2 ⟨y.1.2, y.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def GamCongr {Γ U : Subgroup G} {x x' h u : G} (hh : h ∈ Γ) (hu : u ∈ U) (e : x' = h * x * u) :
    Gam Γ U x ≃* Gam Γ U x' where
  toFun y := ⟨h * y * h⁻¹, mem_Gam.2 ⟨Γ.mul_mem (Γ.mul_mem hh (mem_Gam.1 y.2).1) (Γ.inv_mem hh), by
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) (mem_Gam.1 y.2).2) hu
    rw [e]; convert this using 1; group⟩⟩
  invFun y := ⟨h⁻¹ * y * h, mem_Gam.2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hh) (mem_Gam.1 y.2).1) hh, by
    have := U.mul_mem (U.mul_mem hu (mem_Gam.1 y.2).2) (U.inv_mem hu)
    subst e; convert this using 1; group⟩⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' y z := by ext; simp [mul_assoc]

def toK (Γ K : Subgroup G) (g : G) : Gam Γ K g →* K where
  toFun x := ⟨g⁻¹ * x * g, (mem_Gam.1 x.2).2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] theorem toK_coe (Γ K : Subgroup G) (g : G) (x : Gam Γ K g) : (toK Γ K g x : G) = g⁻¹ * x * g := rfl

instance actK (Γ K U : Subgroup G) (g : G) : MulAction (Gam Γ K g) (K ⧸ U.subgroupOf K) :=
  MulAction.compHom _ (toK Γ K g)

theorem smul_mk (Γ K U : Subgroup G) (g : G) (x : Gam Γ K g) (k : K) :
    x • (k : K ⧸ U.subgroupOf K) = ((toK Γ K g x * k : K) : K ⧸ U.subgroupOf K) := rfl

theorem mk_eq_iff {K U : Subgroup G} {k k' : K} :
    (k : K ⧸ U.subgroupOf K) = (k' : K ⧸ U.subgroupOf K) ↔ (k : G)⁻¹ * k' ∈ U := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

def stabEquiv {Γ K U : Subgroup G} (hUK : U ≤ K) (g : G) (k : K) :
    stabilizer (Gam Γ K g) (k : K ⧸ U.subgroupOf K) ≃* Gam Γ U (g * k) where
  toFun x := ⟨x.1.1, mem_Gam.2 ⟨(mem_Gam.1 x.1.2).1, by
    have h := x.2
    rw [mem_stabilizer_iff, smul_mk, eq_comm, mk_eq_iff] at h
    simpa [mul_assoc] using h⟩⟩
  invFun y := ⟨⟨y.1, mem_Gam.2 ⟨(mem_Gam.1 y.2).1, by
      have h := K.mul_mem (K.mul_mem k.2 (hUK (mem_Gam.1 y.2).2)) (K.inv_mem k.2)
      simpa [mul_assoc] using h⟩⟩, by
    rw [mem_stabilizer_iff, smul_mk, eq_comm, mk_eq_iff]
    simpa [mul_assoc] using (mem_Gam.1 y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def toCls (Γ K U : Subgroup G) (g : G) : K ⧸ U.subgroupOf K → DoubleCoset.Quotient (Γ : Set G) U :=
  Quotient.lift (fun k : K => DoubleCoset.mk Γ U (g * k)) (by
    intro a b h
    have h' : (a : G)⁻¹ * b ∈ U := by
      have := QuotientGroup.leftRel_apply.1 h
      simpa [Subgroup.mem_subgroupOf] using this
    exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨1, Γ.one_mem, _, h', by simp [mul_assoc]⟩)

@[simp] theorem toCls_mk (Γ K U : Subgroup G) (g : G) (k : K) :
    toCls Γ K U g (k : K ⧸ U.subgroupOf K) = DoubleCoset.mk Γ U (g * k) := rfl

theorem toCls_smul (Γ K U : Subgroup G) (g : G) (x : Gam Γ K g) (y : K ⧸ U.subgroupOf K) :
    toCls Γ K U g (x • y) = toCls Γ K U g y := by
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [smul_mk, toCls_mk, toCls_mk]
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨(x : G)⁻¹, Γ.inv_mem (mem_Gam.1 x.2).1, 1, U.one_mem, ?_⟩
    simp only [Subgroup.coe_mul, toK_coe]
    group

def orbToCls (Γ K U : Subgroup G) (g : G) :
    orbitRel.Quotient (Gam Γ K g) (K ⧸ U.subgroupOf K) → DoubleCoset.Quotient (Γ : Set G) U :=
  Quotient.lift (toCls Γ K U g) (by
    rintro a b ⟨x, rfl⟩
    exact toCls_smul Γ K U g x b)

@[simp] theorem orbToCls_mk (Γ K U : Subgroup G) (g : G) (y : K ⧸ U.subgroupOf K) :
    orbToCls Γ K U g (Quotient.mk'' y) = toCls Γ K U g y := rfl

def total (Γ K U : Subgroup G) (rep : DoubleCoset.Quotient (Γ : Set G) K → G) :
    (Σ c : DoubleCoset.Quotient (Γ : Set G) K, orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K)) →
      DoubleCoset.Quotient (Γ : Set G) U :=
  fun p => orbToCls Γ K U (rep p.1) p.2

theorem total_surjective (Γ K U : Subgroup G) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) : Function.Surjective (total Γ K U rep) := by
  intro q
  obtain ⟨h, hh, k, hk, hx⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 (hrep (DoubleCoset.mk Γ K (Quotient.out q)))
  refine ⟨⟨DoubleCoset.mk Γ K (Quotient.out q), Quotient.mk'' ((⟨k, hk⟩ : K) : K ⧸ U.subgroupOf K)⟩, ?_⟩
  show orbToCls Γ K U _ (Quotient.mk'' _) = q
  rw [orbToCls_mk, toCls_mk]
  conv_rhs => rw [← DoubleCoset.out_eq' (H := Γ) (K := U) q]
  refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨h, hh, 1, U.one_mem, ?_⟩
  rw [mul_one, ← mul_assoc]
  exact hx

theorem total_injective {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) : Function.Injective (total Γ K U rep) := by
  rintro ⟨c, o⟩ ⟨c', o'⟩ heq
  induction o using Quotient.inductionOn' with
  | h y =>
  induction o' using Quotient.inductionOn' with
  | h y' =>
  induction y using QuotientGroup.induction_on with
  | H k =>
  induction y' using QuotientGroup.induction_on with
  | H k' =>
  have heq' : DoubleCoset.mk Γ U (rep c * k) = DoubleCoset.mk Γ U (rep c' * k') := heq
  obtain ⟨h, hh, u, hu, he⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1 heq'
  have hcc : c = c' := by
    rw [← hrep c, ← hrep c']
    refine (@DoubleCoset.eq _ _ Γ K _ _).2 ⟨h, hh, (k : G) * u * (k' : G)⁻¹,
      K.mul_mem (K.mul_mem k.2 (hUK hu)) (K.inv_mem k'.2), ?_⟩
    rw [eq_mul_inv_of_mul_eq he]
    group
  subst hcc
  have e1 : h = rep c * k' * u⁻¹ * (k : G)⁻¹ * (rep c)⁻¹ := by
    rw [he]
    group
  have hx : h⁻¹ ∈ Gam Γ K (rep c) := by
    refine mem_Gam.2 ⟨Γ.inv_mem hh, ?_⟩
    have : (rep c)⁻¹ * h⁻¹ * rep c = (k : G) * u * (k' : G)⁻¹ := by
      rw [e1]
      group
    rw [this]
    exact K.mul_mem (K.mul_mem k.2 (hUK hu)) (K.inv_mem k'.2)
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  refine Quotient.sound ⟨⟨h⁻¹, hx⟩, ?_⟩
  show (⟨h⁻¹, hx⟩ : Gam Γ K (rep c)) • ((k' : K) : K ⧸ U.subgroupOf K) = ((k : K) : K ⧸ U.subgroupOf K)
  rw [smul_mk, mk_eq_iff]
  simp only [Subgroup.coe_mul, toK_coe]
  rw [e1]
  convert U.inv_mem hu using 1
  group

def fibRep {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) :
    DoubleCoset.Quotient (Γ : Set G) U ≃
      Σ c : DoubleCoset.Quotient (Γ : Set G) K, orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K) :=
  (Equiv.ofBijective (total Γ K U rep) ⟨total_injective hUK rep hrep, total_surjective Γ K U rep hrep⟩).symm

theorem fibRep_symm_mk {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) (c : DoubleCoset.Quotient (Γ : Set G) K) (k : K) :
    (fibRep hUK rep hrep).symm ⟨c, Quotient.mk'' (k : K ⧸ U.subgroupOf K)⟩ = DoubleCoset.mk Γ U (rep c * k) := rfl

def fib {Γ K U : Subgroup G} (hUK : U ≤ K) :
    DoubleCoset.Quotient (Γ : Set G) U ≃
      Σ c : DoubleCoset.Quotient (Γ : Set G) K,
        orbitRel.Quotient (Gam Γ K (Quotient.out c)) (K ⧸ U.subgroupOf K) :=
  fibRep hUK Quotient.out (DoubleCoset.out_eq' (H := Γ) (K := K))


end Formalism.MainNotions.Gaps.CC.Fib
end
end
