module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle018
public import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
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

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.OBT

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.FrameBoundFromBesselTorus

section Defs

variable {k r : ℕ}

def coefH (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) :
    Mx k r → (L.Wq →L[ℂ] L.Wp) :=
  fun x => P.comp ((L.σ x).comp Q)

def IsKFinPair (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) : Prop :=
  (∀ w, IsKFinHpk (k := k) (r := r) L.σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) L.σ (ContinuousLinearMap.adjoint P x))

def HasBData (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Λ : ℂ)
    (Φ : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Ψ : Mx k r → Measure (PairSp k r) → (L.Wq →L[ℂ] L.Wp)) : Prop :=
  (∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb k * μ = Hb k → L.J F (bigCell k r c μ) = Λ • Φ (bigCell k r c μ)) ∧
    (∀ (γ : Point ℂ (r + 1)) (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
      Gpt (Tz k r L.z) (Tz k r L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR →
      IsOrbQuot L g μR ν → OrbInt L F g ν = Λ • Ψ g ν)

end Defs

def RankOneTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (κ₀ : ℝ),
    0 < κ₀ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
        ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    ∃ (Φ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
      (Ψ : Mx D.R.k D.R.rS → Measure (PairSp D.R.k D.R.rS) → (L.Wq →L[ℂ] L.Wp))
      (Λ₀ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℂ)
      (Λ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℝ → ℝ → ℂ),
      (∀ P Q, IsKFinPair L P Q → HasBData L (coefH L P Q) (Λ₀ P Q) Φ Ψ) ∧
      (∀ P Q (κ τ : ℝ), 0 < κ → 0 < τ → IsKFinPair L P Q →
        HasBData L (fun x => coefH L P Q (cj D.R.k D.R.rS κ τ x)) (Λ P Q κ τ) Φ Ψ) ∧
      (∀ (κ τ : ℝ), 0 < κ → 0 < τ → ∀ P Q, IsKFinPair L P Q → Λ₀ P Q ≠ 0 →
        ∃ P₁ Q₁, IsKFinPair L P₁ Q₁ ∧ Λ P₁ Q₁ κ τ ≠ 0)

section Zero

variable {k r : ℕ}

theorem isKFinHpk_zero (L : LocBessel k r) : IsKFinHpk (k := k) (r := r) L.σ (0 : L.Hs) := by
  exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx
    simp [hx]⟩

theorem J_zero (L : LocBessel k r) (g : Mx k r) : L.J (fun _ => 0) g = 0 := by
  simp [LocBessel.J, Formalism.QuantumDeterminants.besselJ]

theorem orbInt_zero (L : LocBessel k r) (g : Mx k r) (ν : Measure (PairSp k r)) :
    OrbInt L (fun _ => 0) g ν = 0 := by
  simp [OrbInt, besselIntg]

end Zero

theorem oneBesselTor_of_rankOne (D : D7) (Cgf : ℝ) (h : RankOneTor D Cgf) : OneBesselTor D Cgf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hN hN' hε hgap hf
  obtain ⟨Φ, Ψ, Λ₀, Λ, h1, h2, h3⟩ := h L κ₀ hκ₀ hc hN hN' hε hgap
  obtain ⟨P, Q, hQ, hP, hfPQ⟩ := hf
  have hfeq : f = coefH L P Q := funext fun g => hfPQ g
  subst hfeq
  have hPQ : IsKFinPair L P Q := ⟨hQ, hP⟩
  by_cases h0 : Λ₀ P Q = 0
  · refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun w => by simpa using isKFinHpk_zero L,
      fun x => by simpa using isKFinHpk_zero L, fun g => by simp⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      show L.J (fun _ => 0) _ = _
      rw [(h1 P Q hPQ).1 c μ hc0 hμ, h0, J_zero]
      simp
    · intro γ g μR ν hG hrep hst hroot hq
      show OrbInt L (fun _ => 0) g ν = _
      rw [(h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, h0, orbInt_zero]
      simp
  · obtain ⟨P₁, Q₁, hPQ₁, hΛ⟩ := h3 κ τ hκ hτ P Q hPQ h0
    refine ⟨coefH L P₁ Q₁, Λ P₁ Q₁ κ τ / Λ₀ P Q, div_ne_zero hΛ h0,
      ⟨P₁, Q₁, hPQ₁.1, hPQ₁.2, fun g => rfl⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).1 c μ hc0 hμ, (h1 P Q hPQ).1 c μ hc0 hμ, smul_smul,
        div_mul_cancel₀ _ h0]
    · intro γ g μR ν hG hrep hst hroot hq
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).2 γ g μR ν hG hrep hst hroot hq,
        (h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, smul_smul, div_mul_cancel₀ _ h0]

end Formalism.L2.SG.Pf.OBT
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.BesselExpansion

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.RotatedPoints Formalism.MainNotions.S.Pv.Frames

section Loc

variable (D : D7)

variable {D}

theorem frame_bounds {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) :
    2 ≤ b ∧ 1 ≤ b ^ (3 + Ch) ∧ D.host.rdE ≤ b ^ (3 + Ch) := by
  obtain ⟨⟨hk, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  have hbC : 1 ≤ b ^ Ch := by
    rcases le_total 1 (kaRe D) with h | h
    · exact h.trans hk1
    · exact ((one_le_inv₀ hka).2 h).trans hk2
  have hb0 : 0 < b := by linarith
  have hb3 : 1 ≤ b ^ (3 + Ch) := by
    rw [Real.rpow_add hb0]
    have : 1 ≤ b ^ (3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  exact ⟨hb2, hb3, Formalism.MainNotions.TheoremBConstants.rdE_le D b Ch hb2 hka hk2⟩

theorem ch_nonneg {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} {v : D.what₂.Tau} {L : LocBessel D.R.k D.R.rS}
    {f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)} {μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ}
    (hCg : 2 ≤ Cg) (hok : PlaceOKR D Ch Cg T T' b dist v L f μsec) : 0 ≤ Ch := by
  have hb2 := (frame_bounds hCg hok).1
  obtain ⟨⟨-, -, -, -, -, hStd, -, -⟩, -⟩ := hok
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have hlt : b ^ Ch < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hc
  rcases le_total 1 (kaRe D) with h | h
  · linarith
  · have := (one_le_inv₀ hka).2 h
    linarith

end Loc

end Formalism.L2.SG.Pf.BesselExpansion
end
end
