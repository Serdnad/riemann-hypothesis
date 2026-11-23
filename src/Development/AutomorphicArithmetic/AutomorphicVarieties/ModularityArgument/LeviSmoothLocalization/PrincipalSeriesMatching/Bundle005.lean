module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.CrossG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnrOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UpDownX
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem rootBounds {q x a b : ℝ} {f : ℕ} (hf : 0 < f) (hq : 0 < q) (hx : 0 ≤ x)
    (h1 : ((q ^ f : ℝ)) ^ a < x ^ f) (h2 : x ^ f < ((q ^ f : ℝ)) ^ b) :
    q ^ a < x ∧ x < q ^ b := by
  have e : ∀ c : ℝ, ((q ^ f : ℝ)) ^ c = (q ^ c) ^ f := by
    intro c
    rw [← Real.rpow_natCast q f, ← Real.rpow_mul hq.le, mul_comm, Real.rpow_mul hq.le, Real.rpow_natCast]
  rw [e] at h1 h2
  exact ⟨lt_of_pow_lt_pow_left₀ f hx h1, lt_of_pow_lt_pow_left₀ f (Real.rpow_nonneg hq.le _) h2⟩

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winInd :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinInd := by
  intro K M _ _ _ _ _ _ _ h2 P π hsys t v hw
  refine ⟨indTor K M h2 P π hsys v fun w => ⟨(hw w).1.1, (hw w).2⟩, fun s hs ξ hξ => ?_⟩
  have hs' : ∀ w : GroundTheory.Global.SemiLocal.PlacesOver M v, ∃ s', SuppAt π w.1 s' := fun w =>
    (suppFacts M 2 (by norm_num) π w.1).1
  choose s' hs' using hs'
  obtain ⟨w, hζ⟩ := indX K M h2 P π hsys v s s' hs hs' ξ hξ
  obtain ⟨hsm, -⟩ := hξ
  obtain ⟨-, hnorm, hf, hN⟩ := normVal K M v w ξ
  obtain ⟨b1, b2⟩ := (hw w).1.2 (s' w) (hs' w) _ hζ
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot))
  simp only [MonoidHom.comp_apply] at b1 b2
  rw [hnorm hsm, hN, Nat.cast_pow] at b1 b2
  exact rootBounds hf hq (norm_nonneg _) b1 b2
end

section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem win_pow_iff (N M f : ℕ) (hf : 0 < f) (hM : M = N ^ f) (a b x y : ℝ) (hx : 0 ≤ x) (hy : y = x ^ f) :
    ((M : ℝ) ^ a < y ∧ y < (M : ℝ) ^ b) ↔ ((N : ℝ) ^ a < x ∧ x < (N : ℝ) ^ b) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have key : ∀ c : ℝ, (M : ℝ) ^ c = ((N : ℝ) ^ c) ^ f := by
    intro c
    rw [hM, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN, ← Real.rpow_mul hN, mul_comm]
  rw [key, key, hy, pow_lt_pow_iff_left₀ (Real.rpow_nonneg hN _) hx hf.ne',
    pow_lt_pow_iff_left₀ hx (Real.rpow_nonneg hN _) hf.ne']

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winUpDown :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinUpDown := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hbc t v
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hUD := upDown K L hp n hn π P hbc v
  obtain ⟨s, hs⟩ := (suppFacts K n hn1 π v).1
  have hex : ∀ w : GroundTheory.Global.SemiLocal.PlacesOver L v, ∃ s', SuppAt P w.1 s' := fun w => (suppFacts L n hn1 P w.1).1
  choose s' hs' using hex
  have hX := upDownX K L hp n hn π P hbc v s s' hs hs'
  refine ⟨fun hW w => ?_, fun hW => ?_⟩
  · refine ⟨⟨(hUD.1 hW.1 w).1, fun s₁ hs₁ ζ hζ => ?_⟩, (hUD.1 hW.1 w).2⟩
    have e : s₁ = s' w := (suppFacts L n hn1 P w.1).2.1 _ _ hs₁ (hs' w)
    rw [e] at hζ
    obtain ⟨ξ, hξ, rfl⟩ := hX.1 hW.1 w ζ hζ
    have hv := normVal K L v w ξ
    exact (win_pow_iff _ _ _ hv.2.2.1 hv.2.2.2 _ _ _ _ (norm_nonneg _) (hv.2.1 hξ.choose)).2 (hW.2 s hs ξ hξ)
  · refine ⟨hUD.2 fun w => ⟨(hW w).1.1, (hW w).2⟩, fun s₁ hs₁ ξ hξ => ?_⟩
    have e : s₁ = s := (suppFacts K n hn1 π v).2.1 _ _ hs₁ hs
    rw [e] at hξ
    obtain ⟨w, hw⟩ := hX.2 ξ hξ
    have hv := normVal K L v w ξ
    exact (win_pow_iff _ _ _ hv.2.2.1 hv.2.2.2 _ _ _ _ (norm_nonneg _) (hv.2.1 hξ.choose)).1 ((hW w).1.2 _ (hs' w) _ hw)
end
