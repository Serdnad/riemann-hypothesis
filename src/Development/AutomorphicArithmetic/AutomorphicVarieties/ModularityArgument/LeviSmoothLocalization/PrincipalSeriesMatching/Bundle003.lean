module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle957
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isUnifAt_unif {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Formalism.L2.Host.IsUnifAt v (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (v.adicCompletion K)) := by
  have hiff : ∀ x y : v.adicCompletion K,
      ValuativeRel.valuation (v.adicCompletion K) x ≤ ValuativeRel.valuation (v.adicCompletion K) y ↔
        Valued.v x ≤ Valued.v y := by
    intro x y
    letI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact ValuativeRel.isEquiv _ _ x y
  have hlt1 : ∀ x : v.adicCompletion K,
      ValuativeRel.valuation (v.adicCompletion K) x < 1 ↔ Valued.v x < 1 := by
    intro x
    have h := hiff 1 x
    rw [map_one, map_one] at h
    rw [lt_iff_not_ge, lt_iff_not_ge, h]
  have hdisc : ∀ a : WithZero (Multiplicative ℤ), a < 1 → a ≤ WithZero.exp (-1) := by
    intro a h
    rcases eq_or_ne a 0 with rfl | ha
    · exact zero_le'
    · rw [← WithZero.exp_log ha] at h ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
      rw [WithZero.exp_le_exp]
      omega
  have hexp : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v ((Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = WithZero.exp (-1) := Formalism.L2.Host.unif_spec v
  have hex : ∃ p : (v.adicCompletion K)ˣ,
      ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) < 1 ∧
        ∀ x : v.adicCompletion K, ValuativeRel.valuation (v.adicCompletion K) x < 1 →
          ValuativeRel.valuation (v.adicCompletion K) x ≤
            ValuativeRel.valuation (v.adicCompletion K) (p : v.adicCompletion K) := by
    refine ⟨Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v), ?_, ?_⟩
    · rw [hlt1, hπ]
      exact hexp
    · intro x hx
      rw [hiff, hπ]
      exact hdisc _ ((hlt1 x).1 hx)
  obtain ⟨hu1, hu2⟩ := Classical.epsilon_spec hex
  unfold Formalism.L2.Host.IsUnifAt UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif
  apply le_antisymm
  · exact hdisc _ ((hlt1 _).1 hu1)
  · rw [← hπ, ← hiff]
    apply hu2
    rw [hlt1, hπ]
    exact hexp

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.charAbs :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.CharAbs := by
  intro K _ _ χ
  obtain ⟨s, hs⟩ := (GlobalTheory.HeckeNormPow.toQC χ).exists_norm_eq_rpow
  refine ⟨-s, fun v => ⟨GlobalTheory.HeckeComp.smooth_loc χ v, ?_⟩⟩
  have h1 := hs
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding v
      (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (v.adicCompletion K))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (isUnifAt_unif v),
    Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)] at h1
  exact h1
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem tw_eq_iff (y : IrrGL (k := k)) (χ ζ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ↔ ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ ζ = ξ * χ := by
  constructor
  · rintro ⟨hζ, e⟩
    refine ⟨ζ * χ⁻¹, hζ.mul hχ.inv, ?_, ?_⟩
    · rw [← IrrGL.tw_ofChar ζ χ⁻¹ hζ hχ.inv, ← e, IrrGL.tw_tw_inv]
    · rw [inv_mul_cancel_right]
  · rintro ⟨ξ, hξ, rfl, rfl⟩
    exact ⟨hξ.mul hχ, IrrGL.tw_ofChar _ _ _ _⟩

private theorem pol_tw (s : Multiset (IrrGL (k := k))) (χ θ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    pol (s.map (·.tw χ hχ)) θ = pol s (χ * θ) := by
  unfold pol
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun y _ => ?_)
  simp only [Function.comp_apply]
  by_cases h : ∃ ξ : kˣ →* ℂˣ, (∃ hξ, y = IrrGL.ofChar ξ hξ) ∧ IsUnram (ξ * (χ * θ))
  · have h' : ∃ ζ : kˣ →* ℂˣ, (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ∧ IsUnram (ζ * θ) := by
      obtain ⟨ξ, ⟨hξ, e⟩, hu⟩ := h
      exact ⟨ξ * χ, (tw_eq_iff y χ _ hχ).2 ⟨ξ, hξ, e, rfl⟩, by rwa [mul_assoc]⟩
    rw [dite_eq_left h, dite_eq_left h']
    obtain ⟨ξ, hξ, e, e'⟩ := (tw_eq_iff y χ _ hχ).1 h'.choose_spec.1
    obtain ⟨hξ', e''⟩ := h.choose_spec.1
    have : ξ = h.choose := IrrGL.ofChar_inj.1 (e.symm.trans e'')
    rw [e', this, mul_assoc]
  · have h' : ¬ ∃ ζ : kˣ →* ℂˣ, (∃ hζ, y.tw χ hχ = IrrGL.ofChar ζ hζ) ∧ IsUnram (ζ * θ) := by
      rintro ⟨ζ, hζ, hu⟩
      obtain ⟨ξ, hξ, e, rfl⟩ := (tw_eq_iff y χ _ hχ).1 hζ
      exact h ⟨ξ, ⟨hξ, e⟩, by rwa [← mul_assoc]⟩
    rw [dite_eq_right h, dite_eq_right h']

private theorem chars_tw (s : Multiset (IrrGL (k := k))) (χ ζ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    ζ ∈ chars (s.map (·.tw χ hχ)) ↔ ∃ ξ ∈ chars s, ζ = ξ * χ := by
  constructor
  · rintro ⟨hζ, hm⟩
    obtain ⟨y, hy, e⟩ := Multiset.mem_map.1 hm
    obtain ⟨ξ, hξ, rfl, e'⟩ := (tw_eq_iff y χ ζ hχ).1 ⟨hζ, e⟩
    exact ⟨ξ, ⟨hξ, hy⟩, e'⟩
  · rintro ⟨ξ, ⟨hξ, hy⟩, rfl⟩
    exact ⟨hξ.mul hχ, Multiset.mem_map.2 ⟨_, hy, IrrGL.tw_ofChar _ _ _ _⟩⟩

end Loc

section Glob

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem smooth_loc (χ : HChar K) (v : HeightOneSpectrum (𝓞 K)) : IsSmoothChar (χ.loc v) :=
  GlobalTheory.HeckeComp.smooth_loc χ v

private theorem supp_twist [_root_.NumberField.IsTotallyComplex K] {v : HeightOneSpectrum (𝓞 K)} {σ : SmIrr (GL (Fin n) (v.adicCompletion K))} (χ : HChar K)
    {s : Multiset (IrrGL (k := v.adicCompletion K))} (h : HasSupport σ.ρ s) :
    HasSupport (σ.twist (CuspSub.locDet n χ v) (CuspSub.isOpen_ker_locDet χ v)).ρ
      (s.map (·.tw (χ.loc v) (smooth_loc χ v))) :=
  h.tw (χ.loc v) (smooth_loc χ v)

end Glob

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.suppTw :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SuppTw := by
  rintro K _ _ _ n _ π v χ s ⟨σ, hσ, hs⟩
  refine ⟨_, ⟨_, hσ.twist χ, supp_twist χ hs⟩, fun θ => pol_tw s _ θ _, fun ζ => chars_tw s _ ζ _, ?_⟩
  rw [Multiset.map_map]
  rfl
end
end
