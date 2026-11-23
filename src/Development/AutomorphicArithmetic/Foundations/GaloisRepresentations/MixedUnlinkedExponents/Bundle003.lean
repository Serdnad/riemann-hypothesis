module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle295
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle293
import Formalism.DoubleCosetMeasures.Statement
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.splitSuppOf :
    UpperTheory.Gal.GamX.SplitSuppOf := by
  unfold UpperTheory.Gal.GamX.SplitSuppOf
  intro hNm hSF hWS hSS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw
  haveI : w.1.asIdeal.LiesOver v.asIdeal := w.2
  rcases GlobalTheory.CharLiftStep.cycAt_or_split hp v w.1 with hc | ⟨he, hf⟩
  · exfalso
    refine hw fun u => ?_
    haveI : u.1.asIdeal.LiesOver v.asIdeal := u.2
    have hu : u.1.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.1.asIdeal) (p := v.asIdeal)).symm
    obtain ⟨-, -, -, h⟩ := hc
    exact Subtype.ext (h u.1 hu)
  · obtain ⟨hi', hN⟩ := GlobalTheory.CharLiftStep.normU_of_split v w.1 he hf
    set i := RingEquiv.ofBijective _ (GlobalTheory.CharLiftStep.bijective_of_split v w.1 he hf) with hidef
    have hi : Continuous i := GroundTheory.Global.continuous_adicCompletionMap v w.1
    have hcomp : ∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) :=
      GroundTheory.Global.adicCompletionMap_algebraMap v w.1
    refine ⟨i, hi', hi, hcomp, ?_, ?_⟩
    · rw [hNm K L v w]
      exact MonoidHom.ext fun y => Units.ext (hN y)
    · rintro s s' ⟨τ, hτ, h⟩ ⟨τ', hτ', h'⟩
      haveI : Fact (Module.finrank K L).Prime := ⟨hp⟩
      haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
      obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hW' : WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat := hW
      obtain ⟨e, he'⟩ := hSS K L σ hσ hp n hn π P (hWS K L hp n hn π P hW').1 hW' v w.1 i hi hcomp τ τ' hτ hτ'
      have hg : ∀ g : GL (Fin n) (w.1.adicCompletion L),
          Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
        Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
      let φ : Representation.Equiv (τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) τ'.ρ :=
        Representation.Equiv.mk e fun g => LinearMap.ext fun x => by
          simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp]
          exact (he' _ x).trans (congrArg (fun g' => τ'.ρ g' (e x)) (hg g))
      have h2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' h).of_equiv φ
      exact (hSF L n hn P w.1).2.1 s' _ ⟨τ', hτ', h'⟩ ⟨τ', hτ', h2⟩
end

section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem chs_cons_some (ξ : kˣ →* ℂˣ) (hξ) (s : Multiset (IrrGL (k := k))) :
    chs (IrrGL.ofChar ξ hξ ::ₘ s) = ξ ::ₘ chs s := by
  have h : ∃ η : kˣ →* ℂˣ, ∃ hη : IsSmoothChar η, IrrGL.ofChar ξ hξ = IrrGL.ofChar η hη := ⟨ξ, hξ, rfl⟩
  have hc : h.choose = ξ := by
    obtain ⟨hη, he⟩ := h.choose_spec
    exact (IrrGL.ofChar_inj.mp he).symm
  unfold chs
  rw [Multiset.filterMap_cons_some _ _ _ (by rw [dite_eq_left h])]
  rw [hc]

private theorem chs_cons_not {y : IrrGL (k := k)} (hy : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (s : Multiset (IrrGL (k := k))) : chs (y ::ₘ s) = chs s := by
  unfold chs
  rw [Multiset.filterMap_cons_none _ _ (by rw [dite_eq_right hy])]

end Loc

theorem UpperTheory.Gal.GamX.chsTr :
    UpperTheory.Gal.GamX.ChsTr := by
  intro k k' _ _ _ _ _ _ _ _ i hi' s
  induction s using Multiset.induction_on with
  | empty => simp [chs_zero]
  | cons y s ih =>
    rw [Multiset.map_cons]
    by_cases hy : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := hy
      have hξ' : IsSmoothChar (ξ.comp (Units.map (i.symm : k' →* k))) :=
        hξ.comp _ (Units.continuous_map hi')
      rw [GlobalTheory.CharLiftStep.trGL_ofChar i hi' ξ hξ _ hξ' (fun _ => rfl), chs_cons_some, chs_cons_some,
        Multiset.map_cons, ih]
    · have hy' : ¬ ∃ ξ : k'ˣ →* ℂˣ, ∃ hξ, GlobalTheory.SuppIne.trGL i hi' y = IrrGL.ofChar ξ hξ := by
        rintro ⟨ξ, hξ, he⟩
        have h1 : y.fst = 1 := congrArg Sigma.fst he
        exact hy (GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y h1)
      rw [chs_cons_not hy', chs_cons_not hy, ih]
end
