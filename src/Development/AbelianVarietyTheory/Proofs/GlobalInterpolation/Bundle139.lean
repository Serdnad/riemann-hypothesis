module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle280
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle066
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle133
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.Annihilator

variable {F : Type} [Field F] [NumberField F]

private theorem ext_lemma {x y : AF F} (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) :
    x = y :=
  Prod.ext h1 h2

private theorem mul_pairA_zero (x : AF F) (z : Ainf F) :
    x * pairA F z 0 = pairA F (fstA F x * z) 0 := by
  apply ext_lemma
  · rw [map_mul]
    rfl
  · rw [map_mul]
    show sndA F x * 0 = 0
    exact mul_zero _

private theorem mul_pairA_singleV (x : AF F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    x * pairA F 0 (singleV F v t) = pairA F 0 (singleV F v (sndA F x v * t)) := by
  apply ext_lemma
  · rw [map_mul]
    show fstA F x * 0 = 0
    exact mul_zero _
  · rw [map_mul]
    show sndA F x * singleV F v t = singleV F v (sndA F x v * t)
    unfold singleV
    classical
    exact (RestrictedProduct.mul_single _ v t (sndA F x)).symm

theorem eq_zero_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨hloc, -, hinf⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  apply ext_lemma
  ·
    have h0 : fstA F x = 0 := hinf _ fun y => by
      have h := hx (pairA F y 0)
      rw [mul_pairA_zero] at h
      exact h
    rw [h0, map_zero]
  ·
    have key : ∀ v, sndA F x v = 0 := by
      intro v
      by_contra hne
      obtain ⟨s, hs⟩ := hloc v
      apply hs
      have h := hx (pairA F 0 (singleV F v ((sndA F x v)⁻¹ * s)))
      rw [mul_pairA_singleV, mul_inv_cancel_left₀ hne] at h
      exact h
    rw [map_zero]
    exact DFunLike.ext _ _ fun v => (key v).trans rfl

theorem exists_eq_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) : ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  by_cases htriv : ∀ y, ψ (x * y) = 1
  · exact ⟨0, by rw [map_zero]; exact eq_zero_of_forall hψ x htriv⟩
  · push_neg at htriv
    obtain ⟨hc, hn, -, -⟩ := id hψ

    have hχ : IsCharAF F (ψ.compAddMonoidHom (AddMonoidHom.mulLeft x)) := by
      unfold IsCharAF
      exact ⟨hc.comp (continuous_const.mul continuous_id), fun y => hn _, hx, htriv⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ _ hψ hχ
    refine ⟨a, sub_eq_zero.mp (eq_zero_of_forall hψ _ fun y => ?_)⟩
    have h1 : ψ (x * y) = ψ (algebraMap F (AF F) a * y) := ha y
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]

theorem self_annihilator : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∀ x : AF F, (∀ y, ψ (x * y) = 1) → x = 0) ∧ ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  intro F _ _ hF ψ hψ
  haveI := hF
  exact ⟨fun x hx => eq_zero_of_forall hψ x hx, fun x hx => exists_eq_of_forall hψ x hx⟩

end GlobalTheory.SWQ.Annihilator
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Glob

theorem vol_eq_massI_step (D : D7) (hT : VolTie D) (h2 : Conclusion2 D) (hv : DefiniteVolumeEqMass D)
    (W : HSpace D.host.E) (P Q : ℕ) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (P, Q)) (hPQ : 2 ≤ P + Q)
    (hup : ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) → D.vol U = massI D (P + Q + 1)) :
    D.vol W = massI D (P + Q) := by
  obtain ⟨U, hU, hUs⟩ := GlobalTheory.T.exists_hermitianSpace_with_signature D (P + 1) Q
  have hr := GlobalTheory.T.volume_ratio_up_positive_line D hT h2 W P Q hW hs hPQ U hU hUs
  have hb := massRatio_of_definiteVolume D h2 hv (P + Q + 1) (by omega)
  have e : P + Q + 1 - 1 = P + Q := by omega
  rw [e] at hb
  rw [← hb, hup U hU hUs] at hr
  have h1 := massI_pos D (P + Q + 1)
  have h3 := massI_pos D (P + Q)
  have h4 := D.vol_pos W
  field_simp at hr
  nlinarith [hr]

theorem vol_eq_massI_of_two_le_rank : ∀ D : D7, VolTie D → Conclusion2 D → DefiniteVolumeEqMass D → ∀ (W : HSpace D.host.E) (P Q : ℕ),
    W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → D.vol W = massI D (P + Q) := by
  intro D hT h2 hv
  have h2v := volume_eq_mass_of_definite D h2 hv
  have hP1 : ∀ (W : HSpace D.host.E) (Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (1, Q)) → 2 ≤ 1 + Q →
      D.vol W = massI D (1 + Q) := by
    intro W Q hW hs hQ
    refine vol_eq_massI_step D hT h2 hv W 1 Q hW hs hQ fun U hU hUs => ?_
    have := h2v.2 U 2 Q hU hUs le_rfl
    rw [this]; congr 1; omega
  intro W P Q hW hs hPQ
  rcases Nat.lt_or_ge P 2 with hP | hP
  · interval_cases P
    · refine vol_eq_massI_step D hT h2 hv W 0 Q hW hs hPQ fun U hU hUs => ?_
      rw [hP1 U Q hU hUs (by omega)]; congr 1; omega
    · exact hP1 W Q hW hs hPQ
  · exact h2v.2 W P Q hW hs hP

end GlobalTheory.Glob
end
