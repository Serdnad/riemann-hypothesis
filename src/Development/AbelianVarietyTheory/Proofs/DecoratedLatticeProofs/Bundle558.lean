module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle531
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle557
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle544
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle539
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle322
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QLastPf

theorem heisO_smul' {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem comb_smul_left {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • e) f = a • comb ψ S T e f := by
  by_cases ha : a = 0
  · simp [comb, ha]
  · rw [comb, comb, Finsupp.support_smul_eq ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finsupp.smul_apply, smul_smul, smul_eq_mul]

theorem comb_smul_right {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (e : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T e (a • f) = a • comb ψ S T e f := by
  rw [comb, comb, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [heisO_smul', smul_comm]

theorem biComb_smul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a b : ℂ) (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) : biComb ψ A S A' (a • e) (b • e') C = (a * b) • biComb ψ A S A' e e' C := by
  funext u v
  simp only [biComb, comb_smul_left]
  have e1 : (fun u' => (b • comb ψ S A' e' (C u')) v) = b • fun u' => comb ψ S A' e' (C u') v := by
    funext u'; simp
  rw [e1, comb_smul_right]
  simp only [Pi.smul_apply, smul_eq_mul, biComb]
  ring

theorem block_smul₂ {D : D7} (c : Comm D) (j : ℕ) (oma : Om (c.X j) (c.X (j + 1))) (omb : Om (c.X (j + 1)) (c.X (j + 1 + 1)))
    (φ : GA D (c.X j) → ℂ) (a : ℂ) (C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ) :
    c.bl j oma omb φ (a • C) = a • c.bl j oma omb φ C := by
  funext h₂
  simp only [Comm.bl, biLift, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h₁
  rw [← integral_const_mul]
  congr 1; funext h₀
  have e1 : ∀ v, (fun u => a * C u v) = a • fun u => C u v := fun v => by funext u; simp
  simp_rw [e1, map_smul]
  have e2 : (fun v => (a • oma (h₀, h₁) (fun u => C u v)) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v; simp
  rw [e2, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem alg_of_core : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂ → ∀ φ, IsContAut (c.X j) φ → ∀ α β, c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ (w.ε j α).support, w.ε j α g • t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) = (w.cQ j * w.εT (j + 1 + 1) h β 1) • ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  intro D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β
  obtain ⟨F, hF⟩ := id hpin
  obtain ⟨hX, hY⟩ := GlobalTheory.T.twistPlace_normalisedCombinations_preserve_thetaFunctions D c v t w F hc hF j h Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1
  have hom : ∀ g, IsThetaFunO c.ψ _ _ (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    rw [← (ht.sBF j 0 h).1]
    exact (t.sBF j 0 h).weil.om_pres _ _ hX
  have lin := fun (s : Finset (GA D (c.V j))) (a : GA D (c.V j) → ℂ) => (GlobalTheory.T.lastDoubleThetaLift_integrable_linear D c v t hc ht hW j h _ hY φ hφ).2 _ s a _ hom
  have hcore := GlobalTheory.T.seeSaw_last_two_steps_all_twist_places D c v t w F hc ht hv hW hF j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ α β
  have hs : ∀ i, (F.Q i).s = j := fun i => by have := (F.Q i).hs; omega
  have hidx : ∀ i, ((F.Q i).idx (j + 1) : ℂ) ≠ 0 ∧ ((F.Q i).idx (j + 1 + 1) : ℂ) ≠ 0 := by
    intro i
    have h1 := GlobalTheory.T.twistPlace_last_two_level_indices_ne_zero D c v F.χ (F.Q i)
    rw [hs i] at h1
    exact ⟨Nat.cast_ne_zero.2 h1.1, Nat.cast_ne_zero.2 h1.2⟩
  have htop : ∀ i u, (F.Q i).wt (j + 1 + 1) u = (F.Q i).idx (j + 1 + 1) := by
    intro i
    have h1 := (F.Q i).wt_top
    rw [hs i] at h1
    exact h1
  set E := conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) with hE
  set P := ∏ i, (F.Q i).wt j (F.eqv j α i) with hP
  set Z := fun g => t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁) with hZ
  have hε : w.ε j α = P • E := hF.ε j 0 h α
  have hsum : ∑ g ∈ (w.ε j α).support, w.ε j α g • Z g = ∑ g ∈ E.support, (P * E g) • Z g := by
    rw [hε]
    by_cases hP0 : P = 0
    · simp [hP0]
    · rw [Finsupp.support_smul_eq hP0]
      rfl
  have hL : c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h)
      (∑ g ∈ (w.ε j α).support, w.ε j α g • Z g) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) =
      P • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h)
        (∑ g ∈ E.support, E g • Z g) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) := by
    rw [hsum, ← lin E.support (fun g => P * E g), ← lin E.support (fun g => E g), Finset.smul_sum]
    exact Finset.sum_congr rfl fun g _ => by rw [smul_smul]
  simp only [hZ] at hL
  rw [hL]
  have hR : ∀ γ, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
      (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) = (P * ∏ i, (F.Q i).wt (j + 1) (F.eqv (j + 1) γ i)) •
      c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)))
        (aconv (List.ofFn fun i => (F.Q i).dL (j + 1) (F.eqv (j + 1) γ i) (F.eqv (j + 1 + 1) β i)))
        (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
    intro γ
    rw [hF.dQ j (by omega) α γ, hF.dQ (j + 1) (by omega) γ β, biComb_smul, block_smul₂]
  simp only [hR]
  have hεT : w.εT (j + 1 + 1) h β 1 = ∏ i, ((F.Q i).idx (j + 1 + 1) : ℂ) := by
    rw [hF.εT (j + 1 + 1) h β, Finsupp.single_eq_same]
    exact Finset.prod_congr rfl fun i _ => htop i _
  rw [hεT, hF.cQ j (by omega)]
  simp only [← smul_smul]
  rw [← Finset.smul_sum, ← hcore, smul_smul, smul_smul, smul_smul]
  congr 1
  have hone : (∏ i, (((F.Q i).idx (j + 1) : ℂ) * ((F.Q i).idx (j + 1 + 1) : ℂ))⁻¹) *
      (∏ i, ((F.Q i).idx (j + 1 + 1) : ℂ)) * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    field_simp [(hidx i).1, (hidx i).2]
  linear_combination (-P) * hone

theorem qLast_of_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is →
    WeilOK (t := t) v → QPin v w → QLast v w := by
  intro D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ f hf _
  obtain ⟨F, hF⟩ := id hpin
  obtain ⟨hX, hY⟩ := GlobalTheory.T.twistPlace_normalisedCombinations_preserve_thetaFunctions D c v t w F hc hF j h Ψ₁ Ψ₂ hΨ₁.1 hΨ₂.1
  have hfc : IsContAut c.T f := ⟨fun γ hγ g => hf.left γ hγ g, hf.cont⟩
  have hom : ∀ g, IsThetaFunO c.ψ _ _ (t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    rw [← (ht.sBF j 0 h).1]
    exact (t.sBF j 0 h).weil.om_pres _ _ hX
  have han := fun α => GlobalTheory.T.lastDoubleThetaLift_integrable_linear D c v t hc ht hW j h _ hY (φ α) (hφ α).1
  set Y := comb c.ψ _ _ (w.eQT j h) Ψ₂ with hYd
  set X := comb c.ψ _ _ (w.eQ j) Ψ₁ with hXd
  set E := (c.oT (j + 1 + 1) h).emb with hE
  set K := fun α γ β => c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
    (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) with hK
  set G := fun α => c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (c.lst j h (v.τ j h) (t.sBF j 0 h)
    (∑ g ∈ (w.ε j α).support, w.ε j α g • t.om j (g, 1) X) Y) with hG
  have key : ∀ α, (fun h' => f h' * G α (E (h', 1))) = fun h' => ∑ g ∈ (w.ε j α).support, w.ε j α g *
      (f h' * c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, 1) X) Y) (E (h', 1))) := by
    intro α
    funext h'
    simp only [hG]
    rw [← (han α).2 _ _ _ _ hom, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hint : ∀ α, IntegrableOn (fun h' => f h' * G α (E (h', 1))) c.volT.𝓕 c.volT.μ := by
    intro α
    rw [key α]
    exact integrable_finsetSum _ fun g _ => ((han α).1 _ (hom g) f hfc).const_mul _
  have hL : ∀ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * ∫ h' in c.volT.𝓕, f h' * c.bl j (t.kom j) (t.kom (j + 1)) (φ α)
      (c.lst j h (v.τ j h) (t.sBF j 0 h) (t.om j (g, 1) X) Y) (E (h', 1)) ∂c.volT.μ =
      ∫ h' in c.volT.𝓕, f h' * G α (E (h', 1)) ∂c.volT.μ := by
    intro α
    rw [key α, integral_finsetSum _ fun g _ => ((han α).1 _ (hom g) f hfc).const_mul _]
    exact Finset.sum_congr rfl fun g _ => (integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl fun α _ => hL α, ← integral_finsetSum _ fun α _ => hint α]

  have hcard : Fintype.card (t.Ch (j + 1 + 1)) = 1 := by
    rw [Fintype.card_congr (F.eqv (j + 1 + 1)), Fintype.card_pi]
    refine Finset.prod_eq_one fun i _ => ?_
    have hs : (F.Q i).s = j := by have := (F.Q i).hs; omega
    have h1 := (F.Q i).one
    rw [hs] at h1
    exact h1
  have hβ : ∀ β, (w.cQ j * ∫ h' in c.volT.𝓕, trc (w.εT (j + 1 + 1) h β) f h' *
      (∑ α, ∑ γ, c.bl j (t.kom j) (t.kom (j + 1)) (φ α) (biComb c.ψ _ _ _ (w.dQ j α γ) (w.dQ (j + 1) γ β)
        (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂))) (E (h', 1)) ∂c.volT.μ) =
      ∫ h' in c.volT.𝓕, ∑ α, f h' * G α (E (h', 1)) ∂c.volT.μ := by
    intro β
    have htrc : trc (w.εT (j + 1 + 1) h β) f = w.εT (j + 1 + 1) h β 1 • f := by
      rw [hF.εT (j + 1 + 1) h β]
      by_cases ha : (∏ i, (F.Q i).wt (j + 1 + 1) (F.eqv (j + 1 + 1) β i)) = 0
      · simp [trc, ha]
      · rw [trc, Finsupp.support_single _ ha, Finset.sum_singleton]
        funext x
        simp [rTrans]
    rw [← integral_const_mul]
    congr 1
    funext h'
    have hG' : ∀ α, G α = (w.cQ j * w.εT (j + 1 + 1) h β 1) • ∑ γ, K α γ β := fun α =>
      alg_of_core D c v t w hc ht hv hW hpin j h Ψ₁ Ψ₂ hΨ₁ hΨ₂ (φ α) (hφ α).1 α β
    simp only [hG', htrc, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun β _ => hβ β, Finset.sum_const, Finset.card_univ, hcard, one_smul]

end GlobalTheory.QLastPf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QFin v w := by
  first | exact @GlobalTheory.QFinMain.qFin_of_pin | exact GlobalTheory.QFinMain.qFin_of_pin | (intros; apply GlobalTheory.QFinMain.qFin_of_pin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleStep_adelicIntegral_finiteTwistPlaces : ∀ D : D7, ValQ D := by
  first | exact @GlobalTheory.QVal.valQ | exact GlobalTheory.QVal.valQ | (intros; apply GlobalTheory.QVal.valQ <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem GlobalTheory.Unf.unfFB_of_descent : ∀ D : D7, Descent D → UnfFB D := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ
  haveI := s.vW.haar
  obtain ⟨hcnt, hdisc, hfd⟩ := GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D B.V (GQ B.V ⊓ besGrp B.d B.o) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  obtain ⟨hcont, hclN, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  have hU := B.vN.unit
  have hHR : (semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν).IsHaarMeasure :=
    (GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L σ B.d B.o B.vN.ν B.vN.𝓝 hU).2.2 B.vA.μ B.vA.haar
  obtain ⟨𝓡, h𝓡, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hcont hclN hnorm huniq hrat B.vA B.vN.ν B.vN.𝓝
    hU.1 hU.2.1 hHR
  obtain ⟨hFc, hFi⟩ := GlobalTheory.T.unfoldedBessel_continuous_leftInvariant D hD ψ σ J B s vL Y G Φ hY hG hΦ
  obtain ⟨hI, hL⟩ := GlobalTheory.T.fourierJacobiPeriod_lift_eq_integral_unfolded D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have habs := GlobalTheory.Unf.BesInt.absConv_of_invariant D σ B _ hFc hFi
  have hm : ∀ h : GA D B.V, Measurable fun g : GA D B.V => unfF s vL Y G Φ (g * h) :=
    fun h => (hFc.comp (continuous_mul_const h)).measurable
  have key := GlobalTheory.quot_fubini_mean (GA D B.V) s.vW.μ (besGrp B.d B.o) (GQ B.V ⊓ besGrp B.d B.o) inf_le_right
    (GlobalTheory.BesClosed.besGrp_isClosed D B.V B.V₀ B.A B.L σ B.d B.o) hcnt hdisc B.μR hHR 𝓡 𝓑 h𝓡 h𝓑 (unfF s vL Y G Φ)
    hFc.measurable hFi hI (fun h => ((hint _ (hm h)).1).2 (habs h))
  rw [← hL] at key
  convert key using 2 with h
  have e2 : (∫ r : besGrp B.d B.o in 𝓡, unfF s vL Y G Φ (r * h) ∂B.μR) =
      ∫ h₁ in B.vA.𝓕, ∫ n in B.vN.𝓝, unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) ∂B.vN.ν ∂B.vA.μ :=
    (hint _ (hm h)).2 (habs h)
  rw [e2, BesLev.per, besPer]
  congr 1; funext h₁; congr 1; funext n
  exact (GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand D hD ψ σ J B s vL Y G Φ hΦ h h₁ n).symm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → ContrLaw D → FlatLaw D → BiAct D → ValX t := by
  first | exact @GlobalTheory.ValFin.valX | exact GlobalTheory.ValFin.valX | (intros; apply GlobalTheory.ValFin.valX <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  first | exact @GlobalTheory.innerProductFormula_of_hypotheses | exact GlobalTheory.innerProductFormula_of_hypotheses | (intros; apply GlobalTheory.innerProductFormula_of_hypotheses <;> assumption)
end
