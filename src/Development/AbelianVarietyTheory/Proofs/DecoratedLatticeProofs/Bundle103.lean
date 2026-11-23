module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle002
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle022
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle102
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle161
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

open Formalism.IndefR.FWT GlobalTheory.HolDict

namespace GlobalTheory.HolLabel

theorem eq_self_of_strictMono {n : ℕ} {F K : Fin n → Fin n} (hK : StrictMono K) (hF : StrictMono F)
    (hFK : ∀ x, F (K x) = x) (x : Fin n) : K x = x :=
  le_antisymm ((hF.le_apply (x := K x)).trans_eq (hFK x)) hK.le_apply

theorem holShape_signs_first : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ), (∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ) → ∀ (i : Fin D.R.m) (M : DSModel (Wc D i) (Formalism.IndefR.Links.parAt (Wc D i) σ)), GlobalTheory.HolDict.HolShape M ∧ (∃ wt, GlobalTheory.HolDict.WtIs M wt) ∧ ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
  intro D σ hσ i M
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hp : ∀ ρ, Formalism.IndefR.Links.parAt (Wc D i) σ ρ =
      Formalism.L2.NTheta.holPar _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := fun ρ => by
    unfold Formalism.IndefR.Links.parAt; rw [if_pos (hσ ρ)]
  have ho : ∀ ρ, Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := fun ρ => by
    rw [hpq ρ, hrk]; exact Formalism.L2.NTheta.odd_r _
  have hentL : ∀ ρ (c : Fin ((Wc D i).sig (tauE D ρ)).1),
      Formalism.L2.NTheta.holEnt _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) (Sum.inl c) =
        Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (c : ℕ) := fun ρ c => by
    unfold Formalism.IndefR.Links.kapAt
    rw [Formalism.L2.NTheta.holEnt_kapW _ _ _ (ho ρ)]
    rfl
  have hentR : ∀ ρ (c : Fin ((Wc D i).sig (tauE D ρ)).2),
      Formalism.L2.NTheta.holEnt _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) (Sum.inr c) =
        Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (((Wc D i).sig (tauE D ρ)).1 + (c : ℕ)) := fun ρ c => by
    unfold Formalism.IndefR.Links.kapAt
    rw [Formalism.L2.NTheta.holEnt_kapW _ _ _ (ho ρ)]
    rfl
  have heps : ∀ ρ a, M.ε ρ a = decide ((a : ℕ) < pW D i ρ) := by
    intro ρ
    obtain ⟨hanti, f, hf, hS⟩ := M.enum ρ
    rw [hp ρ] at hS
    have hpqρ := hpq ρ
    have hL := hentL ρ
    have hR := hentR ρ
    have hlt : ∀ m n : ℕ, m < n → n < (Wc D i).rank → Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n < Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) m := by
      intro m n hmn hn
      have h1 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc (Formalism.IndefR.Links.lab σ ρ)) (n - m) m (by omega)
      rw [show m + (n - m) = n by omega] at h1
      have h2 : (1 : ℚ) ≤ ((n - m : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ n - m)
      linarith
    have mem1 : ∀ a : Fin (Wc D i).rank, ∃ n : Fin (Wc D i).rank,
        f a = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n ∧ M.ε ρ a = decide ((n : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
      intro a
      have hm : (f a, M.ε ρ a) ∈ Formalism.L2.NTheta.holPar ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := by
        rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
      rcases x with c | c
      · simp only [hL, Sum.elim_inl, Prod.mk.injEq] at hx
        exact ⟨⟨c, by omega⟩, hx.1.symm, by rw [← hx.2]; exact (decide_eq_true c.2).symm⟩
      · simp only [hR, Sum.elim_inr, Prod.mk.injEq] at hx
        exact ⟨⟨((Wc D i).sig (tauE D ρ)).1 + c, by omega⟩, hx.1.symm, by rw [← hx.2]; exact (decide_eq_false (by simp)).symm⟩
    have mem2 : ∀ n : Fin (Wc D i).rank, ∃ a : Fin (Wc D i).rank,
        f a = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n ∧ M.ε ρ a = decide ((n : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
      intro n
      have hm : ∀ x, (Formalism.L2.NTheta.holEnt ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) x,
          Sum.elim (fun _ => true) (fun _ => false) x) ∈ Finset.univ.image (fun a => (f a, M.ε ρ a)) := fun x => by
        rw [← hS]; unfold Formalism.L2.NTheta.holPar; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
      by_cases hn : (n : ℕ) < ((Wc D i).sig (tauE D ρ)).1
      · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hm (Sum.inl ⟨n, hn⟩))
        simp only [hL, Sum.elim_inl, Prod.mk.injEq] at ha
        exact ⟨a, ha.1, by rw [ha.2]; exact (decide_eq_true hn).symm⟩
      · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (hm (Sum.inr ⟨n - ((Wc D i).sig (tauE D ρ)).1, by omega⟩))
        simp only [hR, Sum.elim_inr, Prod.mk.injEq] at ha
        rw [show ((Wc D i).sig (tauE D ρ)).1 + (n - ((Wc D i).sig (tauE D ρ)).1) = n by omega] at ha
        exact ⟨a, ha.1, by rw [ha.2]; exact (decide_eq_false hn).symm⟩
    choose F hF1 hF2 using mem1
    choose K hK1 hK2 using mem2
    have fanti : ∀ a b : Fin (Wc D i).rank, a < b → f b < f a := fun a b hab => by
      have h1 := hanti hab
      rw [hf, hf] at h1
      exact_mod_cast h1
    have hFm : StrictMono F := fun a b hab => by
      have h1 := fanti a b hab
      rw [hF1 a, hF1 b] at h1
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with hc | hc
      · exact lt_asymm h1 (hlt _ _ hc (F a).2)
      · rw [hc] at h1; exact lt_irrefl _ h1
    have hKm : StrictMono K := fun n m hnm => by
      have h1 := hlt _ _ hnm m.2
      rw [← hK1 n, ← hK1 m] at h1
      by_contra hc
      rcases (not_lt.1 hc).lt_or_eq with hc | hc
      · exact lt_asymm h1 (fanti _ _ hc)
      · rw [hc] at h1; exact lt_irrefl _ h1
    have hFK : ∀ n, F (K n) = n := fun n => by
      have h1 : Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) (F (K n)) = Formalism.L2.NTheta.lamAt (D.hc (Formalism.IndefR.Links.lab σ ρ)) n := by rw [← hF1, hK1]
      rcases lt_trichotomy (F (K n)) n with hc | hc | hc
      · exact absurd h1 (hlt _ _ hc n.2).ne'
      · exact hc
      · exact absurd h1 (hlt _ _ hc (F (K n)).2).ne
    intro a
    have h1 := hK2 a
    rw [eq_self_of_strictMono hKm hFm hFK a] at h1
    exact h1
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) := fun ρ => by
    have he := M.enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    rw [hp ρ] at hS
    have hm : (f a, M.ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.IndefR.Links.kapAt (Wc D i) σ ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.IndefR.Links.kapAt (Wc D i) σ ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.IndefR.Links.kapAt (Wc D i) σ ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, heps ρ⟩, ?_, heps⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ (M.ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg (M.ε ρ) (arr (nNeg (M.ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolLabel
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.LabAtRealPlace

theorem sigmaOf_sqrt (D : D7) (τ : D.what₂.Tau) :
    D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD = D.host.sqrtMinusD := by
  have h1 : D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) ∈
      D.R.Psi := by
    rw [show D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) = (D.eTau τ).1 from D.host.gal.apply_symm_apply _]
    exact (D.eTau τ).2
  exact (D.host.galE_mem_Psi_iff _).1 h1

theorem labE_sqrt (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (τ ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = tauE D ρ D.host.sqrtMinusD := by
  have hm : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have e1 : Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = σ (D.embE D.host.sqrtMinusD) := by
    show σ (D.embE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  have e2 : Formalism.IndefR.Conj.labE D.what₂.embLL ρ D.host.sqrtMinusD = D.what₂.embLL (D.embE D.host.sqrtMinusD) := by
    show D.what₂.embLL (D.embE (D.host.sigmaOf ((D.eTau ρ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  rw [e1, h.2 _ hm, ← e2, Formalism.IndefR.Conj.labE_base]

theorem labE_lab (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := by
  have hex : ∃ τ, Formalism.IndefR.Links.labE σ τ = tauE D ρ ∨
      Formalism.IndefR.Links.labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
    obtain ⟨B, hB⟩ := Formalism.IndefR.Conj.labExists σ
    have h' := hB (B.perm.symm ρ)
    rw [Formalism.IndefR.Conj.ArchLab.emb, Equiv.apply_symm_apply] at h'
    refine ⟨B.perm.symm ρ, ?_⟩
    split_ifs at h'
    exacts [Or.inl h', Or.inr h']
  rw [Formalism.IndefR.Links.lab, dite_eq_left hex]
  refine hex.choose_spec.resolve_right fun h' => ?_
  have h2 := labE_sqrt D σ s h hex.choose ρ
  rw [h', RingHom.comp_apply] at h2
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : (tauE D ρ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
    rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
  rw [hx] at h3
  have h4 : x ^ 2 = -(D.host.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  nlinarith [sq_nonneg x]

theorem main : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s → ∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := fun D σ s h ρ => labE_lab D σ s h ρ

end GlobalTheory.LabAtRealPlace
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions


theorem _root_.GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  first | exact @GlobalTheory.SplitValuePow.not_isOfFinOrder_val | exact GlobalTheory.SplitValuePow.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValuePow.not_isOfFinOrder_val <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.sphericalHeckeOperator_eq_smul_of_localParameter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (stabLoc σ J L v), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLoc σ J v) V) (x : V), IsParamVec σ J L h ρ x B → heckeVec ρ (stabLoc σ J L v) φ x = z • x := by
  first | exact @GlobalTheory.LFun.EigLoc.heckeVec_eq_smul_of_isParamVec | exact GlobalTheory.LFun.EigLoc.heckeVec_eq_smul_of_isParamVec | (intros; apply GlobalTheory.LFun.EigLoc.heckeVec_eq_smul_of_isParamVec <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalSum

open GlobalTheory.CuspRep.ParLaws

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem diagU_mul (p q : borel k (Fin N)) (i : Fin N) : diagU (p * q) i = diagU p i * diagU q i := by
  unfold diagU
  erw [map_mul]
  rw [Pi.mul_apply, map_mul]

theorem borelSph_mul_left {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin N) k} (hb : b ∈ borel k (Fin N)) (x : GL (Fin N) k) : ψ (b * x) = ψ b * ψ x := by
  obtain ⟨b', hb', w, hw, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val x
  have hb'' : b' ∈ borel k (Fin N) := (mem_borel _).2 hb'
  have hbb : b * b' ∈ borel k (Fin N) := mul_mem hb hb''
  have e1 : b * (b' * w) = (b * b') * w := (mul_assoc _ _ _).symm
  rw [e1, h.1 _ _ hw, h.1 _ _ hw]
  have t1 := fun i => (val_diagU ⟨b, hb⟩ i).symm
  have t2 := fun i => (val_diagU ⟨b', hb''⟩ i).symm
  have t3 := fun i => (val_diagU ⟨b * b', hbb⟩ i).symm
  rw [h.2 _ hb _ t1, h.2 _ hb'' _ t2, h.2 _ hbb _ t3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e2 : (⟨b * b', hbb⟩ : borel k (Fin N)) = ⟨b, hb⟩ * ⟨b', hb''⟩ := rfl
  rw [e2, diagU_mul, ord_mul, zpow_add₀ (hγ i)]

theorem eq_of_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {g₁ g₂ : GL (Fin N) k} (h₁ : g₁ ∈ R) (h₂ : g₂ ∈ R) (h : g₁⁻¹ * g₂ ∈ KO k (Fin N)) : g₁ = g₂ := by
  obtain ⟨κ, hκ, κ', hκ', e⟩ := hR.1 g₂ h₂
  obtain ⟨g, -, hu⟩ := hR.2 κ hκ
  have a2 : g₂⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₂⁻¹ * (κ * g₀) = κ'⁻¹ := by rw [e]; group
    rw [this]; exact inv_mem hκ'
  have a1 : g₁⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₁⁻¹ * (κ * g₀) = (g₁⁻¹ * g₂) * (g₂⁻¹ * (κ * g₀)) := by group
    rw [this]; exact mul_mem h a2
  rw [hu g₁ ⟨h₁, a1⟩, hu g₂ ⟨h₂, a2⟩]

theorem exists_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) {g : GL (Fin N) k} (hg : g ∈ R) :
    ∃ g' ∈ R, g'⁻¹ * (κ * g) ∈ KO k (Fin N) := by
  obtain ⟨κ₁, hκ₁, κ₁', hκ₁', e⟩ := hR.1 g hg
  obtain ⟨g', ⟨hg', hm⟩, -⟩ := hR.2 (κ * κ₁) (mul_mem hκ hκ₁)
  refine ⟨g', hg', ?_⟩
  have : g'⁻¹ * (κ * g) = (g'⁻¹ * (κ * κ₁ * g₀)) * κ₁' := by rw [e]; group
  rw [this]; exact mul_mem hm hκ₁'

theorem sum_kappa_mul {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ)
    {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) : ∑ g ∈ R, ψ (κ * g) = ∑ g ∈ R, ψ g := by
  classical
  choose f hf hfK using fun g (hg : g ∈ R) => exists_isRepsK hR hκ hg
  refine Finset.sum_bij f hf (fun a ha b hb e => ?_) (fun c hc => ?_) (fun a ha => ?_)
  · have h1 := hfK a ha
    have h2 := hfK b hb
    rw [e] at h1
    apply eq_of_isRepsK hR ha hb
    have : a⁻¹ * b = ((f b hb)⁻¹ * (κ * a))⁻¹ * ((f b hb)⁻¹ * (κ * b)) := by group
    rw [this]; exact mul_mem (inv_mem h1) h2
  · obtain ⟨a, ha, hm⟩ := exists_isRepsK hR (inv_mem hκ) hc
    refine ⟨a, ha, eq_of_isRepsK hR (hf a ha) hc ?_⟩
    have : (f a ha)⁻¹ * c = ((f a ha)⁻¹ * (κ * a)) * (a⁻¹ * (κ⁻¹ * c)) := by group
    rw [this]; exact mul_mem (hfK a ha) hm
  · have : κ * a = f a ha * ((f a ha)⁻¹ * (κ * a)) := by group
    rw [this, h.1 _ _ (hfK a ha)]

end GlobalTheory.ZonalSum


open GlobalTheory.ZonalSum in
theorem GlobalTheory.ZonalSum.sum_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (g₀ : GL (Fin N) k) (R : Finset (GL (Fin N) k)), IsRepsK g₀ R → ∀ m : GL (Fin N) k, ∑ g ∈ R, ψ (m * g) = ψ m * ∑ g ∈ R, ψ g := by
  intro k _ _ _ _ N γ ψ h hγ g₀ R hR m
  obtain ⟨b, hb, κ, hκ, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val m
  have hb' : b ∈ borel k (Fin N) := (mem_borel _).2 hb
  have e : ∀ g, ψ (b * κ * g) = ψ b * ψ (κ * g) := fun g => by
    rw [mul_assoc]; exact borelSph_mul_left h hγ hb' _
  simp only [e]
  rw [← Finset.mul_sum, sum_kappa_mul h hR hκ, h.1 _ _ hκ]

end
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

theorem _root_.GlobalTheory.T.casimir_eq_gelfandValue_of_infinitesimalCharacter : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ χ : Fin n → ℂ, GlobalTheory.Dec.HasInfChar ε χ σ → ∀ v, casimir R.HK.act v = GlobalTheory.Dec.gelfVal χ 2 • v := by
  first | exact @GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar | exact GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar | (intros; apply GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar <;> assumption)
end

section

theorem GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup : GlobalTheory.Published.HarishChandraModules :=
  GlobalTheory.HcPort.print_harishChandraModules
end

section

open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  first | exact @GlobalTheory.TenInj.main | exact GlobalTheory.TenInj.main | (intros; apply GlobalTheory.TenInj.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsSelfDualC S ΛS → IsSelfDualC T ΛT → f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) → f ≠ 0 → f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  first | exact @GlobalTheory.VacCyclic.vac_mem_span | exact GlobalTheory.VacCyclic.vac_mem_span | (intros; apply GlobalTheory.VacCyclic.vac_mem_span <;> assumption)
end

section

namespace GlobalTheory.Corev.CmTwoClosing

theorem cmGoodModel_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : Formalism.L2.Th1.CM.CM2 :=
  GlobalTheory.T.cmLattice_good_model_unramified (GlobalTheory.T.exists_idealClass_artinSymbol_of_globalArtin hA) GlobalTheory.T.chebotarev_degreeOne_valuationSubrings

end GlobalTheory.Corev.CmTwoClosing
end
