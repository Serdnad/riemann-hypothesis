module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle481
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle697
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle388
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiFlatMapEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle698
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle692
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle702
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle574
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.combination_produces_datum_all_localModels : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) → ∀ T₀, p.IsModel ψ FS FT T₀ → ∀ O Ξ : SB (Matrix Y Y' k), IsOne O → T₀ O ≠ 0 → T₀ Ξ = comb ψ S T c (T₀ O) → p.IsCombAt ψ FS FT c Ξ.1 := by
  first | exact @GlobalTheory.FlatPlace.isCombAt_of_one | exact GlobalTheory.FlatPlace.isCombAt_of_one | (intros; apply GlobalTheory.FlatPlace.isCombAt_of_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.exists_localModel_of_splitPlaceThetaFun : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  first | exact @GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt | exact GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt | (intros; apply GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenThetaStep_realZeta_nonvanishing : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, RealZeta D := by
  first | exact @GlobalTheory.EvenOntoRealZeta.realZeta | exact GlobalTheory.EvenOntoRealZeta.realZeta | (intros; apply GlobalTheory.EvenOntoRealZeta.realZeta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselLevel_one_coset_at_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), (∃ u : UX D ρ, ∃ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (Formalism.L2.Theta.mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a)) → ∃ r ∈ Rgrp (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)), r ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ g = r * k := by
  first | exact @GlobalTheory.OneCosetBFPlace.one_coset_place | exact GlobalTheory.OneCosetBFPlace.one_coset_place | (intros; apply GlobalTheory.OneCosetBFPlace.one_coset_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerContFB



theorem kerFB_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0 := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  have hn : ∀ t, ψ t * star (ψ t) = 1 := fun t => by
    have h1 : ‖ψ t‖ = 1 := s.weil₀.std.1.2.1 t
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hpsi : psiBes ψ B.d 1 (vecB B.o B.ζ) 1 = 1 :=
    (GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _)
  have hfl : ∀ Ψ, flFB s Ψ = flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0 Ψ := fun Ψ => by
    simp only [flFB, flatS, hxe]
  have heq : ∀ h h₀ h₁, s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ)) =
      flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) := by
    intro h h₀ h₁
    have e := GlobalTheory.T.jacobiToBesselFlatMap_equivariant D ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ Φ hΦ) h₀ 1 (one_mem _) h₁
    rw [hpsi, star_one, one_smul, one_mul] at e
    rw [← e, hfl]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hth : ∀ h, IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := fun h => by
    rw [hfl]
    exact (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x hx 0 _
      (s.weil.om_pres _ Φ hΦ)).2
  set K : Mx D B.L.rank J.W₀.rank → GA D B.V × GA D J.W₀ × GA D B.A → ℂ := fun w q =>
    s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ w) * star (omz (q.2.1, 1) Φ₀ w) with hK
  have hP : ∀ q : GA D B.V × GA D J.W₀ × GA D B.A, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (q.2.1, B.o.emb (q.2.2, 1))
      (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0 = ∫ w in vL.𝓕, K w q ∂vL.μ := fun q => by
    simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x hx Φ hΦ
    have hJ := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ χ χz omz homz Φ₀ hΦ₀
    have hK' : Function.uncurry K = fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0
          (s.om (J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) Φ) (B.o.jB ⬝ p.1) * star (omz (p.2.2.1, 1) Φ₀ p.1) := by
      funext p
      simp only [Function.uncurry, hK, heq]
    rw [hK']
    have ha : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.2.1 :=
      continuous_fst.comp (continuous_snd.comp continuous_snd)
    have hb : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.2.2 :=
      continuous_snd.comp (continuous_snd.comp continuous_snd)
    have hh : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have hA : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) => embA B.d B.o p.2.2.2 := by
      simp only [embA_apply]
      exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (hb.prodMk continuous_const))
    have h2 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        (((J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) : GA D J.W × GA D B.V), ((0 : Mx D J.W₀.rank σ),
          (B.o.jB ⬝ p.1 : WO J.W₀ B.V₀))) :=
      ((J.d.continuous_embed.comp ha).prodMk (hA.mul hh)).prodMk
        (continuous_const.prodMk (continuous_const.matrix_mul continuous_fst))
    have h3 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        flatAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x) 0
          (s.om (J.d.emb0 p.2.2.1, embA B.d B.o p.2.2.2 * p.2.1) Φ) (B.o.jB ⬝ p.1) := by
      convert h1.comp h2 using 2
      simp only [Function.comp_apply]
    have h4 : Continuous fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        omz (p.2.2.1, 1) Φ₀ p.1 :=
      hJ.comp (f := fun p : Mx D B.L.rank J.W₀.rank × (GA D B.V × GA D J.W₀ × GA D B.A) =>
        (((p.2.2.1, 1) : GA D J.W₀ × GA D B.L), (p.1 : WO J.W₀ B.L))) ((ha.prodMk continuous_const).prodMk continuous_fst)
    exact h3.mul h4.star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ w q, K (γ + w) q = K w q := by
    rintro _ ⟨γ, rfl⟩ w q
    have e1 := (s.weil₀.om_pres (q.2.1, B.o.emb (q.2.2, 1)) _ (hth q.1)).quasi (B.o.iB * γ) (B.o.jB ⬝ w)
    have e2 := (homz.om_pres (q.2.1, 1) Φ₀ hΦ₀).quasi γ w
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ w) = symplOH J.W₀ B.L (rat γ) w := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ (rat γ + w)) *
        star (omz (q.2.1, 1) Φ₀ (rat γ + w)) =
      s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ)) (B.o.jB ⬝ w) * star (omz (q.2.1, 1) Φ₀ w)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ w)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, hcont, -, -⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  have : (fun q : GA D B.V × GA D J.W₀ × GA D B.A => contractT B.o J.W₀ vL.μ vL.𝓕
      (s.om₀ (q.2.1, B.o.emb (q.2.2, 1)) (flFB s (s.om (1, q.1) Φ))) (omz (q.2.1, 1) Φ₀) 0) =
      fun q => ∫ w in vL.𝓕, K w q ∂vL.μ := funext hP
  rw [this]; exact hcont

end GlobalTheory.KerContFB

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.besselToJacobiFlatMap_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ Ψ, IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ flagN J.d, ∀ h', flBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = star (psiFlag ψ J.d n) • s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flBF s Ψ)) := by
  first | exact @GlobalTheory.AscFlatEqui.flBF_equivariant | exact GlobalTheory.AscFlatEqui.flBF_equivariant | (intros; apply GlobalTheory.AscFlatEqui.flBF_equivariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.fourierJacobiToBessel_pairedKernel_heightBound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
  first | exact @GlobalTheory.PairKerBound.kernel_bound | exact GlobalTheory.PairKerBound.kernel_bound | (intros; apply GlobalTheory.PairKerBound.kernel_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.expansionPairing_invariant_inner_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.ExpansionInvariance.pairPts_update_top | exact GlobalTheory.ExpansionInvariance.pairPts_update_top | (intros; apply GlobalTheory.ExpansionInvariance.pairPts_update_top <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass


theorem _root_.GlobalTheory.T.rowPeriodSubgroup_finitePoints_semidirect : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R), ∀ j ∈ idx D,
    IsClosed (((rowGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsClosed (((rowN ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    (rowN ch.G j).subgroupOf (GfC _) ≤ (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) ∧
    IsOpen (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsCompact (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    ∃ (π : (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GfC (ch.G.V (.top j)))
      (σ : GfC (ch.G.V (.top j)) →* (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ (rowN ch.G j).subgroupOf (GfC _)) ∧
      ∀ b : GfC (ch.G.V (.grid D.R.m j)), prSet ch.G j b = π '' {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} := by
  first | exact @GlobalTheory.CellMass.rowGrp_finite_semidirect | exact GlobalTheory.CellMass.rowGrp_finite_semidirect | (intros; apply GlobalTheory.CellMass.rowGrp_finite_semidirect <;> assumption)
end

section

open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear

theorem _root_.GlobalTheory.T.lastSeesaw_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 0 := by
  first | exact @GlobalTheory.LastPositionLin.lastLin_zero | exact GlobalTheory.LastPositionLin.lastLin_zero | (intros; apply GlobalTheory.LastPositionLin.lastLin_zero <;> assumption)
end

section

open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear

theorem _root_.GlobalTheory.T.lastSeesaw_linear_right_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 1 := by
  first | exact @GlobalTheory.ConnectionLinear.big_lastLin_one | exact GlobalTheory.ConnectionLinear.big_lastLin_one | (intros; apply GlobalTheory.ConnectionLinear.big_lastLin_one <;> assumption)
end

section

open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear

theorem _root_.GlobalTheory.T.thetaContraction_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 0 := by
  first | exact @GlobalTheory.ConnectionLinear.contrLin_left | exact GlobalTheory.ConnectionLinear.contrLin_left | (intros; apply GlobalTheory.ConnectionLinear.contrLin_left <;> assumption)
end
