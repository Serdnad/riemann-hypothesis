module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle123
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle110
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureIffMapMemMatrixHomLatticeCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle001
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

theorem exists_cxPts_ker_eq : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  intro X p _ U hU m hm
  have h1 := p.finiteType_appLE (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : m.IsMaximal := hm
  letI : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, U) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, U) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, U) →+* ℂ := (e.symm : (Γ(X, U) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p U a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, U) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  refine ⟨CxPts.ofHom hU φ hφ, CxPts.ofHom_mem hU φ hφ, ?_⟩
  have hev : CxPts.evHom (CxPts.ofHom_mem hU φ hφ) = φ := by
    ext f
    rw [← CxPts.ev_eq, CxPts.ev_ofHom]
  rw [hev]
  ext f
  rw [RingHom.mem_ker]
  show f ∈ m ↔ e.symm (Ideal.Quotient.mk m f) = 0
  rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.AffCxPts

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} {k : ℕ}

def coords (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    Fin k → ℂ :=
  fun i => CxPts.ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) y.1

theorem evHom_comp (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U))
    (hC : ∀ a, φ (MvPolynomial.C a) = algX p U a) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    (CxPts.evHom y.2).comp φ = MvPolynomial.eval (coords φ y) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, hC, MvPolynomial.eval_C, ← CxPts.ev_eq y.2, CxPts.ev_algX y.2,
      RingHom.id_apply]
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, coords, CxPts.ev_eq y.2]

def homAt {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ) (z : Fin k → ℂ)
    (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z)) : Γ(X, U) →+* ℂ :=
  φ.liftOfSurjective hφ ⟨MvPolynomial.eval z, hz⟩

theorem homAt_comp {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ)
    (z : Fin k → ℂ) (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z))
    (P : MvPolynomial (Fin k) ℂ) : homAt hφ z hz (φ P) = MvPolynomial.eval z P :=
  φ.liftOfSurjective_comp_apply hφ ⟨_, hz⟩ P

end GlobalTheory.AffCxPts


open GlobalTheory.AffCxPts GlobalTheory.CxPts GlobalTheory.Points in
theorem GlobalTheory.AffCxPts.homeomorph_zeroSet : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (U : X.Opens),
    IsAffineOpen U → (algX p U).FiniteType → ∃ (k : ℕ) (G : Finset (MvPolynomial (Fin k) ℂ)),
      Nonempty (↥(GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U) ≃ₜ
        ↥{z : Fin k → ℂ | ∀ P ∈ G, MvPolynomial.eval z P = 0}) := by
  intro X p U hU hft
  let := (algX p U).toAlgebra
  obtain ⟨k, φa, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  let φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U) := φa.toRingHom
  have hφ' : Function.Surjective φ := hφ
  have hC : ∀ a, φ (MvPolynomial.C a) = algX p U a := fun a => φa.commutes a
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (RingHom.ker φ) :)
  refine ⟨k, G, ⟨?_⟩⟩
  let Z : Set (Fin k → ℂ) := {z | ∀ P ∈ G, MvPolynomial.eval z P = 0}
  have hker (z : Z) : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval (z : Fin k → ℂ)) := by
    rw [← hG]
    exact Ideal.span_le.2 fun P hP => RingHom.mem_ker.2 (z.2 P hP)
  have hψ (z : Z) (a : ℂ) : homAt hφ' z (hker z) (algX p U a) = RingHom.id ℂ a := by
    rw [← hC, homAt_comp, MvPolynomial.eval_C, RingHom.id_apply]
  let s (z : Z) : CxPts p (RingHom.id ℂ) := ofHom hU (homAt hφ' z (hker z)) (hψ z)
  have hs_ev (z : Z) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (s z) = homAt hφ' z (hker z) f :=
    ev_ofHom hU _ (hψ z) f
  have hcoords (z : Z) (i : Fin k) :
      ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) (s z) = (z : Fin k → ℂ) i := by
    rw [hs_ev, homAt_comp, MvPolynomial.eval_X]
  have htZ (y : ↥(ptsIn p (RingHom.id ℂ) U)) : coords φ y ∈ Z := fun P hP => by
    rw [← evHom_comp φ hC y, RingHom.comp_apply,
      RingHom.mem_ker.1 (hG ▸ Ideal.subset_span hP : P ∈ RingHom.ker φ), map_zero]
  have hgen : Subring.closure (Set.range (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p U) ∪
      Set.range fun i : Fin k => φ (MvPolynomial.X i)) = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨P, rfl⟩ := hφ' f
    induction P using MvPolynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, (hC a).symm⟩)
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul]; exact mul_mem hP (Subring.subset_closure (Or.inr ⟨i, rfl⟩))
  have hsc : Continuous s := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    refine (PtsOver.tendsto_iff_of_generators hU (ofHom_mem hU _ (hψ z)) hgen).2
      ⟨Eventually.of_forall fun w => ofHom_mem hU _ (hψ w), ?_⟩
    rintro _ ⟨i, rfl⟩
    have e (w : Z) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i)) = (w : Fin k → ℂ) i := hcoords w i
    rw [show (fun w : Z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i))) =
        fun w : Z => (w : Fin k → ℂ) i from funext e]
    exact (e z).symm ▸ ((continuous_apply i).comp continuous_subtype_val).tendsto z
  exact
    { toFun := fun y => ⟨coords φ y, htZ y⟩
      invFun := fun z => ⟨s z, ofHom_mem hU _ (hψ z)⟩
      left_inv := fun y => by
        refine Subtype.ext (Subtype.ext (ext_of_valR hU (ofHom_mem hU _ (hψ _)) y.2 fun f => ?_))
        obtain ⟨P, rfl⟩ := hφ' f
        change ev p (RingHom.id ℂ) U (φ P) (s _) = ev p (RingHom.id ℂ) U (φ P) y.1
        rw [hs_ev, homAt_comp, ev_eq y.2, ← RingHom.comp_apply, evHom_comp φ hC y]
      right_inv := fun z => Subtype.ext (funext fun i => hcoords z i)
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
        exact (continuousOn_iff_continuous_domRestrict.1 (continuousOn_ev (φ (MvPolynomial.X i))))
      continuous_invFun := hsc.subtype_mk _ }
end
end

section

namespace GlobalTheory.RowClose

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.RowClose.heckeSplitOne_of_charTied : ∀ (D : _root_.Formalism.BasicNotions.D7) (C : _root_.Formalism.L2.Host.CharFrame D)
    (nch : _root_.Formalism.BasicNotions.NChoice D) (Tp : _root_.Formalism.L2.Host.TupTied D C nch), _root_.Formalism.L2.Host.NCharTied D C nch Tp →
    _root_.GlobalTheory.RowCopy.HeckeSplitOne D := by
  intro D C nch Tp T
  have h := _root_.GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut
    (_root_.GlobalTheory.HeckeSplitRow.heckeCharTie_of_tied T)
  unfold _root_.GlobalTheory.ThetaExh.HeckeSplitOne at h
  exact h

end GlobalTheory.RowClose
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.sphericalRepGL_exists_satakeParameters : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  first | exact @GlobalTheory.SatakeExists.main | exact GlobalTheory.SatakeExists.main | (intros; apply GlobalTheory.SatakeExists.main <;> assumption)
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  first | exact @GlobalTheory.HTW.pageWord_Mi_add_hi_le | exact GlobalTheory.HTW.pageWord_Mi_add_hi_le | (intros; apply GlobalTheory.HTW.pageWord_Mi_add_hi_le <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.standard_series_b_conditions_large_prime : ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]), 5 ≤ l → 2 ≤ d → Even d → BeStd l d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be := by
  first | exact @GlobalTheory.KerStd.bHyps_of_beStd | exact GlobalTheory.KerStd.bHyps_of_beStd | (intros; apply GlobalTheory.KerStd.bHyps_of_beStd <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.exists_integral_orbit_series : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (σ : MaximalUnramifiedExtension Lc.l →+* MaximalUnramifiedExtension Lc.l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension Lc.l)) (om oms : Fin (Lc.d / 2) → MaximalUnramifiedExtension Lc.l) (ζ : MaximalUnramifiedExtension Lc.l), BeData Lc.l Lc.d σ F be0 om oms ζ → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) (beOf Lc.l Lc.d σ be0 om oms ζ) → ∃ U0 : MvPowerSeries (Bool × Fin (Lc.d / 2) × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l], Formalism.DworkPowerSeriesWeights.Integral U0 ∧ (MvPowerSeries.subst (fun v : ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1 => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l])) Lc.Th : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l]) = thetaInZ (d := Lc.d) Lc.l (MaximalUnramifiedExtension Lc.l).subtype σ om oms (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension Lc.l).subtype be0))) * U0) := by
  first | exact @GlobalTheory.KerStd.integral_cofactor_converse | exact GlobalTheory.KerStd.integral_cofactor_converse | (intros; apply GlobalTheory.KerStd.integral_cofactor_converse <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
noncomputable section

namespace GlobalTheory.KerStd.HypOrbit

open Formalism.InvariantFactorPaths.G7 (lgF at1)

theorem lg_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    PowerSeries.subst (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) (lgF ℂ_[p] p) =
      ∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p) := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by

    simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  rw [← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hA), (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hA)]

theorem cc_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    constantCoeff (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) = 0 := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by

    simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hA _ (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1

theorem hypZ_of_inHyp : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  intro D p _ hp σ om oms R M N N' r eA f f' Θ
  have hl : 2 ≤ p := by omega
  have hcl : PowerSeries.constantCoeff (lgF ℂ_[p] p) = 0 := Formalism.L2.Th1.D.Pair.cc_lgF hl
  have hA0 : HasSubst (fun i : Fin r => (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl
  have hu : ∀ k : ((R × Fin (nP D p / 2)) × Fin N × Fin N') ⊕ ((R × Fin (nP D p / 2)) × Fin N × Fin N'),
      constantCoeff ((Sum.elim (fun e => (X (false, e) : MvPowerSeries (Bool × ((R × Fin (nP D p / 2)) × Fin N × Fin N')) ℂ_[p]))
        (fun e => X (true, e))) k) = 0 := by
    intro k; cases k <;> simp
  have hhc : HasSubst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f') :=
    hasSubst_of_constantCoeff_zero fun i => cc_flin hl _ _ hu

  have hL : ∀ i : Fin r, subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p]) =
      ∑ e : (R × Fin (nP D p / 2)) × Fin N × Fin N',
        (C ((f e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (false, e) (lgF ℂ_[p] p) +
          C ((f' e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (true, e) (lgF ℂ_[p] p)) := by
    intro i
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hhc]
    unfold Formalism.L2.Th1.E.hypCoord
    rw [lg_flin hl _ _ hu, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    rfl

  set ren1 := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p])) with hren1
  set Y := (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) with hYdef
  have hR : HasSubst ren1 := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hX : HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) :=
    hasSubst_of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms)
  have hY : HasSubst Y := hasSubst_of_constantCoeff_zero fun y => constantCoeff_X _
  have hRX0 : ∀ x, constantCoeff (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) = 0 :=
    fun x => constantCoeff_subst_eq_zero hX (CofactorConverse.cc_xOfZ hl _ σ om oms) (constantCoeff_X _)
  have hRX : HasSubst (fun x => subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) :=
    hasSubst_of_constantCoeff_zero hRX0
  set W := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' => subst Y
    (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x))) with hWdef
  have hW : HasSubst W := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero hY (fun y => constantCoeff_X _) (hRX0 x)
  have hcomp : ∀ g : MvPowerSeries (Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N') ℂ_[p], subst Y (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms)
      (subst ren1 g)) = subst W g := by
    intro g
    rw [subst_comp_subst_apply hR hX, subst_comp_subst_apply hRX hY]
  have hLf : HasSubst (fun i : Fin r => subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hhc (fun i => cc_flin hl _ _ hu)
      (Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl)

  have hWx : ∀ (c : Bool) (e : (R × Fin (nP D p / 2)) × Fin N × Fin N'), subst W (at1 (c, e) (lgF ℂ_[p] p)) =
      ∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (c, e.1.2) s)) *
        (X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := by
    intro c e
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hW]
    simp only [hWdef, hren1]
    rw [subst_X hX]
    have ha : PowerSeries.HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms
        (c, e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms _)
    rw [← Formalism.L2.Th1.D.Pair.subst_subst1 hY ha]
    have hlog := CofactorConverse.log_xOfZ (d := nP D p) hl (MaximalUnramifiedExtension p).subtype σ om oms (eA.symm (e.1.1, e.2.1)) e.2.2 (c, e.1.2)
    simp only at hlog
    rw [hlog]
    unfold CofactorConverse.linP
    rw [← coe_substAlgHom hY]

    simp only [map_sum, map_mul]
    simp only [coe_substAlgHom hY, subst_C]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [subst_X hY]
    simp only [hYdef, Equiv.apply_symm_apply]
  have hEv : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (false, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linEv D p σ (oms k) q a b := by
    intro k q a b
    unfold linEv
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  have hOd : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (true, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linOd D p σ (om k) q a b := by
    intro k q a b
    unfold linOd
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  unfold Formalism.L2.Th1.D.thetaInZ Formalism.L2.Th1.Top.inHyp
  rw [hcomp, subst_comp_subst_apply hA0 hhc, subst_comp_subst_apply hLf hW]
  congr 1
  funext i
  rw [hL i]

  rw [← coe_substAlgHom hW]

  simp only [map_sum, map_add (f := _), map_mul]
  simp only [coe_substAlgHom hW, subst_C, hWx, hEv, hOd]
  rfl

end GlobalTheory.KerStd.HypOrbit
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.frobeniusSemisimplification_weilDeligne_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v') (X Y : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Weil h) X) (N : Module.End ℂ X) (a : WDRep h X) (ρ' : Representation ℂ (Weil h') Y) (N' : Module.End ℂ Y) (b : WDRep h' Y), IsSmooth ρ → IsSmooth ρ' → IsFrobSS ⇑ρ N a → IsFrobSS ⇑ρ' N' b → ∀ e : X ≃ₗ[ℂ] Y, (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) z = (σ' : _root_.Formalism.ConjugateSelfDual.G L Ω) z) → ∀ x, e (ρ σ x) = ρ' σ' (e x)) → (∀ x, e (N x) = N' (e x)) → Restricts (WD.mk a) (WD.mk b) := by
  first | exact @GlobalTheory.AboveL.restricts_of_isFrobSS | exact GlobalTheory.AboveL.restricts_of_isFrobSS | (intros; apply GlobalTheory.AboveL.restricts_of_isFrobSS <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordNum : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨rfl, hg⟩ := hO
  generalize g 0 = τ at hg
  obtain rfl : g = letter τ ψ := funext hg
  have hsm := pageWord_S_eta_m L j ε τ ψ
  refine ⟨?_, ?_, ?_, hsm.1, hsm.2.1, rfl⟩
  · intro a
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a
    rcases GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ ψ hR a with h | h
    · exact Or.inl (hth.2 h)
    · refine Or.inr ?_
      have h' : (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) ≤ ((wHat D : ℕ) : ℤ) := by
        rw [hsz]; exact h
      exact_mod_cast h'
  · have h := bHat_add_etaHat_add_sHat_le_hPage L C hR
    exact h
  · exact (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).2

end GlobalTheory.HTW.Rec
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem _root_.GlobalTheory.T.mem_closure_iff_map_mem_matrixHomLattice_completion : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (φ : P.adicCompletion E ≃+* Qq) (hφ : ∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) (hop : ∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) (hnb : ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U) {k k' : ℕ} (Y : Submodule (𝓞 E) (Matrix (Fin k') (Fin k) E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) (hb : IsUnit b.det) (hY : ∀ A ∈ Y, A.map ρ ∈ homLat W (colSpan W a) (colSpan W b)) (hT : homLat W (colSpan W a) (colSpan W b) ≤ Submodule.span W ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' (Y : Set (Matrix (Fin k') (Fin k) E)))) (y : Matrix (Fin k') (Fin k) (P.adicCompletion E)), y ∈ (Y.toAddSubgroup.map ((algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix)).topologicalClosure ↔ y.map φ ∈ homLat W (colSpan W a) (colSpan W b) := by
  first | exact @GlobalTheory.VolAt.mem_closure_iff_map_mem_homLat | exact GlobalTheory.VolAt.mem_closure_iff_map_mem_homLat | (intros; apply GlobalTheory.VolAt.mem_closure_iff_map_mem_homLat <;> assumption)
end
