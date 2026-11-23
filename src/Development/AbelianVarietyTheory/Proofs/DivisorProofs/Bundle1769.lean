module

import Development.WeilBound.ThetaLifts.ConeHypotheses.IsLocallyConstantFinprodEvalV
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Formalism.FockGram.StatementFock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle018
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

namespace GlobalTheory.AdelicCoordSupport

theorem hasCompactSupport_finprod : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  apply PositivityTheory.ThKG.hasCompactSupport_finprod <;> assumption

end GlobalTheory.AdelicCoordSupport
end

section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.lowestKTypeSpace_holomorphicKModule_killed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → lowKSub ε lam σ ≤ D ∧ KStab ε E ((lowKSub ε lam σ).comap D.subtype) ∧ (lowKSub ε lam σ).comap D.subtype ≠ ⊥ ∧ ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ (lowKSub ε lam σ).comap D.subtype, E b a x = 0 := by
  first | exact @GlobalTheory.HolDS.lowKSub_kMod | exact GlobalTheory.HolDS.lowKSub_kMod | (intros; apply GlobalTheory.HolDS.lowKSub_kMod <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem jetInVV_of_stepWeights : ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (a b : ℕ), a < b → ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
  intro K _ _ ι _ a b hlt lam ν lam' hw J P hP
  choose s' hs' using fun τ => (hw τ).2.1
  choose s hs using fun τ => (hw τ).2.2
  refine GlobalTheory.JetPoint.jetMap_mem hlt.le _ _ _ (fun ap => ?_) J
  refine GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hlt lam lam' s (fun τ => if 0 < a then s' τ else 0) _
    ⟨fun τ i => ?_, fun τ j hj => ?_, fun τ => ?_⟩ ap _ hP
  · have h := hs τ (Fin.castLE hlt.le i)
    have h0 := hs' τ i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero, Fin.val_castLE, i.2, dif_pos, Fin.eta] at h
    simp only [Fin.pos i, if_true]
    omega
  · have h := hs τ j
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero, dif_neg (not_lt.2 hj)] at h
    omega
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry DomWeight.detShift
    split_ifs with h
    · have h0 := hs' τ ⟨a - 1, by omega⟩
      have h1 := (hw τ).1 ⟨a - 1, by omega⟩
      simp only
      omega
    · simp

end GlobalTheory.ColNorms
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.liftModel_holomorphic_overReflexField : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  first | exact @GlobalTheory.LowRow.holShape_overK | exact GlobalTheory.LowRow.holShape_overK | (intros; apply GlobalTheory.LowRow.holShape_overK <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.badPlacesPrimeToHost_baseTuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  first | exact @GlobalTheory.LowRow.primeToHost_base | exact GlobalTheory.LowRow.primeToHost_base | (intros; apply GlobalTheory.LowRow.primeToHost_base <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.liftRows_antitone_signature_rank : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), Antitone (aPlAt D i σ ρ) ∧ Antitone (aMiAt D i σ ρ) ∧ pW D i ρ + qW D i ρ = (Wc D i).rank ∧ (Wc D i).rank ≤ (Vc D i).rank := by
  first | exact @GlobalTheory.LowRow.lift_rows_antitone | exact GlobalTheory.LowRow.lift_rows_antitone | (intros; apply GlobalTheory.LowRow.lift_rows_antitone <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.thetaLift_weightSizes_eventually_along_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.LowRow.weightSizes_along | exact GlobalTheory.LowRow.weightSizes_along | (intros; apply GlobalTheory.LowRow.weightSizes_along <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ m) → (∀ τ, p τ ≤ n ∧ q τ ≤ n) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) → Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) = ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  first | exact @GlobalTheory.LowRowFock.fock_delta | exact GlobalTheory.LowRowFock.fock_delta | (intros; apply GlobalTheory.LowRowFock.fock_delta <;> assumption)
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem exists_integral_inverse_lieVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  intro E _ _ _ H Dw l Xo c _ p _ T io X y Ch hp inst
  have hbij := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose σV hσV using fun τ : E →+* ℂ =>
    GlobalTheory.PowGerm.exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hι : ∀ τ a, X.ι (σV τ a) = embO io X τ a := fun τ a => X.ints.hom_inj (by
    rw [algebraMap_embO, ← X.comp, hσV']; rfl)
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit (σV τ a - σV τ' a) := by
    intro τ τ' hne
    have h1 : red io X τ ≠ red io X τ' := fun h => hne (hbij.1 h)
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h1
    refine ⟨a, ?_⟩
    have := X.ι_local
    refine (isUnit_map_iff X.ι _).1 ?_
    rw [map_sub, hι, hι]
    by_contra hu
    apply ha
    rw [← sub_eq_zero]
    show residue X.O _ - residue X.O _ = 0
    rw [← map_sub, residue_eq_zero_iff]
    exact (mem_maximalIdeal _).2 hu
  have hex : ∃ lam : Lt1 Dw → Fin (chD Ch.ch) → T.V, ∀ l l', ∑ s, lam l s * Ch.uvecT l' s = if l = l' then 1 else 0 := by
    classical
    obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD Ch.ch)
      (fun a => Matrix.of fun m j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a m))
      (E →+* ℂ) Dw.mult (fun τ a => σV τ a) Ch.uvecT hsep
      (fun a ℓ => ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a _ (hσV' _ _)) (fun τ => by
        obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
        exact GlobalTheory.PowGerm.exists_dual_of_extends (fun i => Ch.uvecT ⟨τ, i⟩) w emb hw hb)
    exact ⟨lam, fun l l' => by convert hlam l l'⟩
  obtain ⟨lam, hlam⟩ := hex
  have h1 : (Matrix.of fun ℓ e => jX X (lam ℓ e)) * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 := by
    ext ℓ ℓ'
    have h := congrArg (jX X) (hlam ℓ ℓ')

    rw [map_sum] at h
    simp only [map_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, lieVec]
    rw [h]
    split_ifs
    · exact map_one _
    · exact map_zero _
  refine ⟨Matrix.of fun ℓ e => jX X (lam ℓ e), fun a b => isIntV_jX X _, h1, ?_⟩
  have e : Lt1 Dw ≃ Fin (chD Ch.ch) := Fintype.equivFinOfCardEq (GlobalTheory.IntChartCheck.dim_eq Ch).symm
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 h1

end GlobalTheory.PrimePart
end

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.logarithmic_group_law_split_by_idempotent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d d' : ℕ) (G : LogFGL v d) (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C), (∀ a b, IsIntV v (I a b)) → (∀ a b, IsIntV v (P a b)) → P * I = 1 → (∃ φ, IsIntHom G G φ (I * P)) → (∃ ψ, IsIntHom G G ψ (1 - I * P)) → ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  first | exact @GlobalTheory.IdemImage.exists_image | exact GlobalTheory.IdemImage.exists_image | (intros; apply GlobalTheory.IdemImage.exists_image <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

theorem v_pow_sub_pow_lt_one {C : Type} [Field C] (v : Valuation C NNReal) {x y : C} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x - y) < 1) (n : ℕ) : v (x ^ n - y ^ n) < 1 := by
  rw [← geom_sum₂_mul x y n, map_mul]
  have hs : v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le hx) zero_le (pow_le_one₀ zero_le hy)
  calc v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * v (x - y) ≤ 1 * v (x - y) :=
        mul_le_mul_of_nonneg_right hs zero_le
    _ = v (x - y) := one_mul _
    _ < 1 := hxy

private lemma exists_mem_sub_one_mem_of_maximal_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal)
    (hQ : Q.IsMaximal) (h : P ≠ Q) : ∃ a ∈ P, a - 1 ∈ Q := by
  have htop : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne hP hQ h
  have h1 : (1 : R) ∈ P ⊔ Q := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  refine ⟨a, ha, ?_⟩
  have hb' : a - 1 = -b := by rw [← hab]; ring
  rw [hb']
  exact Q.neg_mem hb

theorem exists_sub_one_mem_and_mem {R ι : Type} [CommRing R] [Finite ι] (P : ι → Ideal R) (hP : ∀ i, (P i).IsMaximal)
    (t : ι) : ∃ e : R, e - 1 ∈ P t ∧ ∀ i, P i ≠ P t → e ∈ P i := by
  classical
  haveI := Fintype.ofFinite ι
  have hc : ∀ i, ∃ a : R, (P i ≠ P t → a ∈ P i) ∧ a - 1 ∈ P t := by
    intro i
    by_cases hi : P i = P t
    · exact ⟨1, fun h => absurd hi h, by simp⟩
    · obtain ⟨a, ha, ha1⟩ := exists_mem_sub_one_mem_of_maximal_ne (hP i) (hP t) hi
      exact ⟨a, fun _ => ha, ha1⟩
  choose a ha using hc
  refine ⟨∏ i, a i, ?_, ?_⟩
  · refine Ideal.Quotient.eq.1 ?_
    rw [map_prod, map_one]
    exact Finset.prod_eq_one fun i _ => by
      rw [← map_one (Ideal.Quotient.mk (P t))]
      exact Ideal.Quotient.eq.2 (ha i).2
  · intro i hi
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    exact Ideal.mul_mem_right _ _ ((ha i).1 hi)

private lemma pow_pow_mul_eq_self_of_pow_sub_one_eq_one {C : Type} [Field C] {z : C} {h : ℕ} (p : ℕ) (hp : 0 < p)
    (hz : z ^ (p ^ h - 1) = 1) (M : ℕ) : z ^ p ^ (h * M) = z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih]
    have hph : p ^ h = p ^ h - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [hph, pow_succ, hz, one_mul]

theorem exists_approx_root_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  intro E _ _ _ H l c p _ T io X τ h hh lab hlab z hz ha₀ r
  classical
  obtain ⟨a₀, ha₀⟩ := ha₀
  have hp : p.Prime := Fact.out
  haveI : NeZero h := ⟨hh.ne'⟩
  obtain ⟨e, he1, he⟩ := exists_sub_one_mem_and_mem (fun σ : E →+* ℂ => primeBelow io X σ)
    (fun σ => (primeBelow_isMaximal_card E H l c p T io X σ).1) τ
  have hv1 : ∀ σ a, X.v (embX io X σ a) ≤ 1 := fun σ a => v_embX_le_one io X σ a
  have hvz : X.v z ≤ 1 := by
    have hn : p ^ h - 1 ≠ 0 := by
      have : 2 ≤ p ^ h := le_trans hp.two_le (Nat.le_self_pow hh.ne' p)
      omega
    have h1 : X.v z ^ (p ^ h - 1) ≤ 1 := by rw [← map_pow, hz, map_one]
    exact (pow_le_one_iff_of_nonneg zero_le hn).1 h1
  have hvzs : ∀ n : ℕ, X.v (z ^ n) ≤ 1 := fun n => by rw [map_pow]; exact pow_le_one₀ zero_le hvz
  have he1' : X.v (embX io X τ e - 1) < 1 := by
    have : X.v (embX io X τ (e - 1)) < 1 := he1
    rwa [map_sub, map_one] at this
  have hτb : X.v (embX io X τ (e * a₀) - z) < 1 := by
    have hsplit : embX io X τ (e * a₀) - z =
        (embX io X τ e - 1) * embX io X τ a₀ + (embX io X τ a₀ - z) := by rw [map_mul]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ha₀
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le he1' (hv1 τ a₀)
  have hlabb : ∀ s : ZMod h, X.v (embX io X (lab s) (e * a₀) - z ^ p ^ s.val) < 1 := by
    intro s
    have hsplit : embX io X (lab s) (e * a₀) - z ^ p ^ s.val =
        (embX io X (lab s) (e * a₀) - embX io X τ (e * a₀) ^ p ^ s.val) +
          (embX io X τ (e * a₀) ^ p ^ s.val - z ^ p ^ s.val) := by ring
    rw [hsplit]
    exact Valuation.map_add_lt _ (hlab s (e * a₀))
      (v_pow_sub_pow_lt_one X.v (hv1 τ _) hvz hτb _)
  have hoth : ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → X.v (embX io X σ (e * a₀)) < 1 := by
    intro σ hσ
    have hmem : X.v (embX io X σ e) < 1 := he σ hσ
    rw [map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hmem (hv1 σ a₀)
  have hs : ∀ s : ZMod h, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤
      vX_vp X (embX io X (lab s) (e * a₀) ^ p ^ N - (z ^ p ^ s.val) ^ p ^ N) := by
    intro s
    exact GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ _ ((isIntV_iff X _).2 (hv1 _ _))
      ((isIntV_iff X _).2 (hvzs _)) ((vX_vp_pos_iff X _).2 (hlabb s)) r
  have hσ : ∀ σ : E →+* ℂ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → primeBelow io X σ ≠ primeBelow io X τ →
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ (e * a₀) ^ p ^ N) := by
    intro σ
    by_cases hne : primeBelow io X σ = primeBelow io X τ
    · exact ⟨0, fun _ _ h' => absurd hne h'⟩
    · have hlt : X.v (embX io X σ (e * a₀) - 0) < 1 := by rw [sub_zero]; exact hoth σ hne
      obtain ⟨N₀, hN₀⟩ := GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ 0 ((isIntV_iff X _).2 (hv1 _ _))
        ((isIntV_iff X _).2 (by simp)) ((vX_vp_pos_iff X _).2 hlt) r
      refine ⟨N₀, fun N hN _ => ?_⟩
      have := hN₀ N hN
      rwa [zero_pow (pow_ne_zero _ hp.ne_zero), sub_zero] at this
  choose Ns hNs using hs
  choose Nσ hNσ using hσ
  set M := (∑ s, Ns s) + ∑ σ, Nσ σ with hM
  have hMN : M ≤ h * M := Nat.le_mul_of_pos_left M hh
  refine ⟨(e * a₀) ^ p ^ (h * M), fun s => ?_, fun σ hne => ?_⟩
  · have hzN : (z ^ p ^ s.val) ^ p ^ (h * M) = z ^ p ^ s.val := by
      rw [← pow_mul, mul_comm, pow_mul, pow_pow_mul_eq_self_of_pow_sub_one_eq_one p hp.pos hz M]
    have hle : Ns s ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
        (Nat.le_add_right _ _)) hMN
    have := hNs s (h * M) hle
    rwa [hzN, ← map_pow] at this
  · have hle : Nσ σ ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ))
        (Nat.le_add_left _ _)) hMN
    have := hNσ σ (h * M) hle hne
    rwa [← map_pow] at this

end GlobalTheory.PrimePart
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {D : D7} {a a' : ℕ}

def coBar (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) :=
  -((1 : GL (Fin a') (Fv D.host.F Bs.v₁)).1ᵀ * Γ.V'.J.map Bs.τ₁ * u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) *
    (Γ.W.J.map Bs.τ₁)ᵀ * (1 : GL (Fin (a + a')) (Fv D.host.F Bs.v₁)).1)

theorem coBar_add (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u u' : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) :
    coBar Bs Γ (u + u') = coBar Bs Γ u + coBar Bs Γ u' := by
  unfold coBar
  rw [Matrix.map_add _ (map_add _)]
  simp only [Matrix.mul_add, Matrix.add_mul, neg_add]

theorem coBar_zero (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') : coBar Bs Γ 0 = 0 := by
  unfold coBar
  rw [Matrix.map_zero _ (map_zero _)]
  simp

def Sa (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) :
    AddSubgroup (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) where
  carrier := {Y | ∃ u ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, u.map (piW Bs.τ₁) = 0 ∧ coBar Bs Γ u = Y}
  zero_mem' := ⟨0, zero_mem _, Matrix.map_zero _ (map_zero _), coBar_zero Bs Γ⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, hu0, rfl⟩ ⟨u', hu', hu0', rfl⟩
    exact ⟨u + u', add_mem hu hu', by rw [Matrix.map_add _ (map_add _), hu0, hu0', add_zero], coBar_add Bs Γ u u'⟩
  neg_mem' := by
    rintro _ ⟨u, hu, hu0, rfl⟩
    refine ⟨-u, neg_mem hu, by rw [Matrix.map_neg _ (map_neg _), hu0, neg_zero], ?_⟩
    have := coBar_add Bs Γ u (-u)
    rw [add_neg_cancel, coBar_zero] at this
    show coBar Bs Γ (-u) = -coBar Bs Γ u
    exact (neg_eq_of_add_eq_zero_right this.symm).symm

def Bd (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E))
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) :=
  {Y | ∀ x : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E), At (evFin D.host.F Bs.v₁) x →
    x.map (piW Bs.τ₁) = 0 → coBar Bs Γ x = Y → ∀ u ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x u) = 1}

end GlobalTheory.VacShape

end
end
