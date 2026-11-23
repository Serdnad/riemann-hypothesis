module

public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLog
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardOrbitSeriesValuationBoundZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle161
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle162
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

section

open NumberField HeckeCharacterZeroLocus.ThmBIn GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.UnitaryHeckeBaseChange

namespace GlobalTheory.IdeleMapInjective

theorem adeleMap_injective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Function.Injective (adeleMap F E) := by
  intro a b hab
  rw [← toAdele_algebraMap, ← toAdele_algebraMap] at hab
  exact Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
    (algebraMap F E).injective ((bijective_toAdele h).1 hab)

theorem ideleMap_injective (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E) := by
  have h : IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  intro a b hab
  exact Units.ext (adeleMap_injective h (congrArg Units.val hab))

end GlobalTheory.IdeleMapInjective
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_dpst_unramified_le_dim_representation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
  first | exact @GlobalTheory.PstRank.rank_DpstUr_le | exact GlobalTheory.PstRank.rank_DpstUr_le | (intros; apply GlobalTheory.PstRank.rank_DpstUr_le <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isUnit_of_stable_line' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l),
  (∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) → GlobalTheory.RegularRing.LineUnit (P.PD K) →
  ∀ b : Bst P, b ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b := by
  first | exact @GlobalTheory.Pst.StLine.isUnit_of_stable_line | exact GlobalTheory.Pst.StLine.isUnit_of_stable_line | (intros; apply GlobalTheory.Pst.StLine.isUnit_of_stable_line <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem lowCount_eq_smallHodgeTateJumpCountOverLetter {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} (W : Wach P K LL)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : Lat K LL) (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (η : ℕ) :
    TruncatedSeriesCountingBounds.lowCount W T a η = lowCount W T a η := by
  unfold TruncatedSeriesCountingBounds.lowCount lowCount
  congr 1

theorem recS_wordBase_natural : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∃ (ε : ℤˣ) (g : ZMod (RecS.nLet i w hw) → D.R.GG), IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ RecS.WordBase L HW i r ρ π w hw Cx hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i r ρ π w hw Cx hG hR h7 hF hJ hP h2 hq hd
  obtain ⟨ε, κ, hin⟩ := GlobalTheory.T.hodgeTateJumps_coefExt_of_roomy_adm7 L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  obtain ⟨g, hg, hwb⟩ := GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit L C₀ HW i w hw C hG r ρ π ε κ hR h7 h2 hq hd hin
  refine ⟨ε, g, hg, ?_⟩
  have hsm := GlobalTheory.HTW.Rec.recWord_small_pos L C₀ (liftIdx D i) ε g _ hR hg
  obtain ⟨hdeg, hloc, hnum⟩ := hwb
  refine
    { unram := hloc.unram
      deg := hdeg
      split := hloc.split
      t1 := fun T h => ?_
      t2 := fun T h => ?_
      t2win := fun T h => ?_
      num := hnum
      small := hsm }
  · obtain ⟨h1, h2, h3⟩ := hloc.t1 T h
    exact ⟨h1, h2, h3⟩
  · obtain ⟨⟨h1, _, _⟩, h4⟩ := hloc.t2 T h
    refine ⟨h1, fun ft a => ?_⟩
    rw [lowCount_eq_smallHodgeTateJumpCountOverLetter]
    exact h4 ft a
  · obtain ⟨⟨_, h2, h3⟩, _⟩ := hloc.t2 T h
    exact ⟨h2, h3⟩

end GlobalTheory.HTW.Rec
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.subst_unitary_logarithmic_coordinates : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  first | exact @GlobalTheory.KerStd.HostLog.subst_unitary | exact GlobalTheory.KerStd.HostLog.subst_unitary | (intros; apply GlobalTheory.KerStd.HostLog.subst_unitary <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → OrbitPlaces.OrbOK D p → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p (nP D p) σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' r : ℕ) (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p), HypPair σ f f' → ∀ (Θ : MvPowerSeries (Fin r) ℂ_[p]), HostLog p g2 g3 s2 ε Θ → ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') Θ → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) Th := by
  first | exact @GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | exact GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | (intros; apply GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.standardOrbitSeries_valuationBound_zero : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th 0 := by
  first | exact @GlobalTheory.KerZero.kvalGe_zero | exact GlobalTheory.KerZero.kvalGe_zero | (intros; apply GlobalTheory.KerZero.kvalGe_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodProjector_unitaryFormsModel_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i, eH R i * eH R i = eH R i ∧ (∀ g, Commute (eH R i) (R.gW i (sg0 D A) g)) ∧ (∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv) ∧ ∀ t y, eH R i (R.thG i t y) = R.thG i t y := by
  first | exact @GlobalTheory.Hk3.eH_laws | exact GlobalTheory.Hk3.eH_laws | (intros; apply GlobalTheory.Hk3.eH_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) ΛS ΛT (NS NT : ℕ), IsBaseFrame S βS ΛS NS → IsBaseFrame T βT ΛT NT → ∀ P : Pl D.host.E, ((NS * NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ f₀, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ → IsVacAt ψ S T P f₀ := by
  first | exact @GlobalTheory.VacLat.isVacAt_of_isLatVac | exact GlobalTheory.VacLat.isVacAt_of_isLatVac | (intros; apply GlobalTheory.VacLat.isVacAt_of_isLatVac <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents : ∀ (n : ℕ) (d : List ℤ), (d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d) ↔ ∃ s : List ℕ, 2 * s.length ≤ n ∧ s.Pairwise (fun a b => b ≤ a) ∧ (∀ a ∈ s, 0 < a) ∧ d = labIn n s := by
  first | exact @GlobalTheory.Hk3.labIn_selfDual_iff | exact GlobalTheory.Hk3.labIn_selfDual_iff | (intros; apply GlobalTheory.Hk3.labIn_selfDual_iff <;> assumption)
end

section


theorem _root_.GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω →
    GlobalTheory.Hk3.LocPair ϖ σ q (-δ) JT JS ψ
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)))
      (ω.comp (MulEquiv.prodComm : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) × Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) ≃* _).toMonoidHom) ∧
    (∀ s : M, GlobalTheory.Hk3.LocVac ρ s → GlobalTheory.Hk3.LocVac
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L))) s) ∧
    ∀ s : M, Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n') L =>
      ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)) s) = ⊤ := by
  first | exact @GlobalTheory.Hk3.HoweSwap.locPair_swap | exact GlobalTheory.Hk3.HoweSwap.locPair_swap | (intros; apply GlobalTheory.Hk3.HoweSwap.locPair_swap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem locVac_rel_map : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ φ : M →ₗ[ℂ] M, (∀ s, LocVac ρ s → LocVac ρ (φ s)) → ∀ f : Matrix (Fin n') (Fin n) L →₀ M, (∀ x, LocVac ρ (f x)) → (f.sum fun x m => ρ x m) = 0 → (f.sum fun x m => ρ x (φ m)) = 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP φ hφ f hf hsum
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]

  have hinj : ∀ x t, ρ x t = 0 → t = 0 := by
    intro x t h0
    have := congrArg (fun f => f t) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact (smul_eq_zero.mp this.symm).resolve_left hne

  set Λ := intMatSub (L := L) n n' with hΛ
  have hmem : ∀ x : Matrix (Fin n') (Fin n) L, -(QuotientAddGroup.mk x : _ ⧸ Λ).out + x ∈ Λ := by
    intro x
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
  set κ : Matrix (Fin n') (Fin n) L → ℂ := fun x =>
    ψ (-((locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x) +
      σ (locH σ δ JS JT (QuotientAddGroup.mk x : _ ⧸ Λ).out (-(QuotientAddGroup.mk x : _ ⧸ Λ).out + x))) / 2)) with hκ
  have hdec1 : ∀ t, LocVac ρ t → ∀ x, ρ x t = κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out t := by
    intro t ht x
    have := hshift t ht (QuotientAddGroup.mk x : _ ⧸ Λ).out _ (hmem x)
    rwa [add_neg_cancel_left] at this
  set I : Finset (Matrix (Fin n') (Fin n) L ⧸ Λ) := f.support.image (fun x => (QuotientAddGroup.mk x : _ ⧸ Λ)) with hI

  let cl : (Matrix (Fin n') (Fin n) L → M) → (Matrix (Fin n') (Fin n) L ⧸ Λ) → M := fun g y =>
    ∑ x ∈ f.support with (QuotientAddGroup.mk x : _ ⧸ Λ) = y, κ x • g x
  have hdec : ∀ g : Matrix (Fin n') (Fin n) L → M, (∀ x, LocVac ρ (g x)) →
      ∑ x ∈ f.support, ρ x (g x) = ∑ y ∈ I, ρ y.out (cl g y) := by
    intro g hg
    have e1 : ∑ x ∈ f.support, ρ x (g x) =
        ∑ x ∈ f.support, κ x • ρ (QuotientAddGroup.mk x : _ ⧸ Λ).out (g x) :=
      Finset.sum_congr rfl fun x _ => hdec1 _ (hg x) x
    rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := f.support) (t := I) (g := fun x => (QuotientAddGroup.mk x : _ ⧸ Λ))
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    refine Finset.sum_congr rfl fun y _ => ?_

    simp only [cl, map_sum, map_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
  have hclvac : ∀ y, LocVac ρ (cl f y) := by
    intro y u hu

    simp only [cl, map_sum, map_smul]
    exact Finset.sum_congr rfl fun x _ => by rw [hf x u hu]

  have hcl0 : ∀ y ∈ I, cl f y = 0 := by
    intro y hy
    have hsum' : ∑ y ∈ I, ρ y.out (cl f y) = 0 := by
      rw [← hdec f hf]; exact hsum
    have hind := GlobalTheory.joint_eigenvectors_eq_zero_of_sum_eq_zero Λ (Matrix (Fin n') (Fin n) L ⧸ Λ) M
      (fun u : Λ => ρ (u : Matrix (Fin n') (Fin n) L))
      (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : Λ) =>
        ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
      (fun y => ρ y.out (cl f y)) I (fun y _ u => heig _ (hclvac y) y.out u u.2)
      (by
        intro y _ y' _ hyy
        have hm := hdist y.out y'.out (fun u hu => congrFun hyy ⟨u, hu⟩)
        rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
        exact hm)
      hsum' y hy
    exact hinj _ _ hind
  have hφcl : ∀ y, cl (fun x => φ (f x)) y = φ (cl f y) := by
    intro y

    simp only [cl, map_sum, map_smul]
  show ∑ x ∈ f.support, ρ x (φ (f x)) = 0
  rw [hdec (fun x => φ (f x)) (fun x => hφ _ (hf x))]
  exact Finset.sum_eq_zero fun y hy => by rw [hφcl, hcl0 y hy, map_zero, map_zero]

end GlobalTheory.Hk3
end
