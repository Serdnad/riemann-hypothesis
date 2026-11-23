module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle713
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle018
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem jointCondH0all_canon_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → AdmissibleParameterJ.JumpConditions L → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, ∃ M0 h0 : ℕ, GlobalTheory.HubX.DecompositionInvariantsCondition D HW i (X.ρ i) π (X.dc i) (X.c0 i) M0 h0 := by
  intro hF D L HW R X hC hJ h41 hAdm i hTw hg hRA hS π hπ
  obtain ⟨⟨ep, hep⟩, hJb, hJc, hJd, hJe, hJf, hJg⟩ := hJ
  have hls : D.nd.l i ∉ D.host.small := fun h => hRA.1 (Or.inl h)
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hls
  have hlq : D.nd.l i ≠ D.host.q := fun h => hRA.2.1 (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hRA.2.1 (Or.inr h)
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hπZ : π ∈ D.nd.Z i := LargeLevelLemmas.zgoodSubsetZ i hπ
  obtain ⟨-, -, -, hdec⟩ := GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hC.fam i π hπZ
  have hgood := hC.fam.good i
  have hcont := hC.fam.cont i π
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have hrV : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  refine ⟨hOf L, hOf L, hl2, ?_⟩
  intro u _ w hw _
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i hls hlq hld w hw
  refine ⟨GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hur, ?_⟩
  intro C hs hc L2
  have hcrys := (_root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π h41 (hAdm i) hgood hcont hdec hg0 hg1 w hw C).2.2.2
  have hjump := fun τ => GlobalTheory.T.decomposition_local_above D L ep hep hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgood hπZ hdec w hw C τ
    (T2O D.nd i (X.ρ i) π) (Or.inr rfl)
  have key := GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified D.loc HW D.locA (D.nd.l i) (D.nbr i w hw).Kw C.LL hs (hOf L) D.R.r (4 * D.R.n)
    (tTwoLocalLattice D i (X.ρ i) π C hc L2) hur (GlobalTheory.bridge_finrank_le D i w hw) hr1 (fun τ => (hjump τ).1)
  refine ⟨hcrys, key.1, fun τ => (hjump τ).2, ?_⟩
  rw [hC.c0]
  refine key.2.trans ?_
  unfold c0of
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrV)) _
end GlobalTheory.HubX
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem jointCond_H0Wall_of_canon_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → ∀ F : FonOf D.loc D.locA HW, AdmissibleParameterJ.JumpConditions L → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ M0 h0 : ℕ, GlobalTheory.HubX.JointCond_H0Wall D HW F X M0 h0 := by
  intro _ D L HW R X hX F hJ h41 hFont
  obtain ⟨⟨ep, hJa⟩, hJb, hJc, -, hJe, hJf, -⟩ := hJ
  refine ⟨hOf L, hOf L, ?_⟩
  intro i _ _ hsplit u hu π hπ
  have hnI : ¬ TwistedPlaces.InertK D (D.nd.l i) := by
    intro h2
    unfold TwistedPlaces.SplitK at hsplit
    unfold TwistedPlaces.InertK at h2
    rw [hsplit] at h2
    rcases h2 with h2 | h2 <;> cases h2
  rw [hX.dc i hnI] at hu
  unfold dcOf at hu
  split_ifs at hu with hS
  swap
  · simp [KillingConditions.allRows] at hu
  obtain ⟨_, h5, hq, hd, hg, _⟩ := hS.1
  have hu' : u ∈ placesOver D.host.E (D.nd.l i) := ((Exists.choose hS.2).cover u).1 (Or.inr hu)
  have hl2 : D.nd.l i ≠ 2 := by omega
  have hsm : D.nd.l i ∉ D.host.small := fun h => by
    have h' : primeClass D.host.toHostRaw (D.nd.l i) = PrimeClass.splitK := hsplit
    simp [primeClass, h] at h'
  have hKur := GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i hsm hq hd u hu'
  have hgood : Good (D.nbr i u hu').Kw 1 (D.nbr i u hu').LL :=
    (D.self_good i u hu').good_one (D.nbr i u hu').LL_split hl2 (GlobalTheory.HubLoc.le_Ks_one_of_Kur _ hKur)
  have hZ : π ∈ D.nd.Z i := Formalism.MainNotions.LargeLevelLemmas.zgoodSubsetZ i hπ
  have hfam := hX.fam
  have hdec := (GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies D X.r X.ρ hfam i π hZ).2.2.2
  have hgr := hfam.good i
  have hcont := hfam.cont i π
  have hWc : Continuous (WpO D.nd i (X.ρ i) π) := by
    have h1 : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
      refine ((D.nd.chi_cont i 1).comp continuous_inv).congr fun g => ?_
      simp only [Function.comp_apply]
      rw [MonoidHom.inv_apply, ← map_inv]
    exact h1.smul hcont
  have hLc := GlobalTheory.WordJumpsCompare.continuous_loc D i u hu' _ hWc
  have hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu') ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v :=
    fun v => hLc.matrix_mulVec continuous_const
  have hJW := fun τ => GlobalTheory.T.decomposition_local_above D L ep hJa hJb hJc hJe hJf i (X.r i) (X.ρ i) π hgr hZ hdec u hu'
    (TruncatedSeriesCountingIdentities.CoefExt.self i u hu') τ (WpO D.nd i (X.ρ i) π) (Or.inl rfl)
  have hrn : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hnV : 1 ≤ D.R.nV := le_trans D.R.t_odd.pos (Nat.le_add_left _ _)
  have hH := GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified D.loc HW D.locA (D.nd.l i) (D.nbr i u hu').Kw (D.nbr i u hu').LL hgood (hOf L) D.R.nV
    (4 * D.R.n) (wLat D i (X.ρ i) π u hu' hc) hKur (GlobalTheory.bridge_finrank_le D i u hu') hnV
    (fun τ => by
      obtain ⟨U, hU1, hU2, hU3⟩ := (hJW τ).1
      exact ⟨U, hU1.trans hrn, hU2, hU3⟩)
  refine ⟨hu', 1, hgood, hc, ?_, hH.1, fun τ => (hJW τ).2, ?_⟩
  · exact (_root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π h41 (hFont i) hgr hcont hdec (hg 0) (hg 1) u hu'
      (TruncatedSeriesCountingIdentities.CoefExt.self i u hu')).2.2.1
  · rw [hX.c0]
    exact hH.2
end GlobalTheory.HubX
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.isCrys_locC_of_chiOneE : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → _root_.UpperTheory.GalS.G2a D.nd D.naut i r → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → GlobalTheory.PtCore.ChiOneE D i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) := by
  first | exact @_root_.GlobalTheory.DualTwistCrys.main_alt_alt | exact _root_.GlobalTheory.DualTwistCrys.main_alt_alt | (intros; apply _root_.GlobalTheory.DualTwistCrys.main_alt_alt <;> assumption)
end
end

section



section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.DefiniteBC
namespace GlobalTheory.FormDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
def recT_alt {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : RecMap A :=
  fun w _ σ => (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (N.plOm.2 w) (GlobalTheory.LocLanglands.cls (ParLaws.toRep σ)))
end GlobalTheory.FormDict
end
end
end

section



section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.recTExists_of_published_inputs : _root_.UpperTheory.Zero.LLC.RecTExists → LocalConverseGL → DepthZeroInduction → BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → _root_.UpperTheory.Zero.LLC.RecTExists := by
  first | exact @_root_.UpperTheory.One.M.New.llOf_alt | exact _root_.UpperTheory.One.M.New.llOf_alt | (intros; apply _root_.UpperTheory.One.M.New.llOf_alt <;> assumption)
end
end

section



section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
variable {T : WDTie N A} (S : Reading T)
def LawsAlt : Prop :=
  ∀ (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), _root_.UpperTheory.One.M.RecLawsH (S i w hw).rc
end GlobalTheory.SplitRead
end
end
end

section



section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem narrowBig_alt (s : _root_.UpperTheory.One.M.TrivialCondition) (_art : GlobalTheory.Published.GlobalArtinReciprocity) (_hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.DiscreteGroups.sglob.DzType.NarrowBigAlt :=
  fun _ E' _ _ _ _ _ _ _ _ _ _ _ _ _ g _ _ _ _ w' h' _ H i hi n hn _ h1 h2 a' ha' K _ _ red h3 h4 θ hθ τ hτ h5 σ h6 =>
    (_root_.UpperTheory.One.M.New.typeS s H E' g w' h' i hi n hn h1 h2 a' ha' K red h3 h4 θ hθ τ hτ h5 σ h6).2
end UpperTheory.One.M
end
end
end
