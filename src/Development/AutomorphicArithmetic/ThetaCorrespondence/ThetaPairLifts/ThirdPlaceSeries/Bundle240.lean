module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle025
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle417
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle694
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle010
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShareStatementOfKnownTheorems
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HermitianPairingBilinearOnPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle087
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle176
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle231
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle151
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle088
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle654
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl

@[expose] public section

section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.WeilDeligne GlobalTheory.SerSys.LabDepth in
theorem labLP_isLabel_and_actK_fix : Green → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (L : ∀ k, LabelDatum (D.host.g k)), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.SerSys.LabTie D L → DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc → ∀ k v (π : QRep (D.host.g k) D.R.r), IrrSm π → fixK1 π.ρ ≠ ⊥ → IsLabel D k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π)) ∧ ∀ y ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π))) y = y := by
  intro hG hL D T I rc L hRc hLT hLab hP k v π hπ hfix
  let S : Sys (D.host.g k) := OfLabel.ofLabel (L k) (Bridge.five_le D k) hG
  have hSe : ∀ n f, S.e n f = eSerC (L k) n f := fun _ _ => rfl
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
  obtain ⟨f, hf⟩ : ∃ f, actK π.ρ (S.e D.R.r f) y ≠ 0 := by
    obtain ⟨T', hT'⟩ := S.sum D.R.r
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [← LabLoc.actK_one_of_mem π.ρ hy, ← hT', LabLoc.actK_finset_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun f _ => hcon f
  have hne : S.e D.R.r f ≠ 0 := fun e => hf (by rw [e]; simp [actK])
  obtain ⟨hm, hd, h0⟩ := S.label _ f hne
  have hine : D.naut.inePol (rc k v D.R.r π) (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    rw [← (hLab k).1]
    exact hP k v D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f ⟨y, hy, hf⟩
  have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have htame : (T.e _ (rc k v D.R.r π)).tame := by
    obtain ⟨σ, hiso, hσ⟩ := exists_pull D I k v π hπ hfix
    rw [hRc k v D.R.r σ π hiso]
    first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, hl⟩ := hOpn) | obtain ⟨a, ha, ε, -, hl⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
    refine tame_of_isTameWD ((fun hx => haveI := UpperTheory.One.M.charZero_compl (D.naut.plGw k v); _root_.UpperTheory.One.M.LawsM.depth hl _ (UpperTheory.One.M.good_of_fixed ⟨_, ⟨D.host.g_prime k⟩, I.i k v, I.cont k v⟩ _ hx) hx : _ → _) ?_)
    exact GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm hσ
  have hlab : D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π) = f := by
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hLT k v, WD.lab_eq_iff_of_tame hSet htame, ← T.inePol _ _ _ (D.ntypes.tg_gen k v).1, hine, e1,
      roots_multiset_prod_X_sub_C]
    exact ⟨hm, rfl⟩
  refine ⟨hlab ▸ ⟨hm, hd, h0⟩, fun z hz => ?_⟩
  rw [hlab, (hLab k).2 f, ← hSe]
  refine DiscreteGroups.sglob.DzType.Rt.actK_e_eq_self_le _ S (L k).teich (fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) D.R.nV ?_
    (hP k v) D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) π hπ f hm h0 ?_ z hz
  · rw [(hLab k).1]
    exact fun x hx y hy e => D.ntypes.teichC_inj k x y hx hy e
  · rw [(hLab k).1]; exact hine
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end

section



section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem share_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative →
    _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition := by
  intro hX hP hSI hKS hG hQ hSL hDG hS hF hD
  have h1 := hS
  have h2 := hF
  have h3 := hD
  have h4 := _root_.GlobalTheory.T.size_bounds_for_family_alt hS
  have h5 := _root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt hP hG hQ hSI hKS hSL hDG hS hF
  have h6 := _root_.GlobalTheory.T.birOn_weightPair_both_components_alt hX hG hQ hSI hP hS
  unfold _root_.GlobalTheory.CovTop.SizeCondition at h1
  unfold _root_.GlobalTheory.CovTop.FlatDegreeCondition _root_.GlobalTheory.CovTop.CoversCondition at h2
  unfold _root_.GlobalTheory.CovTop.CoverDegree _root_.GlobalTheory.CovTop.CoversCondition at h3
  unfold _root_.GlobalTheory.CovTop.CoversCondition at h4 h5 h6
  have all := _root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h1 h2) (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h3 _root_.GlobalTheory.HSApp.wtBig_run_alt))
    (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS) h4)) (_root_.GlobalTheory.CovTop.ShareRowsNef.lifts_and_alt h5 h6)
  clear h1 h2 h3 h4 h5 h6
  refine Closed.imp all fun Fm _ _ ⟨C, hC, x0, h⟩ => ⟨C, hC, x0, fun x hx hle ι p hp i hi Y hY u1 hu Z => ?_⟩
  obtain ⟨⟨_, ⟨_, ⟨_, ⟨_, hs⟩, _, hfl⟩, _, ⟨_, hdg⟩, _, hB⟩, _, ⟨_, hq⟩, _, hz⟩, _, ⟨_, hv⟩, _, hbi⟩ := h x hx hle ι p hp i
  obtain ⟨hp1, hq1, hf, hqu, hsa, ⟨w, -, hw⟩, hdom⟩ := hq hi
  obtain ⟨hT, hj, -⟩ := hz hi Y hY
  obtain ⟨-, h0, -, hz1⟩ := (hs.2.2.2.2.2.2 hi).2 u1 hu
  obtain ⟨δ, hδ, hδ2⟩ := hdg hi Y hY u1 hu
  obtain rfl := hqu u1 hu
  have htw := (_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hT _ hp1 hq1 hf hj Y _ _ hY.1 _ (hfl hi Y hY)).1
  refine ⟨?_, ?_⟩
  · rw [hw, htw]
    exact _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_lower_bound hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) Z (hbi hi Y hY Z).1
  · have hD2 : (2 : ℝ) ≤ CompHt.dimFlag (dat p i) := by
      rw [GlobalTheory.CompHS.dimFlag_eq]; exact_mod_cast two_le_dimFlag hp1 hq1 hf
    refine _root_.GlobalTheory.CovTop.ShareRowsNef.nef_share_upper_bound hX hP hSI hKS hG hQ hSL hT hp1 hq1 hf hj Y hY.1 _ (hB hi) hsa (fun Z => (hbi hi Y hY Z).1) (hv hi Y hY) h0 ?_ (uM p i) (fun τ => ?_) (fun τ => ?_) Z
      (hδ.trans_le (hδ2 Z).1)
    · unfold zed at hz1
      have : 0 ≤ (CompHt.dimFlag (dat p i) : ℝ) ^ 2 / lenT p i (Fm.parT x hx ι).PP := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hD2 h0]
    · simpa using (hdom 0 (by norm_num) τ).1
    · simpa using (hdom 0 (by norm_num) τ).2
end GlobalTheory.CovTop.ShareRowsNef
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.share_of_deep_good_size_flat_deg_cover_degree : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition := by
  first | exact @_root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt | exact _root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.ShareRowsNef.share_alt_alt <;> assumption)
end
end
end
