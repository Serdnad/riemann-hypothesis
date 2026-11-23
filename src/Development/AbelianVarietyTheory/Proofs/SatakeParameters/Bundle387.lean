module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle384
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle378
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle383
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle368
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle358
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle381
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle377
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle369
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle007
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TieStabKaAtAny
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle386
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle385
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_joints_hold_all_tuples : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∀ a : I.ι, GlobalTheory.TwV.JointsAt t a) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.TwU.AllTuples.joints_all_true | exact GlobalTheory.TwU.AllTuples.joints_all_true | (intros; apply GlobalTheory.TwU.AllTuples.joints_all_true <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV



private theorem admissible_at_each_site : Lt.AdmAtEnt2 → AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => DV.Used D μ → OrbitPlaces.Stab0 D → admitted D (sysS H X std) S.Y) := by
  intro hA D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hU hS0
  have hDict := GlobalTheory.T.latticeTuple_joint_dictionary t std J
  have hPair := GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hDict
  have hPos := GlobalTheory.T.site_place_induces_position_embeddings S
  have hMove := GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames S hDict
  have hAway := GlobalTheory.T.kernelSite_series_independent_away_from_place_over_p S hDict
  have hScal := GlobalTheory.T.kernelSite_seriesScalar_pow_integral S hDict
  have hK1 := GlobalTheory.T.allSites_k1_of_dict_pair_pos_scal S hDict hPair hPos hScal
  obtain ⟨hLaw, hLawIn, hXi⟩ := GlobalTheory.T.kernelSite_law_and_fixedCoordinateStabiliserLaw S hPair hPos hMove hAway
  obtain ⟨ι, hι⟩ := GlobalTheory.ThLoc.place_extends_to_iso _ S.lam
  haveI := Lt.fracAt Gl u w hg
  have key := hA D L hT Gi Gl Kc Dx cX ex t u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (kaAt X H hT) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg))
    (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT))
    (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le)
    S.E S.hfin S.hst S.g S.hLT
    (hT.gat_pos u w hg) ex.tw I (Formalism.L2.PairingIndexBounds.F.lev0At J.Gd u w hg) J.a ∅ t.cc t.δ t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
  have k2 := key S.curve hK1 hXi hLawIn
  refine k2 ⟨ι.toRingHom, Formalism.L2.KerInert.SecondKernelProjection.rdJ I X.onCh ι.toRingHom, Formalism.L2.KerInert.SecondKernelSeries.srOf S.Y, fun j hj => ⟨J.sharp j hj, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := tieStab_kaAtAny X H hT (chainAt H hT) (chainMu_cmp_K _) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y hU hS0 j hj.le
    rw [kaAtAny_cls] at h1
    rw [kaAt_cls]
    exact h1
  · refine Formalism.L2.KerInert.SecondKernelProjection.series_reading_entries D L hT Gi Gl Kc Dx cX ex u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds hT (chainMu_cmp_K _) X.onCh std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y ι.toRingHom ?_ j
    intro r
    have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
      rw [mem_algebraicClosure_iff]
      exact (Algebra.IsAlgebraic.isAlgebraic r).algHom D.what₂.embLL.toRatAlgHom
    show ι (D.what₂.embLL r) = S.E.iK (ex.cmp.embW u w hg r)
    rw [S.hK r hz, ← hι]
  · exact Formalism.L2.KerInert.SecondKernelSeries.series_compatibility_of (D.what₂.places.resChar w) _ S.Y j
  · have hD : S.Del j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        exact GlobalTheory.T.kernelSite_frameValues_step_zero S hDict hPair hPos hLaw
      · exact GlobalTheory.T.kernelSite_frameValues_positive_steps S hDict hPair hPos hLaw j hpos hj
    obtain ⟨cK, hn, hd⟩ := hD ι.toRingHom (fun z => hι z)
    refine ⟨cK, ?_, ?_, ?_, hd⟩
    · show ‖cK‖ ≤ 1
      rw [hn]
    · show ‖cK⁻¹‖ ≤ 1
      rw [norm_inv, hn, inv_one]
    · intro h
      rw [h, norm_zero] at hn
      exact zero_ne_one hn

theorem site_cmpLite_siteAdm : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}, Joint t H X → DV.Used D μ → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg (chainAt H hT) ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) Lv (chainAt H hT) := by
  intro hAdm hCur D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X J hU hS hk
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  refine ⟨⟨(kaAt X H hT).cmp, (kaAt X H hT).cmp_zero, (kaAt X H hT).cmp_K, (kaAt X H hT).rat, (kaAt X H hT).val⟩, ?_⟩
  have std : Lt.StdAtW D Gl u w hg := GlobalTheory.TwU.std_at_served D u w hg L hT Gi Gl J.tied hk
  obtain ⟨S⟩ := GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty hCur t std J
  have hA : admitted D (sysS H X std) S.Y := admissible_at_each_site hAdm S hU hS
  refine ⟨inferInstance, std, vpOf (D.gat u w hg), vpOf_irreducible (D.gat u w hg),
    eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    Lt.dGT D u (D.what₂.places.resChar w), Lt.dGT_spec (kaAt X H hT), _, S.Y, hA, Lt.dGT_zero _ _ _, fun j => ?_⟩
  unfold Lt.dGT
  split_ifs <;> simp

end GlobalTheory.TwV

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))) := by
  first | exact @GlobalTheory.SplitLocPlace.exists_place | exact GlobalTheory.SplitLocPlace.exists_place | (intros; apply GlobalTheory.SplitLocPlace.exists_place <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  first | exact @GlobalTheory.PlaceSupp.comp_idem | exact GlobalTheory.PlaceSupp.comp_idem | (intros; apply GlobalTheory.PlaceSupp.comp_idem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  first | exact @GlobalTheory.PlaceSupp.idem_mul_eq_self | exact GlobalTheory.PlaceSupp.idem_mul_eq_self | (intros; apply GlobalTheory.PlaceSupp.idem_mul_eq_self <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integralSection_splitPlace_componentMap : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  first | exact @GlobalTheory.SplitComp.proj_tensCast_section | exact GlobalTheory.SplitComp.proj_tensCast_section | (intros; apply GlobalTheory.SplitComp.proj_tensCast_section <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_principalCongruence_in_definiteLevel : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  first | exact @GlobalTheory.VFormCong.exists_cong_levEnv | exact GlobalTheory.VFormCong.exists_cong_levEnv | (intros; apply GlobalTheory.VFormCong.exists_cong_levEnv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.definiteLevel_preimage_finitely_many_cosets : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ F : Finset (GAf D.host.E D.R.nV), ∀ κ, (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J → ∃ f ∈ F, f⁻¹ * κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := by
  first | exact @GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets | exact GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets | (intros; apply GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.LabelTransport


open Classical in
theorem coset_transport {G H : Type} [Group G] [Group H] (ψ : G →* H) (T U J : Subgroup G) (K : Set H) (α : H)
    (R : Finset H) (hK : ∀ x, ψ x ∈ K ↔ x ∈ U ∧ x ∈ T) (hKr : ∀ k ∈ K, ∃ x, ψ x = k)
    (hJ : ∀ x ∈ T, x ∈ J ↔ x ∈ U) (pre : H → G) (hpre : ∀ γ ∈ R, ψ (pre γ) = γ ∧ pre γ ∈ T)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : H, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    ∃ Ds : Set G, (∀ x ∈ Ds, x ∈ T) ∧ (∀ x ∈ Ds, ∀ κ ∈ U, κ ∈ T → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧
      {c : G ⧸ J | ∃ x ∈ Ds, (x : G ⧸ J) = c}.Finite ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), (∀ x, ∀ κ ∈ J, κ ∈ T → F (x * κ) = F x) → ∀ g,
        (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ Ds, (x : G ⧸ J) = c then F (g * hc.choose) else 0) = ∑ γ ∈ R, F (g * pre γ) := by
  have hmul : ∀ a ∈ K, ∀ b ∈ K, a * b ∈ K := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := hKr a ha
    obtain ⟨y, rfl⟩ := hKr b hb
    rw [← map_mul, hK]
    exact ⟨mul_mem ((hK x).1 ha).1 ((hK y).1 hb).1, mul_mem ((hK x).1 ha).2 ((hK y).1 hb).2⟩
  let Ds : Set G := {x | x ∈ T ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, ψ x = k₁ * α * k₂}
  have hpD : ∀ γ ∈ R, pre γ ∈ Ds := fun γ hγ => ⟨(hpre γ hγ).2, by rw [(hpre γ hγ).1]; exact h1 γ hγ⟩
  have hrel : ∀ γ ∈ R, ∀ x ∈ T, ((pre γ : G ⧸ J) = (x : G ⧸ J) ↔ γ⁻¹ * ψ x ∈ K) := by
    intro γ hγ x hx
    have ht : (pre γ)⁻¹ * x ∈ T := mul_mem (inv_mem (hpre γ hγ).2) hx
    have e : ψ ((pre γ)⁻¹ * x) = γ⁻¹ * ψ x := by rw [map_mul, map_inv, (hpre γ hγ).1]
    rw [QuotientGroup.eq, hJ _ ht, ← e, hK]
    exact (and_iff_left ht).symm
  have hset : ∀ c : G ⧸ J, (∃ x ∈ Ds, (x : G ⧸ J) = c) ↔ c ∈ R.image fun γ => (pre γ : G ⧸ J) := by
    intro c
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 _ hx.2
      exact ⟨γ, hγ, (hrel γ hγ x hx.1).2 e⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨_, hpD γ hγ, rfl⟩
  refine ⟨Ds, fun x hx => hx.1, ?_, ?_, ?_⟩
  · rintro x ⟨hx, a, ha, b, hb, e⟩ κ hκ hκ'
    have hk : ψ κ ∈ K := (hK κ).2 ⟨hκ, hκ'⟩
    refine ⟨⟨mul_mem hx hκ', a, ha, _, hmul b hb _ hk, ?_⟩, ⟨mul_mem hκ' hx, _, hmul _ hk a ha, b, hb, ?_⟩⟩
    · rw [map_mul, e, mul_assoc]
    · rw [map_mul, e]; simp only [mul_assoc]
  · exact (R.image fun γ => (pre γ : G ⧸ J)).finite_toSet.subset fun c hc => (hset c).1 hc
  · intro W _ F hF g
    rw [finsum_eq_sum_of_support_subset (s := R.image fun γ => (pre γ : G ⧸ J))]
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun γ hγ => ?_
        have hc : ∃ x ∈ Ds, (x : G ⧸ J) = (pre γ : G ⧸ J) := ⟨_, hpD γ hγ, rfl⟩
        rw [dite_eq_left hc]
        have hj : hc.choose⁻¹ * pre γ ∈ J := QuotientGroup.eq.1 hc.choose_spec.2
        have ht : hc.choose⁻¹ * pre γ ∈ T := mul_mem (inv_mem hc.choose_spec.1.1) (hpre γ hγ).2
        rw [← hF (g * hc.choose) _ hj ht, mul_assoc, mul_inv_cancel_left]
      · intro a ha b hb e
        have ha' : a ∈ R := ha
        have hb' : b ∈ R := hb
        have e1 := (hrel a ha' _ (hpre b hb').2).1 e
        have e2 := (hrel b hb' _ (hpre b hb').2).1 rfl
        rw [(hpre b hb').1] at e1 e2
        exact (h2 b (h1 b hb')).unique ⟨ha', e1⟩ ⟨hb', e2⟩
    · intro c hc
      by_contra hn
      exact hc (dif_neg fun h => hn ((hset c).1 h))

theorem tensCast_under {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (P : HeightOneSpectrum (𝓞 E)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α (P.under (𝓞 F1)) = 1)
    (h0 : ∀ v', v' ≠ P.under (𝓞 F1) → α v' = 0) :
    ∃ α' : FiniteAdeleRing (𝓞 F2) F2,
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' (P.under (𝓞 F2)) = 1 ∧
        ∀ v', v' ≠ P.under (𝓞 F2) → α' v' = 0 := by
  subst h
  exact ⟨α, rfl, h1, h0⟩

theorem idem_mul_iff {L : Type} [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (α : AFplus L) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0)
    (z : AL L) : ((1 : L) ⊗ₜ[maximalRealSubfield L] α) * z = z ↔ ∀ v', v' ≠ v → compAt L v' z = 0 := by
  have hc : ∀ u, compAt L u ((1 : L) ⊗ₜ[maximalRealSubfield L] α) = (1 : L) ⊗ₜ[maximalRealSubfield L] (α u) := by
    intro u
    rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  constructor
  · intro h u hu
    rw [← h, map_mul, hc, h0 u hu, TensorProduct.tmul_zero, zero_mul]
  · intro h
    rw [← sub_eq_zero]
    apply GlobalTheory.AL_eq_zero_of_compAt
    intro u
    rw [map_sub, map_mul, hc]
    by_cases hu : u = v
    · subst hu
      rw [h1, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [h u hu, mul_zero, sub_zero]

theorem conj_supp {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (M : Matrix (Fin m) (Fin m) B)
    (hM : M = β * K * β') (h : ∀ i j, φ * (K - 1) i j = (K - 1) i j) : ∀ i j, φ * (M - 1) i j = (M - 1) i j := by
  have e : M - 1 = β * (K - 1) * β' := by
    rw [hM, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have e1 : φ • (K - 1) = K - 1 := Matrix.ext h
  have e2 : φ • (β * (K - 1) * β') = β * (K - 1) * β' := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  rw [e]
  exact fun i j => congrFun (congrFun e2 i) j

theorem conj_supp_iff {B : Type} [CommRing B] {m k : ℕ} (φ : B) (β : Matrix (Fin m) (Fin k) B)
    (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B) (h1 : β * β' = 1) (h2 : β' * β = 1)
    (M : Matrix (Fin m) (Fin m) B) (hM : M = β * K * β') :
    (∀ i j, φ * (M - 1) i j = (M - 1) i j) ↔ ∀ i j, φ * (K - 1) i j = (K - 1) i j := by
  refine ⟨conj_supp φ β' M β h2 K ?_, conj_supp φ β K β' h1 M hM⟩
  rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]


attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem suppF_iff_trivOutside (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV)
    (e f : Formalism.L2.Theta.AE D) (hef : Formalism.IndefR.Mult.IsPrimeIdem s.w e f) (κ : GAf D.host.E n) :
    Formalism.IndefR.Mult.SuppF V f (PV.ψ κ) ↔ TrivOutside {s.v} κ := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, hα1, hα0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hef
  obtain ⟨α', hT, hw1, hw0⟩ := tensCast_under hF s.w α hα1 hα0
  have hv : s.w.under (𝓞 (maximalRealSubfield D.host.E)) = s.v := HeightOneSpectrum.ext s.w_under
  rw [hv] at hw1 hw0
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  have hfin : Formalism.L2.Theta.finPart D x = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  set K := (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm with hKdef
  set M := (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.finPart D) with hMdef
  have e6 : (Formalism.L2.Theta.mt V (PV.ψ κ) - 1).map (Formalism.L2.Theta.finPart D) = M - 1 := by
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.finPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.finPart D)) (map_one (Formalism.L2.Theta.finPart D))]
  have e2 : ((Formalism.L2.Theta.mt V (PV.ψ κ)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
    have hk := MonoidHom.mem_ker.1 (PV.into κ)
    rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
      Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
    have e3 : (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ κ)).val := rfl
    rw [e3, hk, Units.val_one, sub_self]
  have s1 : Formalism.IndefR.Mult.SuppF V x (PV.ψ κ) ↔ ∀ i j, Formalism.L2.Theta.finPart D x * (M - 1) i j = (M - 1) i j := by
    rw [← e6]
    refine forall_congr' fun i => forall_congr' fun j => ⟨fun h => ?_, fun h => ?_⟩
    · exact ((Formalism.L2.Theta.finPart D).map_mul _ _).symm.trans (congrArg (Formalism.L2.Theta.finPart D) h)
    · rw [← sub_eq_zero]
      apply GlobalTheory.PlaceSupp.AE_eq_zero D
      · have h0 : Formalism.L2.Theta.infPart D ((Formalism.L2.Theta.mt V (PV.ψ κ) - 1) i j) = 0 := congrFun (congrFun e2 i) j
        rw [RingHom.map_sub, RingHom.map_mul, h0, mul_zero, sub_zero]
      · rw [RingHom.map_sub, RingHom.map_mul, sub_eq_zero]
        exact h
  have s2 := conj_supp_iff (Formalism.L2.Theta.finPart D x) β K β' h1 h2 M (hm κ)
  have e7 : (K - 1).map (GlobalTheory.NJoin.tensCast hF) = (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1 := by
    rw [Matrix.map_sub _ (map_sub (GlobalTheory.NJoin.tensCast hF)),
      Matrix.map_one _ (map_zero (GlobalTheory.NJoin.tensCast hF)) (map_one (GlobalTheory.NJoin.tensCast hF))]
    congr 1
    exact Matrix.ext fun a b => (GlobalTheory.NJoin.tensCast hF).apply_symm_apply ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b)
  have s3 : ∀ i j, Formalism.L2.Theta.finPart D x * (K - 1) i j = (K - 1) i j ↔
      ∀ v', v' ≠ s.v → compAt D.host.E v' (((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j) = 0 := by
    intro i j
    have e8 : GlobalTheory.NJoin.tensCast hF ((K - 1) i j) = ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1) i j :=
      congrFun (congrFun e7 i) j
    rw [← idem_mul_iff s.v α' hw1 hw0, ← (GlobalTheory.NJoin.tensCast hF).injective.eq_iff, (GlobalTheory.NJoin.tensCast hF).map_mul,
      hfin, hT, e8]
  have e9 : ∀ v', ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) - 1).map (compAt D.host.E v') =
      (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E v') - 1 := fun v' => by
    rw [Matrix.map_sub _ (map_sub (compAt D.host.E v')),
      Matrix.map_one _ (map_zero (compAt D.host.E v')) (map_one (compAt D.host.E v'))]
  rw [s1, s2]
  constructor
  · intro h v' hv'
    rw [← sub_eq_zero, ← e9]
    exact Matrix.ext fun i j => (s3 i j).1 (h i j) v' hv'
  · intro h i j
    refine (s3 i j).2 fun v' hv' => ?_
    have := e9 v'
    rw [h v' hv', sub_self] at this
    exact congrFun (congrFun this i) j


end GlobalTheory.LabelTransport
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  first | exact @GlobalTheory.SplitFrameLattice.glint_mul_frame_basis | exact GlobalTheory.SplitFrameLattice.glint_mul_frame_basis | (intros; apply GlobalTheory.SplitFrameLattice.glint_mul_frame_basis <;> assumption)
end
