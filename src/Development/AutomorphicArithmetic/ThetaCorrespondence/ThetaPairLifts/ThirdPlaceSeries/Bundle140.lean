module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle073
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle118
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle120
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle519
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle093
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle094
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle095
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle517
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle122
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section



section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.cov_size_bound : _root_.GlobalTheory.CovTop.SizeCondition := by
  first | exact @_root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | exact _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | (intros; apply _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option autoImplicit false
noncomputable section
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn.OntoPath
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem onto_path_alt : _root_.GlobalTheory.BigOn.TwoRunsStatement → _root_.GlobalTheory.BigOn.RationalityStatement' → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → _root_.GlobalTheory.BigOn.TwistStatement' →
    _root_.GlobalTheory.BigOn.ShareStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement → _root_.GlobalTheory.BigOn.ExponentStatement → _root_.GlobalTheory.BigOn.PageStatement → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hRuns hRat hGeo hRank hTw hSh hBad hExp hPage
  have H := ((((((((hRuns.and hRat).and hGeo).and hRank).and hTw).and hSh).and hBad).and hExp).and hPage)
  refine Closed.imp H ?_
  intro eps Fm CH _ H _
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨xR, hR⟩, ⟨xQ, hQ⟩⟩, ⟨cG, hG⟩⟩, ⟨cK, hK⟩⟩, ⟨cT, hT⟩⟩, ⟨cS, hS⟩⟩, ⟨cB, hB⟩⟩, ⟨cE, hE⟩⟩, ⟨cP, hP⟩⟩ := H
  set c0 : ℝ := max (max (max (max cG cK) (max cT cS)) (max (max cB cE) cP)) 1 with hc0
  let c : OnConst := ⟨c0, 14, 66 * c0 + 4⟩
  have hcb : OnPage.ConstBad c := ⟨le_rfl, le_rfl⟩
  have l1 : cG ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l2 : cK ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l3 : cT ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l4 : cS ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l5 : cB ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l6 : cE ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l7 : cP ≤ c.C := le_trans (by simp) (le_max_left _ _)
  obtain ⟨x1, h1⟩ := hG c l1 hcb
  obtain ⟨x2, h2⟩ := hK c l2 hcb
  obtain ⟨x3, h3⟩ := hT c l3 hcb
  obtain ⟨x4, h4⟩ := hS c l4 hcb
  obtain ⟨x5, h5⟩ := hB c l5 hcb
  obtain ⟨x6, h6⟩ := hE c l6 hcb
  obtain ⟨x7, h7⟩ := hP c l7 hcb
  refine ⟨2 * max c.CE 0, by positivity,
    max (max (max xR xQ) (max x1 x2)) (max (max x3 x4) (max (max x5 x6) x7)), ?_⟩
  intro x hx hx0 i p hp hm C hCC
  have a0 : max xR xQ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx0)
  have b0 : max x1 x2 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx0)
  have c1 : max x3 x4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx0)
  have d0 : max (max x5 x6) x7 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx0)
  obtain ⟨r, hr, hown⟩ := hR x hx (le_trans (le_max_left _ _) a0) i p hp hm
  have hrat := hQ x hx (le_trans (le_max_right _ _) a0) i p hp hm
  have hct := hm.2.1
  obtain ⟨O, hO⟩ := exists_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ (Fm.parT x hx i) (Fm.ex x hx i).kap_def
    (Fm.ex x hx i).errX r c hct.canon hct.halfEX hr
  have hrec : RecAt p (Fm.parT x hx i) r O := ⟨hO, hown⟩
  obtain ⟨gSup, gSpan, gLem, gData, gIdx, gDepth⟩ := h1 x hx (le_trans (le_max_left _ _) b0) i p hp hm r O hrec
  have kRank := h2 x hx (le_trans (le_max_right _ _) b0) i p hp hm r O hrec
  have tTw := h3 x hx (le_trans (le_max_left _ _) c1) i p hp hm r O hrec
  have sSh := h4 x hx (le_trans (le_max_right _ _) c1) i p hp hm r O hrec
  have bBad := h5 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  have eExp := h6 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  obtain ⟨pPage, pSizes, pX, pBad, pLev, pY, -, pE1u, pTie⟩ :=
    h7 x hx (le_trans (le_max_right _ _) d0) i p hp hm r O hrec
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hm.1
  obtain ⟨hC, hOk, hU, hBL, hRR, -⟩ := hL
  have hI := GlobalTheory.ClassSumIdentity.leafIdentity_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hrat
  have hT2 := GlobalTheory.BaseTwistIncl.leafTW2_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hBL hrat
  obtain ⟨dG, dR, d2, dL⟩ := gDepth c.CE CH
  obtain ⟨err, herr⟩ := GlobalTheory.T.twistedPlacesBoundChain_twoRunChain _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1
    ((R2 p).num (F2 p) c.CE CH) c.CE hOk hC.grp.levels hC.grp.chiW hC.models hC.tup.mu_conj hC.thP.thG hU hBL hrat hRR
    pLev pY gSup gSpan gLem gIdx gData kRank hI hT2 tTw sSh bBad dG dR d2 dL pPage pSizes pX pBad (eExp c.CE CH) le_rfl
    (pTie c.CE CH)
  obtain ⟨hon, hD⟩ := GlobalTheory.T.onClauses_with_error_of_splitPart _ _ _ _ _ _ _ _ _ _ p c.CE CH err herr
  have hDpos : 0 < (p.S false).D := by rw [hD]; exact hRR.1
  have hJ : ∀ w ∈ (p.S false).Tw, ∀ j, 0 ≤ p.Z.J0 ((p.S false).μ w) w j := (eExp C CH).1
  exact on_of_onWith_canonical _ _ _ (p.S false) p.Z c.CE C CH CH err hDpos pE1u
    (le_trans (mul_le_mul_of_nonneg_left (le_max_left c.CE 0) zero_le_two) hCC) hJ (fun w j => p.err_eq w j) hon
end GlobalTheory.BigOn.OntoPath
end
end
end

section

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.TraceClassRank
section General
open scoped TensorProduct
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}
end General
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
theorem rank_at_twisted_places_of_rec_span (hR : p.PointConditions') (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O)
    (hMax : ∀ v ∈ p.R.twPl, ∀ j,
      GlobalTheory.TraceClassRank.SpanOverClasses (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v))
    (hSp : LeafSpan O) (hD : LeafData O)
    (hCmp : ∀ v ∈ p.R.twPl, ∀ j,
      letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
      GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (hrec.1.ok.laws v).p (fw2 p) j (r.lev j)
        (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt D v)) :
    GlobalTheory.TraceClassRank.RankAtPlaces O := by
  obtain ⟨hC, hOk, hLU, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hX := hOk.irr
  have h1 := hC.grp.levels
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, e⟩
  have hProj : LeafProj O := (level_of_tied ⟨z, act, y, ht⟩ hX h1).2.2
  have hd : ∀ j, FormsDetermined (R2 p) j := fun j =>
    formsDetermined_of (GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj.of_char GlobalTheory.LowTypeRestriction.resInj _ _ hC) hC.models.HW hLU
  have hComm : ∀ j (g : Mir (R2 p)), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j := fun j g => by
    obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
    letI : Algebra (r.used v₁).full.J.Q.c.F D.what₂.LL := p.alg
    exact tie_e_comm_rho (ht v₁ j).1 (ht v₁ j).2 hOk.irr g
  have key : ∀ v ∈ p.R.twPl, ∀ j, (O.ThJ v j).FG ∧
      O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := fun v hv j => by
    letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
    have hv' : v ∈ (R2 p).twPl := hv
    have hdel : ∀ x, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range := fun x => by
      obtain ⟨a, ha⟩ := Formalism.L2.Pj.FO_le _ (hm.2.1.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) x)
      exact ⟨a, ha⟩
    have hty := GlobalTheory.T.baseTupleThetaSpan_hasType _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j hLU (hd j) v hv'
      hC.tup.mu_on hdel (fun u => chi_eq_one h1 hC.grp.chiW j u.2)
    exact tie_thetaJ (ht v j).1 (ht v j).2 (mirIncl_injective _) hU (hd j) (hMax v hv j) hty (hrec.1.ok.run v hv' j)
      (hCmp v hv j)
  exact GlobalTheory.T.eigenlattice_local_containment_at_pairs _ _ _ _ _ _ O hSp hD hProj hComm fun w hw =>
    ⟨fun j => key w hw j, fun j => key _ (conjPl_mem_twPl hC hw) j⟩
end Point
end GlobalTheory.BigOn
theorem GlobalTheory.BigOn.rankLocSt_of_max_geo_runs : _root_.GlobalTheory.BigOn.MaximalityStatement → _root_.GlobalTheory.BigOn.GeometricStatement' → (_root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) → (_root_.GlobalTheory.BigOn.ForallRecordObjects fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) := by
  intro hM hG hC
  refine ((hM.and hG).and hC).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨x1, H1⟩, ⟨c0, H2⟩⟩, ⟨x3, H3⟩⟩ := H
  refine ⟨c0, fun c hc hb => ?_⟩
  obtain ⟨x2, H2'⟩ := H2 c hc hb
  refine ⟨max x1 (max x2 x3), fun x hx hle i p hR hm r O hrec => ?_⟩
  have hle1 : x1 ≤ x := (le_max_left _ _).trans hle
  have hle2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hle3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  have hg := H2' x hx hle2 i p hR hm r O hrec
  exact _root_.GlobalTheory.BigOn.rank_at_twisted_places_of_rec_span hR hm hrec (H1 x hx hle1 i p hR hm) hg.2.1 hg.2.2.2.1 (H3 x hx hle3 i p hR hm r hrec.1.ok hrec.2)
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.eventually_norm_bound_of_more_points : _root_.GlobalTheory.BigOn.SurjectiveOntoX → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigOn.More b.pt) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt | exact _root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.onto_at_chosen_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.page_estimate_statement' : _root_.GlobalTheory.BigOn.PageStatement := by
  first | exact @_root_.GlobalTheory.BigOn.pageSt_alt | exact _root_.GlobalTheory.BigOn.pageSt_alt | (intros; apply _root_.GlobalTheory.BigOn.pageSt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_at_split_place_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b))), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), _root_.GlobalTheory.Fam.QAllAlt W PP → ∀ (l : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP), LocY l y v.N (_root_.GlobalTheory.Fam.pk_z W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  first | exact @_root_.GlobalTheory.QGeoAt.geo_of_frames_alt | exact _root_.GlobalTheory.QGeoAt.geo_of_frames_alt | (intros; apply _root_.GlobalTheory.QGeoAt.geo_of_frames_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_places_characterized_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b))), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg → (∀ j, b j ∈ GfC (Yc D j)) → a.bT ∈ GfC D.sp.X' → IsSelfDualC D.sp.X' a.LT → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' a.bT (_root_.GlobalTheory.Fam.pk_z W).ΛX a.LT P) → (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (v.N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (v.N j) P) → v.b = b → v.bT = a.bT → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → ∃ (Ψ : ∀ j, PolF D (Yc D (j + 1)).rank (Yc D j).rank → GA D (Yc D j) → GA D (Yc D (j + 1)) → WO (Yc D j) (Yc D (j + 1)) → ℂ) (ΨT : ∀ j, j + 2 * 0 + 2 = D.R.m → PolF D D.sp.X'.rank (Yc D (j + 1)).rank → WO (Yc D (j + 1)) D.sp.X' → ℂ), (∀ j, j + 1 < D.R.m → ∀ P, ∀ x ∈ GinfC _, ∀ x' ∈ GinfC _, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) (Ψ j P x x')) ∧ (∀ j h P, GlobalTheory.FinPl.Vac (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (v.N (j + 1)) v.NT (fun _ => True) (ΨT j h P)) ∧ ∀ j row col, _root_.GlobalTheory.Fam.CommutingVectorTie (⟨mkGeo m b, j, row, col⟩ : _root_.GlobalTheory.Fam.FamilyCharacter W u) { v with Ψ := Ψ, ΨT := ΨT } := by
  first | exact @_root_.GlobalTheory.CommonVac.exists_common_vacua_alt | exact _root_.GlobalTheory.CommonVac.exists_common_vacua_alt | (intros; apply _root_.GlobalTheory.CommonVac.exists_common_vacua_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RLatMove
end GlobalTheory.RLatMove
namespace GlobalTheory.RLatMove
theorem finJ_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) : Finite {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} := by
  haveI := hW.fin
  have : {PP | PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} = ((_root_.GlobalTheory.Fam.pk_z W).Pg : Set _) ∪ ⋃ t, ((_root_.GlobalTheory.Fam.pk_z W).Q t : Set _) := by
    ext PP; simp [_root_.GlobalTheory.Fam.QAllAlt]
  have hf : Set.Finite {PP | PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} := by
    rw [this]; exact (Finset.finite_toSet _).union (Set.finite_iUnion fun t => Finset.finite_toSet _)
  exact hf.to_subtype
end GlobalTheory.RLatMove
namespace GlobalTheory.RLatMove
theorem move_main_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j)) → ∃ b : ∀ j, GA D (Yc D j), (∀ j, b j ∈ GfC (Yc D j)) ∧ (∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (N j) P) ∧ ∀ PP h j c (hc : j + c = (l PP h).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (l PP h).q) (Yc D j) (b j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hτ hNT hζ hLT hgP htP hdisj hPre hOrth hbas FY N hN hInt
  classical
  haveI : Finite {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} := _root_.GlobalTheory.RLatMove.finJ_alt W hW
  letI : Fintype {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun i : {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} => (l i.1 i.2).q.v) := by
    intro i i' hii
    apply _root_.GlobalTheory.T.level_places_under_injective' W hW
    simp only at hii
    rwa [(l i.1 i.2).under, (l i'.1 i'.2).under] at hii
  have key : ∀ j, j < D.R.m → ∃ t ∈ GfC (Yc D j),
      (∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
        GlobalTheory.FinPl.Moves (Yc D j) t ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (N j) P) ∧
      ∀ PP h c (hc : j + c = (l PP h).s + 1),
        ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
          GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧
          MovedTo (ofSplit (l PP h).q) (Yc D j) t ((_root_.GlobalTheory.Fam.pk_z W).βY j)
            (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id
              fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j hj
    have hsj : ∀ PP h, j + ((l PP h).s + 1 - j) = (l PP h).s + 1 := fun PP h => by
      have := (l PP h).hs; omega
    have hE : ∀ PP h, ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
        GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
      intro PP h
      obtain ⟨eqv, heqv⟩ := GlobalTheory.SymBridge.PhiAgreeProof.zPos_equiv D.R.k ((l PP h).s + 1) D.R.t j
      have hcard := card_eq_of_frame (FY PP h j _ (hsj PP h))
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at hcard
      have hr : D.R.k + ((l PP h).s + 1) + j * D.R.t = (Yc D j).rank := by
        rw [← hcard]; have := hsj PP h; omega
      exact ⟨eqv.trans (finCongr hr), fun x => by simp [heqv]⟩
    choose E hEo using hE
    let σ : ∀ PP h, Fin (Yc D j).rank ≃ (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((l PP h).s + 1 - j)) :=
      fun PP h => (E PP h).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j _ (hsj PP h))
    let M : ∀ i : {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP}, GL (Fin (Yc D j).rank) (l i.1 i.2).k :=
      fun i => frameGL (FY i.1 i.2 j _ (hsj i.1 i.2)) (bas i.1 i.2 j _ (hsj i.1 i.2)) (σ i.1 i.2)
    have hsd := _root_.GlobalTheory.T.selfDual_and_frame_of_pkHyp W hW j hj
    obtain ⟨t, ht, Lt, hLt, hMv, hAgree, hMT⟩ := GlobalTheory.T.exists_base_point_carrying_lattice_and_frames D (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (N j) ((_root_.GlobalTheory.Fam.pk_z W).βY j)
      hsd.1 (hN j hj) {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} (fun i => (l i.1 i.2).k)
      (fun i => (l i.1 i.2).q) hinj M
    refine ⟨t, ht, ?_, ?_⟩
    · intro P hP
      have hloc : ∀ w, P w → GlobalTheory.FinPl.latV (Yc D j) Lt (· = w) = GlobalTheory.FinPl.latV (Yc D j) (N j) (· = w) := by
        intro w hw
        by_cases hex : ∃ i : {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP}, (l i.1 i.2).q.v = w
        · obtain ⟨⟨PP, h⟩, rfl⟩ := hex
          have hPg : PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg := fun hPg => hP _ hw ((hgP _).2 ⟨PP, hPg, (l PP h).under⟩)
          have hb := hbas PP h hPg j _ (hsj PP h)
          have hm := hMT ⟨PP, h⟩
          have hval : (M ⟨PP, h⟩).val = (FY PP h j _ (hsj PP h)).β.submatrix id (σ PP h) := by
            simp only [M, frameGL_val, hb, Units.val_one, Matrix.mul_one]
          rw [hval] at hm
          exact GlobalTheory.T.selfDual_lattice_eq_of_splitPlace_frame_span (Yc D j) t ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Lt (N j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) _ (l PP h).q _
            (FY PP h j _ (hsj PP h)) (σ PP h) ht hsd.1 hsd.2 hLt (hN j hj) (hMv _) hm
            (hInt PP h j _ (hsj PP h))
        · push_neg at hex
          exact hAgree w (fun i => (hex i).symm)
      have hEq := GlobalTheory.T.latticeCompletion_eq_of_local_agreement (Yc D j) Lt (N j) P hLt.1 (hN j hj).1 hloc
      have := hMv P
      unfold GlobalTheory.FinPl.Moves at this ⊢
      rwa [← hEq]
    · intro PP h c hc
      obtain rfl : c = (l PP h).s + 1 - j := by omega
      exact ⟨E PP h, hEo PP h, hMT ⟨PP, h⟩⟩
  choose T hT hMovesT hFrT using key
  refine ⟨fun j => if h : j < D.R.m then T j h else 1, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < D.R.m
    · simp only [dif_pos h]; exact hT j h
    · simp only [dif_neg h]; exact one_mem _
  · intro j hj P hP
    simp only [dif_pos hj]
    exact hMovesT j hj P hP
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    simp only [dif_pos hj]
    exact hFrT j hj PP h c hc
end GlobalTheory.RLatMove
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.Fam.goodBF_of_normalFrames_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP), ∀ j ρ h, GlobalTheory.FinPl.GoodBF (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).ψ ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).B j ρ h) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).J j ρ h) (N₁ j) (M₁ j ρ h) (N₁ (j + 1)) ((commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hgram hτ hNT hζ hSD hgP htP hdisj hPre hOrth hbas FY sc hNF N₁ M₁ hN₁ hFY hM₁ hcore PP hP j ρ h
  have hx : ∀ j, j ≤ D.R.m → (a.x j).Is := fun j hj => hIs.x j hj
  exact ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hN₁ j (by omega), hM₁ j ρ h, hN₁ (j + 1) (by omega), (hIs.x (j + 1) (by omega)).sd,
    GlobalTheory.T.besselLattice_splits_along_witt_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.fourierJacobiLattice_splits_at_normalFrame_place _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselPeriodCharacter_primitive_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselToJacobiMap_carries_normalFrameLines _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.normalFrame_place_yZero_primitive_in_hom_lattice _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h⟩
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilOK_of_rank_one_gram' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → f.ColOK → _root_.GlobalTheory.Fam.CommutingVectorTie f v → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t (w : VTup (f.t t)), (∀ p, p ∈ w.Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → WeilOK (t := f.t t) v ∧ (f.t t).UnrOn (offP v w) ∧ (f.t t).UnrOn (· ∈ v.tP) ∧ (f.t t).UnrK (· ∈ v.tP) ∧ Disjoint w.Q v.gP ∧ Disjoint w.Q v.tP ∧ ∀ (n : ℕ) (G : Fin n → GLoc v) pl, _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ i, (G i).Chars (f.t t) := by
  first | exact @_root_.GlobalTheory.FamChars.weilOK_of_rank_one_gram | exact _root_.GlobalTheory.FamChars.weilOK_of_rank_one_gram | (intros; apply _root_.GlobalTheory.FamChars.weilOK_of_rank_one_gram <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StepLevelP
theorem ioX_levChi_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : LinearMap.range ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX ∘ₗ ((_root_.GlobalTheory.Fam.pk_z W).HX t).e)), F.1 ∈ CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t → ∀ κ ∈ levS (Yc D (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (D.R.m - 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)), ∀ φ x g, ((_root_.GlobalTheory.Fam.pk_z W).ioX t F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItX φ x) (g * κ) = levChi (Yc D (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (D.R.m - 1)) ((_root_.GlobalTheory.Fam.pk_z W).datYt t (D.R.m - 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) κ * ((_root_.GlobalTheory.Fam.pk_z W).ioX t F).1 ((_root_.GlobalTheory.Fam.pk_z W).ItX φ x) g :=
  fun W hW t F hF κ hκ φ x g => ioX_levChi_gen (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) hW.bot.hyp.2.2.2.1.lev hW.bot.hyp.2.2.2.1.models
    hW.bot.hyp.2.2.2.1.chain t F hF κ hκ φ x g
end GlobalTheory.StepLevelP
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.baseChain_com_z_is_of_pkHyp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (_root_.GlobalTheory.BaseChain.com_z W).Is := by
  first | exact @_root_.GlobalTheory.BaseChain.com_is_alt | exact _root_.GlobalTheory.BaseChain.com_is_alt | (intros; apply _root_.GlobalTheory.BaseChain.com_is_alt <;> assumption)
end
end
