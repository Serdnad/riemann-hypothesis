module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle322
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle217
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle205
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle321
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle252
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle219
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlobLatCompanOfLev
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle364
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle355
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle353
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle365
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsSharpAtOfValTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle192
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (u : B.Word) (i : ℕ), i < B.R.m → I.A.LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) ∧ I.A.ESmooth (B.R.N i) (B.R.N (i + 1)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true | exact GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true | (intros; apply GlobalTheory.Mem.Col2.TC.laHyp_eSmooth_true <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.Fwd

theorem sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V)
    (op : I → Module.End K V) (opC : I → Module.End ℂ W)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    (hint : ∀ i x, j (op i x) = opC i (j x)) (hc : Formalism.L2.Col.PairComm opC) (Q : (I → K) → Prop) {u : W}
    (hu : u ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V))) (hu0 : u ≠ 0) {y : I → ℂ}
    (hy : ∀ i, opC i u = y i • u) : ∃ s, Q s ∧ y = fun i => σ (s i) := by
  have h1 := (GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp hint).2.1 Q
  rw [h1] at hu
  by_contra hne
  have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ∃ s, Q s ∧ x = fun i => σ (s i)) (C' := fun x => x = y)
    (fun x hx h => hne (h ▸ hx))
  have hu' : u ∈ Formalism.L2.Col.eigSum opC (fun x => x = y) :=
    Formalism.L2.Col.eigAt_le_eigSum (op := opC) (C := fun x => x = y) rfl (Formalism.L2.Col.mem_eigAt_of_forall_apply hy)
  exact hu0 ((Submodule.disjoint_def.1 hd) u hu hu')

end GlobalTheory.Hk3.Fwd


open GlobalTheory.Hk3.Fwd in

theorem GlobalTheory.Hk3.passage_of_carried : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ p c, R.Carries p c → R.Wc' j c ≠ ⊥ → cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) := by
  intro hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos hB hTr j pl cV cW hLD p c hCar hW
  obtain ⟨sy, x, hxg, hxe, hxW, hx0, hlab⟩ :=
    GlobalTheory.T.exists_good_rational_eigenform_hitting_carried_part hHowe R F hInt hC hEx hSch hJ s hOk hGen hU hGU hGE hLW hA hPos j pl cV cW hLD p c hCar hW
  obtain ⟨hCore, hSF, -, -, hEE, hWW, -⟩ := GlobalTheory.T.heckeCharacterisation_places_of_weakCharacterisation R F hC
  have core := hCore hEx
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCar.1
  have hu0 := GlobalTheory.T.upward_theta_lift_injective_on_carried_part R F hB hPos p c hCar w hw hw0
  obtain ⟨hOpsX, hOpsV⟩ := GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models
  obtain ⟨hX, hXo, hXn⟩ := hOpsX A3.A.μ0
  obtain ⟨hV, hVo, -⟩ := hOpsV j A3.A.μ0
  obtain ⟨plX, cX, c0, hRD⟩ := GlobalTheory.T.every_rowOperator_is_labelOperator_with_partner hHowe R F hInt hC hEx hSch hJ A3.A.μ0
  have hsplit := GlobalTheory.SplitHeckeLabel.split_ops R.toRealDat F.lv2 core.lev core.fam core.models
  have hM := core.models
  have hBx := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R A3.A.μ0).pres
  obtain ⟨hinj, hrange, -⟩ := hM.HX A3.A.μ0
  have hk := kForm_semi (R.jX A3.A.μ0) (R.HX A3.A.μ0).e (R.B.R A3.A.μ0).pres.extL (fun x => hM.jX A3.A.μ0 x) hinj
    (hrange.trans hBx.2.symm) (Formalism.L2.DIV.CSD.basis _) (Module.Basis.ofVectorSpace _ _) hBx.1
  have hjop : ∀ i f, R.jX A3.A.μ0 ((A3.rowI A3.A.μ0).opAll i f) = hX (plX i) (cX i) (R.jX A3.A.μ0 f) := hRD.op hX hXo
  have hcomm : Formalism.L2.Col.PairComm (fun i => hX (plX i) (cX i)) := fun a b => hXn.1 _ _ (hRD.good a) (hRD.good b) _ _
  have hwE : w ∈ EEc R.toRealDat R.SF c := hEE c ▸ hw
  have hy : ∀ i, hX (plX i) (cX i) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
      evC (Yc D 0) (plX i) (fun d => c (plX i) (dualLab d)) (c0 i) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun i =>
    (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 core hSch R.SF hSF A3.A.μ0 (plX i) (hRD.good i) (cX i) (c0 i) (hRD.mat i) hX hXo).2 c w hwE
  have hu : LinearMap.adjoint (R.Th A3.A.μ0) w ∈ Submodule.span ℂ (R.jX A3.A.μ0 ''
      (Formalism.L2.Col.eigSum (A3.rowI A3.A.μ0).opAll ((A3.rowI A3.A.μ0).HasRes3 p.1) : Set (A3.A.fam.R A3.A.μ0).S.Forms)) :=
    hCar.2 (Submodule.mem_map_of_mem hw)
  obtain ⟨sR, hsR, hyR⟩ := sys_of_mem_span D.what₂.embLL (R.jX A3.A.μ0) (Module.Basis.ofVectorSpace _ _)
    (A3.rowI A3.A.μ0).opAll (fun i => hX (plX i) (cX i)) hk.1 hk.2 hjop hcomm _ hu hu0 hy
  have hXs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ D.sp.X'.rank →
      hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (LinearMap.adjoint (R.Th A3.A.μ0) w) =
        D.what₂.embLL (sR (Sum.inl (P, k))) • LinearMap.adjoint (R.Th A3.A.μ0) w := by
    intro P k hkr
    have heq : hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) = hX (plX (Sum.inl (P, k))) (cX (Sum.inl (P, k))) := by
      refine LinearMap.ext_on hk.2 ?_
      rintro _ ⟨b, rfl⟩
      exact ((hsplit.1 A3.A.μ0 hX hXo P k hkr _).symm).trans (hjop (Sum.inl (P, k)) _)
    exact (LinearMap.congr_fun heq _).trans ((hy (Sum.inl (P, k))).trans
      (congrArg (fun z : ℂ => z • LinearMap.adjoint (R.Th A3.A.μ0) w) (congrFun hyR (Sum.inl (P, k)))))
  have hVs : ∀ (P : A3.A.ok A3.A.μ0) k, k ≤ (Vc D j).rank →
      hV (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (sy (Sum.inl (P, k))) • R.jV j A3.A.μ0 x := by
    intro P k hkr
    have h1 : A3.A.heckeL j A3.A.μ0 (P, k) x = sy (Sum.inl (P, k)) • x := hxe (Sum.inl (P, k))
    exact (hsplit.2 j A3.A.μ0 hV hVo P k hkr x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) h1).trans ((R.jV j A3.A.μ0).map_smulₛₗ _ x))
  have hL := GlobalTheory.T.liftSplitHeckePolys_eq_transfer_residualPolys R.toRealDat F.lv2 hInt core hSch hOk.ok2.irr R.SF hSF j c p.1.1 (fun i => sR (Sum.inl i))
    (fun i => sy (Sum.inl i)) hsR.1 hX hV hXo hVo w hwE hu0 hXs (R.jV j A3.A.μ0 x) (hWW j c ▸ hxW) hx0 hVs
  exact ⟨sy, ⟨hL, hTr j p c hCar sy ⟨x, hxg, hxe, hxW, hx0⟩⟩, hlab⟩
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

theorem chars_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {ξ ξ' : Fin n → (kˣ →* ℂˣ)} (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (e : ξ = ξ') :
    chars ξ hξ = chars ξ' hξ' := by
  subst e; rfl

theorem charLift_trans : ∀ (K M N : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Field N] [NumberField N] [_root_.NumberField.IsTotallyComplex N] [Algebra K M] [Algebra M N] [Algebra K N] [IsScalarTower K M N] (a : ℕ) (π : CuspSub K a) (P : CuspSub M a) (Q : CuspSub N a), CharLift π P → CharLift P Q → CharLift π Q := by
  intro K M N _ _ _ _ _ _ _ _ _ _ _ _ _ a π P Q h1 h2
  refine ⟨GlobalTheory.T.cuspidal_baseChange_trans_tower K M N a π P Q h1.1 h2.1, ?_⟩
  intro v w _ τ T hτ hT ξ hξ hs
  let u : HeightOneSpectrum (𝓞 M) := w.under (𝓞 M)
  haveI hwu : w.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  haveI huv : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.tower_bot w.asIdeal u.asIdeal v.asIdeal
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M a P u
  have h3 := h1.2 v u τ σ hτ hσ ξ hξ hs
  have h4 := h2.2 u w σ T hσ hT _ _ h3
  have e := GlobalTheory.BCChar.normU_comp_normU v u w
  refine (congrArg (HasSupport T.ρ) (chars_congr _ _ ?_)).mp h4
  funext j
  rw [MonoidHom.comp_assoc, e]

end GlobalTheory.RoadU
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG

theorem _root_.GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound : JetSplitAmb → ∀ (D : D7) (EX : ErrX D) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _), GlobalTheory.ColPeriod.JetLossAll D EX sel B χ cD := by
  first | exact @GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | exact GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | (intros; apply GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.AdLevCpl

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem levAt_coupled : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hMu i hi hi2 hAw
  have key : ∀ β β' x x' p p', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' → ∀ z,
      xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
    intro β β' x x' p p' hp hp' z
    have hh : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
    unfold xiAd
    rw [dite_eq_left hh]
    rw [hAw β β' x x' x x' p p' hh.1.choose hh.2.choose hp hp' hh.1.choose_spec hh.2.choose_spec (fun v _ => ⟨rfl, rfl⟩)]
  intro β β' x x' x₁ x₁' κ κ' h1 h1' z
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  obtain ⟨p₁, hp₁⟩ := hEx i (Nat.le_of_succ_le hi) β x₁
  obtain ⟨p₁', hp₁'⟩ := hEx (i + 1) hi β' x₁'
  rw [key β β' x₁ x₁' p₁ p₁' hp₁ hp₁' z, key β β' x x' p p' hp hp' z]
  have hs := GlobalTheory.T.firstCoupledStep_adelicDatum_source_level_law A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x₁ x₁' κ p p₁' p₁ h1 hp hp₁' hp₁ (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  have ht := GlobalTheory.T.firstCoupledStep_adelicDatum_law_targetLevel A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' h1' hp hp' hp₁' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  linear_combination (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1)) * hs +
    (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1)) * ht

end GlobalTheory.AdLevCpl
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.finiteDatum_levelEquivariance_at_matrixSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i < t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.TwV.levAt_mat | exact GlobalTheory.TwV.levAt_mat | (intros; apply GlobalTheory.TwV.levAt_mat <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem congAt_fb_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p (κ : ((St i hi).K β).lev.U), IsPtAd A a i hi β x p → ∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) ∧ CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))⁻¹) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x p κ hp P
  exact GlobalTheory.LevStab.lev_stab_cong i hi _ a κ _ _ (GlobalTheory.T.chartBaseFrame_badPrime_eq_companion_lattice A dtU a hP H i hi β x p hp P)

end GlobalTheory.TwV

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernelFunction_adelicPoints_eq_pullback_classKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (latK D.sp (gramN D i (Nat.le_of_succ_le hi)) a x.1 ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.Lb) (latK D.sp (gramN D (i + 1) hi) a x'.1 ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.Lb) (Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x') z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * TaylorLogMetric.pull D t.B.tor (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap) (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) ((t.rd u μ).Th t.seam t.amb i c c') z) := by
  first | exact @GlobalTheory.TwV.SPull.kerTh_eq_pull | exact GlobalTheory.TwV.SPull.kerTh_eq_pull | (intros; apply GlobalTheory.TwV.SPull.kerTh_eq_pull <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelSite_latticeTuplePairs_admissible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  first | exact @GlobalTheory.pairOK_allSites | exact GlobalTheory.pairOK_allSites | (intros; apply GlobalTheory.pairOK_allSites <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem jointsAt_of_jIn : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (μ : D.what₂.Tup), G.LatTied hT Gi Gl → (∀ u, Nonempty (JIn t u μ)) → GlobalTheory.TwV.JointsAt t μ := by
  intro D L hT Gi Gl Kc Dx cX ex t μ hlt hJ u w hg hw
  obtain ⟨J⟩ := hJ u
  have ht : (Gl.Fl u w hg).t = D.R.t := fl_t ex u w hg
  have hm : (Gl.Fl u w hg).mm = D.R.m := fl_mm_eq ex u w hg
  obtain ⟨Z, hFo, hgood, hrest, -⟩ := GlobalTheory.T.exists_comparisonSiteData_over_chainCharts t u w hg μ J hw
  have H : CmpJHyp ex.cmp (Z.inTw (Gl.Fl u w hg) ht hT) :=
    GlobalTheory.T.comparison_data_statements_at_site J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT (fun u => J.Gd.forms u) ex.cmp J.Gd.cmp (fillRec ex u w hg) hgood hrest
  have one := GlobalTheory.T.step_zero_level_statements_of_joint hT ex.cmp J.Gd u w hg J.joint0
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_labIn_c0_cls_eq_levelZeroClass hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht hm hgood J.rat
    (GlobalTheory.chTw_DGam_dvd_mem_DGam t u μ) one J.e0
  obtain ⟨hst, htw⟩ := GlobalTheory.T.comparisonSite_charts_twists_eq_tupleChain J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT J.Hh J.St J.val hFo
  obtain ⟨hiw, hpl, hB, hpos, halg, halg0⟩ := GlobalTheory.T.site_localIdentifications_eq_stepZero hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht
  refine ⟨Z.lv (Gl.Fl u w hg) ht, Z.inTw (Gl.Fl u w hg) ht hT, H, X, ⟨?_⟩⟩
  exact
  { Gd := J.Gd
    St := J.St
    A := J.A
    dtU := J.Hh.dt
    a := J.a
    pins := J.pins
    tie := J.tie
    st := fun j hj => hst j hj
    e0 := J.e0
    jointCmpEmbeddingY := J.jointCmpEmbeddingY
    e0Tw := J.e0Tw
    one := one
    cls0 := fun c La _ => hX c La
    lev0 := J.lev0
    ch0 := J.ch0
    y0 := J.y0
    fr0 := J.fr0
    iw := hiw
    oneB := hB
    pos := hpos
    tw := htw
    rel := J.rel
    base := J.base
    sharp := GlobalTheory.FormsSharpTie.formsSharpAt_of_pins t u μ J.St J.A J.Hh.dt J.pins (fun _ _ => True) (fun j hj => J.val j hj.le)
    dgen := t.O_dgen u μ ▸ (t.O u μ).dgen_gen
    tied := hlt
    away := hw
    cop := t.cc_rec ▸ GlobalTheory.coprime_absNorm_ccK_of_gIdx D _ _ hg
    empty := Z.lv_empty (Gl.Fl u w hg) ht
    alg := halg
    alg0 := halg0
    lbB := GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT
    lb0 := GlobalTheory.TwV.LbB.lbAtB_lev0At hT ex.cmp J.Gd u w hg J.joint0
    pl := hpl
    kin := J.kin }

end GlobalTheory.TwV
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m), FillAt (hT := hT) (H := H) (X := X) std j hj → ∀ x ∈ U1 (sigD D), ‖TaylorLogMetric.lamC S.lam (S.muT (j + 1) x)‖ = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * ordA (A0 J) v x)) := by
  first | exact @GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos | exact GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos | (intros; apply GlobalTheory.TwV.Xc.lambdaCharacter_norm_eq_p_pow_of_pos <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), chiI J (x * y) = chiI J x * chiI J y) ∧ (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E → chiI J x = 1) ∧ (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ)) ∧ ∀ x ∈ U1 (sigD D), ∃ 𝔞, TaylorLogMetric.N1 D 𝔞 ∧ chiI J x = t.χ 𝔞) := by
  first | exact @GlobalTheory.TwV.Xc.chiI_hom | exact GlobalTheory.TwV.Xc.chiI_hom | (intros; apply GlobalTheory.TwV.Xc.chiI_hom <;> assumption)
end
