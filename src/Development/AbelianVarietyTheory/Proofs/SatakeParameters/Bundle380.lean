module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle353
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle363
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle360
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicChainDatumCharacterLawsJointKernel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle299
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle379
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle372
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle375
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle229
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle214
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle378
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle368
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle369
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle252
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle276
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle288
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle321
import Formalism.PeriodIntegrals.OrbJetBase
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.adelicChainDatum_characterLaws_jointKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  first | exact @GlobalTheory.TwV.adLawAt_xiAd | exact GlobalTheory.TwV.adLawAt_xiAd | (intros; apply GlobalTheory.TwV.adLawAt_xiAd <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem tieDel_all_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j < D.R.m, S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw j hj ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hj1 : j + 1 ≤ D.R.m := hj
  by_cases hne : Nonempty (Lv.comp j) ∧ Nonempty (Lv.comp (j + 1))
  swap
  · refine ⟨1, norm_one, ?_⟩
    intro La _ x c' L' _
    exact absurd ⟨⟨La.1⟩, ⟨c'⟩⟩ hne
  obtain ⟨⟨a⟩, ⟨a'⟩⟩ := hne
  obtain ⟨hn1, -, hsame⟩ := GlobalTheory.T.stepDeterminantConstant_unit_independent S hPos ι hι j hj1 a a'
  set cK := cKs S ι j hj1 a a' with hcK
  refine ⟨cK, hn1, ?_⟩
  obtain ⟨-, -, hrk, hRT⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hN := hRT j
  have h1 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := hrk (j + 1)
  obtain ⟨d0⟩ := GlobalTheory.T.exists_adelic_latticeTuple_decomposition S hDict
  intro La hLa x c' L' hL'

  have hQ : K2.SharpQ t ex.tw u μ j x (K2.qOf t ex.tw u μ j x) := by
    have hex := J.sharp j hj x
    unfold K2.qOf
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  set cc := clsAt X H j La.1 La.2 with hcc
  set κ := clsAt X H (j + 1) c' L' with hκ
  set Q := K2.qOf t ex.tw u μ j x with hQdef
  set P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ :=
    ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j cc) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) κ) : ℂˣ) : ℂ)) •
          framePol D (t.O u μ).dgen (Q cc) ((t.rd u μ).Th t.seam t.amb j cc κ)) with hP
  have hPw : P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) :=
    Submodule.smul_mem _ _ ((wt_polDY_framePol D (rk_le _ D hN) (t.O u μ).dgen _ (Q cc) (hQ.1 cc)).2 _)
  set φ := K2.entRec t ex.tw u μ j cc x with hφ
  have hφκ : ∀ y, φ κ y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y := by
    intro y
    have e := (GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial).2 D L hT Gi Gl Kc Dx cX ex t u μ j cc (Q cc) κ y
    have e2 : φ κ y = entQ t u μ j cc (Q cc) κ y := rfl
    rw [e2, e, hP, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

  have hR : ∀ d : Dec J std, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj1 h1 (c', L') φ V ∧
      MvPolynomial.map ι V = cK • S.Y.DelF j ((kaAt X H hT).cmp j x La.1 La.2) (srOf S.Y j La (c', L')) := by
    intro d
    obtain ⟨V, hV, hmap⟩ := GlobalTheory.T.transportedFramePolynomial_complex_values_at_point S hPos ι hι d j hj1 h1 (c', L') φ P hPw hφκ
    refine ⟨V, hV, ?_⟩
    rw [hmap]
    obtain ⟨hMove, hOp, hDeg⟩ := GlobalTheory.T.movedForms_operator_degrees_at_kernelSource S hDict hPos ι hι d j hj ⟨a'⟩ hN
    have hEq := GlobalTheory.FrameB.equiv_frame_b S.Y d.fd2 (ltC S.g S.hLT) (GlobalTheory.FrameB.ltC_ne S.hLT)
      ((GlobalTheory.TwV.DelB.frames_invertible S).2 d) j
    have hsc : ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
        ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 →
        cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) *
          ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2 := by
      intro La La' _ _
      have e := GlobalTheory.T.unit_mul_sourceScalar_eq_nextLevelScalar S hPos ι hι d j hj1 La La'
      rw [hsame] at e
      exact e
    have hDel := GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf S hDict hPair hPos hLaw d ι hι (fun j => phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j)
      (fun j c' L' => GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j (c', L'))
      (fun j c' L' => scT d S ι j c' L') (sO d ι) (gmS d) j hj cK hN hMove hOp hDeg hEq hsc
    have := hDel La hLa x Q hQ c' L' hL'
    exact this
  obtain ⟨V0, hV0, hm0⟩ := hR d0
  have hall : ∀ d : Dec J std, RealAt d (j + 1) hj1 h1 (c', L') φ V0 := by
    intro d
    obtain ⟨V, hV, hm⟩ := hR d
    have : V = V0 := MvPolynomial.map_injective ι ι.injective (hm.trans hm0.symm)
    exact this ▸ hV
  have hrd := GlobalTheory.T.latticeTupleReading_eq_of_realising_polynomial S hDict ι j hj1 h1 (c', L') hL' φ V0 hall
  exact hrd.trans hm0

end GlobalTheory.TwV.DelA
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_atG_pinned : GlobalTheory.AtG.JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd), (∀ K X f T c, Q K X f T c → (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) → AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk := by
  intro hJ Bd Q Lk hQ
  exact GlobalTheory.T.typePrimePeriodRow_of_constructedPointChains hJ Q Lk
    (RowE.of_all fun _ K β _ _ _ hq _ μ _ => GlobalTheory.T.concreteChainAgreesAtTuple_of_normalisedRows K β (hQ _ _ _ _ _ hq) μ)

end GlobalTheory.AtG
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem away_of_dict : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact GlobalTheory.T.kernelSite_away_of_positive_pair S hD ⟨J.alg0, J.alg⟩ J.kin (GlobalTheory.T.site_place_induces_position_embeddings S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hD)

end GlobalTheory.TwV
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue


set_option maxHeartbeats 1000000 in
theorem goodCharts_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi)), (∀ i hi, Finite (Ch i hi) ∧ I.IdY l Z u a i hi (eY i hi) ∧ ReadsOne I l Z u a i hi (chOf i hi) (Kc i hi) ∧ ∀ β, FunKilled ((Kc i hi) β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, ((Kc i hi) β).lev.chi κ ^ n = 1) ∧ Subsingleton (Ch 0 (Nat.zero_le _)) ∧ (∀ β, ((Kc 0 (Nat.zero_le _)) β).lev.Lb = F.to0.cls0.lev.Lb ∧ ((Kc 0 (Nat.zero_le _)) β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ ((Kc 0 (Nat.zero_le _)) β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : ((Kc 0 (Nat.zero_le _)) β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → ((Kc 0 (Nat.zero_le _)) β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, (((Kc 0 (Nat.zero_le _)) ((chOf 0 (Nat.zero_le _)) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  set_option maxHeartbeats 4000000 in
    intro B X I hOk hPins l Z u Ch0 chOf0 F a Q hQ hStd

    have hS : ∀ (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch)
        (Kc : Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a i hi chOf Kc ∧
          ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
      intro i hi h1
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact GlobalTheory.T.trueColumns_goodCharts_middleSteps I hOk hPins l Z u F a Q hQ hStd i hi h1 hlt
      · subst heq
        exact GlobalTheory.T.exists_good_chart_lastStep_allTuples I hOk hPins l Z u F a Q hQ hStd
    choose ChS hfin chOfS KcS hgood using hS
    obtain ⟨K0, h0a, h0b, h0c⟩ := GlobalTheory.T.trueColumnChoice_stepZero_charts_good I hOk hPins l Z u F a Q hQ hStd
    have hC := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
    have hE : ∀ i (hi : i ≤ B.R.m), ∃ eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi,
        I.IdY l Z u a i hi eY := by
      intro i hi
      obtain ⟨e, he, -⟩ := ((hC.2.2.2 i hi).2.2 u a).2
      exact ⟨e, he⟩
    choose eY heY using hE
    let Ch : ∀ i, i ≤ B.R.m → Type := fun i => Nat.casesOn (motive := fun i => i ≤ B.R.m → Type) i
      (fun _ => Unit) (fun j hj => ChS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
    let chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi := fun i => Nat.casesOn
      (motive := fun i => ∀ hi : i ≤ B.R.m, (I.stp u a i).Cl → Ch i hi) i
      (fun _ _ => ()) (fun j hj => chOfS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
    let Kc : ∀ i hi, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi) := fun i => Nat.casesOn
      (motive := fun i => ∀ hi : i ≤ B.R.m, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi)) i
      (fun _ => K0) (fun j hj => KcS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
    refine ⟨Ch, chOf, eY, Kc, ?_, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        refine ⟨(inferInstance : Finite Unit), heY 0 hi, h0a.1, h0a.2⟩
      | succ j =>
        exact ⟨hfin _ hi _, heY _ hi, (hgood _ hi _).1, (hgood _ hi _).2⟩
    · show Subsingleton Unit
      infer_instance
    · exact h0b
    · exact h0c

end GlobalTheory.TwU.AtTrue
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PdvClose

theorem at_of_true_columns : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → I.StdKer l Z t → GlobalTheory.Pdv.IsEntC t → t.Adapted → t.TopPinned → 3 ≤ B.host.splitBound → 5 ≤ K.dl1 → 4 ≤ K.dl2 → (∀ Ee : OrbitPlaces.Ent (I.rec7 l Z), OrbitPlaces.Shape (I.rec7 l Z) L Gi Ee ∧ ∀ u, ∀ j < B.R.m, ∀ s ∈ B.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * L.sc.a) → GlobalTheory.Pdv.At ex t.ent := by
  intro hAlg hG1 hCD hII B X I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC hAd hTop hsplit hdl1 hdl2 hSh
  have hDuty : GlobalTheory.Pdv.Duty t := GlobalTheory.T.conditions_at_standardKernelComparison_trueColumns I hOk hPins l Z l0 L hT Gi Gl K Y cX ex t hNorm hJets htw hStd hEntC
  have hHyp : t.Hyp := GlobalTheory.T.kernelEntries_hyp_of_columnSideProperties _ L hT Gi Gl K Y cX ex t hDuty.col hTop
  have hInp : GlobalTheory.ThLoc.Inputs := GlobalTheory.T.normalisedThetaCMCurveTheorems_of_algebraicTranslates hAlg
  have hHost := GlobalTheory.KerStd.HostInert.hostAt_inert hG1 hCD hII
  obtain ⟨P, Bf, hK, he⟩ := hEntC
  obtain ⟨t', hc', hf'⟩ := hDuty.forms
  obtain ⟨ep, be, hBe, h0⟩ := GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit
  refine ⟨⟨GlobalTheory.T.kernelPairScalars_isUnit_trueColumns I hOk hPins l Z L hT Gi Gl K Y cX ex t hStd,
    GlobalTheory.PdvKm.kmapRat_kerEntC' t P Bf hK he hDuty.rk,
    GlobalTheory.T.kernelClassSums_carry_chainComplexForms _ L hT Gi Gl K Y cX ex t' hc' hf',
    GlobalTheory.T.stab0_rec7_of_levelData I hOk hPins l Z ex.lev⟩, ep, be, (fun _ _ => -1), h0,
    GlobalTheory.T.frobeniusConjugation_conditions_adaptedKernelDatum hAlg hHost _ L hT Gi Gl K Y cX ex t hHyp hAd hsplit ep be _, ?_,
    GlobalTheory.T.jetIntegralityBis_ofKer_of_hyp hInp _ L hT Gi Gl K Y cX ex t hHyp hsplit ep be _,
    GlobalTheory.T.kernelDatum_thetaSeries_shape_at_d_adaptedBases hInp _ L hT Gi Gl K Y cX ex t hHyp hAd ep be _,
    (hSh _).1⟩
  exact GlobalTheory.T.orbitBound_standardSeries_inertPlaces _ L Gi K _ (hSh _).1 (hSh _).2 hdl1 hdl2 hBe rfl

end GlobalTheory.PdvClose
end
