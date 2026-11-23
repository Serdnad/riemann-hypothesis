module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle021
public import Formalism.LocalToGlobal.HermitianForms.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle369
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle543
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle330
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle321
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenForms
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle308
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle381
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle325
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Port.jIn_nonempty_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  intro B X I hI hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJets hex hpi hSK hRd hpin hSC hDt hherm hforms hchiD u a
  classical
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := by
    intro v
    exact Finset.mem_image
  obtain ⟨Ch, chOf, eY, Kc, hK, hCh0, hlev0, hy0⟩ := GlobalTheory.T.trueColumnChoice_goodCharts_every_stage I hI hP l Z u (C.forms u) a Q hQ (hSC u)
  have hbad : ∀ v ∈ badQ (I.rec7 l Z) Q, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v := by
    intro v hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr ((hQ v).1 hv)
  obtain ⟨A, hpins, htie⟩ := GlobalTheory.T.trueColumn_kernelData_compatible_stepCharts I hI hP l Z L hT Gi Gl K Y cX ex t u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
    full.1.base.dt hTw hSK hRd hpin hpi hDt hbad
    (fun i hi => ⟨(hK i hi).2.2.1.readsK, (hK i hi).2.1⟩) (fun i hi β => ((hK i hi).2.2.2 β).1)
    (fun i hi β => by
      obtain ⟨n, hn, h⟩ := ((hK i hi).2.2.2 β).2
      exact ⟨n, hn, fun κ _ => h κ⟩) (fun _ i hi c y hy => by
    obtain ⟨k, hR, hk1⟩ := (hK i hi).2.2.1
    obtain ⟨p, hp, hN⟩ := hR.k_std (chOf i hi c)
    have e := GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level B.R B.host _ _ _ _ I.SQ _ _ (k (chOf i hi c)) y
      (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni (hN ▸ hp.lat)
      (fun P hP => hk1 _ _ (GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P hP)) hy
    obtain ⟨b, hb⟩ := GlobalTheory.Mem.Col2.FullDt.exists_lift B.host y
    rw [e, GlobalTheory.Mem.Col2.FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ y b hb, hDt y b hb])
  have hf : g.forms u = (C.forms u).to0 := congrFun hforms u
  refine ⟨{
      Gd := g
      Hh := full.1.base
      rel := full.1.relDet
      St := charts I l Z u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
      A := A
      a := B.fields.conjO (X.piT u)
      pins := hpins
      tie := htie
      val := ?val
      fin := fun i hi => (hK i hi).1
      ord := fun i hi β => ((hK i hi).2.2.2 β).2
      base := ?base
      joint0 := GlobalTheory.hServTwoSidesJoint0 hT ex.cmp g C full hherm hforms u
      e0 := I.eCls0 l u a
      jointCmpEmbeddingY := Equiv.refl _
      e0Tw := ?e0Tw
      lev0 := ?lev0
      ch0 := hCh0
      y0 := ?y0
      fr0 := ?fr0
      rat := fun j hj => GlobalTheory.T.trueColumnTupleKernels_rational I hI hP l Z l0 ex.tw hJets hex u a j hj
      kin := GlobalTheory.T.kernelCoefficientField_le_coefficientField I hI hP l Z L hT Gi Gl K Y cX ex t hSK
      chiD := hchiD }⟩
  case val =>
    intro i hi
    rw [hex]
    exact GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a i hi _ (Ch i hi) (chOf i hi) (Kc i hi) (eY i hi)
      (hK i hi).2.2.1.readsK (hK i hi).2.1
  case base =>
    intro i hi β
    obtain ⟨k, hR, _⟩ := (hK i hi).2.2.1
    rw [GlobalTheory.T.trueColumn_orthonormalCoords_eq_given I hI hP l Z L hT Gi Gl K Y cX ex t u a _ Ch chOf eY Kc full.1.base.dt A hSK (fun i hi => (hK i hi).2.1) hpins i hi]
    exact GlobalTheory.T.companionLattice_trueColumn_baseLattice_eq_standard I hI hP l Z u i hi _ (fun x => hR.lb β x)
  case e0Tw =>
    intro φ c y
    change φ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) y = φ c y
    exact congrFun (congrArg φ ((I.eCls0 l u a).symm_apply_apply c)) y
  case lev0 =>
    rw [hf]
    exact hlev0
  case y0 =>
    rw [hf]
    intro c
    obtain ⟨κ, h1, h2, h3⟩ := hy0 c
    refine ⟨κ, h1, h2, fun v hv => h3 v fun hvQ => ?_⟩
    obtain ⟨q, hq, hqv⟩ := GlobalTheory.T.placeUnderTwistPrime_over_tupleRamifiedPrime I hI hP l Z L hT Gi Gl K Y cX ex t hSK a v ((hQ v).1 hvQ)
    exact hv q hq hqv
  case fr0 =>
    rw [hf]
    intro y
    apply Subtype.ext
    exact ((hK 0 (Nat.zero_le _)).2.1 y).trans ((hSC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y).symm
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

theorem _root_.GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (C : Subgroup (UA E n)) (χ : C →* ℂˣ) (f : algForms W), (∀ (c : C) v g, f.1 v (g * c) = (χ c : ℂ) * f.1 v g) → ∃ (I : Finset (AutSub E n)) (F : AutSub E n → algForms W), (∀ π ∈ I, F π ∈ π.finPart W) ∧ (∀ π ∈ I, ∀ (c : C) v g, (F π).1 v (g * c) = (χ c : ℂ) * (F π).1 v g) ∧ f = ∑ π ∈ I, F π := by
  first | (exact @GlobalTheory.EigenDecomp.eigen_decomp) | (exact GlobalTheory.EigenDecomp.eigen_decomp) | (intros; apply GlobalTheory.EigenDecomp.eigen_decomp  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_aAtG_of_rowPin : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    (∀ K X f T c, Q K X f T c →
      (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) →
    AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk :=
  GlobalTheory.T.atGRows_bundlePoints_of_jetSplitAmbient GlobalTheory.T.jetTableBound_splitPrime

end GlobalTheory.AtG
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_adelicDatum_with_laws_at_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ Xi muT, AdLawAt J.A J.dtU J.a Xi muT := by
  first | exact @GlobalTheory.TwV.exists_adLawAt_joint | exact GlobalTheory.TwV.exists_adLawAt_joint | (intros; apply GlobalTheory.TwV.exists_adLawAt_joint <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepDel

theorem del_of_pos : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPo hL j _ hj
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPo hL j hj

end GlobalTheory.TwV.StepDel
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepZero

theorem del_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPos hL
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPos hL 0 (by have := GlobalTheory.TwU.m_eq t μ; omega)

end GlobalTheory.TwV.StepZero
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  first | exact @GlobalTheory.PdvTie.at_of_stdTie | exact GlobalTheory.PdvTie.at_of_stdTie | (intros; apply GlobalTheory.PdvTie.at_of_stdTie <;> assumption)
end
