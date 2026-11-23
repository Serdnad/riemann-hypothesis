module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle600
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LambdaPrimeEqLambdaThree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
import Formalism.SharpRestriction.InertJacobiLevels.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section
namespace GlobalTheory.HeightCounting.Up.RealOfReading

open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie

def realOfRead {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    {cf : CharFrame D} {nch : NChoice D} (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd)
    (labPi : E.Pi → A3.A.fam.base.Ix) (hbase : R.BaseW F)
    (htup : ∀ μ, Used0 D μ → R.toLevCh.xiH (Y.tupT μ) = tp.xi μ) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP) :
    GlobalTheory.NJoin.RealAt D cf nch tp where
  G := G
  Pl0 := Pl0
  T := T
  A := A3.A
  Ks := Ks
  R := R
  F := F
  tupT := Y.tupT
  hm := Y.hm
  hTop := Y.hTop
  hinj := Y.hinj
  X0 := X0
  Ish := Y.Ish
  I0 := Y.Iz
  IL := Y.IL
  K := Y.Kc
  Xd := Xd
  E := E
  labPi := labPi
  PY := Y.PY
  PW := Y.PW
  eFT := Y.eFT
  piOf := fun _ _ _ => 0
  ι := Y.ιW
  Tp := hC.symm ▸ tp
  cfEq := hC
  tpEq := by subst hC; rfl
  recR := by
    subst hC
    exact ⟨hbase, Y.tied, Y.prtE, Y.prtE0, Y.prtWE, Y.xi, htup,
      fun w => by rw [Y.muAt w, Y.tupT_tup], Y.isomFin, Y.frameMatch⟩
  given := hg
  full := hf

end GlobalTheory.HeightCounting.Up.RealOfReading
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta



theorem composite_eq_lift : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hPins.char.base.chain hHolds.aux.ex
  have hS : StepLev R.toRealDat F.lv2 := GlobalTheory.T.innerThetaSteps_preserve_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hT : TopLev R.toRealDat F.lv2 := GlobalTheory.T.lastThetaStep_keeps_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hP : RowProj R.toRealDat F.lv2 := rowProj_holds hC.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hUsed : ∀ t, Used0 D (Y.tup t) := by
    intro t
    rcases hPins.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h]
      exact Y.tup0
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  refine ⟨fun t x => ?_, fun t x => ?_⟩
  · rw [iota_sharp]
    exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP (RowSide.sharp D) true Y.Ish Y.tied.sharp
      (Y.tup t) (hUsed t) (Y.jA t x) t (Y.tupT_tup t) _ (Y.topRead t (hUsed t) x)
  · exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP X0.s false Y.Iz Y.tied.base
      (Y.tup t) (hUsed t) (Y.jA0 t x) t (Y.tupT_tup t) _ (Y.topRead0 t (hUsed t) x)

end GlobalTheory.Mem.R3.DTheta
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open Formalism.IndefR.RecTie GlobalTheory.LamPrimeTransport
open scoped InnerProductSpace



theorem eigenvalue_of_part : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.lamP D.what₂.mu0 ((i : ℕ) + 1) π = R.lam3 i A3.A.μ0 c A3.A.v0 := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π p hne hle
  have hC := hP.char
  have hEx := hH.aux.ex
  have hA := hH.prim.thmA
  have hGE := hH.prim.gEquiv
  have hE : R.toRealDat.IsThP := RealDat.thP_of_weak hC.base.thP hEx
  have hM : R.toRealDat.IsModels := hC.base.models
  have hμ : Used0 D D.what₂.mu0 := Or.inl rfl
  have hT := Y.tied.lift
  have htup : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hread := thetaP_read R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj hC.base.lev hC.base.grp hM hE Y.IL hT D.what₂.mu0 hμ i
  rw [← htup]
  refine hT.lamP D.what₂.mu0 hμ i π _ hne fun y hy' => ?_
  have hw0p : Y.mj.eW i y ∈ R.Wp3 i p := hle hy'
  have hw0e : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) = (Y.IL.jMj i y).1 := (Y.mjRead i y).symm
  have hw0W : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e (Y.mj.eW i y)) ∈
      (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc i := by
    rw [hw0e]; exact (Y.IL.jMj i y).2
  have haS := GlobalTheory.LamPrimeTransport.adjoint_mem_base_level R F hCRD hC hEx hGE Y.tupT Y.hm Y.hTop Y.hinj i (Y.mj.eW i y) hw0W
  obtain ⟨a, ha⟩ : ∃ a, LinearMap.adjoint (R.thG i (Y.tupT D.what₂.mu0)) (Y.mj.eW i y) = a := ⟨_, rfl⟩
  rw [ha] at haS
  obtain ⟨x', hx'⟩ : ∃ x', Y.IL.jMt D.what₂.mu0 hμ i x' = ⟨R.toRealDat.extV i (Y.tupT D.what₂.mu0) a, haS⟩ :=
    ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  have hprex : pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x') = a := by
    apply Y.hinj i (Y.tupT D.what₂.mu0)
    rw [ext_pre, hx']
  have hTx : D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y = x' := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : ⟪u, D.what₂.thetaT D.what₂.mu0 ((i : ℕ) + 1) y⟫_ℂ = ⟪D.what₂.thetaP D.what₂.mu0 ((i : ℕ) + 1) u, y⟫_ℂ :=
      LinearMap.adjoint_inner_right _ _ _
    rw [e1, hT.mj i, hT.mt D.what₂.mu0 hμ i, hread u, ← hw0e]
    erw [ipWc_lift R.toRealDat hM.HW F.lv2 Y.tupT Y.hm Y.hTop Y.hinj i]
    rw [← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i u),
      ← ext_pre R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj D.what₂.mu0 i (Y.IL.jMt D.what₂.mu0 hμ i x'),
      ipA_ext, hprex, ← ha, LinearMap.adjoint_inner_right]
  rw [hTx]
  apply (Y.IL.jMj i).injective
  apply Subtype.ext
  rw [hread x', hprex, ← ha, hA i (Y.tupT D.what₂.mu0) p (Y.mj.eW i y) hw0p, LinearEquiv.map_smul, Submodule.coe_smul, ← hw0e]
  rw [map_smul]
  exact map_smul _ _ _

end GlobalTheory.Mem.R3.ScalarComponentUnique
end

noncomputable section
namespace GlobalTheory.Mem.R3.ScalarComponentUnique

open _root_.Formalism.L2.Col GlobalTheory.HeckeLifts₂



theorem part_unique : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) π (c p : A3.fam3.base3.Ix),
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i p).comap (Y.mj.eW i) → c = p := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH i π c p hne hc hp
  by_contra hcp
  obtain ⟨hW, hHk⟩ := hH.prim.hecke.2
  have hu := untw_of_hH hP.char hHk
  have hd0 := disjoint_eigSum (hu.comm i) (C := SysC A3 i c) (C' := SysC A3 i p) fun y h h' =>
    h.elim fun x hx => h'.elim fun x' hx' => by
      have e : x = x' := funext fun k => D.what₂.embLL.injective ((congrFun hx.2 k).symm.trans (congrFun hx'.2 k))
      subst e
      exact (A3.liftI i A3.A.fam.μ0).excl3 (hH.sep c.1 c.2 p.1 p.2 (fun h => hcp (Subtype.ext h)) i) x hx.1 hx'.1
  have hd : Disjoint (R.Wp3 i c) (R.Wp3 i p) := hd0.mono (hu.parts i c).le (hu.parts i p).le
  have hinj : ∀ x, Y.mj.eW i x = 0 → x = 0 := fun x hx => by
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero] at h1
    have hn := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 (show RealDat.nP F.lv2 false * ‖x‖ ^ 2 = 0 by rw [← h1]; ring) with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
  apply hne
  refine eq_bot_iff.2 fun x hx => ?_
  have h1 : Y.mj.eW i x ∈ R.Wp3 i c := hc hx
  have h2 : Y.mj.eW i x ∈ R.Wp3 i p := hp hx
  exact (Submodule.mem_bot ℂ).2 (hinj x ((Submodule.disjoint_def.1 hd) _ h1 h2))

end GlobalTheory.Mem.R3.ScalarComponentUnique
end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  first | exact @GlobalTheory.Mem.R3.DTheta.composite_eq_lift | exact GlobalTheory.Mem.R3.DTheta.composite_eq_lift | (intros; apply GlobalTheory.Mem.R3.DTheta.composite_eq_lift <;> assumption)

end
end
