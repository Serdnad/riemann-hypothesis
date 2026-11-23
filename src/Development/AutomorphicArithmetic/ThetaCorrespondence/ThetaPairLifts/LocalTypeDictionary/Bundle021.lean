module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle491
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle522
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle182
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle083
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle484
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle503
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle510
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle527
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle569
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeEqAtMulSplitSupported
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedHomLat
open Matrix
variable {D : D7}

end GlobalTheory.MovedHomLat
open GlobalTheory.MovedHomLat in

theorem GlobalTheory.MovedDict.moved_lattice_action_compat : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x]
    let N := ch.S.N
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.grid (i + 1) j)) := ((y * N.u (.grid (i + 1) j) : FinPt ch.G (.grid (i + 1) j)) : Formalism.L2.Theta.GA D _)
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.grid i j)) := ((x * N.u (.grid i j) : FinPt ch.G (.grid i j)) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (negSp (ch.G.V (.grid (i + 1) j))) (ch.G.V (.grid i j)) (negGA _ ky) kx
      (colLat (N.fr (.grid (i + 1) j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid (i + 1) j)) ky) (colLat (N.fr (.grid (i + 1) j))))
      (colLat (N.fr (.grid i j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid i j)) kx) (colLat (N.fr (.grid i j))))
      (fwd (ch.G.V (.grid (i + 1) j)) ky _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.grid i j)) kx _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.grid (i + 1) j)) ky _)
      (bwd (ch.G.V (.grid i j)) kx _)
    exact H
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y]
    let N := ch.S.N
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.top j)) := ((x * N.u (.top j) : FinPt ch.G (.top j)) : Formalism.L2.Theta.GA D _)
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.top (j + 1))) := ((y * N.u (.top (j + 1)) : FinPt ch.G (.top (j + 1))) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) kx ky
      (colLat (N.fr (.top j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top j)) kx) (colLat (N.fr (.top j))))
      (colLat (N.fr (.top (j + 1))))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top (j + 1))) ky) (colLat (N.fr (.top (j + 1)))))
      (fwd (ch.G.V (.top j)) kx _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.top (j + 1))) ky _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.top j)) kx _)
      (bwd (ch.G.V (.top (j + 1))) ky _)
    exact H
  | mu t i j => exact absurd hp (by simp [DefPair])
  | core i => exact absurd hp (by simp [DefPair])
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.twisted_moved_lattice_action : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_lattice_action_compat | exact _root_.GlobalTheory.MovedDict.moved_lattice_action_compat | (intros; apply _root_.GlobalTheory.MovedDict.moved_lattice_action_compat <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
variable {D : D7}
end GlobalTheory.StartCusp
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult
variable {D : D7}

theorem cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  intro hP _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  have hT := GlobalTheory.ProjectedLift.thDn_mem R t y
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ (R.MY 0) _ _ _).1 hT
  have hu : ch.cv.lift t y = PiTensorProduct.lift (PiTensorProduct.lift.symm (R.thDn t y)) ch.cv.w := by
    rw [LinearEquiv.apply_symm_apply, ch.cv.thDn_w hS.core.chain]
  rw [hθ, hu]
  refine ⟨GlobalTheory.EndCusp.isAutFunSm_lift hT' _, isCuspFun_lift hT' _, fun τ => ?_⟩
  have h := star_lift_isTypeAt R.θ hP.harishChandraModules (R.MY 0) hT ch.cv.w τ
  rw [show Node.par D ch.sc.cGap (.grid 0 0) τ = (Ptw D).Dpar 0 τ from parV_zero D _ (Nat.zero_le _) τ]
  simp only [parB, dualPar_dualPar, Nat.zero_min] at h
  exact h
end GlobalTheory.StartCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  first | exact @_root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | exact _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | (intros; apply _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.EndCusp
open Formalism.IndefR.Mult Matrix
variable {D : D7}
end GlobalTheory.EndCusp
namespace GlobalTheory.EndCusp
open Formalism.IndefR.Mult Matrix
variable {D : D7}
end GlobalTheory.EndCusp
namespace GlobalTheory.EndCusp
open Formalism.IndefR.Mult Matrix
variable {D : D7}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.EndCusp
namespace GlobalTheory.EndCusp
theorem leadingForm_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hm := hS.core.models
  obtain ⟨h1, h2, h3⟩ := formX_props R hm.inf hm.cX hm.prX hm.HX ch.cv t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  obtain ⟨k1, k2, k3⟩ := props_cast R.θ (fun τ => Node.par D ch.sc.cGap (.grid 0 D.R.m) τ) (columnBlock R.toLevCh D.R.m)
    (colY_m R.toLevCh) (ch.cv.formX t y) h1 h2 (fun τ => by
      rw [show Node.par D ch.sc.cGap (.grid 0 D.R.m) τ = (Ptw D).Dpar D.R.m τ from parV_zero D _ le_rfl τ]
      exact h3 τ)
  rw [hθ]
  exact ⟨k1, k2, k3⟩
end GlobalTheory.EndCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.endCusp_leadingForm_listed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @_root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList | exact _root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList | (intros; apply _root_.GlobalTheory.EndCusp.leadingForm_mem_cuspList <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
variable {n : ℕ}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}
end GlobalTheory.KFinCuspAvgType
end
namespace GlobalTheory.KFinCuspAvgType
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N _ τ e _ he φ hφ
  obtain ⟨H, i1, i2, σ, lam, ε', P, hE, hD, hP, hJ, hx⟩ := hφ.2.2 τ
  obtain ⟨-, hε⟩ := GlobalTheory.SignedParTest.isEnum_unique hE (N.M.enum τ)
  subst hε
  haveI : CompleteSpace H := hD.1
  have hσ : Std (N.M.ε τ) σ := std_of_isDS hPr.harishChandraModules hD
  have hσ1 := hσ.1
  set fr := N.M.fr τ with hfr
  have hf := N.M.fr_unit τ
  have hfJ := N.M.fr_gram τ
  rw [← hfr] at hf hfJ
  have hdP := (isUnit_iff_isUnit_det _).1 hP
  have hdf := (isUnit_iff_isUnit_det _).1 hf
  have hG : IsUnit (gramAt D N.V τ) := isUnit_gram hP hJ
  have hc1 : fr * P⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hP hfJ hJ
  have hc2 : P * fr⁻¹ ∈ UJset (N.M.ε τ) := mul_inv_mem_UH hf hJ hfJ
  have e12 : fr * P⁻¹ * (P * fr⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.mul_nonsing_inv _ hdf]
  have e21 : P * fr⁻¹ * (fr * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdP]
  have hconj : ∀ {Q : Mx N.V.rank}, IsUnit Q → Qᴴ * Jm (N.M.ε τ) * Q = gramAt D N.V τ →
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), Q * g * Q⁻¹ ∈ UJset (N.M.ε τ) := fun {Q} hQ hQJ g hg =>
    mul_inv_mem_UH hQ (by
      calc (Q * g)ᴴ * Jm (N.M.ε τ) * (Q * g) = gᴴ * (Qᴴ * Jm (N.M.ε τ) * Q) * g := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D N.V τ := by rw [hQJ]; exact hg) hQJ
  refine ⟨H, i1, i2, σ, lam, N.M.ε τ, fr, hE, hD, hf, hfJ, fun x => ?_⟩
  have h1 := hasTypeAll_iff.2 (hx x)
  have h2 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) σ (gramAt D N.V τ) (Jm (N.M.ε τ)) fr hG hf hfJ
    (uIso hσ1 hc1 hc2 e12 e21) (fun g hg v => by
      rw [uIso_apply, uIso_apply, ← sigma_mul hσ1 hc1 (hconj hP hJ g hg), ← sigma_mul hσ1 (hconj hf hfJ g hg) hc1]
      congr 2
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdP, Matrix.nonsing_inv_mul_cancel_left _ _ hdf]) _ h1
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := h2
  have h3 := GlobalTheory.SeriesToClosure.moves_avg hθ hf hfJ hσ he φ x S v ℓ C hS hc h
  have h4 : HasTypeAll (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) σ
      (GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x) := ⟨S, hS, hc, _, ℓ, C, h3⟩
  have hfi : IsUnit fr⁻¹ := (isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hdf)
  have hfiJ : (fr⁻¹)ᴴ * gramAt D N.V τ * fr⁻¹ = Jm (N.M.ε τ) := by
    rw [← hfJ]
    calc (fr⁻¹)ᴴ * (frᴴ * Jm (N.M.ε τ) * fr) * fr⁻¹ = (fr * fr⁻¹)ᴴ * Jm (N.M.ε τ) * (fr * fr⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hdf]; simp
  have h5 := hasTypeAll_transport _ H H σ (fun g => σ (fr * g * fr⁻¹)) (Jm (N.M.ε τ)) (gramAt D N.V τ) fr⁻¹
    (isUnit_Jm _) hfi hfiJ (LinearIsometryEquiv.refl ℂ H) (fun g _ w => by
      show σ g w = σ (fr * (fr⁻¹ * g * fr⁻¹⁻¹) * fr⁻¹) w
      rw [Matrix.nonsing_inv_nonsing_inv _ hdf]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hdf, Matrix.mul_nonsing_inv _ hdf,
        Matrix.mul_one]) _ h4
  have e5 : (fun y => GlobalTheory.SeriesToClosure.res θ N.V τ fr (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) x (fr⁻¹⁻¹ * y * fr⁻¹)) =
      fun y => GlobalTheory.KFinCuspApprox.avgN θ N τ e φ (x * atTau θ N.V τ y) := funext fun y => by
    rw [Matrix.nonsing_inv_nonsing_inv _ hdf, GlobalTheory.SeriesToClosure.res_conj hf]
  rw [e5] at h5
  exact hasTypeAll_iff.1 h5
end GlobalTheory.KFinCuspAvgType
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kFinite_cusp_average_hasKType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | exact _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.KFinCuspAvgType.kFinite_average_isTypeAt <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AvgOtherPlace
open Formalism.MainNotions.S Formalism.REAL MeasureTheory Matrix GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
section Avg
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Avg
section Closure
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Closure
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N hN τ τ' hne e he _ φ hφ
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have p1 := hPr.discreteSeriesUpqExists
  have p2 := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have p3 := hPr.harishChandraModules
  have p4 := hPr.casselmanWallach
  have hT := GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') φ p1 p2 p3 p4 hθ hN
    (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hφ.1 (hφ.2.2 τ')
  have hA := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (KG (N.M.ε τ)) (muK (N.M.ε τ)) _ hκ hU e he φ hφ.1
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ N.V τ' (N.S τ') _ p1 p2 p3 p4 hθ hN (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hA
    (hasTypeAt_avgF (muK (N.M.ε τ)) hθ hne hκ hU he hφ.1.cont hT)
end GlobalTheory.AvgOtherPlace
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kType_preserved_average_other_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | exact _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedKappaDec
theorem exists_movedKappa_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ X hX Q hQ x
  obtain ⟨r, s, k, hr, hs, hk, e⟩ := GlobalTheory.RatSplitLat.exists_rat_split_lat (ch.G.V X) (ch.S.N.fr X) (∏ q ∈ Q, q)
    (Finset.prod_pos fun q hq => (hQ q hq).pos) (x * ch.S.N.u X)
  have hs' := GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit _ Q s hs
  have hB := GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL ch.S.toGridChoice X hX k hk
  refine ⟨r, s, k * (ch.S.N.u X)⁻¹, hr, hs', hB, fun q hq => ?_, ?_⟩
  · have key : ∀ s' ∈ GlobalTheory.MovedKappaEx.splitOff (ch.G.V X) Q, ∀ y : FinPt ch.G X,
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s' * y)) (GlobalTheory.SumSize.latAt ch.S.toGridChoice X y) := by
      intro s' hs'
      induction hs' using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact fun y => GlobalTheory.MovedSplitEq.eqAt_latAt_mul ch.S.toGridChoice X hX q (hQ q hq) e he (hoff q hq) g y hsupp
      | one => exact fun y => by rw [one_mul]; exact eqAt_refl q _
      | mul a b _ _ ha hb => exact fun y => by rw [mul_assoc]; exact eqAt_trans (ha (b * y)) (hb y)
      | inv a _ ha =>
        intro y
        have := ha (a⁻¹ * y)
        rw [mul_inv_cancel_left] at this
        exact eqAt_symm this
    have := key s hs' (k * (ch.S.N.u X)⁻¹)
    rw [hB] at this
    exact this
  · rw [← mul_assoc, ← e, mul_inv_cancel_right]
end GlobalTheory.MovedKappaDec
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.movedKappa_decomposition_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  first | exact @_root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition | exact _root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition | (intros; apply _root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition <;> assumption)
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FPair
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPairK ∧ InfPairK := fun _ => ⟨finPair, infPair⟩
end GlobalTheory.FPair
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.field_pair_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPairK ∧ InfPairK := by
  first | exact @_root_.GlobalTheory.FPair.lift_splits_locally | exact _root_.GlobalTheory.FPair.lift_splits_locally | (intros; apply _root_.GlobalTheory.FPair.lift_splits_locally <;> assumption)
end
end
