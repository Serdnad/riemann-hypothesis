module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle130
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle024
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle368
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle334
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle373
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RatKDeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle352
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle366
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSource
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle372
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
import GroundTheory.LocalFields.PadicLogSeries
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv

private theorem nuT_cast_eq_nuW {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau) (r : Fin (B.R.N i)) :
    ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = (B.wts.nuW u (i + 1) τ).w r := by

  have hq : ((B.wts.nuW u (i + 1) τ).w r : ℚ) = Examples₂.wtN (B.hcW u τ) r.1 + wG B.R ((B.hcW u τ).e ⟨i, hi⟩) (i + 1) := by
    rw [Formalism.L2.Col.Wts.nuW_eq _ u hi τ r]
    rw [show B.wts.lamN u i τ = Examples₂.lamOf (B.hcW u τ) i from rfl, Formalism.L2.Col.lamOf_wtN _ hi.le r]

  have hrow : DV.nuRow (I.rec7 l Z) u (i + 1) τ r = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
    rw [GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2]
    have h := congrArg (fun x : ℚ => (x : ℝ)) hq.symm
    simp only [Rat.cast_intCast] at h
    exact h

  have hnn : 0 ≤ (B.wts.nuW u (i + 1) τ).w r := by
    have h1 := Formalism.L2.Ker.natW_cast (B.wts.nuW u (i + 1) τ) r
    have h2 := GlobalTheory.MoveCompare.nuW_detShift_nonneg B.wts u hi τ
    omega
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  show ((⌊DV.nuRow (I.rec7 l Z) u (i + 1) τ r⌋₊ : ℕ) : ℤ) = _
  rw [hrow, hn, Int.cast_natCast, Nat.floor_natCast]

private theorem monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) {i : ℕ} (hi : i < B.R.m) (τ : B.fields.Tau)
    (m : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ)
    (hm : degAt m τ = ∑ r, nuT (I.rec7 l Z) u i τ r) : (monoDeg m τ : ℤ) = nuDeg B u i τ := by
  have h3 : ((∑ r, nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) = nuDeg B u i τ := by
    push_cast
    exact Finset.sum_congr rfl fun r _ => nuT_cast_eq_nuW I l Z u hi τ r
  exact (congrArg (Nat.cast : ℕ → ℤ) hm).trans h3



theorem rk_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → t.RK := by
  intro B X I hok hpins l Z L hT Gi Gl K Y cX ex t hJ hS u μ hμ i hi c c' m hm
  rw [hS.O.dgen u μ, hS.O.Th u μ i c c']
  exact GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField I hok hpins l Z hJ u μ i hi c c' m fun τ => monoDeg_eq_nuDeg_of_degAt_eq_sum_nuT I l Z u hi τ m (hm τ)


end GlobalTheory.Pdv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eigenPart_le_typePart_of_passage : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → ∀ s, A3.fam3.Ok3 s → GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ → R.toRealDat.LUnif → R.PGUnit F → R.PGEquiv F → R.PLevW F → R.PThmA → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.TrISem F A3.trI → (R.toCx3 F).PartsW false → A3.fam3.TypesSep3 → ∀ j pl cV cW, LiftDict R j A3.A.μ0 pl cV cW → ∀ (p : A3.fam3.base3.Ix) c, cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) (labW j pl cW c) → R.Wc' j c ≤ R.Wp3 j p := by
  first | exact @GlobalTheory.Hk3.Back.wc_le_wp_of_passage | exact GlobalTheory.Hk3.Back.wc_le_wp_of_passage | (intros; apply GlobalTheory.Hk3.Back.wc_le_wp_of_passage <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

namespace GlobalTheory.AtG

theorem jetTableBound_constantOne_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D),
    (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) →
    Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  intro hJ D L EX Dx hT hS i w hw u hu μ hμ
  exact GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement hJ D L EX Dx μ (hT μ hμ) i (hS i) w hw u hu

end GlobalTheory.AtG
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  first | exact @GlobalTheory.TwV.isPtAd_mul_lev | exact GlobalTheory.TwV.isPtAd_mul_lev | (intros; apply GlobalTheory.TwV.isPtAd_mul_lev <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem scal_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hd
  exact GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair S hd ⟨J.alg0, J.alg⟩ (pos_at_site S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hd)

end GlobalTheory.TwV
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelB.serAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos d ι hι j hj La La' hLa hLa'
  have hr := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hu := GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d
  have hp := GlobalTheory.T.latticeTupleKernel_eq_smul_pullback_classKernel S hDict d j hj La La' hLa hLa'
  have hs := GlobalTheory.T.pullback_scalar_ne_zero_latticeTuple_pair S d j hj La La' hLa hLa'
  exact GlobalTheory.T.thetaSeriesPair_of_pullbackKernelFunction D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam ι hι (J.rho std) hPos d.eM
    (ltC S.g S.hLT) j La La' (hu j La) (hu (j + 1) La') t.B t.χ (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT hPair
    (hr.1 ▸ hj) hLa hLa' (d.sP S j La La') (thCl (X := sysS H X std) t u μ (clsAt X H) j La La') hs hp
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_arithmeticGroup_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Move) := by
  first | exact @GlobalTheory.TwV.Xc.site_move | exact GlobalTheory.TwV.Xc.site_move | (intros; apply GlobalTheory.TwV.Xc.site_move <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.sourceScalar_latticeTuple_constant : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  first | exact @GlobalTheory.TwV.DelA.source_scalar_const | exact GlobalTheory.TwV.DelA.source_scalar_const | (intros; apply GlobalTheory.TwV.DelA.source_scalar_const <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepDeterminantConstant_unit_independent : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  first | exact @GlobalTheory.TwV.DelA.cKs_unit_indep | exact GlobalTheory.TwV.DelA.cKs_unit_indep | (intros; apply GlobalTheory.TwV.DelA.cKs_unit_indep <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transportedFramePolynomial_complex_values_at_point : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La' : (sysS H X std).Lt (j + 1)) (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ), P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) → (∀ y, φ (clsAt X H (j + 1) La'.1 La'.2) y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y) → ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj h La' φ V ∧ MvPolynomial.map ι V = scT d S ι j La'.1 La'.2 • GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La' (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j P)) := by
  first | exact @GlobalTheory.TwV.DelA.transported_frame_realAt | exact GlobalTheory.TwV.DelA.transported_frame_realAt | (intros; apply GlobalTheory.TwV.DelA.transported_frame_realAt <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedForms_operator_degrees_at_kernelSource : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  first | exact @GlobalTheory.TwV.DelA.moved_forms_at_source | exact GlobalTheory.TwV.DelA.moved_forms_at_source | (intros; apply GlobalTheory.TwV.DelA.moved_forms_at_source <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut7.SizeAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w}


open GlobalTheory.ResW in
theorem isUnitarisable (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (ha : 1 ≤ a)
    (π : CuspSub E a) (wt : ℤ) (hw : IsWeight π wt) (w : HeightOneSpectrum (𝓞 E)) (σ) (hσ : π.IsLocComp w σ) :
    GlobalTheory.SmGL.IsUnitarisable ((algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ)).rep := by
  set t : ℝ := ((a : ℝ) - 1 - wt) / 2 with ht
  have hr := GlobalTheory.UnitLocWeight.rexp_eq ha hw
  have hu : (π.twist (nu E (-t))).IsUnitary := by
    have e := (letter_centralExponent E ⟨a, π⟩).2.2.1 ha (-t)
    refine ((rexp_eq_zero_iff_isUnitary E (tw ⟨a, π⟩ (-t)) ha).1.1 ?_)
    rw [e, hr]; ring
  have hU := isUnitarisable_of_isLocComp_cusp E a _ ha hu w _ (hσ.twist (nu E (-t)))
  have hloc : (nu E (-t)).loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ) :=
    GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (-t)) w
  set σ' := σ.twist (CuspSub.locDet a (nu E (-t)) w) (CuspSub.isOpen_ker_locDet (nu E (-t)) w) with hσ'
  have key : (algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ) = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
    have e1 : (((1 - (a : ℝ)) / 2 : ℝ) : ℂ) + (((wt : ℝ) / 2 : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := by
      rw [ht]; push_cast; ring
    unfold algNorm
    rw [IrrGL.nu_nu, e1]
    unfold IrrGL.nu
    rw [IrrGL.tw_of]
    refine IrrGL.of_eq_of.2 ⟨?_⟩
    have e2 : GlobalTheory.SmGL.twist σ.ρ (GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ))) =
        σ'.ρ := by
      ext g v
      change ((GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ)) g : ℂˣ) : ℂ) • σ.ρ g v =
        ((CuspSub.locDet a (nu E (-t)) w g : ℂˣ) : ℂ) • σ.ρ g v
      congr 2
      simp [CuspSub.locDet, hloc, GlobalTheory.SmGL.detChar]
    rw [e2]
    exact .refl _
  rw [key]
  exact GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred) hU

end GlobalTheory.GalCut7.SizeAway

end
end
