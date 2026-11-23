module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle059
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle548
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle099
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle274
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle012
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.Bundle001
import Formalism.LocalToGlobal.PtKOfReal
public import Formalism.SharpRestriction.Divisibility.HookProducts.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle054
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
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
import Mathlib.RingTheory.Etale.Weakly
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

@[expose] public section

section



section
namespace LinearIndependenceOfCarries
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.ReadingExt
open Module
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def finrankCoordinateEquiv (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      (Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL) :=
  LinearEquiv.funCongrLeft D.what₂.LL D.what₂.LL (finCongr (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
def embeddingAtIndex (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (Y.MjH ((i : ℕ) + 1)).V →ₗ[D.what₂.LL] Q.Sx.WL ((i : ℕ) + 1) :=
  (Q.nexp.fi i).e.symm.toLinearMap ∘ₗ jDL Q.Rl Q.F.lv2 i ∘ₗ (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i).toLinearMap ∘ₗ (P.JM.eW i).symm.toLinearMap
def embeddingAtLevel (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] Q.Sx.WL j
  | 0 => 0
  | k + 1 => if h : k < D.R.m then _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex Q ⟨k, h⟩ else 0
theorem embeddingAtLevel_succ_eq_embeddingAtIndex (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel (Y := Y) Q ((i : ℕ) + 1) = _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex Q i := by
  obtain ⟨k, h⟩ := i
  simp [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel, h]
theorem jDL_injective_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Function.Injective (jDL Q.Rl Q.F.lv2 i) := by
  have h : LinearIndependent D.what₂.LL (Q.Rl.toRealDat.bL Q.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)).linearIndependent.map' (Submodule.subtype _)
      (Submodule.ker_subtype _)
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 h
theorem embeddingAtIndex_injective (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Function.Injective (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex (Y := Y) Q i) := by
  intro x y h
  have h1 := (Q.nexp.fi i).e.symm.injective h
  have h2 := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.jDL_injective_alt Q i h1
  exact (P.JM.eW i).symm.injective ((_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i).injective h2)
theorem e_embeddingAtLevel_succ_eq_jDL_of_heq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V)
    (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL)
    (h : HEq ((P.JM.eW i).symm x) y) : (Q.nexp.fi i).e (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel Q ((i : ℕ) + 1) x) = jDL Q.Rl Q.F.lv2 i y := by
  rw [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel_succ_eq_embeddingAtIndex]
  have h1 : _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i ((P.JM.eW i).symm x) = y := comp_cast_of_heq (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i) _ y h
  simp only [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h1]
theorem jDa_injective_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Function.Injective (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel (Y := Y) Q j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < D.R.m := by omega
  have e := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel_succ_eq_embeddingAtIndex (Y := Y) Q ⟨k, hk⟩
  have h := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex_injective (Y := Y) Q ⟨k, hk⟩
  rw [← e] at h
  exact h
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in

theorem embW_comp_algebraMap_eq_fracExt_comp_iotaK (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) :
    (ex.nch.embW w).comp (algebraMap Q.Sx.Ks D.what₂.LL) =
      (fracExt ex.nch w).comp (ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w)) :=
  GlobalTheory.Proof.FractionFieldEmbeddingCompat.embCompat D ex.nch hc Q.Sx.Ks Q.Sx.kKs Q.Sx.kKs_spec w _ rfl
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in

theorem exists_ext_alt (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hk : (Q.Sx.A j).IsKsForm) :
    ∃ e : Q.Sx.WL j →ₛₗ[ex.nch.embW w]
        FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w),
      (∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx j),
        e (∑ k, a k • (show ↥(Q.Sx.A j).WK from f k).1) =
          ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
            (Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm
              ((1 : KB Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[Q.Sx.Ks] f k)) ∧
      (∀ (ι : Type) (v : ι → Q.Sx.WL j), LinearIndependent D.what₂.LL v →
        LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => e (v a))) := by
  letI aK : Algebra Q.Sx.Ks (FractionRing (D.ntw.O (ex.nch.twI w))) := (ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w)).toAlgebra
  letI aE : Algebra (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) := (fracExt ex.nch w).toAlgebra
  haveI : IsScalarTower (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = fracExt ex.nch w (algebraMap _ (FractionRing (D.ntw.O (ex.nch.twI w))) x)
      rw [IsScalarTower.algebraMap_apply (D.ntw.O (ex.nch.twI w)) (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))]
      simp [fracExt, IsFractionRing.map]
  obtain ⟨⟨e, he, -⟩, hC, -⟩ := GlobalTheory.SemilinearExt.semilinearExtension Q.Sx.Ks D.what₂.LL (Q.Sx.WL j) (Q.Sx.A j).WK hk
    (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) (ex.nch.embW w)
    (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_comp_algebraMap_eq_fracExt_comp_iotaK hc Q w) (D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) (Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2)
  exact ⟨e, fun n a f => he (Fin n) a f, fun ι v hv => li_of_carries e (hC e he) hv⟩
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in

theorem embW_Ks_alt (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) (j : ℕ) (a : Q.Sx.Ks)
    (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) :
    (ex.nch.embW w (algebraMap Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m :
        FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) =
      (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
        ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m) := by
  letI aE : Algebra (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) := (fracExt ex.nch w).toAlgebra
  haveI : IsScalarTower (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = fracExt ex.nch w (algebraMap _ (FractionRing (D.ntw.O (ex.nch.twI w))) x)
      rw [IsScalarTower.algebraMap_apply (D.ntw.O (ex.nch.twI w)) (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))]
      simp [fracExt, IsFractionRing.map]
  have e1 : ex.nch.embW w (algebraMap Q.Sx.Ks D.what₂.LL a) =
      algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w))
        (show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) :=
    RingHom.congr_fun (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_comp_algebraMap_eq_fracExt_comp_iotaK hc Q w) a
  rw [e1]
  exact GlobalTheory.SemilinearExt.algebraMap_tmul (O := D.ntw.O (ex.nch.twI w)) _ m

theorem reading_ext_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → ∃ (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm) ∧ (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) ∧ (∀ w j (a : B.Q.Sx.Ks) (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (ex.nch.embW w (algebraMap B.Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m : FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK B.Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m)) ∧ (∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => eM w j ((Y.MjH j).b a))) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B _ _ hc
  have hks : ∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm := by
    intro j h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : k < D.R.m := by omega
    exact GlobalTheory.isKsForm_of_formsIso _ _ (B.Q.nexp.fi ⟨k, hk⟩) (B.fw.ks ⟨k, hk⟩)
  have hE := fun w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.exists_ext_alt hc B.Q w j h1 h2 (hks j h1 h2)
  choose E hE1 hE2 using hE
  classical
  let eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)]
      D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w) := fun w j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then (E w j h.1 h.2).comp (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j) else 0
  have heM : ∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V), eM w j x = E w j h1 h2 (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j x) := by
    intro w j h1 h2 x
    simp only [eM, dif_pos (And.intro h1 h2)]
    rfl
  refine ⟨_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q, eM, fun i x y h => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.e_embeddingAtLevel_succ_eq_jDL_of_heq B.Q i x y h, hks, ?_, fun w j a m => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_Ks_alt hc B.Q w j a m, ?_⟩
  · intro w j h1 h2 x n a f hx
    rw [heM w j h1 h2, hx]
    exact hE1 w j h1 h2 n a f
  · intro w j _ h1 h2
    have hv : LinearIndependent D.what₂.LL (fun a => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j ((Y.MjH j).b a)) :=
      (Y.MjH j).b.linearIndependent.map' (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j) (LinearMap.ker_eq_bot.2 (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.jDa_injective_alt B.Q j h1 h2))
    have h := hE2 w j h1 h2 _ _ hv
    simp only [heM w j h1 h2]
    exact h
end GlobalTheory.CompanionTheory.ReadingExt
end
end
end LinearIndependenceOfCarries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_first_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → ∃ (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm) ∧ (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) ∧ (∀ w j (a : B.Q.Sx.Ks) (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (ex.nch.embW w (algebraMap B.Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m : FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK B.Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m)) ∧ (∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => eM w j ((Y.MjH j).b a))) := by
  first | exact @_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt | exact _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt | (intros; apply _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt <;> assumption)
end
end
end

section



section
namespace GroupAverageFixedPoints
section
noncomputable section
open scoped TensorProduct
open Module
namespace GlobalTheory.CompanionTheory.LatSpan
section Rep
variable {F M Γ : Type} [Field F] [AddCommGroup M] [Module F M] [Group Γ] [Fintype Γ]
variable (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ) (E : Module.End F M)
end Rep
section Ext
variable {O K K'' Fm : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Ext
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Main
variable {LL O K K'' Fm WL Γ : Type} [Field LL] [CharZero LL] [AddCommGroup WL] [Module LL WL]
  [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm] [Group Γ] [Fintype Γ]
end Main
section Lat
variable {LL Oe K'' V T : Type} [Field LL] [NumberField LL] [AddCommGroup V] [Module LL V] [Module (𝓞 LL) V]
  [IsScalarTower (𝓞 LL) LL V] [CommRing Oe] [IsDomain Oe] [Field K''] [Algebra Oe K''] [IsFractionRing Oe K'']
  [AddCommGroup T] [Module K'' T] [Module Oe T] [IsScalarTower Oe K'' T]
end Lat
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
section Form
variable {Ks LL WL : Type} [Field Ks] [Field LL] [Algebra Ks LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {WK : Submodule Ks WL}
  {O K K'' : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Form
section Iso
open Formalism.IndefR.NX Formalism.IndefR.Arith
variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
end Iso
end GlobalTheory.CompanionTheory.LatSpan
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX
section PiLocalization₂
variable {D : D7} (c : NChoice D) (w : D.what₂.places.Pl)
attribute [local instance] algKK
variable {c w}
end PiLocalization₂
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Alg
variable {k A G : Type} [Field k] [Ring A] [Algebra k A] [Group G]
end Alg
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith
section Stage2
variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}
attribute [local instance] algKK
end Stage2
end GlobalTheory.CompanionTheory.LatSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.LatSpan
attribute [local instance] algKK


theorem lattice_of_lifts_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hPin hRec jD eM hN hjD hSum w j hne h1 h2
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have hgrp := P.tied.div.grp
  have hIe : P.I.eG = B.Q.Rl.eG.trans B.Q.cG := hPin.eGtie
  have hC : ∀ h, (Formalism.L2.DIV.idemOf P.A3.A.X).coeff h = ((D.nexp.eLL0 (P.I.eG h) : D.LL0) : D.what₂.LL) := fun h =>
    D.what₂.embLL.injective ((hgrp.e0 h).trans (D.nStage_trivialCharacter_coeff_eq _).symm)
  obtain ⟨e, he1, he2⟩ := stage2 (w := w) hN P.I.eG B.Q.Sx ((i : ℕ) + 1) (B.Q.Rl.FW i) (B.Q.nexp.fi i) (B.fw.ks i)
    (fun s => by rw [hIe]; exact B.Q.nexp.geq i s) (B.Q.nexp.rho _ h1 h2) (B.Q.nexp.chi _ h1 h2)
    (B.Q.nexp.eF _ _ _ h1 h2) (B.Q.nexp.act _ _ _ h1 h2) (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) hC P.P0 P.ψ0⁻¹
    hgrp.lvl0 (fun u hu => by
      obtain ⟨x, hx1, hx2⟩ := hgrp.psi0 u hu (ex.nch.twI w) (ex.nch.sd w)
      exact ⟨x, hx1, hx2⟩)
  have hd := _root_.Formalism.IndefR.finrank_WL_eq_dW B.Q i
  have hForm := isKsForm_of_iso (B.Q.nexp.fi i) (B.fw.ks i)
  have heM : ∀ x, eM w ((i : ℕ) + 1) x = e (jD ((i : ℕ) + 1) x) := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hForm
    have hx : jD ((i : ℕ) + 1) x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    let f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1) := fun k => ⟨b k, hbK k⟩
    have h5 := hSum w ((i : ℕ) + 1) h1 h2 x n a f ha.symm
    rw [h5, ← ha]
    exact (he1 n a f).symm
  have hWg : (B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) =
      B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i := rfl
  have hrange : Set.range (eM w ((i : ℕ) + 1)) =
      (fun y => e ((B.Q.nexp.fi i).e.symm y)) ''
        ((B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) : Set _) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x), ?_, ?_⟩
      · rw [hjD i x _ (heq_cast hd ((P.JM.eW i).symm x))]
        rw [SetLike.mem_coe, hWg]
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Module.finBasis D.what₂.LL _ k).2
      · simp only [LinearEquiv.symm_apply_apply, heM]
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, hWg] at hy
      let Bs := Module.finBasis D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)
      let z : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL := Bs.equivFun ⟨y, hy⟩
      let x := P.JM.eW i (z ∘ Fin.cast hd.symm)
      have hH : HEq ((P.JM.eW i).symm x) z := by
        simp only [x, LinearEquiv.symm_apply_apply]
        exact (heq_cast hd.symm z).symm
      have h6 := hjD i x z hH
      have h7 : Formalism.IndefR.NX.jDL B.Q.Rl B.Q.F.lv2 i z = y := by
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        have h8 := Bs.sum_equivFun ⟨y, hy⟩
        have h9 : ((∑ k, Bs.equivFun ⟨y, hy⟩ k • Bs k : B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i) : Fin (B.Q.Rl.nW i) → D.what₂.LL) = y :=
          congrArg Subtype.val h8
        rw [AddSubmonoidClass.coe_finsetSum] at h9
        exact h9
      refine ⟨x, ?_⟩
      rw [heM]
      change e _ = e ((B.Q.nexp.fi i).e.symm y)
      rw [← h7, ← h6, LinearEquiv.symm_apply_apply]
  refine isLatIn_span (ex.nch.embW w) (integers_embed _) (eM w ((i : ℕ) + 1)) (Y.MjH ((i : ℕ) + 1)).L
    (Y.MjH_good _).2.1 (Y.MjH_good _).2.2 _ ?_
  rw [hrange]
  exact he2
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
end
end GroupAverageFixedPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_second_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  first | exact @_root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | exact _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | (intros; apply _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt <;> assumption)
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
structure IndefiniteRealisationCompatible {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) : Prop where
  stdPsi : Formalism.IndefR.principalLevelFrame.StdPsi Qp.hF Qr.PY ∧ ∀ i, Formalism.IndefR.principalLevelFrame.StdPsi Qp.hF (Qr.PW i)
  rowLoc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt Rc.T.n.gal.lp Q.Rl.θ Qr.PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR Q.F.lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR Q.F.lv2 b))) (fun _ => Q.Rl.e0) Qr.eFT
end Formalism.IndefR
end
end
end

section



section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
  Formalism.L2.RowDataTransport
namespace Formalism.L2.DIV.FunSharpTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
theorem funSharp_pt_alt [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P Dcf Spf Zscf) Cl CHl)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (hkap : RowsHoldKap3 P)
    (hde0 : 0 ≤ (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).de) (hde : (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).de ≤ 1 / 3) :
    D.div.RR.muMax + meanE D (fun e => Real.log (Y.kapR e)) ≤
      (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).x ^ CHl * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).b +
        14 * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).la := by
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs = P.Zs := Q.zs
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData P.S1 := Q.s1
  have hpass : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.muMaxRR ≤
      (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).x ^ CHl * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).b -
        meanLog (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.κ + 14 * (Zscf (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).la :=
    ((_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.extra.passage hde0 hde _ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.extra.fun0).1
  have hmu : D.div.RR.muMax = (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.muMaxRR :=
    (Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie D.div.RR _ _ P.I.eRR hR.sharpRR.lat hR.sharpRR.metric).symm.trans
      (muMax_heq hZs hS1).symm
  have hκ : meanE D (fun e => Real.log (Y.kapR e)) = meanLog (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.κ := by
    rw [(_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.extra.level.2.1]
    exact meanEmb_eq_meanLog _ _ (fun σ => by rw [hkap σ, kap_heq hZs hS1])
  rw [hmu, hκ]
  linarith
end Formalism.L2.DIV.FunSharpTop
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
open Classical in
structure SelectedSideOfRealRecord (R : _root_.Formalism.L2.RecTAlt ex) (P : Rows.RowSideFamily ex)
    {Dcf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.SPer (Dcf Zs)}
    {Zscf : Indef.DefSub P.A3.fam3.amb3 → Indef.IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (RT : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion RT) (hd : _root_.Formalism.L2.HostDatumWithTies R.T.toTiedDataS)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop where
  sel : _root_.Formalism.L2.SelectedSideOfPrimeAbove R Pq
  twQ : ∀ μ : D.what₂.Tup, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) →
    (Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K)).image
      (Host.CT.plMap R.T.ker.seam.iE) = RT.Rl.Q (Qr.tupT μ)
  de : ∀ v, ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK
  de' : ∀ v, ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK'
end
end Formalism.L2
end
end
end
