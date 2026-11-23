module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle536
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle461
public import Formalism.LocalToGlobal.Columns.MtAdWt
import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle567
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.HeightCounting.Fin3.MvLoc

section Three

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
variable {A : DIV.FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} (R : Links.RealDat3 a.D A Ks)

def thrice : type_of% (real3 c R) := (by with_unfolding_all exact ((real3 (a := b) c (iK := alg b iK) (real3 b R)) :))

def thriceY : type_of% (letI := alg c iK; (real3 c R).ioY) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioY :))

def thriceX : type_of% (letI := alg c iK; (real3 c R).ioX) := letI := alg c iK; (by with_unfolding_all exact ((thrice b c R).ioX :))

theorem thriceY_eq : letI := alg c iK; (real3 c R).ioY = thriceY b c R := by
  have h1 := real_ioY c R.toRealDat
  have h2 := real_ioY b R.toRealDat
  have h3 := real_ioY (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceY b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thriceX_eq : letI := alg c iK; (real3 c R).ioX = thriceX b c R := by
  have h1 := real_ioX c R.toRealDat
  have h2 := real_ioX b R.toRealDat
  have h3 := real_ioX (a := b) c (iK := alg b iK) (real b R.toRealDat)
  have h4 : HEq _ (thriceX b c R) := HEq.trans (HEq.trans h1.symm h2) ((by with_unfolding_all exact (h3 :)))
  letI := alg c iK
  exact eq_of_heq ((by with_unfolding_all exact (h4 :)))

theorem thrice_eq : real3 c R = thrice b c R := by
  letI := alg c iK
  exact (by with_unfolding_all exact ((congrArg₂ (DatCopy.setIo (real3 c R)) (thriceY_eq b c R) (thriceX_eq b c R)) :))

theorem inertTransport_twice_heq_direct : HEq (real3 (a := b) c (iK := alg b iK) (real3 b R)) (real3 c R) :=
  (by with_unfolding_all exact ((HEq.symm (heq_of_eq (thrice_eq b c R))) :))

end Three

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

theorem coreJ_heq {k₀ : Formalism.L2.Pj.CoreJ a.D} {k : Formalism.L2.Pj.CoreJ b.D} (h : HEq k (coreJ b k₀)) : HEq (coreJ c k) (coreJ c k₀) := by
  obtain rfl : k = coreJ b k₀ := eq_of_heq h
  exact (by with_unfolding_all exact ((HEq.refl (coreJ c k₀)) :))

theorem realAdelicInertTransport_heq_of_transport (z₀ : Dat a.st I hX T Wt) (Xg : Finset (Gc B px → B.LL)) (tr : TrI B px) (k : Formalism.L2.Pj.CoreJ b.D)
    (i : Algebra k.Q.c.F b.D.what₂.LL) (hi : ∀ y : k.Q.c.F, B.embLL (algebraMap k.Q.c.F b.D.what₂.LL y) = (y : ℂ))
    (R : Links.RealDat3 b.D (famR b.st I hX (usedOf I T Wt) Xg tr) k.Q.c.F) (hXg : Xg = z₀.Xg)
    (htr : tr = z₀.tr) (hc : HEq k (coreJ b z₀.core)) (hR : HEq R (real3 b (iK := z₀.alg) z₀.R)) :
    HEq (real3 c (iK := i) R) (real3 c (iK := z₀.alg) z₀.R) := by
  subst hXg htr
  obtain rfl : k = coreJ b z₀.core := eq_of_heq hc
  have ha : i = (by with_unfolding_all exact ((alg b z₀.alg) :)) :=
    Algebra.algebra_ext _ _ fun y => (by with_unfolding_all exact ((B.embLL.injective ((hi y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))) :
      _ = (@algebraMap _ _ _ _ z₀.alg ((by with_unfolding_all exact (y :))) : B.LL)) :))
  subst ha
  have hR' : R = (by with_unfolding_all exact ((real3 b (iK := z₀.alg) z₀.R) :)) := eq_of_heq ((by with_unfolding_all exact (hR :)))
  subst hR'
  exact (by with_unfolding_all exact ((inertTransport_twice_heq_direct b c (iK := z₀.alg) z₀.R) :))

end Copy

section Move

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}
  {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o o' : q.Over}

theorem coreP_transfer {Z Z' : w.Lt} (s : SameGrp (B := B) (C := w.C) Z Z') {z : Dat (w.st Z) w.I hX T Wt} (h : CoreP z) :
    CoreP (w := w) (Z := Z') (Dat.transfer (B := B) (C := w.C) (a := Z) (b := Z') s z) := by
  unfold CoreP at h ⊢
  obtain ⟨laws, canon, dim, pb⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact Mv.lawsCore_tr (a := Z) Z' laws
  · with_unfolding_all exact canon
  · with_unfolding_all exact dim
  · with_unfolding_all exact pb

theorem copy_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) {m : Moved o} {m' : Moved o'} (hm : m.Copy)
    (e : m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z) : m'.Copy := by
  have h1 := coreJ_heq (a := Z₀) o.Z o'.Z (k₀ := z₀.core) (k := m.z.core) ((by with_unfolding_all exact (hm.core :)))
  have h2 := realAdelicInertTransport_heq_of_transport (a := Z₀) o.Z o'.Z z₀ m.z.Xg m.z.tr m.z.core m.z.alg m.z.alg_eq m.z.R m.Xg m.tr ((by with_unfolding_all exact (hm.core :))) ((by with_unfolding_all exact (hm.R :)))
  have e1 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.core) e
  have e2 := congr_arg_heq (fun z : Dat (w.st o'.Z) w.I hX T Wt => z.R) e
  have h3 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).core (coreJ (a := Z₀) o'.Z z₀.core) := (by with_unfolding_all exact (h1 :))
  have h4 : HEq (Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z).R (real3 (a := Z₀) o'.Z (iK := z₀.alg) z₀.R) := (by with_unfolding_all exact (h2 :))
  exact ⟨(by with_unfolding_all exact ((HEq.trans e1 h3) :)), (by with_unfolding_all exact ((HEq.trans e2 h4) :))⟩

theorem exists_moved_transfer (s : SameGrp (B := B) (C := w.C) o.Z o'.Z) (m : Moved o) (hm : m.Coh) :
    ∃ m' : Moved o', m'.z = Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z ∧ m'.Coh := by
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C o.Z o'.Z _ _ _ _ _ _ _ _ m.z.alg _ m.z.R.toRealDat m.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := Mv.pkT_tr (a := o.Z) o'.Z (iK := m.z.alg) m.z.F m.y y' hy m.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C o.Z o'.Z _ _ _ _ _ _ _ _ _ m.z.alg _ m.z.R m.z.F).1
  have hW := Dat.nonzeroIndexPlaces_transferAlongSameFiniteGroup (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
  letI : Algebra m.z.core.Q.c.F (Late.D o'.Z).what₂.LL := alg (a := o.Z) o'.Z m.z.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% m.t.tA) = m.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have b2 := HEq.trans hy.PY hm.PY
  have b3 := HEq.trans hy.PW hm.PW
  have b4 := HEq.trans a2 hm.rep
  have b5 := fun c => HEq.trans (a3 c) (hm.jE c)
  have b6 := fun c => HEq.trans (a4 c) (hm.jM c)
  have b7 := fun c => HEq.trans (a5 c) (hm.jX c)
  have b8 := HEq.trans a6 hm.eW
  have b9 := HEq.trans a7 hm.jMt
  have c1 := fun j v => (he j v).trans (m.eta j ((by with_unfolding_all exact (v :))))
  have c2 := fun F0 => (hW F0).symm.trans (m.W1 ((by with_unfolding_all exact (F0 :))))
  have c3 := fun c u => HEq.trans (heq_of_eq (congrArg (fun r : type_of% m.t.tA => (r c u).j) hA)) (m.tA c u)
  refine ⟨{ z := Dat.transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.z
            intersectionNumber_baseChange := (by with_unfolding_all exact ((Dat.holds_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.intersectionNumber_baseChange) :))
            exAt := (by with_unfolding_all exact ((Dat.exAt_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.exAt) :))
            inGeo := (by with_unfolding_all exact ((Dat.inGeo_transfer (B := B) (C := w.C) (a := o.Z) (b := o'.Z) s m.inGeo) :))
            Xg := (by with_unfolding_all exact (m.Xg :))
            tr := (by with_unfolding_all exact (m.tr :))
            core := fun h => coreP_transfer s (m.core h)
            eta := (by with_unfolding_all exact (c1 :))
            W1 := (by with_unfolding_all exact (c2 :))
            y := (by with_unfolding_all exact ((Mv.hd3 (a := o.Z) o'.Z (iK := m.z.alg) m.y y') :))
            tup := (by with_unfolding_all exact (m.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := (by with_unfolding_all exact (c3 :)) }, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (hm.tupT :))
  · exact (by with_unfolding_all exact (b2 :))
  · exact (by with_unfolding_all exact (b3 :))
  · exact (by with_unfolding_all exact (b4 :))
  · exact (by with_unfolding_all exact (b5 :))
  · exact (by with_unfolding_all exact (b6 :))
  · exact (by with_unfolding_all exact (b7 :))
  · exact (by with_unfolding_all exact (b8 :))
  · exact (by with_unfolding_all exact (b9 :))

end Move

theorem exists_moved_loc : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : LocAll (lay0 (Dof x))), ∃ m : Moved (oL x L), m.z = datL x L ∧ m.Copy ∧ m.Coh := by
  intro K B f T w P x L
  obtain ⟨m, h1, h2⟩ := exists_moved_transfer (o := x.o) (o' := oL x L) (sameL x L) x.m x.coh
  exact ⟨m, h1, copy_transfer (o := x.o) (o' := oL x L) (sameL x L) x.copy h1, h2⟩

end GlobalTheory.HeightCounting.Fin3.MvLoc

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.LevCmp
open Formalism.L2.DIV GlobalTheory.CoefModel

section Gen2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem match_mtwRat (γ : GQ L n) : (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
    ((Formalism.L2.Col.mtwRat (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom :=
  (congrArg Units.val (Formalism.L2.Col.mtwInc_mtwRatFun γ)).symm

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; subst h; rfl

end Gen2


end GlobalTheory.LevCmp

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem overPl_subsingleton {L : Type} [Field L] (w : HeightOneSpectrum (𝓞 L)) :
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) | NG.OverPl w v}.Subsingleton := by
  intro v hv v' hv'
  exact HeightOneSpectrum.ext (hv.symm.trans hv')

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem gPl_union_qPl_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  intro D η
  have hS : (⋃ k : Fin 2, placesOver D.host.E (D.host.g k)).Finite :=
    Set.finite_iUnion fun k => placesOver_finite_of_ne_zero _ _ (D.host.g_prime k).ne_zero
  have hR : {w | ¬ η.UnrAt w}.Finite := GlobalTheory.Mem.UnrAe.finite_ramified η
  refine Set.Finite.union ?_ ?_
  · refine (hS.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨w, hw, k, hk⟩
    exact Set.mem_biUnion (Set.mem_iUnion.2 ⟨k, hk⟩) hw
  · refine (hR.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨_, w, hw, hu⟩
    exact Set.mem_biUnion (x := w) hu hw

end GlobalTheory.LevCmp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.CompRamified

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← WithZero.exp_log hx0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem exists_int_locK_ne (χ : HChar L) (t : SplitPlace L) (ht : χ.TameAt t.w) (hr : ¬ χ.UnrAt t.w) :
    ∃ b : 𝓞 (maximalRealSubfield L), b ∉ t.v.asIdeal ∧ ∃ k : Lˣ,
      (k : L) = ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b : 𝓞 L) : L) ∧ χ.locK t.w k ≠ 1 := by
  classical
  simp only [HChar.UnrAt, not_forall] at hr
  obtain ⟨x, hx, hne⟩ := hr
  have hx' : Valued.v (x : t.w.adicCompletion L) = 1 := hx
  obtain ⟨a, ha⟩ := adic_exists_approx t.w (x : t.w.adicCompletion L) (le_of_eq hx')
  obtain ⟨b, hb⟩ := adic_exists_approx t.v (t.i (a : L)) (t.split_le_one a)
  set c : 𝓞 L := algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b with hcdef
  have hac : a - c ∈ t.w.asIdeal := by
    show a - c ∈ t.ideal
    rw [t.split_mem_ideal]
    have e : t.i ((c : 𝓞 L) : L) =
        algebraMap (𝓞 (maximalRealSubfield L)) (t.v.adicCompletion (maximalRealSubfield L)) b := by
      rw [hcdef, split_coe_algebraMap, AlgHom.commutes]; rfl
    have e2 : ((a - c : 𝓞 L) : L) = (a : L) - (c : L) := by push_cast; rfl
    rw [e2, map_sub, e]
    exact hb
  have hval : ∀ z : 𝓞 L, Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) z) = t.w.valuation L (z : L) := fun z => by
    exact adic_valued_algebraMap (R := 𝓞 L) (K := L) t.w (z : L)
  have hxc : Valued.v ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) < 1 := by
    have e : (x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c =
        ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ a) + algebraMap (𝓞 L) _ (a - c) := by
      rw [map_sub]; ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha ?_)
    rw [hval]
    exact (t.w.valuation_lt_one_iff_mem (a - c)).2 hac
  have hc1 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) = 1 := by
    have e : algebraMap (𝓞 L) (t.w.adicCompletion L) c =
        (x : t.w.adicCompletion L) - ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) := by ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hx']; exact hxc)]
    exact hx'
  have hbv : b ∉ t.v.asIdeal := by
    intro hm
    have h1 := (t.split_alg_mem b).2 hm
    have h2 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) < 1 := by
      rw [hval]; exact (t.w.valuation_lt_one_iff_mem c).2 h1
    rw [hc1] at h2
    exact lt_irrefl _ h2
  have hc0 : (c : L) ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 L) (t.w.adicCompletion L) c = 0 := by
      show algebraMap L (t.w.adicCompletion L) (c : L) = 0
      rw [h0, map_zero]
    rw [this, map_zero] at hc1
    exact zero_ne_one hc1
  refine ⟨b, hbv, Units.mk0 (c : L) hc0, rfl, ?_⟩
  intro h1
  apply hne
  set y : (t.w.adicCompletion L)ˣ := atFin t.w (Units.mk0 (c : L) hc0) with hydef
  have hy : (y : t.w.adicCompletion L) = algebraMap (𝓞 L) (t.w.adicCompletion L) c := rfl
  have hu : IsUnitAt t.w (y * x⁻¹) := by
    show Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ)) : t.w.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hc1, hx', inv_one, mul_one]
  have hsub : Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : ((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1 =
        -((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) * (x : t.w.adicCompletion L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hy]
      field_simp
      ring
    rw [e, map_mul, Valuation.map_neg, map_inv₀, hx', inv_one, mul_one]
    exact le_exp_neg_one_of_lt_one' hxc
  have h2 := ht (y * x⁻¹) hu hsub
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [← h2]
  exact h1

end Gen

end GlobalTheory.CompRamified


open GlobalTheory.CompRamified in
theorem GlobalTheory.CompRamified.exists_unit_ne_one : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  classical
  intro D cf j ξH s ξ htr hta hq hc
  set η := cf.mu0 j * ξH with hη
  have htame : ∀ u, η.TameAt u := fun u x hx h1 => by
    change (cf.mu0 j).loc u x * ξH.loc u x = 1
    rw [(cf.isMu0 j).tame u x hx h1, hta u x hx h1, one_mul]
  have htriv : ∀ k : (D.host.F)ˣ, ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, η.locK P (upF D.host.F k) = 1 := fun k => by
    have h1 := (cf.isMu0 j).triv.1 s.v k
    have h2 := htr.1 s.v k
    rw [GlobalTheory.GalToHecke.resFin_eq] at h1 h2
    rw [hη]
    show ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, ((cf.mu0 j).locK P (upF D.host.F k) * ξH.locK P (upF D.host.F k)) = 1
    rw [Finset.prod_mul_distrib, h1, h2, one_mul]
  obtain ⟨-, w, hw, hram⟩ := hq
  have key : ∃ b : 𝓞 (maximalRealSubfield D.host.E), b ∉ s.v.asIdeal ∧ ∃ k : (D.host.E)ˣ,
      (k : D.host.E) = ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) ∧
        η.locK w k ≠ 1 := by
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · subst e
      exact exists_int_locK_ne η s (htame _) hram
    · have e2 := (GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w e).1
      have h := exists_int_locK_ne η (GlobalTheory.TypeTame.conjSP s) (e2 ▸ htame _) (e2 ▸ hram)
      rw [e2] at h
      exact h
  obtain ⟨b, hbv, k, hk, hne⟩ := key
  have hb0 : ((b : maximalRealSubfield D.host.E) : D.host.E) ≠ 0 := by
    intro h0
    apply hbv
    have : (b : maximalRealSubfield D.host.E) = 0 := by exact_mod_cast h0
    have : b = 0 := RingOfIntegers.coe_eq_zero_iff.mp this
    rw [this]; exact s.v.asIdeal.zero_mem
  have hF0 : (b : maximalRealSubfield D.host.E) ≠ 0 := fun h => hb0 (by rw [h]; rfl)
  set f : (D.host.F)ˣ := Units.mk0 (b : maximalRealSubfield D.host.E) hF0 with hfdef
  have hfk : upF D.host.F f = k := by
    apply Units.ext
    rw [hk]
    rfl
  have hsw : η.locK s.w k ≠ 1 := by
    by_cases e : s.w = w
    · rwa [e]
    have hc' : IsConjPl D.host w s.w := (GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw).resolve_left e
    have hab : aboveF (L := D.host.E) D.host.F s.v = {s.w, w} := by
      ext P
      rw [GlobalTheory.GalToHecke.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hP
        have hov : NG.OverPl P s.v := by rw [← hP]; rfl
        rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s P hov with e' | e'
        · exact Or.inl e'.symm
        · exact Or.inr (GlobalTheory.HeightCounting.TrueConjLabels.eq_of_isConjPl e' hc')
      · rintro (rfl | rfl)
        · exact HeightOneSpectrum.ext s.w_under
        · exact HeightOneSpectrum.ext hw
    have h := htriv f
    rw [hab, Finset.prod_pair e, hfk] at h
    intro h1
    rw [h1, one_mul] at h
    exact hne h
  refine ⟨Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k, ?_, ?_⟩
  · show Valued.v (s.i (k : D.host.E)) = 1
    rw [hk, s.split_val_alg]
    refine le_antisymm (s.v.valuation_le_one b) (not_lt.1 fun h => hbv ((s.v.valuation_lt_one_iff_mem b).1 h))
  · rw [hc.2 k]
    exact hsw
end
end
