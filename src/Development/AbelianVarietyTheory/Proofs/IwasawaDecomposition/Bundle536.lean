module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle521
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle511
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle510
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle496
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle462
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle447
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle524
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mv

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

def sameGrp {f : Fr B.toPre} (h : GrpTrue a.N f) (h' : GrpTrue b.N f) : SameGrp a b where
  e k := (by with_unfolding_all exact ((plEquiv a.N.naut b.N.naut k) :))
  pl k v := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv h h' k v) :))
  e0 g := (by with_unfolding_all exact ((h.typeIdempotent_coeff_across_layers h' g) :))

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by with_unfolding_all exact ((alg b z.alg) :))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

theorem levOf_tr {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) : LevOf b.st I U (levCh b L) := by
  constructor
  case is => exact (by with_unfolding_all exact ((levIs_tr b h.is) :))
  case C => exact (by with_unfolding_all exact ((congrArg (chFr b) h.C) :))
  case xiH => exact (by with_unfolding_all exact (h.xiH :))
  case Pg => exact (by with_unfolding_all exact (h.Pg :))
  case Q => exact (by with_unfolding_all exact (h.Q :))
  case beta => exact (by with_unfolding_all exact (h.beta :))

theorem goodSet_tr (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : (fun g => a.D.ntypes.e0.coeff (eR g)) = fun g => b.D.ntypes.e0.coeff ((eR.trans s.iso) g) :=
    funext fun g => (s.e0 (eR g)).symm
  refine (goodSet_iff b.st (px := px) _ Xg).2 ?_
  exact (congrArg (fun c : Gc B px → ℂ => (∀ χ : Gc B px → B.LL, χ ∈ Xg ↔ IsAbsIrrChar χ ∧
    ∑ g : Gc B px, c g * B.embLL (χ g) = B.embLL (χ 1)) ∧ ∀ g, B.embLL ((idemOf Xg).coeff g) = c g) e).mp
    ((goodSet_iff a.st (px := px) eR Xg).1 h)

def cpDat (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((alg b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := cpR b z)
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((geoHalf b (iK := z.alg) z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr b (iK := z.alg) s z.pins) :)))
    (lev := (by with_unfolding_all exact ((levOf_tr b z.lev) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((goodSet_tr b s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

theorem lawsCore_tr {K : Formalism.L2.Pj.Core a.D} (h : Formalism.L2.Pj.LawsCore K) : Formalism.L2.Pj.LawsCore (core b K) := by
  constructor
  case toLawsM => exact (by with_unfolding_all exact ((lawsM_tr b h.toLawsM) :))
  case cuspMul => exact (by with_unfolding_all exact (h.cuspMul :))
  case latZ => exact (by with_unfolding_all exact (h.latZ :))
  case cuNe => exact (by with_unfolding_all exact (h.cuNe :))
  case expo => exact (by with_unfolding_all exact (h.expo :))

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)

theorem cp_holds (h : Holds z.R z.F) : Holds (cpDat b s z).R (cpDat b s z).F := (by with_unfolding_all exact ((holds_tr b (iK := z.alg) h) :))

theorem cp_exAt (h : z.R.toRealDat.ExAt) : (cpDat b s z).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr b (iK := z.alg) h) :))

theorem cp_inGeo (h : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (cpDat b s z).geo := (by with_unfolding_all exact ((inGeo_tr b (iK := z.alg) h) :))

theorem cp_canon (h : z.core.Q.Canon) : (cpDat b s z).core.Q.Canon := (by with_unfolding_all exact (h :))

theorem forcedContentPlaces_eq_transport_sameFiniteGroup (F0) : (cpDat b s z).W1 F0 = z.W1 ((F0)) :=
  (by with_unfolding_all exact ((congrArg (fun X : Cx.CxData (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).fam3.amb3 =>
    {w : B.places.Pl | ∃ j, ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
    (X.data z.F.cr false).Iw j (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
    Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
              (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
        (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ ((F0) : HeightOneSpectrum (𝓞 a.D.what₂.LL) → Fin a.D.R.m → ℝ) w' j ≠ 0})
    (toCx3_eq b (iK := z.alg) z.R z.F).symm) : _))

section Read

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def fixTup {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} (y : Hd R) (y' : HdB b R) : HdB b R :=
  letI := alg b iK
  { y' with tup := (by with_unfolding_all exact (y.tup :)), tupT := (by with_unfolding_all exact (y.tupT :)), tupT_tup := (by with_unfolding_all exact (y.tupT_tup :)), tup0 := (by with_unfolding_all exact (y.tup0 :)) }

theorem fixTup_same {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} {y : Hd R} {y' : HdB b R} (h : Same b y y') :
    Same b y (fixTup b y y') :=
  ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact (h.PY :)), (by with_unfolding_all exact (h.PW :))⟩

variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat)
  (y' : HdB b R.toRealDat)

def hd3 : letI := alg b iK; Hd (real3 b R).toRealDat := (by with_unfolding_all exact ((fixTup b y y') :))

def mCp (mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G) : Bool → b.D.what₂.Tup → Mat1 b.D.what₂.LL G := (by with_unfolding_all exact (mA :))

def pCp (p : PkD a.D G) : PkD b.D G := (by with_unfolding_all exact (p :))

theorem dall_tr {n : ℕ} (h : n = Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
    (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))))) : letI := alg b iK
    n = Module.finrank ℂ (Mult.Mult (real3 b R).θ ((real3 b R).MY 0)
      (levS _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))
      (levChi _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))) := by
  exact (congrArg (fun m : type_of% (@Mult.Mult a.D) => n = Module.finrank ℂ (m R.θ (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))))
    (mult_eq b a)).mp h



theorem pkT_tr (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (GlobalTheory.T.typeRepresentativesParts_otherLaterStages B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.T.chainComparison_transfer_otherLaterStages B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Read



theorem exists_moved : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Holds z₀.R z₀.F →
    z₀.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z₀.geo → GrpTrue Z₀.N f → o.Fits → ∃ m : Moved o, m.Copy ∧ m.Coh := by
  intro B f T w Z₀ hX Wt z₀ q o h1 h2 h3 h4 h5
  have s : SameGrp (B := B) (C := w.C) Z₀ o.Z := sameGrp o.Z h4 h5.grp
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C Z₀ o.Z _ _ _ _ _ _ _ _ z₀.alg _ z₀.R.toRealDat q.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_tr (a := Z₀) o.Z (iK := z₀.alg) z₀.F q.y y' hy q.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C Z₀ o.Z _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).1
  letI : Algebra z₀.core.Q.c.F (Late.D o.Z).what₂.LL := alg (a := Z₀) o.Z z₀.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% q.t.tA) = q.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hs := fixTup_same (a := Z₀) o.Z (iK := z₀.alg) hy
  refine ⟨{ z := cpDat (a := Z₀) o.Z s z₀
            intersectionNumber_baseChange := cp_holds (a := Z₀) o.Z s z₀ h1
            exAt := cp_exAt (a := Z₀) o.Z s z₀ h2
            inGeo := cp_inGeo (a := Z₀) o.Z s z₀ h3
            Xg := rfl
            tr := rfl
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := Z₀) o.Z h.1) :)), cp_canon (a := Z₀) o.Z s z₀ h.2.1, (by with_unfolding_all exact (h.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2 :))⟩
            eta := (by with_unfolding_all exact (he :))
            W1 := (by with_unfolding_all exact ((forcedContentPlaces_eq_transport_sameFiniteGroup (a := Z₀) o.Z s z₀) :))
            y := (by with_unfolding_all exact ((hd3 (a := Z₀) o.Z (iK := z₀.alg) q.y y') :))
            tup := (by with_unfolding_all exact (q.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((heq_of_eq (congrArg (fun r : type_of% q.t.tA => (r c ((u))).j) hA)) : _)) }, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := Z₀) o.Z z₀.core)) :))
  · exact (by with_unfolding_all exact ((HEq.refl (real3 (a := Z₀) o.Z (iK := z₀.alg) z₀.R)) :))
  · exact (by with_unfolding_all exact ((HEq.refl q.y.tupT) :))
  · exact (by with_unfolding_all exact (hy.PY :))
  · exact (by with_unfolding_all exact (hy.PW :))
  · exact (by with_unfolding_all exact (a2 :))
  · exact (by with_unfolding_all exact (a3 :))
  · exact (by with_unfolding_all exact (a4 :))
  · exact (by with_unfolding_all exact (a5 :))
  · exact (by with_unfolding_all exact (a6 :))
  · exact (by with_unfolding_all exact (a7 :))

end GlobalTheory.Mem.R3.Rw.Mv

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr

theorem heq_fin_apply {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : g i' = f i := by
  subst hm
  cases h
  exact congrArg g (Fin.ext hi.symm)

theorem heq_fin_mid {m m' : ℕ} {f : Fin m → ℕ} {g : Fin m' → ℕ} (h : HEq g f) (hm : m' = m) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') (k : Fin (f i)) : ∃ k' : Fin (g i'), (k : ℕ) = k' :=
  ⟨⟨k, lt_of_lt_of_eq k.2 (heq_fin_apply h hm i i' hi).symm⟩, rfl⟩

theorem heq_mid {α β : Type} (h : β = α) (a : α) : ∃ b : β, HEq b a := ⟨cast h.symm a, cast_heq _ _⟩



theorem ext_trans {B₁ B₂ B₃ : Base} {f₁ f₂ f₃ T₁ T₂ T₃} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {w₃ : ColW B₃ f₃ T₃} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {Z₃ : w₃.Lt} {h₁ h₂ h₃ W₁ W₂ W₃} {z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁} {z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂} {z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃} (e₁₂ : Enl B₁ B₂) (e₂₃ : Enl B₂ B₃) (x : Ext z₁ z₂) (y : Ext z₂ z₃) :
    Ext z₁ z₃ := by
  have hmm : (w₂.st Z₂).toD7.R.m = (w₁.st Z₁).toD7.R.m := congrArg (fun P : Pre => P.R.m) e₁₂.1
  have hm : ∀ i : Fin (w₁.st Z₁).toD7.R.m, ∃ i' : Fin (w₂.st Z₂).toD7.R.m, (i : ℕ) = i' :=
    fun i => ⟨⟨i, lt_of_lt_of_eq i.2 hmm.symm⟩, rfl⟩
  refine @Ext.mk B₁ B₃ f₁ f₃ T₁ T₃ w₁ w₃ Z₁ Z₃ h₁ h₃ W₁ W₃ z₁ z₃ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact HEq.trans y.H x.H
  · exact HEq.trans y.l x.l
  · exact HEq.trans y.c x.c
  · exact HEq.trans y.Dw x.Dw
  · exact HEq.trans y.Xo x.Xo
  · exact HEq.trans y.U x.U
  · exact HEq.trans y.V x.V
  · exact HEq.trans y.dict x.dict
  · exact HEq.trans y.mu x.mu
  · exact HEq.trans y.Kf x.Kf
  · exact HEq.trans y.cE x.cE
  · exact HEq.trans y.chiW x.chiW
  · exact HEq.trans y.x₀ x.x₀
  · exact HEq.trans y.iota x.iota
  · exact HEq.trans y.ψ x.ψ
  · exact HEq.trans y.θ x.θ
  · exact HEq.trans y.βW x.βW
  · exact HEq.trans y.βY x.βY
  · exact HEq.trans y.nW x.nW
  · exact HEq.trans y.βV x.βV
  · exact HEq.trans y.ΛV x.ΛV
  · exact HEq.trans y.ΛW x.ΛW
  · exact HEq.trans y.Pg x.Pg
  · exact HEq.trans y.eG x.eG
  · exact HEq.trans y.Sb x.Sb
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.BV i i' hi'
    have b := y.BV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.1 a.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.1 a.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.1 a.2.2.2.2.1
    exact HEq.trans b.2.2.2.2.2 a.2.2.2.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.MW i i' hi'
    have b := y.MW i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.1) (a.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.1) (a.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.1) (a.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.1) (a.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.1) (a.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.1) (a.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.2.1)
    refine And.intro ?_ ?_
    · exact HEq.trans (b.2.2.2.2.2.2.2.2.2.1) (a.2.2.2.2.2.2.2.2.2.1)
    intro φ φ'' hφ
    refine Exists.elim (heq_mid (GlobalTheory.T.cuspFormType_eq_at_corresponding_lifts z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    exact HEq.trans (b.2.2.2.2.2.2.2.2.2.2 φ' φ'' (HEq.trans hφ hφ'.symm)) (a.2.2.2.2.2.2.2.2.2.2 φ φ' hφ')
  · intro i i'' h φ φ'' hφ k k'' hk
    refine Exists.elim (hm i) fun i' hi' => ?_
    refine Exists.elim (heq_mid (GlobalTheory.T.cuspFormType_eq_at_corresponding_lifts z₁ z₂ e₁₂ x i i' hi') φ) fun φ' hφ' => ?_
    refine Exists.elim (heq_fin_mid x.nW hmm i i' hi' k) fun k' hk' => ?_
    exact Eq.trans (y.forms i' i'' (hi'.symm.trans h) φ' φ'' (HEq.trans hφ hφ'.symm) k' k'' (hk'.symm.trans hk)) (x.forms i i' hi' φ φ' hφ' k k' hk')
  · intro v v'' hB
    refine Exists.elim (GlobalTheory.T.exists_intermediate_coefficientPlace_between (w₁.D Z₁) (w₂.D Z₂) (w₃.D Z₃) e₂₃.2.2.2 v v'' hB) fun v' h => ?_
    exact Iff.trans (x.W1 v v' h.1) (y.W1 v' v'' h.2)
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.cV i i' hi'
    have b := y.cV i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    exact HEq.trans b.2 a.2
  · exact HEq.trans y.pb x.pb
  · exact HEq.trans y.ΛY x.ΛY
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.κ i i' hi'
    have b := y.κ i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    exact Eq.trans b.2.2 a.2.2
  · intro i i'' h
    refine Exists.elim (hm i) fun i' hi' => ?_
    have a := x.ref i i' hi'
    have b := y.ref i' i'' (hi'.symm.trans h)
    refine And.intro ?_ ?_
    · exact HEq.trans b.1 a.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.1 a.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.1 a.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.1 a.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.1 a.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.2.1 a.2.2.2.2.2.1
    refine And.intro ?_ ?_
    · exact HEq.trans b.2.2.2.2.2.2.1 a.2.2.2.2.2.2.1
    exact HEq.trans b.2.2.2.2.2.2.2 a.2.2.2.2.2.2.2
  · intro i i'' h ok ok'' φ φ'' C
    refine Exists.elim (hm i) fun i' hi' => ?_
    have hv : HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs := by
      have a := heq_of_eq z₂.lev.Pg.symm
      have b := heq_of_eq z₁.lev.Pg
      exact HEq.trans (HEq.trans a x.Pg) b
    have L := GlobalTheory.T.referenceTupleLiftForms_pass_to_coeffEnlargement w₁ w₂ W₁ W₂ e₁₂ hv (GlobalTheory.T.tameCharacters_typePrimes_eq_of_extension z₁ z₂ e₁₂ x) ((i : ℕ) + 1) ((i' : ℕ) + 1) (congrArg (· + 1) hi')
    refine Exists.elim (L.2 φ) fun φ' C' => ?_
    have ok' : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 ((i' : ℕ) + 1)).Ok := Formalism.L2.Col.mtKOk _ _ _ _ h₂ _
    have a := x.jL i i' hi' ok ok' φ φ' C'
    have b := y.jL i' i'' (hi'.symm.trans h) ok' ok'' φ' φ'' fun d' d'' hd => by
      refine Exists.elim (heq_mid L.1.symm d') fun d hd' => ?_
      exact HEq.trans (C d d'' (HEq.trans hd hd'.symm)) (HEq.symm (C' d d' hd'.symm))
    exact HEq.trans b a

theorem std_copy_and_ext_trans : (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt), z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std) ∧ ∀ (B₁ B₂ B₃ : Base) f₁ f₂ f₃ T₁ T₂ T₃ (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (w₃ : ColW B₃ f₃ T₃) (Z₁ : w₁.Lt) (Z₂ : w₂.Lt) (Z₃ : w₃.Lt) h₁ h₂ h₃ W₁ W₂ W₃ (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂) (z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃), Enl B₁ B₂ → Enl B₂ B₃ → Ext z₁ z₂ → Ext z₂ z₃ → Ext z₁ z₃ :=
  ⟨std_copy, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁₂ e₂₃ x y => ext_trans e₁₂ e₂₃ x y⟩

end GlobalTheory.Mem.R3.Rw.StdTr
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.baseLevelLift_extendedData_eq_map_smallerField : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∃ hP : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).P = ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P.map e.toMonoidHom, ∀ h : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P, ((((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).ψ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).ψ h : (w.st Z).toD7.what₂.LL)) := by
  exact @GlobalTheory.Mem.R3.DefLatBC.lev_ext
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.baseLevelLiftMatrix_solves_relation_extendedData_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, (z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 *ᵥ x)) = (z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x)) := by
  exact @GlobalTheory.Mem.R3.LiftMatBase.baseLevelLiftMatrix_solves_relation_extendedData
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.typePrimeFiniteGroup_eq_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ e : Gc B w.px ≃* Gc B' w'.px, ∀ g, HEq (e g) g) := by
  exact @GlobalTheory.Mem.R3.DefLatBC.gc_ext
end
