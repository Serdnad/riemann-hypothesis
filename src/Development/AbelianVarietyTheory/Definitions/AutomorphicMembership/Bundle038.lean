module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsUniqueTransUnit
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InjectiveOfFlatLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad.LineTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


variable {Dw} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

variable {D : D7} {A : Amb D}

end GlobalTheory.ShFam.Pad.LineTest
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal

namespace GlobalTheory.ShFam.Pad

def inclQb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) : c.F →+* Qb :=
  c.F.val.toRingHom.codRestrict (algebraicClosure ℚ ℂ) fun a =>
    haveI := c.fin
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom c.F.val)


open Classical in
def carry {F : Type} [Field F] (f g : F →+* Qb) : Qb →+* Qb :=
  haveI : Nonempty (Qb →+* Qb) := ⟨RingHom.id Qb⟩
  if f = g then RingHom.id Qb else Classical.epsilon fun σ => σ.comp f = g

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

def ioAt (p : ℕ) [Fact p.Prime] (y : Pt s) : Qb →+* ℂ_[p] := (iotaP p).comp (carry y.fK (inclQb κ.c))

def normDetIo (p : ℕ) [Fact p.Prime] (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (io : Qb →+* ℂ_[p]) (a : Qb) : ℝ :=
  ‖io a‖ * Real.exp (∑ i : Fin N, y.lnRoot io p b (DV.tauEmb D τ) i)


open Classical in
def normDetAt (p : ℕ) (b : Bool) (τ : D.what₂.Tau) (y : Pt s) (a : Qb) : ℝ :=
  if h : p.Prime then (haveI := Fact.mk h; normDetIo s p b τ y (ioAt s p y) a) else 1

def padAt {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
    (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s)
    (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp) : PadPkg D N j s.Comp jC ng :=
  { padOf s L G M F I with
    normDetT := fun p τ (y : Pt s) => normDetAt s p true τ y (F.sv τ y)
    normDetH := fun p τ (y : Pt s) => normDetAt s p false τ y (F.sv τ y) }

section Unfold

variable {jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)} {ng : NgPkg} (L : LocSt D N j ng)
  (G : GlobSt fun p => (L.loc p).Mdl) (M : AdmSt D N j jC) (F : FlatSt s) (I : ArIn D.what₂.Tau N (D.R.f * N) s.Comp)

end Unfold

end GlobalTheory.ShFam.Pad
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

section Generic

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {Λ : Type} [CommRing Λ] [StarRing Λ]
  (P : Point p (fldVal C) ↥(intO ↥C.S) Λ)

def tateIncl : P.T →+ P.V := (TensorProduct.mk ℤ_[p] ↥C.S P.T 1).toAddMonoidHom

def htMap : P.T →+ P.OmC := P.inclOm.toAddMonoidHom.comp P.al₀.toAddMonoidHom

def lieSpan : Submodule ↥C.S P.V := Submodule.span ↥C.S (P.latLie : Set P.V)

theorem span_tateIncl : Submodule.span ↥C.S (Set.range (tateIncl P)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul c t =>
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨t, rfl⟩)

theorem alC_tateIncl (t : P.T) : P.alC (tateIncl P t) = htMap P t := P.alC_tmul 1 t

end Generic

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

def htPt {Z : ct.Mdl} (y : ct.Pt Z) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Point p (fldVal y.C) ↥(intO ↥y.C.S) (𝓞 D.host.E) :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  htPoint (ct.dat y)

def psiEmb (D : D7) (τ : PsiT D) : D.host.E →+* ℂ := DV.tauEmb D (D.eTau.symm τ)


open Classical in
def eigProj {Z : ct.Mdl} (y : ct.Pt Z) (σ : D.host.E →+* ℂ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; (ct.htPt y).V →ₗ[↥y.C.S] (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  proj (isSplitting_embInt y.P) (ct.htPt y).actV σ

end At

def htpTrue (ct : At S κ p) : HTpSt ct :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  { Tp := fun y => (ct.htPt y).T
    tpAdd := fun _ => inferInstance
    OmV := fun y => (ct.htPt y).OmC
    omAdd := fun _ => inferInstance
    omMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).OmC)
    om := fun y => (ct.htPt y).latOm.toAddSubgroup
    ht := fun y => htMap (ct.htPt y)
    om_smul := fun y a ha _ hv => (ct.htPt y).latOm.smul_mem (⟨a, ha⟩ : ↥(intO ↥y.C.S)) hv
    TC := fun y => (ct.htPt y).V
    tcAdd := fun _ => inferInstance
    tcMod := fun y => (inferInstance : Module ↥y.C.S (ct.htPt y).V)
    iT := fun y => tateIncl (ct.htPt y)
    iT_span := fun y => span_tateIncl (ct.htPt y)
    htC := fun y => (ct.htPt y).alC
    htC_iT := fun y => alC_tateIncl (ct.htPt y)
    psiC := fun y => (ct.htPt y).pairV
    lieGt1 := fun y => lieSpan (ct.htPt y)
    eT := fun y τ => ct.eigProj y (At.psiEmb D τ) }

namespace HTp

variable (ct : At S κ p) {Z : ct.Mdl} (y : ct.Pt Z)

end HTp

end GlobalTheory.LocM
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.Cht

section Ball

variable {C : Type} [NormedField C] [IsUltrametricDist C]

end Ball

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

structure PtAt (Z : Mdl Y i₀) (C : SCF p) : Type where
  P : PointsOfFlagModel.PtC (Y Z.i) C
  z : Sp ↥(intO ↥C.S) ⟶ Z.X
  z_π : z ≫ Z.π = P.yt

namespace PtAt

variable {Z : Mdl Y i₀} {C : SCF p} (y : PtAt Z C)

def gen : Sp ↥C.S ⟶ Z.X := spMap (intO ↥C.S).subtype ≫ y.z

end PtAt

structure Fam (Y : LocalSystem Xo p W) (i₀ : Idx H p) (C : SCF p) : Type where
  pt : ∀ Z : Mdl Y i₀, PtAt Z C
  compat : ∀ Z₁ Z₂ : Mdl Y i₀, Corr Z₁ Z₂ → NatImg Z₁ Z₂ (pt Z₁).gen (pt Z₂).gen

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

abbrev idx0 (ct : At S κ p) : Idx A.H p := ⟨κ.l, κ.c, κ.good p ct.hp⟩

structure DVP (ct : At S κ p) : Type where
  C : SCF p
  K : Subfield ↥C.S
  closed : IsClosed (K : Set ↥C.S)
  dvr : IsDiscreteValuationRing ↥(intO ↥K)
  dense : Dense {x : ↥C.S | IsAlgebraic ↥K x}
  fam : Fam ct.Y (idx0 ct) C
  rat : ∃ w : Sp ↥K ⟶ ct.YY.X, spMap K.subtype ≫ w = (fam.pt ct.YY).gen

variable {ct : At S κ p}

structure Ext (y : DVP ct) : Type where
  L : Subfield ↥y.C.S
  le : y.K ≤ L
  fin : (Subfield.inclusion le).Finite
  π : ↥(intO ↥L)
  irr : Irreducible π

variable {y : DVP ct}

variable {Z : ct.Mdl} {e : Ext y}

end GlobalTheory.LocM.Cht
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam GlobalTheory.FieldBaseChange GlobalTheory.ConstFam

namespace GlobalTheory.LocM

namespace Bdy

section Reg

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G) (hR : AdmBase R (maximalIdeal R)) [GeometricallyConnected G.hom]

end Reg

namespace BDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t₀ : SAB H X} {x : X} (B : BDat t₀ x)

abbrev Ylat : Type := B.U.D.toPre.X

def chX : Type := B.Ylat
instance : AddCommGroup B.chX := inferInstanceAs (AddCommGroup B.Ylat)
instance : Module (𝓞 E) B.chX := Module.compHom B.Ylat (H.bar : 𝓞 E →+* 𝓞 E)

def phi : B.Ylat ≃+ B.chX := AddEquiv.refl _

def tau : B.Ylat → B.Ylat → (FractionRing B.R)ˣ :=
  letI := H.starRing
  (exists_reading B.U.D B.U.oD).choose

theorem tau_spec : letI := H.starRing; IsReading B.U.D (𝓞 E) B.tau :=
  letI := H.starRing
  (exists_reading B.U.D B.U.oD).choose_spec

theorem adm : AdmBase B.R (maximalIdeal B.R) := ⟨B.noeth, B.dom, B.normal, B.complete⟩

instance : GeometricallyConnected B.t.G.hom := B.t.semi.geomConnected

def fc : SecGK B.U.U →ₗ[FractionRing B.R] (B.chX → FractionRing B.R) := coef B.U.U B.adm

def trU {w : 𝓞 E} (hw : w + H.bar w = 1) (a : B.Ylat) (χ : B.chX) : B.Rˣ :=
  letI := H.starRing
  (existsUnique_transUnit B.U.oD B.tau_spec hw a χ).choose

end BDat

end Bdy

open Bdy

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

theorem bar_eq_of_conj (A : Amb D) {c c' : 𝓞 D.host.E} (hc : (c' : D.host.E) = D.host.conj (c : D.host.E)) :
    c' = A.H.bar c := by
  apply RingOfIntegers.ext
  rw [hc, A.H.bar_eq]
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem cmHostUnit_add_conj_eq_one (A : Amb D) : w0 D + A.H.bar (w0 D) = 1 := by
  rw [← bar_eq_of_conj A (one_sub_halfSqrt_eq_conj D), add_sub_cancel]

namespace At

variable (ct : At S κ p)

def BPt : Type :=
  {x : ct.Xm.X // IsClosed ({x} : Set ct.Xm.X) ∧ ¬ ct.Xm.abP x ∧ IsDomain (Cpl ct.Xm.X x) ∧ IsIntegrallyClosed (Cpl ct.Xm.X x)}

theorem nonempty_bdat (z : ct.BPt) : Nonempty (BDat ct.Xm.t z.1) :=
  haveI := z.2.2.2.1
  haveI := z.2.2.2.2
  Bdy.nonempty_bdat ct.hp.ne_zero ct.hW ct.Xm ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).1
    ((S.sys.clauses p ct.W ct.hp ct.hW).2 _).2.1 z.1

def bdat (z : ct.BPt) : BDat ct.Xm.t z.1 := pick (ct.nonempty_bdat z)

end At

def bdyTrue (ct : At S κ p) : BdySt ct where
  BPt := ct.BPt
  Rl z := (ct.bdat z).R
  Yb z := (ct.bdat z).Ylat
  Xb z := (ct.bdat z).chX
  phib z := (ct.bdat z).phi
  phib_conj z c c' hc a := by
    obtain rfl := bar_eq_of_conj A hc
    rfl
  taub z := (ct.bdat z).tau
  taub_add_left z := letI := A.H.starRing; (ct.bdat z).tau_spec.add_left
  taub_add_right z a χ χ' := by
    letI := A.H.starRing
    have h := (ct.bdat z).tau_spec
    exact (h.symm _ _).trans ((h.add_left χ χ' a).trans (congrArg₂ (· * ·) (h.symm _ _) (h.symm _ _)))
  taub_symm z := letI := A.H.starRing; (ct.bdat z).tau_spec.symm
  taub_smul z := letI := A.H.starRing; (ct.bdat z).tau_spec.bal
  taub_pos z := letI := A.H.starRing; (ct.bdat z).tau_spec.pos
  Sg z := SecGK (ct.bdat z).U.U
  Sreg z := secReg (ct.bdat z).U.U
  fc z := (ct.bdat z).fc
  trU z := (ct.bdat z).trU (cmHostUnit_add_conj_eq_one A)

end GlobalTheory.LocM
end
end
