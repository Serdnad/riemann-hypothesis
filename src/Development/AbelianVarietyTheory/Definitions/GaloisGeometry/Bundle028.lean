module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle019
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.QuadraticBaseChangeGL3 GlobalTheory.TwV.DelB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)

def bAt : ∀ (j : ℕ) (_ : j ≤ D.R.m), Lv.comp j → GL (Fin (D.R.N j)) D.host.E
  | 0, _, _ => (lev0At J.Gd u w hg).A.B
  | j + 1, hj, a => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm a).1).B

def uB (j : ℕ) (hj : j ≤ D.R.m) (a : Lv.comp j) : GL (Fin (D.R.N j)) D.host.E := J.A.crd j hj * bAt J j hj a

def dPow {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (a : D.what₂.Tau → ℤ) : ℂ := ∏ τ, embT D τ M.det ^ a τ

variable {J std}

def mM (d : Dec J std) (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : GL (Fin (D.R.N j)) D.host.E :=
  J.A.crd j hj * (d.gam j hj La)⁻¹ * bAt J j hj La.1

def sPt (d : Dec J std) (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : ℂ :=
  d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
    dPow (uB J j hj La.1).1 (fun _ => -(cTw D j))

def RealAt (d : Dec J std) (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j)
    (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (V : XR ((sysS H X std).Pj j) ℂ) : Prop :=
  ∀ z z' : Fr D j hj, IsTr (atInf (embT D) (d.gam j hj La).1) z' z →
    evC ((sysS H X std).Pj j) h (posJ (sysS H X std) D (hT.gat_pos u w hg) j) (gramC (gramN D j hj) (embT D)) (crdB (embT D) (bAt J j hj La.1)) V z =
      d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
        dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' *
        φ (clsAt X H j La.1 La.2) ((J.St j hj).eY.symm z')


open Classical in
def sO (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (La : (sysS H X std).Lt j) : ℂ_[D.what₂.places.resChar w] :=
  if hj : j ≤ D.R.m then ι (sPt d j hj La * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) else 0

def gmS (d : Dec J std) (j : ℕ) (La : (sysS H X std).Lt j) (x : ((ex.tw.fm u μ).lat j).V) : ((sysS H X std).Pj j).Xsp :=
  gmOf d.fd2 j La ((kaAt X H hT).cmp j x La.1 La.2)

variable (J std)

def kS (j : ℕ) (hj : j ≤ D.R.m) (a : Lv.comp j) : ℂ :=
  dPow (uB J j hj a).1 (fun τ => -((D.chTw u μ).sSharp j τ)) *
    dPow (gMat J j hj 1) (fun _ => ((D.R.N (j + 1) / 2 : ℕ) : ℤ) + cTw D j)

def kT (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1)) : ℂ :=
  dPow (uB J (j + 1) hj a).1 (fun τ => -((D.chTw u μ).sDiv j τ)) *
    dPow (gMat J (j + 1) hj 1) (fun _ => ((D.R.N j / 2 : ℕ) : ℤ) + cTw D (j + 1))

variable {J std}

def cKs (S : J.At std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)) :
    ℂ_[D.what₂.places.resChar w] :=
  ι (kT J j hj a' * (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)⁻¹) *
    ltC S.g S.hLT ^ (-(∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ))


open Classical in
def scT (d : Dec J std) (S : J.At std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (c' : Lv.comp (j + 1))
    (L' : ((sysS H X std).Pj (j + 1)).Tup) : ℂ_[D.what₂.places.resChar w] :=
  if hj : j + 1 ≤ D.R.m then
    ι (d.uT S j (c', L') * kT J j hj c') * ltC S.g S.hLT ^ (-(∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ))
  else 0

end GlobalTheory.TwV.DelA

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory GlobalTheory.AV GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT.MulModel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

theorem comp_pow' {S : Scheme.{0}} {X Y M : Over S} [MonObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp' {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom (𝟙 A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift (𝟙 A ^ n) (𝟙 A) ≫ μ[A]))

variable {G : HTGroup p} (L : Link D G)

end GlobalTheory.DrinLev.HT.MulModel
end
end
