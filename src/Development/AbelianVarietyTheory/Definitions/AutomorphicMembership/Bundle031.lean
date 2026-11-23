module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle021
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Lean.Meta.Injective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar



def ratL {D : D7} (L : LocAll (lay0 D)) (S : RatDat D.ntw) : RatDat (withLoc L).ntw := { S with }


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure NAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) :
    Type 1 where
  nt : NTrue hL D cf nch tp
  all : NAllC D nch
  chr_eq : (⟨all.cf, all.tp⟩ : Σ c : CharFrame D, TupTied D c nch) = ⟨cf, tp⟩
  host : HostTied D
  frameN : ∀ x, all.gal.fr.jE x = host.fr.j x
  chrN : NCharTied D cf nch tp
  chrGal : NGalChrTied D cf nch tp
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : NX.AdmTw D i k Q ψ),
    (all.exp.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D Pq Q ∧ (all.exp.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D Pq (D.ntw.pD i)
  jE_eq : HEq nt.jE all.gal.fr.jE
  mt_eq : HEq (mtL nt.L nt.M) all.gal.mt
  Pq_eq : HEq nt.Pq Pq
  low : 2 ∈ nt.low ∧ AbsolutelyIrreducibleSpan.q0 D ∈ nt.low ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ nt.low ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ nt.low
  split : GlobalTheory.SplitCoef.OSplit D
  ratIn : RatIn nt.D nt.S
  ratIn_hL : ratIn.hL = nt.hL
  ratIn_eig : ratIn.eig = nt.eig
  ratIn_θ : ratIn.θ = nt.θ
  depth : RowDepth nt.D nt.rep

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure NRow {hL : GlobalTheory.Published.LocalLanglandsGL} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : Type 1 where
  kKs : Ks →+* ↥D.LL0
  hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x
  nexp : NExpRealS R cG (ratDatR R cG kKs hk)
  hecke : NExpRealH R cG (ratDatR R cG kKs hk) nexp
  grp : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)
  rowLoc : principalLevelFrame.RowLocPin a.all.gal.lp R.θ Y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) Y.eFT
  S_eq : HEq (ratL a.nt.L a.nt.S) (ratDatR R cG kKs hk)
  hL_eq : HEq a.nt.hL hecke.hL
  rep_eq : HEq a.nt.rep fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)

end Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure NCore (hL : GlobalTheory.Published.LocalLanglandsGL) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) : Type 1 where
  a : NAt hL (w.D Z) (TC.cf w.I w.l Z) nch n.tp
  row : NRow (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y
  sel : Set.range a.Pq = Set.range w.I.sel

abbrev NExt (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (_ : ThData (w.D Z)),
    NCore hL t n → Type 1

def NX (hL : GlobalTheory.Published.LocalLanglandsGL) (E : NExt hL) : NCondition := fun K B f T w Z Wt p0 t nch n xd =>
  Σ c : NCore hL t n, E K B f T w Z Wt p0 t nch n xd c

end GlobalTheory.Mem.Top.Bl

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

structure Ray (oa : D.OAct O) : Type 1 where

  H : Over (Sp R)
  [grp : GrpObj H]
  [comm : IsCommMonObj H]

  Φ : ∀ T, (T ⟶ H) ≃ GtPt D T
  isGt : (splitExt D).IsGt H
  rep : Represents Φ

  ρ : RingAct H O
  smul : ∀ (a : O) T (x : T ⟶ H), FormalPoint.IsSmulPt oa a (Φ T x) (Φ T (x ≫ ρ.act a))

attribute [instance] Ray.grp Ray.comm

instance (oa : D.OAct O) : Nonempty (Ray oa) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL oa (Φ := Φ) hΦ
  exact ⟨{ H := H, Φ := Φ, isGt := hH, rep := hΦ, ρ := ρ, smul := hρ }⟩

def Chr (D : DegPre R) : Type := D.X

instance : AddCommGroup (Chr D) := inferInstanceAs (AddCommGroup D.X)

instance : Module O (Chr D) := Module.compHom D.X (starRingEnd O)


variable (D O) in
def torAct : OAct O (splitTorus (Sp R) (Chr D)) := Diag.diagAct (Sp R) O (Chr D)

theorem exists_torPt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) (Chr D)) : ∃ g : GtPt D T, g.b = 1 ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      (val (g.s χ) r y J).val = gs r y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  let u : Multiplicative D.X →* Γ(T.left, ⊤) :=
    { toFun := fun χ => (coord x).hom (AddMonoidAlgebra.single χ.toAdd 1)
      map_one' := Diag.coord_single_zero x
      map_mul' := fun a b => Diag.coord_single_add x _ _ }
  let v : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) := fun χ =>
    ⟨fun _ => res le_top (u.toHomUnits (Multiplicative.ofAdd χ))⟩
  have hv : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (v χ) r y J = gm r y ⊤ (u.toHomUnits (Multiplicative.ofAdd χ)) := fun χ Z r y J hJ =>
    gm_res r y _ (hJ.mem PEmpty.elim r) _
  obtain ⟨g, hb, hg⟩ := exists_pt (1 : T ⟶ D.P.A) v (fun χ i j => by
      obtain rfl : i = j := funext fun k => k.elim
      have e : (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
        dsimp only [LB.LinComb]
        erw [Fintype.prod_empty]
        rfl
      rw [e, _root_.one_mul])
    (fun χ U _ h => by
      rw [prod_pt, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel])
    (fun y J hJ => by rw [hv _ _ _ _ _ hJ, ofAdd_zero, map_one, map_one])
    (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, _root_.mul_one, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ofAdd_add, map_mul, map_mul])
  exact ⟨g, hb, fun χ Z r y J hJ => by
    rw [hg _ _ _ _ _ hJ, hv _ _ _ _ _ hJ]; exact (gs_unit r y ⊤ trivial _).symm⟩

namespace Ray

variable {oa : D.OAct O} (Y : Ray oa)

def act : OAct O Y.H := ofRingAct Y.ρ


variable (oa) in
def actB : OAct O D.P.A := ofRingAct oa.onB.toRingAct

def q : Y.H ⟶ D.P.A := (Y.Φ Y.H (𝟙 _)).b

theorem Φ_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

theorem q_linear : IsLinearHom Y.act (actB oa) Y.q :=
  ⟨isMonHom_of_mul _ fun T x x' => by
      rw [← Φ_b, ← Φ_b, ← Φ_b]; exact ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 T x x')).1,
    fun a => by
      have h := (Y.smul a _ (𝟙 _)).1
      rw [Φ_b, Category.id_comp] at h
      exact h⟩

def i : splitTorus (Sp R) (Chr D) ⟶ Y.H := (Y.Φ _).symm (exists_torPt (𝟙 _)).choose

theorem Φ_i {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) (Chr D)) : (Y.Φ T (x ≫ Y.i)).b = 1 ∧
    ∀ (χ : D.X) y J, Good D.P.L y J →
      (cv (Y.Φ T (x ≫ Y.i)) χ y J).val = gs (𝟙 _) y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  obtain ⟨h₁, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T _ x Y.i)
  obtain ⟨e₁, e₂⟩ := (exists_torPt (D := D) (𝟙 _)).choose_spec
  have e : Y.Φ _ Y.i = (exists_torPt (D := D) (𝟙 _)).choose := Equiv.apply_symm_apply _ _
  rw [e] at h₁ h₂
  refine ⟨by rw [h₁, e₁, MonObj.comp_one], fun χ y J hJ => ?_⟩
  rw [h₂ χ y J hJ, e₂ χ _ _ y J hJ]
  conv_rhs => rw [← Category.comp_id x, coord_comp]
  exact (gs_eq x.left y ⊤ trivial _).trans (gs_eq (𝟙 _) y ⊤ trivial _).symm

theorem i_q : Y.i ≫ Y.q = 1 := by
  have h := (Y.Φ_i (𝟙 _)).1
  rwa [Φ_b, Category.id_comp] at h

theorem i_linear : IsLinearHom (torAct D O) Y.act Y.i := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  refine ⟨isMonHom_of_mul _ fun T x x' => (Y.Φ T).injective ?_, fun a => (Y.Φ _).injective ?_⟩
  · refine isAdd_unique ((TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => Units.ext ?_⟩) (Y.rep.2 T _ _)
    · rw [(Y.Φ_i _).1, (Y.Φ_i _).1, (Y.Φ_i _).1, _root_.mul_one]
    · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [(Y.Φ_i x').1, C.face₃, _root_.mul_one, Units.val_mul, (Y.Φ_i _).2 χ y J hJ, (Y.Φ_i _).2 χ y J hJ,
        (Y.Φ_i _).2 χ y J hJ]
      exact (congrArg (gs _ y ⊤) (Diag.coord_mul x x' χ)).trans (gs_mul (𝟙 _) y ⊤ trivial _ _)
  · obtain ⟨h₁, h₂⟩ := (isSmulPt_iff hL oa a _ _).1 (Y.smul a _ (𝟙 _ ≫ Y.i))
    have := oa.onB.hom a
    have := oa.onB.hom (star a)
    rw [Category.id_comp] at h₁ h₂
    have k := Y.Φ_i (𝟙 _)
    rw [Category.id_comp] at k
    refine pt_ext ?_ fun χ y J hJ => Units.ext ?_
    · exact (Y.Φ_i _).1.trans (h₁.trans (by rw [k.1, MonObj.one_comp])).symm
    · have C : IsCub (th D (T := splitTorus (Sp R) (Chr D)) y J) := isCub_cubV D.cub hJ
      have e := (rosGen_add hL oa a hJ 1 1 (cP D _ χ)).2
      rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
      refine ((Y.Φ_i _).2 χ y J hJ).trans (Eq.trans ?_ (congrArg Units.val (h₂ χ y J hJ)).symm)
      rw [k.1, mul_eq_left.1 e.symm, _root_.mul_one, k.2 _ y J hJ]
      refine congrArg (gs _ y ⊤) ?_
      have := Diag.coord_comp_diagMap_single (𝟙 (splitTorus (Sp R) (Chr D)))
        (DistribSMul.toAddMonoidHom (Chr D) a) χ
      rw [Category.id_comp] at this
      exact this

theorem isKernel : IsPullback Y.i (toUnit _) Y.q η[D.P.A] := by
  have ex : ∀ {T : Over (Sp R)} y, ∃ J, Good D.P.L (Z := T.left) y J := fun y => by
    choose I hI using fun χ => exists_chart D.P.isLB ((χ : _ ⟶ D.P.A.left) y)
    exact ⟨I, hI⟩
  refine Diag.isPullback_toUnit_of_lift _ Y.i_q (fun {T} a b h => Diag.hom_ext fun χ => fn_ext fun y _ => ?_)
    fun {T} x hx => ?_
  · obtain ⟨J, hJ⟩ := ex y
    exact ((Y.Φ_i a).2 χ y J hJ).symm.trans (h ▸ (Y.Φ_i b).2 χ y J hJ)
  · have hb : (Y.Φ T x).b = 1 := (Y.Φ_b x).trans hx
    have hF : ∀ χ, FormEq (DegPre.gtφT D T (Y.Φ T x).b χ) DegPre.gtε (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun χ U _ h => by
        rw [prod_pt, hb, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
    choose s _ vs using fun χ => exists_gen D.P.isLB (hF χ) _ ((Y.Φ T x).isGen χ)
    have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    let u : D.X → Γ(T.left, ⊤)ˣ := fun χ => res le ((s χ).s PEmpty.elim)
    have hu : ∀ χ y J, Good D.P.L y J → gs (𝟙 _) y ⊤ (u χ).val = (cv (Y.Φ T x) χ y J).val := fun χ y J hJ =>
      (gs_unit _ y ⊤ trivial _).trans (congrArg Units.val ((gm_res _ y le trivial _).trans
        ((val_of (s χ) _ y J PEmpty.elim fun k => k.elim).symm.trans (vs χ _ _ y J hJ))))
    let g : Multiplicative (Chr D) →* Γ(T.left, ⊤) :=
      { toFun := fun χ => (u χ.toAdd).val
        map_one' := fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          refine (hu 0 y J hJ).trans ?_
          rw [cv_zero _ hJ, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
        map_mul' := fun a b => fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
          have e := cv_add (Y.Φ T x) hJ a.toAdd b.toAdd
          rw [hb, C.face₃, _root_.mul_one] at e
          refine (hu _ y J hJ).trans (Eq.trans ?_ (gs_mul _ y ⊤ trivial _ _).symm)
          exact (congrArg Units.val e).trans (congrArg₂ (· * ·) (hu _ y J hJ) (hu _ y J hJ)).symm }
    refine ⟨Diag.ofChar T g, (Y.Φ T).injective (pt_ext ((Y.Φ_i _).1.trans hb.symm) fun χ y J hJ => Units.ext ?_)⟩
    exact ((Y.Φ_i _).2 χ y J hJ).trans ((congrArg (gs _ y ⊤) (Diag.coord_ofChar T g χ)).trans (hu χ y J hJ))

end Ray

end Ray

section Eig

variable {R S O : Type} [CommRing R] [CommRing S] [CommRing O] (f : R →+* S)
  {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

abbrev LieAt (a : OAct O G) : Type := Lie (a.pullback (spMap f))

def lieMap {a : OAct O G} {a' : OAct O G'} {φ : G ⟶ G'} (h : IsLinearHom a a' φ) : LieAt f a →ₗ[S] LieAt f a' :=
  haveI := h.isMonHom
  Lie.map _ _ ((Over.pullback (spMap f)).map φ)

def tanPt {a : OAct O G} (v : LieAt f a) : Over.mk ((epsR S).hom ≫ spMap f) ⟶ G :=
  HTLat.pushEquiv (isGrpPullback_pullback G (spMap f)) _ v.hom

end Eig

end GlobalTheory.RayEv
end
end
