module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaTraceTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fn_ext_of_surjective {W Y : Scheme.{0}} (Ψ : W ⟶ Y) [Surjective Ψ] [IsReduced Y] {U : Y.Opens}
    {a b : Γ(Y, U)} (h : ∀ w, Ψ w ∈ U → gs Ψ w U a = gs Ψ w U b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨w, rfl⟩ := Ψ.surjective y
  have hU : Ψ w ∈ U := Y.basicOpen_le _ hy
  have hw : w ∈ W.basicOpen ((Ψ.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hy
  rw [W.mem_basicOpen _ w hU] at hw
  have e := h w hU
  rw [gs_eq _ _ _ hU, gs_eq _ _ _ hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  exact absurd (e ▸ hw) not_isUnit_zero

theorem sec_eq_of_surjective {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {T : Over S} {W : Scheme.{0}}
    (Ψ : W ⟶ (T ⊗ A).left) [Surjective Ψ] [IsReduced (T ⊗ A).left] {k : ℤ} {u v : LB.Sec (LPow A L.L k T)}
    (h : ∀ w J, Good L.L w J → sv A L u Ψ w J = sv A L v Ψ w J) : u = v := by
  refine sec_ext fun j => fn_ext_of_surjective Ψ fun w hw => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB w (fun _ : Fin 1 => Ψ ≫ (snd T A).left) j
    (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => Set.mem_iInter.1 hw k)
  exact (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) u Ψ w J j e).symm.trans
    ((h w J hJ).trans (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) v Ψ w J j e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

end GlobalTheory.ThetaTraceTest
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct nonZeroDivisors ComplexConjugate
open GlobalTheory.SepRows GlobalTheory.EvenOnto
open GlobalTheory.Chain (IsVacVec ptOf)
open GlobalTheory.PairLift (adjO)

namespace GlobalTheory.CoreOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure ReLat (V : HSp D) where

  L0 : Submodule (𝓞 D.host.E) V.V
  lat : Submodule.IsLattice D.host.E L0
  unimod : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L0

@[reducible] def ReLat.sp {V : HSp D} (r : ReLat V) : HSp D := { V with L0 := r.L0, standardTuple_isLattice := r.lat, baseLattice_isUnimodular := r.unimod }

@[reducible] def ReLat.mod {V : HSp D} (r : ReLat V) {S : D.what₂.Tau → SPar} (M : DSModel V S) : DSModel r.sp S where
  H := M.H
  σ := M.σ
  lam := M.lam
  ε := M.ε
  fr := M.fr
  enum := M.enum
  ds := M.ds
  fr_unit := M.fr_unit
  fr_gram := M.fr_gram

def scaleLat {n : ℕ} (𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
  Submodule.span (𝓞 D.host.E) {y | ∃ a ∈ 𝔟, ∃ x ∈ Λ, y = a • x}

def exch (A B : HSp D) (f : WO A B → ℂ) : WO (negSp B) A → ℂ := fun x => f (adjO A B x)

def Exch {A B : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ))
    (ω' : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ A B f → ∀ g h, ω (negGA B h, g) (exch A B f) = exch A B (ω' (g, h) f)

def ExchLaw (D : D7) : Prop := ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) →
  (∀ f, IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f)) ∧
  (∀ x f, heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f)) ∧
  (∀ x x' : WO (negSp B) A, symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x')) ∧
  Function.Bijective (adjO A B) ∧
  (∀ m X, IsCovolOne (ratL B A) m X → ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧
    ∀ f f' : WO A B → ℂ, ∫ w in X, f w * conj (f' w) ∂m = ∫ w in X', exch A B f w * conj (exch A B f' w) ∂m') ∧
  ∀ χS χT ω, IsWeilDatumO ψ (negSp B) A χS χT ω → ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω'

def ReLatLaw (D : D7) : Prop :=
  (∀ (V : HSp D) Λ, IsSelfDualC V Λ → ∃ r : ReLat V, GlobalTheory.AdelicU.frameLat r.sp = Λ) ∧
  (∀ (V : HSp D) (r : ReLat V) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)),
    (MultT θ (r.mod M) J 1 : Submodule ℂ (SmT M →ₗ[ℂ] (GA D V → ℂ))) = MultT θ M J 1 ∧
    (KF (r.mod M) : Submodule ℂ (SmT M)) = KF M ∧ cart (r.mod M) = cart M ∧
    GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex V ∧ ∀ F : GA D V → ℂ, RapidDec r.sp F ↔ RapidDec V F) ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B),
    (∀ f : WO A B → ℂ, IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f) ∧
    ∀ χS χT (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)),
      IsWeilDatumO ψ r.sp r'.sp χS χT ω ↔ IsWeilDatumO ψ A B χS χT ω

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)

def gridCom : Com D where
  θ := W.θ
  ψ := W.ψ
  S := G.pl.S0
  n := nRk D
  t := sLen D - 1
  m := D.R.m
  χ := fun k => (G.ch.chi (D.R.m - k))⁻¹
  a := fun k τ => -(cen D sc.cGap τ (D.R.m - k) : ℚ)


variable (G) in
def IsCoreLat (i : ℕ) (r : ReLat (G.V (.core i))) : Prop :=
  GlobalTheory.AdelicU.frameLat r.sp = scaleLat ((D.host.AAbar * D.host.AA⁻¹) ^ i) (G.Λ (.core i))


variable (G) in
@[reducible] def gridStage (v : CoreVol G) (i : ℕ) (r : ReLat (G.V (.core i)))
    (M : DSModel (G.V (.core i)) (Node.par D sc.cGap (.core i))) : PiLocalization₂ D where
  V := r.sp
  par := Node.par D sc.cGap (.core i)
  M := r.mod M
  J := lev G (.core i)
  ν := (v i).μ
  fd := (v i).𝓕


variable (G) in
def IsOntoMod (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E) : Prop :=
  x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)) ∧ ∃ y₀ ∈ homLat (G.Λ (.core i)) (G.Λ (.core (i + 1))),
    x₀ * y₀ - 1 ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))

def CosLaw (i : ℕ) (x₀ : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core (i + 1))).rank) D.host.E)
    (Φ : WO (G.pS (.core i)) (G.pT (.core i)) → ℂ) : Prop :=
  Dep W (.core i) Φ ∧ ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
    (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
    heisO W.ψ _ _ y Φ = W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) • Φ

def Below (v : CoreVol G) (k : ℕ) (F : Fn G (.core k)) : Set (Fn G (.core 0)) :=
  {F₀ | ∃ Ψ : ∀ i, Fn G (.core i), (∀ i, i ≤ k → RapidDec (G.V (.core i)) (Ψ i)) ∧
    (∀ i, i < k → ∃ f : Sch G (.coreDown i), Dep W (.core i) f ∧ Ψ i = dn W v i f (Ψ (i + 1))) ∧ Ψ 0 = F₀ ∧ Ψ k = F}

def ComOK : Prop := Gap fun {_} _ _ _ _ W _ => (gridCom W).Is

def StageOK : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i ≤ D.R.m → (∃ r, IsCoreLat G i r) ∧
  ∀ r, IsCoreLat G i r → ∀ v M, (gridStage G v i r M).Is (gridCom W) i

def ParOK : Prop := ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ i, i < D.R.m → ∀ τ,
  UpPair (sLen D - 1) (Node.par D 1 (.core i) τ) (Node.par D 1 (.core (i + 1)) τ) (-(cen D 1 τ (D.R.m - i) : ℚ))
    (-(cen D 1 τ (D.R.m - i) : ℚ))

def OntoModEx : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∃ x₀, IsOntoMod G i x₀

def LatExch : Prop := All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (x : WO (G.pS (.core i)) (G.pT (.core i))),
    x ∈ latO (G.pS (.core i)) (G.pT (.core i)) (G.latS (T := _) (.core i) : Set _) (G.latT (.core i) : Set _) P ↔
      adjO (G.V (.core i)) (G.V (.core (i + 1))) x ∈
        latO r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp : Set _) (GlobalTheory.AdelicU.frameLat r'.sp : Set _) P

def DatumEx : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' →
  ∀ (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'), ∀ x₀ ∈ homLat (G.Λ (.core (i + 1))) (G.Λ (.core i)),
    ∃ f, IsVacVec W.ψ W.θ M M' f ∧
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff W.ψ r.sp r'.sp (GlobalTheory.AdelicU.frameLat r.sp) (GlobalTheory.AdelicU.frameLat r'.sp) G.pl.S0 f ∧
      ∀ φ, CosLaw W i x₀ (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ M M' f φ))

def CosSupp : Prop := All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ Φ, CosLaw W i x₀ Φ →
  ∀ m X, IsCovolOne (ratL (G.pT (.core i)) (G.pS (.core i))) m X → ∀ g : GA D (G.V (.core i)),
    (∀ v ∉ G.pl.S0, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.core i)).gram v g ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (G.V (.core i)).gram (G.Λ (.core i)) v) →
    (∫ w in X, W.om (.core i) (1, g) Φ w * conj (Φ w) ∂m) ≠ 0 → Lev.finE (G.V (.core i)) g ∈ G.levCong (.core i)

def PreOK : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ r r', IsCoreLat G i r → IsCoreLat G (i + 1) r' → ∀ v M M',
  ∃ ω f, PreStep (gridCom W) i (gridStage G v i r M) (gridStage G v (i + 1) r' M') ω f ∧ Exch W.ψ (W.om (.core i)) ω ∧
    ∀ φ, Dep W (.core i) (exch (G.V (.core i)) (G.V (.core (i + 1))) (ptOf (V := r.sp) (W := r'.sp) W.ψ W.θ (r.mod M) (r'.mod M') f φ))

def ChainEx : Prop := Gap fun {D} _ _ _ {G} W _ => ∀ v r₀ M₀, IsCoreLat G 0 r₀ → ∀ k, k ≤ D.R.m → ∃ r M, IsCoreLat G k r ∧
  ∃ Θ, GlobalTheory.EvenOnto.Reach (gridCom W) (gridStage G v 0 r₀ M₀) k (gridStage G v k r M) Θ ∧
    ∀ y, ∀ x ∈ (gridStage G v 0 r₀ M₀).KF, PiLocalization₂.val (Θ y) x ∈
      Submodule.span ℂ {F₀ : Fn G (.core 0) | ∃ w, F₀ ∈ Below W v k (PiLocalization₂.val y w)}

def TopCols : Prop := All fun {D} _ _ {sc} {G} W _ =>
  ∀ M : DSModel (G.V (.core D.R.m)) (Node.par D sc.cGap (.core D.R.m)), ∀ y ∈ CoreForms G W.θ D.R.m M, ∀ w,
    ∃ c ∈ Cols G W.θ, ∃ ξ : Module.Dual ℂ (coefPlus G W.θ).W, y w = pairVec (coefPlus G W.θ) ξ c

end GlobalTheory.CoreOnto

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open scoped TensorProduct

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PairEx : Prop := ∀ (D : D7) (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ),
  (∀ τ, GlobalTheory.PairLift.PairPar (S τ) (S' τ) (aS τ) (aT τ)) → ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M,
      ∀ ω : GlobalTheory.Grid.WRep V W, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f →
        IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It

def parRow (D : D7) (C : ℝ) (i : ℕ) : D.what₂.Tau → SPar := fun τ => dualPar (Node.par D C (.grid i 0) τ)

def RowModels : Prop := Gap fun {D} _ _ {sc} {G} W _ => ∀ i, i ≤ D.R.m →
  ∃ MV : DSModel (G.V (.grid i 0)) (parRow D sc.cGap i), cart MV = W.cart (.grid i 0)

def RowStep : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ i, i < D.R.m → ∀ (S S' : D.what₂.Tau → SPar)
  (MA : DSModel (G.V (.grid i 0)) S) (MB : DSModel (G.V (.grid (i + 1) 0)) S'), S = parRow D sc.cGap i → S' = parRow D sc.cGap (i + 1) →
    cart MA = W.cart (.grid i 0) → cart MB = W.cart (.grid (i + 1) 0) →
    ∃ It : PolF D (G.V (.grid i 0)).rank (G.V (.grid (i + 1) 0)).rank → SmT MA → SmT MB, ∀ F ∈ MultT W.θ MA ∅ 1, ∀ κ : G.CosAt i,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ P v,
        LiftConv W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) ∧
          liftA W M (.right i 0 : Arrow T) (W.fock (.chi i 0) (W.cosVec i κ) P) (F v) = F' (It P v)

def RowTower : Prop := Gap fun {D} {T} _ {sc} {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ (n : ℕ) (h : n ≤ D.R.m), ∃ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid n 0)) S), S = parRow D sc.cGap n ∧
    cart MB = W.cart (.grid n 0) ∧ ∃ vec : G.RealVec → SmT M₀ → SmT MB, ∀ t ∈ MultT W.θ M₀ ∅ 1, ∀ Φ : G.Datum,
      ∃ F' ∈ MultT W.θ MB ∅ 1, ∀ ρ w,
        PathConv W M (rowPath T 0 n) (rowFam 0 n fun i => W.datum ρ Φ (Fin.castLE h i)) (t w) ∧ part W M ρ Φ (t w) n h = F' (vec ρ w)

def CoefTensor : Prop := ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is →
  ∃ (Wt : D.what₂.Tau → Type) (_ : ∀ τ, AddCommGroup (Wt τ)) (_ : ∀ τ, Module ℂ (Wt τ)) (_ : ∀ τ, FiniteDimensional ℂ (Wt τ))
    (π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (Wt τ)) (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ c.W),
    (∀ τ, GlobalTheory.RealBessel.IsContIrred (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (π τ)) ∧
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ c.ρ (atTau θ V τ g)⁻¹

section Sep

variable {D : D7} {V A : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ}
  (F : D.what₂.Tau → Matrix (Fin V.rank) (Fin A.rank) ℂ) (e : D.what₂.Tau → Matrix (Fin V.rank) (Fin r) ℂ)
  (χ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) {Wt : D.what₂.Tau → Type} [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
  (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → Module.End ℂ (Wt τ))


open Classical in
def SepBes (β : (∀ τ, Wt τ) → M.Vec → ℂ) : Prop :=
  ∀ τ x v, ∃ b ∈ GlobalTheory.RealBessel.besselForms (gramAt D V τ) (gramAt D A τ) (F τ) (e τ) (χ τ) (M.rep τ) (π τ) (M.sm τ),
    ∀ y u, β (Function.update x τ y) (Function.update v τ u) = b y u

end Sep

def TopFrame : Prop := All fun {D} _ _ _ {G} W _ => ∃ z : D.what₂.Tau → Fin (G.V (.grid D.R.m 0)).rank → ℂ, ∀ τ,
  GlobalTheory.RealBessel.IsFrame (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ)
               ((frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ)) (G.besTop.e.map (tauE D τ)) (z τ) ∧
    GlobalTheory.RealBessel.IsGeneric (gramAt D (G.V (.grid D.R.m 0)) τ) (G.besTop.e.map (tauE D τ)) (z τ)
      fun u => besChar W.ψ G.besTop (atTau W.θ _ τ u)

def TopSep : Prop := All fun {D} _ _ _ {G} W M => ∀ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid D.R.m 0)) S),
  ∀ F' ∈ MultT W.θ MB ∅ 1, ∀ Ψ ∈ Cols G W.θ,
    (∃ b : Module.Dual ℂ (coefPlus G W.θ).W →ₗ[ℂ] SmT MB →ₗ[ℂ] ℂ, ∀ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v) = b ξ v) ∧
    ∀ (Wt : D.what₂.Tau → Type) [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)]
      (π : ∀ τ, Matrix (Fin (G.V (.top 0)).rank) (Fin (G.V (.top 0)).rank) ℂ → Module.End ℂ (Wt τ))
      (e : (⨂[ℂ] τ, Wt τ) ≃ₗ[ℂ] Module.Dual ℂ (coefPlus G W.θ).W),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.top 0)) τ), ∀ x y : ∀ τ, Wt τ, y τ = π τ g (x τ) → (∀ τ', τ' ≠ τ → y τ' = x τ') →
        e (PiTensorProduct.tprod ℂ y) = e (PiTensorProduct.tprod ℂ x) ∘ₗ (coefPlus G W.θ).ρ (atTau W.θ _ τ g)⁻¹) →
      SepBes MB (fun τ => (frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ))
        (fun τ => G.besTop.e.map (tauE D τ)) (fun τ u => besChar W.ψ G.besTop (atTau W.θ _ τ u)) π
        fun x v => Bplus W M (pairVec (coefPlus G W.θ) (e (PiTensorProduct.tprod ℂ x)) Ψ) (F' (PiTensorProduct.tprod ℂ v))

def RowConv : Prop := Gap fun {D} _ {L} _ {G} W M => ∀ M₀ : DSModel (Yc D 0) (parB (Ptw D) 0), cart M₀ = W.cart (.grid 0 0) →
  ∀ t ∈ Rows L W.θ M₀, ∀ w ρ ξ, ∀ Ψ ∈ Cols G W.θ, ∀ Φ, FConv W M ρ ξ Ψ Φ (t w)

def GoodRows : Prop := ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ t ∈ R.EEat R.triv,
    PiTensorProduct.lift t ∈ Rows R.toLevCh R.θ (R.MY 0)

theorem parRow_zero (D : D7) (C : ℝ) : parRow D C 0 = parB (Ptw D) 0 :=
  funext fun τ => congrArg dualPar (parV_zero D C (Nat.zero_le _) τ)

end GlobalTheory.SepRows

end
end
