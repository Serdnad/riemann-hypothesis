module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle042
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle038
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtensionPropertyPi
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField TopologicalSpace IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.ShFam GlobalTheory.TotalFrame GlobalTheory.FlagPts Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open Formalism.MainNotions.DIV.Cons (SCF intO)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop}


open Classical in
def FlagFam.lat {Z : Mdl Y i₀} (s : FlagFam P Z) : Lat Z := if h : ∃ L : Lat Z, s.1 = allSteps L then h.choose else Lat.top Z


def Mdl.inclV (Z : Mdl Y i₀) : i₀.c.V W →+* Z.i.c.V W :=
  ((IntermediateField.inclusion Z.le).toRingHom.comp (i₀.c.V W).subtype).codRestrict _ fun a => a.2

end Family

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

section Reduction

abbrev V₀ : Type := κ.c.V ct.W

abbrev kbar : Type := AlgebraicClosure (ResidueField ct.V₀)

def ρ₀ : ct.V₀ →+* ct.kbar := (algebraMap (ResidueField ct.V₀) ct.kbar).comp (residue ct.V₀)

abbrev LaBar : Type := ct.kbar ⊗[ℤ] S.Dw.La

def eigLat (σ : D.host.E →+* ℂ) : Submodule ct.V₀ (ct.V₀ ⊗[ℤ] S.Dw.La) :=
  eigenSub (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* _)) (embV κ.c ct.W σ)

def redLa : ct.V₀ ⊗[ℤ] S.Dw.La →ₗ[ℤ] ct.LaBar := ct.ρ₀.toIntAlgHom.toLinearMap.rTensor S.Dw.La

def eigBar (τ : PsiT D) : Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar (ct.redLa '' ct.eigLat (embOf D τ))

instance : FiniteDimensional ct.kbar ct.LaBar :=
  have := S.Dw.fin
  have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
  Module.Finite.base_change ℤ _ _

abbrev FlP : Type := Flags ct.kbar fun τ : PsiT D => ↥(ct.eigBar τ)

def FlP.sub {ct : At S κ p} (F : ct.FlP) (τ : PsiT D) (i : ℕ) : Submodule ct.kbar ct.LaBar :=
  (F.step τ i).map (ct.eigBar τ).subtype

abbrev LaP (_ct : At S κ p) : Type :=
  S.Dw.La ⧸ (Ideal.span {(p : 𝓞 D.host.E)} • ⊤ : Submodule (𝓞 D.host.E) S.Dw.La)

def Sum1 : Type := {l : Submodule (𝓞 D.host.E) ct.LaP // (∃ l', IsCompl l l') ∧
  Nonempty (l ≃ₗ[𝓞 D.host.E] (𝓞 D.host.E ⧸ Ideal.span {(p : 𝓞 D.host.E)}))}

def Sum1.bar {ct : At S κ p} (l : ct.Sum1) : Submodule ct.kbar ct.LaBar :=
  Submodule.span ct.kbar {s | ∃ a : S.Dw.La, Submodule.Quotient.mk a ∈ l.1 ∧ s = 1 ⊗ₜ a}

def psiBar : LinearMap.BilinForm ct.kbar ct.LaBar := S.Dw.EF.baseChange ct.kbar

def locus (l : ct.Sum1) : Closeds ct.FlP :=
  between j (fun τ => l.bar.submoduleOf (ct.eigBar τ)) fun τ => (ct.psiBar.orthogonal l.bar).submoduleOf (ct.eigBar τ)

end Reduction

section Point

variable {Z : ct.Mdl} (y : ct.Pt Z)

def lieStep (σ : D.host.E →+* ℂ) (r : ℕ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Submodule ↥y.C.S (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  Submodule.span ↥y.C.S {w | ∃ (x : LieG (ct.htPt y).Gt) (u : Vecs S.Dw (ct.Y Z.i).t ↥y.C.S) (i : Fin (S.Dw.mult σ)),
    Z.FlagAt y.gen u ∧ (i : ℕ) < r ∧
    u σ i = spMap (dualMap (intO ↥y.C.S).subtype) ≫ ((ct.htPt y).lieCmp x).1.left ≫ htToModel (ct.dat y) ∧
    w = (ct.htPt y).bLie x}

def htStep (τ : PsiT D) (i : ℕ) :
    letI : Fact p.Prime := ⟨ct.hp⟩; letI := A.H.starRing; Submodule ↥y.C.S (ct.htPt y).V :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  letI := A.H.starRing
  if i ≤ j then ct.lieStep y (embOf D τ) i
  else (ct.htPt y).eigV (embInt y.P (embOf D τ)) ⊓
    (ct.htPt y).pairV.orthogonal (ct.lieStep y (conjEmb (embOf D τ)) (N - i))

def LevelMatch (t : (htpTrue ct).Tp y) (a : S.Dw.La) : Prop :=
  letI : Fact p.Prime := ⟨ct.hp⟩
  (Tate.lev t 1).left ≫ abVarι y.P = y.P.y ≫ ((ct.Y Z.i).oF.etaA a ^ (Z.i.l.A / p)).left

def redGraph (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) : AddSubgroup ((htpTrue ct).TC y × ct.LaBar) :=
  AddSubgroup.closure {q | ∃ (c : ↥(intO ↥y.C.S)) (t : (htpTrue ct).Tp y) (a : S.Dw.La), ct.LevelMatch y t a ∧
    q = ((show (ct.fld y).C from c.1) • (htpTrue ct).iT y t, ρ c ⊗ₜ a)}

def redSub (ρ : ↥(intO ↥y.C.S) →+* ct.kbar) (F : Submodule (ct.fld y).C ((htpTrue ct).TC y)) :
    Submodule ct.kbar ct.LaBar := Submodule.span ct.kbar {s | ∃ w ∈ F, (w, s) ∈ ct.redGraph y ρ}

end Point

def SpPt (Z : ct.Mdl) : Type :=
  {x : Sp ct.kbar ⟶ Z.X // x ≫ Z.s ≫ spMap Z.inclV = spMap ct.ρ₀}

def IsRedFlag {Z : ct.Mdl} (x : ct.SpPt Z) (F : ct.FlP) : Prop :=
  p ∣ Z.i.l.A ∧ ∃ (y : ct.Pt Z) (ρ : ↥(intO ↥y.C.S) →+* ct.kbar), spMap ρ ≫ y.z = x.1 ∧
    ∀ τ i, F.sub τ i = ct.redSub y ρ (ct.htStep y τ i)


open Classical in
def redFlag {Z : ct.Mdl} (x : ct.SpPt Z) : ct.FlP :=
  if h : ∃ F, ct.IsRedFlag x F then h.choose else Classical.arbitrary _


open Classical in
def diffExpo (_ct : At S κ p) (l : PsiT D → ℕ → ℤ) (σ : D.host.E →+* ℂ) : ℤ :=
  ∑ t : D.what₂.Tau, if σ = DV.tauEmb D t then ∑ i ∈ Finset.Icc (j + 1) N, l (D.eTau t) i else 0

def degLatPiece {Z B : ct.Mdl} (L : Lat B) {k : Type} [Field k] (c : Curve k Z.X) (τ : PsiT D) (i : ℕ) : ℤ :=
  c.degLat L (-ct.expo (indWt τ i))

end At

def crhOf (ct : At S κ p) (P : ∀ B : ct.Mdl, Lat B → Prop) (hf : ∀ Z, FlagFam P Z) : CrHSt ct (flgOf ct P) where
  nefHT Z l := ∀ c : Curve ct.Fbar (ct.flagCl Z (hf Z).1).X,
    0 ≤ -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 N, l τ i * (ct.degLatPiece (hf Z).lat c τ i : ℝ)
  descK Z l := Descends (ct.flagCl Z (hf Z).1) (hf Z).lat κ.l (ct.expo l) (ct.diffExpo l)
  bdryLoci Z := ∃ s : Set ct.Sum1, s.Finite ∧
    (∀ x : ct.SpPt (ct.flagCl Z (hf Z).1), (∃ z, ¬ Mdl.abP _ (x.1 z)) → ∃ l ∈ s, ct.redFlag x ∈ ct.locus l) ∧
    ∀ l ∈ s, dim (ct.locus l) + D.R.f * (N - 1) = D.R.f * (N * (N - 1) / 2)
  htFlags := hf
  YsP Z := ct.SpPt (ct.flagCl Z (hf Z).1)
  ysBd x := ∃ z, ¬ Mdl.abP _ (x.1 z)
  FlP := ct.FlP
  hFl x := ct.redFlag x
  FlCl := Closeds ct.FlP
  flMem F s := F ∈ s
  flDim := dim
  Sum1 := ct.Sum1
  locus := ct.locus
  bdryLoci_def _ := Iff.rfl
  CrvS Z := Curve ct.Fbar (ct.flagCl Z (hf Z).1).X
  degGr c := ct.degLatPiece (hf _).lat c
  nefHT_def _ _ := Iff.rfl

end GlobalTheory.LocM
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.LocM

variable {D : D7} {A : Amb D} {N j : ℕ}

structure StFam (S : Sig A N j) (κ : Lv A) : Type 1 where
  st : ∀ {p : ℕ} (ct : At S κ p), Stages ct
  α : ℕ → ℕ → 𝓞 D.host.E
  hα : ∀ {p : ℕ} (ct : At S κ p), (st ct).locB.alp = α p

abbrev Ats (S : Sig A N j) (κ : Lv A) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → At S κ p

variable {S : Sig A N j} {κ : Lv A}

def Ats.Over (cts : Ats S κ) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (v : PlL D p), (cts p v).W = placeW D p v (jC p v)

def Stages.fix {p : ℕ} {ct : At S κ p} (st : Stages ct) : Stages ct := { st with mo := motTrue ct, ky := keyTrue ct }

structure LocAt (S : Sig A N j) (κ : Lv A) (p : ℕ) : Type 1 where
  loc : ModuliIntegralCharts.Loc D N j p
  ex : ModuliIntegralCharts.ExtA D loc
  locB : p.Prime → BoundaryLocalData.LocB D loc
  pbKF : ∀ {c : ℕ}, ngTrue.KF (D.R.f * N) c → loc.Sec (loc.keySh c)
  bc : CodeAt S κ → loc.Mdl


open Classical in
def bcAt {p : ℕ} (ct : At S κ p) (Z : CodeAt S κ) : ct.Mdl :=
  if h : ∃ Z', IsBCAt ct Z Z' then h.choose else ct.Xm

def primeAt (F : StFam S κ) (cts : Ats S κ) (p : ℕ) [Fact p.Prime] : LocAt S κ p :=
  haveI : Fintype (PlL D p) := finPl D p
  haveI : Nonempty (PlL D p) := plL_ne D p
  { loc := Loc.pi fun v => (F.st (cts p v)).fix.loc
    ex := ExtA.pi fun v => (F.st (cts p v)).fix.ex
    locB := fun _ => LocB.pi (fun v => (F.st (cts p v)).fix.locB) (F.α p) fun v => F.hα (cts p v)
    pbKF := fun kf v => (cts p v).pbKF kf
    bc := fun Z v => bcAt (cts p v) Z }

def fillAt (S : Sig A N j) (κ : Lv A) (p : ℕ) (hp : ¬ p.Prime) : LocAt S κ p where
  loc := (exists_loc_extA_nat D N j p).choose
  ex := (exists_loc_extA_nat D N j p).choose_spec.some
  locB h := absurd h hp
  pbKF _ := @Zero.zero _ (((exists_loc_extA_nat D N j p).choose.secAdd _).toZero)
  bc _ := (exists_loc_extA_nat D N j p).choose.Xm

def locAt (F : StFam S κ) (cts : Ats S κ) (p : ℕ) : LocAt S κ p :=
  if hp : p.Prime then @primeAt _ _ _ _ _ _ F cts p ⟨hp⟩ else fillAt S κ p hp

def locStOf (F : StFam S κ) (cts : Ats S κ) : LocSt D N j ngTrue where
  loc p := (locAt F cts p).loc
  ex p := (locAt F cts p).ex
  locB p := (locAt F cts p).locB
  pbKF p := (locAt F cts p).pbKF

def globStOf (F : StFam S κ) (cts : Ats S κ) : GlobSt fun p => ((locStOf F cts).loc p).Mdl where
  Xg := CodeAt S κ
  bc p := (locAt F cts p).bc
  DivG Z := CDiv Z.X
  effD B := B.Eff
  noVertD {Z} B := Z.NoVert B
  posBdD {Z} B := Z.PosBd B
  ampleOnAbelianBase Z m B := Z.AmpleHodge m B
  Met := QLB S.sys.Y κ.c κ.good
  nefFibM := QLB.NefFib
  ampleGen := QLB.AmpleGen
  limRA := QLB.LimRA

end GlobalTheory.LocM
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.TorRef

section Fun

variable {O : Type} [CommRing O]

def resInt (O : Type) [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) : InvFun O where
  toFun n B := φ.eval (Fin n → O) B
  inv n m r hr B := φ.eval_comp (r := r.restrictScalars ℤ) hr B
  zero B := by
    rw [φ.eval_eq (n := 0) (r := 0) fun a => ⟨0, Subsingleton.elim _ _⟩]
    exact φ.zero _

def IsTame (φ : InvFun O) : Prop :=
  (∀ (n k : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), φ.toFun n (fun a b => k * B a b) = k * φ.toFun n B) ∧
    ∀ n B, 0 ≤ φ.toFun n B

end Fun

section Cones

variable {R : Type} [CommRing R] [IsDomain R]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def Refines (H : Host E) (q : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) : Prop :=
  IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ IsTwInv H φ ∧ IsPosFn H φ ∧ IsTame φ ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ →
        (resInt (𝓞 E) φs).LinearOn γ ∧ ∀ N ∈ 𝒩, IsFine N γ

end Cones

end GlobalTheory.TorRef
end
end
