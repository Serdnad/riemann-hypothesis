module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

def tensφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] {r : ℕ} (x : Fin r → (T ⟶ B)) :
    (Fin r × Fin r) × Fin 4 → (T.left ⟶ B.left) := fun k => GlobalTheory.PolDeg.lamPts (x k.1.1) (x k.1.2) k.2

def tensε {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) : (Fin r × Fin r) × Fin 4 → ℤ := fun k => W k.1.1 k.1.2 * Oε k.2

structure Tens (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) where

  pr : Fin r → (D'.P.A ⟶ D.P.A)
  pr_hom : ∀ i, IsMonHom (pr i)

  lim : IsLimit (Fan.mk D'.P.A pr)

  xe : D'.X ≃+ (Fin r → D.X)
  c_pr : ∀ z i, D'.c z ≫ pr i = D.c (xe z i)

  w : LB.Iso D'.P.L (LB.LinComb D.P.L (tensφ pr) (tensε W))
  w_gen : w.IsGen
  psi : ∀ y z J J', Good D.P.L z J → Good D'.P.L z J' →
    val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) *
      ∏ i, ∏ j, val (D.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j

def Tens.IsAct {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W) {O : Type} [CommRing O] [StarRing O]
    [Module O D'.X] (o : D'.OAct O) (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) : Prop :=
  letI := D.P.isAb.comm
  (∀ a z i, T.xe (a • z) i = ∑ j, ρ a i j • T.xe z j) ∧ ∀ a i, o.onB.act a ≫ T.pr i = ∏ j, T.pr j ^ ρ a i j

def GalEqN {D : DegPre R} {A : PolAV (Sp (FractionRing R))} (n : ℕ) (lab : Labels D A) : Prop :=
  ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (j : ℕ) (p p' : QkPt D (Kb R) (n ^ j)), QkExt σ.toRingHom p p' →
    (lab (n ^ j) p').left = spMap σ.toRingHom ≫ (lab (n ^ j) p).left

end

abbrev SecK {X Y : Scheme.{0}} (L : LB X) (h : Y ⟶ X) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ)))

def Agree {X Y Y' : Scheme.{0}} (L : LB X) {h : Y ⟶ X} {h' : Y' ⟶ X} {k : ℕ} (s : SecK L h k) (s' : SecK L h' k) : Prop :=
  ∀ (Z : Scheme.{0}) (p : Z ⟶ Y) (p' : Z ⟶ Y'), p ≫ h = p' ≫ h' → ∀ z J, Good L z J → sval s p z J = sval s' p' z J

def TraitReg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) (L : LB G.left)
    {Y : Scheme.{0}} {α : Y ⟶ G.left} {k : ℕ} (s : SecK L α k) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W')
      (σ : SecK L (pullback.fst G.hom (spMap io ≫ ξ)) k), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ Agree L σ s

structure UCover (R : Type) [CommRing R] [IsDomain R] extends Modif R where

  G : Over S
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  P : GlobalTheory.UU.CP G

  A : PolAV (Sp (FractionRing R))

  α : A.A.left ⟶ G.left
  α_cart : IsGrpPullback A.A G gp α
  α_lb : LBIso A.L (P.L.L.pull α)
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ S),
    Function.Injective φ → ξ ≫ π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W' (maximalIdeal W'))
      (A' : PolAV (Sp (FractionRing W'))) (U' : Unif (maximalIdeal W') D' A' G'),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      LBIso U'.LG.L (P.L.L.pull β)

attribute [instance] UCover.grp UCover.comm

structure Secs {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G] (L : LB G.left)
    {A : Scheme.{0}} (α : A ⟶ G.left) where

  N : ℕ

  k : ℕ

  s : Fin (N + 1) → SecK L α k

  θ : SecK L α 1

  Y : Over (Sp (ResidueField R))
  [grp : GrpObj Y]
  smooth : Smooth Y.hom

  j : Y.left ⟶ PSpace R N
  j_over : j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R)
  imm : IsImmersion j

  O : Y.left.Opens
  O_ne : (O : Set Y.left).Nonempty
  trait : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W) (ξ : Sp W ⟶ M.S),
    Function.Injective φ → IsLocalHom φ → ξ ≫ M.π = spMap φ →
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W') (G' : Over (Sp W'))
      (_ : GrpObj G') (β : G'.left ⟶ G.left) (σ : Fin (N + 1) → SecK L β k) (θ' : SecK L β 1)
      (κ : ResidueField R →+* ResidueField W')
      (e : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ)).obj Y),
      GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsGrpPullback G' G (spMap io ≫ ξ) β ∧
      κ.comp (residue R) = (residue W').comp (io.comp φ) ∧ IsMonHom e.hom ∧ (∀ i, Agree L (σ i) (s i)) ∧ Agree L θ' θ ∧
      ∀ (Ω : Type) [Field Ω] (p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left) (p' : Sp Ω ⟶ G'.left)
        (y : Sp Ω ⟶ Y.left), p' = p ≫ pullback.fst G'.hom (spMap (residue W')) →
        y = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) →
        (∃ hs, GlobalTheory.ProjSpace.toProj (p' ≫ G'.hom ≫ spMap (io.comp φ)) (fun i => GlobalTheory.secPull (σ i) p') hs = y ≫ j) ∧
        ∀ x : Sp Ω, y x ∈ O → p' x ∈ nonzeroLocus θ'

attribute [instance] Secs.grp

namespace TraitWit

section Tensor
open GlobalTheory.ToricData InhTate
variable {K : Type} [CommRing K] [IsDomain K] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

end Tensor

section Cover
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

end Cover

section Sections
variable {X Y Y' : Scheme.{0}}

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]


end Sections

end TraitWit

end GlobalTheory.Mum
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

@[reducible] def GlobalTheory.ZH.ThetaSys.rechart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (c : Ω) (hc : c ≠ 0)
    (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c * S.th x ∈ R')
    (hev : ∀ x i, c * S.ev x i ∈ R') : ThetaSys o Ω :=
  { S with
    th := fun x => c * S.th x
    ev := fun x i => c * S.ev x i
    R := R'
    fg := fg
    frac := frac
    th_mem := hth
    ev_mem := hev
    supp := by simpa [hc] using S.supp
    th_ne := S.th_ne.imp fun _ h => mul_ne_zero hc h }

namespace GlobalTheory.Poinc

variable {g n : ℕ}


open MonObj in
def IsDiagEnd (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) : Prop :=
  ∃ c : SiegPre g n (zetaAway n) (u ≫ F.s), SiegPB c F.univ u ∧ ∃ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
    ∀ E a, ε E ≫ pr a = ((List.finRange 8).map fun b => pr b ^ E a b).prod

def Same {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ρ' : S'.Real)
    (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') : Prop :=
  ∃ (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left)
    (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)),
    IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a ∧ IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a' ∧
    LBIso P₀.L (ρ.P.L.pull a) ∧ LBIso P₀.L (ρ'.P.L.pull a') ∧
    (∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left) ∧
    ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left

variable {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

abbrev ModN (m : ℕ) (X : Type) [AddCommGroup X] : Type := X ⧸ (nsmulAddMonoidHom m : X →+ X).range

def IsLab (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)),
    Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧
    R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧
      ∃ (u : ρ'.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X)),
        (∀ χ, l.q χ = c.sc * (qW W c.T.β (j χ) : ℤ)) ∧
        (∀ a χ, l.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
        ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
          (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε' E).left →
          CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)

structure Deep (X₁ : Setup F W i) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) where

  X : Setup F W i

  ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)
  diag : IsDiagEnd F W X.ρ.P X.u ε
  [alg : Algebra X₁.Ω₁ X.Ω₁]
  fd : FiniteDimensional X₁.Ω₁ X.Ω₁
  gal : IsGalois X₁.Ω₁ X.Ω₁
  proj : IsProjOver X.M.s

  q : X.M.Z ⟶ X₁.M.Z
  fin : IsFinite q
  gen : X.M.pt ≫ q = spMap (algebraMap X₁.Ω₁ X.Ω₁) ≫ X₁.M.pt
  comp : q ≫ X₁.π = X.π

  m : ℕ
  sq : X.S.N = m ^ 2
  dvd : X₁.S.r * X₁.S.N ∣ m

  lab : X₁.S.Gam →+ X.S.Gam
  same : Same X₁.ρ ε₁ X.ρ ε lab (algebraMap X₁.Ω₁ X.Ω₁)
  lab_range : ∀ x : X.S.Gam, ∃ a, lab a = (X.S.r * X.S.N / (X₁.S.r * X₁.S.N)) • x

attribute [instance] Deep.alg

namespace Deep

variable {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (D : Deep X₁ ε₁)

@[reducible] def lift {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) :
    CTrait D.X p (y (cPt p)) where
  y := y
  cen := rfl
  T := c.T
  ι := c.ι
  int := c.int
  comm := by rw [← D.comp, ← Category.assoc y, h, c.comm]

def Compat {X : Type} [AddCommGroup X] (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) X)
    (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) X) : Prop :=
  ∀ a μ, yy₁ a = QuotientAddGroup.mk μ →
    yy (D.lab a) = QuotientAddGroup.mk ((D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • μ)

end Deep

end GlobalTheory.Poinc
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def MinAt5 (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) : Prop :=
  ∃ (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
    (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
    (_ : IsCommMonObj G) (N : ℕ),
    (IsThetaCompact F z i ∧ IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
    (β.Finite ∧ Function.Injective β ∧ IsProjOver s' ∧ IsNormalScheme S' ∧ Dense (U : Set S') ∧ IsFinite c ∧
      Surjective c ∧ U.ι ≫ π = c ≫ i ∧ π ≫ z = s' ≫ spMap β ∧ Surjective π ∧ IsProper π ∧
      IsNoetherian Z) ∧
    (IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
      IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e) ∧
    (1 ≤ N ∧ LBIso (OZ.pull π) (lbPow (hodge G g) N))

theorem MinAt5.isThetaCompact {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {z : Z ⟶ Sp (cycAway n)} {i : F.X ⟶ Z} {OZ : LB Z}
    (h : MinAt5 F z i OZ) : IsThetaCompact F z i ∧ OZ.IsLB ∧ IsAmpleLB OZ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨h₁, -, -, -, -, h₂, h₃⟩, -⟩ := h
  exact ⟨h₁, h₂, h₃⟩

def MinSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∃ (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ

def ChartSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt5 F z i OZ → BlowAt F z i φ d π j BD →
      SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) ∧ ∀ x : S, PreChart F (π ≫ z) j φ BD d x

def DescSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      BlowAt F z i φ d π j BD → (∀ x : S, PreChart F (π ≫ z) j φ BD d x) →
      ∃ (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
        IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j

end GlobalTheory.SiegJoin
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Model

variable {V : Type} [CommRing V] [IsDomain V]

theorem isMonomialTau_of_tauIn {Q : Data V} {τ₀ : Gens Q} {N : ℕ} {s : Fin N → V}
    {ε : Fin N → LinearMap.BilinForm ℤ Q.X} (h : TauIn Q τ₀ s ε) : Q.IsMonomialTau s ε := by
  intro a b
  obtain ⟨hg, k, hk, hv⟩ := h a b
  exact ⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩

end GlobalTheory.Poinc.Sep.Model
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def SharpRef (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X) : Prop :=
  ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
    (∀ a, IsMonHom (pr a)) ∧
    (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
    w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
    ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b

def IsThetaTerms (D : DegPre V₁) (N₁ : ℕ) {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) : Prop :=
  ∃ (th : Fam D (FractionRing V₁) 1) (g : C → GtPtF D (FractionRing V₁)) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A))
    (w : ∀ c, Frm D (FractionRing V₁) 1 (g c).b),
    (∀ c, (g c).b = toUnit _ ≫ b c) ∧ (∀ c, ∃ o, GtPtF.IsNsmul N₁ (g c) o ∧ o.IsZero) ∧
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) ∧
    (∀ c, (w c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val (w c) (𝟙 _) z J ^ (N₁ ^ 2) * val κ (g c).b.left z J = 1) ∧
    (∀ mu c, IsCoef 1 (g c) (w c) (e mu) (th.s (e mu)) (algebraMap V₁ (FractionRing V₁) (T mu c))) ∧
    ∃ c, T 0 c = 1

section Real

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  (X₁ : Setup F W i) (z₁ : X₁.M.Z) {N₁ : ℕ} (Φ : VSys (id : ℤ → ℤ) g W N₁ (X₁.M.Z.presheaf.stalk z₁))

def HasTraits : Prop :=
  ∀ (T : Trait F) (ev : X₁.M.Z.presheaf.stalk z₁ →+* T.V), IsLocalHom ev →
    jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = T.y ≫ i →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃+ T.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.β (e a) (e b)

def IsChartMember [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ Z) {m : ℕ} (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X)
    (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃+ Q.X) (h : Fin (Φ.m y) ≃ Fin m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ X₁.M.Z.fromSpecStalk z₁ ≫ X₁.π = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k = ρ (t (h k)) ∧ ∀ a b, Φ.δ y k a b = δ (h k) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (e₈ : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e₈ ∧
      IsThetaTerms D N₁ e₈ fun mu c => Φ.u y (fun a => e.symm (mu a)) c * mono W (Φ.t y) (Φ.δ y) fun a => e.symm (mu a)

end Real

def Elements {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) (φ : InvFun O) (d : ℕ)
    (ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y)) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  ∃ (O' : Subring (Φ.V y)) (g₀ : Φ.V y) (b : Fin (Φ.m y) → ℕ), (∀ h ∈ O', ev h ∈ k₀ ∧ (h ∈ maximalIdeal (Φ.V y) → ev h = 0)) ∧
    (∀ k, (b k : ℝ) = d * φ.evalZ (Φ.δ y k)) ∧ Associated g₀ (∏ k, Φ.t y k ^ b k) ∧
    ∀ (D l : ℕ) (a : Fin l × Fin s → Φ.X y), Dominant bar φ (D * d) N₁ W ga a → ∀ (c : Fin l → Φ.Q) (e : ℕ), ∃ h ∈ O',
      h * g₀ ^ D - Φ.coefT y a c * Φ.monoT y a ∈
        Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e

def Values {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
    [IsLocalRing A] (Φ : VSys bar q W N₁ A) (y : Φ.Y) {K : Type} [Field K] (ev : Φ.V y →+* K) (k₀ : Subfield K) : Prop :=
  (∀ k, ev (Φ.t y k) = 0) ∧
  (∀ mu c c', IsUnit (Φ.u y mu c') → ∃ r ∈ k₀, ev (Φ.u y mu c) = r * ev (Φ.u y mu c')) ∧
  ∀ lam : LinearMap.BilinForm ℤ (Φ.X y) →ₗ[ℤ] ℤ, (∀ k, lam (Φ.δ y k) = 0) →
    ∃ (l l' M : ℕ) (a : Fin l × Fin s → Φ.X y) (a' : Fin l' × Fin s → Φ.X y) (c : Fin l → Φ.Q) (c' : Fin l' → Φ.Q), 1 ≤ M ∧
      IsUnit (Φ.coefT y a c) ∧ IsUnit (Φ.coefT y a' c') ∧ (∀ β ∈ balForms bar (Φ.X y), lin W a β - lin W a' β = M * lam β) ∧
      ∃ r ∈ k₀, ev (Φ.coefT y a c) = r * ev (Φ.coefT y a' c')

end GlobalTheory.Poinc.Sep
end
end
