module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle042
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

section Met

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

abbrev PolOf (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

def metTrue (x : ToroidalCompactificationData s) (Φ : s.Flag) (P : PolOf x Φ) : MetIn Φ where
  hm := metsOf x Φ
  h0 := refMet x Φ
  r := rFlag x Φ
  ab := P.ab
  dir := P.dir
  reg := P.reg

end Met

namespace Setup

variable {D : D7} (O : Setup D)

structure CoreWith (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) : Prop where
  met : O.met = metTrue x O.Φ P
  Mb : O.Mb = mbarOf P
  bd : IsBdOf x O.L O.B
  fl : O.fl = flBetti O.s O.Φ O.L

def Core : Prop := ∃ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P

namespace CoreWith

variable {O} {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} (h : O.CoreWith x P)
include h

end CoreWith

namespace Core

variable {O} (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ)
include h

end Core

end Setup

end GlobalTheory.Mean4O
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

section Char

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
  {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']

def EndChar (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X) : Prop :=
  ∀ (κ : Type) [Field κ] (a : R →+* κ) (ha : ∀ x ∈ maximalIdeal R ^ (0 + 1), a x = 0) (G₀ : Over (Sp κ)) [GrpObj G₀]
    (φ : G₀.left ⟶ G.left) (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀), f₀.left ≫ φ = φ ≫ f.left →
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) m ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h

def CoordMap (D : DegPre R) (D' : DegPre V) (g : R →+* V) (ρ : D.X →+ D'.X) : Prop :=
  ∀ y r r', PsiCoord D y r → PsiCoord D' (ρ y) r' → Associated (g r) r'

def EquivMap (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (β : G'.left ⟶ G.left)
    (ρ : D.toPre.X →+ D'.toPre.X) : Prop :=
  ∀ (f : G ⟶ G) (f' : G' ⟶ G'), IsMonHom f → IsMonHom f' → f'.left ≫ β = β ≫ f.left →
    ∀ m m', EndChar U f m → EndChar U' f' m' → ∀ y, ρ (m y) = m' (ρ y)

end Char

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

def SharpBy (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) : Prop :=
  SiegPB c F.univ u ∧ (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

theorem sharpOver_iff (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) :
    SharpOver F W P u ↔ ∃ c pr, SharpBy F W P u c pr :=
  ⟨fun ⟨c, h, pr, h'⟩ => ⟨c, pr, h, h'⟩, fun ⟨c, pr, h, h'⟩ => ⟨c, h, pr, h'⟩⟩

def MatEnd {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (a b : Fin 8) (f : B ⟶ B) : Prop :=
  IsMonHom f ∧ ∀ w, f ≫ pr w = if w = a then pr b else 1

def MatRel (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) : Prop :=
  ∀ v, ∑ u, (W + W.transpose) v u • y' u = if v = b then ∑ u, (W + W.transpose) a u • y u else 0

def IsCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] (j : O →+* R) : Prop :=
  ∃ e : AdicCompletion (maximalIdeal O) O ≃+* R, ∀ a, e (algebraMap O _ a) = j a

theorem isCpl_self (O : Type) [CommRing O] [IsLocalRing O] :
    IsCpl (algebraMap O (AdicCompletion (maximalIdeal O) O)) :=
  ⟨RingEquiv.refl _, fun _ => rfl⟩


open Classical in
def MatOn {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) : Prop :=
  IsMonHom f ∧ ∃ f₁ : ρ.P.A ⟶ ρ.P.A, MatEnd pr a b f₁ ∧
    ((Over.pullback FinalForm.u₀).map f₁).left ≫ FinalForm.φ = FinalForm.φ ≫ f.left

end GlobalTheory.Poinc.Eq8
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section

variable {R : Type} [CommRing R] [IsDomain R]

structure Factor (D D' : DegPre R) where

  O : Type
  [ring : Ring O]
  [star : StarRing O]
  [mod : Module O D'.X]

  o : D'.OAct O

  e : O

  f : O

  inc : D.P.A ⟶ D'.P.A

  pr : D'.P.A ⟶ D.P.A

  xi : D.X →+ D'.X

  xp : D'.X →+ D.X

  w : letI := D.P.isAb.comm; letI := D'.P.isAb.comm
    LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D'.P.A D'.P.L).pull
      (lift (fst D.P.A D.P.A ≫ inc) (snd D.P.A D.P.A ≫ inc ≫ o.onB.act f) : G2 D.P.A ⟶ G2 D'.P.A).left)
  idem : e * e = e
  inc_hom : IsMonHom inc
  pr_hom : IsMonHom pr
  inc_pr : inc ≫ pr = 𝟙 _
  pr_inc : pr ≫ inc = o.onB.act e
  xp_xi : ∀ y, xp (xi y) = y
  xi_xp : ∀ z, xi (xp z) = e • z
  c_xi : ∀ y, D'.c (xi y) = D.c y ≫ inc
  inj : Function.Injective fun y => Star.star e • f • xi y
  onto : ∀ z, ∃ y, Star.star e • z = Star.star e • f • xi y
  w_gen : w.IsGen
  tau : ∀ a b z J J', Good D'.P.L z J → Good D.P.L z J' →
    val (D.tau a b) (𝟙 _) z J' =
      GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J J' *
        val (D'.tau (xi a) (f • xi b)) (𝟙 _) z J

attribute [instance] Factor.ring Factor.star Factor.mod

def SamePol (D D' : DegPre R) : Prop :=
  ∃ (Q : GlobalTheory.PolDeg.Data R) (e : D.X ≃+ Q.X) (e' : D'.X ≃+ Q.X),
    GlobalTheory.PolDeg.Refines Q (RingHom.id R) D e ∧ GlobalTheory.PolDeg.Refines Q (RingHom.id R) D' e'

abbrev Kb (R : Type) [CommRing R] [IsDomain R] : Type := AlgebraicClosure (FractionRing R)

abbrev Labels (D : DegPre R) (A : PolAV (Sp (FractionRing R))) : Type :=
  ∀ k : ℕ, QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)

def Induces {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegPre R} {A : PolAV (Sp (FractionRing R))}
    (lab : Labels D A) (φ : R →+* W) {D' : DegData W I} {A' : PolAV (Sp (FractionRing W))} {G' : Over (Sp W)} [GrpObj G']
    [IsCommMonObj G'] (U' : Unif I D' A' G') (hD : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left) (k : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F),
    (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r))) →
    ∀ (p : QkPt D (Kb R) k) (p₁ : QkPt D F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := W) F ⟶ A'.A),
      QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD F p₁.g p'.g →
      x'.left ≫ a = spMap em.toRingHom ≫ (lab k p).left → QkToAkU U'.toUnifPre F k p' x'

def IsFib {W : Type} [CommRing W] [IsDomain W] (φ : R →+* W) (A : PolAV (Sp (FractionRing R)))
    (A' : PolAV (Sp (FractionRing W))) (a : A'.A.left ⟶ A.A.left) : Prop :=
  ∃ ga : FractionRing R →+* FractionRing W, (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
    IsGrpPullback A'.A A.A (spMap ga) a ∧ LBIso A'.L (A.L.pull a)

def OneTrait [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (lab : Labels D A) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (U' : Unif (maximalIdeal W) D' A' G') (hD : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left)
    (_ : Algebra (FractionRing R) (Kb W)) (em : Kb R →ₐ[FractionRing R] Kb W),
    GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsSemiAbelian G' ∧ IsFib φ A A' a ∧
    (∀ r, algebraMap (FractionRing R) (Kb W) (algebraMap R _ r) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧
    ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D (Kb R) k) (p₁ : QkPt D (Kb W) k) (p' : QkPt D'.toPre (Kb W) k)
      (x' : TFK (R := W) (Kb W) ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD (Kb W) p₁.g p'.g →
      x'.left ≫ a = spMap em.toRingHom ≫ (lab k p).left → QkToAkU U'.toUnifPre (Kb W) k p' x'

end

structure Emb {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (G : Over S) [GrpObj G] where

  N : ℕ

  H : G.left.Opens
  H_all : ∀ g : G.left, π (G.hom g) = closedPoint R → g ∈ H

  f : H.toScheme ⟶ PSpace R N
  f_over : f ≫ PSpace.str R N = H.ι ≫ G.hom ≫ π

  Y : Over (Sp (ResidueField R))
  [grp : GrpObj Y]
  smooth : Smooth Y.hom

  j : Y.left ⟶ PSpace R N
  j_over : j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R)
  imm : IsImmersion j
  fib : ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : ResidueField R →+* Ω), x ≫ π = spMap (κ.comp (residue R)) →
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω')
      (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y)
      (l : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ H.toScheme), IsMonHom e.hom ∧
      l ≫ H.ι = pullback.fst G.hom (spMap io ≫ x) ∧ l ≫ f = e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) ≫ j

attribute [instance] Emb.grp

def Emb.Theta {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (E : Emb π G)
    (L : LB G.left) : Prop :=
  ∃ (θ : L.Sec) (O : E.Y.left.Opens), (O : Set E.Y.left).Nonempty ∧ ∀ (g : E.H.toScheme) (y : E.Y.left), y ∈ O →
    π (G.hom (E.H.ι g)) = closedPoint R → E.f g = E.j y → ∃ i : L.ι, E.H.ι g ∈ G.left.basicOpen (θ.f i)

namespace Wit
open InhTate Inh

end Wit

end GlobalTheory.Mum
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.RepFamModel
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem objMap_refl {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) :
    Nonempty (ObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }⟩

variable {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
  {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

end GlobalTheory.UPel.HT.RepFamModel
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

variable {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def ThAt (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {N : ℕ} (f : F.X ⟶ PSpace (cycAway n) N) : Prop :=
  P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ Odd m ∧ 3 ≤ m ∧ IsUnit (m : cycAway n) ∧
    N + 1 = m ^ (4 * (8 * g)) ∧ f ≫ PSpace.str (cycAway n) N = F.s ∧ ThMap P.A P.L rig m (𝟙 F.X) f ∧ IsE8 W

def QFin {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}

def SymE {S : ThetaSys o Ω} (ρ : S.Real) (m : ℕ) {N : ℕ} (e : Fin N → Ω) : Prop :=
  N = m ^ (4 * S.g) ∧ (m : Ω) ≠ 0 ∧ SymAt ρ.P.A ρ.P.L ρ.rig m (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R))
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ S.R.val.toRingHom) e

def SysAt (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) : Prop :=
  β.Finite ∧ Function.Injective β ∧ S.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W ρ.P u ∧
    u ≫ F.s = spMap (algebraMap o S.R) ≫ spMap β

def LevAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (Y : RatModel o Ω) (q : Y.Z ⟶ F.X) : Prop :=
  Geo.Tor.IsNormalScheme Y.Z ∧ IsFinite q ∧ Surjective q ∧ q ≫ F.s = Y.s ≫ spMap β ∧
    Y.pt ≫ q = spMap S.R.val.toRingHom ≫ u

def OpenAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (M : RatModel o Ω) (U : M.Z.Opens)
    (c : U.toScheme ⟶ F.X) : Prop :=
  (U : Set M.Z).Nonempty ∧ IsFinite c ∧ Surjective c ∧ c ≫ F.s = U.ι ≫ M.s ≫ spMap β ∧
    ∀ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt → x ≫ c = spMap S.R.val.toRingHom ≫ u

def MinorAt (S : ThetaSys o Ω) (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) : Prop :=
  X.IsNm S.th ∧ IsProjOver X.s ∧ Geo.Tor.IsNormalScheme X.Z ∧ S.Over₀ M U₀ ∧ S.IsEE M U₀ EE ∧ X.IsHom M (AlgHom.id o Ω) f ∧
    (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab)

def SameScale (M : RatModel o Ω) {I J : Type} (a : I → Ω) (b : J → Ω) (D : ℕ) : Prop :=
  ∀ z i, M.Div a i z → ∃ j, M.Div b j z ∧ a i ^ D / b j ∈ M.O z ∧ b j / a i ^ D ∈ M.O z

end GlobalTheory.SiegTh

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc.Basic₂

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ}

theorem trait_nonneg (T : Trait F) (x : T.D.toPre.X) : 0 ≤ T.β x x := by
  simpa using T.mono.nonneg 0 x

end GlobalTheory.Poinc.Basic₂
end
end

section

set_option autoImplicit false


noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovHt

section Steps

open _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i)

def ShortAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ abelian₂ : ℝ, (∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)),
      IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂) ∧
    Real.log abelian₂ * (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ C * unitE p

def GeomAt (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) ∧
    GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0) ∧ (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1

def MultAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧
    ∀ Z, Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc

def BudgetAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  Y.d.l₂.M'.primeFactors.card ≤ 15 ∧
  ∃ g : ℝ, WtGap (uPrime (dat p i) u1) g ∧ 0 ≤ errX (ell D) (uPrime (dat p i) u1) g ∧
    lenT p i PP * errX (ell D) (uPrime (dat p i) u1) g ≤ C * unitE p ∧
    0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) ∧
    lenT p i PP * (htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1)) ≤ C * unitE p

end Steps

end GlobalTheory.CovHt

end
end
