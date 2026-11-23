module

public import Formalism.HermitianLattices.StatementLat
public import Formalism.HermitianLattices.Bundle001
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
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
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

section

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula

open Formalism.DivisionValues Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K]

def primePow (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Submodule (𝓞 K) K :=
  (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

def scaledAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) (B : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d → K) :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (primePow w n) B)

variable [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}


end GlobalTheory.IndefiniteRowSideFullHecke.ScaledValuationFormula
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lie

variable {S : Scheme.{0}} {R : Type} [CommRing R]

abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)

variable {G : Over S} [GrpObj G]

def IsCombAt {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsEigAt {O : Type} [CommRing O] (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsEigBasis {O : Type} [CommRing O] (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigAt act x χ (v i)) ∧ ∀ w, IsEigAt act x χ w → ∃! c : Fin n → R, IsCombAt c v w

end Lie

def gramSq {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin n → (Fin g → ℂ)) : ℝ :=
  (Matrix.of fun a b => (Real.pi : ℂ) * (z a ⬝ᵥ Hm.mulVec (star (z b)))).det.re

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def embF (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F where
  toFun a := ⟨τ (a : E), c.conj τ a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

def embFc (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F := (embF c τ).comp (H.bar : 𝓞 E →+* 𝓞 E)

variable {Xo : Moduli D l} {c : Coeff l}

def cpt (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) : Set Y.X :=
  closure (Y.j '' (U : Set (Xo.XF c)))

abbrev Rule (Y : Model Xo c (RingHom.id c.F)) : Type 1 :=
  ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.X), (Fin D.p → (epsAt x ⟶ Y.t.G)) → (Fin D.q → (epsAt x ⟶ Y.t.G)) → R

def IsFrame (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) {R : Type} [CommRing R]
    (j : c.F →+* R) (x : Sp R ⟶ Y.X) (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  x ≫ Y.s = spMap j ∧ Set.range x ⊆ cpt Y U ∧
    IsEigBasis Y.t.act x (j.comp (embF c τ)) v ∧ IsEigBasis Y.t.act x (j.comp (embFc c τ)) w

def IsDetSection (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : Rule Y) : Prop :=
  (∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) (v v' : Fin D.p → (epsAt x ⟶ Y.t.G))
      (w w' : Fin D.q → (epsAt x ⟶ Y.t.G)) (M : Matrix (Fin D.p) (Fin D.p) R) (N : Matrix (Fin D.q) (Fin D.q) R),
      IsFrame Y U τ j x v w → IsFrame Y U τ j x v' w' →
      (∀ i, IsCombAt (M i) v (v' i)) → (∀ i, IsCombAt (N i) w (w' i)) →
      sig R x v' w' * M.det = sig R x v w * N.det) ∧
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (j : c.F →+* R) (x : Sp R ⟶ Y.X)
      (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G))
      (v' : Fin D.p → (epsAt (spMap φ ≫ x) ⟶ Y.t.G)) (w' : Fin D.q → (epsAt (spMap φ ≫ x) ⟶ Y.t.G)),
      IsFrame Y U τ j x v w →
      (∀ i, (v' i).left = spMap (Chart.dualMapR φ) ≫ (v i).left) →
      (∀ i, (w' i).left = spMap (Chart.dualMapR φ) ≫ (w i).left) →
      sig R' (spMap φ ≫ x) v' w' = φ (sig R x v w)

end GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

section Lie

variable {R : Type} [CommRing R]

def lieAdd (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (x y : LieG G) : LieG G :=
  ⟨x.1 * y.1, by
    rw [MonObj.comp_mul, x.2, y.2]
    exact mul_one (1 : specO R R ⟶ G)⟩

def lieMap {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u]
    (x : LieG T) : LieG G :=
  ⟨x.1 ≫ u, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩

def LieCongr (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (I : Ideal R) (x y : LieG G) : Prop :=
  ∃ a ∈ I, ∃ z : LieG G, x = lieAdd G y (lieScale G a z)

def IsLieLinear {G H : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj H]
    (f : LieG G → LieG H) : Prop :=
  (∀ x y, f (lieAdd G x y) = lieAdd H (f x) (f y)) ∧
    ∀ (a : R) (x : LieG G), f (lieScale G a x) = lieScale H a (f x)

abbrev torus (R : Type) [CommRing R] (r : ℕ) : Over (Spec (CommRingCat.of R)) :=
  splitTorus (Spec (CommRingCat.of R)) (Fin r → ℤ)

def lieCoord {r : ℕ} (x : LieG (torus R r)) (i : Fin r) : R :=
  TrivSqZeroExt.snd (R := R) (M := R)
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).hom.hom
      (x.1.left.appTop.hom (charUnit (Spec (CommRingCat.of R)) (Fin r → ℤ) (Pi.single i 1)).val))

end Lie

abbrev baseChange (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) ⥤ Over (Spec (CommRingCat.of A)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))

end GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps
end
end
