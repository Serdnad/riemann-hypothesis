module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def conjIdeal (H : Host E) (P : Ideal (𝓞 E)) : Ideal (𝓞 E) := P.map (H.bar : 𝓞 E →+* 𝓞 E)

def IsSplitPrimeOff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : Prop :=
  p.Prime ∧ P.IsMaximal ∧ (p : 𝓞 E) ∈ P ∧ conjIdeal H P ≠ P ∧ ¬ p ∣ l.M'

section Fibre

variable {k : Type} [Field k]

abbrev Pts (t : SAB H (Sp k)) : Type := 𝟙_ (Over (Sp k)) ⟶ t.G

def KilledBy (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∀ a ∈ I, x ≫ t.act.act a = 1

def KilledByPow (t : SAB H (Sp k)) (I : Ideal (𝓞 E)) (x : Pts t) : Prop :=
  ∃ n : ℕ, KilledBy t (I ^ n) x

def IsHeckeDatum (t : SAB H (Sp k)) (P : Ideal (𝓞 E)) (i : ℕ) (C₀ : Subgroup (Pts t)) : Prop :=
  (∀ a, ∀ x ∈ C₀, x ≫ t.act.act a ∈ C₀) ∧ (∀ x ∈ C₀, KilledBy t (conjIdeal H P) x) ∧
    Finite C₀ ∧ Nat.card C₀ = Ideal.absNorm P ^ i

def heckeKernel (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) : Set (Pts t) :=
  {x | ∃ x₁ x₂ x₃ : Pts t, x = x₁ * x₂ * x₃ ∧
    (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ conjIdeal H P ∧ x₁ ≫ t.act.act a = 1) ∧
    (KilledByPow t (conjIdeal H P) x₂ ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ KilledByPow t P x₃ ∧ ∀ c ∈ C₀, Out.WeilIs t.G t.PP.L (p : ℤ) x₃ c 1)}

end Fibre

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Triple

variable {S : Scheme.{0}}

def IsTrivial {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : LB.Gen L, t.IsGen

def diagPull (A : Over S) (P : LB (A ⊗ A).left) : LB A.left := P.pull (lift (𝟙 A) (𝟙 A)).left

def IsSymmetricPair (h : ℕ) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension h A.hom ∧ P.IsLB ∧
    IsTrivial (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) ∧
    IsTrivial (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) ∧
    LBIso P (P.pull (lift (snd A A) (fst A A)).left)

def slice (A : Over S) (P : LB (A ⊗ A).left) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  P.pull (lift (fst T A ≫ x) (snd T A)).left

def IsPrincipal (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) : Prop :=
  Out.RelAmple A (diagPull A P) ∧ ∀ (T : Over S) (x : T ⟶ A), IsTrivial (slice A P x) → x = 1

abbrev Std (h M : ℕ) : Type := (Fin h → ZMod M) × (Fin h → ZMod M)

def stdForm {h M : ℕ} (a b : Std h M) : ZMod M := ∑ i, (a.1 i * b.2 i - a.2 i * b.1 i)

def IsLevel {h M : ℕ} (A : Over S) [GrpObj A] (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lv (a + b) = lv a * lv b) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (Function.Injective fun a => toUnit (Over.mk x) ≫ lv a) ∧
      ∀ g : Over.mk x ⟶ A, g ^ M = 1 ↔ ∃ a, toUnit (Over.mk x) ≫ lv a = g

def IsSymplectic {h M : ℕ} {R : Type} [CommRing R] (ζ : Rˣ) (s : S ⟶ Sp R) (A : Over S) [GrpObj A]
    (P : LB (A ⊗ A).left) (lv : Std h M → (𝟙_ (Over S) ⟶ A)) : Prop :=
  ∀ a b, Out.WeilIs A (diagPull A P) (M : ℤ) (lv a) (lv b)
    (Units.map ((𝟙_ (Over S)).hom ≫ s).appTop.hom.toMonoidHom (unitOn (ζ ^ (2 * stdForm a b).val)))

def IsPullbackTriple {h M : ℕ} {S' : Scheme.{0}} (A' : Over S') [GrpObj A'] (P' : LB (A' ⊗ A').left)
    (lv' : Std h M → (𝟙_ (Over S') ⟶ A')) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left)
    (lv : Std h M → (𝟙_ (Over S) ⟶ A)) (f : S' ⟶ S) : Prop :=
  ∃ (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A f φ ∧
    φ₂ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ φ₂ ≫ (snd A A).left = (snd A' A').left ≫ φ ∧
    LBIso P' (P.pull φ₂) ∧
    ∀ a, (lv' a).left ≫ φ = f ≫ (lv a).left

end Triple

end GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms

def In {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens) : Prop :=
  (⊤ : (Sp R).Opens) ≤ x ⁻¹ᵁ U

def val {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) {U : X.Opens} (h : In x U)
    (f : Γ(X, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE U ⊤ h).hom f)

abbrev Pt (A : Over (Sp ℂ)) : Type := 𝟙_ (Over (Sp ℂ)) ⟶ A

abbrev Pt.mor {A : Over (Sp ℂ)} (x : Pt A) : Sp ℂ ⟶ A.left := x.left

abbrev EpsPt (A : Over (Sp ℂ)) : Type := epsPt (𝟙 (Sp ℂ)) ⟶ A

abbrev EpsPt.mor {A : Over (Sp ℂ)} (v : EpsPt A) : Sp (DualNumber ℂ) ⟶ A.left := v.left


open Classical in
def extZero {V : Type} (s : Set V) (F : ∀ z, z ∈ s → ℂ) : V → ℂ :=
  fun z => if h : z ∈ s then F z h else 0

section Hol

variable {g : ℕ} {A : Over (Sp ℂ)}

def pre (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) : Set (Fin g → ℂ) := {z | In (u z).mor U}

def comp (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) (f : Γ(A.left, U)) : (Fin g → ℂ) → ℂ :=
  extZero (pre u U) (fun z h => val (u z).mor h f)

def IsHol (u : (Fin g → ℂ) → Pt A) : Prop :=
  ∀ U : A.left.Opens, IsOpen (pre u U) ∧ ∀ f : Γ(A.left, U), DifferentiableOn ℂ (comp u U f) (pre u U)

variable [GrpObj A]

def IsTangent (v : EpsPt A) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.mor = (1 : Pt A).mor

def IsDiffAt (u : (Fin g → ℂ) → Pt A) (w : Fin g → ℂ) (v : EpsPt A) : Prop :=
  IsTangent v ∧ ∀ (U : A.left.Opens) (h : In v.mor U) (f : Γ(A.left, U)),
    HasDerivAt (fun t : ℂ => comp u U f (t • w)) (val v.mor h f).snd 0

end Hol

structure Exp (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) where
  exp : (Fin g → ℂ) → Pt A
  exp_add : ∀ z z', exp (z + z') = exp z * exp z'
  hol : IsHol exp
  onto : Function.Surjective exp
  locIso : ∀ v : EpsPt A, IsTangent v → ∃! w, IsDiffAt exp w v
  discrete : DiscreteTopology {z : Fin g → ℂ | exp z = 1}
  span : Submodule.span ℝ {z : Fin g → ℂ | exp z = 1} = ⊤

namespace Exp

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g)

def hom : Multiplicative (Fin g → ℂ) →* Pt A :=
  MonoidHom.mk' (fun z => E.exp z.toAdd) (fun _ _ => E.exp_add _ _)

end Exp

structure Unif (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) extends Exp A g where
  isLB : L.IsLB
  fr : ∀ (i : L.ι) (z : Fin g → ℂ), z ∈ pre exp (L.U i) → ℂ
  fr_ne : ∀ i z h, fr i z h ≠ 0
  fr_hol : ∀ i, DifferentiableOn ℂ (extZero (pre exp (L.U i)) (fr i)) (pre exp (L.U i))
  fr_compat : ∀ (i j : L.ι) (z : Fin g → ℂ) (hi : z ∈ pre exp (L.U i)) (hj : z ∈ pre exp (L.U j))
    (hij : In (exp z).mor (L.U i ⊓ L.U j)),
    fr i z hi = val (exp z).mor hij (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) * fr j z hj

structure AHDatum {g : ℕ} (La : Submodule ℤ (Fin g → ℂ)) where
  H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ
  herm : ∀ x y, H y x = starRingEnd ℂ (H x y)
  pos : ∀ x, x ≠ 0 → 0 < (H x x).re
  integral : ∀ la mu : La, ∃ n : ℤ, (H la mu).im = n
  ch : La → ℂ
  ch_norm : ∀ la, ‖ch la‖ = 1
  ch_add : ∀ la mu : La,
    ch (la + mu) = ch la * ch mu * Complex.exp (π * Complex.I * ((H la mu).im : ℝ))

def AHDatum.factor {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (la : La) (z : Fin g → ℂ) : ℂ :=
  D.ch la * Complex.exp (π * D.H z la + π * D.H la la / 2)

namespace Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)

end Unif

def e (x : ℂ) : ℂ := Complex.exp (2 * π * Complex.I * x)

def Siegel (g : ℕ) : Type :=
  {τ : Matrix (Fin g) (Fin g) ℂ // τ.IsSymm ∧ (τ.map Complex.im).PosDef}

def thetaTerm {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℤ) : ℂ :=
  e ((∑ i, ∑ j, ((l i : ℂ) + a i) * τ i j * ((l j : ℂ) + a j)) / 2 + ∑ i, ((l i : ℂ) + a i) * (z i + b i))

def theta {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Siegel g) : ℂ :=
  ∑' l : Fin g → ℤ, thetaTerm a b z τ.1 l

end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

def Conv (g n k : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ 2 ≤ k ∧ 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < (((n ^ k) ^ 2 : ℕ) : ℝ)

section General
variable {S : Scheme.{0}}

end General

section Forms
variable {R : Type} [CommRing R] {P : PolAV (Sp R)} {I : Type} {e : ℤ}

end Forms

section Norm
variable {K : Type} [Field K] (P : PolAV (Sp K))

def HasTrace (ψ : P.A ⟶ P.A) (t : ℤ) : Prop :=
  ∀ M : ℕ, (M : K) ≠ 0 → ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ M = 1) →
    (∀ z : baseOver (Sp K) ⟶ P.A, z ^ M = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
    ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) ℕ,
      (∀ i, y i ≫ ψ = linComb y fun l => B l i) → ((B.trace : ℕ) : ZMod M) = (t : ZMod M)

end Norm

end GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel
end
end
