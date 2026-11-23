module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Quaternion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.RingTheory.RingHom.Etale
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix
open scoped NNReal Classical

namespace GlobalTheory.WeilM.SplitModel

variable {K : Type} [Field K]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable [Invertible (2 : K)]





variable [Fintype K]

variable [TopologicalSpace K] [DiscreteTopology K] [IsTopologicalRing K]





end GlobalTheory.WeilM.SplitModel

namespace GlobalTheory.WeilM.SplitModel

end GlobalTheory.WeilM.SplitModel

end

noncomputable section

open MeasureTheory Matrix ValuativeRel NumberField
open scoped NNReal Topology

namespace GlobalTheory.WeilM.SiegelModel

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

variable [Invertible (2 : R)]


omit [DecidableEq α] in
theorem rho_diag (ψ : AddChar R ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)} (h : IsDblCoord c ξ JA JB d dd) (z : Matrix α β E)
    (φ : (κ ⊕ κ → R) → ℂ) (u : κ → R) :
    dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β E)ᵀ) φ (Sum.elim u u) = φ (Sum.elim (u + (d.e z).1) (u + (d.e z).1)) := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one, Darboux.rho, h, schr]
  have e : (Sum.elim u u + Sum.elim (d.e z).1 (d.e z).1 : κ ⊕ κ → R) = Sum.elim (u + (d.e z).1) (u + (d.e z).1) := by
    ext (k | k) <;> rfl
  simp [sumElim_dotProduct_sumElim, e]

end Alg

section Forms

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]




end Forms

section RankZero

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]


variable [TopologicalSpace R] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology R E] {C : TestClass R}



end RankZero


end GlobalTheory.WeilM.SiegelModel
end
end

section

noncomputable section

open scoped TensorProduct Quaternion

namespace GlobalTheory.QSA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def nrm {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def coords {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : Fin 4 → R :=
  ![x.re, x.imI, x.imJ, x.imK]

scoped instance top {R : Type*} [CommRing R] [TopologicalSpace R] {a b : R} : TopologicalSpace ℍ[R, a, b] :=
  TopologicalSpace.induced coords inferInstance

variable (F : Type) [Field F] [NumberField F]

abbrev DA (a b : F) : Type := ℍ[AF F, algebraMap F (AF F) a, algebraMap F (AF F) b]

variable {F}

def rat {a b : F} (x : ℍ[F, a, b]) : DA F a b :=
  ⟨algebraMap F (AF F) x.re, algebraMap F (AF F) x.imI, algebraMap F (AF F) x.imJ, algebraMap F (AF F) x.imK⟩

def H0 {a b : F} (ε : AF F) : Set (DA F a b) :=
  {x | ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ x = rat γ * h}

theorem nrm_mul {R : Type*} [CommRing R] {a b : R} (x y : ℍ[R, a, b]) : nrm (x * y) = nrm x * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem mul_star_eq {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : x * star x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem nrm_rat {a b : F} (x : ℍ[F, a, b]) : nrm (rat x) = algebraMap F (AF F) (nrm x) := by
  simp [nrm, rat]

theorem one_mem_H0_weight_zero {a b : F} (ε : AF F) : (1 : DA F a b) ∈ H0 ε :=
  ⟨1, by simp [nrm], 1, by simp [nrm], by simp, by ext <;> simp [rat]⟩

end GlobalTheory.QSA
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

variable {S : Scheme.{0}}

structure HomFixRep (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) where
  H : Scheme.{0}
  π : H ⟶ S
  AH : Over H
  [grpA : GrpObj AH]
  BH : Over H
  [grpB : GrpObj BH]
  φA : AH.left ⟶ A.left
  φB : BH.left ⟶ B.left
  pbA : IsGrpPullback AH A π φA
  pbB : IsGrpPullback BH B π φB
  Φ : AH ⟶ BH
  hom : IsMonHom Φ
  iso : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)
  rep : ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
    ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
      IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

attribute [instance] HomFixRep.grpA HomFixRep.grpB

theorem isGrpPullback_id (A : Over S) [GrpObj A] : IsGrpPullback A A (𝟙 S) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 _) (by simp)
  have h1 : e ≫ x₀ = x := by ext; simp [e, hx]
  have h2 : e ≫ y₀ = y := by ext; simp [e, hy]
  have h3 : e ≫ (x₀ * y₀) = x * y := by rw [MonObj.comp_mul, h1, h2]
  rw [← h3]; simp [e]

def HomFixRep.toTrivial (A : Over S) [GrpObj A] (L : LB A.left) (M : LB (𝟙_ (Over S)).left)
    (h : LBIso (L.pull (𝟙 _)) ((M.pull (𝟙 _)).pull (toUnit A).left)) : HomFixRep A (𝟙_ (Over S)) L M where
  H := S
  π := 𝟙 S
  AH := A
  BH := 𝟙_ (Over S)
  φA := 𝟙 _
  φB := 𝟙 _
  pbA := isGrpPullback_id A
  pbB := isGrpPullback_id _
  Φ := toUnit A
  hom := inferInstance
  iso := h
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB _ _
    refine ⟨t, ⟨by simp, φA', φB', hA, hB, by simp, by simp, ?_⟩, fun h hh => by simpa using hh.1⟩
    have h1 := hA.1.w
    have h2 := hB.1.w
    have h3 := Over.w Φ'
    have h4 := Over.w (toUnit A)
    have h5 : φB' = B'.hom ≫ t := by simpa using h2
    have h6 : (toUnit A).left = A.hom := by simpa using h4
    rw [h5, h6, ← Category.assoc, h3]; exact h1.symm

def trivLB (X : Scheme.{0}) : LB X where
  «ι» := PUnit
  U := fun _ => ⊤
  g := fun _ _ => 1

theorem trivLB_isLB (X : Scheme.{0}) : (trivLB X).IsLB :=
  ⟨by simp [trivLB], fun _ => map_one _, fun _ _ _ =>
    (congrArg₂ (· * ·) (map_one _) (map_one _)).trans ((_root_.mul_one _).trans (map_one _).symm)⟩

end GlobalTheory.EndLoc
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cstOn (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

def IsEtCoord (p : X ⟶ Sp R) (U : X.Opens) {d : ℕ} (t : Fin d → Γ(X, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cstOn p U) t).Etale

structure SncChart (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) where

  U : X.Opens
  affine : IsAffineOpen U

  t : Fin d → Γ(X, U)
  etale : IsEtCoord p U t

  c : ∀ i, (L i).ι
  le : ∀ i, U ≤ (L i).U (c i)

  e : Fin s → Option (Fin d)
  inj : ∀ i j a, e i = some a → e j = some a → i = j

  u : Fin s → Γ(X, U)ˣ
  eq : ∀ i, resG X (le i) ((σ i).f (c i)) = (u i : Γ(X, U)) * (e i).elim 1 t

structure RelSnc (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) : Prop where
  isLB : ∀ i, (L i).IsLB
  chart : ∀ x : X, ∃ C : SncChart p d L σ, x ∈ C.U

end GlobalTheory.LogPair
end
end
