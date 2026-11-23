module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.Module.Lattice.Full
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.DualLattices.Bundle007
import ReciprocityTheory.DualLattices.Bundle002

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatTest

open Module NumberField TensorProduct

section Norms

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

end Norms

section Eigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl

theorem expand_dual (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm

theorem repr_eq_trace (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]

  simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
  ← integralBasis_apply, trace_dualInt]
  simp

end Eigen

section Further

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

end Further

section FurtherEigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]


end FurtherEigen

end GlobalTheory.CompanionTheory.Ar.HT.LatTest
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTPoint (C O : Type) [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (κ : O) (N : ℕ)
    (V Ω : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] where

  T : Submodule O V

  ρ : 𝓞 E →+* Module.End C V

  t : Fin N → V
  free : IsFreeOn ρ T t

  e : V →ₗ[C] V →ₗ[C] C
  alt : ∀ x, e x x = 0
  nondeg : ∀ y, (∀ x, e x y = 0) → y = 0
  perfect : dualLat e T = T
  adj : ∀ (a : 𝓞 E) (x y : V), e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y)

  om : Submodule O Ω
  om_lat : om.IsFullLattice C

  ρΩ : 𝓞 E →+* Module.End C Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  ht : V →ₗ[C] Ω
  ht_lin : ∀ (a : 𝓞 E) (x : V), ht (ρ a x) = ρΩ a (ht x)
  ht_mem : ∀ x ∈ T, ht x ∈ om
  κ_ne : algebraMap O C κ ≠ 0
  κ_mem : ∀ y ∈ om, ∃ x ∈ T, ht x = κ • y
  lagr : ∀ x, ht x = 0 ↔ ∀ y, ht y = 0 → e x y = 0

namespace HTPoint

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

def W : Submodule C V := LinearMap.ker P.ht

def om' : Submodule O Ω := P.T.map (P.ht.restrictScalars O)

def Wsp (σ : E →+* C) : Submodule C V := P.W ⊓ eigSp P.ρ σ

def Ωsp (σ : E →+* C) : Submodule C Ω := eigSp P.ρΩ σ

def W' (σ : E →+* C) : Submodule O V := P.W.restrictScalars O ⊓ eigSub P.ρ σ P.T

def omHT (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om'

def omRec (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om

def tate (x : Fin N → 𝓞 E) : V := ∑ i, P.ρ (x i) (P.t i)

end HTPoint

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

structure TorsRep (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (p : ℕ) where

  A : Type
  [cr : CommRing A]
  [alg : Algebra R A]
  free : Module.Free R A
  fin : Module.Finite R A

  y : sp (R₀ := R) A ⟶ G
  y_p : y ^ p = 1
  univ : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G), z ^ p = 1 →
    ∃! φ : A →ₐ[R] S, spMap φ ≫ y = z

attribute [instance] TorsRep.cr TorsRep.alg

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {p : ℕ}


variable (G p) in
structure IsTorsPts {N : Type} [AddCommGroup N] (pt : N → (sp (R₀ := R) R ⟶ G)) : Prop where
  inj : Function.Injective pt
  add : ∀ x y, pt (x + y) = pt x * pt y
  range : ∀ z, z ^ p = 1 ↔ ∃ x, pt x = z

def torsFun (C : Type) [Field C] [Algebra R C] (T : TorsRep G p) {N : Type}
    (pt : N → (sp (R₀ := R) R ⟶ G)) : Submodule R (N → C) where
  carrier := {f | ∃ a : T.A, ∀ x (φ : T.A →ₐ[R] R), spMap φ ≫ T.y = pt x → f x = algebraMap R C (φ a)}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, fun x φ h => by simp [ha x φ h, hb x φ h]⟩
  zero_mem' := ⟨0, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨a, ha⟩
    exact ⟨c • a, fun x φ h => by simp [ha x φ h, Algebra.smul_def]⟩

def vanIdeal (T : TorsRep G p) {N : Type} (pt : N → (sp (R₀ := R) R ⟶ G)) (K : Set N) : Ideal T.A where
  carrier := {a | ∀ k ∈ K, ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0}
  add_mem' := by
    intro a b ha hb k hk φ h
    simp [ha k hk φ h, hb k hk φ h]
  zero_mem' := fun _ _ _ _ => by simp
  smul_mem' := by
    intro c a ha k hk φ h
    simp [ha k hk φ h]


variable (G) in
structure IsFinFlatSub (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ G) : Prop where
  proj : Module.Projective R B
  fin : Module.Finite R B
  mono : ∀ (S : Type) [CommRing S] [Algebra R S] (φ φ' : B →ₐ[R] S), spMap φ ≫ h = spMap φ' ≫ h → φ = φ'
  one : ∀ (S : Type) [CommRing S] [Algebra R S], ∃ φ : B →ₐ[R] S, spMap φ ≫ h = 1
  mul : ∀ (S : Type) [CommRing S] [Algebra R S] (φ φ' : B →ₐ[R] S),
    ∃ χ : B →ₐ[R] S, spMap χ ≫ h = (spMap φ ≫ h) * (spMap φ' ≫ h)
  inv : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : B →ₐ[R] S),
    ∃ χ : B →ₐ[R] S, (spMap χ ≫ h) * (spMap φ ≫ h) = 1

def tens {C : Type} [Field C] [Algebra R C] {X Y : Type} (M : Submodule R (X → C))
    (M' : Submodule R (Y → C)) : Submodule R (X × Y → C) :=
  Submodule.span R {F | ∃ g ∈ M, ∃ h ∈ M', F = fun z => g z.1 * h z.2}

def IsAbFactor (p : ℕ) {C : Type} [Field C] [Algebra R C] {N : Type} [AddCommGroup N]
    (M : Submodule R (N → C)) : Prop :=
  ∃ (A : Over (Spec (CommRingCat.of R))) (_ : GrpObj A) (L : LB A.left), IsAbelianScheme A ∧ L.IsLB ∧
    Out.RelAmple A L ∧ ∃ (T : TorsRep A p) (N' : Type) (_ : AddCommGroup N')
      (pt : N' → (sp (R₀ := R) R ⟶ A)), IsTorsPts A p pt ∧
      ∃ (i : N →+ N') (π : N' →+ N), (∀ x, π (i x) = x) ∧
        (∀ g ∈ torsFun C T pt, (fun x => g (i (π x))) ∈ torsFun C T pt) ∧
        M = (torsFun C T pt).map (LinearMap.funLeft R C (i : N → N'))

end GlobalTheory.CompanionTheory.Ar.GR
end
end
