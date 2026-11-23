module

public import Lemmata.MiscLemmasQ.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle001
public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Mathlib.Algebra.Order.PUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

section TanLoc

variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]

def dualMapS {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A') :
    DualNumber A →ₐ[S] DualNumber A' := Bl.ThirdBlockLemmaB.goal1 ι

theorem dualMapS_fst {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A')
    (x : DualNumber A) : (dualMapS ι x).fst = ι x.fst := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

theorem dualMapS_snd {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (ι : A →ₐ[S] A')
    (x : DualNumber A) : (dualMapS ι x).snd = ι x.snd := by simp [dualMapS, Bl.ThirdBlockLemmaB.goal1, TrivSqZeroExt.lift_def]

def scaleS {A : Type} [CommRing A] [Algebra S A] (c : A) : DualNumber A →ₐ[S] DualNumber A :=
  (scaleD c).restrictScalars S

theorem scaleS_fst {A : Type} [CommRing A] [Algebra S A] (c : A) (x : DualNumber A) : (scaleS (S := S) c x).fst = x.fst := by
  simp [scaleS, scaleD]

theorem scaleS_snd {A : Type} [CommRing A] [Algebra S A] (c : A) (x : DualNumber A) :
    (scaleS (S := S) c x).snd = c * x.snd := by
  simp [scaleS, scaleD]

variable {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)

def IsTanAt (h : B →ₐ[S] DualNumber A) : Prop := ∀ b, (h b).fst = e b

section Lin

variable [Module B A] [IsScalarTower S B A] (hsm : ∀ (b : B) (a : A), b • a = e b * a)


include hsm in
def derOf (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) : Derivation S B A where
  toFun b := (h b).snd
  map_add' a b := by simp
  map_smul' r b := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by
    show (h (a * b)).snd = a • (h b).snd + b • (h a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hsm, hsm, hh, hh]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

theorem derOf_apply (h : B →ₐ[S] DualNumber A) (hh : IsTanAt e h) (b : B) : derOf e hsm h hh b = (h b).snd := rfl


include hsm in
def ofLin (g : Ω[B⁄S] →ₗ[B] A) : B →ₐ[S] DualNumber A where
  toFun b := TrivSqZeroExt.inl (e b) + TrivSqZeroExt.inr (g (KaehlerDifferential.D S B b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [map_mul, Derivation.leibniz, map_add (f := _), map_smul, hsm, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem ofLin_fst (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).fst = e b := by simp [ofLin]

theorem ofLin_snd (g : Ω[B⁄S] →ₗ[B] A) (b : B) : (ofLin e hsm g b).snd = g (KaehlerDifferential.D S B b) := by
  simp [ofLin]

end Lin

variable {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

theorem isLocalizedModule_tan [Module B A] [Module B A'] (hsm : ∀ (b : B) (a : A), b • a = e b * a)
    (hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a) (f : A →ₗ[B] A') (hf : ∀ a, f a = algebraMap A A' a) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B M) f := by
  refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
  · obtain ⟨_, ⟨m, hm, rfl⟩⟩ := x
    have hu : IsUnit (algebraMap A A' (e (algebraMap S B m))) := by
      rw [AlgHom.commutes]
      exact IsLocalization.map_units A' (⟨algebraMap S A m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩ :
        Algebra.algebraMapSubmonoid A M)
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hu
    constructor
    · intro a₁ a₂ h
      simp only [Module.algebraMap_end_apply, hsm'] at h
      rw [← hu] at h
      exact u.isUnit.mul_left_cancel h
    · intro a
      refine ⟨((u⁻¹ : A'ˣ) : A') * a, ?_⟩
      simp only [Module.algebraMap_end_apply, hsm', ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  · obtain ⟨⟨a, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid A M) y
    refine ⟨⟨a, ⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩⟩, ?_⟩
    show algebraMap S B m • y = f a
    rw [hsm', hf, AlgHom.commutes, ← h, mul_comm]
  · rw [hf, hf] at hx
    obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, h⟩ := IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hx
    refine ⟨⟨algebraMap S B m, Algebra.mem_algebraMapSubmonoid_of_mem (⟨m, hm⟩ : M)⟩, ?_⟩
    show algebraMap S B m • x₁ = algebraMap S B m • x₂
    rw [hsm, hsm, AlgHom.commutes]
    exact h

end TanLoc

section Main

variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B] [Algebra.FinitePresentation S B]
  {A : Type} [CommRing A] [Algebra S A] (e : B →ₐ[S] A)
  {A' : Type} [CommRing A'] [Algebra S A'] [Algebra A A'] [IsScalarTower S A A'] (M : Submonoid S)
  [IsLocalization (Algebra.algebraMapSubmonoid A M) A']

theorem tan_lift (h' : B →ₐ[S] DualNumber A') (hh' : IsTanAt ((IsScalarTower.toAlgHom S A A').comp e) h') :
    ∃ m ∈ M, ∃ h : B →ₐ[S] DualNumber A, IsTanAt e h ∧
      (dualMapS (IsScalarTower.toAlgHom S A A')).comp h = (scaleS (algebraMap S A' m)).comp h' := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  have : IsScalarTower S B A' := ⟨fun r b a => by
    show ι (e (r • b)) * a = r • (ι (e b) * a)
    rw [map_smul, map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  have hsm'' : ∀ (b : B) (a : A'), b • a = (ι.comp e) b * a := fun _ _ => rfl
  let g' := (derOf (ι.comp e) hsm'' h' hh').liftKaehlerDifferential
  obtain ⟨g, ⟨_, ⟨m, hm, rfl⟩⟩, hg⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g'
  refine ⟨m, hm, ofLin e hsm g, fun b => ofLin_fst e hsm g b, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_fst, scaleS_fst, ofLin_fst, hh']
    rfl
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dualMapS_snd, scaleS_snd, ofLin_snd]
    have := LinearMap.congr_fun hg (KaehlerDifferential.D S B b)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    refine this.trans ?_
    show (algebraMap S B m) • g' (KaehlerDifferential.D S B b) = _
    rw [hsm', Derivation.liftKaehlerDifferential_comp_D, derOf_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem tan_uniq (h₁ h₂ : B →ₐ[S] DualNumber A) (t₁ : IsTanAt e h₁) (t₂ : IsTanAt e h₂)
    (heq : (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₁ = (dualMapS (IsScalarTower.toAlgHom S A A')).comp h₂) :
    ∃ m ∈ M, (scaleS (algebraMap S A m)).comp h₁ = (scaleS (algebraMap S A m)).comp h₂ := by
  let ι := IsScalarTower.toAlgHom S A A'
  let iA : Module B A := Module.compHom A e.toRingHom
  let iA' : Module B A' := Module.compHom A' (ι.comp e).toRingHom
  have hsm : ∀ (b : B) (a : A), b • a = e b * a := fun _ _ => rfl
  have hsm' : ∀ (b : B) (a : A'), b • a = algebraMap A A' (e b) * a := fun _ _ => rfl
  have : IsScalarTower S B A := ⟨fun r b a => by
    show e (r • b) * a = r • (e b * a)
    rw [map_smul, smul_mul_assoc]⟩
  let f : A →ₗ[B] A' :=
    { toFun := algebraMap A A'
      map_add' := map_add _
      map_smul' := fun b a => by
        show algebraMap A A' (e b * a) = algebraMap A A' (e b) * algebraMap A A' a
        rw [map_mul] }
  have := isLocalizedModule_tan e M hsm hsm' f (fun _ => rfl)
  let g₁ := (derOf e hsm h₁ t₁).liftKaehlerDifferential
  let g₂ := (derOf e hsm h₂ t₂).liftKaehlerDifferential
  have hfg : f.comp g₁ = f.comp g₂ := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    show f (g₁ (KaehlerDifferential.D S B b)) = f (g₂ (KaehlerDifferential.D S B b))
    simp only [g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply]
    have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq b)
    simp only [AlgHom.comp_apply, dualMapS_snd] at this
    exact this
  obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, hc⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Algebra.algebraMapSubmonoid B M) f g₁ g₂ hfg
  refine ⟨m, hm, ?_⟩
  ext b
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_fst, scaleS_fst, t₁, t₂]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, scaleS_snd, scaleS_snd]
    have := LinearMap.congr_fun hc (KaehlerDifferential.D S B b)
    simp only [LinearMap.smul_apply, g₁, g₂, Derivation.liftKaehlerDifferential_comp_D, derOf_apply] at this
    change algebraMap S B m • (h₁ b).snd = algebraMap S B m • (h₂ b).snd at this
    rwa [hsm, hsm, AlgHom.commutes] at this

end Main

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Semi

section Lie

variable {R : Type} [CommRing R]

abbrev epsR (R : Type) [CommRing R] : Over (Sp R) := Over.mk (spMap (algebraMap R (DualNumber R)))

def epsScaleR (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

def IsTangent {G : Over (Sp R)} [GrpObj G] (v : epsR R ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = η[G].left

def IsLieComb {G : Over (Sp R)} [GrpObj G] {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) : Prop :=
  ∃ u : Fin n → (epsR R ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsLieBasis {G : Over (Sp R)} [GrpObj G] {n : ℕ} (v : Fin n → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsTangent (v i)) ∧ ∀ w, IsTangent w → ∃! c : Fin n → R, IsLieComb c v w

end Lie

def constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) : Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)

structure KeyIn (R : Type) [CommRing R] where
  P : Out.PolAV (Sp R)
  g_pos : 1 ≤ P.g
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  th : P.L.Sec
  th_ne : ∀ s : Sp R, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th
  v : Fin P.g → (epsR R ⟶ P.A)
  basis : IsLieBasis v

def KeyPB {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R') : Prop :=
  ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left

section Complex

variable {X : Scheme.{0}}

def valAt (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f)

open Classical in
def valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ x ⁻¹ᵁ U then valAt x U h f else 0

structure HolUnif (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) where
  ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)
  ex_add : ∀ z w, ex (z + w) = ex z * ex w
  ex_onto : Function.Surjective ex
  Λ : Submodule ℤ (Fin g → ℂ)
  ker : ∀ z, ex z = 1 ↔ z ∈ Λ
  discrete : DiscreteTopology Λ
  full : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤
  hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}
  fr : L.ι → (Fin g → ℂ) → ℂ
  fr_hol : ∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i}
  fr_ne : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → fr i z ≠ 0
  fr_compat : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j) →
    fr i z = valAt' (ex z).left (L.U i ⊓ L.U j) (L.g i j).val * fr j z

namespace HolUnif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def IsFn (s : L.Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → valAt' (u.ex z).left (L.U i) (s.f i) = θ z * u.fr i z

def IsRig (rig : LB.Gen (L.pull (eSec A))) : Prop :=
  ∀ j : (L.pull (eSec A)).ι, ⊤ ≤ (L.pull (eSec A)).U j →
    u.fr (j PUnit.unit) 0 = valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U j) (rig.s j).val

def IsDiff (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) : Prop :=
  ∀ (U : A.left.Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) (f : Γ(A.left, U)),
    TrivSqZeroExt.snd (show DualNumber ℂ from
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.left.appLE U ⊤ h).hom f)) =
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w

def IsAH (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) ∧ (∀ l, ‖χ l‖ = 1) ∧
    ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)

end HolUnif

def thetaChar {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (z : Fin g → ℂ) : ℂ :=
  ∑' n : Fin g → ℤ, Complex.exp (Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
    2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (z + b)))

end Complex

def KeyFormula : Prop :=
  ∃ κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ,

    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ 8 * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ 4 * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧

    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      KeyPB x' x f → (κ K' x' : K') = f (κ K x)) ∧

    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (κ k xk : k) = r u) ∧

    (∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
      τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
      u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
      (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ ℂ x = 1) ∧

    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ‖(κ ℂ x : ℂ)‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma tensor_punit_eq_zero (x : ℝ ⊗[ℤ] PUnit.{1}) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul r u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

instance : Subsingleton (ℝ ⊗[ℤ] PUnit.{1}) :=
  ⟨fun a b => by rw [tensor_punit_eq_zero a, tensor_punit_eq_zero b]⟩

def zeroDatum (H : Host E) : Datum H where
  La := PUnit
  fin := inferInstance
  proj := inferInstance
  EF := 0
  alt _ := rfl
  unimod := ⟨fun _ _ _ => Subsingleton.elim _ _, fun f => ⟨PUnit.unit, LinearMap.ext fun x => by
    have : x = 0 := Subsingleton.elim _ _
    subst this
    exact (map_zero f).symm⟩⟩
  adj _ _ _ := rfl
  p := 0
  q := 0
  rank := Module.finrank_zero_of_subsingleton
  dom := ⟨0, fun _ => Subsingleton.elim _ _, fun _ _ => by simp, fun x hx => absurd (Subsingleton.elim x 0) hx,
    fun a A t _ ht => by
      have hA : A = 0 := LinearMap.ext fun _ => Subsingleton.elim _ _
      subst hA
      simp [ht]⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Test
end
end

section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory IsLocalRing NumberField

def ExtVStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (maximalIdeal V) V →
    ∀ (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V))), IsProper tK.G.hom →
    ∀ (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
      (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))),
      ∃ ψ : SABMap t t' (𝟙 (Sp V)), m.φ ≫ ψ.φ = m'.φ

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
