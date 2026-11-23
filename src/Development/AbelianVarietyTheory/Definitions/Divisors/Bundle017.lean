module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle036
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

structure PLat (O : Type) [Ring O] (bar : O → O) where
  La : Type
  [acg : AddCommGroup La]
  [mod : Module O La]
  fin : Module.Finite ℤ La
  free : Module.Free ℤ La
  EF : LinearMap.BilinForm ℤ La
  alt : ∀ x, EF x x = 0
  nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0
  adj : ∀ (a : O) x y, EF (a • x) y = EF x (bar a • y)

attribute [instance] PLat.acg PLat.mod PLat.fin PLat.free

variable {O : Type} [Ring O] {bar : O → O}

def IsPeriod (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) : Prop :=
  (∀ (a : O) x, P (a • x) = ρ a *ᵥ P x) ∧ Function.Injective P ∧ DiscreteTopology P.range ∧
    Submodule.span ℝ (Set.range P) = ⊤ ∧
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y

def IsHolPeriods (D : PLat O bar) {g m : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (B : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) : Prop :=
  (∀ b ∈ B, IsPeriod D ρ (P b)) ∧ ∀ x, DifferentiableOn ℂ (fun b => P b x) B

def PerCoord (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (d : ℕ) : Prop :=
  ∀ P₀, IsPeriod D ρ P₀ → ∃ (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)))
    (Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ)) (s : Finset D.La) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ IsHolPeriods D ρ B Q ∧
    Z P₀ ∈ B ∧ Q (Z P₀) = P₀ ∧ (∀ b ∈ B, (∀ x ∈ s, ‖Q b x - P₀ x‖ < ε) → Z (Q b) = b) ∧
    (∀ P, IsPeriod D ρ P → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → Z P ∈ B ∧
      ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, P x = h (Q (Z P) x)) ∧
    (∀ P P', IsPeriod D ρ P → IsPeriod D ρ P' → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → (∀ x ∈ s, ‖P' x - P₀ x‖ < ε) →
      ∀ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ x, P' x = h (P x)) → Z P' = Z P) ∧
    ∀ (m : ℕ) (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B' → IsHolPeriods D ρ B' P →
      (∀ b ∈ B', ∀ x ∈ s, ‖P b x - P₀ x‖ < ε) → DifferentiableOn ℂ (fun b => Z (P b)) B'

def IsIsom (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) : Prop := ∀ x y, D'.EF (w x) (w y) = D.EF x y

def IsMarkedIsom {Λ : Type} (N : ℕ) (D D' : PLat O bar) (t : Λ → D.La) (t' : Λ → D'.La) (w : D.La ≃ₗ[O] D'.La) : Prop :=
  IsIsom D D' w ∧ ∀ a, ∃ e, w (t a) = t' a + N • e

def Genus (p N : ℕ) (D D' : PLat O bar) (t : D.La → D'.La) : Prop :=
  ∃ (f : ℕ → D.La →+ D'.La) (ν : ℕ → ℤ), t = f N ∧
    (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ ν (n * m) - ν n ∧ ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
    ∀ n : ℕ, 0 < n → n.Coprime p → IsCoprime (ν n) (n : ℤ) ∧ (∀ (c : O) a, ∃ e, f n (c • a) = c • f n a + n • e) ∧
      (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧
      (∀ a', ∃ a e, a' = f n a + n • e) ∧ ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a'

structure Fam (R : Type) [CommRing R] (O : Type) [Ring O] (Λ : Type) (g : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  A : Over X
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  dim : SmoothOfRelativeDimension g A.hom
  act : O → (A ⟶ A)
  hom : ∀ a, IsMonHom (act a)
  act_one : act 1 = 𝟙 A
  act_mul : ∀ a b, act (a * b) = act b ≫ act a
  act_add : ∀ a b, act (a + b) = act a * act b
  L : LB A.left
  isLB : L.IsLB
  ample : Out.RelAmple A L
  eta : Λ → (𝟙_ (Over X) ⟶ A)

attribute [instance] Fam.grp Fam.comm

variable {R : Type} [CommRing R] {Λ : Type} {g : ℕ}

def IsExp {X : Scheme.{0}} {G : Over X} [GrpObj G] (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left

def UnifAt (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La)
    (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) : Prop :=
  y ≫ F.s = spMap σ ∧ IsPeriod D' ρ P ∧ IsExp y e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧
    (∀ (a : O) z, e (ρ a *ᵥ z) = e z ≫ F.act a) ∧
    (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs F.A F.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) ∧
    ∀ a, toUnit _ ≫ F.eta a = e ((N : ℂ)⁻¹ • P (t a))

structure FineAt (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) : Prop where
  pts : ∀ y : Sp ℂ ⟶ F.X, y ≫ F.s = spMap σ → ∃ D' t P e, C D' t ∧ UnifAt F σ ρ N D' t P y e
  occ : ∀ D' t P, C D' t → IsPeriod D' ρ P → ∃ y e, UnifAt F σ ρ N D' t P y e
  sep : ∀ (D' D'' : PLat O bar) t t' P P' y y' e e', UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y' e' →
    ∀ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w →
      (∀ x, P' (w x) = h (P x)) → y = y'

structure Unif (F : Fam R O Λ g) (σ : R →+* ℂ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) where
  n : ℕ
  Di : Fin n → PLat O bar
  t : ∀ i, Λ → (Di i).La
  mem : ∀ i, C (Di i) (t i)
  ne : ∀ i, ∃ P, IsPeriod (Di i) ρ P
  all : ∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w
  distinct : ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j
  u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ F.X)
  ex : ∀ i P, (Fin g → ℂ) → (Over.mk (u i P) ⟶ F.A)
  unif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F σ ρ N (Di i) (t i) P (u i P) (ex i P)
  onto : ∀ y : Sp ℂ ⟶ F.X, y ≫ F.s = spMap σ → ∃ i P, IsPeriod (Di i) ρ P ∧ u i P = y
  disj : ∀ i j P P', IsPeriod (Di i) ρ P → IsPeriod (Di j) ρ P' → u i P = u j P' → i = j
  fibre : ∀ i P P', IsPeriod (Di i) ρ P → IsPeriod (Di i) ρ P' → (u i P = u i P' ↔
    ∃ (w : (Di i).La ≃ₗ[O] (Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      IsMarkedIsom N (Di i) (Di i) (t i) (t i) w ∧ ∀ x, P' (w x) = h (P x))
  hol : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))), IsOpen B →
    IsHolPeriods (Di i) ρ B P → IsHolTo B (fun b => u i (P b)) ∧
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (ex i (P bz.1) bz.2).left)
  lift : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)), IsOpen B →
    (∀ b ∈ B, y b ≫ F.s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B,
    ∃ (B' : Set (Fin m → ℂ)) (i : Fin n) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (Di i) ρ B' P ∧ ∀ b ∈ B', u i (P b) = y b

def FullMark (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) : Prop := ∀ x, ∃ a e, x = t a + N • e

def IsBC (F' : Fam ℂ O Λ g) (F : Fam R O Λ g) (σ : R →+* ℂ) : Prop :=
  ∃ (f : F'.X ⟶ F.X) (φ : F'.A.left ⟶ F.A.left), IsPullback f F'.s F.s (spMap σ) ∧ IsGrpPullback F'.A F.A f φ ∧
    (∀ a, (F'.act a).left ≫ φ = φ ≫ (F.act a).left) ∧ LBIso F'.L (F.L.pull φ) ∧
    ∀ a, (F'.eta a).left ≫ φ = f ≫ (F.eta a).left

section Groups

variable (D : PLat O bar) {r : ℕ} (b : Module.Basis (Fin r) ℤ D.La) (K : Type) [CommRing K]

def actM (a : O) : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => ((b.repr (a • b j) i : ℤ) : K)

end Groups

end GlobalTheory.PELU
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

variable {S S' : Scheme.{0}} {O : Type} [Ring O]

section Basic

variable {A A' A'' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A'']
  [IsCommMonObj A'']

structure IsLin (ρ : RingAct A O) (ρ' : RingAct A' O) (f : A ⟶ A') : Prop where
  hom : IsMonHom f
  comm : ∀ a, ρ.act a ≫ f = f ≫ ρ'.act a

structure IsIsogDeg (f : A ⟶ A') (d : ℕ) : Prop where
  fin : IsFinite f.left
  flat : Flat f.left
  surj : Surjective f.left
  rank : ∀ y, f.left.finrank y = d

def KilledBy (ρ : RingAct A O) (𝔴 : Ideal O) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ a ∈ 𝔴, x ≫ ρ.act a = 1


omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in
theorem IsIsogDeg.of_isIso (f : A ⟶ A') [IsIso f] : IsIsogDeg f 1 := by
  have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget S).map f))
  exact ⟨inferInstance, inferInstance, inferInstance, congrFun (Scheme.Hom.finrank_eq_one_of_isIso _)⟩


omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] [GrpObj A''] [IsCommMonObj A''] in
theorem IsIsogDeg.comp {f : A ⟶ A'} {g : A' ⟶ A''} {d e : ℕ} (hf : IsIsogDeg f d) (hg : IsIsogDeg g e) :
    IsIsogDeg (f ≫ g) (d * e) := by
  have := hf.fin; have := hf.flat; have := hf.surj
  have := hg.fin; have := hg.flat; have := hg.surj
  refine ⟨?_, ?_, ?_, fun y => ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left, FinrankComp.finrank_comp_of_const _ _ d hf.rank, hg.rank]



omit [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] in
theorem IsIsogDeg.of_isPullback {C C' : Over S'} {f : A ⟶ A'} {g : C ⟶ C'} {d : ℕ} (hf : IsIsogDeg f d)
    {u : C.left ⟶ A.left} {v : C'.left ⟶ A'.left} (H : IsPullback u g.left f.left v) : IsIsogDeg g d := by
  have := hf.fin; have := hf.flat
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H hf.fin,
    MorphismProperty.of_isPullback (P := @Flat) H hf.flat,
    MorphismProperty.of_isPullback (P := @Surjective) H hf.surj,
    fun y => (Scheme.Hom.finrank_of_isPullback _ _ _ _ H y).trans (hf.rank _)⟩

abbrev ker (f : A ⟶ A') : Over S := pullback f η[A']


omit [GrpObj A] [IsCommMonObj A] [IsCommMonObj A'] in
theorem IsIsogDeg.ker {f : A ⟶ A'} {d : ℕ} (hf : IsIsogDeg f d) : IsIsogDeg (toUnit (ker f)) d := by
  rw [toUnit_unique (toUnit _) (pullback.snd f η[A'])]
  exact hf.of_isPullback ((IsPullback.of_hasPullback f η[A']).map (Over.forget S))

theorem killedBy_span (ρ : RingAct A O) (s : Set O) {T : Over S} (x : T ⟶ A) :
    KilledBy ρ (Ideal.span s) x ↔ ∀ a ∈ s, x ≫ ρ.act a = 1 := by
  refine ⟨fun h a ha => h a (Ideal.subset_span ha), fun h a ha => ?_⟩
  have hadd : ∀ a b, x ≫ ρ.act (a + b) = (x ≫ ρ.act a) * (x ≫ ρ.act b) := fun a b => by
    rw [ρ.map_add]; exact MonObj.comp_mul x _ _
  induction ha using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero =>
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  | add a b _ _ ha hb => rw [hadd, ha, hb, _root_.mul_one]
  | smul c a _ ha =>
    have := ρ.hom c
    rw [smul_eq_mul, ρ.map_mul, ← Category.assoc, ha, MonObj.one_comp]

theorem comp_eq_one_iff_push {C C' : Over S'} [GrpObj C] [GrpObj C'] {f : S' ⟶ S} {u : C.left ⟶ A.left}
    {v : C'.left ⟶ A'.left} (hu : IsGrpPullback C A f u) (hv : IsGrpPullback C' A' f v) {g : A ⟶ A'} {g' : C ⟶ C'}
    (hg : g'.left ≫ v = u ≫ g.left) {T : Over S'} (x : T ⟶ C) :
    x ≫ g' = 1 ↔ pushHom hu T x ≫ g = 1 := by
  have e : pushHom hv T (x ≫ g') = pushHom hu T x ≫ g := Over.OverMorphism.ext (by
    change (x.left ≫ g'.left) ≫ v = (x.left ≫ u) ≫ g.left
    rw [Category.assoc, hg, Category.assoc])
  have inj : Function.Injective (pushHom hv T) := fun y z h => Over.OverMorphism.ext
    (hv.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  rw [← e, map_eq_one_iff _ inj]

end Basic

variable {A : Over S} [GrpObj A] [IsCommMonObj A]

structure Chain (ρ : RingAct A O) (𝔴 : Ideal O) (d n : ℕ) where

  B : Fin (n + 1) → Over S
  [grp : ∀ i, GrpObj (B i)]
  [comm : ∀ i, IsCommMonObj (B i)]
  ab : ∀ i, IsAbelianScheme (B i)

  act : ∀ i, RingAct (B i) O

  φ : ∀ i : Fin n, B i.castSucc ⟶ B i.succ
  φ_lin : ∀ i, IsLin (act _) (act _) (φ i)
  φ_deg : ∀ i, IsIsogDeg (φ i) d

  π : ∀ i, A ⟶ B i
  π_zero_lin : IsLin ρ (act 0) (π 0)
  π_zero_iso : IsIso (π 0)
  π_succ : ∀ i : Fin n, π i.succ = π i.castSucc ≫ φ i
  ker_last : ∀ (T : Over S) (x : T ⟶ A), x ≫ π (Fin.last n) = 1 ↔ KilledBy ρ 𝔴 x

attribute [instance] Chain.grp Chain.comm

namespace Chain

variable {ρ : RingAct A O} {𝔴 : Ideal O} {d n : ℕ} (C : Chain ρ 𝔴 d n)

end Chain

structure ChainMap {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
    {𝔴 : Ideal O} {d n : ℕ} (C' : Chain ρ' 𝔴 d n) (C : Chain ρ 𝔴 d n) (f : S' ⟶ S) (u : A'.left ⟶ A.left) where

  ψ : ∀ i, (C'.B i).left ⟶ (C.B i).left
  cart : ∀ i, IsGrpPullback (C'.B i) (C.B i) f (ψ i)
  act : ∀ i a, ((C'.act i).act a).left ≫ ψ i = ψ i ≫ ((C.act i).act a).left
  π_comm : ∀ i, (C'.π i).left ≫ ψ i = u ≫ (C.π i).left

namespace ChainMap

variable {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] {ρ' : RingAct A' O} {ρ : RingAct A O}
  {𝔴 : Ideal O} {d n : ℕ} {C' : Chain ρ' 𝔴 d n} {C : Chain ρ 𝔴 d n} {f : S' ⟶ S} {u : A'.left ⟶ A.left}

end ChainMap

section Unitary

variable {F : Type} [Field F] [NumberField F] [NumberField.IsCMField F] {D : UPel.Datum F} {p N : ℕ}

end Unitary

end GlobalTheory.IwLevel
end
end
