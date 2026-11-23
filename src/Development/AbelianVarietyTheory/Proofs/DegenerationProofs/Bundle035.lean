module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrictModelOfBirational
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleHeightProperScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesFunctionField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionEqMulOfVanishingModElement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.isFinite_ker_of_surj_points_same_dimension : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), SmConn G → SmConn G' → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g G'.hom → ∀ i : G ⟶ G', IsMonHom i → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ i = y) → IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  first | exact @GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq | exact GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq | (intros; apply GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_strict_model_of_birational : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, BirLaw M → ∃ N : Model R A, Strict N ∧ N.Le M := by
  first | exact @GlobalTheory.SS.exists_strict_le | exact GlobalTheory.SS.exists_strict_le | (intros; apply GlobalTheory.SS.exists_strict_le <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_lineBundle_height_properScheme : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (Pl : Places k K) (B : Over (Sp k)), IsProper B.hom → ∀ (L : LB B.left), L.IsLB → ∃ h : (Over.mk (spMap (algebraMap k K)) ⟶ B) → ℤ, (∀ (Z : Over (Sp k)), IsProper Z.hom → ∀ (n : ℕ) (φ : Fin n → (Z ⟶ B)) (ε : Fin n → ℤ), (∃ t : LB.Gen (LB.LinComb L (fun i => (φ i).left) ε), t.IsGen) → ∀ z : Over.mk (spMap (algebraMap k K)) ⟶ Z, ∑ i, ε i * h (z ≫ φ i) = 0) ∧ ∀ (N : ℕ) (s : LB.Sec (GlobalTheory.AbLaw.pw L N)) (x : Over.mk (spMap (algebraMap k K)) ⟶ B), 1 ≤ N → Set.range x.left ⊆ Out.nonzeroLocus s → 0 ≤ h x ∧ (h x = 0 → ∀ i, ∃ b : Sp (Pl.O i) ⟶ B.left, spMap (Pl.O i).subtype ≫ b = x.left ∧ Set.range b ⊆ Out.nonzeroLocus s) := by
  first | exact @GlobalTheory.SS.exists_height | exact GlobalTheory.SS.exists_height | (intros; apply GlobalTheory.SS.exists_height <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_productFormulaPlaces_function_field : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (t : K), Transcendental k t → FiniteDimensional (IntermediateField.adjoin k {t}) K → Algebra.IsSeparable (IntermediateField.adjoin k {t}) K → ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → IsAlgebraic k x := by
  first | exact @GlobalTheory.SS.PlacesExt.exists_places | exact GlobalTheory.SS.PlacesExt.exists_places | (intros; apply GlobalTheory.SS.PlacesExt.exists_places <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SquareZero


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open TopologicalSpace in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X X' : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X),
    IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : X.Opens) (x y : Γ(X, W)),
    (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0 := by
  intro A A' _ _ g hg hsq X X' f f' β hpb W x y hx hy
  apply TopCat.Presheaf.section_ext X.sheaf W (x * y) 0
  intro p hp
  obtain ⟨V, hVaff, hpV, hVW⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  have hres : ∀ z : Γ(X, W), (β.app W).hom z = 0 →
      _root_.GlobalTheory.AbLaw.rs X hVW z ∈
        Ideal.map (_root_.GlobalTheory.SmallExtLift.cst f V) (RingHom.ker g) := fun z hz =>
    _root_.GlobalTheory.SmallExtLift.mem_of_app_eq_zero hg hpb hVaff _
      (by rw [_root_.GlobalTheory.SectionKernel.app_rs, hz, map_zero])
  have hzero : _root_.GlobalTheory.AbLaw.rs X hVW (x * y) = 0 := by
    rw [map_mul]
    have hmem := Ideal.mul_mem_mul (hres x hx) (hres y hy)
    rw [← Ideal.map_mul, ← pow_two, hsq, Ideal.map_bot, Ideal.mem_bot] at hmem
    exact hmem
  have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV (x * y)
  have h2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV 0
  change X.presheaf.germ W p hp (x * y) = X.presheaf.germ W p hp 0
  rw [← h1, ← h2, map_zero]
  exact congrArg _ hzero

end GlobalTheory.SquareZero
end

section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem finite_field_of_finiteType_int (K : Type*) [Field K] [Algebra.FiniteType ℤ K] :
    Finite K := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ _
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := CharP.charP_to_charZero K
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (algebraMap ℤ K).injective_int (Field.toIsField _))
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero K p).resolve_right hp0⟩
  let := ZMod.algebra K p
  have : Module.Finite (ZMod p) K := Module.Finite.of_restrictScalars_finite ℤ _ _
  exact Module.finite_of_finite (ZMod p)

theorem jacobsonSpace_of_locallyOfFiniteType_int {X : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] : JacobsonSpace X := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  exact LocallyOfFiniteType.jacobsonSpace π

theorem finite_residueField_of_isClosed_of_locallyOfFiniteType_int {X : Scheme.{0}}
    (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ (X.residueField x) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ (X.residueField x)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ (X.residueField x) := RingHom.finiteType_algebraMap.mp h'
  exact finite_field_of_finiteType_int _

section Top

variable {T : Type*} [TopologicalSpace T] [JacobsonSpace T]

theorem subset_of_isOpen_of_closedPoints {U V : Set T} (hU : IsOpen U) (hV : IsOpen V)
    (h : ∀ x, IsClosed ({x} : Set T) → x ∈ U → x ∈ V) : U ⊆ V := by
  intro y hy
  by_contra hyV
  obtain ⟨x, ⟨hxU, hxV⟩, hx⟩ := nonempty_inter_closedPoints (Z := U ∩ Vᶜ) ⟨y, hy, hyV⟩
    (hU.isLocallyClosed.inter hV.isClosed_compl.isLocallyClosed)
  exact hxV (h x hx hxU)

theorem exists_isClosed_specializes_mem_iff (ξ : T) {ι : Type*} [Finite ι] (U : ι → Set T)
    (hU : ∀ i, IsOpen (U i)) {W : Set T} (hW : IsOpen W) (hξ : ξ ∈ W) :
    ∃ x : T, IsClosed ({x} : Set T) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i := by
  have hO : IsOpen (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1) :=
    hW.inter (isOpen_iInter_of_finite fun i => hU i.1)
  obtain ⟨x, ⟨hxc, hxW, hxU⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := closure {ξ} ∩ (W ∩ ⋂ i : {i // ξ ∈ U i}, U i.1))
    ⟨ξ, subset_closure rfl, hξ, Set.mem_iInter.mpr fun i => i.2⟩
    (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hx, hs, hxW, fun i =>
    ⟨fun h => hs.mem_open (hU i) h, fun h => Set.mem_iInter.mp hxU ⟨i, h⟩⟩⟩

theorem exists_dense_of_closedPoints_cover [IrreducibleSpace T] {ι : Type*} [Finite ι]
    (S : ι → Set T) (h : ∀ x, IsClosed ({x} : Set T) → ∃ i, x ∈ S i) : ∃ i, Dense (S i) := by
  have hc : (⋃ i, closure (S i)) = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints (X := T),
      (isClosed_iUnion_of_finite fun i => isClosed_closure).closure_subset_iff]
    intro x hx
    obtain ⟨i, hi⟩ := h x hx
    exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
  classical
  have := Fintype.ofFinite ι
  obtain ⟨Z, hZ, hZ'⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ T) (Finset.univ.image fun i => closure (S i))
    (by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact isClosed_closure)
    (by
      intro x _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc ▸ Set.mem_univ x : x ∈ ⋃ i, closure (S i))
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)), hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
  exact ⟨i, fun x => hZ' (Set.mem_univ x)⟩

end Top

theorem jacobson_tools_of_locallyOfFiniteType_int :
    ∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π], JacobsonSpace X ∧
      (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧
      (∀ U V : X.Opens, (∀ x : X, IsClosed ({x} : Set X) → (x ∈ U ↔ x ∈ V)) → U = V) ∧
      (∀ (ξ : X) (ι : Type) [Finite ι] (U : ι → X.Opens) (W : X.Opens), ξ ∈ W →
        ∃ x : X, IsClosed ({x} : Set X) ∧ ξ ⤳ x ∧ x ∈ W ∧ ∀ i, x ∈ U i ↔ ξ ∈ U i) ∧
      (∀ (ι : Type) [Finite ι] (Sg : ι → Set X), IrreducibleSpace X →
        (∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ Sg i) → ∃ i, Dense (Sg i)) := by
  intro X π _
  have hJ := jacobsonSpace_of_locallyOfFiniteType_int π
  refine ⟨hJ, finite_residueField_of_isClosed_of_locallyOfFiniteType_int π, ?_, ?_, ?_⟩
  · intro U V h
    exact TopologicalSpace.Opens.ext (subset_antisymm
      (subset_of_isOpen_of_closedPoints U.isOpen V.isOpen fun x hx => (h x hx).1)
      (subset_of_isOpen_of_closedPoints V.isOpen U.isOpen fun x hx => (h x hx).2))
  · intro ξ ι _ U W hξ
    exact exists_isClosed_specializes_mem_iff ξ (fun i => (U i : Set X)) (fun i => (U i).isOpen)
      W.isOpen hξ
  · intro ι _ Sg _ h
    exact exists_dense_of_closedPoints_cover Sg h

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FibreLinInd

theorem exists_det_ne_zero {K A : Type} [Field K] {r : ℕ} (v : A → Fin r → K)
    (h : ∀ c : Fin r → K, (∀ a, ∑ i, c i * v a i = 0) → c = 0) :
    ∃ a : Fin r → A, (Matrix.of fun k i => v (a k) i).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hφ0
    have hφ' : ∀ w : Fin r → K, φ w = ∑ i, φ (Pi.single i 1) * w i := fun w => by
      rw [LinearMap.pi_apply_eq_sum_univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have := h (fun i => φ (Pi.single i 1)) fun a => by
      rw [← hφ']
      exact hφ (Submodule.subset_span ⟨a, rfl⟩)
    refine LinearMap.ext fun w => ?_
    rw [hφ']
    simp [congrFun this]
  obtain ⟨κ, a, -, hs, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Fin r → K) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ ≃ Fin r := b.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨a ∘ e.symm, ?_⟩
  have h2 : LinearIndependent K ((v ∘ a) ∘ e.symm) := hli.comp _ e.symm.injective
  have h3 : IsUnit (Matrix.of fun k i => v ((a ∘ e.symm) k) i) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 h2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h3).ne_zero

theorem exists_fibrePower {G Z : Scheme.{0}} (f : G ⟶ Z) [UniversallyOpen f]
    [LocallyOfFiniteType f] (r : ℕ) :
    ∃ (P : Scheme.{0}) (p : P ⟶ Z) (π : Fin r → (P ⟶ G)), UniversallyOpen p ∧
      LocallyOfFiniteType p ∧ (∀ k, π k ≫ f = p) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ Z) (g : Fin r → (T ⟶ G)), (∀ k, g k ≫ f = x) →
        ∃ h : T ⟶ P, h ≫ p = x ∧ ∀ k, h ≫ π k = g k := by
  induction r with
  | zero =>
    exact ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun k => k.elim0,
      fun T x g _ => ⟨x, by simp, fun k => k.elim0⟩⟩
  | succ r ih =>
    obtain ⟨P, p, π, h1, h2, h3, h4⟩ := ih
    refine ⟨pullback f p, pullback.snd f p ≫ p,
      Fin.cons (pullback.fst f p) (fun k => pullback.snd f p ≫ π k), inferInstance, inferInstance,
      ?_, ?_⟩
    · refine Fin.cases ?_ fun k => ?_
      · simpa using pullback.condition
      · simp [h3]
    · intro T x g hg
      obtain ⟨h, hp, hπ⟩ := h4 T x (fun k => g k.succ) fun k => hg _
      refine ⟨pullback.lift (g 0) h (by rw [hg, hp]), by rw [pullback.lift_snd_assoc, hp], ?_⟩
      refine Fin.cases ?_ fun k => ?_
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd_assoc, hπ]

theorem exists_lift {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) (w : W) (t : Sp K) (hw : q w = x t) :
    ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

variable {K : Type} [Field K] {P G : Scheme.{0}}

theorem top_le_iff (x : Sp K ⟶ P) (U : P.Opens) (z : Sp K) : ⊤ ≤ x ⁻¹ᵁ U ↔ x z ∈ U := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact ⟨fun h => h (show z ∈ (⊤ : (Sp K).Opens) from trivial),
    fun h y _ => by rw [Subsingleton.elim y z]; exact h⟩

def evalHom (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) : Γ(P, U) →+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (h.appLE U ⊤ hU).hom

theorem mem_basicOpen_iff (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (D : Γ(P, U))
    (t : Sp K) : h t ∈ P.basicOpen D ↔ evalHom h U hU D ≠ 0 := by
  have e : (Sp K).basicOpen (h.appLE U ⊤ hU D) = h ⁻¹ᵁ P.basicOpen D := by
    rw [Scheme.basicOpen_appLE, top_inf_eq]
  have hinj : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.bijective
  change t ∈ h ⁻¹ᵁ P.basicOpen D ↔ _
  rw [← e]
  constructor
  · intro ht h0
    have : h.appLE U ⊤ hU D = 0 := hinj.1 (by rw [map_zero]; exact h0)
    rw [this, Scheme.basicOpen_zero] at ht
    exact ht
  · intro h0
    have : IsUnit (h.appLE U ⊤ hU D) :=
      (MulEquiv.isUnit_map
        (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv).1 (IsUnit.mk0 _ h0)
    rw [Scheme.basicOpen_of_isUnit _ this]
    trivial

theorem evalHom_appLE (h : Sp K ⟶ P) (U : P.Opens) (hU : ⊤ ≤ h ⁻¹ᵁ U) (π : P ⟶ G) (V : G.Opens)
    (hV : U ≤ π ⁻¹ᵁ V) (a : Γ(G, V)) :
    evalHom h U hU (π.appLE V U hV a) = valF (h ≫ π) V a := by
  have hle : ⊤ ≤ (h ≫ π) ⁻¹ᵁ V := fun y hy => hV (hU hy)
  rw [valF, dite_eq_left hle, ← Scheme.Hom.appLE_comp_appLE h π V U ⊤ hV hU]
  rfl

theorem isOpen_setOf_linearIndependent_on_fibres :
    ∀ (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G),
      L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), IsOpen {z : Z | ∀ (K : Type) [Field K]
        [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K,
          (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0} := by
  classical
  intro G Z f _ _ L _ r s
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let K := AlgebraicClosure (Z.residueField z)
  let x : Sp K ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) K)) ≫ Z.fromSpecResidueField z
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  have hx : Set.range x = {z} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact hxt t
    · rintro rfl
      exact ⟨t₀, hxt t₀⟩
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz K x hx c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  refine ⟨p '' (O : Set P), ?_, p.isOpenMap _ O.isOpen, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ K' _ _ x' hx' c hc
    let t : Sp K' := IsLocalRing.closedPoint K'
    have ht : x' t = p w := by
      rw [← Set.mem_singleton_iff, ← hx']
      exact ⟨t, rfl⟩
    obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
    have hO : (h ≫ O.ι) t ∈ O := (h t).2
    have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
    have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
    rw [hM] at hd
    refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
    have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  · obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]

end GlobalTheory.FibreLinInd
end
end
