module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep C hI
  have hS := GlobalTheory.T.smoothOfRelativeDimension_groupScheme_of_tests C hT hF
  have hC : C.TestCart := GlobalTheory.T.testCart_of_specialFibre_surjective C hF hS
  have hL : C.FibLaw := GlobalTheory.T.fibreLaw_of_testCartesian C hC
  exact GlobalTheory.T.nonempty_law_abelianSchemeProperClosure C hS hC (GlobalTheory.T.exists_mul_of_isSquare_of_fibLaw C hT hS hC hL) (GlobalTheory.T.exists_inverse_extension_properClosure C hT hS hC hL)

end GlobalTheory.ZJ
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.NeutralModel

theorem exists_idem_of_rel {S : Type} [Finite S] [Nonempty S] (r : Setoid S) (T : S → S → S → Prop)
    (tot : ∀ i j, ∃ k, T i j k) (resp : ∀ i j k k', T i j k → r k k' → T i j k')
    (assoc : ∀ i j l k m p q, T i j k → T k l m → T j l p → T i p q → r m q) : ∃ e, T e e e := by
  choose f hf using tot
  let mul : Quotient r → Quotient r → Quotient r := fun a b => Quotient.mk r (f a.out b.out)
  have hm : ∀ a b, T a.out b.out (mul a b).out := fun a b =>
    resp _ _ _ _ (hf _ _) (r.symm (Quotient.mk_out _))
  letI : Semigroup (Quotient r) :=
    { mul := mul
      mul_assoc := fun a b c => by
        have := assoc _ _ _ _ _ _ _ (hm a b) (hm (mul a b) c) (hm b c) (hm a (mul b c))
        have h2 := Quotient.sound this
        rwa [Quotient.out_eq, Quotient.out_eq] at h2 }
  letI : TopologicalSpace (Quotient r) := ⊥
  haveI : DiscreteTopology (Quotient r) := ⟨rfl⟩
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r (Classical.arbitrary S)⟩
  obtain ⟨e, he⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left (M := Quotient r)
    (fun _ => continuous_of_discreteTopology)
  refine ⟨e.out, ?_⟩
  have := hm e e
  rwa [show mul e e = e from he] at this

theorem rel_factorial {S : Type} [Fintype S] (T : ℕ → S → S → Prop) (tot : ∀ i, ∃ j, T 1 i j)
    (zero : ∀ i, T 0 i i) (add : ∀ p q i j k, T p i j → T q j k → T (p + q) i k)
    (sub : ∀ p d i j, T p i j → T (p + d) i j → T d i i) (i : S) : T (Fintype.card S).factorial i i := by
  choose σ hσ using tot
  have hit : ∀ p, T p i (σ^[p] i) := by
    intro p
    induction p with
    | zero => exact zero i
    | succ p ih => rw [Function.iterate_succ_apply']; exact add _ _ _ _ _ ih (hσ _)
  have hmul : ∀ d, T d i i → ∀ m, T (d * m) i i := by
    intro d hd m
    induction m with
    | zero => exact zero i
    | succ m ih => rw [Nat.mul_succ]; exact add _ _ _ _ _ ih hd
  have key : ∀ p q : Fin (Fintype.card S + 1), p < q → σ^[p] i = σ^[q] i → T (Fintype.card S).factorial i i := by
    intro p q hpq h
    have hq : (q : ℕ) = p + (q - p) := by have : (p : ℕ) < q := hpq; omega
    have h1 : T (q - p) i i := sub p _ i _ (hit p) (by rw [← hq, h]; exact hit q)
    obtain ⟨m, hm⟩ : (q - p : ℕ) ∣ (Fintype.card S).factorial :=
      Nat.dvd_factorial (by have : (p : ℕ) < q := hpq; omega) (by have := q.2; omega)
    rw [hm]; exact hmul _ h1 m
  obtain ⟨p, q, hne, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun p : Fin (Fintype.card S + 1) => σ^[p] i) (by simp)
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact key p q h' h
  · exact key q p h' h.symm

section
variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A]

noncomputable def shearIso : A ⊗ A ≅ A ⊗ A where
  hom := shear A true
  inv := shear A false
  hom_inv_id := by
    ext <;> simp [shear, MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    ext <;> simp [shear, MonObj.comp_mul, GrpObj.comp_inv]

instance : IsIso (shear A true) := (shearIso A).isIso_hom

theorem triple_fst :
    ((shear A true ⊗ₘ 𝟙 A) ≫ (α_ A A A).hom ≫ (𝟙 A ⊗ₘ (shear A true ≫ (β_ A A).hom)) ≫ (β_ A (A ⊗ A)).hom ≫
      (α_ A A A).hom) ≫ fst A (A ⊗ A) =
    ((α_ A A A).hom ≫ (𝟙 A ⊗ₘ (shear A true ≫ (β_ A A).hom)) ≫ (α_ A A A).inv ≫
      ((shear A true ≫ (β_ A A).hom) ⊗ₘ 𝟙 A) ≫ (α_ A A A).hom) ≫ fst A (A ⊗ A) := by
  simp [shear, MonObj.comp_mul, _root_.mul_assoc]

theorem inv_fst :
    ((β_ A A).hom ≫ shear A true ≫ (β_ A A).hom ≫ shear A false ≫ (β_ A A).hom) ≫ fst A A = fst A A ≫ ι[A] := by
  simp [shear, MonObj.comp_mul, GrpObj.comp_inv]
  rfl

noncomputable def invIso : A ≅ A := asIso ι[A]

variable {A} [IsCommMonObj A]

theorem transl_one : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by
  simp [transl]

theorem transl_mul (a b : 𝟙_ (Over (Sp K)) ⟶ A) : (transl a).hom ≫ (transl b).hom = (transl (a * b)).hom := by
  simp [transl, MonObj.comp_mul, toUnit_unique (_ ≫ toUnit A) (toUnit A), ← Category.assoc, mul_left_comm, _root_.mul_assoc]
end

theorem integral_powers {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left ∧ IsIntegral (A ⊗ A).left ∧ IsIntegral (A ⊗ (A ⊗ A)).left := by
  have := hA.smooth
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have h1 : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have h2 : IsIntegral (A ⊗ A).left := inferInstanceAs (IsIntegral (pullback A.hom A.hom))
  have : LocallyOfFiniteType (A ⊗ A).hom := by
    show LocallyOfFiniteType (pullback.fst _ _ ≫ A.hom); infer_instance
  have : IsLocallyNoetherian (A ⊗ A).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ A).hom
  exact ⟨h1, h2, inferInstanceAs (IsIntegral (pullback A.hom (A ⊗ A).hom))⟩

theorem exists_birLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ N : Model R A, BirLaw N ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso N N (transl (a ^ c)).hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  obtain ⟨h1, h2, h3⟩ := integral_powers A hA
  obtain ⟨hle, hcomp, hiso, hprod, hstr⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  have hP : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr → (X.prod Y).Irr :=
    fun {B B' X Y} => (GlobalTheory.T.prod_irr_and_weakNeron' R K hSH B B').1 X Y
  have hproj := GlobalTheory.T.generic_isomorphism_product_models R K hSH
  obtain ⟨S, hne, hS1, hS2⟩ := GlobalTheory.T.exists_automorphism_permutation_maxOrder_members R K hSH A hA n M hI hW
  have refl : ∀ {B : Over (Sp K)} {X : Model R B}, X.Irr → GenIso X X (𝟙 B) :=
    fun {B X} h => hle B X X h X.le_refl
  have comp : ∀ {B B' B'' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R B''} {f : B ⟶ B'}
      {g : B' ⟶ B''}, Y.Irr → GenIso X Y f → GenIso Y Z g → GenIso X Z (f ≫ g) :=
    fun {B B' B'' X Y Z f g} => hcomp B B' B'' X Y Z f g
  have symm : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'} (f : B ≅ B'),
      GenIso X Y f.hom → GenIso Y X f.inv := fun {B B' X Y} f => (hiso B B' X Y f).1
  have prod : ∀ {B B' C C' : Over (Sp K)} {X : Model R B} {Y : Model R B'} {Z : Model R C} {V : Model R C'}
      {f : B ⟶ C} {g : B' ⟶ C'}, GenIso X Z f → GenIso Y V g → GenIso (X.prod Y) (Z.prod V) (f ⊗ₘ g) :=
    fun {B B' C C' X Y Z V f g} => hprod B B' C C' X Y Z V f g
  have asc : ∀ i j k, GenIso (((M i).prod (M j)).prod (M k)) ((M i).prod ((M j).prod (M k))) (α_ A A A).hom :=
    fun i j k => (hstr A A A _ _ _ (hI i) (hI j) (hI k)).1
  have swp : ∀ {B B' : Over (Sp K)} {X : Model R B} {Y : Model R B'}, X.Irr → Y.Irr →
      GenIso (X.prod Y) (Y.prod X) (β_ B B').hom :=
    fun {B B' X Y} hX hY => (hstr B B' B X Y X hX hY hX).2
  have cmp : ∀ {C B : Over (Sp K)} [IsIntegral (A ⊗ B).left] {P : Model R C} {X X' : Model R A} {Y Y' : Model R B}
      (f g : C ⟶ A ⊗ B) [IsIso f], P.Irr → X.Irr → X'.Irr → Y.Irr → Y'.Irr → f ≫ fst A B = g ≫ fst A B →
      GenIso P (X.prod Y) f → GenIso P (X'.prod Y') g → GenIso X X' (𝟙 A) := by
    intro C B _ P X X' Y Y' f g _ hP hX hX' hY hY' e hf hg
    refine hproj A A B B X X' Y Y' (Iso.refl A) ((asIso f).inv ≫ g) hX hX' hY hY' ?_
      (comp hP (symm (asIso f) hf) hg)
    simp [← e]
  let r : Setoid S :=
    { r := fun i j => GenIso (M i) (M j) (𝟙 A)
      iseqv := ⟨fun i => refl (hI i), fun h => symm (Iso.refl A) h,
        fun h h' => by simpa using comp (hI _) h h'⟩ }
  let T : S → S → S → Prop := fun i j k => GenIso ((M i).prod (M j)) ((M i).prod (M k)) (shear A true)
  have hT : ∀ {i j k : S}, T i j k →
      GenIso ((M i).prod (M j)) ((M k).prod (M i)) (shear A true ≫ (β_ A A).hom) :=
    fun h => comp (hP (hI _) (hI _)) h (swp (hI _) (hI _))
  haveI : Nonempty S := hne.to_subtype
  obtain ⟨e, he⟩ := exists_idem_of_rel r T
    (by
      intro i j
      obtain ⟨i', hi', k, hk, h⟩ := hS2 (shearIso A) i i.2 j j.2
      have h0 : GenIso (M i) (M i') (𝟙 A) :=
        hproj A A A A _ _ _ _ (Iso.refl A) _ (hI _) (hI _) (hI _) (hI _) (by simp [shearIso, shear]) h
      have := comp (hP (hI _) (hI _)) h (prod (symm (Iso.refl A) h0) (refl (hI k)))
      refine ⟨⟨k, hk⟩, ?_⟩
      simpa [shearIso] using this)
    (by
      intro i j k k' h h'
      have := comp (hP (hI _) (hI _)) h (prod (refl (hI i)) h')
      simpa using this)
    (by
      intro i j l k m p q a b c d
      refine cmp _ _ (hP (hP (hI i) (hI j)) (hI l)) (hI m) (hI q) (hP (hI k) (hI i)) (hP (hI i) (hI j))
        (triple_fst A) ?_ ?_
      · exact comp (hP (hP (hI _) (hI _)) (hI _)) (prod a (refl (hI l))) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT b)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (swp (hI _) (hP (hI _) (hI _))) (asc _ _ _)
      · exact comp (hP (hI _) (hP (hI _) (hI _))) (asc _ _ _) <|
          comp (hP (hI _) (hP (hI _) (hI _))) (prod (refl (hI i)) (hT c)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (symm (α_ A A A) (asc _ _ _)) <|
          comp (hP (hP (hI _) (hI _)) (hI _)) (prod (hT d) (refl (hI j))) (asc _ _ _))
  have he' : GenIso ((M e).prod (M e)) ((M e).prod (M e)) (shear A false) := symm (shearIso A) he
  have hee := hP (hI e) (hI e)
  have hs := swp (hI e) (hI e)
  refine ⟨M e, ⟨hI e, fun b => by cases b <;> assumption, ?_⟩, (Fintype.card S).factorial,
    Nat.factorial_pos _, fun a => ?_⟩
  · exact hproj A A A A _ _ _ _ (invIso A) _ (hI e) (hI e) (hI e) (hI e) (inv_fst A)
      (comp hee hs <| comp hee he <| comp hee hs <| comp hee he' hs)
  · refine rel_factorial (fun p (i j : S) => GenIso (M i) (M j) (transl (a ^ p)).hom) ?_ ?_ ?_ ?_ e
    · intro i
      obtain ⟨j, hj, h⟩ := hS1 (transl (a ^ 1)) i i.2
      exact ⟨⟨j, hj⟩, h⟩
    · intro i
      simp only [pow_zero, transl_one]
      exact refl (hI i)
    · intro p q i j k h h'
      have := comp (hI _) h h'
      rwa [transl_mul, ← pow_add] at this
    · intro p d i j h h'
      have := comp (hI _) h' (symm _ h)
      rwa [add_comm, pow_add, ← transl_mul, Category.assoc, Iso.hom_inv_id, Category.comp_id] at this

end GlobalTheory.SS.NeutralModel
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.LocalWeightUnits

theorem exists_weight_zero_sum_one {A X J : Type} [CommRing A] [AddCommGroup X] [Fintype J] (P : X → AddSubgroup A)
    (one : 1 ∈ P 0) (mul : ∀ u v χ χ', u ∈ P χ → v ∈ P χ' → u * v ∈ P (χ + χ'))
    (ex : ∀ u : A, ∃ a : X →₀ A, (∀ χ, a χ ∈ P χ) ∧ u = a.sum fun _ x => x)
    (un : ∀ a : X →₀ A, (∀ χ, a χ ∈ P χ) → (a.sum fun _ x => x) = 0 → a = 0)
    (g : J → A) (δ : X) (hg : ∀ f, g f ∈ P δ) (hs : Ideal.span (Set.range g) = ⊤) :
    ∃ b : J → A, (∀ f, b f ∈ P 0) ∧ (∀ f, g f ∣ b f) ∧ ∑ f, b f = 1 := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs.ge (Submodule.mem_top (x := (1 : A))))
  choose a ha hsum using fun f => ex (c f)
  let T : (X →₀ A) →ₗ[A] A := Finsupp.lsum A fun _ => LinearMap.id
  have hT : ∀ a : X →₀ A, T a = a.sum fun _ x => x := fun a => rfl
  let B : X →₀ A := ∑ f, g f • Finsupp.equivMapDomain (Equiv.addLeft δ) (a f) - Finsupp.single 0 1
  have hB : ∀ χ, B χ = ∑ f, g f * a f (-δ + χ) - Finsupp.single (0 : X) (1 : A) χ := fun χ => by
    simp [B]
  have hm : ∀ f χ, g f * a f (-δ + χ) ∈ P χ := fun f χ => by
    simpa using mul _ _ _ _ (hg f) (ha f (-δ + χ))
  have h0 : B = 0 := by
    refine un B (fun χ => ?_) ?_
    · rw [hB]
      refine sub_mem (sum_mem fun f _ => hm f χ) ?_
      rw [Finsupp.single_apply]
      split_ifs with h
      · exact h ▸ one
      · exact zero_mem _
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← hT, map_sub, map_sum]
        simp only [map_smul]
        simp only [hT, Finsupp.sum_equivMapDomain, ← hsum, smul_eq_mul]
        rw [Finsupp.sum_single_index rfl, sub_eq_zero, ← hc]
        exact Finset.sum_congr rfl fun f _ => mul_comm _ _
  refine ⟨fun f => g f * a f (-δ + 0), fun f => hm f 0, fun f => Dvd.intro _ rfl, ?_⟩
  have := hB 0
  rw [h0, Finsupp.single_eq_same] at this
  exact (sub_eq_zero.1 this.symm)

variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ H}

theorem hasWt_iff {V : H.left.Opens} {u : Γ(H.left, V)} {χ : X} : HasWt i V u χ ↔ GlobalTheory.UU.IsWt i V u χ :=
  ⟨fun h Z t g h₁ h₂ => h Z t g h₂ h₁, fun h Z t g h₁ h₂ => h Z t g h₂ h₁⟩

def wtSpace (i : splitTorus S X ⟶ H) (V : H.left.Opens) (χ : X) : AddSubgroup Γ(H.left, V) where
  carrier := {u | GlobalTheory.UU.IsWt i V u χ}
  zero_mem' := GlobalTheory.UU.isWt_zero χ
  add_mem' := GlobalTheory.UU.IsWt.add
  neg_mem' := fun {u} hu Z t g h₁ h₂ => by rw [map_neg, map_neg, hu Z t g h₁ h₂, mul_neg]

theorem stable_basicOpen {V : H.left.Opens} (hV : Stable i V) {b : Γ(H.left, V)} (hb : HasWt i V b 0) :
    Stable i (H.left.basicOpen b) := by
  intro Y t g h
  have h₁ : ⊤ ≤ g.left ⁻¹ᵁ V := h.trans (g.left.preimage_mono (H.left.basicOpen_le b))
  have e := congrArg Y.left.basicOpen (hb Y t g h₁ (hV Y t g h₁))
  rw [charUnit_zero_val, map_one, _root_.one_mul, Scheme.basicOpen_appLE, Scheme.basicOpen_appLE] at e
  exact ((le_inf le_rfl h).trans e.ge).trans inf_le_right

theorem preimage_le_of_stable {V : H.left.Opens} (hV : Stable i V) :
    (snd (splitTorus S X) H).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) H ≫ i) * snd (splitTorus S X) H).left ⁻¹ᵁ V := by
  let U := (snd (splitTorus S X) H).left ⁻¹ᵁ V
  let Y : Over S := Over.mk (U.ι ≫ (splitTorus S X ⊗ H).hom)
  let j : Y ⟶ splitTorus S X ⊗ H := Over.homMk U.ι rfl
  have h := hV Y (j ≫ fst _ _) (j ≫ snd _ _) (fun y _ => y.2)
  rw [Category.assoc, ← MonObj.comp_mul] at h
  exact fun y hy => h (x := ⟨y, hy⟩) trivial

theorem exists_units {d : ℕ} {i : splitTorus S (Fin d → ℤ) ⟶ H} {V : H.left.Opens} (w : Fin d → Γ(H.left, V)ˣ)
    (hw : ∀ k, GlobalTheory.UU.IsWt i V (w k).val (Pi.single k 1)) :
    ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, V)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let e := Pi.basisFun ℤ (Fin d)
  let l : (Fin d → ℤ) →ₗ[ℤ] Additive Γ(H.left, V)ˣ := e.constr ℤ fun k => Additive.ofMul (w k)
  let M : AddSubgroup (Fin d → ℤ) :=
    { carrier := {χ | GlobalTheory.UU.IsWt i _ (Additive.toMul (l χ)).val χ}
      zero_mem' := by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l 0)).val 0
        rw [map_zero]; exact GlobalTheory.UU.isWt_one
      add_mem' := fun {a c} ha hc => by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (a + c))).val (a + c)
        rw [map_add (f := _)]; exact GlobalTheory.UU.IsWt.mul ha hc
      neg_mem' := fun {a} ha => by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (-a))).val (-a)
        rw [map_neg]; exact GlobalTheory.UU.IsWt.inv ha }
  have hM : Submodule.span ℤ (Set.range e) ≤ M.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (e k))).val (e k)
    rw [Module.Basis.constr_basis, Pi.basisFun_apply]
    exact hw k
  exact ⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => hasWt_iff.2 (hM (e.mem_span χ))⟩

theorem mem_basicOpen_of_mem {Z : Scheme.{0}} (C : Charts Z) {a a'} {j : C.I} {y : Z} (hy : y ∈ C.W a)
    (h : y ∈ Z.basicOpen (C.r a' j)) : y ∈ Z.basicOpen (C.r a j) := by
  have e := congrArg Z.basicOpen (C.trans a' a j)
  rw [Scheme.basicOpen_mul] at e
  erw [Z.basicOpen_res (C.r a' j) (homOfLE _).op, Z.basicOpen_res (C.r a j) (homOfLE _).op] at e
  exact (e.le ⟨⟨Z.basicOpen_le _ h, hy⟩, h⟩).2.2

theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∀ (a) (x : H.left), x ∈ C.W a → ∃ b : Γ(H.left, C.W a), HasWt i (C.W a) b 0 ∧ x ∈ H.left.basicOpen b ∧ Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by
  intro K _ H _ _ _ _ _ C d c i hT a x hx
  classical
  obtain ⟨ex, un⟩ := GlobalTheory.functions_graded_by_weights _ H _ i hT.hom (C.W a) (C.aff a) (preimage_le_of_stable (hT.stable a))
  let J := ∀ k : Fin d, {j : C.I // C.wt j = c k}
  let _ : Fintype J := Fintype.ofFinite J
  let g : J → Γ(H.left, C.W a) := fun f => ∏ k, C.r a (f k).1
  have hg : ∀ f, g f ∈ wtSpace i (C.W a) (∑ k : Fin d, Pi.single k 1) := fun f => by
    change GlobalTheory.UU.IsWt i _ (∏ k ∈ Finset.univ, C.r a (f k).1) (∑ k ∈ Finset.univ, Pi.single k 1)
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => exact GlobalTheory.UU.isWt_one
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact (hasWt_iff.1 (hT.wt a _ k (f k).2)).mul ih
  have hs : Ideal.span (Set.range g) = ⊤ := by
    rw [← (C.aff a).self_le_iSup_basicOpen_iff]
    intro y hy
    choose a' j hj hyj using fun k => hT.bpf k y
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g fun k => ⟨j k, hj k⟩, _, rfl⟩, ?_⟩
    rw [H.left.mem_basicOpen _ y hy, map_prod]
    exact IsUnit.prod_univ_iff.2 fun k => (H.left.mem_basicOpen _ y hy).1 (mem_basicOpen_of_mem C hy (hyj k))
  obtain ⟨b, hb, hd, h1⟩ := exists_weight_zero_sum_one (wtSpace i (C.W a)) GlobalTheory.UU.isWt_one
    (fun _ _ _ _ => GlobalTheory.UU.IsWt.mul) ex un g _ hg hs
  have hu : IsUnit (∑ f, (H.left.presheaf.germ (C.W a) x hx).hom (b f)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h1, map_one]; exact isUnit_one
  obtain ⟨f, -, hf⟩ := IsLocalRing.exists_of_isUnit_sum hu
  refine ⟨b f, hasWt_iff.2 (hb f), (H.left.mem_basicOpen _ x hx).2 hf,
    stable_basicOpen (hT.stable a) (hasWt_iff.2 (hb f)), ?_⟩
  have hw : ∀ k, IsUnit (resG H.left (H.left.basicOpen_le (b f)) (C.r a (f k).1)) := fun k =>
    isUnit_of_dvd_unit (map_dvd _ ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans (hd f)))
      (H.left.toRingedSpace.isUnit_res_basicOpen (b f))
  exact exists_units (fun k => (hw k).unit) fun k => (hasWt_iff.1 (hT.wt a _ k (f k).2)).res _

end GlobalTheory.LocalWeightUnits
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_symmetryHypothesis_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → ∀ (w wd : G ⟶ G) (w₀ wd₀ : A ⟶ A), φ ≫ w.left = w₀.left ≫ φ → φ ≫ wd.left = wd₀.left ≫ φ → IsMonHom w₀ → IsMonHom wd₀ → w₀ * wd₀ = 𝟙 A → LBIso L₀ (cubeLB A ![𝟙 A, w₀] L₀) → LBIso (cubeLB A ![fst A A ≫ w₀, snd A A] L₀) (cubeLB A ![fst A A, snd A A ≫ wd₀] L₀) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → HypS G' L' := by
  first | exact @GlobalTheory.SymSpread.exists_forall_hypS | exact GlobalTheory.SymSpread.exists_forall_hypS | (intros; apply GlobalTheory.SymSpread.exists_forall_hypS <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.torusCoord_unit_and_section_eq_expansion : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC), c ≫ u.G.hom = spMap u.j → gPt p ≫ c = u.toG a → u.Lev c g → u.GtN g 0 ∧ ∀ k, 1 ≤ k → u.ParAt k a g := by
  first | exact @GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt | exact GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt | (intros; apply GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.exists_lift_integralPoint_closure_testModel : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ b : Sp (OO p) ⟶ Q.P.left, b ≫ Q.P.hom = y → ⊤ ≤ b ⁻¹ᵁ Q.G → ∃ c' : Sp (OO p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = b := by
  first | exact @GlobalTheory.ZH.ClosLift.exists_lift | exact GlobalTheory.ZH.ClosLift.exists_lift | (intros; apply GlobalTheory.ZH.ClosLift.exists_lift <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem pull_inv_cls_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) :
    CechPic.pull (GrpObj.inv : G' ⟶ G').left (CechPic.cls L' hL') = CechPic.cls L' hL' ↔
      LBIso ((L.pull (GrpObj.inv : G ⟶ G).left).pull φ) (L.pull φ) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _),
    (CechPic.cls_eq_iff hL' (pull_isLB hL _)).2 e, CechPic.cls_pull hL, CechPic.cls_pull (pull_isLB hL _),
    CechPic.cls_pull hL, ← CechPic.pull_comp, ← CechPic.pull_comp, OddDescent.inv_left_comp h]

theorem exists_sym : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ e hs
  have := hG.proper
  obtain ⟨a, ha, H⟩ := exists_lbIso G.hom h.1 (pull_isLB hL _) hL
    ((pull_inv_cls_iff h hL hL₀ e).1 (OddDescent.pull_inv_cls_of_sym A hL₀ hs))
  exact ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' e' => OddDescent.sym_of_pull_inv_cls G' hL'
    ((pull_inv_cls_iff h' hL hL' e').2 (H R' g hg _ π G'.hom h'.1.w))⟩

end GlobalTheory.GenSpread
end
