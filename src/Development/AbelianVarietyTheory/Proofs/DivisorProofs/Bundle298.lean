module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle186
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Sifted
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Mathlib.Algebra.CharP.Frobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FiniteTypeColimit

noncomputable def diagram (A : CommRingCat.{0}) : Finset A ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin ℤ (t : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 (leOfHom h)))).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def inclusions (A : CommRingCat.{0}) : diagram A ⟶ (Functor.const (Finset A)).obj A where
  app t := CommRingCat.ofHom (Algebra.adjoin ℤ (t : Set A)).val.toRingHom
  naturality _ _ _ := rfl

noncomputable def isColimit (A : CommRingCat.{0}) : IsColimit (Cocone.mk A (inclusions A)) := by
  classical
  haveI : ReflectsColimit (diagram A) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)
  · exact ⟨{x}, ⟨x, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨i, 𝟙 i, by rw [this]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.finiteType (A : CommRingCat.{0}) (t : Finset A) :
    Algebra.FiniteType ℤ ((_root_.GlobalTheory.FiniteTypeColimit.diagram A).obj t) := by
  have h : (Algebra.adjoin ℤ (t : Set A)).FG := Subalgebra.fg_adjoin_finset t
  have := (Subalgebra.fg_iff_finiteType _).1 h
  change Algebra.FiniteType ℤ (CommRingCat.of (Algebra.adjoin ℤ (t : Set A)))
  convert this


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType : ∀ A : CommRingCat.{0},
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
      (ι : D ⟶ (Functor.const J).obj A),
      Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) :=
  fun A => ⟨Finset A, inferInstance, inferInstance, _root_.GlobalTheory.FiniteTypeColimit.diagram A,
    _root_.GlobalTheory.FiniteTypeColimit.inclusions A, ⟨_root_.GlobalTheory.FiniteTypeColimit.isColimit A⟩,
    _root_.GlobalTheory.FiniteTypeColimit.finiteType A⟩

end GlobalTheory.FiniteTypeColimit
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem widePushout_finiteType_int {J : Type} [Finite J] [Nonempty J] (A B : CommRingCat.{0})
    (g : A ⟶ B) (hB : Algebra.FiniteType ℤ B) :
    Algebra.FiniteType ℤ ((widePushout A (fun _ : J => B) (fun _ => g) : CommRingCat.{0})) := by
  classical
  obtain ⟨s, hs⟩ := hB.out
  set W := widePushout A (fun _ : J => B) (fun _ => g) with hW
  let T : Set W := ⋃ j : J, (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)
  have hTfin : T.Finite := Set.finite_iUnion fun j => s.finite_toSet.image _
  let S : Subring W := Subring.closure T
  have hB' : ∀ b : B, b ∈ Subring.closure (s : Set B) := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := hs ▸ Algebra.mem_top
    rw [Algebra.adjoin_int] at hb
    exact hb
  have hmem : ∀ (j : J) (b : B), (WidePushout.ι (fun _ : J => g) j).hom b ∈ S := by
    intro j b
    have hle : (Subring.closure (s : Set B)).map (WidePushout.ι (fun _ : J => g) j).hom ≤ S := by
      rw [RingHom.map_closure]
      exact Subring.closure_mono (Set.subset_iUnion (fun j => (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)) j)
    exact hle ⟨b, hB' b, rfl⟩
  let ιS : J → (B ⟶ CommRingCat.of S) := fun j =>
    CommRingCat.ofHom ((WidePushout.ι (fun _ : J => g) j).hom.codRestrict S (hmem j))
  let j₀ : J := Classical.arbitrary J
  have hw : ∀ j : J, g ≫ ιS j = g ≫ ιS j₀ := by
    intro j
    ext a
    change (g ≫ WidePushout.ι (fun _ : J => g) j) a = (g ≫ WidePushout.ι (fun _ : J => g) j₀) a
    rw [WidePushout.arrow_ι (fun _ : J => g) j, WidePushout.arrow_ι (fun _ : J => g) j₀]
  let d : W ⟶ CommRingCat.of S := WidePushout.desc (g ≫ ιS j₀) ιS hw
  let incl : CommRingCat.of S ⟶ W := CommRingCat.ofHom S.subtype
  have hid : d ≫ incl = 𝟙 W := by
    apply WidePushout.hom_ext
    · intro j
      rw [← Category.assoc, WidePushout.ι_desc]
      ext b <;> rfl
    · rw [← Category.assoc, WidePushout.head_desc, ← WidePushout.arrow_ι (fun _ : J => g) j₀]
      ext a <;> rfl
  have htop : ∀ w : W, w ∈ S := by
    intro w
    have : (d ≫ incl) w = w := by rw [hid]; rfl
    rw [← this]
    exact (d w).2
  refine ⟨⟨hTfin.toFinset, ?_⟩⟩
  rw [Set.Finite.coe_toFinset, Algebra.adjoin_int]
  ext w
  simp only [Algebra.mem_top, iff_true]
  exact htop w

end GlobalTheory

theorem GlobalTheory.cechConerve_obj_finiteType_int : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), Algebra.FiniteType ℤ B →
    ∀ k : SimplexCategory, Algebra.FiniteType ℤ ((Arrow.mk g).cechConerve.obj k) := by
  intro A B g hB k
  exact GlobalTheory.widePushout_finiteType_int (J := Fin (k.len + 1)) A B g hB
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.BaseChangeColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}}
  (g' : D.obj j ⟶ B')

noncomputable def mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout g' (D.map k.hom) ⟶ pushout g' (D.map k'.hom) :=
  pushout.desc (pushout.inl g' (D.map k'.hom)) (D.map f.right ≫ pushout.inr g' (D.map k'.hom))
    (by rw [pushout.condition, ← Category.assoc, ← D.map_comp, Under.w f])

@[reassoc]
lemma inl_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f = pushout.inl g' (D.map k'.hom) :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma inr_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f = D.map f.right ≫ pushout.inr g' (D.map k'.hom) :=
  pushout.inr_desc _ _ _

noncomputable def diag : Under j ⥤ CommRingCat.{0} where
  obj k := pushout g' (D.map k.hom)
  map f := mapPush D j g' f
  map_id k := by
    apply pushout.hom_ext
    · rw [inl_mapPush, Category.comp_id]
    · rw [inr_mapPush, Category.comp_id, Under.id_right, D.map_id, Category.id_comp]
  map_comp f f' := by
    apply pushout.hom_ext
    · rw [inl_mapPush, inl_mapPush_assoc, inl_mapPush]
    · rw [inr_mapPush, inr_mapPush_assoc, inr_mapPush, Under.comp_right, D.map_comp,
        Category.assoc]

noncomputable def inrNat : Under.forget j ⋙ D ⟶ diag D j g' where
  app k := pushout.inr g' (D.map k.hom)
  naturality k k' f := by
    show D.map f.right ≫ pushout.inr g' (D.map k'.hom) = pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inr_mapPush]

noncomputable def inlNat : (Functor.const _).obj B' ⟶ diag D j g' where
  app k := pushout.inl g' (D.map k.hom)
  naturality k k' f := by
    show 𝟙 B' ≫ pushout.inl g' (D.map k'.hom) = pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inl_mapPush, Category.id_comp]

noncomputable def toB (c : Cocone D) {B : CommRingCat.{0}} (h : B' ⟶ B) (g : c.pt ⟶ B)
    (sq : g' ≫ h = c.ι.app j ≫ g) : diag D j g' ⟶ (Functor.const _).obj B where
  app k := pushout.desc h (c.ι.app k.right ≫ g) (by rw [sq, ← c.w k.hom, Category.assoc])
  naturality k k' f := by
    show mapPush D j g' f ≫ pushout.desc h (c.ι.app k'.right ≫ g) _ =
      pushout.desc h (c.ι.app k.right ≫ g) _ ≫ 𝟙 B
    apply pushout.hom_ext
    · rw [inl_mapPush_assoc, pushout.inl_desc, pushout.inl_desc_assoc, Category.comp_id]
    · rw [inr_mapPush_assoc, pushout.inr_desc, pushout.inr_desc_assoc, Category.comp_id,
        ← Category.assoc, c.w]

theorem exists_isColimit_pushout_under : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (B' B : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B) (g : c.pt ⟶ B), IsPushout g' (c.ι.app j) h g → ∃ (D' : Under j ⥤ CommRingCat.{0}) (ι : D' ⟶ (Functor.const _).obj B) (u : Under.forget j ⋙ D ⟶ D') (v : (Functor.const _).obj B' ⟶ D'), Nonempty (IsColimit (Cocone.mk B ι)) ∧ ∀ k : Under j, IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ι.app k = h ∧ u.app k ≫ ι.app k = c.ι.app k.right ≫ g := by
  intro J _ _ D c hc j B' B g' h g hsq
  refine ⟨diag D j g', toB D j g' c h g hsq.w, inrNat D j g', inlNat D j g', ⟨?_⟩,
    fun k => ⟨IsPushout.of_hasPushout _ _, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩⟩
  have hc' : IsColimit (c.whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv _ _).symm hc
  let k0 : Under j := Under.mk (𝟙 j)

  let e : ∀ (s : Cocone (diag D j g')) (k : Under j), pushout g' (D.map k.hom) ⟶ s.pt :=
    fun s k => s.ι.app k
  have he : ∀ (s : Cocone (diag D j g')) {k k' : Under j} (f : k ⟶ k'),
      mapPush D j g' f ≫ e s k' = e s k := fun s _ _ f => s.w f
  let r : Cocone (diag D j g') → Cocone (Under.forget j ⋙ D) := fun s =>
    { pt := s.pt, ι := inrNat D j g' ≫ s.ι }
  have hl : ∀ (s : Cocone (diag D j g')) (k : Under j),
      pushout.inl g' (D.map k.hom) ≫ e s k = pushout.inl g' (D.map k0.hom) ≫ e s k0 := by
    intro s k
    rw [← he s (Under.homMk k.hom (Category.id_comp k.hom) : k0 ⟶ k), inl_mapPush_assoc]
  have hfr : ∀ (s : Cocone (diag D j g')) (k : Under j),
      c.ι.app k.right ≫ hc'.desc (r s) = pushout.inr g' (D.map k.hom) ≫ e s k :=
    fun s k => hc'.fac (r s) k
  have hw : ∀ s : Cocone (diag D j g'),
      g' ≫ (pushout.inl g' (D.map k0.hom) ≫ e s k0) = c.ι.app j ≫ hc'.desc (r s) := by
    intro s
    rw [show c.ι.app j = c.ι.app k0.right from rfl, hfr, ← Category.assoc, pushout.condition,
      Category.assoc]
    exact (congrArg (· ≫ (pushout.inr g' (D.map k0.hom) ≫ e s k0)) (D.map_id j)).trans
      (Category.id_comp _)
  exact
    { desc := fun s => hsq.desc _ _ (hw s)
      fac := fun s k => by
        change pushout.desc _ _ _ ≫ _ = e s k
        apply pushout.hom_ext
        · rw [pushout.inl_desc_assoc, hsq.inl_desc, hl s k]
        · rw [pushout.inr_desc_assoc, Category.assoc, hsq.inr_desc, hfr]
      uniq := fun s m hm => by
        have hm' : ∀ k : Under j, pushout.desc h (c.ι.app k.right ≫ g)
            (by rw [hsq.w, ← c.w k.hom, Category.assoc]) ≫ m = e s k := hm
        apply hsq.hom_ext
        · rw [hsq.inl_desc, ← hm' k0, pushout.inl_desc_assoc]
        · rw [hsq.inr_desc]
          apply hc'.hom_ext
          intro k
          change c.ι.app k.right ≫ g ≫ m = c.ι.app k.right ≫ hc'.desc (r s)
          rw [hfr, ← hm' k, pushout.inr_desc_assoc, Category.assoc] }

end GlobalTheory.BaseChangeColim
end

section

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.FrobDeriv

def FrobTwist (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (M : Type) : Type := M

variable {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime]
  [CharP K p]

instance : AddCommGroup (FrobTwist K p M) := inferInstanceAs (AddCommGroup M)

noncomputable instance : Module K (FrobTwist K p M) :=
  Module.compHom M (frobenius K p)

theorem twist_smul (c : K) (m : FrobTwist K p M) :
    c • m = (c ^ p • (show M from m) : M) := by
  show (frobenius K p c) • (show M from m) = _
  rw [frobenius_def]

end GlobalTheory.DI.FrobDeriv

open GlobalTheory.DI.FrobDeriv in
theorem GlobalTheory.DI.frobDeriv_factors_kaehler : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  intro K _ M _ _ p _ _ φ hφ
  let ψ : K →ₗ[ℤ] FrobTwist K p M := (φ : K →+ M).toIntLinearMap
  have hone : φ 1 = 0 := by
    have h := hφ 1 1
    simp only [mul_one, one_pow, one_smul] at h
    have : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  let D : Derivation ℤ K (FrobTwist K p M) :=
    { toLinearMap := ψ
      map_one_eq_zero' := hone
      leibniz' := fun a b => by
        show φ (a * b) = a • (show FrobTwist K p M from φ b) + b • (show FrobTwist K p M from φ a)
        rw [twist_smul, twist_smul, hφ]; rfl }
  refine ⟨(D.liftKaehlerDifferential).toAddMonoidHom, ?_, ?_⟩
  · intro c v
    show D.liftKaehlerDifferential (c • v) = _
    rw [LinearMap.map_smul, twist_smul]
    rfl
  · intro a
    show D.liftKaehlerDifferential (KaehlerDifferential.D ℤ K a) = φ a
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
end

section

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.SecondOrderNbhd

open TrivSqZeroExt

noncomputable def deform {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) : O →+* DualNumber R where
  toFun x := inl (f x) + inr (f (D x))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] lemma deform_fst {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).fst = f x := by
  simp [deform]

@[simp] lemma deform_snd {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).snd = f (D x) := by
  simp [deform]

lemma isNilpotent_span_of_sq {C : Type} [CommRing C] {e : C} (h : e * e = 0) :
    IsNilpotent (Ideal.span {e}) := by
  refine ⟨2, ?_⟩
  rw [Ideal.span_singleton_pow, pow_two, h]
  simp

theorem exists_second_order_nbhd : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  intro O _ _ D₁ D₂ h
  let i : O →+* DualNumber O := (inlHom O O)
  let j : DualNumber O →+* DualNumber (DualNumber O) := inlHom _ _
  let e₁ : DualNumber (DualNumber O) := inl DualNumber.eps
  let e₂ : DualNumber (DualNumber O) := DualNumber.eps
  have h1 : e₁ * e₁ = 0 := by
    simp only [e₁]; rw [inl_mul_inl, DualNumber.eps_mul_eps]; simp
  have h2 : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  refine ⟨DualNumber (DualNumber O), inferInstance, Ideal.span {e₁} + Ideal.span {e₂},
    j.comp i, j.comp (deform D₁ (RingHom.id O)), deform D₂ i,
    deform D₂ (deform D₁ (RingHom.id O)), e₁, e₂, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Commute.all _ _).isNilpotent_add (isNilpotent_span_of_sq h1) (isNilpotent_span_of_sq h2)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · intro x; ext <;> simp [i, j, e₁]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₁, h]
  · intro x hx
    have := congrArg (fun z : DualNumber (DualNumber O) => z.snd.snd) hx
    simpa [i, j, e₁, e₂] using this

end GlobalTheory.SecondOrderNbhd
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (f : Sp (DualNumber K) ⟶ Sp K), f = spMap (algebraMap K (DualNumber K)) → (∀ x y : Over.mk f ⟶ A, x * y = y * x) → ∀ (u : Over.mk f ⟶ A) (n : ℕ), 0 < n → u ^ n = 1 → u.left = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ u.left := by
  first | exact @GlobalTheory.TorsConst.torsion_eq_const | exact GlobalTheory.TorsConst.torsion_eq_const | (intros; apply GlobalTheory.TorsConst.torsion_eq_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  first | exact @GlobalTheory.SchRing.deformation_on_sections | exact GlobalTheory.SchRing.deformation_on_sections | (intros; apply GlobalTheory.SchRing.deformation_on_sections <;> assumption)
end

section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.TowerLift

theorem closed_lift (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hdc : ∀ n x, d n (c n x) = 0) (hsc : ∀ n x, s n (c (n + 1) x) = c n (r n x)) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x))
    (hr : ∀ n, Function.Surjective (r n)) (hcl : ∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w)
    (b : ∀ n, B n) (hb : ∀ n, t n (b (n + 1)) = b n) (hrg : ∀ n, ∃ a, d n a = b n) :
    ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n := by
  have step : ∀ n (x : {a : A n // d n a = b n}), ∃ y : {a : A (n + 1) // d (n + 1) a = b (n + 1)}, s n y.1 = x.1 := by
    intro n x
    obtain ⟨x', hx'⟩ := hrg (n + 1)
    have h0 : d n (x.1 - s n x') = 0 := by
      rw [map_sub, x.2, ← htd, hx', hb, sub_self]
    obtain ⟨a', w, ha', hw⟩ := hcl n _ h0
    obtain ⟨w', rfl⟩ := hr n w
    refine ⟨⟨x' + a' + c (n + 1) w', ?_⟩, ?_⟩
    · rw [map_add (f := _), map_add (f := _), hx', ha', hdc, add_zero, add_zero]
    · show s n (x' + a' + c (n + 1) w') = x.1
      rw [map_add (f := _), map_add (f := _), hsc, add_assoc, ← hw, add_sub_cancel]
  choose f hf using step
  obtain ⟨a₀, ha₀⟩ := hrg 0
  let g : ∀ n, {a : A n // d n a = b n} := fun n => Nat.rec ⟨a₀, ha₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, fun n => hf n (g n), fun n => (g n).2⟩

theorem closed_extend (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hd : ∀ n x, d n x ∈ Z n) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x)) (hs : ∀ n, Function.Surjective (s n))
    (hZ : ∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) (hl : ∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) :
    ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  intro b₀ hb₀
  have step : ∀ n (x : Z n), ∃ y : Z (n + 1), t n y.1 = x.1 := by
    intro n x
    obtain ⟨b', hb', a, ha⟩ := hl n x.1 x.2
    obtain ⟨a'', rfl⟩ := hs n a
    refine ⟨⟨b' + d (n + 1) a'', (Z (n + 1)).add_mem hb' (hd _ _)⟩, ?_⟩
    show t n (b' + d (n + 1) a'') = x.1
    rw [map_add (f := _), htd, ha]
  choose f hf using step
  let g : ∀ n, Z n := fun n => Nat.rec ⟨b₀, hb₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, rfl, fun n => (g n).2, fun n => hf n (g n)⟩

theorem tower_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n :=
  ⟨closed_lift, closed_extend⟩

end GlobalTheory.TowerLift
end
