module

public import Mathlib
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace Limits Abelian

universe w' u

variable {X : TopCat.{u}} {B : Opens X → Prop}

noncomputable def injectiveSequence (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma injectiveSequence_shortExact (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (injectiveSequence F).ShortExact :=
  ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F)))
    (inferInstanceAs (Mono (Injective.ι F))) coequalizer.π_epi

instance (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Injective (injectiveSequence F).X₂ :=
  inferInstanceAs (Injective (Injective.under F))

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsNormalScheme (X : Scheme.{u}) : Prop where
  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)
  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

def PrimeDivisor (X : Scheme.{u}) : Type u :=
  {x : X // ringKrullDim (X.presheaf.stalk x) = 1}

abbrev WeilDivisor (X : Scheme.{u}) : Type u := PrimeDivisor X →₀ ℤ

variable {X : Scheme.{u}}

namespace PrimeDivisor

def point (x : PrimeDivisor X) : X := x.1

lemma ringKrullDim_stalk (x : PrimeDivisor X) :
    ringKrullDim (X.presheaf.stalk x.point) = 1 := x.2

lemma coheight_point (x : PrimeDivisor X) : Order.coheight x.point = 1 := by
  have h := x.ringKrullDim_stalk
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

lemma point_injective : Function.Injective (point (X := X)) := fun _ _ h => Subtype.ext h

lemma maximalIdeal_ne_bot (x : PrimeDivisor X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.point) ≠ ⊥ := by
  intro h
  have hf : IsField (X.presheaf.stalk x.point) :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
  have := x.ringKrullDim_stalk
  rw [ringKrullDim_eq_zero_of_isField hf] at this
  exact zero_ne_one this

variable [IsIntegral X]

lemma dimensionLEOne_stalk (x : PrimeDivisor X) :
    Ring.DimensionLEOne (X.presheaf.stalk x.point) := by
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk x.point) := by
    rw [Ring.krullDimLE_iff, x.ringKrullDim_stalk]
    norm_num
  refine ⟨fun {p} hp hprime => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
  · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
    exact absurd h hp
  · exact h

variable [IsLocallyNoetherian X] [IsNormalScheme X]

lemma isDedekindDomain_stalk (x : PrimeDivisor X) :
    IsDedekindDomain (X.presheaf.stalk x.point) := by
  have := x.dimensionLEOne_stalk
  have := IsNormalScheme.isIntegrallyClosed_stalk (X := X) x.point
  exact (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk x.point))).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩

noncomputable def heightOneSpectrum (x : PrimeDivisor X) :
    HeightOneSpectrum (X.presheaf.stalk x.point) :=
  ⟨IsLocalRing.maximalIdeal _, (IsLocalRing.maximalIdeal.isMaximal _).isPrime,
    x.maximalIdeal_ne_bot⟩

noncomputable def valuation (x : PrimeDivisor X) : Valuation X.functionField (WithZero (Multiplicative ℤ)) :=
  @HeightOneSpectrum.valuation _ _ x.isDedekindDomain_stalk _ _ _ _ x.heightOneSpectrum

noncomputable def ord (x : PrimeDivisor X) (f : X.functionField) : ℤ :=
  - WithZero.log (x.valuation f)

lemma ord_mul (x : PrimeDivisor X) {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    x.ord (f * g) = x.ord f + x.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf) ((Valuation.ne_zero_iff _).mpr hg)]
  ring

end PrimeDivisor

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

lemma ord_algebraMap_of_isUnit (x : PrimeDivisor X) {a : X.presheaf.stalk x.point}
    (ha : IsUnit a) : x.ord (algebraMap _ X.functionField a) = 0 := by
  have := x.isDedekindDomain_stalk
  have h1 : x.valuation (algebraMap _ X.functionField a) = 1 := by
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal a).mp hm ha
  simp [ord, h1]

lemma ord_germToFunctionField_of_isUnit (x : PrimeDivisor X) {U : X.Opens} [Nonempty U]
    (hx : x.point ∈ U) {g : Γ(X, U)} (hg : IsUnit g) :
    x.ord (X.germToFunctionField U g) = 0 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
  exact x.ord_algebraMap_of_isUnit (hg.map _)

end PrimeDivisor

lemma PrimeDivisor.eq_genericPoint_of_mem [IsIntegral X] (x : PrimeDivisor X) {T : Set X}
    (hT : IsIrreducible T) (hTc : IsClosed T) (hgen : genericPoint X ∉ T) (hx : x.point ∈ T) :
    x.point = hT.genericPoint := by
  set c := hT.genericPoint
  have hc : IsGenericPoint c T := by
    have := hT.isGenericPoint_genericPoint_closure
    rwa [hTc.closure_eq] at this
  have hcx : c ⤳ x.point := hc.specializes hx
  have hcT : c ∈ T := hc.mem
  have hηc : genericPoint X ⤳ c := (genericPoint_spec X).specializes (Set.mem_univ _)
  have hηne : genericPoint X ≠ c := fun h => hgen (h ▸ hcT)
  have hlt1 : c < genericPoint X := by
    refine ⟨hηc, fun h => hηne (h.antisymm hηc).eq.symm⟩
  by_contra hne
  have hlt2 : x.point < c := ⟨hcx, fun h => hne (hcx.antisymm h).eq.symm⟩
  have h1 := Order.coheight_add_one_le hlt1
  have h2 := Order.coheight_add_one_le hlt2
  rw [x.coheight_point] at h2
  have h4 : (1 : ℕ∞) ≤ Order.coheight c := le_trans le_add_self h1
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add_left h4 1) h2
  norm_num at h5

section Finite

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

theorem PrimeDivisor.finite_ord_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    {x : PrimeDivisor X | x.ord f ≠ 0}.Finite := by
  obtain ⟨U, -, g, hne, hgf, hgu⟩ := exists_isUnit_germ_eq X f hf
  set Z : Set X := (U : Set X)ᶜ with hZ
  have hZc : IsClosed Z := U.isOpen.isClosed_compl
  have hgenU : genericPoint X ∈ U := by
    obtain ⟨⟨y, hy⟩⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hsub : {x : PrimeDivisor X | x.ord f ≠ 0} ⊆ {x | x.point ∈ Z} := by
    intro x hx
    by_contra hxU
    simp only [Set.mem_ofPred_eq, hZ, Set.mem_compl_iff, not_not] at hxU
    exact hx (hgf ▸ x.ord_germToFunctionField_of_isUnit hxU hgu)
  refine Set.Finite.subset ?_ hsub
  have key : ∀ (x : PrimeDivisor X) (hx : x.point ∈ Z) (C : Set Z),
      C ∈ irreducibleComponents Z → (⟨x.point, hx⟩ : Z) ∈ C →
      ∃ hT : IsIrreducible (closure (Subtype.val '' C)), x.point = hT.genericPoint := by
    intro x hx C hC hxC
    have hT : IsIrreducible (closure (Subtype.val '' C)) :=
      (hC.1.image _ continuous_subtype_val.continuousOn).closure
    refine ⟨hT, x.eq_genericPoint_of_mem hT isClosed_closure ?_ ?_⟩
    · intro hg
      have : closure (Subtype.val '' C) ⊆ Z :=
        closure_minimal (Subtype.coe_image_subset _ _) hZc
      exact this hg hgenU
    · exact subset_closure ⟨_, hxC, rfl⟩
  have hcomp : ∀ x : {x : PrimeDivisor X | x.point ∈ Z}, ∃ C ∈ irreducibleComponents Z,
      {(⟨x.1.point, x.2⟩ : Z)} ⊆ C := fun x =>
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ isIrreducible_singleton
  let φ : {x : PrimeDivisor X | x.point ∈ Z} → irreducibleComponents Z := fun x =>
    ⟨(hcomp x).choose, (hcomp x).choose_spec.1⟩
  have : Finite (irreducibleComponents Z) :=
    (NoetherianSpace.finite_irreducibleComponents (α := Z)).to_subtype
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hx := (hcomp x).choose_spec
    have hy := (hcomp y).choose_spec
    have hC : (hcomp x).choose = (hcomp y).choose := congrArg Subtype.val hxy
    obtain ⟨hT, hxT⟩ := key x.1 x.2 _ hx.1 (hx.2 rfl)
    obtain ⟨hT', hyT⟩ := key y.1 y.2 _ hy.1 (hy.2 rfl)
    apply Subtype.ext
    apply PrimeDivisor.point_injective
    rw [hxT, hyT]
    simp only [hC]
  have : Finite {x : PrimeDivisor X | x.point ∈ Z} := Finite.of_injective φ hφ
  exact Set.toFinite _

end Finite

section Divisor

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]



end Divisor

end GroundTheory.Arith.SchemeCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian

universe w' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section ExtIso

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w'} 𝒜]

noncomputable def extAddEquivOfIsoLeft {X X' : 𝒜} (e : X ≅ X') (Y : 𝒜) (n : ℕ) :
    Ext X Y n ≃+ Ext X' Y n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [Ext.comp_add]

private lemma extAddEquiv₀_comp_mk₀ {X Y Z : 𝒜} (x : Ext X Y 0) (f : Y ⟶ Z) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective X Z).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]

end ExtIso

section Terminal

variable [HasSheafify J AddCommGrpCat.{v}]

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

end Terminal

section Zero

noncomputable def freeYonedaHomAddEquiv (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) ≃+ P.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) P).trans yonedaEquiv
  map_add' _ _ := rfl

lemma freeYonedaHomAddEquiv_apply (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P g = g.app (op U) (FreeAbelianGroup.of (𝟙 U)) := rfl

variable [HasSheafify J AddCommGrpCat.{v}]

noncomputable abbrev freeSheaf (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

noncomputable def freeSheafHomAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ F).trans
    (freeYonedaHomAddEquiv U F.obj)

lemma freeSheafHomAddEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (g : freeSheaf J U ⟶ F) (φ : F ⟶ G) :
    freeSheafHomAddEquiv U G (g ≫ φ) = φ.hom.app (op U) (freeSheafHomAddEquiv U F g) := by
  exact congrArg (freeYonedaHomAddEquiv U G.obj)
    ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_naturality_right
      (X := yoneda.obj U ⋙ AddCommGrpCat.free) g φ)

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

noncomputable def H'.equiv₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).trans (freeSheafHomAddEquiv U F)

lemma cohomologyPresheafFunctor_map_app_apply {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G)
    (n : ℕ) (U : C) (x : F.H' n U) :
    ((Sheaf.cohomologyPresheafFunctor J n).map φ).app (op U) x =
      (show Ext (freeSheaf J U) F n from x).comp (Ext.mk₀ φ) (add_zero n) := rfl

lemma H'.equiv₀_naturality {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    H'.equiv₀ G U (((Sheaf.cohomologyPresheafFunctor J 0).map φ).app (op U) x) =
      φ.hom.app (op U) (H'.equiv₀ F U x) := by
  let x₀ : Ext (freeSheaf J U) F 0 := x
  exact (congrArg (freeSheafHomAddEquiv U G) (extAddEquiv₀_comp_mk₀ x₀ φ)).trans
    (freeSheafHomAddEquiv_naturality U (Ext.addEquiv₀ x₀) φ)

end Zero

section Injective

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

lemma H.eq_zero_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] {n : ℕ}
    (x : Sheaf.H F (n + 1)) : x = 0 :=
  Ext.eq_zero_of_injective x

instance H'.subsingleton_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (n : ℕ)
    (U : C) : Subsingleton (F.H' (n + 1) U) :=
  subsingleton_of_forall_eq 0 fun x =>
    Ext.eq_zero_of_injective (show Ext (freeSheaf J U) F (n + 1) from x)

end Injective

section LongExact

private lemma exact_ab_zero_apply {T : ShortComplex AddCommGrpCat.{w'}}
    (hT : T.Exact) (x : T.X₁) : T.g (T.f x) = 0 :=
  ((ShortComplex.ab_exact_iff_function_exact T).mp hT).apply_apply_eq_zero x

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

noncomputable def H.δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Sheaf.H S.X₃ n₀ →+ Sheaf.H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

lemma H.δ_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    H.δ hS n₀ n₁ h x = x.comp hS.extClass h := rfl


include hS in
theorem H.exact₂ {n : ℕ} (y : Sheaf.H S.X₂ n) (hy : Sheaf.H.map S.g n y = 0) :
    ∃ x : Sheaf.H S.X₁ n, Sheaf.H.map S.f n x = y :=
  Sheaf.H.longSequence_exact₂ hS y hy

theorem H.exact₃ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (y : Sheaf.H S.X₃ n₀)
    (hy : H.δ hS n₀ n₁ h y = 0) : ∃ x : Sheaf.H S.X₂ n₀, Sheaf.H.map S.g n₀ x = y :=
  Sheaf.H.longSequence_exact₃ hS y h hy

theorem H.exact₁ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₁ n₁)
    (hx : Sheaf.H.map S.f n₁ x = 0) : ∃ y : Sheaf.H S.X₃ n₀, H.δ hS n₀ n₁ h y = x :=
  Sheaf.H.longSequence_exact₁ hS x hx h

lemma H.map_g_map_f {n : ℕ} (x : Sheaf.H S.X₁ n) :
    Sheaf.H.map S.g n (Sheaf.H.map S.f n x) = 0 :=
  (S.map (Sheaf.functorH J n)).ab_zero_apply x

lemma H.δ_map_g {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₂ n₀) :
    H.δ hS n₀ n₁ h (Sheaf.H.map S.g n₀ x) = 0 :=
  exact_ab_zero_apply (Sheaf.H.longSequence_exact₃' hS n₀ n₁ h) x

lemma H.map_f_δ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    Sheaf.H.map S.f n₁ (H.δ hS n₀ n₁ h x) = 0 :=
  exact_ab_zero_apply (Sheaf.H.longSequence_exact₁' hS n₀ n₁ h) x

end LongExact

end GroundTheory.Arith.SchemeCoh
end
