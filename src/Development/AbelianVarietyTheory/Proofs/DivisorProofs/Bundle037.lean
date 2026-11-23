module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.LocallyDirected
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AlgConn

abbrev twoπ (O : Type) [CommRing O] : Spec (.of (O × O)) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))

abbrev fst1 (O : Type) [CommRing O] : Γ(Spec (.of (O × O)), ⊤) :=
  (Scheme.ΓSpecIso (.of (O × O))).inv.hom ((1, 0) : O × O)

theorem isProper_twoπ (O : Type) [CommRing O] : IsProper (twoπ O) := by
  haveI : IsFinite (twoπ O) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  infer_instance

theorem isClopen_basicOpen_specProdSelfFirstIdempotent (O : Type) [CommRing O] :
    IsClopen (((Spec (.of (O × O))).basicOpen (fst1 O) : (Spec (.of (O × O))).Opens) :
      Set (Spec (.of (O × O)))) := by
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.isClopen_iff.2 ⟨((1, 0) : O × O), by ext <;> simp [IsIdempotentElem], rfl⟩

end GlobalTheory.AlgConn
end
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibrePowerProper

theorem isProper_hom_of_iso {T : Scheme.{0}} {X Y : Over T} (e : X ≅ Y) (h : IsProper Y.hom) :
    IsProper X.hom := by
  have hw : X.hom = e.hom.left ≫ Y.hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  rw [hw]
  infer_instance

theorem isProper_prod_hom {T : Scheme.{0}} (X Y : Over T) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by
  have h1 : (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Over.w (prod.fst : X ⨯ Y ⟶ X)).symm
  have hfst : IsProper (pullback.fst X.hom Y.hom) := by haveI := hY; infer_instance
  rw [h1]
  infer_instance

theorem isProper_fan_pt {T : Scheme.{0}} : ∀ (n : ℕ) (f : Fin n → Over T),
    (∀ i, IsProper (f i).hom) → ∀ (c : Fan f), IsLimit c → IsProper c.pt.hom := by
  intro n
  induction n with
  | zero =>
      intro f _ c hc
      have h0 : IsLimit (Fan.mk (Over.mk (𝟙 T)) (fun i => i.elim0 : ∀ i, Over.mk (𝟙 T) ⟶ f i)) :=
        Fan.IsLimit.mk _ (fun _ => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
          (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _)
      have hId : IsProper (𝟙 T) := inferInstance
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso h0) hId
  | succ n ih =>
      intro f hf c hc
      let c₁ : Fan (fun i : Fin n => f i.succ) := limit.cone (Discrete.functor fun i : Fin n => f i.succ)
      have h1 : IsProper c₁.pt.hom :=
        ih (fun i => f i.succ) (fun i => hf i.succ) c₁ (limit.isLimit _)
      have hl := extendFanIsLimit f (limit.isLimit (Discrete.functor fun i : Fin n => f i.succ))
        (prodIsProd (f 0) c₁.pt)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso hl) (isProper_prod_hom _ _ (hf 0) h1)

theorem isProper_eighth_fibre_power : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)),
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) →
    IsProper C.hom → IsProper B.hom := by
  intro T B C pr hu hC
  have hl : IsLimit (Fan.mk B pr) :=
    Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose)
      (fun s a => (hu s.pt s.proj).choose_spec.1 a)
      (fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm)
  exact isProper_fan_pt 8 (fun _ => C) (fun _ => hC) _ hl

end GlobalTheory.FibrePowerProper
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.NormalizationOpenImmersion

theorem isOpenImmersion_toNormalization {V P X : Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j) : IsOpenImmersion c.toNormalization := by
  have : IsImmersion (c ≫ p) := h ▸ inferInstance
  have : IsImmersion c := IsImmersion.of_comp c p
  infer_instance

theorem main : ∀ {V P X : AlgebraicGeometry.Scheme.{0}} (c : V ⟶ P) (p : P ⟶ X) [IsSeparated p]
    (j : V ⟶ X) [IsOpenImmersion j] [inst : QuasiCompact c] [inst_1 : QuasiSeparated c]
    (h : c ≫ p = j), IsOpenImmersion c.toNormalization :=
  fun c p _ j _ _ _ h => isOpenImmersion_toNormalization c p j h

end GlobalTheory.NormalizationOpenImmersion
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_of_mono_factor {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A K : C} [GrpObj A] (i : K ⟶ A) [Mono i] (m : K ⊗ K ⟶ K) (hm : m ≫ i = (i ⊗ₘ i) ≫ μ[A])
    (e : 𝟙_ C ⟶ K) (he : e ≫ i = η[A]) (v : K ⟶ K) (hv : v ≫ i = i ≫ ι[A]) :
    ∃ _ : GrpObj K, IsMonHom i := by
  letI M : MonObj K :=
    { one := e, mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : e ▷ K ≫ (i ⊗ₘ i) = 𝟙_ C ◁ i ≫ η[A] ▷ A := by
          rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, he, tensorHom_def']
        rw [reassoc_of% h1, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm]
        have h1 : K ◁ e ≫ (i ⊗ₘ i) = i ▷ 𝟙_ C ≫ A ◁ η[A] := by
          rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, he, MonoidalCategory.tensorHom_def]
        rw [reassoc_of% h1, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        have h1 : m ▷ K ≫ m ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[A] ▷ A ≫ μ[A] := by
          simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        have h2 : K ◁ m ≫ m ≫ i = (i ⊗ₘ (i ⊗ₘ i)) ≫ A ◁ μ[A] ≫ μ[A] := by
          simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, hm, Category.id_comp,
            Category.comp_id]
        simp only [Category.assoc]
        rw [h1, h2, MonObj.mul_assoc (X := A), associator_naturality_assoc] }
  letI G : GrpObj K :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift v (𝟙 K) ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift (i ≫ ι[A]) i = i ≫ lift ι[A] (𝟙 A) := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.left_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)]
      right_inv := by
        rw [← cancel_mono i]
        simp only [Category.assoc]
        change lift (𝟙 K) v ≫ m ≫ i = toUnit K ≫ e ≫ i
        have h3 : lift i (i ≫ ι[A]) = i ≫ lift (𝟙 A) ι[A] := by simp
        rw [hm, he, lift_map_assoc, hv, Category.id_comp, h3, Category.assoc, GrpObj.right_inv,
          ← Category.assoc, toUnit_unique (i ≫ toUnit A) (toUnit K)] }
  exact ⟨G, { one_hom := he, mul_hom := hm }⟩

theorem overScheme_grpObj_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A),
    Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) →
    (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  intro T A K _ i hi ⟨m, hm⟩ ⟨e, he⟩ ⟨v, hv⟩
  exact grpObj_of_mono_factor i m hm e he v hv

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.mul_mem_identityComponent_of_rational : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by
  intro k _ G _ x y hx hy
  set T : G ⟶ G := (toUnit G ≫ x) * 𝟙 G with hT
  have hyT : y ≫ T = x * y := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (y ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
  have hηT : η[G] ≫ T = x := by
    rw [hT, comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id]
    have : (η[G] : 𝟙_ _ ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [this, _root_.mul_one]
  have hsub := T.left.continuous.image_connectedComponent_subset ((η[G]).left (IsLocalRing.closedPoint k))
  have h1 : (x * y).left (IsLocalRing.closedPoint k) = T.left (y.left (IsLocalRing.closedPoint k)) := by
    rw [← hyT, Over.comp_left]
    exact Scheme.Hom.comp_apply y.left T.left _
  have h2 : T.left ((η[G]).left (IsLocalRing.closedPoint k)) = x.left (IsLocalRing.closedPoint k) := by
    rw [← hηT, Over.comp_left]
    exact (Scheme.Hom.comp_apply (η[G]).left T.left _).symm
  rw [h1, connectedComponent_eq hx]
  have := hsub ⟨_, hy, rfl⟩
  rwa [h2] at this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem image_connectedComponent_of_isEmbedding {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : Topology.IsEmbedding q) (a : A) :
    q '' connectedComponent a = connectedComponentIn (Set.range q) (q a) := by
  apply Set.Subset.antisymm
  · exact (isPreconnected_connectedComponent.image q hq.continuous.continuousOn).subset_connectedComponentIn
      ⟨a, mem_connectedComponent, rfl⟩ (Set.image_subset_range _ _)
  · intro x hx
    have hsub : connectedComponentIn (Set.range q) (q a) ⊆ Set.range q := connectedComponentIn_subset _ _
    have himg : q '' (q ⁻¹' connectedComponentIn (Set.range q) (q a)) = connectedComponentIn (Set.range q) (q a) :=
      Set.image_preimage_eq_of_subset hsub
    have hpc : IsPreconnected (q ⁻¹' connectedComponentIn (Set.range q) (q a)) := by
      rw [← hq.isInducing.isPreconnected_image, himg]
      exact isPreconnected_connectedComponentIn
    have hS : q ⁻¹' connectedComponentIn (Set.range q) (q a) ⊆ connectedComponent a :=
      hpc.subset_connectedComponent (mem_connectedComponentIn ⟨a, rfl⟩)
    rw [← himg] at hx
    exact Set.image_mono hS hx

theorem component_in_fibre_iff_of_isPullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s))
      (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s →
      ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  intro X S f e s Y g q y₀ hP h0 y
  haveI : IsPreimmersion q :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hP.flip inferInstance
  have hq : Topology.IsEmbedding q := q.isEmbedding
  have hr : Set.range q = f ⁻¹' {s} := by
    have h1 : Set.range q = Set.range (pullback.fst f (S.fromSpecResidueField s)) := by
      rw [← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr, Set.image_univ]
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hP.isoPullback)).surjective
    rw [h1, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  rw [← h0, ← hr, ← image_connectedComponent_of_isEmbedding hq]
  exact hq.injective.mem_set_image

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue


set_option backward.isDefEq.respectTransparency false in
theorem isLocallyDirected_of_basis : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : B₀, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → ∀ (F : 𝒰 ⥤ Scheme.{0}), (∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)) → ∀ (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U), (∀ U, Function.Injective (e U)) → (∀ U, Function.Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → (F ⋙ Scheme.forget).IsLocallyDirected := by
  intro B₀ 𝒰 hbas F _hF e hinj hsurj hnat
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme),
      F.map f (e U x) = e V (B₀.homOfLE (show U.1 ≤ V.1 from f.le) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
    rfl
  have key : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme), x.1 = y.1 →
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    intro U V x y h
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 x.1 x.2 (h ▸ y.2)
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ ⟨x.1, hxW⟩, ?_, ?_⟩
    · rw [hnat']; congr 1; apply Subtype.ext; simp
    · rw [hnat']; congr 1; apply Subtype.ext; simpa using h
  constructor
  intro U V W f g x y h
  obtain ⟨x, rfl⟩ := hsurj U x
  obtain ⟨y, rfl⟩ := hsurj V y
  have h' : F.map f (e U x) = F.map g (e V y) := h
  rw [hnat', hnat'] at h'
  have h'' := congrArg Subtype.val (hinj _ h')
  exact key x y (by simpa using h'')

end GlobalTheory.ThickGlue
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

lemma resLE_self_preimage_image_eq {Z Z₁ : Scheme.{0}} (e₁ : Z₁ ⟶ Z) (V : Z.Opens)
    (W : V.toScheme.Opens) :
    (e₁ ⁻¹ᵁ V).ι ''ᵁ ((e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl) ⁻¹ᵁ W) = e₁ ⁻¹ᵁ (V.ι ''ᵁ W) := by
  rw [Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr (fun x hx => V.ι_image_le W hx)

lemma resLE_self_app_eq {Z Z₁ : Scheme.{0}} (e₁ : Z₁ ⟶ Z) (V : Z.Opens) (W : V.toScheme.Opens)
    (a b : Γ(V.toScheme, W))
    (h : (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W a = (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W b) :
    e₁.app (V.ι ''ᵁ W) a = e₁.app (V.ι ''ᵁ W) b := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE] at h
  have hS := resLE_self_preimage_image_eq e₁ V W
  have key := Scheme.Hom.appLE_map' (f := e₁) (U := V.ι ''ᵁ W)
    (e := le_refl (e₁ ⁻¹ᵁ (V.ι ''ᵁ W))) (i := hS.symm)
  rw [Scheme.Hom.appLE_eq_app] at key
  rw [← key]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg _ h

theorem cover_and_joint_inj_restrict : ∀ (Z Z₁ Z₂ : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z),
    (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) →
    (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) →
    ∀ V : Z.Opens, (∀ z : V.toScheme, (∃ z₁, e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl z₁ = z) ∨
      ∃ z₂, e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl z₂ = z) ∧
    ∀ (W : V.toScheme.Opens) (a b : Γ(V.toScheme, W)),
      (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W a = (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W b →
      (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W a = (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W b → a = b := by
  intro Z Z₁ Z₂ e₁ e₂ hcov hinj V
  refine ⟨fun z => ?_, fun W a b h₁ h₂ =>
    hinj _ a b (resLE_self_app_eq e₁ V W a b h₁) (resLE_self_app_eq e₂ V W a b h₂)⟩
  rcases hcov z.1 with ⟨z₁, hz⟩ | ⟨z₂, hz⟩
  · refine Or.inl ⟨⟨z₁, show e₁ z₁ ∈ V from hz ▸ z.2⟩, Subtype.ext ?_⟩
    rw [Scheme.Hom.coe_resLE_apply]; exact hz
  · refine Or.inr ⟨⟨z₂, show e₂ z₂ ∈ V from hz ▸ z.2⟩, Subtype.ext ?_⟩
    rw [Scheme.Hom.coe_resLE_apply]; exact hz

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_idempotent_basicOpen_eq_of_isClopen :
    ∀ (X : Scheme.{0}) (U : Set X), IsClopen U →
      ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  intro X U hU
  let O : Bool → X.Opens := fun i => bif i then ⟨U, hU.isOpen⟩ else ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
  have hd : O true ⊓ O false = ⊥ := by
    ext x
    simp [O]
  have hcov : (⊤ : X.Opens) ≤ ⨆ i, O i := fun x _ => by
    by_cases hx : x ∈ U
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, hx⟩
  let sf : ∀ i, Γ(X, O i) := fun i => bif i then 1 else 0
  have sub : ∀ T : X.Opens, T = ⊥ → Subsingleton Γ(X, T) := fun T hT => by
    subst hT; infer_instance
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 O sf := by
    intro i j
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O ⊤ (fun i => homOfLE le_top) hcov sf hcompat
  obtain ⟨t, hs'⟩ : ∃ t : Γ(X, ⊤), ∀ i, X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op t = sf i :=
    ⟨s, hs⟩
  clear hs s
  refine ⟨t, ?_, ?_⟩
  · refine X.sheaf.eq_of_locally_eq' O ⊤ (fun i => homOfLE le_top) hcov (t * t) t fun i => ?_
    have e1 : X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op (t * t) = sf i * sf i := by
      rw [map_mul, hs' i]
    refine e1.trans (Eq.trans ?_ (hs' i).symm)
    cases i
    · exact mul_zero _
    · exact mul_one _
  · have h1 : O true ⊓ X.basicOpen t = O true := by
      rw [← Scheme.basicOpen_res, hs' true]
      exact X.basicOpen_of_isUnit isUnit_one
    have h0 : O false ⊓ X.basicOpen t = ⊥ := by
      rw [← Scheme.basicOpen_res, hs' false]
      exact X.basicOpen_zero _
    ext x
    constructor
    · intro hx
      by_contra hxU
      have : x ∈ O false ⊓ X.basicOpen t := ⟨hxU, hx⟩
      rw [h0] at this
      exact this
    · intro hx
      have : x ∈ O true := hx
      rw [← h1] at this
      exact this.2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem idem_germ_eq_of_isUnit_iff {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : a * a = a) (hb : b * b = b) (h : IsUnit a ↔ IsUnit b) : a = b := by
  have key : ∀ c : R, c * c = c → (IsUnit c → c = 1) ∧ (¬ IsUnit c → c = 0) := by
    intro c hc
    refine ⟨fun hu => ?_, fun hn => ?_⟩
    · obtain ⟨u, rfl⟩ := hu
      have : (u : R) * u = u * 1 := by rw [mul_one]; exact hc
      exact (Units.mul_right_inj u).mp this
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h1 | h1
      · exact absurd h1 hn
      · have : (1 - c) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
        obtain ⟨u, hu⟩ := h1
        rw [← hu] at this
        simpa using this
  by_cases hau : IsUnit a
  · rw [(key a ha).1 hau, (key b hb).1 (h.mp hau)]
  · rw [(key a ha).2 hau, (key b hb).2 (fun hbu => hau (h.mpr hbu))]

theorem idempotent_eq_of_basicOpen_eq : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' →
    X.basicOpen e = X.basicOpen e' → e = e' := by
  intro X e e' he he' hb
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' (fun x hx => ?_)
  change X.presheaf.germ ⊤ x hx e = X.presheaf.germ ⊤ x hx e'
  apply idem_germ_eq_of_isUnit_iff (R := X.presheaf.stalk x)
  · rw [← map_mul, he]
  · rw [← map_mul, he']
  · rw [← X.mem_basicOpen e x hx, ← X.mem_basicOpen e' x hx, hb]

end GlobalTheory
end
