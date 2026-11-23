module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem clopen_forall {S : Scheme.{0}} (X F : Over S) [IsFinite F.hom] [Etale F.hom]
    (W : (X ⊗ F).left.Opens) (hW : IsClosed (W : Set (X ⊗ F).left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T) (a : T' ⟶ F),
      Set.range (lift (t ≫ h) a).left ⊆ W) := by
  have hWo : IsOpen ((W : Set (X ⊗ F).left)ᶜ) := hW.isOpen_compl
  have hWc : IsClosed ((W : Set (X ⊗ F).left)ᶜ) := W.isOpen.isClosed_compl
  have hKc : IsClosed (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isClosedMap _ hWc
  have hKo : IsOpen (pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ) :=
    (pullback.fst X.hom F.hom).isOpenMap _ hWo
  refine ⟨⟨(pullback.fst X.hom F.hom '' (W : Set (X ⊗ F).left)ᶜ)ᶜ, hKc.isOpen_compl⟩,
    hKo.isClosed_compl, ?_⟩
  intro T h
  constructor
  · intro H
    rintro _ ⟨x, rfl⟩ ⟨z, hz, hzx⟩
    obtain ⟨q, hq1, hq2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := h.left) (g := pullback.fst X.hom F.hom) x z hzx.symm
    let T' : Over S := Over.mk (pullback.fst h.left (pullback.fst X.hom F.hom) ≫ T.hom)
    let t : T' ⟶ T := Over.homMk (pullback.fst h.left (pullback.fst X.hom F.hom)) rfl
    have ha : (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ≫ F.hom
        = T'.hom := by
      simp only [T', Over.mk_hom, Category.assoc]
      rw [← pullback.condition (f := X.hom) (g := F.hom), ← Category.assoc,
        ← pullback.condition (f := h.left) (g := pullback.fst X.hom F.hom), Category.assoc, Over.w h]
    let a : T' ⟶ F :=
      Over.homMk (pullback.snd h.left (pullback.fst X.hom F.hom) ≫ pullback.snd X.hom F.hom) ha
    have hl : (lift (t ≫ h) a).left = pullback.snd h.left (pullback.fst X.hom F.hom) := by
      apply pullback.hom_ext
      · change (lift (t ≫ h) a ≫ fst X F).left = _
        rw [lift_fst]
        exact pullback.condition
      · change (lift (t ≫ h) a ≫ snd X F).left = _
        rw [lift_snd]
        rfl
    apply hz
    have hmem := H T' t a ⟨q, rfl⟩
    rw [hl, hq2] at hmem
    exact hmem
  · intro H T' t a
    rintro _ ⟨y, rfl⟩
    by_contra hy
    have e : (lift (t ≫ h) a).left ≫ pullback.fst X.hom F.hom = t.left ≫ h.left := by
      change (lift (t ≫ h) a ≫ fst X F).left = _
      rw [lift_fst]
      rfl
    apply H ⟨t.left y, rfl⟩
    refine ⟨(lift (t ≫ h) a).left y, hy, ?_⟩
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]

private theorem clopen_pre {S : Scheme.{0}} {X Y : Over S} (e : X ⟶ Y) (U : Y.left.Opens)
    (hU : IsClosed (U : Set Y.left)) :
    GlobalTheory.LevCover.ClopenCond X (fun T h => Set.range (h ≫ e).left ⊆ U) := by
  refine ⟨e.left ⁻¹ᵁ U, hU.preimage e.left.continuous, ?_⟩
  intro T h
  simp only [Over.comp_left, Set.range_subset_iff, Scheme.Hom.comp_apply, Scheme.Hom.mem_preimage, SetLike.mem_coe]

theorem UpperTheory.clopenCond_of_isClosed_subgroupLocus :
    ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [IsFinite G.hom] [Etale G.hom] (U : (X ⊗ G).left.Opens), IsClosed (U : Set (X ⊗ G).left) → GlobalTheory.LevCover.ClopenCond X (fun T h => ∀ (T' : Over S) (t : T' ⟶ T), Set.range (lift (t ≫ h) (1 : T' ⟶ G)).left ⊆ U ∧ ∀ a b : T' ⟶ G, Set.range (lift (t ≫ h) a).left ⊆ U → Set.range (lift (t ≫ h) b).left ⊆ U → Set.range (lift (t ≫ h) (a * b⁻¹)).left ⊆ U) := by
  intro S G X _ _ _ U hU
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).1
  haveI := (GlobalTheory.LevCover.finiteEtale_tensor G G).2
  have hUo : IsOpen (U : Set (X ⊗ G).left) := U.isOpen
  let m1 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ fst G G)
  let m2 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ snd G G)
  let m3 : X ⊗ (G ⊗ G) ⟶ X ⊗ G := lift (fst _ _) (snd _ _ ≫ (fst G G * (snd G G)⁻¹))
  let Ws : Set (X ⊗ (G ⊗ G)).left :=
    (m1.left ⁻¹' U ∩ m2.left ⁻¹' U)ᶜ ∪ m3.left ⁻¹' U
  have hWo : IsOpen Ws :=
    ((hU.preimage m1.left.continuous).inter (hU.preimage m2.left.continuous)).isOpen_compl.union
      (hUo.preimage m3.left.continuous)
  have hWc : IsClosed Ws :=
    ((hUo.preimage m1.left.continuous).inter (hUo.preimage m2.left.continuous)).isClosed_compl.union
      (hU.preimage m3.left.continuous)
  have h1 := clopen_pre (lift (𝟙 X) (1 : X ⟶ G)) U hU
  have h2 := clopen_forall X (G ⊗ G) ⟨Ws, hWo⟩ hWc
  refine (h1.and h2).congr ?_
  intro T h
  have k0 : ∀ (T' : Over S) (t : T' ⟶ T),
      lift (t ≫ h) (1 : T' ⟶ G) = t ≫ h ≫ lift (𝟙 X) (1 : X ⟶ G) := by
    intro T' t
    simp [comp_lift]
  have k1 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m1 = lift u (c ≫ fst G G) := by
    intro T' u c
    simp [m1, comp_lift]
  have k2 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m2 = lift u (c ≫ snd G G) := by
    intro T' u c
    simp [m2, comp_lift]
  have k3 : ∀ (T' : Over S) (u : T' ⟶ X) (c : T' ⟶ G ⊗ G),
      lift u c ≫ m3 = lift u ((c ≫ fst G G) * (c ≫ snd G G)⁻¹) := by
    intro T' u c
    simp [m3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv]
  have pt : ∀ {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (y : A.left),
      (f ≫ g).left y = g.left (f.left y) := by
    intro A B C f g y
    rw [Over.comp_left, Scheme.Hom.comp_apply]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have := (H T (𝟙 T)).1
      rw [k0, Category.id_comp] at this
      exact this
    · intro T' t c
      rintro _ ⟨y, rfl⟩
      change (lift (t ≫ h) c).left y ∈ Ws
      by_cases hy : (lift (t ≫ h) c).left y ∈ m1.left ⁻¹' U ∩ m2.left ⁻¹' U
      · right
        let V : T'.left.Opens :=
          (lift (t ≫ h) c ≫ m1).left ⁻¹ᵁ U ⊓ (lift (t ≫ h) c ≫ m2).left ⁻¹ᵁ U
        have hyV : y ∈ V := by
          refine ⟨?_, ?_⟩
          · change (lift (t ≫ h) c ≫ m1).left y ∈ (U : Set _)
            rw [pt]
            exact hy.1
          · change (lift (t ≫ h) c ≫ m2).left y ∈ (U : Set _)
            rw [pt]
            exact hy.2
        have hVw : ∀ w, V.ι w ∈ V := by
          intro w
          have hw : V.ι w ∈ Set.range V.ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw
        let T'' : Over S := Over.mk (V.ι ≫ T'.hom)
        let j : T'' ⟶ T' := Over.homMk V.ι rfl
        have eq1 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ fst G G) = j ≫ (lift (t ≫ h) c ≫ m1) := by
          rw [k1, comp_lift, Category.assoc]
        have eq2 : lift ((j ≫ t) ≫ h) (j ≫ c ≫ snd G G) = j ≫ (lift (t ≫ h) c ≫ m2) := by
          rw [k2, comp_lift, Category.assoc]
        have eq3 : lift ((j ≫ t) ≫ h) ((j ≫ c ≫ fst G G) * (j ≫ c ≫ snd G G)⁻¹)
            = j ≫ (lift (t ≫ h) c ≫ m3) := by
          rw [k3, comp_lift, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
        have hA := (H T'' (j ≫ t)).2 (j ≫ c ≫ fst G G) (j ≫ c ≫ snd G G)
          (by
            rw [eq1]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).1)
          (by
            rw [eq2]
            rintro _ ⟨w, rfl⟩
            rw [pt]
            exact (hVw w).2)
        obtain ⟨y', hy'⟩ : y ∈ Set.range V.ι := by
          rw [Scheme.Opens.range_ι]
          exact hyV
        have := hA ⟨y', rfl⟩
        rw [eq3, pt] at this
        change m3.left ((lift (t ≫ h) c).left y) ∈ (U : Set _)
        rw [← pt, ← hy']
        exact this
      · left
        exact hy
  · rintro ⟨H1, H2⟩ T' t
    refine ⟨?_, ?_⟩
    · rw [k0]
      rintro _ ⟨y, rfl⟩
      rw [pt]
      exact H1 ⟨t.left y, rfl⟩
    · intro a b ha hb
      rintro _ ⟨y, rfl⟩
      have hz : (lift (t ≫ h) (lift a b)).left y ∈ Ws := H2 T' t (lift a b) ⟨y, rfl⟩
      have e3 := k3 T' (t ≫ h) (lift a b)
      rw [lift_fst, lift_snd] at e3
      rw [← e3, pt]
      rcases hz with hz | hz
      · exfalso
        apply hz
        refine ⟨?_, ?_⟩
        · change (m1.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k1, lift_fst]
          exact ha ⟨y, rfl⟩
        · change (m2.left ((lift (t ≫ h) (lift a b)).left y)) ∈ (U : Set _)
          rw [← pt, k2, lift_snd]
          exact hb ⟨y, rfl⟩
      · exact hz
end

section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

section
variable {k L A : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]

private lemma map_val_injective (R : Subalgebra k L) :
    Function.Injective
      (Algebra.TensorProduct.map R.val (AlgHom.id k A) : R ⊗[k] A →ₐ[k] L ⊗[k] A) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := A)
    (R.val.toLinearMap) Subtype.val_injective
  have e : ∀ z : R ⊗[k] A, LinearMap.rTensor A R.val.toLinearMap z =
      Algebra.TensorProduct.map R.val (AlgHom.id k A) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  intro x y hxy
  apply h
  rw [e, e, hxy]

private lemma spz_add {R : Subalgebra k L} {φ : R →ₐ[k] k} {y y' : L ⊗[k] A} {a a' : A}
    (h : Spz R φ y a) (h' : Spz R φ y' a') : Spz R φ (y + y') (a + a') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨v, hv, rfl⟩ := h'
  exact ⟨u + v, by rw [map_add (f := _), hu, hv], by simp only [map_add (f := _)]⟩

private lemma spz_tmul (R : Subalgebra k L) (φ : R →ₐ[k] k) (r : R) (a : A) :
    Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a) :=
  ⟨r ⊗ₜ[k] a, by simp, by simp⟩

private noncomputable def contr (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] :
    B ⊗[k] A →ₗ[k] B :=
  (TensorProduct.rid k B).toLinearMap ∘ₗ LinearMap.lTensor B l

private lemma contr_tmul (l : A →ₗ[k] k) (B : Type) [CommRing B] [Algebra k B] (b : B) (a : A) :
    contr l B (b ⊗ₜ[k] a) = l a • b := by
  simp [contr]

private lemma exists_contr_ne_zero {y : L ⊗[k] A} (hy : y ≠ 0) :
    ∃ l : A →ₗ[k] k, contr l L y ≠ 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k A
  let E := TensorProduct.equivFinsuppOfBasisRight (R := k) (M := L) (N := A) b
  have hE : E y ≠ 0 := fun h => hy (E.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hE
  refine ⟨b.coord i, ?_⟩
  have key : ∀ z : L ⊗[k] A, contr (b.coord i) L z = E z i := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [contr_tmul, E, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, Finsupp.add_apply]
  rw [key]
  simpa using hi
end

theorem UpperTheory.specialization_tensor_ring_hom_properties :
    ∀ (k L A : Type) [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A], (∀ (R : Subalgebra k L) (φ : R →ₐ[k] k), (∀ (y : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y a' → a = a') ∧ (∀ (y y' : L ⊗[k] A) (a a' : A), Spz R φ y a → Spz R φ y' a' → Spz R φ (y + y') (a + a') ∧ Spz R φ (y * y') (a * a') ∧ Spz R φ (y - y') (a - a')) ∧ (∀ (r : R) (a : A), Spz R φ ((r : L) ⊗ₜ[k] a) (φ r • a)) ∧ ∀ (A' : Type) [CommRing A'] [Algebra k A'] (g : A →ₐ[k] A') (y : L ⊗[k] A) (a : A), Spz R φ y a → Spz R φ (Algebra.TensorProduct.map (AlgHom.id k L) g y) (g a)) ∧ (∀ y : L ⊗[k] A, ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ φ : R →ₐ[k] k, ∃ a, Spz R φ y a) ∧ ∀ y : L ⊗[k] A, y ≠ 0 → ∃ s : Finset L, ∀ R : Subalgebra k L, (s : Set L) ⊆ R → ∀ (φ : R →ₐ[k] k) (a : A), Spz R φ y a → a ≠ 0 := by
  intro k L A _ _ _ _ _
  refine ⟨fun R φ => ⟨?_, ?_, spz_tmul R φ, ?_⟩, ?_, ?_⟩
  · rintro y a a' ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [map_val_injective R (hu.trans hv.symm)]
  · intro y y' a a' h h'
    refine ⟨spz_add h h', ?_, ?_⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u * v, by rw [map_mul, hu, hv], by simp only [map_mul]⟩
    · obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨v, hv, rfl⟩ := h'
      exact ⟨u - v, by rw [map_sub, hu, hv], by simp only [map_sub]⟩
  · rintro A' _ _ g y a ⟨u, rfl, rfl⟩
    refine ⟨Algebra.TensorProduct.map (AlgHom.id k R) g u, ?_, ?_⟩
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    · induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact ⟨∅, fun R _ φ => ⟨0, 0, by simp, by simp⟩⟩
    | tmul l b =>
      classical
      refine ⟨{l}, fun R hs φ => ?_⟩
      have hl : l ∈ R := hs (by simp)
      exact ⟨_, spz_tmul R φ ⟨l, hl⟩ b⟩
    | add x y hx hy =>
      classical
      obtain ⟨s, hs⟩ := hx
      obtain ⟨t, ht⟩ := hy
      refine ⟨s ∪ t, fun R hst φ => ?_⟩
      obtain ⟨a, ha⟩ := hs R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      obtain ⟨b, hb⟩ := ht R (fun z hz => hst (by simp [Finset.mem_coe.mp hz])) φ
      exact ⟨a + b, spz_add ha hb⟩
  · intro y hy
    classical
    obtain ⟨l, hl⟩ := exists_contr_ne_zero hy
    set c := contr l L y with hc
    refine ⟨{c, c⁻¹}, fun R hs φ a ha h0 => ?_⟩
    have hcR : c ∈ R := hs (by simp)
    have hcR' : c⁻¹ ∈ R := hs (by simp)
    obtain ⟨u, hu, hua⟩ := ha
    have e1 : ∀ z : R ⊗[k] A, ((contr l R z : R) : L) =
        contr l L (Algebra.TensorProduct.map R.val (AlgHom.id k A) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul]
      | add x y hx hy => simp only [map_add (f := _), hx, hy, Subalgebra.coe_add]
    have e2 : ∀ z : R ⊗[k] A, φ (contr l R z) =
        l (Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map φ (AlgHom.id k A) z)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => simp [contr_tmul, mul_comm]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    have h1 : contr l R u = ⟨c, hcR⟩ := Subtype.ext (by rw [e1, hu])
    have h2 : φ ⟨c, hcR⟩ = 0 := by rw [← h1, e2, hua, h0, map_zero]
    have h3 : (⟨c, hcR⟩ : R) * ⟨c⁻¹, hcR'⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hl)
    have h4 := congrArg φ h3
    rw [map_mul, h2, zero_mul, map_one] at h4
    exact zero_ne_one h4
end

section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma mem_range_of_fixed {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (q : ℕ) (hq : (q : K) ≠ 0) (σ₀ : K' →ₐ[K] AlgebraicClosure K) (c : K') (d : K) (hd : d ≠ 0)
    (hc : c ^ q = algebraMap K K' d)
    (hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c) : c ∈ (algebraMap K K').range := by
  have hsep : (minpoly K c).Separable := by
    refine (Polynomial.separable_X_pow_sub_C d hq hd).of_dvd (minpoly.dvd K c ?_)
    simp [hc]
  have hsplit : ((minpoly K c).map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hroot : (minpoly K c).rootSet (AlgebraicClosure K) = {σ₀ c} := by
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact hfix σ
    · rintro rfl
      exact ⟨σ₀, rfl⟩
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep hsplit
  rw [← minpoly.natDegree_eq_one_iff, ← hcard, Fintype.card_eq_one_iff]
  refine ⟨⟨σ₀ c, by rw [hroot]; rfl⟩, fun y => Subtype.ext ?_⟩
  have hy : (y : AlgebraicClosure K) ∈ ({σ₀ c} : Set (AlgebraicClosure K)) := hroot ▸ y.2
  exact hy

theorem UpperTheory.finite_kernel_powClasses_of_primitive_root :
    ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] (q : ℕ) [NeZero q], (∃ ζ : K, IsPrimitiveRoot ζ q) → FinCls q {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
  intro K K' _ _ _ _ q _ ⟨ζ, hζ⟩
  classical
  haveI := hζ.neZero'
  have hq : ((q : ℕ) : K) ≠ 0 := NeZero.ne _
  have hq0 : q ≠ 0 := NeZero.ne q
  let σ₀ : K' →ₐ[K] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let S : Set Kˣ := {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q}
  let bb : Kˣ → K' := fun a => if h : ∃ b : K', algebraMap K K' (a : K) = b ^ q then h.choose else 1
  have hbb : ∀ a ∈ S, algebraMap K K' (a : K) = bb a ^ q := by
    intro a ha
    have ha' : ∃ b : K', algebraMap K K' (a : K) = b ^ q := ha
    simp only [bb, dif_pos ha']
    exact ha'.choose_spec
  have hbb0 : ∀ a ∈ S, bb a ≠ 0 := by
    intro a ha h0
    have h := hbb a ha
    rw [h0, zero_pow hq0] at h
    exact a.ne_zero ((algebraMap K K').injective (by rw [h, map_zero]))
  let sig : Kˣ → (K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun a σ => σ (bb a) / σ₀ (bb a)
  have hsig : ∀ a ∈ S, ∀ σ, sig a σ ∈ Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) := by
    intro a ha σ
    rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hq0)]
    have h1 : σ (bb a) ^ q = σ₀ (bb a) ^ q := by
      rw [← map_pow, ← map_pow, ← hbb a ha, AlgHom.commutes, AlgHom.commutes]
    have h2 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr (hbb0 a ha)
    simp only [sig, div_pow, h1, div_self (pow_ne_zero _ h2)]
  have hfin : (sig '' S).Finite := by
    refine (Set.Finite.pi (t := fun _ => (Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) : Set _))
      (fun _ => Finset.finite_toSet _)).subset ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Set.mem_univ_pi.mpr (fun σ => hsig a ha σ)
  let rep : ((K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K) → Kˣ :=
    fun f => if h : ∃ a ∈ S, sig a = f then h.choose else 1
  refine ⟨hfin.toFinset.image rep, ?_⟩
  intro a ha
  have hex : ∃ a' ∈ S, sig a' = sig a := ⟨a, ha, rfl⟩
  have htS : rep (sig a) ∈ S ∧ sig (rep (sig a)) = sig a := by
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  refine ⟨rep (sig a), Finset.mem_image.mpr ⟨sig a, hfin.mem_toFinset.mpr ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  set t := rep (sig a) with ht
  have hat := hbb0 a ha
  have htt := hbb0 t htS.1
  let c : K' := bb a / bb t
  have hc : c ^ q = algebraMap K K' ((a : K) / (t : K)) := by
    rw [map_div₀, hbb a ha, hbb t htS.1, div_pow]
  have hd : (a : K) / (t : K) ≠ 0 := div_ne_zero a.ne_zero t.ne_zero
  have hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c := by
    intro σ
    have e := congrFun htS.2 σ
    simp only [sig] at e
    have h1 : σ (bb t) ≠ 0 := (map_ne_zero σ).mpr htt
    have h2 : σ₀ (bb t) ≠ 0 := (map_ne_zero σ₀).mpr htt
    have h3 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr hat
    simp only [c, map_div₀]
    rw [div_eq_div_iff h1 h2]
    rw [div_eq_div_iff h2 h3] at e
    linear_combination -e
  obtain ⟨e, he⟩ := mem_range_of_fixed q hq σ₀ c _ hd hc hfix
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero] at he
    exact div_ne_zero hat htt he.symm
  refine ⟨Units.mk0 e he0, ?_⟩
  ext
  apply (algebraMap K K').injective
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, he, hc, map_div₀]
  have : algebraMap K K' (t : K) ≠ 0 := (map_ne_zero _).mpr t.ne_zero
  field_simp
end
