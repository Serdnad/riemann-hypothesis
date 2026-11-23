module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem isAffineOpen_preimage_and_tensor_equiv_of_isPullback : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  intro k K _ _ _ X X' f f' π h V hV
  letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  refine ⟨hV.preimage π, ?_⟩
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := V) (UY := π ⁻¹ᵁ V) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  have hpo' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top)
      (CommRingCat.ofHom (algebraMap k K)) (π.app V)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  letI : Algebra K Γ(X', π ⁻¹ᵁ V) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(X', π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  letI : Algebra k Γ(X', π ⁻¹ᵁ V) :=
    ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom).comp
      (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k Γ(X, V) Γ(X', π ⁻¹ᵁ V) := .of_algebraMap_eq fun r => by
    exact (congrArg (fun φ => φ.hom r) hpo'.w).symm
  haveI : Algebra.IsPushout k K Γ(X, V) Γ(X', π ⁻¹ᵁ V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo'.flip
  refine ⟨(Algebra.IsPushout.equiv k K Γ(X, V) Γ(X', π ⁻¹ᵁ V)).toRingEquiv, fun a => ?_, fun c => ?_⟩
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]
  · simp [Algebra.IsPushout.equiv_tmul, RingHom.algebraMap_toAlgebra]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GlueClosed

theorem exists_lift_eq {X : Scheme.{0}} (U V : X.Opens) (x : (pullback U.ι V.ι).carrier) :
    ∃ y : (U ⊓ V).toScheme, pullback.lift (X.homOfLE (inf_le_left : U ⊓ V ≤ U))
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) (by simp) y = x := by
  have hx : U.ι (pullback.fst U.ι V.ι x) ∈ U ⊓ V := by
    refine ⟨(pullback.fst U.ι V.ι x).2, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact (pullback.snd U.ι V.ι x).2
  obtain ⟨y, hy⟩ : ∃ y : (U ⊓ V).toScheme, (U ⊓ V).ι y = U.ι (pullback.fst U.ι V.ι x) :=
    ⟨⟨_, hx⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply (pullback.fst U.ι V.ι ≫ U.ι).isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply _ (pullback.fst U.ι V.ι ≫ U.ι), pullback.lift_fst_assoc,
    Scheme.homOfLE_ι, hy]
  rfl

section
variable {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)

noncomputable def coverOfSet : X.OpenCover where
  I₀ := S
  X U := U.1.toScheme
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun U ↦ inferInstanceAs (IsOpenImmersion U.1.ι)⟩
    obtain ⟨U, hU, hx⟩ := hcov x
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

instance : Preorder (coverOfSet S hcov).I₀ := inferInstanceAs (Preorder S)

@[reducible] noncomputable def locallyDirected (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) :
    (coverOfSet S hcov).LocallyDirected where
  trans {U V} h := X.homOfLE (show U.1 ≤ V.1 from h.le)
  trans_id U := X.homOfLE_rfl _
  trans_comp h k := (X.homOfLE_homOfLE _ _).symm
  w h := X.homOfLE_ι _
  directed {U V} x := by
    obtain ⟨y, hy⟩ := exists_lift_eq U.1 V.1 x
    exact ⟨⟨U.1 ⊓ V.1, hinf _ U.2 _ V.2⟩, homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1),
      homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1), y, hy⟩
  property_trans h := inferInstanceAs (IsOpenImmersion (X.homOfLE _))

end

theorem exists_glue {X : Scheme.{0}} (S : Set X.Opens) (hcov : ∀ x : X, ∃ U ∈ S, x ∈ U)
    (hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S) (C : S → Scheme.{0}) (c : ∀ U, C U ⟶ U.1.toScheme)
    [∀ U, Mono (c U)]
    (H : ∀ (U V : S) (h : U.1 ≤ V.1) (Y : Scheme.{0}) (g : Y ⟶ U.1.toScheme),
      (∃ z : Y ⟶ C U, z ≫ c U = g) ↔ ∃ z : Y ⟶ C V, z ≫ c V = g ≫ X.homOfLE h) :
    ∃ (B : Scheme.{0}) (b : B ⟶ X) (e : ∀ U, C U ⟶ B), ∀ U, IsPullback (c U) (e U) U.1.ι b := by
  choose t ht using fun (U V : S) (h : U.1 ≤ V.1) ↦ (H U V h _ (c U)).1 ⟨𝟙 _, Category.id_comp _⟩
  have hid : ∀ U : S, t U U le_rfl = 𝟙 _ := fun U ↦ by
    rw [← cancel_mono (c U), ht, X.homOfLE_rfl]; simp
  have hcomp : ∀ (U V W : S) (h : U.1 ≤ V.1) (k : V.1 ≤ W.1),
      t U W (h.trans k) = t U V h ≫ t V W k := fun U V W h k ↦ by
    rw [← cancel_mono (c W), ht, Category.assoc, ht, ← Category.assoc, ht, Category.assoc,
      X.homOfLE_homOfLE]
  have hpb : ∀ (U V : S) (h : U.1 ≤ V.1),
      IsPullback (t U V h) (c U) (c V) (X.homOfLE h) := fun U V h ↦ by
    refine ⟨⟨ht _ _ _⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
    · intro s
      rw [← cancel_mono (c V), Category.assoc, ht, ← Category.assoc,
        ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec, s.condition]
    · intro s
      exact ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec
    · intro s m _ h2
      rw [← cancel_mono (c U), h2, ((H U V h _ s.snd).2 ⟨s.fst, s.condition⟩).choose_spec]
  letI := locallyDirected S hcov hinf
  let d : (coverOfSet S hcov).RelativeGluingData :=
    { functor :=
        { obj := C
          map := fun {U V} h ↦ t U V h.le
          map_id := hid
          map_comp := fun {U V W} h k ↦ hcomp U V W h.le k.le }
      natTrans := { app := c, naturality := fun U V h ↦ ht U V h.le }
      equifibered := fun {U V} h ↦ hpb U V h.le }
  exact ⟨d.glued, d.toBase, d.cover.f, d.isPullback_natTrans_ι_toBase⟩

theorem exists_glue_isClosedImmersion : ∀ (X : Scheme.{0}) (ι : Type) (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X), (∀ i, IsOpenImmersion (m i)) → (∀ x : X, ∃ i, x ∈ Set.range (m i)) → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i j : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (g' : Y ⟶ Xi j), g ≫ m i = g' ≫ m j → ((∃ z : Y ⟶ A i, z ≫ a i = g) ↔ (∃ z : Y ⟶ A j, z ≫ a j = g'))) → ∃ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), ((∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) := by
  intro X ι Xi m hm hcov A a ha hcomp
  let S : Set X.Opens := {U | ∃ i, U ≤ (m i).opensRange}
  have hS : ∀ x : X, ∃ U ∈ S, x ∈ U := fun x ↦ by
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨(m i).opensRange, ⟨i, le_rfl⟩, hi⟩
  have hinf : ∀ U ∈ S, ∀ V ∈ S, U ⊓ V ∈ S := fun U ⟨i, hi⟩ V _ ↦ ⟨i, inf_le_left.trans hi⟩
  have hl : ∀ (U : X.Opens) (i : ι), U ≤ (m i).opensRange →
      ∃ l : U.toScheme ⟶ Xi i, l ≫ m i = U.ι := fun U i h ↦
    ⟨IsOpenImmersion.lift (m i) U.ι (by rw [Scheme.Opens.range_ι]; exact h),
      IsOpenImmersion.lift_fac _ _ _⟩
  choose l hl using hl
  have hC : ∀ U : S, ∃ (C : Scheme.{0}) (c : C ⟶ U.1.toScheme), IsClosedImmersion c ∧
      ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (h : Y ⟶ U.1.toScheme), h ≫ U.1.ι = g ≫ m i →
        ((∃ z : Y ⟶ C, z ≫ c = h) ↔ ∃ z : Y ⟶ A i, z ≫ a i = g) := by
    rintro ⟨U, j, hj⟩
    refine ⟨pullback (a j) (l U j hj), pullback.snd _ _, inferInstance, fun i Y g h hg ↦ ?_⟩
    rw [← hcomp j i Y (h ≫ l U j hj) g (by rw [Category.assoc, hl, hg])]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z ≫ pullback.fst _ _, by simp [pullback.condition]⟩
    · rintro ⟨z, hz⟩
      exact ⟨pullback.lift z h hz, pullback.lift_snd _ _ _⟩
  choose C c hc hCa using hC
  obtain ⟨B, b, e, he⟩ := exists_glue S hS hinf C c (by
    intro U V h Y g
    obtain ⟨i, hi⟩ := V.2
    rw [hCa U i Y (g ≫ l U.1 i (h.trans hi)) g (by rw [Category.assoc, hl]),
      hCa V i Y (g ≫ l U.1 i (h.trans hi)) (g ≫ X.homOfLE h)
        (by rw [Category.assoc, Category.assoc, hl, X.homOfLE_ι])])
  refine ⟨B, b, ?_, fun i Y g ↦ ?_⟩
  · apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (coverOfSet S hS)
    intro U
    have := hc U
    change IsClosedImmersion (pullback.snd b U.1.ι)
    rw [← (he U).flip.isoPullback_inv_snd]
    infer_instance
  · let U : S := ⟨(m i).opensRange, i, le_rfl⟩
    have hh : (g ≫ (m i).isoOpensRange.hom) ≫ U.1.ι = g ≫ m i := by simp [U]
    rw [← hCa U i Y g _ hh]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(he U).lift _ z (hh.trans hz.symm), (he U).lift_fst _ _ _⟩
    · rintro ⟨z, hz⟩
      exact ⟨z ≫ e U, by rw [Category.assoc, ← (he U).w, ← Category.assoc, hz, hh]⟩

end GlobalTheory.GlueClosed
end

section

open IsDedekindDomain WeierstrassCurve

namespace GlobalTheory

theorem isMinimal_of_forall_div_pow_twelve (R F : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F]
    (W : WeierstrassCurve F) (hI : W.IsIntegral R)
    (h : ∀ x : R, x ≠ 0 → W.Δ / algebraMap R F x ^ 12 ∈ (algebraMap R F).range → IsUnit x) :
    W.IsMinimal R := by
  refine ⟨⟨by simpa using hI, fun C hC _ => ?_⟩⟩
  simp only [one_smul]
  have hC' : (C • W).IsIntegral R := hC
  rw [← Subtype.coe_le_coe]
  rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral]
  set v := HeightOneSpectrum.valuation F (IsDiscreteValuationRing.maximalIdeal R) with hv
  have hle : ∀ r : R, v (algebraMap R F r) ≤ 1 := fun r =>
    HeightOneSpectrum.valuation_le_one (K := F) (IsDiscreteValuationRing.maximalIdeal R) r
  rw [variableChange_Δ, map_mul, map_pow]
  refine mul_le_of_le_one_left' (pow_le_one' ?_ _)
  rcases ValuationRing.isInteger_or_isInteger R (C.u : F) with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact C.u.ne_zero (by simpa using hx.symm)
    obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral R (C • W)
    have hu : IsUnit x := h x hx0 ⟨r, by
      rw [hr, variableChange_Δ, hx, Units.val_inv_eq_inv_val, inv_pow, div_eq_inv_mul]⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have : ((C.u⁻¹ : Fˣ) : F) = algebraMap R F y := by
      rw [Units.val_inv_eq_inv_val, ← hx]
      exact (eq_inv_of_mul_eq_one_right (by rw [← map_mul, hy, map_one])).symm
    rw [this]
    exact hle y
  · rw [Units.val_inv_eq_inv_val, ← hx]
    exact hle x

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibreStalk

theorem fromSpecResidueField_eq {B : Scheme.{0}} {x b : B} (h : x = b) :
    B.fromSpecResidueField b =
      Spec.map (B.residue x ≫ (B.residueFieldCongr h).hom) ≫ B.fromSpecStalk x := by
  rw [← B.residueFieldCongr_fromSpecResidueField h, Spec.map_comp, Category.assoc]
  rfl

theorem image_eq (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) : π (π.fiberι b z) = b := by
  have := (π.range_fiberι b).le ⟨z, rfl⟩
  simpa using this

theorem ker_stalkMap_fiberι (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    RingHom.ker ((π.fiberι b).stalkMap z).hom =
      (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
        (π.stalkMap (π.fiberι b z)).hom := by
  have h' := image_eq B Y π b z
  have hA := fromSpecResidueField_eq h'
  apply le_antisymm
  · intro a ha
    let y := π.fiberι b z
    let S := Y.presheaf.stalk y
    let I := (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y))).map (π.stalkMap y).hom
    have hIm : I ≤ IsLocalRing.maximalIdeal S :=
      Ideal.map_le_iff_le_comap.2 fun r hr => map_nonunit (π.stalkMap y).hom r hr
    have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.2
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hIm)
    have : IsLocalRing (S ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hl : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let L : B.residueField (π y) ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom
      (Ideal.Quotient.lift (IsLocalRing.maximalIdeal (B.presheaf.stalk (π y)))
        ((Ideal.Quotient.mk I).comp (π.stalkMap y).hom)
        (fun r hr => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)))
    have hres : B.residue (π y) ≫ L = π.stalkMap y ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      ext r; rfl
    let g : Spec (CommRingCat.of (S ⧸ I)) ⟶ Y := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Y.fromSpecStalk y
    let t : Spec (CommRingCat.of (S ⧸ I)) ⟶ Spec (B.residueField b) := Spec.map ((B.residueFieldCongr h').inv ≫ L)
    have w : g ≫ π = t ≫ B.fromSpecResidueField b := by
      rw [hA, ← Category.assoc, ← Spec.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, g]
      rw [hres]
      first
        | (rw [Spec.map_comp (π.stalkMap y) (CommRingCat.ofHom (Ideal.Quotient.mk I)), Category.assoc,
            Scheme.SpecMap_stalkMap_fromSpecStalk])
        | (erw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk])
      all_goals rfl
    let ℓ : Spec (CommRingCat.of (S ⧸ I)) ⟶ π.fiber b := Limits.pullback.lift g t w
    have hℓ : ℓ ≫ π.fiberι b = g := Limits.pullback.lift_fst _ _ _
    have e : ℓ (IsLocalRing.closedPoint _) = z := by
      apply (π.fiberι b).isEmbedding.injective
      refine (congrArg (fun q => q (IsLocalRing.closedPoint _)) hℓ).trans ?_
      exact (congrArg (Y.fromSpecStalk y) (IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I))).trans
        Scheme.fromSpecStalk_closedPoint
    let ψ := (π.fiber b).presheaf.stalkSpecializes (specializes_of_eq e) ≫ Scheme.stalkClosedPointTo ℓ
    have hψ : (π.fiberι b).stalkMap z ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      rw [← cancel_mono (Y.fromSpecStalk y)]
      change _ = g
      rw [← hℓ, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc]
    have hψ' := congrArg (fun q => q.hom a) hψ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hψ'
    rw [RingHom.mem_ker.1 ha, map_zero] at hψ'
    exact Ideal.Quotient.eq_zero_iff_mem.1 hψ'.symm
  · obtain ⟨c, hc⟩ := Spec.map_surjective ((π.fiber b).fromSpecStalk z ≫ π.fiberToSpecResidueField b)
    have key : π.stalkMap (π.fiberι b z) ≫ (π.fiberι b).stalkMap z =
        B.residue _ ≫ (B.residueFieldCongr h').hom ≫ c := by
      apply Spec.map_injective
      rw [← cancel_mono (B.fromSpecStalk (π (π.fiberι b z)))]
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, Scheme.Hom.fiber_fac, ← Category.assoc, ← hc, hA]
      simp only [Spec.map_comp, Category.assoc]
    refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congrArg (fun q => q.hom r) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    have : (B.residue (π (π.fiberι b z))).hom r = 0 := (IsLocalRing.residue_eq_zero_iff r).2 hr
    rw [this, map_zero, map_zero]

theorem nonempty_ringEquiv_stalk_fiber (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    Nonempty ((Y.presheaf.stalk (π.fiberι b z) ⧸
        (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
          (π.stalkMap (π.fiberι b z)).hom) ≃+* (π.fiber b).presheaf.stalk z) := by
  rw [← ker_stalkMap_fiberι]
  exact ⟨RingHom.quotientKerEquivOfSurjective ((π.fiberι b).stalkMap_surjective z)⟩

end GlobalTheory.FibreStalk
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SpecWidePullback

noncomputable def specHomEquiv (X : Scheme.{0}) (R : CommRingCat.{0}) :
    (R ⟶ Γ(X, ⊤)) ≃ (X ⟶ Spec R) where
  toFun φ := ΓSpec.adjunction.homEquiv X (op R) (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op)
  invFun y := ((ΓSpec.adjunction.homEquiv X (op R)).symm y).unop
  left_inv φ := congrArg Quiver.Hom.unop (Equiv.symm_apply_apply (ΓSpec.adjunction.homEquiv X (op R))
    (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op))
  right_inv y := Equiv.apply_symm_apply (ΓSpec.adjunction.homEquiv X (op R)) y

theorem specHomEquiv_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (ψ : R' ⟶ R) (φ : R ⟶ Γ(X, ⊤)) :
    specHomEquiv X R' (ψ ≫ φ) = specHomEquiv X R φ ≫ Spec.map ψ := by
  exact ΓSpec.adjunction.homEquiv_naturality_right (show Scheme.Γ.rightOp.obj X ⟶ op R from φ.op) ψ.op

theorem specHomEquiv_symm_comp (X : Scheme.{0}) {R R' : CommRingCat.{0}} (y : X ⟶ Spec R) (ψ : R' ⟶ R) :
    (specHomEquiv X R').symm (y ≫ Spec.map ψ) = ψ ≫ (specHomEquiv X R).symm y := by
  rw [Equiv.symm_apply_eq, specHomEquiv_comp, Equiv.apply_symm_apply]

theorem existsUnique_lift {A B T : Type} [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) {k : ℕ}
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (X : Scheme.{0}) (y : Fin (k + 1) → (X ⟶ Spec (CommRingCat.of B)))
    (hy : ∀ j, y j ≫ Spec.map (CommRingCat.ofHom a) = y 0 ≫ Spec.map (CommRingCat.ofHom a)) :
    ∃! m : X ⟶ Spec (CommRingCat.of T), ∀ j, m ≫ Spec.map (CommRingCat.ofHom (ι j)) = y j := by
  let g : Fin (k + 1) → (B →+* Γ(X, ⊤)) := fun j => ((specHomEquiv X _).symm (y j)).hom
  have hg : ∀ j, (g j).comp a = (g 0).comp a := fun j => by
    have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of A)).symm z).hom) (hy j)
    simpa [g, specHomEquiv_symm_comp] using this
  obtain ⟨φ, hφ, huniq⟩ := hu Γ(X, ⊤) g hg
  refine ⟨specHomEquiv X _ (CommRingCat.ofHom φ), fun j => ?_, fun m hm => ?_⟩
  · rw [← specHomEquiv_comp, Equiv.apply_eq_iff_eq_symm_apply]
    exact CommRingCat.hom_ext (hφ j)
  · have h1 : ((specHomEquiv X _).symm m).hom = φ := huniq _ fun j => by
      have := congrArg (fun z => ((specHomEquiv X (CommRingCat.of B)).symm z).hom) (hm j)
      simpa [g, specHomEquiv_symm_comp] using this
    rw [← h1]
    simp

end GlobalTheory.SpecWidePullback

namespace GlobalTheory.SpecWidePullback

theorem yoneda_spec_isoWidePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B)
    (k : ℕ) (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)),
      (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  have hleg : ∀ j, Spec.map (CommRingCat.ofHom (ι j)) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom ((ι 0).comp a)) := fun j => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hι j]
  let c : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
      (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a)))) :=
    WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom ((ι 0).comp a))))
      (fun j => yoneda.map (Spec.map (CommRingCat.ofHom (ι j))))
      (fun j => by
        change yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) ≫ yoneda.map (Spec.map (CommRingCat.ofHom a)) = _
        rw [← yoneda.map_comp, hleg j])
  have hc : IsLimit c := by
    apply evaluationJointlyReflectsLimits
    intro U
    have hw : ∀ (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) j,
        s.π.app (some j) x ≫ Spec.map (CommRingCat.ofHom a) = s.π.app none x := fun s x j =>
      ConcreteCategory.congr_hom (s.w (WidePullbackShape.Hom.term j)) x
    have H := fun (s : Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))) ⋙ (evaluation _ _).obj U)) (x : s.pt) =>
      existsUnique_lift a ι hu (unop U) (fun j => s.π.app (some j) x)
        (fun j => (hw s x j).trans (hw s x 0).symm)
    refine IsLimit.mk (fun s => TypeCat.ofHom (fun x => (H s x).exists.choose)) (fun s j => ?_) (fun s m hm => ?_)
    · ext x
      rcases j with _ | j
      · change (H s x).exists.choose ≫ Spec.map (CommRingCat.ofHom ((ι 0).comp a)) = s.π.app none x
        rw [← hleg 0, ← Category.assoc, (H s x).exists.choose_spec 0, hw]
      · exact (H s x).exists.choose_spec j
    · ext x
      refine (H s x).unique (fun j => ?_) (H s x).exists.choose_spec
      have h := ConcreteCategory.congr_hom (hm (some j)) x
      rw [ConcreteCategory.comp_apply] at h
      exact h
  exact ⟨hc.conePointUniqueUpToIso (limit.isLimit _), fun j =>
    hc.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)⟩

end GlobalTheory.SpecWidePullback
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem finite_fibre_and_eq_of_specializes_of_isFinite :
    ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y,
      {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  intro Y Y' k hk y
  refine ⟨k.finite_preimage_singleton y, ?_⟩
  intro a b ha hb h
  have hd := (k.isDiscrete_preimage_singleton y).to_subtype
  have h' : (⟨a, ha⟩ : k ⁻¹' {y}) ⤳ ⟨b, hb⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

end GlobalTheory
end
