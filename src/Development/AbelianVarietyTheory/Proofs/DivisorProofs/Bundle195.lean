module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.LocallyDirected
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle036
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle037
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Mathlib.AlgebraicGeometry.Scheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle030
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

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

theorem lift_of_nilpotent_of_sqZero :
    (∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e) →
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  intro H
  suffices key : ∀ n : ℕ, ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
      RingHom.ker π ^ n = ⊥ →
      ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) →
      Smooth X.hom →
      ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e by
    intro R R₀ _ _ π hπ hnil
    obtain ⟨n, hn⟩ := hnil
    exact key n R R₀ π hπ hn
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn
    refine H R R₀ π hπ ?_
    exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.zero_le 2)).trans hn.le)
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ i hi hX e₀ he₀
    by_cases hn2 : n + 1 ≤ 2
    · exact H R R₀ π hπ (le_bot_iff.mp ((Ideal.pow_le_pow_right hn2).trans hn.le)) X X₀ i hi hX e₀ he₀
    have hn1 : 1 ≤ n := by omega
    set I := RingHom.ker π with hIdef
    set J : Ideal R := I ^ n with hJdef
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self (by omega)
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    let π'' : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π (fun a ha => (RingHom.mem_ker).mp (hJI ha))
    have hcomp : π''.comp q = π := by
      ext a; rfl
    have hsp : spMap π = spMap π'' ≫ spMap q := by
      rw [← hcomp]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have hπ'' : Function.Surjective π'' := Ideal.Quotient.lift_surjective_of_surjective J _ hπ
    have hkerq : RingHom.ker q = J := Ideal.mk_ker
    have hkerπ'' : RingHom.ker π'' = I.map q := by
      have := RingHom.comap_ker π'' q
      rw [hcomp] at this
      rw [← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective (RingHom.ker π''), this]
    have hn'' : RingHom.ker π'' ^ n = ⊥ := by
      rw [hkerπ'', ← Ideal.map_pow]
      exact Ideal.map_quotient_self J
    have hJ2 : RingHom.ker q ^ 2 = ⊥ := by
      rw [hkerq, hJdef, ← pow_mul]
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    let X' : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom (spMap q))
    have hX' : Smooth X'.hom := show Smooth (pullback.snd X.hom (spMap q)) from inferInstance
    have hw : i ≫ X.hom = (X₀.hom ≫ spMap π'') ≫ spMap q := by
      rw [hi.w, hsp, Category.assoc]
    let i' : X₀.left ⟶ X'.left := pullback.lift i (X₀.hom ≫ spMap π'') hw
    have hi'1 : i' ≫ pullback.fst X.hom (spMap q) = i := pullback.lift_fst _ _ _
    have hi'2 : i' ≫ X'.hom = X₀.hom ≫ spMap π'' := pullback.lift_snd _ _ _
    have hi' : IsPullback i' X₀.hom X'.hom (spMap π'') := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom (spMap q)) (h₂₂ := spMap q) (v₁₃ := X.hom) ?_ hi'2
        (IsPullback.of_hasPullback X.hom (spMap q))
      rw [hi'1, ← hsp]
      exact hi
    obtain ⟨e', he'1, he'2⟩ := ih (R ⧸ J) R₀ π'' hπ'' hn'' X' X₀ i' hi' hX' e₀ he₀
    obtain ⟨e, he1, he2⟩ := H R (R ⧸ J) q Ideal.Quotient.mk_surjective hJ2 X X'
      (pullback.fst X.hom (spMap q)) (IsPullback.of_hasPullback X.hom (spMap q)) hX e' he'1
    refine ⟨e, he1, ?_⟩
    calc e₀ ≫ i = e₀ ≫ i' ≫ pullback.fst X.hom (spMap q) := by rw [hi'1]
      _ = (spMap π'' ≫ e') ≫ pullback.fst X.hom (spMap q) := by rw [← Category.assoc, he'2]
      _ = spMap π'' ≫ spMap q ≫ e := by rw [Category.assoc, he2]
      _ = spMap π ≫ e := by rw [hsp, Category.assoc]

end GlobalTheory.SecLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k] [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom → PreirreducibleSpace ↥(pullback (W.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  first | exact @GlobalTheory.preirreducibleSpace_tensor_of_pullback | exact GlobalTheory.preirreducibleSpace_tensor_of_pullback | (intros; apply GlobalTheory.preirreducibleSpace_tensor_of_pullback <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd : ∀ (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T), IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  first | exact @GlobalTheory.whiskerLeft_left_isPullback_snd | exact GlobalTheory.whiskerLeft_left_isPullback_snd | (intros; apply GlobalTheory.whiskerLeft_left_isPullback_snd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A), Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) → (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  first | exact @GlobalTheory.overScheme_grpObj_of_mono_factor | exact GlobalTheory.overScheme_grpObj_of_mono_factor | (intros; apply GlobalTheory.overScheme_grpObj_of_mono_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.mul_mem_identityComponent_of_rational' : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by
  first | exact @GlobalTheory.mul_mem_identityComponent_of_rational | exact GlobalTheory.mul_mem_identityComponent_of_rational | (intros; apply GlobalTheory.mul_mem_identityComponent_of_rational <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s)) (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s → ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  first | exact @GlobalTheory.component_in_fibre_iff_of_isPullback | exact GlobalTheory.component_in_fibre_iff_of_isPullback | (intros; apply GlobalTheory.component_in_fibre_iff_of_isPullback <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem _root_.GlobalTheory.T.exists_stalk_retraction_of_small_lifting : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by
  first | exact @GlobalTheory.SmallLift.exists_retraction | exact GlobalTheory.SmallLift.exists_retraction | (intros; apply GlobalTheory.SmallLift.exists_retraction <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem _root_.GlobalTheory.T.residueFieldMap_surjective_of_mono' : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X), Function.Surjective (f.residueFieldMap x).hom := by
  first | exact @GlobalTheory.residueFieldMap_surjective_of_mono | exact GlobalTheory.residueFieldMap_surjective_of_mono | (intros; apply GlobalTheory.residueFieldMap_surjective_of_mono <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem _root_.GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  first | exact @GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | exact GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | (intros; apply GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.isLocallyDirected_of_bijective_basis_compatible : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : B₀, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → ∀ (F : 𝒰 ⥤ Scheme.{0}), (∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)) → ∀ (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U), (∀ U, Function.Injective (e U)) → (∀ U, Function.Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → (F ⋙ Scheme.forget).IsLocallyDirected := by
  first | exact @GlobalTheory.ThickGlue.isLocallyDirected_of_basis | exact GlobalTheory.ThickGlue.isLocallyDirected_of_basis | (intros; apply GlobalTheory.ThickGlue.isLocallyDirected_of_basis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.jointCover_sectionDetect_restrict_open : ∀ (Z Z₁ Z₂ : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z), (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) → (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) → ∀ V : Z.Opens, (∀ z : V.toScheme, (∃ z₁, e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl z₁ = z) ∨ ∃ z₂, e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl z₂ = z) ∧ ∀ (W : V.toScheme.Opens) (a b : Γ(V.toScheme, W)), (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W a = (e₁.resLE V (e₁ ⁻¹ᵁ V) le_rfl).app W b → (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W a = (e₂.resLE V (e₂ ⁻¹ᵁ V) le_rfl).app W b → a = b := by
  first | exact @GlobalTheory.cover_and_joint_inj_restrict | exact GlobalTheory.cover_and_joint_inj_restrict | (intros; apply GlobalTheory.cover_and_joint_inj_restrict <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite

theorem _root_.GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda : ∀ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ) (ι : Fin (k + 1) → (B →+* T)), (∀ j, (ι j).comp a = (ι 0).comp a) → (∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) → ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) → ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A))) (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))), ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) := by
  first | (exact @GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (exact GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback) | (intros; apply GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback  <;> assumption)
end
