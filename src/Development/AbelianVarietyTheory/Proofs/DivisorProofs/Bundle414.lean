module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocus
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle039
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle351
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

theorem widePullbackCone_congr {X Y W : Scheme.{0}} {n : ℕ} (f : Y ⟶ X) (b : W ⟶ X)
    (π π' : Fin n → (W ⟶ Y)) (h : ∀ i, π i ≫ f = b) (h' : ∀ i, π' i ≫ f = b) (e : π = π')
    (H : Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => f) b π h))) :
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => f) b π' h')) := by
  subst e
  exact H

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def l3 : Fin (2 + 1) → (B →+* B ⊗[A] (B ⊗[A] B)) :=
  ![(Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom,
    ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom,
    ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).comp
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom]

theorem triple_tensor_inclusion_comp_algebraMap : ∀ i, (l3 A B i).comp (algebraMap A B) = algebraMap A (B ⊗[A] (B ⊗[A] B)) := by
  intro i
  fin_cases i <;>
  · simp only [l3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
    rw [AlgHom.toRingHom_eq_coe]
    first
    | exact AlgHom.comp_algebraMap _
    | exact AlgHom.comp_algebraMap (_ : B →ₐ[A] B ⊗[A] (B ⊗[A] B))
    | (ext a; simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.one_def])

theorem tmul_tmul_eq (x y z : B) :
    x ⊗ₜ[A] (y ⊗ₜ[A] z) = l3 A B 0 x * l3 A B 1 y * l3 A B 2 z := by
  simp [l3, Algebra.TensorProduct.tmul_mul_tmul]

theorem triple_tensor_ring_hom_ext {T : Type} [CommRing T] (v w : B ⊗[A] (B ⊗[A] B) →+* T)
    (h : ∀ i, v.comp (l3 A B i) = w.comp (l3 A B i)) : v = w := by
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  | tmul x s =>
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hp, hq]
    | tmul y z =>
      rw [tmul_tmul_eq, map_mul, map_mul, map_mul, map_mul]
      have h0 := RingHom.congr_fun (h 0) x
      have h1 := RingHom.congr_fun (h 1) y
      have h2 := RingHom.congr_fun (h 2) z
      simp only [RingHom.comp_apply] at h0 h1 h2
      rw [h0, h1, h2]

theorem tensor3_univ (T : Type) [CommRing T] (g : Fin (2 + 1) → (B →+* T)) (c : A →+* T)
    (hg : ∀ i, (g i).comp (algebraMap A B) = c) :
    ∃! u : B ⊗[A] (B ⊗[A] B) →+* T, u.comp (algebraMap A _) = c ∧ ∀ i, u.comp (l3 A B i) = g i := by
  letI : Algebra A T := c.toAlgebra
  let G : Fin (2 + 1) → (B →ₐ[A] T) := fun i =>
    { g i with
      commutes' := fun a => by
        have := RingHom.congr_fun (hg i) a
        simpa [RingHom.algebraMap_toAlgebra] using this }
  let inner : B ⊗[A] B →ₐ[A] T := Algebra.TensorProduct.lift (G 1) (G 2) (fun _ _ => Commute.all _ _)
  let U : B ⊗[A] (B ⊗[A] B) →ₐ[A] T := Algebra.TensorProduct.lift (G 0) inner (fun _ _ => Commute.all _ _)
  have hU : ∀ i, U.toRingHom.comp (l3 A B i) = g i := by
    intro i
    fin_cases i <;>
    · ext x
      simp [l3, U, inner, G]
  refine ⟨U.toRingHom, ⟨?_, hU⟩, ?_⟩
  · ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rfl
  · rintro u ⟨-, hu⟩
    exact triple_tensor_ring_hom_ext A B _ _ (fun i => (hu i).trans (hU i).symm)

theorem spec_tensor3_isLimit : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B],
    Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin (2 + 1) => GlobalTheory.CechOne.fB A B)
      (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B))))) (GlobalTheory.CechOne.y2 A B)
      (GlobalTheory.CechOne.hy2 A B))) := by
  intro A B _ _ _
  have H := GlobalTheory.spec_widePushout_isLimit (2 + 1) A B (B ⊗[A] (B ⊗[A] B)) (algebraMap A B)
    (algebraMap A _) (l3 A B) (triple_tensor_inclusion_comp_algebraMap A B) (fun T _ g c hg => tensor3_univ A B T g c hg)
  refine widePullbackCone_congr _ _ _ _ _ _ ?_ H
  funext i
  fin_cases i <;> rfl

end GlobalTheory.CechOne
end
end

section

open CategoryTheory Limits TensorProduct

theorem _root_.GlobalTheory.T.exists_zmod_action_model_of_isColimit_filtered : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra;
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  first | (exact @GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_action_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_action_model_of_isColimit  <;> assumption)
end

section

open IsLocalRing

noncomputable section

namespace GlobalTheory.Henselisation

namespace LocalLimit

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem directedSystem_trans :
    DirectedSystem (fun i : EtNbhd R => i.B) (fun i j h => ⇑(EtNbhd.trans h : i.B →+* j.B)) :=
  ⟨fun {i} x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).1 i x,
    fun {k j i} hij hjk x =>
      (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).2 i j k hij hjk x⟩

theorem directed : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R

theorem of_injective (i : EtNbhd R) : Function.Injective (Hens.of i) := by
  haveI := directedSystem_trans (R := R)
  haveI := directed (R := R)
  exact Ring.DirectLimit.of_injective (G := fun i : EtNbhd R => i.B)
    (fun i j h => EtNbhd.trans h) (fun i j h => (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R i j h).2) i

theorem exists_of (z : Hens R) : ∃ (i : EtNbhd R) (x : i.B), Hens.of i x = z := by
  haveI := directed (R := R)
  exact Ring.DirectLimit.exists_of z

theorem of_trans {i j : EtNbhd R} (h : i ≤ j) (x : i.B) :
    Hens.of j (EtNbhd.trans h x) = Hens.of i x :=
  Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h x

theorem nontrivial : Nontrivial (Hens R) := by
  refine nontrivial_of_ne (1 : Hens R) 0 ?_
  intro h
  rw [← map_one (Hens.of (EtNbhd.base (R := R))), ← map_zero (Hens.of (EtNbhd.base (R := R)))] at h
  exact one_ne_zero (of_injective _ h)

theorem isUnit_or_isUnit_of_add_one {a b : Hens R} (hab : a + b = 1) : IsUnit a ∨ IsUnit b := by
  obtain ⟨i, x, rfl⟩ := exists_of a
  obtain ⟨j, y, rfl⟩ := exists_of b
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x + EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [(Hens.of k).map_add, of_trans, of_trans, map_one, hab]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · left
    rw [← of_trans hik]
    exact h.map _
  · right
    rw [← of_trans hjk]
    exact h.map _

theorem isLocalHom_of (i : EtNbhd R) : IsLocalHom (Hens.of i) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := hx
  obtain ⟨j, y, hy⟩ := exists_of (↑u⁻¹ : Hens R)
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x * EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [map_mul, of_trans, of_trans, map_one, hy, ← hu, Units.mul_inv]
  haveI := (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R i k hik).1
  exact isUnit_of_map_unit (EtNbhd.trans hik) x (IsUnit.of_mul_eq_one _ h1)

end LocalLimit

theorem hens_isLocalRing_and_isLocalHom_of :
    ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  intro R _ _
  haveI := LocalLimit.nontrivial (R := R)
  exact ⟨IsLocalRing.of_is_unit_or_is_unit_of_add_one LocalLimit.isUnit_or_isUnit_of_add_one,
    LocalLimit.isLocalHom_of⟩

end GlobalTheory.Henselisation

end
end

section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem Hens.of_injective_of_nbhd (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    Function.Injective (Hens.of i) := by
  have : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  have : DirectedSystem (fun j : EtNbhd R => j.B) (fun _ _ h => ⇑(EtNbhd.trans h)) :=
    ⟨fun j x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).1 j x,
      fun k j l hlj hjk x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).2 l j k hlj hjk x⟩
  exact Ring.DirectLimit.of_injective (G := fun j : EtNbhd R => j.B) (fun _ _ h => EtNbhd.trans h)
    (fun _ _ h => (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R _ _ h).2) i

end GlobalTheory.Henselisation
end

section

open Matrix Polynomial

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isUnit_det_krylov_of_separable {F : Type} [Field F] {r : ℕ}
    (y : Matrix (Fin r) (Fin r) F) (hs : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field y hs
  exact ⟨v, isUnit_iff_ne_zero.2 hv⟩

end GlobalTheory.LeviDesc.Krylov
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.exists_open_affineHilbertChartBasic_locus : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), ∃ W : Z.Opens, (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Z), Set.range a ⊆ (W : Set Z) ↔ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map a.op y)) ∧ (CompactSpace Z → IsCompact (W : Set Z)) := by
  first | (exact @GlobalTheory.HilbAff.Locus.exists_basic_locus) | (exact GlobalTheory.HilbAff.Locus.exists_basic_locus) | (intros; apply GlobalTheory.HilbAff.Locus.exists_basic_locus  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff
theorem glue_exists {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (J : ∀ i, (V i).IdealSheafData)
    (hJ : ∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') :
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i :=
  GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover V f hf hcov J hJ
theorem glue_ext {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' :=
  GlobalTheory.T.idealSheafData_ext_of_openCover' V f hf hcov I I' h
theorem good_local (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : T, ∃ i y, f i y = x)
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (h : ∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) :
    GlobalTheory.HilbAff.Good A B r g I :=
  GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_openCover A B r V f hf hcov g I h

theorem snd_eq_of_sigma {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g₁ : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I₁ : (pullback (str A B) g₁).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g₁ I₁}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g₁, ⟨I₁, h₁⟩⟩) :
    ∃ h : g₀ = g₁, I₀ = I₁.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  have hg : g₀ = g₁ := congrArg Sigma.fst e
  refine ⟨hg, ?_⟩
  subst hg
  have h2 : I₀ = I₁ := by
    have := (Sigma.mk.inj_iff.mp e).2
    exact congrArg Subtype.val (eq_of_heq this)
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id, h2]

theorem fac_bc {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (φ : Z ⟶ pullback (str A B) g) :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      bc A B g (φ ≫ pullback.snd _ _) = φ := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem lift_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T T' Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A))
    (φ : Z ⟶ pullback (str A B) g) (φ' : Z ⟶ pullback (str A B) g')
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (hh : (φ ≫ pullback.snd _ _) ≫ g = (φ' ≫ pullback.snd _ _) ≫ g') :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      pullback.map (str A B) ((φ ≫ pullback.snd _ _) ≫ g) (str A B) ((φ' ≫ pullback.snd _ _) ≫ g')
        (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hh]) =
    pullback.lift (φ' ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    exact e1
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem comap_eq_of_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    {X X' Z : Scheme.{0}} (y : (functor A B r).obj (op X)) (y' : (functor A B r).obj (op X'))
    (φ : Z ⟶ pullback (str A B) y.1) (φ' : Z ⟶ pullback (str A B) y'.1)
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (e : (functor A B r).map (φ ≫ pullback.snd _ _).op y =
      (functor A B r).map (φ' ≫ pullback.snd _ _).op y') :
    y.2.1.comap φ = y'.2.1.comap φ' := by
  obtain ⟨hh, hI⟩ := snd_eq_of_sigma e
  simp only [Quiver.Hom.unop_op] at hh hI
  rw [← fac_bc y.1 φ, ← fac_bc y'.1 φ', Scheme.IdealSheafData.comap_comp, hI,
    Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp _ _ (pullback.map _ _ _ _ _ _ _ _ _),
    lift_map_eq y.1 y'.1 φ φ' e1 hh, ← Scheme.IdealSheafData.comap_comp]

theorem good_transport {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I : (pullback (str A B) g).IdealSheafData} (hI : Good A B r g I) :
    Good A B r g₀ (I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]))) := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact hI

theorem isOpenImmersion_bc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T T' : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) [IsOpenImmersion a] :
    IsOpenImmersion (bc A B g a) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bc A B g a).flip inferInstance

theorem isSheaf_functor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (functor A B r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro (x : ∀ j, (functor A B r).obj (op (𝒰.X j))) hx
  replace hx : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = a' ≫ 𝒰.f j → (functor A B r).map a.op (x i) = (functor A B r).map a'.op (x j) := hx
  let g : Y ⟶ Spec (CommRingCat.of A) := 𝒰.glueMorphisms (fun j => (x j).1) fun i j =>
    congrArg Sigma.fst (hx i j _ _ _ pullback.condition)
  have hg : ∀ j, 𝒰.f j ≫ g = (x j).1 := fun j => 𝒰.ι_glueMorphisms _ _ j
  have hoi : ∀ j, IsOpenImmersion (bc A B g (𝒰.f j)) := fun j => isOpenImmersion_bc A B g (𝒰.f j)
  have hcov : ∀ p : ↥(pullback (str A B) g : Scheme.{0}), ∃ j q, bc A B g (𝒰.f j) q = p := by
    intro p
    obtain ⟨j, t, ht⟩ := 𝒰.exists_eq (pullback.snd (str A B) g p)
    have hr := (isPullback_bc A B g (𝒰.f j)).isoPullback_hom_fst
    have hmem : p ∈ Set.range (bc A B g (𝒰.f j)) := by
      rw [← hr, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso _).2, Set.image_univ,
        Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    obtain ⟨q, hq⟩ := hmem
    exact ⟨j, q, hq⟩
  let J : ∀ j, (pullback (str A B) (𝒰.f j ≫ g)).IdealSheafData := fun j =>
    (x j).2.1.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hg j]))
  have hJ : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ pullback (str A B) (𝒰.f i ≫ g))
      (a' : Z ⟶ pullback (str A B) (𝒰.f j ≫ g)),
      a ≫ bc A B g (𝒰.f i) = a' ≫ bc A B g (𝒰.f j) → (J i).comap a = (J j).comap a' := by
    intro i j Z a a' e
    have f1 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.fst (str A B) g = pullback.fst _ _ := fun k =>
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have f2 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.snd (str A B) g = pullback.snd _ _ ≫ 𝒰.f k :=
      fun k => pullback.lift_snd _ _ _
    have p1 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have p2 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.snd _ _ = b ≫ pullback.snd _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have e1 : a ≫ pullback.fst _ _ = a' ≫ pullback.fst _ _ := by
      rw [← f1 i, ← f1 j, ← Category.assoc, e, Category.assoc]
    have e2 : (a ≫ pullback.snd _ _) ≫ 𝒰.f i = (a' ≫ pullback.snd _ _) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← f2 i, ← f2 j, ← Category.assoc, e, Category.assoc]
    change ((x i).2.1.comap _).comap a = ((x j).2.1.comap _).comap a'
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    refine comap_eq_of_map_eq (x i) (x j) _ _ (by rw [p1, p1, e1]) ?_
    rw [p2, p2]
    exact hx i j Z _ _ e2
  obtain ⟨I, hI⟩ := glue_exists (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
    (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov J hJ
  have good : Good A B r g I := good_local A B r 𝒰.X 𝒰.f (fun j => inferInstance)
    (fun y => 𝒰.exists_eq y) g I (fun j => by rw [hI j]; exact good_transport (hg j) (x j).2.2)
  have amal : ∀ j, (functor A B r).map (𝒰.f j).op ⟨g, ⟨I, good⟩⟩ = x j := fun j =>
    sigma_eq A B r (hg j) (hI j) _ (x j).2.2
  refine ⟨⟨g, ⟨I, good⟩⟩, amal, fun y' hy' => ?_⟩
  replace hy' : ∀ j, (functor A B r).map (𝒰.f j).op y' = x j := hy'
  have e : y'.1 = g := 𝒰.hom_ext _ _ fun j => (congrArg Sigma.fst (hy' j)).trans (hg j).symm
  obtain ⟨g', I', hI'⟩ := y'
  change g' = g at e
  subst e
  have : I' = I := by
    refine glue_ext (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
      (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov I' I fun j => ?_
    have := (hy' j).trans (amal j).symm
    exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)
  subst this
  rfl

end GlobalTheory.HilbAff
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem _root_.GlobalTheory.T.pow_mul_mem_subalgebra_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  first | exact @GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | exact GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen | (intros; apply GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem _root_.GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by
  first | exact @GlobalTheory.sub_choose_finite | exact GlobalTheory.sub_choose_finite | (intros; apply GlobalTheory.sub_choose_finite <;> assumption)
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem _root_.GlobalTheory.T.gaussianPairing_unitaryGroup_two_three : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι] (e : V ≃L[ℝ] (ι → ℂ)), (∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) → ∀ (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 → ∀ J : V ≃ₗᵢ[ℝ] V, (∀ v, e (J v) = I • s *ᵥ e v) → (∀ (g : Matrix ι ι ℂ) (k : V → V), gᴴ * s * g = s → (∀ v, e (k v) = g *ᵥ e v) → dP s g ≠ 0 ∧ dP s g⁻¹ = star (dP s g) ∧ lam k = (dP s g * dP s g⁻¹)⁻¹) ∧ ∀ (g₁ g₂ : Matrix ι ι ℂ) (k₁ k₂ : V → V), g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s → (∀ v, e (k₁ v) = g₁ *ᵥ e v) → (∀ v, e (k₂ v) = g₂ *ᵥ e v) → mu J k₁ k₂ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by
  first | exact @GlobalTheory.RealWeil.GaussPairing.lam_mu_eq | exact GlobalTheory.RealWeil.GaussPairing.lam_mu_eq | (intros; apply GlobalTheory.RealWeil.GaussPairing.lam_mu_eq <;> assumption)
end
