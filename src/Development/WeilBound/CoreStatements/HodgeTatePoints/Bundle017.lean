module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Htat.StalkDivisibility

def constSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (d : R) : Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)

section valAt

variable {B C R : Type} [CommRing B] [CommRing C] [CommRing R] {X Y : Scheme.{0}}

theorem valAt_congr {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

theorem valAt_res (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem valAt_mul (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

theorem valAt_sub (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem valAt_comp (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U)
    (s : Γ(X, U)) : valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem specMap_appLE_top (φ : B →+* C) (e) (r : Γ(Spec (CommRingCat.of B), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e).hom r) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom r) := by
  have h : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop := by
    exact (Scheme.Hom.app_eq_appLE _).symm
  rw [h]
  exact congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_spec (κ : B →+* C) (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ x) U h' s = κ (valAt x U h s) := by
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom κ)) x U ⊤ ⊤ h (fun _ _ => trivial)
  simp only [valAt]
  rw [← e]
  exact specMap_appLE_top κ _ _

theorem valAt_const (p : X ⟶ Spec (CommRingCat.of R)) (x : Spec (CommRingCat.of B) ⟶ X) (φ : R →+* B)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (d : R) :
    valAt x U h (constSec p U d) = φ d := by
  have e := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  have key : ∀ (y : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (_ : y = Spec.map (CommRingCat.ofHom φ)) (e' : ⊤ ≤ y ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE ⊤ ⊤ e').hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d := by
    intro y hy e'
    subst hy
    rw [specMap_appLE_top]
    simp
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
    ((p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d
  rw [e]
  exact key _ hx _

theorem constSec_res (p : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (i : V ⟶ U) (d : R) :
    (X.presheaf.map i.op).hom (constSec p U d) = constSec p V d :=
  congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d))
    (p.appLE_map (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) i.op)

theorem app_constSec {R' : Type} [CommRing R'] (p : X ⟶ Spec (CommRingCat.of R)) (p' : Y ⟶ Spec (CommRingCat.of R'))
    (F : Y ⟶ X) (φ : R →+* R') (hF : F ≫ p = p' ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (d : R) :
    (F.app U).hom (constSec p U d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
  have e₁ := Scheme.Hom.appLE_comp_appLE F p ⊤ U (F ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e₂ : ∀ (y : Y ⟶ Spec (CommRingCat.of R)) (_ : y = p' ≫ Spec.map (CommRingCat.ofHom φ)) (e' : F ⁻¹ᵁ U ≤ y ⁻¹ᵁ ⊤),
      (y.appLE ⊤ (F ⁻¹ᵁ U) e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
    intro y hy e'
    subst hy
    rw [Scheme.Hom.comp_appLE]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have n' := congrArg (fun ψ => ψ.hom d) n
    simp only [constSec]
    change (p'.appLE _ _ _).hom (((Spec.map (CommRingCat.ofHom φ)).appTop).hom _) = _
    exact congrArg (p'.appLE ⊤ (F ⁻¹ᵁ U) (fun _ _ => trivial)).hom n'.symm
  rw [← e₂ _ hF (fun _ _ => trivial), ← e₁, Scheme.Hom.app_eq_appLE]
  rfl

theorem dvd_of_stalkMap_dvd (r : Y ⟶ X) [Flat r] (z : Y) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact h

theorem top_le_of_spec_comp {K L : Type} [Field K] [Field L] (κ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro y _
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  obtain ⟨w⟩ := this
  have hw := h (show w ∈ (⊤ : (Spec (CommRingCat.of L)).Opens) from trivial)
  rw [Subsingleton.elim y (Spec.map (CommRingCat.ofHom κ) w)]
  simpa using hw

end valAt

theorem regularAt_of_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hfl κ hκ f g' hreg
  obtain ⟨U', hgU', s', hs'⟩ := hreg
  obtain ⟨d, hd0, U, hgU, s, hs⟩ := GlobalTheory.T.exists_denominator_regular R T Γ f (F g')
  have hφ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hfl)
  have hF : Flat F := MorphismProperty.of_isPullback (P := @Flat) hbc.cart.flip hφ
  have hsq : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := hbc.cart.w
  let W' : Γ'.G.left.Opens := (F ⁻¹ᵁ U) ⊓ U'
  have hgW' : g' ∈ W' := ⟨hgU, hgU'⟩
  let i₁ : W' ⟶ F ⁻¹ᵁ U := homOfLE inf_le_left
  let i₂ : W' ⟶ U' := homOfLE inf_le_right
  have key : (Γ'.G.left.presheaf.map i₁.op).hom ((F.app U).hom s) =
      constSec Γ'.G.hom W' (algebraMap R R' d) * (Γ'.G.left.presheaf.map i₂.op).hom s' := by
    refine sub_eq_zero.mp (PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' W' _ fun t h => ?_)
    have h₁ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ (F ⁻¹ᵁ U) := fun x hx => (h hx).1
    have h₂ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U' := fun x hx => (h hx).2
    have hpt := GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t
    have h₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := by
      rw [← hpt]; exact h₁
    have h₄ : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_spec_comp κ _ U h₃
    have hw' : (Γ'.pt t).left ≫ Γ'.G.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) := Over.w (Γ'.pt t)
    rw [valAt_sub, valAt_mul, valAt_res _ i₁ h h₁, valAt_res _ i₂ h h₂, hs' t h₂,
      valAt_const _ _ (algebraMap R' (FractionRing R')) hw', ← valAt_comp _ F U h₁,
      valAt_congr hpt U h₁ h₃, valAt_spec κ _ U h₄ h₃, hs t h₄, map_mul]
    have : κ (algebraMap R _ d) = algebraMap R' _ (algebraMap R R' d) := congrArg (fun ψ => ψ d) hκ
    rw [this, sub_self]
  have hdvd : Γ.G.left.presheaf.germ U (F g') hgU (constSec Γ.G.hom U d) ∣
      Γ.G.left.presheaf.germ U (F g') hgU s := by
    apply dvd_of_stalkMap_dvd F g'
    refine ⟨Γ'.G.left.presheaf.germ W' g' hgW' ((Γ'.G.left.presheaf.map i₂.op).hom s'), ?_⟩
    have e₁ := Scheme.Hom.germ_stalkMap_apply F U g' hgU s
    have e₂ := Scheme.Hom.germ_stalkMap_apply F U g' hgU (constSec Γ.G.hom U d)
    rw [app_constSec _ _ F _ hsq] at e₂
    have e₃ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' ((F.app U).hom s)
    have e₄ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' (constSec Γ'.G.hom (F ⁻¹ᵁ U) (algebraMap R R' d))
    rw [constSec_res] at e₄
    rw [key, map_mul] at e₃
    exact e₁.trans (e₃.symm.trans (by rw [e₄, ← e₂]))
  obtain ⟨x, hx⟩ := hdvd
  obtain ⟨W, hgW, s₀, rfl⟩ := Γ.G.left.presheaf.exists_germ_eq x
  let P : Γ.G.left.Opens := U ⊓ W
  have hgP : F g' ∈ P := ⟨hgU, hgW⟩
  let j₁ : P ⟶ U := homOfLE inf_le_left
  let j₂ : P ⟶ W := homOfLE inf_le_right
  have hP : Γ.G.left.presheaf.germ U (F g') hgU s = Γ.G.left.presheaf.germ P (F g') hgP
      (constSec Γ.G.hom P d * (Γ.G.left.presheaf.map j₂.op).hom s₀) := by
    rw [hx, map_mul, TopCat.Presheaf.germ_res_apply, ← constSec_res _ j₁, TopCat.Presheaf.germ_res_apply]
  obtain ⟨V, hV, iU, iP, hres⟩ := TopCat.Presheaf.germ_eq _ _ hgU hgP _ _ hP
  refine ⟨V, hV, (Γ.G.left.presheaf.map (iP ≫ j₂).op).hom s₀, fun t h => ?_⟩
  have hU : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun x hx => iU.le (h hx)
  have hPt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ P := fun x hx => iP.le (h hx)
  have hWt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ W := fun x hx => (iP ≫ j₂).le (h hx)
  have hw : (Γ.pt t).left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := Over.w (Γ.pt t)
  have hK : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa using hd0
  refine mul_left_cancel₀ hK ?_
  have e₁ := congrArg (valAt (Γ.pt t).left V h) hres
  rw [valAt_res _ iU h hU, hs t hU, valAt_res _ iP h hPt, valAt_mul, valAt_const _ _ _ hw,
    valAt_res _ j₂ hPt hWt] at e₁
  rw [valAt_res _ (iP ≫ j₂) h hWt]
  exact e₁.symm

end PositivityTheory.HtPt.Htat.StalkDivisibility

theorem PositivityTheory.HtPt.Htat.bt_reg_descent : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') :=
  @PositivityTheory.HtPt.Htat.StalkDivisibility.regularAt_of_baseChange
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Mh

section pb

variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {X Y : Scheme.{0}}

def pb (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

def val (x : Spec (CommRingCat.of B) ⟶ X) : Γ(X, ⊤) →+* B :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom

theorem valAt_top (x : Spec (CommRingCat.of B) ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (s : Γ(X, ⊤)) : valAt x ⊤ h s = val x s := by
  simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem pb_ext {j j' : X ⟶ Spec (CommRingCat.of A)} (h : ∀ a, pb j a = pb j' a) : j = j' := by
  apply ext_of_isAffine
  have e : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j'.appTop := by
    ext a
    exact h a
  exact (cancel_epi _).1 e

theorem pb_comp (f : Y ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) : pb (f ≫ j) a = f.appTop (pb j a) := by
  unfold pb
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem val_comp (x : Spec (CommRingCat.of B) ⟶ Y) (f : Y ⟶ X) (s : Γ(X, ⊤)) :
    val (x ≫ f) s = val x (f.appTop s) := by
  unfold val
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem pb_spec (j : X ⟶ Spec (CommRingCat.of B)) (ψ : A →+* B) (a : A) :
    pb (j ≫ Spec.map (CommRingCat.ofHom ψ)) a = pb j (ψ a) := by
  simp only [pb, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem val_pb_id (b : B) : val (𝟙 _) (pb (𝟙 (Spec (CommRingCat.of B))) b) = b := by
  simp [val, pb]

theorem val_pb_comp (x : Spec (CommRingCat.of B) ⟶ X) (j : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    val x (pb j a) = val (𝟙 _) (pb (x ≫ j) a) := by
  rw [pb_comp, ← val_comp, Category.id_comp]

theorem val_pb {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : x ≫ j = Spec.map (CommRingCat.ofHom φ)) (a : A) : val x (pb j a) = φ a := by
  have e := pb_spec (𝟙 (Spec (CommRingCat.of B))) φ a
  rw [Category.id_comp] at e
  rw [val_pb_comp, h, e, val_pb_id]

theorem val_id_injective : Function.Injective (val (𝟙 (Spec (CommRingCat.of B)))) := by
  intro s t hst
  have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) s) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (val (𝟙 _) t) := by
    rw [hst]
  simpa [val] using e

theorem comp_eq_spec {x : Spec (CommRingCat.of B) ⟶ X} {j : X ⟶ Spec (CommRingCat.of A)} {φ : A →+* B}
    (h : ∀ a, val x (pb j a) = φ a) : x ≫ j = Spec.map (CommRingCat.ofHom φ) := by
  refine pb_ext fun a => val_id_injective ?_
  rw [← val_pb_comp, h, val_pb (Category.id_comp _)]

theorem exists_pb (φ : A →+* Γ(X, ⊤)) : ∃ j : X ⟶ Spec (CommRingCat.of A), ∀ a, pb j a = φ a := by
  refine ⟨(ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A))) (CommRingCat.ofHom φ).op,
    fun a => ?_⟩
  rw [pb, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  rfl

theorem spec_inj {φ ψ : A →+* B} (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spec_comp (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
  rw [← Spec.map_comp]
  rfl

end pb

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] [Finite T]

theorem sec_ext (Γ : QFGroup R T) {s s' : Γ(Γ.G.left, ⊤)} (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') :
    s = s' := by
  rw [← sub_eq_zero]
  refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
  rw [valAt_top, map_sub, h, sub_self]

theorem hom_ext_pt (Γ : QFGroup R T) {A : Type} [CommRing A] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
  pb_ext fun a => sec_ext Γ fun t => by rw [val_pb_comp, h, ← val_pb_comp]

theorem mem_top_iff (Γ : QFGroup R T) (f : T → R) : f ∈ Γ.btOrder ⊤ ↔
    ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h, val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
  have hsub : ∀ {B : Type} [CommRing B] {X : Scheme} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
      (hx : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)), valAt x U hx (a - b) = valAt x U hx a - valAt x U hx b := by
    intro B _ X x U hx a b
    simp only [valAt, map_sub]
  constructor
  · intro hf t
    rw [Twhopf.mem_order] at hf
    have hreg : ∀ g : Γ.G.left, ∃ U : Γ.G.left.Opens, g ∈ U ∧ ∃ s : Γ(Γ.G.left, U),
        ∀ (h : T) (hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U),
          valAt (Γ.pt h).left U hh s = algebraMap R (FractionRing R) (f (t * h)) :=
      fun g => hf t g (by simp)
    choose U hgU s hs using hreg
    obtain ⟨g0, hglue, -⟩ := TopCat.Sheaf.existsUnique_gluing' Γ.G.left.sheaf U ⊤
      (fun g => homOfLE le_top) (fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hgU x⟩) s (by
        intro g g'
        rw [← sub_eq_zero]
        apply Twhopf.sec_inj R T Γ _ _
        intro h hh
        have h1 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).1
        have h2 : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U g' :=
          (SubOrder.top_le_iff_mem _ _).2 fun z => ((SubOrder.top_le_iff_mem _ _).1 hh z).2
        refine (hsub _ _ hh _ _).trans ?_
        erw [Twhopf.valAt_restrict _ _ hh h1, Twhopf.valAt_restrict _ _ hh h2]
        rw [hs, hs, sub_self])
    refine ⟨g0, fun h => ?_⟩
    have htop : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ ⊤ := (SubOrder.top_le_iff_mem _ _).2 fun _ => trivial
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    have hh : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U ((Γ.pt h).left z) :=
      Twhopf.top_le_of_mem _ z (hgU _)
    refine (valAt_top _ htop g0).symm.trans ?_
    refine (Twhopf.valAt_restrict _ (homOfLE le_top) hh htop g0).symm.trans ?_
    erw [hglue ((Γ.pt h).left z)]
    exact hs _ h hh
  · intro hf
    rw [Twhopf.mem_order]
    intro t g _
    obtain ⟨s, hs⟩ := hf t
    unfold QFGroup.RegularAt
    exact ⟨⊤, by simp, s, fun h hh => by rw [valAt_top, hs]⟩

omit [Finite T] in
theorem val_const (Γ : QFGroup R T) (t : T) (r : R) :
    val (Γ.pt t).left (pb Γ.G.hom r) = algebraMap R (FractionRing R) r :=
  val_pb (Over.w (Γ.pt t)) r

omit [Finite T] in
theorem val_emb {Γ : QFGroup R T} {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (a : A) :
    val (Γ.pt t).left (pb j a) = algebraMap R (FractionRing R) (a.1 t) :=
  val_pb (hj.pt t) a

theorem exists_emb (Γ : QFGroup R T) (A : Subalgebra R (T → R))
    (hA : ∀ a : A, ∃ s : Γ(Γ.G.left, ⊤), ∀ t, val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t)) :
    ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of A), Γ.IsEmb A j := by
  choose s hs using hA
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := sec_ext Γ fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => sec_ext Γ fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := sec_ext Γ fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => sec_ext Γ fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hom_ext_pt Γ fun t => by rw [hj'.pt, hpt]⟩
  apply hom_ext_pt Γ
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

end PositivityTheory.HtPt.Mh
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Ma

theorem reg_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q :=
  fun _ _ _ ξ p a ha => exists_open_mem_regAt ξ p a ha

theorem reg_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) := by
  intro X Ω _ ξ
  refine ⟨fun p => ?_, fun p q h => (RegAtMono.regAt_mono X Ω ξ p q h).1, fun hg p a => ?_⟩
  · unfold regAt
    exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (RingHom.rangeRestrict_surjective _)
  · haveI := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).2.1
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
    refine ⟨u, u.2, v, v.2, fun h => ?_, rfl⟩
    exact nonZeroDivisors.ne_zero hv (Subtype.ext h)

theorem regat_loc : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v := by
  intro o _ Ω _ _ κ _ x M c p hp
  have h1 : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p := fun a ha => (M.tie.ring c hp.1 a).1 ha p hp
  refine ⟨h1, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction M.X Ω M.ξ o κ x M.tie c p hp a).1 ha
    exact ⟨s * a, hsa, s, hs, hu, by field_simp [hu.1]⟩
  · rintro ⟨u, hu, v, -, hv, rfl⟩
    rw [div_eq_mul_inv]
    exact mul_mem (h1 u hu) hv.2.2

theorem prime_pt : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) := by
  intro o _ Ω _ _ κ _ x M c hc P hP
  obtain ⟨p, ⟨h1, h2⟩, h3⟩ := chart_point_of_prime M.X Ω M.ξ o κ x M.tie c hc P hP
  refine ⟨p, ⟨h1, fun u => ?_⟩, fun q hq => h3 q ⟨hq.1, fun u => ?_⟩⟩
  · rw [← h2 u, not_not]
  · rw [hq.2 u, not_not]

open ChartPrimes in
theorem basic : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U := by
  intro o _ Ω _ _ κ _ x M c p U hp hpU
  have T := M.tie
  have hc := hp.1
  obtain ⟨W, hW, hmem⟩ := T.affine c hc
  have hg : genPt M.ξ ∈ W := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hpW : p.1 ∈ W := (hmem _).2 ⟨p.2, hp⟩
  obtain ⟨f, hf, hpf⟩ := hW.exists_basicOpen_le (V := U) ⟨p.1, hpU⟩ hpW
  have key : ∀ (q : Cpt M.ξ) (hq : q.1 ∈ W), q.1 ∈ M.X.basicOpen f ↔ unitAt M.ξ q (secVal M.ξ W hg f) := by
    intro q hq
    rw [M.X.mem_basicOpen f _ hq, ← genMap_germ_eq W hg q hq f]
    exact isUnit_iff_unitAt q (T.gen.inj _) _
  refine ⟨secVal M.ξ W hg f, ?_, (key p hpW).1 hpf, fun q hq hu => hf ((key q ((hmem _).2 ⟨q.2, hq⟩)).2 hu)⟩
  exact (T.ring c hc _).2 fun q hq => ⟨_, genMap_germ_eq W hg q ((hmem _).2 ⟨q.2, hq⟩) f⟩

theorem reg_le_spec : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  intro o _ Ω _ _ κ _ x M p q
  refine ⟨fun h => ?_, (reg_local M.X Ω M.ξ).2.1 p q⟩
  rw [specializes_iff_forall_open]
  intro s hs hp
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨f, -, hu, hf⟩ := basic o Ω κ x M c p ⟨s, hs⟩ hc hp
  exact hf q ⟨hc.1, fun j => h (hc.2 j)⟩ ⟨hu.1, h hu.2.1, h hu.2.2⟩

end PositivityTheory.HtPt.Ma
end
