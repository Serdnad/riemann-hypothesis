module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.CoordFn

theorem isIso_appLE_of_opensRange {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (hU : f.opensRange = U) (h : ⊤ ≤ f ⁻¹ᵁ U) : IsIso (f.appLE U ⊤ h) := by
  subst hU
  have h1 : IsIso (f.app f.opensRange) := Scheme.Hom.isIso_app f _ le_rfl
  have h2 : (⊤ : X.Opens) = f ⁻¹ᵁ f.opensRange := le_antisymm h le_top
  have h3 : IsIso (homOfLE h) := by
    have : homOfLE h = eqToHom h2 := rfl
    rw [this]; infer_instance
  rw [Scheme.Hom.appLE]
  infer_instance

theorem appLE_SpecMap_comp {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : B ⟶ A)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (p : Spec A ⟶ Y) (hp : p = Spec.map g ≫ f)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) :
    p.appLE U ⊤ h' ≫ (Scheme.ΓSpecIso A).hom = f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom ≫ g := by
  subst hp
  have e1 : (Spec.map g).appTop = (Spec.map g).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.app_eq_appLE (Spec.map g)
  have e2 := Scheme.Hom.appLE_comp_appLE (Spec.map g) f U ⊤ ⊤ h le_top
  rw [← Scheme.ΓSpecIso_naturality, e1, ← Category.assoc, e2]

theorem appLE_structure {Y : Scheme.{0}} {A B : CommRingCat.{0}} (f : Spec B ⟶ Y) (g : A ⟶ B)
    (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (t : Y ⟶ Spec A) (ht : f ≫ t = Spec.map g) :
    (Scheme.ΓSpecIso A).inv ≫ t.appLE ⊤ U le_top ≫ f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom = g := by
  have e2 := Scheme.Hom.appLE_comp_appLE f t ⊤ U ⊤ le_top h
  have e1 : ∀ (q : Spec B ⟶ Spec A) (hq : ⊤ ≤ q ⁻¹ᵁ ⊤), q = Spec.map g →
      q.appLE ⊤ ⊤ hq = (Spec.map g).appTop := by
    rintro _ _ rfl
    exact (Scheme.Hom.app_eq_appLE (Spec.map g)).symm
  rw [← Category.assoc (t.appLE ⊤ U le_top), e2, e1 _ _ ht, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

theorem top_le_preimage {R : Type} [CommRing R] (W : WeierstrassCurve R) (i : Fin 3) :
    ⊤ ≤ awayChart W i ⁻¹ᵁ coordOpen W i := by
  rw [← opensRange_awayChart, Scheme.Hom.preimage_opensRange]

theorem surjective_eval₂Hom_awayCoord {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i)) := by
  intro x
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading W) (coord_mem W i) x
  rw [← evalHom_awayCoord]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨p, rfl⟩

theorem exists_coordFn : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), ∃ c : ∀ i j : Fin 3, Γ(scheme W, coordOpen W i), (∀ (i j : Fin 3) (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P) (h : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ coordOpen W i), (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((ptHom W ρ P hP).appLE (coordOpen W i) ⊤ h).hom (c i j)) * P i = P j) ∧ ∀ i, Function.Surjective (MvPolynomial.eval₂Hom (((toSpec W).appLE ⊤ (coordOpen W i) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (c i)) := by
  intro R _ W
  let φ : ∀ i : Fin 3, Γ(scheme W, coordOpen W i) ⟶ CommRingCat.of (AwayRing W i) := fun i =>
    (awayChart W i).appLE (coordOpen W i) ⊤ (top_le_preimage W i) ≫ (Scheme.ΓSpecIso _).hom
  have hφ : ∀ i, Function.Bijective (φ i).hom := fun i => by
    have := isIso_appLE_of_opensRange (awayChart W i) _ (opensRange_awayChart W i)
      (top_le_preimage W i)
    have : IsIso (φ i) := by dsimp only [φ]; infer_instance
    exact ConcreteCategory.bijective_of_isIso (φ i)
  choose c hc using fun i j => (hφ i).2 (awayCoord W i j)
  refine ⟨c, ?_, ?_⟩
  · intro i j A _ ρ P hP h
    have hi : IsUnit (P i) := by
      rw [ptHom_preimage_coordOpen] at h
      have h1 : PrimeSpectrum.basicOpen (P i) = ⊤ := top_le_iff.mp h
      by_contra hn
      obtain ⟨m, hm, hx⟩ := exists_max_ideal_of_mem_nonunits hn
      have : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen (P i) := by
        rw [h1]; trivial
      exact this hx
    have e := appLE_SpecMap_comp (awayChart W i)
      (CommRingCat.ofHom (awayEval W i ρ P hP.equation hi)) (coordOpen W i)
      (top_le_preimage W i) _ (ptHom_eq_awayChart W i ρ P hP hi) h
    have e2 := congrArg (fun k => k.hom (c i j)) e
    have e3 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        (((ptHom W ρ P hP).appLE (coordOpen W i) ⊤ h).hom (c i j)) =
        awayEval W i ρ P hP.equation hi ((φ i).hom (c i j)) := e2
    rw [e3, hc, awayEval_awayCoord_mul]
  · intro i
    have e := appLE_structure (awayChart W i) (CommRingCat.ofHom (awayConst W i)) (coordOpen W i)
      (top_le_preimage W i) (toSpec W) (awayChart_toSpec W i)
    have key : (φ i).hom.comp (MvPolynomial.eval₂Hom
        (((toSpec W).appLE ⊤ (coordOpen W i) le_top).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (c i)) =
        MvPolynomial.eval₂Hom (awayConst W i) (awayCoord W i) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        exact congrArg (fun k => k.hom r) e
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', hc]
    intro y
    obtain ⟨p, hp⟩ := surjective_eval₂Hom_awayCoord W i ((φ i).hom y)
    exact ⟨p, (hφ i).1 ((RingHom.congr_fun key p).trans hp)⟩

end GlobalTheory.CoordFn
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SameZeroScheme

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom a = _
  rw [← X.presheaf.map_comp]
  rfl

theorem top_le_preimage {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro x _
  apply h
  have : hU.fromSpec (Spec.map φ x) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
  rw [hU.range_fromSpec] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
theorem appLE_spec {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) :
    (Spec.map φ ≫ hU.fromSpec).appLE V ⊤ (top_le_preimage hU h φ) =
      Y.presheaf.map (homOfLE h).op ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ V := by
    rw [← hU.fromSpec_preimage_self]
    exact fun x hx => h hx
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) hU.fromSpec V ⊤ ⊤ h1 le_top,
    Scheme.ΓSpecIso_inv_naturality]
  have e1 : hU.fromSpec.appLE V ⊤ h1 =
      Y.presheaf.map (homOfLE h).op ≫ (Scheme.ΓSpecIso Γ(Y, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_of_le V h, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    congr 1
  have e2 : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  rw [e1, e2, Category.assoc]

theorem dvd_on_affine {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    (a b : Γ(Y, V))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 → (t.appLE V ⊤ h).hom b = 0) :
    resG Y h a ∣ resG Y h b := by
  let I : Ideal Γ(Y, U) := Ideal.span {resG Y h a}
  let φ : Γ(Y, U) ⟶ CommRingCat.of (Γ(Y, U) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have key := H _ _ (top_le_preimage hU h φ)
  rw [appLE_spec hU h φ] at key
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).commRingCatIsoToRingEquiv.symm.injective
  have ha : Ideal.Quotient.mk I (resG Y h a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hb := key (by
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom
      (Ideal.Quotient.mk I (resG Y h a)) = 0
    rw [ha]; exact map_zero _)
  have hb' : Ideal.Quotient.mk I (resG Y h b) = 0 :=
    hinj (hb.trans (map_zero _).symm)
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb')

theorem exists_unit_mul (Y : Scheme.{0}) (V : Y.Opens) (a b : Γ(Y, V))
    (ha : ∀ (V' : Y.Opens) (h : V' ≤ V), resG Y h a ∈ nonZeroDivisors Γ(Y, V'))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 ↔ (t.appLE V ⊤ h).hom b = 0) :
    ∃ c : Γ(Y, V)ˣ, b = (c : Γ(Y, V)) * a := by
  let J := {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}
  let W : J → Y.Opens := fun i => i.1
  have hW : ∀ i, W i ≤ V := fun i => i.2.2
  have hcov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    exact ⟨⟨U, hU, hUV⟩, hyU⟩
  have hc : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 (hcov y hy)
  have hloc : ∀ i, ∃ c : Γ(Y, W i), IsUnit c ∧ resG Y (hW i) b = c * resG Y (hW i) a := fun i => by
    obtain ⟨c, hc⟩ := dvd_on_affine i.2.1 (hW i) a b fun T t h => (H T t h).1
    obtain ⟨d, hd⟩ := dvd_on_affine i.2.1 (hW i) b a fun T t h => (H T t h).2
    refine ⟨c, ?_, hc.trans (mul_comm _ _)⟩
    have e : (c * d) * resG Y (hW i) a = 1 * resG Y (hW i) a := by
      rw [_root_.one_mul]
      conv_rhs => rw [hd, hc]
      ring
    exact IsUnit.of_mul_eq_one d ((mul_cancel_right_mem_nonZeroDivisors (ha _ (hW i))).1 e)
  choose u hu hub using hloc
  have hh : ∀ i j, resG Y (inf_le_left : W i ⊓ W j ≤ W i) (u i) = resG Y inf_le_right (u j) := by
    intro i j
    have e₁ := congrArg (resG Y (inf_le_left : W i ⊓ W j ≤ W i)) (hub i)
    have e₂ := congrArg (resG Y (inf_le_right : W i ⊓ W j ≤ W j)) (hub j)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact (mul_cancel_right_mem_nonZeroDivisors (ha _ (inf_le_left.trans (hW i)))).1
      (e₁.symm.trans e₂)
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc u hh
  have hs' : ∀ i, resG Y (hW i) (show Γ(Y, V) from s) = u i := hs
  have hunit : IsUnit (show Γ(Y, V) from s) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ V _ fun y hy => by
      obtain ⟨i, hi⟩ := hcov y hy
      have h1 := (hu i).map (Y.presheaf.germ (W i) y hi).hom
      rw [← hs' i] at h1
      have h2 := Y.presheaf.germ_res_apply (homOfLE (hW i)) y hi (show Γ(Y, V) from s)
      exact h2 ▸ h1
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  apply Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
  intro i
  change resG Y (hW i) b = resG Y (hW i) ((show Γ(Y, V) from s) * a)
  rw [map_mul, hs', hub]

end GlobalTheory.SameZeroScheme
end
