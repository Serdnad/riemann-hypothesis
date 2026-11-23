module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem ratFunc_C_laurent (F : Type) [Field F] : (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C =
    (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  ext1 a
  have h := (RatFunc.coe_coe (Polynomial.C a)).symm
  rw [Polynomial.coe_C] at h
  exact h

theorem sqr_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : sqr G' ≫ φ = φ ≫ sqr G := by
  let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e := h.2 G' (𝟙 G') (𝟙 G') x₀ x₀ rfl rfl
  have e2 : x₀ * x₀ = x₀ ≫ (𝟙 G * 𝟙 G) := by rw [comp_mul]; simp
  rw [e2] at e
  exact e.symm

theorem ratRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω]
    (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  intro S G _ Ω _ _ b hR ξ hξ ⟨β, hβ⟩
  have hp := isGrpPullback_pullback G b
  have hu : unitSec ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = b ≫ unitSec G := unitSec_comp hp
  have hs : sqr ((Over.pullback b).obj G) ≫ pullback.fst G.hom b = pullback.fst G.hom b ≫ sqr G :=
    sqr_comp_of_isGrpPullback hp
  have hsh : sqr ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = pullback.snd G.hom b :=
    Over.w (𝟙 ((Over.pullback b).obj G) * 𝟙 ((Over.pullback b).obj G))
  have hus : unitSec ((Over.pullback b).obj G) ≫ pullback.snd G.hom b = 𝟙 _ := sec_hom _
  let ξ' : Sp (PowerSeries Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift ξ (spMap PowerSeries.C) hξ.base
  have hξ₁ : ξ' ≫ pullback.fst G.hom b = ξ := pullback.lift_fst _ _ _
  have hξ₂ : ξ' ≫ pullback.snd G.hom b = spMap PowerSeries.C := pullback.lift_snd _ _ _
  have hsp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hpath : IsPath ((Over.pullback b).obj G) 2 (𝟙 (Sp Ω)) ξ' := by
    refine ⟨?_, ?_, ?_⟩
    · exact hξ₂.trans (Category.comp_id _).symm
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, hξ.zero, Category.assoc, hu, Category.id_comp]
      · rw [Category.assoc, hξ₂, Category.assoc, hus, Category.id_comp, hsp]
        have : (PowerSeries.constantCoeff (R := Ω)).comp PowerSeries.C = RingHom.id Ω := by
          ext a; simp
        rw [this]
        show Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = _
        rw [CommRingCat.ofHom_id, Spec.map_id]
    · apply pullback.hom_ext
      · rw [Category.assoc, hξ₁, Category.assoc, hs, ← Category.assoc, hξ₁, hξ.scale]
      · rw [Category.assoc, hξ₂, Category.assoc, hsh, hξ₂, hsp]
        have : (PowerSeries.rescale (2 : Ω)).comp PowerSeries.C = PowerSeries.C := by
          ext1 a; ext n; rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
          rcases n with _ | n <;> simp
        rw [this]
  have hβb : β ≫ G.hom = spMap RatFunc.C ≫ b := by
    have cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    apply cancel (algebraMap (RatFunc Ω) (LaurentSeries Ω))
    rw [← Category.assoc, hβ, Category.assoc, hξ.base, ← Category.assoc, ← Category.assoc, hsp, hsp,
      ratFunc_C_laurent]
  let β' : Sp (RatFunc Ω) ⟶ ((Over.pullback b).obj G).left := pullback.lift β (spMap RatFunc.C) hβb
  have hrat : IsRatPath ξ' := by
    refine ⟨β', ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hξ₁, hβ]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hξ₂, hsp, hsp, ratFunc_C_laurent]
  have e := hR ξ' hpath hrat
  rw [← hξ₁, e]
  simp only [triv, Category.assoc, hu, Category.id_comp]

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

noncomputable section

namespace GlobalTheory.Nef

theorem exists_stalk_fac {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X)
    (h : f (IsLocalRing.closedPoint R) = x) :
    ∃ φ : X.presheaf.stalk x ⟶ R, Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst h
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem exists_stalk_map {X Y : Scheme.{0}} (x : X) (g : X ⟶ Y) (y : Y) (hy : g x = y) :
    ∃ φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x, Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ g := by
  subst hy
  exact exists_stalk_fac (g x) (X.fromSpecStalk x ≫ g) (congrArg (fun z => g z) Scheme.fromSpecStalk_closedPoint)

theorem stalk_hom_eq {X : Scheme.{0}} (x : X) {R : CommRingCat.{0}} (φ ψ : X.presheaf.stalk x ⟶ R)
    (h : Spec.map φ ≫ X.fromSpecStalk x = Spec.map ψ ≫ X.fromSpecStalk x) : φ = ψ :=
  Spec.map_injective ((cancel_mono (X.fromSpecStalk x)).1 h)

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem unitSec_sqr : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h2 : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id, ← Hom.mul_def, ← h1, _root_.one_mul]
  change η[G].left ≫ (𝟙 G * 𝟙 G : G ⟶ G).left = η[G].left
  rw [← Over.comp_left, h2]

theorem sqr_hom : sqr G ≫ G.hom = G.hom := Over.w _

end

theorem stalkData_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ s : S, ∃ π ε m,
    StalkData G s π ε m ∧ ε.comp π = RingHom.id _ ∧ m.comp π = π ∧ ε.comp m = ε := by
  intro S G _ s
  obtain ⟨π, hπ⟩ := exists_stalk_map (unitSec G s) G.hom s (by
    rw [← Scheme.Hom.comp_apply, sec_hom]; rfl)
  obtain ⟨ε, hε⟩ := exists_stalk_map s (unitSec G) (unitSec G s) rfl
  obtain ⟨m, hm⟩ := exists_stalk_map (unitSec G s) (sqr G) (unitSec G s) (by
    rw [← Scheme.Hom.comp_apply, unitSec_sqr])
  refine ⟨π.hom, ε.hom, m.hom, ⟨hπ, hε, hm⟩, ?_, ?_, ?_⟩
  · have : π ≫ ε = 𝟙 _ := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hε, Category.assoc, sec_hom,
        Category.comp_id, Spec.map_id, Category.id_comp])
    exact congrArg CommRingCat.Hom.hom this
  · have : π ≫ m = π := stalk_hom_eq s _ _ (by
      rw [Spec.map_comp, Category.assoc, hπ, ← Category.assoc, hm, Category.assoc, sqr_hom])
    exact congrArg CommRingCat.Hom.hom this
  · have : m ≫ ε = ε := stalk_hom_eq (unitSec G s) _ _ (by
      rw [Spec.map_comp, Category.assoc, hm, ← Category.assoc, hε, Category.assoc, unitSec_sqr])
    exact congrArg CommRingCat.Hom.hom this

end GlobalTheory.Nef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem stalk_formallySmooth_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → π.FormallySmooth := by
  intro S G _ hG s π ε m h
  have hstr := h.str
  clear h
  revert π hstr
  have hs : G.hom.base (unitSec G s) = s := by
    rw [← Scheme.Hom.comp_apply, unitSec, sec_hom]
    rfl
  generalize unitSec G s = p at hs ⊢
  subst hs
  intro π hstr
  have e : Spec.map (CommRingCat.ofHom π) = Spec.map (G.hom.stalkMap p) :=
    (cancel_mono (S.fromSpecStalk (G.hom.base p))).1 (by
      rw [hstr, Scheme.SpecMap_stalkMap_fromSpecStalk])
  have e' : π = (G.hom.stalkMap p).hom := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e']
  exact Scheme.Hom.mem_smoothLocus.mp (G.hom.smoothLocus_eq_top.ge (Set.mem_univ p))

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem fromSpecStalk_preimage_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_preimage_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {g g' : X ⟶ Y} (hg : g = g') (V : Y.Opens) (W : X.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W h = g'.appLE V W h' := by
  subst hg; rfl

theorem germ_comp_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) :
    Y.presheaf.germ V y hy ≫ φ = f.appLE V U h ≫ X.presheaf.germ U x hx := by
  have h1 : ⊤ ≤ (Spec.map φ ≫ Y.fromSpecStalk y) ⁻¹ᵁ V := by
    intro z _
    exact fromSpecStalk_preimage_top y V hy (Set.mem_univ _)
  have h2 : ⊤ ≤ (X.fromSpecStalk x ≫ f) ⁻¹ᵁ V := hφ ▸ h1
  have key := appLE_eq_of_eq hφ V ⊤ h1 h2
  have eL : (Spec.map φ ≫ Y.fromSpecStalk y).appLE V ⊤ h1 =
      (Y.fromSpecStalk y).appLE V ⊤ (fromSpecStalk_preimage_top y V hy) ≫
        (Spec.map φ).appLE ⊤ ⊤ (by simp) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eR : (X.fromSpecStalk x ≫ f).appLE V ⊤ h2 =
      f.appLE V U h ≫ (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eT : (Spec.map φ).appLE ⊤ ⊤ (by simp) = (Spec.map φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top, Category.comp_id]
    first | rfl | simp
  rw [eL, eR, eT, fromSpecStalk_appLE_top y V hy, fromSpecStalk_appLE_top x U hx, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc] at key
  exact (cancel_mono _).1 key

theorem germ_apply_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    φ (Y.presheaf.germ V y hy a) = X.presheaf.germ U x hx (f.appLE V U h a) := by
  have e := congrArg (fun g => g.hom a) (germ_comp_of_spec (CommRingCat.ofHom φ) f hφ V hy U hx h)
  exact e

theorem stalkData_germ : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → (∀ (V : S.Opens) (hs : s ∈ V) (U : G.left.Opens) (hU : unitSec G s ∈ U) (h : U ≤ G.hom ⁻¹ᵁ V) (a : Γ(S, V)), π (S.presheaf.germ V s hs a) = G.left.presheaf.germ U _ hU (G.hom.appLE V U h a)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V : S.Opens) (hs : s ∈ V) (h : V ≤ unitSec G ⁻¹ᵁ U) (f : Γ(G.left, U)), ε (G.left.presheaf.germ U _ hU f) = S.presheaf.germ V s hs ((unitSec G).appLE U V h f)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (U' : G.left.Opens) (hU' : unitSec G s ∈ U') (h : U' ≤ sqr G ⁻¹ᵁ U) (f : Γ(G.left, U)), m (G.left.presheaf.germ U _ hU f) = G.left.presheaf.germ U' _ hU' ((sqr G).appLE U U' h f)) := by
  intro S G _ s π ε m hD
  exact ⟨fun V hs U hU h a => germ_apply_of_spec π G.hom hD.str V hs U hU h a,
    fun U hU V hs h f => germ_apply_of_spec ε (unitSec G) hD.unit U hU V hs h f,
    fun U hU U' hU' h f => germ_apply_of_spec m (sqr G) hD.sq U hU U' hU' h f⟩

end GlobalTheory.Nef
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem parCoc_isCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (K : Type) (W : K → (A ⊗ B).left.Opens) (J : Type) [Fintype J] (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → (∀ i, IsCoc (whole B) (b i)) → IsCupCob W a b n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsCoc (parCov W x) (parCoc a b n x) := by
  intro R _ A B K W J _ a b n ha hb hn D _ _ x
  unfold IsCoc at ha hb ⊢
  unfold IsCupCob at hn
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have hz' : Sm W (z ≫ x ▷ B) := by
    unfold Sm at hz ⊢
    obtain ⟨k, hk⟩ := hz
    refine ⟨k, ?_⟩
    simpa [parCov, Over.comp_left, Scheme.Hom.comp_preimage] using hk
  have h1 := hn E E' E'' φ ψ (z ≫ x ▷ B) hz'
  have hfst : (z ≫ x ▷ B) ≫ fst _ _ = spOver (ptAlg (z ≫ fst _ _)) ≫ x := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc, spOver_ptAlg]
  have hα : ptAlg ((spOver φ ≫ z) ≫ fst _ _) = φ.comp (ptAlg (z ≫ fst _ _)) := by
    rw [Category.assoc, ptAlg_comp]
  have ha' := fun i ↦ ha i D E E' (ptAlg (z ≫ fst _ _)) φ x (sm_whole _)
  have hb' := fun i ↦ hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
  rw [hfst] at h1
  simp only [Category.assoc, whiskerRight_snd] at h1
  simp only [parCoc]
  rw [hα]
  simp only [ha', hb', Category.assoc]

  simp only [map_sub, map_sum, map_mul, map_add (f := _), AlgHom.comp_apply, add_mul, mul_add, Finset.sum_add_distrib]
  linear_combination -h1

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem parCoc_spOver (R : Type) [CommRing R] (A B : Over (Sp R)) (J : Type) [Fintype J]
    (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (ha : ∀ i, IsCoc (whole A) (a i))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) :
    parCoc (D := D') a b n (spOver φ ≫ x) =
      ((parCoc (D := D) a b n x).pull (spOver φ ▷ B)).add
        (sumMul (D := D') (fun i ↦ a i D D' φ x) b) := by
  funext E _ _ E' _ _ ψ z
  simp only [parCoc, Fn1.pull, Fn1.add, sumMul]
  have h1 : z ≫ (spOver φ ≫ x) ▷ B = (z ≫ spOver φ ▷ B) ≫ x ▷ B := by
    rw [comp_whiskerRight, Category.assoc]
  have h2 : (z ≫ spOver φ ▷ B) ≫ snd _ _ = z ≫ snd _ _ := by
    rw [Category.assoc, whiskerRight_snd]
  have h3 : ptAlg ((z ≫ spOver φ ▷ B) ≫ fst _ _) =
      (ptAlg (z ≫ fst (SpAlg R D') B)).comp φ := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc]
    conv_lhs => rw [← spOver_ptAlg (z ≫ fst (SpAlg R D') B)]
    rw [spOver_comp, ptAlg_spOver]
  rw [h1, h2, h3]
  have hc : ∀ i, a i D E ((ptAlg (z ≫ fst _ _)).comp φ) x =
      ptAlg (z ≫ fst _ _) (a i D D' φ x) + a i D' E (ptAlg (z ≫ fst _ _)) (spOver φ ≫ x) :=
    fun i ↦ ha i D D' E φ _ x (sm_whole x)
  simp only [hc, map_add (f := _), add_mul, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (x : T ⟶ A) (m : ℕ) : ρ ≫ x ^ m = (ρ ≫ x) ^ m :=
  MonObj.comp_pow x m ρ

theorem chi_eq_of_torsion : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ g : Fn2 A, IsSecAdd n S g →
    ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb S hS g hg D _ _ x hx
  obtain ⟨E, _, _, ψ, z, hff, hz⟩ := hR D x
  apply hff.injective
  change ψ (chi n g D x) = ψ (b D x)
  have hpow : ∀ i : ℕ, (z ^ i) ^ n = spOver ψ ≫ x ^ i := by
    intro i
    rw [← pow_mul, mul_comm, pow_mul, hz, comp_pow_pt]

  have hterm : ∀ i : ℕ, ψ (g D (x ^ i) x) =
      (S D (x ^ (i + 1)) E ψ (z ^ (i + 1)) - S D (x ^ i) E ψ (z ^ i)) - S D x E ψ z := by
    intro i
    have h := hg D (x ^ i) x E ψ (z ^ i) z (hpow i) hz
    rw [← pow_succ, ← pow_succ] at h
    rw [h]
  have hnE : (n : E) = 0 := by
    rw [← map_natCast (algebraMap R E), hn, map_zero]
  have hsum : ψ (chi n g D x) = S D (x ^ n) E ψ (z ^ n) - S D (x ^ 0) E ψ (z ^ 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [chi, map_sum, hterm, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ S D (x ^ i) E ψ (z ^ i)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnE, zero_mul, sub_zero]
  rw [hsum, hx, pow_zero, pow_zero]

  have h1 : (1 : Pt A E) ^ n = spOver ψ ≫ (1 : Pt A D) := by rw [one_pow, MonObj.comp_one]
  have h2 : (z ^ n) ^ n = 1 := by rw [hpow n, hx, MonObj.comp_one]
  have hs := (hS D 1).2 E ψ 1 (z ^ n) h1 h2
  rw [_root_.one_mul] at hs
  rw [hs, add_sub_cancel_left, hz]
  exact hb.1 D E ψ x hx

end GlobalTheory.PtExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem ev_triv_congr {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 (O (dp0 R) s))
    {D D' : Type} [CommRing D] [CommRing D'] (i j : Algebra R D) (i' j' : Algebra R D') (hi : i = j) (hi' : i' = j')
    (x : Sp D ⟶ X) (x₁ x₂ : Sp D' ⟶ X) (hx₁ : x₁ = x₂)
    (hx : x ≫ s = spMap (@algebraMap R D _ _ i)) (hxj : x ≫ s = spMap (@algebraMap R D _ _ j))
    (hx' : x₁ ≫ s = spMap (@algebraMap R D' _ _ i')) (hxj' : x₂ ≫ s = spMap (@algebraMap R D' _ _ j'))
    (a : @Thick.triv R _ X s D _ i x hx ⟶ @Thick.triv R _ X s D' _ i' x₁ hx')
    (b : @Thick.triv R _ X s D _ j x hxj ⟶ @Thick.triv R _ X s D' _ j' x₂ hxj')
    (h : ∀ r, a.φ r = b.φ r) : ev f a = ev f b := by
  subst hi hi' hx₁
  have : a = b := Thick.Hom.ext' (AlgHom.ext h)
  subst this
  rfl

theorem ev_functor_map_trivMap {R : Type} [CommRing R] {X Y : Over (Sp R)} (q : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [j : Algebra R D] (D' : Type) [CommRing D']
    [j' : Algebra R D'] (φ : D →ₐ[R] D') (y : Pt Y D) :
    ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q)) := by
  let y' : Pt Y D' := spOver φ ≫ y
  have h : (y' ≫ q).left = (spOver φ ≫ y ≫ q).left :=
    congrArg (fun p : Pt X D' ↦ p.left) (Category.assoc (spOver φ) y q)
  exact ev_triv_congr f (((algebraMap R D).comp (RingHom.id R)).toAlgebra) j
    (((algebraMap R D').comp (RingHom.id R)).toAlgebra) j' (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    (Algebra.algebra_ext _ _ fun _ ↦ rfl) (y ≫ q).left (y' ≫ q).left
    (spOver φ ≫ y ≫ q).left h (m.obj (trivAt y)).w (Pt.w (y ≫ q))
    (m.obj (trivAt y')).w (Pt.w (spOver φ ≫ y ≫ q))
    (m.functor.map (trivMap φ y)) (trivMap φ (y ≫ q)) fun _ ↦ rfl

theorem fv_pullbackOneCocycle_eq_pull : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (q : Y ⟶ X) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = (fv f).pull q := by
  intro R _ X Y q m f
  funext D _ _ D' _ _ φ y
  change ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q))
  exact ev_functor_map_trivMap q m f D D' φ y

end GlobalTheory.PtExt
end
end
