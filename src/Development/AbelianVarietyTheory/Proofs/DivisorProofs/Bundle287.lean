module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle001
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

section

noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem isCompact_isIntV (G : HTGroup p) (v : AwayP p) :
    @IsCompact _ (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) {y | IsIntV G v y} := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  set b := basV G v
  have hc : Continuous b.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  have hbox : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank ℚ G.C) ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) :=
    isCompact_univ_pi fun _ ↦ LevelExists.isCompact_intCompl v.1
  have hset : {y | IsIntV G v y} = b.equivFun.symm '' (Set.univ.pi fun _ ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) := by
    rw [LinearEquiv.image_symm_eq_preimage]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Module.Basis.equivFun_apply]
    rfl
  rw [hset]
  exact hbox.image hc

theorem isCompact_IntV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), IsCompact (IntV G v) := by
  intro p _ G v
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
  have hPc := isCompact_isIntV G v
  have hOc := LevelExists.isCompact_intCompl v.1
  set P : Set (Qv v ⊗[ℚ] G.C) := {y | IsIntV G v y}
  set O : Set (Qv v) := (v.1.adicCompletionIntegers ℚ : Set (Qv v))
  have hσ : Continuous (fun y : Qv v ⊗[ℚ] G.C ↦ (starT G.star (Qv v) y).unop) := by
    let σl : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (Qv v) y).unop
        map_add' := fun x y ↦ by simp only [map_add (f := _), MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Qv v) (Qv v ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (Qv v) : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let g : Gv G v → ((Qv v ⊗[ℚ] G.C) × (Qv v ⊗[ℚ] G.C)ᵐᵒᵖ) × (Qv v × (Qv v)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hg : Topology.IsClosedEmbedding g :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal
  let K := (P ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' P)) ×ˢ (O ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' O))
  have hKC : IntV G v = g ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [hKC]
  exact hg.isCompact_preimage ((hPc.prod
    (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hPc)).prod
    (hOc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hOc)))

end GlobalTheory.OrbFinAf
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem bijective_linearCombination_iff_localizedModule_map {R R' S S' : Type} [CommRing R]
    [CommRing R'] [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S] [Algebra R' S']
    [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] (f : R)
    [IsLocalization.Away f R'] [IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) S']
    {r : ℕ} (v : Fin r → S) :
    Function.Bijective (Fintype.linearCombination R' (fun k => algebraMap S S' (v k))) ↔
      Function.Bijective (LocalizedModule.map (Submonoid.powers f) (Fintype.linearCombination R v)) := by
  let gM : (Fin r → R) →ₗ[R] (Fin r → R') :=
    LinearMap.pi (fun k => (Algebra.linearMap R R') ∘ₗ LinearMap.proj k)
  haveI : IsLocalizedModule (Submonoid.powers f) gM :=
    IsLocalizedModule.pi (Submonoid.powers f) (fun _ : Fin r => Algebra.linearMap R R')
  let gS : S →ₗ[R] S' := (IsScalarTower.toAlgHom R S S').toLinearMap
  haveI : IsLocalizedModule (Submonoid.powers f) gS := inferInstance
  let φ : (Fin r → R') →ₗ[R] S' :=
    (Fintype.linearCombination R' (fun k => algebraMap S S' (v k))).restrictScalars R
  have hcomm : φ ∘ₗ gM = gS ∘ₗ Fintype.linearCombination R v := by
    ext c

    simp [φ, gM, gS, Fintype.linearCombination_apply, Algebra.smul_def, map_sum, map_mul,
    ← IsScalarTower.algebraMap_apply]
  have hmap : IsLocalizedModule.map (Submonoid.powers f) gM gS (Fintype.linearCombination R v) = φ := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers f) gM gS
    rw [IsLocalizedModule.map_comp, hcomm]
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective gM gS, hmap]
  rfl

end GlobalTheory.HilbAff

namespace GlobalTheory.HilbAff

theorem coord_basicOpen_bijective_iff : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) (f : Γ(Z, W)),
    Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y (Z.basicOpen f)) ↔
      Function.Bijective (LocalizedModule.map (Submonoid.powers f) (GlobalTheory.HilbAff.coord A B e σ y W)) := by
  intro A B _ _ _ N r e σ Z y W f
  haveI : IsFinite (subStr A B y) := y.2.2.1
  have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage _
  have hle : subStr A B y ⁻¹ᵁ Z.basicOpen f ≤ subStr A B y ⁻¹ᵁ (W : Z.Opens) :=
    fun _ h => Z.basicOpen_le f h
  have hpre : subStr A B y ⁻¹ᵁ Z.basicOpen f =
      y.2.1.subscheme.basicOpen ((subStr A B y).app W f) := Scheme.preimage_basicOpen _ f
  letI i1 : Algebra Γ(Z, W) Γ(Z, Z.basicOpen f) :=
    (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom.toAlgebra
  letI i2 : Algebra (Sec A B y W) (Sec A B y (Z.basicOpen f)) :=
    (y.2.1.subscheme.presheaf.map (homOfLE hle).op).hom.toAlgebra
  letI i3 : Algebra Γ(Z, W) (Sec A B y (Z.basicOpen f)) :=
    ((algebraMap (Sec A B y W) (Sec A B y (Z.basicOpen f))).comp
      (algebraMap Γ(Z, W) (Sec A B y W))).toAlgebra
  haveI : IsScalarTower Γ(Z, W) (Sec A B y W) (Sec A B y (Z.basicOpen f)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Z, W) Γ(Z, Z.basicOpen f) (Sec A B y (Z.basicOpen f)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (congr($((subStr A B y).naturality (homOfLE (Z.basicOpen_le f)).op) a)).symm)
  haveI : IsLocalization.Away f Γ(Z, Z.basicOpen f) :=
    W.2.isLocalization_of_eq_basicOpen f (homOfLE (Z.basicOpen_le f)) rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (Sec A B y W) (Submonoid.powers f))
      (Sec A B y (Z.basicOpen f)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hV.isLocalization_of_eq_basicOpen _ (homOfLE hle) hpre
  have hgen : ∀ b, gen A B y (Z.basicOpen f) b =
      algebraMap (Sec A B y W) (Sec A B y (Z.basicOpen f)) (gen A B y W b) := by
    intro b
    have h := Scheme.Hom.appLE_map (y.2.1.subschemeι ≫ pullback.fst _ y.1) (U := ⊤)
      (V := subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp) (homOfLE hle).op
    simp only [gen]
    rw [← h]
    rfl
  have hc : coord A B e σ y (Z.basicOpen f) = Fintype.linearCombination Γ(Z, Z.basicOpen f)
      (fun k => algebraMap (Sec A B y W) (Sec A B y (Z.basicOpen f)) (gen A B y W (e (σ k)))) := by
    simp only [coord, hgen]
  rw [hc]
  exact bijective_linearCombination_iff_localizedModule_map f _

end GlobalTheory.HilbAff
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem bijective_appLE_of_image_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (V : X.Opens) (h : f ''ᵁ V = U) (e : V ≤ f ⁻¹ᵁ U) :
    Function.Bijective (f.appLE U V e).hom := by
  subst h
  have : f.appLE (f ''ᵁ V) V e = (f.appIso V).hom := (Scheme.Hom.appIso_hom' f V).symm
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _

theorem appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

theorem coord_restrict_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (U : Z.Opens) (W : U.toScheme.Opens),
    Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y (U.ι ''ᵁ W)) →
      Function.Bijective (GlobalTheory.HilbAff.coord A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) W) := by
  intro A B _ _ _ N r e σ Z y U W hb
  set a := U.ι with ha
  set y' := (functor A B r).map a.op y with hy'
  let f := bc A B y.1 a
  let J := y.2.1.comap f
  let φ : J.subscheme ⟶ y.2.1.subscheme := (y.2.1.comapIso f).hom ≫ pullback.snd f y.2.1.subschemeι
  have hbc_fst : f ≫ pullback.fst (str A B) y.1 = pullback.fst (str A B) (a ≫ y.1) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hbc_snd : f ≫ pullback.snd (str A B) y.1 = pullback.snd (str A B) (a ≫ y.1) ≫ a :=
    pullback.lift_snd _ _ _
  have hφι : φ ≫ y.2.1.subschemeι = J.subschemeι ≫ f := by
    simp only [φ, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have h1 : φ ≫ y.2.1.subschemeι ≫ pullback.fst _ y.1 = J.subschemeι ≫ pullback.fst _ (a ≫ y.1) := by
    rw [reassoc_of% hφι, hbc_fst]
  have h2 : φ ≫ y.2.1.subschemeι ≫ pullback.snd _ y.1 = (J.subschemeι ≫ pullback.snd _ (a ≫ y.1)) ≫ a := by
    rw [reassoc_of% hφι, hbc_snd, Category.assoc]
  have H : IsPullback (pullback.snd f y.2.1.subschemeι)
      (pullback.fst f y.2.1.subschemeι ≫ pullback.snd _ (a ≫ y.1))
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) a :=
    (IsPullback.of_hasPullback f y.2.1.subschemeι).flip.paste_vert (isPullback_bc A B y.1 a)
  have hpb : IsPullback (J.subschemeι ≫ pullback.snd _ (a ≫ y.1)) φ a
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) :=
    H.flip.of_iso (y.2.1.comapIso f).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
        Scheme.IdealSheafData.comapIso_inv_subschemeι])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; dsimp only [φ]; rw [Iso.inv_hom_id_assoc])
      (by simp) (by simp)
  haveI : IsOpenImmersion f :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bc A B y.1 a).flip
      (inferInstanceAs (IsOpenImmersion U.ι))
  haveI : IsOpenImmersion φ := by dsimp only [φ]; infer_instance
  set X0 := a ''ᵁ W with hX0
  have hX : φ ''ᵁ ((subStr A B y') ⁻¹ᵁ W) = (subStr A B y) ⁻¹ᵁ X0 :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback hpb W
  have hle : (subStr A B y') ⁻¹ᵁ W ≤ φ ⁻¹ᵁ ((subStr A B y) ⁻¹ᵁ X0) := by
    rw [← hX]; exact (Scheme.Hom.preimage_image_eq φ _).ge
  have hW : W ≤ a ⁻¹ᵁ X0 := (Scheme.Hom.preimage_image_eq a W).ge
  let β := φ.appLE _ _ hle
  let α := a.appLE X0 W hW
  have hβ : Function.Bijective β.hom := bijective_appLE_of_image_eq φ _ _ hX hle
  have hα : Function.Bijective α.hom := bijective_appLE_of_image_eq a _ _ rfl hW
  have hAm : (subStr A B y).app X0 ≫ β = α ≫ (subStr A B y').app W := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((appLE_congr_hom h2 _ _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
  have hA : ∀ x, β.hom (algebraMap Γ(Z, X0) (Sec A B y X0) x) =
      algebraMap Γ(U.toScheme, W) (Sec A B y' W) (α.hom x) := by
    intro x
    change ((subStr A B y).app X0 ≫ β).hom x = (α ≫ (subStr A B y').app W).hom x
    rw [hAm]; rfl
  have hG : ∀ b, β.hom (gen A B y X0 b) = gen A B y' W b := by
    intro b
    change ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ _ _ ≫ β).hom _ =
      ((J.subschemeι ≫ pullback.fst _ (a ≫ y.1)).appLE ⊤ _ _).hom _
    have hGm : (y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ X0) (by simp) ≫ β =
        (J.subschemeι ≫ pullback.fst _ (a ≫ y.1)).appLE ⊤ (subStr A B y' ⁻¹ᵁ W) (by simp) :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_congr_hom h1 _ _ _ _)
    rw [hGm]; rfl
  have hc : ∀ c : Fin r → Γ(Z, X0), β.hom (coord A B e σ y X0 c) =
      coord A B e σ y' W (fun k => α.hom (c k)) := by
    intro c
    rw [coord, coord, Fintype.linearCombination_apply, Fintype.linearCombination_apply]
    simp only [Algebra.smul_def]
    erw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    erw [map_mul, hA, hG]
    rfl
  have hαe : Function.Bijective (fun c : Fin r → Γ(Z, X0) => fun k => α.hom (c k)) :=
    hα.comp_left
  have hcomp : (coord A B e σ y' W) ∘ (fun c : Fin r → Γ(Z, X0) => fun k => α.hom (c k)) =
      β.hom ∘ (coord A B e σ y X0) := by
    funext c; exact (hc c).symm
  rw [← Function.Bijective.of_comp_iff _ hαe, hcomp]
  exact hβ.comp hb

end GlobalTheory.HilbAff
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem span_gen_eq_top (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (functor A B r).obj (op Z))
    (W : Z.affineOpens) :
    Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) = ⊤ := by
  have sq : IsPullback (pullback.fst (str A B) y.1) (pullback.snd (str A B) y.1) (str A B) y.1 :=
    IsPullback.of_hasPullback _ _
  haveI : IsAffineHom (pullback.snd (str A B) y.1) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback sq inferInstance
  have hpo := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) W.2
    (by simp) (by simp)
  have hQ : IsAffineOpen (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage _
  have hsurj := y.2.1.subschemeι_app_surjective ⟨_, hQ⟩
  let R := Γ(Spec (CommRingCat.of A), ⊤)
  let S := Γ(Spec (CommRingCat.of B), ⊤)
  let T := Γ(Z, (W : Z.Opens))
  let Q := Γ(pullback (str A B) y.1, pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))
  letI : Algebra R S := (show R ⟶ S from (str A B).app ⊤).hom.toAlgebra
  letI : Algebra R T := (y.1.appLE ⊤ W (by simp)).hom.toAlgebra
  letI : Algebra T Q := ((pullback.snd (str A B) y.1).app W).hom.toAlgebra
  letI : Algebra S Q :=
    (show S ⟶ Q from (pullback.fst (str A B) y.1).appLE (str A B ⁻¹ᵁ ⊤) _ (by simp)).hom.toAlgebra
  letI : Algebra R Q :=
    ((y.1.appLE ⊤ W (by simp)) ≫ (pullback.snd (str A B) y.1).app W).hom.toAlgebra
  haveI : IsScalarTower R T Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq (fun x => by
    have h := congr($(hpo.w).hom x)
    exact h.symm)
  haveI : Algebra.IsPushout R T S Q := (CommRingCat.isPushout_iff_isPushout).mp hpo.flip
  have hbc := Algebra.IsPushout.out (R := R) (S := T) (R' := S) (S' := Q)

  have key : ∀ s : S, (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom
      (algebraMap S Q s) = ((y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp)).hom s := by
    intro s
    have h : (Scheme.Hom.appLE (pullback.fst (str A B) y.fst) (str A B ⁻¹ᵁ ⊤)
      (pullback.snd (str A B) y.fst ⁻¹ᵁ ↑W) (by simp)) ≫ y.2.1.subschemeι.app _ =
        (y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => (CommRingCat.Hom.hom f) s) h
  have hι : ∀ (t : T) (n : Q), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (t • n) =
      t • (show Sec A B y W from
        (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom n) := by
    intro t n
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
  have term : ∀ (c : A) (j : Fin N), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c * e j))) =
      (algebraMap R T ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c)) • gen A B y W (e j) := by
    intro c j
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c) =
        algebraMap R S ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c) :=
      congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))).hom c)
    rw [map_mul, h1, map_mul, ← IsScalarTower.algebraMap_apply R S Q,
      IsScalarTower.algebraMap_apply R T Q, ← Algebra.smul_def, hι, key]
    rfl
  have hB : ∀ b : B, (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b))) ∈
      Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) := by
    intro b

    rw [← e.sum_repr b, map_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def, term]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨q, rfl⟩ := hsurj x
  refine hbc.inductionOn q (motive := fun q => (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom q) ∈ Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)))
    ?_ ?_ ?_
  · intro s
    obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b = s :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s, by simp⟩
    exact hB b
  · intro t n hn
    rw [hι]
    exact Submodule.smul_mem _ _ hn
  · intro a b ha hb
    rw [map_add (f := _)]
    exact add_mem ha hb

end GlobalTheory.HilbAff
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

theorem isPullback_fromSpec_app_rank {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV]) (by simp)).flip

theorem rankAtStalk_sec (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)) (W : Z.affineOpens)
    (P : PrimeSpectrum Γ(Z, W)) : Module.rankAtStalk (Sec A B y W) P = r := by
  obtain ⟨_hfin, _hflat, h3⟩ := y.2.2
  have hW : IsAffineOpen (W : Z.Opens) := W.2
  have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := hW.preimage _
  haveI : Module.Finite Γ(Z, W) (Sec A B y W) := by
    have := IsFinite.finite_app (subStr A B y) (W : Z.Opens) hW
    exact this
  haveI : Module.Flat Γ(Z, W) (Sec A B y W) := by
    have := Scheme.Hom.flat_appLE (subStr A B y) hW hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at this
    exact this
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec_app_rank (subStr A B y) hW hV) P
  rw [h3] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end GlobalTheory.HilbAff
end
end

section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem charZero_stalk_genPt : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    (letI := GlobalTheory.NormSheafDescent.fieldK π hK
     CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  intro Y Z π _ hY hK
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom) (Y.germToFunctionField_injective ⊤)
  have h0 : CharZero (Z.presheaf.stalk (genPt π)) := (π.stalkMap (genericPoint Y)).hom.charZero
  exact h0

end GlobalTheory.NormSheafDescent
end
