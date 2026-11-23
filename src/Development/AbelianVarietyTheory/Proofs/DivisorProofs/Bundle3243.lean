module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_residue_apply_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (w : Sp (ResidueField R)) :
    spMap (residue R) w = closedPoint R :=
  IsLocalRing.PrimeSpectrum.comap_residue _ _

theorem pullbackLeftPullbackSnd_congr_fst {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.fst f g'' =
      pullback.fst _ _ ≫ pullback.fst f g := by
  subst hg
  simp [pullback.map]

theorem pullbackLeftPullbackSnd_congr_snd {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.snd f g'' = pullback.snd _ _ := by
  subst hg
  simp [pullback.map]

theorem Emb.pullback_iso_of_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (hG : Smooth G'.hom) (E : Emb π G') (T : Scheme.{0}) (t : T ⟶ S)
    (k : T ⟶ Sp (ResidueField R)) (_hT : IsLocallyNoetherian T) (hTr : IsReduced T)
    (htk : t ≫ π = k ≫ spMap (residue R)) :
    ∃ (e : pullback G'.hom t ≅ pullback E.Y.hom k) (l : pullback G'.hom t ⟶ E.H.toScheme),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ l ≫ E.H.ι = pullback.fst _ _ ∧
      l ≫ E.f = e.hom ≫ pullback.fst _ _ ≫ E.j := by
  haveI := hG
  haveI : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  haveI : IsImmersion E.j := E.imm
  haveI : Smooth E.Y.hom := E.smooth
  have hclosed : ∀ w : (pullback G'.hom t : Scheme.{0}), π (G'.hom (pullback.fst G'.hom t w)) = closedPoint R := by
    intro w
    have h1 : π (G'.hom (pullback.fst G'.hom t w)) = (pullback.fst G'.hom t ≫ G'.hom ≫ π) w := by simp
    rw [h1, pullback.condition_assoc, htk]
    simp only [Scheme.Hom.comp_apply]
    exact spMap_residue_apply_eq_closedPoint R _
  have hrng : Set.range (pullback.fst G'.hom t) ⊆ Set.range E.H.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact E.H_all _ (hclosed w)
  let l : pullback G'.hom t ⟶ E.H.toScheme := IsOpenImmersion.lift E.H.ι (pullback.fst G'.hom t) hrng
  have hl : l ≫ E.H.ι = pullback.fst G'.hom t := IsOpenImmersion.lift_fac _ _ _
  haveI : IsReduced (pullback G'.hom t) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G'.hom t)
  have hrj : Set.range (l ≫ E.f) ⊆ Set.range E.j := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R S π G' E).1 (l w) (by
      have e1 : E.H.ι (l w) = pullback.fst G'.hom t w := by rw [← Scheme.Hom.comp_apply, hl]
      rw [e1]; exact hclosed w)
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_isImmersion_range _ _ _ (l ≫ E.f) E.j inferInstance E.imm hrj
  have hgY : g ≫ E.Y.hom = pullback.snd G'.hom t ≫ k := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, reassoc_of% hg, E.f_over,
      reassoc_of% hl, pullback.condition_assoc, htk, Category.assoc]
  let h : pullback G'.hom t ⟶ pullback E.Y.hom k := pullback.lift g (pullback.snd G'.hom t) hgY
  have hh : h ≫ pullback.snd E.Y.hom k = pullback.snd G'.hom t := pullback.lift_snd _ _ _
  have hhf : h ≫ pullback.fst E.Y.hom k = g := pullback.lift_fst _ _ _
  haveI : IsIso h := by
    refine GlobalTheory.T.isIso_of_isIso_on_geometric_fibres_of_smooth T _ _ (pullback.snd G'.hom t) (pullback.snd E.Y.hom k) h hh inferInstance inferInstance ?_
    intro s
    let Ω := T.residueField s
    let x0 : Sp Ω ⟶ T := T.fromSpecResidueField s
    have hx : ∀ w, (x0 ≫ t ≫ π) w = closedPoint R := by
      intro w
      rw [htk]
      simp only [Scheme.Hom.comp_apply]
      exact spMap_residue_apply_eq_closedPoint R _
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x0 ≫ t ≫ π) hx
    have hκk : x0 ≫ k = spMap κ := by
      rw [← cancel_mono (spMap (residue R)), Category.assoc, ← htk, hκ]
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨Ω', _, io, e', l', -, hl1, hl2⟩ := E.fib Ω (x0 ≫ t) κ (by rw [Category.assoc]; exact hκ)
    let x : Sp Ω' ⟶ T := spMap io ≫ x0
    refine ⟨Ω', inferInstance, x, ?_, ?_⟩
    · let w : Sp Ω' := closedPoint Ω'
      refine ⟨w, ?_⟩
      show (spMap io ≫ T.fromSpecResidueField s) w = s
      rw [Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    · have hxk : x ≫ k = spMap (io.comp κ) := by
        simp only [x, Category.assoc, hκk, spMap, ← Spec.map_comp]
        rfl
      let α : pullback (pullback.snd G'.hom t) x ≅ pullback G'.hom (spMap io ≫ x0 ≫ t) :=
        pullbackLeftPullbackSndIso G'.hom t x ≪≫ pullback.congrHom rfl (Category.assoc _ _ _)
      let β : pullback (pullback.snd E.Y.hom k) x ≅ pullback E.Y.hom (spMap (io.comp κ)) :=
        pullbackLeftPullbackSndIso E.Y.hom k x ≪≫ pullback.congrHom rfl hxk
      have hα : α.hom ≫ pullback.fst G'.hom (spMap io ≫ x0 ≫ t) =
          pullback.fst (pullback.snd G'.hom t) x ≫ pullback.fst G'.hom t :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hαs : α.hom ≫ pullback.snd G'.hom (spMap io ≫ x0 ≫ t) = pullback.snd (pullback.snd G'.hom t) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hβ : β.hom ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) =
          pullback.fst (pullback.snd E.Y.hom k) x ≫ pullback.fst E.Y.hom k :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hβs : β.hom ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd (pullback.snd E.Y.hom k) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hll : pullback.fst (pullback.snd G'.hom t) x ≫ l = α.hom ≫ l' := by
        rw [← cancel_mono E.H.ι, Category.assoc, Category.assoc, hl, hl1, hα]
      have he's : e'.hom.left ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd G'.hom (spMap io ≫ x0 ≫ t) :=
        Over.w e'.hom
      let eb := α ≪≫ (Over.forget _).mapIso e' ≪≫ β.symm
      have key0 : ∀ φ : pullback (pullback.snd G'.hom t) x ⟶ pullback (pullback.snd E.Y.hom k) x,
          φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h → φ ≫ pullback.snd _ _ = pullback.snd _ _ → φ = eb.hom := by
        intro φ hφ hφs
        have heb : eb.hom = α.hom ≫ e'.hom.left ≫ β.inv := rfl
        rw [heb, ← Category.assoc, Iso.eq_comp_inv]
        apply pullback.hom_ext
        · rw [← cancel_mono E.j, Category.assoc, Category.assoc, reassoc_of% hβ, Category.assoc, Category.assoc,
            ← hl2, ← reassoc_of% hll, reassoc_of% hφ, reassoc_of% hhf, hg]
        · rw [Category.assoc, Category.assoc, hβs, he's, hαs, hφs]
      rw [key0 (pullback.map _ x _ x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))]
      infer_instance
  exact ⟨asIso h, l, hh, hl, by rw [asIso_hom, reassoc_of% hhf, hg]⟩

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.SharpExt

theorem spMap_comp_ext {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_refined_ext_lift : ∀ g n : ℕ, ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ (Y : Scheme.{0}) (q : Y ⟶ F.X), IsFinite q → Surjective q → ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X) (y : Sp (FractionRing V₁) ⟶ F.X) (y' : Sp (FractionRing V₁) ⟶ Y), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Refines Q ρ D₀.toPre e₀ ∧ y ≫ i = jK V₁ ≫ spMap ρ ≫ ξ ∧ y' ≫ q = y := by
  intro g n F Z i W hW V _ _ _ Q m t δ hrk ht hsym hnn hpos hmono ξ hU Y q hq hs
  obtain ⟨V₀, _, _, _, ρ₀, r, D₀, e₀, hCN₀, hinj₀, hfin₀, -, -, hRef₀, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised V Q m t δ hU.1 hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hpos
  obtain ⟨G', _, _, A', U', y₀, α, α₂, -, hy₀, -⟩ := hU.2 V₀ ρ₀ hCN₀ hinj₀ hfin₀ D₀ e₀ hRef₀
  obtain ⟨L, _, _, _, yL, hyL⟩ := GlobalTheory.T.exists_lift_fieldPoint_finite_surjective_after_extension (FractionRing V₀) F.X Y y₀ q hq hs
  obtain ⟨V₁, _, _, _, ρ, σ, hCN₁, hinj, hfin, hloc, hσ⟩ := GlobalTheory.T.exists_finite_local_extension_with_embedded_field_extension V₀ hCN₀ L
  haveI : IsNoetherianRing V₀ := hCN₀.1
  have hR : AdmBase V₀ (maximalIdeal V₀) := ⟨hCN₀.1, inferInstance, hCN₀.2.1, hCN₀.2.2.1⟩
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists V₀ _ hR D₀
  have hgen : (specOf ρ).base (genericPoint (Spec (CommRingCat.of V₁))) ∈ Wo := by
    have : (specOf ρ).base (genericPoint (Spec (CommRingCat.of V₁))) = genericPoint (Spec (CommRingCat.of V₀)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ hinj)
    rw [this]; exact hWo
  obtain ⟨D₁, hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg GlobalTheory.polBaseChange_holds GlobalTheory.globalFns_holds V₀ V₁ _ _ ρ
    (map_maximalIdeal_le ρ) D₀ Wo hψ hgen
  have hfr : GlobalTheory.Mum.GenDesc.fracMap ρ hinj = σ.comp (algebraMap (FractionRing V₀) L) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V₀) (RingHom.ext fun x => ?_)
    simp [GlobalTheory.Mum.GenDesc.fracMap_algebraMap, hσ]
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ.comp ρ₀, D₁, hD.xe.trans e₀,
    spMap (GlobalTheory.Mum.GenDesc.fracMap ρ hinj) ≫ y₀, spMap σ ≫ yL, hCN₁, hinj.comp hinj₀, hfin.comp hfin₀,
    GlobalTheory.T.refinesPolarised_pullback_injective Q ρ₀ D₀.toPre e₀ hinj₀ hRef₀ ρ D₁.toPre hD hinj, ?_, ?_⟩
  · rw [Category.assoc, hy₀, spMap_comp_ext ρ₀ ρ]
    simp only [Category.assoc]
    rw [← Category.assoc (jK V₁) (spMap ρ), GlobalTheory.Mum.GenDesc.jK_comp_spMap ρ hinj]
    simp only [Category.assoc]
  · rw [Category.assoc, hyL, hfr, spMap_comp_ext]
    simp only [Category.assoc]

end GlobalTheory.Poinc.Sep.SharpExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.YRatio

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W V : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing V] [IsDomain V] [IsLocalRing V] (θ₀ : W →+* V) (D₀ : DegPre W) [Module (𝓞 E) D₀.X] (o₀ : letI := H.starRing; D₀.OAct (𝓞 E)) (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (e : Q.X ≃ₗ[𝓞 E] D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → (letI := H.starRing; TraceFormTwistIso D₀ o₀ H.w0) → Q.TauBimult → (letI := H.starRing; TraceFormTwistIso Q oQ H.w0) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → (letI := H.starRing; ∀ a : 𝓞 E, (oQ.onB.act a).left ≫ β = β ≫ (o₀.onB.act a).left) → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)) (q : Q.X → Q.X → (FractionRing V)ˣ), (∀ y : Q.X, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ (∀ y, PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ) ∧ (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) ∧ ∀ y, (g y)⁻¹ = q y (H.w0 • y) := by
  intro E _ _ _ H W V _ _ _ _ _ _ θ₀ D₀ _ o₀ Q _ oQ e β hB₀ hU hW₀ hBQ hWQ gp hact hL hc
  letI := H.starRing
  obtain ⟨g, hD, hxe, hβ, hWt⟩ := GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere θ₀ D₀ Q e.toAddEquiv β hU gp hL hc
  letI : Module (𝓞 E) (GlobalTheory.PolDeg.rescale Q g).X := ‹Module (𝓞 E) Q.X›
  obtain ⟨hB', o', ho', hW'⟩ := GlobalTheory.T.pullDeg_keeps_bimult_action_polarisationElement o₀ hD oQ.onB
    (fun a y => by rw [hxe, hxe]; exact e.map_smul a y) oQ.c_lin
    (fun a => by rw [hβ]; exact hact a) hB₀ H.w0 hW₀
  obtain ⟨q, h1, h2, h3, h4⟩ := GlobalTheory.T.rescaled_degenerationData_differ_by_scalar Q oQ g o' ho' hBQ hB' H.w0 hWQ hW'
  exact ⟨g, hD, q, hxe, hβ, GlobalTheory.T.psiUnitOn_univ_of_pullback_read_top hD hWt, h1, h2, h3, h4⟩

end GlobalTheory.YRatio
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.LabUniq

section Lin
variable {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem eq_of_congMod (x y : M) (h : ∀ m : ℕ, 1 ≤ m → CongMod m x y) : x = y := by
  let b := Module.Free.chooseBasis ℤ M
  rw [← sub_eq_zero]
  apply b.repr.injective
  ext k
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = (b.repr (x - y) k).natAbs + 1 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := h N (by omega)
  have hxy : x - y = N • w := by rw [hw]; abel
  have h2 : b.repr (x - y) k = (N : ℤ) * b.repr w k := by
    rw [hxy, map_nsmul]; simp [nsmul_eq_mul]
  refine Int.eq_zero_of_abs_lt_dvd ⟨_, h2⟩ ?_
  rw [Int.abs_eq_natAbs]; omega

end Lin

section Diag
variable {Y : Type} [AddCommGroup Y]

theorem act_unit (a b : Fin 8) (w : Fin 8 → Y) :
    (fun i => ∑ j, (Matrix.of fun i' j' => if i' = a ∧ j' = b then (1 : ℤ) else 0) i j • w j) = Pi.single a (w b) := by
  funext i
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem eq_diag (θ : (Fin 8 → Y) ≃+ (Fin 8 → Y))
    (h : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b)
    (v : Fin 8 → Y) (a : Fin 8) : θ v a = θ (Pi.single 0 (v a)) 0 := by
  have h1 := h (Matrix.of fun i' j' => if i' = a ∧ j' = a then (1 : ℤ) else 0) v
  rw [act_unit, act_unit] at h1
  have h2 := h (Matrix.of fun i' j' => if i' = a ∧ j' = 0 then (1 : ℤ) else 0) (Pi.single 0 (v a))
  rw [act_unit, act_unit] at h2
  have e1 := congrFun h1 a
  have e2 := congrFun h2 a
  simp only [Pi.single_eq_same] at e1 e2
  rw [← e1, e2]

end Diag

theorem qW_single {Y : Type} [AddCommGroup Y] (W : Matrix (Fin 8) (Fin 8) ℤ) (β : LinearMap.BilinForm ℤ Y) (y : Y) :
    qW W β (Pi.single 0 y) = W 0 0 * β y y := by
  unfold qW
  rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ κ : c.T.D.toPre.X ≃+ c.T.D.toPre.X, (∀ a b, c.T.β (κ a) (κ b) = c.T.β a b) ∧ ∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (fun a => κ (μ a)) := by
  intro g n F W Z i X ε hdiag p _ z c yy yy' h1 h2
  obtain ⟨θ, hq, hl, hE⟩ := GlobalTheory.T.exists_qW_automorphism_eighthPower_lattice_labels g n F W Z i X ε hdiag p z c yy yy' h1 h2
  have hc : ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) v, θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b :=
    fun E v => eq_of_congMod _ _ fun m hm => hE m hm E v
  let κ0 : c.T.D.toPre.X →+ c.T.D.toPre.X :=
    (Pi.evalAddMonoidHom (fun _ : Fin 8 => c.T.D.toPre.X) 0).comp
      (θ.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 8 => c.T.D.toPre.X) 0))
  have hθ : ∀ v a, θ v a = κ0 (v a) := fun v a => eq_diag θ hc v a
  have hsingle : ∀ y, θ (Pi.single 0 y) = Pi.single 0 (κ0 y) := by
    intro y; funext a; rw [hθ]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  have inj : Function.Injective κ0 := by
    intro y y' hy
    have : θ (Pi.single 0 y) = θ (Pi.single 0 y') := by rw [hsingle, hsingle, hy]
    exact Pi.single_injective 0 (θ.injective this)
  have surj : Function.Surjective κ0 := by
    intro y
    refine ⟨θ.symm (fun _ => y) 0, ?_⟩
    rw [← hθ]; simp
  let κ := AddEquiv.ofBijective κ0 ⟨inj, surj⟩
  have hκ : ∀ x, κ x = κ0 x := fun x => rfl
  have hd : ∀ x, c.T.β (κ0 x) (κ0 x) = c.T.β x x := by
    intro x
    have := hq (Pi.single 0 x)
    rw [hsingle, qW_single, qW_single] at this
    exact mul_left_cancel₀ (X.diag_pos 0).ne' this
  refine ⟨κ, ?_, ?_⟩
  · intro a b
    rw [hκ, hκ]
    have hab := hd (a + b)
    simp only [map_add (f := _), LinearMap.map_add₂, LinearMap.add_apply] at hab
    have s1 := c.T.symm (κ0 a) (κ0 b)
    have s2 := c.T.symm a b
    have ha := hd a
    have hb := hd b
    linarith
  · intro x μ h
    rw [hl x μ h]
    congr 1
    funext a
    exact hθ μ a

end GlobalTheory.Poinc.LabUniq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.Poinc

theorem rechart_at_classical_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp R' ⟶ F.X), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ IsDiagEnd F W ρ'.P u' ε' ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) ∧ spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y ∧ ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  have h1 : X₁.π ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∈ Set.range i := by
    have e1 := congrArg (fun f : Sp (PadicAlgCl p) ⟶ Z => f (closedPoint (PadicAlgCl p))) c.comm
    simp only [Scheme.Hom.comp_apply] at e1
    exact ⟨_, by simp only [Scheme.Hom.comp_apply]; exact e1.symm⟩
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hU, hwU, -, hSame, hi₀, hdiag', hpt⟩ :=
    GlobalTheory.T.exists_thetaSystem_moved_to_affineOpen g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag _ h1
  set w := (gPt p ≫ c.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X₁.M.ringOn U ≤ X₁.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ c.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X₁.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ c.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X₁.M.ringOn U, y₀ a = X₁.M.val (gPt p ≫ c.y) a := fun a => rfl

  let e : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z :=
    Spec.map (CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X₁.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X₁.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X₁.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ c.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ c.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X₁.M.ringOn U).val.toRingHom ≫ e = X₁.M.pt := by
    refine ext_of_valR hU (he _).1 (X₁.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (X₁.M.ringOn U).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsSeparated X₁.z := X₁.isProper_compactificationMap.toIsSeparated
  have hgen2 : spMap (X₁.M.ringOn U).val.toRingHom ≫ (e ≫ X₁.π) =
      spMap (X₁.M.ringOn U).val.toRingHom ≫ (u' ≫ i) := by
    rw [← Category.assoc, hgen, X₁.comp, ← Category.assoc _ u' i, hpt, Category.assoc]
  have hb : e ≫ X₁.π = u' ≫ i :=
    ext_of_isDominant_of_isSeparated X₁.z
      (ext_of_isDominant (spMap (X₁.M.ringOn U).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (X₁.M.ringOn U).val.toRingHom) hgen2
  haveI := himm
  have hpt' : spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y := by
    rw [← cancel_mono i, Category.assoc, ← hb, ← Category.assoc, ha, Category.assoc, c.comm, Category.assoc]

  let τ := Spec.preimage (c.y ≫ X₁.M.s)
  have hσ : (gPt p ≫ c.y) ≫ X₁.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (c.y ≫ X₁.M.s), ← Spec.map_comp]; rfl
  refine ⟨c₀, hc, X₁.M.ringOn U, fg, frac, hth', hev, ρ', ε', u', hSame, hi₀, hle, hdiag', y₀, hy₀, hpt',
    fun a => ?_⟩
  rw [hy₀]
  show ‖X₁.M.val (gPt p ≫ c.y) (algebraMap X₁.o₁ X₁.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLiftRechart

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X hg hn ho himm he8 hth hproj ε hε p _ z c
  set w : X.M.Z := (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw
  have hwr : X.π w ∈ Set.range i := by
    refine ⟨(spMap c.ι ≫ c.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)), ?_⟩
    have h := congrArg (fun f => f (IsLocalRing.closedPoint (PadicAlgCl p))) c.comm
    rw [hw]
    exact h.symm
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hUa, hwU, hUi, hSame, hi₀, hdiag, hcomp⟩ :=
    GlobalTheory.T.exists_thetaSystem_moved_to_affineOpen g n F W Z i X hg hn ho himm he8 hth hproj ε hε w hwr
  have hle : X.M.ringOn (U : Set X.M.Z) ≤ X.M.O w := RatModel.ringOn_le_O hwU
  refine ⟨c₀, hc, X.M.ringOn (U : Set X.M.Z), fg, frac, hth', hev, ρ', ε', hSame, hi₀, hle, ?_⟩
  refine ⟨(X.M.valHom (gPt p ≫ c.y) w (RatModel.range_eq_singleton _ _)).comp
    (Subalgebra.inclusion hle).toRingHom, fun a => rfl, fun a => ?_⟩
  have hmem : algebraMap X.o₁ X.Ω₁ a ∈ X.M.O z := Subalgebra.algebraMap_mem _ a
  have h1 := c.norm_val_le ((X.M.stalkEquiv z).symm ⟨_, hmem⟩)
  simp only [CTrait.val] at h1
  rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply] at h1
  simpa using h1

end GlobalTheory.Poinc.GLiftRechart
end
