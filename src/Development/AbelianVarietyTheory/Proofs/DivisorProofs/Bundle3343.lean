module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle663
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTripleProductMapLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3335
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open CubeCarried

theorem exists_secOver_of_gen {X : Scheme.{0}} (L : LB X) (W : X.Opens) (g : W.toScheme ⟶ X) (hg : g = W.ι)
    (t : LB.Gen (L.pull g)) (ht : t.IsGen) :
    ∃ s : ∀ k, Γ(X, W ⊓ L.U k), IsSecOver L W s ∧
      (∀ (z : X) (k : L.ι), z ∈ W → z ∈ L.U k → IsUnit (gs (𝟙 X) z (W ⊓ L.U k) (s k))) ∧
      ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), W ≤ f ⁻¹ᵁ W →
        (∀ (Z : Scheme.{0}) (r r' : Z ⟶ W) (z : Z) (j k : L.ι), r' ≫ W.ι = (r ≫ W.ι) ≫ f →
          g (r' z) ∈ L.U j → g (r z) ∈ L.U k →
          gm r' z ((L.pull g).U (fun _ => j)) (t.s (fun _ => j)) =
            gw w (r ≫ g) z j k * gm r z ((L.pull g).U (fun _ => k)) (t.s (fun _ => k))) →
        SecCarriedOver L W s f w := by
  subst hg
  obtain ⟨s, hs⟩ := exists_sec_of_gen L W t
  have inj : ∀ z : W.toScheme, Function.Injective (W.ι.stalkMap z).hom := fun z =>
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z)).1
  have v : ∀ (z : W.toScheme) (k : L.ι), W.ι z ∈ L.U k →
      (W.ι.stalkMap z).hom (gs (𝟙 X) (W.ι z) (W ⊓ L.U k) (s k)) =
        (gm (𝟙 _) z ((L.pull W.ι).U (fun _ => k)) (t.s (fun _ => k))).val := fun z k hk => by
    rw [← gs_eq_map_gs W.ι z _ (show W.ι z ∈ W ⊓ L.U k from ⟨z.2, hk⟩), ← hs _ (𝟙 _) z k hk, Category.id_comp]
  refine ⟨s, fun z k k' hz hk hk' => ?_, fun z k hz hk => ?_, fun f w hf H z j k hz hfz hk hj => ?_⟩
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    rw [map_mul, v z k hk, v z k' hk', ← gm_val_map W.ι z (L.U k ⊓ L.U k') ⟨hk, hk'⟩, ← Units.val_mul]
    congr 1
    refine (gen_trans ht (𝟙 _) z (j := fun _ => k) (j' := fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).trans ?_
    rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
    rfl
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    refine (isUnit_map_iff (W.ι.stalkMap z).hom _).1 ?_
    rw [v z k hk]
    exact Units.isUnit _
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    have hr : f.resLE W W hf ≫ W.ι = (𝟙 _ ≫ W.ι) ≫ f := by simp
    have hj' : W.ι (f.resLE W W hf z) ∈ L.U j := by
      rw [← Scheme.Hom.comp_apply, hr]; exact hj
    have e := congrArg Units.val (H _ (𝟙 _) (f.resLE W W hf) z j k hr hj' hk)
    rw [← hs _ _ z j hj', hr, Category.id_comp, Units.val_mul] at e
    rw [map_mul, v z k hk, ← CubeCarried.gs_comp W.ι f z (W ⊓ L.U j) ⟨hfz, hj⟩, e]
    exact congrArg₂ (· * ·) (gm_val_map W.ι z ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hj, hk⟩ _) rfl



theorem exists_carried_sec_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ s : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k), IsSecOver U'.LG.L (β ⁻¹ᵁ V) s ∧ (∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V ⊓ U'.LG.L.U k) (s k))) ∧ ∀ σ : Gal ρ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ ∧ ∃ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h ∧ SecCarriedOver U'.LG.L (β ⁻¹ᵁ V) s _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := GlobalTheory.T.exists_carried_section_nonzero_near_closedFibre R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  have := hB.1.1
  have hfin : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip hfin
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact hnz g' hg hgc
  obtain ⟨p, q, c, h⟩ := OffClosed.exists_ten R hB.1.2.2.2 G hS O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) p q c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  have hyV : y ∈ V := Set.mem_iInter₂.2 h
  refine ⟨V, hyV, ?_⟩
  obtain ⟨hl, hm⟩ := grpPullback_points_lift_mul_inv _ _ (spMap ρ) G G' β hβ G' G β hβ.1.w
  obtain ⟨a', ha⟩ := hl p
  obtain ⟨b', hb⟩ := hl q
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) p q c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  choose hd bc hbc hP hov using a.unif
  let F : Gal ρ → (G'.left ⟶ G'.left) := fun σ => (bc σ).hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))
  have hFa : ∀ σ, F σ = a.act σ := hbc
  have hFc : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (F σ) := fun σ => (hFa σ).symm ▸ a.cart σ
  have hFβ : ∀ σ, F σ ≫ β = β := fun σ => by rw [hFa, hact]
  let w : ∀ σ, LB.Iso U'.LG.L (U'.LG.L.pull (F σ)) := fun σ => Classical.choose (hP σ).lg
  have hw : ∀ σ, (w σ).IsGen := fun σ => (Classical.choose_spec (hP σ).lg).1
  have hrig : ∀ σ, PMaps (w σ) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig
      (spMap (Gal.hom σ)) := fun σ => by
    obtain ⟨he, hr, -⟩ := (Classical.choose_spec (hP σ).lg).2
    exact (maps_iff (w σ) _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (spMap (Gal.hom σ)) _
      (rigPull_le (F σ) (spMap (Gal.hom σ)) he U'.LG.L) (fun _ => rfl)).1 hr
  have comm : ∀ (u : G ⟶ G) (u' : G' ⟶ G'), u'.left ≫ β = β ≫ u.left → ∀ σ, u'.left ≫ F σ = F σ ≫ u'.left := by
    intro u u' hu σ
    have e₁ := hFβ σ
    have e₂ := (hFc σ).1.w
    generalize F σ = f at e₁ e₂ ⊢
    apply hβ.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, hu, ← Category.assoc, e₁]
    · rw [Category.assoc, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  obtain ⟨t, ht, hcar⟩ := exists_gen_carried U'.cubG hFc w hrig
    (fun σ => pmaps_cub R' _ D' A' G' U'.toUnifPre (hFc σ) (w σ) (hw σ)) θ
    (fun σ => hθ σ (hd σ) (bc σ) (hbc σ) (hP σ) (hov σ)) G' F (fun σ => (hFc σ).1.w) (𝟙 G') a' b' c'
    (comm _ _ h1) (comm _ _ ha) (comm _ _ hb) (comm _ _ hc) (β ⁻¹ᵁ V) (by
      intro f' hf' g hg
      obtain ⟨f, hf, e⟩ := hten f' hf'
      have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
      refine h2 (f'.left g) ?_
      rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  obtain ⟨s, hs, hu, hcs⟩ := exists_secOver_of_gen U'.LG.L (β ⁻¹ᵁ V) _ (by simp) t ht
  refine ⟨s, hs, fun z k hz hk => hu z k (show β z ∈ V from hz ▸ hyV) hk, fun σ =>
    ⟨hd σ, bc σ, hbc σ, hP σ, hov σ, hcs (F σ) (w σ) (fun z hz => ?_) (hcar σ)⟩⟩
  show (F σ ≫ β) z ∈ V
  rw [hFβ]
  exact hz

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.product_uniformised_groups_sum_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂), ∃ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂)) (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (j₁ : D₁.toPre.X →+ D.toPre.X) (q₁ : D.toPre.X →+ D₁.toPre.X) (j₂ : D₂.toPre.X →+ D.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSemiAbelian (G₁ ⊗ G₂) ∧ i₁ ≫ p₁ = 𝟙 _ ∧ i₂ ≫ p₂ = 𝟙 _ ∧ (∀ y, q₁ (j₁ y) = y) ∧ (∀ y, q₂ (j₂ y) = y) ∧ Adj (pol D₁) (pol D) i₁ p₁ j₁ q₁ ∧ Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ ∧ LinHom U₁.toUnifPre U.toUnifPre i₁ q₁ (lift (𝟙 G₁) 1) ∧ LinHom U.toUnifPre U₁.toUnifPre p₁ j₁ (fst G₁ G₂) ∧ LinHom U₂.toUnifPre U.toUnifPre i₂ q₂ (lift 1 (𝟙 G₂)) ∧ LinHom U.toUnifPre U₂.toUnifPre p₂ j₂ (snd G₁ G₂) ∧ GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) ∧ GAdj U₂.LG.L U.LG.L (lift 1 (𝟙 G₂)) (snd G₁ G₂) := by
  first | exact @GlobalTheory.MumProd.prod_main | exact GlobalTheory.MumProd.prod_main | (intros; apply GlobalTheory.MumProd.prod_main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem descAt_of_thetaTerms : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  intro g n hn hodd
  obtain ⟨j₁, h₁⟩ := GlobalTheory.T.polarisedAbelianPart_model_over_subfield g n hn hodd
  obtain ⟨j₂, h₂⟩ := GlobalTheory.T.torsionPoints_defined_over_subfield_abelianModel g n hn hodd
  refine ⟨max j₁ j₂, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨B₀, iG₀, iC₀, M₀, B', iG', π₁, π₀, w, hA, hM, hp1, hp0, hw⟩ :=
    h₁ j (le_trans (le_max_left _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
  have hP := h₂ j (le_trans (le_max_right _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
    B₀ M₀ B' π₁ π₀ w hA hM hp1 hp0 hw
  have hsq : ∀ a : D.X, (spMap ev ≫ (D.c a).left) ≫ D.P.A.hom = 𝟙 (Sp K) ≫ spMap ev := by
    intro a
    rw [Category.assoc, Over.w (D.c a)]
    simp
  let c' : D.X → (Sp K ⟶ B'.left) := fun a => hp1.1.lift (spMap ev ≫ (D.c a).left) (𝟙 _) (hsq a)
  have hc1 : ∀ a, c' a ≫ B'.hom = 𝟙 _ := fun a => hp1.1.lift_snd _ _ _
  have hc2 : ∀ a, c' a ≫ π₁ = spMap ev ≫ (D.c a).left := fun a => hp1.1.lift_fst _ _ _
  choose c₀ hc₀ using fun a => hP a (c' a) (hc1 a) (hc2 a)
  exact ⟨B₀, iG₀, iC₀, M₀, c₀, B', iG', π₁, π₀, w, c', hA, hM, hp1, hp0, hw, fun a => ⟨hc1 a, hc2 a, (hc₀ a).symm⟩⟩

end GlobalTheory.USep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.Poinc.Sep.twistAtEach_exists : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg⟩ := GlobalTheory.Poinc.Sep.torusChar_eq_weil g n F W Z i X₁ z₁ act
  refine ⟨sg, ?_, hsg⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c τ hτ
  obtain ⟨χ, hχN, hχo⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.T.twisted_sum_terms_eq_theta_constant_translate g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab hlab T hT c τ hτ χ hχN hχo
  exact ⟨e, GlobalTheory.Poinc.TwistSum₂.twistSum_of_sumF g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.Poinc.Sep.UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv)
    (GlobalTheory.Poinc.Sep.UMem.exists_yy g n F W Z i X₁ z₁ act V ev X m t δ 𝔪) (hsg V ev X m t δ 𝔪 τ χ hχN hχo) he⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TransTerms

theorem affine_on_subgroup_of_second_diff {G : Type*} [AddCommGroup G] (H : AddSubgroup G) {R : Type*} [AddCommGroup R]
    (D : G → R) (hD : ∀ a ∈ H, ∀ b ∈ H, D (a + b) - D a - D b + D 0 = 0) :
    ∃ (κ : R) (h : H →+ R), ∀ (a : G) (ha : a ∈ H), D a = κ + h ⟨a, ha⟩ := by
  refine ⟨D 0, AddMonoidHom.mk' (fun x : H => D x - D 0) ?_, ?_⟩
  · intro x y
    have := hD x x.2 y y.2
    simp only [AddSubgroup.coe_add]
    rw [← sub_eq_zero]
    rw [← this]; abel
  · intro a ha
    simp

theorem frExp_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1), ∀ (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ E1 E2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪1 a τ (E1 a)) → (∀ a ∈ X₁.S.HH X₁.M z₁, GlobalTheory.GSep.TransTerms.FrExp 𝔪2 a τ (E2 a)) → ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro I X₁ z₁ act x₀ hdiv V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2 τ hτ E1 E2 h1 h2
  obtain ⟨c, hc⟩ := GlobalTheory.T.frameExponent_second_difference_constant_members I X₁ z₁ act x₀ hdiv τ hτ
  have k1 := hc V1 ev1 Y1 t1 δ1 𝔪1 E1 h1
  have k2 := hc V2 ev2 Y2 t2 δ2 𝔪2 E2 h2
  refine affine_on_subgroup_of_second_diff (X₁.S.HH X₁.M z₁)
    (fun a => ((E1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((E2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2))) ?_
  intro a ha b hb
  have e1 := k1 a ha b hb
  have e2 := k2 a ha b hb
  rw [← sub_eq_zero.mpr (e1.trans e2.symm)]
  abel

end GlobalTheory.GSep.TransTerms
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.isTwist_of_translate | exact GlobalTheory.MumCmp.isTwist_of_translate | (intros; apply GlobalTheory.MumCmp.isTwist_of_translate <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_pol_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) ∧ Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left)) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o A' _ _ act' ψ hA' hψ hG hact
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.T.exists_descent_bundle_power_hecke_quotient' p D R b g c k N hc hk hN hNp hEF hg hck S s o A' ψ hA' hψ hG
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b (N * k) S s o A' ψ hψ _ P₀ hP₀ w₀
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.1 hk)
  have hk2 : 0 < k ^ 2 := by positivity
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_dvd_iff] at hck; omega)
  have hm1 : 1 ≤ k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd hk2 hck) hc0
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (hk.pow_left 2)
  exact ⟨P', hP', r1, r2,
    GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b (N * k) S s o A' ψ _ hA' hψ hG _ P' hP' w r1 r2,
    GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hm1 P' hP' w,
    GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hmp P' hP' w,
    GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b (N * k) S s o A' act' ψ _ hA' hψ hG hact _ P' hP' w r1 r2, w⟩

end GlobalTheory.UPel.HT.Hecke
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.uniformisedGroup_morphisms_agree_near_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z → ∃ W : Z.Opens, z ∈ W ∧ W.ι ≫ u = W.ι ≫ u' := by
  first | exact @GlobalTheory.Mum.LocAgree.locAgree | exact GlobalTheory.Mum.LocAgree.locAgree | (intros; apply GlobalTheory.Mum.LocAgree.locAgree <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deRham_pairing_perfect_and_hodge_filtration_isotropic : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  first | exact @GlobalTheory.PtExt.perfect_and_orthogonal | exact GlobalTheory.PtExt.perfect_and_orthogonal | (intros; apply GlobalTheory.PtExt.perfect_and_orthogonal <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.Sandwich

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {TF : TorFlag Xo c} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {P : WtPar Dw} (R : Choice TF.X Z U P)

theorem restr_mulPole (j : ℕ) (f : H0 R.str (R.adj j) ⊤) :
    H0.restr le_top (R.mulPole j ⊤ f) = R.mulPole j R.off (H0.restr le_top f) :=
  (ProdChart.restr_mul _ _ _ _).trans (by rw [H0.restr_ofSec]; rfl)

theorem mulPole_injective (h₁ : FreeOnOpen TF.X Z U P.u₁) (j : ℕ) : Function.Injective (R.mulPole j R.off) :=
  ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (R.Δ₁.nowhereZero_pow R.str (R.notMem_support h₁) j)).injective

theorem nowhereZero_pow_zero : NowhereZero (H0.ofSec R.str ⊤ (R.Δ₁.pow 0)) := nowhereZero_of_exists fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart R.Δ₁.isLB y
  exact ⟨fun _ => i, mem_zpow_U.2 hi, by rw [R.Δ₁.germ_pow R.str 0 i y hy hi, pow_zero]; exact isUnit_one⟩

end GlobalTheory.HSApp.Sandwich


open GlobalTheory.HSApp.Sandwich in
theorem GlobalTheory.HSApp.sandwich : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice TF.X Z U P)
    (ω : CanId R.toModif), FnAlgClosed (Xo := Xo) (c := c) → ∀ h₁ : FreeOnOpen TF.X Z U P.u₁,
    (∀ j, CuspIso TF.X Z U (P.wt j) → adjGlobal R j ≤ LinearMap.range (adjSec R ω h₁ j)) ∧
    (CuspIso TF.X Z U (P.wt 0) → LinearMap.range (adjSec R ω h₁ 0) ≤ adjGlobal R 0) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U P R ω hF h₁
  have key := fun (j : ℕ) m => GlobalTheory.T.canonical_ideal_weight_section hP hG E H Dw l Xo c TF Z hF R.toModif ω _ _ (P.kap_add j) m
  refine ⟨fun j hj => ?_, fun hj => ?_⟩
  · rintro _ ⟨f, rfl⟩
    let e := R.adjEquiv ω.ω ω.unit h₁ j (P.kap_add j)
    obtain ⟨m, hm⟩ := (R.bijective_pullOff (isLB_L₀ TF.X Z (P.wt j))).2 (e.symm (H0.restr le_top f))
    have hmul : H0.restr le_top (R.mulPole j ⊤ f) =
        (((common₀ TF.X Z).pull R.σ).canChart R.K.isLB (P.kap_add j)).mul ω.ω (R.pullOff m) := by
      rw [restr_mulPole, hm]
      have := R.mulPole_adjEquiv ω.ω ω.unit h₁ j (P.kap_add j) (e.symm (H0.restr le_top f))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨g, hg, hgm⟩ := (key j m).2 ⟨R.mulPole j ⊤ f, hmul⟩
    obtain ⟨c', hc'⟩ := hj.2 hg
    refine ⟨c', ?_⟩
    show e (R.pullOff (cuspSec TF.X Z U _ c')) = _
    rw [hc', hgm, hm, LinearEquiv.apply_symm_apply]
  · rintro _ ⟨c', rfl⟩
    obtain ⟨s, hs, hsr⟩ := hj.1 c'
    obtain ⟨g, hg⟩ := (key 0 _).1 ⟨s, hs, hsr⟩
    obtain ⟨f, hf⟩ := ((R.com.poleChart R.K.isLB R.Δ₁.isLB rfl).mulEquiv (nowhereZero_pow_zero R)).surjective g
    refine ⟨f, mulPole_injective R h₁ 0 ?_⟩
    rw [← restr_mulPole, mulPole_adjSec]
    exact (congrArg (H0.restr le_top) hf).trans hg
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.degree_eq_integral_topChernForm_complex : GlobalTheory.Published.ChernDegreeComplex := by
  first | exact @GlobalTheory.ChernDegree.chernDegreeComplex | exact GlobalTheory.ChernDegree.chernDegreeComplex | (intros; apply GlobalTheory.ChernDegree.chernDegreeComplex <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.chernWeilNumbers_of_degree_eq_chernIntegral : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex | exact GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex | (intros; apply GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex <;> assumption)
end
