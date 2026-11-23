module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicImageNotOntoModConjIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum



theorem exists_carried_frame_upstairs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ₁ : R →+* R₁), FinExt ρ₁ ∧ ρ₁.Etale ∧ ∃ V₀ : G.left.Opens, y ∈ V₀ ∧ ∃ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ ∧ (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ hθ O hO hOθ y hyc hy
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have hN : IsNoetherianRing R := hR.1
  have hI : IsIntegrallyClosed R := hR.2.2.1
  have := hS.smooth
  have hρf : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ)).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hρf
  have hgi : GeometricallyIrreducible G.hom :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun Ω _ s => GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint _ G hS Ω s⟩
  have s₂ : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : GeometricallyIrreducible (G ⊗ G).hom := GeometricallyIrreducible.comp (pullback.fst G.hom G.hom) G.hom
  have s₃ : Smooth (G ⊗ G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom))
  have i₃ : GeometricallyIrreducible (G ⊗ G ⊗ G).hom :=
    GeometricallyIrreducible.comp (pullback.fst G.hom (G ⊗ G).hom) G.hom
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  obtain ⟨g, hgO, hg⟩ := hO
  have hgO' : g ∈ O' := fun g' e => by
    subst e
    exact hOθ g' hgO hg
  have hfin : IsFinite (G.left.fromSpecResidueField y ≫ G.hom) :=
    ClosedPt.isFinite_fromSpec G.hom y hyc (by rw [hy]; exact isClosed_singleton_closedPoint R)
  obtain ⟨N, hN₁, hN₂⟩ := ClosedPt.exists_open_good G.hom (G ⊗ G ⊗ G).hom y (ClosedPt.ten G)
    (fun f => f.left ⁻¹ᵁ O') fun f hf => by
      obtain ⟨q, h₁, h₂⟩ := ClosedPt.ten_meets G y g (hy.trans hg.symm) f hf
      exact ⟨q, show f.left q ∈ O' from h₁ ▸ hgO', h₂⟩
  rw [hy] at hN₁
  obtain ⟨R₁, _, _, _, ρ₁, t, hρ₁, het, ht, htN⟩ := GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR (G ⊗ G ⊗ G) s₃ N hN₁
  have hρ₁f : IsFinite (spMap ρ₁) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ₁)).2 hρ₁.2.2
  let m : pullback G.hom (spMap ρ₁) ⟶ pullback G.hom (G ⊗ G ⊗ G).hom :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by rw [Category.assoc, ht]; exact pullback.condition)
  have m₁ : m ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ t := pullback.lift_snd _ _ _
  have hU : IsOpen {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} := by
    have : {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} =
        ⋂ f ∈ {f | f ∈ ClosedPt.ten G}, m ⁻¹' (f.left ⁻¹' O') := by ext; simp
    rw [this]
    exact (List.finite_toSet _).isOpen_biInter fun f _ => (O'.isOpen.preimage f.left.continuous).preimage m.continuous
  let V : G.left.Opens := ⟨_, ((pullback.fst G.hom (spMap ρ₁)).isClosedMap _ hU.isClosed_compl).isOpen_compl⟩
  have hyV : y ∈ V := by
    rintro ⟨p, hp, hpy⟩
    refine hp (hN₂ (m p) ?_ ?_)
    · rw [← Scheme.Hom.comp_apply, m₁, hpy]
    · rw [← Scheme.Hom.comp_apply, m₂, Scheme.Hom.comp_apply]
      exact htN ⟨_, rfl⟩
  have hgood : ∀ p : (pullback G.hom (spMap ρ₁) : Scheme.{0}), pullback.fst G.hom (spMap ρ₁) p ∈ V →
      ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O' := fun p hp => by
    by_contra h
    exact hp ⟨p, h, rfl⟩
  let q := pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)
  let s := pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)
  have hqs : (q ≫ β) ≫ G.hom = s ≫ spMap ρ₁ := by
    rw [Category.assoc, hβ.1.w]; exact pullback.condition
  let n' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback G.hom (spMap ρ₁) := pullback.lift (q ≫ β) s hqs
  have n₁ : n' ≫ pullback.fst _ _ = q ≫ β := pullback.lift_fst _ _ _
  have n₂ : n' ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _
  let ζ : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ (G ⊗ G ⊗ G ⊗ G).left := n' ≫ m
  let T : Over (Sp R') := Over.mk (q ≫ G'.hom)
  have hζ : ζ ≫ (fst G (G ⊗ G ⊗ G)).left = q ≫ β := by
    change (n' ≫ m) ≫ pullback.fst G.hom (G ⊗ G ⊗ G).hom = _
    rw [Category.assoc, m₁, n₁]
  have hw : ζ ≫ (G ⊗ G ⊗ G ⊗ G).hom = T.hom ≫ spMap ρ := by
    rw [← Over.w (fst G (G ⊗ G ⊗ G)), ← Category.assoc, hζ, Category.assoc, hβ.1.w]
    exact (Category.assoc _ _ _).symm
  obtain ⟨hl, hm⟩ := GlobalTheory.T.grpPullback_points_lift_and_compat_mul_inv (Sp R) (Sp R') (spMap ρ) G G' β hβ T (G ⊗ G ⊗ G ⊗ G) ζ hw
  obtain ⟨a₁, ha⟩ := hl (snd _ _ ≫ fst _ _)
  obtain ⟨b₁, hb⟩ := hl (snd _ _ ≫ snd _ _ ≫ fst _ _)
  obtain ⟨c₁, hc₁⟩ := hl (snd _ _ ≫ snd _ _ ≫ snd _ _)
  let x : T ⟶ G' := Over.homMk q rfl
  have hx : x.left ≫ β = ζ ≫ (fst G _).left := hζ.symm
  have mu := fun u v u' v' h₁ h₂ => (hm u v u' v' h₁ h₂).1
  have iv := fun u u' h₁ => (hm u u u' u' h₁ h₁).2
  have key : ∀ f' ∈ cubeTen x a₁ b₁ c₁, ∃ f ∈ ClosedPt.ten G, f'.left ≫ β = ζ ≫ f.left := by
    intro f hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ ha)⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ (mu _ _ _ _ hb hc₁))⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ (mu _ _ _ _ hb hc₁)⟩
  have hten : ∀ g ∈ cubeTen x a₁ b₁ c₁, q ⁻¹ᵁ (β ⁻¹ᵁ V) ≤ g.left ⁻¹ᵁ secNz θ := by
    intro g' hg' z hz
    obtain ⟨f, hf, e⟩ := key g' hg'
    have hzV : pullback.fst G.hom (spMap ρ₁) (n' z) ∈ V := by
      rw [← Scheme.Hom.comp_apply, n₁, Scheme.Hom.comp_apply]; exact hz
    have h1 := hgood (n' z) hzV f hf
    refine h1 (g'.left z) ?_
    have e' := congrArg (fun φ => φ z) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact e'
  obtain ⟨τ, hτ, hcar⟩ := GlobalTheory.T.exists_carriedFrame_theoremOfCube G' U'.LG U'.cubG θ T x a₁ b₁ c₁ (q ⁻¹ᵁ (β ⁻¹ᵁ V)) hten
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hρ₁, het, V, hyV, τ, hτ, ?_⟩
  intro σ h bc hbc hP hPO f' hf'q hf's
  have hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) :=
    hbc ▸ a.cart σ
  have hrc := GlobalTheory.T.rigidifiedGaloisLinearisation_carries_rigidification_cube R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact σ h bc hbc hP
  have hTw : f' ≫ T.hom = T.hom ≫ spMap (Gal.hom σ) := by
    change f' ≫ q ≫ G'.hom = (q ≫ G'.hom) ≫ _
    rw [← Category.assoc, hf'q, Category.assoc, (a.cart σ).1.w, Category.assoc]
  have hfn : f' ≫ n' = n' := by
    apply pullback.hom_ext
    · rw [Category.assoc, n₁, ← Category.assoc, hf'q, Category.assoc, hact]
    · rw [Category.assoc, n₂, hf's]
  have hfζ : f' ≫ ζ = ζ := by
    change f' ≫ n' ≫ m = n' ≫ m
    rw [← Category.assoc, hfn]
  have lift_eq : ∀ (u₁ : T ⟶ G') (u : G ⊗ G ⊗ G ⊗ G ⟶ G), u₁.left ≫ β = ζ ≫ u.left →
      u₁.left ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) = f' ≫ u₁.left := by
    intro u₁ u hu
    rw [hbc]
    apply hβ.1.hom_ext
    · rw [Category.assoc, hact, hu, Category.assoc f', hu, ← Category.assoc, hfζ]
    · have e₁ : u₁.left ≫ G'.hom = T.hom := Over.w u₁
      rw [Category.assoc, (a.cart σ).1.w, ← Category.assoc, e₁, Category.assoc, e₁, hTw]
  exact hcar (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (specOf (Gal.hom σ)) hc
    (Classical.choose hP.lg) (Classical.choose_spec hP.lg).1 hrc.1 (hrc.2 hc) (hθ σ h bc hbc hP hPO) f' hTw
    (by rw [hbc]; exact hf'q.symm) (lift_eq a₁ _ ha) (lift_eq b₁ _ hb) (lift_eq c₁ _ hc₁)

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.frameCarried_descend_finiteEtale_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.descend_finiteEtale | exact GlobalTheory.Mum.FrameCarried.descend_finiteEtale | (intros; apply GlobalTheory.Mum.FrameCarried.descend_finiteEtale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_global_iso_translated_bundle_levelComparison : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (hwL : wL.IsGen) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left),
    ∃ W : LB.Iso D₂.toPre.P.L (D.toPre.P.L.pull (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0)), W.IsGen ∧
      ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D₂.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U₂.LG.L.ι),
        (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U jM → (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U jM' →
        ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U jL' →
        Geo.Tor.gw W (r ≫ (U₂.gt e).pG.left) z jM jM' * Geo.Tor.gw (U₂.w e) r z jM' (fun _ => jL') =
          Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z jL jL' := by
  first | exact @GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global | exact GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global | (intros; apply GlobalTheory.MumCmp.TranslLev.exists_iso_translate_global <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_uniformisedGroup_galoisAutomorphism_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ), ∃ a, GalMap hD U' σ a := by
  first | exact @GlobalTheory.Mum.exists_galMap | exact GlobalTheory.Mum.exists_galMap | (intros; apply GlobalTheory.Mum.exists_galMap <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem mem_of_smul_mem_sup {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O} (hI : I.IsMaximal)
    {N : Submodule O X} (hN : I • (⊤ : Submodule O X) ≤ N) {a : O} (ha : a ∉ I) {u : X} (hu : a • u ∈ N) : u ∈ N := by
  obtain ⟨c, i, hi, hc⟩ := hI.exists_inv ha
  have : c • (a • u) + i • u = u := by rw [smul_smul, ← add_smul, hc, one_smul]
  rw [← this]
  exact add_mem (N.smul_mem c hu) (hN (Submodule.smul_mem_smul hi trivial))

theorem map_range_rank_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (Z' : Submodule (𝓞 E) D.La)
    (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (u : D.La) :
    (LinearMap.range (Z'.subtype + ℓ.smulRight u)).map y = LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y u)) := by
  rw [← LinearMap.range_comp]
  congr 1
  ext x
  simp

end GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_real {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  have hm : (0 : D.La) ∈ perp D Z ⊓ perp D Z' := zero_mem _
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one hm θ (fun t => by simp [hθ])
  have hN : 𝔭 • (⊤ : Submodule (𝓞 E) X) ≤ img D y Z' 𝔭 := le_sup_right

  set P1 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => ℓ v ∈ 𝔭 with hP1
  set P2 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭 with hP2
  have P1sub : ∀ a b, P1 (a + b) → P1 b → P1 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP1] using this
  have P2sub : ∀ a b, P2 (a + b) → P2 b → P2 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP2, map_add (f := _)] using this

  obtain ⟨x, ⟨z, hz, rfl⟩, hx⟩ := Set.not_subset.1 hZ
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ 𝔭.zero_mem)
  obtain ⟨ℓ₂, hℓ₂⟩ := GlobalTheory.T.exists_linearForm_factor_through_traceGenerator D Z' θ s hs0 hgen z
  have hζ₂ : ζ ℓ₂ = H.bar s • z := by
    obtain ⟨c, -, hu⟩ := h.symm.2.2.1 (θ.comp ℓ₂.toAddMonoidHom)
    have e1 := hu ⟨ζ ℓ₂, hζZ ℓ₂⟩ fun a => by simpa using hζ ℓ₂ a
    have e2 := hu ⟨H.bar s • z, Z.smul_mem _ hz⟩ fun a => by simpa using (hℓ₂ a).symm
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hℓ₂P : ¬ P2 ℓ₂ := fun hP => by
    simp only [hP2, hζ₂, map_smul] at hP
    exact hx (mem_of_smul_mem_sup h𝔭 hN hs' hP)

  obtain ⟨ℓ₁, h1, h2⟩ : ∃ ℓ₁, ¬ P1 ℓ₁ ∧ ¬ P2 ℓ₁ := by
    by_cases ha : P2 ℓ₀
    · by_cases hb1 : P1 ℓ₂
      · refine ⟨ℓ₀ + ℓ₂, fun hp => hℓ₀ (P1sub _ _ hp hb1), fun hp => hℓ₂P ?_⟩
        rw [add_comm] at hp
        exact P2sub _ _ hp ha
      · exact ⟨ℓ₂, hb1, hℓ₂P⟩
    · exact ⟨ℓ₀, hℓ₀, ha⟩
  have he𝔭 : e ∉ 𝔭 := fun hm' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem hm' he1
    simpa using this))
  have hbe : H.bar e ∉ 𝔭 := fun hm' => he𝔭 (by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm'
    rw [hb] at this
    simpa [bar_bar] using this)
  set ℓ := e • ℓ₁ with hℓ
  refine ⟨LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)), hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => ?_⟩
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    show Z'.map y ⊔ _ ≤ _ ⊔ _
    rw [map_range_rank_one, hZ'm]
    by_cases hq : 𝔮 = 𝔭
    · subst hq
      refine (range_le_of_ker _ ℓ _ 𝔮 h𝔮 (v := v) (by simpa using hv) ?_).2
      show e * ℓ₁ v ∉ 𝔮
      exact fun hm' => h1 ((h𝔮.isPrime.mem_or_mem hm').resolve_left he𝔭)
    · exact range_le_of_mem _ ℓ _ 𝔮 fun x => by
        show e * ℓ₁ x ∈ 𝔮
        exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hmem := (range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (0 + ζ ℓ)) 𝔭 h𝔭 (v := v) (by simpa using hv)
      (show e * ℓ₁ v ∉ 𝔭 from fun hm' => h1 ((h𝔭.isPrime.mem_or_mem hm').resolve_left he𝔭))).1
    have hin : y (ζ ℓ) ∈ img D y Z' 𝔭 := by
      apply hle
      show _ ∈ _ ⊔ _
      rw [map_range_rank_one]
      simpa using hmem
    rw [hℓ, hζs, map_smul] at hin
    exact h2 (mem_of_smul_mem_sup h𝔭 hN hbe hin)

end GlobalTheory.LowFilt
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.exists_isometry_extending_isotropic_shear : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ), 0 < N → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' → ∀ t : Z →ₗ[𝓞 E] D.La,
    (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) → (∀ z z' : Z, D.EF (t z) (t z') = 0) →
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧ ∀ z : Z, g z = t z := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | exact GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_isometry_extend <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_ne_conj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  first | exact @GlobalTheory.LowFilt.exists_improves_of_ne_conj | exact GlobalTheory.LowFilt.exists_improves_of_ne_conj | (intros; apply GlobalTheory.LowFilt.exists_improves_of_ne_conj <;> assumption)
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.isotropicImage_not_onto_mod_conj_ideal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ := by
  first | exact @GlobalTheory.LowFilt.CoisBar.img_bar_ne_top | exact GlobalTheory.LowFilt.CoisBar.img_bar_ne_top | (intros; apply GlobalTheory.LowFilt.CoisBar.img_bar_ne_top <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

theorem _root_.GlobalTheory.T.periodScalarCoordinates_symm_bimult_up_to_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) ∧ ∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b) := by
  first | exact @GlobalTheory.Mum.TensPolRel.tauCoord_rel | exact GlobalTheory.Mum.TensPolRel.tauCoord_rel | (intros; apply GlobalTheory.Mum.TensPolRel.tauCoord_rel <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

theorem _root_.GlobalTheory.T.tensorData_scalars_mem_maximalIdeal_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X → X → (FractionRing R)ˣ), (∀ a b, ∃ u ∈ unitsK R, k b a = u * k a b) → (∀ a a' b, ∃ u ∈ unitsK R, k (a + a') b = u * (k a b * k a' b)) → (∀ y, y ≠ 0 → ∃ s ∈ maximalIdeal R, (k y y : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (a' : (Fin r → X) → (FractionRing R)ˣ), (∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, k (z i) (z j) ^ W i j) → (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧ ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  first | exact @GlobalTheory.Mum.TensPolScal.scalars_tens | exact GlobalTheory.Mum.TensPolScal.scalars_tens | (intros; apply GlobalTheory.Mum.TensPolScal.scalars_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

theorem _root_.GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → ∀ (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1))) (a' : D'.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D' ga' a' → ∀ y : D'.X, ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, k (xe y i) (xe y j) ^ W i j := by
  first | exact @GlobalTheory.Mum.TensPol.scalar_tens | exact GlobalTheory.Mum.TensPol.scalar_tens | (intros; apply GlobalTheory.Mum.TensPol.scalar_tens <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.exists_finite_ext_sqrt_uniformiser_complete_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsPrincipalIdealRing V → ∀ ϖ : V, Irreducible ϖ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (t : V'), IsCN V' ∧ IsPrincipalIdealRing V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ t ^ 2 = f ϖ := by
  first | exact @GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser | exact GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser | (intros; apply GlobalTheory.USep.exists_finite_ext_sq_eq_uniformiser <;> assumption)
end
