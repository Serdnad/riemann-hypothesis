module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3248
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtChart

theorem mvPolynomial_stdSmooth (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  letI : IsEmpty Empty := Empty.instIsEmpty
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])


set_option backward.isDefEq.respectTransparency false in
theorem affineSpace_smooth (S : Scheme.{0}) (n : ℕ) : Smooth (𝔸(Fin n; S) ↘ S) := by
  have : SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
    refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
    have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
      MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
      HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
      (mvPolynomial_stdSmooth (ULift ℤ) n)
  exact SmoothOfRelativeDimension.smooth n _

end GlobalTheory.Mum.EtChart

namespace GlobalTheory.Mum

theorem etale_chart_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsSeparated b → LocallyOfFiniteType b → IsProper a → (∀ V : P'.Opens, Function.Bijective (a.app V).hom) → a ≫ b = X.ι ≫ E.f → Function.Bijective M.π.appTop.hom → Surjective M.π → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X.toScheme), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ X.ι ≫ E.H.ι ≫ G'.hom → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s) → ∃ V : P'.Opens, x ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hbsep hblft ha hsec hab hπΓ hπs x hx hx0 hinj hlift
  haveI := hbsep
  haveI := hblft
  haveI := ha
  haveI : IsProper M.π := M.proper
  haveI : IsProper (PSpace.str R E.N) := isProper_str R E.N
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by
    rw [reassoc_of% hab, E.f_over]
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_mem_fiber_of_geometric_lifting R M.S P' X.toScheme M.π (b ≫ PSpace.str R E.N) a (X.ι ≫ E.H.ι ≫ G'.hom) hπs x hx0 hlift
  have hz0 : M.π (G'.hom (E.H.ι (X.ι z))) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f z) key
    simp only [Scheme.Hom.comp_apply] at h1
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨y, hy⟩ := (GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R M.S M.π G' E).1 (X.ι z) hz0
  have hyb : E.j y = b x := by
    rw [← hy, ← hz]
    have h1 := congrArg (fun f : X.toScheme ⟶ PSpace R E.N => f z) hab
    simpa [Scheme.Hom.comp_apply] using h1.symm
  obtain ⟨W0, g, τ0, O, e, hyO, hOW, hτ0, he, he2, he3⟩ := GlobalTheory.T.exists_etale_coordinates_through_immersion R E.N E.Y E.smooth E.j E.imm E.j_over y
  have hxW1 : x ∈ b ⁻¹ᵁ W0 := by
    show b x ∈ W0
    rw [← hyb]; exact hOW hyO
  let τ1 : (b ⁻¹ᵁ W0).toScheme ⟶ 𝔸(Fin g; Sp R) := (b ∣_ W0) ≫ τ0
  have hτ1 : τ1 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = (b ⁻¹ᵁ W0).ι ≫ b ≫ PSpace.str R E.N := by
    simp only [τ1, Category.assoc, hτ0, morphismRestrict_ι_assoc]
  let c1 : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π :=
    pullback.lift ((a ∣_ (b ⁻¹ᵁ W0)) ≫ τ1) ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (by
      rw [Category.assoc, hτ1, morphismRestrict_ι_assoc, key]
      simp only [Category.assoc])
  have hF := GlobalTheory.T.coordinateMap_etale_near_properFibre R hR M G' hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c1
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨W, hWW1, hxW, hWet⟩ := GlobalTheory.T.exists_open_etale_restrict_of_universallyClosed' X.toScheme P' _ a (b ⁻¹ᵁ W0) c1 x inferInstance hxW1 hF
  have hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ (b ⁻¹ᵁ W0) := fun _ hp => hWW1 hp
  let c := X.toScheme.homOfLE hle ≫ c1
  let τ := P'.homOfLE hWW1 ≫ τ1
  let U : Over (Sp R) := Over.mk (W.ι ≫ b ≫ PSpace.str R E.N)
  have hsq : X.toScheme.homOfLE hle ≫ (a ∣_ (b ⁻¹ᵁ W0)) = (a ∣_ W) ≫ P'.homOfLE hWW1 := by
    rw [← cancel_mono (b ⁻¹ᵁ W0).ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
      Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  obtain ⟨x', hx'⟩ : x ∈ Set.range W.ι := by rw [Scheme.Opens.range_ι]; exact hxW
  have hLFT : LocallyOfFiniteType U.hom := by
    show LocallyOfFiniteType (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hSep : IsSeparated U.hom := by
    show IsSeparated (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hPr : IsProper (a ∣_ W) := inferInstance
  have hSec : ∀ V : U.left.Opens, Function.Bijective ((a ∣_ W).app V).hom := by
    intro V
    rw [morphismRestrict_app]
    exact (ConcreteCategory.bijective_of_isIso (X.toScheme.presheaf.map (eqToHom (image_morphismRestrict_preimage a W V)).op)).comp (hsec (W.ι ''ᵁ V))
  have hτ : τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom := by
    simp only [τ, Category.assoc, hτ1]
    rw [Scheme.homOfLE_ι_assoc]
    rfl
  have hc1 : c ≫ pullback.fst _ _ = (a ∣_ W) ≫ τ := by
    simp only [c, τ, c1, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, hsq, Category.assoc]
  have hc2 : c ≫ pullback.snd _ _ = (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom := by
    simp only [c, c1, Category.assoc, pullback.lift_snd]
    rw [Scheme.homOfLE_ι_assoc]
  have hcl : IsClosed ({x'} : Set U.left) := by
    have : ({x'} : Set U.left) = W.ι ⁻¹' {x} := by
      ext p
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hx', fun h => W.ι.isOpenEmbedding.injective (h.trans hx'.symm)⟩
    rw [this]
    exact hx.preimage W.ι.continuous
  have hx'0 : U.hom x' = closedPoint R := by
    show (W.ι ≫ b ≫ PSpace.str R E.N) x' = closedPoint R
    simpa [Scheme.Hom.comp_apply, hx'] using hx0
  have hrange : ∀ (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ U.left), Set.range ξ = {x'} → Set.range (ξ ≫ W.ι) = {x} := by
    intro Ω _ ξ hr
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    erw [hr]
    rw [Set.image_singleton, hx']
  have hinj' : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme), Set.range (p ≫ (a ∣_ W)) = {x'} →
      p ≫ (a ∣_ W) = p' ≫ (a ∣_ W) → p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom →
      p = p' := by
    intro Ω _ p p' hr he hb
    have hr' : Set.range ((p ≫ (a ⁻¹ᵁ W).ι) ≫ a) = {x} := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc]
      exact hrange Ω _ hr
    have h2 : (p ≫ (a ⁻¹ᵁ W).ι) ≫ a = (p' ≫ (a ⁻¹ᵁ W).ι) ≫ a := by
      simp only [Category.assoc, ← morphismRestrict_ι]
      rw [reassoc_of% he]
    have := hinj Ω (p ≫ (a ⁻¹ᵁ W).ι) (p' ≫ (a ⁻¹ᵁ W).ι) hr' h2 (by simpa only [Category.assoc] using hb)
    exact (cancel_mono _).1 this
  have hlift' : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ M.S), Set.range ξ = {x'} →
      ξ ≫ U.hom = s ≫ M.π → ∃ p : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme, p ≫ (a ∣_ W) = ξ ∧ p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
    intro Ω _ _ ξ s hr hs
    obtain ⟨p, hp1, hp2⟩ := hlift Ω (ξ ≫ W.ι) s (hrange Ω ξ hr) (by rw [Category.assoc]; exact hs)
    have hsub : Set.range p.base ⊆ Set.range (a ⁻¹ᵁ W).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      show a (p t) ∈ W
      have h3 : a (p t) = W.ι (ξ t) := by
        have h4 := congrArg (fun f : Sp Ω ⟶ P' => f t) hp1
        simpa [Scheme.Hom.comp_apply] using h4
      rw [h3]
      have h5 := Set.mem_range_self (f := W.ι) (ξ t)
      rwa [Scheme.Opens.range_ι] at h5
    refine ⟨IsOpenImmersion.lift (a ⁻¹ᵁ W).ι p hsub, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, hp1]
    · rw [IsOpenImmersion.lift_fac_assoc]; exact hp2
  obtain ⟨V, hxV, hVet, hVpb⟩ := GlobalTheory.T.etaleCoordinates_descend_along_proper_map R hR M.S (a ⁻¹ᵁ W).toScheme M.π U (a ∣_ W)
    ((a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) g τ c M.proper hπs hπΓ hLFT hSep hPr hSec hτ hc1 hc2 (hWet hle)
    x' hcl hx'0 hinj' hlift'
  refine ⟨W.ι ''ᵁ V, ⟨x', hxV, hx'⟩, ?_, ?_⟩
  · haveI : Etale (V.ι ≫ τ) := hVet
    haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := GlobalTheory.Mum.EtChart.affineSpace_smooth (Sp R) g
    have e1 : (W.ι ''ᵁ V).ι ≫ b ≫ PSpace.str R E.N =
        (W.ι.isoImage V).inv ≫ (V.ι ≫ τ) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) := by
      rw [Category.assoc, hτ, Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
      rfl
    rw [e1]
    infer_instance
  · exact GlobalTheory.T.isPullback_restrict_image_of_restrict_restrict P' X.toScheme M.S (Sp R) a W V (X.ι ≫ E.H.ι ≫ G'.hom) (b ≫ PSpace.str R E.N) M.π hVpb

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finite_theta_sections_thickening_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_closed | exact GlobalTheory.Mum.exists_ratio_gen_closed | (intros; apply GlobalTheory.Mum.exists_ratio_gen_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.factorPairing_mumfordBundle_principal_polarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  first | exact @GlobalTheory.Mum.pairing_factor_mumford | exact GlobalTheory.Mum.pairing_factor_mumford | (intros; apply GlobalTheory.Mum.pairing_factor_mumford <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.thetaConst_eq_lam_root_mul : ∀ (n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∀ (th : LB.Sec (LPow D.P.A D.P.L ((1 : ℕ) : ℤ) (Over.mk (spMap ev)))), IsGenSec D.P.A D.P.L ((1 : ℕ) : ℤ) th → ∃ (M : ℕ) (lam : K), 1 ≤ M ∧ ∀ (y : Over.mk (spMap ev) ⟶ D.P.A) (c : K), GlobalTheory.Ex.OneGen.ThG D.P.A D.P.L ρ₀ (n ^ j) th y (GlobalTheory.Ex.fnOf c) → ∃ (c₀ : C) (ζ : K), ζ ^ M = 1 ∧ c = lam * ζ * ev (u 0 c₀) := by
  intro n hn hodd
  exact ⟨1, fun j hj V₁ _ _ _ hV hunit =>
    GlobalTheory.USep.thetaConst_eq_lam_root_mul_unit n hn hodd j hj V₁ hV (hunit n hn.ne_zero)⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegenerationData_psi_pos_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Q.IsPos (maximalIdeal R) → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  first | exact @GlobalTheory.Mum.TensPol.psi_pos_tendsto | exact GlobalTheory.Mum.TensPol.psi_pos_tendsto | (intros; apply GlobalTheory.Mum.TensPol.psi_pos_tendsto <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.ULift

theorem psiQ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ) (hq : ∀ χ, u.PsiNorm χ (Real.exp (-q χ))) (χ : u.D.toPre.X) : l.q χ = q χ := by
  have h := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ))
  linarith



theorem labels_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLabW X₁ w₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLabW D.X w₂ (D.lift ct y h) yy ∧ D.Compat yy₁ yy := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p _ z₁ ct yy₁ hL y h
  unfold UIsLabW at hL
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, hi, hu, hR, G, iG, α, β, hα, hβ, hLB, hm, y₀, hy₀, u, lb, j,
    hq, hyy, hcong⟩ := hL
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
    y₂, hy₂, hint₂, u₂, e, T, hpsi, hpt, hw, hfw, hbw⟩ :=
    GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup E H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' hS hi hu hR G iG α β
      hα hβ hLB hm y₀ hy₀ u
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨lb₂⟩ := GlobalTheory.ZH.labels_exist hLaws hLaws2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  have hmap : (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      AddSubgroup.comap (e.trans j).toAddMonoidHom
        (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : ct.T.P.D.toPre.X →+ ct.T.P.D.toPre.X).range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(e.trans j) z, by simp [map_nsmul]⟩
  refine ⟨(QuotientAddGroup.map _ _ (e.trans j).toAddMonoidHom hmap).comp lb₂.yy, ?_, ?_⟩
  · unfold UIsLabW
    refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
      y₂, hy₂, u₂, lb₂, e.trans j, ?_, ?_, ?_⟩
    · intro χ
      rw [psiQ u₂ lb₂ (fun χ => lb.q (e χ)) (fun χ => hpsi χ _ (lb.q_eq (e χ))) χ]
      exact hq (e χ)
    · intro a χ hχ
      rw [AddMonoidHom.comp_apply, hχ, QuotientAddGroup.map_mk]
      rfl
    · intro k a pk pk' x x' w w' hk hx hx' hwx hwx' hww
      obtain ⟨q, hqy, hq'⟩ := hfw k pk x hk hx
      obtain ⟨q', hqy', hq''⟩ := hfw k pk' x' hk hx'
      obtain ⟨v, hvα, hvβ⟩ := hw x w hwx
      obtain ⟨v', hvα', hvβ'⟩ := hw x' w' hwx'
      have hc := hcong k a q q' (T x) (T x') v v' hk hq' hq'' hvα hvα'
        (by rw [hvβ', hww, ← Category.assoc v, hvβ, Category.assoc])
      rw [hqy, hqy'] at hc
      exact hc
  · unfold UDeep.Compat
    intro a μ hμ
    have hN₁ : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
    have hr₁ : 0 < X₁.S.r := by
      obtain ⟨i, -, hi'⟩ := X₁.ρ.r_eq
      rw [hi']; exact pow_pos X₁.ρ.n_prime.pos _
    have hN₂ : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
    have hr₂ : 0 < D.X.S.r := by
      obtain ⟨i, -, hi'⟩ := D.X.ρ.r_eq
      rw [hi']; exact pow_pos D.X.ρ.n_prime.pos _
    have hk1 : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos hr₁ hN₁
    have hk2 : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos hr₂ hN₂
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]
      exact Dvd.dvd.mul_left (D.dvd.trans (dvd_pow_self _ two_ne_zero)) _
    have hd : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) = D.X.S.r * D.X.S.N :=
      Nat.div_mul_cancel hdvd
    have hd1 : 1 ≤ D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) := Nat.div_pos (Nat.le_of_dvd hk2 hdvd) hk1
    obtain ⟨pk₀, x₀, hx₀, hx₀φ⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest _ _ _ ρ' p y₀ u a
    have h1 : lb.yy a = QuotientAddGroup.mk pk₀.y := lb.yy_eq a pk₀ x₀ hx₀ hx₀φ
    have h2 := hyy a pk₀.y h1
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.QLevelRescale.exists_qkPt_rescale _ _ _ ρ' p y₀ u (X₁.S.r * X₁.S.N)
      (D.X.S.r * D.X.S.N) (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) pk₀ x₀ hk1 hd1 hd.symm hx₀
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw _ pk' x₀ hk2 hpk'
    have hx₂ : (T.symm x₀).left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left :=
      (hpt (T.symm x₀) a).2 (by rw [Equiv.apply_symm_apply]; exact hx₀φ)
    have h3 : lb₂.yy (D.lab a) = QuotientAddGroup.mk pk₂.y := lb₂.yy_eq (D.lab a) pk₂ (T.symm x₀) hpk₂ hx₂
    rw [AddMonoidHom.comp_apply, h3, QuotientAddGroup.map_mk]
    have h4 : (e.trans j).toAddMonoidHom pk₂.y = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • j pk₀.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h4]
    rw [h2] at hμ
    rw [QuotientAddGroup.eq] at hμ ⊢
    obtain ⟨z, hz⟩ := hμ
    refine ⟨z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    calc (D.X.S.r * D.X.S.N) • z
        = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • (X₁.S.r * X₁.S.N) • z := by rw [smul_smul, hd]
      _ = _ := by rw [hz, smul_add, smul_neg]

end GlobalTheory.UPoinc.ULift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.labelledUnitaryTraits_lattices_equiv_connectedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → ∀ (ct ct' : UCTrait X p z) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → y' ≫ q = ct'.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ θ : ct.T.P.D.toPre.X ≃+ ct'.T.P.D.toPre.X, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (a : 𝓞 E) v, θ (a • v) = a • θ v := by
  first | exact @GlobalTheory.UPoinc.GFib.labelled_lattices_equiv | exact GlobalTheory.UPoinc.GFib.labelled_lattices_equiv | (intros; apply GlobalTheory.UPoinc.GFib.labelled_lattices_equiv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_add_cub : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (x x' y : Z ⟶ D.P.A) (x₀ x₀' y₀ : Over.mk (Z.hom ≫ spMap ω) ⟶ T.B), x.left ≫ β = x₀.left → x'.left ≫ β = x₀'.left → y.left ≫ β = y₀.left → ∀ (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (x * x') y).left z J J' * cubV D.cub z J' x x' y = lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J x₀ x₀' y₀) ∧ lamVal w (lift y (x * x')).left z J J' * cubV D.cub z J' y x x' = lamVal w (lift y x).left z J J' * lamVal w (lift y x').left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J y₀ x₀ x₀') := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hτ hF Z x x' y x₀ x₀' y₀ hx hx' hy z J J' hJ hJ'
  have hn : ∀ (T' : Over (Sp V)) (z : T'.left) (J : (T'.left ⟶ T.B.left) → T.M.L.ι)
      (J' : (T'.left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T' ⟶ D.P.A) (1 : T' ⟶ D.P.A)).left z J J' = 1 := fun T' z J J' hJ hJ' =>
    (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hτ hF T' 1 z J J' hJ hJ').1
  have L := GlobalTheory.LamRigid.lam_iso_laws (Sp W) (Sp V) T.B D.P.A T.M _ T.cub D.cub (spMap ω) β ββ w hF.1 D.P.isAb
    hF.2.1 hF.2.2.1 hn
  have C₁ : IsCub (cubV D.cub z J') := isCub_cubV D.cub hJ'
  have C₀ : IsCub (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J) := isCub_cubV T.cub hJ
  have A₁ := (L Z x x' y z J J' hJ hJ').2 x₀ x₀' y₀ hx.symm hx'.symm hy.symm
  refine ⟨?_, ?_⟩
  · rw [A₁]; simp only [id]; ac_rfl
  · rw [(L Z y y (x * x') z J J' hJ hJ').1, (L Z y y x z J J' hJ hJ').1, (L Z y y x' z J J' hJ hJ').1,
      C₁.s01 y x x', C₁.s12 x y x', C₀.s01 y₀ x₀ x₀', C₀.s12 x₀ y₀ x₀', A₁]
    simp only [id]; ac_rfl

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.tautological_lattice_identification_eq_id : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  first | exact @GlobalTheory.TInj.lattice_iso_eq_of_tautPts | exact GlobalTheory.TInj.lattice_iso_eq_of_tautPts | (intros; apply GlobalTheory.TInj.lattice_iso_eq_of_tautPts <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem exists_baseSch : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) :=
  BaseSch.exists_baseSch_of_homScheme GlobalTheory.UCanonHom.homScheme_low

end GlobalTheory.UCanon
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pulledLowerObject_descends_with_points_subfield : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (o' : LowObj D' c ((ev.comp iw).comp L.b)) (m₁ : ObjMap o' L.o (spMap (ev.comp iw))), ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left)) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (θ : o'.t.G.left ⟶ B'.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) → IsGrpPullback o'.t.G B' (𝟙 _) θ → LBIso o'.t.PP.L (Q.P.L.pull (θ ≫ π₁)) → (∀ (x : Sp K ⟶ o'.t.G.left) (a : Q.X), x ≫ o'.t.G.hom = 𝟙 _ → x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c (l.M' • e a)).left → x ≫ θ ≫ π₁ = spMap ev ≫ (Q.c a).left) → IsGrpPullback o'.t.G B₀ (spMap k₀.subtype) (θ ≫ π₀) ∧ LBIso o'.t.PP.L (M₀.pull (θ ≫ π₀)) ∧ ∀ y : L.D.X, ∃ x : Sp K ⟶ o'.t.G.left, x ≫ o'.t.G.hom = 𝟙 _ ∧ x ≫ m₁.toSABMap.φ ≫ L.φB = spMap (ev.comp iw) ≫ (L.D.c y).left ∧ ∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ θ ≫ π₀ = spMap k₀.subtype ≫ x₀ := by
  first | exact @GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points | exact GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points | (intros; apply GlobalTheory.UCanon.PtsDescent.pulledObj_descends_with_points <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tautologicalChart_isEtaleCompletion_localRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTautB C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom := by
  first | exact @GlobalTheory.TautEtaleB.tautB_isEtaleCompletion | exact GlobalTheory.TautEtaleB.tautB_isEtaleCompletion | (intros; apply GlobalTheory.TautEtaleB.tautB_isEtaleCompletion <;> assumption)
end
