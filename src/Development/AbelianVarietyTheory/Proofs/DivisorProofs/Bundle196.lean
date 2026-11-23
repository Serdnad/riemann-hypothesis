module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Mathlib.AlgebraicGeometry.Scheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle144
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle039
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

noncomputable section
namespace GlobalTheory.NotCartier

theorem ringKrullDim_stalk_le_one {X : Scheme.{0}} [IsLocallyNoetherian X] (J : X.IdealSheafData) (x : X)
    (hx : x ∈ J.support) (hmin : ∀ z ∈ J.support, z ⤳ x → z = x) (V : X.affineOpens) (hxV : x ∈ V.1)
    (hP : (J.ideal V).IsPrincipal) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  haveI := IsLocallyNoetherian.component_noetherian V
  have hV : IsAffineOpen V.1 := V.2
  let p := hV.primeIdealOf ⟨x, hxV⟩
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hp : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hsupp : ∀ q : Spec Γ(X, V.1), hV.fromSpec q ∈ J.support ↔ J.ideal V ≤ q.asIdeal := by
    intro q
    have hqV : hV.fromSpec q ∈ V.1 := (Set.ext_iff.1 hV.range_fromSpec _).1 ⟨q, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hqV]
    change q ∈ hV.fromSpec ⁻¹' X.zeroLocus (J.ideal V : Set Γ(X, V.1)) ↔ _
    rw [hV.fromSpec_preimage_zeroLocus]
    exact Iff.rfl
  have hmem : p.asIdeal ∈ (J.ideal V).minimalPrimes := by
    refine ⟨⟨p.isPrime, (hsupp p).1 (hp ▸ hx)⟩, fun q hq hqp => ?_⟩
    let y : PrimeSpectrum Γ(X, V.1) := ⟨q, hq.1⟩
    have hsp : hV.fromSpec y ⤳ x := by
      have := ((PrimeSpectrum.le_iff_specializes y p).1 hqp).map hV.fromSpec.continuous
      rwa [hp] at this
    have hyx : hV.fromSpec y = hV.fromSpec p := (hmin _ ((hsupp y).2 hq.2) hsp).trans hp.symm
    have := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hyx)
    exact le_of_eq this.symm
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)]
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem

end GlobalTheory.NotCartier

namespace GlobalTheory.NotCartier

theorem ker_ne_bot_and_not_effCartier : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y)
    [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) →
    i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  intro W Y _ _ i _ hdim
  set y := i (genericPoint W) with hy
  have hsub : (i.ker.support : Set Y) ⊆ closure {y} := by
    rw [Scheme.Hom.support_ker]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ closure {genericPoint W} := by
      rw [(genericPoint_spec W).def]; trivial
    exact specializes_iff_mem_closure.1 ((specializes_iff_mem_closure.2 hw).map i.continuous)
  have hyS : y ∈ i.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure ⟨_, rfl⟩
  have hmin : ∀ z ∈ i.ker.support, z ⤳ y → z = y := fun z hz hzy =>
    (hzy.antisymm (specializes_iff_mem_closure.2 (hsub hz))).eq
  have hlt : ¬ ringKrullDim (Y.presheaf.stalk y) ≤ 1 := fun h => by
    have := hdim.trans h
    exact absurd this (by decide)
  refine ⟨fun hbot => ?_, fun U hyU hC => ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine hlt (ringKrullDim_stalk_le_one i.ker y hyS hmin ⟨V, hV⟩ hyV ?_)
    rw [hbot, Scheme.IdealSheafData.ideal_bot]
    exact bot_isPrincipal
  · let x : U.toScheme := ⟨y, hyU⟩
    obtain ⟨V, f, hxV, -, hf⟩ := hC x
    have hxS : x ∈ (i.ker.comap U.ι).support := by
      rw [Scheme.IdealSheafData.support_comap]; exact hyS
    have hminU : ∀ z ∈ (i.ker.comap U.ι).support, z ⤳ x → z = x := by
      intro z hz hzx
      rw [Scheme.IdealSheafData.support_comap] at hz
      exact Subtype.ext (hmin _ hz (hzx.map U.ι.continuous))
    have h1 := ringKrullDim_stalk_le_one _ x hxS hminU V hxV ⟨⟨f, hf⟩⟩
    rw [← ringKrullDim_eq_of_ringEquiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv] at h1
    exact hlt h1

end GlobalTheory.NotCartier
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces :
    ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  classical
  intro X Z hZ hpc
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have key : ∀ (p : PrimeSpectrum Γ(X, U)) (a : Γ(X, U)),
      hU.fromSpec p ∈ X.basicOpen a ↔ a ∉ p.asIdeal := by
    intro p a
    have h := hU.fromSpec_preimage_basicOpen a
    have h2 : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a ↔ p ∈ PrimeSpectrum.basicOpen a := by
      rw [h]; rfl
    exact h2
  have hopen : IsOpen (X := PrimeSpectrum Γ(X, U)) (hU.fromSpec ⁻¹' Z) := by
    refine GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces Γ(X, U) _ ?_ ?_
    · intro p q hpq hp
      exact hZ (hpq.map hU.fromSpec.continuous) hp
    · intro p hp
      obtain ⟨W, W', J, hWW', hpW, hpJ, hsub⟩ := hpc _ hp
      have hpU : hU.fromSpec p ∈ U := hU.range_fromSpec.le ⟨p, rfl⟩
      obtain ⟨a, haW, hpa⟩ := hU.exists_basicOpen_le (V := W) ⟨_, hpW⟩ hpU
      have hc : ∀ c : Γ(X, W'), ∃ c' : Γ(X, U),
          X.basicOpen c' = X.basicOpen a ⊓ X.basicOpen c := by
        intro c
        obtain ⟨c', hc'⟩ := hU.basicOpen_basicOpen_is_basicOpen a
          (X.presheaf.map (homOfLE (haW.trans hWW')).op c)
        exact ⟨c', by rw [hc', Scheme.basicOpen_res]⟩
      choose g hg using hc
      refine ⟨a, J.image g, (key p a).1 hpa, ?_, ?_⟩
      · intro c' hc'
        obtain ⟨c, hcJ, rfl⟩ := Finset.mem_image.1 hc'
        by_contra hn
        have := (key p _).2 hn
        rw [hg] at this
        exact hpJ c hcJ this.2
      · intro t hta htI
        have hta' := (key t a).2 hta
        refine hsub _ (haW hta') fun c hcJ htc => ?_
        refine (key t (g c)).1 ?_ (htI _ (Finset.mem_image_of_mem g hcJ))
        rw [hg]
        exact ⟨hta', htc⟩
  refine ⟨hU.fromSpec '' (hU.fromSpec ⁻¹' Z), Set.image_preimage_subset _ _,
    hU.fromSpec.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  obtain ⟨p, rfl⟩ := hU.range_fromSpec.ge hxU
  exact ⟨p, hx, rfl⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.points_of_scheme_over_artinian_fibre_product : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Y₁ Y₂ Y₀ : Scheme.{0}) (p : Y ⟶ Spec P) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback j₁ p₁ p (Spec.map f₁) → IsPullback j₂ p₂ p (Spec.map f₂) → IsPullback i₁ p₀ p₁ (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) ∧ ∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → ∃ y₀ : Y₀, i₁ y₀ = y₁ ∧ i₂ y₀ = y₂ := by
  first | exact @GlobalTheory.PinchPoints.points_of_pinch | exact GlobalTheory.PinchPoints.points_of_pinch | (intros; apply GlobalTheory.PinchPoints.points_of_pinch <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem _root_.GlobalTheory.T.exists_pow_kills_on_compact_of_local : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens), IsCompact (W : Set S) → ∀ (s c : Γ(S, W)), (∀ y ∈ W, ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0) → ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom (s ^ n * c) = 0 := by
  first | exact @GlobalTheory.pow_kills_on_compact_of_local | exact GlobalTheory.pow_kills_on_compact_of_local | (intros; apply GlobalTheory.pow_kills_on_compact_of_local; all_goals assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.scheme_hom_ext_of_jointly_surjective_of_app_injective : ∀ (Z Z₁ Z₂ X : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z), (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) → (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) → ∀ f g : Z ⟶ X, e₁ ≫ f = e₁ ≫ g → e₂ ≫ f = e₂ ≫ g → f = g := by
  first | exact @GlobalTheory.scheme_hom_ext_of_jointly_injective | exact GlobalTheory.scheme_hom_ext_of_jointly_injective | (intros; apply GlobalTheory.scheme_hom_ext_of_jointly_injective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.isPullback_app_of_isBasis_opens : ∀ (Y₀ Y₁ Y₂ Y : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (𝒱 : Set Y.Opens), TopologicalSpace.Opens.IsBasis 𝒱 → (∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  first | exact @GlobalTheory.PinchBasis.isPullback_app_of_isBasis | exact GlobalTheory.PinchBasis.isPullback_app_of_isBasis | (intros; apply GlobalTheory.PinchBasis.isPullback_app_of_isBasis <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_valuationRing_dominating_specialization : ∀ (X : Scheme.{0}) (x' x : X), x' ⤳ x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (g : Spec (CommRingCat.of V) ⟶ X), g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  first | exact @GlobalTheory.exists_valuationRing_of_specializes | exact GlobalTheory.exists_valuationRing_of_specializes | (intros; apply GlobalTheory.exists_valuationRing_of_specializes <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem isIntegrallyClosed_stalk_spec_field (K : Type) [Field K] (x : Spec (.of K)) :
    IsIntegrallyClosed ((Spec (.of K)).presheaf.stalk x) := by
  have hU := isAffineOpen_top (Spec (.of K))
  letI := (Spec (.of K)).presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : (Spec (.of K)).Opens))
  have h1 := hU.isLocalization_stalk ⟨x, trivial⟩
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  exact (isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (hU.primeIdealOf ⟨x, trivial⟩).asIdeal
    ((Spec (.of K)).presheaf.stalk x)).2

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite

theorem _root_.GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  first | exact @GlobalTheory.relSpec_map_isIso_over_basicOpen | exact GlobalTheory.relSpec_map_isIso_over_basicOpen | (intros; apply GlobalTheory.relSpec_map_isIso_over_basicOpen <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing

theorem _root_.GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y) (z : Y) (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i], Function.Surjective (IsLocalRing.ResidueField.map i) → ∀ (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (y : X), pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = IsLocalRing.closedPoint R → pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v ⤳ y → π y = z → ∃ w : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π), v ⤳ w ∧ pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π w = y := by
  first | exact @GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | exact GlobalTheory.specializes_lift_closedFibre_stalkBaseChange | (intros; apply GlobalTheory.specializes_lift_closedFibre_stalkBaseChange <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  first | exact @GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | exact GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | (intros; apply GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv <;> assumption)
end

section

open Set

namespace GlobalTheory


open Set in
theorem _root_.GlobalTheory.exists_merge_fibre_primitives : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (C' : Set (Fin g → ℂ)) (G G' : K → P × (Fin g → ℂ) → ℂ), (∀ k, IsOpen (W k)) → IsOpen Z → IsOpen C → Convex ℝ C → IsOpen C' → Convex ℝ C' → (C ∩ C').Nonempty → (∀ p ∈ Z ×ˢ (C ∪ C'), ∃ k, p ∈ W k) → ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) → ((∀ k, AnalyticOnNhd ℂ (G' k) (W k ∩ Z ×ˢ C')) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C' → fderiv ℂ (G' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C' → G' k p - G' l p = c k l p) → ∃ G'' : K → P × (Fin g → ℂ) → ℂ, ((∀ k, AnalyticOnNhd ℂ (G'' k) (W k ∩ Z ×ˢ (C ∪ C'))) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ (C ∪ C') → fderiv ℂ (G'' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ (C ∪ C') → G'' k p - G'' l p = c k l p) := by
  intro P _ _ _ g K W c ω Z C C' G G' hW hZ hC hCc hC' hC'c hne hcov ⟨hGa, hGd, hGc⟩
    ⟨hG'a, hG'd, hG'c⟩
  have hsubC : Z ×ˢ (C ∩ C') ⊆ Z ×ˢ C := prod_mono subset_rfl inter_subset_left
  have hsubC' : Z ×ˢ (C ∩ C') ⊆ Z ×ˢ C' := prod_mono subset_rfl inter_subset_right
  obtain ⟨h, hh, hGG⟩ := _root_.GlobalTheory.exists_analytic_param_of_primitives_on_box W c ω Z (C ∩ C') G G' hW hZ
    (hC.inter hC') (hCc.inter hC'c) hne
    (fun p hp => hcov p (prod_mono subset_rfl subset_union_left (hsubC hp)))
    ⟨fun k => (hGa k).mono (inter_subset_inter_right _ hsubC),
      fun k a p hpk hp => hGd k a p hpk (hsubC hp),
      fun k l p hk hl hp => hGc k l p hk hl (hsubC hp)⟩
    ⟨fun k => (hG'a k).mono (inter_subset_inter_right _ hsubC'),
      fun k a p hpk hp => hG'd k a p hpk (hsubC' hp),
      fun k l p hk hl hp => hG'c k l p hk hl (hsubC' hp)⟩
  classical
  have hCeq : ∀ k, ∀ q ∈ W k ∩ Z ×ˢ C,
      (if q.2 ∈ C then G k q else G' k q + h q.1) = G k q := fun k q hq => if_pos hq.2.2
  have hC'eq : ∀ k, ∀ q ∈ W k ∩ Z ×ˢ C',
      (if q.2 ∈ C then G k q else G' k q + h q.1) = G' k q + h q.1 := by
    intro k q hq
    split_ifs with hqC
    · exact hGG k q hq.1 ⟨hq.2.1, hqC, hq.2.2⟩
    · rfl
  have hU : ∀ k, IsOpen (W k ∩ Z ×ˢ C) := fun k => (hW k).inter (hZ.prod hC)
  have hU' : ∀ k, IsOpen (W k ∩ Z ×ˢ C') := fun k => (hW k).inter (hZ.prod hC')
  have evC : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C,
      (fun q => if q.2 ∈ C then G k q else G' k q + h q.1) =ᶠ[nhds p] G k :=
    fun k p hp => Filter.eventually_of_mem ((hU k).mem_nhds hp) (hCeq k)
  have evC' : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C',
      (fun q => if q.2 ∈ C then G k q else G' k q + h q.1) =ᶠ[nhds p]
        fun q => G' k q + h q.1 :=
    fun k p hp => Filter.eventually_of_mem ((hU' k).mem_nhds hp) (hC'eq k)
  have memcase : ∀ p ∈ Z ×ˢ (C ∪ C'), p ∈ Z ×ˢ C ∨ p ∈ Z ×ˢ C' := fun p hp =>
    hp.2.elim (fun h1 => Or.inl ⟨hp.1, h1⟩) (fun h2 => Or.inr ⟨hp.1, h2⟩)
  have hfd : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C', HasFDerivAt (fun q => G' k q + h q.1)
      (fderiv ℂ (G' k) p + (fderiv ℂ h p.1).comp (ContinuousLinearMap.fst ℂ P (Fin g → ℂ))) p :=
    fun k p hp => (hG'a k p hp).differentiableAt.hasFDerivAt.add
      ((hh p.1 hp.2.1).differentiableAt.hasFDerivAt.comp p (hasFDerivAt_fst))
  refine ⟨fun k => (fun k p => if p.2 ∈ C then G k p else G' k p + h p.1) k, ?_⟩
  refine ⟨fun k p hp => ?_, fun k a p hpk hp => ?_, fun k l p hk hl hp => ?_⟩
  · dsimp only
    rcases memcase p hp.2 with h1 | h2
    · exact (hGa k p ⟨hp.1, h1⟩).congr (evC k p ⟨hp.1, h1⟩).symm
    · exact (hfd k p ⟨hp.1, h2⟩).differentiableAt |> fun _ =>
        ((hG'a k p ⟨hp.1, h2⟩).add ((hh p.1 h2.1).comp analyticAt_fst)).congr
          (evC' k p ⟨hp.1, h2⟩).symm
  · dsimp only
    rcases memcase p hp with h1 | h2
    · rw [(evC k p ⟨hpk, h1⟩).fderiv_eq]
      exact hGd k a p hpk h1
    · rw [(evC' k p ⟨hpk, h2⟩).fderiv_eq, (hfd k p ⟨hpk, h2⟩).fderiv,
        ContinuousLinearMap.add_apply, hG'd k a p hpk h2]
      simp
  · dsimp only
    rcases memcase p hp with h1 | h2
    · rw [if_pos h1.2, if_pos h1.2]
      exact hGc k l p hk hl h1
    · rw [hC'eq k p ⟨hk, h2⟩, hC'eq l p ⟨hl, h2⟩, add_sub_add_right_eq_sub]
      exact hG'c k l p hk hl h2

end GlobalTheory
end
