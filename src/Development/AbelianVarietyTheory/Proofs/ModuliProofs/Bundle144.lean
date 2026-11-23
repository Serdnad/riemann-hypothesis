module

public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle134

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ProjSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
private theorem isImmersion_coprod_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsImmersion f] [IsImmersion g] : IsImmersion (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{0, 0} X' Y') ?_
  rintro (⟨⟩ | ⟨⟩)
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inl)
    have h := (isPullback_inl_inl_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inr)
    have h := (isPullback_inr_inr_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
theorem _root_.GlobalTheory.ProjSpace.isQProjOver_of_isCompl : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0})
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ →
    IsCompl (Set.range f₁) (Set.range f₂) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₁ ≫ s) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₂ ≫ s) →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s := by
  intro R _ X X₁ X₂ f₁ f₂ s h₁ h₂ hc q₁ q₂
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at q₁ q₂ ⊢
  obtain ⟨N₁, i₁, hi₁, hq₁, e₁⟩ := q₁
  obtain ⟨N₂, i₂, hi₂, hq₂, e₂⟩ := q₂
  have hP := _root_.GlobalTheory.ProjSpace.isProjOver_coprodDesc (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₁)
    (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₂)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver at hP
  obtain ⟨M, j, hj, ej⟩ := hP
  have hc' : IsCompl f₁.opensRange f₂.opensRange :=
    ⟨disjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.inf_eq_bot)),
      codisjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.sup_eq_top))⟩
  obtain ⟨hX⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f₁ f₂ hc'
  let e : X₁ ⨿ X₂ ≅ X := (coprodIsCoprod X₁ X₂).coconePointUniqueUpToIso hX
  have he₁ : coprod.inl ≫ e.hom = f₁ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.left⟩
  have he₂ : coprod.inr ≫ e.hom = f₂ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.right⟩
  have hcomp : (e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M = s := by
    rw [Category.assoc, Category.assoc, ej, Iso.inv_comp_eq]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, ← Category.assoc, he₁, e₁]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, ← Category.assoc, he₂, e₂]
  haveI := isImmersion_coprod_map i₁ i₂
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R M
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₁
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₂
  haveI : CompactSpace X₁ := (quasiCompact_iff_compactSpace (f₁ ≫ s)).mp (by rw [← e₁]; infer_instance)
  haveI : CompactSpace X₂ := (quasiCompact_iff_compactSpace (f₂ ≫ s)).mp (by rw [← e₂]; infer_instance)
  haveI : CompactSpace X := ⟨by
    rw [← Set.top_eq_univ, ← hc.sup_eq_top]
    exact (isCompact_range f₁.continuous).union (isCompact_range f₂.continuous)⟩
  haveI : QuasiCompact s := (quasiCompact_iff_compactSpace s).mpr inferInstance
  haveI : QuasiCompact ((e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M) := by
    rw [hcomp]; infer_instance
  exact ⟨M, e.inv ≫ coprod.map i₁ i₂ ≫ j, inferInstance,
    QuasiCompact.of_comp _ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M), hcomp⟩

end GlobalTheory.ProjSpace
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.TripleGlueMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonempty_cast {A B : Scheme.{0}} {t : SAB H A} {t' : SAB H B} {f g : A ⟶ B} (h : f = g)
    (m : SABMap t t' f) : Nonempty (SABMap t t' g) := by
  subst h
  exact ⟨m⟩

theorem exists_transport {A B : Scheme.{0}} (e : A ≅ B) (t : SAB H A) :
    ∃ t' : SAB H B, Nonempty (SABMap t' t e.inv) ∧ Nonempty (SABMap t t' e.hom) := by
  have hp := sabPull Out.CubePf.cubePull e.inv t
  have m := hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  obtain ⟨i, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨i'⟩ := nonempty_cast (by simp) i (g := e.hom ≫ e.inv)
  obtain ⟨k, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m i'
  exact ⟨_, ⟨m⟩, ⟨k⟩⟩

theorem mem_genericPoints_iso {A B : Scheme.{0}} (e : A ≅ B) (x : A) (hx : e.hom x ∈ genericPoints B) :
    x ∈ genericPoints A := by
  have hx' : closure {Scheme.homeoOfIso e x} ∈ irreducibleComponents B := by
    rw [Scheme.coe_homeoOfIso]
    exact hx
  have key := preimage_mem_irreducibleComponents hx' (Scheme.homeoOfIso e).isOpenEmbedding
    ⟨Scheme.homeoOfIso e x, subset_closure rfl, x, rfl⟩
  rw [(Scheme.homeoOfIso e).preimage_closure, ← Set.image_singleton,
    (Scheme.homeoOfIso e).injective.preimage_image] at key
  exact key

theorem generic_transport {A B : Scheme.{0}} (e : A ≅ B) {t : SAB H A} {t' : SAB H B} (m : SABMap t' t e.inv)
    (h : IsReduced A ∧ genericPoints A ⊆ abLocus t.G) : IsReduced B ∧ genericPoints B ⊆ abLocus t'.G := by
  obtain ⟨hr, hg⟩ := h
  refine ⟨@isReduced_of_isOpenImmersion _ _ e.inv _ hr, ?_⟩
  intro y hy
  have hy' : e.inv y ∈ genericPoints A := by
    apply mem_genericPoints_iso e
    have hyy : e.hom (e.inv y) = y := (Scheme.homeoOfIso e).apply_symm_apply y
    rw [hyy]
    exact hy
  have ha := hg hy'
  simp only [abLocus, Set.mem_setOf_eq] at ha ⊢
  intro K _ _ u hu
  have hp : IsProper (pullback.snd t.G.hom (u ≫ e.inv)) := by
    apply ha K (u ≫ e.inv)
    obtain ⟨p, rfl⟩ := hu
    exact ⟨p, rfl⟩
  have sq := (IsPullback.of_hasPullback t'.G.hom u).paste_horiz m.cart.1
  rw [← sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback t.G.hom (u ≫ e.inv))]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mpr hp

theorem exists_sab_glue_of_isPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  intro E _ _ _ H X X₀ X₁ X₂ ψ₁ ψ₂ φ₁ φ₂ t₀ t₁ t₂ m₁ m₂ h₁ h₂ sq hcov g₁ g₂
  obtain ⟨t₁', ⟨a₁⟩, ⟨b₁⟩⟩ := exists_transport ψ₁.isoOpensRange t₁
  obtain ⟨t₂', ⟨a₂⟩, ⟨b₂⟩⟩ := exists_transport ψ₂.isoOpensRange t₂
  have G₁ := generic_transport ψ₁.isoOpensRange a₁ g₁
  have G₂ := generic_transport ψ₂.isoOpensRange a₂ g₂
  have hr : Set.range (pullback.fst ψ₁ ψ₂ ≫ ψ₁) = Set.range (ψ₁.opensRange ⊓ ψ₂.opensRange).ι := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι]
    simp
  let e₀ : X₀ ≅ (ψ₁.opensRange ⊓ ψ₂.opensRange).toScheme :=
    sq.isoPullback ≪≫ IsOpenImmersion.isoOfRangeEq _ _ hr
  have he₀ : e₀.hom ≫ (ψ₁.opensRange ⊓ ψ₂.opensRange).ι = φ₁ ≫ ψ₁ := by
    simp [e₀]
  obtain ⟨t₀', ⟨a₀⟩, -⟩ := exists_transport e₀ t₀
  obtain ⟨c₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ a₀
  obtain ⟨d₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₁ c₁
  obtain ⟨c₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ a₀
  obtain ⟨d₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₂ c₂
  have k₁ : (e₀.inv ≫ φ₁) ≫ ψ₁.isoOpensRange.hom =
      X.homOfLE (inf_le_left : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₁.opensRange) := by
    rw [← cancel_mono ψ₁.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← he₀, Iso.inv_hom_id_assoc]
  have k₂ : (e₀.inv ≫ φ₂) ≫ ψ₂.isoOpensRange.hom =
      X.homOfLE (inf_le_right : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₂.opensRange) := by
    rw [← cancel_mono ψ₂.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← sq.w, ← he₀, Iso.inv_hom_id_assoc]
  obtain ⟨M₁⟩ := nonempty_cast k₁ d₁
  obtain ⟨M₂⟩ := nonempty_cast k₂ d₂
  have hUV : ψ₁.opensRange ⊔ ψ₂.opensRange = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
      Scheme.Hom.coe_opensRange, Set.mem_univ, iff_true]
    exact hcov x
  obtain ⟨t, n₁, n₂, -⟩ := GlobalTheory.TripleGlue.exists_sab_glue E H X _ _ t₁' t₂' t₀' M₁ M₂ hUV G₁ G₂
  obtain ⟨p₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₁ b₁
  obtain ⟨p₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ b₂
  exact ⟨t, nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₁) p₁,
    nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₂) p₂⟩

end GlobalTheory.TripleGlueMap
end
end
