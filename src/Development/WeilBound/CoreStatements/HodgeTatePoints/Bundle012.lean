module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RaTlog
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

section

noncomputable section

namespace PositivityTheory.HtPt.Mc

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem near_all {ι : Type} [Finite ι] (p : Cpt ξ) (P : ι → Cpt ξ → Prop)
    (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  choose U hU hP using h
  refine ⟨⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩, ?_, fun q hq i => hP i q ?_⟩
  · exact Set.mem_iInter.2 hU
  · exact Set.mem_iInter.1 hq i

theorem near_mem_span {n : ℕ} (g : Fin n → E) (p : Cpt ξ) (e : E)
    (h : e ∈ Submodule.span (regAt ξ p) (Set.range g)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range g) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => (c i : Ω) ∈ regAt ξ q)
    fun i => (regAt_unitAt_open X Ω ξ p (c i)).1 (c i).2
  exact ⟨U, hU, fun q hq => (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨c i, H q hq i⟩, hc⟩⟩

theorem near_span_eq {n m : ℕ} (g : Fin n → E) (b : Fin m → E) (p : Cpt ξ)
    (h : Submodule.span (regAt ξ p) (Set.range g) = Submodule.span (regAt ξ p) (Set.range b)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
      Submodule.span (regAt ξ q) (Set.range g) = Submodule.span (regAt ξ q) (Set.range b) := by
  obtain ⟨U, hU, H⟩ := near_all p (fun i q => g i ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun i => near_mem_span b p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨U', hU', H'⟩ := near_all p (fun i q => b i ∈ Submodule.span (regAt ξ q) (Set.range g))
    fun i => near_mem_span g p _ (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq => le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H q hq.1))
  · exact Submodule.span_le.2 (Set.range_subset_iff.2 (H' q hq.2))

end

theorem frame_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q := by
  intro X Ω _ ξ E _ _ L T r b p hL hp hb
  obtain ⟨U, hU, n, g, hg⟩ := hL p hp
  obtain ⟨U', hU', H⟩ := near_span_eq g b p ((hg p hp hU).symm.trans hb.2)
  exact ⟨U ⊓ U', ⟨hU, hU'⟩, fun q hq hqU => ⟨hb.1, (hg q hq hqU.1).trans (H q hqU.2)⟩⟩

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem map_of_span {L : Lat ξ E} (φ : E →ₗ[Ω] E') {q : Cpt ξ} {ι : Type} {b : ι → E}
    (h : L q = Submodule.span (regAt ξ q) (Set.range b)) :
    L.map φ q = Submodule.span (regAt ξ q) (Set.range (φ ∘ b)) := by
  unfold Lat.map
  rw [h, Submodule.map_span, Set.range_comp]
  rfl

theorem coh_map {L : Lat ξ E} {T : Set (Cpt ξ)} (φ : E →ₗ[Ω] E') (h : L.IsCohOn T) : (L.map φ).IsCohOn T := by
  intro p hp
  obtain ⟨U, hU, n, g, hg⟩ := h p hp
  exact ⟨U, hU, n, φ ∘ g, fun q hq hqU => map_of_span φ (hg q hq hqU)⟩

theorem vb_of_coh {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsCohOn T)
    (hb : ∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) : L.IsVBOn T r V := by
  intro p hp
  obtain ⟨b, hV, hb⟩ := hb p hp
  obtain ⟨U, hU, H⟩ := frame_spread X Ω ξ E L T r b p h hp hb
  exact ⟨U, hU, b, hV, H⟩

theorem span_smul_fam {ι : Type} (b : ι → E) {a : Ω} (ha : a ≠ 0) :
    Submodule.span Ω (Set.range fun i => a • b i) = Submodule.span Ω (Set.range b) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    have : b i = a⁻¹ • a • b i := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem li_smul_fam {ι : Type} {b : ι → E} (hb : LinearIndependent Ω b) {a : Ω} (ha : a ≠ 0) :
    LinearIndependent Ω fun i => a • b i :=
  hb.units_smul fun _ => Units.mk0 a ha

end

theorem coh_ops : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) := by
  intro X Ω _ ξ E _ _ E' _ _ L L' T
  refine ⟨fun r V h => Lat.IsCohOn.of_isVBOn h, fun φ h => coh_map φ h, fun h h' p hp => ?_,
    fun r V a ha h p hp => ?_, fun r V h hb => vb_of_coh h hb⟩
  · obtain ⟨U, hU, n, g, hg⟩ := h p hp
    obtain ⟨U', hU', n', g', hg'⟩ := h' p hp
    refine ⟨U ⊓ U', ⟨hU, hU'⟩, n + n', Fin.append g g', fun q hq hqU => ?_⟩
    have e : Set.range (Fin.append g g') = Set.range g ∪ Set.range g' := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        induction i using Fin.addCases with
        | left i => exact Or.inl ⟨i, by simp⟩
        | right i => exact Or.inr ⟨i, by simp⟩
      · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨Fin.castAdd n' i, by simp⟩
        · exact ⟨Fin.natAdd n i, by simp⟩
    rw [e, Submodule.span_union, ← hg q hq hqU.1, ← hg' q hq hqU.2]
  · obtain ⟨U, hU, b, hV, hb⟩ := h p hp
    refine ⟨U, hU, fun i => a • b i, (span_smul_fam b ha).trans hV, fun q hq hqU =>
      ⟨li_smul_fam (hb q hq hqU).1 ha, ?_⟩⟩
    exact map_of_span _ (hb q hq hqU).2

end PositivityTheory.HtPt.Mc
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem dom_local : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' i f hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := RegAtDom.map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, RegAtDom.genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := RegAtDom.genMap_stalkMap hd q hq hp s
    have hone : genMap ξ' ⟨q, hq⟩ (1 - (f.stalkMap q).hom s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hv, ht, mul_inv_cancel₀ h0, sub_self]
    have hu : IsUnit ((f.stalkMap q).hom s) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((f.stalkMap q).hom s * t) with h | h
      · exact isUnit_of_mul_isUnit_left h
      · have h' := h.map (genMap ξ' ⟨q, hq⟩)
        rw [hone] at h'
        exact absurd h' not_isUnit_zero
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

theorem dom_comp {X X₁ X₂ : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂}
    {f : X₁ ⟶ X} {g : X₂ ⟶ X₁} {i : Ω →+* Ω₁} {k : Ω₁ →+* Ω₂} (hf : Dominates ξ₁ ξ f i)
    (hg : Dominates ξ₂ ξ₁ g k) : Dominates ξ₂ ξ (g ≫ f) (k.comp i) := by
  unfold Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem iso_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X₁ X₂ : Scheme.{0}) (Ω' : Type) [Field Ω'] (i : Ω →+* Ω') (p : Cpt ξ), (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g i → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → NormAt ξ₂ g i p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω') ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω') ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω') → NormAt ξ₁ f i p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω') p₁) → NormAt ξ₂ (g ≫ f) i p) ∧ (∀ (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (f : X₁ ⟶ X) (g : X₂ ⟶ X₁), Dominates ξ₂ ξ₁ g (RingHom.id Ω) → IsoAt ξ₁ f (RingHom.id Ω) p → (∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → IsoAt ξ₂ g (RingHom.id Ω) p₁) → IsoAt ξ₂ (g ≫ f) (RingHom.id Ω) p) := by
  intro X Ω _ ξ X₁ X₂ Ω' _ i p
  refine ⟨fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_, fun ξ₁ ξ₂ f g hg hf hn => ?_⟩
  · have hr : ∀ p₁ : Cpt ξ₁, f p₁.1 = p.1 → regAt ξ p = regAt ξ₁ p₁ := fun p₁ h => by
      rw [hf.regAt_eq p₁ h, Subring.map_id]
    refine ⟨fun q hq => ?_, ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q
      rw [hr ⟨_, h⟩ hq]
      exact (hn ⟨_, h⟩ hq).exists_max q rfl
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      rw [hr p₁ h₁]
      intro P hP
      obtain ⟨q, ⟨hq, hq'⟩, hqu⟩ := (hn p₁ h₁).existsUnique P hP
      refine ⟨q, ⟨(congrArg f hq).trans h₁, hq'⟩, fun q' hq'' => hqu q' ⟨?_, hq''.2⟩⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ i g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq''.1)
  · have hr : ∀ (q : Cpt ξ₂) (p₁ : Cpt ξ₁), g q.1 = p₁.1 → f p₁.1 = p.1 → regAt ξ₂ q = regAt ξ₁ p₁ :=
      fun q p₁ h h' => by rw [(hn p₁ h').regAt_eq q h, Subring.map_id]
    refine ⟨fun q hq => ?_, fun P hP => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.id_comp] at h⟩
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [hr q ⟨_, h⟩ rfl hq]
      exact hf.exists_max ⟨_, h⟩ hq
    · obtain ⟨p₁, ⟨h₁, h₁'⟩, hu⟩ := hf.existsUnique P hP
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, ⟨(congrArg f hq).trans h₁, (hr q p₁ hq h₁).trans h₁'⟩, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ ⟨hq'.1, (hr q' ⟨_, h⟩ rfl hq'.1).symm.trans hq'.2⟩)
  · refine ⟨?_, fun q hq => ?_, by
      have h := dom_comp hf.dom hg
      rwa [RingHom.comp_id] at h⟩
    · obtain ⟨p₁, h₁, hu⟩ := hf.existsUnique
      obtain ⟨q, hq, hqu⟩ := (hn p₁ h₁).existsUnique
      refine ⟨q, (congrArg f hq).trans h₁, fun q' hq' => hqu q' ?_⟩
      obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q'
      exact congrArg Subtype.val (hu ⟨_, h⟩ hq')
    · obtain ⟨h, -⟩ := dom_local _ _ ξ₁ _ _ ξ₂ _ g hg q
      rw [(hn ⟨_, h⟩ hq).regAt_eq q rfl, Subring.map_id, hf.regAt_eq ⟨_, h⟩ hq]

end PositivityTheory.HtPt.Mb
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

lemma mem_pInt_iff [CharZero C] (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (z : C) :
    z ∈ pInt (C := C) R p ↔ v z ≤ v (p : C) := by
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
  · intro h
    obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := z / p)
      (by rw [map_div₀]; exact div_le_one_of_le₀ h zero_le)
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ hp0]⟩

lemma pow_mem_order {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) (k : ℕ) :
    f ^ k ∈ A.carrier := by
  induction k with
  | zero => simpa using A.one_mem
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hf

lemma tl_mem_order (hv : v.Integers R) (p : ℕ) [Fact p.Prime] (hp : v (p : C) < 1)
    {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ A.carrier) :
    (fun x => tl p (f x)) ∈ A.carrier := by
  have : (fun x => tl p (f x)) =
      ∑ k ∈ Finset.Ico 1 p, fun x => (-1) ^ (k - 1) * (f x - 1) ^ k / (k : C) := by
    funext x; rw [Finset.sum_apply]; rfl
  rw [this]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := (-1) ^ (k - 1) / (k : C)) (by
    rw [map_div₀, val_nat_eq v p hp k h1 h2, map_pow, Valuation.map_neg, map_one, one_pow, div_one])
  have h3 := A.carrier.smul_mem r (pow_mem_order A (A.carrier.sub_mem hf A.one_mem) k)
  convert h3 using 1
  funext x
  simp only [Pi.smul_apply, Algebra.smul_def, Pi.pow_apply, Pi.sub_apply, Pi.one_apply, hr]
  ring

end

theorem cpaf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ μ : N →+ ZMod p, ∃ g ∈ afFun p AA.carrier, ∃ ε : R, v (algebraMap R C ε) ^ (p - 1) = v (p : C) ∧ g 0 = 0 ∧ ∀ x, g x - algebraMap R C ε * ((μ x).val : C) ∈ pInt (C := C) R p ∧ v (g x - algebraMap R C ε * ((μ x).val : C)) < v (algebraMap R C ε) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ AA μ
  have hpp : p.Prime := Fact.out
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hpp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  let ψ : AddChar N C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom μ
  have hψ : ∀ x, ψ x = ζ ^ (μ x).val := fun x => rfl
  have hψp : ∀ x, ψ x ^ p = 1 := fun x => by
    rw [hψ, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hζ1 := val_root v p hpp.ne_zero hζ.pow_eq_one
  have hε := val_tl_prim v p hp hζ
  obtain ⟨ε, hεe⟩ := hv.exists_of_le_one (r := tl p ζ) (hε.le.trans (val_prim_lt v p hp hζ).le)
  refine ⟨fun x => tl p (ψ x), ⟨tl_mem_order hv p hp AA (charmem p C v R hv hp N AA ψ), ?_⟩,
    ε, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · intro x y
    rw [mem_pInt_iff hv]
    simp only [AddChar.map_add_eq_mul]
    exact val_tl_add v p hp (hψp x) (hψp y)
  · rw [hεe, hε, val_prim v p hζ]
  · simp only [AddChar.map_zero_eq_one, tl_one]
  · rw [mem_pInt_iff hv, hεe]
    exact (val_tl_pow v p hp hζ1 _).trans (val_prim_pow_le v p hp hζ)
  · rw [hεe, hε]
    exact (val_tl_pow v p hp hζ1 _).trans_lt (val_prim_pow_lt v p hp hζ p hpp.one_lt)

lemma form_add {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] (p : ℕ) [Fact p.Prime]
    {ι : Type} [Fintype ι] (l : ι → R) (x y : ι → ZMod p) :
    algebraMap R C (∑ i, l i * (((x + y) i).val : R)) - algebraMap R C (∑ i, l i * ((x i).val : R))
      - algebraMap R C (∑ i, l i * ((y i).val : R)) ∈ pInt (C := C) R p := by

  simp only [map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  have h := Nat.mod_add_div ((x i).val + (y i).val) p
  rw [← ZMod.val_add] at h
  have h' := congrArg (Nat.cast : ℕ → C) h
  rw [pInt, Submodule.mem_span_singleton]
  refine ⟨-(l i * ((((x i).val + (y i).val) / p : ℕ) : R)), ?_⟩
  simp only [Algebra.smul_def, map_neg, map_mul, map_natCast, Pi.add_apply]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul] at h'
  linear_combination (-algebraMap R C (l i)) * h'

theorem lifts : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ (l : ι → R) (ε : R), ε • l ∈ afLat p AA.carrier → v (p : C) ≤ v (algebraMap R C ε) ^ (p - 1) → ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧ (∀ x, v (u x) ≤ 1) ∧ ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 := by
  intro p _ C _ _ _ v R _ _ hv hp ι _ _ AA l ε hl hε
  have hpp : p.Prime := Fact.out
  have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
  have hp0 : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hpp.ne_zero)
  have hε0 : v (algebraMap R C ε) ≠ 0 := by
    intro h
    rw [h, zero_pow hp1] at hε
    exact hp0 (le_antisymm hε zero_le)
  have hε0' : algebraMap R C ε ≠ 0 := (Valuation.ne_zero_iff v).1 hε0
  suffices h : ∃ u : (ι → ZMod p) → C, (fun x => algebraMap R C ε * u x) ∈ afFun p AA.carrier ∧
      ∀ x, v (u x - algebraMap R C (∑ i, l i * ((x i).val : R))) < 1 by
    obtain ⟨u, h1, h2⟩ := h
    refine ⟨u, h1, fun x => ?_, h2⟩
    rw [← sub_add_cancel (u x) (algebraMap R C (∑ i, l i * ((x i).val : R)))]
    exact v.map_add_le (h2 x).le (hv.map_le_one _)
  rcases lt_or_ge (v (p : C)) (v (algebraMap R C ε)) with hlt | hge
  · obtain ⟨g, hg, h⟩ := hl
    refine ⟨fun x => g x / algebraMap R C ε, ?_, fun x => ?_⟩
    · simp only [mul_div_cancel₀ _ hε0']
      refine ⟨hg, fun x y => ?_⟩
      have := Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (h (x + y)) (h x)) (h y))
        (form_add (C := C) p (ε • l) x y)
      convert this using 1
      ring
    · have h1 := (mem_pInt_iff hv p _).1 (h x)
      have h2 : g x / algebraMap R C ε - algebraMap R C (∑ i, l i * ((x i).val : R)) =
          (g x - algebraMap R C (∑ i, (ε • l) i * ((x i).val : R))) / algebraMap R C ε := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, map_mul]
        field_simp
      rw [h2, map_div₀, div_lt_one₀ (pos_iff_ne_zero.2 hε0)]
      exact h1.trans_lt hlt
  · have hc := fun i => cpaf p C v R hv hp (ι → ZMod p) AA (Pi.evalAddMonoidHom _ i)
    choose g hg e he _ hge' using hc
    have hee : ∀ i, v (algebraMap R C ε) ≤ v (algebraMap R C (e i)) := by
      intro i
      refine hge.trans ?_
      rw [← he i]
      exact pow_le_of_le_one zero_le (hv.map_le_one _) hp1
    have he0 : ∀ i, v (algebraMap R C (e i)) ≠ 0 := fun i h =>
      hε0 (le_antisymm (h ▸ hee i) zero_le)
    have he0' : ∀ i, algebraMap R C (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff v).1 (he0 i)
    choose r hr using fun i => hv.dvd_of_le (hee i)
    refine ⟨fun x => ∑ i, algebraMap R C (l i) * (g i x / algebraMap R C (e i)), ?_, fun x => ?_⟩
    · have := Submodule.sum_mem (afFun p AA.carrier) (t := Finset.univ)
        fun i _ => Submodule.smul_mem _ (l i * r i) (hg i)
      convert this using 1
      funext x
      rw [Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h0 := he0' i
      rw [Pi.smul_apply, Algebra.smul_def, map_mul]
      conv_lhs => rw [hr i, map_mul]
      field_simp
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine v.map_sum_lt one_ne_zero fun i _ => ?_
      have h0 := he0' i
      have h2 : algebraMap R C (l i) * (g i x / algebraMap R C (e i)) -
          algebraMap R C (l i * ((x i).val : R)) = algebraMap R C (l i) *
          ((g i x - algebraMap R C (e i) * ((x i).val : C)) / algebraMap R C (e i)) := by
        rw [map_mul, map_natCast]
        field_simp
      rw [h2, map_mul, map_div₀]
      refine mul_lt_one_of_nonneg_of_lt_one_right (hv.map_le_one _) zero_le ?_
      rw [div_lt_one₀ (pos_iff_ne_zero.2 (he0 i))]
      exact (hge' i x).2

end PositivityTheory.HtPt.Ra
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

structure PairHost {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
    (H : Host E) (H' : Host E') where

  ψ : 𝓞 E' →+* Matrix (Fin 2) (Fin 2) (𝓞 E)

  σ : 𝓞 E' ≃+* 𝓞 E'
  bar : ∀ a i j, ψ (H'.bar a) i j = H.bar (ψ a j i)
  w0 : ψ H'.w0 = Matrix.scalar (Fin 2) H.w0
  conj : ∀ a, ψ (σ a) * Matrix.diagonal ![1, -1] = Matrix.diagonal ![1, -1] * ψ a
  rt : σ H'.rt = H'.rt
  chars : ∀ (k : Type) [Field k] [CharZero k] (τ τ' : 𝓞 E' →+* k), τ H'.rt = τ' H'.rt →
    τ' = τ ∨ τ' = τ.comp σ.toRingHom

end PositivityTheory.HtPt.Kftwo
end
end
