module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle024
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtDom

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : X) (hq : genPt ξ ⤳ q) :
    Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩) : X.presheaf.stalk q ⟶ _) ≫ X.fromSpecStalk q = ξ := by
  show Spec.map (X.presheaf.stalkSpecializes (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ X.fromSpecStalk q = ξ
  have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) (x := ξ (IsLocalRing.closedPoint Ω)) (y := q) hq
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (congrArg (fun g => Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ) ≫ g) h1)
  exact (congrArg (fun g => g ≫ X.fromSpecStalk q) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)

theorem map_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) : f (genPt ξ') = genPt ξ := by
  have h1 : (ξ' ≫ f) (IsLocalRing.closedPoint Ω') =
      (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω') := by rw [show ξ' ≫ f = _ from h]
  have h2 : Spec.map (CommRingCat.ofHom i) (IsLocalRing.closedPoint Ω') = IsLocalRing.closedPoint Ω :=
    Subsingleton.elim (α := PrimeSpectrum Ω) _ _
  exact h1.trans (congrArg ξ h2)

theorem genMap_stalkMap {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} (h : Dominates ξ' ξ f i) (q : X') (hq : genPt ξ' ⤳ q) (hp : genPt ξ ⤳ f q)
    (s : X.presheaf.stalk (f q)) :
    genMap ξ' ⟨q, hq⟩ ((f.stalkMap q).hom s) = i (genMap ξ ⟨f q, hp⟩ s) := by
  have e : f.stalkMap q ≫ (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) =
      (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) ≫ CommRingCat.ofHom i := by
    apply Spec.map_injective
    have h1 := spec_genMap ξ' q hq
    have h2 := spec_genMap ξ (f q) hp
    generalize (CommRingCat.ofHom (genMap ξ' ⟨q, hq⟩) : X'.presheaf.stalk q ⟶ _) = u at h1 ⊢
    generalize (CommRingCat.ofHom (genMap ξ ⟨f q, hp⟩) : X.presheaf.stalk (f q) ⟶ _) = v at h2 ⊢
    have h3 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := q)
    refine (cancel_mono (X.fromSpecStalk (f q))).1 ?_
    have l : Spec.map (f.stalkMap q ≫ u) ≫ X.fromSpecStalk (f q) = ξ' ≫ f :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        ((congrArg (fun g => Spec.map u ≫ g) h3).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ f) h1)))
    have r : Spec.map (v ≫ CommRingCat.ofHom i) ≫ X.fromSpecStalk (f q) = Spec.map (CommRingCat.ofHom i) ≫ ξ :=
      ((congrArg (fun g => g ≫ X.fromSpecStalk (f q)) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)).trans
        (congrArg (fun g => Spec.map (CommRingCat.ofHom i) ≫ g) h2)
    exact l.trans (Eq.trans h r.symm)
  exact congrArg (fun g => g.hom s) e

theorem regAt_dominates :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type)
      [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), Dominates ξ' ξ f i →
      ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, (∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧
        (IsCptGen ξ' → ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) := by
  intro X Ω _ ξ X' Ω' _ ξ' f i hd p'
  obtain ⟨q, hq⟩ := p'
  have hp : genPt ξ ⤳ f q := map_genPt hd ▸ hq.map f.continuous
  refine ⟨hp, ?_, fun hg => ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨(f.stalkMap q).hom s, genMap_stalkMap hd q hq hp s⟩
  · rintro _ ⟨s, rfl⟩ ⟨h0, -, t, ht⟩
    have hv := genMap_stalkMap hd q hq hp s
    have hone : (f.stalkMap q).hom s * t = 1 := by
      apply hg.inj ⟨q, hq⟩
      rw [map_mul, map_one, hv, ht]
      exact mul_inv_cancel₀ h0
    have hu : IsUnit ((f.stalkMap q).hom s) := IsUnit.of_mul_eq_one _ hone
    exact RegAtMono.unitAt_of_isUnit ξ ⟨f q, hp⟩ (isUnit_of_map_unit (f.stalkMap q).hom s hu)

end GlobalTheory.CompanionTheory.Ar.RegAtDom
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
private theorem exists_open_forall_mem_regAt' {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) (w : Ω)
    (hw : w ∈ regAt ξ q) : ∃ W : X.Opens, q.1 ∈ W ∧ ∀ q' : Cpt ξ, q'.1 ∈ W → w ∈ regAt ξ q' := by
  obtain ⟨g, rfl⟩ := hw
  obtain ⟨W, hq, s, rfl⟩ := X.presheaf.exists_germ_eq g
  refine ⟨W, hq, fun q' hq' => ⟨X.presheaf.germ W q'.1 hq' s, ?_⟩⟩
  have key : ∀ (y : X) (hy : y ∈ W) (h : genPt ξ ⤳ y),
      X.presheaf.germ W y hy ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo ξ =
        X.presheaf.germ W (genPt ξ) (h.mem_open W.isOpen hy) ≫ Scheme.stalkClosedPointTo ξ := by
    intro y hy h
    exact TopCat.Presheaf.germ_stalkSpecializes_assoc X.presheaf hy h _
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  erw [key q'.1 hq' q'.2, key q.1 hq q.2]

private theorem exists_mul_eq_one_of_dedekind_ideal_ne_bot {Ω : Type} [Field Ω] (O : Type) [CommRing O] [IsDedekindDomain O] (σ : O →+* Ω)
    (𝔡 : Ideal O) (R : Subring Ω) [IsLocalRing R] (hσ : ∀ a, σ a ∈ R) (hinj : Function.Injective σ)
    (h𝔡 : 𝔡 ≠ ⊥) : ∃ d ∈ 𝔡, ∃ u : Ω, (∀ d' ∈ 𝔡, ∃ o : O, σ d' * u = σ o) ∧ ∃ v ∈ R, σ d * u * v = 1 := by
  obtain ⟨x, hx𝔡, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔡
  obtain ⟨𝔞, h𝔞⟩ : 𝔡 ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx𝔡)
  have hσx : σ x ≠ 0 := fun h => hx0 (hinj (by rw [h, map_zero]))
  have hgood : ∀ n ∈ 𝔞, ∀ d' ∈ 𝔡, ∃ o : O, σ d' * (σ n / σ x) = σ o := by
    intro n hn d' hd'
    have hmem : d' * n ∈ Ideal.span {x} := h𝔞 ▸ Ideal.mul_mem_mul hd' hn
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨o, ?_⟩
    rw [← mul_div_assoc, ← map_mul, ← ho, map_mul, mul_div_cancel_right₀ _ hσx]
  by_contra hne
  push_neg at hne
  let C : O → Prop := fun y => ∃ h : σ y / σ x ∈ R, (⟨_, h⟩ : R) ∈ IsLocalRing.maximalIdeal R
  have hx : x ∈ 𝔡 * 𝔞 := h𝔞 ▸ Ideal.mem_span_singleton_self x
  have hC : C x := by
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      obtain ⟨o, ho⟩ := hgood n hn m hm
      have hR : σ (m * n) / σ x ∈ R := by
        rw [map_mul, mul_div_assoc, ho]; exact hσ o
      refine ⟨hR, ?_⟩
      by_contra hnot
      have hu : IsUnit (⟨_, hR⟩ : R) := by
        by_contra h'
        exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr h')
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      refine hne m hm (σ n / σ x) (hgood n hn) w w.2 ?_
      have := congrArg Subtype.val hw
      simpa [map_mul, mul_div_assoc] using this
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      have hab : σ (a + b) / σ x ∈ R := by rw [map_add (f := _), add_div]; exact add_mem ha hb
      refine ⟨hab, ?_⟩
      have : (⟨_, hab⟩ : R) = ⟨_, ha⟩ + ⟨_, hb⟩ := by
        ext; simp [map_add (f := _), add_div]
      rw [this]; exact add_mem ha' hb'
  obtain ⟨h1, h2⟩ := hC
  have : (⟨_, h1⟩ : R) = 1 := by ext; simp [div_self hσx]
  rw [this] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)


theorem _root_.GlobalTheory.CompanionTheory.Relay.ideal_saturated_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (O : Type) [CommRing O] [IsDedekindDomain O] (σ : O →+* Ω) (𝔡 : Ideal O) (L : Lat ξ Li) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω Li), Function.Injective σ → 𝔡 ≠ ⊥ → (∀ q ∈ T, ∀ a, σ a ∈ regAt ξ q) → L.IsVBOn T r V → Lat.IsVBOn (fun q => Submodule.span (regAt ξ q) {e | e ∈ V ∧ ∀ d ∈ 𝔡, σ d • e ∈ L q} : Lat ξ Li) T r V := by
  intro X Ω _ ξ Li _ _ O _ _ σ 𝔡 L T r V hinj h𝔡 hσ hL p hp
  obtain ⟨U₀, hpU₀, b, hbV, hb⟩ := hL p hp
  haveI : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective
  obtain ⟨d, hd, u, hu, v, hv, hdu⟩ := exists_mul_eq_one_of_dedekind_ideal_ne_bot O σ 𝔡 (regAt ξ p) (hσ p hp) hinj h𝔡
  obtain ⟨W₂, hpW₂, hW₂⟩ := exists_open_forall_mem_regAt' ξ p v hv
  have hu0 : u ≠ 0 := by rintro rfl; simp at hdu
  refine ⟨U₀ ⊓ W₂, ⟨hpU₀, hpW₂⟩, fun i => u • b i, ?_, ?_⟩
  · rw [← hbV]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : b i = u⁻¹ • (u • b i) := by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro q hq hqU
    obtain ⟨hli, hLq⟩ := hb q hq hqU.1
    have hvq : v ∈ regAt ξ q := hW₂ q hqU.2
    refine ⟨?_, ?_⟩
    · have := hli.units_smul (fun _ => Units.mk0 u hu0)
      convert this using 1
      funext i
      simp [Units.smul_def]
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro e ⟨heV, he⟩
        have h1 : σ d • e ∈ L q := he d hd
        rw [hLq] at h1
        have h2 : (⟨v, hvq⟩ : regAt ξ q) • (σ d • e) ∈ Submodule.span (regAt ξ q) (Set.range b) :=
          Submodule.smul_mem _ _ h1
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h2
        have he' : e = u • ((⟨v, hvq⟩ : regAt ξ q) • (σ d • e)) := by
          rw [Subring.smul_def, smul_smul, smul_smul]
          rw [show u * v * σ d = 1 by rw [← hdu]; ring, one_smul]
        rw [SetLike.mem_coe, he', ← hc, Finset.smul_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [Subring.smul_def, smul_comm]
        exact Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨?_, fun d' hd' => ?_⟩
        · rw [← hbV]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        · obtain ⟨o, ho⟩ := hu d' hd'
          have hbi : b i ∈ L q := by rw [hLq]; exact Submodule.subset_span ⟨i, rfl⟩
          rw [smul_smul, ho]
          exact Submodule.smul_mem (L q) (⟨σ o, hσ q hq o⟩ : regAt ξ q) hbi
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

def GenIx {S : Type} (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

abbrev GenField (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : Type :=
  FractionRing (MvPolynomial (GenIx r) Ω)

def genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) :
    Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun l k =>
  if h : k < l then algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩)
  else if l = k then 1 else 0

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

def genB (c : ∀ s, Fin (r s) → E) (s : S) (k : Fin (r s)) : TensorProduct Ω (GenField Ω r) E :=
  ∑ l, genU Ω r s l k • TensorProduct.mk Ω (GenField Ω r) E 1 (c s l)

def flagMat {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) * genU Ω r s

def FlagIx (κ : Type) {S : Type} (n : S → ℕ) (r : S → ℕ) : Type :=
  κ × ((q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))

def flagCoord [Fintype S] (κ : Type) (x : κ → Ω) {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) : FlagIx κ n r → GenField Ω r := fun cJ =>
  algebraMap Ω (GenField Ω r) (x cJ.1) *
    ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (cJ.2 q) (Fin.castLE q.2.2)).det

def IsTwistGen {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (L : Lat ξ E) (m : ℕ)
    {n : ℕ} (φ : Fin n → Module.Dual Ω E) : Prop :=
  (∀ j (p : Cpt ξ) c, InChart ξ x c p → ∀ e ∈ L p, φ j e / x c ^ m ∈ regAt ξ p) ∧
  ∀ (p : Cpt ξ) c, InChart ξ x c p → ∀ w : Module.Dual Ω E, (∀ e ∈ L p, w e ∈ regAt ξ p) →
    ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p) ∧ ∀ e ∈ L p, w e = ∑ j, g j * (φ j e / x c ^ m)

theorem coordTie_comp_equiv {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type}
    [CommRing o] [Algebra o Ω] {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' ≃ κ) :
    CoordTie o ξ (x ∘ e) := by
  have hch : ∀ c p, InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
    intro c p
    simp only [InChart, Function.comp]
    exact and_congr Iff.rfl ⟨fun h c' => by simpa using h (e.symm c'), fun h c' => h (e c')⟩
  have hr : ∀ c, Set.range (fun j => (x ∘ e) j / (x ∘ e) c) = Set.range (fun j => x j / x (e c)) := by
    intro c
    ext a
    exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (hch _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    exact ⟨U, hU, fun q => by rw [hq q]; exact exists_congr fun h' => (hch c _).symm⟩
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (hch c p).symm Iff.rfl
end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem char_zero_centre_complex_point : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z), IsCptGen ξ → Char0 ξ ⟨centre z, h⟩ := by
  intro Ω _ X ξ z h _
  unfold Char0 InFibre unitAt regAt
  intro r hr hfib
  apply hfib
  have h1 := map_natCast (Scheme.stalkClosedPointTo z).hom r
  have h2 : IsUnit ((r : ℕ) : ℂ) := (Nat.cast_ne_zero.2 hr.ne_zero).isUnit
  rw [← h1] at h2
  obtain ⟨u, hu'⟩ := isUnit_of_map_unit _ _ h2
  have hv : genMap ξ ⟨centre z, h⟩ u.val = (r : Ω) :=
    (congrArg (genMap ξ ⟨centre z, h⟩) hu').trans (map_natCast _ r)
  refine ⟨?_, ⟨_, hv⟩, ⟨(u⁻¹).val, ?_⟩⟩
  · rw [← hv]
    exact (u.isUnit.map (genMap ξ ⟨centre z, h⟩)).ne_zero
  · exact (map_units_inv (genMap ξ ⟨centre z, h⟩) u).trans (congrArg Inv.inv hv)

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CharTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}

theorem unit_natCast (h : Char0 ξ q) (n : ℕ) (hn : n ≠ 0) : unitAt ξ q (n : Ω) :=
  _root_.UpperTheory.Reformulated.B.GenericMap.main h n hn

theorem char_zero_iff_integers_units (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω]
    (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω) (ht : CoordTie (𝓞 F) ξ t) (p : Cpt ξ) :
    Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  constructor
  · intro h d hd
    have hreg : ∀ b : 𝓞 F, algebraMap (𝓞 F) Ω b ∈ regAt ξ p := by
      intro b
      obtain ⟨c, hc⟩ := ht.cover p
      exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ b) p hc
    have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hd
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {d}))
    have hu := unit_natCast h _ hn
    have e : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Ω) = algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d' := by
      rw [← map_mul, ← hd', map_natCast]
    rw [e] at hu
    have ha : algebraMap (𝓞 F) Ω d ≠ 0 := left_ne_zero_of_mul hu.1
    have hb : algebraMap (𝓞 F) Ω d' ≠ 0 := right_ne_zero_of_mul hu.1
    refine ⟨ha, hreg d, ?_⟩
    have e2 : (algebraMap (𝓞 F) Ω d)⁻¹ =
        algebraMap (𝓞 F) Ω d' * (algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d')⁻¹ := by
      field_simp
    rw [e2]
    exact mul_mem (hreg d') hu.2.2
  · intro h r hr hf
    have hr0 : (r : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
    have := h _ hr0
    rw [map_natCast] at this
    exact hf this

end GlobalTheory.CompanionTheory.Ar.SncBase.CharTie
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

variable {S : Scheme.{0}} {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
  {P V : Type} [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]
  [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

theorem ext_pair_mod {Z : Over S} (f g : ob x (P × P) ⟶ Z)
    (h₁ : hom x (LinearMap.fst R P P) ≫ f = hom x (LinearMap.fst R P P) ≫ g)
    (h₂ : hom x (LinearMap.snd R P P) ≫ f = hom x (LinearMap.snd R P P) ≫ g) : f = g := by
  ext1
  refine joint_epi (TrivSqZeroExt.map (LinearMap.fst R P P)).toRingHom
    (TrivSqZeroExt.map (LinearMap.snd R P P)).toRingHom ?_ ?_ f.left g.left
    (congrArg CommaMorphism.left h₁) (congrArg CommaMorphism.left h₂)
  · intro a b hab
    have e₁ : TrivSqZeroExt.map (LinearMap.fst R P P) a = TrivSqZeroExt.map (LinearMap.fst R P P) b :=
      congrArg Prod.fst hab
    have e₂ : TrivSqZeroExt.map (LinearMap.snd R P P) a = TrivSqZeroExt.map (LinearMap.snd R P P) b :=
      congrArg Prod.snd hab
    ext
    · simpa using congrArg TrivSqZeroExt.fst e₁
    · simpa using congrArg TrivSqZeroExt.snd e₁
    · simpa using congrArg TrivSqZeroExt.snd e₂
  · intro p
    let q : PrimeSpectrum (TrivSqZeroExt R P) :=
      PrimeSpectrum.comap (TrivSqZeroExt.map (LinearMap.inl R P P)).toRingHom p
    refine ⟨q, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
    change TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) ∈ p.asIdeal ↔
      a ∈ p.asIdeal
    set b := TrivSqZeroExt.map (LinearMap.inl R P P) (TrivSqZeroExt.map (LinearMap.fst R P P) a) with hb
    have h0 : (b - a).fst = 0 := by simp [hb]
    have hm : b - a ∈ p.asIdeal := by
      refine p.isPrime.mem_of_pow_mem 2 ?_
      have : (b - a) ^ 2 = 0 := by
        rw [pow_two]
        ext1 <;> simp [h0]
      rw [this]; exact zero_mem _
    constructor
    · intro h; simpa using p.asIdeal.sub_mem h hm
    · intro h; simpa using p.asIdeal.add_mem hm h

theorem hom_add_mod (G : Over S) [GrpObj G] (u : ob x P ⟶ G) (hu : zsec x ≫ u = 1) (f g : P →ₗ[R] V) :
    hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) := by
  have h0 : hom x (0 : P →ₗ[R] P) ≫ u = 1 := by
    rw [hom_zero, Category.assoc, hu, MonObj.comp_one]
  have key : hom x (LinearMap.inl R P P + LinearMap.inr R P P) ≫ u =
      (hom x (LinearMap.inl R P P) ≫ u) * (hom x (LinearMap.inr R P P) ≫ u) := by
    apply ext_pair_mod
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, add_zero, h0, _root_.mul_one]
    · simp only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.snd_comp_inl,
        LinearMap.snd_comp_inr, zero_add, h0, _root_.one_mul]
  have := congrArg (fun k => hom x (f.coprod g) ≫ k) key
  simpa only [MonObj.comp_mul, ← Category.assoc, hom_comp, LinearMap.comp_add, LinearMap.coprod_inl,
    LinearMap.coprod_inr] using this

theorem hom_add_mod_closed : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G] (P V : Type) [AddCommGroup P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P] [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V] (u : ob x P ⟶ G), zsec x ≫ u = 1 → ∀ f g : P →ₗ[R] V, hom x (f + g) ≫ u = (hom x f ≫ u) * (hom x g ≫ u) :=
  fun _ _ _ x G _ _ _ _ _ _ _ _ _ _ _ u hu f g => hom_add_mod x G u hu f g

end GlobalTheory.CompanionTheory.Ar.LieEx.ModSrc
end
end

section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem _root_.GlobalTheory.T.discriminant_valuation_different : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)), P.IsPrime → (p : 𝓞 E) ∈ P → ((padicValInt p (discr E) : ℕ)) * (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P = (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | exact GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | (intros; apply GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem _root_.GlobalTheory.T.finite_open_le_closed_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le | exact GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isFinite_open_le_of_closedFibre_le <;> assumption)
end
