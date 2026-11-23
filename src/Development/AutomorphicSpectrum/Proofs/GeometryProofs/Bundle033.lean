module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DualBasisReverseTriangular
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairing
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle026
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict

variable {X X' : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]

theorem valAt_unique {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (hg : IsCptGen ξ')
    {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a : Ω} {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z a t) :
    r = t := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  have e : s₁ = s₂ := hg.inj ⟨centre z, hA⟩ (hs₁.trans hs₂.symm)
  rw [← hr, ← ht, e]

theorem valAt_mul {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a b : Ω}
    {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z b t) : ValAt ξ' z (a * b) (r * t) := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  exact ⟨hA, s₁ * s₂, by rw [map_mul, hs₁, hs₂],
    (map_mul _ s₁ s₂).trans (congrArg₂ (· * ·) hr ht)⟩

theorem valAt_one {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h : genPt ξ' ⤳ centre z) : ValAt ξ' z (1 : Ω) 1 :=
  ⟨h, 1, map_one _, map_one _⟩

theorem isUnit_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (s : A) (h : φ s ≠ 0) :
    IsUnit s := by
  exact IsUnit.of_map φ s (Ne.isUnit h)

theorem unitAt_of_valAt {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h' : genPt ξ' ⤳ centre z) {a : Ω} {r : ℂ} (hr : r ≠ 0) (hv : ValAt ξ' z a r) :
    unitAt ξ' ⟨centre z, h'⟩ a := by
  obtain ⟨h, s, hs, hr'⟩ := hv
  have hu : IsUnit s := isUnit_of_local (Scheme.stalkClosedPointTo z).hom s (by rw [hr']; exact hr)
  obtain ⟨u, rfl⟩ := hu
  have hinv : genMap ξ' ⟨centre z, h'⟩ ↑u⁻¹ * genMap ξ' ⟨centre z, h'⟩ ↑u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hne : genMap ξ' ⟨centre z, h'⟩ ↑u ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hinv
    exact zero_ne_one hinv
  refine ⟨?_, ⟨↑u, hs⟩, ⟨↑u⁻¹, ?_⟩⟩
  · rw [← hs]; exact hne
  · rw [← hs]; exact eq_inv_of_mul_eq_one_left hinv

private theorem stalkSpecializes_comp_stalkClosedPointTo_congr {K : Type} [Field K] (g₁ g₂ : Spec (CommRingCat.of K) ⟶ X)
    (e : g₁ = g₂) {q : X} (h₁ : g₁ (IsLocalRing.closedPoint K) ⤳ q) (h₂ : g₂ (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo g₁ =
      X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo g₂ := by
  subst e; rfl

private theorem stalkSpecializes_comp_stalkClosedPointTo_specMap_comp {K K' : Type} [Field K] [Field K'] (i : K →+* K')
    (g : Spec (CommRingCat.of K) ⟶ X) {q : X}
    (h₂ : (Spec.map (CommRingCat.ofHom i) ≫ g) (IsLocalRing.closedPoint K') ⤳ q)
    (hp : g (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ g) =
      X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom i := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.germ_stalkClosedPointTo, Scheme.germ_stalkClosedPointTo_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality]
  simp only [← Category.assoc]
  congr 1

theorem valAt_of_regAt {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ X}
    {i : Ω₀ →+* Ω} (hd : Dominates ξ' ξ f i) (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h' : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) {a : Ω₀}
    (ha : a ∈ regAt ξ ⟨f (centre z), hp⟩) :
    ∃ r : ℂ, ValAt ξ (z ≫ f) a r ∧ ValAt ξ' z (i a) r := by
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 ha
  refine ⟨(Scheme.stalkClosedPointTo (z ≫ f)).hom s, ⟨hp, s, hs, rfl⟩, h', (f.stalkMap (centre z)).hom s, ?_, ?_⟩
  · have h₁ : (ξ' ≫ f) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := f.base.hom.map_specializes h'
    have h₂ : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := by
      rw [← hd]; exact h₁
    have h'' : ξ' (IsLocalRing.closedPoint Ω) ⤳ centre z := h'
    have hp'' : ξ (IsLocalRing.closedPoint Ω₀) ⤳ f (centre z) := hp
    have key : f.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h'' ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes hp'' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      rw [← Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap, Category.assoc,
        ← Scheme.stalkClosedPointTo_comp]
      exact (stalkSpecializes_comp_stalkClosedPointTo_congr (ξ' ≫ f) (Spec.map (CommRingCat.ofHom i) ≫ ξ) hd h₁ h₂).trans
        (stalkSpecializes_comp_stalkClosedPointTo_specMap_comp i ξ h₂ hp'')
    have := congrArg (fun φ => φ.hom s) key
    rw [← hs]
    exact this
  · rw [Scheme.stalkClosedPointTo_comp]
    rfl

theorem coordsAt_restrict : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, addJ J N k) → ℂ),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → IsCptGen ξ' →
    (∀ q : X', genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordsAt ξ' (addY y x') z w → CoordsAt ξ y (z ≫ f) (fun p => w (addV J N p)) := by
  intro X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' z w hgen htie hcpt hgen' hd hc
  classical
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨fun k => hc1 (Sum.inr k), fun k c hu => ?_⟩
  have hyA : ∀ j : J k, addY y x' ⟨Sum.inr k, j⟩ = algebraMap Ω₀ Ω (y ⟨k, j⟩) := fun j => rfl
  obtain ⟨hy, hv⟩ := hc2 (Sum.inr k) c hu
  rw [hyA] at hy
  have hyc : y ⟨k, c⟩ ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
  refine ⟨hyc, fun j => ?_⟩
  have hp : genPt ξ ⤳ f (centre z) := hgen _
  have h' : genPt ξ' ⤳ centre z := hgen' _
  obtain ⟨c₀, hc₀ne, hc₀⟩ := htie.cover ⟨f (centre z), hp⟩
  have hx0 : (∏ k', y ⟨k', c₀ k'⟩) ≠ 0 := hc₀ne
  have hy0 : y ⟨k, c₀ k⟩ ≠ 0 := fun h0 => hx0 (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  have hprod : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) * y ⟨k, c₀ k⟩ =
      (∏ k', y ⟨k', c₀ k'⟩) * y ⟨k, j⟩ := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c₀ k j k'⟩) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c₀ k'⟩) (Finset.mem_univ k)]
    have e : ∏ x ∈ Finset.univ.erase k, y ⟨x, Function.update c₀ k j x⟩ =
        ∏ x ∈ Finset.univ.erase k, y ⟨x, c₀ x⟩ :=
      Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    simp only [Function.update_self]
    rw [e]
    ring
  have hratio : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) / (∏ k', y ⟨k', c₀ k'⟩) =
      y ⟨k, j⟩ / y ⟨k, c₀ k⟩ := by
    intro j
    rw [div_eq_div_iff hx0 hy0, hprod j, mul_comm]
  have hreg : ∀ j : J k, y ⟨k, j⟩ / y ⟨k, c₀ k⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := fun j => by
    rw [← hratio j]
    exact hc₀ (Function.update c₀ k j)
  obtain ⟨r₂, hr₂a, hr₂b⟩ := valAt_of_regAt hd z h' hp (hreg c)
  obtain ⟨r₀, hr₀, -⟩ := hv (c₀ k)
  rw [hyA, hyA] at hr₀
  have hmul := valAt_mul hr₂b hr₀
  have hy0' : algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) ≠ 0 := (map_ne_zero _).2 hy0
  have hone : algebraMap Ω₀ Ω (y ⟨k, c⟩ / y ⟨k, c₀ k⟩) *
      (algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) / algebraMap Ω₀ Ω (y ⟨k, c⟩)) = 1 := by
    rw [map_div₀]
    field_simp
  rw [hone] at hmul
  have h1 : r₂ * r₀ = 1 := valAt_unique hcpt hmul (valAt_one h')
  have hr₂ne : r₂ ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hunit := unitAt_of_valAt hp hr₂ne hr₂a
  have hinvreg : (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ ∈ regAt ξ ⟨f (centre z), hp⟩ := hunit.2.2
  have hregjc : y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := by
    have e : y ⟨k, j⟩ / y ⟨k, c⟩ = (y ⟨k, j⟩ / y ⟨k, c₀ k⟩) * (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ := by
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hreg j) hinvreg
  obtain ⟨r, hr1, hr2⟩ := valAt_of_regAt hd z h' hp hregjc
  obtain ⟨r', hr', hw⟩ := hv j
  rw [hyA, hyA] at hr'
  rw [map_div₀] at hr2
  have e3 : r = r' := valAt_unique hcpt hr2 hr'
  refine ⟨r, hr1, ?_⟩
  rw [e3]
  exact hw

end GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict
end
end

section

open NumberField Matrix IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem locAt_locAt {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L)
    (A : Submodule (𝓞 L) W) : locAt v (locAt v A) = locAt v A := by
  refine le_antisymm (fun x hx => ?_) (le_locAt v _)
  obtain ⟨s, hs, h⟩ := mem_locAt.1 hx
  obtain ⟨t, ht, h'⟩ := mem_locAt.1 h
  refine mem_locAt.2 ⟨t * s, fun hm => (v.maximalIdeal.isPrime.mem_or_mem hm).elim ht hs, ?_⟩
  rwa [mul_smul]

theorem locAt_mono {W : Type} [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L)
    {A B : Submodule (𝓞 L) W} (h : A ≤ B) : locAt v A ≤ locAt v B := fun x hx => by
  obtain ⟨t, ht, hx⟩ := mem_locAt.1 hx
  exact mem_locAt.2 ⟨t, ht, h hx⟩

theorem finite_not_le_one (a : L) : {w : FinitePlace L | ¬ w a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · subst ha
    refine Set.finite_empty.subset fun w hw => hw ?_
    rw [map_zero]
    exact zero_le_one
  · refine (FinitePlace.hasFiniteMulSupport ha).subset fun w hw => ?_
    change w a ≠ 1
    intro h
    exact hw (h ▸ le_rfl)

theorem exists_mul_le_one {v w : FinitePlace L} (hvw : w ≠ v) (a : L) :
    ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ w ((t : L) * a) ≤ 1 := by
  have hne : w.maximalIdeal.asIdeal ≠ v.maximalIdeal.asIdeal := fun h =>
    hvw (FinitePlace.maximalIdeal_injective (HeightOneSpectrum.ext h))
  have hnle : ¬ w.maximalIdeal.asIdeal ≤ v.maximalIdeal.asIdeal := fun h =>
    hne (w.maximalIdeal.isMaximal.eq_of_le v.maximalIdeal.isPrime.ne_top h)
  obtain ⟨p, hpw, hpv⟩ := SetLike.not_le_iff_exists.1 hnle
  have hp0 : (p : L) ≠ 0 := by
    intro h
    have : p = 0 := by exact_mod_cast h
    exact hpv (this ▸ Ideal.zero_mem _)
  have hlt : w (p : L) < 1 := by
    have h1 : w (p : L) ≤ 1 := place_int_le_one w p
    refine lt_of_le_of_ne h1 fun h => ?_
    have h2 := (place_le_one_iff w ((p : L)⁻¹)).1 (by rw [map_inv₀, h, inv_one])
    have h3 : w.maximalIdeal.valuation L (p : L) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hpw
    have h4 : 0 < w.maximalIdeal.valuation L (p : L) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hp0)
    rw [map_inv₀, inv_le_one₀ h4] at h2
    exact absurd h3 (not_lt.2 h2)
  by_cases ha : w a = 0
  · exact ⟨1, fun h => v.maximalIdeal.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
      simp [ha]⟩
  · have hapos : 0 < w a := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm ha)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hapos) hlt
    refine ⟨p ^ k, fun h => hpv (v.maximalIdeal.isPrime.mem_of_pow_mem _ h), ?_⟩
    push_cast
    rw [map_mul, map_pow]
    calc w (p : L) ^ k * w a ≤ (w a)⁻¹ * w a := by gcongr
      _ = 1 := inv_mul_cancel₀ ha

theorem exists_smul_mem_locAt_frame {v w : FinitePlace L} (hvw : w ≠ v)
    {T : Matrix (Fin n) (Fin n) L} (hT : T.det ≠ 0) (x : Fin n → L) :
    ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ locAt w (frame T) := by
  classical
  choose s hs hs' using fun i => exists_mul_le_one hvw ((T⁻¹ *ᵥ x) i)
  refine ⟨∏ i, s i, fun h => ?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.maximalIdeal.isPrime)).1 h
    exact hs i hi
  · refine mem_locAt_frame.2 ⟨((∏ i, s i : 𝓞 L) : L) • (T⁻¹ *ᵥ x), fun i => ?_, ?_⟩
    · have e : (((∏ i, s i : 𝓞 L) : L) • (T⁻¹ *ᵥ x)) i =
          ((∏ j ∈ Finset.univ.erase i, s j : 𝓞 L) : L) * ((s i : L) * (T⁻¹ *ᵥ x) i) := by
        rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i), Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e]
      exact place_mul_le_one w (place_int_le_one w _) (hs' i)
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hT),
        Matrix.one_mulVec]
      funext i
      simp [Algebra.smul_def]

theorem finite_notMem_locAt_frame {T : FinitePlace L → Matrix (Fin n) (Fin n) L}
    (hfin : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) (x : Fin n → L) :
    {w : FinitePlace L | x ∉ locAt w (frame (T w))}.Finite := by
  refine (hfin.union (Set.finite_iUnion fun i => finite_not_le_one (x i))).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hc
  apply hw
  rw [hc.1.locAt_frame]
  exact mem_locAt_frame_one.2 hc.2

end SlopeTestRemainingChoices

theorem locAt_glued (L : Type) [Field L] [NumberField L] (n : ℕ)
    (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (hdet : ∀ v, (T v).det ≠ 0)
    (hfin : {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite) (v : FinitePlace L) :
    locAt v (glued T) = locAt v (frame (T v)) := by
  classical
  refine le_antisymm ?_ fun x hx => ?_
  · have h : glued T ≤ locAt v (frame (T v)) := iInf_le _ v
    exact (locAt_mono v h).trans (locAt_locAt v _).le
  · have hone : (1 : 𝓞 L) ∉ v.maximalIdeal.asIdeal := fun h =>
      v.maximalIdeal.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    have hex : ∀ w : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧
        (w ≠ v → t • x ∈ locAt w (frame (T w))) := fun w => by
      by_cases hw : w = v
      · exact ⟨1, hone, fun h => absurd hw h⟩
      · obtain ⟨t, ht, h⟩ := exists_smul_mem_locAt_frame hw (hdet w) x
        exact ⟨t, ht, fun _ => h⟩
    choose τ hτ hτ' using hex
    let S : Finset (FinitePlace L) := (finite_notMem_locAt_frame hfin x).toFinset.erase v
    refine mem_locAt.2 ⟨∏ w ∈ S, τ w, fun h => ?_, ?_⟩
    · obtain ⟨w, -, hw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.maximalIdeal.isPrime)).1 h
      exact hτ w hw
    · refine Submodule.mem_iInf _ |>.2 fun w => ?_
      by_cases hw : w ∈ S
      · rw [← Finset.mul_prod_erase S τ hw, mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (hτ' w (Finset.ne_of_mem_erase hw))
      · refine Submodule.smul_mem _ _ ?_
        by_cases hv : w = v
        · rw [hv]; exact hx
        · by_contra hc
          exact hw (Finset.mem_erase.2 ⟨hv, (Set.Finite.mem_toFinset _).2 hc⟩)

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.finite_surjective_open_image : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective | exact GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem smoothOfRelativeDimension_opensRange_ι_comp
    (A B T : Scheme.{0}) (j : A ⟶ B) [IsOpenImmersion j] (g : B ⟶ T) (n : ℕ)
    (h : SmoothOfRelativeDimension n (j ≫ g)) :
    SmoothOfRelativeDimension n (j.opensRange.ι ≫ g) := by
  have e : j.opensRange.ι = j.isoOpensRange.inv ≫ j :=
    (Iso.eq_inv_comp _).mpr j.isoOpensRange_hom_ι
  rw [e, Category.assoc, ← zero_add n]
  exact smoothOfRelativeDimension_comp 0 n _ _

end GlobalTheory.CompanionTheory.Ar.SncBase
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)


theorem _root_.GlobalTheory.T.exists_reversed_dual_basis : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w : Module.Basis (Fin r) Ω (Fin r → Ω)),
    ∃ v : Module.Basis (Fin r) Ω (Fin r → Ω), ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | exact GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.DualRev.dotDualRevBasis <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.DualPair

theorem dualRevTri : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  intro Ω _ r w w' v v' h1 h2 h3
  exact PositivityTheory.Xgn.dual_basis_reverse_triangular Ω r w w' v v' h1 h2 h3

end GlobalTheory.CompanionTheory.Ar.DualPair
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.primitive_derivation_pairing : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A]
    (P : Submodule k A) (W : Submodule k (A →ₗ[k] k)),
    (∀ f ∈ P, Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) →
    (∀ v ∈ W, ∀ f g : A, v (f * g) = v f * Coalgebra.counit (R := k) g + Coalgebra.counit (R := k) f * v g) →
    (∀ v ∈ W, ∀ f ∈ P, v f = 0) →
    p ^ (Module.finrank k P + Module.finrank k W) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | exact GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.HopfCount.primitive_tangent_dvd_finrank <;> assumption)
end

section


theorem _root_.GlobalTheory.T.kaehler_rank_localization_bound : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | exact GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalStep.local_step <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.holomorphic_inverse_chart_value : ∀ (e : ℕ) (X₁ X₂ V : Type) [TopologicalSpace X₁] [TopologicalSpace X₂] [NormedAddCommGroup V] [NormedSpace ℂ V] (A₁ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₁) (A₂ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₂) (π : X₁ → X₂) (inv : X₂ → X₁), ReciprocityTheory.AnForm.M.HoloMap A₁ A₂ π → ReciprocityTheory.AnForm.M.HoloMap A₂ A₁ inv → Function.Bijective π → (∀ x, inv (π x) = x) → ∀ (Φ : X₁ → V) (x : X₂) (j₁ : Fin A₁.n) (j₂ : Fin A₂.n), inv x ∈ (A₁.chart j₁).source → x ∈ (A₂.chart j₂).source → DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x)) → (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x))).ker = ⊥ → (fderiv ℂ (fun v => Φ (inv ((A₂.chart j₂).symm v))) (A₂.chart j₂ x)).ker = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo | exact GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo | (intros; apply GlobalTheory.CompanionTheory.Ar.ImmersionBiholo.ker_fderiv_comp_biholo <;> assumption)
end
