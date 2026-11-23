module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L L' : Type} [Field L] [Field L']

theorem centre_field (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) = centre z := by
  show z (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint L')) = z (IsLocalRing.closedPoint L)
  exact congrArg z (Subsingleton.elim _ _)

theorem centre_specializes (ψ : L →+* L') (z : Sp L ⟶ X) : centre (spMap ψ ≫ z) ⤳ centre z :=
  specializes_of_eq (centre_field ψ z)


set_option backward.isDefEq.respectTransparency false in
theorem stalk_comp (ψ : L →+* L') (z : Sp L ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes ψ z) ≫ Scheme.stalkClosedPointTo (spMap ψ ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _).trans
    (congrArg (spMap ψ ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)

theorem valAt_field {ξ : Sp Ω ⟶ X} (ψ : L →+* L') {z : Sp L ⟶ X} {a : Ω} {r : L}
    (h : ValAt ξ z a r) : ValAt ξ (spMap ψ ≫ z) a (ψ r) := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  have h' : genPt ξ ⤳ centre (spMap ψ ≫ z) := by rw [centre_field]; exact h1
  refine ⟨h', (X.presheaf.stalkSpecializes (centre_specializes ψ z)).hom s, ?_, ?_⟩
  · have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf h' (centre_specializes ψ z)
    have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom s) e
    exact e2
  · exact congrArg (fun q => q.hom s) (stalk_comp ψ z)

theorem coordsAt_field {ξ : Sp Ω ⟶ X} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (ψ : L →+* L')
    {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (h : CoordsAt ξ y z w) :
    CoordsAt ξ y (spMap ψ ≫ z) fun p => ψ (w p) := by
  refine ⟨fun k => (h.1 k).imp fun c hc => hc.map ψ, fun k c hc => ?_⟩
  have hc' : IsUnit (w ⟨k, c⟩) := by
    rw [isUnit_iff_ne_zero] at hc ⊢
    exact fun h0 => hc (by simp [h0])
  refine ⟨(h.2 k c hc').1, fun i => ?_⟩
  obtain ⟨r, hr, e⟩ := (h.2 k c hc').2 i
  exact ⟨ψ r, valAt_field ψ hr, by simp only [e, map_mul]⟩

theorem coordsAt_embedding : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ),
    CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w →
    CoordsAt ξ y (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) (fun p => σ (w p)) := by
  intro X Ω _ ξ K J y L _ _ w z σ h
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [e]
  exact coordsAt_field σ h

end GlobalTheory.CompanionTheory.Ar.RootHt.PullCoords
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_spec {a : Ω} {r : R} (h : ValAt ξ z a r) : ∃ hz : genPt ξ ⤳ centre z, a ∈ regAt ξ ⟨centre z, hz⟩ := by
  obtain ⟨hz, s, hs, -⟩ := h
  exact ⟨hz, s, hs⟩

theorem val_exists {a : Ω} {hz : genPt ξ ⤳ centre z} (h : a ∈ regAt ξ ⟨centre z, hz⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, hz, s, hs, rfl⟩

theorem val_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, hs, rfl⟩ := h
  obtain ⟨hz', s', hs', rfl⟩ := h'
  have : s = s' := hξ.inj ⟨centre z, hz⟩ (hs.trans hs'.symm)
  rw [this]

theorem val_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t * t', by rw [map_mul, ht]; rw [← ht'], map_mul _ _ _⟩

theorem val_add {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t + t', by rw [map_add (f := _), ht]; rw [← ht'], map_add _ _ _⟩

theorem val_nat (hz : genPt ξ ⤳ centre z) (n : ℕ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩

theorem val_one (hz : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 1

theorem val_zero (hz : genPt ξ ⤳ centre z) : ValAt ξ z (0 : Ω) (0 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 0

theorem val_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : ValAt ξ z a⁻¹ (↑r⁻¹ : R) := by
  obtain ⟨hz, s, hs, hr⟩ := h
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (hr ▸ r.isUnit)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · rw [← hs, map_units_inv]
  · have : (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom u) = r := Units.ext hr
    rw [← this]
    exact congrArg Units.val (map_inv (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom) u)

theorem val_ne_zero (hξ : IsCptGen ξ) [Nontrivial R] {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 := by
  rintro rfl
  obtain ⟨hz, -⟩ := val_spec h
  have := val_unique hξ h (val_zero hz)
  exact r.ne_zero this

theorem val_inv₀ {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) :
    ValAt ξ z a⁻¹ r⁻¹ := by
  have := val_inv (r := Units.mk0 r hr) h
  simpa using this

theorem val_zpow {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, -⟩ := val_spec h
  have hp : ∀ k : ℕ, ∀ {b : Ω} {s : F}, ValAt ξ z b s → ValAt ξ z (b ^ k) (s ^ k) := by
    intro k b s hb
    induction k with
    | zero => simpa using val_one hz
    | succ k ih => rw [pow_succ, pow_succ]; exact val_mul ih hb
  rcases n with k | k
  · simpa using hp k h
  · simpa [zpow_negSucc] using val_inv₀ (pow_ne_zero _ hr) (hp (k + 1) h)

theorem in_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
  have h1 := fun k => hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (h1 k).1, fun c' => ?_⟩
  simp only
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (h1 k).2 (c' k)
  obtain ⟨hz', s, hs, -⟩ := hr
  exact ⟨s, hs⟩

theorem coordsAt_smul {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (hw : CoordsAt ξ y z w) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k c' hu => ?_⟩
  · obtain ⟨c', h'⟩ := hw.1 k
    exact ⟨c', (isUnit_iff_ne_zero.2 (hc k)).mul h'⟩
  · have hu' : IsUnit (w ⟨k, c'⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hu.ne_zero)
    obtain ⟨h1, h2⟩ := hw.2 k c' hu'
    refine ⟨h1, fun i => ?_⟩
    obtain ⟨r, hr, hr'⟩ := h2 i
    refine ⟨r, hr, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, c'⟩)
    rw [hr']; ring

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsLocalRing R]

theorem valAt_mul {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, t, rfl, rfl⟩ := ha
  obtain ⟨_, u, rfl, rfl⟩ := hb
  exact ⟨h, t * u, map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_one {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) : ValAt ξ z 1 1 :=
  ⟨h, 1, map_one _, map_one _⟩

theorem valAt_prod {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) {K : Type} (S : Finset K)
    (a : K → Ω) (r : K → R) (ha : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k ∈ S, a k) (∏ k ∈ S, r k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using valAt_one h
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact valAt_mul (ha k) ih

theorem inv_mem_regAt_of_isUnit {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω} {r : R}
    (ha : ValAt ξ z a r) (hr : IsUnit r) : a⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨_, s, rfl, rfl⟩ := ha
  obtain ⟨u, rfl⟩ : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s hr
  refine ⟨(u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_⟩
  rw [← map_mul, Units.inv_mul, map_one]

theorem bestChart_finite : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L)
    (v : FinitePlace L) (A : Type) [CommRing A] [IsLocalRing A] [Algebra A L] (zA : Sp A ⟶ X),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ r : A, v (algebraMap A L r) ≤ 1) → (∀ r : A, v (algebraMap A L r) = 1 → IsUnit r) →
    CoordsAt ξ y (spMap (algebraMap A L) ≫ zA) w →
    ∃ (c : (k : K) → J k) (h : genPt ξ ⤳ centre zA), (∀ k, w ⟨k, c k⟩ ≠ 0) ∧
      (∀ k i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c k⟩)) ∧
      InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zA, h⟩ := by
  intro X Ω _ ξ K _ J _ y L _ _ w v A _ _ _ zA hq hT hle hun hC

  have hmax : ∀ k, ∃ c : J k, w ⟨k, c⟩ ≠ 0 ∧ ∀ i, v (w ⟨k, i⟩) ≤ v (w ⟨k, c⟩) := by
    intro k
    obtain ⟨u, hu⟩ := hC.1 k
    haveI : Nonempty (J k) := ⟨u⟩
    obtain ⟨c, hc⟩ := Finite.exists_max (fun i => v (w ⟨k, i⟩))
    refine ⟨c, ?_, hc⟩
    have h0 : 0 < v (w ⟨k, u⟩) := FinitePlace.pos_iff.2 hu.ne_zero
    exact FinitePlace.pos_iff.1 (h0.trans_le (hc u))
  choose c hc0 hcm using hmax
  have h := hq (centre zA)
  refine ⟨c, h, hc0, hcm, ?_⟩
  set x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩ with hx
  set zL : Sp L ⟶ X := spMap (algebraMap A L) ≫ zA with hzL
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).1
  have hxc : x c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k

  obtain ⟨c', hc', hreg⟩ := hT.cover ⟨centre zA, h⟩

  obtain ⟨s, hs⟩ := hreg c
  set r : A := (Scheme.stalkClosedPointTo zA).hom s with hr
  have hvA : ValAt ξ zA (x c / x c') r := ⟨h, s, hs, rfl⟩
  have hvL : ValAt ξ zL (x c / x c') (algebraMap A L r) := LieTangent.valAt_base hT.gen _ hvA

  have hL : genPt ξ ⤳ centre zL := hq _
  have hk : ∀ k, ∃ ρ : L, ValAt ξ zL (y ⟨k, c' k⟩ / y ⟨k, c k⟩) ρ ∧ w ⟨k, c' k⟩ = ρ * w ⟨k, c k⟩ :=
    fun k => (hC.2 k (c k) (isUnit_iff_ne_zero.2 (hc0 k))).2 (c' k)
  choose ρ hρ hρw using hk
  have hprod : ValAt ξ zL (x c' / x c) (∏ k, ρ k) := by
    have e : x c' / x c = ∏ k, y ⟨k, c' k⟩ / y ⟨k, c k⟩ := (Finset.prod_div_distrib _ _).symm
    rw [e]
    exact valAt_prod hL _ _ _ fun k => hρ k
  have hone : algebraMap A L r * ∏ k, ρ k = 1 := by
    have e : x c / x c' * (x c' / x c) = 1 := by field_simp
    have := valAt_mul hvL hprod
    rw [e] at this
    exact LieTangent.valAt_unique hT.gen this (valAt_one hL)

  have hρ1 : ∀ k, v (ρ k) ≤ 1 := by
    intro k
    have e := congrArg v (hρw k)
    rw [map_mul] at e
    have hp : 0 < v (w ⟨k, c k⟩) := FinitePlace.pos_iff.2 (hc0 k)
    have := hcm k (c' k)
    rw [e] at this
    exact le_of_mul_le_mul_right (by simpa using this) hp
  have hP : v (∏ k, ρ k) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one₀ (fun _ _ => by positivity) fun k _ => hρ1 k
  have hsize : v (algebraMap A L r) = 1 := by
    have e := congrArg v hone
    rw [map_mul, map_one] at e
    refine le_antisymm (hle r) ?_
    have h0 : 0 ≤ v (algebraMap A L r) := by positivity
    nlinarith
  have hinv : (x c / x c')⁻¹ ∈ regAt ξ ⟨centre zA, h⟩ :=
    inv_mem_regAt_of_isUnit h hvA (hun r hsize)
  refine ⟨hxc, fun d => ?_⟩
  have e : x d / x c = x d / x c' * (x c / x c')⁻¹ := by field_simp
  rw [e]
  exact mul_mem (hreg d) hinv

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem exists_algHom_eq_zero_of_not_isUnit {T : Type} [CommRing T] [Algebra ℂ T] [Algebra.FiniteType ℂ T]
    (a : T) (h : ¬ IsUnit a) : ∃ χ : T →ₐ[ℂ] ℂ, χ a = 0 := by
  obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : a ∈ M := haM (Ideal.mem_span_singleton_self a)
  letI := Ideal.Quotient.field M
  haveI : Algebra.FiniteType ℂ (T ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ M) (Ideal.Quotient.mkₐ_surjective ℂ M)
  haveI : Module.Finite ℂ (T ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ M)
  have hbij : Function.Bijective (algebraMap ℂ (T ⧸ M)) :=
    ⟨(algebraMap ℂ (T ⧸ M)).injective, IsSepClosed.algebraMap_surjective ℂ (T ⧸ M)⟩
  let e : ℂ ≃ₐ[ℂ] T ⧸ M := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ M)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M), ?_⟩
  simp [Ideal.Quotient.eq_zero_iff_mem.2 hmem]

theorem fromSpec_comp_structure {X : Scheme.{0}} (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ s = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)) := by
  rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial)]
  congr 1
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

private theorem germ_comp_stalkClosedPointTo_eq {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    (χ : Γ(X, V) ⟶ CommRingCat.of ℂ)
    (hp : (Spec.map χ ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ V) :
    X.presheaf.germ V _ hp ≫ Scheme.stalkClosedPointTo (Spec.map χ ≫ hV.fromSpec) = χ := by
  rw [Scheme.stalkClosedPointTo_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc]
  rw [IsAffineOpen.fromSpec_app_self, Category.assoc]
  erw [TopCat.Presheaf.germ_res_assoc]
  erw [Scheme.germ_stalkClosedPointTo_Spec]
  simp

theorem isUnit_res_of_forall_point {X : Scheme.{0}} (s : X ⟶ Sp ℂ) [LocallyOfFiniteType s] {U V : X.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ U) (a : Γ(X, U))
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) :
    IsUnit (X.presheaf.map (homOfLE hVU).op a) := by
  by_contra hr
  let φ : CommRingCat.of ℂ ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)
  letI : Algebra ℂ Γ(X, V) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, V) := by
    have h1 : (s.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact h1.comp h2
  obtain ⟨χ, hχ⟩ := exists_algHom_eq_zero_of_not_isUnit (X.presheaf.map (homOfLE hVU).op a) hr
  let χ' : Γ(X, V) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom χ.toRingHom
  let x : Sp ℂ ⟶ X := Spec.map χ' ≫ hV.fromSpec
  have hxs : x ≫ s = 𝟙 _ := by
    have hc : φ ≫ χ' = 𝟙 _ := by
      ext z
      exact χ.commutes z
    simp only [x, Category.assoc, fromSpec_comp_structure s hV]
    rw [← Spec.map_comp]
    exact (congrArg Spec.map hc).trans (Spec.map_id _)
  have hxV : (Spec.map χ' ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ V := by
    have hr' : (Spec.map χ' ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈
        Set.range hV.fromSpec := ⟨_, rfl⟩
    rwa [hV.range_fromSpec] at hr'
  have hxU : centre x ∈ U := hVU hxV
  apply h x hxs hxU
  rw [← val_germ x U hxU a]
  have e1 := congrArg (fun f => f.hom (X.presheaf.map (homOfLE hVU).op a)) (germ_comp_stalkClosedPointTo_eq hV χ' hxV)
  have e2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) _ hxV a
  simp only [CommRingCat.comp_apply] at e1
  erw [← e2]
  exact e1.trans hχ

theorem isUnit_of_forall_complexPoint (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (U : X.Opens) (a : Γ(X, U))
    (hs : LocallyOfFiniteType s)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace U a fun p hp => ?_
  obtain ⟨V, hV, hpV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  haveI := hs
  have hu := isUnit_res_of_forall_point s hV hVU a h
  have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) p hpV a
  have := hu.map (X.presheaf.germ V p hpV).hom
  rw [e] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.twist_ok_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | exact GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.special_fibre_closed_specialization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ∀ (y x : Cpt ξ) (g : Ω), ¬ unitAt ξ y (algebraMap O Ω ϖ) → y.1 ⤳ x.1 → IsClosed ({x.1} : Set X) → g ∈ regAt ξ x → unitAt ξ y g → ¬ unitAt ξ x g → ∃ (Γ : FibreCurve ξ (algebraMap O Ω ϖ)) (i : Γ.C.I), y.1 ⤳ centre Γ.η ∧ unitAt ξ ⟨centre Γ.η, Γ.η_spec⟩ g ∧ centre (Γ.z i) = x.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_fibreCurve_through_closed_point | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_fibreCurve_through_closed_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_fibreCurve_through_closed_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.period_set_closed : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSeparated G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∀ (s : (Fin n → ℂ) → (Fin g → ℂ)), ContinuousAt s b₀ → (∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b) → s b₀ ∈ e.per b₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_per_of_frequently | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_per_of_frequently | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_per_of_frequently <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.label_embedding_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H) (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧ Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.labels_all_once | exact GlobalTheory.CompanionTheory.Ar.labels_all_once | (intros; apply GlobalTheory.CompanionTheory.Ar.labels_all_once <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem _root_.GlobalTheory.T.finite_norm_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | exact GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.FinPlace.exists_rho <;> assumption)
end
