module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LLineiso
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle067
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsVerticalBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.finite_type_over_integers_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFType.main | exact GlobalTheory.CompanionTheory.Ar.ChartFType.main | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFType.main <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RegVal

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem germ_frac {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U) (s : X.presheaf.stalk p) :
    ∃ (n d : Γ(X, U)) (m : ℕ), IsUnit (X.presheaf.germ U p hp d) ∧
      s * X.presheaf.germ U p hp d ^ m = X.presheaf.germ U p hp n := by
  obtain ⟨V, hpV, t, rfl⟩ := X.presheaf.exists_germ_eq s
  obtain ⟨d, hdV, hpd⟩ := hU.exists_basicOpen_le (V := V) ⟨p, hpV⟩ hp
  have := hU.isLocalization_basicOpen d
  obtain ⟨m, n, e⟩ := IsLocalization.Away.surj (S := Γ(X, X.basicOpen d)) d
    (X.presheaf.map (homOfLE hdV).op t)
  refine ⟨n, d, m, (X.mem_basicOpen d p hp).1 hpd, ?_⟩
  have e' := congrArg (X.presheaf.germ (X.basicOpen d) p hpd) e
  rw [map_mul, map_pow] at e'
  have h0 : ∀ f : Γ(X, U), X.presheaf.germ (X.basicOpen d) p hpd (algebraMap Γ(X, U) Γ(X, X.basicOpen d) f) =
      X.presheaf.germ U p hp f := fun f =>
    X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le d)) p hpd f
  rw [h0, h0, TopCat.Presheaf.germ_res_apply] at e'
  exact e'

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U : X.Opens} {q : X} (hq : q ∈ U) (h : genPt ξ ⤳ q)
    (f : Γ(X, U)) :
    genMap ξ ⟨q, h⟩ (X.presheaf.germ U q hq f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (h.mem_open U.isOpen hq) f) := by
  have e := congr($(X.presheaf.germ_stalkSpecializes hq h) f)
  simp only [CommRingCat.comp_apply] at e
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom e

theorem add_val {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of ℂ) ⟶ X} {a b : Ω} {r s : ℂ}
    (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨h, x, rfl, rfl⟩ := h
  obtain ⟨_, y, rfl, rfl⟩ := h'
  exact ⟨h, x + y, map_add _ _ _, map_add _ _ _⟩

def QV (i : Ω →+* Ω') (W : Subring Ω') (φ : W →+* ℂ) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (n : Ω) : Prop :=
  ∃ h : i n ∈ W, ValAt ξ z n (φ ⟨i n, h⟩)

variable {i : Ω →+* Ω'} {W : Subring Ω'} {φ : W →+* ℂ} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem QV.add {a b : Ω} (ha : QV i W φ ξ z a) (hb : QV i W φ ξ z b) : QV i W φ ξ z (a + b) := by
  obtain ⟨h1, v1⟩ := ha
  obtain ⟨h2, v2⟩ := hb
  have hm : i (a + b) ∈ W := by rw [map_add (f := _)]; exact W.add_mem h1 h2
  refine ⟨hm, ?_⟩
  have e : (⟨i (a + b), hm⟩ : W) = ⟨_, h1⟩ + ⟨_, h2⟩ := Subtype.ext (by simp)
  rw [e, map_add (f := _)]
  exact add_val v1 v2

theorem QV.mul {a b : Ω} (ha : QV i W φ ξ z a) (hb : QV i W φ ξ z b) : QV i W φ ξ z (a * b) := by
  obtain ⟨h1, v1⟩ := ha
  obtain ⟨h2, v2⟩ := hb
  have hm : i (a * b) ∈ W := by rw [map_mul]; exact W.mul_mem h1 h2
  refine ⟨hm, ?_⟩
  have e : (⟨i (a * b), hm⟩ : W) = ⟨_, h1⟩ * ⟨_, h2⟩ := Subtype.ext (by simp)
  rw [e, map_mul]
  exact CxVal.mul v1 v2

theorem QV.int (hz : genPt ξ ⤳ centre z) (n : ℤ) : QV i W φ ξ z (n : Ω) := by
  have hm : i (n : Ω) ∈ W := by rw [map_intCast]; exact intCast_mem W n
  refine ⟨hm, ?_⟩
  have e : (⟨i (n : Ω), hm⟩ : W) = (n : W) := Subtype.ext (by simp)
  rw [e, map_intCast]
  exact ⟨hz, n, by simp, (map_intCast (Scheme.stalkClosedPointTo z).hom n).trans (by simp)⟩

theorem QV.prod {ι : Type} (hz : genPt ξ ⤳ centre z) (s : Finset ι) (f : ι → Ω)
    (h : ∀ k ∈ s, QV i W φ ξ z (f k)) : QV i W φ ξ z (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using QV.int (i := i) (W := W) (φ := φ) hz 1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    exact (h k (Finset.mem_insert_self k s)).mul (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem QV.adjoin (hz : genPt ξ ⤳ centre z) {S : Set Ω} (hS : ∀ n ∈ S, QV i W φ ξ z n) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ S) : QV i W φ ξ z a := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap n => simpa using QV.int (i := i) (W := W) (φ := φ) hz n
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

theorem val_frac {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {s g n : S} {m : ℕ} (e : s * g ^ m = n) :
    f s * f g ^ m = f n := by
  rw [← e, map_mul, map_pow]

theorem frac_mem (hU : ∀ a : W, φ a ≠ 0 → IsUnit a) {a nn dd : Ω} {m : ℕ} {r vn vd : ℂ}
    (hn : i nn ∈ W) (hd : i dd ∈ W) (vn' : φ ⟨_, hn⟩ = vn) (vd' : φ ⟨_, hd⟩ = vd) (hvd : vd ≠ 0)
    (e : a * dd ^ m = nn) (e' : r * vd ^ m = vn) : ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  obtain ⟨u, hu⟩ := hU ⟨_, hd⟩ (by rw [vd']; exact hvd)
  have h1 : ((u : W) : Ω') = i dd := by rw [hu]
  have h2 : (((u⁻¹ : Wˣ) : W) : Ω') * i dd = 1 := by
    rw [← h1]
    exact congrArg Subtype.val u.inv_mul
  have hia : i a = i nn * (((u⁻¹ : Wˣ) : W) : Ω') ^ m := by
    rw [← e, map_mul, map_pow, mul_assoc, ← mul_pow, mul_comm (i dd), h2, one_pow, mul_one]
  have hm : i a ∈ W := by
    rw [hia]
    exact W.mul_mem hn (W.pow_mem (SetLike.coe_mem _) m)
  refine ⟨hm, ?_⟩
  have e2 : (⟨i a, hm⟩ : W) = ⟨_, hn⟩ * ((u⁻¹ : Wˣ) : W) ^ m := Subtype.ext (by simpa using hia)
  have h3 : φ ((u⁻¹ : Wˣ) : W) * vd = 1 := by
    rw [← vd', ← hu, ← map_mul, u.inv_mul, map_one]
  rw [e2, map_mul, map_pow, vn', ← e', mul_assoc, ← mul_pow, mul_comm vd, h3, one_pow, mul_one]

theorem contains_localRing : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (W : Subring Ω') (φ : W →+* ℂ),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w →
    (∀ a : W, φ a ≠ 0 → IsUnit a) →
    (∀ (k : K) (c e : J k), w ⟨k, c⟩ ≠ 0 →
      ∃ h : i (y ⟨k, e⟩ / y ⟨k, c⟩) ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) →
    ∀ (a : Ω) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  intro X Ω Ω' _ _ i ξ K _ J y z w W φ tie hw hU hyp a r har
  obtain ⟨hz, s, hsa, hsr⟩ := har
  choose c hc using hw.1
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have ratio : ∀ (k : K) (e : J k), QV i W φ ξ z (y ⟨k, e⟩ / y ⟨k, c k⟩) := fun k e => by
    obtain ⟨h, v⟩ := hyp k (c k) e (hc0 k)
    obtain ⟨t, ht, ht'⟩ := (hw.2 k (c k) (hc k)).2 e
    refine ⟨h, ?_⟩
    rwa [mul_right_cancel₀ (hc0 k) (v.trans ht')]
  have gen : ∀ c' : (k : K) → J k, QV i W φ ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) := fun c' => by
    rw [← Finset.prod_div_distrib]
    exact QV.prod hz _ _ fun k _ => ratio k (c' k)
  have hin : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
    refine ⟨hxc, fun c' => ?_⟩
    obtain ⟨_, _, s', hs', _⟩ := gen c'
    exact ⟨s', hs'⟩
  obtain ⟨U, hUa, hUm⟩ := tie.affine c hxc
  have hpU : centre z ∈ U := (hUm _).2 ⟨hz, hin⟩
  obtain ⟨n, d, m, hd, e⟩ := germ_frac hUa hpU s
  have hgU : genPt ξ ∈ U := hz.mem_open U.isOpen hpU
  have hQ : ∀ f : Γ(X, U), QV i W φ ξ z
      ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f)) := fun f => by
    refine QV.adjoin hz (S := Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ?_ ((tie.ring c hxc _).2 fun q hq => ?_)
    · rintro _ ⟨j, rfl⟩
      exact gen j
    · have hqU : q.1 ∈ U := (hUm _).2 ⟨q.2, hq⟩
      exact ⟨X.presheaf.germ U q.1 hqU f, genMap_germ ξ hqU q.2 f⟩
  have hval : ∀ f : Γ(X, U), ∃ h : i ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU f)) ∈ W,
      φ ⟨_, h⟩ = (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hpU f) := fun f => by
    obtain ⟨h, v⟩ := hQ f
    exact ⟨h, CxVal.unique v ⟨hz, _, genMap_germ ξ hpU hz f, rfl⟩⟩
  obtain ⟨hn, vn⟩ := hval n
  obtain ⟨hd', vd⟩ := hval d
  refine frac_mem (m := m) hU hn hd' vn vd (hd.map (Scheme.stalkClosedPointTo z).hom).ne_zero ?_ ?_
  · have e1 := congrArg (genMap ξ ⟨centre z, hz⟩) e
    rw [map_mul, map_pow, hsa, genMap_germ ξ hpU hz, genMap_germ ξ hpU hz] at e1
    exact e1
  · rw [← hsr]
    exact val_frac (Scheme.stalkClosedPointTo z).hom e

end GlobalTheory.CompanionTheory.Ar.RegVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.local_ring_points_existsUnique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (R : Type) [CommRing R] [IsLocalRing R], (∀ w : (Σ k, J k) → R, (∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) → ∃! z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w) ∧ (∀ z : Spec (CommRingCat.of R) ⟶ X, genPt ξ ⤳ centre z → ∃ w, CoordsAt ξ y z w) ∧ ∀ (z : Spec (CommRingCat.of R) ⟶ X) w, genPt ξ ⤳ centre z → CoordsAt ξ y z w → (∀ g ∈ mCoordIdeal y, MvPolynomial.aeval w g = 0) ∧ ∀ w', CoordsAt ξ y z w' ↔ ∃ a : K → Rˣ, w' = fun p => (a p.1 : R) * w p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.tie_points | exact GlobalTheory.CompanionTheory.Ar.tie_points | (intros; apply GlobalTheory.CompanionTheory.Ar.tie_points <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_chart_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ), CoordTie ℤ ξ x → L.IsVB r ⊤ → ∃ W : ChartBundle ℤ x r E, L.IsChartOf x W.lat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB | exact GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB <;> assumption)
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

namespace GlobalTheory.CompanionTheory.Ar.LineIso

theorem lineIso_of_two_degrees : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (a a' : K → ℤ) (e₀ : E) (ρ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → L.IsDegOn Set.univ y a e₀ → L.IsDegOn Set.univ y a' (ρ • e₀) → ∃ f g : MRing ι, IsLineIso (mCoordIdeal y) a a' f g ∧ aeval y f = ρ * aeval y g :=
  @PositivityTheory.UnitarySelfGeneration.l_lineiso

end GlobalTheory.CompanionTheory.Ar.LineIso
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.wedge_line_lattice_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isVBOn_gen_frames | exact GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isVBOn_gen_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isVBOn_gen_frames <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.lattice_generator_invert_constant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread | exact GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curve_degree_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.curveIn_isDeg_unique_of_isCptGen | exact GlobalTheory.CompanionTheory.Ar.Crv.curveIn_isDeg_unique_of_isCptGen | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.curveIn_isDeg_unique_of_isCptGen <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.block_pullback_herm_line : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k), IsBlockMap κ v → (∀ A : HermLine ι, ∃! A' : HermLine ι', IsPullHerm κ v A A') ∧ (∀ (A : HermLine ι) (A' : HermLine ι'), IsPullHerm κ v A A' → IsSmoothHerm A → IsSmoothHerm A') ∧ (∀ (P' : Ideal (MRing ι')), ∀ z ∈ mcPts P', (fun p => z (v p)) ∈ mcPts (imageZ v P')) ∧ ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap | exact GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.hermLine_pull_blockMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorsPull

theorem spMap_cancel {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {Z : Scheme.{0}}
    (a b : Spec (CommRingCat.of Ω) ⟶ Z) (h : spMap i ≫ a = spMap i ≫ b) : a = b := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom i)) :=
    GlobalTheory.CompanionTheory.Ar.LieEx.std_of_inj (CommRingCat.ofHom i) i.injective
  refine GlobalTheory.CompanionTheory.Ar.LieEx.epi_of_surj (Spec.map (CommRingCat.ofHom i)) ?_ a b h
  intro y
  have hs : Subsingleton (Spec (CommRingCat.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of Ω')) :=
    inferInstanceAs (Nonempty (PrimeSpectrum Ω'))
  exact ⟨x, Subsingleton.elim _ _⟩

theorem tr_pow {S : Scheme.{0}} {T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (h : a = b)
    (n : ℕ) (u : Over.mk a ⟶ G) (hu : u ^ n = 1) :
    ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
  subst h
  exact ⟨u, rfl, hu⟩

theorem torsion_of_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ n : ℕ, FullTorsion G ξ n →
  FullTorsion G' ξ' n ∧
  (∀ y : Over.mk ξ ⟶ G, y ^ n = 1 → ∃ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ y' : Over.mk ξ' ⟶ G', y' ^ n = 1 → ∃ y : Over.mk ξ ⟶ G, y ^ n = 1 ∧ y'.left ≫ φ = spMap i ≫ y.left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c'.left → (a * a').left ≫ φ = spMap i ≫ (c * c').left) ∧
  (∀ (a a' : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a'.left ≫ φ = spMap i ≫ c.left → a = a') ∧
  (∀ (a : Over.mk ξ' ⟶ G') (c c' : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → a.left ≫ φ = spMap i ≫ c'.left → c = c') := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hd G _ _ G' _ _ φ h n hf
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  let u : Over.mk (ξ' ≫ f) ⟶ Over.mk ξ := Over.homMk (spMap i) (by simpa using hd'.symm)
  let P : (Over.mk ξ' ⟶ G') →* (Over.mk (ξ' ≫ f) ⟶ G) := pushHom h (Over.mk ξ')
  let Q : (Over.mk ξ ⟶ G) →* (Over.mk (ξ' ≫ f) ⟶ G) := preHom u
  have rel : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), a.left ≫ φ = spMap i ≫ c.left → P a = Q c :=
    fun a c e => Over.OverMorphism.ext e
  have lerp : ∀ (a : Over.mk ξ' ⟶ G') (c : Over.mk ξ ⟶ G), P a = Q c → a.left ≫ φ = spMap i ≫ c.left :=
    fun a c e => congrArg (fun z => z.left) e
  have Pinj : Function.Injective P := by
    intro a a' e
    have e1 : a.left ≫ φ = a'.left ≫ φ := congrArg (fun z => z.left) e
    have w : ∀ b : Over.mk ξ' ⟶ G', b.left ≫ G'.hom = ξ' := fun b => by simpa using Over.w b
    exact Over.OverMorphism.ext (h.1.hom_ext e1 ((w a).trans (w a').symm))
  have Qinj : Function.Injective Q := by
    intro c c' e
    have e1 : spMap i ≫ c.left = spMap i ≫ c'.left := congrArg (fun z => z.left) e
    exact Over.OverMorphism.ext (spMap_cancel i _ _ e1)
  refine ⟨GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates X X' Ω Ω' ξ ξ' f i G G' φ n hd h hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hxw : y.left ≫ G.hom = ξ := by simpa using Over.w y
    have hw : (spMap i ≫ y.left) ≫ G.hom = ξ' ≫ f := by rw [Category.assoc, hxw, hd']
    let y' : Over.mk ξ' ⟶ G' := Over.homMk (h.1.lift (spMap i ≫ y.left) ξ' hw) (h.1.lift_snd _ _ _)
    have e : y'.left ≫ φ = spMap i ≫ y.left := h.1.lift_fst _ _ _
    refine ⟨y', Pinj ?_, e⟩
    rw [map_pow, map_one, rel y' y e, ← map_pow, hy, map_one]
  · intro y' hy'
    have hP : (P y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    obtain ⟨g, hl, hg⟩ := tr_pow hd' n (P y') hP
    obtain ⟨y, hy⟩ := hf Ω' i g hg
    have e : y'.left ≫ φ = spMap i ≫ y.left := hl.symm.trans hy
    refine ⟨y, Qinj ?_, e⟩
    rw [map_pow, map_one, ← rel y' y e, hP]
  · intro a a' c c' e e'
    apply lerp
    rw [map_mul, map_mul, rel a c e, rel a' c' e']
  · intro a a' c e e'
    exact Pinj ((rel a c e).trans (rel a' c e').symm)
  · intro a c c' e e'
    exact Qinj ((rel a c e).symm.trans (rel a c' e'))

end GlobalTheory.CompanionTheory.Ar.TorsPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fibreCurve_curveIn_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) :=
  @PositivityTheory.Xgn.exists_curve_in_fibre_degree

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.exists_vertical_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω), GenUnit y a u → ∃ c : ℝ, VertBound y a u c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound | exact GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound <;> assumption)
end
