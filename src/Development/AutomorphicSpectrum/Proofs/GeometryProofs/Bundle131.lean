module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle082
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle122
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle121
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogX
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq {U : X.Opens} (g : Γ(X, U)) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) :
    genMap ξ p (X.presheaf.germ U p.1 hp g) = genMap ξ q (X.presheaf.germ U q.1 hq g) := by
  have key : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.2 hr) g) := by
    intro r hr
    show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes r.2 (X.presheaf.germ U r.1 hr g)) = _
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hr r.2 g)
  rw [key p hp, key q hq]

theorem unitAt_of_isUnit {p : Cpt ξ} {s : X.presheaf.stalk p.1} (hs : IsUnit s) :
    unitAt ξ p (genMap ξ p s) := by
  have hu : IsUnit (genMap ξ p s) := hs.map (genMap ξ p)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hu.ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

theorem isUnit_of_unitAt (hξ : IsCptGen ξ) {p : Cpt ξ} {s : X.presheaf.stalk p.1}
    (h : unitAt ξ p (genMap ξ p s)) : IsUnit s := by
  obtain ⟨h0, _, t, ht⟩ := h
  refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
  rw [map_mul, ht, map_one, mul_inv_cancel₀ h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem inFrameDomain_of_unitAt (hT : CoordTie ℤ ξ (segreCoord y)) {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (hz : CoordsAt ξ y z w) (h : genPt ξ ⤳ centre z) {c : (k : K) → J k} {f : Ω}
    (hc : InChart ξ (segreCoord y) c ⟨centre z, h⟩) (hf : unitAt ξ ⟨centre z, h⟩ f) :
    InFrameDomain y c f w := by
  let gv : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, h⟩
  let ev : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have hinj : Function.Injective gv := hT.gen.inj ⟨centre z, h⟩
  constructor
  · choose d hd using hz.1
    have key : ∀ k, ∃ (r : ℂ) (s : X.presheaf.stalk (centre z)),
        gv s = y ⟨k, c k⟩ / y ⟨k, d k⟩ ∧ ev s = r ∧ w ⟨k, c k⟩ = r * w ⟨k, d k⟩ := by
      intro k
      obtain ⟨r, ⟨_, s, hs, hv⟩, hw⟩ := (hz.2 k (d k) (hd k)).2 (c k)
      exact ⟨r, s, hs, hv, hw⟩
    choose r s hs hv hw using key
    obtain ⟨t, ht⟩ : ∃ t, gv t = segreCoord y d / segreCoord y c := hc.2 d
    have hxd : segreCoord y d ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => (hz.2 k (d k) (hd k)).1
    have hxc : segreCoord y c ≠ 0 := hc.1
    have hone : t * ∏ k, s k = 1 := by
      refine hinj ?_
      rw [map_mul, map_prod, ht, map_one]
      simp only [hs]
      rw [Finset.prod_div_distrib]
      change segreCoord y d / segreCoord y c * (segreCoord y c / segreCoord y d) = 1
      field_simp
    have hval := congrArg ev hone
    rw [map_mul, map_prod, map_one] at hval
    simp only [hv] at hval
    have hr : ∏ k, r k ≠ 0 := right_ne_zero_of_mul_eq_one hval
    intro k
    rw [hw k]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.1 hr k (Finset.mem_univ k)) (hd k).ne_zero
  · obtain ⟨s, hs⟩ : ∃ s, gv s = f := hf.2.1
    obtain ⟨t, ht⟩ : ∃ t, gv t = f⁻¹ := hf.2.2
    have hone : s * t = 1 := by
      refine hinj ?_
      rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf.1]
    have hval := congrArg ev hone
    rw [map_mul, map_one] at hval
    exact ⟨ev s, (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hz f _).1 ⟨h, s, hs, rfl⟩,
      left_ne_zero_of_mul_eq_one hval⟩

variable {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ} {W : ChartBundle ℤ (segreCoord y) r F} {L : Lat ξ F}

theorem exists_frames_on_chart (hT : CoordTie ℤ ξ (segreCoord y)) (hV : L.IsVB r ⊤)
    (hC : L.IsChartOf (segreCoord y) W.lat) (c : (k : K) → J k) (hc : segreCoord y c ≠ 0) :
    ∃ S : Set (Ω × (Fin r → F)), S.Finite ∧ (∀ a ∈ S, IsFrameOver y W c a.1 a.2) ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → ∃ a ∈ S, unitAt ξ p a.1 := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have loc : ∀ q : U, ∃ (g : Γ(X, U)) (b : Fin r → F), q.1 ∈ X.basicOpen g ∧
      ∀ p : Cpt ξ, p.1 ∈ X.basicOpen g → L.IsFrameAt b p := by
    intro q
    obtain ⟨h, -⟩ := (hmem q.1).1 q.2
    obtain ⟨V, hqV, b, -, hb⟩ := hV ⟨q.1, h⟩ (Set.mem_univ _)
    obtain ⟨g, hgV, hqg⟩ := hU.exists_basicOpen_le (V := V) ⟨q.1, hqV⟩ q.2
    exact ⟨g, b, hqg, fun p hp => hb p (Set.mem_univ _) (hgV hp)⟩
  choose g b hq hfr using loc
  have hsp : ∀ q : U, genPt ξ ⤳ q.1 := fun q => ((hmem q.1).1 q.2).1
  have hpU : ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → p.1 ∈ U :=
    fun p hp => (hmem p.1).2 ⟨p.2, hp⟩
  let v : U → Ω := fun q => genMap ξ ⟨q.1, hsp q⟩ (X.presheaf.germ U q.1 q.2 (g q))
  have hv : ∀ (q : U) (p : Cpt ξ) (hp : p.1 ∈ U), v q = genMap ξ p (X.presheaf.germ U p.1 hp (g q)) :=
    fun q p hp => genMap_germ_eq (g q) ⟨q.1, hsp q⟩ p q.2 hp
  have hunit : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → p.1 ∈ X.basicOpen (g q) → unitAt ξ p (v q) := by
    intro q p hp hb
    rw [hv q p hp]
    exact unitAt_of_isUnit ((Scheme.mem_basicOpen _ _ _ hp).1 hb)
  have hbasic : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → unitAt ξ p (v q) → p.1 ∈ X.basicOpen (g q) := by
    intro q p hp hu
    rw [hv q p hp] at hu
    exact (Scheme.mem_basicOpen _ _ _ hp).2 (isUnit_of_unitAt hT.gen hu)
  have hcov : (U : Set X) ⊆ ⋃ q : U, (X.basicOpen (g q) : Set X) :=
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hq _⟩
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover _ (fun q => (X.basicOpen (g q)).isOpen) hcov
  refine ⟨(fun q => (v q, b q)) '' (↑t : Set _), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    have hne : v q ≠ 0 := (hunit q ⟨q.1, hsp q⟩ q.2 (hq q)).1
    have hring : v q ∈ chartRing ℤ (segreCoord y) c :=
      (hT.ring c hc (v q)).2 fun p hp => ⟨_, (hv q p (hpU p hp)).symm⟩
    exact (GlobalTheory.T.segre_chart_bundle X Ω ξ K J y F r W L hT hV hC c (v q) (b q) hc hring hne).2
      fun p hp hu => hfr q p (hbasic q p (hpU p hp) hu)
  · intro p hp
    obtain ⟨q, hqt, hqp⟩ := Set.mem_iUnion₂.1 (ht (hpU p hp))
    exact ⟨_, ⟨q, hqt, rfl⟩, hunit q p (hpU p hp) hqp⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrames

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem exists_frames_cover_mcPts : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F : Type) [AddCommGroup F] [Module Ω F] (r : ℕ) (W : ChartBundle ℤ (segreCoord y) r F) (L : Lat ξ F), CoordTie ℤ ξ (segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (segreCoord y) W.lat → ∃ (m : ℕ) (ch : Fin m → (k : K) → J k) (fr : Fin m → Ω) (b : Fin m → Fin r → F), (∀ i, IsFrameOver y W (ch i) (fr i) (b i)) ∧ ∀ w ∈ mcPts (mCoordIdeal y), ∃ i, InFrameDomain y (ch i) (fr i) w := by
  classical
  intro X Ω _ ξ K _ J _ y F _ _ r W L hT hV hC
  have hloc := fun c : {c : (k : K) → J k // segreCoord y c ≠ 0} =>
    ChartFrames.exists_frames_on_chart (W := W) (L := L) hT hV hC c.1 c.2
  choose S hfin hframe hcov using hloc
  let T : Set (((k : K) → J k) × Ω × (Fin r → F)) :=
    ⋃ c, (fun a : Ω × (Fin r → F) => (c.1, a.1, a.2)) '' S c
  have hTfin : T.Finite := Set.finite_iUnion fun c => (hfin c).image _
  haveI := hTfin.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨m, fun i => (e.symm i).1.1, fun i => (e.symm i).1.2.1, fun i => (e.symm i).1.2.2, ?_, ?_⟩
  · have hall : ∀ t ∈ T, IsFrameOver y W t.1 t.2.1 t.2.2 := by
      intro t ht
      obtain ⟨c, a, ha, rfl⟩ := Set.mem_iUnion.1 ht
      exact hframe c a ha
    exact fun i => hall _ (e.symm i).2
  · intro w hw
    obtain ⟨z, h, hz⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hw
    obtain ⟨c, hc⟩ := hT.cover ⟨centre z, h⟩
    obtain ⟨a, ha, hu⟩ := hcov ⟨c, hc.1⟩ ⟨centre z, h⟩ hc
    have hmem : (c, a.1, a.2) ∈ T := Set.mem_iUnion.2 ⟨⟨c, hc.1⟩, a, ha, rfl⟩
    refine ⟨e ⟨_, hmem⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ChartFrames.inFrameDomain_of_unitAt hT hz h hc hu

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.BlockFrame

theorem frame_of_sum_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P Wv : Type) [AddCommGroup P] [Module Ω P] [AddCommGroup Wv] [Module Ω Wv] (i : Wv →ₗ[Ω] P) (A B : Lat ξ P) (Va Vb : Submodule Ω P) (N j : ℕ) (hj : j ≤ N) (b : Fin N → Wv) (s : Fin (N - j) → P) (p : Cpt ξ), Function.Injective i → LinearMap.range i = Va ⊔ Vb → Disjoint Va Vb → (∀ x ∈ A p, x ∈ Va) → (∀ x ∈ B p, x ∈ Vb) → (Lat.comap (fun q => A q ⊔ B q) i).IsFrameAt b p → Submodule.span Ω (Set.range (b ∘ headIdx hj)) = Va.comap i → (∀ k, s k ∈ Vb ∧ i (b (tailIdx hj k)) - s k ∈ Va) → B.IsFrameAt s p ∧ (∀ k, i (b (tailIdx hj k)) - s k ∈ A p) ∧ ∀ k, i (b (headIdx hj k)) ∈ A p := by
  intro X Ω _ ξ P Wv _ _ _ _ i A B Va Vb N j hj b s p hinj hrange hdisj hAV hBV hfr hhead hs
  have hzero : ∀ {x : P}, x ∈ Va → x ∈ Vb → x = 0 := fun h1 h2 => Submodule.disjoint_def.1 hdisj _ h1 h2
  have hmemfr : ∀ k, i (b k) ∈ A p ⊔ B p := fun k => by
    have h : b k ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hbhead : ∀ k, i (b (headIdx hj k)) ∈ Va := fun k => by
    have h : b (headIdx hj k) ∈ Va.comap i := by
      rw [← hhead]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h
  have hH : ∀ k, i (b (headIdx hj k)) ∈ A p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (headIdx hj k))
    have he0 : e = 0 := hzero (by
      have h : e = i (b (headIdx hj k)) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hbhead k) (hAV a ha)) (hBV e he)
    rw [← hae, he0, add_zero]
    exact ha
  have hT : ∀ k, i (b (tailIdx hj k)) - s k ∈ A p ∧ s k ∈ B p := fun k => by
    obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 (hmemfr (tailIdx hj k))
    have hes : e - s k = 0 := hzero (by
      have h : e - s k = (i (b (tailIdx hj k)) - s k) - a := by rw [← hae]; abel
      rw [h]
      exact Va.sub_mem (hs k).2 (hAV a ha)) (Vb.sub_mem (hBV e he) (hs k).1)
    have hes' : e = s k := sub_eq_zero.1 hes
    refine ⟨?_, hes' ▸ he⟩
    have h : i (b (tailIdx hj k)) - s k = a := by rw [← hae, hes']; abel
    rw [h]
    exact ha
  have hcase : ∀ k : Fin N, (∃ a, k = headIdx hj a) ∨ ∃ a, k = tailIdx hj a := fun k => by
    by_cases h : (k : ℕ) < j
    · exact Or.inl ⟨⟨k, h⟩, by ext; rfl⟩
    · exact Or.inr ⟨⟨k - j, by have := k.2; omega⟩, by ext; simp [tailIdx]; omega⟩
  have hspan : ∀ x ∈ Submodule.span (regAt ξ p) (Set.range b),
      ∃ t ∈ Submodule.span (regAt ξ p) (Set.range s), i x - t ∈ Va := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rcases hcase k with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨0, zero_mem _, by simpa using hbhead a⟩
      · exact ⟨s a, Submodule.subset_span ⟨a, rfl⟩, (hs a).2⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨t, ht, hxt⟩ := hx
      obtain ⟨t', ht', hyt⟩ := hy
      refine ⟨t + t', add_mem ht ht', ?_⟩
      have h : i (x + y) - (t + t') = (i x - t) + (i y - t') := by rw [map_add (f := _)]; abel
      rw [h]
      exact Va.add_mem hxt hyt
    | smul r x _ hx =>
      obtain ⟨t, ht, hxt⟩ := hx
      refine ⟨r • t, Submodule.smul_mem _ r ht, ?_⟩
      have h : i (r • x) - r • t = (r : Ω) • (i x - t) := by
        rw [smul_sub]
        show i ((r : Ω) • x) - (r : Ω) • t = _
        rw [map_smul]
      rw [h]
      exact Va.smul_mem _ hxt
  have hle : Submodule.span (regAt ξ p) (Set.range s) ≤ B p := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact (hT k).2)
  have hgen : B p = Submodule.span (regAt ξ p) (Set.range s) := by
    refine le_antisymm (fun e he => ?_) hle
    have hr : e ∈ LinearMap.range i := by
      rw [hrange]
      exact Submodule.mem_sup_right (hBV e he)
    obtain ⟨x, rfl⟩ := hr
    have hxc : x ∈ (Lat.comap (fun q => A q ⊔ B q) i) p := by
      show i x ∈ A p ⊔ B p
      exact Submodule.mem_sup_right he
    rw [hfr.2] at hxc
    obtain ⟨t, ht, hxt⟩ := hspan x hxc
    have h0 : i x - t = 0 := hzero hxt (Vb.sub_mem (hBV _ he) (hBV _ (hle ht)))
    rw [sub_eq_zero.1 h0]
    exact ht
  have htinj : Function.Injective (tailIdx hj) := fun a c h => by
    have h' := congrArg Fin.val h
    simp only [tailIdx] at h'
    ext
    omega
  have hli : LinearIndependent Ω s := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have hx1 : (∑ k, g k • b (tailIdx hj k)) ∈ Va.comap i := by
      have h : i (∑ k, g k • b (tailIdx hj k)) = ∑ k, g k • (i (b (tailIdx hj k)) - s k) := by

        simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, hg, sub_zero]
      show i _ ∈ Va
      rw [h]
      exact Va.sum_mem fun k _ => Va.smul_mem _ (hs k).2
    have hdis : Disjoint (Set.range (headIdx hj)) (Set.range (tailIdx hj)) := by
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨a, rfl⟩ ⟨c, h⟩
      have h' := congrArg Fin.val h
      simp only [headIdx, tailIdx, Fin.val_castLE] at h'
      have := a.2
      omega
    have hd := hfr.1.disjoint_span_image hdis
    have hx2 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (tailIdx hj)) :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨_, ⟨k, rfl⟩, rfl⟩)
    have hx3 : (∑ k, g k • b (tailIdx hj k)) ∈ Submodule.span Ω (b '' Set.range (headIdx hj)) := by
      rw [← Set.range_comp, hhead]
      exact hx1
    have hx0 := Submodule.disjoint_def.1 hd _ hx3 hx2
    exact Fintype.linearIndependent_iff.1 (hfr.1.comp _ htinj) g hx0
  exact ⟨⟨hli, hgen⟩, fun k => (hT k).1, hH⟩

end GlobalTheory.CompanionTheory.Ar.BlockFrame
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LiesOver

open GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem valAt_add {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t + t', map_add _ _ _, map_add _ _ _⟩

theorem valAt_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {w : (Σ k, J k) → ℂ}

theorem evC_xpow (w : (Σ k, J k) → ℂ) (c : ∀ k, J k) (e : K → ℕ) :
    evC w (ArakelovGeometry.xpow c e) = ∏ k, w ⟨k, c k⟩ ^ e k := by
  simp [evC, ArakelovGeometry.xpow, map_prod]

theorem exists_form_valAt (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (G : MRing J), IsMultiHomog G δ ∧ aeval y G = x * ∏ k, y ⟨k, c k⟩ ^ δ k ∧
      ValAt ξ z x (evC w G / ∏ k, w ⟨k, c k⟩ ^ δ k) := by
  classical
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hW : ∀ δ : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 := fun δ =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc0 k)
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpowC : ∀ δ₁ δ₂ : K → ℕ, ∏ k, w ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, w ⟨k, c k⟩ ^ δ₁ k) * ∏ k, w ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, MvPolynomial.X ⟨k, i⟩, ArakelovGeometry.isMultiHomog_X' k i, ?_, ?_⟩
    · rw [aeval_X, Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
      simp [div_mul_cancel₀ _ (hy k)]
    · obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
      have e1 : (∏ k', w ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k') = w ⟨k, c k⟩ := by
        rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
        simp
      have e2 : evC w (MvPolynomial.X ⟨k, i⟩ : MRing J) = w ⟨k, i⟩ := by simp [evC]
      rw [e1, e2, e, mul_div_cancel_right₀ _ (hc0 k)]
      exact hr
  | algebraMap r =>
    refine ⟨0, C r, isMultiHomog_C r, by simp, ?_⟩
    have e : evC w (C r : MRing J) = (r : ℂ) := by simp [evC]
    simp only [e, Pi.zero_apply, pow_zero, Finset.prod_const_one, div_one]
    simpa using valAt_int hz r
  | add a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁,
      isMultiHomog_add (ArakelovGeometry.isMultiHomog_mul h₁ (ArakelovGeometry.isMultiHomog_xpow c δ₂)) ?_, ?_, ?_⟩
    · rw [add_comm δ₁]
      exact ArakelovGeometry.isMultiHomog_mul h₂ (ArakelovGeometry.isMultiHomog_xpow c δ₁)
    · rw [map_add (f := _), map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, hpow]
      ring
    · convert valAt_add u₁ u₂ using 1
      have e : evC w (e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁) =
          evC w e₁ * evC w (ArakelovGeometry.xpow c δ₂) + evC w e₂ * evC w (ArakelovGeometry.xpow c δ₁) := by
        simp only [evC, map_add (f := _), map_mul]
      rw [e, evC_xpow, evC_xpow, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp
  | mul a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * e₂, ArakelovGeometry.isMultiHomog_mul h₁ h₂, ?_, ?_⟩
    · rw [map_mul, v₁, v₂, hpow]
      ring
    · convert CoordModel.valAt_mul u₁ u₂ using 1
      have e : evC w (e₁ * e₂) = evC w e₁ * evC w e₂ := by simp only [evC, map_mul]
      rw [e, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp

end Values

theorem valAt_cst : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (σ : F' →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), NormalCpt ξ → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → PtOver y ψ σ w → genPt ξ ⤳ centre z → ∀ a : F', ValAt ξ z (ψ a) (σ a) := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ σ z w hN ht hw hp hz a
  classical
  choose c hc using hw.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hO : OverInt y ψ := overInt_of_normalCpt ht hN ψ
  have hint : ∀ b : 𝓞 F', ValAt ξ z (ψ (b : F')) (σ (b : F')) := by
    intro b
    obtain ⟨δ, G, hG, hv, hu⟩ := exists_form_valAt hz hw c hy hc (hO.2 c hy b)
    have h1 := hp.2 (b : F') δ G (ArakelovGeometry.xpow c δ) hG (ArakelovGeometry.isMultiHomog_xpow c δ) (by
      rw [hv, GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.aeval_xpow])
    rw [evC_xpow] at h1
    have hW : (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
    rwa [h1, mul_div_cancel_right₀ _ hW] at hu
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F').2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 := hint (⟨n • a, hi⟩ : 𝓞 F')
  have h2 : ValAt ξ z (n : Ω) ((Units.mk0 (n : ℂ) hnC : ℂˣ) : ℂ) := valAt_int hz n
  obtain ⟨hn0, h3⟩ := CoordModel.valAt_inv h2
  have h4 := CoordModel.valAt_mul h3 h1
  convert h4 using 1
  · show ψ a = (n : Ω)⁻¹ * ψ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ hn0]
  · show σ a = ((Units.mk0 (n : ℂ) hnC)⁻¹ : ℂˣ) * σ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ hnC]

end GlobalTheory.CompanionTheory.Ar.Flat.LiesOver
end
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.line_degree_special_fibre : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical | exact GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.propZ_numerical <;> assumption)
end
