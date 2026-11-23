module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

private theorem stalkClosedPointTo_specMap_comp_eq {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) :
    ∃ e : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω),
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ ξ) =
        (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have hξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hi : IsLocalHom i := ⟨fun a ha => isUnit_iff_ne_zero.mpr (fun h0 => by simp [h0] at ha)⟩
  have hloc : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have key := (SpecToEquivOfLocalRing X (CommRingCat.of G)).right_inv
    ⟨_, Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i, hloc⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at key
  obtain ⟨h1, h2⟩ := key
  change (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω) at h1
  change Scheme.stalkClosedPointTo (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) = (X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom ≫
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i at h2
  have hg : Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [Spec.map_comp, Category.assoc, hξ]
  revert h1 h2
  generalize Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = k at hg
  subst hg
  intro h1 h2
  exact ⟨h1, h2⟩

private theorem stalkClosedPointTo_stalkSpecializes_comp {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) (g : Spec (CommRingCat.of G) ⟶ X)
    (hg : g = Spec.map (CommRingCat.ofHom i) ≫ ξ) (y : X) (hy : g (IsLocalRing.closedPoint G) ⤳ y)
    (h : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (s : X.presheaf.stalk y) :
    (Scheme.stalkClosedPointTo g).hom ((X.presheaf.stalkSpecializes hy).hom s) =
      i ((Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes h).hom s)) := by
  subst hg
  obtain ⟨e, he⟩ := stalkClosedPointTo_specMap_comp_eq ξ i
  rw [he]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.stalkCongr_hom, CommRingCat.hom_ofHom]
  congr 2
  have hh := TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq e.symm).specializes hy
  exact congrArg (fun k => CommRingCat.Hom.hom k s) hh

theorem PositivityTheory.Xgp.inChart_iff_inChart_map_of_dominates : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' := by
  intro X X' Ω G _ _ ξ ξ' f i κ x hT hG' hD p' c₁ h
  set q : Cpt ξ := ⟨f p'.1, h⟩ with hq
  have K : ∀ s : X.presheaf.stalk (f p'.1), genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ q s) := by
    intro s
    have e1 := stalkClosedPointTo_stalkSpecializes_comp ξ i (ξ' ≫ f) hD (f p'.1) (f.base.hom.map_specializes p'.2) h s
    rw [Scheme.stalkClosedPointTo_comp] at e1
    exact (congrArg (Scheme.stalkClosedPointTo ξ').hom
      (Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ p'.2 s).symm).trans e1
  have F1 : ∀ a, a ∈ regAt ξ q → i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨_, K s⟩
  have F2 : ∀ a, a ∈ regAt ξ q → (i a)⁻¹ ∈ regAt ξ' p' → a⁻¹ ∈ regAt ξ q := by
    intro a ha hinv
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp hinv
    by_cases h0 : genMap ξ q s = 0
    · rw [h0, _root_.inv_zero]
      exact zero_mem _
    have hu : IsUnit ((f.stalkMap p'.1).hom s) := by
      have hm : (f.stalkMap p'.1).hom s * t = 1 := by
        apply hG'.inj p'
        rw [map_mul, map_one, K, ht, mul_inv_cancel₀ ((map_ne_zero i).mpr h0)]
      exact isUnit_iff_exists_inv.mpr ⟨t, hm⟩
    obtain ⟨v, hv⟩ := (isUnit_map_iff (f.stalkMap p'.1).hom s).mp hu
    refine RingHom.mem_range.mpr ⟨↑v⁻¹, ?_⟩
    rw [← hv, map_units_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(map_ne_zero i).mpr h1, fun c' => ?_⟩
    show i (x c') / i (x c₁) ∈ regAt ξ' p'
    rw [← map_div₀]
    exact F1 _ (h2 c')
  · rintro ⟨h1, h2⟩
    have h1' : x c₁ ≠ 0 := fun h0 => h1 (by simp [h0])
    obtain ⟨c, hc⟩ := hT.cover q
    obtain ⟨hc0, hc⟩ := hc
    refine ⟨h1', fun c' => ?_⟩
    have hinv : (i (x c₁ / x c))⁻¹ ∈ regAt ξ' p' := by
      rw [map_div₀, inv_div]
      exact h2 c
    have hw := F2 _ (hc c₁) hinv
    have e : x c' / x c₁ = (x c' / x c) * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hc c') hw
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.c_fm_exists_flags_pullmap

theorem flagStep_comp {G M N : Type} [Field G] [AddCommGroup M] [Module G M] [AddCommGroup N] [Module G N]
    (T : M →ₗ[G] N) {r : ℕ} (b : Fin r → M) (i : ℕ) :
    flagStep G (fun k => T (b k)) i = (flagStep G b i).map T := by
  simp only [flagStep, Submodule.map_span, Set.image_image]

end PositivityTheory.Xgp.c_fm_exists_flags_pullmap

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_pullmap : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (E E₁ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (ι : E →ₗ[Ω] E₁) (π : E₁ →ₗ[Ω] E) (L : Lat ξ E) (r : ℕ) (c : Fin r → E) (u : Matrix (Fin r) (Fin r) G), π ∘ₗ ι = LinearMap.id → ((L.map ι).pull ξ' f (TensorProduct.mk Ω G E₁ 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) → (L.pull ξ' f (TensorProduct.mk Ω G E 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E 1 (c l)) := by
  intro X X' Ω G _ _ _ ξ ξ' f E E₁ _ _ _ _ ι π L r c u hπ hfl p hp
  obtain ⟨U, hU, b, hb, hfr⟩ := hfl p hp
  let T := π.baseChange G
  let T' := ι.baseChange G
  have hπι : ∀ e, π (ι e) = e := fun e => LinearMap.congr_fun hπ e
  have hT : ∀ e, T (TensorProduct.mk Ω G E₁ 1 (ι e)) = TensorProduct.mk Ω G E 1 e := fun e => by
    simp [T, hπι]
  have hT' : ∀ e, T' (TensorProduct.mk Ω G E 1 e) = TensorProduct.mk Ω G E₁ 1 (ι e) := fun e => by
    simp [T']
  have hbk : ∀ k, T' (T (b k)) = b k := by
    intro k
    have h1 : b k ∈ flagStep G b r := Submodule.subset_span ⟨k, k.2, rfl⟩
    rw [hb] at h1
    have h2 : flagStep G (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) r ≤
        LinearMap.eqLocus (T' ∘ₗ T) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨m, -, rfl⟩
      refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ?_
      rw [LinearMap.mem_eqLocus, LinearMap.comp_apply, hT, hT']
      rfl
    exact h2 h1
  refine ⟨U, hU, fun k => T (b k), fun i => ?_, fun q hq hqU => ?_⟩
  · rw [c_fm_exists_flags_pullmap.flagStep_comp, hb, ← c_fm_exists_flags_pullmap.flagStep_comp]

    simp only [map_sum, map_smul, hT]
  · obtain ⟨hli, hsp⟩ := hfr q hq hqU
    refine ⟨LinearIndependent.of_comp T' ?_, ?_⟩
    · have : (T' ∘ fun k => T (b k)) = b := funext hbk
      rwa [this]
    · have h3 := congrArg (Submodule.map (T.restrictScalars (regAt ξ' q))) hsp
      have h4 := h3.trans ((Submodule.map_span _ _).trans (congrArg _ (Set.range_comp _ _).symm))
      refine Eq.trans ?_ h4
      refine Eq.trans ?_ (Submodule.map_span _ _).symm
      refine congrArg (Submodule.span (regAt ξ' q)) ?_
      ext y
      constructor
      · rintro ⟨h, e, he, rfl⟩
        exact ⟨_, ⟨h, ι e, ⟨e, he, rfl⟩, rfl⟩, hT e⟩
      · rintro ⟨_, ⟨h, _, ⟨e, he, rfl⟩, rfl⟩, rfl⟩
        exact ⟨h, e, he, hT e⟩
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_res_lift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W J J' : Ideal (MRing ι)) (D d : ℕ) (R : AnLogRes P J D) (R' : AnLogRes W J' d), J = ⊤ → P ≤ W → ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x) := by
  intro K _ ι _ P W J J' D d R R' hJ hPW
  subst hJ
  exact GlobalTheory.CompanionTheory.Ar.PB.Proj.exists_holoMap_of_local_lifts R R'.A (V := R'.U) (μ := R'.lift)
    R'.isOpen_U R'.mem_U R'.holo
    (fun y u hu => ⟨(R'.mem y u hu).1, fun f hf => (R'.mem y u hu).2 f (hPW hf)⟩) R'.compat
end
