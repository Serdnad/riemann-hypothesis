module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationDeterminesChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactor
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.CoverEff

section Gen

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_div_of_isGenAt {Λ : Lat ξ Ω} {p : Cpt ξ} {s s' : Ω} (h : Λ.IsGenAt p s) (h' : Λ.IsGenAt p s') :
    unitAt ξ p (s' / s) := by
  obtain ⟨h0, e⟩ := h
  obtain ⟨h0', e'⟩ := h'
  have m1 : s' ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← e, e']; exact Submodule.mem_span_singleton_self s'
  have m2 : s ∈ Submodule.span (regAt ξ p) {s'} := by
    rw [← e', e]; exact Submodule.mem_span_singleton_self s
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 m1
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 m2
  have hr1 : (r : Ω) * s = s' := hr
  have hr2 : (r' : Ω) * s' = s := hr'
  refine ⟨div_ne_zero h0' h0, ?_, ?_⟩
  · rw [(div_eq_iff h0).2 hr1.symm]; exact r.2
  · rw [inv_div, (div_eq_iff h0').2 hr2.symm]; exact r'.2

theorem tens_isGenAt {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {p : Cpt ξ} {s : I → Ω}
    (h : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h i).1, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨s', hs', rfl⟩
    have hu : unitAt ξ p (∏ i, (s' i / s i) ^ a i) :=
      unitAt.prod _ fun i _ => (unitAt_div_of_isGenAt (h i) (hs' i)).zpow _
    have e : ∏ i, s' i ^ a i = (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, div_mul_cancel₀ _ (h i).1]
    rw [e]
    exact Submodule.mem_span_singleton.2 ⟨⟨_, hu.2.1⟩, rfl⟩
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨s, h, rfl⟩

theorem exists_gen_of_tens {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {p : Cpt ξ} {t : Ω}
    (h : (Lat.tens Λ a).IsGenAt p t) : ∃ s : I → Ω, ∀ i, (Λ i).IsGenAt p (s i) := by
  by_contra hn
  have hE : {t | ∃ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) ∧ t = ∏ i, s i ^ a i} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ ⟨s, hs, _⟩ => hn ⟨s, hs⟩
  have m : t ∈ (Lat.tens Λ a) p := by
    rw [h.2]; exact Submodule.mem_span_singleton_self t
  have m' : t ∈ Submodule.span (regAt ξ p) (∅ : Set Ω) := by
    rw [← hE]; exact m
  rw [Submodule.span_empty, Submodule.mem_bot] at m'
  exact h.1 m'

theorem unitAt_of_mul {p : Cpt ξ} {a b : Ω} (hab : unitAt ξ p (a * b)) (hb : unitAt ξ p b) : unitAt ξ p a := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hab.1
  refine ⟨ha, ?_, ?_⟩
  · have e : a = a * b * b⁻¹ := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.1 hb.2.2
  · have e : a⁻¹ = (a * b)⁻¹ * b := by field_simp [hb.1]
    rw [e]; exact mul_mem hab.2.2 hb.2.1

end Gen

section Below

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀}

theorem inChart_below {p : Cpt ξ} {p₀ : Cpt ξ₀} (i : Ω₀ →+* Ω)
    (hU : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → unitAt ξ p (i a) → unitAt ξ₀ p₀ a)
    (hR : ∀ a : Ω₀, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p) {κ : Type} {x : κ → Ω₀} {a a₀ : κ}
    (h₀ : InChart ξ₀ x a₀ p₀) (h : InChart ξ (fun k => i (x k)) a p) : InChart ξ₀ x a p₀ := by
  have hx : x a ≠ 0 := fun e => h.1 (by simp [e])
  have hu : unitAt ξ₀ p₀ (x a / x a₀) := by
    refine hU _ (h₀.2 a) ⟨(map_ne_zero i).2 (div_ne_zero hx h₀.1), hR _ (h₀.2 a), ?_⟩
    rw [← map_inv₀, inv_div, map_div₀]
    exact h.2 a₀
  refine ⟨hx, fun c => ?_⟩
  have e : x c / x a = x c / x a₀ * (x a / x a₀)⁻¹ := by
    have := h₀.1
    field_simp
  rw [e]
  exact mul_mem (h₀.2 c) hu.2.2

end Below

theorem rootLat_isGenAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y}
    (Fl : 𝔐.Flag) (r : RootIx D) {p : Cpt 𝔐.ξ} {g : Ω}
    (hg : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt p g) :
    (Fl.rootLat r).IsGenAt p (g ^ HodgeCpt.rootSgn D r) := by
  have := tens_isGenAt (I := Unit)
    (Λ := fun _ => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (fun _ => HodgeCpt.rootSgn D r) (p := p) (s := fun _ => g) fun _ => hg
  simpa [HodgeCpt.Flag.rootLat] using this

theorem section_on_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (S₀ S : Finset ℕ) (o : RootOrigin Y S₀ R Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (𝔐 : HodgeCpt Y S y) (i : R.Ω →+* Ω) (h : 𝔐.X ⟶ o.𝔐.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) → GenPull o.Fl Fl i hd → Fl.RootLines xdeg e → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt o.𝔐.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : R.Ω), a ∈ regAt o.𝔐.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ x : 𝔐.X, x ∈ abLocus 𝔐.t.G ↔ h x ∈ abLocus o.𝔐.t.G) → ∀ p : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p) → ∀ (a : Fin (Fx.m + 1)) (t : Ω), InChart 𝔐.ξ (fun i' => (i.comp o.g) (Fx.yf i')) a p → (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p t → (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t ∈ regAt 𝔐.ξ p ∧ (p.1 ∉ abLocus 𝔐.t.G → ¬ unitAt 𝔐.ξ p ((i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t)) := by
  intro E _ _ _ H D l Xo c O _ β Y Sys Fx R S₀ S o Ω _ K _ J _ y bk bx 𝔐 i h hd Fl xdeg e hy hG hL hU hR hab p hp a t
    hch ht
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r (pushCpt hd p) := by
    intro r hr hf
    apply hf
    have u : unitAt 𝔐.ξ p (r : Ω) := not_not.1 (hp r hr)
    exact hU p (r : R.Ω) (natCast_mem _ r) (by rw [map_natCast]; exact u)
  obtain ⟨c₀, hc₀⟩ := o.𝔐.tie.cover (pushCpt hd p)
  have hprod : ∀ k, R.y ⟨k, c₀ k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc₀.1) k (Finset.mem_univ k)
  have ya₀ : o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) = R.y ⟨o.k₀, c₀ o.k₀⟩ := by
    rw [← o.y_eq, Equiv.apply_symm_apply]
  have hch₀ : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c₀ o.k₀)) (pushCpt hd p) := by
    refine ⟨?_, fun j => ?_⟩
    · show o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ≠ 0
      rw [ya₀]; exact hprod _
    · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c₀ o.k₀))) ∈ _
      rw [ya₀, ← o.y_eq]
      exact Lat.block_ratio_mem hc₀ o.k₀ (o.ix j)
  have hcha : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) a (pushCpt hd p) :=
    inChart_below i (hU p) (hR p) hch₀ hch
  have gens : ∀ r : RootIx D, ∃ g : R.Ω, ((o.𝔐.V (HodgeCpt.rootIdx D r).1).gr (o.Fl.b (HodgeCpt.rootIdx D r).1)
      (HodgeCpt.rootIdx D r).2).IsGenAt (pushCpt hd p) g := by
    intro r
    have hgen : (o.Fl.rootLat r).IsGenAt (pushCpt hd p) ((∏ k, R.y ⟨k, c₀ k⟩ ^ R.xdeg r k) • o.e r) :=
      ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hprod k)) (o.lines r).1,
        (o.lines r).2 _ trivial c₀ hc₀⟩
    obtain ⟨s, hs⟩ := exists_gen_of_tens hgen
    exact ⟨s (), hs ()⟩
  choose g hg using gens
  have ht₀ := tens_isGenAt (fun r => -Fx.n r) fun r => rootLat_isGenAt o.Fl r (hg r)
  have ht₁ : (Lat.tens Fl.rootLat fun r => -Fx.n r).IsGenAt p
      (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r))) := by
    have := tens_isGenAt (Λ := Fl.rootLat) (fun r => -Fx.n r) fun r =>
      rootLat_isGenAt Fl r (hG p hp _ _ _ (hg r))
    simpa only [map_prod, map_zpow₀] using this
  have hv := unitAt_div_of_isGenAt ht ht₁
  obtain ⟨hreg, hnu⟩ := o.eff (pushCpt hd p) hp0 a _ hcha ht₀
  have key : (i.comp o.g) Fx.sE * (i.comp o.g) (Fx.yf a) ^ Fx.q' / t =
      i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q' / ∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) *
        (i (∏ r, (g r ^ HodgeCpt.rootSgn D r) ^ (-Fx.n r)) / t) := by
    have h1 := ht₁.1
    have h2 := ht.1
    rw [map_div₀ i (o.g Fx.sE * o.g (Fx.yf a) ^ Fx.q'), div_mul_div_cancel₀ h1, map_mul, map_pow]
    rfl
  rw [key]
  refine ⟨mul_mem (hR p _ hreg) hv.2.1, fun hnab hu => ?_⟩
  exact hnu (fun hm => hnab ((hab p.1).2 hm)) (hU p _ hreg (unitAt_of_mul hu hv))

end GlobalTheory.CompanionTheory.Ar.Chg.CoverEff
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt

theorem fnField_top_of_adjoin_root : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω), fnField O y = ⊤ →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (Ω' : Type) [Field Ω']
      [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'] (ζ : O'),
      Algebra.adjoin Ω {algebraMap O' Ω' ζ} = ⊤ → fnField O' (fun v => algebraMap Ω Ω' (y v)) = ⊤ := by
  intro O _ _ _ Ω _ _ K J y hy O' _ _ _ _ Ω' _ _ _ _ _ _ ζ hζ
  set L := fnField O' (fun v => algebraMap Ω Ω' (y v)) with hL

  have himg : ∀ a : Ω, algebraMap Ω Ω' a ∈ L := by
    have hmap : (⊤ : Subfield Ω).map (algebraMap Ω Ω') ≤ L := by
      rw [← hy]
      unfold fnField
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro x (⟨a, rfl⟩ | ⟨q, rfl⟩)
      · show algebraMap Ω Ω' (algebraMap O Ω a) ∈ L
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O O' Ω']
        exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
      · show algebraMap Ω Ω' (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) ∈ L
        rw [map_div₀]
        exact Subfield.subset_closure (Or.inr ⟨q, rfl⟩)
    intro a
    exact hmap ⟨a, Subfield.mem_top a, rfl⟩
  have hζL : algebraMap O' Ω' ζ ∈ L := Subfield.subset_closure (Or.inl ⟨ζ, rfl⟩)
  let S : Subalgebra Ω Ω' :=
    { L.toSubring with algebraMap_mem' := himg }
  have hle : Algebra.adjoin Ω {algebraMap O' Ω' ζ} ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rw [Set.singleton_subset_iff]
    exact hζL
  rw [hζ] at hle
  rw [eq_top_iff]
  intro x _
  exact hle (Algebra.mem_top (x := x))

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt


open scoped ComplexOrder in
theorem gramDet_ne_zero_of_linearIndependent :
    ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (f : Fin n → B.carrier), LinearIndependent (𝓞 L) f → B.gramDet σ f ≠ 0 := by
  intro L _ _ B σ n f hf
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec B.metric σ (f i)) =
      Matrix.of fun i j ↦ (B.metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] f j) := by
    ext i j
    rfl
  have hp := (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hf)).det_pos
  rw [hG] at hp
  exact hp.ne'

end GlobalTheory.CompanionTheory.Ar.RootHt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt

theorem bound_of_local_bounds_of_blockScale :
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (T : Set ((Σ k, J k) → ℂ))
    (Bd : ((Σ k, J k) → ℂ) → ℝ → Prop),
    (∀ w ∈ T, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ w ∈ closure T, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → w ∈ T) →
    (∀ w x, Bd w x → w ∈ T) →
    (∀ w x (c : K → ℂ), (∀ k, c k ≠ 0) → Bd w x → Bd (fun p => c p.1 * w p) x) →
    (∀ w₀ ∈ T, ∃ N ∈ 𝓝 w₀, ∃ C : ℝ, ∀ w ∈ N, ∀ x, Bd w x → |x| ≤ C) →
    ∃ C : ℝ, ∀ w x, Bd w x → |x| ≤ C := by
  intro K _ J _ T Bd hT hcl hBdT hscale hloc
  classical
  obtain ⟨A, hA⟩ : ∃ A : Set ((Σ k, J k) → ℂ),
      A = (⋂ p, {w | ‖w p‖ ≤ 1}) ∩ ⋂ k, ⋃ i, {w | ‖w ⟨k, i⟩‖ = 1} := ⟨_, rfl⟩
  have hAcl : IsClosed A := by
    rw [hA]
    exact (isClosed_iInter fun p => isClosed_le (continuous_norm.comp (continuous_apply p))
      continuous_const).inter (isClosed_iInter fun k => isClosed_iUnion_of_finite fun i =>
        isClosed_eq (continuous_norm.comp (continuous_apply _)) continuous_const)
  have hA_le : ∀ w ∈ A, ∀ p, ‖w p‖ ≤ 1 := by
    intro w hw p
    rw [hA] at hw
    exact Set.mem_iInter.mp hw.1 p
  have hA_ne : ∀ w ∈ A, ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := by
    intro w hw k
    rw [hA] at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hw.2 k)
    refine ⟨i, fun h0 => ?_⟩
    have hi' : ‖w ⟨k, i⟩‖ = 1 := hi
    rw [h0, norm_zero] at hi'
    exact zero_ne_one hi'
  have hScl : IsClosed (T ∩ A) := by
    apply isClosed_of_closure_subset
    intro w hw
    have hwT : w ∈ closure T := closure_mono Set.inter_subset_left hw
    have hwA : w ∈ A := hAcl.closure_subset (closure_mono Set.inter_subset_right hw)
    exact ⟨hcl w hwT (hA_ne w hwA), hwA⟩
  have hSsub : T ∩ A ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact hA_le w hw.2
  have hScpt : IsCompact (T ∩ A) := (isCompact_closedBall 0 1).of_isClosed_subset hScl hSsub
  choose N hN C hC using fun w (hw : w ∈ T ∩ A) => hloc w hw.1
  obtain ⟨t, ht⟩ := hScpt.elim_nhds_subcover' N hN
  refine ⟨∑ s ∈ t, |C s.1 s.2|, ?_⟩
  intro w x hBd
  have hwT := hBdT w x hBd
  have hmax : ∀ k, ∃ i, ∀ j, ‖w ⟨k, j⟩‖ ≤ ‖w ⟨k, i⟩‖ := by
    intro k
    obtain ⟨i₀, -⟩ := hT w hwT k
    haveI : Nonempty (J k) := ⟨i₀⟩
    exact Finite.exists_max fun j => ‖w ⟨k, j⟩‖
  choose m hm using hmax
  have hmpos : ∀ k, 0 < ‖w ⟨k, m k⟩‖ := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hT w hwT k
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi₀) (hm k i₀)
  obtain ⟨c, hc⟩ : ∃ c : K → ℂ, c = fun k => ((‖w ⟨k, m k⟩‖⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    rw [hc]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (hmpos k).ne')
  have hBd' := hscale w x c hc0 hBd
  have hnorm : ∀ (k : K) (j : J k), ‖c k * w ⟨k, j⟩‖ = ‖w ⟨k, j⟩‖ / ‖w ⟨k, m k⟩‖ := by
    intro k j
    rw [hc, norm_mul, Complex.norm_real, norm_inv, norm_norm, div_eq_inv_mul]
  have hw'S : (fun p => c p.1 * w p) ∈ T ∩ A := by
    refine ⟨hBdT _ _ hBd', ?_⟩
    rw [hA]
    refine ⟨Set.mem_iInter.mpr fun p => ?_, Set.mem_iInter.mpr fun k => Set.mem_iUnion.mpr ⟨m k, ?_⟩⟩
    · obtain ⟨k, j⟩ := p
      show ‖c k * w ⟨k, j⟩‖ ≤ 1
      rw [hnorm]
      exact (div_le_one (hmpos k)).mpr (hm k j)
    · show ‖c k * w ⟨k, m k⟩‖ = 1
      rw [hnorm]
      exact div_self (hmpos k).ne'
  obtain ⟨s, hs, hsN⟩ := Set.mem_iUnion₂.mp (ht hw'S)
  calc |x| ≤ C s.1 s.2 := hC s.1 s.2 _ hsN x hBd'
    _ ≤ |C s.1 s.2| := le_abs_self _
    _ ≤ ∑ s ∈ t, |C s.1 s.2| :=
      Finset.single_le_sum (f := fun s : ↥(T ∩ A) => |C s.1 s.2|) (fun _ _ => abs_nonneg _) hs

end GlobalTheory.CompanionTheory.Ar.RootHt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem embedding_const_preconnected {F : Type} [Field F] [NumberField F] {m : ℕ} {B : Set (Fin m → ℂ)} (hpre : IsPreconnected B)
    (κ : (Fin m → ℂ) → (F →+* ℂ))
    (hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) B) {b b' : Fin m → ℂ} (hb : b ∈ B) (hb' : b' ∈ B) :
    κ b = κ b' := by
  have key : ∀ x : 𝓞 F, κ b (x : F) = κ b' (x : F) := by
    intro x
    have hT : IsDiscrete (Set.range fun s : F →+* ℂ => s (x : F)) :=
      (Set.finite_range _).isDiscrete
    have hmaps : Set.MapsTo (fun c => κ c (x : F)) B (Set.range fun s : F →+* ℂ => s (x : F)) :=
      fun c _ => ⟨κ c, rfl⟩
    exact hpre.constant_of_mapsTo hT (hd x).continuousOn hmaps hb hb'
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
  ext x
  exact key x

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.derivation_determines_chart : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardSmooth R A] (n g : ℕ) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), IsOpen B → (∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B) → ∀ b₀ ∈ B, ∀ (χ₀ : A →+* ℂ) (t : Fin g → A), χ₀.comp (algebraMap R A) = ψ b₀ → (∀ c, χ₀ (t c) = 0) →
  (∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0) →
  (∀ c, ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧ (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0) →
  ∃ (N : ℕ) (f : Fin N → A) (ε δ : ℝ) (Ψ : (Fin n → ℂ) → (Fin g → ℂ) → (A →+* ℂ)), 0 < ε ∧ 0 < δ ∧ ball b₀ ε ⊆ B ∧ Ψ b₀ 0 = χ₀ ∧
    (∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, (Ψ b z).comp (algebraMap R A) = ψ b ∧ (∀ c, Ψ b z (t c) = z c) ∧
      ∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = Ψ b z x * D y + Ψ b z y * D x) → (∀ c, D (t c) = 0) → D = 0) ∧
    (∀ a : A, DifferentiableOn ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψ bz.1 bz.2 a) (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε)) ∧
    (∀ c, ∃ j, f j = t c) ∧
    ∀ b ∈ ball b₀ δ, ∀ χ : A →+* ℂ, χ.comp (algebraMap R A) = ψ b → (∀ j, ‖χ (f j) - χ₀ (f j)‖ < δ) →
      (fun c => χ (t c)) ∈ ball (0 : Fin g → ℂ) ε ∧ χ = Ψ b (fun c => χ (t c)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.StdSmoothChart.exists_sections | exact GlobalTheory.CompanionTheory.Ar.StdSmoothChart.exists_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.StdSmoothChart.exists_sections <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem divSuppArith_holds : ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith

end GlobalTheory.CompanionTheory.Ar.Link
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_theta_basis_of_factor : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsAbelianScheme A → Out.RelAmple A L → (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)) → ∃ (N : ℕ) (J : Type) (Θ : J → (Fin g → ℂ) → ℂ), 0 < N ∧ (∀ i, Differentiable ℂ (Θ i)) ∧ (∀ i (l : u.Λ) z, Θ i (z + l) = (χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ N * Θ i z) ∧ (∃ i, Θ i ≠ 0) ∧ ∀ w : Fin g → ℂ, w ≠ 0 → ¬ ∀ i (t : ℂ) z, Θ i (z + t • w) = Θ i z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SecTheta.exists_theta_family | exact GlobalTheory.CompanionTheory.Ar.SecTheta.exists_theta_family | (intros; apply GlobalTheory.CompanionTheory.Ar.SecTheta.exists_theta_family <;> assumption)
end
