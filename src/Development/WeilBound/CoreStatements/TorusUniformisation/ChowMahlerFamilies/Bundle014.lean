module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle014
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle011
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_exists
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)
open PositivityTheory.Xgn.A_pull_line (comb mseg_join map_mem)
open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC (smul_mem_spanOver mem_spanOver_of_mem locFree_baseChange)

theorem pow_mul_mem {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K]
    {ι : K → Type} (x : (Σ k, ι k) → Ω) (s t : ∀ k, ι k) (hs : mseg x s ≠ 0) (a : Ω)
    (ha : a ∈ chartRing O (mseg x) s) :
    ∃ n : ℕ, (mseg x s / mseg x t) ^ n * a ∈ chartRing O (mseg x) t := by
  have hq := div_mem_chartRing (o := O) (mseg x) t s
  unfold chartRing at ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have h : (mseg x s / mseg x t) ^ 1 * (mseg x u / mseg x s) = mseg x u / mseg x t := by
      rw [pow_one, mul_comm, div_mul_div_cancel₀ hs]
    have h2 := div_mem_chartRing (o := O) (mseg x) t u
    rw [← h] at h2
    exact h2
  | algebraMap r => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : (mseg x s / mseg x t) ^ (m + n) * (a + b) =
        (mseg x s / mseg x t) ^ n * ((mseg x s / mseg x t) ^ m * a) +
        (mseg x s / mseg x t) ^ m * ((mseg x s / mseg x t) ^ n * b) := by ring
    rw [h]
    exact add_mem (mul_mem (pow_mem hq n) hm) (mul_mem (pow_mem hq m) hn)
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : (mseg x s / mseg x t) ^ (m + n) * (a * b) =
        ((mseg x s / mseg x t) ^ m * a) * ((mseg x s / mseg x t) ^ n * b) := by ring
    rw [h]
    exact mul_mem hm hn

theorem closure_eq {O Ω₁ V V₁ : Type} [CommRing O] [Field Ω₁] [Algebra O Ω₁] [AddCommGroup V₁]
    [Module Ω₁ V₁] (R : Subalgebra O Ω₁) (f : V → V₁) (L : Set V) :
    spanOver R (f '' L) = AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L, v = a • f e} := by
  unfold spanOver
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, e, he, rfl⟩
  · rintro ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩

theorem main (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type)
    [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V)
    (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type)
    [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁)
    (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]
    (bc : V →ₗ[Ω] V₁) (hbc : IsBaseChange Ω₁ bc) :
    ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, ∀ s, mseg (bcCoord x z) s ≠ 0 →
      EB.lat s = AddSubgroup.closure
        {v | ∃ a ∈ chartRing O (mseg (bcCoord x z)) s, ∃ e ∈ E.lat (restrictChart s), v = a • bc e} := by
  let φ : Ω →ₐ[O] Ω₁ := IsScalarTower.toAlgHom O Ω Ω₁
  obtain ⟨hfam, hloc⟩ := (PositivityTheory.Xgn.t_bundle_of_family O Ω K ι x N V).2 E
  have hj : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (bcCoord x z) s =
      algebraMap Ω Ω₁ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) :=
    fun s => mseg_join φ x z s
  have hne : ∀ s : ∀ k : K ⊕ K', Sum.elim ι ι' k, mseg (bcCoord x z) s ≠ 0 →
      mseg x (restrictChart s) ≠ 0 := by
    intro s hs h
    rw [hj, h, map_zero, zero_mul] at hs
    exact hs rfl
  suffices hov : IsLatFamily O (bcCoord x z) (fun s =>
      spanOver (chartRing O (mseg (bcCoord x z)) s) (bc '' (E.lat (restrictChart s) : Set V))) by
    obtain ⟨EB, hEB⟩ :=
      (PositivityTheory.Xgn.t_bundle_of_family O Ω₁ (K ⊕ K') (Sum.elim ι ι') (bcCoord x z) N V₁).1 _ hov
        (fun s hs => locFree_baseChange _ _ (fun a ha => map_mem φ x z s hs a ha) bc hbc N _
          (hloc _ (hne s hs)))
    exact ⟨EB, fun s hs => (hEB s hs).trans (closure_eq _ _ _)⟩
  refine ⟨fun s _ a ha v hv => smul_mem_spanOver _ _ ha hv, ?_⟩
  intro s t hs ht v hv
  beta_reduce at hv ⊢
  have hq := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t s
  set q := mseg (bcCoord x z) s / mseg (bcCoord x z) t with hqdef
  rw [spanOver] at hv
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩ := hy
    obtain ⟨n, hn⟩ := pow_mul_mem (bcCoord x z) s t hs a ha
    obtain ⟨m, hm⟩ := hfam.2 _ _ (hne s hs) (hne t ht) e he
    have hw := div_mem_chartRing (o := O) (mseg (bcCoord x z)) t (comb (restrictChart t) s)
    set w := mseg (bcCoord x z) (comb (restrictChart t) s) / mseg (bcCoord x z) t with hwdef
    have ht' : algebraMap Ω Ω₁ (mseg x (restrictChart t)) ≠ 0 := (map_ne_zero _).mpr (hne t ht)
    have hqw : q = w * algebraMap Ω Ω₁ (mseg x (restrictChart s) / mseg x (restrictChart t)) := by
      have h1 : mseg (bcCoord x z) (comb (restrictChart t) s) =
          algebraMap Ω Ω₁ (mseg x (restrictChart t)) * mseg z (fun k => s (.inr k)) := hj _
      rw [hqdef, hwdef, h1, hj s, map_div₀]
      field_simp
    refine ⟨n + m, ?_⟩
    have h : q ^ (n + m) • a • bc e = (q ^ n * a * w ^ m) •
        bc ((mseg x (restrictChart s) / mseg x (restrictChart t)) ^ m • e) := by
      rw [map_smul, ← algebraMap_smul Ω₁ (_ ^ m : Ω), smul_smul, smul_smul, map_pow, pow_add,
        mul_assoc (q ^ n * a), ← mul_pow, ← hqw]
      congr 1
      ring
    rw [h]
    exact smul_mem_spanOver _ _ (mul_mem hn (pow_mem hw m)) (mem_spanOver_of_mem _ ⟨_, hm, rfl⟩)
  | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have h : q ^ (m + n) • (a + b) = q ^ n • q ^ m • a + q ^ m • q ^ n • b := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n m]
    rw [h]
    exact add_mem (smul_mem_spanOver _ _ (pow_mem hq n) hm) (smul_mem_spanOver _ _ (pow_mem hq m) hn)
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

end PositivityTheory.Xgn.A_pull_exists

theorem PositivityTheory.Xgn.t_pull_exists : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V), (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), ∃ EB : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB) ∧ ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁) (V₁ : Type) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁] (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc → ∃ EB : ChartBundle O (mseg (bcCoord x z)) N V₁, IsPullBC O x z bc E EB := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E
  refine ⟨fun K' _ _ ι' _ z => ?_, fun Ω₁ _ _ _ _ K' _ _ ι' _ z V₁ _ _ _ _ bc hbc =>
    PositivityTheory.Xgn.A_pull_exists.main O Ω K ι x N V E Ω₁ K' ι' z V₁ bc hbc⟩
  exact PositivityTheory.Xgn.A_pull_exists.main O Ω K ι x N V E Ω K' ι' z V (LinearEquiv.refl Ω V).toLinearMap
    (IsBaseChange.ofEquiv _)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticePushdown

theorem exists_lift {X X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (f : X' ⟶ X) [IsProper f] (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra V Ω']
    [IsFractionRing V Ω'] (z : Spec (CommRingCat.of V) ⟶ X)
    (w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ z) :
    ∃ p' : Cpt ξ', f p'.1 = z (IsLocalRing.closedPoint V) ∧
      ∀ a ∈ regAt ξ' p', ∃ v : V, algebraMap V Ω' v = a := by
  have hex : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Spec (CommRingCat.of V) ⟶ X',
      Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ l = ξ' ∧ l ≫ f = z := by
    obtain ⟨l, hl₁, hl₂⟩ := (hex { R := V, K := Ω', commSq := ⟨w⟩, .. }).exists_lift
    exact ⟨l, hl₁, hl₂⟩
  have hsp : genPt ξ' ⤳ l (IsLocalRing.closedPoint V) := by
    unfold genPt
    rw [← hl₁]
    exact (IsLocalRing.specializes_closedPoint _).map l.continuous
  have key : X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ' =
      Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω') := by
    apply Spec.map_injective
    rw [← cancel_mono (X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))]
    have h1 : Spec.map (X'.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ') ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      refine Eq.trans (congrArg (· ≫ X'.fromSpecStalk (l (IsLocalRing.closedPoint V)))
        (Spec.map_comp (X'.presheaf.stalkSpecializes hsp) (Scheme.stalkClosedPointTo ξ'))) ?_
      refine Eq.trans (Category.assoc _ _ _) ?_
      refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ') ≫ ·)
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)) ?_
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
    have h2 : Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V Ω')) ≫
        X'.fromSpecStalk (l (IsLocalRing.closedPoint V)) = ξ' := by
      rw [Spec.map_comp, Category.assoc]
      refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom (algebraMap V Ω')) ≫ ·)
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk l)) hl₁
    exact h1.trans h2.symm
  refine ⟨⟨_, hsp⟩, ?_, ?_⟩
  · rw [← hl₂]
    exact (Scheme.Hom.comp_apply l f _).symm
  · rintro _ ⟨g, rfl⟩
    exact ⟨(Scheme.stalkClosedPointTo l).hom g, (congrArg (fun t => t.hom g) key).symm⟩

theorem spec_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) :
    Spec.map (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk q.1 = ξ := by
  refine Eq.trans (congrArg (· ≫ X.fromSpecStalk q.1)
    (Spec.map_comp (X.presheaf.stalkSpecializes q.2) (Scheme.stalkClosedPointTo ξ))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·)
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2)) ?_
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem exists_over {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    [IsLocallyNoetherian X] {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {f : X' ⟶ X} {i : Ω →+* Ω'} [IsProper f] (hD : Dominates ξ' ξ f i) (hi : Function.Bijective i)
    (hg : IsCptGen ξ) (hn : NormalCpt ξ) (q : Cpt ξ) (hd : ringKrullDim (X.presheaf.stalk q.1) = 1) :
    ∃ p' : Cpt ξ', f p'.1 = q.1 ∧ ∀ a : Ω, i a ∈ regAt ξ' p' → a ∈ regAt ξ q := by
  obtain ⟨hfr, -, -⟩ := RegAtRing.regAt_ring X Ω ξ hg q
  have : IsFractionRing (regAt ξ q) Ω := hfr
  have : IsIntegrallyClosed (regAt ξ q) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn q x hx⟩, rfl⟩
  have hdom : IsDomain (X.presheaf.stalk q.1) := (hg.inj q).isDomain (genMap ξ q)
  have : IsIntegrallyClosed (X.presheaf.stalk q.1) :=
    IsIntegrallyClosed.of_equiv (RegAtRing.stalkEquiv hg q).symm
  have : IsDiscreteValuationRing (X.presheaf.stalk q.1) := normal_noeth_local_dim_one_isDVR _ hd
  let _ : Algebra (X.presheaf.stalk q.1) Ω' := (i.comp (genMap ξ q)).toAlgebra
  have : FaithfulSMul (X.presheaf.stalk q.1) Ω' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hi.1.comp (hg.inj q))
  have hfr' : IsFractionRing (X.presheaf.stalk q.1) Ω' := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨y, rfl⟩ := hi.2 z
    obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, rfl⟩ := RegAtRing.exists_div hg q y
    exact ⟨a, b, map_div₀ i _ _⟩
  have w : ξ' ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω')) ≫
      X.fromSpecStalk q.1 := by
    have e : CommRingCat.ofHom (algebraMap (X.presheaf.stalk q.1) Ω') =
        (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ CommRingCat.ofHom i := rfl
    refine hD.trans ?_
    refine Eq.trans (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (spec_genMap ξ q).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (· ≫ X.fromSpecStalk q.1) (Spec.map_comp _ _).symm
  have hv : ValuationRing (X.presheaf.stalk q.1) := inferInstance
  obtain ⟨p', h1, h2⟩ := @exists_lift X X' Ω' _ ξ' f _ (X.presheaf.stalk q.1) _ hdom hv _ hfr'
    (X.fromSpecStalk q.1) w
  refine ⟨p', h1.trans Scheme.fromSpecStalk_closedPoint, fun a ha => ?_⟩
  obtain ⟨v, hv⟩ := h2 _ ha
  exact ⟨v, hi.1 hv⟩

end PositivityTheory.Xgn.LineLatticePushdown

theorem PositivityTheory.Xgn.line_lattice_proper_pushdown : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') [IsProper f], Dominates ξ' ξ f i → Function.Bijective i → IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → (∀ p' : Cpt ξ', f p'.1 ⤳ p.1 → (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' (i t)) → L.IsGenAt p t := by
  intro X Ω _ ξ _ X' Ω' _ ξ' f i _ hD hi hg hn L T p t hL hT hp
  have ht : t ≠ 0 := by
    have h0 := (hp ⟨genPt ξ', specializes_rfl⟩ (by
      show f (genPt ξ') ⤳ p.1
      rw [hD.map_genPt]; exact p.2)).1
    rintro rfl
    exact h0 (map_zero i)
  refine PositivityTheory.Xgn.line_lattice_generator_codim_one X Ω ξ hg hn L T p t hL hT ht fun q hqp hd => ?_
  obtain ⟨p', hq, hreg⟩ := PositivityTheory.Xgn.LineLatticePushdown.exists_over hD hi hg hn q hd
  obtain ⟨q, hq0⟩ := q
  obtain rfl : f p'.1 = q := hq
  obtain ⟨U, hU, b, -, h⟩ := hL _ (hT _ hqp)
  obtain ⟨h1, h2⟩ := h _ (hT _ hqp) hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  rw [hr] at h2
  have he : b 0 ≠ 0 := h1.ne_zero 0
  obtain ⟨_, -, hpull⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  have g1 := hpull L (b 0) ⟨he, h2⟩
  have g2 := hp p' hqp
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq g2.1 (g2.2.symm.trans g1.2)
  have hu' : u = i (t / b 0) := by
    rw [map_div₀, e, smul_eq_mul, mul_div_cancel_right₀ _ g1.1]
  subst hu'
  have hu2 : unitAt ξ ⟨f p'.1, hq0⟩ (t / b 0) :=
    ⟨div_ne_zero ht he, hreg _ hu.2.1, hreg _ (by rw [map_inv₀]; exact hu.2.2)⟩
  refine ⟨ht, h2.trans (span_singleton_eq_of_unitAt hu2 ?_).symm⟩
  rw [smul_eq_mul, div_mul_cancel₀ _ he]
end
