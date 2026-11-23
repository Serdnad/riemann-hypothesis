module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle119
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle125
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle126
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle124
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle098
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.FractionRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.Retie

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Transport

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {y : Y}
    (h : genPt (η ≫ f) ⤳ f y) : genPt η ⤳ y := by
  have h1 := h.map (inv f).continuous
  have e : ∀ z : Y, (inv f) (f z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  have e2 : genPt (η ≫ f) = f (genPt η) := Scheme.Hom.comp_apply _ _ _
  rw [e2, e, e] at h1
  exact h1

theorem exists_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (q : Cpt (η ≫ f)) :
    ∃ p : Cpt η, push η f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  exact ⟨⟨y, specializes_of_iso η f hq⟩, rfl⟩

theorem inChart_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] {κ : Type} (x : κ → Ω) (c : κ)
    (p : Cpt η) : InChart (η ≫ f) x c (push η f p) ↔ InChart η x c p := by
  unfold InChart
  rw [regAt_push]

theorem coordTie_comp_iso {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsIso f] (h : CoordTie o η x) :
    CoordTie o (η ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp η f]
    have hb : Function.Bijective (f.stalkMap (η (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push η f q
    exact genMap_push_injective η f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push η f q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push η f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨(inv f) ⁻¹ᵁ U, hU.preimage (inv f), fun q => ?_⟩
    obtain ⟨y, rfl⟩ : ∃ y, f y = q := ⟨(inv f) q, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    have e : (inv f) (f y) = y := by
      rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
    have e1 : f y ∈ (inv f) ⁻¹ᵁ U ↔ y ∈ U := by
      change (inv f) (f y) ∈ U ↔ _
      rw [e]
    rw [e1, hq y]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(push η f ⟨y, h1⟩).2, (inChart_push η f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨specializes_of_iso η f h1, (inChart_push η f x c ⟨y, specializes_of_iso η f h1⟩).1 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push η f q
      rw [regAt_push]
      exact H p ((inChart_push η f x c p).1 hq)
    · intro H p hp
      have := H (push η f p) ((inChart_push η f x c p).2 hp)
      rwa [regAt_push] at this

end Transport

theorem dominates_id_iff {X Y : Scheme.{0}} {Ω : Type} [Field Ω] {ξ' : Spec (CommRingCat.of Ω) ⟶ Y}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : Y ⟶ X} : Dominates ξ' ξ f (RingHom.id Ω) ↔ ξ' ≫ f = ξ := by
  unfold Dominates
  rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id, Category.id_comp]

theorem mem_ctrSet_self {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (p : Cpt M.ξ) : p ∈ ctrSet o x (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  exact ⟨c, hc.1, fun a ha => (GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).1 a ha⟩

theorem mem_ctrSet_join {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {κ' : Type} {w : κ' → Ω} (p : Cpt M.ξ) (hw : ∃ l, InChart M.ξ w l p) :
    p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  obtain ⟨l, hl⟩ := hw
  refine ⟨(c, l), mul_ne_zero hc.1 hl.1, fun a ha => ?_⟩
  change a ∈ regAt M.ξ p
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨j, m⟩, rfl⟩ := hy
    have e : joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
        (x j / x c) * (w m / w l) := by
      simp only [joinCo, RingHom.id_apply]
      rw [mul_div_mul_comm]
    beta_reduce
    rw [e]
    exact mul_mem (hc.2 j) (hl.2 m)
  | algebraMap r =>
    exact (GlobalTheory.T.regAt_chart_localization o Ω κ x M c p hc).1 _ (Subalgebra.algebraMap_mem _ r)
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

theorem coordTie_join_of_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω),
    (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  intro o _ Ω _ _ κ _ x M κ' _ w hw
  have hl : ∃ l, w l ≠ 0 := by
    obtain ⟨l, h⟩ := hw ⟨genPt M.ξ, specializes_rfl⟩
    exact ⟨l, h.1⟩
  obtain ⟨M', f, hf⟩ := GlobalTheory.T.exists_join_model_dominates o Ω κ x M Ω (RingHom.id Ω) κ' w (fun _ => rfl) hl
    (eq_top_iff.2 fun a _ => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_dominating_map o Ω (κ × κ') _ M' o Ω κ x M (RingHom.id Ω)
    (fun p => mem_ctrSet_join M p (hw p))
  rw [dominates_id_iff] at hf hg
  have u1 := GlobalTheory.T.existsUnique_dominating_map o Ω κ x M o Ω κ x M (RingHom.id Ω) (mem_ctrSet_self M)
  have u2 := GlobalTheory.T.existsUnique_dominating_map o Ω (κ × κ') _ M' o Ω (κ × κ') _ M' (RingHom.id Ω) (mem_ctrSet_self M')
  have e1 : g ≫ f = 𝟙 _ := u1.unique (dominates_id_iff.2 (by rw [← Category.assoc, hg, hf]))
    (dominates_id_iff.2 (Category.comp_id _))
  have e2 : f ≫ g = 𝟙 _ := u2.unique (dominates_id_iff.2 (by rw [← Category.assoc, hf, hg]))
    (dominates_id_iff.2 (Category.comp_id _))
  haveI : IsIso f := ⟨g, e2, e1⟩
  have := coordTie_comp_iso M'.ξ f M'.tie
  rwa [hf] at this

end GlobalTheory.CompanionTheory.Ar.Retie
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.log_periods_conjugate_exists : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L' : Flat.LogPeriods n a g Λ), ∃ L : Flat.LogPeriods n a g Λ, (∀ w x, L.P w x = star (L'.P (star w) x)) ∧ ∀ z, L.H z = (L'.H (star z)).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | exact GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LogPer.exists_conj_logPeriods <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.log_period_limit : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) ∧ Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) ∧ (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) ∧ (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) ∧ (∀ φ : W →+ ℤ, (∀ x : W, (∀ x' : W, L.E x x' = 0) → φ x = 0) → ∃ x₀ : W, ∀ x : W, φ x = L.E x₀ x) ∧ ∀ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian → (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.E x x') → (∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0) → ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ (v ⬝ᵥ Hb *ᵥ star v).re ≤ C * ∑ i, ‖v i‖ ^ 2 ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (∀ x' : W, L.E x x' = 0) ∧ p = per x}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | exact GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartTwist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

theorem prod_pow_toNat {K : Type} [Fintype K] {F : Type} [Field F] (u : K → F) (hu : ∀ k, u k ≠ 0) (a : K → ℤ) :
    ∏ k, u k ^ (a k).toNat = (∏ k, u k ^ a k) * ∏ k, u k ^ (-a k).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := hu k
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h]
  congr 1
  omega

theorem hasVal_twist : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L) (a : K → ℤ) (s : Ω) (w : L),
    Small.HasVal y (0 : K → ℤ) s z w → w ≠ 0 → ∀ c : (k : K) → J k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∃ v : L, v ≠ 0 ∧ Small.HasVal y a (s * ∏ k, y ⟨k, c k⟩ ^ a k) z v := by
  intro K _ J _ Ω _ y L _ z a s w h hw c hy hz
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hn, ev⟩ := h
  have hM : ∀ m : K → ℕ, aeval z (cMon c m) ≠ 0 := fun m => by
    rw [aeval_cMon]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  refine ⟨w * ∏ k, z ⟨k, c k⟩ ^ a k,
    mul_ne_zero hw (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hz k)),
    dg + fun k => (a k).toNat, dh + fun k => (-a k).toNat,
    g * cMon c fun k => (a k).toNat, f * cMon c fun k => (-a k).toNat,
    homog_mul hg (homog_cMon c _), homog_mul hf (homog_cMon c _), fun k => ?_, ?_,
    by rw [map_mul]; exact mul_ne_zero hn (hM _), ?_⟩
  · have h1 := hd k
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    push_cast
    omega
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, e,
      prod_pow_toNat (fun k => y ⟨k, c k⟩) hy a]
    ring
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, ev,
      prod_pow_toNat (fun k => z ⟨k, c k⟩) hz a]
    ring

end GlobalTheory.CompanionTheory.Ar.ChartTwist
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg


theorem _root_.GlobalTheory.T.group_scheme_integral_noetherian : ∀ (L : Type) [Field L] [NumberField L] (G : Over (Sp (𝓞 L))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsIntegral G.left ∧ ∀ W : G.left.Opens, IsAffineOpen W → IsNoetherianRing Γ(G.left, W) ∧ (sc G.hom W).FiniteType ∧ ∀ p : Ideal (𝓞 L), p.IsMaximal → ∀ a b : Γ(G.left, W), a * b ∈ p.map (sc G.hom W) → a ∈ p.map (sc G.hom W) ∨ b ∈ p.map (sc G.hom W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.semiAb_props | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.semiAb_props | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.semiAb_props <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

theorem _root_.GlobalTheory.T.derivation_hol_unif_tangent : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A] (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left) (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left → u.IsDiff c v' → ∀ (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)) (w : Fin g → ℂ), ⊤ ≤ ((u.ex w).left ≫ φ) ⁻¹ᵁ V → fderiv ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V f) w c = valAt' ((u.ex w).left ≫ φ) V (der v₀ hv₀ hV f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | exact GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | (intros; apply GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

theorem _root_.GlobalTheory.T.section_ratio_overlap : ∀ (R K : Type) [CommRing R] [Field K] (G : Over (Sp R)) [GrpObj G] (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (y : Sp K ⟶ G.left) (V₀ V₁ : G.left.Opens) (h₀ : IsAffineOpen V₀) (h₁ : IsAffineOpen V₁) (t₀ : ⊤ ≤ y ⁻¹ᵁ V₀) (t₁ : ⊤ ≤ y ⁻¹ᵁ V₁) (t : ⊤ ≤ y ⁻¹ᵁ (V₀ ⊓ V₁)) (r : ℕ) (f : Fin r → Γ(G.left, V₀)) (f' : Fin r → Γ(G.left, V₁)) (uu : Γ(G.left, V₀ ⊓ V₁)), ev y _ t uu ≠ 0 → (∀ j, (G.left.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op).hom (f j) = uu * (G.left.presheaf.map (homOfLE (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op).hom (f' j)) → ∀ (i : ℕ) (c : Fin r → R), (∀ k < i, ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[k] (f j)) = 0) → ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[i] (f j)) = ev y _ t uu * ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₁ t₁ ((der v₀ hv₀ h₁)^[i] (f' j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp.jet_cmp | exact GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp.jet_cmp | (intros; apply GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp.jet_cmp <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DenValue

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem dh_mem_adjoin (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (f : MRing ι) :
    TiePrimes.dh y c f ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩

theorem adjoin_le_subring (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (A : Subring Ω)
    (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩)) : x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hr j.1 j.2
  | algebraMap r =>
    rw [eq_intCast]
    exact intCast_mem A r
  | add x y _ _ hx hy => exact A.add_mem hx hy
  | mul x y _ _ hx hy => exact A.mul_mem hx hy

theorem hasVal_ratio (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (z ⟨k, i⟩ / z ⟨k, c k⟩) := by
  classical
  unfold Small.HasVal
  refine ⟨Pi.single k 1, Pi.single k 1, MvPolynomial.X ⟨k, i⟩, MvPolynomial.X ⟨k, c k⟩,
    TiePrimes.homog_X _, TiePrimes.homog_X _, fun k' => by simp, ?_, ?_, ?_⟩
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hyc k)]
  · rw [MvPolynomial.aeval_X]
    exact hzc k
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, div_mul_cancel₀ _ (hzc k)]

theorem hasVal_dh (y : (Σ k, ι k) → Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜)
    (c : (k : K) → ι k) (hzc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0) {h : MRing ι}
    {d : K → ℕ} (hh : IsMultiHomog h d) :
    Small.HasVal y 0 (TiePrimes.dh y c h) z (aeval z h / aeval z (TiePrimes.cMon c d)) := by
  have hc0 : aeval z (TiePrimes.cMon c d) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  unfold Small.HasVal
  refine ⟨d, d, h, TiePrimes.cMon c d, hh, TiePrimes.homog_cMon c d, fun k => by simp, ?_, hc0, ?_⟩
  · rw [TiePrimes.aeval_eq_dh_mul y c hyc hh, TiePrimes.aeval_eq_dh_mul y c hyc (TiePrimes.homog_cMon c d),
      TiePrimes.dh_cMon y c hyc, one_mul]
  · exact (div_mul_cancel₀ _ hc0).symm

private theorem hasVal_eq_of_hasVal_of_le {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}
    (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) {s : Ω} {w w' : 𝕜}
    (h1 : Small.HasVal y 0 s z w) (h2 : Small.HasVal y 0 s z w') : w = w' := by
  have hz' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ mCoordIdeal y, aeval z f = 0 := hz
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzw'⟩ := h2
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hdeq' : dg' = dh' := funext fun k => by
    have := hd' k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hm1 := TiePrimes.homog_mul hg hh'
  have hm2 := TiePrimes.homog_mul hg' hh
  rw [hdeq', ← hdeq, add_comm] at hm2
  have hneg := TiePrimes.homog_mul (TiePrimes.homog_C (K := K) (J := ι) (-1)) hm2
  rw [zero_add] at hneg
  have hF := TiePrimes.homog_add hm1 hneg
  have hFy : aeval y (g * h' + MvPolynomial.C (-1) * (g' * h)) = 0 := by
    simp only [map_add (f := _), map_mul, hy, hy', MvPolynomial.aeval_C, map_neg, map_one]
    ring
  have hFz := hz'.2 _ ((TiePrimes.mem_coord_iff y hF).2 hFy)
  simp only [map_add (f := _), map_mul, hzw, hzw', MvPolynomial.aeval_C, map_neg, map_one] at hFz
  have hprod : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination hFz
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact sub_eq_zero.1 h0
  · exact absurd h0 (mul_ne_zero hz0 hz0')

theorem value_and_denominator : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (A : Subring Ω) (ev : A →+* 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → (∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x)) → ∀ (c : (k : K) → ι k), (∀ k, z ⟨k, c k⟩ ≠ 0) → (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, ev ⟨_, hr k i⟩ = z ⟨k, i⟩ / z ⟨k, c k⟩) ∧ ∀ a : A, ∃ b : A, ev b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, ι k => y j / y ⟨j.1, c j.1⟩) := by
  intro K _ ι _ Ω _ y 𝕜 _ z A ev hz hval c hzc hyc hr
  refine ⟨fun k i => hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hr k i⟩) (hasVal_ratio y z c hzc hyc k i), ?_⟩
  intro a
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzw⟩ := hval a
  have hdeq : dg = dh := funext fun k => by
    have := hd k
    rw [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hbA : TiePrimes.dh y c h ∈ A := adjoin_le_subring y c A hr (dh_mem_adjoin y c h)
  have hc0 : aeval z (TiePrimes.cMon c dh) ≠ 0 := by
    simp only [TiePrimes.cMon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
  refine ⟨⟨_, hbA⟩, ?_, dh_mem_adjoin y c h, ?_⟩
  · rw [hasVal_eq_of_hasVal_of_le hz (hval ⟨_, hbA⟩) (hasVal_dh y z c hzc hyc hh)]
    exact div_ne_zero hz0 hc0
  · have hab : (a : Ω) * TiePrimes.dh y c h = TiePrimes.dh y c g := by
      have e1 := TiePrimes.aeval_eq_dh_mul y c hyc hg
      have e2 := TiePrimes.aeval_eq_dh_mul y c hyc hh
      rw [hdeq] at e1
      have hP : ∏ k, y ⟨k, c k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
      apply mul_right_cancel₀ hP
      rw [mul_assoc, ← e2, ← e1, hy]
    show (a : Ω) * TiePrimes.dh y c h ∈ _
    rw [hab]
    exact dh_mem_adjoin y c g

end GlobalTheory.CompanionTheory.Ar.DenValue
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.dual_lattice_base_change : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.dual_baseChange_fractionField | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.dual_baseChange_fractionField | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.dual_baseChange_fractionField <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

theorem _root_.GlobalTheory.T.abelianScheme_model_baseChange_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] (A₀ : Over (Sp k)) [GrpObj A₀] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap (algebraMap k V)) φ → ∀ R : Subalgebra k V, ∃ (_ : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R))))) (φ₁ : A.left ⟶ pullback A₀.hom (spMap (algebraMap k R))), IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R)) (pullback.fst _ _) ∧ IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) (spMap R.val.toRingHom) φ₁ ∧ φ₁ ≫ pullback.fst _ _ = φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra | exact GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.isReduced_moduli' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l), IsReduced Xo.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.moduli_isReduced | exact GlobalTheory.CompanionTheory.Ar.moduli_isReduced | (intros; apply GlobalTheory.CompanionTheory.Ar.moduli_isReduced <;> assumption)
end
