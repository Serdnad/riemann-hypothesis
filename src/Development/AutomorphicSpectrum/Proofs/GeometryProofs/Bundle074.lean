module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MorphismEqOfGenericPointEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle065
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle067
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
import Mathlib.SetTheory.ZFC.PSet
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.dominant_weight_gap_shift : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (nu : Wt Ψ N) (c₀ : ℝ), 1 ≤ j → j < N → 0 < c₀ → ∃ θ₀ > (0 : ℝ), θ₀ ≤ 1 ∧ ∀ (lam : Wt Ψ N) (θ : ℝ), ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (∀ τ, θ ≤ gap j lam τ) → CompactGapsGE j c₀ lam → Dominant (lam - θ ^ 2 • nu) ∧ ‖lam - θ ^ 2 • nu‖ ≤ 2 ∧ ∀ τ, θ / 2 ≤ gap j (lam - θ ^ 2 • nu) τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant | exact GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant | (intros; apply GlobalTheory.CompanionTheory.Ar.WtShift.sub_small_dominant <;> assumption)
end

section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.delta_term_log_degree_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | exact GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.generic_point_component_local_ring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ q : Cpt ξ, IsLocalRing (regAt ξ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar TopologicalSpace

theorem isOpen_of_isClosed_of_generizing {α : Type*} [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α]
    (S : Set α) (hc : IsClosed S) (hs : ∀ x y : α, x ⤳ y → y ∈ S → x ∈ S) : IsOpen S := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hT : IsClosed (⋃₀ {C ∈ irreducibleComponents α | Disjoint C S}) := by
    rw [Set.sUnion_eq_biUnion]
    exact (hfin.subset fun C (h : C ∈ {C ∈ irreducibleComponents α | Disjoint C S}) => h.1).isClosed_biUnion
      fun C h => isClosed_of_mem_irreducibleComponents C h.1
  have e : Sᶜ = ⋃₀ {C ∈ irreducibleComponents α | Disjoint C S} := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro s hsC hsS
      have hC := isIrreducible_irreducibleComponent (x := x)
      have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
      obtain ⟨c, hcg⟩ := QuasiSober.sober hC hcl
      have hcs : c ∈ S := hs c s (hcg.specializes hsC) hsS
      exact hx (hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hcs) (by
        rw [hcg.def]; exact mem_irreducibleComponent))
    · rintro ⟨C, ⟨-, hd⟩, hx⟩ hxS
      exact Set.disjoint_left.1 hd hx hxS
  rw [← isClosed_compl_iff, e]
  exact hT

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genPt_specializes_of_specializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p y : X}
    (hp : genPt ξ ⤳ p) (hy : y ⤳ p) : genPt ξ ⤳ y := by
  haveI := CptInh.dom ξ h ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := this
  obtain ⟨a, ha⟩ : genPt ξ ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  obtain ⟨b, hb⟩ : y ∈ Set.range (X.fromSpecStalk p) := by
    rwa [Scheme.range_fromSpecStalk]
  let o : Spec (CommRingCat.of (X.presheaf.stalk p)) :=
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p))
  have hoc : ∀ c : Spec (CommRingCat.of (X.presheaf.stalk p)), o ⤳ c := fun c =>
    (PrimeSpectrum.le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) c).1 bot_le
  have h1 : X.fromSpecStalk p o ⤳ genPt ξ := by
    rw [← ha]; exact (hoc a).map (X.fromSpecStalk p).continuous
  have h2 : X.fromSpecStalk p o ⤳ y := by
    rw [← hb]; exact (hoc b).map (X.fromSpecStalk p).continuous
  rwa [CptInh.nogen ξ h _ h1] at h2

theorem isOpen_closure_genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsOpen (closure {genPt ξ}) := by
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  obtain ⟨W, hpW⟩ : ∃ W : X.affineOpens, p ∈ W.1 := by
    obtain ⟨W, hW, hpW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    exact ⟨⟨W, hW⟩, hpW⟩
  haveI : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  haveI : NoetherianSpace (W.1 : X.Opens) := noetherianSpace_of_isAffineOpen W.1 W.2
  haveI : QuasiSober (W.1 : X.Opens) := inferInstanceAs (QuasiSober (W.1 : X.Opens).toScheme)
  have ho : IsOpen (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)) :=
    isOpen_of_isClosed_of_generizing _ (isClosed_closure.preimage continuous_subtype_val)
      fun x y hxy hy => by
        have hy' : genPt ξ ⤳ y.1 := specializes_iff_mem_closure.2 hy
        exact specializes_iff_mem_closure.1
          (genPt_specializes_of_specializes ξ h hy' (hxy.map continuous_subtype_val))
  refine ⟨Subtype.val '' (Subtype.val ⁻¹' (closure {genPt ξ}) : Set (W.1 : X.Opens)), ?_,
    W.1.isOpen.isOpenMap_subtype_val _ ho, ⟨⟨p, hpW⟩, hp, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hx

theorem cpt_open_integral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → ∃ U : X.Opens, (∀ q : X, q ∈ U ↔ genPt ξ ⤳ q) ∧
      IsClosed (U : Set X) ∧ IsIntegral U.toScheme := by
  intro X Ω _ ξ _ h
  let U : X.Opens := ⟨closure {genPt ξ}, isOpen_closure_genPt ξ h⟩
  have hU : ∀ q : X, q ∈ U ↔ genPt ξ ⤳ q := fun q => specializes_iff_mem_closure.symm
  refine ⟨U, hU, isClosed_closure, ?_⟩
  haveI : IrreducibleSpace U.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := genPt ξ)).closure
  haveI : ∀ x : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk x) := fun x => by
    haveI := CptInh.dom ξ h ⟨U.ι x, (hU _).1 x.2⟩
    have e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  haveI : IsReduced U.toScheme := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieMove

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {R : Type} [CommRing R] {x : Sp R ⟶ S'}

theorem fst_comp_alg : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Spec.map_id _

theorem epsMul_comp_alg (c : R) : Spec.map (CommRingCat.ofHom (epsMul c)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]

def pushEps (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : epsAt (x ≫ f) ⟶ G :=
  Over.homMk (p.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w p]
    exact Category.assoc _ _ _)

def liftEps (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : epsAt x ⟶ G' :=
  Over.homMk (h.1.lift v.left (epsAt x).hom ((Over.w v).trans (Category.assoc _ _ _).symm)) (h.1.lift_snd _ _ _)

theorem pushEps_left (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : (pushEps h p).left = p.left ≫ φ := rfl

theorem liftEps_left (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : (liftEps h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem push_lift (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : pushEps h (liftEps h v) = v :=
  Over.OverMorphism.ext (liftEps_left h v)

theorem pushEps_inj (h : IsGrpPullback G' G f φ) : Function.Injective (pushEps (x := x) h) := fun p q e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w p).trans (Over.w q).symm))

theorem pushEps_mul (h : IsGrpPullback G' G f φ) (p q : epsAt x ⟶ G') :
    pushEps h (p * q) = pushEps h p * pushEps h q := by
  let U : epsAt (x ≫ f) ⟶ Over.mk ((epsAt x).hom ≫ f) := Over.homMk (𝟙 _) (by simp)
  let V : Over.mk ((epsAt x).hom ≫ f) ⟶ epsAt (x ≫ f) := Over.homMk (𝟙 _) (by simp)
  have UV : U ≫ V = 𝟙 _ := Over.OverMorphism.ext (by simp [U, V])
  have e := h.2 (epsAt x) p q (V ≫ pushEps h p) (V ≫ pushEps h q) (by simp [V, pushEps_left])
    (by simp [V, pushEps_left])
  have e' : U ≫ ((V ≫ pushEps h p) * (V ≫ pushEps h q)) = pushEps h p * pushEps h q := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, UV, Category.id_comp, Category.id_comp]
  rw [← e']
  apply Over.OverMorphism.ext
  rw [pushEps_left, ← e]
  simp [U]

theorem one_left (h : IsGrpPullback G' G f φ) :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left :=
  congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))

theorem tan_iff (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') :
    IsTanAt G' x p ↔ IsTanAt G (x ≫ f) (pushEps h p) := by
  constructor
  · intro t
    show _ ≫ p.left ≫ φ = _
    rw [← Category.assoc, t, one_left h]
  · intro t
    refine h.1.hom_ext ?_ ?_
    · rw [Category.assoc, one_left h]
      exact t
    · have w := Over.w p
      have w₁ := Over.w (1 : Over.mk x ⟶ G')
      rw [Category.assoc, w, w₁]
      show _ ≫ Spec.map _ ≫ x = x
      rw [← Category.assoc, fst_comp_alg, Category.id_comp]

def pullModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G (x ≫ f) L) :
    LieModel G' x L where
  pt e := liftEps h (M.pt e)
  tan e := (tan_iff h _).2 (by rw [push_lift]; exact M.tan e)
  inj a b e := M.inj ((push_lift h _).symm.trans ((congrArg (pushEps h) e).trans (push_lift h _)))
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((tan_iff h v).1 t)
    exact ⟨e, pushEps_inj h (by rw [push_lift, he])⟩
  add a b := pushEps_inj h (by rw [pushEps_mul, push_lift, push_lift, push_lift, M.add])
  smul c e := by
    refine h.1.hom_ext ?_ ?_
    · rw [liftEps_left, Category.assoc, liftEps_left, M.smul]
    · have w := fun v => Over.w (liftEps (x := x) h v)
      rw [Category.assoc, w, w]
      show Spec.map _ ≫ x = _ ≫ Spec.map _ ≫ x
      rw [← Category.assoc, epsMul_comp_alg]

def pushModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G' x L) :
    LieModel G (x ≫ f) L where
  pt e := pushEps h (M.pt e)
  tan e := (tan_iff h _).1 (M.tan e)
  inj a b e := M.inj (pushEps_inj h e)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto (liftEps h v) ((tan_iff h _).2 (by rw [push_lift]; exact t))
    exact ⟨e, by rw [he, push_lift]⟩
  add a b := by rw [M.add, pushEps_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem models_correspond (h : IsGrpPullback G' G f φ) (L : Type) [AddCommGroup L] [Module R L] :
    (∀ M : LieModel G (x ≫ f) L, ∃ M' : LieModel G' x L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧
      ∀ M' : LieModel G' x L, ∃ M : LieModel G (x ≫ f) L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left :=
  ⟨fun M => ⟨pullModel h M, fun _ => liftEps_left h _⟩, fun M' => ⟨pushModel h M', fun _ => rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieMove

theorem GlobalTheory.CompanionTheory.Ar.LieMove.main : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G]
    (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L],
    IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
      ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  intro R _ X x G _ G₀ _ ψ L _ _ h
  have key : ∀ y : Sp R ⟶ X, 𝟙 _ ≫ x = y →
      (∀ M : LieModel G y L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
        ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G y L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
    rintro _ rfl
    exact GlobalTheory.CompanionTheory.Ar.LieMove.models_correspond h L
  exact key x (Category.id_comp x)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem maps_eq_of_eq_at_generic : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g :=
  @PositivityTheory.UnitarySelfGeneration.morphism_eq_of_generic_point_eq

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.coord_charts_match_regular : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (X W : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω), CoordTie o ξ t → CoordTie F ξ' t → (∀ p' : Cpt ξ', ∃ p : Cpt ξ, regAt ξ p = regAt ξ' p') ∧ ∀ p : Cpt ξ, (∀ d : o, d ≠ 0 → unitAt ξ p (algebraMap o Ω d)) → ∃ p' : Cpt ξ', regAt ξ p = regAt ξ' p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac | exact GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.FracPts.regAt_frac <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem seccomp : ∀ (B : Type) [CommRing B] (Z Z' : Scheme.{0}) (x : Spec (CommRingCat.of B) ⟶ Z') (φ : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) (s : Γ(Z, W)), secVal x (φ ⁻¹ᵁ W) h (φ.app W s) = secVal (x ≫ φ) W h' s := by
  intro B _ Z Z' x φ W h h' s
  unfold secVal
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem secring : ∀ (B B' : Type) [CommRing B] [CommRing B'] (ψ : B →+* B') (Z : Scheme.{0}) (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ W) (s : Γ(Z, W)), secVal (spMap ψ ≫ x) W h' s = ψ (secVal x W h s) := by
  intro B B' _ _ ψ Z x W h h' s
  unfold secVal
  have e : (spMap ψ ≫ x).appLE W ⊤ h' = x.appLE W ⊤ h ≫ (spMap ψ).appTop := by
    have e₁ : (spMap ψ).appTop = (spMap ψ).appLE ⊤ ⊤ le_top := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [e₁]
    exact (Scheme.Hom.appLE_comp_appLE (spMap ψ) x W ⊤ ⊤ h _).symm
  rw [e]
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have n' : (Scheme.ΓSpecIso (CommRingCat.of B')).hom.hom ((spMap ψ).appTop.hom ((x.appLE W ⊤ h).hom s)) =
      ψ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom s)) :=
    (ConcreteCategory.congr_hom n.symm ((x.appLE W ⊤ h).hom s)).symm
  exact n'

theorem eta : ∀ (X X' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  intro X X' G _ G' _ f φ h
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over X'))))
  have e₁ : (1 : 𝟙_ (Over X') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem tanin : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (q : X) (v : epsAt (X.fromSpecStalk q) ⟶ G), IsTanAt G _ v → ∀ W : G.left.Opens, (η[G]).left q ∈ W → ⊤ ≤ v.left ⁻¹ᵁ W := by
  intro X G _ q v hv W hq z _
  obtain ⟨p, rfl⟩ := LieCarrier.surjective_fst z
  have h1 : (1 : Over.mk (X.fromSpecStalk q) ⟶ G).left = X.fromSpecStalk q ≫ (η[G]).left := by
    rw [Hom.one_def]
    simp
  have e : v.left (Spec.map _ p) = (η[G]).left (X.fromSpecStalk q p) := congrArg (fun g => g p) (hv.trans h1)
  show v.left _ ∈ W
  refine e.symm ▸ ?_
  have h3 : X.fromSpecStalk q p ⤳ q := by
    have : X.fromSpecStalk q p ∈ Set.range (X.fromSpecStalk q) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (h3.map (η[G]).left.continuous).mem_open W.isOpen hq

theorem comp_ring {B B' : Type} [CommRing B] [CommRing B'] (ψ : B →+* B') {Z Z' : Scheme.{0}}
    (x' : Spec (CommRingCat.of B') ⟶ Z') (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z' ⟶ Z) (hx : x' ≫ φ = spMap ψ ≫ x)
    (W : Z.Opens) (h : ⊤ ≤ x' ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h0 : ⊤ ≤ x ⁻¹ᵁ W) (s : Γ(Z, W)) :
    secVal x' (φ ⁻¹ᵁ W) h (φ.app W s) = ψ (secVal x W h0 s) := by
  have key : ∀ (t : Spec (CommRingCat.of B') ⟶ Z) (_ : t = spMap ψ ≫ x) (h2 : ⊤ ≤ t ⁻¹ᵁ W),
      secVal t W h2 s = ψ (secVal x W h0 s) := by
    rintro _ rfl h2
    exact secring B B' ψ Z x W h0 h2 s
  rw [seccomp B' Z Z' x' φ W h h s]
  exact key _ hx h

theorem dualMap_snd {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : DualNumber R) :
    (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

end GlobalTheory.CompanionTheory.Ar.HtPull
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.full_torsion_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates | exact GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isComb_lieModel_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (n : ℕ) (b : Fin n → Em) (cf : Fin n → R) (e : Em),
    IsComb cf (fun i => M.pt (b i)) (M.pt e) ↔ e = ∑ i, cf i • b i := by
  intro S R _ G _ _ x Em _ _ M n b cf e
  have hu : ∀ u : Fin n → (epsAt x ⟶ G),
      (∀ i, (u i).left = spMap (epsMul (cf i)) ≫ (M.pt (b i)).left) ↔ u = fun i => M.pt (cf i • b i) := by
    intro u
    constructor
    · intro h
      funext i
      exact Over.OverMorphism.ext ((h i).trans (M.smul _ _).symm)
    · rintro rfl i
      exact M.smul _ _
  have h0 : M.pt 0 = 1 := by
    have h := M.add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsum : ∀ (m : ℕ) (f : Fin m → Em), M.pt (∑ i, f i) = (List.ofFn fun i => M.pt (f i)).prod := by
    intro m f
    induction m with
    | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, List.ofFn_zero, List.prod_nil, h0]
    | succ m ih => rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, M.add, ih]
  constructor
  · rintro ⟨u, hu1, hu2⟩
    rw [(hu u).1 hu1] at hu2
    apply M.inj
    rw [hu2]
    exact (hsum n (fun i => cf i • b i)).symm
  · intro he
    refine ⟨fun i => M.pt (cf i • b i), (hu _).2 rfl, ?_⟩
    rw [he]
    exact hsum n (fun i => cf i • b i)

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.chart_prime_existsUnique_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_prime_point | exact GlobalTheory.CompanionTheory.Ar.chart_prime_point | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_prime_point <;> assumption)
end
