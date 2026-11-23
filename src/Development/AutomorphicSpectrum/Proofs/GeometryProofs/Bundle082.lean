module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle077
import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle026
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle003
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullback
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.WeilBound.CoreStatements.AmpleLineBundles.KillsOverOfSquareZeroIdeal
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle075
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.LocalSubring
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle073
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle027
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_isOpen_common_generization {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] (p : Y) :
    ∃ V : Set Y, IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V, ∃ z : Y, z ⤳ p ∧ z ⤳ q := by
  have hF : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine ⟨⋂ Z ∈ {Z ∈ irreducibleComponents Y | p ∉ Z}, Zᶜ, ?_, ?_, ?_⟩
  · refine (hF.subset (Set.sep_subset _ _)).isOpen_biInter fun Z hZ => ?_
    exact (isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl
  · simp only [Set.mem_iInter]
    exact fun Z hZ => hZ.2
  · intro q hq
    have hmem := irreducibleComponent_mem_irreducibleComponents q
    have hpZ : p ∈ irreducibleComponent q := by
      by_contra hp
      exact (Set.mem_iInter₂.1 hq _ ⟨hmem, hp⟩) mem_irreducibleComponent
    obtain ⟨z, hz⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := q))
      isClosed_irreducibleComponent
    exact ⟨z, hz.specializes hpZ, hz.specializes mem_irreducibleComponent⟩

theorem genPt_specializes_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p z : X}
    (hp : genPt ξ ⤳ p) (hz : z ⤳ p) : genPt ξ ⤳ z := by
  apply GlobalTheory.CompanionTheory.Ar.Flat.genPt_specializes_of_specializes <;> assumption

theorem isClopen_setOf_genPt_specializes (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsClopen {q : X | genPt ξ ⤳ q} := by
  refine ⟨?_, ?_⟩
  · have : {q : X | genPt ξ ⤳ q} = closure {genPt ξ} := by
      ext q; exact specializes_iff_mem_closure
    rw [this]; exact isClosed_closure
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨V, hV, hpV, hVq⟩ := @exists_isOpen_common_generization U _
      (noetherianSpace_of_isAffineOpen U hU) U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
      ⟨p, hpU⟩
    have hopen : IsOpen (Subtype.val '' V : Set X) := U.isOpen.isOpenMap_subtype_val V hV
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨_, hpV, rfl⟩) ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, hzp, hzq⟩ := hVq q hq
    exact (genPt_specializes_of_specializes ξ h (p := p) hp
      (hzp.map continuous_subtype_val)).trans (hzq.map continuous_subtype_val)

end GlobalTheory.CompanionTheory.Ar
end

section

open ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.ChartVal

theorem isIntegral_of_forall_valuationSubring {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  apply GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_of_forall_valuationSubring' <;> assumption

theorem mem_chartLatNm_of_forall_valuationSubring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q : ℕ) (x : Ω),
    (∀ (c : (k : K) → ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω,
      (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) → x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q ∈ W) →
    x * u ^ q ∈ chartLatNm y a q := by
  intro K _ ι _ Ω _ y a u q x H c hc
  have e : x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) =
      x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q := by
    rw [mul_pow, ← Finset.prod_pow, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  show x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω
  rw [e, mem_integralClosure_iff]
  refine isIntegral_of_forall_valuationSubring Subtype.val_injective _ fun V hV => H c hc V fun p => ?_
  exact hV ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.ChartVal
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj
namespace GenericFibreProof

theorem spMap_field_pt {R K : Type} [CommRing R] [Field K] (δ : R →+* K) (z : Sp K) :
    (spMap δ z).asIdeal = RingHom.ker δ := by
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := z.2)
  show Ideal.comap δ z.asIdeal = _
  rw [hz]; rfl

theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  letI := β.toAlgebra
  haveI := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

theorem generic_max {X : Type} [TopologicalSpace X] [T0Space X] {v v' : X} (h : v ∈ genericPoints X)
    (hs : v' ⤳ v) : v' = v := by
  have h1 : closure {v} ⊆ closure {v'} := specializes_iff_closure_subset.1 hs
  have h2 : closure {v'} ⊆ closure {v} := h.2 isIrreducible_singleton.closure h1
  exact (hs.antisymm (specializes_iff_closure_subset.2 h2)).eq

theorem mem_of_dense_of_max {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (ho : IsOpen U) (hd : Dense U) {z : X} (hz : ∀ z', z' ⤳ z → z' = z) : z ∈ U := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨o, hoo, ⟨u, hu⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨w, hwo, hwU⟩ := hd.inter_open_nonempty o hoo ⟨u, hu⟩
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hC).closure_eq] at hg
  have hgz : hC.1.genericPoint = z := hz _ (hg.specializes mem_irreducibleComponent)
  have hzw : z ⤳ w := hgz ▸ hg.specializes (hoC hwo)
  exact hzw.mem_open ho hwU

private theorem isLocallyNoetherian_of_closedImmersion_pSpace (O F : Type) [CommRing O] [Field F] (β : O →+* F) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (hp : IsProjOver s) : TopologicalSpace.NoetherianSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := by
  obtain ⟨N, i, hi, hs⟩ := hp
  haveI := hi
  haveI : Algebra.FiniteType ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
      (MvPolynomial (Fin (N + 1)) O) :=
    haveI : IsScalarTower O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
        (MvPolynomial (Fin (N + 1)) O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have hsurj : Function.Surjective
      (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)) := by
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p)).mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0).symm
  haveI : LocallyOfFiniteType (spMap (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ hsurj
  haveI : LocallyOfFiniteType (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : QuasiCompact (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : LocallyOfFiniteType s := by
    rw [← hs]
    infer_instance
  haveI : QuasiCompact s := by
    rw [← hs]
    infer_instance
  haveI : IsLocallyNoetherian (pullback s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))
  haveI : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))
  haveI : IsNoetherian (pullback s (spMap β)) := {}
  infer_instance

theorem generic_points_range_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  apply PositivityTheory.HtPt.Ml.generic_points_range <;> assumption

end GenericFibreProof


theorem _root_.GlobalTheory.T.generic_points_in_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  exact @GenericFibreProof.generic_points_range_local
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btOrder_eq_of_open_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A :=
  @PositivityTheory.HtPt.Mh.char

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_isHopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) :=
  @PositivityTheory.HtPt.Htat.bt_sub_hopf
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ConstClosure

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

theorem exists_chart_div (h : CoordTie ℤ ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b := by
  let η : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover η
  refine ⟨c, hc.1, fun ω => ?_⟩
  obtain ⟨U, hU, hmem⟩ := h.affine c hc.1
  have hη : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(X, U), (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (h.ring c hc.1 _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
    exact ⟨X.presheaf.germ U p.1 hpU r, genMap_germ_eq_stalk_closed ξ p U hpU hη r⟩
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = ω := h.gen.bij.2 ω
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨_, _, key r, key t, hne, ?_⟩
  rw [eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

theorem adjoin_le_subfield (F : Subfield Ω) {c : κ} (h : ∀ j, x j / x c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h j
  | algebraMap n => simpa using intCast_mem F n
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem subfield_eq_top {c : κ} (hc : ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b)
    (F : Subfield Ω) (h : ∀ j, x j / x c ∈ F) : F = ⊤ := by
  refine eq_top_iff.2 fun ω _ => ?_
  obtain ⟨a, b, ha, hb, -, rfl⟩ := hc ω
  exact div_mem (adjoin_le_subfield F h ha) (adjoin_le_subfield F h hb)

end Chart

section Field

variable {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {n : ℕ} (h : IsArithVar (mCoordIdeal y) n) : CharZero Ω := by
  obtain ⟨-, -, hH, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing J) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have e : mConeMap y (C (n : ℤ)) = C (n : Ω) := by
      simp [mConeMap, aeval_C]
    rw [e, hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing J) = ⊥ from hH] at hmem
  simpa using hmem

theorem dedekind_finite_of_finite [CharZero Ω] (hf : FiniteDimensional ℚ (algebraicClosure ℚ Ω))
    (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] :
    IsDedekindDomain A ∧ Module.Finite ℤ A := by
  let L := algebraicClosure ℚ Ω
  have hmem : ∀ a : A, algebraMap A Ω a ∈ L := fun a =>
    mem_algebraicClosure_iff'.2 ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩).tower_top
  letI : Algebra A L := ((algebraMap A Ω).codRestrict L.toSubalgebra.toSubring hmem).toAlgebra
  have hcoe : ∀ a : A, ((algebraMap A L a : L) : Ω) = algebraMap A Ω a := fun _ => rfl
  haveI : IsScalarTower ℤ A L := inferInstance
  haveI : NumberField L := ⟨⟩
  haveI : IsIntegralClosure A ℤ L := by
    refine ⟨fun a b hab => IsIntegralClosure.algebraMap_injective A ℤ Ω ?_, fun {v} => ?_⟩
    · rw [← hcoe, ← hcoe, hab]
    · rw [← isIntegral_algebraMap_iff (A := L) (B := Ω) (R := ℤ) ]
      rw [IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := Ω)]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
  haveI : IsDomain A := (IsIntegralClosure.algebraMap_injective A ℤ Ω).isDomain _
  exact ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ L A, IsIntegralClosure.finite ℤ ℚ L A⟩

end Field

section Local

variable {Ω : Type} [Field Ω]

theorem isIntegrallyClosedIn_of_atPrime (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] : IsIntegrallyClosedIn O Ω := by
  have hA := IsIntegralClosure.algebraMap_injective A ℤ Ω
  have hs : ∀ s : m.primeCompl, algebraMap A Ω s ≠ 0 := fun s h0 =>
    s.2 (by rw [hA (h0.trans (map_zero _).symm)]; exact m.zero_mem)
  refine isIntegrallyClosedIn_iff.2 ⟨?_, fun {w} hw => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun o ho => ?_
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj m.primeCompl o
    have e' := congrArg (algebraMap O Ω) e
    simp only [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at e'
    have ha : a = 0 := hA (e'.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units O s).mul_left_eq_zero.1 e
  · obtain ⟨s, hsw⟩ := IsIntegral.exists_multiple_integral_of_isLocalization m.primeCompl w hw
    haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ Ω
    have hz : IsIntegral ℤ (s • w) := isIntegral_trans _ hsw
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).1 hz
    refine ⟨IsLocalization.mk' O a s, ?_⟩
    have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω s = algebraMap A Ω a := by
      rw [IsScalarTower.algebraMap_apply A O Ω s, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap A Ω a = algebraMap A Ω s * w := by
      rw [ha, Submonoid.smul_def, Algebra.smul_def]
    exact mul_right_cancel₀ (hs s) (by rw [h1, h2, mul_comm])

end Local

theorem const_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω], IsDedekindDomain A ∧ Module.Finite ℤ A ∧ Function.Injective (algebraMap A Ω) ∧ HasConstants ℤ A y ∧ ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], IsIntegrallyClosedIn O Ω ∧ fnField O y = ⊤ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV A _ _ _
  classical
  haveI : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨c₀, -, hdiv⟩ := exists_chart_div 𝔐.tie
  have hfin : FiniteDimensional ℚ (algebraicClosure ℚ Ω) := by
    refine GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof ℚ Ω
      (Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩) ?_
    have htop := subfield_eq_top hdiv (IntermediateField.adjoin ℚ
      ((Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩ : Finset Ω) : Set Ω)).toSubfield
      fun j => IntermediateField.subset_adjoin _ _ (by simp)
    refine eq_top_iff.2 fun ω _ => ?_
    have hω : ω ∈ (⊤ : Subfield Ω) := Subfield.mem_top ω
    rw [← htop] at hω
    exact hω
  have hconst : HasConstants ℤ A y := fun c' hc' a =>
    (𝔐.tie.ring c' hc' _).2 fun p _ =>
      IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ 𝔐.tie.gen (𝔐.normal p.1).2 _
        ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)
  obtain ⟨hd, hfA⟩ := dedekind_finite_of_finite hfin A
  refine ⟨hd, hfA, IsIntegralClosure.algebraMap_injective A ℤ Ω, hconst, ?_⟩
  intro m _ O _ _ _ _ _ _ _
  refine ⟨isIntegrallyClosedIn_of_atPrime A m O, subfield_eq_top hdiv _ fun j => ?_⟩
  show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c₀ k⟩) ∈ fnField O y
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, j k, c₀ k⟩, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Num.ConstClosure
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.exists_isBaseChange_of_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F :=
  @PositivityTheory.UnitarySelfGeneration.bt_exists_bc

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.torsion_along_group_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (x' : Sp R ⟶ S') (y : Sp R ⟶ S) (N : ℕ) (i₁ : Γ.G.left ⟶ G.left), IsGrpPullback G' G f φ → x' ≫ f = y → Γ.IsTorsionAlong G y N i₁ → ∃ i' : Γ.G.left ⟶ G'.left, i' ≫ φ = i₁ ∧ Γ.IsTorsionAlong G' x' N i' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong | exact GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong | (intros; apply GlobalTheory.CompanionTheory.Ar.TorPull.exists_lift_isTorsionAlong <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem killsOver_of_sq_zero : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (I : Ideal B), I ^ 2 = ⊥ → KillsOver u Y (spMap (Ideal.Quotient.mk I) ≫ b) → KillsOver u Y b :=
  @CoverDenseAlt.kills_over_of_square_zero_ideal

end GlobalTheory.CompanionTheory.Ar
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.subring_coords_complex_value : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (W : Subring Ω') (φ : W →+* ℂ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (k : K) (c e : J k), w ⟨k, c⟩ ≠ 0 → ∃ h : i (y ⟨k, e⟩ / y ⟨k, c⟩) ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) → ∀ (a : Ω) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing | exact GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing | (intros; apply GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.segre_chart_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (W : ChartBundle ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) r E) (L : Lat ξ E), CoordTie ℤ ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) W.lat → ∀ (c : (k : K) → J k) (f : Ω) (b : Fin r → E), GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y c ≠ 0 → f ∈ chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c → f ≠ 0 → (GroundTheory.Heights₂.Heights.LowerBoundFree.IsFrameOver y W c f b ↔ ∀ p : Cpt ξ, InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p → unitAt ξ p f → L.IsFrameAt b p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | exact GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | (intros; apply GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt <;> assumption)
end
