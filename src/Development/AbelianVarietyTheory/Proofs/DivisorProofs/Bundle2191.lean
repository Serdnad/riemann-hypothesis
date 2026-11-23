module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosed
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle003
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfForall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionUnramified_of_hasGoodReduction_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], HasGoodReduction R K A → ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := by
  first | exact @GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction | exact GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction | (intros; apply GlobalTheory.Published.AbVarRed.torsionUnramified_of_hasGoodReduction <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.galois_transitive_on_valuation_rings : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω] [FiniteDimensional K Ω] (V V' : ValuationSubring Ω), IsAbove R K V.toSubring → IsAbove R K V'.toSubring → ∃ g : Ω ≃ₐ[K] Ω, g • V = V' := by
  first | exact @GlobalTheory.ProlongConj.exists_smul_eq_of_isAbove | exact GlobalTheory.ProlongConj.exists_smul_eq_of_isAbove | (intros; apply GlobalTheory.ProlongConj.exists_smul_eq_of_isAbove <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isDiscreteValuationRing_of_isAbove_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] (V : ValuationSubring L), IsAbove R K V.toSubring → IsDiscreteValuationRing V := by
  first | exact @GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove | exact GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove | (intros; apply GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaRestrict

variable {Ω : Type} [Field Ω]

theorem lt_one_iff_of_sub_lt (V : ValuationSubring Ω) {x y : Ω} (h : V.valuation (x - y) < 1) :
    V.valuation x < 1 ↔ V.valuation y < 1 := by
  constructor
  · intro hx
    have : y = x - (x - y) := by ring
    rw [this]
    exact Valuation.map_sub_lt _ hx h
  · intro hy
    have : x = y + (x - y) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hy h

theorem comap_valuation_lt_one_iff {L : Type} [Field L] (f : L →+* Ω) (V : ValuationSubring Ω) (z : L) :
    (V.comap f).valuation z < 1 ↔ V.valuation (f z) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

theorem valuation_eq_one {V : ValuationSubring Ω} {s : Ω} (hs : s ∈ V) (h : ¬ V.valuation s < 1) :
    V.valuation s = 1 :=
  le_antisymm ((V.valuation_le_one_iff s).2 hs) (not_lt.1 h)

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj IntermediateField

theorem exists_den_integral (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V) {x : Ω}
    (hx : x ∈ V) :
    ∃ s t : Ω, IsIntegral R s ∧ IsIntegral R t ∧ V.valuation s = 1 ∧ s * x = t := by
  let M : IntermediateField K Ω := K⟮x⟯
  haveI : FiniteDimensional K M := adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral K x)
  haveI : Algebra.IsSeparable K M := Algebra.isSeparable_tower_bot_of_isSeparable K M Ω
  haveI : IsDedekindDomain (integralClosure R M) := integralClosure.isDedekindDomain R K M
  haveI : IsFractionRing (integralClosure R M) M := integralClosure.isFractionRing_of_finite_extension K M
  haveI : IsScalarTower R M Ω := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R K Ω, IsScalarTower.algebraMap_apply R K M]
    rfl
  let A := V.comap (algebraMap M Ω)
  have hint : ∀ s : integralClosure R M, IsIntegral R ((s : M) : Ω) := fun s =>
    (s.2).map (IsScalarTower.toAlgHom R M Ω)
  have hS : ∀ s : integralClosure R M, algebraMap (integralClosure R M) M s ∈ A := fun s =>
    mem_of_isIntegral V hR (hint s)
  obtain ⟨s, t, hs, e⟩ := exists_den (integralClosure R M) A hS (x := ⟨x, mem_adjoin_simple_self K x⟩) hx
  refine ⟨((s : M) : Ω), ((t : M) : Ω), hint s, hint t, valuation_eq_one (hS s) ?_, ?_⟩
  · intro h
    have h2 : A.valuation (algebraMap (integralClosure R M) M s) < 1 :=
      (comap_valuation_lt_one_iff (algebraMap M Ω) V _).2 h
    rw [hs] at h2
    exact lt_irrefl _ h2
  · have := congrArg (algebraMap M Ω) e
    simpa using this

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

section crit

variable (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    [Algebra.IsSeparable K Ω] (V : ValuationSubring Ω) (hR : ∀ r : R, algebraMap R Ω r ∈ V)

include hR in
theorem map_mem_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) {x : Ω} (hx : x ∈ V) :
    g x ∈ V := by
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [hg s hs, hs1]; exact lt_irrefl 1)
  have e' : g s * g x = g t := by rw [← map_mul, e]
  have := congrArg V.valuation e'
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [← V.valuation_le_one_iff, this, V.valuation_le_one_iff]
  exact mem_of_isIntegral V hR (ht.map (g.restrictScalars R))


include hR in
theorem smul_eq_of_lt_one_iff (g : Ω ≃ₐ[K] Ω)
    (hg : ∀ b : Ω, IsIntegral R b → (V.valuation (g b) < 1 ↔ V.valuation b < 1)) : g • V = V := by
  have hgi : ∀ y : Ω, g (g⁻¹ y) = y := fun y => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hg' : ∀ b : Ω, IsIntegral R b → (V.valuation (g⁻¹ b) < 1 ↔ V.valuation b < 1) := by
    intro b hb
    have := hg (g⁻¹ b) (hb.map ((g⁻¹ : Ω ≃ₐ[K] Ω).restrictScalars R))
    rw [hgi] at this
    exact this.symm
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  constructor
  · intro h
    have := map_mem_of_lt_one_iff R K Ω V hR g hg h
    rwa [hgi] at this
  · intro h
    exact map_mem_of_lt_one_iff R K Ω V hR g⁻¹ hg' h


include hR in
theorem mem_inertia_of_sub_lt_one (g : Ω ≃ₐ[K] Ω)
    (h : ∀ b : Ω, IsIntegral R b → V.valuation (g b - b) < 1) : g ∈ inertia K V := by
  have hg : g • V = V := smul_eq_of_lt_one_iff R K Ω V hR g fun b hb => lt_one_iff_of_sub_lt V (h b hb)
  rw [mem_inertia_iff]
  refine ⟨hg, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den_integral R K Ω V hR hx
  have hgs : V.valuation (g s) = 1 :=
    valuation_eq_one (mem_of_isIntegral V hR (hs.map (g.restrictScalars R))) (by
      rw [lt_one_iff_of_sub_lt V (h s hs), hs1]; exact lt_irrefl 1)
  have key : g s * (g x - x) = (g t - t) - x * (g s - s) := by
    rw [← e, map_mul]; ring
  have := congrArg V.valuation key
  rw [Valuation.map_mul, hgs, _root_.one_mul] at this
  rw [this]
  refine Valuation.map_sub_lt _ (h t ht) ?_
  rw [Valuation.map_mul]
  calc V.valuation x * V.valuation (g s - s) ≤ 1 * V.valuation (g s - s) :=
        mul_le_mul_left ((V.valuation_le_one_iff x).2 hx) _
    _ < 1 := by rw [_root_.one_mul]; exact h s hs

end crit

end GlobalTheory.InertiaRestrict

namespace GlobalTheory.InertiaRestrict

open GlobalTheory.ProlongConj

theorem exists_mem_inertia_eq_on : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] (τ : L ≃ₐ[K] L), τ ∈ inertia K (V.comap (algebraMap L Ω)) →
    ∃ σ ∈ inertia K V, ∀ y : L, σ (y : Ω) = (τ y : Ω) := by
  first
  | exact @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective
  | (apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralFractionLift.inertia_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralFractionLift.inertia_surjective ..)

end GlobalTheory.InertiaRestrict
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma baseChangePtEquiv_galPts (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (σ : Ω ≃ₐ[L] Ω)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ptOver L Ω ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) :
    _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x) =
      _root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) (_root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A x) := by
  apply Over.OverMorphism.ext
  show (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x).left ≫ _ = (_root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) _).left
  rw [_root_.GlobalTheory.Published.AbVarRed.galPts_left, _root_.GlobalTheory.Published.AbVarRed.galPts_left, Category.assoc]
  rfl


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), _root_.GlobalTheory.Published.AbVarRed.galTate ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) l σ = 1 ↔ _root_.GlobalTheory.Published.AbVarRed.galTate A l (σ.restrictScalars K) = 1 := by
  intro K L Ω _ _ _ _ _ _ _ A _ _ _ l _ σ
  set e := _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv (K := K) (L := L) (Ω := Ω) A
  have he := baseChangePtEquiv_galPts K L Ω A σ
  constructor
  · intro h
    refine LinearMap.ext fun s => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have ht := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.symm.toMonoidHom s)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at ht
    have := congrArg e ht
    rw [he] at this
    simpa [e] using this
  · intro h
    refine LinearMap.ext fun t => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have hs := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.toMonoidHom t)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at hs
    apply e.injective
    rw [he]
    exact hs

end GlobalTheory.TateBaseChange
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.inertia_pow_fixes_of_commutative_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω), FiniteDimensional K L → IsGalois K L → (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) → ∀ σ ∈ inertia K V, ∃ a : ℕ, ∀ x ∈ L, (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) x = x := by
  first | exact @GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative | exact GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative | (intros; apply GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.residueField_inertiaFixed_isAlgClosed_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsAlgClosed (IsLocalRing.ResidueField (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω))) := by
  first | exact @GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed | exact GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed | (intros; apply GlobalTheory.InertiaRes.residueField_inertiaFixed_isAlgClosed <;> assumption)
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ResAniso.VacSchwartz


open Classical in
theorem realPar_ne_zero (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (l : D.what₂.Tau → ℝ) (hl : StdUnn.HasRealPar ψ θ l) (τ₀ : D.what₂.Tau) : l τ₀ ≠ 0 := by
  intro h0
  obtain ⟨a, ha, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling hψ
  have hbij := GlobalTheory.CMTypePlaces.places_bijective D
  let w : D.what₂.Tau → InfinitePlace D.host.F := fun τ =>
    InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))
  have hemb : ∀ τ, (w τ).embedding = (tauE D τ).comp (algebraMap D.host.F D.host.E) := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  have hθ' : ∀ τ (x : Ainf D.host.F), θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ)) := fun τ =>
    congrFun ((InfiniteAdeleRing.denseRange_algebraMap D.host.F).equalizer (hθ τ).2
      ((InfinitePlace.Completion.isometry_extensionEmbedding (w τ)).continuous.comp (continuous_apply (w τ)))
      (funext fun b => by
        show θ τ (algebraMap D.host.F (Ainf D.host.F) b ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, (hθ τ).1, Function.comp_apply]
        erw [GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap (w τ) b, hemb]
        rfl))
  set e : ℝ := ((w τ₀).embedding a).re with he
  have hre : ((w τ₀).embedding a).im = 0 := by
    have hr : NumberField.ComplexEmbedding.IsReal (w τ₀).embedding :=
      InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
    have := congrArg (fun φ : D.host.F →+* ℂ => φ a) hr
    exact Complex.conj_eq_iff_im.1 this
  have he0 : e ≠ 0 := by
    intro h
    apply ha
    have : (w τ₀).embedding a = 0 := Complex.ext (by simpa [he] using h) (by simpa using hre)
    exact (map_eq_zero_iff _ (w τ₀).embedding.injective).1 this
  obtain ⟨x, hx⟩ := GlobalTheory.StdUnn.RealPar.exists_real_point hθ τ₀ (1 / (2 * e))
  have e1 := hl x
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h0, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero] at e1
  have e2 := hinf x
  have hsum : ∑ u : InfinitePlace D.host.F, (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re = e * (1 / (2 * e)) := by
    rw [← hbij.sum_comp (fun u : InfinitePlace D.host.F => (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re)]
    have hterm : ∀ τ, ((w τ).embedding a).re * (InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ))).re =
        if τ = τ₀ then e * (1 / (2 * e)) else 0 := fun τ => by
      rw [← hθ' τ x, hx τ]
      split_ifs with h
      · subst h; simp [he]
      · simp
    refine (Finset.sum_congr rfl fun τ _ => hterm τ).trans ?_
    simp
  rw [hsum, e1] at e2
  have h2 : e * (1 / (2 * e)) = 1 / 2 := by field_simp
  rw [h2] at e2
  have h3 : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I := by push_cast; ring
  rw [h3, Complex.exp_pi_mul_I] at e2
  norm_num at e2

end GlobalTheory.ResAniso.VacSchwartz
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_branching_constant_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  first | exact @GlobalTheory.InfSize.main | exact GlobalTheory.InfSize.main | (intros; apply GlobalTheory.InfSize.main <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.bi_invariant_test_function_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 := by
  first | (exact @GlobalTheory.LKDef.Regroup.regroup) | (exact GlobalTheory.LKDef.Regroup.regroup) | (intros; apply GlobalTheory.LKDef.Regroup.regroup <;> assumption)
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV

theorem _root_.GlobalTheory.T.irreducible_character_good_idempotent_cuspidal_product' : ∀ (D : D7) [Fintype (G0g D.nd)], (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → ∀ χ : G0g D.nd → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, D.ntypes.e0.coeff g * χ g = χ 1 → ∃ θ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GL (Fin D.R.r) (ZMod (D.host.g kv.1)) → ℂ, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩; GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (θ kv)) ∧ ∀ g, χ g = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv (g kv) := by
  first | exact @GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product | exact GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product | (intros; apply GlobalTheory.GoodFactor.irreducible_character_good_idempotent_cuspidal_product <;> assumption)
end

section

open CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

theorem _root_.GlobalTheory.T.levMove_comp_r_eq_of_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (g gA : Dw.La →ₗ[𝓞 E] Dw.La), IsIso ρ₂ → IsLevMove ρ₂ ν₂ g gA → (∀ a, g a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ρ₂ ≫ d.r = d.r ∧ ν₂.φ ≫ d.m.φ = d.m.φ := by
  first | exact @GlobalTheory.levMove_comm_levelMap_of_trivial_mod | exact GlobalTheory.levMove_comm_levelMap_of_trivial_mod | (intros; apply GlobalTheory.levMove_comm_levelMap_of_trivial_mod <;> assumption)
end
