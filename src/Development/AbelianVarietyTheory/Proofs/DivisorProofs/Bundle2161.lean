module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle027
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.LocalGeometry.Imports
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Proof

theorem exists_prime_natCast_ne_zero (k : Type) [Field k] :
    ∃ (l : ℕ) (_ : Fact l.Prime), (l : k) ≠ 0 := by
  by_cases h2 : ((2 : ℕ) : k) = 0
  · refine ⟨3, ⟨Nat.prime_three⟩, fun h3 => one_ne_zero (α := k) ?_⟩
    have : ((3 : ℕ) : k) - ((2 : ℕ) : k) = 1 := by push_cast; ring
    rw [← this, h2, h3, sub_zero]
  · exact ⟨2, ⟨Nat.prime_two⟩, h2⟩

theorem torsionUnramified_imp_tate_and_infinite :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [Field Ω]
      [Algebra K Ω] (V : ValuationSubring Ω) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
      (∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m) →
      (∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l) ∧
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ V A _ _ hb
  obtain ⟨l, hl, hl0⟩ := exists_prime_natCast_ne_zero (ResidueField R)
  have hpow : ∀ n : ℕ, ((l ^ n : ℕ) : ResidueField R) ≠ 0 := fun n => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hl0
  refine ⟨⟨l, hl, hl0, tateUnramified_of_torsionUnramified fun n => hb _ (hpow n)⟩, ?_⟩
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hl.out.two_le) fun n => ⟨hpow n, hb _ (hpow n)⟩

end GlobalTheory.Proof
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem not_mem_div_uniformizer_pow : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → ∀ x : Ω, x ≠ 0 → ∃ n : ℕ, x / algebraMap K Ω (algebraMap R K π) ^ n ∉ V := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ x hx
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable

  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨r, rfl⟩
    exact this

  have hKV : ∀ c : K, algebraMap K Ω c ∈ V → ∃ r : R, algebraMap R K r = c := by
    intro c hc
    have : c ∈ V.toSubring.comap (algebraMap K Ω) := hc
    rw [hV] at this
    exact this
  have halgK : IsAlgebraic K x⁻¹ := Algebra.IsAlgebraic.isAlgebraic _
  have halgR : IsAlgebraic R x⁻¹ := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨d, hd0, hint⟩ := halgR.exists_integral_multiple
  let f : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV
  letI : Algebra R V := f.toAlgebra
  haveI : IsScalarTower R V Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hintV : IsIntegral V (d • x⁻¹) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintV
  have hyV : d • x⁻¹ ∈ V := by rw [← hy]; exact y.2

  have hfin : FiniteMultiplicity π d := FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hd0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ π ^ n ∣ d := by
    obtain ⟨m, hm⟩ := hfin
    exact ⟨m + 1, hm⟩
  refine ⟨n, fun hmem => hn ?_⟩
  have hprod : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) ∈ V := V.mul_mem _ _ hyV hmem
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have heq : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) =
      algebraMap K Ω (algebraMap R K d / algebraMap R K π ^ n) := by
    rw [Algebra.smul_def, map_div₀, map_pow]
    change (algebraMap K Ω) (algebraMap R K d) * x⁻¹ * _ = _
    field_simp
  rw [heq] at hprod
  obtain ⟨r, hr⟩ := hKV _ hprod
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_pow, hr]
  field_simp

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem inertia_conj_mem_smul : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  intro K Ω _ _ _ V g σ hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨h1, h2⟩ := hσ

  have hn : ∀ z : Ω, V.valuation z < 1 → (g • V).valuation (g z) < 1 := by
    intro z hz
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hz ⊢
    rcases hz with hz | hz
    · left; simp [hz]
    · right
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      intro h
      apply hz
      have : (g⁻¹ • (g z)⁻¹) = z⁻¹ := by
        change g⁻¹ ((g z)⁻¹) = z⁻¹
        rw [map_inv₀]
        simp
      rwa [this] at h
  refine ⟨?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
    set y := g⁻¹ • x with hy
    have hxy : x = g y := by simp [hy]
    have : (g * σ * g⁻¹) x - x = g (σ y - y) := by
      rw [map_sub, hxy]
      simp
    rw [this]
    exact hn _ (h2 y hx)

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaLift

theorem mem_iff_pow_mem {F : Type} [Field F] (A : ValuationSubring F) {m : ℕ} (hm : 0 < m) (y : F) :
    y ∈ A ↔ y ^ m ∈ A := by
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_pow]
  exact (pow_le_one_iff_of_nonneg zero_le' hm.ne').symm

theorem nonunit_of_pow {F : Type} [Field F] (A : ValuationSubring F) {m : ℕ} (hm : 0 < m) (z : F)
    (h : A.valuation (z ^ m) < 1) : A.valuation z < 1 := by
  rw [map_pow] at h
  by_contra h'
  push_neg at h'
  exact absurd h (not_lt.2 (one_le_pow₀ h'))

end GlobalTheory.InertiaLift

open GlobalTheory.InertiaLift in
theorem GlobalTheory.inertia_lift_of_purelyInseparable : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra L Ω'] [Algebra K Ω'] (j : Ω →ₐ[K] Ω'), (∀ y : Ω', ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m) → ∀ (V' : ValuationSubring Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[L] Ω'), (∀ x, σ' (j x) = j (σ x)) → σ ∈ inertia K (V'.comap (j : Ω →+* Ω')) → σ' ∈ inertia L V' := by
  intro K L Ω Ω' _ _ _ _ _ _ _ j hpi V' σ σ' hcomm hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨hσV, hσv⟩ := hσ
  set V := V'.comap (j : Ω →+* Ω') with hV
  have hmemV : ∀ x, j x ∈ V' ↔ x ∈ V := fun x => Iff.rfl
  have hσmem : ∀ x, σ x ∈ V ↔ x ∈ V := by
    intro x
    constructor
    · intro h
      have h2 : σ x ∈ σ • V := by rw [hσV]; exact h
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h2
      simpa using h2
    · intro h
      have h2 : σ • x ∈ σ • V := ValuationSubring.smul_mem_pointwise_smul σ x V h
      rw [hσV] at h2
      exact h2
  have hσ'mem : ∀ y, σ' y ∈ V' ↔ y ∈ V' := by
    intro y
    obtain ⟨m, x, hm, hyx, -⟩ := hpi y
    rw [mem_iff_pow_mem V' hm, mem_iff_pow_mem V' hm y, ← map_pow, hyx, hcomm, hmemV, hmemV, hσmem]
  have hlt : ∀ w, V.valuation w < 1 → V'.valuation (j w) < 1 := by
    intro w hw
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hw ⊢
    rcases hw with hw | hw
    · left; simp [hw]
    · right
      rw [← map_inv₀]
      exact hw
  refine ⟨?_, ?_⟩
  · ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have := hσ'mem (σ'⁻¹ • z)
    simp only [AlgEquiv.smul_def] at this ⊢
    rw [← this]
    simp
  · intro y hy
    obtain ⟨m, x, hm, hyx, hfrob⟩ := hpi y
    have hx : x ∈ V := by rw [← hmemV, ← hyx]; exact (mem_iff_pow_mem V' hm y).1 hy
    apply nonunit_of_pow V' hm
    rw [hfrob, ← map_pow, hyx, hcomm, ← map_sub]
    exact hlt _ (hσv x hx)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtFin

theorem exists_finset_fix : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)),
    LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω,
      (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  classical
  intro K Ω _ _ _ A hA x
  haveI := hA
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω A.left).symm.surjective x.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hxs : x.left ≫ A.hom = spMap (algebraMap K Ω) := Over.w x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (A.left.fromSpecResidueField p ≫ A.hom)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType A.hom p ψ hψ
  rw [← hx, Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
  letI : Algebra K (A.left.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType K (A.left.residueField p) := hess
  let fa : A.left.residueField p →ₐ[K] Ω :=
    { φ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
  refine ⟨(Algebra.EssFiniteType.finset K (A.left.residueField p)).image fa, fun σ hσ => ?_⟩
  have e : (σ : Ω →ₐ[K] Ω).comp fa = fa :=
    Algebra.EssFiniteType.algHom_ext Ω _ _ fun c hc => hσ _ (Finset.mem_image_of_mem _ hc)
  apply Over.OverMorphism.ext
  change spMap (σ : Ω →+* Ω) ≫ x.left = x.left
  rw [← hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext c
  exact congrArg (fun g => g c) e

end GlobalTheory.PtFin
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem exists_fixedField_point (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) (_ : LocallyOfFiniteType A.hom) (x : ptOver K Ω ⟶ A)
    (hx : ∀ σ ∈ H, specAut σ ≫ x = x) :
    ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left,
      spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  have hfix : ∀ c ∈ E, ∀ σ ∈ H, σ c = c := by
    intro c hc σ hσ
    have h1 : spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
      rw [hid, Category.id_comp]
      exact congrArg CommaMorphism.left (hx σ hσ)
    exact (hE1 _ _).1 h1 c hc
  refine (hE2 (IntermediateField.fixedField H) (algebraMap (IntermediateField.fixedField H) Ω)).1 ?_
  intro c hc
  exact ⟨⟨c, fun σ => hfix c hc σ σ.2⟩, rfl⟩

end GlobalTheory.Published.AbVarRed
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Published.AbVarRed

theorem torsionUnramified_of_hasGoodReduction : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω),
    IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], HasGoodReduction R K A →
    ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := by
  intro R K Ω _ _ _ _ _ _ _ _ V hV A _ _ hA m hm σ hσ x hx
  obtain ⟨G, _, hG, e, he⟩ := hA
  have : IsCommMonObj G := hG.comm
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hP : IsGrpPullback A G (spMap (algebraMap R K)) (e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K))) :=
    ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G (spMap (algebraMap R K)))).congr
      (Category.id_comp _) rfl
  set φ := e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K)) with hφ

  let T0 : Over (Sp R) := Over.mk ((ptOver K Ω).hom ≫ spMap (algebraMap R K))
  let Φ : (ptOver K Ω ⟶ A) → (T0 ⟶ G) := fun y => Over.homMk (y.left ≫ φ) (by
    change (y.left ≫ φ) ≫ G.hom = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w y])
  have Φmul : ∀ y y', Φ (y * y') = Φ y * Φ y' := fun y y' =>
    Over.OverMorphism.ext (hP.2 (ptOver K Ω) y y' (Φ y) (Φ y') rfl rfl).symm
  let ΦM : (ptOver K Ω ⟶ A) →* (T0 ⟶ G) := MonoidHom.mk' Φ Φmul
  have Φinj : Function.Injective Φ := fun y y' h =>
    Over.OverMorphism.ext (hP.1.hom_ext (congrArg Over.Hom.left h) ((Over.w y).trans (Over.w y').symm))

  have hmemV : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  let rV : R →+* V := ((algebraMap K Ω).comp (algebraMap R K)).codRestrict V hmemV
  have hrV : (algebraMap V Ω).comp rV = (algebraMap K Ω).comp (algebraMap R K) := RingHom.ext fun _ => rfl

  obtain ⟨hσV, hσr⟩ := (mem_inertia_iff V σ).1 hσ
  have hmem : ∀ y ∈ V, σ y ∈ V := fun y hy => by
    have h := (ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := V) (x := y)).2 hy
    rw [hσV] at h
    exact h
  let σV : V →+* V := ((σ : Ω →+* Ω).comp (algebraMap V Ω)).codRestrict V fun y => hmem y y.2
  have F1 : (algebraMap V Ω).comp σV = (σ : Ω →+* Ω).comp (algebraMap V Ω) := RingHom.ext fun _ => rfl
  have F2 : σV.comp rV = rV := RingHom.ext fun r => Subtype.ext (σ.commutes (algebraMap R K r))
  have F3 : (residue V).comp σV = residue V := RingHom.ext fun y => by
    change residue V (σV y) = residue V y
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hσr y y.2

  have hE : ValuativeCriterion.Existence G.hom := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) G.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  let S : ValuativeCommSq G.hom := ⟨V, Ω, (Φ x).left, spMap rV, ⟨by
    change (x.left ≫ φ) ≫ G.hom = spMap (algebraMap V Ω) ≫ spMap rV
    rw [Category.assoc, hP.1.w, ← Category.assoc, Over.w x, GlobalTheory.RedPts.spMap_comp, hrV]
    exact GlobalTheory.RedPts.spMap_comp _ _⟩⟩
  obtain ⟨l, hl1, hl2⟩ := (hE S).exists_lift.some
  change spMap (algebraMap V Ω) ≫ l = x.left ≫ φ at hl1
  change l ≫ G.hom = spMap rV at hl2
  let P : Over (Sp R) := Over.mk (spMap rV)
  let a : P ⟶ G := Over.homMk l hl2
  let b : P ⟶ G := Over.homMk (spMap σV ≫ l) (by
    change (spMap σV ≫ l) ≫ G.hom = spMap rV
    rw [Category.assoc, hl2, GlobalTheory.RedPts.spMap_comp, F2])
  let u : T0 ⟶ P := Over.homMk (spMap (algebraMap V Ω)) (by
    change spMap (algebraMap V Ω) ≫ spMap rV = (ptOver K Ω).hom ≫ spMap (algebraMap R K)
    rw [GlobalTheory.RedPts.spMap_comp, hrV]
    exact (GlobalTheory.RedPts.spMap_comp _ _).symm)
  have hua : u ≫ a = Φ x := Over.OverMorphism.ext hl1
  have hub : u ≫ b = Φ (galPts A σ x) := Over.OverMorphism.ext (by
    change spMap (algebraMap V Ω) ≫ spMap σV ≫ l = (galPts A σ x).left ≫ φ
    rw [galPts_left, ← Category.assoc, GlobalTheory.RedPts.spMap_comp, F1, ← GlobalTheory.RedPts.spMap_comp, Category.assoc, hl1,
      Category.assoc])

  let Z : Over (Sp R) := Over.mk (spMap ((residue V).comp rV))
  let j : Z ⟶ P := Over.homMk (spMap (residue V)) (GlobalTheory.RedPts.spMap_comp _ _)
  have hjb : j ≫ b = j ≫ a := Over.OverMorphism.ext (by
    change spMap (residue V) ≫ spMap σV ≫ l = spMap (residue V) ≫ l
    rw [← Category.assoc, GlobalTheory.RedPts.spMap_comp, F3])
  have hdom : IsDominant (spMap (algebraMap V Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap V Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V Ω)]; exact bot_le)⟩
  have hu : Function.Injective (GlobalTheory.RedPts.precomp G u) := fun c d h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp V) G.hom ((Over.w c).trans (Over.w d).symm)
      (spMap (algebraMap V Ω)) (congrArg Over.Hom.left h))
  have hz : (b * a⁻¹) ^ m = 1 := by
    apply hu
    rw [map_pow, map_one, map_mul, map_inv]
    change ((u ≫ b) * (u ≫ a)⁻¹) ^ m = 1
    rw [hua, hub]
    change (ΦM (galPts A σ x) * (ΦM x)⁻¹) ^ m = 1
    rw [← map_inv, ← map_mul, ← map_pow, mul_pow, inv_pow, ← map_pow, hx, map_one, inv_one, _root_.mul_one, map_one]
  have hjz : j ≫ (b * a⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hjb, mul_inv_cancel]
  have hn : IsUnit (m : V) := by
    have h1 : IsUnit (m : R) := by
      by_contra h
      apply hm
      rw [← map_natCast (residue R), residue_eq_zero_iff]
      exact h
    simpa using h1.map rV
  have h1 := GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G (spMap rV) hn (b * a⁻¹) hz j
    ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue V)⟩ hjz
  have hba : b = a := mul_inv_eq_one.1 h1
  apply Φinj
  rw [← hub, ← hua, hba]

end GlobalTheory.Published.AbVarRed
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ᶠ w in cofinite, ∀ x : UA E n, x ∈ locU n w → cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ h : x ∈ finU (E := E) (n := n), (⟨x, h⟩ : finU (E := E) (n := n)) ∈ L := by
  first | exact @GlobalTheory.BCT.GlobLev.eventually_locU_mem | exact GlobalTheory.BCT.GlobLev.eventually_locU_mem | (intros; apply GlobalTheory.BCT.GlobLev.eventually_locU_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_jacquetShalika : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.GelfandKazhdanDual :=
  fun hJ hA => gelfandKazhdanDual_of_rapidDecay hJ hA (GlobalTheory.cuspRapidDecaySiegelGL_of_finite hA)

end GlobalTheory.GelfandKazhdanTop
end

section

namespace GlobalTheory

theorem geometricLemmaFiltration_holds : GlobalTheory.Published.GeometricLemmaFiltration :=
  CompanionTheory.Geo.geometricLemmaFiltration

end GlobalTheory
end
