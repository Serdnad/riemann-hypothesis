module

public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle004
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle013
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.DualLattices.Bundle009
public import ReciprocityTheory.DualLattices.Bundle011
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import ReciprocityTheory.DualLattices.Bundle007

@[expose] public section

section

namespace PositivityTheory.HtPt.Plen

open GroundTheory.FunctionField IsLocalRing

theorem finite_closure (k K A : Type) [Field k] [Field K] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra A K] [IsFractionRing A K] [Algebra.EssFiniteType k A] :
    Module.Finite A (integralClosure A K) := by
  classical
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hR : ∀ r : Algebra.EssFiniteType.subalgebra k A, algebraMap _ K r = algebraMap A K (r : A) :=
    fun _ => rfl
  have hfs : FaithfulSMul (Algebra.EssFiniteType.subalgebra k A) K := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact Subtype.ext (hinj h)
  have hfr : IsFractionRing (Algebra.EssFiniteType.subalgebra k A) K := by
    refine IsFractionRing.of_field _ K fun z => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨⟨a₁, s⟩, ha⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid k A) a
    obtain ⟨⟨b₁, t⟩, hb'⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid k A) b
    have hs : IsUnit ((s.1 : Algebra.EssFiniteType.subalgebra k A) : A) := s.2
    have ht : IsUnit ((t.1 : Algebra.EssFiniteType.subalgebra k A) : A) := t.2
    have hs0 : algebraMap A K (s.1 : A) ≠ 0 := (hs.map _).ne_zero
    have ht0 : algebraMap A K (t.1 : A) ≠ 0 := (ht.map _).ne_zero
    have hb0 : algebraMap A K b ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
    have ha2 : a * (s.1 : A) = (a₁ : A) := ha
    have hb2 : b * (t.1 : A) = (b₁ : A) := hb'
    refine ⟨a₁ * t.1, b₁ * s.1, ?_⟩
    rw [map_mul, map_mul, hR, hR, hR, hR, ← ha2, ← hb2, map_mul, map_mul]
    field_simp
  have hfin := GroundTheory.Heights₂.Heights.FieldNumbers.NoetherIntegralClosureFinite.proof k
    (Algebra.EssFiniteType.subalgebra k A) K K
  have hfg : (integralClosure (Algebra.EssFiniteType.subalgebra k A) K).toSubmodule.FG :=
    Module.Finite.iff_fg.1 hfin
  obtain ⟨t, ht⟩ := hfg
  have hmem : ∀ x : K, IsIntegral (Algebra.EssFiniteType.subalgebra k A) x ↔
      x ∈ Submodule.span (Algebra.EssFiniteType.subalgebra k A) (t : Set K) := by
    intro x
    rw [ht]
    rfl
  have : (integralClosure A K).toSubmodule.FG := by
    refine ⟨t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      exact ((hmem x).2 (Submodule.subset_span hx)).tower_top
    · intro x hx
      have hx' : IsIntegral A x := hx
      obtain ⟨m, hm⟩ := hx'.exists_multiple_integral_of_isLocalization
        (Algebra.EssFiniteType.submonoid k A)
      have h1 := Submodule.span_le_restrictScalars (Algebra.EssFiniteType.subalgebra k A) A
        (t : Set K) ((hmem _).1 hm)
      have hu : IsUnit ((m.1 : Algebra.EssFiniteType.subalgebra k A) : A) := m.2
      obtain ⟨u, hu⟩ := hu
      have h2 : (u : A) • x ∈ Submodule.span A (t : Set K) := by
        rw [hu]
        exact h1
      have h3 := Submodule.smul_mem _ ((u⁻¹ : Aˣ) : A) h2
      rwa [smul_smul, Units.inv_mul, one_smul] at h3
  exact Module.Finite.iff_fg.2 this

variable {k K : Type} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

noncomputable def resHom (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) : A →ₐ[k] v.ResidueField where
  toRingHom := (residue v.ring).comp (RingHom.codRestrict (algebraMap A K) v.ring hv)
  commutes' c := by
    change residue v.ring _ = residue v.ring (algebraMap k v.ring c)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply k A K c).symm

omit [IsFunctionField k K] in
theorem resHom_eq_zero (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) (a : A) :
    resHom A v hv a = 0 ↔ v.ring.valuation (algebraMap A K a) < 1 := by
  change residue v.ring ⟨algebraMap A K a, hv a⟩ = 0 ↔ _
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem isMaximal_center (A : Type) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
    (v : Place k K) (hv : ∀ a : A, algebraMap A K a ∈ v.ring) (p : Ideal A)
    (hp : ∀ a, a ∈ p ↔ v.ring.valuation (algebraMap A K a) < 1) : p.IsMaximal := by
  have hker : p = RingHom.ker (resHom A v hv) := by
    ext a
    rw [hp, RingHom.mem_ker, resHom_eq_zero]
  subst hker
  have hinj := Ideal.kerLiftAlg_injective (resHom A v hv)
  have : Module.Finite k (A ⧸ RingHom.ker (resHom A v hv)) :=
    Module.Finite.of_injective (Ideal.kerLiftAlg (resHom A v hv)).toLinearMap hinj
  have : IsArtinianRing (A ⧸ RingHom.ker (resHom A v hv)) := IsArtinianRing.of_finite k _
  have : (RingHom.ker (resHom A v hv)).IsPrime := RingHom.ker_isPrime _
  exact Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)

theorem isMaximal_of_ne_bot (A : Type) [CommRing A] [Algebra k A] [Algebra A K]
    [IsScalarTower k A K] (hinj : Function.Injective (algebraMap A K)) (p : Ideal A) (hp0 : p ≠ ⊥)
    (hp : p.IsPrime) : p.IsMaximal := by
  have hu : ∀ y : p.primeCompl, IsUnit (algebraMap A K y) := fun y => by
    refine IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 fun h => y.2 ?_)
    rw [h]
    exact p.zero_mem
  let g : Localization.AtPrime p →+* K := IsLocalization.lift (M := p.primeCompl) hu
  have hg : ∀ a, g (algebraMap A _ a) = algebraMap A K a := fun a => IsLocalization.lift_eq hu a
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g
  have hA : ∀ a, algebraMap A K a ∈ V := fun a => hg a ▸ hV (algebraMap A _ a)
  have key : ∀ a, a ∈ p ↔ V.valuation (algebraMap A K a) < 1 := by
    intro a
    have h1 : IsUnit (g.codRestrict V.toSubring hV (algebraMap A _ a)) ↔
        IsUnit (algebraMap A (Localization.AtPrime p) a) := isUnit_map_iff _ _
    have h2 : IsUnit (g.codRestrict V.toSubring hV (algebraMap A _ a)) ↔
        V.valuation (g (algebraMap A _ a)) = 1 :=
      V.valuation_eq_one_iff ⟨g (algebraMap A _ a), hV _⟩
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p, h2, hg] at h1
    have h3 : V.valuation (algebraMap A K a) ≤ 1 := (V.valuation_le_one_iff _).2 (hA a)
    rw [lt_iff_le_and_ne, and_iff_right h3, Ne, h1]
    exact not_not.symm
  have hne : V ≠ ⊤ := by
    rintro rfl
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
    have h1 := (key a).1 ha
    have h0 : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha0
    have h2 := ((⊤ : ValuationSubring K).valuation_le_one_iff (algebraMap A K a)⁻¹).2
      (ValuationSubring.mem_top _)
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))] at h2
    exact absurd h1 (not_lt.2 h2)
  let v : Place k K := ⟨V, hne, fun c => by
    rw [IsScalarTower.algebraMap_apply k A K]
    exact hA _⟩
  exact isMaximal_center A v hA p key

end PositivityTheory.HtPt.Plen
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

private theorem mem_range_bc_of_entries_mem_intL {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (k : K)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ c : A, s • k = algebraMap A K c) :
    ∃ c : A, algebraMap A K c = k := by
  have hk : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
    rw [GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof A K]
    refine (Submodule.mem_iInf _).2 fun p => (Submodule.mem_iInf _).2 fun hp => ?_
    obtain ⟨s, hs, c, hc⟩ := h p.asIdeal p.isPrime hp
    refine ⟨s, hs, ?_⟩
    rw [hc, Subalgebra.mem_toSubmodule]
    exact Subalgebra.algebraMap_mem _ c
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, hc⟩

theorem test_incl : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω), M.IsFullLattice K → Module.Projective A M → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ M) → x ∈ M := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x hlat hproj hloc
  classical
  have hden : ∀ w ∈ Submodule.span K (M : Set Ω), ∃ d ∈ nonZeroDivisors A, d • w ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact ⟨1, one_mem _, by rw [one_smul]; exact hw⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
    | add u w _ _ hu hw =>
      obtain ⟨d1, hd1, h1⟩ := hu
      obtain ⟨d2, hd2, h2⟩ := hw
      refine ⟨d1 * d2, mul_mem hd1 hd2, ?_⟩
      have e1 : (d1 * d2) • u = d2 • (d1 • u) := by rw [mul_comm, mul_smul]
      have e2 : (d1 * d2) • w = d1 • (d2 • w) := by rw [mul_smul]
      rw [smul_add, e1, e2]
      exact M.add_mem (M.smul_mem _ h1) (M.smul_mem _ h2)
    | smul k w _ hw =>
      obtain ⟨d, hd, h1⟩ := hw
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) k
      refine ⟨b * d, mul_mem hb hd, ?_⟩
      have hb0 : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have e : (b * d) • ((algebraMap A K a / algebraMap A K b) • w) = a • (d • w) := by
        rw [← algebraMap_smul K (b * d), smul_smul, smul_smul a d w, ← algebraMap_smul K (a * d) w]
        congr 1
        rw [map_mul, map_mul]
        field_simp
      rw [e]
      exact M.smul_mem a h1
  letI := hlat
  obtain ⟨d, hd, hdx⟩ := hden x (by rw [Submodule.IsFullLattice.span_eq_top]; trivial)
  have hd0' : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨σ, hσ⟩ := hproj.out
  set z : M := ⟨d • x, hdx⟩ with hzdef
  have hdiv : ∀ m : M, ∃ c : A, σ z m = d * c := by
    intro m
    have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
        ∃ c : A, s • (algebraMap A K (σ z m) / algebraMap A K d) = algebraMap A K c := by
      intro q hq hh
      obtain ⟨s, hs, hsx⟩ := hloc q hq hh
      refine ⟨s, hs, σ ⟨s • x, hsx⟩ m, ?_⟩
      have hz : s • z = d • (⟨s • x, hsx⟩ : M) := Subtype.ext (smul_comm s d x)
      have hm : s * σ z m = d * σ ⟨s • x, hsx⟩ m := by
        have h' := congrArg (fun f => f m) (congrArg σ hz)
        simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hm, map_mul]
      field_simp
    obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := K) _ hl
    refine ⟨c, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hc]
    field_simp
  choose c hc using hdiv
  have hyM : (∑ m ∈ (σ z).support, c m • (m : Ω)) ∈ M :=
    M.sum_mem (fun m _ => M.smul_mem _ m.2)
  have hsum : (∑ m ∈ (σ z).support, (σ z m) • (m : Ω)) = (z : Ω) := by
    have h1 := congrArg Subtype.val (hσ z)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at h1
    simpa using h1
  have hzy : d • (∑ m ∈ (σ z).support, c m • (m : Ω)) = d • x := by
    rw [Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hsum
    rw [hc m, mul_smul]
  have hcancel : ∀ u w : Ω, d • u = d • w → u = w := by
    intro u w huw
    have h1 : (algebraMap A K d) • u = (algebraMap A K d) • w := by
      rw [algebraMap_smul, algebraMap_smul]
      exact huw
    have h2 : (algebraMap A K d)⁻¹ • ((algebraMap A K d) • u) =
        (algebraMap A K d)⁻¹ • ((algebraMap A K d) • w) := by rw [h1]
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hd0', one_smul, one_smul] at h2
    exact h2
  rw [← hcancel _ _ hzy]
  exact hyM

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a t : A} (ha : a ≠ 0)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ a ∣ s * t) : a ∣ t := by
  classical
  have ha' : algebraMap A (FractionRing A) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha
  have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
      ∃ c : A, s • (algebraMap A (FractionRing A) t / algebraMap A (FractionRing A) a) =
        algebraMap A (FractionRing A) c := by
    intro q hq hh
    obtain ⟨s, hs, u, hu⟩ := h q hq hh
    refine ⟨s, hs, u, ?_⟩
    rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hu, map_mul]
    field_simp
  obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := FractionRing A) _ hl
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc]
  field_simp

theorem smul_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {M : Type} [AddCommGroup M] [Module A M] [Module.Projective A M]
    {a : A} (ha : a ≠ 0) (x : M)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ ∃ y : M, s • x = a • y) :
    ∃ y : M, x = a • y := by
  classical
  obtain ⟨σ, hσ⟩ := ‹Module.Projective A M›.out
  have hdiv : ∀ m : M, a ∣ σ x m := by
    intro m
    refine dvd_of_height_one ha (fun q hq hh => ?_)
    obtain ⟨s, hs, y, hy⟩ := h q hq hh
    refine ⟨s, hs, σ y m, ?_⟩
    have h' := congrArg (fun f => f m) (congrArg σ hy)
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
  choose c hc using hdiv
  refine ⟨∑ m ∈ (σ x).support, c m • m, ?_⟩
  conv_lhs => rw [← hσ x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [hc m, mul_smul, id_eq]

theorem test_div : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x a b _ hproj hx ha hab hloc
  have hloc' : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ y : M, s • (⟨x, hx⟩ : M) = a • y := by
    intro q hq hh
    by_cases hb : b ∈ q
    · obtain ⟨s, hs, y, hy, hsy⟩ := hloc q hq hh hb
      exact ⟨s, hs, ⟨y, hy⟩, Subtype.ext hsy⟩
    · exact ⟨a, fun haq => hb (hab q hq haq), ⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy⟩ := smul_of_height_one ha (⟨x, hx⟩ : M) hloc'
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end PositivityTheory.HtPt.Gc
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace PositivityTheory.HtPt.Mi

theorem flat_of_forall {X Z : Scheme.{0}} (f : X ⟶ Z)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (g : W ⟶ X) (w : W), g w = x ∧ Flat g ∧ Flat (g ≫ f)) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨W, g, w, rfl, _, _⟩ := h x
  have h := Flat.stalkMap (g ≫ f) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact GlobalTheory.ringHom_flat_of_comp_faithfullyFlat (GlobalTheory.faithfullyFlat_stalkMap_of_flat g w) h

theorem open_crit : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  intro R _ X Y j q _ H
  have key : ∀ x : X, ∃ (U V : Scheme.{0}) (g : U ⟶ X) (u : U) (δ : U ⟶ V) (m : V ⟶ pullback j j),
      g u = x ∧ Flat g ∧ Flat (g ≫ j) ∧ IsOpenImmersion δ ∧ Flat m ∧ δ ≫ m = g ≫ pullback.diagonal j ∧
      ∀ z, pullback.snd j j z = x → ∃ u', m (δ u') = z := by
    intro x
    obtain ⟨R', _, _, _, X', Y', j', q', a, b, U, hfl, hP, hb, ha, hU, hcl⟩ := @H (q (j x)).asIdeal (q (j x)).isPrime
    have hs : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 hfl)
    have hbf : Flat b := MorphismProperty.of_isPullback hb.flip hs
    have haf : Flat a := MorphismProperty.of_isPullback ha.flip hbf
    obtain ⟨x', hx1, hx2⟩ := Scheme.exists_preimage_of_isPullback (ha.paste_vert hb) x
      (IsLocalRing.closedPoint R') (PrimeSpectrum.ext hP.symm)
    have hx2' : q' (j' x') = IsLocalRing.closedPoint R' := by rw [← hx2]; simp
    let u : U.toScheme := ⟨x', hcl x' hx2'⟩
    have hu : U.ι u = x' := rfl
    have hw : (U.ι ≫ a) ≫ j = (U.ι ≫ j') ≫ b := by rw [Category.assoc, ha.w, Category.assoc]
    let δ : U.toScheme ⟶ pullback j' (U.ι ≫ j') := pullback.lift U.ι (𝟙 _) (by simp)
    have hδ : δ ≫ pullback.fst _ _ = U.ι := pullback.lift_fst _ _ _
    have hδ' : δ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hV := (IsPullback.of_hasPullback j' (U.ι ≫ j')).paste_horiz ha
    rw [← hw] at hV
    let m : pullback j' (U.ι ≫ j') ⟶ pullback j j :=
      pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ U.ι ≫ a) (by rw [hV.w]; simp only [Category.assoc])
    have hm1 : m ≫ pullback.fst j j = pullback.fst _ _ ≫ a := pullback.lift_fst _ _ _
    have hm2 : m ≫ pullback.snd j j = pullback.snd _ _ ≫ U.ι ≫ a := pullback.lift_snd _ _ _
    have hm : IsPullback m (pullback.snd j' (U.ι ≫ j')) (pullback.snd j j) (U.ι ≫ a) :=
      IsPullback.of_right (by rw [hm1]; exact hV) hm2 (IsPullback.of_hasPullback j j)
    have hg : Flat (U.ι ≫ a) := inferInstance
    have hδo : IsOpenImmersion δ := by
      have : IsOpenImmersion (δ ≫ pullback.fst j' (U.ι ≫ j')) := by rw [hδ]; infer_instance
      exact IsOpenImmersion.of_comp δ (pullback.fst j' (U.ι ≫ j'))
    have hgu : (U.ι ≫ a) u = x := by rw [Scheme.Hom.comp_apply, hu]; exact hx1
    refine ⟨U, _, U.ι ≫ a, u, δ, m, hgu, hg, by rw [hw]; infer_instance, hδo,
      MorphismProperty.of_isPullback hm.flip hg, ?_, fun z hz => ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, reassoc_of% hδ]; simp
      · rw [Category.assoc, hm2, reassoc_of% hδ']; simp
    · obtain ⟨v, hv1, hv2⟩ := Scheme.exists_preimage_of_isPullback hm z u (hz.trans hgu.symm)
      have h1 : j' (pullback.fst j' (U.ι ≫ j') v) = j' x' := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact congrArg (fun t => j' (U.ι t)) hv2
      let u' : U.toScheme := ⟨pullback.fst j' (U.ι ≫ j') v, hcl _ (by rw [h1, hx2'])⟩
      have h2 : δ u' = v := by
        apply (pullback.fst j' (U.ι ≫ j')).isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hδ]
        rfl
      exact ⟨u', by rw [h2]; exact hv1⟩
  have : Flat j := flat_of_forall j fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, h3, -⟩ := key x
    exact ⟨U, g, u, h1, h2, h3⟩
  have : Flat (pullback.diagonal j) := flat_of_forall _ fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, -, h4, h5, h6, -⟩ := key x
    exact ⟨U, g, u, h1, h2, by rw [← h6]; infer_instance⟩
  have : Surjective (pullback.diagonal j) := ⟨fun z => by
    obtain ⟨U, V, g, u, δ, m, -, -, -, -, -, h6, h7⟩ := key (pullback.snd j j z)
    obtain ⟨u', hu'⟩ := h7 z rfl
    exact ⟨g u', by rw [← hu', ← Scheme.Hom.comp_apply, ← h6, Scheme.Hom.comp_apply]⟩⟩
  have : IsClosedImmersion (pullback.diagonal j) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [(pullback.diagonal j).surjective.range_eq]; exact isClosed_univ)
  have : IsIso (pullback.diagonal j) := Flat.isIso_of_surjective_of_mono _
  have : Mono j := (pullback.isIso_diagonal_iff j).1 this
  exact IsOpenImmersion.of_flat_of_mono j

end PositivityTheory.HtPt.Mi
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem charmem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA ψ
  obtain ⟨B, hB, hAA⟩ := AA.lat
  rw [hAA, ← dualLat_dualLat_spanCols B hB, ← hAA]
  intro u hu
  obtain ⟨r, hr⟩ := hv.exists_of_le_one
    (valuation_fourier_le_one v hv (fun _ : Unit => ψ) AA hu ())
  refine ⟨r, hr.trans ?_⟩
  rw [fourier_apply']
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end PositivityTheory.HtPt.Ra
end
end
