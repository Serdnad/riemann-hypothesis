module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory

theorem exists_eq_ptHom_of_isLocalRing : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (A : Type) [CommRing A] [IsLocalRing A] (ρ : R →+* A) (x : Sp A ⟶ scheme W), x ≫ toSpec W = spMap ρ → ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
  intro R _ W A _ _ ρ x hx
  have key : ∀ i : Fin 3, x (IsLocalRing.closedPoint A) ∈ coordOpen W i →
      ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
    intro i hi
    have htop : x ⁻¹ᵁ coordOpen W i = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff (R := A) (x ⁻¹ᵁ coordOpen W i)).mp hi
    have hr : Set.range x ⊆ Set.range (awayChart W i) := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ x ⁻¹ᵁ coordOpen W i := htop.ge trivial
      rw [← opensRange_awayChart] at hy
      exact hy
    obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (awayChart W i) x hr)
    have hx' : x = Spec.map (CommRingCat.ofHom g.hom) ≫ awayChart W i := by
      rw [CommRingCat.ofHom_hom, hg, IsOpenImmersion.lift_fac]
    rw [SpecMap_awayChart] at hx'
    have hρ : g.hom.comp (awayConst W i) = ρ := by
      rw [hx', ptHom_toSpec] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
    subst hρ
    exact ⟨_, _, hx'⟩
  have h : x (IsLocalRing.closedPoint A) ∈ coordOpen W 1 ⊔ coordOpen W 2 := by
    rw [coordOpen_one_sup_coordOpen_two]
    trivial
  rcases h with h | h
  · exact key 1 h
  · exact key 2 h

end GlobalTheory
end

section

open Filter PeriodPair
open scoped Topology Real UpperHalfPlane

noncomputable section

namespace GlobalTheory

theorem lattice_le_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  have hz := L.ω₁_div_two_notMem_lattice
  set z := L.ω₁ / 2
  obtain ⟨w, hw, hw1, hw2⟩ := exists_weierstrassP_eq_and_derivWeierstrassP_eq L' (x := ℘[L] z) (y := ℘'[L] z)
    (by rw [← h₂, ← h₃]; exact L.derivWeierstrassP_sq z hz)
  obtain ⟨c, rfl⟩ : ∃ c, w = z + c := ⟨w - z, by ring⟩
  have h1 := eventuallyEq_of_weierstrass_system
    (weierstrass_system_add_const L 0 (z := z) (by simpa using hz))
    (h₂ ▸ weierstrass_system_add_const L' c hw) (by simp [hw1]) (by simp [hw2])
  have h2 := eqOn_compl_of_countable
    ((countable_add_mem_periodLattice L 0).union (countable_add_mem_periodLattice L' c))
    (fun t ht ↦ analyticAt_weierstrassP_add L 0 fun h ↦ ht (.inl h))
    (fun t ht ↦ analyticAt_weierstrassP_add L' c fun h ↦ ht (.inr h))
    (z := z) (by rintro (h | h); exacts [hz (by simpa using h), hw h]) h1
  have key : ∀ l ∈ L.lattice, l + c ∈ L'.lattice := fun l hl ↦ by
    by_contra h0
    refine not_eventually_weierstrassP_eq L hl
      (analyticAt_weierstrassP_add L' c h0).continuousAt ?_
    filter_upwards [eventually_ne_notMem_periodLattice L l, mem_nhdsWithin_of_mem_nhds
      ((continuous_add_const c).continuousAt.eventually
        (eventually_notMem_periodLattice L' h0))] with t h3 h4
    simpa using h2 (x := t) (by rintro (h | h); exacts [h3 (by simpa using h), h4 h])
  intro l hl
  simpa using sub_mem (key l hl) (key 0 (zero_mem _))

theorem lattice_eq_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_g₂_eq_of_g₃_eq h₂ h₃) (lattice_le_of_g₂_eq_of_g₃_eq h₂.symm h₃.symm)

theorem g₂_cube_sub_g₃_sq_ne_zero (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 :=
  latticeCurve_Δ L ▸ latticeCurve_Δ_ne_zero L

theorem IsHomothetic.g₂_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    L'.g₂ = (c ^ 4)⁻¹ * L.g₂ := by
  rw [g₂, g₂, h.G_eq]; ring

theorem IsHomothetic.g₃_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    L'.g₃ = (c ^ 6)⁻¹ * L.g₃ := by
  rw [g₃, g₃, h.G_eq]; ring

theorem exists_scale_of_j_eq {a b a' b' : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0)
    (h' : a' ^ 3 - 27 * b' ^ 2 ≠ 0)
    (e : a ^ 3 * (a' ^ 3 - 27 * b' ^ 2) = a' ^ 3 * (a ^ 3 - 27 * b ^ 2)) :
    ∃ u : ℂ, u ≠ 0 ∧ a' = u ^ 2 * a ∧ b' = u ^ 3 * b := by
  have e' : a ^ 3 * b' ^ 2 = a' ^ 3 * b ^ 2 := by linear_combination -e / 27
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by rintro rfl; simp at h
    have ha' : a' = 0 := by simpa [hb] using e'
    subst ha'
    have hb' : b' ≠ 0 := by rintro rfl; simp at h'
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (b' / b) (n := 3) (by norm_num)
    refine ⟨u, ?_, by simp, by rw [hu]; field_simp⟩
    rintro rfl
    exact div_ne_zero hb' hb (by simpa using hu.symm)
  by_cases hb : b = 0
  · subst hb
    have hb' : b' = 0 := by simpa [ha] using e'
    subst hb'
    have ha' : a' ≠ 0 := by rintro rfl; simp at h'
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a' / a) (n := 2) (by norm_num)
    refine ⟨u, ?_, by rw [hu]; field_simp, by simp⟩
    rintro rfl
    exact div_ne_zero ha' ha (by simpa using hu.symm)
  have ha' : a' ≠ 0 := by
    rintro rfl
    have : b' = 0 := by simpa [ha] using e'
    simp [this] at h'
  have hb' : b' ≠ 0 := by
    rintro rfl
    simp [ha', hb] at e'
  refine ⟨b' * a / (b * a'), by simp [*], ?_, ?_⟩
  · field_simp
    linear_combination -e'
  · field_simp
    linear_combination -e'

theorem exists_isHomothetic_of_j_eq {L L' : PeriodPair}
    (e : L.g₂ ^ 3 * (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L'.g₂ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) :
    ∃ c : ℂ, IsHomothetic c L L' := by
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq (g₂_cube_sub_g₃_sq_ne_zero L)
    (g₂_cube_sub_g₃_sq_ne_zero L') e
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  have : (scalePeriods L c hc0).lattice = L'.lattice := by
    refine lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_
    · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
    · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp
  exact ⟨c, fun x ↦ this ▸ H x⟩

theorem lattice_determined_by_invariants (L L' : PeriodPair) :
    (L.g₂ = L'.g₂ → L.g₃ = L'.g₃ → L.lattice = L'.lattice) ∧
    (L.g₂ ^ 3 * (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) = L'.g₂ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ w ∈ L.lattice, z = c * w) := by
  refine ⟨lattice_eq_of_g₂_eq_of_g₃_eq, fun e ↦ ?_⟩
  obtain ⟨c, h⟩ := exists_isHomothetic_of_j_eq e
  refine ⟨c, h.ne_zero, fun z ↦ ⟨fun hz ↦ ⟨c⁻¹ * z, (h _).1 (by simpa [h.ne_zero] using hz),
    by simp [h.ne_zero]⟩, ?_⟩⟩
  rintro ⟨w, hw, rfl⟩
  exact (h w).2 hw

section

variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

theorem g₂_cube_sub_g₃_sq_eq_discriminant :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π / a) ^ 12 * ModularForm.discriminant τ := by
  rw [← latticeCurve_Δ, latticeCurve_Δ_eq_discriminant ha h]

theorem g₂_cube_sub_g₃_sq_eq_eta :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π / a) ^ 12 * ModularForm.eta τ ^ 24 :=
  g₂_cube_sub_g₃_sq_eq_discriminant ha h

theorem g₂_cube_div_eq_modularJ :
    1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = modularJ τ := by
  rw [modularJ_def, ← latticeCurve_j ha h, WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', latticeCurve_Δ, latticeCurve_c₄]
  ring

end

theorem mem_lattice_iff_of_periods_eq {L : PeriodPair} {τ : ℍ}
    (h : (L.ω₁ = 1 ∧ L.ω₂ = τ) ∨ (L.ω₁ = τ ∧ L.ω₂ = 1)) (x : ℂ) :
    x ∈ L.lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by
  rw [mem_lattice]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · constructor <;> rintro ⟨m, n, rfl⟩ <;> exact ⟨n, m, by ring⟩
  · simp

theorem invariants_of_periods_eq {L : PeriodPair} {τ : ℍ}
    (h : (L.ω₁ = 1 ∧ L.ω₂ = τ) ∨ (L.ω₁ = τ ∧ L.ω₂ = 1)) :
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π) ^ 12 * ModularForm.discriminant τ ∧
    L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = (2 * π) ^ 12 * ModularForm.eta τ ^ 24 ∧
    1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = modularJ τ :=
  ⟨by simpa using g₂_cube_sub_g₃_sq_eq_discriminant one_ne_zero (mem_lattice_iff_of_periods_eq h),
    by simpa using g₂_cube_sub_g₃_sq_eq_eta one_ne_zero (mem_lattice_iff_of_periods_eq h),
    g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_iff_of_periods_eq h)⟩

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

variable {K : Type} [Field K] [NumberField K]

theorem isLocGen_iff_valuation_eq (p : HeightOneSpectrum (𝓞 K)) (c : K) (I : FractionalIdeal (𝓞 K)⁰ K) :
    IsLocGen p c I ↔ p.valuation K c = exp (-FractionalIdeal.count K p I) := by
  constructor
  · rintro ⟨h0, h⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, h]
  · intro h
    have h0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact exp_ne_zero h.symm
    refine ⟨h0, ?_⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, exp_inj] at h
    exact neg_injective h

theorem valuation_le_iff_exists_smul_mem (p : HeightOneSpectrum (𝓞 K)) {I : FractionalIdeal (𝓞 K)⁰ K}
    (hI : I ≠ 0) (c : K) :
    p.valuation K c ≤ exp (-FractionalIdeal.count K p I) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I := by
  constructor
  · intro h
    obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    have hvy : p.valuation K y ≠ 0 := by rw [hv]; exact exp_ne_zero
    have hy0 : y ≠ 0 := by rintro rfl; simp at hvy
    have h1 : p.valuation K (c / y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvy), hv]; exact h
    obtain ⟨a, s, hs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p (c / y) h1
    refine ⟨s.1, s.2, ?_⟩
    have : (s.1 : 𝓞 K) • c = a • y := by
      rw [Algebra.smul_def, Algebra.smul_def, ← hs]
      field_simp
    rw [this]
    exact Submodule.smul_mem (I : Submodule (𝓞 K) K) a hy
  · rintro ⟨s, hs, hc⟩
    have h := (GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hc p
    have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
      exact (p.valuation_lt_one_iff_mem s).1 hlt
    rwa [Algebra.smul_def, map_mul, h1, one_mul] at h

theorem mem_iff_forall_exists_smul_mem {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (Λ : Submodule (𝓞 K) V) (z : V) :
    z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  constructor
  · intro hz p
    exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hz⟩
  · intro h
    let A : Ideal (𝓞 K) := Λ.comap (LinearMap.toSpanSingleton (𝓞 K) V z)
    have hA : A = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hAm⟩ := Ideal.exists_le_maximal A hne
      have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
      obtain ⟨s, hs, hsz⟩ := h ⟨m, hm.isPrime, hm0⟩
      exact hs (hAm (by simpa [A] using hsz))
    have : (1 : 𝓞 K) ∈ A := hA ▸ Submodule.mem_top
    simpa [A] using this

theorem local_global_ideal_lattice : ∀ (K : Type) [Field K] [NumberField K],
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (cl : HeightOneSpectrum (𝓞 K) → K), I ≠ 0 →
      (∀ p, IsLocGen p (cl p) I) → ∀ c : K,
        c ∈ I ↔ ∀ p : HeightOneSpectrum (𝓞 K), p.valuation K c ≤ p.valuation K (cl p)) ∧
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (p : HeightOneSpectrum (𝓞 K)), I ≠ 0 →
      (∃ cl ∈ I, IsLocGen p cl I) ∧ ∀ cl, IsLocGen p cl I ↔ cl ≠ 0 ∧ ∀ c : K,
        p.valuation K c ≤ p.valuation K cl ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I) ∧
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 K) V] (Λ : Submodule (𝓞 K) V) (z : V),
      z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  intro K _ _
  refine ⟨fun I cl hI hcl c => ?_, fun I p hI => ⟨?_, fun cl => ?_⟩,
    fun V _ _ Λ z => mem_iff_forall_exists_smul_mem Λ z⟩
  · rw [GlobalTheory.Idele.mem_iff_valuation_le hI]
    refine forall_congr' fun p => ?_
    rw [(isLocGen_iff_valuation_eq p _ I).1 (hcl p)]
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    exact ⟨y, hy, (isLocGen_iff_valuation_eq p y I).2 hv⟩
  · constructor
    · intro h
      refine ⟨h.1, fun c => ?_⟩
      rw [(isLocGen_iff_valuation_eq p _ I).1 h]
      exact valuation_le_iff_exists_smul_mem p hI c
    · rintro ⟨-, h⟩
      obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
      refine (isLocGen_iff_valuation_eq p cl I).2 (le_antisymm ?_ ?_)
      · exact (valuation_le_iff_exists_smul_mem p hI cl).2 ((h cl).1 le_rfl)
      · rw [← hv]
        exact (h y).2 ((valuation_le_iff_exists_smul_mem p hI y).1 hv.le)

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.OntoSurj

theorem surjective_of_points {R K : Type} [CommRing R] [Field K] [IsAlgClosed K] (σ : R →+* K)
    (hσ : Function.Injective σ) {P A : Scheme.{0}} (a : A ⟶ Sp R) [LocallyOfFiniteType a]
    (ha : IsOpenMap a) (ψ : P ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by
  have hd : Dense (Set.range (spMap σ)) := by
    have : DenseRange (PrimeSpectrum.comap σ) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot σ).mp hσ]
      exact bot_le
    exact this
  have hJ : JacobsonSpace ↥(pullback a (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd a (spMap σ))
  have hZ : IsClosed ((pullback.fst a (spMap σ)) ⁻¹' Set.range ψ) :=
    hψ.preimage (pullback.fst a (spMap σ)).continuous
  have hsub : closedPoints ↥(pullback a (spMap σ)) ⊆
      (pullback.fst a (spMap σ)) ⁻¹' Set.range ψ := by
    intro z hz
    replace hz : IsClosed {z} := hz
    obtain ⟨p, hp⟩ := h (pointOfClosedPoint (pullback.snd a (spMap σ)) z hz ≫ pullback.fst _ _)
      (by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc])
    obtain ⟨w⟩ : Nonempty ↥(Sp K) := inferInstance
    refine ⟨p w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  have hsub' : a ⁻¹' Set.range (spMap σ) ⊆ Set.range ψ := by
    rw [← Scheme.Pullback.range_fst]
    rintro _ ⟨z, rfl⟩
    exact hall (Set.mem_univ z)
  have hall' := closure_minimal hsub' hψ
  rw [(hd.preimage ha).closure_eq] at hall'
  exact ⟨fun y ↦ hall' (Set.mem_univ y)⟩

theorem surjective_of_onto_complex_points :
    ∀ (R : Type) [CommRing R] [IsDomain R] (σ : R →+* ℂ), Function.Injective σ → ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (Φ : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → (∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Over.mk (spMap σ) ⟶ B, y = x ≫ Φ) → Surjective Φ.left ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ A), ∃ x : Over.mk t ⟶ B, y = x ≫ Φ := by
  intro R _ _ σ hσ A B _ _ Φ hA hB h
  have := hB.proper
  have := hA.proper
  have := hA.smooth
  have hpr : IsProper Φ.left := by
    have : IsProper (Φ.left ≫ A.hom) := by rwa [Over.w]
    exact IsProper.of_comp Φ.left A.hom
  have hs : Surjective Φ.left := by
    refine surjective_of_points σ hσ A.hom A.hom.isOpenMap Φ.left
      Φ.left.isClosedMap.isClosed_range fun y hy ↦ ?_
    obtain ⟨p, hp⟩ := h (Over.homMk y hy)
    exact ⟨p.left, congrArg (·.left) hp⟩
  refine ⟨hs, fun k _ _ t y ↦ ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end GlobalTheory.OntoSurj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem surjective_of_generic_fibre_subset_range
    {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp V) [UniversallyClosed f] [Flat g]
    (h : ∀ y : Y, g y ∈ Set.range (spMap (algebraMap V K)) → y ∈ Set.range f) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  let e : Sp V := (⊥ : PrimeSpectrum V)
  have hη : e ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum V))
  obtain ⟨y', hy', hy''⟩ := Flat.generalizingMap g hη
  refine hy'.mem_closed hcl (h y' ?_)
  rw [hy'']
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V K) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)

theorem isAbelianScheme_of_generically_surjective :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (B G : Over (Sp V)) [GrpObj B] [GrpObj G],
      IsAbelianScheme B → IsSemiAbelian G → ∀ ψ : B ⟶ G,
      (∀ x : G.left, G.hom x ∈ Set.range (spMap (algebraMap V K)) → x ∈ Set.range ψ.left) →
      IsAbelianScheme G := by
  intro V K _ _ _ _ _ _ B G _ _ hB hG ψ h
  have := hB.proper
  have := hG.smooth
  have := hG.separated
  have hw : ψ.left ≫ G.hom = B.hom := Over.w ψ
  have : IsProper (ψ.left ≫ G.hom) := hw ▸ hB.proper
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have : Surjective ψ.left := surjective_of_generic_fibre_subset_range ψ.left G.hom h
  have : UniversallyClosed G.hom := UniversallyClosed.of_comp_surjective ψ.left G.hom
  exact ⟨hG.comm, hG.smooth, ⟨⟩, hG.geomConnected⟩

end GlobalTheory
end
