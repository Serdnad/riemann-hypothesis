module

import ReciprocityTheory.SemistableReduction.Bundle018
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdele
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSmulMemOfMemSpanFraction
public import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

namespace GlobalTheory.SmulMemSpanTop

open NumberField

theorem exists_smul_mem_of_span_eq_top {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  apply ReciprocityTheory.MultiplicativeHeights.sc_scale <;> assumption

end GlobalTheory.SmulMemSpanTop
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix

theorem _root_.GlobalTheory.T.exists_integral_unit_root_norm_one_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  first | exact @GlobalTheory.AdLat.exists_integral_unit_root | exact GlobalTheory.AdLat.exists_integral_unit_root | (intros; apply GlobalTheory.AdLat.exists_integral_unit_root <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

theorem hilbert90_involution_of_idempotent_unit {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (u d e s : R) (hu : u * σ u = 1) (hd : σ d = -d) (hdu : IsUnit d) (h2 : IsUnit (2 : R))
    (he : e * e = e) (hσe : σ e = e) (hs : u + σ u = 2 * s)
    (hun : IsUnit (e * (1 + s) + (1 - e) * (1 - s))) :
    ∃ x : Rˣ, (x : R) = u * σ x := by
  obtain ⟨d', hd'⟩ := hdu.exists_right_inv
  have h3 : IsUnit (e - (1 - e) * d ^ 2) := by
    refine IsUnit.of_mul_eq_one (e - (1 - e) * d' ^ 2) ?_
    have h : d ^ 2 * d' ^ 2 = 1 := by rw [← mul_pow, hd', one_pow]
    linear_combination (1 + d ^ 2 + d' ^ 2 + d ^ 2 * d' ^ 2) * he + (1 - e) * h
  have hx : σ (e * (1 + u) + (1 - e) * d * (1 - u)) = e * (1 + σ u) - (1 - e) * d * (1 - σ u) := by
    simp only [map_add (f := _), map_mul, map_sub, map_one, hσe, hd]; ring
  have hN : (e * (1 + u) + (1 - e) * d * (1 - u)) * (e * (1 + σ u) - (1 - e) * d * (1 - σ u)) =
      2 * (e * (1 + s) + (1 - e) * (1 - s)) * (e - (1 - e) * d ^ 2) := by
    have hv : σ u = 2 * s - u := by linear_combination hs
    rw [hv] at hu ⊢
    have h1 : e * (1 - e) = 0 := by linear_combination - he
    have h4 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
    generalize 1 - e = f at h1 h4 ⊢
    linear_combination (e * e - f * f * d ^ 2) * hu +
      (d * ((1 - u) * (1 + (2 * s - u)) - (1 + u) * (1 - (2 * s - u))) + 2 * (1 + s) * d ^ 2 - 2 * (1 - s)) * h1
  have hxu : IsUnit (e * (1 + u) + (1 - e) * d * (1 - u)) :=
    isUnit_of_mul_isUnit_left (hN ▸ (h2.mul hun).mul h3)
  refine ⟨hxu.unit, ?_⟩
  rw [IsUnit.unit_spec, hx]
  linear_combination (- e - (1 - e) * d) * hu

theorem aut_eq_one_or_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (g : E ≃ₐ[F] E) : g = 1 ∨ g = c := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  by_contra hg
  push Not at hg
  obtain ⟨x, -, hx⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact hg.2 ((hx g hg.1).trans (hx c hc).symm)

theorem hilbert90_adeleRing_tensor_quadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → ∀ u : AdeleRing (𝓞 F) F ⊗[F] E, u * sg (AdeleRing (𝓞 F) F) c u = 1 → ∃ x : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, (x : AdeleRing (𝓞 F) F ⊗[F] E) = u * sg (AdeleRing (𝓞 F) F) c (x : AdeleRing (𝓞 F) F ⊗[F] E) := by
  intro F E _ _ _ _ _ c h2 hc u hu
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcc : ∀ x, c (c x) = x := by
    intro x
    rcases aut_eq_one_or_of_finrank_two c h2 hc (c * c) with h | h
    · simpa using congrArg (fun g : E ≃ₐ[F] E => g x) h
    · exact absurd (by simpa using h) hc
  have htr : ∀ x : E, ∃ t : F, x + c x = algebraMap F E t := by
    intro x
    have : x + c x ∈ Set.range (algebraMap F E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro g
      rcases aut_eq_one_or_of_finrank_two c h2 hc g with rfl | rfl
      · rfl
      · rw [map_add (f := _), hcc, add_comm]
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht.symm⟩
  have hsg : ∀ (a : AdeleRing (𝓞 F) F) (x : E), sg (AdeleRing (𝓞 F) F) c (a ⊗ₜ x) = a ⊗ₜ c x := by
    intro a x; simp [sg]
  have hσ : ∀ z, sg (AdeleRing (𝓞 F) F) c (sg (AdeleRing (𝓞 F) F) c z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [hsg, hsg, hcc]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hT : ∀ z, ∃ t : AdeleRing (𝓞 F) F, z + sg (AdeleRing (𝓞 F) F) c z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      rw [hsg, ← TensorProduct.tmul_add, ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  obtain ⟨t, ht⟩ := hT u
  obtain ⟨e, he, hun⟩ := GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele F ((2 : F)⁻¹ • t)
  let ι : AdeleRing (𝓞 F) F →+* AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeLeftRingHom
  have hι : ∀ a, ι a = a ⊗ₜ 1 := fun a => rfl
  let κ : E →ₐ[F] AdeleRing (𝓞 F) F ⊗[F] E := Algebra.TensorProduct.includeRight
  have hκ : ∀ a, κ a = 1 ⊗ₜ a := fun a => rfl
  refine hilbert90_involution_of_idempotent_unit (sg (AdeleRing (𝓞 F) F) c : _ →+* _) hσ u (κ (y - c y)) (ι e)
    (ι ((2 : F)⁻¹ • t)) hu ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change sg _ c _ = _
    rw [← map_neg, hκ, hκ, hsg, map_sub, hcc, neg_sub]
  · exact (IsUnit.mk0 _ (sub_ne_zero.2 hy.symm)).map κ
  · have := (IsUnit.mk0 (2 : E) two_ne_zero).map κ
    rwa [map_ofNat] at this
  · rw [← map_mul, he]
  · change sg _ c _ = _
    rw [hι, hsg, map_one]
  · change u + sg _ c u = _
    rw [ht, two_mul, ← map_add (f := _), ← add_smul, hι]
    norm_num
  · have := hun.map ι
    simpa only [map_add (f := _), map_mul, map_sub, map_one] using this

end GlobalTheory.AdLat
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem herm_comb_eq_zero_of_iso {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (e : Fin ρ → Fin r → E)
    (h : ∀ a b, herm G (e a) (e b) = 0) (u v : Fin ρ → E) :
    herm G (∑ i, u i • e i) (∑ j, v j • e j) = 0 := by
  have key : herm G (∑ i, u i • e i) (∑ j, v j • e j)
      = ∑ i, ∑ j, u i * cc (v j) * herm G (e i) (e j) := by
    have h1 : ∀ (y : Fin r → E), herm G (∑ i, u i • e i) y = ∑ i, u i * herm G (e i) y := by
      intro y
      simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∀ (x : Fin r → E), herm G x (∑ j, v j • e j) = ∑ j, cc (v j) * herm G x (e j) := by
      intro x

      simp only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [h1, h2, Finset.mul_sum, mul_assoc]
  rw [key]
  simp [h]

theorem exists_cusp_pseudoBasis :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu₀ : FJ.CuspFD X ρ), ∃ (cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), IsUnit P.det ∧ (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) ∧ (∀ b, cc' b ≠ 0) ∧ (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) := by
  intro E _ _ _ r ρ X cu₀
  classical
  let T : (Fin ρ → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E cu₀.e
  have hT : ∀ v, T v = ∑ i, v i • cu₀.e i := fun v => Fintype.linearCombination_apply E cu₀.e v
  obtain ⟨Ψ, hΨ⟩ := FJ.exists_crdMap cu₀
  have hinj : Function.Injective T := by
    refine Function.LeftInverse.injective (g := Ψ) fun v => ?_
    rw [hT, hΨ]
  let L : Submodule (𝓞 E) (Fin ρ → E) := X.Λ.comap (T.restrictScalars (𝓞 E))
  have hL : ∀ v, v ∈ L ↔ T v ∈ X.Λ := fun v => Iff.rfl
  have hfg : L.FG := by
    refine Submodule.FG.of_le (X.Λ_fg.map (Ψ.restrictScalars (𝓞 E))) fun v hv => ?_
    refine ⟨T v, (hL v).1 hv, ?_⟩
    show Ψ (T v) = v
    rw [hT, hΨ]
  have hsp : Submodule.span E (L : Set (Fin ρ → E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨c, hc, hcw⟩ := FJ.exists_smul_mem X (T w)
    have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h =>
      hc (IsFractionRing.injective (𝓞 E) E (by rw [map_zero]; exact h))
    have hm : algebraMap (𝓞 E) E c • w ∈ L := by
      rw [hL, map_smul, algebraMap_smul]
      exact hcw
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin ρ → E))) (algebraMap (𝓞 E) E c)⁻¹
      (Submodule.subset_span hm)
    rwa [smul_smul, inv_mul_cancel₀ hcE, one_smul] at this
  obtain ⟨s, e, c, hc, hmem, -⟩ := exists_pseudoBasis_adapted E ρ L ⊤ hfg hsp
  have hsum : ∀ a : Fin ρ → E, ∑ b, a b • T (e b) = T (∑ b, a b • e b) := by
    intro a

    simp only [map_sum, map_smul]
  refine ⟨⟨fun b => T (e b), e.linearIndependent.map' T (LinearMap.ker_eq_bot.2 hinj), ?_⟩,
    (e.toMatrix (Pi.basisFun E (Fin ρ)))ᵀ, c, ?_, ?_, hc, ?_⟩
  · intro a b
    simp only [hT]
    exact herm_comb_eq_zero_of_iso _ _ cu₀.iso _ _
  · rw [Matrix.det_transpose]
    exact e.isUnit_det _
  · intro a
    show cu₀.e a = ∑ b, e.repr (Pi.basisFun E (Fin ρ) a) b • T (e b)
    rw [hsum, e.sum_repr, hT]
    simp [Pi.single_apply]
  · intro a
    show ∑ b, a b • T (e b) ∈ X.Λ ↔ _
    rw [hsum, ← hL, hmem]
    simp only [e.repr_sum_self]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem isOpenImmersion_spMap_of_isDiscreteValuationRing (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] :
    IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away π K := by
    refine IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_)
      (fun a b hab => ⟨0, by simpa using IsFractionRing.injective T K hab⟩)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T) s
    obtain ⟨n, v, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (v⁻¹ : Tˣ), ?_⟩
    have h1 : algebraMap T K π ≠ 0 := by simpa using hπ.ne_zero
    have h2 : algebraMap T K v ≠ 0 := by simp
    simp only [map_mul, map_pow, map_units_inv]
    field_simp
  exact IsOpenImmersion.of_isLocalization π

theorem isIntegral_of_flat_of_isIntegral_genericFibre (T K : Type) [CommRing T] [IsDomain T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [IsIntegral (pullback f (spMap (algebraMap T K)))] : IsIntegral X := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  let g := pullback.fst f (spMap (algebraMap T K))
  have : IsReduced X := IsSchemeTheoreticallyDominant.isReduced g
  have : IsDominant g := inferInstance
  have h : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image g g.continuous.continuousOn).closure
  rw [g.denseRange.closure_range] at h
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem isIso_of_quasiFinite_of_isIso_genericFibre_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (Ga G : Over (Sp T)) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      Flat Ga.hom → IsSeparated p.left → LocallyOfFiniteType p.left → QuasiCompact p.left →
      LocallyQuasiFinite p.left → Smooth G.hom → GeometricallyConnected G.hom →
      IsIso ((Over.pullback (spMap (algebraMap T K))).map p) → IsIso p := by
  intro T K _ _ _ _ _ _ Ga G _ _ p _ _ _ _ _ _ _ _ _
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have hc : ConnectedSpace ((Over.pullback t).obj G).left :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
  obtain ⟨hG, hN⟩ := isIntegral_and_isNormalScheme_of_smooth_dvr T K G ‹_› hc
  let q : pullback Ga.hom t ⟶ pullback G.hom t := ((Over.pullback t).map p).left
  have : IsIso q := inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback t).map p)))
  have e : q ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left := pullback.lift_fst _ _ _
  have : ConnectedSpace ↥(pullback G.hom t) := hc
  have : IsIntegral (pullback G.hom t) := isIntegral_of_isOpenImmersion (pullback.fst G.hom t)
  have : Nonempty ↥(pullback Ga.hom t) := ⟨inv q (Classical.arbitrary _)⟩
  have : IsIntegral (pullback Ga.hom t) := isIntegral_of_isOpenImmersion q
  have : IsIntegral Ga.left := isIntegral_of_flat_of_isIntegral_genericFibre T K Ga.hom
  let j := pullback.fst Ga.hom t
  have : IsOpenImmersion (j.opensRange.ι ≫ p.left) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc, ← e]
    infer_instance
  have : IsOpenImmersion p.left :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict p.left (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact isIso_of_isOpenImmersion_of_geometricallyConnected _ Ga G p ‹_› ‹_› inferInstance ‹_›

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace MulEtaleDvr

variable {S : Scheme.{0}}

theorem mulN_eq_pow (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = 𝟙 G ^ n := by
  rw [← MulUnramified.comp_mulN, Category.id_comp]

theorem isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) := by
  constructor
  · rw [MulUnramified.comp_mulN, one_eq_one, one_pow]
  · simp only [MulUnramified.comp_mulN, MonObj.mul_eq_mul, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd, mul_pow]

theorem pullback_map_mulN {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) :
    (Over.pullback p).map (mulN G n) = mulN ((Over.pullback p).obj G) n := by
  rw [mulN_eq_pow, mulN_eq_pow, ← (Over.pullback p).map_id]
  exact map_pow (Over.pullback p).homMonoidHom _ _

theorem isPullback_torsion (G : Over S) [GrpObj G] (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by
  have h := (IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).left = (torsion G n).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem isUnit_natCast_sections {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) :
    IsUnit (n : Γ(Sp R, ⊤)) := by
  simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom

theorem flat_mulN_field (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : k)) (hG : LocallyOfFiniteType G.hom) : Flat (mulN G n).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) G G _ ?_
  rw [pullback_map_mulN]
  refine flat_of_formallyUnramified_grpEnd _ _ _ ?_ (isMonHom_mulN _ n)
    (formallyUnramified_mulN _ _ n (isUnit_natCast_sections ?_))
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
  · simpa using hn.map (algebraMap k (AlgebraicClosure k))

theorem flat_pullback_mulN {T k : Type} [CommRing T] [Field k] (σ : T →+* k) (G : Over (Sp T))
    [GrpObj G] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : T)) (hG : LocallyOfFiniteType G.hom) :
    Flat ((Over.pullback (spMap σ)).map (mulN G n)).left := by
  rw [pullback_map_mulN]
  refine flat_mulN_field k _ n (by simpa using hn.map σ) ?_
  exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))

end MulEtaleDvr


open MulEtaleDvr in
theorem etale_mulN_torsion_dvr :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G]
      [IsCommMonObj G] (n : ℕ), IsUnit (n : T) → Flat G.hom → LocallyOfFiniteType G.hom →
      Etale (mulN G n).left ∧ Etale (torsion G n).hom := by
  intro T _ _ _ G _ _ n hn hf hG
  have h1 : Flat (mulN G n).left :=
    flat_of_flat_fibres_dvr T (FractionRing T) G G _ hf hf hG hG
      (MulEtaleDvr.flat_pullback_mulN _ G n hn hG) (MulEtaleDvr.flat_pullback_mulN _ G n hn hG)
  have h2 := formallyUnramified_mulN _ G n (MulEtaleDvr.isUnit_natCast_sections hn)
  have h3 : LocallyOfFiniteType ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have h4 := locallyOfFiniteType_of_comp (mulN G n).left G.hom
  have h5 : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have h6 : LocallyOfFinitePresentation (mulN G n).left := inferInstance
  have h : Etale (mulN G n).left := Etale.of_formallyUnramified_of_flat _
  exact ⟨h, MorphismProperty.of_isPullback (P := @Etale) (MulEtaleDvr.isPullback_torsion G n) h⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_valuationSubring_complex_comap_val_eq (F : IntermediateField ℚ ℂ)
    (U : ValuationSubring F) (p : ℕ) (hp : (p : F) ∈ U.nonunits) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ W.comap F.val.toRingHom = U := by
  obtain ⟨W, hW⟩ : ∃ W : ValuationSubring ℂ, W.comap (algebraMap F ℂ) = U :=
    exists_valuationSubring_comap_eq U _
  refine ⟨W, ?_, hW⟩
  rw [ValuationSubring.mem_nonunits_iff_or] at hp ⊢
  rcases hp with h | h
  · left
    simpa using congrArg (algebraMap F ℂ) h
  · right
    rw [← hW, ValuationSubring.mem_comap] at h
    simpa using h

end GlobalTheory
end
