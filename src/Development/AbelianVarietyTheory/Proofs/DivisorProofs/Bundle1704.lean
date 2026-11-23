module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
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
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → ∀ (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (m m' : ℕ) T T', IsMix p m T → IsMix q m' T' → ∀ d : ℕ, d ≤ m → d ≤ m' → ∀ (L : Fin d → HermLB p) (L' : Fin d → HermLB q), (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ y : Y, HasDim y d → T d L (i y) = T' d L' y := by
  first | exact @GlobalTheory.MixHt.eq_of_isMix | exact GlobalTheory.MixHt.eq_of_isMix | (intros; apply GlobalTheory.MixHt.eq_of_isMix <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.minpoly_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1), f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ), ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  first | (exact @GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (exact GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (intros; apply GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.p_adic_denominator_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (h₂ : Gr G 1), ∃ k : ℕ, ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization p ≤ k) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization p ≤ k := by
  first | (exact @GlobalTheory.AtP.main) | (exact GlobalTheory.AtP.main) | (intros; apply GlobalTheory.AtP.main <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.fixed_vector_squared_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (i j : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ K * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKCx.entries_sq_le_of_fixL) | (exact GlobalTheory.LKCx.entries_sq_le_of_fixL) | (intros; apply GlobalTheory.LKCx.entries_sq_le_of_fixL  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinPtsAway

theorem supp_compact (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f g ≠ 0 → g ∈ Q := by
  obtain ⟨-, -, -, S, hS⟩ := hf
  refine ⟨⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · exact S.isCompact_biUnion fun s _ => (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_iUnion₂.2 ⟨s, hs, (k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

theorem coeff_continuous (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) :
    Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k :=
  GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP p G k

theorem bdd_at_places (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ :=
  GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators p Q hQ

theorem rat_of_integral_away (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : ∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z :=
  GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away p q hq

theorem bdd_denom (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Q → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * q = z := by
  obtain ⟨D, hD, hQD⟩ := bdd_at_places p Q hQ
  refine ⟨D, hD, fun q hq => ?_⟩
  obtain ⟨m, z, hz⟩ := rat_of_integral_away p (D * q) fun v => by
    have := hQD _ hq v
    rwa [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, (AfP.eval v).commutes] at this
  exact ⟨m, z, by rw [← hz, mul_assoc]⟩

theorem charpoly_conj_tmul (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (A : Type) [CommRing A]
    [Algebra ℚ A] (y : C) (u : (A ⊗[ℚ] C)ˣ) :
    LinearMap.charpoly (LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C))) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ A) := by
  let e : (A ⊗[ℚ] C) ≃ₗ[A] (A ⊗[ℚ] C) :=
    { LinearMap.mulLeft A (u : A ⊗[ℚ] C) with
      invFun := fun z => ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C) * z
      left_inv := fun z => by simp [← mul_assoc]
      right_inv := fun z => by simp [← mul_assoc] }
  have h1 : LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C)) =
      e.conj (LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y)) := by
    ext z
    simp [e, LinearEquiv.conj_apply, mul_assoc]
  have h2 : LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y) = (LinearMap.mulLeft ℚ y).baseChange A := by
    ext c
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h1, LinearEquiv.charpoly_conj, h2, LinearMap.charpoly_baseChange]

theorem integral_of_charpoly (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (y : C) (p D : ℕ)
    (h : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).coeff i = z) :
    ∃ m : ℕ, IsIntegral ℤ ((p : C) ^ m * D * y) := by
  choose m z hz using h
  set χ := LinearMap.charpoly (LinearMap.mulLeft ℚ y) with hχ
  set N := χ.natDegree
  set M := ∑ i ∈ Finset.range N, m i
  refine ⟨M, ?_⟩
  set s : ℚ := (p : ℚ) ^ M * D with hs
  have hχy : Polynomial.aeval y χ = 0 := by
    have e := LinearMap.aeval_self_charpoly (LinearMap.mulLeft ℚ y)
    have e2 : Polynomial.aeval (LinearMap.mulLeft ℚ y) χ = Algebra.lmul ℚ C (Polynomial.aeval y χ) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [e2] at e
    have := congrArg (fun f : Module.End ℚ C => f 1) e
    simpa using this
  have hlift : χ.scaleRoots s ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i N with hi | hi | hi
    · have hmi : m i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_range.2 hi)
      refine ⟨(p : ℤ) ^ (M - m i) * z i * ((p : ℤ) ^ M * D) ^ (N - i - 1), ?_⟩
      have e1 : s ^ (N - i) = s * s ^ (N - i - 1) := by
        rw [← pow_succ']; congr 1; omega
      have e2 : s * χ.coeff i = (p : ℚ) ^ (M - m i) * z i := by
        rw [← hz i, hs, ← mul_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmi]
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [e1, ← mul_assoc, mul_comm (χ.coeff i) s, e2, hs]
    · subst hi
      refine ⟨1, ?_⟩
      rw [Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, LinearMap.charpoly_monic]; simp
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]; simp
  obtain ⟨P, hP, hPdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    ((Polynomial.monic_scaleRoots_iff s).2 (LinearMap.charpoly_monic _))
  refine ⟨P, hPm, ?_⟩
  have e3 : Polynomial.eval₂ (algebraMap ℤ C) ((p : C) ^ M * D * y) P =
      Polynomial.aeval ((p : C) ^ M * D * y) (χ.scaleRoots s) := by
    rw [← hP, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
  rw [e3, Polynomial.aeval_def]
  have e4 : (p : C) ^ M * D * y = algebraMap ℚ C s * y := by
    rw [hs]; simp
  rw [e4, Polynomial.scaleRoots_eval₂_mul_of_commute _ _ _ (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _),
    ← Polynomial.aeval_def, hχy, mul_zero]

theorem minpoly_coeff_integral (F : Type) [Field F] (S : Type) [Ring S] [Algebra F S] (y : S) (c : F)
    (hc : IsIntegral ℤ (algebraMap F S c * y)) (hy : IsIntegral F y) (k : ℕ) :
    IsIntegral ℤ (c ^ ((minpoly F y).natDegree - k) * (minpoly F y).coeff k) := by
  by_cases hc0 : c = 0
  · subst hc0
    rcases lt_trichotomy k (minpoly F y).natDegree with hk | hk | hk
    · rw [zero_pow (by omega), zero_mul]; exact isIntegral_zero
    · rw [hk, Nat.sub_self, pow_zero, one_mul, ← Polynomial.leadingCoeff, minpoly.monic hy, ]; exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, mul_zero]; exact isIntegral_zero
  obtain ⟨P, hPm, hP⟩ := hc
  set Pm := P.map (algebraMap ℤ F)
  have hPz : Polynomial.eval₂ (algebraMap F S) (algebraMap F S c * y) Pm = 0 := by
    rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]; exact hP
  have h1 : Polynomial.aeval y (Pm.scaleRoots c⁻¹) = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul_of_commute (p := Pm) (algebraMap F S) (algebraMap F S c * y) c⁻¹
      (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _)
    rw [hPz, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at e
    rw [Polynomial.aeval_def]; exact e
  have h2 : minpoly F y ∣ Pm.scaleRoots c⁻¹ := minpoly.dvd F y h1
  have h3 : (minpoly F y).scaleRoots c ∣ Pm := by
    have := Polynomial.scaleRoots_dvd _ _ (r := c) h2
    rwa [← Polynomial.scaleRoots_mul, inv_mul_cancel₀ hc0, Polynomial.scaleRoots_one] at this
  have h4 := Polynomial.isIntegral_coeff_of_dvd P _ hPm ((Polynomial.monic_scaleRoots_iff c).2 (minpoly.monic hy)) h3 k
  rw [Polynomial.coeff_scaleRoots, mul_comm] at h4
  exact h4

theorem exists_den_minpoly_coeff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ D : ℕ, 0 < D ∧ ∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → ∀ k : ℕ, ∃ m : ℕ, IsIntegral ℤ ((p : G.F) ^ m * D * (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k) := by
  intro p _ G L f hf β x t hx
  obtain ⟨Q, hQc, hQ⟩ := supp_compact p G L f hf
  set N := Module.finrank ℚ G.C
  let cf : ℕ → G.GAf → AfP p := fun k g => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k
  have hQ'c : IsCompact (⋃ k ∈ Finset.range (N + 1), cf k '' Q) :=
    (Finset.range (N + 1)).isCompact_biUnion fun k _ => hQc.image (coeff_continuous p G k)
  obtain ⟨D', hD'0, hD'⟩ := bdd_denom p _ hQ'c
  refine ⟨D' ^ Module.finrank G.F G.C, pow_pos hD'0 _, ?_⟩
  intro y h hfy k
  set yc : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyc
  have hg := hQ _ hfy

  set u : (AfP p ⊗[ℚ] G.C)ˣ := ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * x with hu
  have hrep : ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) =
      (u : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] yc) * ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    have e : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
        u * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * u⁻¹ := by
      have e0 : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
          ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹) *
            (h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 := rfl
      rw [e0, hu]; group
    rw [e]; simp only [Units.val_mul]; rfl
  have hchar : LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).map (algebraMap ℚ (AfP p)) := by
    rw [hrep]; exact charpoly_conj_tmul G.C (AfP p) yc u
  have hcoef : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D' * (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).coeff i = z := by
    intro i
    by_cases hi : i ≤ N
    · apply hD'
      refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), _, hg, ?_⟩
      simp only [cf]
      rw [hchar, Polynomial.coeff_map]
    · refine ⟨0, 0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
      simp
  obtain ⟨M, hM⟩ := integral_of_charpoly G.C yc p D' hcoef
  have hint : IsIntegral ℤ (algebraMap G.F G.C ((p : G.F) ^ M * D') * yc) := by
    convert hM using 2
    simp [map_mul, map_pow, map_natCast]
  have hI := minpoly_coeff_integral G.F G.C yc _ hint (Algebra.IsIntegral.isIntegral _) k
  set d := (minpoly G.F yc).natDegree
  have hd : d ≤ Module.finrank G.F G.C := minpoly.natDegree_le yc
  by_cases hk : k ≤ d
  · refine ⟨M * (d - k), ?_⟩
    have e : (p : G.F) ^ (M * (d - k)) * ((D' ^ Module.finrank G.F G.C : ℕ) : G.F) * (minpoly G.F yc).coeff k =
        (D' : G.F) ^ (Module.finrank G.F G.C - (d - k)) *
          (((p : G.F) ^ M * D') ^ (d - k) * (minpoly G.F yc).coeff k) := by
      rw [mul_pow, ← pow_mul, Nat.cast_pow]
      have : Module.finrank G.F G.C = (Module.finrank G.F G.C - (d - k)) + (d - k) := by omega
      conv_lhs => rw [this, pow_add]
      ring
    rw [e]
    have hD : IsIntegral ℤ (D' : G.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ G.F (D' : ℤ)))
    exact (hD.pow _).mul hI
  · refine ⟨0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
    exact isIntegral_zero

end GlobalTheory.FinPtsAway
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.TermPair

theorem finsum_dc_translate {H : Type} [Group H] (A B K : Subgroup H) (u : H)
    (hAB : B = A.map (MulAut.conj u).toMonoidHom) (S₁ S₂ : H → ℂ)
    (hS₂ : ∀ b ∈ B, ∀ k ∈ K, ∀ h, S₂ (b * h * k) = S₂ h) (h12 : ∀ h, S₁ h = S₂ (u * h)) :
    ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (K : Set H), S₁ (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (B : Set H) (K : Set H), S₂ (Quotient.out q) := by
  have memB : ∀ a, a ∈ A → u * a * u⁻¹ ∈ B := fun a ha => by
    rw [hAB]; exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have memA : ∀ b, b ∈ B → u⁻¹ * b * u ∈ A := fun b hb => by
    rw [hAB] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simpa [MulAut.conj_apply, mul_assoc] using ha
  let e : DoubleCoset.Quotient (A : Set H) (K : Set H) ≃ DoubleCoset.Quotient (B : Set H) (K : Set H) :=
    { toFun := Quotient.map' (u * ·) (fun x y hxy => by
        obtain ⟨a, ha, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u * a * u⁻¹, memB a ha, k, hk, by group⟩)
      invFun := Quotient.map' (u⁻¹ * ·) (fun x y hxy => by
        obtain ⟨b, hb, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 hxy
        exact DoubleCoset.rel_iff.2 ⟨u⁻¹ * b * u, memA b hb, k, hk, by group⟩)
      left_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl
      right_inv := fun q => by
        induction q using Quotient.inductionOn' with
        | h x =>
          simp only [Quotient.map'_mk'', inv_mul_cancel_left, mul_inv_cancel_left]
          rfl }
  have hF : ∀ x y : H, DoubleCoset.mk B K x = DoubleCoset.mk B K y → S₂ x = S₂ y := fun x y hxy => by
    obtain ⟨b, hb, k, hk, rfl⟩ := (@DoubleCoset.eq _ _ B K x y).1 hxy
    exact (hS₂ b hb k hk x).symm
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  rw [h12]
  apply hF
  rw [DoubleCoset.out_eq']
  conv_rhs => rw [← DoubleCoset.out_eq' q]
  rfl

theorem card_eq_of_conj {Γ : Type} [Group Γ] (S T : Subgroup Γ) (v : Γ) (h : ∀ w, w ∈ T ↔ v⁻¹ * w * v ∈ S) :
    Nat.card T = Nat.card S :=
  Nat.card_congr
    { toFun := fun w => ⟨v⁻¹ * w * v, (h w).1 w.2⟩
      invFun := fun w => ⟨v * w * v⁻¹, (h _).2 (by simpa [mul_assoc] using w.2)⟩
      left_inv := fun w => by ext; simp [mul_assoc]
      right_inv := fun w => by ext; simp [mul_assoc] }

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

theorem mem_map_conj {H : Type} [Group H] (K : Subgroup H) (a x : H) :
    x ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ K := by
  rw [Subgroup.mem_map_equiv]; simp [MulAut.conj_symm_apply]

theorem conj_mem_iff {H : Type} [Group H] (K : Subgroup H) (a h k y : H) (hk : k ∈ K) :
    (a * h * k)⁻¹ * y * (a * h * k) ∈ K ↔ h⁻¹ * (a⁻¹ * y * a) * h ∈ K := by
  have e : (a * h * k)⁻¹ * y * (a * h * k) = k⁻¹ * (h⁻¹ * (a⁻¹ * y * a) * h) * k := by group
  rw [e, K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem cent_le_grp (P : DPair G) : P.cent ≤ GlobalTheory.LKCx.grp G P.β := fun y hy =>
  ⟨hy.2, DFormPos.sim_pos p G (DForm.ofDPair P) y.1 y.2 hy.2⟩

theorem centralizer_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) :
    Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
      (Subgroup.inclusion (cent_le_grp P)).range := by
  ext v
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range]
  constructor
  · intro h
    have h' := congrArg (fun w : GlobalTheory.LKCx.grp G P.β => (w : G.Cˣ × ℚˣ).1) h
    simp only [Subgroup.coe_mul, Prod.fst_mul] at h'
    exact ⟨⟨v, h', v.2.1⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    exact Prod.ext w.2.1 (mul_comm _ _)

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair
variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem termAt_eq (P : DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G 1)
    (hδ : IsNrm G 1 P.atP δ z) :
    P.termAt Kf f 1 K' f' x t hx δ z =
      centSum (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) Kf K' 1 f f'
        ⟨(P.γ, P.c), hm⟩ := by
  have hδ' : δ = z⁻¹ * inclG G 1 P.atP * z := by simpa [IsNrm, nrmG] using hδ
  have hle := cent_le_grp P
  have e1 : ∀ w, GlobalTheory.LKCx.toAfF G P.β x t hx (Subgroup.inclusion hle w) = P.toAf x t hx w := fun w => rfl
  have e2 : ∀ w, P.toQr 1 z w = z⁻¹ * GlobalTheory.LKCx.toP1 G P.β (Subgroup.inclusion hle w) * z := fun w => by
    simp [DPair.toQr, GlobalTheory.LKCx.toP1, carry, MulAut.conj_apply]
  have eg : Subgroup.inclusion hle P.self = ⟨(P.γ, P.c), hm⟩ := rfl
  have hj2g : GlobalTheory.LKCx.toP1 G P.β ⟨(P.γ, P.c), hm⟩ = inclG G 1 P.atP := rfl
  have hC := centralizer_eq P hm
  unfold DPair.termAt pointSum centSum
  refine finsum_dc_translate ((P.toAf x t hx).prod (P.toQr 1 z)).range
    ((Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)}).map
      ((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β))) (Kf.prod K') ((1 : G.GAf), z) ?_
    (fun h => ((Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) : ℕ) : ℂ)⁻¹ *
      (f (h.1⁻¹ * (P.toAf x t hx) P.self * h.1) * f' (h.2⁻¹ * δ * (sigG G 1) h.2)))
    (fun h => ((Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓
      Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) : ℕ) : ℂ)⁻¹ *
      term (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) 1 f f' h
        ⟨(P.γ, P.c), hm⟩) ?_ ?_
  · rw [hC, MonoidHom.map_range, MonoidHom.map_range]
    refine congrArg MonoidHom.range (MonoidHom.ext fun w => ?_)
    refine Prod.ext ?_ ?_
    · simp [MulAut.conj_apply, e1]
    · simp [MulAut.conj_apply, e2]
      group
  · rintro b hb k hk h
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    have hvc : v * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v := Subgroup.mem_centralizer_singleton_iff.1 hv
    have hvg : v⁻¹ * (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * v = (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [mul_assoc, ← hvc, inv_mul_cancel_left]
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((GlobalTheory.LKCx.toAfF G P.β x t hx).prod (GlobalTheory.LKCx.toP1 G P.β)) v * h * k) ⊓
        Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) =
        Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' h ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} : Subgroup _) := by
      refine card_eq_of_conj _ _ v fun w => ?_
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, MonoidHom.prod_apply, Prod.fst_mul,
        Prod.snd_mul]
      rw [conj_mem_iff _ _ _ _ _ hk1, conj_mem_iff _ _ _ _ _ hk2, map_mul, map_mul, map_mul, map_mul, map_inv,
        map_inv]
      have hCv : w ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} ↔ v⁻¹ * w * v ∈ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} := by
        rw [Subgroup.mul_mem_cancel_right _ hv, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hv)]
      rw [hCv]
    have ef : ∀ a y : G.GAf, f ((a * h.1 * k.1)⁻¹ * y * (a * h.1 * k.1)) = f (h.1⁻¹ * (a⁻¹ * y * a) * h.1) :=
      fun a y => by
        rw [← hf k.1 hk1 (h.1⁻¹ * (a⁻¹ * y * a) * h.1)]; congr 1; group
    have ef' : ∀ a y : Gr G 1, f' ((a * h.2 * k.2)⁻¹ * y * (a * h.2 * k.2)) =
        f' (h.2⁻¹ * (a⁻¹ * y * a) * h.2) := fun a y => by
      rw [← hf' k.2 hk2 (h.2⁻¹ * (a⁻¹ * y * a) * h.2)]; congr 1; group
    have g1 : ((GlobalTheory.LKCx.toAfF G P.β x t hx) v)⁻¹ * (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * (GlobalTheory.LKCx.toAfF G P.β x t hx) v = (GlobalTheory.LKCx.toAfF G P.β x t hx) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) := by
      rw [← map_inv, ← map_mul, ← map_mul, hvg]
    have g2 : ((GlobalTheory.LKCx.toP1 G P.β) v)⁻¹ * ((GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1) * (GlobalTheory.LKCx.toP1 G P.β) v = (GlobalTheory.LKCx.toP1 G P.β) (⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β) * 1 := by
      rw [mul_one, ← map_inv, ← map_mul, ← map_mul, hvg]
    beta_reduce
    rw [hcard]
    simp only [term, MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply]
    rw [ef, ef', g1, g2]
  · intro h
    have hmem : ∀ w, Subgroup.inclusion hle w ∈ stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ↔
        w ∈ stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h := fun w => by
      simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, mem_map_conj, Prod.fst_mul, Prod.snd_mul, one_mul, e1, e2]
      have e3 : (z * h.2)⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * (z * h.2) =
          h.2⁻¹ * (z⁻¹ * (GlobalTheory.LKCx.toP1 G P.β) (Subgroup.inclusion hle w) * z) * h.2 := by group
      rw [e3]
    have hsub : stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} =
        (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h).map (Subgroup.inclusion hle) := by
      rw [hC]
      ext v
      simp only [Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map]
      constructor
      · rintro ⟨hv, w, rfl⟩
        exact ⟨w, (hmem w).1 hv, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(hmem w).2 hw, w, rfl⟩
    have hcard : Nat.card (stab (GlobalTheory.LKCx.toAfF G P.β x t hx) (GlobalTheory.LKCx.toP1 G P.β) Kf K' (((1 : G.GAf), z) * h) ⊓ Subgroup.centralizer {(⟨(P.γ, P.c), hm⟩ : GlobalTheory.LKCx.grp G P.β)} :
        Subgroup _) = Nat.card (stab (P.toAf x t hx) (P.toQr 1 z) Kf K' h) := by
      rw [hsub]; exact Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)
    beta_reduce
    rw [hcard]
    simp only [term, Prod.fst_mul, Prod.snd_mul, MonoidHom.id_apply, one_mul, mul_one, GlobalTheory.LKCx.sigG_one]
    rw [← e1 P.self, eg, hδ', ← hj2g]
    congr 3
    group

end GlobalTheory.LKDef.TermPair

namespace GlobalTheory.LKDef.TermPair

theorem term_eq_centSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩ := by
  intro p _ G P hm L f hf K' f' hf'
  have hex : ∃ dz : Gr G 1 × Gr G 1, IsNrm G 1 P.atP dz.1 dz.2 :=
    ⟨(inclG G 1 P.atP, 1), by simp [IsNrm, nrmG]⟩
  unfold DPair.term
  rw [dite_eq_left hex]
  exact termAt_eq P hm _ f (fun k hk g => by simpa using hf.2.2.1 k hk g) K' f'
    (fun k hk g => by simpa [GlobalTheory.LKCx.sigG_one] using hf'.2.2.1 k hk g) _ _ _ _ _ hex.choose_spec

end GlobalTheory.LKDef.TermPair
end
