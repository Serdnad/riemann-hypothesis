module

import Development.WeilBound.CoreStatements.FlagImmersions.Bundle004
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianDarbouxSplitProduct
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.WeilBound.CoreStatements.IdealCycleValues.IntNumLComapBaseExtension
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle002
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle006
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

@[expose] public section

section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem combLine_smooth_conj :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  apply RootFieldNumerics.combLine_smooth_conj_invariant <;> assumption

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitian_darboux_split_product : ∀ (k : Type) [Field k] [CharZero k] (R S E₁ E₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [IsArtinianRing E₁] [Algebra k E₁] [CommRing E₂] (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (ξ₁ : E₁) (s : S ≃+* E₁ × E₂), IsUnit ξ₁ → c₁ ξ₁ = -ξ₁ → (∀ x, c₁ (c₁ x) = x) → (∀ x, (s (c x)).1 = c₁ (s x).1) → (∀ x, (s (c x)).2 = c₂ (s x).2) → ∀ (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β S), IsUnit J.det → ∀ lam : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) →* ℂˣ, (∀ (p : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) (t : GL β S), (∀ i j, (s ((((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → (∀ i j, (s (((t : Matrix β β S) - 1) i j)).2 = 0) → ((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) * GlobalTheory.WeilM.diagCols β = GlobalTheory.WeilM.diagCols β * (t : Matrix β β S) → lam p = 1) → ∀ g : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J), (∀ i j, (s ((((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → lam g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RT.CellSplit.char_trivial_first | exact GlobalTheory.CompanionTheory.Ar.RT.CellSplit.char_trivial_first | (intros; apply GlobalTheory.CompanionTheory.Ar.RT.CellSplit.char_trivial_first <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.limit_height_constant_shift : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II → M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) → M.PP II F = M'.PP II F + c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add | exact GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section ChartForms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem isMultiHomog_chartMonomial (d : ∀ k, ι k) :
    IsMultiHomog (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) (fun _ => 1) := by
  have h := IsWeightedHomogeneous.prod (R := ℤ) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, d k⟩ : MRing ι ℤ)) (fun k => blockWeight ι ⟨k, d k⟩)
    (fun k _ => isWeightedHomogeneous_X ℤ _ _)
  have e : (∑ k, blockWeight ι ⟨k, d k⟩) = fun _ : K => 1 := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem isMultiHomog_mul_const {f g : MRing ι ℤ} {a b : ℕ}
    (hf : IsMultiHomog f (fun _ => a)) (hg : IsMultiHomog g (fun _ => b)) :
    IsMultiHomog (f * g) (fun _ => a + b) :=
  IsWeightedHomogeneous.mul hf hg

theorem isMultiHomog_pow_const {f : MRing ι ℤ} (hf : IsMultiHomog f (fun _ => 1)) (n : ℕ) :
    IsMultiHomog (f ^ n) (fun _ => n) := by
  induction n with
  | zero => rw [pow_zero]; exact isWeightedHomogeneous_one ℤ (blockWeight ι)
  | succ n ih => rw [pow_succ]; exact isMultiHomog_mul_const ih hf

theorem pointConeMap_chartMonomial (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) :
    pointConeMap ℤ y (∏ k, X ⟨k, d k⟩ : MRing ι ℤ) =
      C (segreVec y d) * ∏ k : K, (X k : MvPolynomial K Ω) := by
  simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]

theorem exists_form_of_mem_chart (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hs : segreVec y c ≠ 0)
    {r : Ω} (hr : r ∈ chartRing ℤ (segreVec y) c) :
    ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧
      pointConeMap ℤ y G = C (r * segreVec y c ^ n) * (∏ k : K, (X k : MvPolynomial K Ω)) ^ n := by
  set T : MvPolynomial K Ω := ∏ k : K, (X k : MvPolynomial K Ω) with hT
  set s : Ω := segreVec y c with hsdef
  set M : MRing ι ℤ := ∏ k, X ⟨k, c k⟩ with hM
  have hMh : IsMultiHomog M (fun _ => 1) := isMultiHomog_chartMonomial c
  have hMc : pointConeMap ℤ y M = C s * T := pointConeMap_chartMonomial y c
  unfold chartRing at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    refine ⟨1, ∏ k, X ⟨k, d k⟩, isMultiHomog_chartMonomial d, ?_⟩
    rw [pointConeMap_chartMonomial, pow_one, pow_one, div_mul_cancel₀ _ hs]
  | algebraMap z =>
    refine ⟨0, C z, ?_, ?_⟩
    · exact isWeightedHomogeneous_C (blockWeight ι) z
    · have h1 : (C z : MRing ι ℤ) = algebraMap ℤ (MRing ι ℤ) z := rfl
      rw [h1, AlgHom.commutes]
      simp [MvPolynomial.algebraMap_eq]
  | add u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * M ^ b + G * M ^ a, ?_, ?_⟩
    · have h1 := isMultiHomog_mul_const hF (isMultiHomog_pow_const hMh b)
      have h2 := isMultiHomog_mul_const hG (isMultiHomog_pow_const hMh a)
      rw [add_comm b a] at h2
      exact IsWeightedHomogeneous.add h1 h2
    · simp only [map_add (f := _), map_mul, map_pow, hFc, hGc, hMc]
      ring
  | mul u v _ _ hu hv =>
    obtain ⟨a, F, hF, hFc⟩ := hu
    obtain ⟨b, G, hG, hGc⟩ := hv
    refine ⟨a + b, F * G, isMultiHomog_mul_const hF hG, ?_⟩
    simp only [map_mul, map_pow, hFc, hGc]
    ring

theorem pointConeMap_map_int (A : Type) [CommRing A] [Algebra A Ω] (y : (Σ k, ι k) → Ω) (G : MRing ι ℤ) :
    pointConeMap A y (MvPolynomial.map (Int.castRingHom A) G) = pointConeMap ℤ y G := by
  induction G using MvPolynomial.induction_on with
  | C z => simp [pointConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.map_X]; simp [pointConeMap]

end ChartForms

theorem const_mul_chartMonomial_pow_form : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (c : ∀ k, ι k) (a : A), ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - (MvPolynomial.map (Int.castRingHom A) G) ∈ pointIdeal A y := by
  intro K _ _ ι _ Ω _ y A _ _ hA c a
  by_cases hs : segreVec y c = 0
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 hs
    refine ⟨1, 0, isWeightedHomogeneous_zero ℤ _ _, ?_⟩
    have hX : (X ⟨k, c k⟩ : MRing ι A) ∈ pointIdeal A y := by
      simp [pointIdeal, RingHom.mem_ker, pointConeMap, hk]
    rw [map_zero, sub_zero, pow_one]
    exact Ideal.mul_mem_left _ _
      (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem (fun k => (X ⟨k, c k⟩ : MRing ι A)) (Finset.mem_univ k)) hX)
  · obtain ⟨n, G, hG, hGc⟩ := exists_form_of_mem_chart y c hs (hA c hs a)
    refine ⟨n, G, hG, ?_⟩
    rw [pointIdeal, RingHom.mem_ker, map_sub, pointConeMap_map_int, hGc, map_mul, map_pow]
    have hM : pointConeMap A y (∏ k, X ⟨k, c k⟩ : MRing ι A) =
        C (segreVec y c) * ∏ k : K, (X k : MvPolynomial K Ω) := by
      simp [pointConeMap, segreVec, Finset.prod_mul_distrib, map_prod]
    have hC : pointConeMap A y (C a : MRing ι A) = C (algebraMap A Ω a) := by
      simp [pointConeMap, MvPolynomial.algebraMap_eq]
    rw [hM, hC, mul_pow, ← C_pow, C_mul]
    ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem gap_nonneg_of_dominant {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) (τ : Ψ) : 0 ≤ gap j mu τ := by
  have h1 : j - 1 < N := by omega
  have hle : mu τ ⟨j, hjN⟩ ≤ mu τ ⟨j - 1, h1⟩ := hd τ ⟨j - 1, h1⟩ ⟨j, hjN⟩ (by rw [Fin.mk_le_mk]; omega)
  simp only [gap, ent, dif_pos h1, dif_pos hjN]
  exact sub_nonneg.mpr hle

theorem NefThreshold.mono {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) {b b' : ℝ} (hb : b ≤ b') (h : NefThreshold j b mu) :
    NefThreshold j b' mu := by
  intro τ
  have hg : 0 ≤ gap j mu τ := gap_nonneg_of_dominant hj1 hjN hd τ
  calc 4 * (Fintype.card Ψ : ℝ) * ‖mu‖ ≤ (b - 2) * gap j mu τ := h τ
    _ ≤ (b' - 2) * gap j mu τ := mul_le_mul_of_nonneg_right (by linarith) hg

theorem RootTower.nefFib_of_nefThreshold :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.ModelNefStatement → T.M2 →
      ∀ (B : ℕ) (c : T.Comp) (mu : Wt Ψ N), Dominant mu → NefThreshold T.j B mu →
        (T.M B c).NefFib mu 0 := by
  intro Ψ _ _ N T h1 h2 B c mu hd hB p hp
  by_cases hS : T.InS B p
  · exact h1 B c p hS mu hd
  · have hBp : B < p := by
      by_contra hc
      exact hS (show p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hp, Or.inl (not_lt.mp hc)⟩)
    refine h2 B c p hp hS mu hd ?_
    exact NefThreshold.mono T.j_pos T.j_lt hd (by exact_mod_cast hBp.le) hB

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

theorem GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, ι k), segreVec y c ≠ 0 → ∀ t : Ω, t ∈ chartRing O (segreVec y) c ↔ ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ chartRing ℤ (segreVec y) c := by
  intro K _ _ ι _ Ω _ y A _ _ hA m _ O _ _ _ _ _ _ _ c hc t
  have hconst : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ (segreVec y) c := hA c hc
  have hmul : ∀ {a b : A}, a ∉ m → b ∉ m → a * b ∉ m := fun ha hb h =>
    (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha hb
  constructor
  · intro ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha =>
      refine ⟨1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one m).2 h), ?_⟩
      rw [map_one, one_mul]
      exact Algebra.subset_adjoin ha
    | algebraMap o =>
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl o
      refine ⟨s, s.2, ?_⟩
      have h' : algebraMap A Ω (s : A) * algebraMap O Ω o = algebraMap A Ω a := by
        rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul,
          mul_comm, h]
      rw [h']
      exact hconst a
    | add a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a + b) =
          algebraMap A Ω r * (algebraMap A Ω s * a) + algebraMap A Ω s * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (mul_mem (hconst r) ha) (mul_mem (hconst s) hb)
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs, ha⟩ := ha
      obtain ⟨r, hr, hb⟩ := hb
      refine ⟨s * r, hmul hs hr, ?_⟩
      have : algebraMap A Ω (s * r) * (a * b) = (algebraMap A Ω s * a) * (algebraMap A Ω r * b) := by
        rw [map_mul]; ring
      rw [this]
      exact mul_mem ha hb
  · rintro ⟨s, hs, ht⟩
    have hle : ∀ {a : Ω}, a ∈ chartRing ℤ (segreVec y) c → a ∈ chartRing O (segreVec y) c := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem a ha => exact Algebra.subset_adjoin ha
      | algebraMap n =>
        have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      | add a b _ _ ha hb => exact add_mem ha hb
      | mul a b _ _ ha hb => exact mul_mem ha hb
    obtain ⟨u, hu⟩ := IsLocalization.map_units O (⟨s, hs⟩ : m.primeCompl)
    have hu' : (u : O) = algebraMap A O s := hu
    have hinv : algebraMap O Ω ((u⁻¹ : Oˣ) : O) * algebraMap A Ω s = 1 := by
      rw [IsScalarTower.algebraMap_apply A O Ω, ← hu', ← map_mul, Units.inv_mul, map_one]
    have : t = algebraMap O Ω ((u⁻¹ : Oˣ) : O) * (algebraMap A Ω s * t) := by
      rw [← mul_assoc, hinv, one_mul]
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (hle ht)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section Lin

variable {K : Type} [Fintype K] {ι : K → Type} {σ : Type}
  (I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
  (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (A : σ → HermLine ι)

theorem arNum_eq_sum_of_subset (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)) (hs : H.support ⊆ s) :
    arNum I P A H = ∑ μ ∈ s, H.coeff μ * arList I P (μ.toMultiset.map A).toList := by
  unfold arNum
  refine Finset.sum_subset hs fun μ _ hμ => ?_
  rw [MvPolynomial.notMem_support_iff.1 hμ, zero_mul]

theorem arNum_add' (H H' : MvPolynomial σ ℝ) :
    arNum I P A (H + H') = arNum I P A H + arNum I P A H' := by
  classical
  rw [arNum_eq_sum_of_subset I P A (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
    arNum_eq_sum_of_subset I P A H (H.support ∪ H'.support) Finset.subset_union_left,
    arNum_eq_sum_of_subset I P A H' (H.support ∪ H'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

theorem arNum_C_mul' (c : ℝ) (H : MvPolynomial σ ℝ) :
    arNum I P A (C c * H) = c * arNum I P A H := by
  have hs : (C c * H).support ⊆ H.support := by
    intro μ hμ
    rw [MvPolynomial.mem_support_iff] at hμ ⊢
    intro h0
    exact hμ (by rw [MvPolynomial.coeff_C_mul, h0, mul_zero])
  rw [arNum_eq_sum_of_subset I P A (C c * H) H.support hs, arNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_C_mul, mul_assoc]

theorem arNum_zero' : arNum I P A (0 : MvPolynomial σ ℝ) = 0 := by
  simp [arNum]

theorem arNum_sum' {α : Type} (s : Finset α) (H : α → MvPolynomial σ ℝ) :
    arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using arNum_zero' I P A
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, arNum_add', ih]

theorem arNum_monomial' (μ : σ →₀ ℕ) (c : ℝ) :
    arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList := by
  classical
  rw [arNum_eq_sum_of_subset I P A (monomial μ c) {μ} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem arNum_rename' {σ' : Type} (e : σ' → σ) (H : MvPolynomial σ' ℝ) :
    arNum I P A (rename e H) = arNum I P (A ∘ e) H := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [MvPolynomial.rename_monomial, arNum_monomial', arNum_monomial',
      show Finsupp.toMultiset (Finsupp.mapDomain e μ) = (Finsupp.toMultiset μ).map e from
        (Finsupp.toMultiset_map _ _).symm, Multiset.map_map]
  | add p q hp hq => rw [map_add (f := _), arNum_add', arNum_add', hp, hq]

end Lin

theorem exists_perm_of_ofFn_perm' {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ s : Equiv.Perm (Fin n), v = w ∘ s :=
  _root_.UpperTheory.Reformulated.B.Yde7.main v w h

theorem arList_eq_of_perm {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1))
    {I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (hp : l.Perm (List.ofFn L)) : arList I P l = I P (D + 1) L := by
  have key : ∀ (m : ℕ) (v : Fin m → HermLine ι), (List.ofFn v).Perm (List.ofFn L) →
      I P m v = I P (D + 1) L := by
    intro m v h
    have hm : m = D + 1 := by simpa using h.length_eq
    subst hm
    obtain ⟨s, rfl⟩ := exists_perm_of_ofFn_perm' v L h
    exact hI.1 P _ L s hP hL
  refine key l.length l.get ?_
  rwa [List.ofFn_get]

theorem arNum_linear_arList_symm : (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι ℤ)) (σ : Type) (A : σ → HermLine ι), (∀ H H' : MvPolynomial σ ℝ, arNum I P A (H + H') = arNum I P A H + arNum I P A H') ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), arNum I P A (C c * H) = c * arNum I P A H) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), arNum I P A (∑ a ∈ s, H a) = ∑ a ∈ s, arNum I P A (H a)) ∧ (∀ (μ : σ →₀ ℕ) (c : ℝ), arNum I P A (monomial μ c) = c * arList I P (μ.toMultiset.map A).toList) ∧ ∀ (σ' : Type) (e : σ' → σ) (H : MvPolynomial σ' ℝ), arNum I P A (rename e H) = arNum I P (A ∘ e) H) ∧ (∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (l : List (HermLine ι)) (L : Fin (D + 1) → HermLine ι), (∀ j, IsSmoothHerm (L j)) → l.Perm (List.ofFn L) → arList I P l = I P (D + 1) L) := by
  refine ⟨?_, ?_⟩
  · intro K _ _ ι _ I P σ A
    exact ⟨arNum_add' I P A, arNum_C_mul' I P A, fun α s H => arNum_sum' I P A s H,
      arNum_monomial' I P A, fun σ' e H => arNum_rename' I P A e H⟩
  · intro K _ _ ι _ P D hP I hI l L hL hp
    exact arList_eq_of_perm hP hI l L hL hp

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem intNumL_subfield_constants : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F'] (V' : Ideal (MRing ι F')), IsMultiHomogIdeal V' → (∀ (c : ∀ k, ι k) (a : F'), ∃ (n : ℕ) (G : MRing ι F), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - MvPolynomial.map (algebraMap F F') G ∈ V') → ∀ l : List (K → ℤ), intNumL F (V'.comap (MvPolynomial.map (algebraMap F F'))) l = (Module.finrank F F' : ℤ) * intNumL F' V' l := by
  intro K _ _ ι _ F F' _ _ _ _ V' _ hgen l
  have hgood : ∀ (c : ∀ k, ι k) (a : F'), ∃ n, BaseChangeColon.PlField.Good (F := F) V' n c a := by
    intro c a
    obtain ⟨n, G, hG, hmem⟩ := hgen c a
    exact ⟨n, G, hG, hmem⟩
  obtain ⟨n, hn⟩ := BaseChangeColon.PlField.exists_uniform hgood
  have hev : ∀ᶠ m : K → ℤ in Filter.atTop,
      hilbFn (V'.comap (MvPolynomial.map (algebraMap F F'))) m
        = (Module.finrank F F' : ℤ) * hilbFn V' m := by
    filter_upwards [Filter.eventually_ge_atTop
      (fun k : K => ((n * Fintype.card (ι k) + 1 : ℕ) : ℤ))] with m hm
    have hm' : ∀ k, ((n * Fintype.card (ι k) + 1 : ℕ) : ℤ) ≤ m k := fun k => hm k
    have hm0 : ∀ k, 0 ≤ m k := fun k => le_trans (Int.natCast_nonneg _) (hm' k)
    have hlt : ∀ k, n * Fintype.card (ι k) < (m k).toNat := by
      intro k
      have := hm' k
      omega
    unfold hilbFn
    rw [if_pos hm0, if_pos hm0,
      BaseChangeColon.PlField.finrank_piece (fun q hq => BaseChangeColon.PlField.lift_form hn hlt hq), Nat.cast_mul]
  have hne : (Module.finrank F F' : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := F')).ne'
  simp only [intNumL, intNum, mixedDiff, List.ofFn_get]
  exact BaseChangeColon.PlField.eventualValue_mul hne (BaseChangeColon.PlField.foldr_eventually _ l hev)

end GlobalTheory.CompanionTheory.Ar.Num
end

section

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem sum_log_div_pred_le :
    ∀ (x : ℝ) (S : Finset ℕ), 1 ≤ x → (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ x) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ Real.log x + 17 / 5 := by
  intro x S hx hS
  have hsplit : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1)
      = Real.log p / p + Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h1 : ∑ p ∈ S, Real.log p / (p : ℝ) ≤ Real.log x + Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (GlobalTheory.T.sum_prime_log_div_le x hx)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨Nat.le_floor (hS p hp).2, (hS p hp).1⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h2 : ∑ p ∈ S, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 :=
    GlobalTheory.T.sum_log_div_n_sq_le_two S (fun p hp => (hS p hp).1.two_le)
  have hl4 : Real.log 4 < 7 / 5 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h := Real.log_two_lt_d9
    norm_num at h
    linarith
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem subst_abs_list : ∀ (G : Type) [AddCommGroup G] (d : ℕ) (n : List G → ℝ), (∀ l l', l.Perm l' → n l = n l') → (∀ b b' l, l.length + 1 = d → n ((b + b') :: l) = n (b :: l) + n (b' :: l)) → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → G) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List G, m + Q.length = d → (∑ μ ∈ H.support, H.coeff μ * n ((μ.toMultiset.map fun t => ∑ i, M t i • cls i).toList ++ Q)) = ∑ μ ∈ (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).support, (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H).coeff μ * n ((μ.toMultiset.map cls).toList ++ Q) := by
  exact @BaseChangeColon.homogeneous_sum_linear_change_classes

end GlobalTheory.CompanionTheory.Ar.Num
end

end

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.descent_intersection_number : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F'] (V' : Ideal (MRing ι F')), IsMultiHomogIdeal V' → (∀ (c : ∀ k, ι k) (a : F'), ∃ (n : ℕ) (G : MRing ι F), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - MvPolynomial.map (algebraMap F F') G ∈ V') → ∀ l : List (K → ℤ), intNumL F (V'.comap (MvPolynomial.map (algebraMap F F'))) l = (Module.finrank F F' : ℤ) * intNumL F' V' l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.intNumL_subfield_constants | exact GlobalTheory.CompanionTheory.Ar.Num.intNumL_subfield_constants | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.intNumL_subfield_constants <;> assumption)

end
end
