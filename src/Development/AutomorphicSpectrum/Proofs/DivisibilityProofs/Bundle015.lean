module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScaling
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle011
public import Development.WeilBound.CoreStatements.IdealCycleValues.LengthLocQuot
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle001

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem degree_eq_card_toMultiset {α : Type} (d : α →₀ ℕ) :
    d.degree = Multiset.card (Finsupp.toMultiset d) := by
  rw [Finsupp.card_toMultiset]
  rfl

theorem ofFn_monoLines_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J J' : Type}
    (ℓ : J' → HermLine ι) (e : J → J') (μ : J →₀ ℕ) (m : J' →₀ ℕ) (d : ℕ)
    (hm : Finsupp.toMultiset m = (Finsupp.toMultiset μ).map e)
    (hd : (Finsupp.toMultiset m).toList.length = d) :
    ((Finsupp.toMultiset μ).map (ℓ ∘ e)).toList.Perm (List.ofFn (monoLines ℓ m d)) := by
  have h1 : List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ := by
    refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, hd]) fun n h₁ h₂ => ?_
    have hn : n < (Finsupp.toMultiset m).toList.length := by rwa [List.length_map] at h₂
    rw [List.getElem_ofFn, List.getElem_map]
    simp only [monoLines]
    rw [dite_eq_left hn]
    rfl
  rw [h1, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList, hm,
    Multiset.map_map]

theorem arMono_mapDomain_some {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
    (II : IntersectionSystem) (hII : IsIntersectionSystem II) (t : ℝ) (μ : Ψ × Fin N →₀ ℕ)
    (hμ : μ.degree = dimFl Ψ N + 1) :
    M.arMono II t (Finsupp.mapDomain some μ) =
      arList (II M.K M.ι) M.P (μ.toMultiset.map (M.x t)).toList / (M.δ : ℝ) := by
  classical
  have hms : Finsupp.toMultiset (Finsupp.mapDomain some μ) = (Finsupp.toMultiset μ).map some :=
    (Finsupp.toMultiset_map _ _).symm
  have hcard : Multiset.card (Finsupp.toMultiset μ) = dimFl Ψ N + 1 := by
    rw [← degree_eq_card_toMultiset, hμ]
  have hdeg : (Finsupp.mapDomain some μ).degree = dimFl Ψ N + 1 := by
    rw [degree_eq_card_toMultiset, hms, Multiset.card_map, hcard]
  have hnone : (Finsupp.mapDomain some μ) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hlen : (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length = dimFl Ψ N + 1 := by
    rw [Multiset.length_toList, hms, Multiset.card_map, hcard]
  have hperm := ofFn_monoLines_perm (M.line t) some μ (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) hms hlen
  have hall : ∀ r ∈ (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList, IsSmoothHerm (M.line t r) := by
    intro r hr
    rw [Multiset.mem_toList, hms, Multiset.mem_map] at hr
    obtain ⟨r', -, rfl⟩ := hr
    exact M.x_smooth t r'
  have hsm : ∀ j, IsSmoothHerm (monoLines (M.line t) (Finsupp.mapDomain some μ) (dimFl Ψ N + 1) j) := by
    intro j
    have hj : (j : ℕ) < (Finsupp.toMultiset (Finsupp.mapDomain some μ)).toList.length := by
      rw [hlen]; exact j.2
    simp only [monoLines]
    rw [dite_eq_left hj]
    exact hall _ (List.get_mem _ _)
  have hmain := arNum_linear_arList_symm.2 M.K M.ι M.P (dimFl Ψ N) M.arith (II M.K M.ι) (hII M.K M.ι) _ _ hsm
    (by simpa [Function.comp_def, RootModel.line] using hperm)
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  congr 1
  exact hmain.symm

theorem arFun_toA_eq_arNum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (t : ℝ) (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N + 1) → M.arFun II t (toA F) = arNum (II M.K M.ι) M.P (M.x t) F / (M.δ : ℝ) := by
  intro Ψ _ _ N M II hII t F hF
  classical
  have hmono : ∀ μ ∈ F.support, M.arFun II t (toA (monomial μ (F.coeff μ))) =
      F.coeff μ * (arList (II M.K M.ι) M.P (μ.toMultiset.map (M.x t)).toList / (M.δ : ℝ)) := by
    intro μ hμ
    have hdeg : μ.degree = dimFl Ψ N + 1 := by
      have h := hF (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact h
    have h1 : toA (monomial μ (F.coeff μ)) =
        (F.coeff μ) • (basisMonomials (Option (Ψ × Fin N)) ℝ) (Finsupp.mapDomain some μ) := by
      simp [toA, MvPolynomial.rename_monomial, MvPolynomial.smul_monomial]
    rw [h1, map_smul, RootModel.arFun, Module.Basis.constr_basis, smul_eq_mul,
      arMono_mapDomain_some M II hII t μ hdeg]
  have hsum : toA F = ∑ μ ∈ F.support, toA (monomial μ (F.coeff μ)) := by
    unfold toA
    conv_lhs => rw [F.as_sum]

    rw [map_sum]

  rw [hsum, map_sum, Finset.sum_congr rfl hmono]
  unfold arNum
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.hermitian_combination_smooth_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj | exact GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.combLine_smooth_conj <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.curve_degree_linear_nef_cone : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam mu : Wt Ψ N) (s s' a : ℝ), (∀ W, M.curveDeg (lam + mu) (s + s') W = M.curveDeg lam s W + M.curveDeg mu s' W) ∧ (∀ W, M.curveDeg (a • lam) (a * s) W = a * M.curveDeg lam s W) ∧ (∀ p, 0 ≤ s → M.NefAt p lam 0 → M.NefAt p 0 1 → M.NefAt p lam s) ∧ (0 ≤ s → M.NefGen lam 0 → M.NefGen 0 1 → M.NefGen lam s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.curveDeg_linear_nef | exact GlobalTheory.CompanionTheory.Ar.Top.curveDeg_linear_nef | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.curveDeg_linear_nef <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.monomial_lines_permutation : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) (ℓ : J → HermLine ι) (w : Fin d → J), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d ∧ ∃ σ : Equiv.Perm (Fin d), monoLines ℓ (∑ k, Finsupp.single (w k) 1) d = (fun k => ℓ (w k)) ∘ σ ∧ II K ι P d (monoLines ℓ (∑ k, Finsupp.single (w k) 1) d) = II K ι P d (fun k => ℓ (w k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.monoLines_monomial_word | exact GlobalTheory.CompanionTheory.Ar.Top.monoLines_monomial_word | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.monoLines_monomial_word <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.rational_weight_integral_coeffs : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef | exact GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.root_model_curve_degree_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → (∀ W : Ideal (MRing M.ι), (geoNum 1 W (fun _ => (combLine (M.line t) n).a) : ℝ) = q * M.curveDeg lam s W) ∧ (M.NefFib lam s → NefOnFibres M.P (combLine (M.line t) n).a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple | exact GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.root_model_semipositive_conj : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple | exact GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

theorem _root_.GlobalTheory.T.chart_ring_localization_membership : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, ι k), segreVec y c ≠ 0 → ∀ t : Ω, t ∈ chartRing O (segreVec y) c ↔ ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ chartRing ℤ (segreVec y) c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff | exact GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.constants_monomial_approximation : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (c : ∀ k, ι k) (a : A), ∃ (n : ℕ) (G : MRing ι ℤ), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - (MvPolynomial.map (Int.castRingHom A) G) ∈ pointIdeal A y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.const_mul_chartMonomial_pow_form | exact GlobalTheory.CompanionTheory.Ar.Num.const_mul_chartMonomial_pow_form | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.const_mul_chartMonomial_pow_form <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

theorem _root_.GlobalTheory.T.degree_lattice_prime_scaling : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), IsMultiProjPrime (pointIdeal ℤ y) → ∀ (S : Finset Nat.Primes) (b b' : K → ℤ) (s : Ω), s ≠ 0 → (∀ c, segreVec y c ≠ 0 → (∀ t ∈ degLat ℤ y b c, ∃ n : ℕ, ∃ t' ∈ degLat ℤ y b' c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * t = s * t') ∧ ∀ t' ∈ degLat ℤ y b' c, ∃ n : ℕ, ∃ t ∈ degLat ℤ y b c, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n * (s * t') = t) → IsHorizontal (pointIdeal ℤ y) → ∃ f g : MRing ι ℤ, (⟨fun _ => b, fun _ => b', fun _ => f, fun _ => g⟩ : LocPair ι ℤ Unit).IsVertOff (pointIdeal ℤ y) S ∧ aeval y f = s * aeval y g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | exact GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lineVert_of_eq_off <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section ConstantsCorrespondence

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {A : Type} [CommRing A] [Algebra A Ω]

theorem pointConeMap_map_intCast (y : (Σ k, ι k) → Ω) (g : MRing ι ℤ) :
    pointConeMap A y (MvPolynomial.map (Int.castRingHom A) g) = ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, map_X]
    simp [pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]

theorem comap_pointIdeal_eq_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (pointIdeal A y).comap (MvPolynomial.map (Int.castRingHom A)) = mCoordIdeal y := by
  ext g
  rw [Ideal.mem_comap]
  simp only [pointIdeal, mCoordIdeal, RingHom.mem_ker, pointConeMap_map_intCast]

theorem exists_pow_chartMonomial_mul_sub_map_mem {y : (Σ k, ι k) → Ω} (hA : HasConstants ℤ A y) (c : ∀ k, ι k)
    (r : MRing ι A) :
    ∃ (n : ℕ) (g : MRing ι ℤ),
      (MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ)) ^ n * r -
        MvPolynomial.map (Int.castRingHom A) g ∈ pointIdeal A y := by
  have hs : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) =
      (∏ k, X ⟨k, c k⟩ : MRing ι A) := by
    simp [map_prod]
  rw [hs]
  set s : MRing ι A := ∏ k, X ⟨k, c k⟩ with hsdef
  induction r using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨n, G, -, hG⟩ := const_mul_chartMonomial_pow_form K ι Ω y A hA c a
    refine ⟨n, G, ?_⟩
    rw [mul_comm]
    exact hG
  | add p q hp hq =>
    obtain ⟨n, g, hg⟩ := hp
    obtain ⟨m, k, hk⟩ := hq
    refine ⟨n + m, (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ^ m * g + (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ^ n * k, ?_⟩
    have h := (pointIdeal A y).add_mem ((pointIdeal A y).mul_mem_left (s ^ m) hg)
      ((pointIdeal A y).mul_mem_left (s ^ n) hk)
    convert h using 1
    simp only [map_add (f := _), map_mul, map_pow, hs, ← hsdef]
    ring
  | mul_X p i hp =>
    obtain ⟨n, g, hg⟩ := hp
    refine ⟨n, g * X i, ?_⟩
    have h := (pointIdeal A y).mul_mem_right (X i) hg
    convert h using 1
    simp only [map_mul, map_X]
    ring

theorem exists_chart_not_mem {R : Type} [CommRing R] {W : Ideal (MRing ι R)} (hW : W.IsPrime) (hr : IsRelevant W) :
    ∃ c : ∀ k, ι k, (∏ k, X ⟨k, c k⟩ : MRing ι R) ∉ W := by
  choose c hc using hr
  refine ⟨c, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := (hW.prod_mem_iff).1 h
  exact hc k hk

theorem isRelevant_comap_map_intCast {W' : Ideal (MRing ι A)} (hr : IsRelevant W') :
    IsRelevant (W'.comap (MvPolynomial.map (Int.castRingHom A)) : Ideal (MRing ι ℤ)) := by
  intro k
  obtain ⟨i, hi⟩ := hr k
  exact ⟨i, by simpa [Ideal.mem_comap] using hi⟩

end ConstantsCorrespondence

theorem pl_corr : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → (pointIdeal A y).comap (MvPolynomial.map (Int.castRingHom A)) = mCoordIdeal y ∧ (∀ W : Ideal (MRing ι ℤ), W.IsPrime → IsRelevant W → mCoordIdeal y ≤ W → ∃! W' : Ideal (MRing ι A), W'.IsPrime ∧ pointIdeal A y ≤ W' ∧ W'.comap (MvPolynomial.map (Int.castRingHom A)) = W) ∧ ∀ (f : MRing ι ℤ) (W' : Ideal (MRing ι A)), W'.IsPrime → IsRelevant W' → pointIdeal A y ≤ W' → divCycle (pointIdeal A y) (MvPolynomial.map (Int.castRingHom A) f) W' = divCycle (mCoordIdeal y) f (W'.comap (MvPolynomial.map (Int.castRingHom A))) := by
  intro K _ _ ι _ Ω _ y A _ _ hA
  have hcomap := comap_pointIdeal_eq_mCoordIdeal (A := A) y
  refine ⟨hcomap, ?_, ?_⟩
  · intro W hW hr hle
    obtain ⟨c, hc⟩ := exists_chart_not_mem hW hr
    have h := exists_pow_chartMonomial_mul_sub_map_mem hA c
    obtain ⟨W', hW', hPW', hWc⟩ := BaseChangeColon.Corr.exists_lift h hW (by rw [hcomap]; exact hle) hc
    have hc' : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ W' := by
      intro hm
      apply hc
      rw [← hWc]
      exact hm
    refine ⟨W', ⟨hW', hPW', hWc⟩, ?_⟩
    rintro V ⟨hV, hPV, hVc⟩
    have hcV : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ V := by
      intro hm
      apply hc
      rw [← hVc]
      exact hm
    exact le_antisymm (BaseChangeColon.Corr.mono h hW' hPV hPW' hc' (by rw [hVc, hWc]))
      (BaseChangeColon.Corr.mono h hV hPW' hPV hcV (by rw [hVc, hWc]))
  · intro f W' hW' hr hPW'
    obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k,
        MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : MRing ι ℤ) ∉ W' := by
      obtain ⟨c, hc⟩ := exists_chart_not_mem hW' hr
      exact ⟨c, by simpa [map_prod] using hc⟩
    have h := exists_pow_chartMonomial_mul_sub_map_mem hA c
    set φ := MvPolynomial.map (σ := (Σ k, ι k)) (Int.castRingHom A) with hφ
    set J : Ideal (MRing ι ℤ) := mCoordIdeal y ⊔ Ideal.span {f} with hJdef
    have hJ : (pointIdeal A y).comap φ ≤ J := by rw [hcomap]; exact le_sup_left
    have hJeq : pointIdeal A y ⊔ Ideal.span {φ f} = pointIdeal A y ⊔ J.map φ := by
      rw [hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton, ← sup_assoc]
      congr 1
      refine (sup_eq_left.2 ?_).symm
      rw [Ideal.map_le_iff_le_comap, hcomap]
    have hmin := BaseChangeColon.Corr.minimal_iff h J hJ hW' hPW' hc
    have hrel := isRelevant_comap_map_intCast hr
    have hWp : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
    have hlen := BaseChangeColon.Corr.length_eq h J hJ W' (W'.comap φ) rfl hPW' hc
    have hmin' : W' ∈ (pointIdeal A y ⊔ Ideal.span {φ f}).minimalPrimes ↔ W'.comap φ ∈ J.minimalPrimes := by
      rw [hJeq]
      exact hmin
    have hlen' : Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (MRing ι A ⧸ (pointIdeal A y ⊔ Ideal.span {φ f}))) =
        Module.length (Localization.AtPrime (W'.comap φ))
          (LocalizedModule (W'.comap φ).primeCompl (MRing ι ℤ ⧸ J)) := by
      rw [hJeq]
      exact hlen
    unfold divCycle
    by_cases hm : W'.comap φ ∈ J.minimalPrimes
    · rw [dite_eq_left ⟨hmin'.2 hm, hr⟩, dite_eq_left ⟨hm, hrel⟩]
      exact congrArg (fun t : ℕ∞ => ((ENat.toNat t : ℕ) : ℤ)) hlen'
    · rw [dite_eq_right (fun hh => hm (hmin'.1 hh.1)), dite_eq_right (fun hh => hm hh.1)]

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem isLeft_pow_congr {Ψ : Type} (f : Equiv.Perm (Ψ ⊕ Ψ))
    (hf : (∀ σ, (f σ).isLeft = σ.isLeft) ∨ ∀ σ, (f σ).isLeft = σ.isRight) (k : ℕ) :
    ∀ σ σ' : Ψ ⊕ Ψ, σ.isLeft = σ'.isLeft → ((f ^ k) σ).isLeft = ((f ^ k) σ').isLeft := by
  induction k with
  | zero =>
    intro σ σ' h
    simpa using h
  | succ k ih =>
    intro σ σ' h
    have h' := ih σ σ' h
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rcases hf with hf | hf
    · rw [hf, hf]
      exact h'
    · rw [hf, hf]
      cases h1 : (f ^ k) σ <;> cases h2 : (f ^ k) σ' <;> simp_all

theorem frobShape_of_side : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), (∀ p, (∀ σ, (φ p σ).isLeft = σ.isLeft) ∨ ∀ σ, (φ p σ).isLeft = σ.isRight) → FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ : Ψ ⊕ Ψ) := by
  intro Ψ _ _ φ h
  unfold FrobShape
  intro p n τ τ'
  exact isLeft_pow_congr (φ p) (h p) (n + 1) _ _ rfl

end GlobalTheory.CompanionTheory.Ar.Num
end
