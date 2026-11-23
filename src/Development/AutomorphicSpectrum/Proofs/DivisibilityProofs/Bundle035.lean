module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HasBaseDegreeSetting
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsMultiProjPrimeExtTo
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle009
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle028

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerArithAgreement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerGeometricAgreement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainUnitLogIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rootModel_nefFib_zero_one_of_nonneg :
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 :=
  @RootFieldNumerics.root_model_nef_fibres_base

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.GenInt

section SlopeTestRemainingChoices

variable {K : Type} {ι : K → Type}

theorem intNumL_ofFn_eq [DecidableEq K] (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem divCycle_one (P W : Ideal (MRing ι ℤ)) : divCycle P (1 : MRing ι ℤ) W = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  rintro ⟨h, -⟩
  have e : (P ⊔ Ideal.span {(1 : MRing ι ℤ)}) = ⊤ := by simp
  rw [e] at h
  exact h.1.1.ne_top (top_le_iff.1 h.1.2)

theorem isPrime_mem_of_divCycle_ne {P W : Ideal (MRing ι ℤ)} {s : MRing ι ℤ}
    (h : divCycle P s W ≠ 0) : W.IsPrime ∧ s ∈ W := by
  unfold divCycle at h
  by_cases hc : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W
  · exact ⟨hc.1.1.1, hc.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩
  · rw [dite_eq_right hc] at h
    exact absurd rfl h

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Ar.Num.GenInt

namespace GlobalTheory.CompanionTheory.Ar.Num.GenInt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoHomog_C (c : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C c : MRing ι ℤ) (0 : K → ℕ) := by
  intro m hm k
  rw [C_apply] at hm
  have h0 : m = 0 := Finset.mem_singleton.1 (support_monomial_subset hm)
  subst h0
  simp

theorem vertAt_two_of_ne (P : Ideal (MRing ι ℤ)) (p : Nat.Primes) (hp : (p : ℕ) ≠ 2) (l : List (K → ℤ)) :
    vertAt p P (C (2 : ℤ)) l = 0 := by
  classical
  unfold vertAt cycEval
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  by_cases h : divCycle P (C (2 : ℤ)) W = 0
  · rw [h, zero_mul]
  · obtain ⟨hW, h2⟩ := isPrime_mem_of_divCycle_ne h
    have hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
      intro hpW
      have hcop : IsCoprime (((p : ℕ) : ℤ)) 2 := by
        have : Nat.Coprime (p : ℕ) 2 := (Nat.coprime_primes p.2 Nat.prime_two).2 hp
        exact_mod_cast Nat.isCoprime_iff_coprime.2 this
      obtain ⟨a, b, hab⟩ := hcop
      apply hW.ne_top
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Σ k, ι k) ℤ) = C a * C ((p : ℕ) : ℤ) + C b * C 2 := by
        rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
      rw [this]
      exact W.add_mem (W.mul_mem_left _ hpW) (W.mul_mem_left _ h2)
    exact mul_eq_zero_of_right _ (if_neg hpW)

theorem ptsIntegral_one_eq_vertAt (P : Ideal (MRing ι ℤ)) (D : ℕ) (hP : IsArithVar P (D + 1))
    (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (hI : IsIntersectionFamily I)
    (L : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) :
    ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) =
      (vertAt ⟨2, Nat.prime_two⟩ P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  have hA : IsSmoothHerm (trivLine ι) := contDiffOn_const
  have hc := ptsIntegral_congr_and_homog K ι P D (fun j z => Real.log ((L j).h z))
  have nm1 : (1 : MRing ι ℤ) ∉ P := fun h => hPp.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have nm2 : (C (2 : ℤ) : MRing ι ℤ) ∉ P := by
    intro h
    have h2 : (2 : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at h2
    simp at h2
  have g1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ) := by
    simpa using geoHomog_C (K := K) (ι := ι) 1
  have g2 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ) := geoHomog_C 2
  have f1 : IsMultiHomog (1 : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_one _ _
  have f2 : IsMultiHomog (C (2 : ℤ) : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_C _ _
  have e1 := hI.2.2 P D L (trivLine ι) 1 0 hP hL hA (fun k => by simp [trivLine]) g1 nm1
  have e2 := hI.2.2 P D L (trivLine ι) (C 2) 0 hP hL hA (fun k => by simp [trivLine]) g2 nm2
  rw [(GlobalTheory.T.finite_vertical_recursion K ι P D hP I 0 1 f1 nm1 L (trivLine ι)).2] at e1
  rw [(GlobalTheory.T.finite_vertical_recursion K ι P D hP I 0 (C 2) f2 nm2 L (trivLine ι)).2] at e2
  have a1 : arInt P (1 : MRing ι ℤ) (trivLine ι) L = 0 := by
    unfold arInt
    rw [hc.1 _ (fun _ => (0 : ℝ) * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]),
      hc.2 0 (fun _ => 1)]
    simp
  have a2 : arInt P (C (2 : ℤ) : MRing ι ℤ) (trivLine ι) L =
      Real.log 2 * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    unfold arInt
    rw [hc.1 _ (fun _ => Real.log 2 * 1) (fun z _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, trivLine]),
      hc.2 (Real.log 2) (fun _ => 1)]
  have v1 : ∀ p : Nat.Primes, vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) = 0 := by
    intro p
    unfold vertAt cycEval
    exact finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp
  have h1 : ∑ᶠ W, (divCycle P (1 : MRing ι ℤ) W : ℝ) *
      Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun W => by rw [divCycle_one]; simp
  have h2 : ∑ᶠ W, (divCycle P (C (2 : ℤ) : MRing ι ℤ) W : ℝ) *
      Set.indicator {W | IsHorizontal W} (fun W => I W D L) W = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
    by_cases h : divCycle P (C (2 : ℤ) : MRing ι ℤ) W = 0
    · rw [h, Int.cast_zero, zero_mul]
    · have hW := (isPrime_mem_of_divCycle_ne h).2
      have : W ∉ {W : Ideal (MRing ι ℤ) | IsHorizontal W} := by
        intro hH
        have h2 : (2 : ℤ) ∈ W.comap (C : ℤ →+* MRing ι ℤ) := hW
        rw [show W.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hH] at h2
        simp at h2
      rw [Set.indicator_of_notMem this, mul_zero]
  have p1 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) *
      (vertAt p P (1 : MRing ι ℤ) (List.ofFn fun j => (L j).a) : ℝ) = 0 :=
    finsum_eq_zero_of_forall_eq_zero fun p => by rw [v1]; simp
  have p2 : ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) *
      (vertAt p P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) =
      Real.log 2 * (vertAt ⟨2, Nat.prime_two⟩ P (C (2 : ℤ)) (List.ofFn fun j => (L j).a) : ℝ) := by
    refine (finsum_eq_single _ (⟨2, Nat.prime_two⟩ : Nat.Primes) ?_).trans ?_
    · intro p hp
      have : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
      rw [vertAt_two_of_ne P p this, Int.cast_zero, mul_zero]
    · norm_num
  rw [h1, p1, a1] at e1
  rw [h2, p2, a2] at e2
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  apply mul_left_cancel₀ hlog
  linarith

theorem vertAt_self_eq_intNum (P : Ideal (MRing ι ℤ)) (D : ℕ) (hP : IsArithVar P (D + 1))
    (p : Nat.Primes) (b : Fin D → K → ℤ) :
    (vertAt p P (C ((p : ℕ) : ℤ)) (List.ofFn b) : ℝ) = (intNum ℚ (extTo ℚ P) b : ℝ) := by
  classical
  have hlen : (List.ofFn b).length = D := by simp
  have hm := zp_model K ι P D hP p
  have f2 : IsMultiHomog (C ((p : ℕ) : ℤ) : MRing ι ℤ) (0 : K → ℕ) := isWeightedHomogeneous_C _ _
  have nm2 : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∉ P := by
    intro h
    have h2 : ((p : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing ι ℤ) := h
    rw [show P.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from hP.2.2.1] at h2
    have := p.2.ne_zero
    simp_all
  rw [GlobalTheory.T.vertical_number_local_cycle K ι P D hP p 0 (C ((p : ℕ) : ℤ)) f2 nm2 (List.ofFn b) hlen]
  have hcy := GlobalTheory.T.uniformizer_divisor_cycle_number (ZP p) (((p : ℕ) : ZP p)) hm.1 K ι (extTo (ZP p) P) D hm.2.1 1 1
    Empty Empty.elim 1 0 (MvPolynomial.isHomogeneous_one _ _) (List.ofFn b) (by simp)
  have hg := genNum_zp_eq_rat K ι P p Empty Empty.elim 1 (List.ofFn b)
  have hcN : ∀ Z : Ideal (MRing ι (ZP p)) → ℤ,
      cycNum Z (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) = (cycList Z (List.ofFn b) : ℝ) := by
    intro Z
    unfold cycNum
    simp [classList]
  have hgN : genNum ℚ (extTo ℚ P) (Empty.elim : Empty → K → ℤ) 1 (List.ofFn b) =
      (intNum ℚ (extTo ℚ P) b : ℝ) := by
    unfold genNum
    simp [classList, intNumL_ofFn_eq]
  rw [hcN, hg, hgN] at hcy
  have e : MvPolynomial.map (Int.castRingHom (ZP p)) (C ((p : ℕ) : ℤ) : MRing ι ℤ) =
      C (((1 : (ZP p)ˣ) : ZP p) * ((p : ℕ) : ZP p) ^ 1) := by
    simp
  rw [e, hcy]
  simp

end GlobalTheory.CompanionTheory.Ar.Num.GenInt

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ptsIntegral_one_eq_intNum :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) = (intNum ℚ (extTo ℚ P) (fun j => (L j).a) : ℝ) := by
  intro K _ _ ι _ P D hP I hI L hL
  rw [GenInt.ptsIntegral_one_eq_vertAt P D hP I hI L hL]
  have h := GenInt.vertAt_self_eq_intNum P D hP ⟨2, Nat.prime_two⟩ (fun j => (L j).a)
  have e : (((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) : ℤ) = 2 := rfl
  rwa [e] at h

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

theorem divCycle_eq_off {K : Type} {ι : K → Type} {P : Ideal (MRing ι ℤ)} {f g : MRing ι ℤ} {S : Finset Nat.Primes}
    (h : ∀ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime → P ≤ W → IsRelevant W →
      (∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) →
      ∃ u v : MvPolynomial (Σ k, ι k) ℤ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P)
    {W : Ideal (MRing ι ℤ)}
    (hW : W.IsPrime → ∀ p ∈ S, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) :
    divCycle P f W = divCycle P g W := by
  by_cases hc : W.IsPrime ∧ P ≤ W ∧ IsRelevant W
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hc.1 hc.2.1 hc.2.2 (hW hc.1)
    exact divCycle_eq_of_mul_sub_mem hu hv huv
  · have h0 : ∀ s : MRing ι ℤ, divCycle P s W = 0 := fun s => by
      by_contra hne
      exact hc (le_and_isRelevant_of_divCycle_ne_zero hne)
    rw [h0, h0]

theorem not_mem_of_mem {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime) {p q : Nat.Primes}
    (hpq : p ≠ q) (hp : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W) :
    (C ((q : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hq
  have hcop : IsCoprime ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := hcop
  apply hW.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : MvPolynomial (Σ k, ι k) ℤ) =
      C a * C ((p : ℕ) : ℤ) + C b * C ((q : ℕ) : ℤ) := by
    rw [← C_mul, ← C_mul, ← C_add, hab, C_1]
  rw [e]
  exact W.add_mem (W.mul_mem_left _ hp) (W.mul_mem_left _ hq)

theorem not_mem_of_horizontal {K : Type} {ι : K → Type} {W : Ideal (MRing ι ℤ)} (hW : IsHorizontal W)
    (p : Nat.Primes) : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W := by
  intro hp
  have h1 : ((p : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) := hp
  rw [show W.comap (C : ℤ →+* MvPolynomial (Σ k, ι k) ℤ) = ⊥ from hW, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

theorem change_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (S : Finset Nat.Primes) (T : LocPair ι ℤ Unit), T.IsVertOff P S → ∀ A A' : HermLine ι, IsSmoothHerm A → IsSmoothHerm A' → T.IsIsometric P (fun _ => A) (fun _ => A') → ∀ L : Fin D → HermLine ι, (∀ j, IsSmoothHerm (L j)) → I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') = ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) - (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
  intro K _ _ ι _ P D hP I hI S T hT A A' hA hA' hiso L hL
  obtain ⟨⟨bf, bg, hf, hg, hdeg⟩, hfP, hgP, hunit⟩ := hT ()
  obtain ⟨hAa, hA'a, hnorm⟩ := hiso ()
  let B : HermLine ι := (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric bf).tensor A.inv
  have hB : IsSmoothHerm B := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor
    (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric bf) (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_inv hA)
  have hAB : IsSmoothHerm (A.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA hB
  have hAB' : IsSmoothHerm (A'.tensor B) := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hA' hB
  have dF : ∀ k, (A.tensor B).a k = bf k := fun k => by
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric]
  have dG : ∀ k, (A'.tensor B).a k = bg k := fun k => by
    have h1 := congrFun hdeg k
    have h2 := congrFun hAa k
    have h3 := congrFun hA'a k
    simp only [Pi.sub_apply] at h1
    simp only [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv,
      ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric, Pi.add_apply, Pi.neg_apply]
    linarith
  have e1 := hI.2.1 P D L A B hP hL hA hB
  have e2 := hI.2.1 P D L A' B hP hL hA' hB
  have r1 := hI.2.2 P D L (A.tensor B) (T.f ()) bf hP hL hAB dF
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hf) hfP
  have r2 := hI.2.2 P D L (A'.tensor B) (T.g ()) bg hP hL hAB' dG
    ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 hg) hgP
  obtain ⟨fin1, s1⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bf (T.f ()) hf hfP L (A.tensor B)
  obtain ⟨fin2, s2⟩ := GlobalTheory.T.finite_vertical_recursion K ι P D hP I bg (T.g ()) hg hgP L (A'.tensor B)
  have hor : (∑ᶠ W, (divCycle P (T.f ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
      ∑ᶠ W, (divCycle P (T.g ()) W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
    refine finsum_congr fun W => ?_
    by_cases hW : IsHorizontal W
    · rw [divCycle_eq_off hunit (fun _ p _ => not_mem_of_horizontal hW p)]
    · have : W ∉ {W | IsHorizontal W} := hW
      simp [Set.indicator_of_notMem this]
  have ar : arInt P (T.f ()) (A.tensor B) L = arInt P (T.g ()) (A'.tensor B) L := by
    refine (GlobalTheory.T.log_integral_congr_smul K ι P D _).1 _ _ fun z hz => ?_
    have h1 := hnorm z hz
    have pA := A.pos z hz.1
    have pA' := A'.pos z hz.1
    have pB := B.pos z hz.1
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.logNorm, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor]
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (B.h z) * h1
  have hv : ∀ p : Nat.Primes, p ∉ S → vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) =
      vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) := by
    intro p hp
    unfold vertAt cycEval
    refine finsum_congr fun W => ?_
    by_cases hpW : (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∈ W
    · rw [divCycle_eq_off hunit (fun hWp q hq => not_mem_of_mem hWp
        (fun h : p = q => hp (by rw [h]; exact hq)) hpW)]
    · simp only [if_neg hpW, mul_zero]
  have vert : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)) -
      (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) =
      ∑ p ∈ S, Real.log (p : ℕ) * ((vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ) -
        (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)) := by
    have hF : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.f ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin1.subset fun p hp h0 => hp (by simp [h0])
    have hG : (Function.support fun p : Nat.Primes =>
        Real.log (p : ℕ) * (vertAt p P (T.g ()) (List.ofFn fun j => (L j).a) : ℝ)).Finite :=
      fin2.subset fun p hp h0 => hp (by simp [h0])
    rw [← finsum_sub_distrib hF hG,
      finsum_eq_sum_of_support_subset (s := S) _ fun p hp => ?_]
    · exact Finset.sum_congr rfl fun p _ => by ring
    · by_contra hpS
      exact hp (by simp [hv p (by simpa using hpS)])
  have e3 : I P (D + 1) (Fin.snoc L A) - I P (D + 1) (Fin.snoc L A') =
      I P (D + 1) (Fin.snoc L (A.tensor B)) - I P (D + 1) (Fin.snoc L (A'.tensor B)) := by
    rw [e1, e2]; ring
  rw [e3, r1, r2, s1, s2, hor, ar, ← vert]
  ring

end GlobalTheory.CompanionTheory.Ar.Num.Link
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

theorem _root_.GlobalTheory.T.flag_m3_from_local : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ), (p : O) ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j j' : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin (j + j'))) (lie : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j) (fun _ : Ψ => j')) σ))) (om : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j') (fun _ : Ψ => j)) σ))), (∀ τ, lie (Sum.inl τ) = T.comp fun i : Fin j => (τ, Fin.castAdd j' i)) → (∀ τ, om (Sum.inl τ) = T.comp fun i : Fin j' => (τ, Fin.natAdd j i)) → (∀ τ k Q, Q.length + k = d + 1 → laNum P (p : O) (lie (Sum.inr τ)).x k Q = laNum P (p : O) (fun i : Fin j' => -T.x (τ, Fin.natAdd j i)) k Q) → LabelChernComparison P d p φ lie om → FlagChernComparison P d p j φ T := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.flag_m3_of_local_m3 | exact GlobalTheory.CompanionTheory.Ar.Num.flag_m3_of_local_m3 | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.flag_m3_of_local_m3 <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.flag_height_polynomial_eval : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) = eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow | exact GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hhFl_linRoot_pow <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rt_nefgen : PB.NefPol → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 :=
  @RootFieldNumerics.tower_nef_generic_dominant

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.real_tower_arith_agreement : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) (R : RealTie M S n) (lam : Wt Ψ N) (s : ℝ), 0 < n ∧ (∀ t, 0 < t → t ≤ S.t₀ → (n : ℝ) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.FT II t)) ∧ ((∀ w, Tendsto (fun t => R.Re.num II t w) (𝓝[>] 0) (𝓝 (R.Re.limNum II w))) → 0 < S.t₀ → M.Converges II ∧ (n : ℝ) * M.PP II (linA lam s ^ (dimFl Ψ N + 1)) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) (R.Re.PB II)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees | exact GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.RootNum.arith_degrees <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.real_tower_geometric_agreement : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (S : PB.AnSys (dimFl Ψ N) (Option (Ψ × Fin N))) (n : ℕ) (R : RealTie M S n) (lam : Wt Ψ N) (s : ℝ), (n : ℝ) * M.geoFun (linA lam s ^ dimFl Ψ N) = eval (PB.gapS (fun x => lam x.1 x.2) (s / M.kA)) S.degPoly := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.geoFun_linA_pow_of_realTie | exact GlobalTheory.CompanionTheory.Ar.Top.geoFun_linA_pow_of_realTie | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.geoFun_linA_pow_of_realTie <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem _root_.GlobalTheory.T.cm_host_rank_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 2 ≤ hostRd E ∧ Nonempty (CMType H) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | exact GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem _root_.GlobalTheory.T.flag_chain_unit_log_integral : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ k₀ : K, (∀ a : K, a = k₀) → ∀ j : K → FlBlock Ψ N, IsChain j → ptsIntegral (PPart j) (pot fun _ : Fin (N - 1) => unitLine j k₀) (fun _ => 1) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.Base.ptsIntegral_first <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem kleiman_generic_fibre_integral : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement → (∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι) → ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι), IsArithVar W (e + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j W', IsArithVar W' 2 → W ≤ W' → 0 ≤ geomDeg W' (L j) 1) → 0 ≤ ptsIntegral W (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
  RootFieldNumerics.arithmetic_intersection_divisor_support

end GlobalTheory.CompanionTheory.Ar.Top
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.root_model_point_height_degree : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ) (W : Ideal (MRing M.ι)), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.IsPt W → 0 < degC W ∧ II M.K M.ι W 1 ![combLine (M.line t) n] = q * M.ht II t lam s W * degC W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple | exact GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple <;> assumption)
end
