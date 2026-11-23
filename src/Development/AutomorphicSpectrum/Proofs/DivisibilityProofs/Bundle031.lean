module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle010
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.RecSplit

section SlopeTestRemainingChoices

variable {K : Type} {ι : K → Type}

theorem intNumL_ofFn [DecidableEq K] (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem exists_prime_mem (W : Ideal (MRing ι ℤ)) (hW : W.IsPrime) (h : ¬ IsHorizontal W) :
    ∃ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W := by
  set J : Ideal ℤ := W.comap (C : ℤ →+* MRing ι ℤ) with hJ
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hJ0 : J ≠ ⊥ := h
  obtain ⟨g, hg⟩ : ∃ g : ℤ, J = Ideal.span {g} := ⟨_, (Ideal.span_singleton_generator J).symm⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hJ0 (by simpa using hg)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).1 (hg ▸ hJp)
  refine ⟨⟨g.natAbs, Int.prime_iff_natAbs_prime.1 hgp⟩, ?_⟩
  have : ((g.natAbs : ℕ) : ℤ) ∈ J := by
    rw [hg]
    exact Ideal.mem_span_singleton.2 (Int.dvd_natAbs.2 dvd_rfl)
  exact this

variable [Fintype K] [∀ k, Fintype (ι k)]

theorem divCycle_eq_zero_of_not_mem (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : W ∉ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s) : divCycle P s W = 0 := by
  unfold divCycle
  exact dif_neg h

theorem mem_of_divCycle_ne (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : divCycle P s W ≠ 0) : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by
  by_contra hc
  exact h (divCycle_eq_zero_of_not_mem P s W hc)

theorem multAt_eq (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s) :
    ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℤ) = divCycle P s W := by
  rw [← VocabDivCycle.proof ℤ K ι P s W]
  congr 1
  classical
  show _ = (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0)
  rw [if_pos h]

end SlopeTestRemainingChoices

section Main

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
noncomputable def vertTerm (p : Nat.Primes) (W : Ideal (MRing ι ℤ)) (l : List (K → ℤ)) : ℤ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  if (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W then intNumL (ZMod p) (extTo (ZMod p) W) l else 0

theorem vertTerm_of_not_mem (p : Nat.Primes) (W : Ideal (MRing ι ℤ)) (l : List (K → ℤ))
    (h : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∉ W) : vertTerm p W l = 0 := by
  unfold vertTerm
  exact if_neg h

theorem vertAt_eq_sum (p : Nat.Primes) (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (l : List (K → ℤ))
    (T : Finset (Ideal (MRing ι ℤ))) (hT : Function.support (divCycle P s) ⊆ T) :
    vertAt p P s l = ∑ W ∈ T, divCycle P s W * vertTerm p W l := by
  unfold vertAt cycEval
  exact finsum_eq_sum_of_support_subset _ fun W hW => hT (left_ne_zero_of_mul hW)

theorem key_of_mem {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    {W : Ideal (MRing ι ℤ)} (hW : divCycle P s W ≠ 0) (p : Nat.Primes)
    (hp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W) :
    charOf W = p ∧ ¬ IsHorizontal W ∧ geoNum D W b = vertTerm p W (List.ofFn b) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.vertical_divisor_geometric_number K ι P D hP a s hs hsP W hW (p : ℕ) hp
  refine ⟨h1, h2, ?_⟩
  rw [h3 b]
  unfold vertTerm
  rw [if_pos hp, intNumL_ofFn]

theorem support_term_subset {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    (W : Ideal (MRing ι ℤ)) {p : Nat.Primes} (hW : divCycle P s W ≠ 0)
    (hp : vertTerm p W (List.ofFn b) ≠ 0) : charOf W = p := by
  by_cases hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W
  · exact (key_of_mem hP hs hsP b hW p hm).1
  · exact absurd (vertTerm_of_not_mem p W _ hm) hp


open Classical in
theorem finsum_term {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    (W : Ideal (MRing ι ℤ)) :
    ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * ((divCycle P s W * vertTerm p W (List.ofFn b) : ℤ) : ℝ) =
      (divCycle P s W : ℝ) *
        (if IsHorizontal W then 0 else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
  by_cases hW : divCycle P s W = 0
  · simp [hW]
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
    have : vertTerm p W (List.ofFn b) = 0 := by
      by_contra hne
      by_cases hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W
      · exact (key_of_mem hP hs hsP b hW p hm).2.1 hh
      · exact hne (vertTerm_of_not_mem p W _ hm)
    simp [this]
  · rw [if_neg hh]
    have hWp : W.IsPrime := (mem_of_divCycle_ne P s W hW).1.1.1
    obtain ⟨q, hq⟩ := exists_prime_mem W hWp hh
    obtain ⟨hc, -, hg⟩ := key_of_mem hP hs hsP b hW q hq
    rw [finsum_eq_single _ q]
    · rw [hc, hg]
      push_cast
      ring
    · intro p hpq
      have : vertTerm p W (List.ofFn b) = 0 := by
        by_contra hne
        have h2 := support_term_subset hP hs hsP b W hW hne
        exact hpq (Nat.Primes.coe_nat_injective (h2.symm.trans hc))
      simp [this]

theorem recR_split : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (a : K → ℕ) (s : MRing ι ℤ), IsMultiHomog s a → s ∉ P → ∀ (L : Fin D → HermLine ι) (A : HermLine ι), (Function.support fun p : Nat.Primes => vertAt p P s (List.ofFn fun j => (L j).a)).Finite ∧ recR I P L A s = (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) + (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn fun j => (L j).a) : ℝ)) - arInt P s A L := by
  intro K _ _ ι _ P D hP I a s hs hsP L A
  classical
  set b : Fin D → K → ℤ := fun j => (L j).a with hb
  set T : Finset (Ideal (MRing ι ℤ)) := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).toFinset with hT
  have hTm : ∀ W, W ∈ T ↔ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := fun W => by simp [hT]
  have hsub : Function.support (divCycle P s) ⊆ T := fun W hW =>
    (hTm W).2 (mem_of_divCycle_ne P s W hW)
  constructor
  · have hfin : ((fun W : Ideal (MRing ι ℤ) => charOf W) '' (T : Set _)).Finite :=
      T.finite_toSet.image _
    refine (hfin.preimage (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_
    have hp' : vertAt p P s (List.ofFn b) ≠ 0 := hp
    rw [vertAt_eq_sum p P s _ T hsub] at hp'
    obtain ⟨W, hWT, hW⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
    exact ⟨W, hWT, support_term_subset hP hs hsP b W (left_ne_zero_of_mul hW)
      (right_ne_zero_of_mul hW)⟩
  · have h1 : (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s,
          ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) =
        ∑ W ∈ T, (divCycle P s W : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
      refine Finset.sum_congr rfl fun W hW => ?_
      rw [← multAt_eq P s W ((hTm W).1 hW)]
      norm_cast
    have h2 : (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
        ∑ W ∈ T, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
      refine finsum_eq_sum_of_support_subset _ fun W hW => hsub ?_
      have := left_ne_zero_of_mul hW
      exact fun h0 => this (by simp [h0])
    have h3 : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ)) =
        ∑ W ∈ T, (divCycle P s W : ℝ) *
          (if IsHorizontal W then 0 else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
      have e : ∀ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ) =
          ∑ W ∈ T, Real.log (p : ℕ) * ((divCycle P s W * vertTerm p W (List.ofFn b) : ℤ) : ℝ) := by
        intro p
        rw [vertAt_eq_sum p P s _ T hsub, Int.cast_sum, Finset.mul_sum]
      simp_rw [e]
      rw [finsum_sum_comm]
      · exact Finset.sum_congr rfl fun W _ => finsum_term hP hs hsP b W
      · intro W _
        refine ((Set.finite_singleton (charOf W)).preimage
          (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_
        have hne := right_ne_zero_of_mul (show _ ≠ (0 : ℝ) from hp)
        have hne' : divCycle P s W * vertTerm p W (List.ofFn b) ≠ 0 := by exact_mod_cast hne
        exact (support_term_subset hP hs hsP b W (left_ne_zero_of_mul hne')
          (right_ne_zero_of_mul hne')).symm
    have h0 : recR I P L A s = (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s,
          ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) -
        arInt P s A L := rfl
    rw [h0, h1, h2, h3, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hh : IsHorizontal W
    · simp [hh, Set.indicator]
    · simp [hh, Set.indicator]

end Main

end GlobalTheory.CompanionTheory.Ar.Num.RecSplit
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.divisor_cycle_substitution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (a a' : K → ℕ) (f g : MRing ι O), IsMultiHomog f a → IsMultiHomog g a' → f ∉ P → g ∉ P → ∀ (σ σ' : Type) [Fintype σ] (cls : σ → K → ℤ) (M : σ' → σ → ℤ) (H : MvPolynomial σ' ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (ratDiv P f g) (fun t => ∑ i, M t i • cls i) H Q = cycNum (ratDiv P f g) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q ∧ cycNum (divCycle P f) (fun t => ∑ i, M t i • cls i) H Q = cycNum (divCycle P f) cls (aeval (fun t => ∑ i, (C (M t i : ℝ) * X i : MvPolynomial σ ℝ)) H) Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_linear_subst <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ZTop

theorem isFibreComp_variety {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {W : Ideal (MRing ι O)} (hW : IsFibreComp P W) :
    IsMultiProjPrime (specialIdeal W) ∧
      ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hmin, hrel⟩ := hW
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmin
  refine PairNumberJoinLeft.verticalComponentFibre O ϖ hϖ K ι P d hP (C ϖ) 0
    (isWeightedHomogeneous_C _ _) (fun h => hϖ.ne_zero ?_) W hmin hrel
    (hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  exact Ideal.mem_bot.mp (hP.noTorsion ▸ Ideal.mem_comap.mpr h)

theorem cast_classNum {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    ((classNum cls H Q W : ℤ) : ℝ) =
      genNum (IsLocalRing.ResidueField O) (specialIdeal W) cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q := by
  unfold classNum genNum
  rw [MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℝ))]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_map]
  rfl

theorem powerSumsVanish_of_trivFlagAt :
    NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
      Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ),
      (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  intro hS O _ _ _ ϖ hϖ K _ _ ι _ P d hP N x hx W hW k hk Q hQ
  obtain ⟨Ω, _, _, y, w, hy, hflag⟩ := hx W hW
  obtain ⟨hprime, hdim⟩ := isFibreComp_variety hϖ hP hW
  have h := GlobalTheory.T.flag_frame_point_dimension hS (IsLocalRing.ResidueField O) Ω K ι y d (hy ▸ hprime) (hy ▸ hdim) N w x hflag
    k hk Q hQ
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin N) ℤ k) = ∑ i, X i ^ k := by
    simp [psum]
  have h2 := cast_classNum x (psum (Fin N) ℤ k) Q W
  rw [hmap, ← hy, h] at h2
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Num.ZTop
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem degree_prod_monic {σ ι : Type*} (m : MonomialOrder σ) (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) (d : ι → σ →₀ ℕ)
    (h : ∀ i ∈ s, m.degree (P i) = d i ∧ m.leadingCoeff (P i) = 1) :
    m.degree (∏ i ∈ s, P i) = ∑ i ∈ s, d i ∧ m.leadingCoeff (∏ i ∈ s, P i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [m.degree_one, m.leadingCoeff_one]
  | insert a s has ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ha1, ha2⟩ := h a (Finset.mem_insert_self a s)
    have hne : ∀ f : MvPolynomial σ ℝ, m.leadingCoeff f = 1 → f ≠ 0 := fun f hf =>
      m.leadingCoeff_ne_zero_iff.mp (by rw [hf]; exact one_ne_zero)
    rw [Finset.prod_insert has, Finset.sum_insert has,
      m.degree_mul (hne _ ha2) (hne _ ih2), m.leadingCoeff_mul, ha1, ih1, ha2, ih2]
    simp

theorem lex_sum_Ico {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] {n : ℕ} (v : Fin n → σ)
    (hv : StrictMono v) {a b : Fin n} (hab : a < b) :
    (MonomialOrder.lex : MonomialOrder σ).degree (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ))
        = Finsupp.single (v a) 1 ∧
      (MonomialOrder.lex : MonomialOrder σ).leadingCoeff
        (∑ s ∈ Finset.Ico a b, (X (v s) : MvPolynomial σ ℝ)) = 1 := by
  have hlt : ∀ s, a < s → (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v s) 1) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := fun s hs =>
    MonomialOrder.lex_lt_iff.mpr (Finsupp.Lex.single_strictAnti (hv hs))
  have hzero : (MonomialOrder.lex : MonomialOrder σ).toSyn 0 <
      (MonomialOrder.lex : MonomialOrder σ).toSyn (Finsupp.single (v a) 1) := by
    rw [map_zero, ← MonomialOrder.bot_eq_zero]
    refine bot_lt_iff_ne_bot.mpr fun h => ?_
    rw [MonomialOrder.bot_eq_zero] at h
    have h0 := (MonomialOrder.lex : MonomialOrder σ).toSyn.injective (h.trans (map_zero _).symm)
    simp at h0
  have hdegX : (MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)
      = Finsupp.single (v a) 1 := MonomialOrder.degree_X
  have hrest : (MonomialOrder.lex : MonomialOrder σ).toSyn
      ((MonomialOrder.lex : MonomialOrder σ).degree
        (∑ s ∈ Finset.Ioo a b, (X (v s) : MvPolynomial σ ℝ))) <
      (MonomialOrder.lex : MonomialOrder σ).toSyn
        ((MonomialOrder.lex : MonomialOrder σ).degree (X (v a) : MvPolynomial σ ℝ)) := by
    rw [hdegX, MonomialOrder.degree_lt_iff hzero]
    intro c hc
    obtain ⟨s, hs, hcs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hc)
    rw [X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hcs
    rw [hcs]
    exact hlt s (Finset.mem_Ioo.mp hs).1
  rw [← Finset.Ioo_insert_left hab, Finset.sum_insert (by simp)]
  refine ⟨?_, ?_⟩
  · rw [MonomialOrder.degree_add_of_lt hrest, hdegX]
  · rw [MonomialOrder.leadingCoeff_add_of_lt hrest, MonomialOrder.leadingCoeff_X]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffDelta

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg

theorem rhoM_eq_sum (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    (∑ τ : Ψ, ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1 : (Ψ × Fin N) →₀ ℕ)
      = rhoM Ψ N := by
  ext ⟨τ, a⟩
  simp only [Finset.sum_apply', Finsupp.single_apply, Prod.mk.injEq]
  rw [Finset.sum_eq_single τ, Finset.sum_eq_single a]
  · simp [rhoM, Fin.card_Ioi]
  · intro b _ hb; simp [hb]
  · simp
  · intro τ' _ h; simp [h]
  · simp

theorem coeff_rhoM_gapDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    AddMonoidAlgebra.coeff (gapDelta Ψ N) (rhoM Ψ N) = 1 := by
  let e := Fintype.equivFin Ψ
  letI : LinearOrder (Ψ × Fin N) :=
    LinearOrder.lift' (fun p => toLex (e p.1, p.2)) (fun p q h => by
      have h' : (e p.1, p.2) = (e q.1, q.2) := toLex.injective h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h'
      exact Prod.ext (e.injective h1) h2)
  haveI : WellFoundedGT (Ψ × Fin N) := Finite.to_wellFoundedGT
  have hv : ∀ τ : Ψ, StrictMono (fun s : Fin N => (τ, s)) := fun τ s t hst => by
    show toLex (e τ, s) < toLex (e τ, t)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hst⟩)
  have key := CoeffDelta.degree_prod_monic (MonomialOrder.lex : MonomialOrder (Ψ × Fin N))
    Finset.univ
    (fun τ : Ψ => ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, ∑ s ∈ Finset.Ico a b, (X (τ, s) : MvPolynomial _ ℝ))
    (fun τ => ∑ a : Fin N, ∑ _b ∈ Finset.Ioi a, Finsupp.single (τ, a) 1)
    (fun τ _ => CoeffDelta.degree_prod_monic _ Finset.univ _ _ fun a _ =>
      CoeffDelta.degree_prod_monic _ _ _ _ fun b hb =>
        CoeffDelta.lex_sum_Ico (fun s => (τ, s)) (hv τ) (Finset.mem_Ioi.mp hb))
  have h2 := key.2
  rw [MonomialOrder.leadingCoeff, key.1, rhoM_eq_sum] at h2
  exact h2

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem prod_range_sub_eq_factorial (i n : ℕ) :
    ∏ k ∈ Finset.range n, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (((n - 1 - i).factorial : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : i < n
    · obtain ⟨t, rfl⟩ : ∃ t, n = i + 1 + t := ⟨n - (i + 1), by omega⟩
      have e1 : i + 1 + t - 1 - i = t := by omega
      have e2 : i + 1 + t + 1 - 1 - i = t + 1 := by omega
      rw [if_pos h, e1, e2, Nat.factorial_succ]
      push_cast
      ring
    · have e1 : n - 1 - i = 0 := by omega
      have e2 : n + 1 - 1 - i = 0 := by omega
      rw [if_neg h, e1, e2]
      simp

theorem prod_rhoM_factorial (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∏ p, (((rhoM Ψ N) p).factorial : ℝ) =
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
  have h := prod_range_sub_eq_factorial (i : ℕ) N
  rw [← Fin.prod_univ_eq_prod_range (fun k => if (i : ℕ) < k then ((k : ℝ) - ((i : ℕ) : ℝ)) else 1) N] at h
  have hr : (rhoM Ψ N) (τ, i) = N - 1 - (i : ℕ) := rfl
  rw [hr, ← h]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Fin.lt_def]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.root_model_log_integral_formula : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Fin (dimFl Ψ N) → Wt Ψ N) (s : Fin (dimFl Ψ N) → ℝ) (q : ℕ) (n : Fin (dimFl Ψ N) → Option (Ψ × Fin N) → ℤ), (∀ k j, (n k j : ℝ) = q * M.coef (lam k) (s k) j) → ptsIntegral M.P (fun k z => Real.log ((combLine (M.line t) (n k)).h z)) (fun _ => 1) = M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (∏ k, linA (lam k) (s k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed | exact GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed <;> assumption)
end
