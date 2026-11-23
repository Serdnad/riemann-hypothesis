module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle066
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem LocalQuotFinsum.proof (h : LocalQuotPrimes.Statement.{u}) : LocalQuotFinsum.Statement.{u} := by
  intro R _ P U _ hPU F F' hF hF' hFF'
  have hP := h R P U hPU
  set S : Set (Ideal R) := {G | G.IsPrime ∧ P ≤ G ∧ G ≤ U} with hS
  set T : Set (Ideal (localQuot P U)) := {p | p.IsPrime} with hT
  have h1 : ∑ᶠ G, F G = ∑ᶠ G ∈ S, F G := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro G hG
    exact ⟨fun _ => hF G hG, fun _ => Set.mem_univ G⟩
  have h2 : ∑ᶠ p, F' p = ∑ᶠ p ∈ T, F' p := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro p hp
    exact ⟨fun _ => hF' p hp, fun _ => Set.mem_univ p⟩
  have hbij : S.BijOn (fun G => G.map (localQuotMap P U)) T := by
    refine ⟨fun G hG => (hP.1 G hG.1 hG.2.1 hG.2.2).1, ?_, ?_⟩
    · intro G₁ hG₁ G₂ hG₂ he
      have e₁ := (hP.1 G₁ hG₁.1 hG₁.2.1 hG₁.2.2).2
      have e₂ := (hP.1 G₂ hG₂.1 hG₂.2.1 hG₂.2.2).2
      simp only at he
      rw [← e₁, ← e₂, he]
    · intro p hp
      obtain ⟨hle, hleU, hmap⟩ := hP.2 p hp
      exact ⟨p.comap (localQuotMap P U), ⟨by have : p.IsPrime := hp; exact Ideal.comap_isPrime _ p, hle, hleU⟩, hmap⟩
  rw [h1, h2]
  exact finsum_mem_eq_of_bijOn _ hbij fun G hG => hFF' G hG.1 hG.2.1 hG.2.2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem localizedModule_quot_nontrivial {R : Type u} [CommRing R] (J W : Ideal R) [W.IsPrime]
    (hJW : J ≤ W) : Nontrivial (LocalizedModule W.primeCompl (R ⧸ J)) := by
  refine ⟨⟨LocalizedModule.mk (1 : R ⧸ J) 1, 0, fun h => ?_⟩⟩
  rw [← LocalizedModule.zero_mk (1 : W.primeCompl), LocalizedModule.mk_eq] at h
  obtain ⟨v, hv⟩ := h
  have hv' : ((v : R) : R ⧸ J) = 0 := by
    simpa [Submonoid.smul_def, Algebra.smul_def] using hv
  exact v.2 (hJW (Ideal.Quotient.eq_zero_iff_mem.mp hv'))

theorem LocCyclePos.proof : LocCyclePos.Statement := by
  intro R _ _ J W hW
  have : W.IsPrime := hW.1.1
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hW
  unfold ReciprocityTheory.ChartRestriction.G.AI.locLen at hfin
  have := localizedModule_quot_nontrivial J W hW.1.2
  have hpos : 0 < Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.length_pos
  unfold locCycle
  rw [dite_eq_left hW]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  simp only at hn
  rw [← hn] at hpos ⊢
  simp only [ENat.toNat_natCast, Nat.cast_pos]
  exact_mod_cast hpos

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem enat_eq_two_of_le_of_lt {x : ℕ∞} (h2 : 2 ≤ x) (h3 : x < 3) : x = 2 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h3 (by simp)
  | coe n =>
    have a : 2 ≤ n := by exact_mod_cast h2
    have b : n < 3 := by exact_mod_cast h3
    have : n = 2 := by omega
    subst this; rfl

private theorem enat_le_one_of_add_one_le_two {x : ℕ∞} (h : x + 1 ≤ 2) : x ≤ 1 := by
  induction x using ENat.recTopCoe with
  | top => exact absurd h (by simp)
  | coe n =>
    have : n + 1 ≤ 2 := by exact_mod_cast h
    exact_mod_cast (by omega : n ≤ 1)

theorem LocalDomainDimTwo.proof : LocalDomainDimTwo.Statement := by
  intro A _ _ _ _ hno hQ
  obtain ⟨Q, hQp, h0, hQm⟩ := hQ
  have := hQp
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm
  have hm2 : (2 : ℕ∞) ≤ (IsLocalRing.maximalIdeal A).height :=
    le_trans (by rw [← one_add_one_eq_two]; exact add_le_add (le_trans le_add_self e1) le_rfl) e2
  have hm3 : (IsLocalRing.maximalIdeal A).height < 3 := by
    by_contra h3
    have hle : ((3 : ℕ) : ℕ∞) ≤ Order.height (IsLocalRing.closedPoint A) := by
      rw [← PrimeSpectrum.height_eq_orderHeight]
      exact not_lt.mp h3
    obtain ⟨p, hlast, hlen⟩ := Order.exists_series_of_le_height _ hle
    have s0 := p.step ⟨0, by omega⟩
    have s1 := p.step ⟨1, by omega⟩
    have s2 := p.step ⟨2, by omega⟩
    have e01 : (Fin.succ (⟨0, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨1, by omega⟩ := Fin.ext rfl
    have e12 : (Fin.succ (⟨1, by omega⟩ : Fin p.length)) = Fin.castSucc ⟨2, by omega⟩ := Fin.ext rfl
    have e2l : (Fin.succ (⟨2, by omega⟩ : Fin p.length)) = Fin.last p.length := Fin.ext (by simp [hlen])
    rw [e01] at s0
    rw [e12] at s1
    rw [e2l] at s2
    have hl : p.toFun (Fin.last p.length) = IsLocalRing.closedPoint A := hlast
    rw [hl] at s2
    refine hno (p.toFun (Fin.castSucc ⟨1, by omega⟩)).asIdeal (p.toFun (Fin.castSucc ⟨2, by omega⟩)).asIdeal
      (p.toFun _).isPrime (p.toFun _).isPrime ?_ ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s1)
      ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s2)
    exact lt_of_le_of_lt bot_le ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr s0)
  have hm : (IsLocalRing.maximalIdeal A).height = 2 := enat_eq_two_of_le_of_lt hm2 hm3
  refine ⟨?_, hm, ?_⟩
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm]
    rfl
  · intro Q' hQ' h0' hQm'
    have := hQ'
    have f1 := Ideal.height_add_one_le_of_lt_of_isPrime h0'
    have f2 := Ideal.height_add_one_le_of_lt_of_isPrime hQm'
    rw [hm] at f2
    exact le_antisymm (enat_le_one_of_add_one_le_two f2) (le_trans le_add_self f1)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MinimalPrimesSpanSingleton.proof : MinimalPrimesSpanSingleton.Statement.{u} := by
  intro A _ _ _ x hx W
  constructor
  · intro hW
    have hWp : W.IsPrime := hW.isPrime
    have hxW : x ∈ W := hW.1.2 (Ideal.mem_span_singleton_self x)
    refine ⟨hWp, ?_, hxW⟩
    have hle : W.height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) W hW
    have hne : W.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
      intro hbot
      rw [hbot, Ideal.mem_bot] at hxW
      exact hx hxW
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  · rintro ⟨hWp, hh, hxW⟩
    refine ⟨⟨hWp, (Ideal.span_singleton_le_iff_mem W).mpr hxW⟩, ?_⟩
    rintro Q ⟨hQp, hxQ⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun h => hWQ (h ▸ le_refl Q))
    have hfin : W.FiniteHeight := W.finiteHeight_iff.mpr (Or.inr (by rw [hh]; exact ENat.one_ne_top))
    have hQh : Q.height < 1 := hh ▸ Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
    have hQ0 : Q.height = 0 := Order.lt_one_iff.mp hQh
    rw [Ideal.height_eq_zero_iff_eq_bot] at hQ0
    have hx0 : x ∈ (⊥ : Ideal A) := hQ0 ▸ (Ideal.span_singleton_le_iff_mem Q).mp hxQ
    exact hx ((Ideal.mem_bot).mp hx0)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing

noncomputable section

namespace DimTwoSumReading

variable {A : Type*} [CommRing A]

theorem length_loc_eq_ordLoc (W : Ideal A) [hW : W.IsPrime] (a : A) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc ⟨W, hW⟩ a := by
  have h := length_localizedModule_quot_eq (T := Localization.AtPrime W) W.primeCompl ⊥ a
    (fun s hs => IsLocalization.map_units _ (⟨s, hs⟩ : W.primeCompl))
    (fun y => by
      obtain ⟨⟨r, s⟩, hy⟩ := IsLocalization.surj W.primeCompl y
      exact ⟨r, s, s.2, hy.symm⟩)
    (fun r hr => by
      obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff W.primeCompl _ r).mp hr
      exact ⟨s, s.2, (Ideal.mem_bot).mpr hs⟩)
    (fun v hv => by rw [(Ideal.mem_bot).mp hv, map_zero])
  rw [bot_sup_eq] at h
  exact h

theorem length_max_eq_ordMod [IsLocalRing A] (W : Ideal A) [hW : W.IsPrime] (b : A) :
    Module.length (Localization.AtPrime (maximalIdeal A))
        (LocalizedModule (maximalIdeal A).primeCompl (A ⧸ (W ⊔ Ideal.span {b}))) =
      ordMod ⟨W, hW⟩ b := by
  have h := length_localizedModule_quot_eq (T := A ⧸ W) (maximalIdeal A).primeCompl W b
    (fun s hs => (notMem_maximalIdeal.mp hs).map _)
    (fun y => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨r, 1, (maximalIdeal A).primeCompl.one_mem, by simp⟩)
    (fun r hr => ⟨1, (maximalIdeal A).primeCompl.one_mem, by
      rw [one_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mp hr⟩)
    (fun v hv => Ideal.Quotient.eq_zero_iff_mem.mpr hv)
  rw [h, ordMod, Ring.ord, Ideal.Quotient.algebraMap_eq]

variable [IsDomain A] [IsNoetherianRing A]

theorem mem_minimalPrimes_iff {a : A} (ha : a ≠ 0) (W : Ideal A) [W.IsPrime] :
    W ∈ (Ideal.span {a}).minimalPrimes ↔ W.height = 1 ∧ a ∈ W := by
  have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  constructor
  · intro hW
    have haW : a ∈ W := hW.1.2 (Ideal.subset_span rfl)
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) W hW
    have h0 : W.height ≠ 0 := fun h => ha ((Ideal.mem_bot).mp (Ideal.height_eq_zero_iff_eq_bot.mp h ▸ haW))
    exact ⟨le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), haW⟩
  · rintro ⟨h1, haW⟩
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := W)
      ((Ideal.span_singleton_le_iff_mem W).mpr haW)
    rcases hQW.lt_or_eq with hlt | rfl
    · have := hQ.1.1
      have haQ : a ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
      have hbQ : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun h => ha ((Ideal.mem_bot).mp (h ▸ haQ))
      have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hbQ
      have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, zero_add] at e1
      rw [h1] at e2
      have : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add e1 le_rfl) e2
      exact absurd this (by decide)
    · exact hQ


omit [IsDomain A] [IsNoetherianRing A] in
theorem max_mem_minimalPrimes [IsLocalRing A] (h2 : ringKrullDim A = 2) (W : Ideal A) [hW : W.IsPrime]
    (h1 : W.height = 1) {b : A} (hbW : b ∉ W) (hbm : b ∈ maximalIdeal A) :
    maximalIdeal A ∈ (W ⊔ Ideal.span {b}).minimalPrimes := by
  have hle : W ⊔ Ideal.span {b} ≤ maximalIdeal A :=
    sup_le (le_maximalIdeal hW.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  refine ⟨⟨(maximalIdeal.isMaximal A).isPrime, hle⟩, fun Q hQ hQm => ?_⟩
  have := hQ.1
  by_contra hne
  have hlt : Q < maximalIdeal A := lt_of_le_of_ne hQm fun h => hne (h ▸ le_rfl)
  have hWQ : W < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
    hbW (h ▸ hQ.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime hWQ
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm := maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [h2, show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at hm
  rw [WithBot.coe_injective hm] at e2
  rw [h1] at e1
  have : (1 : ℕ∞) + 1 + 1 ≤ 2 := le_trans (add_le_add e1 le_rfl) e2
  exact absurd this (by decide)

end DimTwoSumReading


open DimTwoSumReading in
theorem DimTwoSumReading.proof : DimTwoSumReading.Statement := by
  intro A _ _ _ _ h2 a b ha hab
  classical
  have hT : {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).preimage
      (fun p _ q _ h => PrimeSpectrum.ext h)).subset
      (fun p hp => (mem_minimalPrimes_iff ha p.asIdeal).mpr hp)
  have key : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 ∧ a ∈ p.asIdeal →
      (locCycle (Ideal.span {a}) p.asIdeal = ((ordLoc p a).toNat : ℤ) ∧ ordLoc p a ≠ ⊤) ∧
      (locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = ((ordMod p b).toNat : ℤ) ∧
        ordMod p b ≠ ⊤) := by
    intro p hp
    have hmin := (mem_minimalPrimes_iff ha p.asIdeal).mpr hp
    have hlA := length_loc_eq_ordLoc p.asIdeal a
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold locCycle; rw [dite_eq_left hmin]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlA
    · rw [← hlA]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmin
    by_cases hbm : b ∈ maximalIdeal A
    · have hmm := max_mem_minimalPrimes h2 p.asIdeal hp.1 (hab _ p.isPrime hp.1 hp.2) hbm
      have hlB := length_max_eq_ordMod p.asIdeal b
      refine ⟨?_, ?_⟩
      · unfold locCycle; rw [dite_eq_left hmm]; exact congrArg (fun x : ℕ∞ => (x.toNat : ℤ)) hlB
      · rw [← hlB]; exact ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hmm
    · have h0 : ordMod p b = 0 := Ring.ord_of_isUnit ((notMem_maximalIdeal.mp hbm).map _)
      have hnm : maximalIdeal A ∉ (p.asIdeal ⊔ Ideal.span {b}).minimalPrimes := fun h =>
        hbm (h.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      rw [h0]
      refine ⟨?_, ENat.zero_ne_top⟩
      unfold locCycle; rw [dite_eq_right hnm]; rfl
  have hsupp : Function.support (fun W : Ideal A => locCycle (Ideal.span {a}) W *
      locCycle (W ⊔ Ideal.span {b}) (maximalIdeal A)) ⊆
      (hT.toFinset.map ⟨PrimeSpectrum.asIdeal, by intro p q h; exact PrimeSpectrum.ext h⟩ : Finset (Ideal A)) := by
    intro W hW
    have hne : locCycle (Ideal.span {a}) W ≠ 0 := left_ne_zero_of_mul hW
    have hmin : W ∈ (Ideal.span {a}).minimalPrimes := by
      by_contra h
      exact hne (by unfold locCycle; rw [dite_eq_right h])
    have := hmin.1.1
    rw [Finset.coe_map, Set.Finite.coe_toFinset]
    exact ⟨⟨W, hmin.1.1⟩, (mem_minimalPrimes_iff ha W).mp hmin, rfl⟩
  refine ⟨∑ p ∈ hT.toFinset, (ordLoc p a).toNat * (ordMod p b).toNat, ?_, ?_⟩
  · rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_map]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    show locCycle (Ideal.span {a}) p.asIdeal * locCycle (p.asIdeal ⊔ Ideal.span {b}) (maximalIdeal A) = _
    rw [hk.1.1, hk.2.1]
  · refine (finsum_mem_eq_finite_toFinset_sum (fun p => ordLoc p a * ordMod p b) hT).trans ?_
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    have hk := key p (hT.mem_toFinset.mp hp)
    rw [ENat.natCast_toNat hk.1.2, ENat.natCast_toNat hk.2.2]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem LocCycleSpanMul.mem_minimalPrimes_iff {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {z : A} (hz : z ≠ 0) (W : Ideal A) :
    W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ z ∈ W :=
  _root_.UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff hz W

theorem LocCycleSpanMul.proof : LocCycleSpanMul.Statement := by
  intro A _ _ _ x y hx hy W
  by_cases hP : W.IsPrime ∧ W.height = 1
  · obtain ⟨hp, h1⟩ := hP
    have key : ∀ z : A, z ≠ 0 →
        locCycle (Ideal.span {z}) W = ((locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩).toNat : ℤ) ∧
          locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ ≠ ⊤ := by
      intro z hz
      by_cases hzW : z ∈ W
      · have hm : W ∈ (Ideal.span {z}).minimalPrimes :=
          (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mpr ⟨hp, h1, hzW⟩
        refine ⟨?_, locLen_ne_top hm⟩
        unfold locCycle
        rw [dite_eq_left hm]
        rfl
      · have hm : W ∉ (Ideal.span {z}).minimalPrimes := fun h =>
          hzW ((LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp h).2.2
        have h0 : locLen (A ⧸ Ideal.span {z}) ⟨W, hp⟩ = 0 := by
          have := locLen_quot_eq_zero (V := (⊥ : Ideal A)) (g := z) ⟨W, hp⟩ hzW
          rwa [bot_sup_eq] at this
        refine ⟨?_, by rw [h0]; exact ENat.zero_ne_top⟩
        unfold locCycle
        rw [dite_eq_right hm, h0]
        simp
    obtain ⟨ex, fx⟩ := key x hx
    obtain ⟨ey, fy⟩ := key y hy
    obtain ⟨exy, -⟩ := key (x * y) (mul_ne_zero hx hy)
    have hmul := locLen_mul (V := (⊥ : Ideal A)) Ideal.isPrime_bot (f := x)
      (by rw [Ideal.mem_bot]; exact hx) y ⟨W, hp⟩
    rw [bot_sup_eq, bot_sup_eq, bot_sup_eq] at hmul
    rw [exy, ex, ey, hmul, ENat.toNat_add fy fx]
    push_cast
    ring
  · have hz : ∀ z : A, z ≠ 0 → locCycle (Ideal.span {z}) W = 0 := by
      intro z hz
      unfold locCycle
      rw [dite_eq_right]
      intro hm
      have h := (LocCycleSpanMul.mem_minimalPrimes_iff hz W).mp hm
      exact hP ⟨h.1, h.2.1⟩
    rw [hz _ (mul_ne_zero hx hy), hz x hx, hz y hy]
    simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagCutSpecialize.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (k : ℕ) (hk : k < N),
      pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
      ∀ s h : MRing (bundleIdx (bundleIdx ι M) M') O,
        aeval (flagClosurePt y w e φ φ' t (k + 1)) s =
            flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ * aeval (flagClosurePt y w e φ φ' t (k + 1)) h →
          aeval (flagClosurePt y w e φ φ' t k) s = 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
