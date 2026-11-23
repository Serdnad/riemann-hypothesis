module

import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.GroupWithZero.Indicator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace AdditivityInDivisor

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_add_cycle {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) : cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by
  unfold cycEval
  rw [← finsum_add_distrib (h₁.subset (Function.support_mul_subset_left _ _))
    (h₂.subset (Function.support_mul_subset_left _ _))]
  exact finsum_congr fun W => by simp [add_mul]

theorem cycEval_add_fn {n n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (h : ∀ W, Z W ≠ 0 → n W = n₁ W + n₂ W) : cycEval n Z = cycEval n₁ Z + cycEval n₂ Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW, mul_add]

theorem ratDiv_support_finite {P : Ideal (MRing ι R)} {f g : MRing ι R}
    (hf : (Function.support (divCycle P f)).Finite) (hg : (Function.support (divCycle P g)).Finite) :
    (Function.support (ratDiv P f g)).Finite := by
  refine (hf.union hg).subset fun W hW => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

theorem withBot_lt_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (hx : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  apply GroundTheory.Heights₂.Heights.NumbersDVR.lt_natCast_of_add_one_le <;> assumption

theorem ratDiv_mul_mul (hmul : DivCycleMul.Statement.{u}) {O : Type u} [CommRing O] [IsNoetherianRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    {f₁ g₁ f₂ g₂ : MRing ι O} (hf₁ : f₁ ∉ P) (hf₂ : f₂ ∉ P) (hg₁ : g₁ ∉ P) (hg₂ : g₂ ∉ P) :
    ratDiv P (f₁ * f₂) (g₁ * g₂) = ratDiv P f₁ g₁ + ratDiv P f₂ g₂ := by
  funext W
  simp only [ratDiv, Pi.add_apply, hmul O K ι P f₁ f₂ hP hf₁ hf₂, hmul O K ι P g₁ g₂ hP hg₁ hg₂]
  ring

end AdditivityInDivisor

theorem AdditivityInDivisor.proof (hmul : DivCycleMul.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u})
    (hadd : IntNumAddFirst.Statement.{u}) (hsup : SupSpanMultiHomog.Statement.{u})
    (hmin : MinimalPrimeMultiHomog.Statement.{u}) (hspm : SpecialIdealMultiHomog.Statement.{u})
    (hcor : SpecialIdealCorresp.Statement.{u}) (hqd : SpecialQuotDim.Statement.{u})
    (hdrop : DimStrictDrop.Statement.{u}) : AdditivityInDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b₁ b₂ f₁ g₁ f₂ g₂ hD₁ hD₂ c s hs hsP hsH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have rfin : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ratDiv_support_finite (hfin O K ι Q x) (hfin O K ι Q y)
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [ratDiv_mul_mul hmul hPp hD₁.num_not_mem hD₂.num_not_mem hD₁.den_not_mem hD₂.den_not_mem]
    exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)
  · unfold cutIdentityRightSide
    refine cycEval_add_fn (hfin O K ι P s) fun W hW => ?_
    obtain ⟨hWp, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    split_ifs with hϖW
    ·
      have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        unfold divCycle at hW
        split_ifs at hW with h
        · exact h.1
        · exact absurd rfl hW
      have hWh : IsMultiHomogIdeal W :=
        hmin O K ι _ W (hsup O K ι P s c hP.multiProj.multiHomog hs) hWmin
      have hsW : s ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hsW)
      have hdim := hdrop (MRing ι O) P W hlt
      rw [hP.dim, ← hqd O ϖ hϖ K ι W hϖW,
        show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by ring] at hdim
      exact hadd _ K ι d (specialIdeal W) (hcor O ϖ hϖ K ι P W hWp hϖW).1 (hspm O K ι W hWh)
        (withBot_lt_of_add_one_le hdim) b₁ b₂ L
    ·
      obtain ⟨hV₁, hV₂⟩ := hsH W hW hϖW
      rw [ratDiv_mul_mul hmul hWp hV₁.num_not_mem hV₂.num_not_mem hV₁.den_not_mem hV₂.den_not_mem]
      exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalComponentFibre.proof (h : FibreVarieties.Statement.{0}) :
    VerticalComponentFibre.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP f b hf hfP W hW hrel hϖW
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro hmem
    have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hP.noTorsion, Ideal.mem_bot] at this
    exact hϖ.ne_zero this

  have hmin : W ∈ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).minimalPrimes := by
    refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hϖW)⟩, ?_⟩
    rintro Q ⟨hQ, hQle⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun e => hWQ (e ▸ le_rfl))
    have hPQ : P ≤ Q := le_sup_left.trans hQle
    have hϖQ : (C ϖ : MRing ι O) ∈ Q := hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    let π := Ideal.Quotient.mk P
    have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
    have : (W.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPW)
    have : (Q.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPQ)
    have hle1 : (W.map π).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    have hlt' : Q.map π < W.map π := by
      refine (Ideal.map_mono hlt.le).lt_of_not_ge fun e => hlt.not_ge ?_
      have := Ideal.comap_mono (f := π) e
      rwa [Ideal.comap_map_of_surjective' π hsurj, Ideal.comap_map_of_surjective' π hsurj,
        Ideal.mk_ker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ] at this
    have : (W.map π).FiniteHeight := ⟨Or.inr (hle1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
    have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt').trans_le hle1
    rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
    have hbot : Q.map π ≤ ⊥ := h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    have : π (C ϖ) ∈ (⊥ : Ideal (MRing ι O ⧸ P)) := hbot (Ideal.mem_map_of_mem π hϖQ)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hϖP this

  have hdiv : divCycle P (C ϖ) W ≠ 0 := by
    unfold divCycle
    rw [dite_eq_left ⟨hmin, hrel⟩]
    have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
        ((P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W),
        Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
      exact hmin
    have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
    have : Nontrivial (Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
    have hpos := Module.length_pos (R := Localization.AtPrime W)
      (M := Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W)))
    rw [multAt, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
    exact_mod_cast (ENat.toNat_pos hpos.ne' hne).ne'
  exact (h O ϖ hϖ K ι P d hP).2 W hdiv

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem GenericProjClosureModel.proof (h₁ : TwistedDualGensExist.Statement)
    (h₂ : GenericProjClosureDim.Statement) (h₃ : GenericProjClosureDivisor.Statement) :
    GenericProjClosureModel.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB Φ _ _ _ _ e t ht
  obtain ⟨a₁, ha₁⟩ := h₁ O Ω K ι y N E B
  obtain ⟨M, φ, hφ⟩ := ha₁ a₁ le_rfl
  obtain ⟨a₁', ha₁'⟩ := h₁ O Ω K ι y N E B'
  obtain ⟨M', φ', hφ'⟩ := ha₁' a₁' le_rfl
  have hZ := h₂ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht
  obtain ⟨f₀, g₀, hD, hfg⟩ :=
    h₃ O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₁ a₁' φ φ' hφ hφ' Φ e t ht hZ
  exact ⟨M, M', a₁, a₁', φ, φ', hφ, hφ', hZ, f₀, g₀, hD, hfg⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]

abbrev localQuot (P U : Ideal R) [U.IsPrime] : Type _ :=
  Localization.AtPrime U ⧸ P.map (algebraMap R (Localization.AtPrime U))

def localQuotMap (P U : Ideal R) [U.IsPrime] : R →+* localQuot P U :=
  (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime U))

end Defs

section Lemmas

def LocalQuotRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P.IsPrime → P ≤ U →
    IsDomain (localQuot P U) ∧ IsLocalRing (localQuot P U) ∧
      (∀ y : localQuot P U, IsUnit y ↔ y ∉ U.map (localQuotMap P U)) ∧
      ∀ x : R, localQuotMap P U x = 0 ↔ x ∈ P

def LocalQuotPrimes.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    (∀ W : Ideal R, W.IsPrime → P ≤ W → W ≤ U →
      (W.map (localQuotMap P U)).IsPrime ∧ (W.map (localQuotMap P U)).comap (localQuotMap P U) = W) ∧
    ∀ p : Ideal (localQuot P U), p.IsPrime →
      P ≤ p.comap (localQuotMap P U) ∧ p.comap (localQuotMap P U) ≤ U ∧
        (p.comap (localQuotMap P U)).map (localQuotMap P U) = p

def LocCycleLocalQuot.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (J W : Ideal R), P ≤ J → W.IsPrime → P ≤ W →
    W ≤ U → locCycle J W = locCycle (J.map (localQuotMap P U)) (W.map (localQuotMap P U))

def LocalQuotColon.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (f g : R),
    ((P ⊔ Ideal.span {f}).colon {g}).map (localQuotMap P U) =
      (Ideal.span {localQuotMap P U f}).colon {localQuotMap P U g}

def LocalQuotFinsum.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    ∀ (F : Ideal R → ℤ) (F' : Ideal (localQuot P U) → ℤ),
      (∀ G, F G ≠ 0 → G.IsPrime ∧ P ≤ G ∧ G ≤ U) → (∀ p, F' p ≠ 0 → p.IsPrime) →
      (∀ G : Ideal R, G.IsPrime → P ≤ G → G ≤ U → F G = F' (G.map (localQuotMap P U))) →
      ∑ᶠ G, F G = ∑ᶠ p, F' p

def LocalCoeffLocal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    ∀ f g s u v : A, f ≠ 0 → g ≠ 0 → s ≠ 0 → IsUnit u → u * f = v * g →
    (∀ W : Ideal A, locCycle (Ideal.span {s}) W ≠ 0 →
      locCycle (Ideal.span {f}) W = locCycle (Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      ∑ᶠ W, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ (Ideal.span {f}).colon {g}) (IsLocalRing.maximalIdeal A)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem divCycle_ne_zero_facts {O : Type u} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {P : Ideal (MRing ι O)} (hP : IsMultiHomogIdeal P) {f : MRing ι O} {e : K → ℕ}
    (hf : IsMultiHomog f e) {W : Ideal (MRing ι O)} (h : divCycle P f W ≠ 0) :
    W.IsPrime ∧ IsRelevant W ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  unfold divCycle at h
  split_ifs at h with hW
  · obtain ⟨hmin, hrel⟩ := hW
    refine ⟨hmin.1.1, hrel, le_trans le_sup_left hmin.1.2, ?_⟩
    exact MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P f e hP hf) hmin
  · exact absurd rfl h

theorem LeftTermSupport.proof : LeftTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs G U hU
  by_contra hne
  apply hU
  have hG : ratDiv P f g G ≠ 0 := left_ne_zero_of_mul hne
  have hU' : divCycle G s U ≠ 0 := right_ne_zero_of_mul hne
  have hϖG : (C ϖ : MRing ι O) ∈ G := hD.vertical G hG
  obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
  have hGfacts : P ≤ G ∧ IsMultiHomogIdeal G := by
    have : divCycle P f G ≠ 0 ∨ divCycle P g G ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hG (by unfold ratDiv; rw [h.1, h.2, sub_zero])
    rcases this with h | h
    · exact (divCycle_ne_zero_facts hP hf h).2.2
    · exact (divCycle_ne_zero_facts hP hg h).2.2
  obtain ⟨hUp, hUr, hGU, hUm⟩ := divCycle_ne_zero_facts hGfacts.2 hs hU'
  exact ⟨hUp, hUm, hUr, hGU hϖG, le_trans hGfacts.1 hGU⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem IsMultiHomogIdeal.sup {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
    {I J : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) (hJ : IsMultiHomogIdeal J) :
    IsMultiHomogIdeal (I ⊔ J) := by
  intro f hf b
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hI x hx b) (hJ y hy b)

theorem RightTermSupport.proof : RightTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs hH W U hU
  by_contra hne
  have hW : divCycle P s W ≠ 0 := left_ne_zero_of_mul hne
  have hWU : idealCycle (W ⊔ divisorIdeal P f g) U ≠ 0 := right_ne_zero_of_mul hne
  have hWm : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  have hUm : U ∈ (W ⊔ divisorIdeal P f g).minimalPrimes ∧ IsRelevant U := by
    unfold idealCycle at hWU
    split_ifs at hWU with h
    · exact h
    · exact absurd rfl hWU
  have hWp : W.IsPrime := hWm.1.1.1
  have hUp : U.IsPrime := hUm.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hWm.1.1.2
  have hWU' : W ≤ U := le_sup_left.trans hUm.1.1.2
  have hDU : divisorIdeal P f g ≤ U := le_sup_right.trans hUm.1.1.2
  have hWmh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P s c hP hs) hWm.1
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.1.degrees
  have hDm : IsMultiHomogIdeal (divisorIdeal P f g) :=
    ColonMultiHomog.proof O K ι _ g bg (SupSpanMultiHomog.proof O K ι P f bf hP hbf) hbg
  have hUmh : IsMultiHomogIdeal U :=
    MinimalPrimeMultiHomog.proof O K ι _ U (hWmh.sup hDm) hUm.1
  apply hU
  refine ⟨hUp, hUmh, hUm.2, ?_, hPW.trans hWU'⟩
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · exact hWU' hϖW
  by_contra hϖU
  have hV := hH W hW hϖW
  obtain ⟨u, v, hu, hv, huv⟩ := hV.unit_off_special U hUp hWU' hUm.2 hϖU
  obtain ⟨u', v', hu', huv'⟩ := hD.2 U hUp (hPW.trans hWU') hUm.2
  have hv'D : v' ∈ divisorIdeal P f g := by
    unfold divisorIdeal
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have e : v' * g = u' * f - (u' * f - v' * g) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
      (Ideal.mem_sup_left huv')
  have hmem : g * (u * v' - u' * v) ∈ W := by
    have e : g * (u * v' - u' * v) = u' * (u * f - v * g) - u * (u' * f - v' * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left _ huv) (W.mul_mem_left _ (hPW huv'))
  have hdiff : u * v' - u' * v ∈ U :=
    hWU' ((hWp.mem_or_mem hmem).resolve_left hV.den_not_mem)
  have hv'U : v' ∈ U := hDU hv'D
  have hu'v : u' * v ∈ U := by
    have e : u' * v = u * v' - (u * v' - u' * v) := by ring
    rw [e]
    exact U.sub_mem (U.mul_mem_left _ hv'U) hdiff
  exact (hUp.mem_or_mem hu'v).elim hu' hv

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

abbrev lineBlocks (M M' : ℕ) : Option Unit → Type := bundleIdx (fun _ : Unit => Fin M) M'

section Objects

variable {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
  [Algebra Ω Φ]

def flagLinePt (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) (k : ℕ) : (Σ o, lineBlocks M M' o) → Φ
  | ⟨none, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ' l (w i))
  | ⟨some _, l⟩ => ∑ i, flagCoord w e t k i * algebraMap Ω Φ (φ l (w i))

end Objects

def SegreFlagClosureBirational.Statement : Prop :=
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
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t → 1 ≤ N →
      IsBirationalJoin O (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t 1)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
