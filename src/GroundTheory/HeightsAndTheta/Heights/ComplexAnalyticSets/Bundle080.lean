module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import Mathlib.Algebra.Category.Grp.Zero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
public import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem IsCohenMacaulayLocalRing.of_ringEquiv {A C : Type*} [CommRing A] [CommRing C]
    [IsCohenMacaulayLocalRing A] (e : A ≃+* C) : IsCohenMacaulayLocalRing C := by
  have : Nontrivial C := e.injective.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv A e
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  refine { exists_isWeaklyRegular := ⟨rs.map e, ?_, ?_, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs' := hm s hs
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs' ⊢
    exact fun h => hs' (by simpa using h.map e.symm)
  · have := RingHomInvPair.of_ringEquiv e
    have := RingHomInvPair.symm (↑e : A →+* C) (e.symm : C →+* A)
    exact (e.toSemilinearEquiv.isWeaklyRegular_congr' rs).1 hreg
  · rw [← ringKrullDim_eq_of_ringEquiv e, hdim, List.length_map]

theorem exists_nat_of_add_natCast_eq {a : WithBot ℕ∞} {m n : ℕ}
    (h : a + (m : WithBot ℕ∞) = (n : WithBot ℕ∞)) : ∃ k : ℕ, a = k ∧ k + m = n := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj, top_add] at h
      exact absurd h (ENat.top_ne_natCast n)
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

theorem CMParameterQuotient.proof (hreg : CMRegularElement.Statement.{0}) :
    CMParameterQuotient.Statement := by
  intro B _ _ d
  induction d generalizing B with
  | zero =>
    intro x _ _
    have h0 : Ideal.span (Set.range x) = ⊥ := by
      rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsCohenMacaulayLocalRing.of_ringEquiv
      ((RingEquiv.quotientBot B).symm.trans (Ideal.quotEquivOfEq h0.symm))
  | succ d ih =>
    classical
    intro x hx hdim
    let x' : Fin d → B ⧸ Ideal.span {x 0} := fun i => Ideal.Quotient.mk _ (x i.succ)
    have hIJ : Ideal.span (Set.range x) =
        Ideal.span {x 0} ⊔ Ideal.span (Set.range (Fin.tail x)) := by
      rw [Fin.range_fin_succ, Ideal.span_insert]
    have hmap : (Ideal.span (Set.range (Fin.tail x))).map (Ideal.Quotient.mk (Ideal.span {x 0})) =
        Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let e : (B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x') ≃+* B ⧸ Ideal.span (Set.range x) :=
      (Ideal.quotEquivOfEq hmap.symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hIJ.symm))
    have hIne : Ideal.span {x 0} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hx 0)))
    have : Nontrivial (B ⧸ Ideal.span {x 0}) := Ideal.Quotient.nontrivial_iff.2 hIne
    have : IsLocalRing (B ⧸ Ideal.span {x 0}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x 0})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hx' : ∀ i, x' i ∈ maximalIdeal (B ⧸ Ideal.span {x 0}) := fun i =>
      (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal _).1 (hx i.succ) (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hu)
    obtain ⟨rs, -, -, hD⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
    have he := ringKrullDim_eq_of_ringEquiv e
    obtain ⟨k, hk, hkn⟩ := exists_nat_of_add_natCast_eq (hdim.trans hD)

    have hKrull : ringKrullDim (B ⧸ Ideal.span {x 0}) ≤ (k : WithBot ℕ∞) + (d : WithBot ℕ∞) := by
      have hs : ((Finset.univ.image x' : Finset _) : Set _) ⊆ SetLike.coe (Ring.jacobson (B ⧸ Ideal.span {x 0})) := by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        intro z hz
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hz
        obtain ⟨i, rfl⟩ := hz
        exact hx' i
      have h1 := ringKrullDim_le_ringKrullDim_quotient_add_card _ hs
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, he, hk] at h1
      refine h1.trans ?_
      gcongr
      exact_mod_cast Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_fin d)).le
    have hmin : ∀ p ∈ minimalPrimes B, x 0 ∉ p := by
      intro p hp hyp
      have hle : Ideal.span {x 0} ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hyp
      have h1 := ringKrullDim_quotient_eq_of_mem_minimalPrimes hp
      have h2 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ Ideal.span {x 0}) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
      have h3 := (h1.symm.trans_le h2).trans hKrull
      rw [hD] at h3
      have h4 : rs.length ≤ k + d := by exact_mod_cast h3
      omega
    obtain ⟨hnzd, hCM⟩ := hreg B (x 0) (hx 0) hmin
    have hdimI : ringKrullDim (B ⧸ Ideal.span {x 0}) + ((1 : ℕ) : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) := by
      rw [Nat.cast_one, ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd (hx 0),
        hD]
    obtain ⟨k', hk', hk'n⟩ := exists_nat_of_add_natCast_eq hdimI
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x')) + (d : WithBot ℕ∞) =
        ringKrullDim (B ⧸ Ideal.span {x 0}) := by
      rw [he, hk, hk']
      exact_mod_cast (by omega : k + d = k')
    have : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {x 0}) := hCM
    have := ih (B ⧸ Ideal.span {x 0}) x' hx' hdim'
    exact IsCohenMacaulayLocalRing.of_ringEquiv e

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets IsLocalRing

theorem isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes {n : ℕ}
    {I W : Ideal (MvPolynomial (Fin n) ℂ)} [W.IsPrime] (hW : W ∈ I.minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime W))) := by
  set S := Localization.AtPrime W
  set J := I.map (algebraMap (MvPolynomial (Fin n) ℂ) S)
  have hJm : J ≤ maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hW.1.2
  have hJ : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hJm))
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hdim : Ring.KrullDimLE 0 (S ⧸ J) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro K hK
    have : K.IsPrime := hK.1.1
    have hKm : K ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal hK.1.1.ne_top
    have hI : I ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      Ideal.map_le_iff_le_comap.mp hK.1.2
    have hKW : K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) ≤ W := by
      have h := Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin n) ℂ) S) hKm
      rwa [show (maximalIdeal S).comap (algebraMap (MvPolynomial (Fin n) ℂ) S) = W from
        Localization.AtPrime.under_maximalIdeal] at h
    have hWK : W ≤ K.comap (algebraMap (MvPolynomial (Fin n) ℂ) S) :=
      hW.2 ⟨Ideal.IsPrime.comap _, hI⟩ hKW
    have hmK : maximalIdeal S ≤ K := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_le_iff_le_comap.mpr hWK
    rw [le_antisymm hKm hmK]
    exact maximalIdeal.isMaximal S
  have h0 : ringKrullDim (S ⧸ J) = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdim
  exact
    { exists_isWeaklyRegular := ⟨[], by simp, RingTheory.Sequence.IsWeaklyRegular.nil _ _, by simpa using h0⟩ }

theorem CMGeneralPoint.proof (hOpen : CMLocusOpen.Statement) : CMGeneralPoint.Statement := by
  intro n I W hW
  have : W.IsPrime := hW.1.1
  obtain ⟨g, hgW, hg⟩ :=
    hOpen n I W hW.1.2 (isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes hW)
  have hfin : (I.minimalPrimes \ {W}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset Set.sdiff_subset
  have hsel : ∀ W' ∈ I.minimalPrimes \ {W}, ∃ h, h ∈ W' ∧ h ∉ W := by
    rintro W' ⟨hW', hne⟩
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc (hW.2 hW'.1 hc))
  choose! h hh using hsel
  refine ⟨g * ∏ W' ∈ hfin.toFinset, h W', ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› hmem with h1 | h1
    · exact hgW h1
    · obtain ⟨W', hW', h2⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (hh W' (hfin.mem_toFinset.mp hW')).2 h2
  · intro q hq hf
    rw [map_mul, map_prod] at hf
    have hg0 : eval q g ≠ 0 := left_ne_zero_of_mul hf
    have hp0 := right_ne_zero_of_mul hf
    refine ⟨fun W' hW' hqW' => ?_, ?_⟩
    · by_contra hne
      have hmem : W' ∈ I.minimalPrimes \ {W} := ⟨hW', hne⟩
      exact hp0 (Finset.prod_eq_zero (hfin.mem_toFinset.mpr hmem) (hqW' _ (hh W' hmem).1))
    · have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
        fun x hx => RingHom.mem_ker.mpr (hq x hx)
      exact hg _ (hW.1.2.trans hWq) fun hk => hg0 (RingHom.mem_ker.mp hk)

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem map_mem_associatedPrimes_quotient {B : Type*} [CommRing B] [IsNoetherianRing B] (I p : Ideal B)
    (hp : p ∈ associatedPrimes B (B ⧸ I)) :
    I ≤ p ∧ p.map (Ideal.Quotient.mk I) ∈ associatedPrimes (B ⧸ I) (B ⧸ I) := by
  obtain ⟨hprime, a, rfl⟩ := (isAssociatedPrime_iff (I := p) (M := B ⧸ I)).1 hp
  have hI : I ≤ Submodule.colon (⊥ : Submodule B (B ⧸ I)) {a} := fun b hb => by
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hb, zero_mul]
  refine ⟨hI, (isAssociatedPrime_iff).2 ⟨?_, a, ?_⟩⟩
  · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  · ext c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective, Submodule.mem_colon_singleton]
    constructor
    · rintro ⟨b', hb', hbb'⟩
      rw [← hbb']
      simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using hb'
    · intro h
      exact ⟨b, by simpa [Submodule.mem_colon_singleton, Algebra.smul_def] using h, rfl⟩

theorem CMQuotientUnmixed.proof (hQ : CMParameterQuotient.Statement) (hU : CMRingUnmixed.Statement) :
    CMQuotientUnmixed.Statement := by
  intro B _ _ d x hx hdim p hp
  set I := Ideal.span (Set.range x) with hIdef
  have hCM : IsCohenMacaulayLocalRing (B ⧸ I) := hQ B d x hx hdim
  obtain ⟨hIp, hq⟩ := map_mem_associatedPrimes_quotient I p hp
  obtain ⟨hmin, hdq⟩ := hU (B ⧸ I) _ hq
  have hcomap : (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.2 hIp]
  refine ⟨?_, ?_⟩
  · rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨_, hmin, hcomap⟩
  · rw [← hdq]
    exact (ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIp)).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def VarLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      r ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y) -
        s ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y) =
      r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem CMLocusOpen.proof (hcrit : CMProjDimCriterion.Statement) (hpd : ProjDimSpread.Statement)
    (hht : IdealHeightSpread.Statement) : CMLocusOpen.Statement := by
  intro n I P _ hIP hCM
  obtain ⟨ℓ, hℓ, hℓht⟩ := (hcrit n I P hIP).mp hCM
  obtain ⟨g₁, hg₁P, hg₁⟩ := hpd (MvPolynomial (Fin n) ℂ) I P ℓ hℓ
  obtain ⟨g₂, hg₂P, hg₂⟩ := hht (MvPolynomial (Fin n) ℂ) I P hIP
  refine ⟨g₁ * g₂, fun h => (‹P.IsPrime›.mem_or_mem h).elim hg₁P hg₂P, fun Q _ hIQ hgQ => ?_⟩
  have h₁ : g₁ ∉ Q := fun h => hgQ (Q.mul_mem_right g₂ h)
  have h₂ : g₂ ∉ Q := fun h => hgQ (Q.mul_mem_left g₁ h)
  exact (hcrit n I Q hIQ).mpr ⟨ℓ, hg₁ Q h₁, hℓht.trans (hg₂ Q hIQ h₂)⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise

universe u

theorem mem_minimalPrimes_of_mem_associatedPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {p : Ideal B} (hp : p ∈ associatedPrimes B B) : p ∈ minimalPrimes B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  obtain ⟨hprime, m, hpm⟩ := isAssociatedPrime_iff.mp hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hpm, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs m hm0 hm hreg
  rw [← hpm] at hD
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
  by_cases hqp' : q = p
  · exact hqp' ▸ hq
  exfalso
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hqp')
  have : q.IsPrime := hq.1.1
  have hnzd : Ideal.Quotient.mk q a ∈ nonZeroDivisors (B ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have heq : (B ⧸ q) ⧸ Ideal.span {Ideal.Quotient.mk q a} ≃+* B ⧸ (q ⊔ Ideal.span {a}) := by
    have : Ideal.span {Ideal.Quotient.mk q a} = (Ideal.span {a}).map (Ideal.Quotient.mk q) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [this]
    exact DoubleQuot.quotQuotEquivQuotSup q (Ideal.span {a})
  rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
  have hle : q ⊔ Ideal.span {a} ≤ p := sup_le hqp ((Ideal.span_singleton_le_iff_mem p).mpr hap)
  have h1 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have h2 : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  have h3 : ringKrullDim (B ⧸ p) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hdim] at h2 h3
  have h4 : ringKrullDim (B ⧸ p) = (rs.length : WithBot ℕ∞) := le_antisymm h3 hD
  have h5 : ringKrullDim (B ⧸ p) + 1 ≤ (rs.length : WithBot ℕ∞) :=
    ((by gcongr : ringKrullDim (B ⧸ p) + 1 ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) + 1).trans hd2).trans h2
  rw [h4] at h5
  norm_cast at h5
  omega

theorem mem_nonZeroDivisors_of_not_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B] {y : B}
    (hy : ∀ p ∈ minimalPrimes B, y ∉ p) : y ∈ nonZeroDivisors B := by
  by_contra h
  have h' : y ∈ (nonZeroDivisors B : Set B)ᶜ := h
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂] at h'
  obtain ⟨p, hp, hyp⟩ := h'
  exact hy p (mem_minimalPrimes_of_mem_associatedPrimes hp) hyp

theorem exists_isRegular_quotSMulTop {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {rs : List B} (hm : ∀ r ∈ rs, r ∈ maximalIdeal B) (hreg : IsWeaklyRegular B rs)
    {y : B} (hy : IsSMulRegular B y) (hym : y ∈ maximalIdeal B) :
    ∃ rs' : List B, rs'.length = rs.length - 1 ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧
      IsRegular (QuotSMulTop y B) rs' := by
  have key : ∀ (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] [Nontrivial X],
      maximalIdeal B • (⊤ : Submodule B X) < ⊤ := fun X _ _ _ _ => by
    refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
    have H : Module.annihilator B X ≠ ⊤ := fun h => not_subsingleton X (Module.annihilator_eq_top_iff.mp h)
    exact (jacobson_eq_maximalIdeal _ H).ge
  have hne : (y • (⊤ : Submodule B B)) ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ y • (⊤ : Submodule B B) := by rw [h]; exact Submodule.mem_top
    obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact (mem_maximalIdeal _).mp hym (IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hb))
  have : Nontrivial (QuotSMulTop y B) := Submodule.Quotient.nontrivial_iff.mpr hne
  let M : ModuleCat.{u} B := ModuleCat.of B B
  let S := ModuleCat.smulShortComplex M y
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact (M := M) hy
  let N : ModuleCat.{u} B := ModuleCat.of B (Shrink.{u} (B ⧸ maximalIdeal B))
  have hregB : IsRegular B rs := (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hreg
  have hextB : ∀ i < rs.length, Subsingleton (Ext N M i) :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) rs.length M (key B)).out 2 4).mpr
      (⟨rs, rfl, hm, hregB⟩ : ∃ rs' : List B, rs'.length = rs.length ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧ IsRegular M rs')
  have hext3 : ∀ i < rs.length - 1, Subsingleton (Ext N S.X₃ i) := by
    intro i hi
    have hex := Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl
    have h1 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₂ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB i (by omega))
    have h3 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₁ (i + 1))) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero (hex.isZero_of_both_zeros (h1.eq_of_src _ _) (h3.eq_of_tgt _ _))
  have : Module.Finite B S.X₃ := inferInstanceAs (Module.Finite B (QuotSMulTop y B))
  have : Nontrivial S.X₃ := inferInstanceAs (Nontrivial (QuotSMulTop y B))
  obtain ⟨rs', hlen, hm', hreg'⟩ :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) (rs.length - 1) S.X₃ (key S.X₃)).out 2 4).mp hext3
  exact ⟨rs', hlen, hm', hreg'⟩

theorem CMRegularElement.proof : CMRegularElement.Statement.{u} := by
  intro B _ _ y hym hy
  have hnzd := mem_nonZeroDivisors_of_not_mem_minimalPrimes hy
  refine ⟨hnzd, ?_⟩
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hyreg : IsSMulRegular B y := Module.Flat.isSMulRegular_of_nonZeroDivisors hnzd
  obtain ⟨rs', hlen, hm', hreg'⟩ := exists_isRegular_quotSMulTop hm hreg hyreg hym
  set I := Ideal.span {y} with hIdef
  have hI : I ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal _).mp hym)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I (by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hym)
  have hsub : (y • (⊤ : Submodule B B)) = I := by
    rw [hIdef, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop y B ≃ₗ[B] B ⧸ I := Submodule.quotEquivOfEq _ _ hsub
  have hw : IsWeaklyRegular (B ⧸ I) (rs'.map (algebraMap B (B ⧸ I))) :=
    (isWeaklyRegular_map_algebraMap_iff (S := B ⧸ I) (M := B ⧸ I) rs').mpr
      ((e.isWeaklyRegular_congr rs').mp hreg'.toIsWeaklyRegular)
  have hdimq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hym
  refine { exists_isWeaklyRegular := ⟨rs'.map (algebraMap B (B ⧸ I)), ?_, hw, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact map_nonunit (Ideal.Quotient.mk I) s (hm' s hs)
  · rw [List.length_map, hlen]
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ I) := ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at hdimq
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (B ⧸ I) = d :=
      (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)).imp fun _ h => h.symm
    rw [hd] at hdimq ⊢
    have h2 : d + 1 = (rs.length : ℕ∞) := by exact_mod_cast hdimq
    induction d using ENat.recTopCoe with
    | top => simp at h2
    | coe k =>
      norm_cast at h2 ⊢
      rw [show k = rs.length - 1 by omega]

end GroundTheory.Heights₂.Heights
end
