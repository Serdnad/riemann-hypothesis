module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle045
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle046
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
import Mathlib.RingTheory.KrullDimension.Polynomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)

namespace JoinPointModel

section Split

variable {K : Type} {ι : K → Type}

def varEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl

variable (K) (Ω : Type*) [CommRing Ω]

def tgtEquiv : MvPolynomial (K ⊕ Unit) Ω ≃ₐ[Ω] Polynomial (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.optionEquivSumPUnit.{0, 0} K).symm).trans (optionEquivLeft Ω K)

variable {K} (O : Type*) [CommRing O]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O ≃ₐ[O]
    Polynomial (MvPolynomial (Σ k, ι k) O) :=
  (renameEquiv O varEquiv).trans (optionEquivLeft O _)

end Split

section Cone

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem tgtEquiv_mcMap (y : (Σ k, ι k) → Ω) (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    tgtEquiv K Ω (mcMap O (joinCoord y (ptCoord (Ω := Ω))) p) =
      Polynomial.map (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω) (srcEquiv O p) := by
  have h : ((tgtEquiv K Ω : MvPolynomial (K ⊕ Unit) Ω →+* Polynomial (MvPolynomial K Ω)).comp
      (mcMap O (joinCoord y (ptCoord (Ω := Ω))) : _ →+* MvPolynomial (K ⊕ Unit) Ω)) =
      (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)).comp
        (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tgtEquiv, srcEquiv, mcMap, optionEquivLeft_C]
    · rintro ⟨k | u, i⟩
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, optionEquivLeft_X_some, optionEquivLeft_C]
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, ptCoord, optionEquivLeft_X_none]
  exact RingHom.congr_fun h p

theorem mem_pointIdeal_join_iff (y : (Σ k, ι k) → Ω)
    (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    p ∈ pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) ↔
      srcEquiv O p ∈ RingHom.ker
        (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)) := by
  rw [← BundleExamples.mcIdeal_eq_pointIdeal, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, RingHom.mem_ker, RingHom.mem_ker,
    Polynomial.coe_mapRingHom, ← tgtEquiv_mcMap, map_eq_zero_iff _ (tgtEquiv K Ω).injective]

theorem ringKrullDim_join [IsNoetherianRing O] (y : (Σ k, ι k) → Ω) :
    ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ pointIdeal O (joinCoord y (ptCoord (Ω := Ω)))) =
      ringKrullDim (MRing ι O ⧸ pointIdeal O y) + 1 := by
  let J := RingHom.ker (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω))
  let Φ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O →+* Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J :=
    (Ideal.Quotient.mk J).comp (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp (srcEquiv O).surjective
  have hker : pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) = RingHom.ker Φ := by
    ext p
    rw [mem_pointIdeal_join_iff, RingHom.mem_ker (f := Φ)]
    change _ ↔ Ideal.Quotient.mk J (srcEquiv O p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
  have hJ : J = (pointIdeal O y).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) := by
    simp only [J]
    rw [Polynomial.ker_mapRingHom]
    rfl
  have hq : ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ RingHom.ker Φ) =
      ringKrullDim (Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hΦ)
  have hp : ringKrullDim (Polynomial (MRing ι O ⧸ pointIdeal O y)) =
      ringKrullDim (Polynomial (MRing ι O) ⧸ (pointIdeal O y).map (Polynomial.C : MRing ι O →+* _)) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial (pointIdeal O y))
  rw [hker, hq, hJ, ← hp, Polynomial.ringKrullDim_of_isNoetherianRing]

end Cone

end JoinPointModel


open JoinPointModel in
theorem JoinPointModel.proof : JoinPointModel.Statement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y d hW
  rw [BundleExamples.isModelOver_iff]
  refine ⟨inferInstance, ⟨?_, ?_, ?_⟩⟩
  · apply GenericProjClosureDim.isMultiProjPrime_pointIdeal
    rintro (k | u)
    · obtain ⟨j, hj⟩ := hW.multiProj.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      change y ⟨k, j⟩ = 0 at h0
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    · exact ⟨(0 : Fin 1), by simp [joinCoord, ptCoord]⟩
  · rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, pointIdeal, RingHom.mem_ker,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  · rw [BundleExamples.mcIdeal_eq_pointIdeal, ringKrullDim_join, hW.dim, Fintype.card_sum, Fintype.card_unit,
      show d + 1 + (Fintype.card K + 1) = (d + 1 + Fintype.card K) + 1 by omega]
    norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalLift.full : BlowUpHorizontalLift.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime
  obtain ⟨hWp, hPW, hrelW⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have hWmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  obtain ⟨j₀, hj₀⟩ := hloc W hWp hPW hrelW hϖW
  choose v w hvW hvw using hj₀

  have hu₀ : u j₀ ∉ P := by
    intro h0
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have h2 := P.add_mem (hvw j) (P.mul_mem_left (w j) h0)
      rwa [sub_add_cancel] at h2
    rcases hPp.mem_or_mem h1 with h2 | h2
    · exact hvW j (hPW h2)
    · exact hj h2

  set V : MRing ι O := ∏ j, v j with hV
  set a : J → MRing ι O := fun j => w j * ∏ i ∈ Finset.univ.erase j, v i with ha_def
  have hVW : V ∉ W := by
    intro h
    obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hvW j hj
  have ha : ∀ j, V * u j - u j₀ * a j ∈ P := by
    intro j
    have e : V * u j - u j₀ * a j = (∏ i ∈ Finset.univ.erase j, v i) * (v j * u j - w j * u j₀) := by
      simp only [hV, ha_def]
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]
      ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hVa : V - a j₀ ∈ P := by
    have h1 : (V - a j₀) * u j₀ ∈ P := by
      have h2 := ha j₀
      rwa [show V * u j₀ - u j₀ * a j₀ = (V - a j₀) * u j₀ by ring] at h2
    exact (hPp.mem_or_mem h1).resolve_right hu₀
  have haW : a j₀ ∉ W := fun h => hVW (by simpa using W.add_mem (hPW hVa) h)

  set Wt : Ideal (MRing (extIdx ι J) O) :=
    (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W).comap
      (aeval (R := O) (chartSubst a)) with hWt
  have hWtp : Wt.IsPrime := Ideal.comap_isPrime _ _
  have hcomap : ∀ s, liftForm (J := J) s ∈ Wt ↔ s ∈ W := by
    intro s
    rw [hWt, Ideal.mem_comap, aeval_chartSubst_liftForm]
    constructor
    · intro h
      simpa using Ideal.mem_map_C_iff.mp h 0
    · intro h
      exact Ideal.mem_map_of_mem _ h
  have hBWt : blowUpOf P u ≤ Wt := fun F hF =>
    Ideal.map_mono hPW (aeval_chartSubst_mem_of_mem_blowUpOf hPp hu₀ ha hF)
  have hxWt : liftForm x ∈ Wt := (hcomap x).2 hxW
  have hrelWt : IsRelevant Wt := by
    rintro (_ | k)
    · refine ⟨j₀, fun h => haW ?_⟩
      rw [hWt, Ideal.mem_comap] at h
      simp only [aeval_X, chartSubst] at h
      simpa using Ideal.mem_map_C_iff.mp h 1
    · obtain ⟨i, hi⟩ := hrelW k
      refine ⟨i, fun h => hi ((hcomap _).1 ?_)⟩
      rw [liftForm_X]
      exact h

  have hmin : Wt ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    refine ⟨⟨hWtp, sup_le hBWt ((Ideal.span_singleton_le_iff_mem _).mpr hxWt)⟩, fun Q hQ hQWt => ?_⟩
    have hQp := hQ.1
    have hBQ : blowUpOf P u ≤ Q := le_sup_left.trans hQ.2
    have hxQ : liftForm x ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hle : Q.comap (liftForm (J := J)) ≤ W := fun s hs => (hcomap s).1 (hQWt hs)
    have hQ₀ : Q.comap (liftForm (J := J)) = W :=
      le_antisymm hle (hWmin.2 ⟨Ideal.comap_isPrime _ _,
        sup_le (fun p hp => hBQ (liftForm_mem_blowUpOf hp))
          ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩ hle)
    intro F hF
    refine mem_of_aeval_chartSubst_mem hQp hQ₀.ge j₀ (fun h => haW ?_) (fun j => hBQ ?_) hF
    · rw [← hQ₀]
      exact h
    · apply mem_blowUpOf_of_sub
      have e : u j * a j₀ - u j₀ * a j = (V * u j - u j₀ * a j) - u j * (V - a j₀) := by ring
      rw [e]
      exact P.sub_mem (ha j) (P.mul_mem_left _ hVa)
  refine ⟨Wt, ?_, fun h => hϖW ((hcomap _).1 (by rw [liftForm_C]; exact h)), ?_⟩
  ·
    unfold divCycle
    rw [dite_eq_left ⟨hmin, hrelWt⟩]
    have hne := length_localizedQuot_ne_top (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt hmin
    have hnz : multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt ≠ 0 := by
      unfold multAt
      rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
      intro hs
      obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at hr0
      exact hr (hmin.1.2 hr0)
    have htn : (multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Wt).toNat ≠ 0 :=
      fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
    exact_mod_cast htn
  · ext s
    rw [Ideal.mem_comap]
    exact hcomap s

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

theorem BlowUpHorizontalMinimal.full : BlowUpHorizontalMinimal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨hWp, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine ⟨⟨hW₀p, sup_le hPW₀ ((Ideal.span_singleton_le_iff_mem _).mpr hxW)⟩, fun P' hP' hP'W₀ => ?_⟩
  have := hP'.1
  have hxP' : x ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))

  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P').comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono (le_sup_left.trans hP'.2)
        (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxP'
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp hP'W₀ j₀ ha₀ (fun j => hBW (hrelB j)) hG

  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  intro p hp
  have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) P' := by
    rw [← aeval_chartSubst_liftForm a p]
    exact hWQ' hp
  simpa using Ideal.mem_map_C_iff.mp h5 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutProjection

theorem relDim_anti {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} {I J : Ideal (MRing ι F)}
    (hIJ : I ≤ J) : FieldNumbers.relDim J ≤ FieldNumbers.relDim I := by
  have hmono : Monotone (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.monotone_map_iff.2 (WithTop.monotone_map_iff.2 (fun a b h =>
      Int.sub_le_sub_right (by exact_mod_cast h) _))
  exact hmono (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ) (Ideal.Quotient.factor_surjective hIJ))

theorem specialIdeal_le_contractPrime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K K' : Type*} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    {I : Ideal (MRing (fun k => ι' (j k)) O)} {W : Ideal (MRing ι' O)}
    (h : I ≤ W.comap (rename (FieldNumbers.blockIncl j ι'))) :
    specialIdeal I ≤ FieldNumbers.contractPrime j (specialIdeal W) := by
  refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
  simp only [Ideal.mem_comap, FieldNumbers.contractPrime, specialIdeal]
  rw [← map_rename]
  exact Ideal.mem_map_of_mem _ (h hf)

end SegreFlagCutProjection

open SegreFlagCutProjection in
theorem SegreFlagCutProjection.proof (hLies : SegreFlagCutLiesOver.Statement)
    (hDim : SegreFlagProjSpecialDim.Statement) : SegreFlagCutProjection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  obtain ⟨hl1, hl2⟩ := hLies O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  obtain ⟨hd1, hd2⟩ := hDim O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW => ?_⟩
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd1
  · exact lt_of_le_of_lt (relDim_anti (specialIdeal_le_contractPrime _
      (hl2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW))) hd2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
