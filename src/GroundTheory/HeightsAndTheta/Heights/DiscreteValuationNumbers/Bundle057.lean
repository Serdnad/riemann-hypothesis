module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle053
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrictBundle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle052
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem residual_newVar_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u}
    [CommRing R] [IsNoetherianRing R] {P : Ideal (MRing ι R)} [P.IsPrime] {s g f m : MRing ι R}
    (e : K → ℕ) (hfP : f ∉ P) (hmP : m ∉ P) {G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) R)}
    (hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G')
    (hres : 0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G') :
    ∀ j, j ≠ none → (newVar j : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof R (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim hfP hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) R) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hres; omega
  rintro (_ | _ | i) hj
  · exact absurd rfl hj
  · exact hY₁G'
  by_contra hYi
  have hrel : liftForm (powMonomial e i) * newVar (some none) -
      liftForm m * newVar (some (some i)) ∈ P' := by
    rw [hP'def, blowUpOf, RingHom.mem_ker]
    simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
    ring
  have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) R) ∉ P' := fun h => hYi (hP'G' h)
  by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι R) ∈ P'
  · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
    rw [sub_sub_cancel] at h
    exact (hP'prime.mem_or_mem h).elim hlm hYiP'
  · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
    rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
    simp only [Pi.add_apply] at h1
    have h2 : divCycle P' (newVar (some (some i))) G' = 0 := by
      by_contra h; exact hYi (form_mem_of_divCycle_ne_zero h)
    have h3 := hnonneg (liftForm (powMonomial e i)) G'
    unfold ratDiv at hres; omega

theorem ResidualContractionComponent.proof (hpieces : BlowUpDecomposition.Statement.{u}) :
    ResidualContractionComponent.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  obtain ⟨hP', hsc', hsP', -⟩ := hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  have : P.IsPrime := hP.multiProj.isPrime
  have hG'supp : G' ∈ (blowUpOf P (blowUpGens s g f m e) ⊔ Ideal.span {liftForm s}).minimalPrimes ∧
      IsRelevant G' := by
    unfold divCycle at hsG'
    split_ifs at hsG' with hG'
    · exact hG'
    · exact (lt_irrefl _ hsG').elim
  have : G'.IsPrime := hG'supp.1.1.1
  have hP'G' : blowUpOf P (blowUpGens s g f m e) ≤ G' := le_sup_left.trans hG'supp.1.1.2
  have hY := residual_newVar_mem e hD.1.num_not_mem hmP hP'G' hresG'
  have hdim' := ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) _ (d + 1) hP'
    (liftMDeg c) (liftForm s) hsc' hsP' G' hsG'.ne' hϖG'
  have hdim := ringKrullDim_quotient_le_comap_add_one G' none hY
  refine mem_minimalPrimes_of_ringKrullDim P _ s hsP (d + 1 + 1 + Fintype.card K) hP.dim ?_ ?_
  · refine sup_le (fun p hp => hP'G' ?_) ?_
    · rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hG'supp.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  · rw [Fintype.card_option, show d + 1 + (Fintype.card K + 1) = d + 1 + 1 + Fintype.card K by omega]
      at hdim'
    exact hdim' ▸ hdim

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpLocRingFrac.proof (hiso : BlowUpLocRingIso.Statement.{u})
    (hfam : BlowUpOverLocFamilyFinite.Statement.{u}) (havoid : MultiHomogPrimeAvoid.Statement.{u}) :
    BlowUpLocRingFrac.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  obtain ⟨e, L, hL, he, hLQ⟩ := havoid O (Option K) (extIdx ι J) _
    (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
  have hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl

  have hne : ∀ (d : Option K → ℕ) (H : MRing (extIdx ι J) O), IsMultiHomog H d → H ∉ W' →
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) ≠ 0 := by
    intro d H hH hHW h0
    have h1 := hφ d H H hH hH hHW
    rw [h0, div_zero] at h1
    have h2 : (⟨_, Subring.subset_closure ⟨d, H, H, hH, hH, hHW, rfl⟩⟩ :
        homLocRing (blowUpOf P u) W') = 1 := by
      apply Subtype.ext
      show _ / _ = (1 : FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
      apply div_self
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => hHW (hbl h)
    rw [h2, map_one] at h1
    exact one_ne_zero h1

  have hgen : ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) O), IsMultiHomog F b → IsMultiHomog G b →
      G ∉ W' → ∃ bb ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
        (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * s = bb := by
    intro b F G hF hG hGW
    set k := ∑ o, b o with hk
    obtain ⟨M, hM, hMW⟩ := homLocRing_form_not_mem hW'p hW'rel (fun o => k * e o - b o)
    have hdeg : b + (fun o => k * e o - b o) = k • e := by
      funext o
      have : b o ≤ k * e o := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ o)) (Nat.le_mul_of_pos_right _ (he o))
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    have hFM : IsMultiHomog (F * M) (k • e) := hdeg ▸ hF.mul hM
    have hGM : IsMultiHomog (G * M) (k • e) := hdeg ▸ hG.mul hM
    have hLk : IsMultiHomog (L ^ k) (k • e) := hL.pow k
    have hLkQ : ∀ Q : Ideal (MRing (extIdx ι J) O), Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W → L ^ k ∉ Q :=
      fun Q hQ h => hLQ Q hQ (hQ.1.mem_of_pow_mem k h)
    have hmemB : ∀ H, IsMultiHomog H (k • e) →
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (L ^ k)) ∈
          blowUpOverLoc P W u := fun H hH =>
      Subring.mem_iInf.mpr fun Q => Subring.mem_iInf.mpr fun hQ =>
        Subring.subset_closure ⟨k • e, H, L ^ k, hH, hLk, hLkQ Q hQ, rfl⟩
    have hGMW : G * M ∉ W' := fun h => (hW'p.mem_or_mem h).elim hGW hMW
    have hLkW : L ^ k ∉ W' := hLkQ W' hW'fam
    have hG0 := hne _ _ hG hGW
    have hGM0 := hne _ _ hGM hGMW
    have hLk0 := hne _ _ hLk hLkW
    refine ⟨_, hmemB _ hFM, _, hmemB _ hGM, ⟨_,
      Subring.subset_closure ⟨k • e, L ^ k, G * M, hLk, hGM, hGMW, rfl⟩, ?_⟩, ?_⟩
    · rw [div_mul_div_comm, mul_comm]
      exact div_self (mul_ne_zero hLk0 hGM0)
    · rw [map_mul, map_mul] at hGM0 ⊢
      rw [map_mul, map_mul]
      field_simp
  intro z hz
  induction hz using Subring.closure_induction with
  | mem z hz =>
    obtain ⟨b, F, G, hF, hG, hGW, rfl⟩ := hz
    exact hgen b F G hF hG hGW
  | zero => exact ⟨0, zero_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, zero_mul 1⟩
  | one => exact ⟨1, one_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, one_mul 1⟩
  | add x y _ _ h₁ h₂ =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
    obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
    refine ⟨b₁ * s₂ + b₂ * s₁, add_mem (mul_mem hb₁ hs₂) (mul_mem hb₂ hs₁), s₁ * s₂, mul_mem hs₁ hs₂,
      ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
    rw [← hx₁, ← hx₂]
    ring
  | neg x _ h =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ht, hx₁⟩ := h
    exact ⟨-b₁, neg_mem hb₁, s₁, hs₁, ht, by rw [← hx₁]; ring⟩
  | mul x y _ _ h₁ h₂ =>
    obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
    obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
    refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, s₁ * s₂, mul_mem hs₁ hs₂,
      ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
    rw [← hx₁, ← hx₂]
    ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalDivisorSupportFibre.fibreVarieties : FibreVarieties.Statement.{0} :=
  FibreVarieties.proof GenericFibProps.proof (GenericDimBound.proof MaximalIdealHeightFG.proof)
    GenericDimGe.proof SpecialIdealCorresp.proof SpecialIdealMultiHomog.proof SupSpanMultiHomog.proof
    MinimalPrimeMultiHomog.proof SpecialQuotDim.proof ComponentDim.proof

theorem VerticalDivisorSupportFibre.proof : VerticalDivisorSupportFibre.Statement := by
  classical
  intro O _ _ _ K _ ι _ P d hP b f g hV W hW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hP1⟩ := (BundleExamples.isModelOver_iff O P d).mp hP
  have hV1 := (VerticalDivisorCharacterisation.proof O K ι P ϖ b f g hϖ hP1.multiProj).mp hV
  rw [BundleExamples.ratCyc_eq] at hW
  have hϖW := hV1.vertical W hW
  rw [BundleExamples.redIdeal_eq]

  have key : ∀ (h : MRing ι O) (bh : K → ℕ), IsMultiHomog h bh → h ∉ P → divCycle P h W ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (specialIdeal W) d := by
    intro h bh hh hhP hne
    unfold divCycle at hne
    split_ifs at hne with hc
    · obtain ⟨hmp, hdim⟩ := VerticalComponentFibre.proof VerticalDivisorSupportFibre.fibreVarieties O ϖ hϖ
        K ι P d hP1 h bh hh hhP W hc.1 hc.2 hϖW
      obtain ⟨hpr, hho, hre⟩ := hmp
      exact ⟨⟨hpr, (VocabMultiHomogIdeal.proof VocabMultiHomog.proof _ K ι _).2 hho, hre⟩, hdim⟩
    · exact absurd rfl hne
  obtain ⟨bf, bg, hf, hg, -⟩ := hV1.degrees
  by_cases hfW : divCycle P f W = 0
  · refine key g bg hg hV1.den_not_mem fun hgW => hW ?_
    simp [ratDiv, hfW, hgW]
  · exact key f bf hf hV1.num_not_mem hfW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict

theorem FullFlagRestriction.proof : FullFlagRestriction.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ B _ Q _ hQ hPQ
  obtain ⟨_, hQh, hQr⟩ := hQ
  refine ⟨mcIdeal_genPt Q hQh, resBundle B hPQ, rfl, fun fl => ?_⟩
  obtain ⟨fl', h1, h2⟩ := exists_resFlag hPQ hQr fl
  exact ⟨fl', h1, h2⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (liftVar pullDeg joinCoord mcIdeal IsVertDiv)


open JoinPointVerticalDivisor in
theorem JoinVerticalDivisor.proof : JoinVerticalDivisor.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨Sum.elim α 0, Sum.elim β 0, isMultiHomog_rename hf, isMultiHomog_rename hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k)
    · simpa [pullDeg] using hb k
    · simp [pullDeg]
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O x ≤ Q.comap (rename (liftVar (ι := ι) ι')) := fun h hh =>
      Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x z h).mpr hh))
    have hO : (Q.comap (rename (liftVar (ι := ι) ι'))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (liftVar ι') u, rename (liftVar ι') v, ⟨_, isMultiHomog_rename hu⟩,
      ⟨_, isMultiHomog_rename hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x z _).mpr huv
    simpa only [map_sub, map_mul] using this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPairValueIndependence

theorem polyNum_congr {F : Type*} [Field F] {K : Type} [Fintype K] {κ : K → Type} [∀ k, Fintype (κ k)]
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F κ) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F κ)) (n : ℕ)
    {m : ℕ} {deg₁ deg₂ : Fin m → K → ℤ} (P : MvPolynomial (Fin m) ℤ)
    (h : ∀ s ∈ P.vars, deg₁ s = deg₂ s) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₁ P = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W n deg₂ P := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hm : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₁ μ = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList deg₂ μ := by
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.monoList
    congr 1
    funext s
    by_cases hs : μ s = 0
    · simp [hs]
    · rw [h s ((mem_vars_iff_mem_support s).mpr ⟨μ, hμ, Finsupp.mem_support_iff.mpr hs⟩)]
  exact congrArg (fun l : List (K → ℤ) => P.coeff μ * if h : l.length = n then
    I W n (fun j => l.get (Fin.cast h.symm j)) else 0) hm

theorem not_mem_vars_divDiff_castAdd {N r : ℕ} (i : Fin N) (j : Fin r) (G : MvPolynomial (Fin N) ℤ)
    (Q : MvPolynomial (Fin r) ℤ) :
    Fin.natAdd (N + r) (Fin.natAdd N j) ∉ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
      (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)).vars := by
  classical
  intro hs
  obtain ⟨μ, hμ, hsμ⟩ := (mem_vars_iff_mem_support _).mp hs
  have he : Function.Injective
      (finSumFinEquiv.symm : Fin ((N + r) + (N + r)) → Fin (N + r) ⊕ Fin (N + r)) :=
    finSumFinEquiv.symm.injective
  have h1 : Finsupp.mapDomain finSumFinEquiv.symm μ ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).support := by
    rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ hμ
  have h2 : finSumFinEquiv.symm (Fin.natAdd (N + r) (Fin.natAdd N j)) ∈ (rename finSumFinEquiv.symm
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.castAdd r i)
        (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q))).vars := by
    refine (mem_vars_iff_mem_support _).mpr ⟨_, h1, ?_⟩
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain_apply_of_injective he]
    exact Finsupp.mem_support_iff.mp hsμ
  rw [finSumFinEquiv_symm_apply_natAdd, plainPolynomialPairNumber.rename_divDiff_castAdd_mul] at h2
  rcases Finset.mem_union.mp (vars_mul _ _ h2) with h3 | h3
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    rcases t with t | t
    · exact Sum.inl_ne_inr ht
    · simp only [Sum.map_inr, Sum.inr.injEq] at ht
      have := congrArg Fin.val ht
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
  · obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (vars_rename _ _ h3)
    exact Sum.inl_ne_inr ht

theorem proof (hPlain : FlagPlainValueIndependence.Statement)
    (hFur : flagFurtherTerm_independent.Statement) : FlagPairValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ
  classical
  have hz : ∀ J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver (IsLocalRing.ResidueField O) ι) → ℤ,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J 0 = 0 := fun J => Finsupp.sum_zero_index
  have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 :=
    sub_self _
  have split : ∀ φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E',
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                (Fin.append φ.deg y) (Fin.append φ.deg' y') (Fin.append φ.f f) (Fin.append φ.g g)
                                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                                  (Fin.append φ.deg y) (Fin.append φ.deg' y) (Fin.append φ.f fun _ => 1)
                                  (Fin.append φ.g fun _ => 1) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) +
          ∑ l : Fin r, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
            (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
              (Fin.append (Fin.append φ.deg y) (Fin.append φ.deg' y'))
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
            (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) := by
    intro φ
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, h0, hz, Finset.sum_const_zero, add_zero]
    refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
    refine congrArg (fun J => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O J _) (funext fun W => ?_)
    refine polyNum_congr I W d _ fun s hs => ?_
    induction s using Fin.addCases with
    | left a => simp only [Fin.append_left]
    | right b =>
      induction b using Fin.addCases with
      | left a => simp only [Fin.append_right, Fin.append_left]
      | right j => exact absurd hs (not_mem_vars_divDiff_castAdd i j G Q)
  rw [split φ₁, split φ₂, hPlain O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y c Q hc hGc hQ]
  congr 1
  exact Finset.sum_congr rfl fun l _ =>
    hFur O Ω K ι x d N V E E' hM hS φ₁ φ₂ I hI G hG r y y' f g hv c Q hc hGc hQ l

end FlagPairValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end
