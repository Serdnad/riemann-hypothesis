module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle055
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle041
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle001
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocLocalization.proof (hfam : BlowUpOverLocFamilyFinite.Statement.{u}) :
    BlowUpOverLocLocalization.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W⟩
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' hW'fam
  obtain ⟨e, L, hL, he, hLQ⟩ := MultiHomogPrimeAvoid.proof O (Option K) (extIdx ι J) _
    (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, -⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing

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

  have hfrac : ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
      (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b := by
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

  let 𝔭 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)
  have h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨hBR, 𝔭, h𝔭, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ := hfrac z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocMaxCentre.proof (h₁ : BlowUpOverLocCentreDom.Statement.{u})
    (h₂ : BlowUpOverLocLocalization.Statement.{u}) (h₃ : BlowUpOverLocFinite.Statement.{u})
    (h₄ : BlowUpLocRingIso.Statement.{u}) :
    BlowUpOverLocMaxCentre.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hdom⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  obtain ⟨h', 𝔭, h𝔭, hl⟩ :=
    h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  let _ := (Subring.inclusion h).toAlgebra
  have hl' : IsLocalization.AtPrime (blowUpLocRing P u W') 𝔭 := hl
  have hn𝔭 : 𝔫 ≤ 𝔭 := fun b hb => by
    by_contra hb𝔭
    exact hdom b hb ((IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔭 b).2 hb𝔭)
  obtain rfl : 𝔫 = 𝔭 := h𝔫.eq_of_le h𝔭.ne_top hn𝔭
  refine ⟨W', hW'p, hW'h, hW'r, hW'le, le_antisymm hW'c ?_, h, hl'⟩
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_trans le_sup_left hWmin.1.2
  have hWmh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.full O K ι _ W
      (SupSpanMultiHomog.full O K ι P x c hP.multiProj.multiHomog hx) hWmin
  obtain ⟨hAloc, hAunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  obtain ⟨hfin, -⟩ := h₃ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have : Algebra.IsIntegral (homLocRing P W) (blowUpOverLoc P W u) := Algebra.IsIntegral.of_finite _ _
  have hmax : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := homLocRing P W) 𝔫
  have hcomap : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) =
      IsLocalRing.maximalIdeal (homLocRing P W) := IsLocalRing.eq_maximalIdeal hmax
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := h₄ O K ι J P u W' hW'le
  obtain ⟨-, hBunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J)
    (blowUpOf P u) W' hW'p hW'le
  have key : ∀ (b : K → ℕ) (w : MRing ι O), IsMultiHomog w b → w ∈ W →
      liftForm (J := J) w ∈ W' := by
    intro b w hw hwW
    by_contra hwW'
    obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hWrel b
    have hg := isMultiHomog_powMonomial (R := O) b i
    have hgW' : liftForm (J := J) (powMonomial b i) ∉ W' := fun hg' => hi (hW'c hg')
    have hzA := Subring.subset_closure (s := {z | ∃ (b : K → ℕ) (f g : MRing ι O), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ W ∧
      z = algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P g)})
      ⟨b, w, powMonomial b i, hw, hg, hi, rfl⟩
    have hm : (⟨_, hzA⟩ : homLocRing P W) ∈
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rw [hcomap]
      exact fun hu => (hAunit b w _ hw hg hi hzA).1 hu hwW
    have hzB : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
          (Ideal.Quotient.mk (blowUpOf P u) (liftForm w)) /
        algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
          (Ideal.Quotient.mk (blowUpOf P u) (liftForm (powMonomial b i))) ∈
        homLocRing (blowUpOf P u) W' := by
      unfold homLocRing
      exact Subring.subset_closure ⟨liftMDeg b, liftForm w, liftForm (powMonomial b i),
        isMultiHomog_liftForm hw, isMultiHomog_liftForm hg, hgW', rfl⟩
    have hU := ((hBunit (liftMDeg b) (liftForm w) (liftForm (powMonomial b i))
      (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW' hzB).2 hwW').map φ
    have hval : φ ⟨_, hzB⟩ =
        algebraMap (blowUpOverLoc P W u) (blowUpLocRing P u W')
          (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hzA⟩) := by
      apply Subtype.ext
      rw [hφ (liftMDeg b) _ _ (isMultiHomog_liftForm hw) (isMultiHomog_liftForm hg) hgW',
        blowUpEval_liftForm, blowUpEval_liftForm]
      rfl
    rw [hval, IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔫] at hU
    exact hU hm
  intro w hwW

  rw [Ideal.mem_comap, ← sum_weightedHomogeneousComponent (w := blockWeight ι) w,
  finsum_eq_sum _ (weightedHomogeneousComponent_finsupp _), map_sum]
  exact Ideal.sum_mem _ fun b _ =>
    key b _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hWmh w hwW b)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocPointMax.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hiso : BlowUpLocRingIso.Statement.{u}) (hfrac : BlowUpLocRingFrac.Statement.{u}) : BlowUpOverLocPointMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have : 𝔫.IsPrime := Ideal.comap_isPrime (Subring.inclusion hBR) (IsLocalRing.maximalIdeal _)
  have h𝔫 : 𝔫.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  have := h𝔫.isPrime
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ :=
      hfrac O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hW' hW'rel hW'W z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem pow_add_mul_eq_span_pow_mul {A : Type*} [CommRing A] {I : Ideal A} {k n₀ : ℕ} {y : A}
    (h : I ^ (n₀ + k) = Ideal.span {y} * I ^ n₀) (s : ℕ) :
    I ^ (n₀ + k * s) = Ideal.span {y ^ s} * I ^ n₀ := by
  have hprop : ∀ t, I ^ (n₀ + t + k) = Ideal.span {y} * I ^ (n₀ + t) := by
    intro t
    induction t with
    | zero => simpa using h
    | succ t ih =>
      rw [show n₀ + (t + 1) + k = n₀ + t + k + 1 by omega, pow_succ, ih,
        show n₀ + (t + 1) = n₀ + t + 1 by omega, pow_succ, mul_assoc]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show n₀ + k * (s + 1) = n₀ + k * s + k by ring, hprop, ih, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, ← pow_succ']

theorem mem_div_self_mul_of_mem_div_self {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    {P : Submodule A L} (Q : Submodule A L) {f : L} (hf : f ∈ P / P) : f ∈ (P * Q) / (P * Q) := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hf ⊢
  intro z hz
  refine Submodule.mul_induction_on hz (fun p hp q hq => ?_) (fun a b ha hb => ?_)
  · rw [← mul_assoc]
    exact Submodule.mul_mem_mul (hf p hp) hq
  · rw [mul_add]
    exact add_mem ha hb

theorem BlowUpColonFinite.proof (h₁ : PowSpanFinrankBounded.Statement.{u})
    (h₂ : PrincipalReductionOfBoundedGens.Statement.{u}) : BlowUpColonFinite.Statement.{u} := by
  intro A _ _ _ _ L _ _ hinj _hdim I hI
  obtain ⟨k, hk, y, hy, n₀, hred⟩ := h₂ A I (h₁ A _hdim I)
  have hlin : Algebra.linearMap A L = (Algebra.ofId A L).toLinearMap := LinearMap.ext fun _ => rfl
  have hmap : ∀ (J : Ideal A) (n : ℕ), (Submodule.map (Algebra.linearMap A L) J) ^ n =
      Submodule.map (Algebra.linearMap A L) (J ^ n) := fun J n => by
    rw [hlin]; exact (Submodule.map_pow _ _ n).symm
  set 𝓘 := Submodule.map (Algebra.linearMap A L) I with h𝓘

  have hy0 : y ≠ 0 := by
    rintro rfl
    have : I ^ (n₀ + k) = ⊥ := by
      rw [hred, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]
    exact pow_ne_zero _ hI this
  have hy' : algebraMap A L y ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))

  have hkey : ∀ s, 𝓘 ^ (n₀ + k * s) = Submodule.span A {algebraMap A L y ^ s} * 𝓘 ^ n₀ := by
    intro s
    rw [h𝓘, hmap, hmap, pow_add_mul_eq_span_pow_mul hred s, hlin, Submodule.map_mul,
      ← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton,
      AlgHom.toLinearMap_apply, map_pow, Algebra.ofId_apply]

  have hle : ∀ n, 𝓘 ^ n / 𝓘 ^ n ≤ 𝓘 ^ n₀ / 𝓘 ^ n₀ := by
    intro n f hf
    have hn : n ≤ n₀ + k * n := by nlinarith
    have hf' := mem_div_self_mul_of_mem_div_self (𝓘 ^ (n₀ + k * n - n)) hf
    rw [← pow_add, Nat.add_sub_cancel' hn, hkey] at hf'
    rw [Submodule.mem_div_iff_forall_mul_mem] at hf' ⊢
    intro z hz
    obtain ⟨w, hw, hweq⟩ := Submodule.mem_span_singleton_mul.mp
      (hf' _ (Submodule.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩))
    have : f * z = w := by
      apply mul_left_cancel₀ (pow_ne_zero n hy')
      rw [hweq]; ring
    rw [this]; exact hw

  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set c := algebraMap A L (a ^ n₀) with hc
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n₀ ha0 (hinj (by rw [← hc, h, map_zero]))
  have hcI : c ∈ 𝓘 ^ n₀ := by
    rw [h𝓘, hmap]; exact Submodule.mem_map_of_mem (Ideal.pow_mem_pow haI n₀)
  have hfg : (𝓘 ^ n₀).FG := by
    rw [h𝓘, hmap]; exact (IsNoetherian.noetherian (I ^ n₀)).map _
  have hcol : (𝓘 ^ n₀ / 𝓘 ^ n₀).FG := by
    refine Submodule.fg_of_fg_map_injective (LinearMap.mulLeft A c)
      (fun x x' h => mul_left_cancel₀ hc0 h) (hfg.of_le ?_)
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_div_iff_forall_mul_mem] at hf
    rw [LinearMap.mulLeft_apply, mul_comm]
    exact hf c hcI
  exact hcol.of_le (iSup_le hle)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
