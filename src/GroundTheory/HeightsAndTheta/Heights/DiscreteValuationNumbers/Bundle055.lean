module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.RingTheory.OrderOfVanishing.Basic
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

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxPoint.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          (W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W) ∧
          (∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

def BlowUpOverLocPointMax.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔫.isPrime
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpLocRingInj.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (J : Type)
    (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (Q Q' : Ideal (MRing (extIdx ι J) R)),
    Q.IsPrime → IsMultiHomogIdeal Q → IsRelevant Q → blowUpOf P u ≤ Q →
    Q'.IsPrime → IsMultiHomogIdeal Q' → IsRelevant Q' → blowUpOf P u ≤ Q' →
    blowUpLocRing P u Q = blowUpLocRing P u Q' → Q = Q'

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

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxCentre.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (MRing (extIdx ι J) O),
          W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W ∧
          ∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpOverLocFibreMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
    ∀ W' : Ideal (MRing (extIdx ι J) O), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
      blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes

def BlowUpOverLocPointDeg.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          (letI := (Subring.inclusion h).toAlgebra
           haveI := h𝔫.isPrime
           IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

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

noncomputable section

universe u

section Lemmas

def BlowUpOverLocPointLoc.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (MRing (extIdx ι J) O), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
        blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          letI := (Subring.inclusion h).toAlgebra
          haveI := h𝔫.isPrime
          IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

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

noncomputable section

universe u

theorem length_quot_span_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R ≃+* R') (r : R) :
    Module.length R (R ⧸ Ideal.span {r}) = Module.length R' (R' ⧸ Ideal.span {ψ r}) := by
  let _ : Algebra R R' := ψ.toRingHom.toAlgebra
  let e : (R ⧸ Ideal.span {r}) ≃ₐ[R] R' ⧸ Ideal.span {ψ r} :=
    Ideal.quotientEquivAlg _ _ (AlgEquiv.ofRingEquiv (f := ψ) fun _ => rfl)
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  rw [e.toLinearEquiv.length_eq, Module.length_eq_of_surjective ψ.surjective]



theorem BlowUpFibreSemilocal.proof (ha : HomLocRingLocal.Statement.{u})
    (hb : DivCycleHomLoc.Statement.{u}) (hiso : BlowUpLocRingIso.Statement.{u})
    (hfin : BlowUpOverLocFinite.Statement.{u}) (hmax : BlowUpOverLocMax.Statement.{u}) :
    BlowUpFibreSemilocal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel g hg hgW hz
  have := hP.multiProj.isPrime
  obtain ⟨hfinite, hrank⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  obtain ⟨e, he⟩ := hmax O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hbl : IsModelOver (blowUpOf P u) n := BlowUpModel.full O K ι J P n hP N u hu hu'
  refine ⟨blowUpOverLoc P W u, inferInstance, inferInstance, inferInstance, hfinite,
    Subring.inclusion_injective _, hrank, e, fun 𝔫 => ⟨?_, (he 𝔫).2⟩⟩
  obtain ⟨h, hloc⟩ := (he 𝔫).1
  generalize e 𝔫 = Q at h hloc ⊢
  obtain ⟨Q, hQmin, hQrel, hQW⟩ := Q
  dsimp only at h hloc ⊢
  have hblQ : blowUpOf P u ≤ Q := le_trans le_sup_left hQmin.1.2
  have hxl : IsMultiHomog (liftForm (J := J) x) (liftMDeg c) := isMultiHomog_liftForm hx
  have hgl : IsMultiHomog (liftForm (J := J) g) (liftMDeg c) := isMultiHomog_liftForm hg
  have hgQ : liftForm (J := J) g ∉ Q := fun hm => hgW (by rw [← hQW]; exact hm)
  have hxbl : liftForm (J := J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm x)) /
      algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
      homLocRing (blowUpOf P u) Q :=
    Subring.subset_closure ⟨liftMDeg c, _, _, hxl, hgl, hgQ, rfl⟩
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u Q hblQ

  have hlen : Module.length (homLocRing (blowUpOf P u) Q)
      (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) =
        ((divCycle (blowUpOf P u) (liftForm x) Q).toNat : ℕ∞) := by
    have hinj := IsFractionRing.injective (MRing (extIdx ι J) O ⧸ blowUpOf P u)
      (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
    have hne : ∀ y : MRing (extIdx ι J) O, y ∉ blowUpOf P u →
        algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ y) ≠ 0 := by
      intro y hy
      rw [Ne, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    have hz0 : (⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q) ≠ 0 := fun h0 =>
      div_ne_zero (hne _ hxbl) (hne _ fun hm => hgQ (hblQ hm)) (congrArg Subtype.val h0)
    have hQp : Q.IsPrime := hQmin.1.1
    have hmult := hb O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c) (liftForm x) hxl
      hxbl Q hQmin hQrel (liftForm g) hgl hgQ hz'
    have hloc' := ha O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c)
      (liftForm x) hxl hxbl Q hQmin hQrel
    have hn : IsNoetherianRing (homLocRing (blowUpOf P u) Q) := hloc'.2.1
    have hd : ringKrullDim (homLocRing (blowUpOf P u) Q) = 1 := hloc'.2.2
    have hdivQ : divCycle (blowUpOf P u) (liftForm x) Q =
        ((multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Q).toNat : ℤ) := by
      unfold divCycle
      rw [dite_eq_left ⟨hQmin, hQrel⟩]
    have : Ring.KrullDimLE 1 (homLocRing (blowUpOf P u) Q) := by
      rw [Ring.krullDimLE_iff, hd]
      rfl
    have hfinl : Module.length (homLocRing (blowUpOf P u) Q)
        (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr
        (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hz0))
    rw [hdivQ, Int.toNat_natCast, hmult, ENat.natCast_toNat hfinl]

  let _ := (Subring.inclusion h).toAlgebra
  have := 𝔫.2.isPrime
  have := hloc
  let ψ₁ : Localization.AtPrime 𝔫.1 ≃ₐ[blowUpOverLoc P W u] blowUpLocRing P u Q :=
    IsLocalization.algEquiv 𝔫.1.primeCompl _ _
  let ψ : Localization.AtPrime 𝔫.1 ≃+* homLocRing (blowUpOf P u) Q := ψ₁.toRingEquiv.trans φ.symm
  have hψ : ψ (algebraMap (blowUpOverLoc P W u) (Localization.AtPrime 𝔫.1)
      (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩)) = ⟨_, hz'⟩ := by
    apply φ.injective
    simp only [ψ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    apply Subtype.ext
    rw [hφ (liftMDeg c) _ _ hxl hgl hgQ, blowUpEval_liftForm, blowUpEval_liftForm]
    rfl
  rw [length_quot_span_ringEquiv ψ, hψ]
  exact hlen

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Abstract

variable {D A : Type*} [CommRing D] [IsDomain D] [CommRing A] [IsDomain A]

theorem exists_ringEquiv_closure_div_of_eq_C_mul_X_pow (θ : A →+* Polynomial D)
    (hθ : Function.Injective θ) {I : Type*} (f g : I → A) (a c : I → D) (n : I → ℕ)
    (hf : ∀ i, θ (f i) = Polynomial.C (a i) * Polynomial.X ^ n i)
    (hg : ∀ i, θ (g i) = Polynomial.C (c i) * Polynomial.X ^ n i)
    (s₁ : Subring (FractionRing A)) (s₂ : Subring (FractionRing D))
    (h₁ : s₁ = Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)))
    (h₂ : s₂ = Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))) :
    ∃ φ : s₁ ≃+* s₂, ∀ i (hi : algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i) ∈ s₁),
      (φ ⟨_, hi⟩ : FractionRing D) =
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i) := by
  subst h₁ h₂
  let M := FractionRing (Polynomial D)
  have hM : Function.Injective (algebraMap (Polynomial D) M) := IsFractionRing.injective _ M
  let g₁ : A →+* M := (algebraMap (Polynomial D) M).comp θ
  let g₂ : D →+* M := (algebraMap (Polynomial D) M).comp Polynomial.C
  have hg₁ : Function.Injective g₁ := hM.comp hθ
  have hg₂ : Function.Injective g₂ := hM.comp Polynomial.C_injective
  let ι₁ : FractionRing A →+* M := IsFractionRing.lift hg₁
  let ι₂ : FractionRing D →+* M := IsFractionRing.lift hg₂
  have hgen : ∀ i, ι₁ (algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i)) =
      ι₂ (algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i)) := by
    intro i
    rw [map_div₀, map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap,
      IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    have hX : algebraMap (Polynomial D) M (Polynomial.X ^ n i) ≠ 0 := fun h =>
      pow_ne_zero _ Polynomial.X_ne_zero (hM (h.trans (map_zero _).symm))
    simp only [g₁, g₂, RingHom.comp_apply, hf, hg, map_mul]
    exact mul_div_mul_right _ _ hX
  have himg : (Subring.closure (Set.range fun i =>
        algebraMap A (FractionRing A) (f i) / algebraMap A (FractionRing A) (g i))).map ι₁ =
      (Subring.closure (Set.range fun i =>
        algebraMap D (FractionRing D) (a i) / algebraMap D (FractionRing D) (c i))).map ι₂ := by
    rw [RingHom.map_closure, RingHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (hgen i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hgen i⟩
  refine ⟨(Subring.equivMapOfInjective _ ι₁ ι₁.injective).trans ((RingEquiv.subringCongr himg).trans
    (Subring.equivMapOfInjective _ ι₂ ι₂.injective).symm), fun i hi => ?_⟩
  apply ι₂.injective
  rw [← hgen i, ← Subring.coe_equivMapOfInjective_apply _ ι₂ ι₂.injective, RingEquiv.trans_apply,
    RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

end Abstract

variable {K : Type*} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem aeval_blowUpSubst_of_isMultiHomog (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b) :
    aeval (blowUpSubst P u) F = Polynomial.C (blowUpEval P u F) * Polynomial.X ^ (b none) := by
  classical
  set w := blockWeight (extIdx ι J)
  set ωT : (Σ o, extIdx ι J o) → ℕ := fun v => Pi.evalAddMonoidHom (fun _ => ℕ) none (w v)
  have hT : ∀ d, Finsupp.weight ωT d = Finsupp.weight w d none := fun d =>
    weight_comp_addMonoidHom_apply w (Pi.evalAddMonoidHom (fun _ => ℕ) none) d
  have hsubst : blowUpSubst P u = fun v =>
      Polynomial.C (Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) * Polynomial.X ^ ωT v := by
    funext v
    obtain ⟨o, i⟩ := v
    cases o <;> simp [blowUpSubst, blowUpAtOne, ωT, w, blockWeight]
  have hFT : IsWeightedHomogeneous ωT F (b none) := by
    intro d hd
    rw [hT]
    exact congrFun (hF hd) none
  set c := aeval (fun v => Ideal.Quotient.mkₐ R P (blowUpAtOne u v)) F
  have key : aeval (blowUpSubst P u) F = Polynomial.C c * Polynomial.X ^ (b none) := by
    refine Polynomial.ext fun n => ?_
    rw [hsubst, coeff_aeval_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hn
    · rw [hn, hFT.weightedHomogeneousComponent_same]
    · rw [hFT.weightedHomogeneousComponent_ne n hn, map_zero]
  have hσ : blowUpEval P u F = c := by
    show Polynomial.eval 1 (aeval (blowUpSubst P u) F) = c
    rw [key]
    simp
  rw [hσ]
  exact key

theorem BlowUpLocRingIso.proof : BlowUpLocRingIso.Statement.{u} := by
  intro R _ K _ ι J P _ u Q _
  have hB : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  let θ : MRing (extIdx ι J) R ⧸ blowUpOf P u →+* Polynomial (MRing ι R ⧸ P) :=
    Ideal.Quotient.lift (blowUpOf P u) (aeval (blowUpSubst P u)).toRingHom
      (fun a ha => RingHom.mem_ker.mp ha)
  have hθ : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr ha)
  let I := {t : (Option K → ℕ) × MRing (extIdx ι J) R × MRing (extIdx ι J) R //
    IsMultiHomog t.2.1 t.1 ∧ IsMultiHomog t.2.2 t.1 ∧ t.2.2 ∉ Q}
  have hf : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) =
      Polynomial.C (blowUpEval P u i.1.2.1) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.1
  have hg : ∀ i : I, θ (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2) =
      Polynomial.C (blowUpEval P u i.1.2.2) * Polynomial.X ^ (i.1.1 none) := fun i => by
    rw [Ideal.Quotient.lift_mk]
    exact aeval_blowUpSubst_of_isMultiHomog P u i.2.2.1
  have h₁ : homLocRing (blowUpOf P u) Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) /
        algebraMap _ (FractionRing (MRing (extIdx ι J) R ⧸ blowUpOf P u)) (Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)) := by
    rw [homLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  have h₂ : blowUpLocRing P u Q = Subring.closure (Set.range fun i : I =>
      algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.1) /
        algebraMap _ (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u i.1.2.2)) := by
    rw [blowUpLocRing]
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGQ, rfl⟩
      exact ⟨⟨(b, F, G), hF, hG, hGQ⟩, rfl⟩
    · rintro ⟨⟨⟨b, F, G⟩, hF, hG, hGQ⟩, rfl⟩
      exact ⟨b, F, G, hF, hG, hGQ, rfl⟩
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_closure_div_of_eq_C_mul_X_pow θ hθ
    (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.1) (fun i : I => Ideal.Quotient.mk (blowUpOf P u) i.1.2.2)
    (fun i : I => blowUpEval P u i.1.2.1) (fun i : I => blowUpEval P u i.1.2.2) (fun i : I => i.1.1 none)
    hf hg _ _ h₁ h₂
  refine ⟨φ, ?_⟩
  intro b F G hF hG hGQ
  exact hφ ⟨(b, F, G), hF, hG, hGQ⟩ _

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
