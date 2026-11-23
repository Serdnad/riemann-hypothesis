module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
public import Mathlib.RingTheory.Ideal.Height
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def blowUpEval (P : Ideal (MRing ι R)) (u : J → MRing ι R) : MRing (extIdx ι J) R →+* MRing ι R ⧸ P :=
  (Polynomial.evalRingHom 1).comp (aeval (blowUpSubst P u)).toRingHom

variable [DecidableEq K]

def blowUpLocRing (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R)
    (Q : Ideal (MRing (extIdx ι J) R)) : Subring (FractionRing (MRing ι R ⧸ P)) :=
  Subring.closure {z | ∃ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b ∧
    IsMultiHomog G b ∧ G ∉ Q ∧
    z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G)}

def blowUpOverLoc (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    Subring (FractionRing (MRing ι R ⧸ P)) :=
  ⨅ (Q : Ideal (MRing (extIdx ι J) R)) (_ : Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
      blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ W),
    blowUpLocRing P u Q


omit [DecidableEq K] in
theorem blowUpEval_liftForm (P : Ideal (MRing ι R)) (u : J → MRing ι R) (f : MRing ι R) :
    blowUpEval P u (liftForm f) = Ideal.Quotient.mk P f := by
  show Polynomial.eval 1 (aeval (blowUpSubst P u) (liftForm f)) = _
  rw [aeval_blowUpSubst_liftForm, Polynomial.eval_C]

theorem homLocRing_le_blowUpOverLoc {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    homLocRing P W ≤ blowUpOverLoc P W u := by
  refine le_iInf₂ fun Q hQ => Subring.closure_le.mpr ?_
  rintro z ⟨b, f, g, hf, hg, hgW, rfl⟩
  refine Subring.subset_closure ⟨liftMDeg b, liftForm f, liftForm g, isMultiHomog_liftForm hf,
    isMultiHomog_liftForm hg, fun h => hgW (hQ.2.2.2.2 h), ?_⟩
  rw [blowUpEval_liftForm, blowUpEval_liftForm]

instance blowUpOverLoc.instAlgebra {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    Algebra (homLocRing P W) (blowUpOverLoc P W u) :=
  (Subring.inclusion (homLocRing_le_blowUpOverLoc P W u)).toAlgebra

end Objects

section Lemmas

def BlowUpLocRingIso.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (J : Type)
    (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (Q : Ideal (MRing (extIdx ι J) R)),
    blowUpOf P u ≤ Q →
    haveI : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
    ∃ φ : homLocRing (blowUpOf P u) Q ≃+* blowUpLocRing P u Q,
      ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R) (hF : IsMultiHomog F b)
        (hG : IsMultiHomog G b) (hGQ : G ∉ Q),
        (φ ⟨_, Subring.subset_closure ⟨b, F, G, hF, hG, hGQ, rfl⟩⟩ : FractionRing (MRing ι R ⧸ P)) =
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G)

def BlowUpOverLocFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      Module.Finite (homLocRing P W) (blowUpOverLoc P W u) ∧
        Module.finrank (homLocRing P W) (blowUpOverLoc P W u) = 1

def BlowUpOverLocMax.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∃ e : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} ≃ {W' : Ideal (MRing (extIdx ι J) O) //
          W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
        ∀ 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal},
          (∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u (e 𝔫).1,
            letI := (Subring.inclusion h).toAlgebra
            haveI := 𝔫.2.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u (e 𝔫).1) 𝔫.1) ∧
          𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open Module IsLocalRing

noncomputable section

universe u

namespace FiniteBirationalLength

theorem length_quot_maximal_eq_inertiaDeg {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (𝔫 : Ideal B) [𝔫.IsMaximal] :
    Module.length A (B ⧸ 𝔫) = (𝔫.inertiaDeg A : ℕ∞) := by
  have hmax : (𝔫.under A).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔫
  have hm : 𝔫.under A = maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  have : 𝔫.LiesOver (maximalIdeal A) := ⟨hm.symm⟩
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ 𝔫) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) 𝔫,
    Module.length_eq_of_surjective (R := A ⧸ maximalIdeal A) (S := A) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

theorem full : FiniteBirationalLength.Statement.{u} := by
  intro A B _ _ _ _ _ _ _ _ hdim hinj hrank z hz
  classical
  have hfinMS := Vertical.LengthDecomp.finite_maximalSpectrum (R := A) (B := B)
  have hfin : Finite {𝔫 : Ideal B // 𝔫.IsMaximal} :=
    Finite.of_injective
      (fun 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal} => (⟨𝔫.1, 𝔫.2⟩ : MaximalSpectrum B))
      (fun a b h => Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
  refine ⟨hfin, ?_⟩
  let : Fintype {𝔫 : Ideal B // 𝔫.IsMaximal} := Fintype.ofFinite _
  have : Module.IsTorsionFree A B := isTorsionFree_iff_algebraMap_injective.mpr hinj
  have h1 := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A B z hdim hz
  rw [hrank, Nat.cast_one, one_mul, Ring.ord] at h1
  let hP : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal}, 𝔫.1.IsPrime := fun 𝔫 => 𝔫.2.isPrime
  have h2 := FieldNumbers.FiniteAlgebraLengthSum.proof A B {𝔫 : Ideal B // 𝔫.IsMaximal}
    (fun 𝔫 => 𝔫.1) (fun 𝔫 => 𝔫.2) Subtype.val_injective (fun M hM => ⟨⟨M, hM⟩, rfl⟩)
    (fun 𝔫 => Localization.AtPrime 𝔫.1) (fun 𝔫 => inferInstance) z
  rw [← h1, h2, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have := 𝔫.2
  rw [length_quot_maximal_eq_inertiaDeg, Ring.ord]

end FiniteBirationalLength

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

def HomLocRingMem.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    ∀ z : FractionRing (MRing ι R ⧸ P), z ∈ homLocRing P W ↔
      ∃ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
        z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g)

def HomLocRingIsLocal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (MRing ι R)) [P.IsPrime], W.IsPrime → P ≤ W →
    IsLocalRing (homLocRing P W) ∧
      ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
        ∀ hz : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P g) ∈
              homLocRing P W,
          IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W

def HomLocRingNoetherian.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      IsNoetherianRing (homLocRing P W)

def HomLocRingDimLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι R)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      ringKrullDim (homLocRing P W) ≤ ((W.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace plainPairNumber

section ClassNum

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename {σ τ : Type*} (e : σ → τ) (he : Function.Injective e) (cls : τ → K → ℤ)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he]
  congr 2
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_eq_sum_of_subset {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) {S : Finset (σ →₀ ℕ)} (hS : H.support ⊆ S) :
    classNum cls H Q W = ∑ μ ∈ S, H.coeff μ * vNumL W (classList cls μ ++ Q) :=
  Finset.sum_subset hS fun μ _ hμ => by
    rw [mem_support_iff, not_not] at hμ
    rw [hμ, zero_mul]


omit [DecidableEq K] in
theorem classList_add_perm {σ : Type*} (cls : σ → K → ℤ) (μ ν : σ →₀ ℕ) :
    (classList cls (μ + ν)).Perm (classList cls μ ++ classList cls ν) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [classList, Multiset.coe_toList, map_add (f := _), Multiset.map_add (f := _)]


theorem classNum_mul_monomial {σ : Type*} [DecidableEq σ] (cls : σ → K → ℤ) (A : MvPolynomial σ ℤ)
    (t : σ →₀ ℕ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (A * monomial t 1) Q W = classNum cls A (classList cls t ++ Q) W := by
  have hsub : (A * monomial t 1).support ⊆ A.support.image (· + t) := by
    intro ν hν
    rw [mem_support_iff, coeff_mul_monomial'] at hν
    split_ifs at hν with hle
    · rw [mul_one] at hν
      exact Finset.mem_image.mpr ⟨ν - t, mem_support_iff.mpr hν, tsub_add_cancel_of_le hle⟩
    · exact absurd rfl hν
  rw [classNum_eq_sum_of_subset cls _ Q W hsub,
    Finset.sum_image fun a _ b _ h => add_right_cancel h]
  unfold classNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_mul_monomial, mul_one, ← List.append_assoc,
    FlagTypings.vNumL_perm W ((classList_add_perm cls μ t).append_right Q)]

end ClassNum

section DivDiff

def term {r : ℕ} (l : Fin r) (μ : Fin r →₀ ℕ) : MvPolynomial (Fin r ⊕ Fin r) ℤ :=
  (∏ j ∈ Finset.univ.filter (fun j => j < l), X (Sum.inr j) ^ μ j) *
    (∑ a ∈ Finset.range (μ l), X (Sum.inl l) ^ a * X (Sum.inr l) ^ (μ l - 1 - a)) *
    ∏ j ∈ Finset.univ.filter (fun j => l < j), X (Sum.inl j) ^ μ j

theorem rename_divDiff_eq_sum {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ)
    {S : Finset (Fin r →₀ ℕ)} (hS : G.support ⊆ S) :
    rename finSumFinEquiv.symm (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff l G) =
      ∑ μ ∈ S, C (G.coeff μ) * term l μ := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff

  simp only [map_sum, map_mul, map_prod, map_pow, rename_X, rename_C,
  finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
  refine (Finset.sum_subset hS ?_).trans (Finset.sum_congr rfl fun μ _ => ?_)
  · intro μ _ hμ
    rw [mem_support_iff, not_not] at hμ
    simp [hμ]
  · unfold term
    ring

end DivDiff

end plainPairNumber

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end
