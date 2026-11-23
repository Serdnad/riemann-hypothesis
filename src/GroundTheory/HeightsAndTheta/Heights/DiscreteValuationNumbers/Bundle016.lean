module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle001
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Algebra.Module.SpanRankOperations
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IsLocalRing Module

universe u

theorem PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    (h : ringKrullDim A = 1) : ∃ x ∈ maximalIdeal A, x ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro hbot
  have h0 := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hbot)
  rw [h] at h0
  exact absurd h0 (by decide)

theorem PowSpanFinrankBounded.finrank_quotient_eq_length {A : Type u} [CommRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (finrank (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) : ℕ∞) =
      length A (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) := by
  have : Module.Finite (A ⧸ maximalIdeal A) (M ⧸ maximalIdeal A • (⊤ : Submodule A M)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective]
  let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  exact (Module.length_eq_finrank (A ⧸ maximalIdeal A) _).symm

theorem PowSpanFinrankBounded.spanFinrank_le_length {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (N : Ideal A) {x : A} (hx : x ∈ maximalIdeal A) :
    (N.spanFinrank : ℕ∞) ≤ length A (↥N ⧸ LinearMap.range (LinearMap.lsmul A ↥N x)) := by
  have hle : LinearMap.range (LinearMap.lsmul A ↥N x) ≤ maximalIdeal A • (⊤ : Submodule A ↥N) := by
    rintro _ ⟨m, rfl⟩
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  rw [spanFinrank_eq_finrank_quotient N (IsNoetherian.noetherian N),
    PowSpanFinrankBounded.finrank_quotient_eq_length]
  exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

theorem PowSpanFinrankBounded.proof : PowSpanFinrankBounded.Statement.{u} := by
  intro A _ _ _ _ h I
  obtain ⟨x, hxm, hx0⟩ := PowSpanFinrankBounded.exists_ne_zero_mem_maximalIdeal h
  have := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq (A := A) h
  have hA := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A A x h hx0
  have hfin := ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top A hx0
  rw [finrank_self, Nat.cast_one, one_mul] at hA
  have hord : Ring.ord A x ≠ ⊤ := hA ▸ hfin
  refine ⟨(Ring.ord A x).toNat, fun n => ?_⟩
  have hN := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A ↥(I ^ n) x h hx0
  have hr : finrank A ↥(I ^ n) ≤ 1 := (Submodule.finrank_le (I ^ n)).trans_eq (finrank_self A)
  have key : ((I ^ n).spanFinrank : ℕ∞) ≤ ((Ring.ord A x).toNat : ℕ∞) := by
    rw [ENat.natCast_toNat hord]
    calc ((I ^ n).spanFinrank : ℕ∞)
        ≤ length A (↥(I ^ n) ⧸ LinearMap.range (LinearMap.lsmul A ↥(I ^ n) x)) :=
          PowSpanFinrankBounded.spanFinrank_le_length (I ^ n) hxm
      _ = (finrank A ↥(I ^ n) : ℕ∞) * Ring.ord A x := hN
      _ ≤ 1 * Ring.ord A x := by gcongr; exact_mod_cast hr
      _ = Ring.ord A x := one_mul _
  exact_mod_cast key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

section General

variable {A : Type*} [CommRing A]

theorem mem_minimalPrimes_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨‹Q.IsPrime›, hJQ⟩, fun W hW hWQ q hq => ?_⟩
  obtain ⟨s, hs, hsq⟩ := hsat q hq
  exact (hW.1.mem_or_mem (hW.2 hsq)).resolve_left (fun h => hs (hWQ h))

theorem localizedQuot_map_bijective_of_saturated (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q)
    (hsat : ∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) :
    Function.Bijective (LocalizedModule.map Q.primeCompl
      (Submodule.mapQ J Q LinearMap.id (fun _ ha => hJQ ha) : (A ⧸ J) →ₗ[A] A ⧸ Q)) := by
  refine ⟨?_, LocalizedModule.map_surjective _ _ ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using LocalizedModule.induction_on with | h m s => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [LinearMap.mem_ker, LocalizedModule.map_mk] at hx
    have haQ : a ∈ Q := localizedQuotient_mk_eq_zero Q a s hx
    obtain ⟨t, ht, hta⟩ := hsat a haQ
    rw [Submodule.mem_bot, ← LocalizedModule.zero_mk (1 : Q.primeCompl), LocalizedModule.mk_eq]
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [smul_zero, smul_zero, one_smul, Submonoid.smul_def, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hta
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk J a, rfl⟩

end General

universe u

theorem MultAtOfSaturated.proof : MultAtOfSaturated.Statement.{u} := by
  intro R _ K ι J Q _ hJQ hsat
  refine ⟨mem_minimalPrimes_of_saturated J Q hJQ hsat, ?_⟩
  unfold multAt
  rw [(LinearEquiv.ofBijective _ (localizedQuot_map_bijective_of_saturated J Q hJQ hsat)).length_eq,
    Module.length_eq_one_iff]
  exact localizedQuotient_isSimpleModule Q

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace PointIdealMultiProj

variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}

def coneWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_monomial_isWeightedHomogeneous (z : (Σ k, ι k) → L) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap F z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := L) (coneWeight K) p.1).C_mul (z p)).pow (d p)

theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι F) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap F z f) =
      pointConeMap F z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := coneMap_monomial_isWeightedHomogeneous (K := K) (F := F) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι F)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem proof : PointIdealMultiProj.Statement := by
  intro F _ L _ _ K _ ι z hz
  refine ⟨?_, ?_, ?_⟩
  · exact RingHom.ker_isPrime _
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (F := F) z b f
    rw [show (pointConeMap F z) f = 0 from hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap F z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

end PointIdealMultiProj

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem EffectiveCase.proof (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ

  suffices H : ∀ n : ℕ, ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      commonExcess ϖ P f g s = n → ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L by
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH L
    exact H _ K ι P d hP b f g hD c s hs hsP hH rfl L
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH hn L
    by_cases hcom : ∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0
    · refine h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hcom ?_ L
      intro K' _ _ ι' _ P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' hlt L'
      exact ih _ (hn ▸ hlt) K' ι' P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' rfl L'
    · refine h₀ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH (fun G hG hsG => ?_) L
      by_contra hDG
      exact hcom ⟨G, hG, hsG, hDG⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section JoinPullback

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}

theorem joinCoords_inl {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (k : K)
    (i : ι k) : joinCoords y y' ⟨Sum.inl k, i⟩ = y ⟨k, i⟩ := rfl

theorem pointConeMap_joinCoords_joinForm {Ω : Type*} [Field Ω] (R : Type*) [CommRing R]
    [Algebra R Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    pointConeMap R (joinCoords y y') (joinForm f) =
      rename (Sum.inl : K → K ⊕ K') (pointConeMap R y f) := by
  simp only [pointConeMap, joinForm, aeval_rename]
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    obtain ⟨k, i⟩ := v
    simp [hp, joinCoords_inl]

theorem joinForm_mem_pointIdeal_iff {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    joinForm f ∈ pointIdeal R (joinCoords y y') ↔ f ∈ pointIdeal R y := by
  simp only [pointIdeal, RingHom.mem_ker, pointConeMap_joinCoords_joinForm]
  exact map_eq_zero_iff _ (rename_injective _ Sum.inl_injective)

theorem isMultiHomog_joinForm [DecidableEq K] [DecidableEq K'] {R : Type*} [CommRing R]
    {f : MRing ι R} {bf : K → ℕ} (hf : IsMultiHomog f bf) :
    IsMultiHomog (joinForm (ι' := ι') f) (Sum.elim bf 0) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa [joinForm] using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [joinForm, map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    simp only [joinForm, rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
      Finsupp.weight_apply]
    funext s
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight]
    rcases s with k | k
    · simp [Pi.single_apply]
    · simp

end JoinPullback

theorem VerticalDivisorJoinPullback.proof : VerticalDivisorJoinPullback.Statement := by
  intro O _ _ _ ϖ Ω _ _ K _ _ ι _ K' _ _ ι' _ y y' b f g hD
  refine IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨Sum.elim bf 0, Sum.elim bg 0, isMultiHomog_joinForm hf, isMultiHomog_joinForm hg, ?_⟩
    funext s
    rcases s with k | k
    · simp [joinDeg, ← hb]
    · simp [joinDeg]
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.num_not_mem
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.den_not_mem
  · intro W hW hPW hrel hϖ
    let φ : MRing ι O →ₐ[O] MRing (Sum.elim ι ι') O :=
      rename (fun p : (Σ k, ι k) => (⟨Sum.inl p.1, p.2⟩ : Σ s : K ⊕ K', Sum.elim ι ι' s))
    have hφ : ∀ h, joinForm (ι' := ι') h = φ h := fun _ => rfl
    have hle : pointIdeal O y ≤ W.comap φ := by
      intro h hh
      rw [Ideal.mem_comap, ← hφ]
      exact hPW ((joinForm_mem_pointIdeal_iff O y y' h).mpr hh)
    have hrel' : IsRelevant (W.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap]; simpa [φ, rename_X] using hi⟩
    have hϖ' : (C ϖ : MRing ι O) ∉ W.comap φ := by
      rw [Ideal.mem_comap]; simpa [φ, rename_C] using hϖ
    obtain ⟨u, v, hu, hv, huv⟩ :=
      hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ'
    refine ⟨joinForm u, joinForm v, hu, hv, ?_⟩
    have := (joinForm_mem_pointIdeal_iff O y y' _).mpr huv
    simpa [hφ, map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]


open scoped Classical in
open Classical in
def locCycle (J W : Ideal R) : ℤ :=
  if h : W ∈ J.minimalPrimes then
    haveI : W.IsPrime := h.1.1
    ((Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J))).toNat : ℤ)
  else 0

end Defs

section Lemmas

def LeftTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    ∀ G U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      ratDiv P f g G * divCycle G s U = 0

def RightTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι O)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ W U : Ideal (MRing ι O),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U) →
      divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U = 0

def LocalCoeffRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (P U : Ideal R), P.IsPrime → U.IsPrime → P ≤ U →
    (∀ Q₁ Q₂ : Ideal R, Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U → False) →
    ∀ f g s u v : R, f ∉ P → g ∉ P → s ∉ P → u ∉ U → u * f - v * g ∈ P →
    (∀ W : Ideal R, W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U =
      ∑ᶠ W, locCycle (P ⊔ Ideal.span {s}) W *
        locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U

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

theorem NoCommonComponentCase.proof (h₁ : LeftExpansion.Statement.{u}) (h₂ : RightExpansion.Statement.{u})
    (h₃ : LocalCoefficient.Statement.{u}) (h₄ : IntNumVanish.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno L
  unfold cutIdentity
  rw [h₁ O ϖ hϖ K ι P d hP b f g hD.1 c s hs hsP hno L,
    h₂ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno L]
  unfold cycEval
  refine finsum_congr fun U => ?_
  beta_reduce
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧
      ¬ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)
  ·
    obtain ⟨hUp, hUm, -, hϖU, hdim⟩ := hU
    have hv : vNum U L = 0 := by
      refine h₄ _ K ι d (specialIdeal U) (SpecialIdealCorresp.proof O ϖ hϖ K ι ⊥ U hUp hϖU).1
        (SpecialIdealMultiHomog.proof O K ι U hUm) (Or.inr ?_) L
      rw [SpecialQuotDim.proof O ϖ hϖ K ι U hϖU]
      exact lt_of_not_ge hdim
    rw [hv, mul_zero, mul_zero]
  ·
    have e := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno U fun hp hm hr hϖU => by
      by_contra h
      exact hU ⟨hp, hm, hr, hϖU, h⟩
    unfold cycEval at e
    rw [e]

end GroundTheory.Heights₂.Heights.NumbersDVR
end
