module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle019
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem LocalCoefficient.proof (h₁ : LeftTermSupport.Statement.{u})
    (h₂ : RightTermSupport.Statement.{u}) (h₃ : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno U hUdim
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧ P ≤ U
  swap
  ·
    have hl := h₁ O ϖ K ι P hP.multiProj.multiHomog b f g hD.1 c s hs
    have hr := h₂ O ϖ K ι P hP.multiProj.multiHomog b f g hD c s hs hH
    unfold cycEval
    rw [finsum_congr fun G => hl G U hU, finsum_congr fun W => hr W U hU, finsum_zero]
  obtain ⟨hUp, hUm, hUr, hϖU, hPU⟩ := hU
  have hUdim' := hUdim hUp hUm hUr hϖU
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hrel : ∀ W : Ideal (MRing ι O), W ≤ U → IsRelevant W := fun W hW k =>
    let ⟨i, hi⟩ := hUr k
    ⟨i, fun h => hi (hW h)⟩
  have hcyc : ∀ J W : Ideal (MRing ι O), IsRelevant W → idealCycle J W = locCycle J W := by
    intro J W hW
    unfold idealCycle locCycle
    by_cases hm : W ∈ J.minimalPrimes
    · rw [dite_eq_left ⟨hm, hW⟩, dite_eq_left hm]
      rfl
    · rw [dite_eq_right fun h => hm h.1, dite_eq_right hm]
  have hzero : ∀ J : Ideal (MRing ι O), ¬ J ≤ U → locCycle J U = 0 := by
    intro J hJ
    unfold locCycle
    rw [dite_eq_right fun h => hJ h.1.2]
  have hL : ∀ G, ratDiv P f g G * divCycle G s U =
      (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U := by
    intro G
    rw [divCycle_eq_idealCycle, hcyc _ _ hUr]
    by_cases hG : G ≤ U
    · unfold ratDiv
      rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel G hG), hcyc _ _ (hrel G hG)]
    · rw [hzero _ fun h => hG (le_sup_left.trans h), mul_zero, mul_zero]
  have hR : ∀ W, divCycle P s W * idealCycle (W ⊔ divisorIdeal P f g) U =
      locCycle (P ⊔ Ideal.span {s}) W * locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U := by
    intro W
    show divCycle P s W * idealCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U = _
    rw [hcyc _ _ hUr]
    by_cases hW : W ≤ U
    · rw [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    · rw [hzero _ fun h => hW (le_sup_left.trans h), mul_zero, mul_zero]

  have hchain : ∀ Q₁ Q₂ : Ideal (MRing ι O), Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U →
      False := by
    intro Q₁ Q₂ _ _ hPQ hQQ hQU
    have e₁ := DimStrictDrop.proof (MRing ι O) P Q₁ hPQ
    have e₂ := DimStrictDrop.proof (MRing ι O) Q₁ Q₂ hQQ
    have e₃ := DimStrictDrop.proof (MRing ι O) Q₂ U hQU
    rw [hP.dim] at e₁
    have key : ((d + Fintype.card K : ℕ) : WithBot ℕ∞) + 1 + 1 + 1 ≤
        ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      ((add_le_add (add_le_add (add_le_add hUdim' le_rfl) le_rfl) le_rfl).trans
        ((add_le_add (add_le_add e₃ le_rfl) le_rfl).trans ((add_le_add e₂ le_rfl).trans e₁)))
    have key' : ((d + Fintype.card K + 3 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc, one_add_one_eq_two, two_add_one_eq_three] using key
    have := WithBot.coe_le_coe.mp key'
    norm_cast at this
    omega

  obtain ⟨u', v', hu', huv⟩ := hD.2 U hUp hPU hUr

  have hnc : ∀ W : Ideal (MRing ι O), W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W := by
    intro W hW h
    have hs' : divCycle P s W ≠ 0 := by rwa [divCycle_eq_idealCycle, hcyc _ _ (hrel W hW)]
    have hr : ratDiv P f g W = 0 := by
      by_cases hϖW : (C ϖ : MRing ι O) ∈ W
      · exact hno W hϖW hs'
      · by_contra h
        exact hϖW (hD.1.vertical W h)
    unfold ratDiv at hr
    rw [divCycle_eq_idealCycle, divCycle_eq_idealCycle, hcyc _ _ (hrel W hW),
      hcyc _ _ (hrel W hW)] at hr
    omega
  unfold cycEval
  rw [finsum_congr hL, finsum_congr hR]
  exact h₃ (MRing ι O) P U hPp hUp hPU hchain f g s u' v' hD.1.num_not_mem hD.1.den_not_mem hsP hu'
    huv hnc

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

universe u

section Lemmas

def LocCycleSpanMul.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x y : A), x ≠ 0 → y ≠ 0 →
    ∀ W : Ideal A, locCycle (Ideal.span {x * y}) W =
      locCycle (Ideal.span {x}) W + locCycle (Ideal.span {y}) W

def LocCyclePos.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (J W : Ideal R), W ∈ J.minimalPrimes →
    0 < locCycle J W

def MinimalPrimesSpanSingleton.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x : A), x ≠ 0 →
    ∀ W : Ideal A, W ∈ (Ideal.span {x}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ x ∈ W

def LocalDomainDimTwo.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    (∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A) →
    ringKrullDim A = 2 ∧ (IsLocalRing.maximalIdeal A).height = 2 ∧
      ∀ Q : Ideal A, Q.IsPrime → ⊥ < Q → Q < IsLocalRing.maximalIdeal A → Q.height = 1

def DimTwoSumReading.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    ringKrullDim A = 2 → ∀ a b : A, a ≠ 0 →
    (∀ p : Ideal A, p.IsPrime → p.height = 1 → a ∈ p → b ∉ p) →
    ∃ n : ℕ, ∑ᶠ W : Ideal A, locCycle (Ideal.span {a}) W *
        locCycle (W ⊔ Ideal.span {b}) (IsLocalRing.maximalIdeal A) = n ∧
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b = n

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Ring

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]

def projCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) :
    (Σ o, bundleIdx ι M o) → B
  | ⟨none, l⟩ => ∑ i, u i * algebraMap Ω B (φ l (w i))
  | ⟨some k, i⟩ => algebraMap Ω B (y ⟨k, i⟩)

theorem projCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx ι M o) :
    g (projCoordRing y w φ u p) = projCoordRing y w φ (g ∘ u) p := by
  rcases p with ⟨_ | k, l⟩ <;> simp [projCoordRing, map_sum]

theorem projCoord_eq_projCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    projCoord y w φ t = projCoordRing y w φ t := by
  funext p
  rcases p with ⟨_ | k, l⟩ <;> rfl

end Ring

theorem map_coneMap {σ τ R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] (f : R →+* B)
    (g : B →+* B') (c : σ → B) (q : σ → τ) (x : MvPolynomial σ R) :
    map g (eval₂ (C.comp f) (fun p => C (c p) * X (q p)) x) =
      eval₂ (C.comp (g.comp f)) (fun p => C (g (c p)) * X (q p)) x := by
  rw [eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext p
    simp

theorem TruncSpecialize.proof : TruncSpecialize.Statement := by
  intro F _ Ω _ _ K ι y N E _ _ w M φ Φ _ _ t ht i
  let ev : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ := aeval t
  have hev : Function.Injective ev := ht
  let sub : MvPolynomial (Fin N) Ω →ₐ[Ω] MvPolynomial (Fin N) Ω := aeval fun k => if k = i then 0 else X k
  have hevT : ∀ j : ℕ, ev ∘ truncCoord (X : Fin N → MvPolynomial (Fin N) Ω) j = truncCoord t j := by
    intro j
    funext k
    by_cases hk : (k : ℕ) < j <;> simp [truncCoord, hk, ev]
  have hsubT : sub ∘ truncCoord (X : Fin N → MvPolynomial (Fin N) Ω) ((i : ℕ) + 1) = truncCoord X i := by
    funext k
    simp only [Function.comp_apply, truncCoord]
    rcases lt_trichotomy (k : ℕ) i with h | h | h
    · have hki : k ≠ i := fun e => by subst e; exact lt_irrefl _ h
      simp [h, Nat.lt_succ_of_lt h, sub, hki]
    · have hki : k = i := Fin.ext h
      subst hki
      simp [sub]
    · have h1 : ¬ (k : ℕ) < i + 1 := by omega
      have h2 : ¬ (k : ℕ) < i := by omega
      simp [h1, h2]
  let cA : ℕ → (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω :=
    fun j => projCoordRing y w φ (truncCoord X j)
  have hcoord : ∀ j : ℕ, projCoord y w φ (truncCoord t j) = fun p => ev (cA j p) := by
    intro j
    funext p
    rw [projCoord_eq_projCoordRing, ← hevT, projCoordRing_map]
  have hsubc : ∀ p, sub (cA ((i : ℕ) + 1) p) = cA i p := by
    intro p
    simp only [cA]
    rw [projCoordRing_map, hsubT]
  let algA : F →+* MvPolynomial (Fin N) Ω := (algebraMap Ω (MvPolynomial (Fin N) Ω)).comp (algebraMap F Ω)
  have hevA : (ev : MvPolynomial (Fin N) Ω →+* Φ).comp algA = (algebraMap Ω Φ).comp (algebraMap F Ω) :=
    RingHom.ext fun a => by simp [algA]
  have hsubA : (sub : MvPolynomial (Fin N) Ω →+* MvPolynomial (Fin N) Ω).comp algA = algA :=
    RingHom.ext fun a => by simp [algA]
  refine ⟨fun x hx => ?_, fun x z hxz => ?_⟩
  · have key : ∀ j : ℕ, eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
        (fun p => C (projCoord y w φ (truncCoord t j) p) * X p.1) x =
        map (ev : MvPolynomial (Fin N) Ω →+* Φ) (eval₂ (C.comp algA) (fun p => C (cA j p) * X p.1) x) := by
      intro j
      rw [map_coneMap, hevA, hcoord]
      rfl
    have ksub : map (sub : MvPolynomial (Fin N) Ω →+* MvPolynomial (Fin N) Ω)
        (eval₂ (C.comp algA) (fun p => C (cA ((i : ℕ) + 1) p) * X p.1) x) =
        eval₂ (C.comp algA) (fun p => C (cA i p) * X p.1) x := by
      rw [map_coneMap, hsubA]
      simp only [AlgHom.coe_toRingHom, hsubc]
    simp only [projIdeal, RingHom.mem_ker] at hx ⊢
    rw [key] at hx ⊢
    have h0 : eval₂ (C.comp algA) (fun p => C (cA ((i : ℕ) + 1) p) * X p.1) x = 0 :=
      map_injective _ hev (hx.trans (map_zero _).symm)
    rw [← ksub, h0, map_zero, map_zero]
  · have val : ∀ (j : ℕ) (v : MRing (bundleIdx ι M) F),
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t j)) v =
          ev (eval₂ algA (cA j) v) := by
      intro j v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hevA, hcoord]
      rfl
    have vsub : ∀ v : MRing (bundleIdx ι M) F,
        sub (eval₂ algA (cA ((i : ℕ) + 1)) v) = eval₂ algA (cA i) v := by
      intro v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hsubA]
      congr 1
      funext p
      exact hsubc p
    rw [val, val] at hxz
    have hx' : eval₂ algA (cA ((i : ℕ) + 1)) x = X i * eval₂ algA (cA ((i : ℕ) + 1)) z :=
      hev (by rw [hxz, map_mul]; simp [ev])
    rw [val, ← vsub, hx', map_mul]
    simp [sub]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenericProjClosureDim

variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}

def tWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι R) :
    weightedHomogeneousComponent (tWeight K) b (pointConeMap R z f) =
      pointConeMap R z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 : IsWeightedHomogeneous (tWeight K) (pointConeMap R z (monomial d a))
        (Finsupp.weight (blockWeight ι) d) := by
      rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
        Finsupp.sum]
      refine IsWeightedHomogeneous.C_mul ?_ _
      refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
      exact ((isWeightedHomogeneous_X (R := L) (tWeight K) p.1).C_mul (z p)).pow (d p)
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι R)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem isMultiProjPrime_pointIdeal (z : (Σ k, ι k) → L) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    IsMultiProjPrime (pointIdeal R z) := by
  refine ⟨RingHom.ker_isPrime _, ?_, ?_⟩
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (R := R) z b f
    rw [hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap R z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

theorem exists_ne_zero_of_span {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (hN : 0 < N) (e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) :
    ∃ l, ∑ i, t i * algebraMap Ω Φ (ψ l (e i)) ≠ 0 := by
  by_contra! h0
  have hall : ∀ l, ψ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have := Fintype.linearIndependent_iff.1 ht (fun i => ψ l (e i))
      (by rw [← h0 l]; exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm])
    simpa using this i
  have htop : (⊤ : Submodule Ω (Module.Dual Ω E)) = ⊥ := by
    rw [← hψ, Submodule.span_eq_bot]
    rintro _ ⟨l, rfl⟩
    exact hall l
  have hc : e.coord ⟨0, hN⟩ = 0 := by
    have : e.coord ⟨0, hN⟩ ∈ (⊥ : Submodule Ω (Module.Dual Ω E)) := htop ▸ Submodule.mem_top
    simpa using this
  have := congrArg (fun f => f (e ⟨0, hN⟩)) hc
  simp at this

end GenericProjClosureDim


open GenericProjClosureDim in
theorem GenericProjClosureDim.proof (hDim : DvrConeDimTrdeg.Statement) (hTr : PairBundleTrdeg.Statement) :
    GenericProjClosureDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, pairProjCoord y e φ φ' t ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k)
    · exact exists_ne_zero_of_span hN e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)
    · exact exists_ne_zero_of_span hN e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc)
    · exact ⟨c k, fun h0 => hc k ((FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (pairProjCoord y e φ φ' t)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  refine ⟨hP, hnt, ?_⟩

  have hdy := hDim O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  rw [hDim _ _ _ _ hP hnt, hTr O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht, hty,
    ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
    show d + (N - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (N + 1) + 1 by omega]
  norm_cast

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SegreFlagDegreeZero.Statement : Prop :=
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
    ∀ k : ℕ, k < N →
      ∃ f₃ g₃ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ (zetaFirst a₀ - zetaSecond a₀') f₃ g₃ ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) f₃ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₃ ∧
        (0 < k → f₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧ g₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          aeval (flagClosurePt y w e φ φ' t k) f₃ = aeval (flagClosurePt y w e φ φ' t k) g₃)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
