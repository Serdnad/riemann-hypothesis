module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open FlagBundleSectionDivProof GenericProjClosureDivisor in
theorem SegreFlagCutDivisor.proof (hSpec : SegreFlagCutSpecialize.Statement)
    (hChart : SegreFlagCutChart.Statement) : SegreFlagCutDivisor.Statement := by
  have hModel : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSat : MultAtOfSaturated.Statement.{0} := MultAtOfSaturated.proof
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk cs ch s h hs hh hdeg hsP hhP hval W hW
  classical
  have hPp : (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))).IsPrime := RingHom.ker_isPrime _
  have hQp : (pointIdeal O (flagClosurePt y w e φ φ' t k)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨hPQ, hspec⟩ := hSpec O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  have hτ : flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ ≠ 0 := by
    intro h0
    exact hsP (mem_of_homog hs (by rw [hval, h0, zero_mul]))
  by_cases hWc : W.IsPrime ∧ IsRelevant W ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hWc
    obtain ⟨cl, cm, l, μ, u, hl, hμ, hdl, hμW, huW, hlv, hl0, hsat⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk W
        hWp hWrel hPW hW
    have hμP : μ ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := fun h' => hμW (hPW h')
    have hlP : l ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      intro h'
      have h0 := aeval_eq_zero_of_mem h'
      rw [hlv] at h0
      exact hμP (mem_of_homog hμ ((mul_eq_zero.mp h0).resolve_left hτ))
    have huW' : ∀ n : ℕ, u ^ n ∉ W := fun n h' => huW (hWp.mem_of_pow_mem n h')
    have hdeg' : cs + cm = cl + ch := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : s * μ - l * h ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      have h2 := hl.mul hh
      rw [← hdeg'] at h2
      refine mem_of_homog (b := cs + cm) ((mem_weightedHomogeneousSubmodule _ _ _ _).mp
        (Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))) ?_
      rw [map_sub, map_mul, map_mul, hval, hlv]
      ring
    rw [ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff]
    unfold ratDiv
    rw [divCycle_eq_zero_of_not_mem hμW, sub_zero]
    have hlQ : 0 < k → l ∈ pointIdeal O (flagClosurePt y w e φ φ' t k) := fun _ =>
      mem_of_homog hl (hspec l μ hlv)
    split_ifs with hc
    · obtain ⟨hkpos, rfl⟩ := hc
      obtain ⟨hmin, hmult⟩ := hSat O (Option (Option K)) (bundleIdx (bundleIdx ι M) M') _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr (hlQ hkpos)))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact ⟨_, huW' n, hn⟩)
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hWrel⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h'
        · exact h'.1
        · exact absurd rfl hne
      have hlW : l ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self l))
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exact hl0 hk0 hlW
      · have hQW : pointIdeal O (flagClosurePt y w e φ φ' t k) ≤ W := fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW' n)
        have hPQ' : pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) <
            pointIdeal O (flagClosurePt y w e φ φ' t k) :=
          lt_of_le_of_ne hPQ (fun h' => hlP (by rw [h']; exact hlQ hkpos))
        exact hc ⟨hkpos, (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm⟩
  · have h0 : ∀ z, divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) z W = 0 := fun z => by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h', hr⟩
      exact hWc ⟨h'.1.1, hr, le_sup_left.trans h'.1.2⟩
    have hWQ : ¬ (0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k)) := by
      rintro ⟨hkpos, rfl⟩
      exact hWc ⟨hQp, (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
        Φ e t ht k hkpos hk.le).1.multiProj.relevant, hPQ⟩
    rw [ite_eq_right hWQ]
    simp [ratDiv, h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Ring

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]

def flagCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (w e : Module.Basis (Fin N) Ω E) (u : Fin N → B)
    (k : ℕ) : Fin N → B :=
  fun j => if (j : ℕ) < k then ∑ i, u i * algebraMap Ω B (w.repr (e i) j) else 0

def pairCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (u : Fin N → B) : (Σ o, bundleIdx (bundleIdx ι M) M' o) → B
  | ⟨none, l⟩ => ∑ i, u i * algebraMap Ω B (φ' l (w i))
  | ⟨some o, j⟩ => projCoordRing y w φ u ⟨o, j⟩

theorem flagCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (w e : Module.Basis (Fin N) Ω E) (u : Fin N → B) (k : ℕ) :
    g ∘ flagCoordRing w e u k = flagCoordRing w e (g ∘ u) k := by
  funext j
  by_cases hj : (j : ℕ) < k <;> simp [flagCoordRing, hj, map_sum]

theorem pairCoordRing_map {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx (bundleIdx ι M) M' o) :
    g (pairCoordRing y w φ φ' u p) = pairCoordRing y w φ φ' (g ∘ u) p := by
  rcases p with ⟨_ | o, l⟩

  · simp [pairCoordRing, map_sum]
  · simp only [pairCoordRing]
    exact projCoordRing_map g y w φ u _

theorem flagCoord_eq_flagCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (w e : Module.Basis (Fin N) Ω E)
    (t : Fin N → Φ) (k : ℕ) : flagCoord w e t k = flagCoordRing w e t k := rfl

theorem pairProjCoord_eq_pairCoordRing {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (t : Fin N → Φ) : pairProjCoord y w φ φ' t = pairCoordRing y w φ φ' t := by
  funext p
  rcases p with ⟨_ | o, l⟩
  · rfl
  · simp only [pairProjCoord, pairCoordRing]
    rw [projCoord_eq_projCoordRing]

theorem aeval_flagSub_sigma (w e : Module.Basis (Fin N) Ω E) (k j : Fin N) :
    aeval (fun i => X i - (∑ m, X m * C (w.repr (e m) k)) * C (e.repr (w k) i))
        (∑ i, X i * C (w.repr (e i) j) : MvPolynomial (Fin N) Ω) =
      (∑ i, X i * C (w.repr (e i) j)) - if k = j then ∑ i, X i * C (w.repr (e i) k) else 0 := by
  set S : MvPolynomial (Fin N) Ω := ∑ m, X m * C (w.repr (e m) k) with hS
  have hsum : ∑ i, e.repr (w k) i * w.repr (e i) j = if k = j then 1 else 0 := by
    have h := congrArg (fun v => w.repr v j) (e.sum_repr (w k))

    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] at h
    rw [h]
  have hx : ∀ x, aeval (fun i => X i - S * C (e.repr (w k) i)) (X x * C (w.repr (e x) j)) =
      X x * C (w.repr (e x) j) - S * C (e.repr (w k) x * w.repr (e x) j) := by
    intro x
    rw [map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq, sub_mul, map_mul, mul_assoc]

  rw [map_sum, Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum, hsum]
  split_ifs with h
  · subst h; rw [map_one, mul_one]
  · rw [map_zero, mul_zero]

end Ring

theorem SegreFlagCutSpecialize.proof : SegreFlagCutSpecialize.Statement := by
  intro O _ _ _ ϖ _ Ω _ _ K _ _ ι _ y d _ N E _ _ B B' _ w w' x x' f g hF M M' a₀ a₀' φ φ' _ _ Φ _ _ _ _ e t ht
    k hk
  classical
  let ev : (MvPolynomial (Fin N) Ω) →ₐ[Ω] Φ := aeval t
  have hev : Function.Injective ev := ht
  let kk : Fin N := ⟨k, hk⟩
  let sub : (MvPolynomial (Fin N) Ω) →ₐ[Ω] (MvPolynomial (Fin N) Ω) := aeval fun i => X i - (∑ m, X m * C (w.repr (e m) kk)) * C (e.repr (w kk) i)
  have hevF : ∀ j : ℕ, ev ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) j = flagCoordRing w e t j := by
    intro j
    rw [flagCoordRing_map]
    congr 1
    funext i
    simp [ev, aeval_X]
  have hsubF : sub ∘ flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) = flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) k := by
    funext j
    have hs := aeval_flagSub_sigma w e kk j
    simp only [Function.comp_apply, flagCoordRing]
    rcases lt_trichotomy (j : ℕ) k with h | h | h
    · have hkj : kk ≠ j := fun h' => by rw [← h'] at h; exact lt_irrefl _ h
      rw [if_pos (by omega), if_pos h]
      simp only [MvPolynomial.algebraMap_eq]
      refine hs.trans ?_
      rw [if_neg hkj, sub_zero]
    · have hkj : kk = j := Fin.ext h.symm
      rw [if_pos (by omega), if_neg (by omega)]
      simp only [MvPolynomial.algebraMap_eq]
      refine hs.trans ?_
      rw [if_pos hkj, hkj, sub_self]
    · rw [if_neg (by omega), if_neg (by omega), map_zero]
  let cA : ℕ → (Σ o, bundleIdx (bundleIdx ι M) M' o) → (MvPolynomial (Fin N) Ω) :=
    fun j => pairCoordRing y w φ φ' (flagCoordRing w e X j)
  have hcoord : ∀ j : ℕ, flagClosurePt y w e φ φ' t j = fun p => ev (cA j p) := by
    intro j
    funext p
    simp only [cA, flagClosurePt, pairProjCoord_eq_pairCoordRing, flagCoord_eq_flagCoordRing, pairCoordRing_map,
      hevF]
  have hsubc : ∀ p, sub (cA (k + 1) p) = cA k p := by
    intro p
    simp only [cA]
    rw [pairCoordRing_map, hsubF]
  let algA : O →+* (MvPolynomial (Fin N) Ω) := (algebraMap Ω (MvPolynomial (Fin N) Ω)).comp (algebraMap O Ω)
  have hevA : (ev : (MvPolynomial (Fin N) Ω) →+* Φ).comp algA = algebraMap O Φ :=
    RingHom.ext fun a => by simp [algA, ← IsScalarTower.algebraMap_apply]
  have hsubA : (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)).comp algA = algA := RingHom.ext fun a => by simp [algA]
  refine ⟨fun s hs => ?_, fun s h hsh => ?_⟩
  · have key : ∀ j : ℕ, pointConeMap O (flagClosurePt y w e φ φ' t j) s =
        map (ev : (MvPolynomial (Fin N) Ω) →+* Φ) (eval₂ (C.comp algA) (fun p => C (cA j p) * X p.1) s) := by
      intro j
      rw [map_coneMap, hevA, hcoord]
      simp only [pointConeMap, aeval_def, MvPolynomial.algebraMap_eq]
      rfl
    have ksub : map (sub : (MvPolynomial (Fin N) Ω) →+* (MvPolynomial (Fin N) Ω)) (eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s) =
        eval₂ (C.comp algA) (fun p => C (cA k p) * X p.1) s := by
      rw [map_coneMap, hsubA]
      simp only [AlgHom.coe_toRingHom, hsubc]
    simp only [pointIdeal, RingHom.mem_ker] at hs ⊢
    rw [key] at hs ⊢
    have h0 : eval₂ (C.comp algA) (fun p => C (cA (k + 1) p) * X p.1) s = 0 :=
      map_injective _ hev (hs.trans (map_zero _).symm)
    rw [← ksub, h0, map_zero, map_zero]
  · have val : ∀ (j : ℕ) (v : MRing (bundleIdx (bundleIdx ι M) M') O),
        aeval (flagClosurePt y w e φ φ' t j) v = ev (eval₂ algA (cA j) v) := by
      intro j v
      rw [aeval_def, ← AlgHom.coe_toRingHom, eval₂_comp_left, hevA, hcoord]
      rfl
    have vsub : ∀ v : MRing (bundleIdx (bundleIdx ι M) M') O,
        sub (eval₂ algA (cA (k + 1)) v) = eval₂ algA (cA k) v := by
      intro v
      rw [← AlgHom.coe_toRingHom, eval₂_comp_left, hsubA]
      congr 1
      funext p
      exact hsubc p
    let τA : (MvPolynomial (Fin N) Ω) := ∑ j, flagCoordRing w e (X : Fin N → (MvPolynomial (Fin N) Ω)) (k + 1) j * algebraMap Ω (MvPolynomial (Fin N) Ω) (w'.repr (w j) kk)
    have hτ : flagLineCoord w' w e t (k + 1) kk = ev τA := by

      simp only [τA, flagLineCoord, map_sum, map_mul, AlgHom.commutes, flagCoord_eq_flagCoordRing, ← hevF,
      Function.comp_apply]
    have hsubτ : sub τA = 0 := by

      simp only [τA, map_sum, map_mul, AlgHom.commutes]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj := congrFun hsubF j
      simp only [Function.comp_apply] at hj
      rw [hj]
      by_cases hjk : (j : ℕ) < k
      · rw [repr_flag_inv w w' hF.sameFlag j kk (Fin.lt_def.mpr hjk), map_zero, mul_zero]
      · simp [flagCoordRing, hjk]
    rw [val, val, hτ] at hsh
    have hs' : eval₂ algA (cA (k + 1)) s = τA * eval₂ algA (cA (k + 1)) h :=
      hev (by rw [hsh, map_mul])
    rw [val, ← vsub, hs', map_mul, hsubτ, zero_mul, map_zero]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutLiesOverProof

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ικ : κ → Type} [∀ o, Fintype (ικ o)] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem le_comap_of_chart (pt : (Σ o, ικ o) → Φ) {A F : Type*} [CommRing A] [FunLike F A (MRing ικ O)]
    [RingHomClass F A (MRing ικ O)] (ρ : F) (Q : Ideal A) (u : MRing ικ O) (τ : Φ) {cs ch dl dm : κ → ℕ}
    {s h l μ : MRing ικ O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hl : IsMultiHomog l dl)
    (hμ : IsMultiHomog μ dm) (hdeg : cs + dm = dl + ch) (hsP : s ∉ pointIdeal O pt)
    (hhP : h ∉ pointIdeal O pt) (hsv : aeval pt s = τ * aeval pt h) (hlv : aeval pt l = τ * aeval pt μ)
    (hsat : ∀ q ∈ Q, ∃ n : ℕ, u ^ n * ρ q ∈ pointIdeal O pt ⊔ Ideal.span {l})
    {W : Ideal (MRing ικ O)} (hμW : μ ∉ W) (huW : ∀ n : ℕ, u ^ n ∉ W)
    (hPW : pointIdeal O pt ≤ W) (hW : ratDiv (pointIdeal O pt) s h W ≠ 0) : Q ≤ W.comap ρ := by
  have : (pointIdeal O pt).IsPrime := RingHom.ker_isPrime _
  have hμP : μ ∉ pointIdeal O pt := fun h' => hμW (hPW h')
  have hsv0 : aeval pt s ≠ 0 := fun h0 => hsP (GenericProjClosureDivisor.mem_of_homog hs h0)
  have hτ : τ ≠ 0 := by
    rintro rfl
    exact hsv0 (by rw [hsv, zero_mul])
  have hμv : aeval pt μ ≠ 0 := fun h0 => hμP (GenericProjClosureDivisor.mem_of_homog hμ h0)
  have hlP : l ∉ pointIdeal O pt := fun h' =>
    mul_ne_zero hτ hμv (hlv ▸ GenericProjClosureDivisor.aeval_eq_zero_of_mem h')
  have hdiff : s * μ - l * h ∈ pointIdeal O pt := by
    have h2 := hl.mul hh
    rw [← hdeg] at h2
    have h1 : IsMultiHomog (s * μ - l * h) (cs + dm) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
    refine GenericProjClosureDivisor.mem_of_homog h1 ?_
    rw [map_sub, map_mul, map_mul, hsv, hlv]
    ring
  have hrat := congrFun (ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff) W
  have hμ0 : divCycle (pointIdeal O pt) μ W = 0 := by
    unfold divCycle
    rw [dite_eq_right]
    rintro ⟨h', -⟩
    exact hμW (h'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self μ)))
  have hl0 : divCycle (pointIdeal O pt) l W ≠ 0 := by
    rw [hrat] at hW
    unfold ratDiv at hW
    rwa [hμ0, sub_zero] at hW
  have hmin : W ∈ (pointIdeal O pt ⊔ Ideal.span {l}).minimalPrimes := by
    unfold divCycle at hl0
    split_ifs at hl0 with h'
    · exact h'.1
    · exact absurd rfl hl0
  have hWp : W.IsPrime := hmin.1.1
  intro q hq
  obtain ⟨n, hn⟩ := hsat q hq
  exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW n)


omit [Fintype κ] [DecidableEq κ] [∀ o, Fintype (ικ o)] [IsDomain O] [IsDiscreteValuationRing O] in
theorem support_ratDiv {P W : Ideal (MRing ικ O)} {s h : MRing ικ O} (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  have key : ∀ v, divCycle P v W ≠ 0 → W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
    intro v hv
    unfold divCycle at hv
    split_ifs at hv with h'
    · exact ⟨h'.1.1.1, le_sup_left.trans h'.1.1.2, h'.2⟩
    · exact absurd rfl hv
  by_cases h1 : divCycle P s W = 0
  · exact key h fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key s h1

end SegreFlagCutLiesOverProof


open SegreFlagCutLiesOverProof in
theorem SegreFlagCutLiesOver.proof (hChart : SegreFlagCutChartSection.Statement) :
    SegreFlagCutLiesOver.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hchart : ∀ (s h : MRing (bundleIdx (bundleIdx ι M) M') O) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
      ∃ c : ∀ j, ι j, segreVec y c ≠ 0 ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W ∧
        ∀ m : K → ℕ, (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j) ∉ W := by
    intro s h W hW
    obtain ⟨hWp, hPW, hWr⟩ := support_ratDiv hW
    choose c hc using fun j : K => hWr (some (some j))
    refine ⟨c, ?_, hPW, ?_⟩
    · unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro j _ hj
      apply hc j (hPW ?_)
      refine GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      simp [flagClosurePt, pairProjCoord, projCoord, hj]
    · intro m hm
      obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp hm
      exact hc j (hWp.mem_of_pow_mem _ hj)
  have hdeg : ∀ {cs ch dl dm : Option (Option K) → ℕ} {D : Option (Option K) → ℤ},
      (fun o => (cs o : ℤ) - ch o) = D → (fun o => (dl o : ℤ) - dm o) = D → cs + dm = dl + ch := by
    intro cs ch dl dm D h1 h2
    funext o
    have e1 := congrFun h1 o
    have e2 := congrFun h2 o
    simp only [Pi.add_apply] at e1 e2 ⊢
    omega
  refine ⟨fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_, fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_⟩
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩, -⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨-, ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
