module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle016
public import Mathlib.Algebra.Module.Submodule.Union
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceMultGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, localMult (J ⊔ Ideal.span {linForm u}) W =
            localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceReducedGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, IsRadicalAt (sliceIdeal J L q) q

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceUnmixedGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ)
              (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
            P ≤ RingHom.ker (eval q) →
              P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GenericNoetherNormalisation

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)



end Nagata

section Combination

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}

variable {c : A} {z : Fin m → D} {s : Finset D}

end Combination

universe u

theorem proof : GenericNoetherNormalisation.Statement.{u} :=
  _root_.UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof

end GenericNoetherNormalisation

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem GenericFibreRadicalAway.proof (hR : GenericFibreRadical.Statement) :
    GenericFibreRadicalAway.Statement := by
  intro σ _ n K g hK
  obtain ⟨F, hF0, hF⟩ := hR σ (Option (Fin n)) (rabinowitschIdeal K g)
    ((isRadicalAway_iff_isRadical_rabinowitschIdeal K g).1 hK)
  refine ⟨F, hF0, fun t ht => ?_⟩
  have h := hF t ht
  rw [rabinowitschIdeal_map] at h
  exact (isRadicalAway_iff_isRadical_rabinowitschIdeal (fibreIdeal K t) _).2 h

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionBranchLocus.proof (hL : ProperOpenProjectionLocalCover.Statement)
    (hH : FibreDiscriminantHolomorphic.Statement) (hM : MaximalCountUnbranched.Statement) :
    ProperOpenProjectionBranchLocus.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hDc hDne hmaps hprop hopen
  have loc := hL σ X B k f d A D hB hf hXB hDo hmaps hprop hopen
  choose! U g n hUo hyU hUD hg hgd hle hgen using loc

  have key : ∀ y₀ ∈ D, ∀ y ∈ U y₀, n y = n y₀ := by
    intro y₀ hy₀ y hy
    have hyD : y ∈ D := hUD y₀ hy₀ hy
    obtain ⟨t₁, ht₁, hgt₁⟩ := hgd y₀ hy₀ (U y ∩ U y₀) ((hUo y hyD).inter (hUo y₀ hy₀))
      Set.inter_subset_right ⟨y, hyU y hyD, hy⟩
    have hWo : IsOpen (U y ∩ (U y₀ ∩ g y₀ ⁻¹' {0}ᶜ)) :=
      (hUo y hyD).inter ((hg y₀ hy₀).continuousOn.isOpen_inter_preimage (hUo y₀ hy₀) isOpen_compl_singleton)
    obtain ⟨t, ht, hgt⟩ := hgd y hyD _ hWo Set.inter_subset_left
      ⟨t₁, ht₁.1, ht₁.2, by simpa using hgt₁⟩
    have e1 := (hgen y hyD t ht.1 hgt).1
    have e2 := (hgen y₀ hy₀ t ht.2.1 (by simpa using ht.2.2)).1
    exact_mod_cast e1.symm.trans e2
  obtain ⟨y₀, hy₀⟩ := hDne
  have hcont : ContinuousOn n D := by
    intro y hy
    have hc0 : ContinuousAt (fun _ : Fin d → ℂ => n y) y := continuousAt_const
    have hca : ContinuousAt n y := by
      refine hc0.congr ?_
      filter_upwards [(hUo y hy).mem_nhds (hyU y hy)] with z hz
      exact (key y hy z hz).symm
    exact hca.continuousWithinAt
  have hN : ∀ y ∈ D, n y = n y₀ := fun y hy => hDc.constant hcont hy hy₀

  have hcov : IsGenericCountCover (X ∩ B) A D (n y₀) := by
    refine ⟨fun y hy => ?_, fun y hy => ⟨U y, g y, hUo y hy, hyU y hy, hUD y hy, hg y hy, hgd y hy,
      fun z hz hgz => ?_⟩⟩
    · have := hle y hy y (hyU y hy)
      rwa [hN y hy] at this
    · obtain ⟨h1, h2⟩ := hgen y hy z hz hgz
      exact ⟨by rw [h1, hN y hy], h2⟩

  obtain ⟨ys, hysU, hgys⟩ := hgd y₀ hy₀ (U y₀) (hUo y₀ hy₀) subset_rfl ⟨y₀, hyU y₀ hy₀⟩
  have hysD : ys ∈ D := hUD y₀ hy₀ hysU
  have hcys : {x | x ∈ X ∩ B ∧ A x = ys}.encard = (n y₀ : ℕ∞) := (hgen y₀ hy₀ ys hysU hgys).1
  have hfin := Set.finite_of_encard_eq_coe hcys
  obtain ⟨l₀, hl₀⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun p : hfin.toFinset.offDiag => (p.1.1 - p.1.2 : σ → ℂ))
    (fun p => sub_ne_zero.2 (Finset.mem_offDiag.1 p.2).2.2)
  let l : (σ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap l₀
  refine ⟨fibreDiscr (X ∩ B) A l (n y₀), hH σ (X ∩ B) d A D (n y₀) l hDo hmaps hprop hopen hcov,
    ⟨ys, hysD, ?_⟩, ?_⟩
  · unfold fibreDiscr
    rw [dite_eq_left hcys, Finset.prod_ne_zero_iff]
    intro p hp
    have := hl₀ ⟨p, hp⟩
    simpa [l, map_sub, sub_eq_zero] using this
  · intro x hx hδ
    have hc : {x' | x' ∈ X ∩ B ∧ A x' = A x}.encard = (n y₀ : ℕ∞) := by
      by_contra hne
      exact hδ (by unfold fibreDiscr; rw [dite_eq_right hne])
    exact hM σ (X ∩ B) d A D (n y₀) hDo hmaps hprop hopen hcov x hx hc

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

private theorem germ_zero_of_mul_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

private theorem germ_factor_zero_of_prod_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_zero_of_mul_zero (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

private theorem isOpen_diff_of_zeroSet {σ : Type} [Fintype σ] {Y N : Set (σ → ℂ)} {k : ℕ}
    {φ : Fin k → (σ → ℂ) → ℂ} (hN : IsOpen N) (hφ : ∀ m, AnalyticOnNhd ℂ (φ m) N)
    (hY : Y ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0}) : IsOpen (N \ Y) := by
  have hEq : N \ Y = ⋃ m, N ∩ φ m ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hzN, hzY⟩
      by_contra hcon
      push Not at hcon
      have hz : z ∈ Y ∩ N := by
        rw [hY]
        exact ⟨hzN, fun m => hcon m hzN⟩
      exact hzY hz.1
    · rintro ⟨m, hzN, hzm⟩
      refine ⟨hzN, fun hzY => hzm ?_⟩
      have hz : z ∈ Y ∩ N := ⟨hzY, hzN⟩
      rw [hY] at hz
      exact hz.2 m
  rw [hEq]
  exact isOpen_iUnion fun m => (hφ m).continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton

theorem IsolatedFibreLocalUnbranched.proof (hcomp : OpenProjectionDominantComponents.Statement)
    (hmeet : IrreducibleGermMeetOverHypersurface.Statement)
    (hprim : IrreducibleGermPrimitiveForm.Statement)
    (hsheet : PrimitiveFormSheetedOffDiscriminant.Statement) :
    IsolatedFibreLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A hB hf hXB hopen w hw hiso
  obtain ⟨n, Y, hY, hsepY, W0, hW0, hXW0⟩ := hcomp σ X B k f d A hB hf hXB hopen w hw
  obtain ⟨W, hW, hWiso⟩ := hiso

  have hisoY : ∀ i, ∃ W' ∈ 𝓝 w, ∀ x ∈ Y i ∩ W', A x = A w → x = w := fun i =>
    ⟨W ∩ W0, inter_mem hW hW0, fun x hx hAx => by
      have hxX : x ∈ X ∩ B ∩ W0 := by
        rw [hXW0]
        exact ⟨Set.mem_iUnion.2 ⟨i, hx.1⟩, hx.2.2⟩
      exact hWiso x ⟨hxX.1, hx.2.1⟩ hAx⟩

  have hsh : ∀ i, ∃ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) ∧
      ∃ M ∈ 𝓝 w, ∀ y ∈ Y i ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ Y i ∩ V = g '' O := by
    intro i
    obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hP, hsep, hQ⟩ :=
      hprim σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2
    exact ⟨δ, hδ, hδ0,
      hsheet σ (Y i) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY i).2.2 ℓ N a δ q ha hδ hq hδ0 hP hsep hQ⟩
  choose δ hδa hδ0 M hM hMsh using hsh

  have hsp : ∀ i j, ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
      (i ≠ j → ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j → e (A z) = 0) := by
    intro i j
    by_cases hij : i = j
    · refine ⟨fun _ => 1, analyticAt_const, fun h => ?_, fun h => absurd hij h⟩
      obtain ⟨y, hy⟩ := h.exists
      exact one_ne_zero hy
    · obtain ⟨e, he, he0, hez⟩ :=
        hmeet σ (Y i) (Y j) w d A (hY i).1 (hY i).2.1 (hisoY i) (hY j).1 (hsepY i j hij)
      exact ⟨e, he, he0, fun _ => hez⟩
  choose e hea he0 hez using hsp

  have hYa : ∀ j, ∃ (N : Set (σ → ℂ)) (kk : ℕ) (φ : Fin kk → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
      (∀ m, AnalyticOnNhd ℂ (φ m) N) ∧ Y j ∩ N = {z | z ∈ N ∧ ∀ m, φ m z = 0} := fun j => (hY j).1
  choose N kk φ hNo hwN hφ hYN using hYa
  have hfac : ∀ i, AnalyticAt ℂ (fun y => δ i y * ∏ j, e i j y) (A w) := fun i =>
    (hδa i).mul (Finset.analyticAt_fun_prod _ fun j _ => hea i j)
  refine ⟨interior W0 ∩ (⋂ i, M i) ∩ (⋂ j, N j) ∩
      {z | ∀ i j, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0},
    fun y => ∏ i, (δ i y * ∏ j, e i j y), ?_, Finset.analyticAt_fun_prod _ fun i _ => hfac i, ?_, ?_⟩
  · refine inter_mem (inter_mem (inter_mem (interior_mem_nhds.2 hW0) (iInter_mem.2 hM))
      (iInter_mem.2 fun j => (hNo j).mem_nhds (hwN j))) ?_
    have hev : ∀ i j, ∀ᶠ z in 𝓝 w, i ≠ j → z ∈ Y i → z ∈ Y j → e i j (A z) = 0 := fun i j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · filter_upwards [hez i j hij] with z hz _ using hz
    exact eventually_all.2 fun i => eventually_all.2 fun j => hev i j
  · intro hg0
    obtain ⟨i, -, hi⟩ := germ_factor_zero_of_prod_zero (fun i y => δ i y * ∏ j, e i j y) Finset.univ
      (fun i _ => hfac i) hg0
    rcases germ_zero_of_mul_zero (hδa i) (Finset.analyticAt_fun_prod _ fun j _ => hea i j) hi with h1 | h1
    · exact hδ0 i h1
    · obtain ⟨j, -, hj⟩ := germ_factor_zero_of_prod_zero (e i) Finset.univ (fun j _ => hea i j) h1
      exact he0 i j hj
  · intro x hx hgx
    obtain ⟨hxXB, ⟨⟨hxW0, hxM⟩, hxN⟩, hxe⟩ := hx
    simp only [Set.mem_iInter] at hxM hxN
    have hgx' : ∀ i, δ i (A x) ≠ 0 ∧ ∀ j, e i j (A x) ≠ 0 := by
      intro i
      have hi := (Finset.prod_ne_zero_iff.1 hgx) i (Finset.mem_univ i)
      exact ⟨left_ne_zero_of_mul hi,
        fun j => (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hi)) j (Finset.mem_univ j)⟩
    have hxU : x ∈ (⋃ i, Y i) ∩ W0 := by
      rw [← hXW0]
      exact ⟨hxXB, interior_subset hxW0⟩
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxU.1
    have hxnot : ∀ j, j ≠ i → x ∉ Y j := fun j hji hxj =>
      (hgx' i).2 j (hxe i j (Ne.symm hji) hxi hxj)

    let U : Set (σ → ℂ) := interior W0 ∩ ⋂ j, (if j = i then Set.univ else N j \ Y j)
    have hUo : IsOpen U := by
      refine isOpen_interior.inter (isOpen_iInter_of_finite fun j => ?_)
      split_ifs
      · exact isOpen_univ
      · exact isOpen_diff_of_zeroSet (hNo j) (hφ j) (hYN j)
    have hxUm : x ∈ U := by
      refine ⟨hxW0, Set.mem_iInter.2 fun j => ?_⟩
      split_ifs with hji
      · trivial
      · exact ⟨hxN j, hxnot j hji⟩
    have hXU : X ∩ B ∩ U = Y i ∩ U := by
      ext z
      constructor
      · rintro ⟨hzXB, hzU⟩
        have hzW : z ∈ (⋃ i, Y i) ∩ W0 := by
          rw [← hXW0]
          exact ⟨hzXB, interior_subset hzU.1⟩
        obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hzW.1
        by_cases hji : j = i
        · rw [hji] at hzj
          exact ⟨hzj, hzU⟩
        · have hzj' := Set.mem_iInter.1 hzU.2 j
          rw [if_neg hji] at hzj'
          exact absurd hzj hzj'.2
      · rintro ⟨hzi, hzU⟩
        have hzW : z ∈ X ∩ B ∩ W0 := by
          rw [hXW0]
          exact ⟨Set.mem_iUnion.2 ⟨i, hzi⟩, interior_subset hzU.1⟩
        exact ⟨hzW.1, hzU⟩

    obtain ⟨O, V, h, hO, hV, hxV, hh, hAh, hYV⟩ := hMsh i x ⟨hxi, hxM i⟩ (hgx' i).1
    refine ⟨O ∩ h ⁻¹' U, V ∩ U, h, hh.continuousOn.isOpen_inter_preimage hO hUo, hV.inter hUo,
      ⟨hxV, hxUm⟩, hh.mono Set.inter_subset_left, fun t ht => hAh t ht.1, ?_⟩
    rw [Set.image_inter_preimage, ← hYV]
    ext z
    constructor
    · rintro ⟨hzXB, hzV, hzU⟩
      have hz : z ∈ Y i ∩ U := by
        rw [← hXU]
        exact ⟨hzXB, hzU⟩
      exact ⟨⟨hz.1, hzV⟩, hzU⟩
    · rintro ⟨⟨hzi, hzV⟩, hzU⟩
      have hz : z ∈ X ∩ B ∩ U := by
        rw [hXU]
        exact ⟨hzi, hzU⟩
      exact ⟨hz.1, hzV, hzU⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def BranchLift.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (M : NormalModel J)
    (γ : GroundTheory.Heights₂.Heights.VarBranch J k p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    ∃ Γ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ,
      DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) ∧
      (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) ∧
      ∀ V ⊆ Metric.ball 0 γ.radius, IsOpen V →
        ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ Γ '' V = zeroSetIn M.ideal ∩ O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
