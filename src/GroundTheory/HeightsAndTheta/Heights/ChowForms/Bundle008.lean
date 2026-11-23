module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle018
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartHomogenise

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type} [Field F] {n : ℕ}

theorem exists_homogeneous_sub_mem_span (ℓ g : MvPolynomial (Fin n) F) (hℓ : ℓ.IsHomogeneous 1) :
    ∃ (G : MvPolynomial (Fin n) F) (D : ℕ), G.IsHomogeneous D ∧ G - g ∈ Ideal.span {ℓ - 1} := by
  classical
  refine ⟨∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g,
    g.totalDegree, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    have hdD : d ≤ g.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (hℓ.pow (g.totalDegree - d)).mul (homogeneousComponent_isHomogeneous d g)
    rwa [one_mul, Nat.sub_add_cancel hdD] at h
  · have e : ∑ d ∈ Finset.range (g.totalDegree + 1), ℓ ^ (g.totalDegree - d) * homogeneousComponent d g - g =
        ∑ d ∈ Finset.range (g.totalDegree + 1), (ℓ ^ (g.totalDegree - d) - 1) * homogeneousComponent d g := by
      simp only [sub_one_mul, Finset.sum_sub_distrib, sum_homogeneousComponent]
    rw [e]
    refine Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_
    rw [Ideal.mem_span_singleton]
    simpa using sub_dvd_pow_sub_pow ℓ 1 (g.totalDegree - d)

theorem proof : ChartHomogenise.Statement := by
  intro F _ n Q t hQ ht
  set 𝒜 := homogeneousSubmodule (Fin n) F
  set W : Ideal (MvPolynomial (Fin n) F) := (Q.homogeneousCore 𝒜).toIdeal with hW
  have hWQ : W ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hWprime : W.IsPrime := hQ.homogeneousCore
  have hWhom : IsHomogIdeal W := (isHomogIdeal_iff W).mpr (Q.homogeneousCore 𝒜).isHomogeneous
  have hℓ : (linForm t).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
  have hℓQ : linForm t ∉ Q := by
    intro h
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using Q.sub_mem h ht
  have hℓW : linForm t ∉ W := fun h => hℓQ (hWQ h)
  have hrel : IsRelevant W := by
    by_contra h
    simp only [IsRelevant, not_exists, not_not] at h
    exact hℓW (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h j))
  refine ⟨W, ⟨hWprime, hWhom, hrel⟩, hℓW, le_antisymm ?_ ?_, ?_⟩
  · exact sup_le hWQ ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  · intro g hg
    obtain ⟨G, D, hG, hGg⟩ := exists_homogeneous_sub_mem_span (linForm t) g hℓ
    have hspan : Ideal.span {linForm t - 1} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr ht
    have hGQ : G ∈ Q := by simpa using Q.add_mem (hspan hGg) hg
    have hGW : G ∈ W :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨D, (mem_homogeneousSubmodule D G).mpr hG⟩ hGQ
    have : g = G - (G - g) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
  · intro J hJ hJQ
    have hJh := (isHomogIdeal_iff J).mp hJ
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hJQ

end ChartHomogenise

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Chart

variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem chartLoc_algebraMap_tower (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem chartX_C (c : F) :
    chartX I t e (C c) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C c) := by
  show Ideal.Quotient.mk _ (rename Sum.inl (C c)) = Ideal.Quotient.mk _ (rename Sum.inr (C c))
  simp only [rename_C]

theorem algebraMap_localization_C (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p),
    MvPolynomial.algebraMap_eq]

theorem chartLin_eq_sum (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by

  simp only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← algebraMap_localization_C p, chartLoc_algebraMap_tower, chartX_C]

theorem chartLin_self : chartLin I t e t = 1 := by
  have h : chartX I t e (linForm t - 1) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

theorem chartLoc_adjoin_eq_top :
    Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by
  set A := Algebra.adjoin (Localization.AtPrime p)
    (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))
  have hS : ∀ x : MvPolynomial (Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) ∈ A := by
    intro x
    rw [← chartLoc_algebraMap_tower]
    exact Subalgebra.algebraMap_mem A _
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk (chartIncIdeal I t e)
  have hSig : ∀ y : MvPolynomial (Fin n ⊕ Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) ∈ A := by
    intro y
    induction y using MvPolynomial.induction_on with
    | C a =>
      have h : π (C a) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) := by
        show _ = Ideal.Quotient.mk _ (rename Sum.inr (C a))
        rw [rename_C]
        rfl
      rw [h]
      exact hS _
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb
    | mul_X a v ha =>
      rw [map_mul, map_mul]
      refine mul_mem ha ?_
      rcases v with m | im
      · refine Algebra.subset_adjoin ⟨m, ?_⟩
        show algebraMap (ChartInc I t e) (ChartLoc I t e p)
          ((Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) : ChartInc I t e)) = _
        rw [rename_X]
        rfl
      · have h : π (X (Sum.inr im)) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im) := by
          show _ = Ideal.Quotient.mk _ (rename Sum.inr (X im))
          rw [rename_X]
          rfl
        rw [h]
        exact hS _
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z
  obtain ⟨s₀, hs₀, hs⟩ := s.2
  obtain ⟨y, rfl⟩ : ∃ y, π y = x := Ideal.Quotient.mk_surjective x
  set w := algebraMap (Localization.AtPrime p) (ChartLoc I t e p)
    (IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin e × Fin n) F) ⟨s₀, hs₀⟩)
  have hw : algebraMap (ChartInc I t e) (ChartLoc I t e p) (s : ChartInc I t e) * w = 1 := by
    rw [← hs, ← chartLoc_algebraMap_tower, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one,
      IsLocalization.mk'_self, map_one]
  have hz : IsLocalization.mk' (ChartLoc I t e p) (π y) s =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) * w := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, mul_comm w, hw, mul_one]
  show IsLocalization.mk' (ChartLoc I t e p) (π y) s ∈ A
  rw [hz]
  exact mul_mem (hSig y) (Subalgebra.algebraMap_mem A _)

end Chart

theorem eval_map_firstGroup {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by
  rw [eval_map]
  simp only [firstGroup, specFirst]
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, bind₁_C_right, MvPolynomial.algebraMap_apply, eval₂_C, MvPolynomial.algebraMap_eq]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), eval₂_add, ha, hb, map_add (f := _)]
  | mul_X a ij ha =>
    rw [map_mul, map_mul, eval₂_mul, ha, map_mul, aeval_X, bind₁_X_right]
    congr 1
    obtain ⟨i, m⟩ := ij
    cases i using Fin.cases with
    | zero => simp [specFirstVar, algebraMap_localization_C]
    | succ i => simp [specFirstVar]

theorem ChartNorm.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : LocalizationPrimeDVR.Statement) (h₄ : ChartFinite.Statement) (h₅ : ChartLocDomain.Statement)
    (h₆ : ChartFirstGroupPrime.Statement) (h₇ : ChartFirstGroupDvd.Statement)
    (h₈ : NormOfDividedForm.Statement) : ChartNorm.Statement := by
  intro F _ _ n e I f t p _ hI hf hp hft u
  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact hft (hmem ▸ p.zero_mem)
  obtain ⟨hdom, hinj, -⟩ := h₅ F n e I f t p hI hf htI
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₄ F n e I f t p hI hf hft
  have : IsPrincipalIdealRing (Localization.AtPrime p) := by
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · have hfield : IsField (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) := by
        rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
          Ideal.map_bot]
      let := hfield.toField
      infer_instance
    · have := h₃ _ q _ hq rfl
      infer_instance
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) := Module.free_of_finite_type_torsion_free'
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (algebraMap F (Localization.AtPrime p)).injective
  have hsum : ∑ m, algebraMap F (Localization.AtPrime p) (t m) •
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) = 1 := by
    rw [← chartLin_eq_sum, chartLin_self, map_one]
  have hcomp : (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    RingHom.ext fun x => (chartLoc_algebraMap_tower I t p x).symm
  have hdvd := map_dvd (MvPolynomial.map (algebraMap (ChartInc I t e) (ChartLoc I t e p)))
    (h₇ F n e I f t hI hf htI)

  simp only [map_sum, map_mul, map_X, map_C, map_map, hcomp] at hdvd
  rw [← map_map] at hdvd
  have key := h₈ (Localization.AtPrime p) (ChartLoc I t e p) n _ _ _ (chartLoc_adjoin_eq_top I t p) hsum
    (h₆ F n e I f p hI hf) hdvd (fun m => algebraMap F (Localization.AtPrime p) (u m))
  rw [eval_map_firstGroup, eval_map_firstGroup, ← chartLin_eq_sum] at key
  exact key

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ConeDimComponent.proof_closed : ConeDimComponent.Statement := by
  intro F _ n e I W u hI hdim hu hW
  obtain ⟨hmin, hrel⟩ := hW
  have hWprime : W.IsPrime := hmin.1.1

  have hJ : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := isHomogIdeal_sup_span_linForm hI.isHomog u
  have hproj : IsProjPrime W := by
    classical
    have hJh := (isHomogIdeal_iff _).mp hJ
    refine ⟨hWprime, (isHomogIdeal_iff W).mpr ?_, hrel⟩
    set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal
    have hcore_prime : core.IsPrime := hWprime.homogeneousCore
    have hJcore : I ⊔ Ideal.span {linForm u} ≤ core := by
      rw [← hJh.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono _ hmin.1.2
    have hle : core ≤ W := Ideal.toIdeal_homogeneousCore_le _ _
    have heq : core = W := le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  refine ⟨hproj, ?_⟩

  have hIprime : I.IsPrime := hI.isPrime
  have hIW : I ≤ W := le_sup_left.trans hmin.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MvPolynomial (Fin n) F ⧸ I
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I)
      (Ideal.Quotient.mkₐ_surjective F I)
  set W' : Ideal B := W.map (Ideal.Quotient.mk I)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk I (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F) W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl

theorem ConeDimComponent.proof (_h₁ : MinimalPrimeHomog.Statement) : ConeDimComponent.Statement :=
  ConeDimComponent.proof_closed

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem chowFormMultiHomog : ChowFormMultiHomog.Statement :=
  fun _ _ _ _ _ _ hP hf => hf.exists_multiHomog hP

theorem ChowFormMultiHomog.proof (_h₁ : ProjNullstellensatz.Statement) :
    ChowFormMultiHomog.Statement :=
  chowFormMultiHomog

end GroundTheory.Heights₂.Heights
end
