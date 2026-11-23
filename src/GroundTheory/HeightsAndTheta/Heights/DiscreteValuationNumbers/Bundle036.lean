module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle005
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleChartSectionTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle030
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem SpanBundleDim.proof (h : PointIdealMultiProj.Statement) (hge : SpanBundleTrdegGe.Statement)
    (hle : SpanBundleTrdegLe.Statement) : SpanBundleDim.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hy hdim M i G hi hG c a H hc hH hGH Φ _ _ s hs
  have hprime : IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) := by
    let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
    refine h F Φ (Option K) (bundleIdx ι M) _ ?_
    rintro (_ | k)
    · obtain ⟨l, hl⟩ : ∃ l, G l ⟨0, hi⟩ ≠ 0 := by
        by_contra! h0
        exact hG.ne_zero ⟨0, hi⟩ (funext h0)
      refine ⟨l, fun h0 => hl ?_⟩
      have hsum : ∑ j, G l j • s j = 0 := by
        rw [← h0]
        simp only [projCoord]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Algebra.smul_def, mul_comm, Matrix.mulVec, dotProduct, Pi.single_apply]
      exact Fintype.linearIndependent_iff.1 hs.linearIndependent _ hsum ⟨0, hi⟩
    · obtain ⟨j, hj⟩ := hy.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      have hy0 : y ⟨k, j⟩ = 0 := (FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [projCoord] using h0)
      simp [pointIdeal, RingHom.mem_ker, pointConeMap, hy0]
  refine ⟨hprime, ?_⟩
  have := hprime.isPrime
  have := hy.isPrime
  have hty : Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : Cardinal) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F] at hdim
    exact Cardinal.toENat_eq_natCast.1 (WithBot.coe_injective (by simpa using hdim))
  have htz : Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
      ((e + Fintype.card K + i : ℕ) : Cardinal) := by
    apply le_antisymm
    · simpa [hty] using hle F Ω K ι y M i G c a H hc hH hGH Φ s
    · simpa [hty] using hge F Ω K ι y M i G hG Φ s hs
  apply (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (e + i - 1)).2
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, htz, Fintype.card_option,
    show e + i - 1 + (Fintype.card K + 1) = e + Fintype.card K + i by omega]
  simp

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


open FlagBundleSectionForms (chartPow chartMono liftNat) in
open FlagBundleChartSection in
theorem FlagBundleChartSection.proof : FlagBundleChartSection.Statement := by
  intro F _ Ω _ _ K _ _ ι y N E _ _ B w b hfl M a φ hφ Φ _ _ t ht i c hsc
  classical
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hsc) k (Finset.mem_univ _)
  have hcpb : chartPow y c (b i) ≠ 0 := chartPow_ne_zero hY _
  obtain ⟨dl, β, f, hfh, hdeg, hfv⟩ := exists_section_form (M := M) y B w b hfl a φ hφ t i c hsc

  obtain ⟨vi, hviL, hviT, hviD⟩ : ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
      w.repr v i = chartPow y c (b i) := by
    have h := hfl.graded c hsc i
    rw [Set.ext_iff] at h
    exact (h (chartPow y c (b i))).2 ⟨1, one_mem _, (one_mul _).symm⟩

  have hr : ∀ l, ∃ r ∈ chartRing F (segreVec y) c, φ l vi = r * chartPow y c a :=
    fun l => hφ.sections c hsc l vi hviL
  choose r hrA hrv using hr
  obtain ⟨n₂, R, hRh, hRe⟩ := chartRing_forms_fin (M := M) y w φ (truncCoord t ((i : ℕ) + 1)) c hsc hrA

  let γ₁ : K → ℕ := fun k => (b i k - a k).toNat
  let γ₂ : K → ℕ := fun k => (a k - b i k).toNat
  let δ : K → ℕ := β + fun k => n₂ + γ₁ k
  let u : MRing (bundleIdx ι M) F := chartMono M c δ
  let Y : Fin M → MRing (bundleIdx ι M) F := fun l => u * X ⟨none, l⟩ - R l * chartMono M c γ₂ * f
  let g : (Σ o, bundleIdx ι M o) → MRing (bundleIdx ι M) F := fun v =>
    match v with
    | ⟨none, l⟩ => Y l
    | ⟨some k, p⟩ => X ⟨some k, p⟩
  let e : Option K → ℕ := fun o => liftNat δ o + Option.elim o 1 (fun _ => 0)
  have hYh : ∀ l, IsMultiHomog (Y l) e := by
    intro l
    refine isMultiHomog_sub ?_ ?_
    · have h := (chartMono_homog (F := F) M c δ).mul
        (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
      have he : e = liftNat δ + blockWeight (bundleIdx ι M) ⟨none, l⟩ := by
        funext o
        cases o <;> simp [e, liftNat, blockWeight]
      rw [he]
      exact h
    · have h := ((hRh l).mul (chartMono_homog (F := F) M c γ₂)).mul hfh
      have he : e = (liftNat fun _ => n₂) + liftNat γ₂ + dl := by
        funext o
        cases o with
        | none =>
          have h0 := congrFun hdeg none
          simp [liftNat, zetaDeg, liftDeg] at h0
          simp [e, liftNat]
          omega
        | some k =>
          have h0 := congrFun hdeg (some k)
          simp [liftNat, zetaDeg, liftDeg] at h0
          simp [e, liftNat, δ, γ₁, γ₂]
          omega
      rw [he]
      exact h
  have hid : (∏ k, y ⟨k, c k⟩ ^ δ k) * chartPow y c a =
      (∏ k, y ⟨k, c k⟩ ^ β k) * segreVec y c ^ n₂ * (∏ k, y ⟨k, c k⟩ ^ γ₂ k) * chartPow y c (b i) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_natCast]
    simp only [← chartPow_add hY]
    congr 1
    funext k
    simp only [Pi.add_apply, Nat.cast_add, δ, γ₁, γ₂]
    omega
  have hevY : ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (Y l) =
      algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ -
        algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * (t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹) *
          algebraMap Ω Φ (φ l vi) := by
    intro l
    have hΩ : r l * segreVec y c ^ n₂ * (∏ k, y ⟨k, c k⟩ ^ γ₂ k) * (∏ k, y ⟨k, c k⟩ ^ β k) =
        (∏ k, y ⟨k, c k⟩ ^ δ k) * (chartPow y c (b i))⁻¹ * (r l * chartPow y c a) := by
      rw [show (∏ k, y ⟨k, c k⟩ ^ δ k) * (chartPow y c (b i))⁻¹ * (r l * chartPow y c a) =
        r l * ((∏ k, y ⟨k, c k⟩ ^ δ k) * chartPow y c a) * (chartPow y c (b i))⁻¹ by ring, hid]
      field_simp
    have h2 := congrArg (algebraMap Ω Φ) hΩ
    simp only [Y, u, eval₂_sub, eval₂_mul, eval₂_X, hRe, eval_chartMono, hfv, hrv]
    simp only [map_mul, map_inv₀] at h2 ⊢
    linear_combination (-(t i)) * h2

  have hgev : (fun v => eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (g v)) =
      projCoord y w φ (truncCoord (fun j => algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) *
        (t j - t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ * algebraMap Ω Φ (w.repr vi j))) i) := by
    funext v
    rcases v with ⟨_ | k, p⟩
    · show eval₂ _ _ (Y p) = _
      have hφv : algebraMap Ω Φ (φ p vi) =
          ∑ j, algebraMap Ω Φ (w.repr vi j) * algebraMap Ω Φ (φ p (w j)) := by
        conv_lhs => rw [← w.sum_repr vi]

        simp only [map_sum, map_smul, smul_eq_mul, map_mul]
      rw [hevY p, hφv]
      simp only [projCoord]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [truncCoord]
      rcases lt_trichotomy j i with h | h | h
      · have h1 : (j : ℕ) < i := h
        have h2 : (j : ℕ) < (i : ℕ) + 1 := by omega
        simp only [h1, h2, if_true]
        ring
      · subst h
        have h1 : ¬ (j : ℕ) < j := lt_irrefl _
        have h2 : (j : ℕ) < (j : ℕ) + 1 := Nat.lt_succ_self _
        have hσ : t j * algebraMap Ω Φ (chartPow y c (b j))⁻¹ * algebraMap Ω Φ (chartPow y c (b j)) = t j := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hcpb, map_one, mul_one]
        simp only [h1, h2, if_true, if_false, hviD]
        linear_combination (-(algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * algebraMap Ω Φ (φ p (w j)))) * hσ
      · have h1 : ¬ (j : ℕ) < i := by
          have : (i : ℕ) < j := h
          omega
        have h2 : ¬ (j : ℕ) < (i : ℕ) + 1 := by
          have : (i : ℕ) < j := h
          omega
        simp only [h1, h2, if_false, hviT j h, map_zero]
        ring
    · rw [eval₂_X]
      rfl

  have hform : ∀ (d : Option K → ℕ) (q : MRing (bundleIdx ι M) F), IsMultiHomog q d →
      q ∈ projIdeal F y w φ (truncCoord t i) →
      u ^ d none * q ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} := by
    intro d q hq hqI
    have h1 : bind₁ g q ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := by
      rw [ProjIdealFormValue.proof F Ω K ι y N E w M φ Φ _ _ _
        (bind₁_isMultiHomog g e (fun _ _ => rfl) hYh hq)]
      rw [← coe_eval₂Hom, eval₂Hom_bind₁, coe_eval₂Hom]
      simp only [coe_eval₂Hom]
      rw [hgev]
      exact eval_trunc_eq_zero y w φ ht i hqI _
    have h2 : u ^ d none * q - bind₁ g q ∈ Ideal.span {f} := by
      rw [← bind₁_scale u hq]
      refine bind₁_sub_mem _ g _ (fun v => ?_) q
      rcases v with ⟨_ | k, p⟩
      · have h3 : u ^ blockWeight (bundleIdx ι M) ⟨none, p⟩ none * X ⟨none, p⟩ - g ⟨none, p⟩ =
            R p * chartMono M c γ₂ * f := by
          simp [g, Y, blockWeight]
        rw [h3]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)
      · have h3 : u ^ blockWeight (bundleIdx ι M) ⟨some k, p⟩ none * X ⟨some k, p⟩ - g ⟨some k, p⟩ = 0 := by
          simp [g, blockWeight]
        rw [h3]
        exact zero_mem _
    have h3 : bind₁ g q + (u ^ d none * q - bind₁ g q) ∈
        projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} :=
      Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    rwa [add_sub_cancel] at h3
  refine ⟨dl, liftNat β, f, chartMono M c β, β, rfl, hfh, chartMono_homog M c β, hdeg, hfv, ?_⟩
  intro q hq

  have hsat : ∀ d, ∃ n : ℕ, (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n *
      weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q ∈
      projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} := by
    intro d
    have hqd := hform d _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (component_mem_projIdeal y w φ _ hq d)
    obtain ⟨r', hr'⟩ := chartMono_pow_dvd (F := F) (M := M) c δ (d none)
    refine ⟨d none * ∑ k, δ k, ?_⟩
    rw [hr', mul_comm (chartMono M c δ ^ d none) r', mul_assoc]
    exact Ideal.mul_mem_left _ _ hqd
  choose nn hnn using hsat
  obtain ⟨S, hS⟩ : ∃ S : Finset (Option K → ℕ),
      q = ∑ d ∈ S, weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q := by
    have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight (bundleIdx ι M)) q
    refine ⟨hfin.toFinset, ?_⟩
    conv_lhs => rw [← sum_weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) q]
    exact finsum_eq_sum _ hfin
  refine ⟨∑ d ∈ S, nn d, ?_⟩
  rw [hS, Finset.mul_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [← Nat.sub_add_cancel (Finset.single_le_sum (f := nn) (fun _ _ => Nat.zero_le _) hd), pow_add,
    mul_assoc]
  exact Ideal.mul_mem_left _ _ (hnn d)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotRing.proof : LocalQuotRing.Statement.{u} := by
  intro R _ P U _ hP hPU
  have hdisj : Disjoint (U.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun x hx hxP => hx (hPU hxP)
  have hPS : (P.map (algebraMap R (Localization.AtPrime U))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) P hP hdisj
  have hker : (P.map (algebraMap R (Localization.AtPrime U))).comap
      (algebraMap R (Localization.AtPrime U)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint U.primeCompl (Localization.AtPrime U) hP hdisj
  haveI := hPS
  have hdom : IsDomain (localQuot P U) := Ideal.Quotient.isDomain _
  have hloc : IsLocalRing (localQuot P U) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmax : U.map (localQuotMap P U) = IsLocalRing.maximalIdeal (localQuot P U) := by
    rw [localQuotMap, ← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨hdom, hloc, fun y => ?_, fun x => ?_⟩
  · rw [hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  · rw [localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hker]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotPrimes.proof : LocalQuotPrimes.Statement.{u} := by
  intro R _ P U _ hPU
  let S := Localization.AtPrime U
  let PS : Ideal S := P.map (algebraMap R S)
  have hsurj : Function.Surjective (Ideal.Quotient.mk PS) := Ideal.Quotient.mk_surjective
  have hmap : ∀ I : Ideal R,
      I.map (localQuotMap P U) = (I.map (algebraMap R S)).map (Ideal.Quotient.mk PS) := by
    intro I
    rw [Ideal.map_map]
    rfl
  have hcomap : ∀ J : Ideal (localQuot P U),
      J.comap (localQuotMap P U) = (J.comap (Ideal.Quotient.mk PS)).comap (algebraMap R S) := by
    intro J
    rw [Ideal.comap_comap]
    rfl
  refine ⟨fun W hW hPW hWU => ?_, fun p hp => ?_⟩
  · have hdisj : Disjoint (U.primeCompl : Set R) W := by
      rw [Set.disjoint_left]
      intro x hx hxW
      exact hx (hWU hxW)
    have hWS : (W.map (algebraMap R S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint U.primeCompl S W hW hdisj
    have hWSc : (W.map (algebraMap R S)).comap (algebraMap R S) = W :=
      IsLocalization.under_map_of_isPrime_disjoint U.primeCompl S hW hdisj
    have hker : RingHom.ker (Ideal.Quotient.mk PS) ≤ W.map (algebraMap R S) := by
      rw [Ideal.mk_ker]
      exact Ideal.map_mono hPW
    refine ⟨?_, ?_⟩
    · rw [hmap]
      exact Ideal.map_isPrime_of_surjective hsurj hker
    · rw [hmap, hcomap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hker, hWSc]
  · let q : Ideal S := p.comap (Ideal.Quotient.mk PS)
    have hq : q.IsPrime := Ideal.comap_isPrime _ p
    have hq' := (IsLocalization.isPrime_iff_isPrime_disjoint U.primeCompl S q).mp hq
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Ideal.mem_comap]
      have h0 : localQuotMap P U x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
      rw [h0]
      exact p.zero_mem
    · intro x hx
      by_contra hxU
      rw [hcomap] at hx
      exact Set.disjoint_left.mp hq'.2 (show x ∈ U.primeCompl from hxU) hx
    · rw [hmap, hcomap]
      have hloc : (q.comap (algebraMap R S)).map (algebraMap R S) = q :=
        IsLocalization.map_under U.primeCompl S q
      rw [hloc]
      exact Ideal.map_comap_of_surjective _ hsurj p

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem LocalQuotColon.proof : LocalQuotColon.Statement.{u} := by
  intro R _ P U _ f g
  set S := Localization.AtPrime U
  set I := P.map (algebraMap R S)
  have hφ : ∀ x : R, localQuotMap P U x = Ideal.Quotient.mk I (algebraMap R S x) := fun _ => rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hp0 : localQuotMap P U p = 0 := by
      rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hp
    refine Ideal.mem_span_singleton'.mpr ⟨localQuotMap P U a, ?_⟩
    rw [← map_mul, ← map_mul, ← hpz, map_add (f := _), hp0, zero_add, map_mul]
  · intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b0, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl y0
    obtain ⟨⟨r', t'⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b0
    simp only [hφ] at hb
    have hI := Ideal.Quotient.eq.mp hb
    have e1 := IsLocalization.mk'_spec S r t
    have e2 := IsLocalization.mk'_spec S r' t'
    have hw : algebraMap R S ((t : R) * r' * f - (t' : R) * r * g) ∈ I := by
      have := I.mul_mem_left (algebraMap R S ((t : R) * t')) hI
      convert this using 1
      simp only [map_mul, map_sub]
      linear_combination (algebraMap R S t' * algebraMap R S g) * e1 -
        (algebraMap R S t * algebraMap R S f) * e2
    obtain ⟨⟨p, s⟩, hps⟩ := (IsLocalization.mem_map_algebraMap_iff U.primeCompl S).mp hw
    rw [← map_mul] at hps
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists U.primeCompl S).mp hps
    have hx : (c : R) * s * t' * r ∈ (P ⊔ Ideal.span {f}).colon {g} := by
      rw [Submodule.mem_colon_singleton, smul_eq_mul]
      refine Submodule.mem_sup.mpr ⟨-((c : R) * p), P.neg_mem (P.mul_mem_left _ p.2),
        (c : R) * s * t * r' * f, Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩, ?_⟩
      linear_combination hc
    have hy' : Ideal.Quotient.mk I (IsLocalization.mk' S r t) =
        localQuotMap P U ((c : R) * s * t' * r) *
          Ideal.Quotient.mk I (IsLocalization.mk' S (1 : R) (c * s * t' * t)) := by
      rw [hφ, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
      congr 1
      rw [IsLocalization.mk'_eq_iff_eq]
      congr 1
      push_cast
      ring
    rw [hy']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull FlagPair assocDeg assocVar)

def FlagPairJoinLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (EF E'F : ChartBundle O (mseg (joinCoord x z)) N V),
    IsPull O x z E EF → IsPull O x z E' E'F → ∀ φ : FlagPair O (joinCoord x z) EF E'F,
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord z w))) N V,
      IsPull O x (joinCoord z w) E EB → IsPull O x (joinCoord z w) E' E'B →
    ∃ ψ : FlagPair O (joinCoord x (joinCoord z w)) EB E'B,
      ψ.Vs = φ.Vs ∧ ψ.gen = φ.gen ∧ ψ.gen' = φ.gen' ∧
      ψ.deg = (fun i => assocDeg (K₂ := K₂) (φ.deg i)) ∧
      ψ.deg' = (fun i => assocDeg (K₂ := K₂) (φ.deg' i)) ∧
      ψ.f = (fun i => rename (assocVar ι₂) (φ.f i)) ∧ ψ.g = (fun i => rename (assocVar ι₂) (φ.g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end
