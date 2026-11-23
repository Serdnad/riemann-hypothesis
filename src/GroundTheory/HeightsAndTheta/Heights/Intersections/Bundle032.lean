module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.RegularizedCurvature
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HorizNotMem.ringKrullDim_quotient_add_one_le {R : Type*} [CommRing R] {W₀ W : Ideal R}
    [hW₀ : W₀.IsPrime] [hW : W.IsPrime] (hlt : W₀ < W) :
    ringKrullDim (R ⧸ W) + 1 ≤ ringKrullDim (R ⧸ W₀) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨⟨⟨W, hW⟩, fun _ h => h⟩⟩
  rw [← Order.krullDim_withBot]
  let f : WithBot (PrimeSpectrum.zeroLocus (R := R) W) → PrimeSpectrum.zeroLocus (R := R) W₀ :=
    fun x => WithBot.recBotCoe ⟨⟨W₀, hW₀⟩, fun _ h => h⟩ (fun q => ⟨q.1, fun _ h => q.2 (hlt.le h)⟩) x
  refine Order.krullDim_le_of_strictMono f ?_
  intro a b hab
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (lt_irrefl _)
    | coe q =>
      change (⟨⟨W₀, hW₀⟩, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp
        (hlt.trans_le (fun _ h => q.2 h)))
  | coe p =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd hab (WithBot.not_lt_bot _)
    | coe q =>
      change (⟨p.1, _⟩ : PrimeSpectrum.zeroLocus (R := R) W₀) < ⟨q.1, _⟩
      exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp (WithBot.coe_lt_coe.mp hab))

theorem HorizNotMem.proof : HorizNotMem.Statement := by
  intro K _ ι _ P d s s' W hP hsP hs'P hnc hW hWh hs'W
  have : P.IsPrime := hP.2.1.1
  have hWp : W.IsPrime := hW.1.1.1
  have hle : P ⊔ Ideal.span {s'} ≤ W :=
    sup_le (le_sup_left.trans hW.1.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hs'W)
  obtain ⟨W₀, hW₀, hW₀W⟩ := Ideal.exists_minimalPrimes_le hle
  have : W₀.IsPrime := hW₀.1.1
  have h1 := dim_quot_minimal_add_one P W s hsP hW.1
  have h2 := dim_quot_minimal_add_one P W₀ s' hs'P hW₀
  have heq : W₀ = W := by
    by_contra hne
    have hstep := HorizNotMem.ringKrullDim_quotient_add_one_le (lt_of_le_of_ne hW₀W hne)
    have h3 := add_le_add hstep (le_refl (1 : WithBot ℕ∞))
    rw [h1, h2, hP.2.2.2] at h3
    have h4 : ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h5
    omega
  exact hnc W hW ⟨heq ▸ hW₀, hW.2⟩ hWh

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

theorem regularityDehomogenization_holds.proof (h₁ : GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.Statement.{0, 0})
    (h₂ : regularityLocalFlat_holds.Statement) : regularityDehomogenization_holds.Statement := by
  intro K _ ι _ P s t a W y hP hs hsP hW ht htW hy
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have := hP.1
  have := hWp
  have hWm : IsMultiProjPrime W := ⟨hWp, isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hs hW.1, hW.2⟩

  have htnz : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hPW h)
  have hyO : y ∈ locRing P W := by
    refine Subring.subset_closure ⟨s, t, a, htnz, htW, hs, ht, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hy
  refine ⟨hyO, ?_⟩
  obtain ⟨_, _, _, hmax⟩ := h₂ K ι P W hP hWm hPW
  have : IsLocalHom (algebraMap (locRing P W) (coneLocRing P W hPW)) :=
    ((local_hom_tfae _).out 3 1).mp hmax.le

  have hu : IsUnit (algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t)) :=
    IsLocalization.map_units (coneLocRing P W hPW)
      (⟨_, ⟨t, htW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hs' : algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s) =
      algebraMap (locRing P W) (coneLocRing P W hPW) ⟨y, hyO⟩ *
        algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, locRing.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hy]
  have hspan : Ideal.span {algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s)} =
      (Ideal.span {(⟨y, hyO⟩ : locRing P W)}).map (algebraMap (locRing P W) (coneLocRing P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, hs', Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B],
      (maximalIdeal A).map (algebraMap A B) = maximalIdeal B → ∀ x : A,
        Module.length B (B ⧸ (Ideal.span {x}).map (algebraMap A B)) = Module.length A (A ⧸ Ideal.span {x}) := by
    intro A B _ _ _ _ _ _ _ hm x
    have hres : Module.length B (B ⧸ maximalIdeal B) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hres, mul_one]
  unfold multAt
  rw [dite_eq_left hWp, h₁ (MRing ι) P W s (coneLocRing P W hPW) inferInstance, hspan, locIdeal_eq_span hyO,
    key (locRing P W) (coneLocRing P W hPW) hmax]

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing

noncomputable section

namespace LocRingPow

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


open Classical in
def multiDegWeight (ι : K → Type*) : (Σ k, ι k) → (K → ℕ) := fun p k => if p.1 = k then 1 else 0

theorem weight_multiDegWeight (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (multiDegWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  classical
  funext k
  rw [← weight_blockWeight k m, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    Finset.sum_apply]
  simp only [Pi.smul_apply, multiDegWeight, blockWeight]

theorem isMultiHomog_iff {f : MRing ι} {a : K → ℕ} :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (multiDegWeight ι) f a := by
  constructor
  · intro h d hd
    rw [weight_multiDegWeight]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_multiDegWeight] at this
    exact congrFun this k

theorem component_mem [DecidableEq K] {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    (hf : f ∈ J) (D : K → ℕ) : weightedHomogeneousComponent (multiDegWeight ι) D f ∈ J := by
  obtain ⟨g, hg, hgc⟩ := exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hJ) D Finset.univ hf
  convert hg using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hgc, weight_multiDegWeight]
  by_cases h : ∀ k, ∑ i, m ⟨k, i⟩ = D k
  · simp [h]
  · simp [h, funext_iff]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_component_not_mem {J : Ideal (MRing ι)} {f : MRing ι} (hf : f ∉ J) :
    ∃ D : K → ℕ, weightedHomogeneousComponent (multiDegWeight ι) D f ∉ J := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  rw [← sum_weightedHomogeneousComponent (w := multiDegWeight ι) (φ := f),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  exact Ideal.sum_mem _ fun D _ => h D

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [∀ k, Fintype (ι k)] in
theorem component_mul_right [DecidableEq K] {f g : MRing ι} {i j : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) :
    weightedHomogeneousComponent (multiDegWeight ι) (i + j) (f * g) =
      weightedHomogeneousComponent (multiDegWeight ι) i f * g := by
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg)


omit [∀ k, Fintype (ι k)] in
theorem component_mul_of_not_le [DecidableEq K] {f g : MRing ι} {j n : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) (h : ¬ j ≤ n) :
    weightedHomogeneousComponent (multiDegWeight ι) n (f * g) = 0 := by
  rw [← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg) h

end LocRingPow


open LocRingPow in
theorem LocRingPow.proof : LocRingPow.Statement := by
  classical
  intro K _ ι _ P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hy
  have := hPp
  obtain ⟨hWmin, -⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2

  obtain ⟨n, d, hdW, hd⟩ : ∃ n : ℕ, ∃ d ∉ W, d * u ^ n ∈ P ⊔ Ideal.span {s} := by
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W _ hWmin
    have hu' : algebraMap (MRing ι) (Localization.AtPrime W) u ∈
        ((P ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).radical :=
      hrad ▸ Ideal.mem_map_of_mem _ huW
    obtain ⟨n, hn⟩ := hu'
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at hn
    obtain ⟨⟨⟨i, hi⟩, ⟨c, hc⟩⟩, he⟩ := hn
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at he
    obtain ⟨⟨e, he'⟩, hee⟩ := he
    refine ⟨n, e * c, W.primeCompl.mul_mem he' hc, ?_⟩
    have : e * c * u ^ n = e * (u ^ n * c) := by ring
    rw [this, hee]
    exact Ideal.mul_mem_left _ _ hi

  obtain ⟨e, he⟩ := exists_component_not_mem hdW
  set ce := weightedHomogeneousComponent (multiDegWeight ι) e d with hce_def
  have hce : IsMultiHomog ce e :=
    isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hd
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hq

  set D : K → ℕ := e + n • b with hD
  have h1 : weightedHomogeneousComponent (multiDegWeight ι) D (d * u ^ n) = ce * u ^ n :=
    component_mul_right (isMultiHomog_iff.mp (isMultiHomog_pow hu n))
  obtain ⟨G, hG, hGs⟩ : ∃ G : MRing ι, IsMultiHomog (G * t) D ∧
      weightedHomogeneousComponent (multiDegWeight ι) D (g * s) = G * s := by
    by_cases hle : a ≤ D
    · refine ⟨weightedHomogeneousComponent (multiDegWeight ι) (D - a) g, ?_, ?_⟩
      · have := isMultiHomog_mul
          (isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (D - a) g)) ht
        rwa [tsub_add_cancel_of_le hle] at this
      · conv_lhs => rw [← tsub_add_cancel_of_le hle]
        exact component_mul_right (isMultiHomog_iff.mp hs)
    · exact ⟨0, fun m hm => by simp at hm,
        by rw [zero_mul]; exact component_mul_of_not_le (isMultiHomog_iff.mp hs) hle⟩
  have hrel : ce * u ^ n - G * s ∈ P := by
    have := component_mem hPh hp D
    rwa [← add_sub_cancel_right p (g * s), hpq, map_sub, h1, hGs] at this

  have hden : ce * v ^ n ∉ W := fun h =>
    (hWp.mem_or_mem h).elim he fun h => hvW (hWp.mem_of_pow_mem _ h)
  have hdenP : Ideal.Quotient.mk P (ce * v ^ n) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hden (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  refine ⟨n, IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (G * t)) ⟨_, hdenP⟩,
    Subring.subset_closure ⟨G * t, ce * v ^ n, D, hdenP, hden, hG, isMultiHomog_mul hce (isMultiHomog_pow hv n), rfl⟩,
    ?_⟩
  have hne : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (ce * v ^ n)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdenP
  apply mul_right_cancel₀ hne
  rw [mul_assoc x, IsLocalization.mk'_spec]
  have key := congrArg (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))) (Ideal.Quotient.eq.mpr hrel)
  simp only [map_mul, map_pow] at key hx hy ⊢
  calc y ^ n * (algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P v) ^ n)
      = algebraMap _ _ (Ideal.Quotient.mk P ce) * (y * algebraMap _ _ (Ideal.Quotient.mk P v)) ^ n := by ring
    _ = algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P u) ^ n := by rw [hy]
    _ = algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P s) := key
    _ = x * (algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P t)) := by
        rw [← hx]; ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian RegularizedCurvature MvPolynomial

theorem RegCurvBound.proof (hB : TorusInvLevi.Statement) : RegCurvBound.Statement := by
  intro K _ ι _ E t ht hE
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  have hlogH : ∀ M : HermLine ι, IsSmoothHerm M → ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun M hM z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (E.h y) + ∑ k, (-(E.a k : ℝ)) * F k y with hu
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(E.a k : ℝ)) (hlogH E hE z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι := ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι := ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (E.h (fun p => c p.1 * z p)) =
        ∑ k, (E.a k : ℝ) * Real.log ‖c k‖ + Real.log (E.h z) := by
      rw [E.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (E.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (E.h (fun p => c p.1 * z p)) + ∑ k, (-(E.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (E.h z) + ∑ k, (-(E.a k : ℝ)) * F k z
    rw [hh]
    simp only [hF, mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  obtain ⟨C, hC⟩ := hB K ι u (fun z hz => (hu2 z hz).contDiffWithinAt) hinv

  have hΦ : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w,
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
        ∑ k, ReciprocityTheory.AnForm.levi (F k) z w := by
    intro z hz w
    have h := (levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => 1) contDiffAt_const (contDiffAt_F hz) w
      Finset.univ).2
    simp only [zero_add, one_mul, levi_const] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(E.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (E.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(E.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(E.a k : ℝ)| ≤ ∑ k, |(E.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(E.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (E.a k : ℝ)
    linarith
  refine ⟨N, fun ε hε => ?_⟩
  set R : HermLine ι := regLine E t ht ε with hR
  have hRs : IsSmoothHerm R := isSmoothHerm_regLine hE hε
  intro z hz v
  have hW0 : 0 ≤ ∑ k, ReciprocityTheory.AnForm.levi (F k) z v :=
    Finset.sum_nonneg fun k _ => levi_F_nonneg hz k v

  have hLW : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    have hs := levi_add_sum u F (fun k => (E.a k : ℝ)) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    have hfun : (fun y => u y + ∑ k, (E.a k : ℝ) * F k y) = fun y => Real.log (E.h y) := by
      funext y
      simp only [hu, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hfun] at hs
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, (E.a k : ℝ) * ReciprocityTheory.AnForm.levi (F k) z v + N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    rw [hs.2]
    linarith

  have hΦ1 : ContDiffAt ℝ 2 (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) z :=
    (hlogH E hE z hz).add (contDiffAt_const.mul (hlogH R hRs z hz))
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := levi_logSum (h := E.h)
    (T := fun y => eval y (map (Int.castRingHom ℂ) t))
    (Φ := fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) (hlogH E hE z hz)
    (by filter_upwards [hUo.mem_nhds hz] with y hy; exact E.pos y hy) (analyticAt_eval_map t z) hε hΦ1
    (fun y => by rw [hR, log_regLine_h, secNorm, one_mul]) v

  have hs := levi_add_sum (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) F (fun _ => (N : ℝ)) hΦ1
    (contDiffAt_F hz) v Finset.univ
  have hev : (fun y => Real.log (((E.tensor R).tensor
      (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (N : ℤ)))).h y)) =ᶠ[𝓝 z]
      fun y => (Real.log (E.h y) + 1 * Real.log (R.h y)) + ∑ k, (N : ℝ) * F k y := by
    filter_upwards [hUo.mem_nhds hz] with y hy
    show Real.log ((E.h y * R.h y) * ∏ k, (fsMetric (ι := ι k)).ρ (fun i => y ⟨k, i⟩) ^ ((N : ℤ))) = _
    rw [Real.log_mul (mul_pos (E.pos y hy) (R.pos y hy)).ne'
        (Finset.prod_pos fun k _ => zpow_pos (rho_pos hy k) _).ne',
      Real.log_mul (E.pos y hy).ne' (R.pos y hy).ne',
      Real.log_prod (fun k _ => (zpow_pos (rho_pos hy k) _).ne')]
    simp only [Real.log_zpow, F, Int.cast_natCast, one_mul]
  rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2,
    ← Finset.mul_sum]
  have hmu : 0 ≤ μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    rcases le_or_gt 0 (ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v) with hL0 | hL0
    · exact add_nonneg (mul_nonneg hμ0 hL0) (mul_nonneg (Nat.cast_nonneg _) hW0)
    · nlinarith
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocResidueAdjoin.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    ∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')]
      (G' : GenFibre v W') (i' : ∀ k', ι' k'), (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ W') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.length (locRing (imageZ v P') W)
        (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' (fibreOver v P' W) W' hW') =
      (Module.finrank G'.Φ (IntermediateField.adjoin G'.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G'.x' ⟨q.1.1, q.2⟩ / G'.x' ⟨q.1.1, i' q.1.1⟩)) : ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
end
end
