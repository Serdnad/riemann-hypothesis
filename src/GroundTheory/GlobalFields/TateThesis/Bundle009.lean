module

public import GroundTheory.GlobalFields.TateThesis.Bundle008
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite
public import GroundTheory.GlobalFields.TateThesis.GlobalZeta
import GroundTheory.GlobalFields.TateThesis.Bundle007
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
public import GroundTheory.GlobalFields.TateThesis.SchwartzBruhat
public import GroundTheory.GlobalFields.TateThesis.AdelePoisson
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import GroundTheory.GlobalFields.TateThesis.Bundle001
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex
open scoped NumberField.AdeleRing Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def gammaFactor (s : ℂ) : ℂ := ∏ w, χ.infiniteGamma w s

omit [NumberField K] in
theorem prod_infiniteConst [NumberField K] :
    ∏ w : InfinitePlace K, infiniteConst w = (π : ℂ) ^ nrComplexPlaces K := by
  rw [prod_eq_prod_mul_prod]
  have h1 : ∀ w : {w : InfinitePlace K // IsReal w}, infiniteConst w.1 = 1 := fun w ↦ by
    rw [infiniteConst, if_pos w.2]
  have h2 : ∀ w : {w : InfinitePlace K // IsComplex w}, infiniteConst w.1 = π := fun w ↦ by
    rw [infiniteConst, if_neg (not_isReal_iff_isComplex.2 w.2)]
  simp only [h1, h2, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ]

def testFunction : 𝔸[K] → ℂ := schwartzBruhatTensor χ.infiniteSchwartz χ.finiteTestFun

theorem pi_pow_nrComplexPlaces_ne_zero : (π : ℂ) ^ nrComplexPlaces K ≠ 0 :=
  pow_ne_zero _ (ofReal_ne_zero.2 Real.pi_ne_zero)

theorem testFunction_mem : χ.testFunction ∈ schwartzBruhat K :=
  schwartzBruhatTensor_mem _ χ.finiteTestFun_mem

theorem zetaIntegrand_testFunction (s : ℂ) (x : IdeleGroup K) :
    χ.testFunction x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s =
      (χ.infiniteSchwartz (homeomorphMixedSpace K (toInfinite K x)) *
          (χ.toIdele (ofInfinite (toInfinite K x)) : ℂ) *
          ((∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult :
            ℝ) : ℂ) ^ s) *
        (χ.finiteTestFun (toFinite K x) * (χ.toIdele (ofFinite (toFinite K x)) : ℂ) *
          ((finiteModule (ofFinite (toFinite K x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (χ.toIdele x : ℂ) = (χ.toIdele (ofFinite (toFinite K x)) : ℂ) *
      (χ.toIdele (ofInfinite (toInfinite K x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule K x : ℝ) : ℂ) ^ s =
      ((∏ w, ‖((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult :
        ℝ) : ℂ) ^ s * ((finiteModule (ofFinite (toFinite K x)) : ℝ) : ℂ) ^ s := by
    rw [ideleModule_apply, ofReal_mul, mul_cpow_ofReal_nonneg (infiniteModule_pos x).le
      (finiteModule_pos x).le]
    rfl
  rw [hchi, hmod]
  change χ.infiniteSchwartz (homeomorphMixedSpace K (x : 𝔸[K]).1) * χ.finiteTestFun (x : 𝔸[K]).2 *
    _ * _ = _
  have e1 : (x : 𝔸[K]).1 = ((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) :=
    rfl
  have e2 : (x : 𝔸[K]).2 = ((toFinite K x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    FiniteAdeleRing (𝓞 K) K) := rfl
  rw [e1, e2]
  ring

theorem globalZeta_testFunction {s : ℂ} (hs : 1 < s.re) :
    globalZeta χ.testFunction χ s = (π : ℂ) ^ nrComplexPlaces K * χ.gammaFactor s * χ.LFunction s := by
  have hs0 : 0 < s.re := by linarith
  set A : (InfiniteAdeleRing K)ˣ → ℂ := fun a ↦ χ.infiniteSchwartz (homeomorphMixedSpace K a) *
    (χ.toIdele (ofInfinite a) : ℂ) * ((∏ w, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ^ s
    with hA
  set B : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ := fun b ↦ χ.finiteTestFun b *
    (χ.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup K, χ.testFunction x * (χ.toIdele x : ℂ) *
      ((ideleModule K x : ℝ) : ℂ) ^ s = A (toInfinite K x) * B (toFinite K x) :=
    χ.zetaIntegrand_testFunction s
  have hBinv : ∀ b, ∀ w ∈ finiteIntegralUnits K, B (b * w) = B b := fun b w hw ↦ by
    simp only [hB, χ.finiteTestFun_mul_toIdele_mul_cpow, ordFinsupp_ofFinite_mul b hw]
  have hinv : ∀ x : IdeleGroup K, ∀ w ∈ finiteIntegralUnits K,
      χ.testFunction (x * (prodEquiv K).symm (1, w) : IdeleGroup K) *
        (χ.toIdele (x * (prodEquiv K).symm (1, w)) : ℂ) *
        ((ideleModule K (x * (prodEquiv K).symm (1, w)) : ℝ) : ℂ) ^ s =
      χ.testFunction x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s := by
    intro x w hw
    rw [hF, hF, map_mul, map_mul]
    have h1 : toInfinite K ((prodEquiv K).symm (1, w)) = 1 := by
      change ((prodEquiv K) ((prodEquiv K).symm (1, w))).1 = 1
      rw [ContinuousMulEquiv.apply_symm_apply]
    have h2 : toFinite K ((prodEquiv K).symm (1, w)) = w := by
      change ((prodEquiv K) ((prodEquiv K).symm (1, w))).2 = w
      rw [ContinuousMulEquiv.apply_symm_apply]
    rw [h1, h2, mul_one, hBinv _ w hw]
  have h := hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits
    (integrable_globalZetaIntegrand χ.testFunction_mem χ hs) hinv
  have hc : ∀ c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K,
      ∫ a, χ.testFunction ((prodEquiv K).symm (a, c.out) : IdeleGroup K) *
        (χ.toIdele ((prodEquiv K).symm (a, c.out)) : ℂ) *
        ((ideleModule K ((prodEquiv K).symm (a, c.out)) : ℝ) : ℂ) ^ s ∂infiniteIdeleMeasure K =
      (∏ w, infiniteConst w * χ.infiniteGamma w s) * B c.out := by
    intro c
    have hsymm : ∀ a, toInfinite K ((prodEquiv K).symm (a, c.out)) = a ∧
        toFinite K ((prodEquiv K).symm (a, c.out)) = c.out := fun a ↦ by
      constructor
      · change ((prodEquiv K) ((prodEquiv K).symm (a, c.out))).1 = a
        rw [ContinuousMulEquiv.apply_symm_apply]
      · change ((prodEquiv K) ((prodEquiv K).symm (a, c.out))).2 = c.out
        rw [ContinuousMulEquiv.apply_symm_apply]
    simp only [hF, (hsymm _).1, (hsymm _).2]
    rw [integral_mul_const, ← χ.integral_infiniteSchwartz hs0]
  simp only [hc] at h
  have h2 := (χ.hasSum_finiteTestFun hs).mul_left (∏ w, infiniteConst w * χ.infiniteGamma w s)
  rw [globalZeta, h.unique h2, Finset.prod_mul_distrib, prod_infiniteConst, gammaFactor]

end HeckeCharacter

end

end GroundTheory.Global
end

section

open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def partialZetaSum (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) : ℂ :=
  ∑' ξ : Kˣ, f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
    (χ.toIdele (moduleSection w t * (u : IdeleGroup K)) : ℂ)

theorem partialZetaSum_mul (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) {δ : normOneSubgroup K}
    (hδ : δ ∈ diagonalNormOne K) : partialZetaSum w f χ t (u * δ) = partialZetaSum w f χ t u := by
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hδ
  obtain ⟨ξ₀, hξ₀⟩ := hδ
  unfold partialZetaSum
  conv_rhs => rw [← (Equiv.mulRight ξ₀).tsum_eq]
  refine tsum_congr fun ξ ↦ ?_
  have hχ : χ.toIdele (moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K)) =
      χ.toIdele (moduleSection w t * (u : IdeleGroup K)) := by
    rw [Subgroup.coe_mul, ← hξ₀, ← mul_assoc, map_mul, HeckeCharacter.toIdele_diagonal, mul_one]
  have hf : diagonal K ξ * moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K) =
      diagonal K ((Equiv.mulRight ξ₀) ξ) * moduleSection w t * (u : IdeleGroup K) := by
    rw [Subgroup.coe_mul, ← hξ₀, Equiv.coe_mulRight, map_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [hχ, hf]

def partialZetaClass (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : normOneSubgroup K ⧸ diagonalNormOne K → ℂ :=
  Quotient.lift (s := QuotientGroup.leftRel (diagonalNormOne K)) (partialZetaSum w f χ t)
    fun u v h ↦ by
      have h' : u⁻¹ * v ∈ diagonalNormOne K := QuotientGroup.leftRel_apply.1 h
      conv_rhs => rw [← mul_inv_cancel_left u v]
      rw [partialZetaSum_mul w f χ t u h']

def partialZeta (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ c, partialZetaClass w f χ t c ∂normOneClassMeasure K

theorem measurable_partialZetaSum (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) : Measurable (partialZetaSum w f χ t) := by
  refine Measurable.tsum fun ξ ↦ Continuous.measurable ?_
  have hu : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  have hu' : Continuous fun u : normOneSubgroup K ↦
      diagonal K ξ * moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  exact (hf.comp (Units.continuous_val.comp hu')).mul
    (continuous_subtype_val.comp (χ.continuous_toIdele.comp hu))

theorem partialZeta_eq_setIntegral (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    partialZeta w f χ t =
      ∫ u in normOneFundamentalDomain K, partialZetaSum w f χ t u ∂normOneMeasure K := by
  have hm : Measurable (partialZetaClass w f χ t) :=
    QuotientGroup.measurable_from_quotient.2 (measurable_partialZetaSum w hf χ t)
  rw [partialZeta, normOneClassMeasure,
    integral_map QuotientGroup.measurable_coe.aemeasurable hm.aestronglyMeasurable]
  rfl

theorem zetaIntegrand_diagonal_mul (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (s : ℂ) (ξ : Kˣ) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) :
    f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
        (χ.toIdele (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) : ℂ) *
        ((ideleModule K (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) : ℝ) : ℂ) ^ s =
      f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
        (χ.toIdele (moduleSection w t * (u : IdeleGroup K)) : ℂ) * ((t : ℝ) : ℂ) ^ s := by
  have hu : ideleModule K (u : IdeleGroup K) = 1 := u.2
  have hmod : ideleModule K (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) = t := by
    rw [map_mul, map_mul, ideleModule_diagonal, one_mul, ideleModule_moduleSection, hu, mul_one]
  have hχ : χ.toIdele (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) =
      χ.toIdele (moduleSection w t * (u : IdeleGroup K)) := by
    rw [mul_assoc, map_mul, HeckeCharacter.toIdele_diagonal, one_mul]
  simp only [hmod, hχ]

theorem globalZeta_eq_integral_partialZeta (w : InfinitePlace K) {f : 𝔸[K] → ℂ}
    (hf : f ∈ schwartzBruhat K) (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun t ↦ partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s) posRealMeasure ∧
      globalZeta f χ s = ∫ t, partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s ∂posRealMeasure := by
  have hfc := continuous_of_mem_schwartzBruhat hf
  set G : IdeleGroup K → ℂ := fun x ↦ f x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s
    with hGdef
  have hG : Integrable G (ideleMeasure K) := integrable_globalZetaIntegrand hf χ hs
  have hg : Integrable (fun p : normOneSubgroup K × {r : ℝ // 0 < r} ↦
      G ((p.1 : IdeleGroup K) * moduleSection w p.2))
      ((normOneMeasure K).prod posRealMeasure) := by
    rw [← map_normOneSplitting_eq_prod w]
    refine (integrable_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv _).2 ?_
    convert hG using 1
    funext x
    exact congrArg G ((normOneSplitting w).symm_apply_apply x)
  have hae : (fun t ↦ ∫ u, G ((u : IdeleGroup K) * moduleSection w t) ∂normOneMeasure K)
      =ᵐ[posRealMeasure] fun t ↦ partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s := by
    filter_upwards [hg.prod_left_ae] with t ht
    rw [integral_normOneMeasure_eq_setIntegral_tsum ht, partialZeta_eq_setIntegral w hfc,
      ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
    simp only [partialZetaSum]
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ ↦ ?_
    have hx : ((diagonalToNormOne K ξ * u : normOneSubgroup K) : IdeleGroup K) *
        moduleSection w t = diagonal K ξ * moduleSection w t * (u : IdeleGroup K) := by
      rw [Subgroup.coe_mul, coe_diagonalToNormOne, mul_right_comm]
    rw [hx]
    exact zetaIntegrand_diagonal_mul w f χ s ξ t u
  refine ⟨hg.integral_prod_right.congr hae, ?_⟩
  rw [globalZeta, integral_ideleMeasure_eq_integral_normOne w hG]
  exact integral_congr_ae hae

end

end GroundTheory.Global
end

section

namespace GroundTheory.Global

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem exists_mul_mem_integralFiniteAdeles_of_isCompact {S : Set 𝔸ᶠ[K]} (hS : IsCompact S) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ s ∈ S,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d) * s ∈ integralFiniteAdeles (𝓞 K) K := by
  have hint : ∀ r : 𝓞 K,
      algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K r) ∈ integralFiniteAdeles (𝓞 K) K :=
    fun r v ↦ coe_algebraMap_mem_adicCompletionIntegers v r
  let U : {d : 𝓞 K // d ≠ 0} → Set 𝔸ᶠ[K] := fun d ↦
    {s | algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1) * s ∈ integralFiniteAdeles (𝓞 K) K}
  have hUo : ∀ d, IsOpen (U d) := fun d ↦
    isOpen_integralFiniteAdeles.preimage (continuous_const_mul _)
  have hsU : S ⊆ ⋃ d, U d := by
    intro s _
    obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles (R := 𝓞 K) s
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    have hmK : algebraMap (𝓞 K) K m ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hm0
    refine Set.mem_iUnion.mpr ⟨⟨m, hm0⟩, ?_⟩
    have h : algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s =
        algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n) + algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) *
          (s - algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m)) := by
      rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hmK]
      ring
    show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K m) * s ∈ integralFiniteAdeles (𝓞 K) K
    rw [h]
    exact add_mem (hint n) (mul_mem (hint m) hk)
  have hdU : Directed (· ⊆ ·) U := by
    intro d e
    refine ⟨⟨d.1 * e.1, mul_ne_zero d.2 e.2⟩, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · have := mul_mem (hint e.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_comm (algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K d.1)), mul_assoc]
    · have := mul_mem (hint d.1) hs
      show algebraMap K 𝔸ᶠ[K] (algebraMap (𝓞 K) K (d.1 * e.1)) * s ∈ integralFiniteAdeles (𝓞 K) K
      rwa [map_mul, map_mul, mul_assoc]
  have : Nonempty {d : 𝓞 K // d ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  obtain ⟨d, hd⟩ := hS.elim_directed_cover U hUo hsU hdU
  exact ⟨d.1, d.2, fun s hs ↦ hd hs⟩

theorem summable_ite_mem_of_summable_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {h : mixedSpace K → ℝ} (hh : Summable fun α : idealLattice K J ↦ h α) :
    Summable fun ξ : K ↦
      if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0 := by
  set e := idealLatticeEquiv J
  let g : idealLattice K J → K := fun α ↦ ((e.symm α : _) : K)
  have hinj : Function.Injective g := fun α β hαβ ↦ e.symm.injective (Subtype.ext hαβ)
  have hsupp : ∀ ξ ∉ Set.range g,
      (if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then h (mixedEmbedding K ξ) else 0) = 0 := by
    intro ξ hξ
    rw [if_neg]
    intro hm
    exact hξ ⟨e ⟨ξ, hm⟩, by simp [g]⟩
  rw [← hinj.summable_iff hsupp]
  convert hh using 1
  funext α
  change (if ((e.symm α : _) : K) ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
    h (mixedEmbedding K ((e.symm α : _) : K)) else 0) = h α
  rw [if_pos (show ((e.symm α : _) : K) ∈ (J : FractionalIdeal (𝓞 K)⁰ K) from (e.symm α).2)]
  have he := coe_idealLatticeEquiv J (e.symm α)
  rw [Equiv.apply_symm_apply] at he
  rw [he]

theorem summable_inv_one_add_norm_pow_idealLattice (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun α : idealLattice K J ↦
      ((1 + ‖(α : mixedSpace K)‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹ := by
  have hs := ZLattice.summable_norm_pow_inv (L := idealLattice K J)
    (Module.finrank ℤ (idealLattice K J) + 1) (by omega)
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLattice K J)).compl_mem_cofinite] with ℓ hℓ
  have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  rw [Real.norm_of_nonneg (by positivity), inv_pow]
  gcongr
  change ‖ℓ‖ ≤ 1 + ‖ℓ‖
  linarith

theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K,
      ‖schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by

  set S : Set 𝔸ᶠ[K] := (fun p : IdeleGroup K × 𝔸ᶠ[K] ↦
      ((IdeleGroup.toFinite K p.1⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * p.2) ''
    (C ×ˢ (b +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])))
  have hS : IsCompact S := (hC.prod ((isCompact_idealFiniteAdeles I).vadd b)).image
    ((Units.continuous_val.comp ((IdeleGroup.continuous_toFinite (K := K)).comp
      (continuous_inv.comp continuous_fst))).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))
  have hJ : ∀ a ∈ C, ∀ ξ : K,
      ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
        idealFiniteAdeles I → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a ha ξ hξ
    have hmem : algebraMap K 𝔸ᶠ[K] ξ ∈ S := by
      refine ⟨(a, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ),
        ⟨ha, mem_vadd_idealFiniteAdeles.mpr hξ⟩, ?_⟩
      simp only [map_inv, Units.inv_mul_cancel_left]
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

  set k := Module.finrank ℤ (idealLattice K J) + 1
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ k
  have hcont : Continuous fun a : IdeleGroup K ↦ ‖homeomorphMixedSpace K
      ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ :=
    continuous_norm.comp ((homeomorphMixedSpace K).continuous.comp (Units.continuous_val.comp
      ((IdeleGroup.continuous_toInfinite (K := K)).comp continuous_inv)))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
      A * B' ^ k * ((1 + ‖mixedEmbedding K ξ‖) ^ k)⁻¹ else 0, ?_, ?_⟩
  · exact summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹)
      ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (A * B' ^ k))
  intro a ha ξ
  set c := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set c' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  have hcc : c' * c = 1 := by
    rw [← homeomorphMixedSpace_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
      Units.val_one, homeomorphMixedSpace_apply, map_one]
  have hval : schwartzBruhatTensor φ (cosetIndicator I b) (a • algebraMap K 𝔸[K] ξ) =
      φ (c * mixedEmbedding K ξ) * cosetIndicator I b
        (((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ) := by
    have h1 : (a • algebraMap K 𝔸[K] ξ).1 = ((IdeleGroup.toInfinite K a : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) * algebraMap K (InfiniteAdeleRing K) ξ := rfl
    have h2 : (a • algebraMap K 𝔸[K] ξ).2 =
        ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ := rfl
    simp only [schwartzBruhatTensor]
    rw [h1, h2, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]
  rw [hval, cosetIndicator_apply]
  beta_reduce
  split_ifs with hm hJm hJm
  · rw [mul_one]
    set x := mixedEmbedding K ξ
    have hx : ‖x‖ ≤ B' * ‖c * x‖ := by
      calc ‖x‖ = ‖c' * (c * x)‖ := by rw [← mul_assoc, hcc, one_mul]
        _ ≤ ‖c'‖ * ‖c * x‖ := norm_mul_le _ _
        _ ≤ B' * ‖c * x‖ := by
          gcongr
          exact ((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _)
    have key : 1 + ‖x‖ ≤ B' * (1 + ‖c * x‖) := by nlinarith [norm_nonneg (c * x)]
    calc ‖φ (c * x)‖ ≤ A * ((1 + ‖c * x‖) ^ k)⁻¹ := hφ _
      _ = A * (B' ^ k * ((B' * (1 + ‖c * x‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc (B' ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ A * (B' ^ k * ((1 + ‖x‖) ^ k)⁻¹) := by gcongr
      _ = A * B' ^ k * ((1 + ‖x‖) ^ k)⁻¹ := by ring
  · exact absurd (hJ a ha ξ hm) hJm
  · rw [mul_zero, norm_zero]
    positivity
  · rw [mul_zero, norm_zero]

theorem exists_summable_bound_smul_algebraMap {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ ξ : K, ‖F (a • algebraMap K 𝔸[K] ξ)‖ ≤ u ξ := by
  have hF' := schwartzBruhat_le_span_cosetIndicator hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw, fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

end

end GroundTheory.Global
end
