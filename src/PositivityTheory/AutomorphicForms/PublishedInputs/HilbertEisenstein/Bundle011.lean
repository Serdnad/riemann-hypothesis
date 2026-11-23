module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle008
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierInfinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

variable {F : Type} [Field F] [NumberField F]

theorem ordI_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) : ordI v w.asIdeal = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).1 h0
  exact h (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))

theorem ordI_top (v : HeightOneSpectrum (𝓞 F)) : ordI v (⊤ : Ideal (𝓞 F)) = 0 := by
  by_contra h0
  have h1 := (Associates.count_ne_zero_iff_dvd top_ne_bot v.irreducible).1 h0
  exact v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h1))

open Classical in
theorem ordI_pow (v w : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    ordI v (w.asIdeal ^ k) = if v = w then k else 0 := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, ordI_top]; split_ifs <;> rfl
  | succ k ih =>
    rw [pow_succ, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ w.ne_bot) w.ne_bot, ih]
    by_cases h : v = w
    · rw [if_pos h, if_pos h, h, Fresh.ordI_asIdeal_self]
    · rw [if_neg h, if_neg h, ordI_ne h]

theorem prodS_ne_bot (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ) :
    (∏ w ∈ T, w.asIdeal ^ p w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro w _
  exact pow_ne_zero _ w.ne_bot

open Classical in
theorem ordI_prodS (T : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F) → ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : ordI v (∏ w ∈ T, w.asIdeal ^ p w) = if v ∈ T then p v else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Ideal.one_eq_top, ordI_top]; simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Fresh.ordI_mul_of_ne_bot v (pow_ne_zero _ a.ne_bot) (prodS_ne_bot T p), ordI_pow, ih]
    by_cases h1 : v = a
    · subst h1
      simp [ha]
    · by_cases h2 : v ∈ T
      · simp [h1, h2]
      · simp [h1, h2]

theorem eq_of_ordI {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w : HeightOneSpectrum (𝓞 F), ordI w I = ordI w J) :
    I = J := by
  classical
  have key : Associates.mk I = Associates.mk J := by
    refine Associates.eq_of_eq_counts (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) fun p hp => ?_
    obtain ⟨P, rfl⟩ := Associates.exists_rep p
    have hP : Irreducible P := Associates.irreducible_mk.1 hp
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, Ideal.isPrime_of_prime hP.prime, hP.ne_zero⟩
    have := h v
    unfold ordI at this
    convert this using 2
  exact associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 key)

theorem ordI_le_of_dvd {r m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (h : r ∣ m) (w : HeightOneSpectrum (𝓞 F)) :
    ordI w r ≤ ordI w m := by
  obtain ⟨s, rfl⟩ := h
  have hr : r ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.bot_mul])
  have hs : s ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
  rw [Fresh.ordI_mul_of_ne_bot w hr hs]
  exact Nat.le_add_right _ _

theorem dvd_fin {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) : {r : Ideal (𝓞 F) | r ∣ m}.Finite := by
  have := UniqueFactorizationMonoid.fintypeSubtypeDvd m hm
  exact Set.finite_coe_iff.1 (Finite.of_fintype {r // r ∣ m})


open Classical in
def ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℕ :=
  if h : w ∈ S then p ⟨w, h⟩ else 0

theorem ordI_prod_ext (S : Finset (HeightOneSpectrum (𝓞 F))) (p : S → ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    ordI v (∏ w ∈ S, w.asIdeal ^ ext S p w) = ext S p v := by
  classical
  rw [ordI_prodS]
  unfold ext
  split_ifs <;> rfl

theorem divS_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) {m : Ideal (𝓞 F)} (hm : m ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ w ∉ S, ordI w m = 0) :
    divS ω c m = ∏ w ∈ S, ∑ j ∈ Finset.range (ordI w m + 1), L4.chiW ω c w ^ j := by
  classical
  rw [← Finset.prod_coe_sort S, Finset.prod_univ_sum]
  unfold divS
  rw [finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm)]
  symm
  refine Finset.sum_nbij' (fun p => ∏ w ∈ S, w.asIdeal ^ ext S p w) (fun r => fun w : S => ordI w.1 r) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have hp' : ∀ w : S, p w ≤ ordI w.1 m := fun w => by
      have := Fintype.mem_piFinset.1 hp w
      rw [Finset.mem_range] at this
      omega
    refine ⟨∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w), ?_⟩
    have hne : (∏ w ∈ S, w.asIdeal ^ ext S p w) * (∏ w ∈ S, w.asIdeal ^ (ordI w m - ext S p w)) ≠ ⊥ := by
      rw [Ne, Ideal.mul_eq_bot, not_or]
      exact ⟨prodS_ne_bot _ _, prodS_ne_bot _ _⟩
    refine eq_of_ordI hm hne fun v => ?_
    rw [Fresh.ordI_mul_of_ne_bot v (prodS_ne_bot _ _) (prodS_ne_bot _ _), ordI_prod_ext, ordI_prodS]
    by_cases hv : v ∈ S
    · rw [if_pos hv]
      have h1 : ext S p v = p ⟨v, hv⟩ := by unfold ext; rw [dite_eq_left hv]
      have h2 : p ⟨v, hv⟩ ≤ ordI v m := hp' ⟨v, hv⟩
      rw [h1]
      omega
    · rw [if_neg hv, hS v hv]
      unfold ext
      rw [dite_eq_right hv]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    rw [Fintype.mem_piFinset]
    intro w
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (ordI_le_of_dvd hm hr w)
  · intro p _
    funext w
    rw [ordI_prod_ext]
    unfold ext
    rw [dite_eq_left w.2]
  · intro r hr
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hr
    have hr0 : r ≠ ⊥ := fun h0 => hm (by rw [h0] at hr; exact zero_dvd_iff.1 hr)
    refine eq_of_ordI (prodS_ne_bot _ _) hr0 fun v => ?_
    rw [ordI_prod_ext]
    unfold ext
    split_ifs with hv
    · rfl
    · have := ordI_le_of_dvd hm hr v
      rw [hS v hv] at this
      omega
  · intro p _
    unfold chiI
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [ordI_prod_ext]
      unfold ext L4.chiW
      rw [dite_eq_left w.2]
    · intro v hv
      by_contra hvS
      apply hv
      beta_reduce
      rw [ordI_prod_ext]
      unfold ext
      rw [dite_eq_right fun h => hvS (Finset.mem_coe.2 h), pow_zero]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.DivisorSumOrder

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open DivisorSumOrder

theorem coefficient_divisor_holds : CoefDiv := by
  intro F _ _ _ ω c z m S hz hS
  classical
  unfold coefAt
  by_cases hpos : ∀ w ∈ S, 0 ≤ m w
  · rw [if_pos hpos]
    have hex : ∃ 𝔪, GenD z 𝔪 := by
      refine ⟨∏ w ∈ S, w.asIdeal ^ (m w).toNat, prodS_ne_bot _ _, fun w => ?_⟩
      rw [hz w, ordI_prodS]
      congr 1
      by_cases hw : w ∈ S
      · rw [if_pos hw, Int.toNat_of_nonneg (hpos w hw)]; rfl
      · rw [if_neg hw, hS w hw]; rfl
    rw [dite_eq_left hex]
    have hspec := hex.choose_spec
    set 𝔪 := hex.choose
    have hord : ∀ w, (ordI w 𝔪 : ℤ) = m w := by
      intro w
      have h := (hspec.2 w).symm.trans (hz w)
      rw [WithZero.exp_inj] at h
      unfold dd at h
      omega
    rw [divS_eq ω c hspec.1 S fun w hw => by have := hord w; rw [hS w hw] at this; omega]
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 2
    have := hord w
    omega
  · rw [if_neg hpos, dite_eq_right]
    rintro ⟨𝔪, -, h𝔪⟩
    apply hpos
    intro w _
    have h := (h𝔪 w).symm.trans (hz w)
    rw [WithZero.exp_inj] at h
    unfold dd at h
    omega

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

open NumberField.mixedEmbedding NumberField.InfinitePlace Function
open scoped SchwartzMap FourierTransform Real Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem mem_units_of_isUnitAt (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    x ∈ (Submonoid.ofClass (w.adicCompletionIntegers F)).units := by
  rw [Submonoid.mem_units_iff]
  have hx' : Valued.v (x : w.adicCompletion F) = 1 := hx
  refine ⟨?_, ?_⟩
  · change (x : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx']
  · change ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]

theorem integral_arch_one (a y : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
        (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      ((a : ℂ) + (y : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) := by
  set c1 : ℂ := (a : ℂ) * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  set c2 : ℂ := Complex.I * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  have hpt : ∀ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
      (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      c1 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t) +
        c2 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t) := by
    intro t
    simp only [c1, c2, realGaussian, realGaussianOdd]
    have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
        Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (t : ℂ) ^ 2) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this]
    ring
  have hce : Continuous fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hg : Continuous realGaussian := by unfold realGaussian; fun_prop
  have hgo : Continuous realGaussianOdd := by unfold realGaussianOdd; fun_prop
  have hi1 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t :=
    integrable_realGaussian.norm.mono' (hce.mul hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hi2 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t :=
    integrable_realGaussianOdd.norm.mono' (hce.mul hgo).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hf1 : 𝓕 realGaussian y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  have hf2 : 𝓕 realGaussianOdd y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  simp only [hpt]
  rw [integral_add (hi1.const_mul c1) (hi2.const_mul c2), integral_const_mul, integral_const_mul, ← hf1, ← hf2,
    fourier_realGaussian, fourier_realGaussianOdd]
  simp only [c1, c2, realGaussian, realGaussianOdd]
  have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) =
      Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (y : ℂ) ^ 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem mixedFourier_archSchwartz (a : InfinitePlace F → ℝ) (Z : Ad F) :
    mixedFourier F (archSchwartz a) (homeomorphMixedSpace F Z.1) =
      ∏ v, (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  set m := homeomorphMixedSpace F Z.1
  set A : ∀ w : {w : InfinitePlace F // IsReal w}, ℝ → ℂ := fun w t => ((𝐞 (-(t * m.1 w)) : Circle) : ℂ) *
    ((((a w.1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + (t : ℂ) ^ 2)))
  set B : ∀ w : {w : InfinitePlace F // IsComplex w}, ℂ → ℂ := fun _ _ => 1
  have hint : ∀ x : mixedSpace F, 𝐞 (-mixedTraceForm F x m) • archSchwartz a x =
      (∏ w, A w (x.1 w)) * ∏ w, B w (x.2 w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, HeckeCharacter.fourierChar_neg_mixedTraceForm, archSchwartz_eq_prod]
    simp only [A, B, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty,
      mul_one, Finset.prod_mul_distrib]
  have hA : ∀ w : {w : InfinitePlace F // IsReal w}, ∫ t, A w t =
      (((a w.1 : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ) ^ 2)) :=
    fun w => integral_arch_one (a w.1) (m.1 w)
  rw [mixedFourier_apply, selfDualMeasure, integral_smul_measure, Measure.volume_eq_prod]
  simp only [hint]
  rw [integral_prod_mul (f := fun x : {w : InfinitePlace F // IsReal w} → ℝ ↦ ∏ w, A w (x w))
    (g := fun z : {w : InfinitePlace F // IsComplex w} → ℂ ↦ ∏ w, B w (z w)),
    integral_fintype_prod_volume_eq_prod, integral_fintype_prod_volume_eq_prod]
  simp only [hA, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty, mul_one,
    IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, ENNReal.toReal_one, one_smul]
  exact prod_real (fun v => (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)))

theorem adelicFourier_slice {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A Z : Ad F) :
    adelicFourier F (slice c A) Z =
      ((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ) * kernF c A Z := by
  classical
  rw [slice_eq hc A, adelicFourier_smul, Pi.smul_apply, adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor,
    mixedFourierSchwartz_apply, finiteFourier_cosetIndicator, mixedFourier_archSchwartz, smul_eq_mul, one_mul]
  unfold kernF
  rw [Set.indicator_apply]
  simp only [SetLike.mem_coe, Pi.one_apply]
  rw [mem_dual_iff hc]
  have hZ : Z.2 = pFin F Z := rfl
  rw [hZ]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)
    · simp only [h1, h2, and_self, implies_true, ↓reduceIte]; ring
    · simp only [h1, h2, implies_true, true_and, ↓reduceIte]; ring
  · simp only [h1, false_and, ↓reduceIte]; ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

theorem finite_expansion_holds : SFin := by
  intro F _ _ _ ω c H
  set χ : (FiniteAdeleRing (𝓞 F) F)ˣ →* ℂˣ := ω.1.comp IdeleGroup.ofFinite with hχdef
  have hχ : Continuous χ := ω.2.1.comp IdeleGroup.continuous_ofFinite
  refine (IdeleGroup.finite_support_conductorExponentAt Complex.units_noSmallSubgroups χ hχ).subset ?_
  intro w hw
  rw [Function.mem_support]
  intro h0
  apply hw
  have hk := (IdeleGroup.conductorExponentAt_eq_zero_iff Complex.units_noSmallSubgroups χ hχ w).1 h0
  have hmem : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
    intro x hx _
    have h1 := hk (mem_units_of_isUnitAt w x hx)
    rw [MonoidHom.mem_ker] at h1
    exact h1
  exact Nat.le_zero.1 ((H.cond w).2 hmem)

theorem kernel_expansion_holds : SKern := by
  intro F _ _ _ c hc
  refine ⟨((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ), ?_,
    fun A Z => adelicFourier_slice hc A Z⟩
  rw [Complex.ofReal_ne_zero, finiteAdeleMeasure_idealFiniteAdeles_toReal]
  refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact (levelIdeal c).ne_zero
  · rw [NNReal.coe_ne_zero, Ne, NNReal.sqrt_eq_zero, nnnorm_eq_zero]
    exact_mod_cast NumberField.discr_ne_zero F

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end
