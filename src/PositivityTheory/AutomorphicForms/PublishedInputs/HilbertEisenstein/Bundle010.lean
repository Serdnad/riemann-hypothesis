module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import GroundTheory.GlobalFields.TateThesis.Bundle008
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Mathlib.Tactic.TypeStar
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.CharpolyCoeffsInSubalgebra

open L5

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem hasTemperateGrowth_wpoly : (wpoly F).HasTemperateGrowth := by
  unfold wpoly
  refine hasTemperateGrowth_finsetProd _ fun v _ => ?_
  have hL := ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj
    (⟨v, IsTotallyReal.isReal v⟩ : {w : InfinitePlace F // IsReal w}) :
      ({w : InfinitePlace F // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ
        ({w : InfinitePlace F // IsReal w} → ℝ) ({w : InfinitePlace F // IsComplex w} → ℂ))) :
          mixedSpace F →L[ℝ] ℂ)).hasTemperateGrowth
  have h1 : (fun _ : mixedSpace F => (1 : ℂ)).HasTemperateGrowth := by fun_prop
  exact h1.add (hL.pow 2)

instance isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩

def rp (v : InfinitePlace F) : {w : InfinitePlace F // IsReal w} := ⟨v, IsTotallyReal.isReal v⟩

theorem gaussian_weight_apply (x : mixedSpace F) :
    phi1 F x = ((∏ v : InfinitePlace F, ((1 + (x.1 (rp v)) ^ 2) * Real.exp (-Real.pi * (x.1 (rp v)) ^ 2)) : ℝ) : ℂ) := by
  rw [phi1, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_wpoly,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]
  have hc : ∑ w : {w : InfinitePlace F // IsComplex w}, ‖x.2 w‖ ^ 2 = 0 := Finset.sum_of_isEmpty _
  have hs : ∑ w : {w : InfinitePlace F // IsReal w}, x.1 w ^ 2 = ∑ v : InfinitePlace F, x.1 (rp v) ^ 2 := by
    refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _ fun w => ?_
    rfl
  rw [hc, mul_zero, add_zero, hs, Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_prod, wpoly]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    push_cast
    rfl

theorem pos_factor (a : ℝ) : 0 < (1 + a ^ 2) * Real.exp (-Real.pi * a ^ 2) :=
  mul_pos (by positivity) (Real.exp_pos _)

theorem gaussian_weight_real_nonneg (x : mixedSpace F) : ∃ r : ℝ, 0 ≤ r ∧ phi1 F x = (r : ℂ) :=
  ⟨_, (Finset.prod_pos fun v _ => pos_factor _).le, gaussian_weight_apply x⟩

theorem norm_real_test_matrix (x : mixedSpace F) :
    ‖phi1 F x‖ = ∏ v : InfinitePlace F, ((1 + (x.1 (rp v)) ^ 2) * Real.exp (-Real.pi * (x.1 (rp v)) ^ 2)) := by
  rw [gaussian_weight_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Finset.prod_pos fun v _ => pos_factor _)]

theorem hms_fst (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    (homeomorphMixedSpace F x).1 (rp v) = (UpperTheory.V.TR.infEq F).symm x v := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal _ (x v) =
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.symm (x v)
  rw [RingEquiv.symm_symm, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]

theorem place_bound (a z : ℝ) :
    |a + z| * Real.exp (-Real.pi * (a ^ 2 + z ^ 2)) ≤
      ((1 + a ^ 2) * Real.exp (-Real.pi * a ^ 2)) * ((1 + z ^ 2) * Real.exp (-Real.pi * z ^ 2)) := by
  have he : Real.exp (-Real.pi * (a ^ 2 + z ^ 2)) = Real.exp (-Real.pi * a ^ 2) * Real.exp (-Real.pi * z ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : |a + z| ≤ (1 + a ^ 2) * (1 + z ^ 2) := by
    have e1 := sq_abs a
    have e2 := sq_abs z
    have e3 := sq_nonneg (abs a - 1 / 2)
    have e4 := sq_nonneg (abs z - 1 / 2)
    have e5 := mul_nonneg (sq_nonneg a) (sq_nonneg z)
    have e6 := abs_add_le a z
    nlinarith
  rw [he]
  have hp1 := Real.exp_pos (-Real.pi * a ^ 2)
  have hp2 := Real.exp_pos (-Real.pi * z ^ 2)
  calc |a + z| * (Real.exp (-Real.pi * a ^ 2) * Real.exp (-Real.pi * z ^ 2))
      ≤ ((1 + a ^ 2) * (1 + z ^ 2)) * (Real.exp (-Real.pi * a ^ 2) * Real.exp (-Real.pi * z ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := by ring

theorem norm_place (a z : ℝ) :
    ‖((a : ℂ) + (z : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (z : ℂ) ^ 2))‖ =
      |a + z| * Real.exp (-Real.pi * (a ^ 2 + z ^ 2)) := by
  have h : -(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (z : ℂ) ^ 2) = ((-Real.pi * (a ^ 2 + z ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [h, norm_mul, Complex.norm_exp_ofReal, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]

theorem mem_one_of_condA {c : HeightOneSpectrum (𝓞 F) → ℕ} {A : Ad F}
    (h : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))) :
    A.2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) := by
  rw [mem_idealFiniteAdeles]
  intro v
  rw [Units.val_one, FractionalIdeal.count_one, neg_zero]
  exact (h v).trans (WithZero.exp_le_exp.2 (by omega))

theorem standard_hermitian_apply (x : Ad F) : H1 F x = phi1 F (homeomorphMixedSpace F x.1) * cosetIndicator 1 0 x.2 := rfl

theorem cosetIndicator_one_of_mem {z : Af F} (h : z ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) :
    cosetIndicator 1 0 z = 1 := by
  rw [cosetIndicator_apply, sub_zero, if_pos h]

theorem cosetIndicator_real (z : Af F) : ∃ r : ℝ, 0 ≤ r ∧ cosetIndicator (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) 0 z = (r : ℂ) := by
  rw [cosetIndicator_apply]
  split_ifs
  · exact ⟨1, zero_le_one, by simp⟩
  · exact ⟨0, le_rfl, by simp⟩

theorem arch_norm (A Z : Ad F) :
    ‖∏ v, (((UpperTheory.V.TR.pInf F A v : ℂ) + (UpperTheory.V.TR.pInf F Z v : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((UpperTheory.V.TR.pInf F A v : ℂ) ^ 2 + (UpperTheory.V.TR.pInf F Z v : ℂ) ^ 2)))‖ ≤
      ‖phi1 F (homeomorphMixedSpace F A.1)‖ * ‖phi1 F (homeomorphMixedSpace F Z.1)‖ := by
  rw [norm_prod, norm_real_test_matrix, norm_real_test_matrix, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => ?_
  rw [norm_place, hms_fst, hms_fst]
  exact place_bound _ _

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.CharpolyCoeffsInSubalgebra

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L5 CharpolyCoeffsInSubalgebra

theorem dominating_function_holds : P5dom := by
  intro F _ _ _
  refine ⟨schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat _ _), ?_, ?_⟩
  · intro x
    obtain ⟨r, hr, hr'⟩ := gaussian_weight_real_nonneg (homeomorphMixedSpace F x.1)
    obtain ⟨s, hs, hs'⟩ := cosetIndicator_real (F := F) x.2
    rw [standard_hermitian_apply, hr', hs', ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr hs)]
  · intro c A Z Z' h1 h2
    unfold kernF
    split_ifs with h
    · rw [norm_mul, Circle.norm_coe, mul_one, standard_hermitian_apply, standard_hermitian_apply, norm_mul, norm_mul,
        cosetIndicator_one_of_mem (mem_one_of_condA h.1), cosetIndicator_one_of_mem (h2 h.2), norm_one, mul_one,
        mul_one, h1]
      exact arch_norm A Z
    · rw [mul_zero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding WithZero

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.VanishingLemma

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem finId_val' (yf : (Af F)ˣ) : ((finId F yf : (Ad F)ˣ) : Ad F) = (1, (yf : Af F)) := by
  change 1 - sFin F 1 + sFin F yf.val = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  · change (1 : Af F) - 1 + (yf : Af F) = _
    rw [sub_self, zero_add]

theorem exists_m {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      w.intValuation m ≤ exp (-((c w : ℤ) + dd w)) := by
  classical
  have hπ : ∀ w : HeightOneSpectrum (𝓞 F), ∃ x ∈ w.asIdeal, x ≠ 0 := fun w =>
    Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  choose π hπmem hπ0 using hπ
  obtain ⟨δ, hδmem, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  set S := hc.toFinset
  set p : 𝓞 F := ∏ w ∈ S, π w ^ c w
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hπ0 w)
  refine ⟨δ * p, mul_ne_zero hδ0 hp0, fun w => ?_⟩
  have hδv : w.intValuation δ ≤ exp (-dd w) := by
    have h := intValuation_le_of_mem_ideal w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) hδmem
    rw [FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))] at h
    exact h
  have hpv : w.intValuation p ≤ exp (-(c w : ℤ)) := by
    refine (w.intValuation_le_pow_iff_mem p (c w)).2 ?_
    by_cases hw : w ∈ S
    · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun w => π w ^ c w) hw
      rw [show p = π w ^ c w * q from hq]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hπmem w) _)
    · have : c w = 0 := by
        by_contra h
        exact hw (hc.mem_toFinset.2 h)
      rw [this, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  rw [map_mul, neg_add, add_comm (-(c w : ℤ)), exp_add]
  exact mul_le_mul' hδv hpv

theorem exp_neg_mul_le_one_iff (n : ℤ) (a : ℤᵐ⁰) : exp (-n) * a ≤ 1 ↔ a ≤ exp n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rw [← exp_log ha, ← exp_add, ← exp_zero, exp_le_exp, exp_le_exp]
  omega

theorem isClosed_le_exp (w : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    IsClosed {z : w.adicCompletion F | Valued.v z ≤ exp n} := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπ0 : (π : w.adicCompletion F) ≠ 0 := by
    intro h
    have h' : Valued.v ((π : F) : w.adicCompletion F) = 0 := by rw [h, map_zero]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at h'
    exact exp_ne_zero h'
  set u : w.adicCompletion F := (π : w.adicCompletion F) ^ n
  have hu : Valued.v u = exp (-n) := by
    rw [map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← exp_zsmul]
    congr 1
    simp
  have heq : {z : w.adicCompletion F | Valued.v z ≤ exp n} =
      (fun z => u * z) ⁻¹' {z : w.adicCompletion F | Valued.v z ≤ 1} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, hu, exp_neg_mul_le_one_iff]
  rw [heq]
  exact (Valued.isClopen_integer (w.adicCompletion F)).isClosed.preimage (continuous_const.mul continuous_id)

theorem continuous_pInf_apply (v : InfinitePlace F) : Continuous fun x : Ad F => UpperTheory.V.TR.pInf F x v := by
  simp only [L2.pInf_apply_eq]
  exact ((continuous_apply _).comp continuous_fst).comp ((homeomorphMixedSpace F).continuous.comp continuous_fst)

theorem isClosed_cond {X : Type*} [TopologicalSpace X] {f : X → Ad F} (hf : Continuous f) (n : HeightOneSpectrum (𝓞 F) → ℤ) :
    IsClosed {p | ∀ w, Valued.v (pLoc F w (pFin F (f p))) ≤ exp (n w)} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun w => (isClosed_le_exp w (n w)).preimage ?_
  exact (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp hf)

theorem measurable_kernF_comp {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (c : HeightOneSpectrum (𝓞 F) → ℕ) {A Z : X → Ad F} (hA : Continuous A) (hZ : Continuous Z) :
    Measurable fun p => kernF c (A p) (Z p) := by
  classical
  unfold kernF
  refine Measurable.mul (Continuous.measurable ?_) (Measurable.ite ?_ (Continuous.measurable ?_) measurable_const)
  · refine continuous_finsetProd _ fun v _ => ?_
    have h1 : Continuous fun p => (UpperTheory.V.TR.pInf F (A p) v : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hA)
    have h2 : Continuous fun p => (UpperTheory.V.TR.pInf F (Z p) v : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hZ)
    exact (h1.add h2).mul (Complex.continuous_exp.comp (continuous_const.mul ((h1.pow 2).add (h2.pow 2))))
  · refine ((isClosed_cond hA fun w => -(c w : ℤ)).inter (isClosed_cond hZ fun w => (c w : ℤ) + dd w)).measurableSet
  · exact continuous_subtype_val.comp (continuous_finiteAdelicChar.comp (continuous_snd.comp hZ))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.VanishingLemma

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open VanishingLemma

theorem measure_bound_holds : P5mu := by
  intro F _ _ _ c hc
  obtain ⟨m, hm0, hmv⟩ := exists_m hc
  have hmF : ((m : 𝓞 F) : F) ≠ 0 := by
    simpa using hm0
  set mu : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom (Units.mk0 _ hmF)
  refine ⟨finId F mu, fun Z => ?_, fun Z hZ => ?_⟩
  · rw [Units.smul_def, finId_val']
    change (1 : InfiniteAdeleRing F) * Z.1 = Z.1
    rw [one_mul]
  · rw [Units.smul_def, finId_val', mem_idealFiniteAdeles]
    intro w
    rw [Units.val_one, FractionalIdeal.count_one, neg_zero, exp_zero]
    change Valued.v ((((algebraMap (𝓞 F) F m : F)) : w.adicCompletion F) * Z.2 w) ≤ 1
    rw [map_mul, valued_coe_algebraMap]
    have h1 := hmv w
    have h2 := hZ w
    change Valued.v (Z.2 w) ≤ _ at h2
    calc w.intValuation m * Valued.v (Z.2 w) ≤ exp (-((c w : ℤ) + dd w)) * exp ((c w : ℤ) + dd w) :=
          mul_le_mul' h1 h2
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

theorem measurability_holds : P5meas := by
  intro F _ _ _ c κ hκ Y ξ
  unfold coefK
  refine Measurable.tsum fun a => ?_
  have hτ : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => tau p.1 p.2 * diagonal F a :=
    (((continuous_moduleSection (w0 F)).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul continuous_const
  simp only [kern, hκ]
  refine Measurable.mul (Continuous.measurable ?_) (measurable_const.mul ?_)
  · have hm : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        ((IdeleGroup.ideleModule F (tau p.1 p.2 * diagonal F a) : {r : ℝ // 0 < r}) : ℝ) :=
      continuous_subtype_val.comp ((IdeleGroup.continuous_ideleModule (K := F)).comp hτ)
    exact (Complex.continuous_ofReal.comp hm).inv₀ fun p => Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F _).2.ne'
  · refine measurable_kernF_comp c ?_ ?_
    · exact (Units.continuous_val.comp hτ).mul continuous_const
    · simp only [Units.smul_def]
      exact (Units.continuous_val.comp hτ.inv).mul continuous_const

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection


open Classical in
def finK (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (b : (Af F)ˣ) : ℂ :=
  if (∀ w, Valued.v (pLoc F w ((b : Af F) * (yf : Af F))) ≤ WithZero.exp (-(c w : ℤ))) ∧
      (∀ w, Valued.v (pLoc F w (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ)) ≤
        WithZero.exp ((c w : ℤ) + dd w))
  then ((finiteAdelicChar F (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ) : Circle) : ℂ) else 0

def ωF (ω : HChar F) (b : (Af F)ˣ) : ℂ := ((ω.1 (ofFinite b) : ℂˣ) : ℂ)

def qc (ω : HChar F) : QuasiCharacter F where
  toMonoidHom := QuotientGroup.lift _ ω.1 (by
    rintro _ ⟨a, rfl⟩
    exact ω.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ω.2.1

theorem norm_qc (ω : HChar F) (h : IsOfFinOrder ω) (c : GroundTheory.Global.IdeleClassGroup F) :
    ‖((qc ω c : ℂˣ) : ℂ)‖ = 1 := by
  induction c using QuotientGroup.induction_on with
  | H x => exact L2.norm_omega_eq_one h x

def hc (ω : HChar F) (h : IsOfFinOrder ω) : HeckeCharacter F := QuasiCharacter.toUnitary (qc ω) (norm_qc ω h)

theorem hc_toIdele (ω : HChar F) (h : IsOfFinOrder ω) (x : IdeleGroup F) :
    (((hc ω h).toIdele x : Circle) : ℂ) = ((ω.1 x : ℂˣ) : ℂ) := rfl

def xiF (ξ : Fˣ) : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom ξ

def ordAt (b : (Af F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : ℤ := ord (pLoc F v (b : Af F))


open Classical in
def locF (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) : ℂ :=
  (if Valued.v ((a : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤ WithZero.exp (-(c v : ℤ)) ∧
      Valued.v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ξ) ≤
        WithZero.exp ((c v : ℤ) + dd v)
    then (localAdelicChar F v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) ξ) : ℂ) else 0) * ((ω.loc v a : ℂˣ) : ℂ)⁻¹

def cst (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c v = 0 then ((ω.val v : ℂˣ) : ℂ) ^ (-dd v) else
    ∫ x in ordShell (v.adicCompletion F) (-((c v : ℤ) + dd v)), ((ω.loc v x : ℂˣ) : ℂ) *
      (localAdelicChar F v (x : v.adicCompletion F) : ℂ) ∂multHaar (v.adicCompletion F)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 GroundTheory.Automorphic.GodementSection

def InvSubst : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (f : (v.adicCompletion F)ˣ → ℂ) (t : (v.adicCompletion F)ˣ),
    (Integrable f (multHaar (v.adicCompletion F)) ↔
      Integrable (fun x => f (t * x⁻¹)) (multHaar (v.adicCompletion F))) ∧
    ∫ a, f a ∂multHaar (v.adicCompletion F) = ∫ x, f (t * x⁻¹) ∂multHaar (v.adicCompletion F)

def LocInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (v : HeightOneSpectrum (𝓞 F)),
    Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F)) ∧
    ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F) =
      ((ω.loc v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ) : ℂˣ) : ℂ)⁻¹ *
        if ordAt (xiF ξ * yf) v + dd v < 0 then 0 else
          cst ω c v * ∑ j ∈ Finset.range ((ordAt (xiF ξ * yf) v + dd v).toNat + 1), chiW ω c v ^ j

def OmegaProd : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (b : (Af F)ˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ IsIntegralUnitAt b w) →
    ωF ω b = ∏ v ∈ S, ((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ)

def FinSplit : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ dd w = 0 ∧ IsIntegralUnitAt yf w ∧ IsIntegralUnitAt (xiF ξ) w) →
    (∀ v, Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F))) →
    Integrable (fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹) (finiteIdeleMeasure F) ∧
      ∫ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ ∂finiteIdeleMeasure F =
        ∏ v ∈ S, ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F)

def OmegaPos : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ ξ : Fˣ, (∀ v, 0 < reAt v (ξ : F)) → ωF ω (xiF ξ) = 1

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end
