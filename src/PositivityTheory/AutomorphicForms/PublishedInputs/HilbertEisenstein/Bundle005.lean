module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Imports
public import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
public import GroundTheory.GlobalFields.TateThesis.Bundle002
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle056
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
public import GroundTheory.GlobalFields.TateThesis.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem finite_c {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) : {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 H.fin
  have ho := isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) hpow
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  apply hw
  exact Nat.le_zero.1 ((H.cond w).2 (show (0 : ℕ) ∈ _ from fun x hu _ => key w x hu fun h => absurd h hwS))

theorem finite_dd : {w : HeightOneSpectrum (𝓞 F) | dd w ≠ 0}.Finite := by
  have h0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := _root_.differentIdeal_ne_bot
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simp only [Set.mem_ofPred_eq, dd, ordI, Nat.cast_ne_zero] at hw ⊢
  exact (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 hw


variable (F) in
def idealOf (e : HeightOneSpectrum (𝓞 F) → ℤ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := ∏ᶠ w, primeIdealUnit w ^ e w

def Jc (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := idealOf F fun w => (c w : ℤ)

def Jh (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := idealOf F fun w => -((c w : ℤ) + dd w)

private theorem count_Jc {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((Jc c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w := by
  refine count_finprod_primeIdealUnit_zpow (fun w => (c w : ℤ)) ?_ w
  exact Filter.eventually_cofinite.2 ((finite_c H).subset fun w hw => by simpa using hw)

private theorem count_Jh {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((Jh c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = -((c w : ℤ) + dd w) := by
  refine count_finprod_primeIdealUnit_zpow (fun w => -((c w : ℤ) + dd w)) ?_ w
  refine Filter.eventually_cofinite.2 (((finite_c H).union finite_dd).subset fun w hw => ?_)
  simp only [Set.mem_ofPred_eq] at hw
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  apply hw
  rw [h.1, h.2]
  simp

theorem phi_eq {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (y : Fin 2 → Ad F) :
    Phi c y = arch (UpperTheory.V.TR.pInf F (y 0)) (UpperTheory.V.TR.pInf F (y 1)) *
      if pFin F (y 0) ∈ idealFiniteAdeles (Jc c) ∧ pFin F (y 1) - 1 ∈ idealFiniteAdeles (Jc c) then 1 else 0 := by
  unfold Phi
  congr 1
  refine if_congr ?_ rfl rfl
  simp only [mem_idealFiniteAdeles, count_Jc H]
  rw [← forall_and]
  exact Iff.rfl

theorem norm_phiH_le {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (y : Fin 2 → Ad F) :
    ‖PhiH c y‖ ≤ ‖arch (UpperTheory.V.TR.pInf F (y 0)) (UpperTheory.V.TR.pInf F (y 1))‖ *
      if pFin F (y 0) ∈ idealFiniteAdeles (Jh c) ∧ pFin F (y 1) ∈ idealFiniteAdeles (Jh c) then (1 : ℝ) else 0 := by
  unfold PhiH
  rw [norm_mul]
  split_ifs with h1 h2
  · rw [Circle.norm_coe]
  · exfalso
    apply h2
    simp only [mem_idealFiniteAdeles, count_Jh H, neg_neg]
    exact ⟨fun w => (h1 w).1, fun w => (h1 w).2⟩
  · rw [norm_zero, mul_zero]
    positivity
  · simp

private theorem pInf_coord_eq (x : Ad F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F x v = (homeomorphMixedSpace F x.1).1 ⟨v, IsTotallyReal.isReal v⟩ := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

private theorem continuous_pInf_coord (v : InfinitePlace F) :
    Continuous fun x : Ad F => UpperTheory.V.TR.pInf F x v := by
  have h : (fun x : Ad F => UpperTheory.V.TR.pInf F x v) =
      fun x => (homeomorphMixedSpace F x.1).1 ⟨v, IsTotallyReal.isReal v⟩ := funext fun x => pInf_coord_eq x v
  rw [h]
  exact (continuous_apply _).comp (continuous_fst.comp ((homeomorphMixedSpace F).continuous.comp continuous_fst))

private theorem continuous_arch_comp {X : Type*} [TopologicalSpace X] {a b : X → Ad F} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun p => arch (UpperTheory.V.TR.pInf F (a p)) (UpperTheory.V.TR.pInf F (b p)) := by
  unfold arch
  refine continuous_finsetProd _ fun v _ => ?_
  have h1 : Continuous fun p => ((UpperTheory.V.TR.pInf F (a p) v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_pInf_coord v).comp ha)
  have h2 : Continuous fun p => ((UpperTheory.V.TR.pInf F (b p) v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_pInf_coord v).comp hb)
  exact (h1.add (continuous_const.mul h2)).mul
    (Complex.continuous_exp.comp (continuous_const.mul ((h1.pow 2).add (h2.pow 2))))

private theorem coe_scalar_mul (z : Ideles F) (g : GA F 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      Matrix.scalar (Fin 2) (z : Ad F) * (g : Matrix (Fin 2) (Fin 2) (Ad F)) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]

private theorem continuous_Y (g : GA F 2) (ξ : Fin 2 → F) :
    Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
        GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) := by
  have hz : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      ((moduleSection (w0 F) p.1 * (p.2 : Ideles F) : Ideles F) : Ad F) :=
    Units.continuous_val.comp (((continuous_moduleSection _).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  simp_rw [coe_scalar_mul, Matrix.scalar_apply]
  exact continuous_const.matrix_vecMul ((Continuous.matrix_diagonal (continuous_pi fun _ => hz)).matrix_mul
    continuous_const)

theorem measurable_eisInt {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (g : GA F 2) :
    Measurable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => eisInt ω (Phi c) g p.1 p.2) := by
  have hz : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      (moduleSection (w0 F) p.1 * (p.2 : Ideles F) : Ideles F) :=
    ((continuous_moduleSection _).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hterm : ∀ ξ : Fin 2 → F, Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      Phi c (rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
        GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) := by
    intro ξ
    have hY := continuous_Y g ξ
    have hY0 := (continuous_apply (0 : Fin 2)).comp hY
    have hY1 := (continuous_apply (1 : Fin 2)).comp hY
    have hf0 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
          GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 0) := continuous_snd.comp hY0
    have hf1 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g :
          GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 1) := continuous_snd.comp hY1
    have hO := ((isOpen_idealFiniteAdeles (Jc c)).preimage hf0).inter
      ((isOpen_idealFiniteAdeles (Jc c)).preimage (hf1.sub (continuous_const (y := (1 : Af F)))))
    simp_rw [phi_eq H]
    exact (continuous_arch_comp hY0 hY1).measurable.mul
      (Measurable.ite hO.measurableSet measurable_const measurable_const)
  have hθ : Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) * g) := by
    unfold thetaS
    exact Measurable.tsum fun ξ => hterm ξ.1
  have hω : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      ((ω.1 (moduleSection (w0 F) p.1 * (p.2 : Ideles F)) : ℂˣ) : ℂ)⁻¹ :=
    (Units.continuous_val.comp (ω.2.1.comp hz)).inv₀ fun p => Units.ne_zero _
  have ht : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  unfold eisInt
  exact ((hθ.mul hω.measurable).mul ht.measurable).mul measurable_const

end UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability
end
end

section

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory GroundTheory.Global Complex
open scoped Classical FourierTransform

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

def gP (a b : ℝ) : ℂ :=
  ((a : ℂ) + I * (b : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2))

theorem gP_eq (a b : ℝ) :
    gP a b = (a : ℂ) * realGaussian a * realGaussian b +
      I * (realGaussian a * ((b : ℂ) * realGaussian b)) := by
  unfold gP realGaussian
  rw [show -(Real.pi : ℂ) * ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) =
      -(Real.pi : ℂ) * (a : ℂ) ^ 2 + -(Real.pi : ℂ) * (b : ℂ) ^ 2 by ring, Complex.exp_add]
  ring

theorem continuous_gP : Continuous fun p : ℝ × ℝ => gP p.1 p.2 := by
  unfold gP
  fun_prop

theorem continuous_charR (a : ℝ) : Continuous fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))

theorem integrable_charR_mul {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * f t) := by
  refine hf.norm.mono' ((continuous_charR a).aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun t => by simp [Circle.norm_coe]

theorem integral_charR_even (a : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * a)) : Circle) : ℂ) * realGaussian t = realGaussian a := by
  have h := congrFun fourier_realGaussian a
  rw [Real.fourier_real_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul] using h

theorem integral_charR_odd (a : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * a)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t) =
      -I * ((a : ℂ) * realGaussian a) := by
  have h := congrFun fourier_realGaussianOdd a
  rw [Real.fourier_real_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul, realGaussianOdd, realGaussian] using h

theorem integral_place (a b : ℝ) :
    ∫ p : ℝ × ℝ, ((𝐞 (-(p.1 * a + p.2 * b)) : Circle) : ℂ) * gP p.1 p.2 = -I * gP a b := by
  have hsplit : ∀ p : ℝ × ℝ, ((𝐞 (-(p.1 * a + p.2 * b)) : Circle) : ℂ) * gP p.1 p.2 =
      (((𝐞 (-(p.1 * a)) : Circle) : ℂ) * ((p.1 : ℂ) * realGaussian p.1)) *
          (((𝐞 (-(p.2 * b)) : Circle) : ℂ) * realGaussian p.2) +
        I * ((((𝐞 (-(p.1 * a)) : Circle) : ℂ) * realGaussian p.1) *
          (((𝐞 (-(p.2 * b)) : Circle) : ℂ) * ((p.2 : ℂ) * realGaussian p.2))) := by
    intro p
    rw [neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, gP_eq]
    ring
  have hodd : Integrable (fun t : ℝ => (t : ℂ) * realGaussian t) := integrable_realGaussianOdd
  simp_rw [hsplit]
  rw [Measure.volume_eq_prod,
    integral_add ((integrable_charR_mul hodd a).mul_prod (integrable_charR_mul integrable_realGaussian b))
      (((integrable_charR_mul integrable_realGaussian a).mul_prod (integrable_charR_mul hodd b)).const_mul I),
    integral_const_mul,
    integral_prod_mul (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t))
      (fun t : ℝ => ((𝐞 (-(t * b)) : Circle) : ℂ) * realGaussian t),
    integral_prod_mul (fun t : ℝ => ((𝐞 (-(t * a)) : Circle) : ℂ) * realGaussian t)
      (fun t : ℝ => ((𝐞 (-(t * b)) : Circle) : ℂ) * ((t : ℂ) * realGaussian t)),
    integral_charR_even, integral_charR_even, integral_charR_odd, integral_charR_odd, gP_eq]
  ring

variable (F : Type) [Field F] [NumberField F]

theorem selfDualMeasure_eq_volume [IsTotallyReal F] : selfDualMeasure F = volume := by
  rw [selfDualMeasure, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, one_smul]

theorem isEmpty_complexPlaces [IsTotallyReal F] : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1) w.2⟩

theorem isProbabilityMeasure_complexPart [IsTotallyReal F] :
    IsProbabilityMeasure (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) := by
  haveI := isEmpty_complexPlaces F
  have h : (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) =
      Measure.dirac isEmptyElim := by
    rw [volume_pi, Measure.pi_of_empty]
  rw [h]
  infer_instance

def proj2 (x : Fin 2 → mixedSpace F) : {w : InfinitePlace F // IsReal w} → ℝ × ℝ :=
  fun w => ((x 0).1 w, (x 1).1 w)

theorem measurePreserving_proj2 [IsTotallyReal F] :
    MeasurePreserving (proj2 F) (GroundTheory.Automorphic.Adele2.mixedMeasure2 F) volume := by
  haveI := isProbabilityMeasure_complexPart F
  have h1 := measurePreserving_finTwoArrow (volume : Measure (mixedSpace F))
  have hf : MeasurePreserving (Prod.fst : mixedSpace F → ({w : InfinitePlace F // IsReal w} → ℝ))
      volume volume := by
    rw [Measure.volume_eq_prod]
    exact measurePreserving_fst
  have h2 := hf.prod hf
  have h3 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ
    {w : InfinitePlace F // IsReal w}).symm
  have h : proj2 F = (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ
      {w : InfinitePlace F // IsReal w}).symm ∘ Prod.map Prod.fst Prod.fst ∘
      MeasurableEquiv.finTwoArrow := by
    funext x w
    rfl
  rw [h, GroundTheory.Automorphic.Adele2.mixedMeasure2, selfDualMeasure_eq_volume]
  exact h3.comp (h2.comp h1)

theorem arch_eq_prod [IsTotallyReal F] (x₀ x₁ : mixedSpace F) :
    arch (toR F x₀) (toR F x₁) = ∏ w : {w : InfinitePlace F // IsReal w}, gP (x₀.1 w) (x₁.1 w) :=
  (Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun v => IsTotallyReal.isReal v) _ _
    fun _ => rfl).symm

theorem char_pairing_eq_prod [IsTotallyReal F] (x y : Fin 2 → mixedSpace F) :
    ((𝐞 (-GroundTheory.Automorphic.Adele2.mixedPairing2 F x y) : Circle) : ℂ) =
      ∏ w : {w : InfinitePlace F // IsReal w},
        ((𝐞 (-((x 0).1 w * (y 0).1 w + (x 1).1 w * (y 1).1 w)) : Circle) : ℂ) := by
  haveI := isEmpty_complexPlaces F
  rw [GroundTheory.Automorphic.Adele2.mixedPairing2, Fin.sum_univ_two, mixedTraceForm_apply',
    mixedTraceForm_apply']
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, addChar_map_finsetSum]
  exact map_prod Circle.coeHom _ _

theorem mixedFourier2_arch [IsTotallyReal F] (y : Fin 2 → mixedSpace F) :
    GroundTheory.Automorphic.Adele2.mixedFourier2 F (fun u => arch (toR F (u 0)) (toR F (u 1))) y =
      (-Complex.I) ^ Fintype.card (InfinitePlace F) * arch (toR F (y 0)) (toR F (y 1)) := by
  set f : {w : InfinitePlace F // IsReal w} → ℝ × ℝ → ℂ := fun w p =>
    ((𝐞 (-(p.1 * (y 0).1 w + p.2 * (y 1).1 w)) : Circle) : ℂ) * gP p.1 p.2 with hfdef
  have hpt : ∀ x : Fin 2 → mixedSpace F,
      𝐞 (-GroundTheory.Automorphic.Adele2.mixedPairing2 F x y) • arch (toR F (x 0)) (toR F (x 1)) =
        ∏ w, f w (proj2 F x w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, char_pairing_eq_prod, arch_eq_prod, ← Finset.prod_mul_distrib]
    rfl
  have hcont : Continuous fun z : {w : InfinitePlace F // IsReal w} → ℝ × ℝ => ∏ w, f w (z w) := by
    refine continuous_finsetProd _ fun w _ => ?_
    simp only [hfdef]
    refine Continuous.mul ?_ (continuous_gP.comp (continuous_apply w))
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  rw [GroundTheory.Automorphic.Adele2.mixedFourier2]
  simp_rw [hpt]
  rw [← integral_map (measurePreserving_proj2 F).aemeasurable hcont.aestronglyMeasurable,
    (measurePreserving_proj2 F).map_eq, integral_fintype_prod_volume_eq_prod f]
  simp only [hfdef, integral_place]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, arch_eq_prod,
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun v : InfinitePlace F => IsTotallyReal.isReal v)]

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
end
end

section

noncomputable section

open NumberField NumberField.mixedEmbedding MeasureTheory GroundTheory.Global
open scoped FourierTransform Matrix Classical
open GlobalTheory.CuspRep

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

theorem toR_homeomorphMixedSpace (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : Ad F) :
    toR F (homeomorphMixedSpace F x.1) = UpperTheory.V.TR.pInf F x := by
  funext v
  rfl

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

instance isEmpty_isComplex : IsEmpty {w : InfinitePlace F // InfinitePlace.IsComplex w} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 w.2) (IsTotallyReal.isReal w.1)⟩

theorem norm_sq_mixedToEuclidean (u : mixedSpace F) :
    ‖mixedToEuclidean F u‖ ^ 2 = ∑ v, (toR F u v) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclidean, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, mapComplexCoord_apply]
  rw [← Equiv.sum_comp (Equiv.subtypeUnivEquiv (fun v => IsTotallyReal.isReal v)).symm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [toR, sq]

theorem norm_sq_toEuclid2 (u : Fin 2 → mixedSpace F) :
    ‖GroundTheory.Automorphic.Adele2.toEuclid2 F u‖ ^ 2 = ∑ v, ((toR F (u 0) v) ^ 2 + (toR F (u 1) v) ^ 2) := by
  rw [GroundTheory.Automorphic.Adele2.toEuclid2_apply, WithLp.prod_norm_sq_eq_of_L2, Finset.sum_add_distrib,
    ← norm_sq_mixedToEuclidean, ← norm_sq_mixedToEuclidean]
  rfl

def coordCLM (i : Fin 2) (v : InfinitePlace F) : (Fin 2 → mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => toR F (u i) v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coordCLM_apply (i : Fin 2) (v : InfinitePlace F) (u : Fin 2 → mixedSpace F) :
    coordCLM F i v u = toR F (u i) v := rfl

def lin (v : InfinitePlace F) : (Fin 2 → mixedSpace F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordCLM F 0 v) + Complex.I • Complex.ofRealCLM.comp (coordCLM F 1 v)

theorem lin_apply (v : InfinitePlace F) (u : Fin 2 → mixedSpace F) :
    lin F v u = (toR F (u 0) v : ℂ) + Complex.I * (toR F (u 1) v : ℂ) := by
  simp [lin, coordCLM_apply]

theorem hasTemperateGrowth_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) (f : ι → E → ℂ) (hf : ∀ i, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h := (hf a).mul ih
    have e : (fun x => ∏ i ∈ insert a s, f i x) = (f a * fun x => ∏ i ∈ s, f i x) := by
      funext x
      simp [Finset.prod_insert ha]
    rw [e]
    exact h

def poly (u : Fin 2 → mixedSpace F) : ℂ := ∏ v, lin F v u

theorem hasTemperateGrowth_poly : (poly F).HasTemperateGrowth :=
  hasTemperateGrowth_prod _ (fun v u => lin F v u) fun v => (lin F v).hasTemperateGrowth

theorem exists_schwartz_arch :
    ∃ φ : SchwartzMap (Fin 2 → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1)) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (poly F)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (GroundTheory.Automorphic.Adele2.toEuclid2 F)
      (gaussianSchwartz _)), fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_poly F)]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    gaussianSchwartz_apply, smul_eq_mul]
  rw [norm_sq_toEuclid2, arch, Finset.prod_mul_distrib, poly]
  congr 1
  all_goals first
    | exact Finset.prod_congr rfl fun v _ => lin_apply F v u
    | (rw [← Complex.exp_sum, Complex.ofReal_exp]
       congr 1
       push_cast
       rw [Finset.mul_sum])

section Support

open IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base

theorem finite_support_of_cond (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (hfin : IsOfFinOrder ω)
    (hc : ∀ w, UpperTheory.V.Sd.IsCondAt w ω (c w)) : {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  apply hw
  refine Nat.le_zero.1 ((hc w).2 ?_)
  simp only [Set.mem_ofPred_eq]
  intro x hu _
  exact key w x hu fun h => absurd h hwS

end Support

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic
end
end
