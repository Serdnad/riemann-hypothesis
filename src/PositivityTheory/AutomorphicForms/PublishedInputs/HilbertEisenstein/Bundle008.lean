module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle004
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle006
public import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import GroundTheory.LocalFields.LocalZetaShell
public import GroundTheory.GlobalFields.TateThesis.Bundle001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import GroundTheory.GlobalFields.TateThesis.Bundle008
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
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem isClosed_valuation_le (w : HeightOneSpectrum (𝓞 F)) (γ : WithZero (Multiplicative ℤ)) :
    IsClosed {x : w.adicCompletion F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : γ < Valued.v x := lt_of_not_ge hx
  filter_upwards [Valued.locally_const (lt_of_le_of_lt zero_le hx').ne'] with y hy
  intro hy'
  have e : Valued.v y = Valued.v x := hy
  exact absurd (e ▸ hy') (not_le.mpr hx')

theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 F)) : Continuous (pLoc F w) :=
  RestrictedProduct.continuous_eval w

theorem continuous_pFin : Continuous (pFin F) := continuous_snd

theorem continuous_pInf : Continuous (UpperTheory.V.TR.pInf F) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem isClosed_row (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F (y 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      (((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1))).sub continuous_const)

theorem isClosed_col (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
      Valued.v (pLoc F w (pFin F (y 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1)))

theorem coe_scalar (a : Ideles F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      Matrix.diagonal fun _ => (a : Ad F) := rfl

theorem continuous_av : Continuous (av (F := F)) :=
  ((continuous_moduleSection (w0 F)).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

theorem continuous_rowv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => rowv g a ξ := by
  unfold rowv Mrow
  simp only [Units.val_mul, coe_scalar]
  exact continuous_const.matrix_vecMul
    ((continuous_pi fun _ => Units.continuous_val).matrix_diagonal.matrix_mul continuous_const)

theorem continuous_colv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => colv g a ξ := by
  unfold colv Mcol
  simp only [Units.val_mul, coe_scalar]
  exact (continuous_const.matrix_mul
    (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal).matrix_mulVec continuous_const

theorem continuous_vInf : Continuous (vInf (F := F)) :=
  continuous_pi fun i => continuous_pInf.comp (continuous_apply i)

theorem measurable_finRow (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finRow c (f p) := by
  unfold finRow
  exact Measurable.ite ((isClosed_row c).preimage hf).measurableSet measurable_const measurable_const

theorem measurable_finCol (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finCol c (f p) := by
  unfold finCol
  refine Measurable.ite ((isClosed_col c).preimage hf).measurableSet ?_ measurable_const
  exact (continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_pFin.comp ((continuous_apply 1).comp hf)))).measurable

theorem measurable_chi (χ : HChar F) : Measurable fun p : Pp F => ((χ.1 (av p) : ℂˣ) : ℂ)⁻¹ :=
  ((Units.continuous_val.comp (χ.2.1.comp continuous_av)).measurable).inv

theorem measurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap1 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finRow c ((continuous_rowv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable

theorem measurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap2 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finCol c ((continuous_colv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable.inv

theorem measurable_row_weight (g : GA F 2) : Measurable (w1 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_rowv g ξ.1).comp continuous_av)).measurable

theorem measurable_column_weight (g : GA F 2) : Measurable (w2 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_colv g ξ.1).comp continuous_av)).measurable

theorem aestronglyMeasurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap1 χ c g) (μS F S) := (measurable_first_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap2 χ c g) (μS F S) := (measurable_second_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_row_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w1 g) (μS F S) :=
  (measurable_row_weight g).aestronglyMeasurable

theorem aestronglyMeasurable_column_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w2 g) (μS F S) :=
  (measurable_column_weight g).aestronglyMeasurable

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
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

def rc (a : (InfiniteAdeleRing F)ˣ) (v : InfinitePlace F) : ℝ :=
  (UpperTheory.V.TR.infEq F).symm (a : InfiniteAdeleRing F) v

def archK (y : (UpperTheory.V.TR.Rinf F)ˣ) (ξ : F) (a : (InfiniteAdeleRing F)ˣ) : ℂ :=
  ∏ v, ((((rc a v * y.val v + (rc a v)⁻¹ * reAt v ξ : ℝ)) : ℂ) *
    Complex.exp (-(Real.pi : ℂ) * (((rc a v * y.val v) ^ 2 + ((rc a v)⁻¹ * reAt v ξ) ^ 2 : ℝ) : ℂ)))

def ωI (ω : HChar F) (a : (InfiniteAdeleRing F)ˣ) : ℂ := ((ω.1 (ofInfinite a) : ℂˣ) : ℂ)

def chiW (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4

def ArchInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ ξ : Fˣ,
    Integrable (fun a => archK y (ξ : F) a * (ωI ω a)⁻¹) (infiniteIdeleMeasure F) ∧
      ∫ a, archK y (ξ : F) a * (ωI ω a)⁻¹ ∂infiniteIdeleMeasure F =
        if ∀ v, 0 < reAt v (ξ : F) then (2 : ℂ) ^ Fintype.card (InfinitePlace F) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ)) else 0

def CoefDiv : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ) (z : Af F) (m : HeightOneSpectrum (𝓞 F) → ℤ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w, Valued.v (pLoc F w z) = WithZero.exp (dd w - m w)) → (∀ w ∉ S, m w = 0) →
    coefAt (divS ω c) z =
      if ∀ w ∈ S, 0 ≤ m w then ∏ w ∈ S, ∑ j ∈ Finset.range ((m w).toNat + 1), chiW ω c w ^ j else 0

def LocRam : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ w : HeightOneSpectrum (𝓞 F), c w ≠ 0 →
    (∀ k : ℤ, -((c w : ℤ) + dd w) < k →
      ∫ x in ordShell (w.adicCompletion F) k, ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) = 0) ∧
    ∫ x in ordShell (w.adicCompletion F) (-((c w : ℤ) + dd w)), ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) ≠ 0

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

def levelIdeal (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_levelIdeal {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((levelIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w := by
  unfold levelIdeal
  rw [count_finprod_primeIdealUnit_zpow]
  refine Filter.eventually_cofinite.2 (hc.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq, Nat.cast_eq_zero] at hv ⊢
  exact hv

theorem mem_level_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (B : Af F) :
    B ∈ idealFiniteAdeles (levelIdeal c) ↔ ∀ w, Valued.v (pLoc F w B) ≤ WithZero.exp (-(c w : ℤ)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_levelIdeal hc]
  rfl

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ))]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (Z : Af F) :
    Z ∈ idealFiniteAdeles (traceDualIdeal F (levelIdeal c)) ↔
      ∀ w, Valued.v (pLoc F w Z) ≤ WithZero.exp ((c w : ℤ) + dd w) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_levelIdeal hc, count_different, neg_neg]
  rfl

theorem isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩

theorem prod_real (f : InfinitePlace F → ℂ) : ∏ w : {w : InfinitePlace F // IsReal w}, f w.1 = ∏ v, f v :=
  (Equiv.subtypeUnivEquiv (fun w : InfinitePlace F => IsTotallyReal.isReal w)).prod_comp f

def archPoly (a : InfinitePlace F → ℝ) (x : mixedSpace F) : ℂ :=
  ∏ w : {w : InfinitePlace F // IsReal w},
    (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) * Complex.exp (-(π : ℂ) * ((a w.1 : ℝ) : ℂ) ^ 2)

theorem hasTemperateGrowth_archPoly (a : InfinitePlace F → ℝ) : (archPoly (F := F) a).HasTemperateGrowth := by
  unfold archPoly
  refine hasTemperateGrowth_finsetProd _ fun w _ => ?_
  have hlin : (fun x : mixedSpace F => ((x.1 w : ℝ) : ℂ)).HasTemperateGrowth :=
    ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace F →L[ℝ] ℂ)).hasTemperateGrowth
  exact ((HasTemperateGrowth.const _).add ((HasTemperateGrowth.const Complex.I).mul hlin)).mul
    (HasTemperateGrowth.const _)

def archSchwartz (a : InfinitePlace F → ℝ) : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (archPoly a)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))

theorem archSchwartz_apply (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = archPoly a x * ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [archSchwartz, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_archPoly a),
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

theorem archSchwartz_eq_prod (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = ∏ w : {w : InfinitePlace F // IsReal w},
      (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((x.1 w : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  rw [archSchwartz_apply, archPoly, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}),
    Finset.sum_empty, mul_zero, add_zero, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem archSchwartz_homeo (A B : Ad F) :
    archSchwartz (UpperTheory.V.TR.pInf F A) (homeomorphMixedSpace F B.1) =
      arch (UpperTheory.V.TR.pInf F A) (UpperTheory.V.TR.pInf F B) := by
  rw [archSchwartz_eq_prod, arch]
  exact prod_real (fun v => (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) + Complex.I * ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ)) *
    Complex.exp (-(π : ℂ) * (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ) ^ 2)))

open Classical in
theorem slice_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A = (if ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) then (1 : ℂ) else 0) •
      schwartzBruhatTensor (archSchwartz (UpperTheory.V.TR.pInf F A)) (cosetIndicator (levelIdeal c) 1) := by
  funext B
  simp only [slice, Phi, Pi.smul_apply, smul_eq_mul, schwartzBruhatTensor, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [archSchwartz_homeo, cosetIndicator_apply, mem_level_iff hc]
  have hB : ∀ w, pLoc F w (B.2 - 1) = pLoc F w (pFin F B) - 1 := fun w => by
    rw [map_sub, map_one]; rfl
  simp only [hB]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ))
    · have h3 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun w => ⟨h1 w, h2 w⟩
      simp only [forall_and, h1, h2, and_self, implies_true, ↓reduceIte, mul_one, one_mul]
    · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h2 fun w => (h w).2
      simp only [forall_and, h1, h2, true_and, and_false, ↓reduceIte, mul_zero, one_mul]
  · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h1 fun w => (h w).1
    simp only [forall_and, h1, false_and, ↓reduceIte, mul_zero, zero_mul]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem slice_mem_sb {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A ∈ schwartzBruhat F := by
  rw [L1.slice_eq hc A]
  exact Submodule.smul_mem _ _ (schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat _ _))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]


variable (F) in
def wpoly (x : mixedSpace F) : ℂ :=
  ∏ v : InfinitePlace F, (1 + ((x.1 ⟨v, IsTotallyReal.isReal v⟩ : ℝ) : ℂ) ^ 2)


variable (F) in
def phi1 : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wpoly F)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))


variable (F) in
def H1 : Ad F → ℂ := schwartzBruhatTensor (phi1 F) (cosetIndicator 1 0)

def condZ (c : HeightOneSpectrum (𝓞 F) → ℕ) (Z : Ad F) : Prop :=
  ∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)

def theta (G : Ad F → ℂ) (b : IdeleGroup F) : ℝ := ∑' ξ : Fˣ, ‖G (b • algebraMap F (Ad F) (ξ : F))‖

def gB (t : {r : ℝ // 0 < r}) : ℝ := if 1 ≤ (t : ℝ) then (t : ℝ)⁻¹ else (t : ℝ)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L5

def P5dom : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
  H1 F ∈ schwartzBruhat F ∧ (∀ x : Ad F, H1 F x = ((‖H1 F x‖ : ℝ) : ℂ)) ∧
    ∀ (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z Z' : Ad F), Z'.1 = Z.1 →
      (condZ c Z → Z'.2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) →
      ‖kernF c A Z‖ ≤ ‖H1 F A‖ * ‖H1 F Z'‖

def P5mu : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ),
  {w | c w ≠ 0}.Finite → ∃ μ : IdeleGroup F, (∀ Z : Ad F, (μ • Z).1 = Z.1) ∧
    ∀ Z : Ad F, condZ c Z → (μ • Z).2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

def P5meas : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ) (κ : ℂ),
  (∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z) → ∀ (Y : Ad F) (ξ : F),
    Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F => coefK c Y (tau p.1 p.2) ξ

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end
