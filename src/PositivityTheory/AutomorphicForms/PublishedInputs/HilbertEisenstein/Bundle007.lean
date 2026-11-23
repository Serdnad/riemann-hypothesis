module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle001
public import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Imports
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle004
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle001
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open NumberField.mixedEmbedding MeasureTheory GroundTheory.Global GroundTheory.Automorphic.Adele2 UpperTheory.V.Sd UpperTheory.V.Published
open scoped Matrix Classical NumberField.AdeleRing nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

variable {F : Type} [Field F] [NumberField F]

def nId (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_nId {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((nId c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w :=
  count_finprod_primeIdealUnit_zpow _ (Filter.eventually_cofinite.2 (hc.subset fun v hv => by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    exact_mod_cast hv)) w

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w differentIdeal_ne_bot]
  rfl

theorem mem_nId_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp (-(c w : ℤ))) ↔ a ∈ idealFiniteAdeles (nId c) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_nId hc]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp ((c w : ℤ) + dd w)) ↔
      a ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_nId hc, count_different, neg_neg]
  rfl

theorem arch_zero [IsTotallyReal F] : arch (0 : UpperTheory.V.TR.Rinf F) 0 = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)

def gFin (c : HeightOneSpectrum (𝓞 F) → ℕ) : (Fin 2 → Af F) → ℂ :=
  finiteTensor2 ![cosetIndicator (nId c) 0, cosetIndicator (nId c) 1]

theorem gFin_mem (c : HeightOneSpectrum (𝓞 F) → ℕ) : gFin c ∈ finiteSchwartzBruhat2 F :=
  finiteTensor2_mem fun i => by
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _

variable [IsTotallyReal F]

theorem phi_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1))) :
    Phi c = schwartzBruhatTensor2 φ (gFin c) := by
  funext x
  rw [schwartzBruhatTensor2, hφ, gFin, finiteTensor2_apply, Phi]
  simp only [infPart, finPart, toR_homeomorphMixedSpace, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, cosetIndicator_apply, sub_zero]
  congr 1
  have h0 := mem_nId_iff hc (pFin F (x 0))
  have h1 := mem_nId_iff hc (pFin F (x 1) - 1)
  simp only [map_sub, map_one] at h1
  by_cases a : (x 0).2 ∈ idealFiniteAdeles (nId c) <;> by_cases b : (x 1).2 - 1 ∈ idealFiniteAdeles (nId c)
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩, if_pos a, if_pos b, mul_one]
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2)), if_neg b, mul_zero]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]

def cst (c : HeightOneSpectrum (𝓞 F) → ℕ) : ℂ :=
  (-Complex.I) ^ Fintype.card (InfinitePlace F) *
    (((finiteAdeleMeasure F (idealFiniteAdeles (nId c))).toReal : ℝ) : ℂ) ^ 2

theorem cst_ne_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : cst c ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) (pow_ne_zero _ ?_)
  rw [Complex.ofReal_ne_zero]
  exact ENNReal.toReal_ne_zero.mpr ⟨(isOpen_idealFiniteAdeles _).measure_ne_zero _ ⟨0, zero_mem _⟩,
    finiteAdeleMeasure_idealFiniteAdeles_ne_top _⟩

theorem fourier_phi {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1)))
    (y : Fin 2 → Ad F) :
    adelicFourier2 F (Phi c) y = cst c * PhiH c y := by
  have hφ' : (⇑φ : (Fin 2 → mixedSpace F) → ℂ) = fun u => arch (toR F (u 0)) (toR F (u 1)) := funext hφ
  rw [phi_eq hc φ hφ, adelicFourier2_schwartzBruhatTensor2, schwartzBruhatTensor2,
    mixedFourier2Schwartz_apply, hφ', mixedFourier2_arch, gFin, finiteFourier2_finiteTensor2,
    finiteTensor2_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    finiteFourier_cosetIndicator, zero_mul, one_mul, AddChar.map_zero_eq_one, Circle.coe_one,
    infPart, finPart, toR_homeomorphMixedSpace, PhiH, cst]
  have h0 := mem_dual_iff hc (pFin F (y 0))
  have h1 := mem_dual_iff hc (pFin F (y 1))
  rw [show pFin F (y 1) = (y 1).2 from rfl]
  by_cases a : (y 0).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) <;>
    by_cases b : (y 1).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c))
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, Pi.one_apply]
    ring
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring

theorem rowA_zero : rowA (0 : Fin 2 → F) = 0 := by
  funext i
  simp [rowA]

theorem phi_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : Phi c 0 = 0 := by
  simp [Phi, map_zero, arch_zero]

theorem phiH_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : PhiH c 0 = 0 := by
  simp [PhiH, map_zero, arch_zero]

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

open UpperTheory.HilbertEisensteinWeightOne UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic in
theorem UpperTheory.HilbertEisensteinWeightOne.poisson_summation_holds : SPois := by
  intro F _ _ _ ω c hyp
  have hc := finite_support_of_cond F ω c hyp.fin hyp.cond
  obtain ⟨φ, hφ⟩ := exists_schwartz_arch F
  have hmem : Phi c ∈ schwartzBruhat2 F := by
    rw [phi_eq hc φ hφ]
    exact schwartzBruhatTensor2_mem φ (gFin_mem c)
  refine ⟨cst c, fun h => ?_⟩
  obtain ⟨S1, S2, E⟩ := poisson_rightTranslate hmem h
  have hF : ∀ ξ : Fin 2 → F, adelicFourier2 F (Phi c) ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ*
      ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))ᵀ) =
      cst c * PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) := by
    intro ξ
    rw [fourier_phi hc φ hφ, Matrix.vecMul_transpose]
    rfl
  simp only [hF, norm_mul] at S2 E
  have hsupp1 : Function.support (fun ξ : Fin 2 → F => Phi c (rowA ξ ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) ⊆
      {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.zero_vecMul, phi_zero]
  have hsupp2 : Function.support (fun ξ : Fin 2 → F =>
      PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ)) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.mulVec_zero, phiH_zero]
  have hC : ‖cst c‖ ≠ 0 := norm_ne_zero_iff.mpr (cst_ne_zero c)
  refine ⟨?_, ?_, ?_⟩
  · exact (S1.subtype (fun ξ : Fin 2 → F => ξ ≠ 0) : _)
  · exact (((summable_mul_left_iff hC).mp S2).subtype (fun ξ : Fin 2 → F => ξ ≠ 0) : _)
  · rw [thetaS, thetaT]
    rw [show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), Phi c (rowA (ξ : Fin 2 → F) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) from rfl,
      tsum_subtype_eq_of_support_subset hsupp1,
      show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA (ξ : Fin 2 → F)) from rfl,
      tsum_subtype_eq_of_support_subset hsupp2]
    change ∑' ξ : Fin 2 → F, Phi c ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) = _
    rw [E, tsum_mul_left, absD, Complex.ofReal_inv]
    ring
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem Phi_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    Phi c v = archS F (vInf v) * finRow c v := by
  rw [archS_apply]; rfl

theorem PhiH_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    PhiH c v = archS F (vInf v) * finCol c v := by
  rw [archS_apply]; rfl

theorem finRow_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finRow c v = finRow c v' := by
  unfold finRow; rw [h 0, h 1]

theorem finCol_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finCol c v = finCol c v' := by
  unfold finCol; rw [h 0, h 1]

theorem map_pFin_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = 1 :=
  congrArg Units.val (UpperTheory.V.TR.pFin_infGL y)

theorem map_pInf_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
  congrArg Units.val (UpperTheory.V.TR.pInf_infGL y)

theorem pFin_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
  rw [RingHom.map_vecMul, map_pFin_infGL, Matrix.vecMul_one]; rfl

theorem vInf_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      vInf v ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) := by
  funext i
  simp only [vInf]
  rw [RingHom.map_vecMul, map_pInf_infGL]; rfl

theorem pFin_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) i) = pFin F (v i) := by
  rw [RingHom.map_mulVec, map_pFin_infGL, Matrix.one_mulVec]; rfl

theorem vInf_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) *ᵥ vInf v := by
  funext i
  simp only [vInf]
  rw [RingHom.map_mulVec, map_pInf_infGL]; rfl

theorem row_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    Phi c (rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F))) =
      archS F (B1 (vInf (rowv g a ξ)) (UpperTheory.V.TR.toL y.val)) * finRow c (rowv g a ξ) := by
  have hv : rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowv g a ξ ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    simp only [rowv, Mrow, Units.val_mul, Matrix.vecMul_vecMul, mul_assoc]
  rw [hv, Phi_eq, finRow_congr (pFin_vecMul_infGL _ _), vInf_vecMul_infGL, left_bilinear_apply]
  rfl

theorem col_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) =
      archS F (B2 (vInf (colv g a ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) * finCol c (colv g a ξ) := by
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ =
      UpperTheory.V.TR.infGL F 2 y⁻¹ * Mcol g a := by
    simp only [Mcol, mul_inv_rev, map_inv, mul_assoc]
  have hv : (((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ =
      ((UpperTheory.V.TR.infGL F 2 y⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ colv g a ξ := by
    rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec]; rfl
  rw [hv, PhiH_eq, finCol_congr (pFin_infGL_mulVec _ _), vInf_infGL_mulVec, right_bilinear_apply]
  rfl

theorem eisInt_row (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      (∑' ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val))) *
        ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  have h : ∀ ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val)) =
      Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)) := by
    intro ξ
    rw [row_term]
    simp only [kap1, w1, av]
    ring
  have e : (∑' ξ : Xi F, Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)))) =
      thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  ring

theorem eisInt_col (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : ℂ}
    (hC : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      C * ((absD (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : ℝ) * ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        ∑' ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) := by
  have h : ∀ ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) =
      PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)⁻¹) := by
    intro ξ
    rw [col_term]
    simp only [kap2, w2, av]
    ring
  have e : (∑' ξ : Xi F, PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
      thetaT (PhiH c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  rw [hC, absD_scalar_mul]
  have ht : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr t.2.ne'
  push_cast
  field_simp

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix ENNReal
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published Filter

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace L6

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem omega_diagonal (ω : HChar F) (a : Fˣ) : ω.1 (diagonal F a) = 1 := ω.2.2 a

theorem module_tau_diag (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (a : Fˣ) :
    (ideleModule F (tau t u * diagonal F a) : ℝ) = t := by
  have hu : ideleModule F (u : IdeleGroup F) = 1 := u.2
  rw [tau, map_mul, map_mul, ideleModule_diagonal, ideleModule_moduleSection, hu, mul_one, mul_one]

theorem G_unfold (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (a : Fˣ) :
    kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    kern c Y (tau t u * diagonal F a) ξ * wt ω t u := by
  have he : diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F) = tau t u * diagonal F a := by
    rw [tau, mul_assoc, mul_comm]
  rw [he, module_tau_diag, map_mul, omega_diagonal, mul_one, wt, mul_assoc]

theorem tsum_G (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) :
    ∑' a : Fˣ, kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    coefK c Y (tau t u) ξ * wt ω t u := by
  simp_rw [G_unfold]
  rw [coefK, tsum_mul_right]

def phiA (a : Fˣ) (p : {r : ℝ // 0 < r} × normOneSubgroup F) : IdeleGroup F :=
  diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F)

theorem continuous_phiA (a : Fˣ) : Continuous (phiA (F := F) a) :=
  (continuous_const.mul ((continuous_moduleSection (w0 F)).comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)

theorem measurePreserving_phiA (a : Fˣ) :
    MeasurePreserving (phiA (F := F) a) (posRealMeasure.prod (normOneMeasure F)) (ideleMeasure F) := by
  have h0 : MeasurePreserving (normOneSplitting (w0 F)).toHomeomorph.toMeasurableEquiv (ideleMeasure F)
      ((normOneMeasure F).prod posRealMeasure) := measurePreserving_normOneSplitting (w0 F)
  have h1 := (MeasurePreserving.symm _ h0).comp (Measure.measurePreserving_swap
    (μ := posRealMeasure) (ν := normOneMeasure F))
  have h3 := (measurePreserving_mul_left (ideleMeasure F) (diagonal F a)).comp h1
  convert h3 using 1
  funext p
  change diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F) =
    diagonal F a * ((p.2 : IdeleGroup F) * moduleSection (w0 F) p.1)
  rw [mul_assoc, mul_comm (moduleSection (w0 F) p.1)]

theorem muE_ac : muE F ≪ posRealMeasure.prod (normOneMeasure F) := by
  have h : muE F = (posRealMeasure.prod (normOneMeasure F)).restrict (Set.univ ×ˢ normOneFundamentalDomain F) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [h]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

theorem lintegral_unfold {g : IdeleGroup F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, ∑' a : Fˣ, g (phiA a p) ∂(muE F) = ∫⁻ x, g x ∂ideleMeasure F := by
  have hm : ∀ a : Fˣ, Measurable fun p => g (phiA a p) := fun a => hg.comp (continuous_phiA a).measurable
  have hin : ∀ t : {r : ℝ // 0 < r}, ∫⁻ u in normOneFundamentalDomain F, ∑' a : Fˣ, g (phiA a (t, u)) ∂normOneMeasure F
      = ∫⁻ u, g (phiA 1 (t, u)) ∂normOneMeasure F := by
    intro t
    have h𝓕 := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
    let e : Fˣ ≃ (diagonalNormOne F).op := (diagonalNormOneEquiv F).trans (diagonalNormOne F).equivOp
    rw [lintegral_tsum (f := fun a u => g (phiA a (t, u))) (fun a => ((hm a).comp measurable_prodMk_left).aemeasurable),
      h𝓕.lintegral_eq_tsum'',
      ← e.tsum_eq]
    refine tsum_congr fun a => lintegral_congr fun u => ?_
    change g (phiA a (t, u)) = g (phiA 1 (t, u * diagonalToNormOne F a))
    simp only [phiA, map_one, one_mul, Subgroup.coe_mul, coe_diagonalToNormOne]
    congr 1
    ac_rfl
  rw [lintegral_prod _ (Measurable.tsum hm).aemeasurable]
  simp_rw [hin]
  rw [← (measurePreserving_phiA 1).lintegral_comp hg, lintegral_prod _ (hm 1).aemeasurable]

theorem integrable_unfold {G : IdeleGroup F → ℂ} (hG : Integrable G (ideleMeasure F)) :
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G (phiA a p)) (muE F) := by
  set G' := hG.1.mk G
  have hG'm : StronglyMeasurable G' := hG.1.stronglyMeasurable_mk
  have hGG' : G =ᵐ[ideleMeasure F] G' := hG.1.ae_eq_mk
  have hae : ∀ᵐ p ∂(muE F), ∀ a : Fˣ, G (phiA a p) = G' (phiA a p) := by
    refine ae_all_iff.2 fun a => muE_ac.ae_le ?_
    exact (measurePreserving_phiA a).quasiMeasurePreserving.ae_eq_comp hGG'
  have hP' : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G' (phiA a p)) (muE F) := by
    refine ⟨(Measurable.tsum fun a => hG'm.measurable.comp (continuous_phiA a).measurable).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖∑' a : Fˣ, G' (phiA a p)‖ₑ ∂(muE F)
        ≤ ∫⁻ p, ∑' a : Fˣ, ‖G' (phiA a p)‖ₑ ∂(muE F) := lintegral_mono fun p => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ x, ‖G' x‖ₑ ∂ideleMeasure F := lintegral_unfold hG'm.measurable.enorm
      _ = ∫⁻ x, ‖G x‖ₑ ∂ideleMeasure F := lintegral_congr_ae (hGG'.fun_comp _).symm
      _ < ∞ := hG.2
  refine hP'.congr ?_
  filter_upwards [hae] with p hp
  exact tsum_congr fun a => (hp a).symm

end L6

open L6 in
theorem sUnfold_statement : SUnfold := by
  intro F _ _ _ ω c H Y ξ hG
  set G : IdeleGroup F → ℂ := fun τ => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)
  have hP : ∀ p : {r : ℝ // 0 < r} × normOneSubgroup F,
      coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 = ∑' a : Fˣ, G (phiA a p) := fun p => (tsum_G ω c Y ξ p.1 p.2).symm
  simp_rw [hP]
  rw [integral_prod _ (integrable_unfold hG), integral_ideleMeasure_eq_integral_fundamentalDomain (w0 F) hG]
  rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end
