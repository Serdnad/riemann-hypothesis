module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  simp only [absD, map_mul, Positive.val_mul]

theorem absD_pos (g : GA F 2) : 0 < absD g := (IdeleGroup.ideleModule F _).2

theorem ideleModule_infId (d : (UpperTheory.V.TR.Rinf F)ˣ) :
    (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F d) : ℝ) = ∏ v, |(d : UpperTheory.V.TR.Rinf F) v| := by
  rw [ideleModule_apply]
  have h2 : finiteModule (UpperTheory.V.TR.infId F d) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    change ‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).2 v‖ = 1
    change ‖((1 : Af F) - 0 + 0) v‖ = 1
    simp
  rw [h2, mul_one, infiniteModule]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hm : w.mult = 1 := by
    unfold InfinitePlace.mult; rw [if_pos (IsTotallyReal.isReal w)]
  rw [hm, pow_one]
  change ‖(((1 : Ad F) - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (d : UpperTheory.V.TR.Rinf F) : Ad F)).1 w‖ = _
  change ‖((1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F (d : UpperTheory.V.TR.Rinf F)) w‖ = _
  rw [map_one, sub_self, zero_add]
  change ‖(InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm ((d : UpperTheory.V.TR.Rinf F) w)‖ = _
  set e := InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  have he : ∀ r, (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r = e.symm r :=
    fun _ => rfl
  rw [he, ← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right]
  have h0 : e.symm 0 = 0 := by
    rw [← he]; exact map_zero _
  rw [← h0, e.symm.dist_eq]

theorem absD_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    absD (UpperTheory.V.TR.infGL F 2 y) = ∏ v, |(Matrix.det (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) v| := by
  rw [absD, UpperTheory.V.TR.det_infGL, ideleModule_infId]
  rfl

theorem absD_scalar_mul (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g) =
      (t : ℝ) ^ 2 * absD g := by
  rw [absD_mul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F))) = (moduleSection (w0 F) t * (u : Ideles F)) ^ 2 := by
    ext
    simp [sq]
    ring
  have hu : IdeleGroup.ideleModule F (u : Ideles F) = 1 := u.2
  rw [absD, hdet, map_pow, map_mul, ideleModule_moduleSection, hu, mul_one]
  rfl

theorem norm_hchar_of_finOrder {χ : HChar F} (hχ : IsOfFinOrder χ) (a : Ideles F) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := hχ.exists_pow_eq_one
  have h1 : (χ.1 a) ^ n = 1 := by
    have := congrArg (fun ψ : HChar F => ψ.1 a) hpow
    simpa using this
  have h2 : ‖((χ.1 a : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem measurableEmbedding_expPos : MeasurableEmbedding expPos :=
  expPosHomeomorph.measurableEmbedding

instance sigmaFinite_posRealMeasure : SigmaFinite posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  exact measurableEmbedding_expPos.sigmaFinite_map

theorem measurableSet_ge_one : MeasurableSet {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} :=
  measurable_subtype_coe measurableSet_Ici

theorem measurableSet_lt_one : MeasurableSet {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} :=
  measurable_subtype_coe measurableSet_Iio

theorem integrableOn_ge_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) {t | 1 ≤ (t : ℝ)} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)} = Set.Ici 0 := by
    ext x; simp [Real.one_le_exp_iff]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ r)⁻¹ * (t : ℝ)) ∘ expPos =
      fun x => Real.exp ((1 - (r : ℝ)) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hneg : (1 - (r : ℝ)) < 0 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Ioi hneg 0).congr_set_ae Ioi_ae_eq_Ici.symm

theorem integrableOn_lt_one {r : ℕ} (hr : 2 ≤ r) :
    IntegrableOn (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) {t | (t : ℝ) < 1} posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos, IntegrableOn,
    measurableEmbedding_expPos.restrict_map, measurableEmbedding_expPos.integrable_map_iff]
  have hpre : expPos ⁻¹' {t : {r : ℝ // 0 < r} | (t : ℝ) < 1} = Set.Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, coe_expPos, Set.mem_Iio]
    rw [← Real.exp_zero, Real.exp_lt_exp]
  rw [hpre]
  have hf : (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ r * (t : ℝ)⁻¹) ∘ expPos =
      fun x => Real.exp (((r : ℝ) - 1) * x) := by
    funext x
    simp only [Function.comp_apply, coe_expPos]
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  rw [hf]
  have hpos : 0 < ((r : ℝ) - 1) := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact (integrableOn_exp_mul_Iic hpos 0).mono_set Set.Iio_subset_Iic_self

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

theorem scalar_action_holds : SPois → SInt → SSmooth → SSmul := by
  intro _ _ _ F _ _ _ ω c k φ a ha
  have e2 : ∀ g, (a • φ).1 g = a * φ.1 g := fun _ => rfl
  refine ⟨fun h => ?_, fun c₀ b h => ?_⟩
  · obtain ⟨⟨hl, hlev, hk, hz, hg⟩, hlevel, hcent, hwt, hlow⟩ := h
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, fun w => Submodule.smul_mem _ a (hlevel w),
      fun z g => ?_, fun v => ?_, fun v => ?_⟩
    · rw [e2, e2, hl]
    · have e : {x | UpperTheory.V.TR.finRep F 2 x (a • φ) = a • φ} = {x | UpperTheory.V.TR.finRep F 2 x φ = φ} := by
        ext x
        simp only [Set.mem_ofPred_eq, map_smul]
        exact smul_right_inj ha
      rw [e]
      exact hlev
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ (Set.range fun x => UpperTheory.V.TR.cptRep F 2 x φ)) (Submodule.span_le.2 ?_)
      rintro _ ⟨x, rfl⟩
      show UpperTheory.V.TR.cptRep F 2 x (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (UpperTheory.V.TR.Sm F 2) => z φ) '' UpperTheory.V.TR.Zalg F 2))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz', rfl⟩
      show z (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz', rfl⟩)
    · obtain ⟨C, N, hC⟩ := hg g
      refine ⟨‖a‖ * C, N, fun y => ?_⟩
      rw [e2, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)
    · rw [e2, e2, hcent]
      ring
    · simp only [map_smul]
      rw [← smul_sub, hwt v]
      exact smul_comm _ _ _
    · simp only [map_smul]
      rw [← smul_sub, hlow v, ← smul_add]
      exact smul_comm _ _ _
  · intro x y hy yf
    have e : ∀ z : Af F, coefAt (fun 𝔪 => a * b 𝔪) z = a * coefAt b z := by
      intro z
      unfold coefAt
      split_ifs <;> simp
    convert (h x y hy yf).mul_left a using 1
    · funext ξ
      rw [e, mul_assoc]
    · rw [e2]
      simp only
      ring

end UpperTheory.HilbertEisensteinWeightOne
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace LeftInvarianceEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rowA_vecMul (ξ : Fin 2 → F) (γ : GL (Fin 2) F) :
    rowA ξ ᵥ* ((ratGL F 2 γ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowA (ξ ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) := by
  funext i
  exact (RingHom.map_vecMul (algebraMap F (Ad F)) (γ : Matrix (Fin 2) (Fin 2) F) ξ i).symm

def permE (γ : GL (Fin 2) F) : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} where
  toFun ξ := ⟨ξ.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  invFun ξ := ⟨ξ.1 ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  left_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])
  right_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])

theorem thetaS_ratGL (Ψ : (Fin 2 → Ad F) → ℂ) (a : (Ad F)ˣ) (γ : GL (Fin 2) F) (g : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (ratGL F 2 γ * g)) =
      thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g) := by
  unfold thetaS
  refine Eq.trans ?_ ((permE γ).tsum_eq (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
    Ψ (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))))
  refine tsum_congr fun ξ => ?_
  rw [← mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, Units.val_mul,
    ← Matrix.vecMul_vecMul, rowA_vecMul]
  rfl

theorem absD_ratGL (γ : GL (Fin 2) F) (g : GA F 2) : absD (ratGL F 2 γ * g) = absD g := by
  have h : Matrix.GeneralLinearGroup.det (ratGL F 2 γ) =
      IdeleGroup.diagonal F (Matrix.GeneralLinearGroup.det γ) := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap F (Ad F)) γ) = _
    rw [Matrix.GeneralLinearGroup.map_det]
    rfl
  unfold absD
  rw [map_mul, map_mul, h, IdeleGroup.ideleModule_diagonal, one_mul]

end LeftInvarianceEisenstein

theorem left_invariance_holds : SPois → SInt → SSmooth → SLeft := by
  intro _ _ _ F _ _ _ ω c γ g
  unfold Eis eisInt
  simp_rw [LeftInvarianceEisenstein.thetaS_ratGL, LeftInvarianceEisenstein.absD_ratGL]

end UpperTheory.HilbertEisensteinWeightOne
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def ca (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.cos θ else 1

def sa (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.sin θ else 0

omit [NumberField F] [IsTotallyReal F] in
theorem ca_sq (v : InfinitePlace F) (θ : ℝ) (u : InfinitePlace F) : ca v θ u ^ 2 + sa v θ u ^ 2 = 1 := by
  unfold ca sa
  split_ifs <;> simp [Real.cos_sq_add_sin_sq]

def rotv (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Kinf F 2 :=
  ⟨!![ca v θ, sa v θ; -sa v θ, ca v θ], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [ca_sq v θ u]⟩

theorem rotv_zero (v : InfinitePlace F) : rotv v 0 = (1 : UpperTheory.V.TR.Kinf F 2) := by
  ext i j u
  fin_cases i <;> fin_cases j <;> simp [rotv, ca, sa]

def Xv (v : InfinitePlace F) : UpperTheory.V.TR.Lie F 2 :=
  UpperTheory.V.TR.toL (Matrix.single 0 1 (Pi.single v 1)) - UpperTheory.V.TR.toL (Matrix.single 1 0 (Pi.single v 1))

theorem rot_deriv (v : InfinitePlace F) :
    HasDerivAt (fun t : ℝ => UpperTheory.V.TR.toL (Unitary.toUnits (rotv v t)).val) (Xv v) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
  by_cases hu : u = v
  · subst hu
    fin_cases i <;> fin_cases j
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_sin 0
    · simpa [Xv, rotv, ca, sa] using (Real.hasDerivAt_sin 0).fun_neg
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
  · fin_cases i <;> fin_cases j <;> simp [Xv, rotv, ca, sa, hu, hasDerivAt_const]

theorem det_rotv (v : InfinitePlace F) (θ : ℝ) :
    Matrix.GeneralLinearGroup.det (Unitary.toUnits (rotv v θ)) = 1 := by
  refine Units.ext ?_
  ext u
  simp [rotv, Matrix.det_fin_two]
  nlinarith [ca_sq v θ u]

theorem factor (x y a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (((x * a + y * -b : ℝ) : ℂ) + Complex.I * ((x * b + y * a : ℝ) : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2)) =
      ((a : ℂ) + Complex.I * (b : ℂ)) *
        (((x : ℂ) + Complex.I * (y : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hr : (x * a + y * -b) ^ 2 + (x * b + y * a) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * h
  have hc : (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hr
  rw [hc]
  push_cast
  linear_combination (-(b : ℂ) * y * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) * Complex.I_sq

omit [IsTotallyReal F] in
theorem prod_rot (v : InfinitePlace F) (θ : ℝ) :
    ∏ u, (((ca v θ u : ℝ) : ℂ) + Complex.I * ((sa v θ u : ℝ) : ℂ)) = Complex.exp (θ * Complex.I) := by
  rw [Fintype.prod_eq_single v (fun u hu => by simp [ca, sa, hu])]
  simp [ca, sa, Complex.exp_mul_I]
  ring

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (η : Fin 2 → Ad F) :
    Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      Complex.exp (θ * Complex.I) * Phi c η := by
  set M := ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))
  have hI : M.map (UpperTheory.V.TR.pInf F) = ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
      Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
    congrArg Units.val (UpperTheory.V.TR.pInf_infGL (Unitary.toUnits (rotv v θ)))
  have hF : M.map (pFin F) = 1 := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (Unitary.toUnits (rotv v θ)))
  have eI : ∀ i, UpperTheory.V.TR.pInf F ((η ᵥ* M) i) = ((fun j => UpperTheory.V.TR.pInf F (η j)) ᵥ*
      ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) i :=
    fun i => by rw [RingHom.map_vecMul, hI]; rfl
  have eF : ∀ i, pFin F ((η ᵥ* M) i) = pFin F (η i) := fun i => by
    rw [RingHom.map_vecMul, hF, Matrix.vecMul_one]; rfl
  unfold Phi
  rw [eF 0, eF 1, eI 0, eI 1, ← mul_assoc]
  congr 1
  unfold arch
  rw [← prod_rot v θ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun u _ => ?_
  have h := factor (UpperTheory.V.TR.pInf F (η 0) u) (UpperTheory.V.TR.pInf F (η 1) u) (ca v θ u) (sa v θ u) (ca_sq v θ u)
  simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, rotv] using h

theorem thetaS_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (h : GA F 2) :
    thetaS (Phi c) (h * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * thetaS (Phi c) h := by
  unfold thetaS
  rw [← tsum_mul_left]
  congr 1
  funext ξ
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, phi_rot]

theorem eis_rot (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (g : GA F 2) :
    Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * Eis ω (Phi c) g := by
  have hd : absD (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) = absD g := by
    unfold absD
    rw [map_mul, UpperTheory.V.TR.det_infGL, det_rotv, map_one, mul_one]
  have he : ∀ t u, eisInt ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) t u =
      Complex.exp (θ * Complex.I) * eisInt ω (Phi c) g t u := by
    intro t u
    unfold eisInt
    rw [← mul_assoc, thetaS_rot, hd]
    ring
  simp only [Eis, he, integral_const_mul]

end UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation in
theorem UpperTheory.HilbertEisensteinWeightOne.weight_holds : SPois → SInt → SSmooth → SWt := by
  intro _ _ _ F _ _ _ ω c _ hs v
  set φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hX : UpperTheory.V.TR.Eop v 0 1 φ - UpperTheory.V.TR.Eop v 1 0 φ = UpperTheory.V.TR.lie F 2 (Xv v) φ := by
    unfold UpperTheory.V.TR.Eop
    rw [← LinearMap.sub_apply, ← map_sub]
    rfl
  rw [hX]
  apply Subtype.ext
  funext g
  have h1 := UpperTheory.V.TR.hasDerivAt_curve φ g (fun t => Unitary.toUnits (rotv v t)) (Xv v)
    (by rw [rotv_zero, map_one]) (rot_deriv v)
  have h2 : HasDerivAt (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t))))
      (Complex.I * φ.1 g) 0 := by
    have e : (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t)))) =
        fun t : ℝ => Complex.exp (t * Complex.I) * φ.1 g := funext fun t => eis_rot ω c v t g
    rw [e]
    have h3 := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp.mul_const (φ.1 g)
    simpa using h3
  rw [UpperTheory.V.TR.lie_apply, h1.unique h2]
  simp [φ]
end
end
