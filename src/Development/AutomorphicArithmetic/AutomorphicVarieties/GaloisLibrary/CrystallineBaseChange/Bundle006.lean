module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
public import GroundTheory.AutomorphicForms.ReductionIwasawa
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.Conformal
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.AutomorphicForms.ReductionHeight

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem tend : Filter.Tendsto (fun w : Pl ℚ => normV w) Filter.cofinite Filter.cofinite :=
  Function.Injective.tendsto_cofinite fun w w' e => HeightOneSpectrum.ext <| by
    rw [(places w).2.1, (places w').2.1]
    exact congrArg (fun n : ℕ => Ideal.span {(n : 𝓞 ℚ)}) e
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix UpperTheory.V

namespace UpperTheory.V.Br.RotationEigenvalues

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

omit [NumberField F] in
private theorem rot_add (θ η : TR.Rinf F) : rot (θ + η) = rot θ * rot η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
private theorem rot_zero : rot (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

variable [IsTotallyReal F]

private theorem rot_eig (φ : TR.Sm F 2) (z : ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ) (g : GA F 2) (θ : TR.Rinf F) :
    φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot θ))) = Complex.exp (z * ∑ v, (θ v : ℂ)) * φ.1 g := by
  classical
  set μ : ℂ := z * ∑ v, (θ v : ℂ) with hμ
  let X : TR.Lie F 2 := TR.toL !![0, θ; -θ, 0]
  have hX : X = ∑ v, θ v • (TR.toL (Matrix.single 0 1 (Pi.single v 1)) - TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [X, Finset.sum_apply, Pi.single_apply]
  have hL : TR.lie F 2 X φ = μ • φ := by

    rw [hX, map_sum, LinearMap.sum_apply, hμ, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, Complex.coe_smul, ← h v]
    simp only [TR.Eop]
  have hc : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (t • θ))).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
    fin_cases i <;> fin_cases j
    · simpa [X, rot] using h1.cos
    · simpa [X, rot] using h1.sin
    · simpa [X, rot] using h1.sin.fun_neg
    · simpa [X, rot] using h1.cos
  let f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ))))
  have hf : ∀ t, HasDerivAt f (μ * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (Unitary.toUnits (rot (t • θ)))) (fun s => Unitary.toUnits (rot (s • θ))) X
      (by rw [zero_smul, rot_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) (μ * f t) 0 := by
      simpa only [f, add_smul, rot_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-μ * s) * f s) 0 t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -μ * (s : ℂ)) (-μ) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-μ)
    exact (h1.cexp.fun_mul (hf t)).congr_deriv (by ring)
  have h4 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, one_smul, zero_smul, rot_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul] at h4
  rw [← h4, ← mul_assoc, ← Complex.exp_add]
  simp

end UpperTheory.V.Br.RotationEigenvalues

open UpperTheory.V.Br.RotationEigenvalues in
theorem UpperTheory.V.Br.rotEig :
    UpperTheory.V.Br.RotEig := by
  intro F _ _ _ φ z hφ θ h hh g
  have e : h = Unitary.toUnits (rot θ) := Units.ext hh
  rw [e]
  exact rot_eig φ z hφ g θ
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GroundTheory.Automorphic
open scoped Matrix

private theorem upper_eq {R : Type} [CommRing R] (b : GL (Fin 2) R) (h : b 1 0 = 0) (h0 : IsUnit (b 0 0)) (h1 : IsUnit (b 1 1)) :
    ∃ (z y : Rˣ) (x : R), b = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y x := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨d, hd⟩ := h1
  refine ⟨d, d⁻¹ * a, (d⁻¹ : Rˣ) * b 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, h, ← ha, ← hd]

private theorem orth {E : Type} [NormedField E] (φ : E ≃+* ℝ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (k : Matrix (Fin 2) (Fin 2) E)
    (hk : ∀ y : Fin 2 → E, Reduction.euclidNorm (y ᵥ* k) = Reduction.euclidNorm y) (i j : Fin 2) :
    φ (k i 0) * φ (k j 0) + φ (k i 1) * φ (k j 1) = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  have h : ∀ s t : E, (φ s * φ (k 0 0) + φ t * φ (k 1 0)) ^ 2 + (φ s * φ (k 0 1) + φ t * φ (k 1 1)) ^ 2 = φ s ^ 2 + φ t ^ 2 := by
    intro s t
    have := hk ![s, t]
    unfold Reduction.euclidNorm at this
    rw [Real.sqrt_inj (by positivity) (by positivity)] at this
    simpa [← hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using this
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [map_one, map_zero] at h1 h2 h3
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith

theorem UpperTheory.V.Br.iwasawaA :
    UpperTheory.V.Br.IwasawaA := by
  intro F _ _ _ g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨z, y, x, hz⟩ := upper_eq b (hb (show (0 : Fin 2) < 1 by decide))
    (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0) (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1)
  have hr : ((Matrix.GeneralLinearGroup.map (TR.pInf F) k : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) ∈
      Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j w
    have := orth (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)).norm_map_of_map_zero
        (map_zero _) x) _ (hk.1 w) i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine Eq.trans this ?_
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  have hu : Matrix.GeneralLinearGroup.map (pFin F) k ∈ AdelicGLn.integralFiniteGL F 2 :=
    (AdelicGLn.mem_integralFiniteGL_iff_forall F 2).2 hk.2
  obtain ⟨hu1, hu2⟩ := (AdelicGLn.mem_integralFiniteGL_iff F 2).1 hu
  refine ⟨z, y, x, ⟨_, hr⟩, Matrix.GeneralLinearGroup.map (pFin F) k, ?_, ?_⟩
  · refine mem_KLev.2 ⟨fun a c => mem_Ohat.2 (hu1 a c), fun a c => mem_Ohat.2 (hu2 a c), fun a c => ⟨_, ?_, by rw [Nat.cast_one, one_mul]⟩⟩
    refine sub_mem (mem_Ohat.2 (hu1 a c)) ?_
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  · have e : Unitary.toUnits (⟨_, hr⟩ : TR.Kinf F 2) = Matrix.GeneralLinearGroup.map (TR.pInf F) k := Units.ext rfl
    rw [e, TR.infGL_mul_finGL, ← hz]
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Sd UpperTheory.V.Sd.Eis

private theorem co_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem co_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]

theorem UpperTheory.V.Br.ctOne :
    UpperTheory.V.Br.CtOne := by
  intro F _ _
  obtain ⟨h1, h2, h3, h4, -, -, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock F
  letI iM : MeasurableSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := MeasurableSpace.pi
  have hμ : (unipMeasure F 2 1).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos 2 1 → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have hL : ratN F 2 1 = unipLattice F 2 1 := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  have hF : IsAddFundamentalDomain (ratN F 2 1) (unipFundamentalDomain F 2 1) (unipMeasure F 2 1) := by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain
  have main : ∀ [MeasurableSpace (NA F)] [BorelSpace (NA F)] (ν : Measure (NA F)) [ν.IsAddHaarMeasure] (D₀ : Set (NA F)),
      IsAddFundamentalDomain (ratN F 2 1) D₀ ν → ∀ φ : GA F 2 → ℂ, (∀ γ g, φ (ratGL F 2 γ * g) = φ g) →
      (∀ g, cterm ν D₀ φ g = 0) → GlobalTheory.CuspRep.IsCuspidal φ := by
    intro j1 j2 ν _ D₀ hD₀ φ hl h0 r hr0 hr1 i1 i2 μ D hμ' hD g
    obtain rfl : r = 1 := by omega
    obtain rfl : i1 = j1 :=
      (@BorelSpace.measurable_eq _ _ i1 i2).trans (@BorelSpace.measurable_eq _ _ j1 j2).symm
    have hper : ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * g) = φ (unip x * g) := by
      rintro _ ⟨y, rfl⟩ x
      rw [hx, hx x]
      refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
      rw [← mul_assoc, co_rat_aff, co_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
      rfl
    have hD' : IsAddFundamentalDomain (ratN F 2 1) D ν := hD.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
    have h : ∫ x in D, φ (unip x * g) ∂ν = 0 :=
      (hD'.setIntegral_eq hD₀ (f := fun x => φ (unip x * g)) fun γ x => hper γ γ.2 x).trans (h0 g)
    rw [Measure.isAddLeftInvariant_eq_smul μ ν, Measure.restrict_smul, integral_smul_nnreal_measure, h, smul_zero]
  exact ⟨iM, hB, unipMeasure F 2 1, hμ, unipFundamentalDomain F 2 1, hF, @main iM hB _ hμ _ hF⟩
end

section

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf UpperTheory.V.Sd Topology
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Br.DescentHolomorphic


open Classical in
private def EE (i j : Fin 2) : TR.Lie ℚ 2 := TR.toL (Matrix.single i j (Pi.single Rat.infinitePlace 1))

private def AA (w : ℂ) : TR.Lie ℚ 2 := w.im • EE 0 0 + w.re • EE 0 1 + EE 1 1

private theorem AA_eq (w : ℂ) (h : w.im ≠ 0) :
    AA w = TR.toL (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff (Units.mk0 w.im h) w.re)).val := by
  funext i j v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  change _ = (aff (Units.mk0 w.im h) w.re).val i j
  fin_cases i <;> fin_cases j <;> simp [AA, EE, aff, Matrix.single]

private theorem rmul_AA (w : ℂ) (j : Fin 2) : TR.rmul (EE 0 j) (AA w) = w.im • EE 0 j := by
  funext a b v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  change (Matrix.of (AA w) * Matrix.of (EE 0 j)) a b Rat.infinitePlace = _
  fin_cases a <;> fin_cases b <;> fin_cases j <;> simp [AA, EE, Matrix.single, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem chart_AA (ψ : GA ℚ 2 → ℂ) (w : ℂ) (h : w.im ≠ 0) :
    TR.chart ψ 1 (AA w) = ψ (upR (aff (Units.mk0 w.im h) w.re)) := by
  rw [AA_eq w h, TR.chart_val, one_mul]
  rfl

private theorem hasFDerivAt_AA (w : ℂ) :
    HasFDerivAt AA (Complex.imCLM.smulRight (EE 0 0) + Complex.reCLM.smulRight (EE 0 1)) w :=
  (Complex.imCLM.smulRight (EE 0 0) + Complex.reCLM.smulRight (EE 0 1)).hasFDerivAt.add_const (EE 1 1)

private theorem key (k : ℕ) (φ : TR.Sm ℚ 2) (hφ : IsLow k φ) (w : ℂ) (hw : 0 < w.im) :
    DifferentiableAt ℂ (fun w : ℂ => ((w.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * TR.chart φ.1 1 (AA w)) w := by
  have hm : AA w ∈ TR.invSet ℚ 2 := by rw [AA_eq w hw.ne']; exact TR.val_mem_invSet _
  have hc := ((TR.contDiffAt_chart φ.2 1 hm).differentiableAt (by simp)).hasFDerivAt
  set D := fderiv ℝ (TR.chart φ.1 1) (AA w) with hD
  set g := upR (aff (Units.mk0 w.im hw.ne') w.re) with hg
  have he : ∀ j, (TR.Eop Rat.infinitePlace 0 j φ).1 g = (w.im : ℂ) * D (EE 0 j) := fun j => by
    have h1 := TR.chart_lieD φ.2 (EE 0 j) 1 hm
    rw [chart_AA _ w hw.ne', rmul_AA, map_smul, Complex.real_smul] at h1
    exact h1
  have h1 : (TR.Eop Rat.infinitePlace 0 1 φ).1 g - (TR.Eop Rat.infinitePlace 1 0 φ).1 g = Complex.I * k * φ.1 g :=
    congrFun (congrArg Subtype.val (hφ.wt Rat.infinitePlace)) g
  have h2 : (TR.Eop Rat.infinitePlace 0 0 φ).1 g - (TR.Eop Rat.infinitePlace 1 1 φ).1 g =
      Complex.I * ((TR.Eop Rat.infinitePlace 0 1 φ).1 g + (TR.Eop Rat.infinitePlace 1 0 φ).1 g) :=
    congrFun (congrArg Subtype.val (hφ.low Rat.infinitePlace)) g
  have h3 : (TR.Eop Rat.infinitePlace 0 0 φ).1 g + (TR.Eop Rat.infinitePlace 1 1 φ).1 g = 0 :=
    congrFun (congrArg Subtype.val (hφ.one Rat.infinitePlace)) g
  rw [he] at h1 h2 h3
  rw [he] at h2
  have h4 : (w.im : ℂ) * D (EE 0 0) = Complex.I * (w.im * D (EE 0 1)) + k / 2 * φ.1 g := by
    linear_combination (h2 + h3) / 2 - Complex.I / 2 * h1 - (k / 2 * φ.1 g) * Complex.I_mul_I
  have hp := Complex.ofRealCLM.hasFDerivAt.comp w
    ((Complex.imCLM.hasFDerivAt (x := w)).rpow_const (p := -((k : ℝ) / 2)) (Or.inl hw.ne'))
  have hF := hp.fun_mul (hc.comp w (hasFDerivAt_AA w))
  refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨hF.differentiableAt, ?_⟩
  erw [hF.fderiv]
  have hy : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
  have hr : w.im ^ (-((k : ℝ) / 2) - 1) = w.im ^ (-((k : ℝ) / 2)) / w.im := Real.rpow_sub_one hw.ne' _
  simp [chart_AA _ w hw.ne', ← hg, hr]
  field_simp
  linear_combination 2 * ((w.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * h4

end UpperTheory.V.Br.DescentHolomorphic

open UpperTheory.V.Br.DescentHolomorphic in
theorem UpperTheory.V.Br.downHol :
    UpperTheory.V.Br.DownHol := by
  intro k φ hφ
  refine UpperHalfPlane.mdifferentiable_iff.2 ?_
  refine DifferentiableOn.congr (fun w hw => (key k φ hφ w hw).differentiableWithinAt) fun w hw => ?_
  have hw' : 0 < w.im := hw
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hw', chart_AA _ w hw'.ne']
  rfl
end
end

section

namespace UpperTheory.V.Br

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {k : ℕ}

private theorem wt_low (hL : W * L - L * W = (-2 : ℂ) • L) {x : V} {n : ℤ} (hx : W x = (n : ℂ) • x) :
    W (L x) = ((n - 2 : ℤ) : ℂ) • L x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hL
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

private theorem cas (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W)) {x : V} {n : ℤ}
    (hx : W x = (n : ℂ) • x) :
    R (L x) = ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) • x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hC
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul,
    Module.End.one_apply] at h
  have e : R (L x) = (1 / 4 : ℂ) • (4 : ℂ) • R (L x) := by
    rw [smul_smul]; norm_num
  rw [e, h]
  push_cast
  module

private theorem bound (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    {x : V} (hx0 : x ≠ 0) {n : ℤ} (hx : W x = (n : ℂ) • x) : (k : ℤ) * (k - 2) ≤ n * (n - 2) := by
  by_contra hlt
  push_neg at hlt
  have hltR : (n : ℝ) * (n - 2) < (k : ℝ) * (k - 2) := by exact_mod_cast hlt
  set c : ℝ := ((k : ℝ) * (k - 2) - n * (n - 2)) / 4 with hc
  have hcpos : 0 < c := div_pos (by linarith) (by norm_num)
  have hcC : ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) = (c : ℂ) := by
    rw [hc]; push_cast; ring
  have hwl := wt_low hL hx
  have h1 : H x (L x) = 0 := by
    have e := hW x (L x)
    rw [hx, hwl] at e
    simp [map_smulₛₗ] at e
    rcases e with e | e
    · have h2 : (2 : ℂ) = 0 := by linear_combination e
      norm_num at h2
    · exact e
  have h2 : H (L x) x = 0 := by
    have e := hW (L x) x
    rw [hwl, hx] at e
    simp [map_smulₛₗ] at e
    exact e
  have h3 : H (L x) (L x) = -(c : ℂ) * H x x := by
    have e := hH x (L x)
    rw [cas hC hx, hcC] at e
    simp only [map_smul, smul_eq_mul] at e
    rw [e]; ring
  set s : ℂ := ((Real.sqrt c : ℝ) : ℂ) with hsdef
  have hs : (starRingEnd ℂ) s = s := Complex.conj_ofReal _
  have hss : s * s = (c : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hcpos.le]
  have hy : H (s • x + L x) (s • x + L x) = 0 := by
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hs,
      h1, h2, h3, RingHom.id_apply]
    ring_nf
    linear_combination (H x x) * hss
  have hy0 := h0 _ hy
  have hLx : L x = -(s • x) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy0)
  have e1 : W (L x) = -(s • ((n : ℂ) • x)) := by rw [hLx, map_neg, map_smul, hx]
  rw [hwl, hLx] at e1
  have key : ((2 : ℂ) * s) • x = 0 := by
    have e2 : ((2 : ℂ) * s) • x = (((n - 2 : ℤ) : ℂ) • -(s • x)) - (-(s • ((n : ℂ) • x))) := by
      push_cast; module
    rw [e2, e1, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    have hc0 : (c : ℂ) = 0 := by rw [← hss, hs0, mul_zero]
    have : c = 0 := by exact_mod_cast hc0
    linarith
  · exact hx0 h

private theorem descend (hk : 3 ≤ k) (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    (j : ℕ) : ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x → ∃ x, x ≠ 0 ∧ W x = (k : ℂ) • x ∧ L x = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx0 hx
  have hb := bound hL hC h0 hW hH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hj2 : 2 ≤ j := by
    by_contra h
    push_neg at h
    interval_cases j <;> (push_cast at hb; nlinarith)
  by_cases hL0 : L x = 0
  · refine ⟨x, hx0, ?_, hL0⟩
    have hc := cas hC hx
    rw [hL0, map_zero] at hc
    have hq : ((((k : ℤ) * (k - 2) - ((j : ℤ) : ℤ) * ((j : ℤ) - 2) : ℤ)) : ℂ) / 4 = 0 := by
      rcases smul_eq_zero.mp hc.symm with h | h
      · exact h
      · exact absurd h hx0
    have hq' : (k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0 := by
      have h4 : (((k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ) = 0 := by
        linear_combination 4 * hq
      exact_mod_cast h4
    have hf : ((k : ℤ) - j) * ((k : ℤ) + j - 2) = 0 := by linear_combination hq'
    have hjk : j = k := by
      rcases mul_eq_zero.mp hf with h | h
      · omega
      · omega
    rw [hx, hjk]
    simp
  · have hwl := wt_low hL hx
    refine ih (j - 2) (by omega) (L x) hL0 ?_
    rw [hwl, show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega]

end

theorem sl2Low : UpperTheory.V.Br.Sl2Low := by
  intro V _ _ W R L H k hk hR hL hC hC' h0 hW hRH hLH hex
  obtain ⟨x, hx0, n, hx⟩ := hex
  have hb := bound hL hC h0 hW hLH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hf : (n - k) * (n + k - 2) = n * (n - 2) - k * (k - 2) := by ring
  rcases le_or_gt (k : ℤ) n with hn | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j := ⟨n.toNat, by omega⟩
    obtain ⟨y, hy0, hy1, hy2⟩ := descend hk hL hC h0 hW hLH j x hx0 hx
    exact ⟨y, hy0, Or.inl ⟨hy1, hy2⟩⟩
  · have hn2 : n + k - 2 ≤ 0 := by nlinarith
    obtain ⟨j, hj⟩ : ∃ j : ℕ, -n = j := ⟨(-n).toNat, by omega⟩
    have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [show (-W) * R - R * (-W) = -(W * R - R * W) by noncomm_ring, hR]
      module
    have hC2 : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - ((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hC']
      congr 1
      rw [neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]
    have hx' : (-W) x = ((j : ℤ) : ℂ) • x := by
      rw [LinearMap.neg_apply, hx, ← neg_smul, ← hj]
      push_cast
      rfl
    obtain ⟨y, hy0, hy1, hy2⟩ :=
      descend (W := -W) (R := L) (L := R) (H := H) hk hL' hC2 h0 hW' hRH j x hx0 hx'
    refine ⟨y, hy0, Or.inr ⟨?_, hy2⟩⟩
    rw [neg_smul, ← hy1, LinearMap.neg_apply, neg_neg]

end UpperTheory.V.Br
end
