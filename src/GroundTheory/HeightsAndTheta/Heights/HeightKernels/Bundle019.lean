module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartHessHolo
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.LocalSubring
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {e : ℕ}

def chartInv (y : Fin (e + 1) → ℂ) : Fin (e + 1) → ℂ := fun j => (y 0)⁻¹ * (if j = 0 then 1 else y j)

theorem chartInv_zero (y : Fin (e + 1) → ℂ) : chartInv y 0 = (y 0)⁻¹ := by
  simp [chartInv]

theorem chartInv_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : chartInv (chartInv y) = y := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [chartInv]
  · simp only [chartInv, hj, if_false, if_true]
    field_simp

theorem swap_mulVec_cons (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    swapFirstTwo e *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) =
      y 0 • (Fin.cons 1 (chartInv y) : Fin (e + 1 + 1) → ℂ) := by
  funext p
  rw [swapFirstTwo, PEquiv.toMatrix_toPEquiv_mulVec]
  refine Fin.cases ?_ (fun i => ?_) p
  · simp
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp [chartInv, hy]
    · have h0 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
        exact Fin.succ_ne_zero _
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.cons_succ, Pi.smul_apply,
        smul_eq_mul, chartInv, Fin.succ_ne_zero, if_false]
      field_simp

theorem hermChartPot_swap (M : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hM : M.PosDef)
    (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    hermChartPot ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) y = hermChartPot M (chartInv y) + Real.log ‖y 0‖ := by
  set u : Fin (e + 1 + 1) → ℂ := Fin.cons 1 (chartInv y) with hu
  have hTv := swap_mulVec_cons y hy
  have hq : star (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) ⬝ᵥ
      (((swapFirstTwo e)ᴴ * M * swapFirstTwo e) *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ)) =
      (Complex.normSq (y 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (y 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr hy) (Real.sqrt_pos.mpr hx).ne']
  ring

theorem contDiff_gbPot {D : ℕ} : ContDiff ℝ 2 (gbPot (D := D)) := by
  have hs : ContDiff ℝ 2 fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2 :=
    contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) i))
  have hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2 := fun y => by positivity
  exact (hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'

theorem contDiff_hermChartPot (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ContDiff ℝ 2 (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact (contDiff_gbPot.comp (contDiff_const.add (realCLE P hP).contDiff)).add contDiff_const

theorem contDiffAt_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 chartInv y := by
  have h0 : ContDiffAt ℂ 2 (fun y : Fin (e + 1) → ℂ => (y 0)⁻¹) y :=
    (contDiff_apply ℂ (fun _ => ℂ) (0 : Fin (e + 1))).contDiffAt.inv hy
  refine contDiffAt_pi.2 fun j => ?_
  by_cases hj : j = 0
  · subst hj
    simpa [chartInv] using h0
  · simpa [chartInv, hj] using h0.mul (contDiff_apply ℂ (fun _ => ℂ) j).contDiffAt

def logCoord (y : Fin (e + 1) → ℂ) (y' : Fin (e + 1) → ℂ) : ℂ :=
  Complex.log (y' 0 / y 0) + (Real.log ‖y 0‖ : ℂ)

theorem logCoord_re (y y' : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) (hy' : y' 0 ≠ 0) :
    (logCoord y y').re = Real.log ‖y' 0‖ := by
  rw [logCoord, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hy') (norm_ne_zero_iff.mpr hy)]
  ring

theorem contDiffAt_logCoord {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 (logCoord y) y := by
  have hmem : y 0 / y 0 ∈ Complex.slitPlane := by
    rw [div_self hy]
    exact Complex.one_mem_slitPlane
  exact ((Complex.contDiffAt_log hmem).comp y
    ((contDiff_apply ℂ (fun _ => ℂ) (0 : Fin (e + 1))).contDiffAt.div_const (y 0))).add contDiffAt_const

end ChartEnergySwapHessian


open ChartEnergySwapHessian ChartMongeAmpereAffineInvariance in
theorem ChartEnergySwapInvariant.proof : ChartEnergySwapInvariant.Statement := by
  intro e M N hM hN k
  set S := swapFirstTwo e with hS
  set U : Set (Fin (e + 1) → ℂ) := {y | y 0 ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun (continuous_apply 0) continuous_const
  have hUm : MeasurableSet U := hUo.measurableSet
  have hae : ∀ᵐ y ∂(volume : Measure (Fin (e + 1) → ℂ)), y ∈ U := by
    set K : Submodule ℝ (Fin (e + 1) → ℂ) :=
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (e + 1) => ℂ) 0) with hK
    have hKtop : K ≠ ⊤ := fun h => by
      have hm : (Pi.single 0 1 : Fin (e + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
      simp [hK] at hm
    have h0 := Measure.addHaar_submodule (volume : Measure (Fin (e + 1) → ℂ)) K hKtop
    rw [ae_iff]
    convert h0 using 2
    ext y
    simp [hK, hU]
  set Φ : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ :=
    fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  set f : (Fin (e + 1) → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y ∈ U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
      maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) y = |(fderiv ℝ chartInv y).det| • f (chartInv y) := by
    intro y hy
    have hy : y 0 ≠ 0 := hy
    have hev : ∀ᶠ y' in 𝓝 y, y' 0 ≠ 0 := (continuous_apply 0).continuousAt.eventually_ne hy
    have hΦ' : ∀ j : Fin (e + 1), (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) j =ᶠ[𝓝 y] fun y' => Φ j (chartInv y') + (logCoord y y').re := by
      intro j
      filter_upwards [hev] with y' hy'
      rw [logCoord_re y y' hy hy']
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact hermChartPot_swap M hM y' hy'
      · simp only [hΦ, hj, if_false]
        exact hermChartPot_swap N hN y' hy'
    have hΦs : ∀ j, ContDiffAt ℝ 2 (Φ j) (chartInv y) := fun j => by
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact (contDiff_hermChartPot M hM).contDiffAt
      · simp only [hΦ, hj, if_false]
        exact (contDiff_hermChartPot N hN).contDiffAt
    rw [maDensity_comp_holo _ Φ chartInv (logCoord y) y hΦs (contDiffAt_chartInv hy)
      (contDiffAt_logCoord hy) hΦ', det_fderiv_real ((contDiffAt_chartInv hy).differentiableAt (by norm_num)),
      abs_of_nonneg (Complex.normSq_nonneg _), hermChartPot_swap M hM y hy, hermChartPot_swap N hN y hy, hf,
      smul_eq_mul]
    ring
  have hinj : Set.InjOn chartInv U := fun a ha b hb hab => by
    rw [← chartInv_chartInv (show a 0 ≠ 0 from ha), hab, chartInv_chartInv (show b 0 ≠ 0 from hb)]
  have himage : chartInv '' U = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show chartInv x 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hx
    · intro hy
      refine ⟨chartInv y, ?_, chartInv_chartInv hy⟩
      show chartInv y 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hy
  have hderiv : ∀ y ∈ U, HasFDerivWithinAt chartInv (fderiv ℝ chartInv y) U y := fun y hy =>
    (((contDiffAt_chartInv (show y 0 ≠ 0 from hy)).restrict_scalars ℝ).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  unfold chartMixedEnergy
  calc ∫ y, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y
      = ∫ y in U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∫ y in U, |(fderiv ℝ chartInv y).det| • f (chartInv y) := setIntegral_congr_fun hUm hpt
    _ = ∫ y in chartInv '' U, f y :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f).symm
    _ = ∫ y in U, f y := by rw [himage]
    _ = ∫ y, f y := by rw [Measure.restrict_eq_self_of_ae_mem hae]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ClosedPointUnitSection.exists_valuationSubring {K : Type*} [Field K] (A : Subring K)
    (P : Ideal A) [P.IsPrime] :
    ∃ W : ValuationSubring K, (∀ a : A, (a : K) ∈ W) ∧ (∀ a : A, a ∉ P → W.valuation (a : K) = 1) ∧
      ∀ a : A, a ∈ P → W.valuation (a : K) < 1 := by
  obtain ⟨W, h, hloc⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.ofPrime A P)
  have hA : ∀ a : A, (a : K) ∈ (LocalSubring.ofPrime A P).toSubring :=
    fun a => LocalSubring.le_ofPrime A P a.2
  have key : ∀ a : A, (IsUnit (algebraMap A (LocalSubring.ofPrime A P).toSubring a) ↔ a ∉ P) :=
    fun a => IsLocalization.AtPrime.isUnit_to_map_iff _ P a
  refine ⟨W, fun a => h (hA a), fun a ha => ?_, fun a ha => ?_⟩
  · have hu := ((key a).mpr ha).map (Subring.inclusion h)
    exact (W.valuation_eq_one_iff ⟨a, h (hA a)⟩).mp hu
  · refine lt_of_le_of_ne (W.valuation_le_one ⟨a, h (hA a)⟩) fun h1 => ?_
    have hu : IsUnit (Subring.inclusion h (algebraMap A (LocalSubring.ofPrime A P).toSubring a)) :=
      (W.valuation_eq_one_iff ⟨a, h (hA a)⟩).mpr h1
    exact (key a).mp ((isUnit_map_iff (Subring.inclusion h) _).mp hu) ha

def ClosedPointUnitSection.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 →
      ∀ m : Ideal (curveRing y), m.IsMaximal →
        ∃ (e : ℕ) (g : K'), 1 ≤ e ∧ g ≠ 0 ∧ g ∈ chartLat y 1 e ∧
          ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
            (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) →
              ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def sectionMod (y : (Σ k, ι k) → Ω) : Submodule (curveRing y) Ω where
  carrier := chartLat y (fun _ => 1) 1
  zero_mem' := (chartLat y (fun _ => 1) 1).zero_mem
  add_mem' := fun ha hb => (chartLat y (fun _ => 1) 1).add_mem ha hb
  smul_mem' := fun b m hm c hc => by
    have hb : (b : Ω) ∈ chartRingZ y c := mem_curveRing.mp b.2 c hc
    have hm' := hm c hc
    rw [Subring.smul_def, smul_eq_mul, mul_assoc]
    exact mul_mem hb hm'

abbrev sectionQuot (y : (Σ k, ι k) → Ω) (x : Ω) : Type _ :=
  ↥(sectionMod y) ⧸ (Submodule.span (curveRing y) {x}).comap (sectionMod y).subtype

def curvePtIdeal (y : (Σ k, ι k) → Ω) (W : Ideal (MRing ι)) : Ideal (curveRing y) :=
  Ideal.span {b | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ W ∧ h ∉ W ∧
    (b : Ω) * aeval y h = aeval y g}

end Objects

def SectionQuotFinite.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Finite (sectionQuot y (aeval y s))

def VertPointLength.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.BijOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
          {m | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0} ∧
        ∀ W ∈ divSupp (mCoordIdeal y) s,
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (sectionQuot y (aeval y s))

def VertPointResidue.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s,
        (geoNum 0 W Fin.elim0 : ℝ) * Real.log (charOf W) =
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootPointsFiniteAlt

variable {K : Type*} {ι : K → Type*}

def homog (q : Polynomial ℤ) (p a : Σ k, ι k) : MRing ι :=
  ∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i) * X p ^ i * X a ^ (q.natDegree - i)

theorem homog_mem (y : (Σ k, ι k) → ℂ) (k : K) (i i₀ : ι k) (ha : y ⟨k, i₀⟩ = 1) (q : Polynomial ℤ)
    (hq : q.eval₂ (Int.castRingHom ℂ) (y ⟨k, i⟩) = 0) :
    homog q ⟨k, i⟩ ⟨k, i₀⟩ ∈ mCoordIdeal y := by
  show mConeMap y _ = 0
  have hterm : ∀ n ∈ Finset.range (q.natDegree + 1),
      mConeMap y (C (q.coeff n) * X ⟨k, i⟩ ^ n * X ⟨k, i₀⟩ ^ (q.natDegree - n)) =
        MvPolynomial.C ((q.coeff n : ℂ) * y ⟨k, i⟩ ^ n) * MvPolynomial.X k ^ q.natDegree := by
    intro n hn
    have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
    simp only [mConeMap, map_mul, map_pow, map_intCast, aeval_X, ha, map_one, one_mul]
    conv_rhs => rw [← pow_mul_pow_sub (MvPolynomial.X k) hle]
    rw [aeval_C, eq_intCast (algebraMap ℤ (MvPolynomial K ℂ))]
    ring

  rw [homog, map_sum, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
  have : ∑ n ∈ Finset.range (q.natDegree + 1), (q.coeff n : ℂ) * y ⟨k, i⟩ ^ n = 0 := by
    rw [← hq, Polynomial.eval₂_eq_sum_range]; rfl
  rw [this, map_zero, zero_mul]

theorem homog_eval (z : (Σ k, ι k) → ℂ) (p a : Σ k, ι k) (hza : z a ≠ 0) (q : Polynomial ℤ) :
    eval z (map (Int.castRingHom ℂ) (homog q p a)) =
      z a ^ q.natDegree * q.eval₂ (Int.castRingHom ℂ) (z p / z a) := by

  rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum, homog, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
  simp only [map_mul, map_pow, map_intCast, map_X, eval_X, eq_intCast]
  conv_rhs => rw [← pow_mul_pow_sub (z a) hle, div_pow]
  field_simp

theorem isIntegral_of_pow_eq_one {x : ℂ} {k : ℕ} (hk : 0 < k) (hx : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hx]⟩

theorem rootCoord_isIntegral {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine IsIntegral.det fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hx⟩ := hζ p.1 a c
    exact isIntegral_of_pow_eq_one hk hx

end RootPointsFiniteAlt


open RootPointsFiniteAlt in
theorem RootPointsFinite.proof (h : RootAnchorNonzero.Statement) : RootPointsFinite.Statement := by
  intro f j m ζ hζ
  have hint : ∀ p, ∃ q : Polynomial ℤ, q.Monic ∧ q.eval₂ (Int.castRingHom ℂ) (rootCoord ζ p) = 0 := by
    intro p
    obtain ⟨q, hqm, hq⟩ := rootCoord_isIntegral ζ hζ p
    exact ⟨q, hqm, by rwa [← RingHom.ext_int (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]⟩
  choose q hqm hq using hint
  let S : Set ((Σ _ : Fin f, PlIdx j m) → ℂ) :=
    Set.pi Set.univ fun p => {u | Polynomial.IsRoot ((q p).map (Int.castRingHom ℂ)) u}
  have hS : S.Finite := Set.Finite.pi fun p =>
    Polynomial.finite_setOfPred_isRoot ((hqm p).map _).ne_zero
  have hmem : ∀ z ∈ mcPts (rootPointIdeal ζ),
      (fun p : Σ _ : Fin f, PlIdx j m => z p / z ⟨p.1, plAnchor j m⟩) ∈ S := by
    intro z hz p _
    have hza := h f j m ζ hζ z hz p.1
    have h0 := hz.2 _ (homog_mem (rootCoord ζ) p.1 p.2 (plAnchor j m)
      (by simp [rootCoord, anchor_minor]) (q p) (hq p))
    rw [homog_eval z _ _ hza] at h0
    simpa [Polynomial.IsRoot, Polynomial.eval_map, hza] using h0
  let F : McClasses (rootPointIdeal ζ) → S := Quot.lift
    (fun z => ⟨fun p => z.1 p / z.1 ⟨p.1, plAnchor j m⟩, hmem z.1 z.2⟩) (by
      rintro z z' ⟨c, hc, hz'⟩
      apply Subtype.ext
      funext p
      simp only [hz']
      exact (mul_div_mul_left _ _ (hc p.1)).symm)
  have := hS.to_subtype
  refine Finite.of_injective F ?_
  intro x x'
  induction x using Quot.ind with | mk z => ?_
  induction x' using Quot.ind with | mk z' => ?_
  intro hF
  have hfun := fun p => congrFun (congrArg Subtype.val hF) p
  apply Quot.sound
  refine ⟨fun τ => z'.1 ⟨τ, plAnchor j m⟩ / z.1 ⟨τ, plAnchor j m⟩,
    fun τ => div_ne_zero (h f j m ζ hζ z'.1 z'.2 τ) (h f j m ζ hζ z.1 z.2 τ), ?_⟩
  funext p
  have hza := h f j m ζ hζ z.1 z.2 p.1
  have hza' := h f j m ζ hζ z'.1 z'.2 p.1
  have e : z.1 p / z.1 ⟨p.1, plAnchor j m⟩ = z'.1 p / z'.1 ⟨p.1, plAnchor j m⟩ := hfun p
  rw [div_eq_div_iff hza hza'] at e
  rw [div_mul_eq_mul_div, eq_div_iff hza]
  linear_combination -e

end

end GroundTheory.Heights₂.Heights
end
