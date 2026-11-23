module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle539
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle292
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle362
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle536
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle540
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle542
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle541
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle543
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle544
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.topologicalBasis_basic_facts : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι), IsHausdorff I S → (∀ x, (∀ i, TB.c i x = 0) → x = 0) ∧ Function.Injective s ∧ (∀ (L : Ideal S) (n : ℕ), I ^ n ≤ L → ∀ x, x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L) ∧ (∀ z : ι → S, (∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) → ∃ x, ∀ i, TB.c i x = z i) ∧ ∀ a ∈ nonZeroDivisors S, s a ∈ nonZeroDivisors A := by
  first | exact @GlobalTheory.BSP.TopBasis.basic_facts | exact GlobalTheory.BSP.TopBasis.basic_facts | (intros; apply GlobalTheory.BSP.TopBasis.basic_facts <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.closedDiscGaugeCompletion_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), IsUltrametricDist (Disc l u ρ) ∧ (∀ y : Disc l u ρ, ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l) ∧ (∀ (N : Type) [NormedAddCommGroup N], (∀ z : N, l • z = 0 → z = 0) → ∀ F G : Disc l u ρ →+ N, Continuous F → Continuous G → (∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) → F = G) ∧ ∀ (A' A'' : Type) [CommRing A'] [CommRing A''] (u' : A') (u'' : A'') (ρ' ρ'' : ℝ≥0) (f : A →+* A') (f' : A' →+* A'') (F : Disc l u ρ →+* Disc l u' ρ') (F' : Disc l u' ρ' →+* Disc l u'' ρ''), IsDiscMap (l := _) (u := _) (ρ := _) f F → IsDiscMap (l := _) (u := _) (ρ := _) f' F' → IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) := by
  first | exact @GlobalTheory.BSP.DiscBasic.disc_basic | exact GlobalTheory.BSP.DiscBasic.disc_basic | (intros; apply GlobalTheory.BSP.DiscBasic.disc_basic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.mirabolicAverage_eq_coeff_singlePlaceElement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  first | exact @GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | exact GlobalTheory.MirAvg.mirC_eq_coeff_mirEl | (intros; apply GlobalTheory.MirAvg.mirC_eq_coeff_mirEl <;> assumption)
end

section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW Topology

namespace GlobalTheory.JSW.KerDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
def rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := rmul
      map_add' := fun y z => ContinuousLinearMap.ext fun x => Matrix.mul_add (Matrix.of x) (Matrix.of y) (Matrix.of z)
      map_smul' := fun c y => ContinuousLinearMap.ext fun x => Matrix.mul_smul (Matrix.of x) c (Matrix.of y) }

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_rmul_le (y : Lie E a) : ‖rmul y‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ :=
  (rmulL (E := E) (a := a)).le_opNorm y

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_mul_le (x y : Lie E a) :
    ‖toL (Matrix.of x * Matrix.of y)‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ * ‖x‖ :=
  (rmulL (E := E) (a := a)).le_opNorm₂ y x


omit [_root_.NumberField.IsTotallyComplex E] in
theorem eventually_inv_bdd :
    ∀ᶠ Y in 𝓝 (oneL E a), Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < ‖oneL E a‖ + 1 := by
  have hc : ContinuousAt (fun Y : Lie E a => toL (Matrix.of Y)⁻¹) (oneL E a) := by
    have h := continuousAt_matrix_inv (1 : Matrix (Fin a) (Fin a) (Cinf E)) (by
      rw [Matrix.det_one]
      exact NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ))
    exact h
  have h1 : toL (Matrix.of (oneL E a))⁻¹ = oneL E a := by simp
  have h0 : ‖toL (Matrix.of (oneL E a))⁻¹‖ < ‖oneL E a‖ + 1 := by rw [h1]; exact lt_add_one _
  have h2 := hc.norm.eventually (gt_mem_nhds h0)
  exact Filter.Eventually.and (isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)) h2

theorem norm_chart_le (φ : GA E a → ℂ) (g : GA E a) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (Y : Lie E a) :
    ‖chart φ g Y‖ ≤ max C 0 := by
  unfold chart
  split_ifs
  · exact le_max_of_le_left (hC _)
  · simp

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have h := ContinuousOn.measurable_piecewise (hφ g).continuousOn (continuousOn_const (c := (0 : ℂ)))
    isOpen_invSet.measurableSet
  convert h using 1
  funext Y
  by_cases hY : Y ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hY]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hY]
    have hY' : ¬ IsUnit (Matrix.of Y) := hY
    simp [chart, hY']

theorem hasFDerivAt_chart_kerOp_of_bound {X : Type} [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hD : ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖)
    (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  obtain ⟨hkm, hγm, hint⟩ := hk
  obtain ⟨Cφ, hCφ⟩ := hφ
  obtain ⟨CD, hCD⟩ := hD
  set M := ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ with hM
  set B := ‖oneL E a‖ + 1 with hB
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := by positivity
  set s : Set (Lie E a) := {Y | Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < B} with hs_def
  have hs : s ∈ 𝓝 (oneL E a) := eventually_inv_bdd
  set F : Lie E a → X → ℂ := fun Y x => k x * chart φ.1 g (rmul (toL (γ x).val) Y) with hF
  set F' : Lie E a → X → (Lie E a →L[ℝ] ℂ) := fun Y x =>
    k x • (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)).comp (rmul (toL (γ x).val)) with hF'
  have hγL : Measurable fun x => toL (γ x).val := hγm
  have heq : chart (kerOp ν k γ φ.1) g =ᶠ[𝓝 (oneL E a)] fun Y => ∫ x, F Y x ∂ν := by
    filter_upwards [isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)] with Y hY
    obtain ⟨u, hu⟩ := hY
    have hY' : Y = toL u.val := hu.symm
    subst hY'
    rw [chart_val]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change k x * φ.1 (g * infGL E a u * infGL E a (γ x)) = k x * chart φ.1 g (rmul (toL (γ x).val) (toL u.val))
    rw [mul_assoc, ← map_mul, ← chart_val φ.1 g (u * γ x)]
    rfl
  have e1 : ∀ x, rmul (toL (γ x).val) (oneL E a) = toL (γ x).val := fun x => one_mul (γ x).val
  have hF'1 : F' (oneL E a) =
      fun x => k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) := by
    funext x; simp only [hF', e1]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  rw [← hF'1]

  have hmeasF : ∀ Y, AEStronglyMeasurable (F Y) ν := fun Y => by
    refine (hkm.aestronglyMeasurable).mul ?_
    refine ((measurable_chart φ.2 g).comp ?_).aestronglyMeasurable
    exact ((rmulL (E := E) (a := a)).flip Y).continuous.measurable.comp hγL
  have hmeasF' : AEStronglyMeasurable (F' (oneL E a)) ν := by
    rw [hF'1]
    refine hkm.aestronglyMeasurable.smul ?_
    exact (ContinuousLinearMap.compL ℝ (Lie E a) (Lie E a) ℂ).aestronglyMeasurable_comp₂
      ((measurable_fderiv ℝ (chart φ.1 g)).comp hγL).aestronglyMeasurable
      ((rmulL (E := E) (a := a)).continuous.measurable.comp hγL).aestronglyMeasurable

  have hint0 : Integrable (F (oneL E a)) ν := by
    refine Integrable.mono' ((hint 0).mul_const (max Cφ 0)) (hmeasF _) (ae_of_all _ fun x => ?_)
    simp only [hF, norm_mul, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_chart_le φ.1 g hCφ _) (norm_nonneg _)

  set K := max CD 0 * M * B * M with hK
  have hbound : ∀ᵐ x ∂ν, ∀ Y ∈ s, ‖F' Y x‖ ≤ ‖k x‖ * height (γ x) ^ 2 * K := by
    refine ae_of_all _ fun x Y hY => ?_
    have hu : IsUnit (Matrix.of Y) := hY.1
    set y := hu.unit * γ x with hy
    have hyv : rmul (toL (γ x).val) Y = toL y.val := by
      rw [hy, Units.val_mul, IsUnit.unit_spec]; rfl
    have hyi : toL (y⁻¹).val = toL (Matrix.of (toL (γ x)⁻¹.val) * Matrix.of (toL (hu.unit⁻¹).val)) := by
      rw [hy, _root_.mul_inv_rev, Units.val_mul]; rfl
    have hui : ‖toL (hu.unit⁻¹).val‖ ≤ B := by
      rw [Matrix.coe_units_inv, IsUnit.unit_spec]; exact hY.2.le
    have hg1 : ‖toL (γ x).val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x)⁻¹.val)]
    have hg2 : ‖toL (γ x)⁻¹.val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x).val)]
    have hL : ‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ ≤ max CD 0 * (M * B * height (γ x)) := by
      rw [hyv]
      refine (hCD g y).trans ?_
      have h1 : ‖toL (y⁻¹).val‖ ≤ M * B * height (γ x) := by
        rw [hyi]
        refine (norm_mul_le _ _).trans ?_
        gcongr
      calc CD * ‖toL (y⁻¹).val‖ ≤ max CD 0 * ‖toL (y⁻¹).val‖ := by gcongr; exact le_max_left _ _
        _ ≤ _ := by gcongr
    have hR : ‖rmul (toL (γ x).val)‖ ≤ M * height (γ x) := (norm_rmul_le _).trans (mul_le_mul_of_nonneg_left hg1 hM0)
    calc ‖F' Y x‖ ≤ ‖k x‖ * (‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ * ‖rmul (toL (γ x).val)‖) := by
          simp only [hF', norm_smul]
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖k x‖ * ((max CD 0 * (M * B * height (γ x))) * (M * height (γ x))) := by
          have hh0 : 0 ≤ height (γ x) := (norm_nonneg _).trans hg1
          gcongr
      _ = ‖k x‖ * height (γ x) ^ 2 * K := by rw [hK]; ring
  have hdiff : ∀ᵐ x ∂ν, ∀ Y ∈ s, HasFDerivAt (F · x) (F' Y x) Y := by
    refine ae_of_all _ fun x Y hY => ?_
    have hmem : rmul (toL (γ x).val) Y ∈ invSet E a := IsUnit.mul hY.1 (γ x).isUnit
    have h1 : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y))
        (rmul (toL (γ x).val) Y) :=
      ((contDiffAt_chart φ.2 g hmem).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp Y (rmul (toL (γ x).val)).hasFDerivAt).const_mul (k x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Filter.Eventually.of_forall hmeasF) hint0 hmeasF'
    hbound ((hint 2).mul_const K) hdiff

end GlobalTheory.JSW.KerDeriv

namespace GlobalTheory.JSW

theorem hasFDerivAt_chart_kerOp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) :=
  fun E _ _ _ a _ _ ν k γ hk φ hφ hL g =>
    KerDeriv.hasFDerivAt_chart_kerOp_of_bound ν k γ hk φ hφ (GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives E a φ hL) g

end GlobalTheory.JSW
end
end

section

noncomputable section

namespace GlobalTheory.HTBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_dR_frame : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    Module.finrank ↥LL.1 ↥(DdR (P.PD K) (repOf r')) = Module.finrank ℚ_[l] ↥K.1 * m →
    ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) →
    ∃ (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ),
      (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) (repOf r') τ' a) ∧
      (∀ i j, u i j ∈ (P.PD K).Fil (k i)) ∧
      (∀ g : ↥(GK K), (∀ x ∈ LL.1, (g : GQ l) x = x) → ∀ i,
        ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
          (fun j => P.actQdR (g : GQ l) (u i j)) = u i) ∧
      (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
        ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) ∧
      LinearIndependent P.R.BdR u := by
  intro l _ P AI T K LL m r' hdR τ' hτ
  haveI := K.2
  haveI := LL.2
  have hDR : IsDR (P.PD K) (repOf r') := by
    unfold IsDR
    rw [hdR, Module.finrank_fin_fun]
  haveI hfinD : FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) (repOf r')) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · haveI : Subsingleton ((Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) := ⟨fun x y => by
        have h : ∀ z : (Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add a b ha hb => rw [ha, hb, add_zero]
        rw [h x, h y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos (by rw [hdR]; exact Nat.mul_pos Module.finrank_pos hm)
  obtain ⟨m', d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) (repOf r')
    (GlobalTheory.DRFil.filSpans T K LL (repOf r') hDR) τ'
  let u' : Fin m' → Fin m → P.R.BdR := fun i => coordF P LL m (d i)
  have hspan' : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m' → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u' i := by
    intro n y hy
    have hY : (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) ∈
        FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n :=
      Submodule.sum_mem _ fun j _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (hy j)
    have hcY : coordF P LL m (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) = y := by
      funext j'
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finset.sum_apply, Pi.single_apply]
    obtain ⟨r, hr, he⟩ := had.span n _ hY
    refine ⟨fun i => mulF P LL (r i), fun i => mulF_mem_fil P LL K (hr i), ?_⟩
    have e1 := coordF_sm P LL m (GlobalTheory.DRFil.idem P.R.BdR τ')
      (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j)
    rw [mulF_idem P LL K τ' hτ, one_smul, hcY] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1, he, map_sum]
    exact Finset.sum_congr rfl fun i _ => coordF_sm P LL m (r i) (d i)
  have htop : ⊤ ≤ Submodule.span P.R.BdR (Set.range u') := by
    rintro y -
    choose f hf using fun j => (P.PD K).Fil_exh (y j)
    have hn : ∀ j, y j ∈ (P.PD K).Fil (-(∑ j, |f j|)) := by
      intro j
      have hle : -(∑ j, |f j|) ≤ f j := by
        have h1 : |f j| ≤ ∑ j, |f j| :=
          Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 := neg_abs_le (f j)
        linarith
      exact SetLike.le_def.1 (GlobalTheory.DRFil.fil_antitone (P.PD K) hle) (hf j)
    obtain ⟨c, -, hc⟩ := hspan' _ y hn
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  letI : Field P.R.BdR := (GlobalTheory.DRFil.isField_dR T).toField
  have hle1 : m ≤ m' := by
    have h1 := finrank_range_le_card (R := P.R.BdR) u'
    rw [Set.finrank, eq_top_iff.2 htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hle2 : m' ≤ m := by
    have := GlobalTheory.Per.Components.card_le_of_idem_indep (GlobalTheory.DRFil.idem_mul_idem (F := P.R.BdR) τ')
      (GlobalTheory.DRFil.idem_ne_zero (F := P.R.BdR) τ')
      (fun i j => GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥LL.1 (Fin m)).coord j) (d i))
      (fun r hr => had.indep r (by
        rw [GlobalTheory.DRFil.eq_sum_basis (Pi.basisFun ↥LL.1 (Fin m))
          (∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) (r i) (d i))]
        refine Finset.sum_eq_zero fun j _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self]
        rw [hr j, map_zero, LinearMap.zero_apply]))
    simpa using this
  obtain rfl : m = m' := le_antisymm hle1 hle2
  have hind : LinearIndependent P.R.BdR u' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨u', k, fun a => ?_, fun i j => coordF_mem_fil P LL m K (had.mem i).2 j, fun g hg i => ?_,
    hspan', hind⟩
  · rw [had.multV_eq a, Multiset.count_map]
    simp [Finset.sum_boole, eq_comm]
    rfl
  · have h1 := coordF_act P LL m K r' g hg (d i)
    rw [((GlobalTheory.DRFil.mem_DdR (P.PD K) (repOf r') (d i)).1 (had.mem i).1.1) g] at h1
    exact h1.symm

end GlobalTheory.HTBasis

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.HTBasis.htc_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI T K LL m r' ρ hdR τ' hτ K' _hK hL
  obtain ⟨u, k, hcount, hmem, heq, hspan, hind⟩ :=
    GlobalTheory.HTBasis.exists_dR_frame l P AI T K LL m r' hdR τ' hτ
  have hU := GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det (GlobalTheory.HTBasis.thetaOf T) u k hmem hspan hind
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hU).unit, k, hcount, fun g hg => ?_⟩
  have hfix : ∀ x ∈ LL.1, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (hL hx)
  exact GlobalTheory.T.hodgeTateSymbolMatrix_equivariant (GlobalTheory.HTBasis.thetaOf T) r' u k hmem g (heq g hfix)
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ∃ D : Set (GlobalTheory.CellDec.NA E n),
    IsFundamentalDomain ((GlobalTheory.CellDec.NE E n).subgroupOf (GlobalTheory.CellDec.NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  first | exact @GlobalTheory.CellDec.exists_fundamentalDomain_NE | exact GlobalTheory.CellDec.exists_fundamentalDomain_NE | (intros; apply GlobalTheory.CellDec.exists_fundamentalDomain_NE <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

theorem _root_.GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 = starRingEnd ℂ (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) := by
  first | exact @GlobalTheory.RSConj.partial_conj | exact GlobalTheory.RSConj.partial_conj | (intros; apply GlobalTheory.RSConj.partial_conj; all_goals assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ), (∀ i, 0 ≤ v i) → Antitone v →
    (((q : ℝ) ^ GlobalTheory.CellDec.wtS n v : ℝ) : ℂ) *
      (GlobalTheory.JSW.sphW q α (fun i => (v i).toNat) * conj (GlobalTheory.JSW.sphW q β (fun i => (v i).toNat))) *
      (((q : ℝ) ^ (-x * ∑ i, (v i : ℝ)) : ℝ) : ℂ) = GlobalTheory.ZEul.rsTerm q α β x v := by
  first | (exact @GlobalTheory.ZEulLocal.localTerm_eq) | (exact GlobalTheory.ZEulLocal.localTerm_eq) | (intros; apply GlobalTheory.ZEulLocal.localTerm_eq  <;> assumption)
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

theorem _root_.GlobalTheory.T.fourierTransform_uniformRapidDecay_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (ι : Type) (w : ι → ℝ) (𝒞 : Set (ι → (Fin n → Cinf E) → ℂ)), (∀ f ∈ 𝒞, (∀ i, ContDiff ℝ ∞ (f i) ∧ HasCompactSupport (f i)) ∧ ∃ C : ℝ, ∀ i, ∫ y, ‖f i y‖ ∂(infMeasure E n) ≤ C * w i) → (∀ f ∈ 𝒞, ∀ v : Fin n → Cinf E, (fun i y => fderiv ℝ (f i) y v) ∈ 𝒞) → ∀ M : ℕ, ∀ f ∈ 𝒞, ∃ C : ℝ, ∀ i u, ‖infFourier (f i) u‖ * (1 + ‖u‖) ^ M ≤ C * w i := by
  first | exact @GlobalTheory.fourier_decay_family | exact GlobalTheory.fourier_decay_family | (intros; apply GlobalTheory.fourier_decay_family <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

theorem _root_.GlobalTheory.T.herr_cocycle_of_witt_tensor_relations : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  exact @GlobalTheory.NL.HerrCocycleCriterion.cocyc
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

theorem _root_.GlobalTheory.T.herr_class_of_cocycle_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  first | exact @GlobalTheory.NL.HerrClassUniq.class_of_values | exact GlobalTheory.NL.HerrClassUniq.class_of_values | (intros; apply GlobalTheory.NL.HerrClassUniq.class_of_values <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

theorem _root_.GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l]), Continuous lam → (∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1) → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → ∀ g₁ : ↥((HW l).W K s LL h).GKs, lam g₁ = Multiplicative.ofAdd 1 → ∀ z₁ ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₁ = ((F l).E K s LL h).tie.jD T z₁ → ∀ g : ↥((HW l).W K s LL h).GKs, ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = ((F l).E K s LL h).tie.jD T z := by
  first | exact @GlobalTheory.NL.ZVal.zval | exact GlobalTheory.NL.ZVal.zval | (intros; apply GlobalTheory.NL.ZVal.zval <;> assumption)
end
