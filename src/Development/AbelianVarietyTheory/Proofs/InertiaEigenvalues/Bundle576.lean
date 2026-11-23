module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle554
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByCyclotomicKernelEtalePhiSolutionMemWach
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix

noncomputable section

namespace GlobalTheory.JSW.WhitSmooth

open GroundTheory.Automorphic.FourierWhittaker GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_oneL (F : GA E a → ℂ) (g : GA E a) : chart F g (oneL E a) = F g := by
  have := chart_val F g 1
  simpa using this

theorem chart_whit (F : GA E a → ℂ) (g : GA E a) :
    chart (GlobalTheory.JSW.whit F) g = fun y => ∫ X in vecDomain E (Pos a),
      chart F (uGL X * g) y * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, GlobalTheory.JSW.WhitAlg.whit_eq, mul_assoc]
  · simp only [chart, dif_neg h, zero_mul, integral_zero]

theorem hasFDerivAt_chart_whit {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∫ X in vecDomain E (Pos a), (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
        fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) ∂vecMeasure E (Pos a)) (oneL E a) := by
  rw [chart_whit]
  have hy : oneL E a ∈ invSet E a := isUnit_one
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hm : Continuous fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a) :=
    ((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd
  have hmt : Set.MapsTo (fun p : (Pos a → Ad E) × Lie E a => ((uGL p.1 * g, p.2) : GA E a × Lie E a))
      (Set.univ ×ˢ invSet E a) (Set.univ ×ˢ invSet E a) := fun p hp => ⟨Set.mem_univ _, hp.2⟩
  have hc := h.continuousOn_fderiv.comp hm.continuousOn hmt
  have hc0 := h.continuousOn_chart.comp hm.continuousOn hmt
  obtain ⟨C, hC⟩ := (isCompact_closure_vecDomain.prod hS).exists_bound_of_continuousOn
    (hc.mono (Set.prod_mono (Set.subset_univ _) hSU))
  have hint : ∀ z ∈ invSet E a, Integrable (fun X => chart φ.1 (uGL X * g) z *
      (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    fun z hz => ((((hc0.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨trivial, hz⟩)).mul
      GlobalTheory.JSW.WhitAlg.continuous_psiNeg).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set
      subset_closure
  have hint' : Integrable (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a)) ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ((GlobalTheory.JSW.WhitAlg.continuous_psiNeg.smul (hc.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ => ⟨trivial, hy⟩)).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun z X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) • fderiv ℝ (chart φ.1 (uGL X * g)) z) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz => (hint z hz).1) (hint _ hy) hint'.1
    ?_ (integrable_const C) ?_
  · filter_upwards [ae_restrict_mem measurableSet_vecDomain] with X hX z hz
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hC (X, z) ⟨subset_closure hX, hz⟩
  · refine .of_forall fun X z hz => ?_
    exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt.mul_const _

theorem hasFDerivAt_chart_whit' {φ : Sm E a} (h : Good φ) (g : GA E a) :
    HasFDerivAt (chart (GlobalTheory.JSW.whit φ.1) g)
      (∑ i, GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g • coef i (oneL E a)) (oneL E a) := by
  refine (hasFDerivAt_chart_whit h g).congr_fderiv ?_
  have hy : oneL E a ∈ invSet E a := isUnit_one
  have e : ∀ X : Pos a → Ad E, (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) •
      fderiv ℝ (chart φ.1 (uGL X * g)) (oneL E a) = ∑ i,
        (chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (uGL X * g) (oneL E a) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) • coef i (oneL E a) := fun X => by
    rw [fderiv_chart φ _ hy, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const, ← congrFun (chart_whit _ g) (oneL E a), chart_oneL]
  · have hl := h.lie (Module.finBasis ℝ (Lie E a) i)
    refine (Integrable.smul_const ?_ _)
    simp_rw [chart_oneL]
    exact GlobalTheory.JSW.WhitAlg.integrableOn_whit (ContAut.continuous_of_isOpen_stab E a _ hl.2) g

theorem whit_mem_Sm (φ : Sm E a) (h : Good φ) : GlobalTheory.JSW.whit φ.1 ∈ Sm E a := by
  refine GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt E a {f | ∃ ψ : Sm E a, Good ψ ∧ f = GlobalTheory.JSW.whit ψ.1} ?_ _
    ⟨φ, h, rfl⟩
  rintro f ⟨ψ, hψ, rfl⟩
  exact ⟨_, inferInstance, fun i => GlobalTheory.JSW.whit (lie E a (Module.finBasis ℝ (Lie E a) i) ψ).1,
    fun i => coef i (oneL E a), fun i => ⟨_, hψ.lie _, rfl⟩, hasFDerivAt_chart_whit' hψ⟩

theorem whit_contDiffOn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → ∀ g, ContDiffOn ℝ ∞ (chart (GlobalTheory.JSW.whit φ.1) g) (invSet E a) := by
  intro E _ _ _ a φ hφ g
  exact whit_mem_Sm φ ⟨hφ.left, hφ.level⟩ g

end GlobalTheory.JSW.WhitSmooth
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem isLogJ_pow {e : Per.Fl l} (hJ : InJ (Per.tm e - 1)) {y : Per.Acris l} (hy : IsLogJ (Per.tm e - 1) y) :
    ∀ m : ℕ, IsLogJ (Per.tm (e ^ m) - 1) ((m : Per.Acris l) * y)
  | 0 => by simpa using (isLogJ_zero : IsLogJ (l := l) 0 0)
  | m + 1 => by
    have h := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ (inJ_pow hJ m) hJ (isLogJ_pow hJ hy m) hy
    have e1 : Per.tm (e ^ (m + 1)) - 1 = (Per.tm (e ^ m) - 1) + (Per.tm e - 1) +
        (Per.tm (e ^ m) - 1) * (Per.tm e - 1) := by
      rw [pow_succ, show Per.tm (e ^ m * e) = Per.tm (e ^ m) * Per.tm e from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [e1]
    convert h using 1
    push_cast
    ring

theorem iter_mul (a b : Per.Fl l) (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] (a * b) =
    ((frobeniusEquiv (Per.Fl l) l).symm)^[m] a * ((frobeniusEquiv (Per.Fl l) l).symm)^[m] b := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]

theorem iter_one (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] 1 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem rootT_mul (a b : Per.Fl l) (m : ℕ) : rootT (a * b) m = rootT a m * rootT b m := by
  simp only [rootT, iter_mul, map_mul]

theorem rootT_one (m : ℕ) : rootT (1 : Per.Fl l) m = 1 := by
  simp only [rootT, iter_one, map_one]

theorem exists_gal_log (C : Core l) (x : Per.Fl l) (hx : IsUnit x) (g : GQ l) (c : ℤ_[l])
    (H : ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) :
    ∃ e : Per.Fl l, e.untilt = 1 ∧ Per.σF g x = x * e ∧
      IsLogA e (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t) := by
  obtain ⟨v, hv⟩ := hx.exists_left_inv
  have hxe : Per.σF g x = x * (v * Per.σF g x) := by rw [← mul_assoc, mul_comm x v, hv, one_mul]
  have hre : ∀ m, rootT (v * Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := by
    intro m
    have hu : IsUnit (rootT x m) := by
      have h1 := congrArg (fun z => rootT z m) hv
      simp only [rootT_mul, rootT_one] at h1
      exact ⟨⟨rootT x m, rootT v m, by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    apply hu.mul_left_cancel
    rw [← rootT_mul, ← hxe, H m, mul_comm]
  have he1 : (v * Per.σF g x).untilt = 1 := by
    have := hre 0
    simp only [rootT, Function.iterate_zero, id] at this
    rw [this, TAct.eps_untilt C, one_pow]
  have hr : ∀ m, (rootT (v * Per.σF g x) m : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (C.ζ m ^ (PadicInt.toZModPow m c).val) := by
    intro m
    rw [hre m, SubmonoidClass.coe_pow, C.ε_root m, map_pow]
  obtain ⟨y, hy⟩ := Model.exists_isLogA he1
  exact ⟨_, he1, hxe, GlobalTheory.Pst.NoLog.log_eq C _ c y hr hy ▸ hy⟩

theorem map_inv_units {R : Type} [CommRing R] (f : R →+* R) (u : Rˣ) (h : f u = u) :
    f (↑u⁻¹ : R) = ↑u⁻¹ := by
  have h1 := congrArg f (Units.inv_mul u)
  rw [map_mul, h, map_one] at h1
  calc f (↑u⁻¹ : R) = f ↑u⁻¹ * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem exists_log_unit : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  intro l _ C x hx
  obtain ⟨ω, x₁, N, hxω, hJ, hω⟩ := GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split l x hx
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_acris_log_one_add l _ hJ
  have hpow := isLogJ_pow hJ hy
  obtain ⟨u, hu⟩ := (isUnit_l_Bcris l).pow N
  have hωu : IsUnit ω := isUnit_of_mul_isUnit_left (hxω ▸ hx)
  refine ⟨↑u⁻¹ * algebraMap (Per.Acris l) (Per.Bcris l) y, ?_, fun g c H => ?_⟩
  · have h2 := isLogJ_extends (GlobalTheory.CrisMaps.phiA_extends l) hy
    have h3 : Per.φA l (Per.tm (x₁ ^ l ^ N) - 1) = Per.tm ((x₁ ^ l ^ N) ^ l) - 1 := by
      rw [map_sub, map_one, show Per.φA l (Per.tm (x₁ ^ l ^ N)) = Per.tm ((x₁ ^ l ^ N) ^ l) from
        GlobalTheory.RingIface.phiA_teich l _]
    rw [h3] at h2
    have h1 : GlobalTheory.MemLoc.phiA l y = (l : Per.Acris l) * y := isLogJ_unique h2 (hpow l)
    have hφY : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) y := by
      have : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
          algebraMap _ _ (GlobalTheory.MemLoc.phiA l y) :=
        GlobalTheory.CrisMaps.φB_phiA l y
      rw [this, h1, map_mul, map_natCast]
    have hφu : Per.φB l (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    rw [map_mul, hφu, hφY]
    ring
  · obtain ⟨e, he1, hgx, hle⟩ := exists_gal_log C x hx g c H
    have hgω : Per.σF g ω = ω := hω g e he1 hgx
    have hgx₁ : Per.σF g x₁ = x₁ * e := by
      apply hωu.mul_left_cancel
      rw [← mul_assoc, ← hxω, ← hgx, hxω, map_mul, hgω]
    have hge₁ : Per.σF g (x₁ ^ l ^ N) = x₁ ^ l ^ N * e ^ l ^ N := by rw [map_pow, hgx₁, mul_pow]
    have hle' := TAct.logA_pow C.j_cris he1 hle (l ^ N)
    have hsum := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ hJ (inJ_mu (e := e ^ l ^ N) (by rw [map_pow, he1, one_pow])) hy hle'
    have hσ := isLogJ_extends (GlobalTheory.CrisMaps.sigA_extends g) hy
    have hw : Per.σA g (Per.tm (x₁ ^ l ^ N) - 1) = (Per.tm (x₁ ^ l ^ N) - 1) + mu (e ^ l ^ N) +
        (Per.tm (x₁ ^ l ^ N) - 1) * mu (e ^ l ^ N) := by
      rw [map_sub, map_one, show Per.σA g (Per.tm (x₁ ^ l ^ N)) = Per.tm (Per.σF g (x₁ ^ l ^ N)) from
        GlobalTheory.RingIface.sigA_teich l g _, hge₁, mu,
        show Per.tm (x₁ ^ l ^ N * e ^ l ^ N) = Per.tm (x₁ ^ l ^ N) * Per.tm (e ^ l ^ N) from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [hw] at hσ
    have hy' := isLogJ_unique hσ hsum
    have hσY : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        algebraMap _ _ (GlobalTheory.MemLoc.sigA g y) :=
      GlobalTheory.CrisMaps.σB_sigA g y
    have hσu : Per.σB g (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    have hul : (↑u⁻¹ : Per.Bcris l) * ((l ^ N : ℕ) : Per.Bcris l) = 1 := by
      rw [Nat.cast_pow, ← hu, Units.inv_mul]
    rw [map_mul, hσu, hσY, hy', map_add (f := _), map_mul, map_mul, map_natCast]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA l c, GlobalTheory.RingIface.aB_eq_alg l (Per.zA l c)]
    simp only [Core.tB]
    linear_combination (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) *
      algebraMap (Per.Acris l) (Per.Bcris l) C.t) * hul

end GlobalTheory.LogU
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BdRLatticeGens

variable {l : ℕ} [Fact l.Prime]

theorem iota_sigma {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (g : ↥(GK K)) (b : _root_.Formalism.Per.Bcris l) :
    C.ι (_root_.Formalism.Per.σB (g : GQ l) b) = _root_.Formalism.Per.σD (g : GQ l) (C.ι b) := by
  obtain ⟨b0, rfl⟩ := T.eB.surjective b
  have h1 := (P.PD K).ι_comm g b0
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h1
  rw [← T.actB, ← hF.ι, ← hF.ι, h1, T.actD]

theorem iota_zB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (a : ℤ_[l]) : C.ι (_root_.Formalism.Per.zB l a) = Per.zD l a := by
  rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]

theorem sigma_U' {d : ℕ} {K : FinExt l} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (_root_.Formalism.Per.zB l) * U.map (_root_.Formalism.Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    U'.map (_root_.Formalism.Per.σB (g : GQ l)) = U' * (ρ g).map (_root_.Formalism.Per.zB l) := by
  have h1 : U.map (_root_.Formalism.Per.σB (g : GQ l)) * U'.map (_root_.Formalism.Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (ρ g).map (_root_.Formalism.Per.zB l) = U * U'.map (_root_.Formalism.Per.σB (g : GQ l)) := by
    conv_rhs => rw [← hU g]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : U' * U = 1 := mul_eq_one_comm.1 hUU
  rw [h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem inv_vec {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (_root_.Formalism.Per.zB l) * U.map (_root_.Formalism.Per.σB (g : GQ l)) = U)
    (v : Fin d → _root_.Formalism.Per.BdR l)
    (hv : ∀ g : ↥(GK K), ((ρ g).map (Per.zD l)).mulVec (fun r => _root_.Formalism.Per.σD (g : GQ l) (v r)) = v)
    (g : ↥(GK K)) (r : Fin d) :
    _root_.Formalism.Per.σD (g : GQ l) ((U'.map C.ι).mulVec v r) = (U'.map C.ι).mulVec v r := by
  rw [RingHom.map_mulVec]
  have e1 : (U'.map C.ι).map (_root_.Formalism.Per.σD (g : GQ l)) = U'.map C.ι * (ρ g).map (Per.zD l) := by
    have : (U'.map C.ι).map (_root_.Formalism.Per.σD (g : GQ l)) = (U'.map (_root_.Formalism.Per.σB (g : GQ l))).map C.ι := by
      ext a b; simp [iota_sigma hF g]
    rw [this, sigma_U' ρ U U' hUU hU g, Matrix.map_mul]
    congr 1
    ext a b; simp [iota_zB hF]
  rw [e1, ← Matrix.mulVec_mulVec]
  exact congrFun (congrArg _ (hv g)) r

theorem isUnit_aDp_zA {y : ℤ_[l]} (hy : y ≠ 0) : IsUnit (aDp l (_root_.Formalism.Per.zA l y)) := by
  rw [PadicInt.unitCoeff_spec hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  exact ((PadicInt.unitCoeff hy).isUnit.map _).map _ |>.mul ((isUnit_l_BdRp l).pow _)

theorem oD_int (C : Core l) (y : ℤ_[l]) (x : Om l) :
    C.oD (algebraMap ℚ_[l] (Om l) (y : ℚ_[l]) * x) =
      algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l y)) * C.oD x := by
  rw [map_mul]
  congr 1
  simp only [Core.oD, RingHom.comp_apply, C.o_sec.z]

theorem descend {K : FinExt l} (C : Core l) (hI : C.InvdR) {d : ℕ} (w : Fin d → _root_.Formalism.Per.BdR l)
    (hw : ∀ (g : ↥(GK K)) r, _root_.Formalism.Per.σD (g : GQ l) (w r) = w r) :
    ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z r))) =
        algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l y)) * w r := by
  have hx : ∀ r, ∃ x ∈ K.1, C.oD x = w r := fun r => hI K (w r) (fun g hg => hw ⟨g, hg⟩ r)
  choose x hxK hxw using hx
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  classical
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ_[l] ℚ_[l]
    (Finset.univ.image fun r => (⟨x r, hxK r⟩ : ↥K.1))
  refine ⟨y, fun r => ⟨y • ⟨x r, hxK r⟩, hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))⟩, hy0, fun r => ?_⟩
  rw [← hxw r, ← oD_int]
  congr 1
  change ((y • (⟨x r, hxK r⟩ : ↥K.1) : ↥K.1) : Om l) = _
  rw [← algebraMap_smul ℚ_[l] y, Algebra.smul_def]
  simp

theorem exists_lattice_generators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (_root_.Formalism.Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (_root_.Formalism.Per.zB l) * U.map (_root_.Formalism.Per.σB (g : GQ l)) = U) → (∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → _root_.Formalism.Per.BdR l) (v : Fin m → Fin d → _root_.Formalism.Per.BdR l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zD l)).mulVec (fun r => _root_.Formalism.Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → _root_.Formalism.Per.BdR l) = ∑ i, c i • v i) → ∀ N₀ : ℕ, ∃ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (_root_.Formalism.Per.BdR l)), N₀ ≤ N ∧ (∀ i, |k i| ≤ N) ∧ (∀ r s, C.ι (U r s) ∈ Per.FilD l (-(N : ℤ))) ∧ (∀ r i, (U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) ∧ (∀ i j, β i j ∈ Per.FilD l (-k i)) ∧ U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 := by
  intro l _ K P AI T C hF hI d ρ U U' hUU hU hfam N₀
  have hfil := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  obtain ⟨-, -, hmono, -, hbd, -, -⟩ := hfil
  choose m k c v hv hvF hcF hsum using hfam
  have hUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcol : ∀ (j : Fin d) (a : Fin (m j)), ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, (U.map C.ι).mulVec (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) r =
        algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l y)) * v j a r := by
    intro j a
    obtain ⟨y, z, hy0, hz⟩ := descend (K := K) C hI ((U'.map C.ι).mulVec (v j a))
      (inv_vec hF ρ U U' hUU hU (v j a) (hv j a))
    refine ⟨y, z, hy0, fun r => ?_⟩
    have : (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) =
        (algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l y))) • (U'.map C.ι).mulVec (v j a) := by
      ext s; rw [hz s]; rfl
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hUι, Matrix.one_mulVec]
    rfl
  choose y z hy0 hz using hcol
  choose n hn using hbd

  classical
  let e : Fin (∑ j, m j) ≃ (Σ j : Fin d, Fin (m j)) := finSigmaFinEquiv.symm
  let inv : (p : Σ j : Fin d, Fin (m j)) → _root_.Formalism.Per.BdRp l := fun p => ((isUnit_aDp_zA (hy0 p.1 p.2)).unit⁻¹ : (_root_.Formalism.Per.BdRp l)ˣ)
  let kk : Fin (∑ j, m j) → ℤ := fun i => k (e i).1 (e i).2
  let cc : Matrix (Fin d) (Fin (∑ j, m j)) ↥(OL K) := fun r i => z (e i).1 (e i).2 r
  let β : Matrix (Fin (∑ j, m j)) (Fin d) (_root_.Formalism.Per.BdR l) := fun i j' =>
    if (e i).1 = j' then algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (inv (e i)) * c (e i).1 (e i).2 else 0
  let N : ℕ := max N₀ (max (Finset.univ.sup fun i => (kk i).natAbs) (Finset.univ.sup fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))))
  have hA : ∀ r i, (U.map C.ι * cc.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i =
      algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r := by
    intro r i
    rw [← hz]
    rfl
  refine ⟨N, ∑ j, m j, kk, cc, β, le_max_left _ _, fun i => ?_, fun r s => ?_, fun r i => ?_, fun i j' => ?_, ?_⟩
  · have h1 : (kk i).natAbs ≤ N :=
      le_trans (Finset.le_sup (f := fun i => (kk i).natAbs) (Finset.mem_univ i))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  · have h1 : n (C.ι (U r s)) ≤ N :=
      le_trans (Finset.le_sup (f := fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))) (Finset.mem_univ (r, s)))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    exact hmono _ _ (by simpa using h1) (hn _)
  · rw [hA, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hvF _ _ _)
  · simp only [β]
    split_ifs
    · rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hcF _ _)
    · exact Submodule.zero_mem _
  · ext r j'
    rw [Matrix.mul_apply]
    simp_rw [hA]
    let G : (Σ j : Fin d, Fin (m j)) → _root_.Formalism.Per.BdR l := fun p =>
      algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l (y p.1 p.2))) * v p.1 p.2 r *
        (if p.1 = j' then algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (inv p) * c p.1 p.2 else 0)
    have e1 : ∀ i, algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r * β i j' = G (e i) := fun i => rfl
    simp_rw [e1]
    rw [Equiv.sum_comp e G, Fintype.sum_sigma, Finset.sum_eq_single j']
    · have hs : ∀ a : Fin (m j'), G ⟨j', a⟩ = c j' a * v j' a r := by
        intro a
        show algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l (y j' a))) * v j' a r *
          (if j' = j' then algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (inv ⟨j', a⟩) * c j' a else 0) = _
        rw [if_pos rfl]
        have hu : algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l (y j' a))) *
            algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (inv ⟨j', a⟩) = 1 := by
          rw [← map_mul, show aDp l (_root_.Formalism.Per.zA l (y j' a)) * inv ⟨j', a⟩ = 1 from
            (isUnit_aDp_zA (hy0 j' a)).mul_val_inv, map_one]
        calc _ = (algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (aDp l (_root_.Formalism.Per.zA l (y j' a))) *
            algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) (inv ⟨j', a⟩)) * (c j' a * v j' a r) := by ring
          _ = _ := by rw [hu, one_mul]
      simp_rw [hs]
      have h2 := congrFun (hsum j') r
      rw [Finset.sum_apply] at h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2, Pi.single_apply, Matrix.one_apply]
    · intro j _ hj
      exact Finset.sum_eq_zero fun a _ => by simp [G, hj]
    · intro h; exact absurd (Finset.mem_univ j') h

end GlobalTheory.BdRLatticeGens
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.fixedByCyclotomicKernel_etalePhi_solution_mem_wach :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
      (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R),
      IoW I → ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) R.EE) (A' : Matrix (Fin q) (Fin q) R.EE)
      (Y : Matrix (Fin p) (Fin q) R.EE) (U : Matrix (Fin p) (Fin q) (RW LL)),
      IsUnit A → IsUnit A' → (∀ i j, FixH AI K (U i j)) →
      HMul.hMul (α := Matrix (Fin p) (Fin p) (RW LL)) (β := Matrix (Fin p) (Fin q) (RW LL))
        (A.map I.ioE) (U.map (φRW LL)) =
        HMul.hMul (α := Matrix (Fin p) (Fin q) (RW LL)) (β := Matrix (Fin q) (Fin q) (RW LL))
          U (A'.map I.ioE) + Y.map I.ioE → ∀ i j, U i j ∈ Set.range I.ioE := by
  intro l _ P AI K s LL hG Γ R I hW p q A A' Y U _ hA' hU h i j
  obtain ⟨C, hC⟩ := hA'.exists_right_inv
  let σ := (finProdFinEquiv : Fin p × Fin q ≃ Fin (p * q)).symm
  obtain ⟨e, he⟩ := GlobalTheory.HWL.Rational.vec hG I hW (p * q)
    (fun a b => A (σ a).1 (σ b).1 * C (σ b).2 (σ a).2)
    (fun a => U (σ a).1 (σ a).2) (fun a => hU _ _) (fun a => ⟨_,
      GlobalTheory.HWL.Rational.matrix_eq (I.ioE : R.EE →+* RW LL) (φRW LL : RW LL →+* RW LL)
        A A' C Y U hC h σ a⟩) (σ.symm (i, j))
  rw [σ.apply_symm_apply] at he
  exact ⟨e, he.symm⟩
end
