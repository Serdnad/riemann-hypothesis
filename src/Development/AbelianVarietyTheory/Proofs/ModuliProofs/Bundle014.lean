module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle004
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Algebraic.Defs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfNormResultantEq
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle011
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_veryGeneral_point_of_holomorphic_family :
    ∀ (o : Type) [CommRing o] [Countable o] (em : o →+* ℂ) (I : Type) [Countable I] (m : ℕ) (B : Set (Fin m → ℂ)) (θ : (Fin m → ℂ) → I → ℂ), IsOpen B → IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) → ∃ z ∈ B, ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPolynomial I o, MvPolynomial.eval₂ em (c • θ z) F = 0 → ∀ z' ∈ B, ∀ c' : ℂ, c' ≠ 0 → MvPolynomial.eval₂ em (c' • θ z') F = 0 := by
  intro o _ _ em I _ m B θ hB hBc hBne hθ
  classical
  have : Countable (MvPolynomial I o) :=
    Function.Surjective.countable
      (f := (AddMonoidAlgebra.ofCoeff : ((I →₀ ℕ) →₀ o) → MvPolynomial I o))
      fun F => ⟨AddMonoidAlgebra.coeff F, rfl⟩

  set Ω : Set (Fin (m + 1) → ℂ) := {p | Fin.tail p ∈ B ∧ p 0 ∈ ({0}ᶜ : Set ℂ)} with hΩ
  have htail : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => Fin.tail p) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hhead : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => p 0) := differentiable_apply _
  have hΩo : IsOpen Ω :=
    (hB.preimage htail.continuous).inter (isOpen_compl_singleton.preimage hhead.continuous)
  have hΩimg : Ω = (fun q : (Fin m → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (m + 1) → ℂ)) ''
      (B ×ˢ ({0}ᶜ : Set ℂ)) := by
    ext p
    constructor
    · intro hp
      exact ⟨(Fin.tail p, p 0), ⟨hp.1, hp.2⟩, Fin.cons_self_tail p⟩
    · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, rfl⟩
      exact ⟨by simpa using hz, by simpa using hc⟩
  have hΩc : IsPreconnected Ω := by
    rw [hΩimg]
    refine (hBc.prod (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected).image _ ?_
    · rw [Complex.rank_real_complex]; norm_num
    · exact (Continuous.finCons (A := fun _ => ℂ) continuous_snd continuous_fst).continuousOn
  have hΩne : Ω.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hBne
    exact ⟨Fin.cons 1 z₀, by simpa using hz₀, by simp⟩

  let f : MvPolynomial I o → (Fin (m + 1) → ℂ) → ℂ :=
    fun F p => MvPolynomial.eval₂ em (p 0 • θ (Fin.tail p)) F
  have hfd : ∀ F, DifferentiableOn ℂ (f F) Ω := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a =>
      simp only [f, MvPolynomial.eval₂_C]
      exact differentiableOn_const _
    | add F G hF hG =>
      simp only [f, MvPolynomial.eval₂_add]
      exact hF.add hG
    | mul_X F a hF =>
      have ha : DifferentiableOn ℂ (fun p : Fin (m + 1) → ℂ => θ (Fin.tail p) a) Ω :=
        (hθ a).comp htail.differentiableOn fun p hp => hp.1
      simp only [f, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.smul_apply, smul_eq_mul]
      exact hF.mul (hhead.differentiableOn.mul ha)
  have hfa : ∀ F, AnalyticOnNhd ℂ (f F) Ω := fun F =>
    ReciprocityTheory.AnForm.Osgood.osgood (m + 1) Ω (f F) hΩo (hfd F)

  let W : MvPolynomial I o → Set (Fin (m + 1) → ℂ) := fun F =>
    if Set.EqOn (f F) 0 Ω then Set.univ else (Ω ∩ f F ⁻¹' {0}ᶜ) ∪ (closure Ω)ᶜ
  have hWo : ∀ F, IsOpen (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact isOpen_univ
    · simp only [W, if_neg h]
      exact ((hfd F).continuousOn.isOpen_inter_preimage hΩo isOpen_compl_singleton).union
        isClosed_closure.isOpen_compl
  have hWd : ∀ F, Dense (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact dense_univ
    · simp only [W, if_neg h]
      have hsub : Ω ⊆ closure (Ω ∩ f F ⁻¹' {0}ᶜ) := by
        intro q hq
        by_contra hq'
        apply h
        refine (hfa F).eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc hq ?_
        have hn : (closure (Ω ∩ f F ⁻¹' {0}ᶜ))ᶜ ∩ Ω ∈ nhds q :=
          Filter.inter_mem (isClosed_closure.isOpen_compl.mem_nhds hq') (hΩo.mem_nhds hq)
        filter_upwards [hn] with p hp
        by_contra hne
        exact hp.1 (subset_closure ⟨hp.2, hne⟩)
      intro x
      by_cases hx : x ∈ closure Ω
      · exact closure_mono Set.subset_union_left (closure_minimal hsub isClosed_closure hx)
      · exact subset_closure (Or.inr hx)

  obtain ⟨p, hpΩ, hpW⟩ := (dense_iInter_of_isOpen hWo hWd).inter_open_nonempty Ω hΩo hΩne
  refine ⟨Fin.tail p, hpΩ.1, p 0, hpΩ.2, fun F hF z' hz' c' hc' => ?_⟩
  by_cases h : Set.EqOn (f F) 0 Ω
  · have hmem : (Fin.cons c' z' : Fin (m + 1) → ℂ) ∈ Ω := ⟨by simpa using hz', by simpa using hc'⟩
    simpa [f] using h hmem
  · have hpW' := Set.mem_iInter.1 hpW F
    simp only [W, if_neg h] at hpW'
    rcases hpW' with hp' | hp'
    · exact absurd hF hp'.2
    · exact absurd (subset_closure hpΩ) hp'

end GlobalTheory
end

section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory
namespace RapidFourier

noncomputable def linForm {n : ℕ} (ν : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ k, (ν k : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k

theorem linForm_apply {n : ℕ} (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    linForm ν x = ∑ k, (ν k : ℝ) * x k := by
  simp [linForm]

theorem norm_linForm_le {n : ℕ} (ν : Fin n → ℤ) : ‖linForm ν‖ ≤ ∑ k, |(ν k : ℝ)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun k _ => abs_nonneg _) fun x => ?_
  calc ‖linForm ν x‖ = |∑ k, (ν k : ℝ) * x k| := by rw [linForm_apply, Real.norm_eq_abs]
    _ ≤ ∑ k, |(ν k : ℝ) * x k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |(ν k : ℝ)| * ‖x‖ := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x k)
          (abs_nonneg _)
    _ = (∑ k, |(ν k : ℝ)|) * ‖x‖ := by rw [Finset.sum_mul]

noncomputable def wave (a : ℂ) (t : ℝ) : ℂ := a * cexp (2 * π * I * t)

theorem hasDerivAt_wave (a : ℂ) (t : ℝ) :
    HasDerivAt (wave a) (wave (2 * π * I * a) t) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul (2 * π * I)).cexp.const_mul a).comp_ofReal
  convert (preTransparency := .reducible) h using 1
  · funext y
    simp [wave]
  · simp only [wave, id]
    ring

theorem contDiff_wave (a : ℂ) : ContDiff ℝ ∞ (wave a) := by
  have h : ContDiff ℝ ∞ fun t : ℝ => ((t : ℝ) : ℂ) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul ((contDiff_const.mul h).cexp)

theorem iteratedDeriv_wave (m : ℕ) (a : ℂ) :
    iteratedDeriv m (wave a) = wave ((2 * π * I) ^ m * a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_wave _ t).deriv, pow_succ]
    ring_nf

theorem norm_wave (a : ℂ) (t : ℝ) : ‖wave a t‖ = ‖a‖ := by
  have h : (2 * π * I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [wave, norm_mul, h, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_two_pi_I : ‖(2 * π * I : ℂ)‖ = 2 * π := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    mul_one]
  norm_num

theorem term_eq {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    a * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = wave a (linForm ν x) := by
  rw [wave, linForm_apply]
  push_cast
  rfl

theorem norm_iteratedFDeriv_term_le {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (m : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (wave a ∘ linForm ν) x‖
      ≤ (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_wave a) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_wave, norm_wave, norm_mul,
    norm_pow, norm_two_pi_I, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hpow : ‖linForm ν‖ ^ m ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ m := pow_le_pow_left₀ (norm_nonneg _) hL m
  calc (2 * π) ^ m * ‖a‖ * ‖linForm ν‖ ^ m ≤ (2 * π) ^ m * ‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by ring

theorem summable_inv_one_add_abs_sq : Summable fun m : ℤ => ((1 + |(m : ℝ)|) ^ 2)⁻¹ := by
  have hN : Summable fun k : ℕ => ((1 + (k : ℝ)) ^ 2)⁻¹ := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
    refine h.congr fun k => ?_
    push_cast
    ring_nf
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hN.congr fun k => ?_
    simp
  · refine hN.congr fun k => ?_
    simp

theorem summable_inv_pow (n : ℕ) :
    Summable fun ν : Fin n → ℤ => ((1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n))⁻¹ := by
  have hprod : Summable fun ν : Fin n → ℤ => ∏ k, ((1 + |(ν k : ℝ)|) ^ 2)⁻¹ :=
    GlobalTheory.summable_pi_prod_of_nonneg (f := fun _ (m : ℤ) => ((1 + |(m : ℝ)|) ^ 2)⁻¹)
      (fun _ _ => by positivity) fun _ => summable_inv_one_add_abs_sq
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) hprod
  rw [Finset.prod_inv_distrib]
  apply inv_anti₀ (Finset.prod_pos fun k _ => by positivity)
  calc ∏ k, (1 + |(ν k : ℝ)|) ^ 2 ≤ ∏ _k : Fin n, (1 + ∑ k, |(ν k : ℝ)|) ^ 2 :=
        Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ =>
          pow_le_pow_left₀ (by positivity)
            (add_le_add le_rfl (Finset.single_le_sum (f := fun k => |(ν k : ℝ)|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ k))) 2
    _ = (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]

theorem summable_weighted {n : ℕ} {c : (Fin n → ℤ) → ℂ}
    (hc : ∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) (m : ℕ) :
    Summable fun ν => ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m := by
  obtain ⟨C, hC⟩ := hc (m + 2 * n)
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_)
    ((summable_inv_pow n).mul_left C)
  have hpos : 0 < (1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_assoc, ← pow_add]
  exact hC ν

theorem hasFDerivAt_term {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (wave a ∘ linForm ν)
      ((linForm ν).smulRight (wave (2 * π * I * a) (linForm ν x))) x := by
  have h := (hasDerivAt_wave a (linForm ν x)).hasFDerivAt.comp x (linForm ν).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp

end RapidFourier


open RapidFourier in
theorem contDiff_and_fderiv_tsum_fourier_of_rapid :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) → ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) ∧ ∀ (x : Fin n → ℝ) (j : Fin n), fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) x (Pi.single j 1) = ∑' ν, 2 * π * I * (ν j : ℂ) * c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) :=
  open RapidFourier in
  by
  intro n c hc
  have hfun : (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) =
      fun x => ∑' ν, (wave (c ν) ∘ linForm ν) x := by
    funext x
    exact tsum_congr fun ν => term_eq (c ν) ν x
  have hL : ∀ ν : Fin n → ℤ, ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := fun ν =>
    (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hsum : ∀ m : ℕ, Summable fun ν : Fin n → ℤ =>
      (2 * π) ^ m * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := fun m =>
    (summable_weighted hc m).mul_left _
  have hD : ∀ (ν : Fin n → ℤ) (y : Fin n → ℝ),
      ‖(linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν y))‖ ≤
        (2 * π) ^ 1 * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ 1) := by
    intro ν y
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_wave, norm_mul, norm_two_pi_I, pow_one,
      pow_one]
    calc ‖linForm ν‖ * (2 * π * ‖c ν‖) ≤ (1 + ∑ k, |(ν k : ℝ)|) * (2 * π * ‖c ν‖) :=
          mul_le_mul_of_nonneg_right (hL ν) (by positivity)
      _ = 2 * π * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|)) := by ring
  rw [hfun]
  refine ⟨contDiff_tsum (fun ν => (contDiff_wave (c ν)).comp (linForm ν).contDiff)
    (fun m _ => hsum m) (fun m ν x _ => norm_iteratedFDeriv_term_le (c ν) ν m x), fun x j => ?_⟩
  have h0 : Summable fun ν : Fin n → ℤ => (wave (c ν) ∘ linForm ν) x := by
    refine Summable.of_norm_bounded (hsum 0) fun ν => ?_
    simp [norm_wave]
  have hder := hasFDerivAt_tsum (hsum 1) (fun ν y => hasFDerivAt_term (c ν) ν y) hD h0 x
  have hs : Summable fun ν : Fin n → ℤ =>
      (linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν x)) :=
    Summable.of_norm_bounded (hsum 1) fun ν => hD ν x
  have hap := (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℝ))).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hder.fderiv, hap]
  refine tsum_congr fun ν => ?_
  rw [ContinuousLinearMap.smulRight_apply, ← term_eq, linForm_apply]
  simp [Pi.single_apply, Complex.real_smul]
  ring

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

private theorem submatrix_eq_pt_mul_map_mul_transpose {O H K Γ : Type} [CommRing O] [CommRing H] [Algebra O H] [Field K]
    [Algebra O K] {r : ℕ} (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O)
    (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K)
    (hX : ∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j))
    (e : Fin r ≃ Γ) :
    (Matrix.of X).submatrix e e = Matrix.of (fun i j => pt (e i) (b j)) * D.map (algebraMap O K) *
      Matrix.transpose (Matrix.of (fun i j => pt (e i) (b j))) := by
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, hX]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem isUnit_det_of_bicharacter_of_dvd_trace :
    ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  intro O H K Γ _ _ _ _ _ _ _ _ r b D pt X c hinj hred hpt hX hne hm₁ hm₂ hnd hc hr hdvd
  classical
  haveI : Module.Free O H := Module.Free.of_basis b
  haveI : Module.Finite O H := Module.Finite.of_basis b
  obtain ⟨hfin, hcard, htrace⟩ :=
    finite_card_trace_algHom_of_isReduced_baseChange O H K hred
  let E : Γ ≃ (H →ₐ[O] K) := Equiv.ofBijective pt hpt
  haveI : Finite Γ := Finite.of_equiv _ E.symm
  letI : Fintype Γ := Fintype.ofFinite Γ
  letI : Fintype (H →ₐ[O] K) := Fintype.ofFinite _
  have hcardΓ : Fintype.card Γ = r := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr E, hcard, Module.finrank_eq_card_basis b,
      Fintype.card_fin]

  let e : Fin r ≃ Γ := (Fintype.equivFinOfCardEq hcardΓ).symm
  let P : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => pt (e i) (b j)
  let D' : Matrix (Fin r) (Fin r) K := D.map (algebraMap O K)

  have hXP : (Matrix.of X).submatrix e e = P * D' * Matrix.transpose P := submatrix_eq_pt_mul_map_mul_transpose b D pt X hX e

  have hsum : ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ i, pt (e i) h := by
    intro h
    rw [htrace h, finsum_eq_sum_of_fintype]
    exact (Fintype.sum_equiv (e.trans E) (fun i => pt (e i) h) (fun ga => ga h)
      fun _ => rfl).symm
  have hdvd' : ∀ h : H, ∃ d, Algebra.trace O H h = c * d := fun h => hdvd h
  choose T hT using hdvd'
  let Tm : Matrix (Fin r) (Fin r) O := Matrix.of fun j k => T (b j * b k)

  have hPP : Matrix.transpose P * P = (algebraMap O K c) • Tm.map (algebraMap O K) := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, P, Matrix.of_apply, Matrix.smul_apply,
      Matrix.map_apply, Tm, smul_eq_mul]
    have hjk : algebraMap O K c * algebraMap O K (T (b j * b k)) =
        algebraMap O K (Algebra.trace O H (b j * b k)) := by
      rw [hT, map_mul]
    rw [hjk, hsum]
    exact Finset.sum_congr rfl fun i _ => (map_mul (pt (e i)) (b j) (b k)).symm
  have hTm : (Tm.map (algebraMap O K)).det = algebraMap O K Tm.det :=
    ((algebraMap O K).map_det Tm).symm
  have hD' : D'.det = algebraMap O K D.det := ((algebraMap O K).map_det D).symm
  have hdetP : P.det ^ 2 = algebraMap O K c ^ r * algebraMap O K Tm.det := by
    have h := congrArg Matrix.det hPP
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, hTm] at h
    rw [sq, h]
  have h4 := det_bicharacter_pow_four Γ K X hne hm₁ hm₂ hnd
  rw [← Matrix.det_submatrix_equiv_self e (Matrix.of X), hXP, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hcardΓ] at h4
  have hrK : (r : K) = algebraMap O K c ^ 2 := by
    rw [← map_natCast (algebraMap O K) r, hr, map_pow]

  have key : algebraMap O K c ^ (4 * r) * algebraMap O K (Tm.det ^ 4 * D.det ^ 4) =
      algebraMap O K c ^ (4 * r) * 1 := by
    rw [map_mul, map_pow, map_pow, ← hD', mul_one]
    calc algebraMap O K c ^ (4 * r) * (algebraMap O K Tm.det ^ 4 * D'.det ^ 4)
        = (algebraMap O K c ^ r * algebraMap O K Tm.det) ^ 4 * D'.det ^ 4 := by ring
      _ = (P.det ^ 2) ^ 4 * D'.det ^ 4 := by rw [hdetP]
      _ = (P.det * D'.det * P.det) ^ 4 := by ring
      _ = (r : K) ^ (2 * r) := h4
      _ = algebraMap O K c ^ (4 * r) := by
        rw [hrK, ← pow_mul]
        congr 1
        ring
  have hu : algebraMap O K c ^ (4 * r) ≠ 0 :=
    pow_ne_zero _ (by rwa [ne_eq, map_eq_zero_iff _ hinj])
  have h1 := mul_left_cancel₀ hu key
  rw [← map_one (algebraMap O K)] at h1
  have h2 := hinj h1
  exact isUnit_iff_exists_inv.mpr ⟨Tm.det ^ 4 * D.det ^ 3, by linear_combination h2⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule : ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ), ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) = Q.eval (e : ℚ) := by
  first | exact @GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | exact GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | (intros; apply GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.eq_of_norm_prod_aeval_eq_moduli : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ_[l] Ω] [Algebra.IsAlgebraic ℚ_[l] Ω] (a b : Multiset Ω) (P Q : Polynomial ℚ_[l]), P.map (algebraMap ℚ_[l] Ω) = (a.map fun x => Polynomial.X - Polynomial.C x).prod → Q.map (algebraMap ℚ_[l] Ω) = (b.map fun x => Polynomial.X - Polynomial.C x).prod → (∀ (F : Polynomial ℤ) (u v : ℚ_[l]), algebraMap ℚ_[l] Ω u = (a.map fun x => Polynomial.aeval x F).prod → algebraMap ℚ_[l] Ω v = (b.map fun x => Polynomial.aeval x F).prod → ‖u‖ = ‖v‖) → P = Q := by
  first | exact @GlobalTheory.eq_of_norm_resultant_eq | exact GlobalTheory.eq_of_norm_resultant_eq | (intros; apply GlobalTheory.eq_of_norm_resultant_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.sup_span_X_sub_one_isRadical_and_torsionFree : ∀ (o σ : Type) [CommRing o] (I : Ideal (MvPolynomial σ o)) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (I.IsRadical → (I ⊔ Ideal.span {MvPolynomial.X i - 1}).IsRadical) ∧ ((∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1} → F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1}) := by
  first | exact @GlobalTheory.dehomogenisation_isRadical_and_torsionFree | exact GlobalTheory.dehomogenisation_isRadical_and_torsionFree | (intros; apply GlobalTheory.dehomogenisation_isRadical_and_torsionFree <;> assumption)
end
