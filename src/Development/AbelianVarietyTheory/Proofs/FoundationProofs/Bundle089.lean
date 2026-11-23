module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle053
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle054
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.NumberTheory.ModularForms.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ.ExpBound

theorem series_bound (a : ℕ → ℂ) (ψ : ℂ → ℂ) (C : ℝ)
    (hs : ∀ z : ℂ, C < z.im →
      HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (ψ z)) :
    ∃ B t : ℝ, ∀ w : ℂ, t < w.im → ‖ψ w - a 0‖ ≤ B * Real.exp (-(2 * Real.pi * (w.im - t))) := by
  have hnorm : ∀ (n : ℕ) (z : ℂ), ‖a n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)‖ =
      ‖a n‖ * Real.exp (-(2 * Real.pi * n * z.im)) := by
    intro n z
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re, Complex.mul_im]
  set t0 : ℝ := C + 1 with ht0
  have hz0 : ((t0 : ℂ) * Complex.I).im = t0 := by simp
  have hsm : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0))) := by
    have h1 := (hs ((t0 : ℂ) * Complex.I) (by rw [hz0]; linarith)).summable
    have h2 := summable_norm_iff.mpr h1
    simpa only [hnorm, hz0] using h2
  set B0 : ℝ := ∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) with hB0
  have hle : ∀ n : ℕ, ‖a n‖ * Real.exp (-(2 * Real.pi * n * t0)) ≤ B0 := fun n =>
    hsm.le_tsum n (fun j _ => by positivity)
  have hB0nn : 0 ≤ B0 := tsum_nonneg (fun j => by positivity)
  refine ⟨2 * B0, t0 + 1, fun w hw => ?_⟩
  set ρ : ℝ := Real.exp (-(2 * Real.pi * (w.im - t0))) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hpi := Real.pi_gt_three
  have hρ2 : ρ ≤ 1 / 2 := by
    have h1 : 1 ≤ 2 * Real.pi * (w.im - t0) := by nlinarith
    have h2 := Real.add_one_le_exp (2 * Real.pi * (w.im - t0))
    rw [hρ, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hsh := (hasSum_nat_add_iff' 1).mpr (hs w (by linarith))
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at hsh
  have hg : HasSum (fun n : ℕ => B0 * ρ * ρ ^ n) (B0 * ρ * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0.le (by linarith)).mul_left _
  have hb := tsum_of_norm_bounded hg (f := fun n : ℕ =>
      a (n + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * w)) (fun n => by
    rw [hnorm]
    have e : Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * w.im)) =
        Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t0)) * ρ ^ (n + 1) := by
      rw [hρ, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [e, ← mul_assoc, mul_assoc B0, ← pow_succ']
    exact mul_le_mul_of_nonneg_right (hle (n + 1)) (by positivity))
  rw [hsh.tsum_eq] at hb
  have h3 : B0 * ρ * (1 - ρ)⁻¹ ≤ 2 * B0 * ρ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hB0nn hρ0.le) (show 0 ≤ 1 - 2 * ρ by linarith)]
  have h4 : ρ ≤ Real.exp (-(2 * Real.pi * (w.im - (t0 + 1)))) := by
    rw [hρ]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc ‖ψ w - a 0‖ ≤ B0 * ρ * (1 - ρ)⁻¹ := hb
    _ ≤ 2 * B0 * ρ := h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem bound_at_infinity : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  intro Ω _ _ ε X h φ hφc hφ hsupp
  obtain ⟨φ', C, hφ', hsum⟩ := X.an_exp h
  have hsumN : ∀ z : ℂ, C < z.im → HasSum (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ)) *
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z)) (φ' z) := by
    intro z hz
    have h1 := hsum z hz
    rw [← (Nat.cast_injective (R := ℚ)).hasSum_iff] at h1
    · simpa [Function.comp_def] using h1
    · intro r hr
      have : (X.exp h).coeff r = 0 := by
        by_contra hne
        obtain ⟨n, rfl⟩ := hsupp r hne
        exact hr ⟨n, rfl⟩
      simp [this]
  obtain ⟨B, t, hB⟩ := series_bound (fun n : ℕ => ε ((X.exp h).coeff (n : ℚ))) φ' C hsumN
  simp only [Nat.cast_zero] at hB
  refine ⟨B, t, fun z hz htz => ?_⟩
  have hev : φ =ᶠ[Filter.codiscreteWithin Hs] φ' := Filter.Germ.coe_eq.mp (hφ.symm.trans hφ')
  have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hev z hz
  have hHs : Hs ∈ nhds z := SiegelModel.isOpen_Hs.mem_nhds hz
  have h2 : Hs ∈ nhdsWithin z {z}ᶜ := mem_nhdsWithin_of_mem_nhds hHs
  have h3 : {w : ℂ | t < w.im} ∈ nhdsWithin z {z}ᶜ :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds htz)
  have hl : Filter.Tendsto (fun w => ‖φ w - ε ((X.exp h).coeff 0)‖) (nhdsWithin z {z}ᶜ)
      (nhds ‖φ z - ε ((X.exp h).coeff 0)‖) :=
    (((hφc.continuousAt hHs).sub continuousAt_const).norm.tendsto).mono_left nhdsWithin_le_nhds
  have hc : Continuous fun w : ℂ => B * Real.exp (-(2 * Real.pi * (w.im - t))) := by fun_prop
  refine le_of_tendsto_of_tendsto hl ((hc.tendsto z).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  rcases hw1 with e | e
  · have e' : φ w = φ' w := e
    rw [e']
    exact hB w hw3
  · exact absurd hw2 e

end GlobalTheory.KZ.ExpBound
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.InvFun

open Filter Topology

theorem mob_ofSL_den_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) :
    (ent (ofSL γ) 1 0 : ℂ) * z + (ent (ofSL γ) 1 1 : ℂ) ≠ 0 := by
  have hz' : 0 < z.im := hz
  have e10 : (ent (ofSL γ) 1 0 : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by simp [ent, ofSL]
  have e11 : (ent (ofSL γ) 1 1 : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by simp [ent, ofSL]
  rw [e10, e11]
  intro h0
  have him := congrArg Complex.im h0
  simp at him
  rcases him with hc | hc
  · have hre := congrArg Complex.re h0
    simp [hc] at hre
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    rw [hc, hre] at hdet
    simp at hdet
  · exact absurd hc hz'.ne'

theorem continuousAt_mob_ofSL (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : ContinuousAt (mob (ofSL γ)) z := by
  unfold mob
  exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.div
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt (mob_ofSL_den_ne_zero γ hz)

theorem mob_ofSL_mem (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : mob (ofSL γ) z ∈ Hs := by
  have := SiegelModel.mob_ofSL γ ⟨z, hz⟩
  show 0 < (mob (ofSL γ) z).im
  have e : ((⟨z, hz⟩ : UpperHalfPlane) : ℂ) = z := rfl
  rw [e] at this
  rw [this]
  exact (γ • (⟨z, hz⟩ : UpperHalfPlane)).im_pos

theorem fun_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ) :
    ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := by
  intro hφ han hinv γ z hz
  have e := X.an_sl (ofSL γ) h φ han
  rw [hinv γ, han, Filter.Germ.coe_eq] at e
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 e) z hz
  have h2 : Hs ∈ 𝓝[≠] z := mem_nhdsWithin_of_mem_nhds (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hev : (fun w => φ (mob (ofSL γ) w)) =ᶠ[𝓝[≠] z] φ := by
    filter_upwards [h1, h2] with w hw1 hw2
    rcases hw1 with hw | hw
    · exact hw.symm
    · exact absurd hw2 hw
  have hc1 : ContinuousAt φ z := hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds hz)
  have hc2 : ContinuousAt (fun w => φ (mob (ofSL γ) w)) z :=
    ContinuousAt.comp (f := mob (ofSL γ)) (g := φ)
      (hφ.continuousAt (SiegelModel.isOpen_Hs.mem_nhds (mob_ofSL_mem γ hz))) (continuousAt_mob_ofSL γ hz)
  have t1 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ (mob (ofSL γ) z))) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun w => φ (mob (ofSL γ) w)) (𝓝[≠] z) (𝓝 (φ z)) :=
    (hc1.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  exact tendsto_nhds_unique t1 t2

end GlobalTheory.KZ.InvFun
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ

open UpperHalfPlane ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.KZ.LevelOne

theorem const_of_invariant_bounded :
    ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) →
      (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  intro φ hd hinv hb
  let f : ℍ → ℂ := fun τ => φ τ
  have hfinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := fun γ τ => by
    simp only [f]
    rw [← GlobalTheory.KZ.SiegelModel.mob_ofSL]
    exact hinv γ τ τ.2
  have hs (γ : SL(2, ℤ)) : f ∣[(0 : ℤ)] γ = f := by
    ext τ; simpa [SL_slash_apply] using hfinv γ τ
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine hd.congr fun z hz => ?_
    simp only [Function.comp_apply, f]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hbdd : IsBoundedAtImInfty f := by
    obtain ⟨M, t, h⟩ := hb
    refine isBoundedAtImInfty_iff.2 ⟨M, t + 1, fun τ hτ => ?_⟩
    exact h τ τ.2 (by rw [UpperHalfPlane.coe_im]; linarith [hτ])
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
      holo' := hholo
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hs γ]
        exact hbdd }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  refine ⟨c, fun z hz => ?_⟩
  have := congrFun hc ⟨z, hz⟩
  exact this

end GlobalTheory.KZ.LevelOne
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  first | exact @GlobalTheory.FN.germ_main | exact GlobalTheory.FN.germ_main | (intros; apply GlobalTheory.FN.germ_main <;> assumption)
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isBoundedAt_finsetSum {ι : Type*} (s : Finset ι) (c : OnePoint ℝ) (k : ℤ) {F : ι → ℍ → ℂ}
    (h : ∀ i ∈ s, c.IsBoundedAt (F i) k) : c.IsBoundedAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uOp_modularForm : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k,
      ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  intro N l q k hN hl hq hqd f
  have hq0 : 0 < q := hq.pos
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hU := GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 N l q k (⇑f) hN hl hq hqd hinv
  refine ⟨{ toFun := uOp q ⇑f
            slash_action_eq' := ?_
            holo' := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k 1 (⇑f) hq0 f.holo').1
            bdd_at_cusps' := ?_ }, rfl⟩
  · intro γ hγ
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hγ
    have := hU s hs
    rw [SL_slash] at this
    exact this
  · intro c hc
    rw [GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0]
    exact isBoundedAt_finsetSum _ c k fun j _ => GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level N l k _ hN hl (by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isZeroAt_zero_fun (c : OnePoint ℝ) (k : ℤ) : c.IsZeroAt (0 : ℍ → ℂ) k := fun g _ => by
  simpa using! Filter.zero_zeroAtFilter _

theorem isZeroAt_finset_sum {ι : Type*} (s : Finset ι) (c : OnePoint ℝ) (k : ℤ) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isZeroAt_zero_fun c k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uOp_cuspForm : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  intro N l q k hN hl hq hqd f
  have hinv : ∀ γ ∈ GlobalTheory.Hk.lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ =>
    SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩
  have hU := GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 N l q k (⇑f) hN hl hq hqd hinv
  refine ⟨{ toFun := GlobalTheory.Hk.uOp q ⇑f
            slash_action_eq' := fun A hA => by
              obtain ⟨A, hA, rfl⟩ := hA
              exact hU A hA
            holo' := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k 1 (⇑f) hq.pos (CuspFormClass.holo f)).1
            zero_at_cusps' := fun {c} hc => by
              rw [GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq.pos]
              exact isZeroAt_finset_sum _ c k _ fun j _ =>
                GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.pos) f c hc }, rfl⟩

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem coef_heckeT : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ),
    GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) +
      (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  intro N l q k σ hN hq _ hσ f n
  have hq0 : 0 < q := hq.pos
  obtain ⟨g, hg⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k (q : ℤ) σ hN hσ f
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f
  have hgs := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g
  have hU := GlobalTheory.T.hasSum_heckeUOperatorExplicit q (⇑f) (fun m => GlobalTheory.Hk.coef ⇑f m) hq0 hf
  have hV := GlobalTheory.T.hasSum_heckeVOperatorExplicit q (⇑g) (fun m => GlobalTheory.Hk.coef ⇑g m) hq0 hgs
  have hsum : ∀ τ : ℍ, HasSum (fun m => (GlobalTheory.Hk.coef ⇑f (q * m) +
      (q : ℂ) ^ (k - 1) * (if q ∣ m then GlobalTheory.Hk.coef ⇑g (m / q) else 0)) •
        Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.heckeT k q σ ⇑f τ) := by
    intro τ
    have h2 := (hU τ).add ((hV τ).mul_left ((q : ℂ) ^ (k - 1)))
    have e : GlobalTheory.Hk.heckeT k q σ ⇑f τ =
        GlobalTheory.Hk.uOp q ⇑f τ + (q : ℂ) ^ (k - 1) * GlobalTheory.Hk.vOp q ⇑g τ := by
      rw [hg]; rfl
    rw [e]
    convert h2 using 1 <;> ext m <;> simp only [smul_eq_mul] <;> ring
  rw [GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum _ _ hsum n, ← hg]

end GlobalTheory.Hk
end

section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem eq_of_coef_eq : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k,
    (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  intro N l k hN f g h
  ext τ
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f τ
  have hg := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g τ
  simp_rw [h] at hf
  exact hf.unique hg

end GlobalTheory.Hk
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.glTwoPosRat_conj_principal_congruence : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n), ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  first | exact @GlobalTheory.FN.exists_conj_principal_congruence | exact GlobalTheory.FN.exists_conj_principal_congruence | (intros; apply GlobalTheory.FN.exists_conj_principal_congruence <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius : ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ γ₀ : SL(2, ℤ), ∃ (γ : SL(2, ℤ)) (a d : ℕ) (b : ℤ), a * d = n ∧ ∀ τ : ℍ, mob g ((γ₀ • τ : ℍ) : ℂ) = mob (ofSL γ) (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.HermFN.hermite | exact GlobalTheory.HermFN.hermite | (intros; apply GlobalTheory.HermFN.hermite <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ ε.range) ∧ (∀ x : ℚ, ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ∧ eOm ε 0 = 1 ∧ (∀ x y : ℚ, eOm ε (x + y) = eOm ε x * eOm ε y) ∧ (∀ N : ℕ, 0 < N → IsPrimitiveRoot (eOm ε (1 / N)) N) ∧ ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ ε.range := by
  first | exact @GlobalTheory.FNRoots.main | exact GlobalTheory.FNRoots.main | (intros; apply GlobalTheory.FNRoots.main <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.kroneckerRatio_reduces_to_const_mod_valuation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := by
  first | exact @GlobalTheory.KZ.kronecker_ratio_reduces_to_const | exact GlobalTheory.KZ.kronecker_ratio_reduces_to_const | (intros; apply GlobalTheory.KZ.kronecker_ratio_reduces_to_const <;> assumption)
end
