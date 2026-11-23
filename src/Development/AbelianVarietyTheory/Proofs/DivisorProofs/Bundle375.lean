module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle303
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonInteger
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle307
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.exists_clopen_integral_of_smooth_over_field' : ∀ (F : Type) [Field F] (Z : Scheme.{0}) (q : Z ⟶ Sp F), Smooth q → ∀ z : Z, ∃ (W' : Scheme.{0}) (j : W' ⟶ Z), IsClosedImmersion j ∧ IsOpenImmersion j ∧ IsIntegral W' ∧ z ∈ Set.range j := by
  first | exact @GlobalTheory.exists_clopen_integral_of_smooth_over_field | exact GlobalTheory.exists_clopen_integral_of_smooth_over_field | (intros; apply GlobalTheory.exists_clopen_integral_of_smooth_over_field <;> assumption)
end

section

open scoped SchwartzMap NNReal ContDiff
open GlobalTheory.Published.Metaplectic

namespace GlobalTheory.SchwartzTranslateLip

theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K N k n : ℕ) (hk : k ≤ K) (hn : n ≤ N) (a : V) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K *
        ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) := by
  set B := 2 ^ K * ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) = (fun z => f (z + a)) - ⇑f := by
    funext z; simp
  have eit : iteratedFDeriv ℝ n ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) x
      = iteratedFDeriv ℝ n f (x + a) - iteratedFDeriv ℝ n f x := by
    rw [efun, iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    c0.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
      (‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => x + s • a) a s := by
      simpa using ((hasDerivAt_id s).smul_const a).const_add x
    exact ((hd (x + s • a)).hasFDerivAt.comp_hasDerivAt s hl).const_smul (‖x‖ ^ k)
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a‖ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by
    intro s hs
    set y := x + s • a with hy
    have hsa : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    have hx : ‖x‖ ≤ ‖y‖ + ‖a‖ := by
      have h4 := norm_sub_le y (s • a)
      rw [show y - s • a = x by simp [hy]] at h4
      linarith
    have hx2 : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg a, norm_nonneg y, mul_nonneg (norm_nonneg a) (norm_nonneg y)]
    have ha1 : 1 ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    have hxk : ‖x‖ ^ k ≤ (1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k := by
      calc ‖x‖ ^ k ≤ ((1 + ‖a‖) * (1 + ‖y‖)) ^ k := pow_le_pow_left₀ (norm_nonneg _) hx2 k
        _ = (1 + ‖a‖) ^ k * (1 + ‖y‖) ^ k := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have hop : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖ := by
      rw [← norm_fderiv_iteratedFDeriv]; exact (fderiv ℝ (iteratedFDeriv ℝ n f) y).le_opNorm a
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, N + 1)) (k := k)
      (n := n + 1) hk (by simp; omega) f y
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖x‖ ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖
        ≤ ((1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k) * (‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖) := by gcongr
      _ = ‖a‖ * (1 + ‖a‖) ^ K * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f y‖) := by ring
      _ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by gcongr
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := 1) (fun s _ => (hderiv s).hasDerivWithinAt) hbound (by simp) (by simp)
  simp only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one] at key
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key

theorem translate_sub_le : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
      p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f := by
  intro V _ _ p hp
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  set K := s.sup Prod.fst
  set N := s.sup Prod.snd
  refine ⟨(C * 2 ^ K) • (Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2,
    K, ?_, fun a f => ?_⟩
  · have h : Continuous ⇑((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) :=
      Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
    rw [Seminorm.coe_smul]
    exact h.const_smul _
  set S := ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have h1 : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S) := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    exact seminorm_translate_sub_le K N i.1 i.2 (Finset.le_sup (f := Prod.fst) hi)
      (Finset.le_sup (f := Prod.snd) hi) a f
  have h2 := hC (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
  rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  push_cast
  calc p (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (SchwartzMap.compSubConstCLM ℂ (-a) f - f) := h2
    _ ≤ (C : ℝ) * (‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K * S)) := by gcongr
    _ = _ := by ring

end GlobalTheory.SchwartzTranslateLip
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_schwartz_eq_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  first | exact @GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | exact GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | (intros; apply GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form <;> assumption)
end

section


theorem _root_.GlobalTheory.T.modulation_invariant_functional_kills_linear_multiple : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  first | exact @GlobalTheory.CharInvForm.kills_linear_mul | exact GlobalTheory.CharInvForm.kills_linear_mul | (intros; apply GlobalTheory.CharInvForm.kills_linear_mul <;> assumption)
end

section

open Filter Topology


theorem _root_.GlobalTheory.T.polynomial_growth_of_periodic_integral_spans : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ), ContinuousOn lam {s : ℂ | s.re < 0} → (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lam s)) → (∀ s : ℂ, s.re < 0 → ∀ z : Fin g → ℂ, (∃ n : Fin m → ℤ, z = ∑ j, n j • lam (s + 2 * Real.pi * Complex.I) j) ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam s j) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.StripGrowth.strip_growth | exact GlobalTheory.StripGrowth.strip_growth | (intros; apply GlobalTheory.StripGrowth.strip_growth <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  first | exact @GlobalTheory.WpFam.RowReal.row_real | exact GlobalTheory.WpFam.RowReal.row_real | (intros; apply GlobalTheory.WpFam.RowReal.row_real <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.tsum_residueClass_split_by_sign : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (R : ℤ → ℂ), Summable (fun n : ℤ => R ((r.val : ℤ) + n * N)) → ∑' n : ℤ, R ((r.val : ℤ) + n * N) = (if r = 0 then R 0 else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = r then R ((d : ℕ) : ℤ) else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = -r then R (-((d : ℕ) : ℤ)) else 0) := by
  first | exact @GlobalTheory.WpFam.tsum_residue_class_split | exact GlobalTheory.WpFam.tsum_residue_class_split | (intros; apply GlobalTheory.WpFam.tsum_residue_class_split <;> assumption)
end

section

open ValuativeRel
open scoped Matrix Topology

noncomputable section
namespace GlobalTheory.CondRescale

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one_of_pow_near (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1) : ‖z‖ ≤ 1 := by
  by_contra hz
  push_neg at hz
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hz
  have h1 := h n
  have h2 : ‖z ^ n‖ ≤ ‖z ^ n - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖z ^ n‖ = ‖(z ^ n - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_pow, norm_one] at h2
  linarith

theorem exists_ball_trivial (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ0 t = 1 := by
  have hc : Continuous fun t : k => ‖ψ0 t - 1‖ := (hψ.sub continuous_const).norm
  have h0 : ‖ψ0 0 - 1‖ < 1 := by simp
  have hU : {t : k | ‖ψ0 t - 1‖ < 1} ∈ nhds (0 : k) :=
    (isOpen_lt hc continuous_const).mem_nhds h0
  obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hU
  refine ⟨γ, hγ, fun t ht => ?_⟩
  have hp : ∀ s : k, valuation k s < γ → ∀ n : ℕ, ‖ψ0 s ^ n - 1‖ < 1 := by
    intro s hs n
    have h1 : n • s ∈ {t : k | ‖ψ0 t - 1‖ < 1} :=
      hsub (lt_of_le_of_lt (GlobalTheory.CharDualMat.valuation_nsmul_le s n) hs)
    rw [Set.mem_setOf_eq, AddChar.map_nsmul_eq_pow] at h1
    exact h1
  have hneg : valuation k (-t) < γ := by rwa [Valuation.map_neg]
  have a1 := norm_le_one_of_pow_near _ (hp t ht)
  have a2 := norm_le_one_of_pow_near _ (hp (-t) hneg)
  have hm : ψ0 (-t) * ψ0 t = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 t‖ = 1 := by
    have := congrArg norm hm
    rw [norm_mul, norm_one] at this
    nlinarith [norm_nonneg (ψ0 t), norm_nonneg (ψ0 (-t))]
  exact GlobalTheory.IrredSB.eq_one_of_forall_pow hn (hp t ht)

theorem exists_rescale_conductor_integers [CharZero k]
    (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (hne : ψ0 ≠ 1) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (c * (x * y)) = 1) ↔ x ∈ 𝒪[k] := by
  classical
  let P : k → Prop := fun a => ∀ y ∈ 𝒪[k], ψ0 (a * y) = 1
  obtain ⟨t, ht⟩ : ∃ t : k, ψ0 t ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hne (AddChar.ext _ _ fun s => by simpa using hall s)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one _)
  have hbd : ∀ a, P a → a ≠ 0 → valuation k a < valuation k t := by
    intro a ha ha0
    by_contra hle
    push_neg at hle
    apply ht
    have hmem : t / a ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    have := ha _ hmem
    rwa [mul_div_cancel₀ _ ha0] at this
  obtain ⟨γ, hγ, hball⟩ := exists_ball_trivial ψ0 hψ
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hr1 (Units.mk0 γ hγ)
  have hPr : P (r ^ m) := by
    intro y hy
    apply hball
    rw [map_mul, map_pow]
    calc valuation k r ^ m * valuation k y ≤ valuation k r ^ m * 1 :=
          mul_le_mul' le_rfl ((Valuation.mem_integer_iff _ _).1 hy)
      _ < γ := by simpa using hm
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have hex : ∀ a : k, a ≠ 0 → ∃ n : ℤ, e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro a ha
    have h1 : e (valuation k a) ≠ 0 := by
      intro h
      apply ha
      have : valuation k a = 0 := by
        have h2 : e (valuation k a) = e 0 := by rw [h, map_zero]
        exact e.injective h2
      simpa using this
    obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h1
    exact ⟨Multiplicative.toAdd u, by simpa using hu.symm⟩
  let Q : ℤ → Prop := fun n => ∃ a, P a ∧ a ≠ 0 ∧
    e (valuation k a) = ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨N, hN⟩ := hex t ht0
  have hr0' : r ^ m ≠ 0 := pow_ne_zero _ hr0
  obtain ⟨n1, hn1⟩ := hex _ hr0'
  obtain ⟨n0, ⟨a0, ha0P, ha0, hn0⟩, hmax⟩ := Int.exists_greatest_of_bdd (P := Q)
    ⟨N, fun n ⟨a, ha, ha0, hn⟩ => by
      have h1 : e (valuation k a) < e (valuation k t) := e.strictMono (hbd a ha ha0)
      rw [hn, hN, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt] at h1
      exact h1.le⟩ ⟨n1, r ^ m, hPr, hr0', hn1⟩
  have hdown : ∀ b, P b → b ≠ 0 → valuation k b ≤ valuation k a0 := by
    intro b hb hb0
    obtain ⟨n, hn⟩ := hex b hb0
    have h1 := hmax n ⟨b, hb, hb0, hn⟩
    have h2 : e (valuation k b) ≤ e (valuation k a0) := by
      rw [hn, hn0, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
      exact h1
    exact (map_le_map_iff e).1 h2
  have hv0 : valuation k a0 ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  refine ⟨a0, ha0, fun x => ⟨fun hx => ?_, fun hx y hy => ha0P _ (mul_mem hx hy)⟩⟩
  by_cases hx0 : x = 0
  · rw [hx0]
    exact zero_mem _
  have hP : P (a0 * x) := fun y hy => by
    rw [mul_assoc]
    exact hx y hy
  have h1 := hdown _ hP (mul_ne_zero ha0 hx0)
  rw [Valuation.mem_integer_iff]
  have h2 : valuation k x = valuation k (a0 * x) / valuation k a0 := by
    rw [map_mul, mul_div_cancel_left₀ _ hv0]
  rw [h2]
  exact (div_le_one₀ (zero_lt_iff.2 hv0)).2 h1

end GlobalTheory.CondRescale
end
end

section


theorem _root_.GlobalTheory.T.continuous_character_cocycle_trivial_near_zero : ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  first | exact @GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | exact GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero | (intros; apply GlobalTheory.CocycleChar.cocycle_char_trivial_near_zero <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ] (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  first | exact @GlobalTheory.CharDotKill.charDot_kill | exact GlobalTheory.CharDotKill.charDot_kill | (intros; apply GlobalTheory.CharDotKill.charDot_kill <;> assumption)
end

section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal


theorem _root_.GlobalTheory.T.norm_le_lintegral_ray_iteratedFDeriv' : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) → ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) * (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by
  first | exact @GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv | exact GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv | (intros; apply GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_compact_support_dense : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  first | exact @GlobalTheory.schwartz_mem_closure_hasCompactSupport | exact GlobalTheory.schwartz_mem_closure_hasCompactSupport | (intros; apply GlobalTheory.schwartz_mem_closure_hasCompactSupport <;> assumption)
end
