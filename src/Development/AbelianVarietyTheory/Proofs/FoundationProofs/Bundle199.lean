module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Mathlib.Algebra.Order.Field.GeomSum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariant
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_bdd_den : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K),
    ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hexpS : ∀ c : ring ε.range, ∃ S : Finset Ω, ∀ r, (T.exp (T.io c)).coeff r ∈ Subring.closure (S : Set Ω) := by
    intro c
    have hc : InR ε.range (c : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 c).1 c.2
    exact GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring Ω ε c _ hc (T.exp_io c)
  obtain ⟨Sa, hSa⟩ := hexpS a
  obtain ⟨Sb, hSb⟩ := hexpS b
  have hiob : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have hexpb : T.exp (T.io b) ≠ 0 := by
    intro h
    apply hiob
    exact (injective_iff_map_eq_zero (T.exp : T.K →+* HahnSeries ℚ Ω)).1
      (T.exp : T.K →+* HahnSeries ℚ Ω).injective _ h
  have hf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ hexpb, mul_one]
  classical
  let S : Finset Ω := Sa ∪ Sb ∪ {(T.exp (T.io b)).leadingCoeff⁻¹}
  let A : Subring Ω := Subring.closure (S : Set Ω)
  have hA_a : ∀ r, (T.exp (T.io a)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSa r)
  have hA_b : ∀ r, (T.exp (T.io b)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSb r)
  have hA_l : (T.exp (T.io b)).leadingCoeff⁻¹ ∈ A := Subring.subset_closure (by simp [S])
  have hP := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω A
  have hA_inv := hP.2 _ hA_b hA_l
  have hA_f : ∀ r, (T.exp f).coeff r ∈ A := by
    intro r
    rw [hf]
    exact hP.1 _ _ hA_a hA_inv r
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨D, hD, hDk⟩ := GlobalTheory.T.algebraic_subring_closure_common_denominator Ω S
  exact ⟨D, hD, fun r => hDk _ (hA_f r)⟩

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.LevelLower

def idx (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) : Fin l :=
  ⟨(((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩

lemma idx_cast (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) :
    ((idx l b d j : ℕ) : ZMod l) = (((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l) := by
  simp [idx, ZMod.natCast_zmod_val]

lemma idx_inj (l : ℕ) [NeZero l] (a b d : ℤ) (had : ((a * d : ℤ) : ZMod l) = 1) :
    Function.Injective (idx l b d) := by
  intro j₁ j₂ h
  have h' := congrArg (fun x : Fin l => ((x : ℕ) : ZMod l)) h
  simp only [idx_cast] at h'
  push_cast at h' had
  have e : ((j₁ : ℕ) : ZMod l) = ((j₂ : ℕ) : ZMod l) := by
    linear_combination (a : ZMod l) ^ 2 * h' -
      (((j₁ : ℕ) : ZMod l) - ((j₂ : ℕ) : ZMod l)) * (1 + (a : ZMod l) * d) * had
  apply Fin.ext
  rw [ZMod.natCast_eq_natCast_iff'] at e
  simpa [Nat.mod_eq_of_lt j₁.2, Nat.mod_eq_of_lt j₂.2] using e

lemma coset (L l : ℕ) [NeZero l] (hlL : l ∣ L) (γ : SL(2, ℤ)) (hc : (L : ℤ) ∣ γ 1 0) (j : Fin l) :
    ∃ γ' : SL(2, ℤ), ((L * l : ℕ) : ℤ) ∣ γ' 1 0 ∧
      γ' 1 1 = γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) ∧
      repU l j * (γ : M2) = (γ' : M2) * repU l (idx l (γ 0 1) (γ 1 1) j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
  have hdiv : (l : ℤ) ∣ γ 0 1 + ((j : ℕ) : ℤ) * γ 1 1 -
      (γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0) * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have hj' := idx_cast l (γ 0 1) (γ 1 1) j
    have hd1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at hj' hd1 ⊢
    rw [hj']
    linear_combination (-((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l))) * hd1 -
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) *
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) * hc0
  obtain ⟨B, hB⟩ := hdiv
  obtain ⟨m, hm⟩ := hc
  refine ⟨⟨!![γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0, B; (l : ℤ) * γ 1 0,
      γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + γ 1 0 * hB
  · refine ⟨m, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [hm]; push_cast; ring
  · simp
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [repU, Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination hB | linear_combination -hB

end GlobalTheory.LevelLower

namespace GlobalTheory.LevelLower

lemma slz_sum (k : ℕ) (δ : M2) {ι : Type} [Fintype ι] (F : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => ∑ i, F i τ) τ = ∑ i, slz k δ (F i) τ := by
  simp only [slz, Finset.mul_sum]

lemma slz_smul (k : ℕ) (δ : M2) (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => c * f τ) τ = c * slz k δ f τ := by
  simp only [slz]; ring

lemma per (L : ℕ) (χ : ℤ → ℂ) (hχ : ∀ d, χ (d + L) = χ d) (m : ℤ) : ∀ d : ℤ, χ (d + m * L) = χ d := by
  refine Int.induction_on m ?_ ?_ ?_
  · intro d; simp
  · intro i ih d
    rw [show d + ((i : ℤ) + 1) * (L : ℤ) = (d + (i : ℤ) * L) + L by ring, hχ, ih]
  · intro i ih d
    have := hχ (d + (-(i : ℤ) - 1) * L)
    rw [show d + (-(i : ℤ) - 1) * (L : ℤ) + L = d + -(i : ℤ) * L by ring, ih] at this
    exact this.symm

end GlobalTheory.LevelLower

theorem GlobalTheory.Uo_lowers_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L →
    (∀ d, χ (d + L) = χ d) → MF k (L * l) χ a → MF k L χ (Uo l a) := by
  intro k L l χ a hk hl hlL hχ hMF
  obtain ⟨hP, hI⟩ := hMF
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨hPU, hqs⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hl.pos hP
  obtain ⟨hcoc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk
  have hI' := (hinv (L * l) χ).mp hI
  refine ⟨hPU, ?_⟩
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (qs (Uo l a)) hk).2.2.1]
  intro γ hc
  have hg : qs (Uo l a) = fun τ => ∑ j : Fin l, slz k (repU l j) (qs a) τ := funext hqs
  have hdU : ∀ j : Fin l, 0 < (repU l j).det := by
    intro j; simp [repU, Matrix.det_fin_two_of]; exact hl.pos
  have hdγ : ∀ γ : SL(2, ℤ), 0 < (γ : M2).det := by
    intro γ; rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos

  have had : ((γ 0 0 * γ 1 1 : ℤ) : ZMod l) = 1 := by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2
      rw [Matrix.det_fin_two] at this
      exact this
    have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at h1 hc0 ⊢
    rw [hc0, mul_zero, sub_zero] at h1
    exact h1
  let e : Fin l ≃ Fin l := Equiv.ofBijective (GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1))
    (Finite.injective_iff_bijective.mp (GlobalTheory.LevelLower.idx_inj l _ _ _ had))
  have key : ∀ (τ : ℍ) (j : Fin l), slz k (γ : M2) (slz k (repU l j) (qs a)) τ =
      χ (γ 1 1) * slz k (repU l (e j)) (qs a) τ := by
    intro τ j
    obtain ⟨γ', h1, h2, h3⟩ := GlobalTheory.LevelLower.coset L l hlL γ hc j
    rw [← hcoc _ _ (hdU j) (hdγ γ), h3, hcoc _ _ (hdγ γ') (hdU _), hI' γ' h1,
      GlobalTheory.LevelLower.slz_smul, h2]
    obtain ⟨m, hm⟩ := hc
    have : χ (γ 1 1 - γ 1 0 * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)) = χ (γ 1 1) := by
      rw [hm, show γ 1 1 - (L : ℤ) * m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) =
        γ 1 1 + (-(m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ))) * L by ring,
        GlobalTheory.LevelLower.per L χ hχ]
    rw [this]
    rfl
  rw [hg]
  funext τ
  rw [GlobalTheory.LevelLower.slz_sum]
  simp_rw [key τ]
  rw [← Finset.mul_sum, Equiv.sum_comp e (fun j => slz k (repU l j) (qs a) τ)]
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.MeanSquareEstimates

theorem key (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y)) ∧
      ∑' n : ℕ, ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) ≤ C / y ^ k := by
  have hp := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line h h y hc.1.1 hc.1.1 hy
  set I := ∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))
  have hr := Complex.hasSum_re hp
  have e : (fun n : ℕ => (conj (h n) * h n * ((Real.exp (-4 * π * n * y) : ℝ) : ℂ)).re) =
      fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) := by
    funext n
    rw [Complex.conj_mul']
    norm_cast
  rw [e] at hr
  refine ⟨hr.summable, ?_⟩
  rw [hr.tsum_eq]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))‖ ≤ C / y ^ k := by
    intro x _
    have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
    rw [ofComplex_apply_of_im_pos him, Complex.conj_mul']
    have h1 := hC ⟨(x : ℂ) + y * Complex.I, him⟩
    have h2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by simp [UpperHalfPlane.im]
    rw [h2] at h1
    rw [le_div_iff₀ (by positivity)]
    simpa using h1
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc I.re ≤ ‖I‖ := Complex.re_le_norm I
    _ ≤ C / y ^ k * |1 - 0| := this
    _ = C / y ^ k := by simp

theorem key2 (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (t : ℝ) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ C * (4 * π) ^ k / t ^ k := by
  have hy : 0 < t / (4 * π) := by positivity
  obtain ⟨hs, hb⟩ := key k L χ h hc C hC _ hy
  have e : ∀ n : ℕ, -4 * π * n * (t / (4 * π)) = -(n : ℝ) * t := fun n => by field_simp
  simp only [e] at hs hb
  have e2 : C / (t / (4 * π)) ^ k = C * (4 * π) ^ k / t ^ k := by rw [div_pow]; field_simp
  rw [e2] at hb
  exact (hs.sum_le_tsum _ (fun n _ => by positivity)).trans hb

theorem blk (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (a0 : a 0 = 0) (k : ℕ) (D : ℝ)
    (hD : ∀ t : ℝ, 0 < t → ∀ N : ℕ, ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k)
    (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) := by
  set x : ℝ := (2 : ℝ) ^ (-s) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hD0 : 0 ≤ D := by
    have := hD 1 one_pos 0
    simpa using this
  set G : ℕ → ℕ → ℝ := fun j n => Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) with hG
  have G0 : ∀ j n, 0 ≤ G j n := fun j n => by have := ha n; positivity
  have pt : ∀ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ j ∈ Finset.range N, G j n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [a0, zero_div]; exact Finset.sum_nonneg fun j _ => G0 j 0
    set j := Nat.log 2 n
    have hj1 : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0.ne'
    have hj2 : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hjN : j < N := by
      have : j < 2 ^ j := Nat.lt_two_pow_self
      have := Finset.mem_range.mp hn
      omega
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => G0 i n) (Finset.mem_range.mpr hjN))
    have npos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h2j : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hj1
    have h2j' : (n : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
      have : (n : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hj2
      push_cast at this; rw [pow_succ] at this; linarith
    have P : ((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s ≤ (n : ℝ) ^ k * (n : ℝ) ^ s := by gcongr
    have E : 1 ≤ Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have : (n : ℝ) * ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
      linarith
    have hxj : x ^ j = (((2 : ℝ) ^ j) ^ s)⁻¹ := by
      rw [hxdef, Real.rpow_neg (by norm_num), inv_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have L : (n : ℝ) ^ ((k : ℝ) + s) = (n : ℝ) ^ k * (n : ℝ) ^ s := by
      rw [Real.rpow_add npos, Real.rpow_natCast]
    have R : G j n = a n * (Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
      rw [hG]; dsimp only; rw [hxj]; field_simp
    rw [L, R]
    have an := ha n
    calc a n / ((n : ℝ) ^ k * (n : ℝ) ^ s) ≤ a n / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_mul_of_one_le_right an E
  calc ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N, G j n :=
        Finset.sum_le_sum pt
    _ = ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range N, G j n := Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) *
          ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
        simp only [hG, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (D / (((2 : ℝ) ^ j)⁻¹) ^ k) := by
        gcongr with j _
        exact hD _ (by positivity) N
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * D * x ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inv_pow]; field_simp
    _ = Real.exp 2 * D * ∑ j ∈ Finset.range N, x ^ j := by rw [Finset.mul_sum]
    _ ≤ Real.exp 2 * D * (x ^ 0 / (1 - x)) := by
        gcongr
        rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hx0 hx1
    _ = Real.exp 2 * D / (1 - x) := by rw [pow_zero]; ring

theorem geo (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : s / 3 ≤ 1 - (2 : ℝ) ^ (-s) := by
  have L := Real.log_two_gt_d9
  have h1 : 1 + s * Real.log 2 ≤ (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    linarith [Real.add_one_le_exp (Real.log 2 * s)]
  have hp : 0 < 1 + s * Real.log 2 := by nlinarith
  have h2 : (2 : ℝ) ^ (-s) ≤ 1 / (1 + s * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num), one_div]
    exact inv_anti₀ hp h1
  have h3 : 1 / (1 + s * Real.log 2) ≤ 1 - s / 3 := by
    rw [div_le_iff₀ hp]
    have q : 0 ≤ Real.log 2 - 1 / 3 - s * Real.log 2 / 3 := by nlinarith
    nlinarith [mul_nonneg hs.le q]
  linarith

end GlobalTheory.MeanSquareEstimates

namespace GlobalTheory


open GlobalTheory.MeanSquareEstimates in
theorem rankin_mean_square : ∀ (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ), 1 ≤ k → CF k L χ h → h 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, ‖h n‖ ^ 2 ≤ C * (n : ℝ) ^ k) ∧ (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s)) ∧ ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ C := by
  intro k L χ h hk hc
  obtain ⟨C, hC⟩ := hc.2
  have C0 : 0 ≤ C := le_trans (by positivity) (hC UpperHalfPlane.I)
  set D := C * (4 * π) ^ k with hDdef
  have D0 : 0 ≤ D := by positivity
  have K := key2 k L χ h hc C hC
  have K1 : ∀ t : ℝ, 0 < t → ∀ n : ℕ, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k := by
    intro t ht n
    refine le_trans ?_ (K t ht (n + 1))
    exact Finset.single_le_sum (f := fun m : ℕ => ‖h m‖ ^ 2 * Real.exp (-(m : ℝ) * t)) (fun m _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have h0 : h 0 = 0 := by
    have lim : Tendsto (fun t : ℝ => D / t ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
    have b : ‖h 0‖ ^ 2 ≤ 0 := by
      refine ge_of_tendsto lim ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simpa using K1 t ht 0
    have : ‖h 0‖ = 0 := by nlinarith [norm_nonneg (h 0)]
    exact norm_eq_zero.mp this
  have B : ∀ s : ℝ, 0 < s → ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) :=
    fun s hs N => blk (fun n => ‖h n‖ ^ 2) (fun n => by positivity) (by simp [h0]) k D K s hs N
  have nn : ∀ s : ℝ, ∀ n : ℕ, 0 ≤ ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) := fun s n => by positivity
  refine ⟨h0, ⟨D * Real.exp 1, fun n => ?_⟩, fun s hs => summable_of_sum_range_le (nn s) (B s hs), ⟨3 * (Real.exp 2 * D), fun s hs hs1 => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0, zero_pow (by omega : k ≠ 0)]
    have npos : (0 : ℝ) < n := by exact_mod_cast hn
    have := K1 (n : ℝ)⁻¹ (by positivity) n
    rw [neg_mul, mul_inv_cancel₀ npos.ne', inv_pow, div_inv_eq_mul] at this
    have e : ‖h n‖ ^ 2 = ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 ≤ D * (n : ℝ) ^ k * Real.exp 1 := by gcongr
      _ = D * Real.exp 1 * (n : ℝ) ^ k := by ring
  · have T := Real.tsum_le_of_sum_range_le (nn s) (B s hs)
    have g := geo s hs hs1
    have pos : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
    calc s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ s * (Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s))) := by gcongr
      _ ≤ 3 * (Real.exp 2 * D) := by
        rw [mul_div_assoc', div_le_iff₀ pos]
        have : 0 ≤ Real.exp 2 * D := by positivity
        nlinarith

end GlobalTheory
end
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
  IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
  ∀ j < p ^ N, IsInt (p := p) (c j) := by
  first | exact @GlobalTheory.K5.Orth.orth | exact GlobalTheory.K5.Orth.orth | (intros; apply GlobalTheory.K5.Orth.orth <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp TensorProduct
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def IsUnram (ν : ℚ_[g]ˣ →* ℂˣ) : Prop :=
  ∀ u : ℤ_[g]ˣ, ν (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1

def MapsToProd {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W') : Prop :=
  n = a + b ∧ ∃ (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W'), IsUnram ν₁ ∧ IsUnram ν₂ ∧ Λ ≠ 0 ∧
    ∀ (p : GL (Fin n) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
    (∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) →
    (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j) →
    (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) (a + i) (a + j)) →
    ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
      TensorProduct.map (σ x) (ρ y) (Λ v)

abbrev GLRep (g : ℕ) [Fact g.Prime] : Type 1 := Σ n : ℕ, Rep.{0} ℂ (GL (Fin n) ℚ_[g])

inductive InInd : GLRep g → List (GLRep g) → Prop
  | nil (π : GLRep g) : π.1 = 0 → IsIrrRep π.2.ρ → InInd π []
  | cons (π σ ρ : GLRep g) (S : List (GLRep g)) : IsIrrRep π.2.ρ → IsIrrRep ρ.2.ρ → InInd σ S →
      MapsToProd π.2.ρ σ.2.ρ ρ.2.ρ → InInd π (ρ :: S)

end GlobalTheory.GLp.Supp
end
end
