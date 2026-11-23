module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
public import Formalism.PieriBlockIdeals.StatementE
public import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LargeParameterEstimates
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Nat.Factorial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle016
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Coinduced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle931
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.LocalRingCardinality.Bundle004
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Formalism.LocalToGlobal.Divisibility.DefGroup

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgebraicitySecondEisenstein

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L →
    IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  intro L β Ω hst him hΩ
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => mem_algebraicClosure_iff.symm
  have intAlg : ∀ x : ℂ, IsIntegral ℤ x → x ∈ algebraicClosure ℚ ℂ := fun x hx =>
    (alg x).1 (hx.tower_top (A := ℚ)).isAlgebraic
  have natMem : ∀ k : ℕ, (k : ℂ) ∈ algebraicClosure ℚ ℂ := fun k => natCast_mem _ k
  have part2 : ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
    intro M P hM hP
    obtain ⟨h1, -⟩ := GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω M hst him hΩ hM
    obtain ⟨i1, i2⟩ := h1 P hP
    have a1 := intAlg _ i1
    have a2 := intAlg _ i2
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [mul_div_assoc] at a1 a2
    have c1 : (12 * (M : ℂ) ^ 2) = ((12 * M ^ 2 : ℕ) : ℂ) := by push_cast; ring
    have c2 : ((M : ℂ) ^ 3) = ((M ^ 3 : ℕ) : ℂ) := by push_cast; ring
    have n1 : (12 * (M : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hMc)
    have n2 : ((M : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ hMc
    constructor
    · rw [alg]
      have := div_mem a1 (c1 ▸ natMem (12 * M ^ 2))
      rwa [mul_div_cancel_left₀ _ n1] at this
    · rw [alg]
      have := div_mem a2 (c2 ▸ natMem (M ^ 3))
      rwa [mul_div_cancel_left₀ _ n2] at this
  refine ⟨?_, part2⟩
  have hβ0 : β ≠ 0 := by rintro rfl; simp at him
  obtain ⟨S, hS⟩ := kernel_reps_exist L β hβ0 hst
  have hcard := kernel_reps_card L β S hβ0 hst hS
  obtain ⟨t, n, ht, hn, hq⟩ := mul_stable_integral L β hst
  have hs2 := cm_s2 L β S hst him hS
  have hconj : MulStable L (conj β) := fun ω hω => by
    have e : conj β * ω = t • ω - β * ω := by rw [zsmul_eq_mul, ← ht]; ring
    rw [e]
    exact sub_mem (Submodule.smul_mem _ t hω) (hst ω hω)
  have hM : ((S.card + 1 : ℕ) : ℂ) = conj β * β := by
    rw [← Complex.normSq_eq_conj_mul_self]
    have := congrArg (fun r : ℝ => (r : ℂ)) hcard
    push_cast at this ⊢
    exact this
  have hP : ∀ P ∈ S, L.weierstrassP P / Ω ^ 2 ∈ algebraicClosure ℚ ℂ := fun P hP => by
    have hmem : ((S.card + 1 : ℕ) : ℂ) * P ∈ L.lattice := by
      rw [hM, mul_assoc]; exact hconj _ (hS.1 P hP).1
    exact (alg _).1 (part2 _ P (Nat.succ_pos _) hmem).1
  have hβint : IsIntegral ℤ β := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simpa using hq
  have hβm := intAlg _ hβint
  have hcm : conj β ∈ algebraicClosure ℚ ℂ := by
    have e : conj β = (t : ℂ) - β := by rw [← ht]; ring
    rw [e]; exact sub_mem (intCast_mem _ t) hβm
  rw [alg, hs2, div_div, mul_comm (β * _), ← div_div, Finset.sum_div]
  exact div_mem (sum_mem hP) (mul_mem hβm (sub_mem hβm hcm))

end GlobalTheory.AlgebraicitySecondEisenstein
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IsogFormula

theorem main : ∀ (L : PeriodPair) (α β Ω P : ℂ) (M n : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → MulStable L α → Complex.normSq α = n → 0 < n → 0 < M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))) := by
  intro L α β Ω P M n hβ hβim hΩ hα hnorm hn hM hP hMP
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero] at hnorm
    have h0 : n = 0 := by exact_mod_cast hnorm.symm
    omega
  obtain ⟨S, hS⟩ := kernel_reps_exist L α hα0 hα
  have hcard := kernel_reps_card L α S hα0 hα hS
  have hs2 := quasiPeriodConstIsogeny_thm L α S hα0 hα hS
  obtain ⟨t, m, ht, hm, -⟩ := mul_stable_integral L α hα
  have hcardn : S.card + 1 = n := by
    rw [hnorm] at hcard
    exact_mod_cast hcard
  have hVL := (GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω (M * n) hβ hβim hΩ (Nat.mul_pos hM hn)).2
  have hnat : ∀ (k : ℕ) (x : ℂ), x ∈ L.lattice → (k : ℂ) * x ∈ L.lattice := by
    intro k x hx
    have := L.lattice.nsmul_mem hx k
    simpa [nsmul_eq_mul] using this
  have hconj : ∀ ω ∈ L.lattice, conj α * ω ∈ L.lattice := by
    intro ω hω
    have hc : conj α = (t : ℂ) - α := by rw [← ht]; ring
    rw [hc, sub_mul]
    refine L.lattice.sub_mem ?_ (hα ω hω)
    have := L.lattice.smul_mem t hω
    simpa [zsmul_eq_mul] using this
  have hnT : ∀ T ∈ S, (n : ℂ) * T ∈ L.lattice := by
    intro T hT
    have h1 := hconj _ (hS.1 T hT).1
    have hn' : (n : ℂ) = conj α * α := by
      rw [mul_comm, Complex.mul_conj, hnorm]
      simp
    rw [hn', mul_assoc]
    exact h1
  have hs2' : (α ^ 2 - (n : ℂ)) * s2 L = ∑ T ∈ S, L.weierstrassP T := by
    rw [← hs2, hnorm]
    simp
  have hnc : (n : ℂ) = (S.card : ℂ) + 1 := by exact_mod_cast hcardn.symm
  have key : ((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2)
      - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))
      = ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2 := by
    have e1 : ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2
        = ((M * n : ℕ) : ℂ) ^ 2 * (∑ T ∈ S, L.weierstrassP T - (S.card : ℂ) * L.weierstrassP P) / Ω ^ 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [e1, ← hs2']
    rw [show (α ^ 2 - (n : ℂ)) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)
        = ((α ^ 2 - (n : ℂ)) * s2 L + (1 - (n : ℂ)) * L.weierstrassP P) / Ω ^ 2 by ring]
    rw [hnc]
    ring
  rw [key]
  refine IsIntegral.sum _ (fun T hT => ?_)
  refine hVL T P (hS.1 T hT).2 hP ?_ ?_
  · have h := hnat M _ (hnT T hT)
    rw [show ((M * n : ℕ) : ℂ) * T = (M : ℂ) * ((n : ℂ) * T) by push_cast; ring]
    exact h
  · have h := hnat n _ hMP
    rw [show ((M * n : ℕ) : ℂ) * P = (n : ℂ) * ((M : ℂ) * P) by push_cast; ring]
    exact h

end GlobalTheory.IsogFormula
end

section

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem sum_exponent_log_le_of_cut :
    Formalism.CohomologicalDescent.E.ExCut → ∀ (P : Par) (X' A : ℝ), P.Hyp → P.Large → LargeParameterEstimates.Rows P X' A → LargeParameterEstimates.Big P.L P.x X' A →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f → W.Sp.card ≤ 5 →
    ∀ T : ℕ, W.T2.card ≤ T → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
    ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b := by
  intro hC P X' A hH hL hR hB ι _ _ W hW hcard hSp T hT Q hQ
  have hs := Formalism.CohomologicalDescent.E.recursion_sum_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC Formalism.CohomologicalDescent.Top.prime_count_bound_rs
    P hH hL ι W hW hcard hSp Q hQ
  have hTf : W.T2.card ≤ P.f := by rw [← hcard]; exact Finset.card_le_univ _
  have ht := LargeParameterEstimates.tail_bound_holds P X' A _ hH hR hB hTf
  have F := LargeParameterEstimates.large_parameter_facts_of_hyp hH hR hB
  have hb : 0 ≤ P.b := F.b_pos.le
  have hm : (0 : ℝ) ≤ (P.m : ℝ) * P.b * P.L ^ 2 := by positivity
  have hTT : (W.T2.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have key : 30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 ≤ 30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 := by
    nlinarith
  linarith

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.CharModOne

open scoped nonZeroDivisors

section General

variable {E : Type} [Field E] [NumberField E]

def intMap (σ : E ≃ₐ[ℚ] E) (r : 𝓞 E) : 𝓞 E :=
  ⟨σ r, (RingOfIntegers.isIntegral_coe r).map (σ.toAlgHom.restrictScalars ℤ)⟩

def cj (σ : E ≃ₐ[ℚ] E) (M : Submodule (𝓞 E) E) : Submodule (𝓞 E) E where
  carrier := {x | σ x ∈ M}
  add_mem' {x y} hx hy := by
    show σ (x + y) ∈ M
    rw [map_add (f := _)]; exact M.add_mem hx hy
  zero_mem' := by
    show σ 0 ∈ M
    rw [map_zero]; exact M.zero_mem
  smul_mem' r x hx := by
    show σ (r • x) ∈ M
    rw [Algebra.smul_def, map_mul]
    have : σ (algebraMap (𝓞 E) E r) * σ x = intMap σ r • σ x := by
      rw [Algebra.smul_def]; rfl
    rw [this]; exact M.smul_mem _ hx

theorem mem_cj (σ : E ≃ₐ[ℚ] E) (M : Submodule (𝓞 E) E) (x : E) : x ∈ cj σ M ↔ σ x ∈ M := Iff.rfl

theorem cj_mono (σ : E ≃ₐ[ℚ] E) {M N : Submodule (𝓞 E) E} (h : M ≤ N) : cj σ M ≤ cj σ N :=
  fun _ hx => h hx

theorem cj_cj (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M : Submodule (𝓞 E) E) : cj σ (cj σ M) = M := by
  ext x; rw [mem_cj, mem_cj, hσ]

theorem cj_mul_le (σ : E ≃ₐ[ℚ] E) (M N : Submodule (𝓞 E) E) : cj σ M * cj σ N ≤ cj σ (M * N) := by
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  rw [mem_cj, map_mul]
  exact Submodule.mul_mem_mul hx hy

theorem cj_mul (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M N : Submodule (𝓞 E) E) :
    cj σ (M * N) = cj σ M * cj σ N := by
  refine le_antisymm ?_ (cj_mul_le σ M N)
  have h := cj_mono σ (cj_mul_le σ (cj σ M) (cj σ N))
  rwa [cj_cj σ hσ, cj_cj σ hσ, cj_cj σ hσ] at h

theorem one_le_cj_one (σ : E ≃ₐ[ℚ] E) : (1 : Submodule (𝓞 E) E) ≤ cj σ 1 := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨intMap σ y, rfl⟩

theorem cj_one (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) : cj σ (1 : Submodule (𝓞 E) E) = 1 := by
  refine le_antisymm ?_ (one_le_cj_one σ)
  have h := cj_mono σ (one_le_cj_one σ)
  rwa [cj_cj σ hσ] at h

theorem cj_pow (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M : Submodule (𝓞 E) E) (n : ℕ) :
    cj σ (M ^ n) = cj σ M ^ n := by
  induction n with
  | zero => simp [cj_one σ hσ]
  | succ n ih => rw [pow_succ, pow_succ, cj_mul σ hσ, ih]

theorem span_le_cj_span (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (a : E) :
    Submodule.span (𝓞 E) {σ a} ≤ cj σ (Submodule.span (𝓞 E) {a}) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact (mem_cj σ _ _).2 (by rw [hσ]; exact Submodule.mem_span_singleton_self a)

theorem cj_span (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (a : E) :
    cj σ (Submodule.span (𝓞 E) {a}) = Submodule.span (𝓞 E) {σ a} := by
  refine le_antisymm ?_ (span_le_cj_span σ hσ a)
  have h := cj_mono σ (span_le_cj_span σ hσ (σ a))
  rwa [cj_cj σ hσ, hσ] at h

theorem span_mul_span_singleton (a b : E) :
    Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {b} = Submodule.span (𝓞 E) {a * b} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem exists_pow_card_eq_span (𝔞 𝔟 : Submodule (𝓞 E) E) (h : 𝔞 * 𝔟 = 1) :
    ∃ a : E, 𝔞 ^ Fintype.card (ClassGroup (𝓞 E)) = Submodule.span (𝓞 E) {a} := by
  have hfa : IsFractional (𝓞 E)⁰ 𝔞 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (Units.mkOfMulEqOne 𝔞 𝔟 h).isUnit)
  have hfb : IsFractional (𝓞 E)⁰ 𝔟 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (Units.mkOfMulEqOne 𝔟 𝔞 (by rw [mul_comm]; exact h)).isUnit)
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔞, hfa⟩
  let J : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔟, hfb⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) = ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 := pow_card_eq_one (x := ClassGroup.mk E U)
  rw [← map_pow, ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨a, ha⟩ := h1.principal
  refine ⟨a, ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

end General

end GlobalTheory.CharModOne

namespace GlobalTheory.CharModOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem emb_conj (D : D7) (ρ : D.host.E →+* ℂ) (x : D.host.E) :
    ρ (D.host.conj x) = starRingEnd ℂ (ρ x) :=
  D.host.conjE_apply ρ x

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem mod1All_of_isChi : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
    StandardLatticesGL3.Mod1All (χ 𝔞) := by
  intro D χ hχ 𝔞 h𝔞
  set σ := D.host.conj with hσdef
  have hinv : ∀ x, σ (σ x) = x := conj_conj D
  obtain ⟨𝔟, h𝔟, hab⟩ := h𝔞
  have hb : 𝔟 = cj σ 𝔞 := Submodule.ext h𝔟
  have hN1 : ∀ n : ℕ, TaylorLogMetric.N1 D (𝔞 ^ n) := fun n =>
    ⟨𝔟 ^ n, fun x => by rw [hb, ← cj_pow σ hinv]; exact mem_cj σ _ x, by rw [← mul_pow, hab, one_pow]⟩
  have hχpow : ∀ n : ℕ, χ (𝔞 ^ (n + 1)) = χ 𝔞 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ 𝔞 (n + 1), hχ.1 _ _ (hN1 _) ⟨𝔟, h𝔟, hab⟩, ih]; ring
  obtain ⟨a, ha⟩ := exists_pow_card_eq_span 𝔞 𝔟 hab
  set h := Fintype.card (ClassGroup (𝓞 D.host.E)) with hhdef
  have hpos : 0 < h := Fintype.card_pos
  have hb' : 𝔟 ^ h = Submodule.span (𝓞 D.host.E) {σ a} := by rw [hb, ← cj_pow σ hinv, ha, cj_span σ hinv]
  have h1 : Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {σ a} = 1 := by
    rw [← ha, ← hb', ← mul_pow, hab, one_pow]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.bot_mul] at h1
    have : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [← h1, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hσa0 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
  set z : D.host.E := a / σ a with hzdef
  have hσz : σ z = σ a / a := by rw [hzdef, map_div₀, hinv]
  have hz1 : z * σ z = 1 := by rw [hσz, hzdef]; field_simp
  have hz : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, star_eq_conj]
    exact ⟨by rw [mul_comm]; exact hz1, hz1⟩
  have hspan : Submodule.span (𝓞 D.host.E) {z} = 𝔞 ^ (2 * h) := by
    have e1 : z * σ a = a := by rw [hzdef]; field_simp
    calc Submodule.span (𝓞 D.host.E) {z}
        = Submodule.span (𝓞 D.host.E) {z} * (Submodule.span (𝓞 D.host.E) {σ a} * Submodule.span (𝓞 D.host.E) {a}) := by
          rw [mul_comm (Submodule.span (𝓞 D.host.E) {σ a}), h1, mul_one]
      _ = Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {a} := by
          rw [← mul_assoc, span_mul_span_singleton, e1]
      _ = 𝔞 ^ (2 * h) := by rw [← ha, two_mul, pow_add]
  have key : χ 𝔞 ^ (2 * h) = ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ z)⁻¹ := by
    have e := hχ.2 ⟨z, hz⟩
    simp only at e
    rw [hspan] at e
    obtain ⟨k, hk⟩ : ∃ k, 2 * h = k + 1 := ⟨2 * h - 1, by omega⟩
    rw [← e, hk, hχpow]

  have hemb : ∀ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hc : (∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ z)⁻¹) ∈ TaylorLogMetric.Qbar :=
    prod_mem fun τ _ => inv_mem (hemb τ)
  have hx : χ 𝔞 ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2 * h) (by omega) ?_
    rw [key]
    exact mem_algebraicClosure_iff.1 hc
  refine ⟨hx, fun ρ => ?_⟩
  have hw : (⟨χ 𝔞, hx⟩ : TaylorLogMetric.Qbar) ^ (2 * h) = ∏ τ : D.what₂.Tau, (⟨TaylorLogMetric.embT D τ z, hemb τ⟩ : TaylorLogMetric.Qbar)⁻¹ := by
    apply Subtype.ext
    push_cast
    exact key
  have hone : ∀ τ : D.what₂.Tau, ‖ρ ⟨TaylorLogMetric.embT D τ z, hemb τ⟩‖ = 1 := by
    intro τ
    let ρ' : D.host.E →+* ℂ := ρ.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar fun x =>
      mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom))
    have hρ' : ρ' z = ρ ⟨TaylorLogMetric.embT D τ z, hemb τ⟩ := rfl
    have h2 : ρ' z * starRingEnd ℂ (ρ' z) = 1 := by rw [← emb_conj, ← map_mul, hz1, map_one]
    have h3 : ‖ρ' z‖ ^ 2 = 1 := by
      calc ‖ρ' z‖ ^ 2 = ‖ρ' z * starRingEnd ℂ (ρ' z)‖ := by rw [norm_mul, Complex.norm_conj, sq]
        _ = 1 := by rw [h2, norm_one]
    rw [← hρ']
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  have h4 : ‖ρ ⟨χ 𝔞, hx⟩‖ ^ (2 * h) = 1 := by
    rw [← norm_pow, ← map_pow, hw, map_prod, norm_prod]
    simp [map_inv₀, norm_inv, hone]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h4

end GlobalTheory.CharModOne
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds : ∀ (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ), (∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤ C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1))) → (∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤ C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) → ((d : ℤ) + 1) * b < a → ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  first | exact @GlobalTheory.morse_inequality_arith | exact GlobalTheory.morse_inequality_arith | (intros; apply GlobalTheory.morse_inequality_arith <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem log_div_pred_mem_of_prime {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log p / ((p : ℝ) - 1) ∧ Real.log p / ((p : ℝ) - 1) ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  refine ⟨div_nonneg (Real.log_nonneg (by linarith)) hpos.le, ?_⟩
  rw [div_le_one hpos]
  exact Real.log_le_sub_one_of_pos (by linarith)

end GlobalTheory.MeanTop
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.exists_injective_kernel_coind_intertwiningMap : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V'), ∃ K : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V'), Function.Injective K ∧ ∀ (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ')) (p' : P') (g : G) (p : P), K Φ ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K Φ g ∘ₗ σ p := by
  first | exact @GlobalTheory.CoindKernel.exists_kernel | exact GlobalTheory.CoindKernel.exists_kernel | (intros; apply GlobalTheory.CoindKernel.exists_kernel <;> assumption)
end
