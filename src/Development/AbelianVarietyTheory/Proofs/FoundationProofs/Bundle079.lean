module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.HahnSeries.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import GroundTheory.PAdicHodge.AxLemma
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Valuation.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle043
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle044
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hasSum_reindex_nat : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (h : HahnSeries ℚ Ω) (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω) (z v : ℂ), 0 < N → (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) → (∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0) → (HasSum (fun r : ℚ => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) v ↔ HasSum (fun k : ℕ => ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)))) := by
  intro Ω _ ε h N n₀ a z v hN ha h0
  set g : ℕ → ℚ := fun k => (((n₀ + k : ℤ) : ℚ) / N) with hg
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hinj : Function.Injective g := by
    intro k l hkl
    simp only [hg] at hkl
    have := (div_left_inj' hNq).mp hkl
    have h2 : ((n₀ + k : ℤ)) = n₀ + l := by exact_mod_cast this
    omega
  set f : ℚ → ℂ := fun r => ε (h.coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with hf
  have hzero : ∀ r, r ∉ Set.range g → f r = 0 := by
    intro r hr
    have : ∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N := by
      intro k hk; exact hr ⟨k, hk.symm⟩
    simp [hf, h0 r this]
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * n₀ * z / N) with hc
  have hc0 : c ≠ 0 := Complex.exp_ne_zero _
  have hcomp : f ∘ g = fun k : ℕ => (ε (a k) * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) * c := by
    funext k
    simp only [Function.comp, hf, hg, ha k, hc]
    rw [← Complex.exp_nat_mul, mul_assoc (ε (a k)), ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [← hinj.hasSum_iff hzero, hcomp]
  have hv : v = (v * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) * c := by
    rw [hc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  conv_lhs => rw [hv]
  exact hasSum_mul_right_iff hc0

end GlobalTheory
end

section

open TensorProduct GroundTheory.PAdicHodge UniformSpace

namespace GlobalTheory

theorem line_functional_eq_period_mul : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
  (g : S → Module.End ℤ_[l] M) (ρ : S → Matrix (Fin 2) (Fin 2) (PadicAlgCl l))
  (L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l]) (F : Finset (PadicAlgCl l)),
  (∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ a ∈ F, a ∈ K) → ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l,
    ∃ s, ∀ b ∈ B, L (1 ⊗ₜ[ℤ_[l]] g s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b)) →
  ∀ (m : ℕ) (σ : Fin m → (Fin 2 → PadicAlgCl l) →ₗ[PadicAlgCl l] TensorProduct ℤ_[l] (PadicAlgCl l) M),
  (∀ i v, σ i v ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype)) →
  (∀ i s v, LinearMap.baseChange (PadicAlgCl l) (g s) (σ i v) = σ i (Matrix.mulVec (ρ s) v)) →
  (∀ i, L (σ i ![1, 0]) = 0) →
  ∃ (κ : Fin m → PadicAlgCl l) (per : ℂ_[l]), ‖per‖ = 1 ∧ ∀ i v, L (σ i v) = per * ((κ i * v 1 : PadicAlgCl l) : ℂ_[l]) := by
  intro l _ M S _ _ B g ρ L F hgal m σ hσB hσeq hσ0
  classical

  have hsm : ∀ (a : PadicAlgCl l) (z : ℂ_[l]), a • z = (a : ℂ_[l]) * z := fun a z => by
    rw [Algebra.smul_def]; rfl
  set y : Fin m → ℂ_[l] := fun i => L (σ i ![0, 1]) with hy
  have hLv : ∀ i v, L (σ i v) = (v 1 : ℂ_[l]) * y i := by
    intro i v
    have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
      ext j; fin_cases j <;> simp
    calc L (σ i v) = L (σ i (v 0 • ![1, 0] + v 1 • ![0, 1])) := by rw [← hv]
      _ = _ := by rw [map_add (f := _), map_smul, map_smul, map_add (f := _), map_smul, map_smul, hσ0, smul_zero,
          zero_add, hsm]
  by_cases hall : ∀ i, y i = 0
  · refine ⟨0, 1, norm_one, fun i v => ?_⟩
    rw [hLv, hall i]; simp
  push_neg at hall
  obtain ⟨i₀, hy0⟩ := hall

  have hex : ∀ i, ∃ Sf : Finset (PadicAlgCl l × B),
      σ i ![0, 1] = ∑ q ∈ Sf, q.1 ⊗ₜ[ℤ_[l]] (q.2 : M) := by
    intro i
    obtain ⟨t, ht⟩ := hσB i ![0, 1]
    obtain ⟨Sf, rfl⟩ := TensorProduct.exists_finset t
    refine ⟨Sf, ?_⟩

    rw [← ht, map_sum]
    simp [LinearMap.baseChange_tmul]
  choose Sf hSf using hex
  set T : Finset (PadicAlgCl l) := F ∪ Finset.univ.biUnion (fun i => (Sf i).image Prod.fst) with hT
  set K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
    with hK
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTK : ∀ a ∈ T, a ∈ K := fun a ha => IntermediateField.subset_adjoin _ _ (by simpa using ha)
  have hFK : ∀ a ∈ F, a ∈ K := fun a ha => hTK a (Finset.mem_union_left _ ha)
  have hSK : ∀ i, ∀ q ∈ Sf i, q.1 ∈ K := fun i q hq =>
    hTK _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hq⟩))

  have hmul : ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, ∃ c : PadicAlgCl l,
      ∀ i, τ • y i = (c : ℂ_[l]) * y i := by
    intro τ
    obtain ⟨s, hs⟩ := hgal K hFK τ
    refine ⟨ρ s 1 1, fun i => ?_⟩
    have h1 : L (LinearMap.baseChange (PadicAlgCl l) (g s) (σ i ![0, 1])) = τ • y i := by
      rw [hy]
      simp only

      rw [hSf i, map_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [LinearMap.baseChange_tmul]
      have e1 : ∀ x : M, q.1 ⊗ₜ[ℤ_[l]] x = q.1 • ((1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] x) := fun x => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e1 (q.2 : M), map_smul, map_smul, hsm, hsm, hs _ q.2.2, smul_mul',
        gal_smul_coe, show τ q.1 = q.1 from τ.commutes ⟨q.1, hSK i q hq⟩]
    rw [← h1, hσeq, hLv]
    congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hfix : ∀ i, ∃ k : K, ((k : PadicAlgCl l) : ℂ_[l]) = y i / y i₀ := by
    intro i
    refine exists_eq_coe_of_forall_smul_eq fun τ => ?_
    obtain ⟨c, hc⟩ := hmul τ
    have hne : τ • y i₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_smul_gal, norm_ne_zero_iff]; exact hy0
    have hc0 : (c : ℂ_[l]) ≠ 0 := by
      intro h0; apply hne; rw [hc, h0, zero_mul]
    rw [smul_div₀', hc, hc]
    field_simp
  choose k hk using hfix

  obtain ⟨a, ha⟩ := (Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt (y i₀)
    (norm_pos_iff.2 hy0)
  rw [dist_eq_norm] at ha
  have hna : ‖(a : ℂ_[l])‖ = ‖y i₀‖ := by
    have e : (a : ℂ_[l]) = -(y i₀ - (a : ℂ_[l])) + y i₀ := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact ha.ne),
      norm_neg, max_eq_right ha.le]
  have ha0 : (a : ℂ_[l]) ≠ 0 := by
    rw [← norm_ne_zero_iff, hna, norm_ne_zero_iff]; exact hy0
  refine ⟨fun i => (k i : PadicAlgCl l) * a, y i₀ / (a : ℂ_[l]), ?_, fun i v => ?_⟩
  · rw [norm_div, hna, div_self (norm_ne_zero_iff.2 hy0)]
  · rw [hLv, Completion.coe_mul, Completion.coe_mul, hk i]
    field_simp

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_extend_of_embedding :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ g : ℂ ≃+* ℂ, ∀ x, g (ε x) = ε (s x) := by
  intro Ω _ ε s
  letI : Algebra Ω ℂ := ε.toAlgebra
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis Ω ℂ
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let e := hB.1.aevalEquiv.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv B s).trans hB.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun x => ?_⟩
  have h1 : ∀ y : Ω,
      algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.C y)) = ε y := fun y => by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  conv_lhs => rw [← h1 x]
  rw [IsAlgClosure.equivOfEquiv_algebraMap, ← h1 (s x)]
  congr 1
  simp [e]

end GlobalTheory.FN
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) → v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  first | exact @GlobalTheory.AlmostEt.frob_sum_sub_le' | exact GlobalTheory.AlmostEt.frob_sum_sub_le' | (intros; apply GlobalTheory.AlmostEt.frob_sum_sub_le' <;> assumption)
end

section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_le_one_iff_isIntegral_of_complete_dvr :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω]
      [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) →
      ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  intro R Ω _ _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr hinj
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R (FractionRing R))
  obtain ⟨f, hna, hnt, hball, hcomp⟩ := GlobalTheory.T.exists_absoluteValue_completeSpace_of_dvr R (FractionRing R)
  obtain ⟨v, -, hv⟩ := GlobalTheory.T.exists_spectral_valuation_algebraic_extension (FractionRing R) Ω f hna hnt hcomp
  refine ⟨v, fun x => ?_⟩
  rw [hv]
  simp only [hball]
  constructor
  · intro h
    have hl : minpoly (FractionRing R) x ∈ Polynomial.lifts (algebraMap R (FractionRing R)) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr h
    obtain ⟨q, hq, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    refine ⟨q, hmon, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (FractionRing R), hq]
    exact minpoly.aeval _ _
  · intro h i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩

end GlobalTheory
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.valuation_primitiveRoot_sub_one_pow_pred_eq : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ ζ : L, IsPrimitiveRoot ζ p → v (ζ - 1) ^ (p - 1) = v (p : L) := by
  first | exact @GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime | exact GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime | (intros; apply GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime <;> assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_of_coprime' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  first | exact @GlobalTheory.AlmostEt.natCast_eq_one_of_coprime | exact GlobalTheory.AlmostEt.natCast_eq_one_of_coprime | (intros; apply GlobalTheory.AlmostEt.natCast_eq_one_of_coprime <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m n i : ℕ} (hm : 1 ≤ m)
    (hi : ¬ p ^ (n - m) ∣ i) :
    m < n ∧ ∃ K d u : ℕ, ¬ p ∣ d ∧ ¬ p ∣ u ∧ i * (1 + p ^ m) ^ K = i + u * d * p ^ (n - 1) ∧
      ∃ w, (1 + p ^ m) ^ K = 1 + p * w := by
  have hp : p.Prime := Fact.out
  have hi0 : i ≠ 0 := by rintro rfl; exact hi (dvd_zero _)
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp.ne_one
  have hv : v < n - m := by
    by_contra h
    push_neg at h
    exact hi (Dvd.dvd.mul_right (pow_dvd_pow p h) _)
  refine ⟨by omega, ?_⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpm : 0 < p ^ m := pow_pos hp.pos m
  have hlt : 1 < 1 + p ^ m := by omega
  have hnd : ¬ p ∣ 1 + p ^ m := fun h =>
    hp.not_dvd_one ((Nat.dvd_add_left (dvd_pow_self p (by omega))).1 h)
  have hval := padicValNat.pow_sub_pow (p := p) hodd (x := 1 + p ^ m) (y := 1) hlt
    (by rw [Nat.add_sub_cancel_left]; exact dvd_pow_self p (by omega)) hnd
    (n := p ^ (n - v - 1 - m)) (pow_ne_zero _ hp.ne_zero)
  rw [one_pow, Nat.add_sub_cancel_left, padicValNat.prime_pow, padicValNat.prime_pow] at hval
  have hK1 : 1 < (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) :=
    Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hlt
  obtain ⟨e, d, hd, hed⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.sub_ne_zero_of_lt hK1) p
    hp.ne_one
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (dvd_zero _)
  rw [hed, Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero) hd0,
    Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hd, add_zero] at hval
  have hK : (1 + p ^ m) ^ (p ^ (n - v - 1 - m)) = 1 + p ^ e * d := by omega
  refine ⟨p ^ (n - v - 1 - m), d, u, hd, hu, ?_, p ^ (e - 1) * d, ?_⟩
  · rw [hK, mul_add, mul_one, show n - 1 = v + e by omega, pow_add]
    ring
  · rw [hK, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog

end GlobalTheory.K5.MonX

namespace GlobalTheory.K5.MonX

open GlobalTheory.K5 GlobalTheory.KumDlog

end GlobalTheory.K5.MonX
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_monic_irreducible_integral_primitive_element : ∀ {F : Type} [Field F] [CharZero F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧ Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧ ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  first | exact @GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | exact GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | (intros; apply GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq : ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀] [IsFractionRing A₀ K₀]
  [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E] [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
  ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ → (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
  ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
    ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E)) (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  first | exact @GlobalTheory.kummer_not_map_comap_le_sq | exact GlobalTheory.kummer_not_map_comap_le_sq | (intros; apply GlobalTheory.kummer_not_map_comap_le_sq <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.intMatrix_prime_det_coset_representatives : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q → (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨ ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  first | exact @GlobalTheory.cosetPrimeDet | exact GlobalTheory.cosetPrimeDet | (intros; apply GlobalTheory.cosetPrimeDet <;> assumption)
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem specialLinearGroup_map_intCast_zmod_surjective :
    ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) :
      SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) :=
  fun M => GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M

end GlobalTheory
end
