module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle159
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle200
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle181
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle202
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AutomorphicArithmetic.WeightCongruences.ProdCMTypeEmbeddingsRootOfUnityEqOne
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries : ∀ (h b : ℕ → ℂ) (w : ℝ), 0 < w → PolyB h → PolyB b → h 0 = 0 → LSeriesSummable (fun n => conj (h n) * b n) w → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) strip → ∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ) = ((Real.Gamma w / (4 * π) ^ w : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) w := by
  first | exact @GlobalTheory.EisM.strip_eq_LSeries | exact GlobalTheory.EisM.strip_eq_LSeries | (intros; apply GlobalTheory.EisM.strip_eq_LSeries <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sturm_sum_coef_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ,
    (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  classical
  intro k L N hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  choose f hf using fun ε => modularForm_gammaOne_of_MF k L N ε (a ε) hL hN (ha ε)
  have hc : ∀ ε n, (qExpansion 1 (f ε)).coeff n = a ε n := by
    intro ε n
    have := coef_qs (a ε) (ha ε).1 n
    unfold coef at this
    rw [← this, hf]
  have hsum : ∀ (s : Finset (DirichletCharacter ℂ N)) (n : ℕ),
      (qExpansion 1 ⇑(∑ ε ∈ s, f ε)).coeff n = ∑ ε ∈ s, a ε n := by
    intro s n
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.coe_zero, qExpansion_zero, map_zero]
    | insert e s he ih =>
      rw [Finset.sum_insert he, ModularForm.coe_add, ModularForm.qExpansion_add one_pos hΓ, map_add (f := _), ih, hc, Finset.sum_insert he]
  have h0 : ∑ ε, f ε = 0 := hm _ fun n hn => by
    rw [hsum]
    simpa [Finset.sum_apply] using hz n hn
  funext n
  have := hsum Finset.univ n
  rw [h0] at this
  rw [ModularForm.coe_zero, qExpansion_zero, map_zero] at this
  rw [Finset.sum_apply, ← this]
  rfl

end GlobalTheory.EisM
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  first | exact @GlobalTheory.FockBilin.exists_bilin | exact GlobalTheory.FockBilin.exists_bilin | (intros; apply GlobalTheory.FockBilin.exists_bilin <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomBridge

theorem exists_int_of_isIntegral {r : ℚ} (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℚ) = r := by
  have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := h
  exact IsIntegrallyClosed.isIntegral_iff.1 ((isIntegral_algebraMap_iff ).1 h')

theorem isIntLattice_of {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) {Λ : PeriodPair} (h1 : Λ.ω₁ = 1)
    (h2 : Λ.ω₂ = (1 + Complex.I * (Real.sqrt d : ℝ)) / 2) : IsIntLattice d Λ := by
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hw
  have hw2 : w ^ 2 = -(d : ℂ) := by
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    simp
  have hwc : starRingEnd ℂ w = -w := by simp [hw]
  have hZ : ∀ n : ℤ, IsIntegral ℤ (n : ℂ) := fun n => isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := n)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d + 1 = 4 * c := ⟨(d + 1) / 4, by omega⟩
  have hcC : (d : ℂ) + 1 = 4 * c := by exact_mod_cast hc
  intro x
  rw [PeriodPair.mem_lattice, h1, h2]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨((hZ m).mul isIntegral_one).add ((hZ n).mul ?_), m + n / 2, n / 2, by push_cast; ring⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (c : ℤ), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    linear_combination (1 / 4 : ℂ) * hw2 - (1 / 4 : ℂ) * hcC
  · rintro ⟨hx, a, b, rfl⟩
    have hx' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * w) := by
      have := hx.map_of_comp_eq (RingHom.id ℤ) (starRingEnd ℂ) (RingHom.ext_int _ _)
      simpa [hwc, sub_eq_add_neg] using this
    obtain ⟨t, ht⟩ := exists_int_of_isIntegral (r := 2 * a) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.add hx')
      push_cast; ring)
    obtain ⟨n, hn⟩ := exists_int_of_isIntegral (r := a ^ 2 + d * b ^ 2) (by
      refine (congrArg (IsIntegral ℤ) ?_).mpr (hx.mul hx')
      push_cast
      linear_combination (b : ℂ) ^ 2 * hw2)
    have hm2 : ((d : ℚ) * (2 * b)) ^ 2 = ((d * (4 * n - t ^ 2) : ℤ) : ℚ) := by
      push_cast
      rw [hn, ht]; ring
    obtain ⟨m, hm⟩ := exists_int_of_isIntegral (r := d * (2 * b)) (IsIntegral.of_pow two_pos (by
      rw [← Rat.cast_pow, hm2, Rat.cast_intCast]
      exact hZ _))
    have hm3 : m ^ 2 = d * (4 * n - t ^ 2) := by
      rw [← hm] at hm2
      exact_mod_cast hm2
    obtain ⟨u, rfl⟩ : (d : ℤ) ∣ m := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow ⟨_, hm3⟩
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
    have hu : (u : ℚ) = 2 * b := by
      push_cast at hm
      exact mul_left_cancel₀ hd0 hm
    have hn4 : 4 * n = t ^ 2 + d * u ^ 2 := by
      have : (4 : ℚ) * n = t ^ 2 + d * u ^ 2 := by rw [hn, ht, hu]; ring
      exact_mod_cast this
    have hcZ : (d : ℤ) = 4 * c - 1 := by omega
    have hpar : Even (t - u) := by
      have h5 : Even ((t - u) * (t - u)) :=
        ⟨2 * n - 2 * c * u ^ 2 + u ^ 2 - t * u, by rw [hcZ] at hn4; linear_combination -hn4⟩
      exact (Int.even_mul.1 h5).elim id id
    obtain ⟨k, hk⟩ := hpar
    refine ⟨k, u, ?_⟩
    have e1 : (t : ℂ) = 2 * a := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) ht
    have e2 : (u : ℂ) = 2 * b := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hu
    have e3 : (t : ℂ) - u = k + k := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hk
    linear_combination (-1 / 2 : ℂ) * e3 + (1 / 2 : ℂ) * e1 + (w / 2) * e2

variable {R : Ranks} (H : Host R)

theorem host_isAbelianGalois : IsAbelianGalois ℚ H.E := by
  have := H.hostE_isGalois
  have : IsMulCommutative Gal(H.E/ℚ) :=
    ⟨⟨fun σ τ => (H.gal).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  exact {}

theorem host_unramFin : UnramFin H.E := by
  have : IsCMField H.E := H.isCMField_hostE
  have h : discr H.E = discr (maximalRealSubfield H.E) ^ 2 := H.der.discr_sq
  have h2 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (maximalRealSubfield H.E) (OF H.E) H.E (𝓞 H.E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two, h, Int.natAbs_pow] at h2
  have h0 : (discr (maximalRealSubfield H.E)).natAbs ^ 2 ≠ 0 := pow_ne_zero _ (Int.natAbs_ne_zero.2 (discr_ne_zero _))
  exact Ideal.absNorm_eq_one_iff.1 (mul_right_cancel₀ h0 (h2.symm.trans (one_mul _).symm))

theorem two_dvd_discr_host : (2 : ℤ) ∣ discr H.E := H.der.discr_primes.2.1

theorem finrank_le_of_isCMType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (h : IsCMType φ) : Module.finrank ℚ E ≤ 2 * Fintype.card I := by
  have := Fintype.card_le_of_surjective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) fun σ => by
    obtain ⟨i, hi | hi, -⟩ := h σ
    · exact ⟨Sum.inl i, hi.symm⟩
    · exact ⟨Sum.inr i, hi.symm⟩
  rwa [Embeddings.card, Fintype.card_sum, ← two_mul] at this

theorem isFieldData_host {I : Type} [Fintype I] {φ : I → H.E →+* ℂ} (h : IsCMType φ)
    (h' : ∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) : IsFieldData H.d φ := by
  have hcard : 2 ≤ Fintype.card I := by
    have h1 := finrank_le_of_isCMType h
    have h2 : Module.finrank ℚ H.E = 4 * R.ord := H.finrank_cmField
    have h3 : 0 < R.ord := R.ord_pos
    rw [h2] at h1
    omega
  refine ⟨H.hyp.2.1, by have := H.hyp.2.2.2.1; omega, host_unramFin H, fun x hx => ?_, two_dvd_discr_host H, hcard, h, ?_⟩
  · exact UpperTheory.prod_CMType_embeddings_root_of_unity_eq_one R H I φ h h' x (isOfFinOrder_iff_pow_eq_one.1 hx)
  · obtain ⟨i⟩ : Nonempty I := Fintype.card_pos_iff.1 (by omega)
    have hb : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqrtMinusD_sq
    have hsq : φ i H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℝ)) ^ 2 := by
      rw [← map_pow, hb, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e
    · exact ⟨_, hb, fun j => (h' j i).trans e⟩
    · exact ⟨-H.sqrtMinusD, by rw [neg_sq, hb], fun j => by rw [map_neg, h' j i, e, neg_neg]⟩

theorem classTermBoundBeta_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBoundBeta := by
  intro R H I _ φ s κ 𝔣 χ hD Λ h1 h2 l hl
  have : IsCMField H.E := H.isCMField_hostE
  have := host_isAbelianGalois H
  obtain ⟨z, -, hz⟩ := h H.E I H.d φ s (isFieldData_host H hD.1 hD.2.1) hD.2.2.1
  have hΛ := isIntLattice_of H.hyp.2.1 (by have := H.hyp.2.2.2.1; omega) h1 h2
  refine ⟨⌈betaBound_vp H.d s κ 𝔣 z l⌉₊, fun Q hQ hQl y T hT => ?_⟩
  have := (hz κ 𝔣 Λ χ hD.2.2.2.2.1 hΛ hD.2.2.2.2.2 l hl Q hQ hQl).1 y T hT (⌈betaBound_vp H.d s κ 𝔣 z l⌉₊ : ℕ) 1 one_pos
    (by simpa using Nat.le_ceil _)
  simpa using this

theorem classTermBound_of_toricDenominator (h : ToricDenominator) : GlobalTheory.ToricDenom.ClassTermBound :=
  GlobalTheory.ToricDenom.classTermBound_of_beta (classTermBoundBeta_of_toricDenominator h)

end GlobalTheory.ToricDenomBridge
end
end

section

noncomputable section

open UpperTheory.V.HV

namespace GlobalTheory.Ord2.CoefDual

variable (l : ℕ) [Fact l.Prime] (c : Coef l)

def dualModule : Module c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) where
  smul a f := f ∘ₗ LinearMap.mulLeft ℤ_[l] a
  one_smul f := by apply LinearMap.ext; intro x; show f (1 * x) = f x; rw [one_mul]
  mul_smul a b f := by apply LinearMap.ext; intro x; show f (a * b * x) = f (b * (a * x)); rw [mul_comm a b, mul_assoc]
  smul_zero a := by apply LinearMap.ext; intro x; show (0 : c.O →ₗ[ℤ_[l]] ℤ_[l]) (a * x) = 0; rfl
  smul_add a f g := by apply LinearMap.ext; intro x; show (f + g) (a * x) = f (a * x) + g (a * x); rfl
  add_smul a b f := by apply LinearMap.ext; intro x; show f ((a + b) * x) = f (a * x) + f (b * x); rw [add_mul, map_add (f := _)]
  zero_smul f := by apply LinearMap.ext; intro x; show f (0 * x) = 0; rw [zero_mul, map_zero]

theorem dualModule_apply (a : c.O) (f : c.O →ₗ[ℤ_[l]] ℤ_[l]) (x : c.O) :
    (letI := dualModule l c; a • f) x = f (a * x) := rfl

theorem dual_tower :
    letI := dualModule l c; IsScalarTower ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine ⟨fun r a f => ?_⟩
  ext x
  rw [dualModule_apply, LinearMap.smul_apply, dualModule_apply, smul_mul_assoc, map_smul]

theorem dual_torsionFree :
    letI := dualModule l c; Module.IsTorsionFree c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := by
  letI := dualModule l c
  refine Module.IsTorsionFree.of_smul_eq_zero fun a f h => ?_
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ_[l]) (I := Ideal.span {a}) ha
    (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hr
  obtain ⟨b, hb⟩ := hr
  ext x
  have h1 : r • f x = 0 := by
    rw [← map_smul, Algebra.smul_def, hb, mul_assoc, ← dualModule_apply, h]
    rfl
  simpa [hr0] using h1

end GlobalTheory.Ord2.CoefDual


open GlobalTheory.Ord2.CoefDual in
theorem GlobalTheory.Ord2.coef_dual_free_rank_one :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ τ : c.O →ₗ[ℤ_[l]] ℤ_[l],
      ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = τ (a * x) := by
  intro l _ c
  letI := dualModule l c
  haveI := dual_tower l c
  haveI : Module.IsTorsionFree ℤ_[l] c.O := FaithfulSMul.to_isTorsionFree ℤ_[l] c.O
  haveI : Module.Free ℤ_[l] c.O := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := dual_torsionFree l c
  haveI : Module.Free c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) := Module.free_of_finite_type_torsion_free'
  have h1 := Module.finrank_linearMap ℤ_[l] ℤ_[l] c.O ℤ_[l]
  have h2 := Module.finrank_mul_finrank ℤ_[l] c.O (c.O →ₗ[ℤ_[l]] ℤ_[l])
  have hpos : 0 < Module.finrank ℤ_[l] c.O := Module.finrank_pos
  have hr : Module.finrank c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) = 1 := by
    rw [h1, Module.finrank_self, mul_one] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans (mul_one _).symm)
  let b := Module.finBasisOfFinrankEq c.O (c.O →ₗ[ℤ_[l]] ℤ_[l]) hr
  refine ⟨b 0, fun f => ⟨b.repr f 0, fun x => ?_, fun a ha => ?_⟩⟩
  · have hs := b.sum_repr f
    rw [Fin.sum_univ_one] at hs
    rw [← dualModule_apply, hs]
  · have hf : f = a • b 0 := LinearMap.ext fun x => (ha x).trans (dualModule_apply l c a (b 0) x).symm
    rw [hf, map_smul, b.repr_self]
    simp

end
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def nonnegRing_vw (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {a | 0 ≤ vw w a}
  zero_mem' := (ValuationRepresentative.vw_zero w).ge
  one_mem' := (ValuationRepresentative.vw_one w).ge
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    by_cases h0 : a = 0
    · rw [h0, zero_mul]; exact (ValuationRepresentative.vw_zero w).ge
    by_cases h1 : b = 0
    · rw [h1, mul_zero]; exact (ValuationRepresentative.vw_zero w).ge
    rw [ValuationRepresentative.vw_mul w a b h0 h1]
    exact add_nonneg ha hb
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    by_cases h0 : a = 0
    · rwa [h0, zero_add]
    by_cases h1 : b = 0
    · rwa [h1, add_zero]
    by_cases h2 : a + b = 0
    · rw [h2]; exact (ValuationRepresentative.vw_zero w).ge
    exact (le_min ha hb).trans (Formalism.PairingDivisionLocalBalance.vw_add w a b h0 h1 h2)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    by_cases h0 : a = 0
    · rw [h0, neg_zero]; exact (ValuationRepresentative.vw_zero w).ge
    have h1 : 0 ≤ vw w (-1 : K) := by
      have := ValuationRepresentative.vw_int_nonneg w (-1 : 𝓞 K)
      simpa using this
    rw [← neg_one_mul, ValuationRepresentative.vw_mul w _ a (neg_ne_zero.2 one_ne_zero) h0]
    exact add_nonneg h1 ha

end

section

variable {K : Type} [Field K] (R : Subring K)

theorem mem_range_map_subtype_iff {σ : Type} (P : MvPolynomial σ K) :
    P ∈ (MvPolynomial.map (σ := σ) R.subtype).range ↔ ∀ m, AddMonoidAlgebra.coeff P m ∈ R := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]
    exact (AddMonoidAlgebra.coeff Q m).2
  · intro h
    rw [P.as_sum]
    exact sum_mem fun m _ => ⟨monomial m ⟨_, h m⟩, by rw [map_monomial]; rfl⟩

theorem blockAct_mem_range_map_subtype {ι : Type} [Fintype ι] {n : ℕ}
    (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ R)
    {P : MvPolynomial (ι × Fin n × Fin n) K}
    (hP : P ∈ (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range := by
  have hC : ∀ {a : K}, a ∈ R → (C a : MvPolynomial (ι × Fin n × Fin n) K) ∈
      (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range :=
    fun {a} ha => ⟨C ⟨a, ha⟩, by simp⟩
  have hX : ∀ v, (X v : MvPolynomial (ι × Fin n × Fin n) K) ∈
      (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range :=
    fun v => ⟨X v, by simp⟩
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact hC a.2
  | add p q hp hq =>
    rw [map_add (MvPolynomial.map R.subtype), map_add (f := _)]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (MvPolynomial.map R.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem (hC (hU _ _ _)) (hX _))

end

theorem vw_fockS_blockAct_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (w : HeightOneSpectrum (𝓞 K)) (F F' : Pol K ι n) (U : ι → Matrix (Fin n) (Fin n) K), (∀ mo, 0 ≤ vw (conjPl w) (AddMonoidAlgebra.coeff F mo)) → (∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F' mo)) → (∀ τ a b, 0 ≤ vw w (U τ a b)) → 0 ≤ vw w (fockS F (Formalism.GradedWeylDivisibility.blockAct K U F')) := by
  intro K _ _ _ ι _ n w F F' U hF hF' hU
  have h := (mem_range_map_subtype_iff (nonnegRing_vw w) _).1
    (blockAct_mem_range_map_subtype (nonnegRing_vw w) U hU
      ((mem_range_map_subtype_iff (nonnegRing_vw w) F').2 hF'))
  change fockS F (Formalism.GradedWeylDivisibility.blockAct K U F') ∈ nonnegRing_vw w
  unfold fockS
  refine sum_mem fun m _ => mul_mem (mul_mem ?_ (h m)) (natCast_mem _ _)
  change 0 ≤ vw w (star (AddMonoidAlgebra.coeff F m))
  rw [ValuationRepresentative.vw_star]
  exact hF m

end GlobalTheory.TestLat
end
