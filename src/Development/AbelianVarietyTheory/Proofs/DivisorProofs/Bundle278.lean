module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LatticeTheta.Statement
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Fourier.FourierTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle171
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem X_sq_add_one_ne_zero : (X ^ 2 + 1 : F[X]) ≠ 0 := Monic.ne_zero (by monicity!)

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!

def basisOneI : Module.Basis (Fin 2) F (Ext F) :=
  (AdjoinRoot.powerBasis (X_sq_add_one_ne_zero F)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_sq_add_one]))

theorem basisOneI_apply (j : Fin 2) : basisOneI F j = ii F ^ (j : ℕ) := by
  simp [basisOneI, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, ii]

theorem basisOneI_zero : basisOneI F 0 = 1 := by simp [basisOneI_apply]
theorem basisOneI_one : basisOneI F 1 = ii F := by simp [basisOneI_apply]

theorem gEmb_eq (a b : F) : gEmb F (a, b) = a • basisOneI F 0 + b • basisOneI F 1 := by
  simp [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def]

theorem gEmb_mul_ii (a b : F) : gEmb F (a, b) * ii F = (-b) • basisOneI F 0 + a • basisOneI F 1 := by
  simp only [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def, map_neg]
  linear_combination (algebraMap F (Ext F) b) * ii_sq F

theorem norm_gEmb_F (a b : F) : Algebra.norm F (gEmb F (a, b)) = a ^ 2 + b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (basisOneI F), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [basisOneI_zero, mul_one, basisOneI_one, gEmb_mul_ii, gEmb_eq]
  simp [Module.Basis.repr_self, Finsupp.single_apply]
  ring

theorem norm_gEmb (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  rw [← Algebra.norm_norm (S := F), norm_gEmb_F]
  have h := prod_emb (F := F) (a ^ 2 + b ^ 2)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← h, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp

end GlobalTheory.GaussExt
end
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  first | exact @GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | exact GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | (intros; apply GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual <;> assumption)
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.isZLattice_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)], IsZLattice ℝ (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.isZLattice_latOf | exact GlobalTheory.LipschitzTR.isZLattice_latOf | (intros; apply GlobalTheory.LipschitzTR.isZLattice_latOf <;> assumption)
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  first | exact @GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | exact GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | (intros; apply GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi <;> assumption)
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.fourier_lipschitzOneVariableKernel_eq : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ), 𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  first | exact @GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | exact GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow | (intros; apply GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow <;> assumption)
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

theorem _root_.GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.discrete_latOf | exact GlobalTheory.LipschitzTR.discrete_latOf | (intros; apply GlobalTheory.LipschitzTR.discrete_latOf <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (h : A), IsExcisionNbhd A A' h → ∀ a b : A', a * b - 1 ∈ Ideal.span {algebraMap A A' h} → IsExcisionNbhd A (Localization.Away a) h := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away) | (exact GlobalTheory.EtC.isExcisionNbhd_away) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away  <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_section_lifting_residue_values : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  first | exact @GlobalTheory.DenseSec.hensel_etChart | exact GlobalTheory.DenseSec.hensel_etChart | (intros; apply GlobalTheory.DenseSec.hensel_etChart <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisComparisonMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  first | (exact @GlobalTheory.GoodEtale.galMap_injective_of_flat) | (exact GlobalTheory.GoodEtale.galMap_injective_of_flat) | (intros; apply GlobalTheory.GoodEtale.galMap_injective_of_flat  <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.etale_localizationAtPrime_tensor_of_low_height : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  first | (exact @GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (exact GlobalTheory.GoodEtale.etale_localization_of_etaleLow) | (intros; apply GlobalTheory.GoodEtale.etale_localization_of_etaleLow  <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.finite_of_galois_trace_relation : ∀ (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  first | (exact @GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (exact GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (intros; apply GlobalTheory.GoodEtaleFinite.finite_of_trace_relation  <;> assumption)
end

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem algHom_quot_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  intro A R C _ _ _ _ _ _ ρ hρ t hker ht hE n f f' hff
  set P₀ : Ideal R := RingHom.ker ρ with hP₀
  haveI hP : P₀.IsPrime := RingHom.ker_isPrime ρ
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => by
    have := congrArg (fun g => g a) hρ
    simpa using this
  have hcomap : P₀.comap (algebraMap A R) = ⊥ := by
    ext a
    simp only [Ideal.mem_comap, hP₀, RingHom.mem_ker, Ideal.mem_bot, hρa]
  have hht : (P₀.comap (algebraMap A R)).height ≤ 1 := by
    rw [hcomap, Ideal.height_bot]; exact zero_le_one
  set Rp := Localization.AtPrime P₀
  haveI : Algebra.Etale Rp (Rp ⊗[R] C) := hE P₀ hht
  haveI : Algebra.FormallyUnramified R Rp := Algebra.FormallyUnramified.of_isLocalization P₀.primeCompl
  haveI : Algebra.FormallyUnramified R (Rp ⊗[R] C) := Algebra.FormallyUnramified.comp R Rp (Rp ⊗[R] C)
  set Q := R ⧸ Ideal.span {t} ^ n
  set B := Localization (Algebra.algebraMapSubmonoid Q P₀.primeCompl)
  letI : Algebra Rp B := localizationAlgebra P₀.primeCompl Q

  have hle : Algebra.algebraMapSubmonoid Q P₀.primeCompl ≤ nonZeroDivisors Q := by
    rintro _ ⟨s, hs, rfl⟩
    suffices H : ∀ x : Q, x * algebraMap R Q s = 0 → x = 0 from
      mem_nonZeroDivisors_iff.2 ⟨fun x hx => H x (by rw [mul_comm]; exact hx), H⟩
    intro x hx
    set a := ρ s
    have ha : a ≠ 0 := fun h => hs (RingHom.mem_ker.2 h)
    have hd : s - algebraMap A R a ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker, map_sub, hρa, sub_self]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hd
    set u : Q := Ideal.Quotient.mk _ s
    set e : Q := Ideal.Quotient.mk _ (s - algebraMap A R a)
    have he : e ^ n = 0 := by
      simp only [e, ← map_pow, ← hr, mul_pow]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n)
    have hdv : u ∣ (u - e) ^ n := by
      have h1 := sub_dvd_pow_sub_pow (u - e) (-e) n
      rw [neg_pow, he, mul_zero, sub_zero, sub_neg_eq_add, sub_add_cancel] at h1
      exact h1
    obtain ⟨k, hk⟩ := hdv
    have hue : u - e = Ideal.Quotient.mk _ (algebraMap A R a) := by
      simp only [u, e, map_sub, sub_sub_cancel]
    have hzero : algebraMap A R (a ^ n) • x = 0 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow, map_pow, ← hue, hk]
      calc u * k * x = k * (x * u) := by ring
        _ = 0 := by rw [show x * u = 0 from hx, mul_zero]
    exact torsionFree_quot A R ρ hρ t hker ht n (a ^ n) (pow_ne_zero n ha) x hzero
  have hinj : Function.Injective (algebraMap Q B) := IsLocalization.injective B hle
  let φ : Rp →ₐ[R] B := (Algebra.ofId Rp B).restrictScalars R
  let ι : Q →ₐ[R] B := IsScalarTower.toAlgHom R Q B
  let g₁ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f)
  let g₂ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f')
  set J : Ideal B := Ideal.span {algebraMap R B t}
  have hJ : IsNilpotent J := by
    refine ⟨n, ?_⟩
    rw [Ideal.span_singleton_pow (algebraMap R B t) n, ← map_pow, IsScalarTower.algebraMap_apply R Q B,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n), map_zero, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot]
  have e : (Ideal.Quotient.mkₐ R J).comp g₁ = (Ideal.Quotient.mkₐ R J).comp g₂ := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro x; simp [g₁, g₂]
    · ext c
      simp only [g₁, g₂, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, one_mul, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq, ← map_sub]
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (hff c)
      rw [← hq, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [show ι (Ideal.Quotient.mk _ t) = algebraMap R B t from
        (IsScalarTower.algebraMap_apply R Q B t).symm]
      exact Ideal.mem_span_singleton_self _
  have hg : g₁ = g₂ := Algebra.FormallyUnramified.ext J hJ fun x => by
    simpa using congrArg (fun g => g x) e
  ext c
  apply hinj
  have := congrArg (fun g => g ((1 : Rp) ⊗ₜ[R] c)) hg
  simpa [g₁, g₂, ι] using this

end GlobalTheory.GoodEtaleSection
end
