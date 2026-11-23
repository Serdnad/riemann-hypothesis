module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import GroundTheory.GlobalFields.Bundle001
public import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.isIntegral_of_adicIntegralTensorBasis_ring : ∀ (v : HeightOneSpectrum ℤ) (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type)
    (b : Module.Basis κ ℚ C), IsIntB v b 1 → (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) →
      ∀ y, IsIntB v b y → IsIntegral (v.adicCompletionIntegers ℚ) y := by
  first | (exact @GlobalTheory.AdicSpan.isIntegral_of_isIntB) | (exact GlobalTheory.AdicSpan.isIntegral_of_isIntB) | (intros; apply GlobalTheory.AdicSpan.isIntegral_of_isIntB  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_one_tmul_adic_integral_coords : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] (κ : Type) (b : Module.Basis κ ℚ M) (x : M),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] x) := by
  first | (exact @GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul) | (exact GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul) | (intros; apply GlobalTheory.AdicSpan.exists_finset_isIntB_one_tmul  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ResidueNorm

variable (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
  (b : Module.Basis κ ℚ M)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) : IsIntB v b (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem isSmallB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsSmallB v b x) (hy : IsSmallB v b y) :
    IsSmallB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact Valuation.map_add_lt _ (hx i) (hy i)

theorem isSmallB_zero : IsSmallB v b (0 : v.adicCompletion ℚ ⊗[ℚ] M) := fun i => by simp

theorem isSmallB_sub_of_residue_eq {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y)
    (h : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨_, hx i⟩ =
      IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨_, hy i⟩) : IsSmallB v b (x - y) := fun i => by
  have h0 : IsLocalRing.residue (v.adicCompletionIntegers ℚ) (⟨_, hx i⟩ - ⟨_, hy i⟩) = 0 := by
    rw [map_sub, h i, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
  have h1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp h0
  rw [map_sub, Finsupp.sub_apply]
  exact h1

theorem eq_neg_inv_of_mul_neg {R : Type*} [CommRing R] (u : Rˣ) (x : R) (h : x * -↑u = 1) : x = -↑u⁻¹ := by
  have k2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (-(↑u⁻¹ : R)) * h + (-x) * k2

theorem eq_inv_of_mul {R : Type*} [CommRing R] (u : Rˣ) (x : R) (h : x * ↑u = 1) : x = ↑u⁻¹ := by
  have k2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (↑u⁻¹ : R) * h - x * k2

theorem sq_mul_inv_sq {R : Type*} [CommRing R] (u : Rˣ) : (↑u * ↑u : R) * (↑u⁻¹ * ↑u⁻¹) = 1 := by
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

theorem norm_expand {R : Type*} [CommRing R] (a b t e : R) :
    (a + b * t) * (a - b * t) - e = a ^ 2 - t * t * b ^ 2 - e := by ring

end GlobalTheory.ResidueNorm


open GlobalTheory.ResidueNorm in
theorem GlobalTheory.ResidueNorm.exists_norm_mod_small : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) →
    ∀ θ : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑θ → IsIntB v bL ↑θ⁻¹ →
    Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑θ = -↑θ →
    ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e →
    IsIntB v bL ↑e → IsIntB v bL ↑e⁻¹ →
    ∃ z : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL z ∧
      IsSmallB v bL (z * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c z - ↑e) := by
  intro v L _ _ c _ κ bL h2 h1 hmul hsm _ θ hθ hθi hσθ e hσe he hei
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef

  obtain ⟨P, hP⟩ : ∃ P : Subring (v.adicCompletion ℚ ⊗[ℚ] L), ∀ x, x ∈ P ↔ IsIntB v bL x ∧ σ x = x := ⟨
    { carrier := {x | IsIntB v bL x ∧ σ x = x}
      mul_mem' := fun {a b} ha hb => ⟨hmul a b ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨h1, map_one σ⟩
      add_mem' := fun {a b} ha hb => ⟨isIntB_add v bL ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2]⟩
      zero_mem' := ⟨isIntB_zero v bL, map_zero σ⟩
      neg_mem' := fun {a} ha => ⟨isIntB_neg v bL ha.1, by rw [map_neg, ha.2]⟩ }, fun x => Iff.rfl⟩
  have hPi : ∀ x : P, IsIntB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) := fun x => ((hP _).1 x.2).1
  have hPs : ∀ x : P, σ (x : v.adicCompletion ℚ ⊗[ℚ] L) = x := fun x => ((hP _).1 x.2).2
  obtain ⟨I, hmemI⟩ : ∃ I : Ideal P, ∀ x : P, x ∈ I ↔ IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) := ⟨
    { carrier := {x | IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L)}
      add_mem' := fun {a b} ha hb => isSmallB_add v bL ha hb
      zero_mem' := isSmallB_zero v bL
      smul_mem' := fun a b hb => hsm _ _ (hPi a) hb }, fun x => Iff.rfl⟩

  haveI : Finite κ := Module.Finite.finite_basis bL
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv
  let φ : P → κ → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) := fun x i =>
    IsLocalRing.residue _ ⟨_, hPi x i⟩
  let out := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  haveI : Finite (P ⧸ I) := by
    refine Finite.of_injective (fun q => φ (out q)) fun q1 q2 h => ?_
    rw [← Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) q1,
      ← Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) q2, Ideal.Quotient.eq, hmemI]
    exact isSmallB_sub_of_residue_eq v bL (hPi (out q1)) (hPi (out q2)) fun i => congrFun h i

  have hσθi : σ ↑θ⁻¹ = -↑θ⁻¹ :=
    eq_neg_inv_of_mul_neg θ _ (by rw [← hσθ, ← map_mul, Units.inv_mul, map_one])
  have hσei : σ ↑e⁻¹ = ↑e⁻¹ :=
    eq_inv_of_mul e _ (by rw [← hσe, ← map_mul, Units.inv_mul, map_one])

  have memP : ∀ x, IsIntB v bL x → σ x = x → x ∈ P := fun x h h' => (hP x).2 ⟨h, h'⟩
  have hθθ : σ (↑θ * ↑θ) = ↑θ * ↑θ := by rw [map_mul, hσθ, neg_mul_neg]
  have hθθi : σ (↑θ⁻¹ * ↑θ⁻¹) = ↑θ⁻¹ * ↑θ⁻¹ := by rw [map_mul, hσθi, neg_mul_neg]
  have dmem : (↑θ * ↑θ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ (hmul _ _ hθ hθ) hθθ
  let dP : P := ⟨_, dmem⟩
  have dimem : (↑θ⁻¹ * ↑θ⁻¹ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ (hmul _ _ hθi hθi) hθθi
  let diP : P := ⟨_, dimem⟩
  have emem : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ he hσe
  let eP : P := ⟨_, emem⟩
  have eimem : (↑e⁻¹ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ hei hσei
  let eiP : P := ⟨_, eimem⟩
  have hhalf : (2⁻¹ : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
  have hmem2 : ((2⁻¹ : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L)) ∈ P := memP _ (fun i => by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hhalf (h1 i)) (by
      rw [Algebra.smul_def, mul_one, Algebra.TensorProduct.algebraMap_apply, hσdef,
        Algebra.TensorProduct.map_tmul, map_one]; rfl)
  let hh : P := ⟨_, hmem2⟩
  have h2P : (2 : P) * hh = 1 := by
    apply Subtype.ext
    show (2 : v.adicCompletion ℚ ⊗[ℚ] L) * ((2⁻¹ : v.adicCompletion ℚ) • 1) = 1
    have h20 : (2 : v.adicCompletion ℚ) ≠ 0 := by
      intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
    rw [mul_smul_comm, mul_one, ← map_ofNat (algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)) 2,
      Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h20, one_smul]
  have hdP : dP * diP = 1 := by
    apply Subtype.ext
    show (↑θ * ↑θ : v.adicCompletion ℚ ⊗[ℚ] L) * (↑θ⁻¹ * ↑θ⁻¹) = 1
    exact sq_mul_inv_sq θ
  have heP : eP * eiP = 1 := Subtype.ext (Units.mul_inv e)
  obtain ⟨a', b', hab⟩ := GlobalTheory.FinRingNorm.exists_sq_sub_mul_sq_eq (P ⧸ I)
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I hh) (by rw [← map_ofNat (Ideal.Quotient.mk I) 2, ← map_mul, h2P, map_one]))
    (Ideal.Quotient.mk I dP) (Ideal.Quotient.mk I eP)
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I diP) (by rw [← map_mul, hdP, map_one]))
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I eiP) (by rw [← map_mul, heP, map_one]))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  set_option synthInstance.maxHeartbeats 200000 in
  have hmem : a ^ 2 - dP * b ^ 2 - eP ∈ I := by
    refine Ideal.Quotient.eq.1 ?_
    simpa only [map_sub (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I),
      map_pow (Ideal.Quotient.mk I)] using hab
  rw [hmemI] at hmem
  refine ⟨(a : v.adicCompletion ℚ ⊗[ℚ] L) + (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L), isIntB_add v bL (hPi a) (hmul _ _ (hPi b) hθ), ?_⟩
  have hσz : σ ((a : v.adicCompletion ℚ ⊗[ℚ] L) + (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L)) = (a : v.adicCompletion ℚ ⊗[ℚ] L) - (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L) := by
    rw [map_add (f := _), map_mul, hPs a, hPs b, hσθ, mul_neg, ← sub_eq_add_neg]
  rw [hσz, norm_expand]
  exact hmem
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.HenselSqrt

open IsDedekindDomain.HeightOneSpectrum WithZero

variable (v : HeightOneSpectrum ℤ) {L : Type} [Field L] [NumberField L] {κ : Type}
  (bL : Module.Basis κ ℚ L)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) (hy : IsIntB v bL y) :
    IsIntB v bL (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) : IsIntB v bL (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem isIntB_smul {a : v.adicCompletion ℚ} (ha : a ∈ v.adicCompletionIntegers ℚ)
    {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) : IsIntB v bL (a • x) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem ha (hx i)

theorem isSmallB_neg {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsSmallB v bL x) : IsSmallB v bL (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]; exact hx i

variable (h1 : IsIntB v bL 1) (hmul : ∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y))

def lam : Subring (v.adicCompletion ℚ ⊗[ℚ] L) where
  carrier := {x | IsIntB v bL x}
  mul_mem' := fun {x y} hx hy => hmul x y hx hy
  one_mem' := h1
  add_mem' := fun hx hy => isIntB_add v bL hx hy
  zero_mem' := isIntB_zero v bL
  neg_mem' := fun hx => isIntB_neg v bL hx

def unif (π : v.adicCompletionIntegers ℚ) : lam v bL h1 hmul :=
  ⟨(π : v.adicCompletion ℚ) • 1, isIntB_smul v bL π.2 h1⟩

variable (π : v.adicCompletionIntegers ℚ) (hπ : Valued.v (π : v.adicCompletion ℚ) = exp (-1 : ℤ))
include hπ

theorem mem_pow_iff (x : lam v bL h1 hmul) (n : ℕ) :
    x ∈ (Ideal.span {unif v bL h1 hmul π}) ^ n • (⊤ : Submodule (lam v bL h1 hmul) (lam v bL h1 hmul)) ↔
      ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) bL).repr (x : v.adicCompletion ℚ ⊗[ℚ] L) i)
        ≤ exp (-(n : ℤ)) := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hc : ((unif v bL h1 hmul π ^ n : lam v bL h1 hmul) : v.adicCompletion ℚ ⊗[ℚ] L) =
      (π : v.adicCompletion ℚ) ^ n • (1 : v.adicCompletion ℚ ⊗[ℚ] L) := by
    rw [SubmonoidClass.coe_pow]
    show ((π : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L)) ^ n = _
    rw [smul_pow, one_pow]
  have hv : Valued.v ((π : v.adicCompletion ℚ) ^ n) = exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [Subring.coe_mul, hc, mul_smul_comm, mul_one, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hv]
    exact mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).1 (y.2 i))
  · intro hx
    have hπ0 : (π : v.adicCompletion ℚ) ^ n ≠ 0 := by
      intro h; rw [h, map_zero] at hv; exact exp_ne_zero hv.symm
    refine ⟨⟨((π : v.adicCompletion ℚ) ^ n)⁻¹ • (x : v.adicCompletion ℚ ⊗[ℚ] L), fun i => ?_⟩, Subtype.ext ?_⟩
    · rw [mem_adicCompletionIntegers, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, hv]
      calc (exp (-(n : ℤ)))⁻¹ * Valued.v _ ≤ (exp (-(n : ℤ)))⁻¹ * exp (-(n : ℤ)) :=
            by gcongr; exact hx i
        _ = 1 := inv_mul_cancel₀ exp_ne_zero
    · rw [Subring.coe_mul, hc, mul_smul_comm, mul_one, smul_smul, mul_inv_cancel₀ hπ0, one_smul]

theorem small_iff (x : lam v bL h1 hmul) :
    IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) ↔ x ∈ Ideal.span {unif v bL h1 hmul π} := by
  have := mem_pow_iff v bL h1 hmul π hπ x 1
  rw [pow_one, smul_eq_mul, Ideal.mul_top] at this
  rw [this]
  simp only [Nat.cast_one]
  exact forall_congr' fun i => Formalism.BasicNotions.Examples₂.wz_lt_one_iff _

theorem isAdicComplete :
    IsAdicComplete (Ideal.span {unif v bL h1 hmul π}) (lam v bL h1 hmul) := by
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have key := mem_pow_iff v bL h1 hmul π hπ
  haveI hO := Formalism.BasicNotions.Examples₂.adicInt_isAdicComplete (K := ℚ) v
  set e := Algebra.TensorProduct.basis (v.adicCompletion ℚ) bL with he
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · suffices h : (x : v.adicCompletion ℚ ⊗[ℚ] L) = 0 from Subtype.ext h
    apply e.repr.injective
    refine Finsupp.ext fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine Formalism.BasicNotions.Examples₂.adicInt_eq_zero_of_forall (K := ℚ) v _ fun n => ?_
    have := (key x n).1 (by simpa using (SModEq.sub_mem.1 (hx n)))
    exact this i
  · have hcoord : ∀ i, ∃ Li : v.adicCompletionIntegers ℚ, ∀ n,
        Valued.v (e.repr (f n : v.adicCompletion ℚ ⊗[ℚ] L) i - Li) ≤ exp (-(n : ℤ)) := by
      intro i
      obtain ⟨Li, hLi⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ))
        (fun n => (⟨e.repr (f n : v.adicCompletion ℚ ⊗[ℚ] L) i, (f n).2 i⟩ : v.adicCompletionIntegers ℚ))
        (fun {m n} hmn => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Formalism.BasicNotions.Examples₂.adicInt_mem_pow_iff]
          have := (key (f m - f n) m).1 (SModEq.sub_mem.1 (hf hmn)) i
          simpa [map_sub] using this)
      refine ⟨Li, fun n => ?_⟩
      have := SModEq.sub_mem.1 (hLi n)
      rw [smul_eq_mul, Ideal.mul_top, Formalism.BasicNotions.Examples₂.adicInt_mem_pow_iff] at this
      simpa using this
    choose Lc hLc using hcoord
    have hrep : ∀ (w : κ → v.adicCompletion ℚ) i, e.repr (e.equivFun.symm w) i = w i := fun w i => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hLmem : IsIntB v bL (e.equivFun.symm fun i => (Lc i : v.adicCompletion ℚ)) := fun i => by
      rw [hrep]; exact (Lc i).2
    refine ⟨⟨_, hLmem⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    have h := hLc i n
    rw [AddSubgroupClass.coe_sub, map_sub, Finsupp.sub_apply]
    rw [show (e.repr ((⟨_, hLmem⟩ : lam v bL h1 hmul) : v.adicCompletion ℚ ⊗[ℚ] L)) i = (Lc i : v.adicCompletion ℚ) from hrep _ i]
    simpa using h

end GlobalTheory.AdicSpan.HenselSqrt

namespace GlobalTheory.AdicSpan.HenselSqrt

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem exists_sqrt : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (κ : Type)
    (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    ∀ u : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL u → IsSmallB v bL (u - 1) →
    ∃ f : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑f ∧ IsIntB v bL ↑f⁻¹ ∧
      (f : v.adicCompletion ℚ ⊗[ℚ] L) ^ 2 = u ∧
      IsSmallB v bL (↑f - 1) ∧
      ∀ g : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL g → g ^ 2 = u → IsSmallB v bL (g - 1) → g = ↑f := by
  intro v L _ _ κ bL h2 h1 hmul _ u hu hsu
  obtain ⟨π, hπ⟩ := Formalism.BasicNotions.Examples₂.adicInt_exists_unif (K := ℚ) v
  haveI := isAdicComplete v bL h1 hmul π hπ
  haveI : HenselianRing (lam v bL h1 hmul) (Ideal.span {unif v bL h1 hmul π}) :=
    IsAdicComplete.henselianRing _ _
  have hI := small_iff v bL h1 hmul π hπ
  have hjac : ∀ x ∈ Ideal.span {unif v bL h1 hmul π}, IsUnit (x + 1) := fun x hx => by
    simpa using Ring.mem_jacobson_iff.1 (HenselianRing.jac hx) 1

  have h20 : (2 : v.adicCompletion ℚ) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  have h2O : (2 : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
  let t : lam v bL h1 hmul := ⟨(2 : v.adicCompletion ℚ)⁻¹ • 1, isIntB_smul v bL h2O h1⟩
  have ht : (2 : lam v bL h1 hmul) * t = 1 := by
    apply Subtype.ext
    show (2 : v.adicCompletion ℚ ⊗[ℚ] L) * ((2 : v.adicCompletion ℚ)⁻¹ • 1) = 1
    rw [mul_smul_comm, mul_one,
      show (2 : v.adicCompletion ℚ ⊗[ℚ] L) = (2 : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L) by
        rw [two_smul, one_add_one_eq_two],
      smul_smul, inv_mul_cancel₀ h20, one_smul]
  have h2u : IsUnit (2 : lam v bL h1 hmul) := ⟨⟨2, t, ht, by rw [mul_comm]; exact ht⟩, rfl⟩

  let u' : lam v bL h1 hmul := ⟨u, hu⟩
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian (I := Ideal.span {unif v bL h1 hmul π})
    (Polynomial.X ^ 2 - Polynomial.C u') (Polynomial.monic_X_pow_sub_C _ two_ne_zero) 1 (by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow,
        ← hI]
      have := isSmallB_neg v bL hsu
      rwa [neg_sub] at this) (by
      have : Polynomial.eval 1 (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u')) = 2 := by
        set_option synthInstance.maxHeartbeats 200000 in
          simp; try norm_num
      rw [this]; exact h2u.map _)
  have ha2 : a ^ 2 = u' := by
    have := ha.eq_zero
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
    exact sub_eq_zero.1 this
  have haU : IsUnit a := by
    have := hjac _ haI
    rwa [sub_add_cancel] at this
  refine ⟨Units.map (lam v bL h1 hmul).subtype.toMonoidHom haU.unit, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Units.coe_map, IsUnit.unit_spec]; exact a.2
  · rw [← map_inv]; simp only [Units.coe_map]; exact (haU.unit⁻¹ : (lam v bL h1 hmul)ˣ).1.2
  · simp only [Units.coe_map, IsUnit.unit_spec]
    exact congrArg Subtype.val ha2
  · simp only [Units.coe_map, IsUnit.unit_spec]
    exact (hI (a - 1)).2 haI
  · intro g hg hg2 hgs
    simp only [Units.coe_map, IsUnit.unit_spec]
    let g' : lam v bL h1 hmul := ⟨g, hg⟩
    have hgI : g' - 1 ∈ Ideal.span {unif v bL h1 hmul π} := (hI (g' - 1)).1 hgs
    have hg'2 : g' ^ 2 = u' := Subtype.ext hg2
    have h0 : (g' - a) * (g' + a) = 0 := by
      have : (g' - a) * (g' + a) = g' ^ 2 - a ^ 2 := by ring
      rw [this, hg'2, ha2, sub_self]
    have hx := hjac _ (Ideal.mul_mem_right t _ (add_mem hgI haI))
    have hsum : g' + a = 2 * (((g' - 1) + (a - 1)) * t + 1) := by
      linear_combination (-(g' + a - 2)) * ht
    have hU : IsUnit (g' + a) := by rw [hsum]; exact h2u.mul hx
    have := (hU.mul_left_eq_zero).1 h0
    exact congrArg Subtype.val (sub_eq_zero.1 this)

end GlobalTheory.AdicSpan.HenselSqrt
end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.integral_depth_power_lastSimpleReflectionCell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ z : ℂ, ‖z‖ < 1 →
      Integrable (fun u : cellU y => (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)) μ ∧
      ∫ u : cellU y, (z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) ∂μ = cSU q z ∧
      ∫⁻ u : cellU y, ‖(z / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n)‖ₑ ∂μ = ‖cSU q ((‖z‖ : ℝ) : ℂ)‖ₑ := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell | exact GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.integral_depth_cell <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.integral_diagonal_conj_lastSimpleReflectionCell : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) * ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal, ∫⁻ u : cellU y, F (t⁻¹ * (u : GU σ n) * t) ∂μ =
        ‖(q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k)))‖ₑ * ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last | exact GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.integral_conj_diag_cellU_last <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

theorem _root_.GlobalTheory.T.unitaryWeylCell_haar_rightTranslate_invariant : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ p : cellU y,
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal,
        ∫⁻ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  first | exact @GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv | exact GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv | (intros; apply GlobalTheory.WeylCell.WeylUnipotentShell.cellU_haar_rightInv <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical

theorem _root_.GlobalTheory.T.lintegral_det_pow_integer_matrices_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (n : ℕ) (s : ℝ), -1 < s →
    ∫⁻ X : Matrix (Fin n) (Fin n) k, (intM k (Fin n) (Fin n)).indicator (fun Y => ENNReal.ofReal (if h : Y.det = 0 then 0 else nabs k (Units.mk0 Y.det h)) ^ s) X ∂(volM μ (Fin n) (Fin n)) < ⊤ := by
  first | exact @GlobalTheory.GJInt.intdet | exact GlobalTheory.GJInt.intdet | (intros; apply GlobalTheory.GJInt.intdet <;> assumption)
end
