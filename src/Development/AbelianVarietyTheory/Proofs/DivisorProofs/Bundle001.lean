module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
public import Lean.Elab.AutoBound
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Basis
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

section

set_option autoImplicit false

namespace GlobalTheory.DegCmp

open Polynomial

end GlobalTheory.DegCmp
end

section

open Matrix

namespace GlobalTheory.OrbitsGLParab

variable {k : Type} [Field k]

variable {n m : ℕ}



end GlobalTheory.OrbitsGLParab
end

section

open scoped TensorProduct

namespace GlobalTheory.OneTensorSpanTop

theorem span_one_tmul_eq_top (k : Type) [Field k] (C O : Type) [CommRing C] [Ring O]
    [Algebra C O] [Algebra C k] :
    Submodule.span k (Set.range fun (o : O) ↦ (1 : k) ⊗ₜ[C] o) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a o =>
    have h : a ⊗ₜ[C] o = a • ((1 : k) ⊗ₜ[C] o) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨o, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end GlobalTheory.OneTensorSpanTop
end

section

namespace GlobalTheory.CommutatorPowerFormula

theorem commutator_pow_of_commutator_eq_smul {A : Type} [Ring A] [Algebra ℚ A] {H X : A} {s : ℚ}
    (h : H * X - X * H = s • X) (k : ℕ) :
    H * X ^ k - X ^ k * H = ((k : ℚ) * s) • X ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have e : H * X ^ (n + 1) - X ^ (n + 1) * H
        = (H * X ^ n - X ^ n * H) * X + X ^ n * (H * X - X * H) := by
      rw [pow_succ]
      noncomm_ring
    rw [e, ih, h, smul_mul_assoc, mul_smul_comm, ← pow_succ, ← add_smul]
    congr 1
    push_cast
    ring

end GlobalTheory.CommutatorPowerFormula
end

section

namespace GlobalTheory.CocycleCoboundaryNumerator

theorem exists_numerator (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (u v : D)
    (f : (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hf : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ u) → IsUnit (ψ v) →
        f E' (θ.comp ψ) = θ (f E ψ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ u) → IsUnit (ψ v) → f E ψ * (ψ u * ψ v) ^ N = ψ c := by
  classical
  let L := Localization.Away (u * v)
  let ψ₀ : D →ₐ[R] L := IsScalarTower.toAlgHom R D L
  have hψ₀ : IsUnit (ψ₀ u * ψ₀ v) := by
    rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (u * v)
  obtain ⟨⟨a, _, k, rfl⟩, hk⟩ := IsLocalization.surj (Submonoid.powers (u * v)) (f L ψ₀)
  refine ⟨k, fun N hN => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨a * (u * v) ^ j, fun E _ _ ψ hu hv => ?_⟩
  have huv : IsUnit (ψ (u * v)) := by rw [map_mul]; exact hu.mul hv
  let θ : L →ₐ[R] E := IsLocalization.Away.liftAlgHom (u * v) huv
  have hθ : ∀ x : D, θ (algebraMap D L x) = ψ x := fun x =>
    IsLocalization.Away.lift_eq (u * v) huv x
  have hcomp : θ.comp ψ₀ = ψ := AlgHom.ext fun x => hθ x
  have key := hf L E ψ₀ θ (isUnit_of_mul_isUnit_left hψ₀) (isUnit_of_mul_isUnit_right hψ₀)
  rw [hcomp] at key
  have hk' := congrArg θ hk
  simp only [map_mul, hθ] at hk'
  rw [key, map_mul, ← hk']
  simp only [map_pow, map_mul]
  ring

theorem exists_pow_mul_eq_zero (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (u x : D)
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ u) → ψ x = 0) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → u ^ M * x = 0 := by
  let L := Localization.Away u
  have h0 : algebraMap D L x = 0 :=
    h L (IsScalarTower.toAlgHom R D L) (IsLocalization.Away.algebraMap_isUnit u)
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) L x).mp h0
  refine ⟨m, fun M hM => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hm' : u ^ m * x = 0 := hm
  rw [pow_add, mul_comm (u ^ m), mul_assoc, hm', mul_zero]

theorem map_inverse_of_isUnit {E E' : Type} [CommRing E] [CommRing E'] (θ : E →+* E') {x : E}
    (hx : IsUnit x) : Ring.inverse (θ x) = θ (Ring.inverse x) := by
  obtain ⟨w, rfl⟩ := hx
  have hw : θ (w : E) = ((Units.map θ.toMonoidHom w : E'ˣ) : E') := rfl
  rw [Ring.inverse_unit, hw, Ring.inverse_unit]
  rfl

theorem cocycle_is_coboundary (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (n : ℕ) (s : Fin n → D) (hs : Ideal.span (Set.range s) = ⊤)
    (d : Fin n → Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hnat : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
      [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E' (AlgHom.comp θ ψ) = θ (d a b E ψ))
    (hcoc : ∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) →
        d a b E ψ + d b c E ψ = d a c E ψ) :
    ∃ (e : Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E),
      (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
        [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
          e a E' (AlgHom.comp θ ψ) = θ (e a E ψ)) ∧
      ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  classical

  have h1 : ∀ a b : Fin n, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E]
      [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E ψ * (ψ (s a) * ψ (s b)) ^ N = ψ c := fun a b =>
    exists_numerator R D (s a) (s b) (d a b) (fun E _ _ E' _ _ ψ θ ha hb => hnat a b E E' ψ θ ha hb)
  choose N₀ hN₀ using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ a b, N₀ a b ≤ N :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n => N₀ p.1 p.2), fun a b =>
      Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (a, b))⟩
  choose c hc using fun a b => hN₀ a b N (hN a b)

  have h2 : ∀ a b k : Fin n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → (s a * s b * s k) ^ M *
      (s k ^ N * c a b - s a ^ N * c k b + s b ^ N * c k a) = 0 := by
    intro a b k
    apply exists_pow_mul_eq_zero R D
    intro E _ _ ψ hu
    rw [map_mul, map_mul] at hu
    have ha := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
    have hb := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
    have hk := isUnit_of_mul_isUnit_right hu
    have e4 := hcoc k a b E ψ hk ha hb
    simp only [map_add (f := _), map_sub, map_mul, map_pow]
    rw [← hc a b E ψ ha hb, ← hc k b E ψ hk hb, ← hc k a E ψ hk ha]
    linear_combination (ψ (s a) * ψ (s b) * ψ (s k)) ^ N * e4
  choose M₀ hM₀ using h2
  obtain ⟨M, hM⟩ : ∃ M, ∀ a b k, M₀ a b k ≤ M :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2), fun a b k =>
      Finset.le_sup (f := fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2)
        (Finset.mem_univ (a, b, k))⟩

  obtain ⟨K, c', hc', hy⟩ : ∃ (K : ℕ) (c' : Fin n → Fin n → D),
      (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ * (ψ (s a) * ψ (s b)) ^ K = ψ (c' a b)) ∧
      ∀ a b k, s k ^ K * c' a b = s a ^ K * c' k b - s b ^ K * c' k a := by
    refine ⟨N + M, fun a b => c a b * (s a * s b) ^ M, fun a b E _ _ ψ ha hb => ?_,
      fun a b k => ?_⟩
    · rw [map_mul, ← hc a b E ψ ha hb, map_pow, map_mul, pow_add]
      ring
    · linear_combination hM₀ a b k M (hM a b k)

  have hsK : Ideal.span (Set.range fun i => s i ^ K) = ⊤ := by
    have h := Ideal.span_pow_eq_top _ hs K
    rw [← Set.range_comp] at h
    exact h
  have h1mem : (1 : D) ∈ Ideal.span (Set.range fun i => s i ^ K) := by
    rw [hsK]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun D).mp h1mem
  refine ⟨fun a E _ _ ψ => ∑ k, ψ (g k * c' k a) * Ring.inverse (ψ (s a)) ^ K, ?_, ?_⟩
  · intro a E _ _ E' _ _ ψ θ ha
    have hinv : Ring.inverse (θ (ψ (s a))) = θ (Ring.inverse (ψ (s a))) :=
      map_inverse_of_isUnit (θ : E →+* E') ha

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hinv]
    simp only [map_mul, map_pow]
  · intro a b E _ _ ψ ha hb
    have hAK : ψ (s a) ^ K * Ring.inverse (ψ (s a)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ ha, one_pow]
    have hBK : ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ hb, one_pow]
    have hab := hc' a b E ψ ha hb
    have hsum : ∑ k, ψ (g k) * ψ (s k) ^ K = 1 := by
      have h := congrArg ψ hg

      simpa only [map_sum, smul_eq_mul, map_mul, map_pow, map_one] using h
    have hd : d a b E ψ = ∑ k, ψ (g k) * ψ (s k) ^ K * d a b E ψ := by
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hyk := congrArg ψ (hy a b k)
    simp only [map_mul, map_pow, map_sub] at hyk
    simp only [map_mul]
    linear_combination (ψ (g k)) * ((Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hyk
      + (ψ (s k) ^ K * Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hab
      + (Ring.inverse (ψ (s b)) ^ K * ψ (c' k b)
          - ψ (s k) ^ K * d a b E ψ * ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K) * hAK
      - (Ring.inverse (ψ (s a)) ^ K * ψ (c' k a) + ψ (s k) ^ K * d a b E ψ) * hBK)

end GlobalTheory.CocycleCoboundaryNumerator
end

section

open scoped nonZeroDivisors

namespace GlobalTheory

namespace IndexNormEmb

theorem card_quot_span_eq (B : Type) [CommRing B] [IsDomain B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (b : B) (hb : b ≠ 0) : Nat.card (B ⧸ Ideal.span {b}) = (Algebra.norm ℤ b).natAbs := by
  classical
  rw [Algebra.norm_apply]
  let bs := Module.Free.chooseBasis ℤ B
  have := Submodule.natAbs_det_equiv ((Ideal.span {b}).restrictScalars ℤ)
    (bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _))
  rw [show Nat.card (B ⧸ Ideal.span {b}) = Nat.card (B ⧸ (Ideal.span {b}).restrictScalars ℤ) from rfl,
    ← this]
  congr
  refine bs.ext fun i => ?_
  simp
  show ((bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _) (bs i) : Ideal.span {b}) : B) = b * bs i
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Ideal.basisSpanSingleton_apply]

theorem injective_of_ringHom (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B]
    (τ : B →+* ℂ) : Function.Injective τ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have h : (RingHom.ker τ).comap (algebraMap ℤ B) = ⊥ := by
    ext n
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have := Ideal.eq_bot_of_comap_eq_bot h
  have hx' : x ∈ RingHom.ker τ := hx
  rw [this] at hx'
  simpa using hx'

noncomputable def embEquiv (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] :
    (FractionRing B →ₐ[ℚ] ℂ) ≃ (B →+* ℂ) where
  toFun σ := (σ : FractionRing B →+* ℂ).comp (algebraMap B (FractionRing B))
  invFun τ := (IsFractionRing.lift (K := FractionRing B) (injective_of_ringHom B τ)).toRatAlgHom
  left_inv σ := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext B⁰
    ext x
    simp
  right_inv τ := by
    ext x
    simp

theorem log_card_quot_span_eq_finsum_log_norm : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B),
    b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧
      Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  intro B _ _ _ _ b hb
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B ℤ⁰) (FractionRing B) :=
    Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors ℤ B (FractionRing B)
  haveI : IsScalarTower ℤ ℚ (FractionRing B) :=
    ⟨fun n q x => by rw [zsmul_eq_mul, zsmul_eq_mul, Algebra.smul_def, Algebra.smul_def, map_mul, map_intCast, mul_assoc]⟩
  haveI : @IsScalarTower ℤ ℚ (FractionRing B) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : FiniteDimensional ℚ (FractionRing B) := Module.Finite.of_isLocalization ℤ B ℤ⁰
  have hcard := card_quot_span_eq B b hb
  have hN0 : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.mpr hN0), ?_⟩
  have hN : algebraMap ℤ ℂ (Algebra.norm ℤ b) =
      ∏ σ : FractionRing B →ₐ[ℚ] ℂ, σ (algebraMap B (FractionRing B) b) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ ℂ,
      ← Algebra.norm_localization ℤ (Sₘ := FractionRing B) ℤ⁰, Algebra.norm_eq_prod_embeddings]
  have hx : algebraMap B (FractionRing B) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B (FractionRing B))).mpr hb
  rw [← finsum_comp_equiv (embEquiv B), finsum_eq_sum_of_fintype]
  change _ = ∑ σ : FractionRing B →ₐ[ℚ] ℂ, Real.log ‖σ (algebraMap B (FractionRing B) b)‖
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hx)),
    ← norm_prod, ← hN, hcard, Nat.cast_natAbs, eq_intCast, Complex.norm_intCast, Int.cast_abs]

end IndexNormEmb

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem localizedModule_mem_annSpan_smul_top (D : Type) [CommRing D] (S : Submonoid D) (x : D)
    (N : Type 1) [AddCommGroup N] [Module D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    ∀ n : LocalizedModule S N, algebraMap D (Localization S) x • n = 0 →
      n ∈ Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} •
        (⊤ : Submodule (Localization S) (LocalizedModule S N)) := by
  intro n hn
  set J : Ideal (Localization S) :=
    Ideal.span {a : Localization S | algebraMap D (Localization S) x * a = 0} with hJ
  have hIJ : Ideal.span {a : D | x * a = 0} ≤ J.comap (algebraMap D (Localization S)) := by
    rw [Ideal.span_le]
    intro a ha
    show algebraMap D (Localization S) a ∈ J
    apply Ideal.subset_span
    show algebraMap D (Localization S) x * algebraMap D (Localization S) a = 0
    rw [← map_mul, show x * a = 0 from ha, map_zero]
  have key : Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N) ≤
      ((J • (⊤ : Submodule (Localization S) (LocalizedModule S N))).restrictScalars D).comap
        (LocalizedModule.mkLinearMap S N) := by
    rw [Submodule.smul_le]
    intro r hr m _
    show LocalizedModule.mk (r • m) 1 ∈ J • (⊤ : Submodule (Localization S) (LocalizedModule S N))
    rw [← LocalizedModule.smul'_mk, ← algebraMap_smul (Localization S) r]
    exact Submodule.smul_mem_smul (hIJ hr) trivial
  induction n using LocalizedModule.induction_on with
  | _ m s =>
    rw [algebraMap_smul (Localization S) x, LocalizedModule.smul'_mk,
      ← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq] at hn
    obtain ⟨u, hu⟩ := hn
    simp only [one_smul, smul_zero] at hu
    have hxu : x • (u • m) = 0 := by rw [smul_comm]; exact hu
    have hmem := key (h _ hxu)
    have he : LocalizedModule.mk m s =
        (Localization.mk 1 (u * s) : Localization S) • LocalizedModule.mk (u • m) 1 := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one, LocalizedModule.mk_cancel_common_left]
    rw [he]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ker_smul_le_ideal_smul_of_free : ∀ (Λ : Type) [CommRing Λ] (t : Λ), (∀ x : Λ, t * x = 0 → x ∈ Ideal.span {t}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M], Module.Free Λ M → ∀ m : M, t • m = 0 → m ∈ Ideal.span {t} • (⊤ : Submodule Λ M) := by
  intro Λ _ t ht M _ _ hfree m hm
  let b := Module.Free.chooseBasis Λ M
  have hc : ∀ i, ∃ d, b.repr m i = t * d := by
    intro i
    have h0 : t * b.repr m i = 0 := by
      have := congrArg (fun x => b.repr x i) hm
      simpa using this
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ht _ h0)
    exact ⟨d, by rw [← hd, mul_comm]⟩
  choose d hd using hc
  have hm' : m = t • ∑ i ∈ (b.repr m).support, d i • b i := by
    have e := b.linearCombination_repr m
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
    rw [Finset.smul_sum]
    conv_lhs => rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i, mul_smul]
  rw [hm']
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top

end GlobalTheory
end

section

open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem Submodule.exists_pow_smul_mem_of_forall_exists :
    ∀ (S : Type) [CommRing S] (I : Ideal S) (M : Type) [AddCommGroup M] [Module S M]
      [Module.Finite S M] (N : Submodule S M),
      (∀ y : M, ∃ k : ℕ, ∀ a ∈ I ^ k, a • y ∈ N) → ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ y : M, a • y ∈ N := by
  intro S _ I M _ _ _ N h
  choose f hf using h
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := M)
  refine ⟨s.sup f, fun a ha y => ?_⟩
  have key : _root_.Submodule.span S (s : Set M) ≤ N.comap (a • LinearMap.id) := by
    rw [_root_.Submodule.span_le]
    intro x hx
    show (a • LinearMap.id : M →ₗ[S] M) x ∈ N
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact hf x a (Ideal.pow_le_pow_right (Finset.le_sup (f := f) hx) ha)
  have hy : y ∈ _root_.Submodule.span S (s : Set M) := by rw [hs]; trivial
  have := key hy
  rwa [_root_.Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at this

end GlobalTheory
end
