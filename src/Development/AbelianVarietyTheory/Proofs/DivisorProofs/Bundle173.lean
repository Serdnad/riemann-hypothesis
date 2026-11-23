module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle129
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

section

open TensorProduct

noncomputable section
namespace GlobalTheory.DenseSec

theorem locQuot_finiteType_formallyUnramified (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A]
    (g : ℕ) (t : Fin g → A) (h : A) (hE : GlobalTheory.DenseSec.EtChart R A t h) (Ω : Type) [Field Ω] [Algebra R Ω]
    (I : Ideal (TensorProduct R Ω A)) :
    (letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
      (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
    Algebra.FiniteType (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) ∧
      Algebra.FormallyUnramified (MvPolynomial (Fin g) Ω)
        (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) := by
  letI algPD : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I)
      (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  letI algRA : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI algRP : Algebra (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω) := MvPolynomial.algebraMvPolynomial
  letI algRD : Algebra (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    ((algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      (algebraMap (MvPolynomial (Fin g) R) (MvPolynomial (Fin g) Ω))).toAlgebra
  haveI hST := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algRP algPD algRD (fun _ => rfl)
  let f : A →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    (algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))).comp
      ((Ideal.Quotient.mk I).comp (Algebra.TensorProduct.includeRight (R := R) (A := Ω) (B := A)).toRingHom)
  have hf : ∀ a, f a = algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
      (Ideal.Quotient.mk I (1 ⊗ₜ[R] a)) := fun a => rfl
  have hu : IsUnit (f h) := by rw [hf]; exact IsLocalization.Away.algebraMap_isUnit _
  let ψ0 : Localization.Away h →+* Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    IsLocalization.Away.lift h hu
  have hψ0 : ∀ a, ψ0 (algebraMap A (Localization.Away h) a) = f a :=
    IsLocalization.Away.lift_eq h hu
  have hΩ : ∀ w : Ω, algebraMap Ω (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) w =
      algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))
        (Ideal.Quotient.mk I (w ⊗ₜ[R] 1)) := by
    intro w
    rw [IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ I)]
    rfl
  have hcomp : ψ0.comp (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h)) =
      algebraMap (MvPolynomial (Fin g) R) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.C r))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.C r))
      rw [hψ0, MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C, hf, hΩ]
      congr 2
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
    · intro i
      show ψ0 (algebraMap A _ (MvPolynomial.aeval t (MvPolynomial.X i))) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap R Ω) (MvPolynomial.X i))
      rw [hψ0, MvPolynomial.map_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hf]
  let ψ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    { ψ0 with commutes' := fun p => RingHom.congr_fun hcomp p }
  let Φ : MvPolynomial (Fin g) Ω ⊗[MvPolynomial (Fin g) R] Localization.Away h →ₐ[MvPolynomial (Fin g) Ω]
      Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ψ (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (p : MvPolynomial (Fin g) Ω) (y : Localization.Away h), Φ (p ⊗ₜ y) = algebraMap _ _ p * ψ0 y :=
    fun p y => Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hQ : ∀ x : TensorProduct R Ω A ⧸ I,
      algebraMap _ (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x ∈ Φ.range := by
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction b using TensorProduct.inductionOn with
    | tmul w a =>
      refine ⟨MvPolynomial.C w ⊗ₜ algebraMap A _ a, ?_⟩
      show Φ (MvPolynomial.C w ⊗ₜ algebraMap A _ a) = _
      rw [hΦ, hψ0, hf]
      show MvPolynomial.aeval _ (MvPolynomial.C w) * _ = _
      rw [MvPolynomial.aeval_C, hΩ, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [RingHom.map_add (Ideal.Quotient.mk I), RingHom.map_add (algebraMap (Ω ⊗[R] A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) ]; exact add_mem hx hy
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) z
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
    have hs : s = ⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ ^ n := Subtype.ext hn.symm
    have hinv : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
        (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
          Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) =
        Φ (1 ⊗ₜ IsLocalization.mk' (Localization.Away h) (1 : A) (⟨h, Submonoid.mem_powers _⟩ : Submonoid.powers h)) := by
      rw [hΦ, map_one, one_mul, IsLocalization.mk'_eq_iff_eq_mul]
      show _ = _ * f h
      rw [← hψ0, ← map_mul, IsLocalization.mk'_spec]
      simp
    have : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) x s ∈ Φ.range := by
      have hpow : IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I) s =
          (IsLocalization.mk' (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (1 : TensorProduct R Ω A ⧸ I)
            (⟨Ideal.Quotient.mk I (1 ⊗ₜ[R] h), Submonoid.mem_powers _⟩ :
              Submonoid.powers (Ideal.Quotient.mk I (1 ⊗ₜ[R] h)))) ^ n := by
        rw [hs, ← IsLocalization.mk'_pow, one_pow]
      rw [IsLocalization.mk'_eq_mul_mk'_one, hpow, hinv]
      exact mul_mem (hQ x) (pow_mem (AlgHom.mem_range_self Φ _) n)
    exact this
  exact ⟨Algebra.FiniteType.of_surjective Φ hsurj, Algebra.FormallyUnramified.of_surjective Φ hsurj⟩

end GlobalTheory.DenseSec
end
end

section

open IsLocalRing

namespace GlobalTheory.DenseSec

theorem factorₐ_comp_factorₐ {P R : Type} [CommRing P] [CommRing R] [Algebra P R] {I J K : Ideal R}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    (Ideal.Quotient.factorₐ P hJK).comp (Ideal.Quotient.factorₐ P hIJ) =
      Ideal.Quotient.factorₐ P (hIJ.trans hJK) := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem hensel_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R →
    ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h →
    ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) →
    ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  intro R _ _ hc A _ _ g t h hE ε hε c hcε
  classical
  haveI := hc
  letI iPB : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI iPR : Algebra (MvPolynomial (Fin g) R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  have hPB : ∀ p, algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p =
      algebraMap A (Localization.Away h) (MvPolynomial.aeval t p) := fun _ => rfl
  have hPR : ∀ p, algebraMap (MvPolynomial (Fin g) R) R p = MvPolynomial.aeval c p := fun _ => rfl
  let m := maximalIdeal R

  let e' : Localization.Away h →+* R := IsLocalization.Away.lift h (g := (ε : A →+* R)) hε
  have he' : ∀ x : A, e' (algebraMap A (Localization.Away h) x) = ε x := fun x =>
    IsLocalization.Away.lift_eq h (g := (ε : A →+* R)) hε x
  have hmod : (Ideal.Quotient.mk m).comp ((ε : A →+* R).comp (MvPolynomial.aeval (R := R) t).toRingHom) =
      (Ideal.Quotient.mk m).comp (MvPolynomial.aeval c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact (Ideal.Quotient.eq.2 (by
        have := hcε i
        rw [← neg_mem_iff, neg_sub] at this
        exact this))
  let f₁ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m :=
    { toRingHom := (Ideal.Quotient.mk m).comp e'
      commutes' := fun p => by
        show Ideal.Quotient.mk m (e' (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p)) =
          algebraMap (MvPolynomial (Fin g) R) (R ⧸ m) p
        rw [hPB, he']
        show Ideal.Quotient.mk m (ε (MvPolynomial.aeval t p)) = Ideal.Quotient.mk m (MvPolynomial.aeval c p)
        exact congrArg (fun φ : MvPolynomial (Fin g) R →+* R ⧸ m => φ p) hmod }

  have hle : ∀ n : ℕ, m ^ (n + 1) ≤ m := fun n => Ideal.pow_le_self n.succ_ne_zero
  let q : ∀ n : ℕ, R ⧸ m ^ (n + 1) →ₐ[MvPolynomial (Fin g) R] R ⧸ m := fun n =>
    Ideal.Quotient.factorₐ _ (hle n)
  have hqs : ∀ n, Function.Surjective (q n) := fun n x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hqn : ∀ n, IsNilpotent (RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m)) := fun n => by
    refine ⟨n + 1, le_bot_iff.1 ?_⟩
    have hk : RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m) = Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m :=
      Ideal.Quotient.factor_ker (hle n)
    rw [hk, ← Ideal.map_pow, Ideal.map_quotient_self]
  let F : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ (n + 1) := fun n =>
    Algebra.FormallySmooth.liftOfSurjective f₁ (q n) (hqs n) (hqn n)
  have hF : ∀ n, (q n).comp (F n) = f₁ := fun n => Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hFc : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn))).comp (F n) = F k := by
    intro k n hkn
    refine Algebra.FormallyUnramified.ext' (q k : R ⧸ m ^ (k + 1) →+* R ⧸ m) (hqn k) _ _ fun x => ?_
    have h1 := congrArg (fun φ => φ x) (hF n)
    have h2 := congrArg (fun φ => φ x) (hF k)
    simp only [AlgHom.comp_apply] at h1 h2
    show (q k) ((Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1))) (F n x)) = q k (F k x)
    rw [h2, ← h1]
    have := congrArg (fun φ => φ (F n x)) (factorₐ_comp_factorₐ (P := MvPolynomial (Fin g) R)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1)) (hle k))
    simpa only [AlgHom.comp_apply] using this
  let f : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ n := fun n =>
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (F n)
  have hf : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right hkn)).comp (f n) = f k := by
    intro k n hkn
    simp only [f]
    rw [← AlgHom.comp_assoc, factorₐ_comp_factorₐ, ← hFc hkn, ← AlgHom.comp_assoc, factorₐ_comp_factorₐ]
  let Φ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R := IsAdicComplete.liftAlgHom m f hf
  let a : A →ₐ[R] R :=
    { toRingHom := (Φ : Localization.Away h →+* R).comp (algebraMap A (Localization.Away h))
      commutes' := fun r => by
        show Φ (algebraMap A (Localization.Away h) (algebraMap R A r)) = algebraMap R R r
        have : algebraMap A (Localization.Away h) (algebraMap R A r) =
            algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.C r) := by
          rw [hPB, MvPolynomial.aeval_C]
        rw [this, Φ.commutes, hPR, MvPolynomial.aeval_C] }
  refine ⟨a, ?_, fun i => ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit h).map Φ
  · show Φ (algebraMap A (Localization.Away h) (t i)) = c i
    have : algebraMap A (Localization.Away h) (t i) =
        algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.X i) := by
      rw [hPB, MvPolynomial.aeval_X]
    rw [this, Φ.commutes, hPR, MvPolynomial.aeval_X]

end GlobalTheory.DenseSec
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.HartFlatBaseChange

def divIdeal (A S X : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup X] [Module S X]
    (a : A) (y : X) : Ideal A where
  carrier := {u | ∃ x : X, algebraMap A S u • y = algebraMap A S a • x}
  add_mem' := by
    rintro u v ⟨x, hx⟩ ⟨x', hx'⟩
    exact ⟨x + x', by rw [map_add (f := _), add_smul, hx, hx', smul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c u ⟨x, hx⟩
    refine ⟨algebraMap A S c • x, ?_⟩
    rw [smul_eq_mul, map_mul, mul_smul, hx, smul_comm]

theorem lTensor_smul_id_apply (R M O : Type) [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    [Algebra R O] (r : R) (x : O ⊗[R] M) :
    (r • LinearMap.id : M →ₗ[R] M).lTensor O x = algebraMap R O r • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o n => simp [LinearMap.lTensor_tmul, algebraMap_smul, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

end GlobalTheory.HartFlatBaseChange

open GlobalTheory.HartFlatBaseChange in
theorem GlobalTheory.GoodEtale.hart_tensor_of_flat : ∀ (A R M O : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module R M] [CommRing O] [Algebra R O] [Algebra A O] [IsScalarTower A R O]
    [Module.Flat R O], GlobalTheory.GoodEtale.Hart A R M → GlobalTheory.GoodEtale.Hart A O (O ⊗[R] M) := by
  intro A R M O _ _ _ _ _ _ _ _ _ _ _ hM a ha m hm
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (divIdeal A O (O ⊗[R] M) a m) : Submodule.FG _)
  have hsI : ∀ b ∈ s, b ∈ divIdeal A O (O ⊗[R] M) a m := fun b hb => hs ▸ Ideal.subset_span hb
  let f : M →ₗ[R] M := algebraMap A R a • LinearMap.id
  let N : Submodule R M := LinearMap.range f
  let g : M →ₗ[R] (s → M ⧸ N) := LinearMap.pi fun i => N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id)
  have hex : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have hyI : divIdeal A O (O ⊗[R] M) a m ≤ divIdeal A R M a y := by
        rw [← hs, Ideal.span_le]
        intro b hb
        have := congrFun hy ⟨b, hb⟩
        simp only [g, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range] at this
        obtain ⟨x, hx⟩ := this
        exact ⟨x, by simpa [f] using hx.symm⟩
      obtain ⟨m', hm'⟩ := hM a ha y fun p hp hp1 => by
        obtain ⟨u, hup, hu⟩ := hm p hp hp1
        exact ⟨u, hup, hyI hu⟩
      exact ⟨m', by simp [f, hm']⟩
    · rintro ⟨x, rfl⟩
      funext i
      simp only [g, f, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.zero_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N, LinearMap.mem_range]
      exact ⟨algebraMap A R i.1 • x, by simp [f, smul_comm (algebraMap A R a)]⟩
  have hexO := Module.Flat.lTensor_exact O hex
  have hcomp : ∀ (z : O ⊗[R] (s → M ⧸ N)) (i : s),
      TensorProduct.piRight R R O (fun _ : s => M ⧸ N) z i = (LinearMap.proj i).lTensor O z := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul o n => simp [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
    | add x y hx hy => rw [map_add (f := _), Pi.add_apply, hx, hy, map_add (f := _)]
  have hg : g.lTensor O m = 0 := by
    apply (TensorProduct.piRight R R O (fun _ : s => M ⧸ N)).injective
    funext i
    rw [hcomp, map_zero, Pi.zero_apply, ← LinearMap.lTensor_comp_apply]
    have hpg : (LinearMap.proj i).comp g = N.mkQ ∘ₗ (algebraMap A R i.1 • LinearMap.id) := rfl
    obtain ⟨m', hm'⟩ := hsI i.1 i.2
    rw [hpg, LinearMap.lTensor_comp_apply, lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply,
      hm', IsScalarTower.algebraMap_apply A R O, ← lTensor_smul_id_apply, ← LinearMap.lTensor_comp_apply,
      LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨m', hm'⟩ := (hexO m).1 hg
  exact ⟨m', by rw [← hm', lTensor_smul_id_apply, ← IsScalarTower.algebraMap_apply]⟩
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem faithfullyFlat_adicCompletion_span (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    Module.FaithfullyFlat R (AdicCompletion (Ideal.span {t}) R) := by
  haveI : Module.Flat R (AdicCompletion (Ideal.span {t}) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩
  rw [IsLocalRing.eq_maximalIdeal hm]
  have hle : Ideal.span {t} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).2 ht
  have hmax := AdicCompletion.isMaximal_map_of_le (Ideal.span {t}) (maximalIdeal R) hle
    (Submodule.fg_span_singleton t)
  intro h
  apply hmax.ne_top
  have e := Ideal.smul_top_eq_map (S := AdicCompletion (Ideal.span {t}) R) (maximalIdeal R)
  rw [h] at e
  apply Submodule.restrictScalars_injective R
  rw [← e]; rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem exists_integral_point (A R C : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing R] [CommRing C] [Algebra R C] (ρ : R →+* A) (hint : Algebra.IsIntegral R C)
    (s : C →+* FractionRing A) (hs : s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) :
    ∃ g : C →+* A, (algebraMap A (FractionRing A)).comp g = s ∧ g.comp (algebraMap R C) = ρ := by
  set K := FractionRing A
  have hmem : ∀ c : C, s c ∈ (algebraMap A K).range := by
    intro c
    obtain ⟨p, hp, hpc⟩ := hint.isIntegral c
    have hi : IsIntegral A (s c) := by
      refine ⟨p.map ρ, hp.map ρ, ?_⟩
      rw [Polynomial.eval₂_map, ← hs, ← Polynomial.hom_eval₂, hpc, map_zero]
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
    exact ⟨a, ha⟩
  let e := RingEquiv.ofBijective (algebraMap A K).rangeRestrict
    ⟨fun x y h => IsFractionRing.injective A K (congrArg Subtype.val h),
     (algebraMap A K).rangeRestrict_surjective⟩
  let g : C →+* A := e.symm.toRingHom.comp (s.codRestrict _ hmem)
  have hg : (algebraMap A K).comp g = s := by
    ext c
    have : e (g c) = s.codRestrict _ hmem c := by simp [g]
    exact congrArg Subtype.val this
  refine ⟨g, hg, ?_⟩
  ext r
  apply IsFractionRing.injective A K
  have := congrArg (fun f => f r) hs
  simp only [RingHom.comp_apply] at this
  change (algebraMap A K) (g (algebraMap R C r)) = _
  rw [← this, ← hg, RingHom.comp_apply]
  rfl

end GlobalTheory.GoodEtaleSection

namespace GlobalTheory.GoodEtaleSection

theorem mem_pow_of_mul_mem_pow (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A) (hρ : ρ.comp (algebraMap A R) = RingHom.id A)
    (t : R) (hker : RingHom.ker ρ = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R)
    (a : A) (ha : a ≠ 0) : ∀ (n : ℕ) (r : R), algebraMap A R a * r ∈ Ideal.span {t ^ n} →
      r ∈ Ideal.span {t ^ n} := by
  have hρa : ρ (algebraMap A R a) = a := by
    simpa using congrArg (fun f => f a) hρ
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r hr
    have hr1 : algebraMap A R a * r ∈ RingHom.ker ρ := by
      rw [hker, Ideal.mem_span_singleton]
      exact (dvd_pow_self t (Nat.succ_ne_zero n)).trans (Ideal.mem_span_singleton.1 hr)
    rw [RingHom.mem_ker, map_mul, hρa] at hr1
    have hr0 : r ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker]
      exact (mul_eq_zero.1 hr1).resolve_left ha
    obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton.1 hr0
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hr
    have h2 : algebraMap A R a * r' = t ^ n * q := by
      have : t * (algebraMap A R a * r') = t * (t ^ n * q) := by
        rw [pow_succ] at hq
        linear_combination hq
      have h3 : t * (algebraMap A R a * r' - t ^ n * q) = 0 := by rw [mul_sub, this, sub_self]
      exact sub_eq_zero.1 ((mul_left_mem_nonZeroDivisors_eq_zero_iff ht).1 h3)
    have := ih r' (Ideal.mem_span_singleton.2 ⟨q, h2⟩)
    obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton.1 this
    exact Ideal.mem_span_singleton.2 ⟨q', by ring⟩

theorem torsionFree_quot : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    ∀ n : ℕ, GlobalTheory.GoodEtale.TorsionFreeOver A R (R ⧸ Ideal.span {t} ^ n) := by
  intro A R _ _ _ _ ρ hρ t hker ht n a ha m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
  exact mem_pow_of_mul_mem_pow A R ρ hρ t hker ht a ha n r hm

end GlobalTheory.GoodEtaleSection
end

section

open IsLocalRing



namespace GlobalTheory

noncomputable def tensorIntegralClosureInclusion (S L D : Type) [CommRing S] [Field L] [Algebra S L]
    [CommRing D] [Algebra S D] :
    integralClosure S L →ₐ[S] integralClosure D (TensorProduct S D L) where
  toRingHom := GlobalTheory.AbhyankarLocal.toNorm S L D
  commutes' s := by
    ext
    change (1 : D) ⊗ₜ[S] (algebraMap S L s) = _
    exact (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes s

noncomputable instance instAlgebraIntegralClosureTensor (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    Algebra (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  (GlobalTheory.AbhyankarLocal.toNorm S L D).toAlgebra

instance (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D] :
    IsScalarTower S (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  IsScalarTower.of_algebraMap_eq fun s =>
    ((tensorIntegralClosureInclusion S L D).commutes s).symm

theorem algebraMap_integralClosure_tensor_eq (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) =
      GlobalTheory.AbhyankarLocal.toNorm S L D := rfl

end GlobalTheory
end
