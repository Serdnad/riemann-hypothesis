module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle023
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle019
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle027
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory

theorem supLattice_localisation_of_unitBall (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK)
    (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s : 𝓞 Ks, s ∉ la.asIdeal ∧ s • (f : WL) ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | (apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice ..)

end GlobalTheory
end

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem recursive_matrixPower_eq_matrix_pow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) :
    Matrix.of (Formalism.REAL.epow E k) = (Matrix.of E) ^ k := by
  induction k with
  | zero =>
    ext a b
    simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    ext a b
    rw [pow_succ, ← ih]
    simp [Formalism.REAL.epow, Matrix.mul_apply]

theorem scalarMatrix_mul_algebraMatrix_mul_apply {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((algebraMap ℂ A).mapMatrix P.transpose * M * (algebraMap ℂ A).mapMatrix Q.transpose) a b
      = ∑ c, ∑ d, (P c a * Q b d) • M c d := by
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, mul_comm]

theorem etr_conj_scalar_matrix {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  set L : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix P.transpose with hL
  set R : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix (P⁻¹).transpose with hR
  have hLR : L * R = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one, map_one]
  have hRL : R * L = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one, map_one]
  have hE : Matrix.of (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) = L * Matrix.of E * R := by
    ext a b
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]
    rfl
  have hpow : ∀ m : ℕ, (L * Matrix.of E * R) ^ m = L * (Matrix.of E) ^ m * R := by
    intro m
    induction m with
    | zero => simp [hLR]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc L * Matrix.of E ^ m * R * (L * Matrix.of E * R)
          = L * Matrix.of E ^ m * (R * L) * Matrix.of E * R := by simp only [mul_assoc]
        _ = L * (Matrix.of E ^ m * Matrix.of E) * R := by rw [hRL]; simp only [mul_assoc, one_mul]
  have hk := recursive_matrixPower_eq_matrix_pow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k
  rw [hE, hpow, ← recursive_matrixPower_eq_matrix_pow] at hk
  have hent : ∀ a, Formalism.REAL.epow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k a a
      = ∑ c, ∑ d, (P c a * P⁻¹ a d) • Formalism.REAL.epow E k c d := by
    intro a
    have := congrFun (congrFun hk a) a
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply] at this
    exact this
  unfold Formalism.REAL.etr
  simp only [hent]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, h1, Matrix.one_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.hasSignature_fst_unique_sylvester : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ}, Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' := by
  first | exact @GlobalTheory.SylvesterInertia.hasSignature_fst_unique | exact GlobalTheory.SylvesterInertia.hasSignature_fst_unique | (intros; apply GlobalTheory.SylvesterInertia.hasSignature_fst_unique <;> assumption)
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem quadAlg_isField_or_split {K A : Type} [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
    (h2 : (2 : K) ≠ 0) (τ : A →+* A) (hτ : ∀ k, τ (algebraMap K A k) = algebraMap K A k)
    (δ : A) (d : K) (hd : d ≠ 0) (hδ : δ * δ = algebraMap K A d) (hs : τ δ = -δ)
    (hsp : ∀ x : A, ∃ a b : K, x = algebraMap K A a + algebraMap K A b * δ) :
    IsField A ∨ ∃ φ : A ≃+* K × K, ∀ x, φ (τ x) = (φ x).swap := by
  by_cases hsq : ∃ s : K, d = s * s
  · right
    obtain ⟨s, rfl⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hd (by simp [h])
    set e : A := algebraMap K A (2⁻¹) + algebraMap K A (2⁻¹ * s⁻¹) * δ with he
    have h1 : algebraMap K A (2⁻¹) * 2 = 1 := by
      rw [show (2 : A) = algebraMap K A 2 from (map_ofNat _ 2).symm, ← map_mul,
        inv_mul_cancel₀ h2, map_one]
    have h3 : algebraMap K A (s⁻¹) * algebraMap K A s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs0, map_one]
    rw [map_mul] at hδ he
    have hee : e * e = e := by
      rw [he]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (p + p * q * δ) * h1 + p ^ 2 * q ^ 2 * hδ + p ^ 2 * (q * t + 1) * h3
    have hτe : τ e = 1 - e := by
      rw [he]
      simp only [map_add (f := _), map_mul, hτ, hs]
      linear_combination h1
    have hτe' : τ (1 - e) = e := by
      rw [map_sub, map_one, hτe]; ring
    have hδe : δ = algebraMap K A s * e + algebraMap K A (-s) * (1 - e) := by
      rw [he, map_neg]
      generalize algebraMap K A (2⁻¹) = p at *
      generalize algebraMap K A (s⁻¹) = q at *
      generalize algebraMap K A s = t at *
      linear_combination (-t - t * q * δ) * h1 - δ * h3
    have he0 : e ≠ 0 := by
      intro h
      rw [h] at hτe
      simp at hτe
    have he1 : 1 - e ≠ 0 := by
      intro h
      rw [h, map_zero] at hτe'
      exact he0 hτe'.symm
    let ψ : K × K →+* A :=
      { toFun := fun x => algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e)
        map_one' := by simp
        map_zero' := by simp
        map_add' := by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring
        map_mul' := by
          intro x y
          simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
          generalize algebraMap K A x.1 = a
          generalize algebraMap K A x.2 = b
          generalize algebraMap K A y.1 = c
          generalize algebraMap K A y.2 = f
          linear_combination (-(a - b) * (c - f)) * hee }
    have hψ : ∀ x, ψ x = algebraMap K A x.1 * e + algebraMap K A x.2 * (1 - e) := fun _ => rfl
    have hinj : Function.Injective ψ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      rw [hψ] at hx
      have ha : algebraMap K A x.1 * e = 0 := by
        linear_combination e * hx - (algebraMap K A x.1 - algebraMap K A x.2) * hee
      have hb : algebraMap K A x.2 * (1 - e) = 0 := by
        linear_combination hx - ha
      rw [← Algebra.smul_def, smul_eq_zero] at ha hb
      exact Prod.ext (ha.resolve_right he0) (hb.resolve_right he1)
    have hsurj : Function.Surjective ψ := by
      intro x
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨(a + b * s, a - b * s), ?_⟩
      rw [hψ]
      simp only [map_add (f := _), map_sub, map_mul]
      rw [map_neg] at hδe
      linear_combination (-algebraMap K A b) * hδe
    refine ⟨(RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩).surjective x
    rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq]
    change τ (ψ y) = ψ y.swap
    simp only [hψ, map_add (f := _), map_mul, hτ, hτe, hτe', Prod.fst_swap,
      Prod.snd_swap]
    ring
  · left
    refine ⟨exists_pair_ne A, mul_comm, fun {x} hx => ?_⟩
    obtain ⟨a, b, rfl⟩ := hsp x
    have hn : a * a - d * (b * b) ≠ 0 := by
      intro h
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using h
        subst this
        simp at hx
      · refine hsq ⟨a / b, ?_⟩
        field_simp
        linear_combination -h
    refine ⟨(algebraMap K A a - algebraMap K A b * δ) * algebraMap K A (a * a - d * (b * b))⁻¹, ?_⟩
    have h4 : algebraMap K A (a * a - d * (b * b)) * algebraMap K A (a * a - d * (b * b))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn, map_one]
    generalize algebraMap K A (a * a - d * (b * b))⁻¹ = u at *
    simp only [map_sub, map_mul] at h4
    linear_combination h4 - (algebraMap K A b) ^ 2 * u * hδ

theorem quadExt_exists_skew {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ a, σ (σ a) = a) (hne : ∃ a, σ a ≠ a) :
    ∃ (δ : E) (d : F), d ≠ 0 ∧ δ * δ = algebraMap F E d ∧ σ δ = -δ ∧
      ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
  obtain ⟨t, ht⟩ := hne
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  set δ := t - σ t with hδ
  have hδ0 : δ ≠ 0 := fun h => ht (sub_eq_zero.mp h).symm
  have hs : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h' := congrArg σ h
    rw [map_add (f := _), Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, hs,
      map_one, map_zero, ← Algebra.smul_def, ← Algebra.smul_def, smul_neg] at h'
    have ha : (2 * a) • (1 : E) = 0 := by
      rw [two_mul, add_smul]; linear_combination h + h'
    have hb : (2 * b) • δ = 0 := by
      rw [two_mul, add_smul]; linear_combination h - h'
    rw [smul_eq_zero] at ha hb
    exact ⟨by simpa using ha, by simpa [hδ0] using hb⟩
  have hsp : ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
    intro x
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    have h := B.sum_repr x
    rw [Fin.sum_univ_two] at h
    have h0 : B 0 = 1 := by simp [B]
    have h1 : B 1 = δ := by simp [B]
    rw [h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
    exact h.symm
  obtain ⟨a, b, hab⟩ := hsp (δ * δ)
  have h' := congrArg σ hab
  simp only [map_add (f := _), map_mul, hs, AlgHom.commutes] at h'
  have hd : δ * δ = algebraMap F E a := by
    have h2 : (2 : E) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2
    linear_combination hab + h'
  refine ⟨δ, a, ?_, hd, hs, hsp⟩
  rintro rfl
  simp [hδ0] at hd

theorem quadBaseChange_isField_or_split :
    ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field K] [Algebra F K] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ a, σ (σ a) = a) → (∃ a, σ a ≠ a) → (IsField (K ⊗[F] E) ∨ ∃ φ : K ⊗[F] E ≃+* K × K, ∀ x, φ (sigR K σ x) = (φ x).swap) ∧ ∃ (δ : K ⊗[F] E) (d : K), d ≠ 0 ∧ δ * δ = algebraMap K (K ⊗[F] E) d ∧ sigR K σ δ = -δ ∧ ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a + algebraMap K (K ⊗[F] E) b * δ := by
  intro F E K _ _ _ _ _ _ σ hr hσ hne
  obtain ⟨δ, d, hd, hδ, hs, hsp⟩ := quadExt_exists_skew σ hr hσ hne
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hd' : algebraMap F K d ≠ 0 := by simpa using hd
  have hδ' : ((1 : K) ⊗ₜ[F] δ) * ((1 : K) ⊗ₜ[F] δ) =
      algebraMap K (K ⊗[F] E) (algebraMap F K d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, one_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply']
  have hsig : ∀ (k : K) (x : E), sigR K σ (k ⊗ₜ[F] x) = k ⊗ₜ[F] σ x := fun k x => by
    simp [sigR]
  have hs' : sigR K σ ((1 : K) ⊗ₜ[F] δ) = -((1 : K) ⊗ₜ[F] δ) := by
    rw [hsig, hs, TensorProduct.tmul_neg]
  have hsp' : ∀ x : K ⊗[F] E, ∃ a b : K, x = algebraMap K (K ⊗[F] E) a +
      algebraMap K (K ⊗[F] E) b * ((1 : K) ⊗ₜ[F] δ) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul k x =>
      obtain ⟨a, b, rfl⟩ := hsp x
      refine ⟨a • k, b • k, ?_⟩
      rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, TensorProduct.tmul_smul]
      simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, e, rfl⟩ := hy
      exact ⟨a + c, b + e, by simp only [map_add (f := _)]; ring⟩
  refine ⟨quadAlg_isField_or_split two_ne_zero (sigR K σ) (fun k => ?_) _ _ hd' hδ' hs' hsp',
    _, _, hd', hδ', hs', hsp'⟩
  rw [Algebra.TensorProduct.algebraMap_apply, hsig, map_one]

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Gen

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {κ : Type} [Fintype κ] [DecidableEq κ]

def mulVecCE (M : Matrix κ κ S) (hM : IsUnit M.det) : (κ → S) ≃ₜ+ (κ → S) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by simp [mulVec_mulVec, nonsing_inv_mul M hM]
  right_inv x := by simp [mulVec_mulVec, mul_nonsing_inv M hM]
  map_add' x y := mulVec_add M x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem mulVecCE_apply (M : Matrix κ κ S) (hM : IsUnit M.det) (x : κ → S) : mulVecCE M hM x = M *ᵥ x := rfl

end Gen

def prodCE {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) : (G₁ × G₂) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodCongr e₁.toAddEquiv e₂.toAddEquiv with
    continuous_toFun := e₁.continuous.prodMap e₂.continuous
    continuous_invFun := e₁.symm.continuous.prodMap e₂.symm.continuous }

theorem prodCE_apply {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂]
    [TopologicalSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) (x : G₁ × G₂) : prodCE e₁ e₂ x = (e₁ x.1, e₂ x.2) := rfl

def lrCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) : Matrix (Fin m) (Fin n) R ≃ₜ+ Matrix (Fin m) (Fin n) R where
  toFun u := (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R)
  invFun u := ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * u * ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  left_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  right_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  map_add' u v := by rw [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem lrCE_apply {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) (u : Matrix (Fin m) (Fin n) R) :
    lrCE g a u = (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R) := rfl

def zipHom (κ X Y : Type) [AddCommGroup X] [AddCommGroup Y] : (κ → X) × (κ → Y) →+ (κ → X × Y) where
  toFun p i := (p.1 i, p.2 i)
  map_zero' := rfl
  map_add' _ _ := rfl

section Places

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SPart : Type := ∀ v : S, Fv F v.1

abbrev OPart : Type := ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, v.1.adicCompletionIntegers F


open Classical in
def jS : SPart F S × OPart F S →+* Af F where
  toFun p := ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v),
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (by simp only [dif_neg (show v ∉ S from h)]; exact (p.2 ⟨v, h⟩).2))⟩
  map_one' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 1
    split_ifs <;> rfl)
  map_mul' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ * dite (v ∈ S) _ _
    split_ifs <;> rfl)
  map_zero' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 0
    split_ifs <;> rfl)
  map_add' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ + dite (v ∈ S) _ _
    split_ifs <;> rfl)

open Classical in
theorem evalV_jS (p : SPart F S × OPart F S) (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (jS F S p) = if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v) := rfl

end Places

end GlobalTheory.ModuLR
end
end

section


theorem _root_.GlobalTheory.T.matrix_conj_transpose_by_symmetric_taussky_zassenhaus : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k), ∃ P : Matrix ι ι k, IsUnit P ∧ P.transpose = P ∧ P * A = A.transpose * P := by
  first | exact @GlobalTheory.SymmetricSimilarTranspose.main | exact GlobalTheory.SymmetricSimilarTranspose.main | (intros; apply GlobalTheory.SymmetricSimilarTranspose.main <;> assumption)
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam : ∀ (l : Type) [Fintype l] [DecidableEq l] (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ), Continuous g → g 0 = 1 →
    (∀ s t, g (s + t) = g s * g t) → (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ t : ℝ, g t = NormedSpace.exp (t • Z) := by
  first | exact @GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp | exact GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp | (intros; apply GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp <;> assumption)
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  first | exact @GlobalTheory.hasSum_pi_prod_of_summable_norm | exact GlobalTheory.hasSum_pi_prod_of_summable_norm | (intros; apply GlobalTheory.hasSum_pi_prod_of_summable_norm <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add : ∀ (lam : ℝ → ℂ), lam 0 = 1 → (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  first | exact @GlobalTheory.multiplicative_hasDerivAt_zero | exact GlobalTheory.multiplicative_hasDerivAt_zero | (intros; apply GlobalTheory.multiplicative_hasDerivAt_zero <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W),
    (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) → A 0 = LinearMap.id →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  first | exact @GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | exact GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_toCLM_of_continuous_oneParameter <;> assumption)
end
