module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

section LocalHom

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Type*} [CommGroup A]
  {ρ : ℝ} {e₀ : V → A}

theorem localHom_nsmul (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) (k : ℕ) (hk : (k : ℝ) * ‖z‖ < ρ) : e₀ ((k : ℝ) • z) = e₀ z ^ k := by
  induction k with
  | zero =>
    have h0 := h 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    simp only [add_zero] at h0
    simpa using h0
  | succ k ih =>
    have hz := norm_nonneg z
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast at hk ⊢
    have h1 : (k : ℝ) * ‖z‖ < ρ := by nlinarith
    have h2 : ‖z‖ < ρ := by nlinarith
    have h3 : ‖(k : ℝ) • z‖ < ρ := by rwa [norm_smul, Real.norm_of_nonneg hk0]
    have h4 : ‖(k : ℝ) • z + z‖ < ρ := by
      have : (k : ℝ) • z + z = ((k : ℝ) + 1) • z := by rw [add_smul, one_smul]
      rwa [this, norm_smul, Real.norm_of_nonneg (by positivity)]
    rw [add_smul, one_smul, h _ _ h3 h2 h4, ih h1, pow_succ]

theorem localHom_norm_inv_smul_lt (z : V) {N : ℕ} (hN : 0 < N) (hz : ‖z‖ < N * ρ) :
    ‖(N : ℝ)⁻¹ • z‖ < ρ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_lt_iff₀ hN']
  exact hz

theorem localHom_pow_mul (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hz : ‖z‖ < N * ρ) :
    e₀ ((N : ℝ)⁻¹ • z) ^ N = e₀ (((N : ℝ) * M)⁻¹ • z) ^ (N * M) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e1 : (N : ℝ)⁻¹ • z = (M : ℝ) • (((N : ℝ) * M)⁻¹ • z) := by
    rw [smul_smul]; congr 1; field_simp
  have hb := localHom_norm_inv_smul_lt z hN hz
  have hk : (M : ℝ) * ‖((N : ℝ) * M)⁻¹ • z‖ < ρ := by
    rwa [e1, norm_smul, Real.norm_of_nonneg hM'.le] at hb
  rw [e1, localHom_nsmul hρ h _ M hk, ← pow_mul, mul_comm M N]

theorem localHom_pow_indep (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hzN : ‖z‖ < N * ρ) (hzM : ‖z‖ < M * ρ) :
    e₀ ((N : ℝ)⁻¹ • z) ^ N = e₀ ((M : ℝ)⁻¹ • z) ^ M := by
  rw [localHom_pow_mul hρ h z hN hM hzN, localHom_pow_mul hρ h z hM hN hzM, mul_comm N M,
    mul_comm (N : ℝ) M]

theorem localHom_exists_nat (hρ : 0 < ρ) (r : ℝ) : ∃ N : ℕ, 0 < N ∧ r < N * ρ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (r / ρ)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [div_lt_iff₀ hρ] at hn
  push_cast
  nlinarith

theorem localHom_existsUnique_extension (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w) :
    ∃! e : V → A, (∀ z w, e (z + w) = e z * e w) ∧ ∀ z, ‖z‖ < ρ → e z = e₀ z := by
  choose N hN hNz using fun z : V => localHom_exists_nat hρ ‖z‖
  refine ⟨fun z => e₀ ((N z : ℝ)⁻¹ • z) ^ N z, ⟨fun z w => ?_, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨M, hM, hMz⟩ := localHom_exists_nat hρ (‖z‖ + ‖w‖)
    have hz : ‖z‖ < M * ρ := by linarith [norm_nonneg w]
    have hw : ‖w‖ < M * ρ := by linarith [norm_nonneg z]
    have hzw : ‖z + w‖ < M * ρ := (norm_add_le z w).trans_lt hMz
    have hb := localHom_norm_inv_smul_lt _ hM hzw
    rw [smul_add] at hb
    simp only
    rw [localHom_pow_indep hρ h z (hN z) hM (hNz z) hz,
      localHom_pow_indep hρ h w (hN w) hM (hNz w) hw,
      localHom_pow_indep hρ h (z + w) (hN _) hM (hNz _) hzw, smul_add,
      h _ _ (localHom_norm_inv_smul_lt z hM hz) (localHom_norm_inv_smul_lt w hM hw) hb, mul_pow]
  · simp only
    rw [localHom_pow_indep hρ h z (hN z) one_pos (hNz z) (by simpa using hz)]
    simp
  · rintro e ⟨he, he₀⟩
    funext z
    have hN' : (0 : ℝ) < N z := by exact_mod_cast hN z
    have hb := localHom_norm_inv_smul_lt z (hN z) (hNz z)
    have key := localHom_nsmul (ρ := ‖z‖ + 1) (e₀ := e) (by positivity)
      (fun a b _ _ _ => he a b) ((N z : ℝ)⁻¹ • z) (N z) (by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_inv_cancel_left₀ hN'.ne']
        linarith)
    rw [smul_inv_smul₀ hN'.ne', he₀ _ hb] at key
    exact key

end LocalHom

theorem existsUnique_extension_of_ball :
    ∀ (g : ℕ) (A : Type) [CommGroup A] (ρ : ℝ), 0 < ρ → ∀ e₀ : (Fin g → ℂ) → A,
      (∀ z ∈ ball (0 : Fin g → ℂ) ρ, ∀ w ∈ ball (0 : Fin g → ℂ) ρ,
        z + w ∈ ball (0 : Fin g → ℂ) ρ → e₀ (z + w) = e₀ z * e₀ w) →
      ∃! e : (Fin g → ℂ) → A, (∀ z w, e (z + w) = e z * e w) ∧
        ∀ z ∈ ball (0 : Fin g → ℂ) ρ, e z = e₀ z := by
  intro g A _ ρ hρ e₀ h
  simp only [mem_ball_zero_iff] at h ⊢
  exact localHom_existsUnique_extension hρ fun z w hz hw hzw => h z hz w hw hzw

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_max_ratio_cleared :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ι → ℤ) (m : ι → ℕ), (∀ i, 0 < m i) →
      ∃ (M : ℕ) (a : ℤ) (i₀ : ι), 0 < M ∧ (∀ i, (M : ℤ) * n i ≤ a * m i) ∧
        (M : ℤ) * n i₀ = a * m i₀ := by
  intro ι _ _ n m hm
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => (n i : ℚ) / m i) Finset.univ_nonempty
  refine ⟨m i₀, n i₀, i₀, hm i₀, fun i => ?_, mul_comm _ _⟩
  have h := hi₀ i (Finset.mem_univ i)
  have hmi : (0 : ℚ) < m i := by exact_mod_cast hm i
  have hm0 : (0 : ℚ) < m i₀ := by exact_mod_cast hm i₀
  rw [div_le_div_iff₀ hmi hm0] at h
  have hq : (m i₀ : ℚ) * n i ≤ n i₀ * (m i : ℚ) := by linarith
  exact_mod_cast hq

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix

theorem det_fromCols_frame_change : ∀ (R : Type) [CommRing R] (p q : ℕ) (J J₂ : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S S₂ : Matrix (Fin q) (Fin p ⊕ Fin q) R) (T T₂ : Matrix (Fin p ⊕ Fin q) (Fin q) R) (A : Matrix (Fin p) (Fin p) R) (B : Matrix (Fin q) (Fin q) R), S * J = 0 → S * T = 1 → IsUnit (Matrix.fromCols J T).det → S₂ * T₂ = 1 → J₂ = J * A → S = B * S₂ → (Matrix.fromCols J₂ T₂).det = (Matrix.fromCols J T).det * A.det * B.det := by
  intro R _ p q J J₂ S S₂ T T₂ A B hSJ hST hU hST₂ hJ hS
  set W : Matrix (Fin p ⊕ Fin q) (Fin q) R := (Matrix.fromCols J T)⁻¹ * T₂ with hW
  have h1 : Matrix.fromCols J T * W = T₂ := by
    rw [hW, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have h2 : J * W.toRows₁ + T * W.toRows₂ = T₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromRows_toRows, h1]
  have h3 : W.toRows₂ = B := by
    have h := congrArg (fun X => S * X) h2
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hSJ, hST, Matrix.zero_mul, Matrix.one_mul,
      zero_add] at h
    rw [h, hS, Matrix.mul_assoc, hST₂, Matrix.mul_one]
  have h4 : Matrix.fromCols J₂ T₂ =
      Matrix.fromCols J T * Matrix.fromBlocks A W.toRows₁ 0 B := by
    rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, ← hJ, ← h3, h2]
  rw [h4, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fromRows_mul_fromCols_split {R : Type} [CommRing R] {p q : ℕ}
    (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R)
    (J' : Matrix (Fin p) (Fin p ⊕ Fin q) R) (S' : Matrix (Fin p ⊕ Fin q) (Fin q) R)
    (h0 : S * J = 0) (hJ : J' * J = 1) (hS : S * S' = 1) :
    Matrix.fromRows (J' * (1 - S' * S)) S * Matrix.fromCols J S' = 1 := by
  rw [Matrix.fromRows_mul_fromCols]
  have e1 : J' * (1 - S' * S) * J = 1 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      h0, Matrix.mul_zero, sub_zero, hJ]
  have e2 : J' * (1 - S' * S) * S' = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      hS, Matrix.mul_zero, sub_self]
  rw [e1, e2, h0, hS, Matrix.fromBlocks_one]

theorem splitExact_of_rank : ∀ (R : Type) [CommRing R] (p q : ℕ) (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R), S * J = 0 → (∃ J' : Matrix (Fin p) (Fin p ⊕ Fin q) R, J' * J = 1) → (∃ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1) → (∀ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1 → IsUnit (Matrix.fromCols J S').det) ∧ ∀ v, S.mulVec v = 0 ↔ ∃ w, J.mulVec w = v := by
  rintro R inst p q J S h0 ⟨J', hJ⟩ ⟨S₀, hS₀⟩
  refine ⟨fun S' hS => ?_, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact Matrix.isUnit_det_of_left_inverse (fromRows_mul_fromCols_split J S J' S' h0 hJ hS)
  · have hMN := fromRows_mul_fromCols_split J S J' S₀ h0 hJ hS₀
    have hNM : Matrix.fromCols J S₀ * Matrix.fromRows (J' * (1 - S₀ * S)) S = 1 := by
      first
      | exact mul_eq_one_comm.mp hMN
      | (rw [← Matrix.inv_eq_left_inv hMN]
         exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hMN))
    rw [Matrix.fromCols_mul_fromRows] at hNM
    refine ⟨(J' * (1 - S₀ * S)).mulVec v, ?_⟩
    calc J.mulVec ((J' * (1 - S₀ * S)).mulVec v)
        = J.mulVec ((J' * (1 - S₀ * S)).mulVec v) + S₀.mulVec (S.mulVec v) := by
          rw [hv, Matrix.mulVec_zero, add_zero]
      _ = (J * (J' * (1 - S₀ * S)) + S₀ * S).mulVec v := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = v := by rw [hNM, Matrix.one_mulVec]
  · rintro ⟨w, rfl⟩
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.QuotPrime

theorem exists_surjective_zmod_of_ne_top (X : Type*) [AddCommGroup X] [Module.Finite ℤ X]
    (Y : AddSubgroup X) (hY : Y ≠ ⊤) :
    ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ ∀ y ∈ Y, ψ y = 0 := by
  have hY' : Y.toIntSubmodule ≠ ⊤ := by
    intro h
    apply hY
    rw [eq_top_iff]
    intro x _
    have : x ∈ Y.toIntSubmodule := by rw [h]; trivial
    exact this
  obtain ⟨M, hM, hYM⟩ := (eq_top_or_exists_le_coatom Y.toIntSubmodule).resolve_left hY'
  have hs : IsSimpleModule ℤ (X ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, I = Ideal.span {p} := ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    have h : (⊥ : Ideal ℤ).IsMaximal := by simpa using hI
    exact Int.not_isField (Ring.isField_iff_maximal_bot.2 h)
  have hp : Prime p := (Ideal.span_singleton_prime hp0).1 hI.isPrime
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.1 hp,
    ((Int.quotientSpanEquivZMod p).toAddEquiv.toAddMonoidHom.comp
      e.toAddEquiv.toAddMonoidHom).comp M.mkQ.toAddMonoidHom, ?_, ?_⟩
  · exact ((Int.quotientSpanEquivZMod p).surjective.comp e.surjective).comp M.mkQ_surjective
  · intro y hy
    have h0 : M.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero M).2 (hYM hy)
    change (Int.quotientSpanEquivZMod p) (e (M.mkQ y)) = 0
    rw [h0, map_zero, map_zero]

theorem exists_surjective_zmod_of_ne_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Finite ℤ X] (Y : AddSubgroup X)
      (δ : X →+ k), δ ≠ 0 → (∀ y ∈ Y, δ y = 0) →
      ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ ∀ y ∈ Y, ψ y = 0 := by
  intro k X _ _ _ Y δ hδ hY
  refine exists_surjective_zmod_of_ne_top X Y ?_
  rintro rfl
  exact hδ (AddMonoidHom.ext fun x => hY x trivial)

end GlobalTheory.CompanionTheory.QuotPrime
end

section

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor

open Polynomial

theorem natDegree_minpoly_eq_of_closed {k F A : Type*} [Field k] [Field F] [Field A] [Algebra k F]
    [Algebra F A] [Algebra k A] [IsScalarTower k F A]
    (h : ∀ x : F, IsAlgebraic k x → x ∈ Set.range (algebraMap k F))
    {θ : A} (hθ : IsIntegral k θ) : (minpoly F θ).natDegree = (minpoly k θ).natDegree := by
  have hF : IsIntegral F θ := hθ.tower_top
  have hd : minpoly F θ ∣ (minpoly k θ).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F θ
  have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F (minpoly.monic hθ)
    (minpoly.monic hF) hd
  have h2 : minpoly F θ ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨y, hy⟩ := h1 n
    rw [← hy]
    exact h _ (IsIntegral.isAlgebraic y.2)
  obtain ⟨q, hq, hdeg, hm⟩ := lifts_and_natDegree_eq_and_monic h2 (minpoly.monic hF)
  apply le_antisymm
  · have := natDegree_le_of_dvd hd ((minpoly.monic hθ).map _).ne_zero
    rwa [natDegree_map] at this
  · rw [← hdeg]
    refine natDegree_le_of_dvd (minpoly.dvd k θ ?_) hm.ne_zero
    rw [← aeval_map_algebraMap F, hq, minpoly.aeval]

end GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem symplectic_unipotent_shape : ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ), (∀ x, B x x = 0) → (∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 ∧ B (bas (.inr i)) (bas (.inr j)) = 0 ∧ B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0) → ∀ T : Λ →ₗ[ℤ] Λ, (∀ x y, B (T x) (T y) = B x y) → (∀ i, T (bas (.inl i)) = bas (.inl i)) → ∃ N : Matrix (Fin g) (Fin g) ℤ, Nᵀ = N ∧ ∀ j, T (bas (.inr j)) = bas (.inr j) + ∑ k, N j k • bas (.inl k) := by
  intro g Λ _ B bas halt hB T hT hTa
  have hB1 : ∀ i j, B (bas (.inl i)) (bas (.inl j)) = 0 := fun i j => (hB i j).1
  have hB2 : ∀ i j, B (bas (.inr i)) (bas (.inr j)) = 0 := fun i j => (hB i j).2.1
  have hB3 : ∀ i j, B (bas (.inl i)) (bas (.inr j)) = if i = j then 1 else 0 :=
    fun i j => (hB i j).2.2
  have skew : ∀ x y, B x y = -B y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
    linarith
  have hexp : ∀ v : Λ, v = ∑ k, bas.repr v (.inl k) • bas (.inl k) +
      ∑ k, bas.repr v (.inr k) • bas (.inr k) := by
    intro v
    conv_lhs => rw [← bas.sum_repr v]
    rw [Fintype.sum_sum_type]
  have pa : ∀ i v, B (bas (.inl i)) v = bas.repr v (.inr i) := by
    intro i v
    conv_lhs => rw [hexp v]
    simp [hB1, hB3]
  have pb : ∀ i v, B (bas (.inr i)) v = -bas.repr v (.inl i) := by
    intro i v
    have hba : ∀ k, B (bas (.inr i)) (bas (.inl k)) = -(if k = i then 1 else 0) :=
      fun k => by rw [skew, hB3]
    conv_lhs => rw [hexp v]
    simp [hba, hB2]
  have hd : ∀ i j, bas.repr (T (bas (.inr j))) (.inr i) = if i = j then 1 else 0 := by
    intro i j
    rw [← pa, ← hTa i, hT, hB3]
  have hTb : ∀ j, T (bas (.inr j)) =
      bas (.inr j) + ∑ k, bas.repr (T (bas (.inr j))) (.inl k) • bas (.inl k) := by
    intro j
    conv_lhs => rw [hexp (T (bas (.inr j)))]
    rw [add_comm]
    congr 1
    simp [hd, ite_smul]
  refine ⟨fun j k => bas.repr (T (bas (.inr j))) (.inl k), ?_, hTb⟩
  ext i j
  show bas.repr (T (bas (.inr j))) (.inl i) = bas.repr (T (bas (.inr i))) (.inl j)
  have h0 : B (T (bas (.inr j))) (T (bas (.inr i))) = 0 := by rw [hT, hB2]
  rw [hTb j, map_add (f := _), LinearMap.add_apply, pb j] at h0

  simp [map_sum, LinearMap.sum_apply, pa, hd] at h0
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.UnimodularBaseChange

theorem bijective_baseChange :
    ∀ (Z : Type) [CommRing Z] (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
      (B : LinearMap.BilinForm ℤ L), Function.Bijective B →
      Function.Bijective (B.baseChange Z) := by
  intro Z _ L _ _ _ B hB
  classical
  let b := Module.Free.chooseBasis ℤ L
  let c := b.baseChange Z
  have h1 : IsUnit (LinearMap.toMatrix b b.dualBasis B).det :=
    LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have h2 : LinearMap.toMatrix c c.dualBasis (B.baseChange Z) =
      (algebraMap ℤ Z).mapMatrix (LinearMap.toMatrix b b.dualBasis B) := by
    ext i j
    simp [c, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  have h3 : IsUnit (LinearMap.toMatrix c c.dualBasis (B.baseChange Z)).det := by
    rw [h2, ← RingHom.map_det]
    exact h1.map _
  exact (LinearEquiv.ofIsUnitDet h3).bijective

end GlobalTheory.CompanionTheory.UnimodularBaseChange
end

section

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

def FiniteFreeHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Prop :=
  letI := φ.toAlgebra
  Module.Free A B ∧ Module.Finite A B

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

section

open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem normal_noeth_local_dim_one_isDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ringKrullDim R = 1 → IsDiscreteValuationRing R := by
  intro R _ _ _ _ _ h1
  have hnf : ¬ IsField R := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp h1).1
  have hdim : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [h1])
  have h4 : IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨inferInstance, IsLocalRing.maximalIdeal R,
      ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩, ?_⟩
    rintro P ⟨hP, hPp⟩
    exact IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim P hP hPp)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 4).mpr h4

end GlobalTheory.CompanionTheory.Ar.Flat
end
