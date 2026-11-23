module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Support
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle073
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle074
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplectic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle076
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.FieldTheory.Galois.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle075
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.SupportBC

theorem mem_support_quotient_span_iff_of_isPushout :
    ∀ (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R') (ga : S ⟶ S') (qa' : R' ⟶ S'),
      IsPushout qa ba ga qa' → qa.hom.Finite → ∀ {ι : Type} (s : ι → S) (p : PrimeSpectrum R'),
      ((letI := qa'.hom.toAlgebra;
        p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra;
        PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)))) := by
  first
  | exact @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff
  | (apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientSupportBaseChange.mem_support_quotient_iff ..)

end GlobalTheory.SupportBC
end

section


theorem _root_.GlobalTheory.T.prod_four_maps_lam_pow_eq_one : ∀ (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ) (lam : Fin r → Fin r → U), (∀ k l, lam k l = lam l k) → W = (W + W.transpose) * A → ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k * (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  first | exact @GlobalTheory.SymmProd.prod_four_maps_eq_one | exact GlobalTheory.SymmProd.prod_four_maps_eq_one | (intros; apply GlobalTheory.SymmProd.prod_four_maps_eq_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mapDomain_relation_lift_commuting_square : ∀ (M : Type 1) [AddCommGroup M] (X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Type) (c : X₂ → X₄) (d : X₃ → X₄) (u : Y₁ → Y₂) (v : Y₁ → Y₃) (c' : Y₂ → Y₄) (d' : Y₃ → Y₄) (r₂ : X₂ → Y₂) (r₃ : X₃ → Y₃) (r₄ : X₄ → Y₄) (G : Y₄ → Prop), (∀ x, c' (r₂ x) = r₄ (c x)) → (∀ y, d' (r₃ y) = r₄ (d y)) → (∀ x, c' (u x) = d' (v x)) → Function.Injective c' → (∀ x, G (c' x)) → (∀ y, G (d' y) → ∃ x, v x = y) → ∀ (a₂ : X₂ →₀ M) (a₃ : X₃ →₀ M), Finsupp.mapDomain c a₂ + Finsupp.mapDomain d a₃ = 0 → (∀ y ∈ a₃.support, ∀ y' ∈ a₃.support, d y = d y' → r₃ y = r₃ y' ∨ G (d' (r₃ y))) → ∃ a : Y₁ →₀ M, Finsupp.mapDomain u a = Finsupp.mapDomain r₂ a₂ ∧ Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
  first | (exact @GlobalTheory.mapDomain_corner_lift) | (exact GlobalTheory.mapDomain_corner_lift) | (intros; apply GlobalTheory.mapDomain_corner_lift  <;> assumption)
end

section

open scoped TensorProduct
open Function

theorem _root_.GlobalTheory.T.algEquiv_matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.matrix_glue_crt) | (exact GlobalTheory.matrix_glue_crt) | (intros; apply GlobalTheory.matrix_glue_crt  <;> assumption)
end

section

noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def quat (d : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Classical.choose (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))

theorem quat_transpose_mul (d : ℕ) :
    (quat d)ᵀ * quat d = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).1

theorem quat_mul_transpose (d : ℕ) :
    quat d * (quat d)ᵀ = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).2

def form (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks 1 (quat d)ᵀ (quat d) ((d : ℤ) • 1)

def formInv (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks ((d : ℤ) • 1) (-(quat d)ᵀ) (-(quat d)) 1

theorem form_transpose (d : ℕ) : (form d)ᵀ = form d := by
  simp [form, fromBlocks_transpose]

theorem form_mul_formInv {d : ℕ} (hd : 0 < d) : form d * formInv d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [form, formInv, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [Matrix.mul_neg, quat_transpose_mul, h1]; simp [sub_smul]
  · simp
  · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_neg, smul_neg, add_neg_cancel]
  · rw [Matrix.mul_neg, quat_mul_transpose, h1]; simp [sub_smul]

theorem formInv_mul_form {d : ℕ} (hd : 0 < d) : formInv d * form d = 1 :=
  mul_eq_one_comm.mp (form_mul_formInv hd)

def ord (d : ℕ) : Subring (Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) where
  carrier := {N | ∀ i j, (d : ℤ) ∣ N (Sum.inr i) (Sum.inl j)}
  mul_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    exact dvd_add (Finset.dvd_sum fun k _ => (hN i k).mul_right _)
      (Finset.dvd_sum fun k _ => (hN' k j).mul_left _)
  one_mem' i j := by simp
  add_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    exact dvd_add (hN i j) (hN' i j)
  zero_mem' i j := by simp
  neg_mem' {N} hN i j := by
    simp only [Set.mem_setOf_eq] at hN
    simpa using hN i j

theorem form_mul_transpose_mul_formInv_mem {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ}
    (hN : N ∈ ord d) : form d * Nᵀ * formInv d ∈ ord d := by
  intro i j
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : ∀ i j, ((N (Sum.inr i) (Sum.inl j) : ℤ) : ZMod d) = 0 := fun i j =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hN i j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, form, formInv, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Int.cast_add, Int.cast_sum, Int.cast_mul,
    Matrix.smul_apply, Matrix.neg_apply, Int.cast_neg, smul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    mul_zero, key, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul]
  simp

def barM (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  form d * Nᵀ * formInv d

def bar (d : ℕ) (N : ord d) : ord d := ⟨barM d N, form_mul_transpose_mul_formInv_mem N.2⟩

@[simp] theorem bar_coe (d : ℕ) (N : ord d) :
    ((bar d N : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ)ᵀ * formInv d :=
  rfl

theorem bar_add (d : ℕ) (a b : ord d) : bar d (a + b) = bar d a + bar d b := by
  ext1
  simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem formInv_transpose (d : ℕ) : (formInv d)ᵀ = formInv d := by
  simp [formInv, fromBlocks_transpose]

theorem bar_bar {d : ℕ} (hd : 0 < d) (a : ord d) : bar d (bar d a) = a := by
  ext1
  simp only [bar_coe, Matrix.transpose_mul, Matrix.transpose_transpose, form_transpose, formInv_transpose]
  calc form d * (formInv d * ((a : Matrix _ _ ℤ) * form d)) * formInv d
      = (form d * formInv d) * (a : Matrix _ _ ℤ) * (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = (a : Matrix _ _ ℤ) := by rw [form_mul_formInv hd, Matrix.one_mul, Matrix.mul_one]

def idem (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inl 0) 1, fun i j => by simp [single]⟩

theorem idem_mul_self (d : ℕ) : idem d * idem d = idem d := by
  ext1
  simp [idem]

end GlobalTheory.ZarhinFam
end
end

section

open Matrix

theorem _root_.GlobalTheory.T.lu_decomposition_unitriangular_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (A₁ A₂ N₁ U N₀ : Matrix (Fin m) (Fin m) R), (∀ i j, i < j → A₁ i j = 0) → (∀ i j, i < j → A₂ i j = 0) → (∀ i j, j < i → N₁ i j = 0) → (∀ i, N₁ i i = 1) → (∀ i j, j < i → U i j = 0) → (∀ i, U i i = 1) → (∀ i j, j < i → N₀ i j = 0) → (∀ i, N₀ i i = 1) → A₁ * A₂ * N₁ = U * N₀ → N₁ = U * N₀ := by
  first | exact @GlobalTheory.lu_unique | exact GlobalTheory.lu_unique | (intros; apply GlobalTheory.lu_unique <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M) (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O), P * P' = 1 → P' * P = 1 → (∀ i j, P (Sum.inl i) (Sum.inr j) = 0) → ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  first | exact @GlobalTheory.exists_basis_of_blockLowerTriangular_inv | exact GlobalTheory.exists_basis_of_blockLowerTriangular_inv | (intros; apply GlobalTheory.exists_basis_of_blockLowerTriangular_inv <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_compatible_symplectic_alt : ∀ (F : Type) [Field F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ (g : ℕ) (G : ℕ → Type) [∀ n, AddCommGroup (G n)] (e : ∀ n, G n → G n → Fˣ) (π : ∀ M n, G M →+ G n), (∀ n, 0 < n → Nonempty (G n ≃+ (Fin (2 * g) → ZMod n))) → (∀ n x y z, e n (x + y) z = e n x z * e n y z) → (∀ n x y z, e n x (y + z) = e n x y * e n x z) → (∀ n x, e n x x = 1) → (∀ n, 0 < n → ∀ x, (∀ y, e n x y = 1) → x = 0) → (∀ n m, 0 < n → 0 < m → ∀ x y, e n (π (n * m) n x) (π (n * m) n y) = e (n * m) x y ^ m) → (∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x, π n k (π M n x) = π M k x) → ∃ ev : ∀ n, ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, (∀ n, 0 < n → ∀ a b, ev n a = ev n b ↔ ∃ e', a = b + n • e') ∧ (∀ n, 0 < n → Function.Surjective (ev n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, π (n * m) n (ev (n * m) a) = ev n a) ∧ (∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) := by
  first | exact @GlobalTheory.SympTower.exists_compatible_symplectic | exact GlobalTheory.SympTower.exists_compatible_symplectic | (intros; apply GlobalTheory.SympTower.exists_compatible_symplectic <;> assumption)
end

section

open CategoryTheory Limits

theorem _root_.GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime], Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) * p ^ Module.finrank ℤ M := by
  first | exact @GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | exact GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank | (intros; apply GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank <;> assumption)
end

section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.involution_norm_class_remove_rational_factor : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E ≃ₐ[ℚ] E) (S : Finset ℕ) (A : Finset E),
    (∀ a : E, IsUnit a → τ a = a →
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
        ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
      ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e) →
    ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : Eˣ), a = algebraMap ℚ E (r : ℚ) * ((e : E) * a₀ * τ e) := by
  first | (exact @GlobalTheory.RatRed.ratred) | (exact GlobalTheory.RatRed.ratred) | (intros; apply GlobalTheory.RatRed.ratred  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.TensorTorsionNsmul

open scoped TensorProduct

variable {L : Type} [AddCommGroup L]

theorem tmul_surjective (n : ℕ) (x : ZMod n ⊗[ℤ] L) : ∃ a : L, (1 : ZMod n) ⊗ₜ[ℤ] a = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul r a =>
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨m • a, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

theorem eq_nsmul_of_tmul_eq_zero {n : ℕ} {a : L} (h : (1 : ZMod n) ⊗ₜ[ℤ] a = 0) : ∃ d, a = n • d := by
  let e : ZMod n ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    (Int.quotientSpanNatEquivZMod n).symm.toAddEquiv.toIntLinearEquiv
  have he : e 1 = 1 := map_one (Int.quotientSpanNatEquivZMod n).symm
  have h1 := congrArg (fun y => TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(n : ℤ)})
    (LinearMap.rTensor L e.toLinearMap y)) h
  simp only [LinearMap.rTensor_tmul, map_zero, LinearEquiv.coe_coe, he,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨d, -, hd⟩ := h1
  exact ⟨d, by rw [← hd, natCast_zsmul]⟩

theorem tmul_nsmul_eq_zero (n : ℕ) (d : L) : (1 : ZMod n) ⊗ₜ[ℤ] (n • d) = 0 := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, _root_.mul_one, ZMod.natCast_self,
    TensorProduct.zero_tmul]

variable {G : Type} [Group G]

theorem map_nsmul_of_add {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c) (m : ℕ) (a : L) :
    φ (m • a) = φ a ^ m := by
  have h0 : φ 0 = 1 := by
    have := hφ 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction m with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ m ih => rw [succ_nsmul, hφ, ih, pow_succ]

theorem tmul_eq_tmul_iff {n : ℕ} {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b) (a c : L) :
    (1 : ZMod n) ⊗ₜ[ℤ] a = 1 ⊗ₜ c ↔ φ a = φ c := by
  have e : φ a = φ (a - c) * φ c := by rw [← hφ, sub_add_cancel]
  rw [e, mul_eq_right, hk, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  constructor
  · exact eq_nsmul_of_tmul_eq_zero
  · rintro ⟨d, hd⟩
    rw [hd]
    exact tmul_nsmul_eq_zero n d

def matchMap (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) : (ZMod n ⊗[ℤ] L) →ₗ[ZMod n] (ZMod n ⊗[ℤ] L) :=
  LinearMap.liftBaseChange (ZMod n)
    (AddMonoidHom.mk' (fun b => (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b)) (fun b b' => by
      rw [← TensorProduct.tmul_add, tmul_eq_tmul_iff hφ hk, hφ, Classical.choose_spec (hr _),
        Classical.choose_spec (hr _), Classical.choose_spec (hr _), hφ']) : L →+ ZMod n ⊗[ℤ] L).toIntLinearMap

theorem matchMap_tmul (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) (b c : L) :
    matchMap n φ φ' hφ hφ' hk hr ((1 : ZMod n) ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  rw [matchMap, LinearMap.liftBaseChange_tmul, one_smul]
  change (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b) = _ ↔ _
  rw [tmul_eq_tmul_iff hφ hk, Classical.choose_spec (hr b), eq_comm]

theorem exists_equiv (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hk' : ∀ a, φ' a = 1 ↔ ∃ b, a = n • b) (hr : ∀ b, ∃ c, φ c = φ' b) (hr' : ∀ c, ∃ b, φ' b = φ c) :
    ∃ e : (ZMod n ⊗[ℤ] L) ≃ₗ[ZMod n] (ZMod n ⊗[ℤ] L), ∀ b c, e (1 ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  let f := matchMap n φ φ' hφ hφ' hk hr
  let g := matchMap n φ' φ hφ' hφ hk' hr'
  have hfg : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr b
    obtain ⟨d, hd⟩ := hr' c
    rw [(matchMap_tmul n φ φ' hφ hφ' hk hr b c).2 hc, (matchMap_tmul n φ' φ hφ' hφ hk' hr' c d).2 hd,
      tmul_eq_tmul_iff hφ' hk', hd, hc]
  have hgf : ∀ x, f (g x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr' b
    obtain ⟨d, hd⟩ := hr c
    rw [(matchMap_tmul n φ' φ hφ' hφ hk' hr' b c).2 hc, (matchMap_tmul n φ φ' hφ hφ' hk hr c d).2 hd,
      tmul_eq_tmul_iff hφ hk, hd, hc]
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hgf) (LinearMap.ext hfg), fun b c => ?_⟩
  exact matchMap_tmul n φ φ' hφ hφ' hk hr b c

end GlobalTheory.UPel.TensorTorsionNsmul

namespace GlobalTheory.UPel

open scoped TensorProduct

end GlobalTheory.UPel
end
end

section


theorem _root_.GlobalTheory.T.exists_finite_galois_fractionRing_fixing : ∀ (A K L : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra A L], (∀ a : A, algebraMap A L a = algebraMap K L (algebraMap A K a)) → ∃ (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L), FiniteDimensional (FractionRing A) L ∧ IsGalois (FractionRing A) L ∧ ∀ (σ : L ≃ₐ[FractionRing A] L) (x : K), σ (algebraMap K L x) = algebraMap K L x := by
  first | exact @GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | exact GlobalTheory.finiteGalois_fractionRing_of_isFractionRing | (intros; apply GlobalTheory.finiteGalois_fractionRing_of_isFractionRing <;> assumption)
end
