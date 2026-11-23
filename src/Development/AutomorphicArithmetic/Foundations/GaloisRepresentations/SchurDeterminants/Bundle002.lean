module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private lemma prod_scaleOff {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) :
    ∏ k, scaleOff y i g k = y ^ (n - 1) * ∏ k, g k := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ g (mem_univ i)]
  have h : ∏ k ∈ univ.erase i, scaleOff y i g k = ∏ k ∈ univ.erase i, (y * g k) :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleOff, (mem_erase.1 hk).1])
  rw [h, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]
  simp only [scaleOff, if_true]
  ring

theorem fibre_of : SchurY → SchurHomog → SchurDet → Fibre := by
  intro hY hH hD R ι _ _ _ _ n t₀ t₁ h01 ε lam m hm g y hu
  have hconst : ∀ h : Fin n → R, sch (lam t₁) h = (∏ k, h k) ^ m := by
    intro h
    have e := (hD R n h).2 (fun _ => 0) m
    simp only [zero_add, (hD R n h).1, mul_one] at e
    have hl : lam t₁ = fun _ => m := funext hm
    rw [hl, e]
  have h10 : t₁ ≠ t₀ := fun h => h01 h.symm
  have h1mem : t₁ ∈ univ.erase t₀ := mem_erase.mpr ⟨h10, mem_univ _⟩
  have hrest : ∀ i, ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
      y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
        ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t) := by
    intro i
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    apply prod_congr rfl
    intro t ht
    have ht1 : t ≠ t₁ := (mem_erase.mp ht).1
    have ht0 : t ≠ t₀ := (mem_erase.mp (mem_erase.mp ht).2).1
    simp only [twist, if_neg ht0, if_neg ht1]
    rw [hH R n (lam t) (g t) (y ^ ε t), ← pow_mul]
  have hi : ∀ i, ∏ t, sch (lam t) (twist t₀ t₁ ε y i g t) =
      sch (lam t₀) (scaleAt y i (g t₀)) *
        (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) := by
    intro i
    rw [← mul_prod_erase univ _ (mem_univ t₀), ← mul_prod_erase (univ.erase t₀) _ h1mem,
      ← mul_prod_erase (univ.erase t₀) (fun t => sch (lam t) (g t)) h1mem, hrest i]
    simp only [twist, eq_self_iff_true, ↓reduceIte, h10]
    rw [hconst, hconst, prod_scaleOff, mul_pow, ← pow_mul, pow_add]
    ring
  calc ∑ i, (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
        ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i)
      = (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) *
        ∑ i, sch (lam t₀) (scaleAt y i (g t₀)) *
          ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [hi i]
        ring
    _ = _ := by
        rw [hY R n (lam t₀) (g t₀) y hu, ← mul_prod_erase univ (fun t => sch (lam t) (g t)) (mem_univ t₀)]
        ring

end UpperTheory.Gal.Schur
end
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

private lemma vdm_X_ne (n : ℕ) : vdm (X : Fin n → MvPolynomial (Fin n) ℚ) ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  exact sub_ne_zero.2 (MvPolynomial.X_injective.ne (Finset.mem_Ioi.1 hj).ne)

private lemma aeval_sch {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (lam : Fin n → ℕ)
    (g : Fin n → R) :
    aeval g (sch lam (X : Fin n → MvPolynomial (Fin n) ℚ)) = sch lam g := by
  unfold sch
  rw [MvPolynomial.aeval_X_left_apply]

private lemma altn_zero {R : Type} [CommRing R] {n : ℕ} (g : Fin n → R) :
    altn (shift fun _ => 0) g = vdm g := by
  have h := GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_staircase_eq_vandermondeOf g
  have h' : vdm g = GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf g := rfl
  unfold altn
  rw [h']
  simpa [shift] using h

private lemma altn_add {R : Type} [CommRing R] {n : ℕ} (lam : Fin n → ℕ) (m : ℕ) (g : Fin n → R) :
    altn (shift fun i => lam i + m) g = (∏ k, g k) ^ m * altn (shift lam) g := by
  unfold altn
  have h : (Matrix.of fun i j : Fin n => g j ^ (shift (fun i => lam i + m)) i) =
      Matrix.of fun i j : Fin n =>
        g j ^ m * (Matrix.of fun i j : Fin n => g j ^ (shift lam) i) i j := by
    ext i j
    simp only [Matrix.of_apply, shift]
    rw [← pow_add]
    congr 1
    omega
  rw [h, Matrix.det_mul_row, Finset.prod_pow]

private lemma sch_zero_X (tie : Comparison₂) (n : ℕ) :
    sch (fun _ => 0) (X : Fin n → MvPolynomial (Fin n) ℚ) = 1 := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun _ => 0) X
  rw [altn_zero] at h
  exact mul_right_cancel₀ (vdm_X_ne n) (h.trans (one_mul _).symm)

private lemma sch_add_X (tie : Comparison₂) (n : ℕ) (lam : Fin n → ℕ) (m : ℕ) :
    sch (fun i => lam i + m) (X : Fin n → MvPolynomial (Fin n) ℚ) =
      (∏ k, (X k : MvPolynomial (Fin n) ℚ)) ^ m * sch lam X := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun i => lam i + m) X
  rw [altn_add, ← tie (MvPolynomial (Fin n) ℚ) n lam X, ← mul_assoc] at h
  exact mul_right_cancel₀ (vdm_X_ne n) h

theorem schurDet_of :
    Comparison₂ → SchurDet := by
  intro tie R _ _ n g
  refine ⟨?_, fun lam m => ?_⟩
  · rw [← aeval_sch, sch_zero_X tie, map_one]
  · rw [← aeval_sch, sch_add_X tie, map_mul, map_pow, map_prod, aeval_sch]
    simp only [aeval_X]

end UpperTheory.Gal.Schur
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.tie :
    Comparison₂ := by
  intro R _ _ n lam g
  have h := congrArg (aeval g) (GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_add_staircase_eq lam)
  rw [AlgHom.map_det, map_mul] at h
  have hM : ((Matrix.of fun i j => (X j : MvPolynomial (Fin n) ℚ) ^ (lam i + (n - 1 - (i : ℕ)))).map
      (aeval g)) = Matrix.of fun i j => g j ^ (lam i + (n - 1 - (i : ℕ))) := by
    ext i j
    simp
  simp [AlgHom.mapMatrix_apply, GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf, map_prod, hM] at h
  simpa [sch, vdm, altn, shift] using h.symm
end

section

noncomputable section

open Finset
open scoped Classical

namespace UpperTheory.Gal.Schur

def FibreSum : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [CharZero K] (n : ℕ)
    (lam : (E →+* K) → Fin n → ℕ), ∃ k₀, ∀ k, k₀ ≤ k →
    ∀ (N : NumberField.RingOfIntegers E), N ≠ 0 → ∀ B : Finset K,
      ∃ c : (Fin k → NumberField.RingOfIntegers E) →₀ K,
        (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ N ∣ α s ∧ ∀ τ : E →+* K, ∀ b ∈ B, 1 - resO τ (α s) * b ≠ 0) ∧
        ∀ (R : Type) [CommRing R] [Algebra K R] [Algebra ℚ R] (t₀ t₁ : E →+* K), t₀ ≠ t₁ →
          ∀ (ε : (E →+* K) → ℕ) (m : ℕ) (g : (E →+* K) → Fin n → R) (y : R),
          ((∀ i, lam t₁ i = m) → (∀ i j, j ≠ i → IsUnit (g t₀ j - g t₀ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₀ j - y * g t₀ i) * Ring.inverse (g t₀ j - g t₀ i))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ ((n - 1) * m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))) ∧
          ((∀ i, lam t₀ i = m) → (∀ i j, j ≠ i → IsUnit (g t₁ j - g t₁ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₁ i - y * g t₁ j) * Ring.inverse (g t₁ i - g t₁ j))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ (m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (∑ j ∈ univ.erase i, lam t₁ j + (i : ℕ))))

theorem fibreSum_of (h : InterpNF) (h₁ : Fibre) (h₂ : FibreOff) : FibreSum := by
  intro E K _ _ _ _ n lam
  obtain ⟨k₀, hk⟩ := h E K n lam
  refine ⟨k₀, fun k hk' N hN B => ?_⟩
  obtain ⟨c, hc, hsum⟩ := hk k hk' N hN B
  refine ⟨c, hc, fun R _ _ _ t₀ t₁ ht ε m g y => ?_⟩
  have swap : ∀ C : Fin n → R,
      (c.sum fun α r => r • ∑ i,
        (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) * C i) =
      ∑ i, (∏ τ, sch (lam τ) (twist t₀ t₁ ε y i g τ)) * C i := by
    intro C
    rw [Finsupp.sum]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsum R (twist t₀ t₁ ε y i g), Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_mul_assoc]
  refine ⟨fun hm hu => ?_, fun hm hu => ?_⟩
  · rw [swap]
    exact h₁ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu
  · rw [swap]
    exact h₂ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu

end UpperTheory.Gal.Schur
end
end

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

def MixDet : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (d d' : Fin n → R),
    ∑ i, (Matrix.of fun a j : Fin n => (if j = i then d a else d' a) * M a j).det =
      (∑ a, d a * ∏ b ∈ univ.erase a, d' b) * M.det

def vdmAway {R : Type} [CommRing R] {n : ℕ} (i : Fin n) (g : Fin n → R) : R :=
  ∏ a ∈ univ.erase i, ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b)

def PairSplit : Prop :=
  ∀ (R : Type) [CommMonoid R] (n : ℕ) (F : Fin n → Fin n → R) (i : Fin n),
    ∏ a, ∏ b ∈ Finset.Ioi a, F a b =
      (∏ a ∈ univ.erase i, ∏ b ∈ (Finset.Ioi a).erase i, F a b) *
        ∏ k ∈ univ.erase i, (if k < i then F k i else F i k)

def VdmSplit : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (g : Fin n → R) (i : Fin n),
    vdm g = (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - g k)

def PairCount : Prop :=
  ∀ (n : ℕ) (i : Fin n),
    ∑ k ∈ univ.erase i, (n - 1 - (k : ℕ)) = (n - 1).choose 2 + (i : ℕ) ∧
    ∑ a ∈ univ.erase i, ((Finset.Ioi a).erase i).card = (n - 1).choose 2

def OffClrRed : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    ∑ i, sch lam (scaleOff y i g) * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))

def OffClrPow : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    y ^ (n - 1).choose 2 *
      ∑ i, sch lam (scaleOff y i g) * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      y ^ (n - 1).choose 2 * (sch lam g * vdm g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)))

def Expand : Prop :=
  ∀ (K R π : Type) [CommRing K] [CommRing R] [Algebra K R] [Fintype π] [DecidableEq π] (n : ℕ) (x : π → R)
    (g : π → Fin n → R),
    ∏ p, detOne (x p) (g p) =
      ∑ m : π → Fin (n + 1), (∏ p, x p ^ (m p : ℕ)) *
        ∏ p, ((-1) ^ (m p : ℕ) * aeval (g p) (esymm (Fin n) K (m p)))

def DenseSub : Prop :=
  ∀ (K σ : Type) [Field K] [CharZero K] [Fintype σ] (L : AddSubgroup (σ → K)) (a : σ → K),
    Submodule.span K (L : Set (σ → K)) = ⊤ → ZDense {x | x - a ∈ L}

def SpanTop : Prop :=
  ∀ (O K ι : Type) [CommRing O] [Field K] [Fintype ι] (τ : ι → (O →+* K)), Function.Injective τ →
    ∀ (N : O), (∀ t, τ t N ≠ 0) → ∀ k : ℕ,
      Submodule.span K {x : ι × Fin k → K | ∃ β : Fin k → O, x = pt τ (fun s => N * β s)} = ⊤

def DenseOff : Prop :=
  ∀ (K σ : Type) [Field K] (D : Set (σ → K)), ZDense D → ∀ Q : MvPolynomial σ K, Q ≠ 0 →
    ZDense {x | x ∈ D ∧ eval x Q ≠ 0}

def SpanProd : Prop :=
  ∀ (K ι : Type) [CommRing K] [Fintype ι] [DecidableEq ι] (n : ℕ) (P : ι → MvPolynomial (Fin n) K),
    (∀ t, (P t).IsSymmetric) → ∃ k₀, ∀ k, k₀ ≤ k → ∃ w : (ι × Fin k → Fin (n + 1)) → K,
      ∀ (R : Type) [CommRing R] [Algebra K R] (g : ι → Fin n → R),
        ∏ t, aeval (g t) (P t) =
          ∑ m, w m • ∏ p : ι × Fin k, ((-1) ^ (m p : ℕ) * aeval (g p.1) (esymm (Fin n) K (m p)))

def eSpan (K : Type) [CommRing K] (n k : ℕ) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (Set.range fun m : Fin k → Fin (n + 1) => ∏ s, esymm (Fin n) K (m s))

def ESpanMul : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ),
    (∀ k l, k ≤ l → eSpan K n k ≤ eSpan K n l) ∧
    (∀ k l P Q, P ∈ eSpan K n k → Q ∈ eSpan K n l → P * Q ∈ eSpan K n (k + l))

end UpperTheory.Gal.Schur
end
end
