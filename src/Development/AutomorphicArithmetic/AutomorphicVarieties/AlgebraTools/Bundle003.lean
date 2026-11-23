module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Polynomial.Splits
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.FieldTheory.Extension

@[expose] public section

section

open IsLocalRing MvPolynomial

namespace UpperTheory.V.AlgebraTools

variable {P : Type} [CommRing P] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem isPrime_map_C (p : Ideal P) [p.IsPrime] :
    (p.map (C : P →+* MvPolynomial ι P)).IsPrime := by
  have he : p.map (C : P →+* MvPolynomial ι P) =
      RingHom.ker (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk p)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [he]
  exact RingHom.ker_isPrime _

def relIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := Ideal.span (Set.range (z.mulVec m))

def detIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := relIdeal z m ⊔ Ideal.span {z.det}

noncomputable def lam (P : Type) [CommRing P] (c : ι) (j : ι) : MvPolynomial ι P :=
  if j = c then 1 else X j

noncomputable def chartGen (z : Matrix ι ι P) (m : ι → P) (c : ι) :
    ι ⊕ {j : ι // j ≠ c} → MvPolynomial ι P :=
  Sum.elim ((z.map C).mulVec (lam P c)) (fun j => C (m j.1) - lam P c j.1 * C (m c))

noncomputable def chartIdeal (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal (MvPolynomial ι P) :=
  Ideal.span (Set.range (chartGen z m c))

noncomputable def genKer [IsLocalRing P] (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal P where
  carrier := {f | ∃ s : MvPolynomial ι P, s ∉ (maximalIdeal P).map (C : P →+* MvPolynomial ι P) ∧
    s * C f ∈ chartIdeal z m c}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 (Ideal.IsPrime.ne_top (by
    have : (maximalIdeal P).IsPrime := inferInstance
    exact isPrime_map_C _)), by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    have hp : ((maximalIdeal P).map (C : P →+* MvPolynomial ι P)).IsPrime :=
      isPrime_map_C _
    refine ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * C (a + b) = t * (s * C a) + s * (t * C b) := by rw [map_add (f := _)]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  smul_mem' := by
    rintro r a ⟨s, hs, ha⟩
    refine ⟨s, hs, ?_⟩
    have : s * C (r • a) = C r * (s * C a) := by rw [smul_eq_mul, map_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha

end UpperTheory.V.AlgebraTools
end

section

noncomputable section

open MvPolynomial Equiv

namespace UpperTheory.V.AlgebraTools.Hk

variable (R : Type) [CommRing R] (n : ℕ)

def pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2

def De : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - X p.1)


variable {R} in
def NN (q : R) : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - C q * X p.1)

variable {R n}

def alt (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R := ∑ w : Perm (Fin n), Perm.sign w • rename w x


open scoped Classical in
open Classical in
def dd (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  if h : ∃ y, De R n * y = alt x then h.choose else 0

def invSet (w : Perm (Fin n)) : Finset (Fin n × Fin n) := (pairs n).filter fun p => w⁻¹ p.2 < w⁻¹ p.1

def invN (w : Perm (Fin n)) : ℕ := (invSet w).card


variable (n) in
def poin (q : R) : R := ∑ w : Perm (Fin n), q ^ invN w

def IsDual {ι : Type} [Fintype ι] (a b : ι → MvPolynomial (Fin n) R) : Prop :=
  ∀ w : Perm (Fin n), ∑ i, a i * rename w (b i) = if w = 1 then De R n else 0

structure Bern (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] where
  th : MvPolynomial (Fin n) R →ₐ[R] H
  T : Perm (Fin n) → H
  T_one : T 1 = 1
  T_mul : ∀ a b : Fin n, a.val + 1 = b.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ b → T (swap a b * w) = T (swap a b) * T w
  T_sq : ∀ a b : Fin n, a.val + 1 = b.val → T (swap a b) * T (swap a b) = (q - 1) • T (swap a b) + q • (1 : H)
  comm : ∀ a b : Fin n, a.val + 1 = b.val → ∀ j, j ≠ a → j ≠ b → T (swap a b) * th (X j) = th (X j) * T (swap a b)
  relA : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X a) = th (X b) * T (swap a b) + (q - 1) • th (X a)
  relB : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X b) = th (X a) * T (swap a b) - (q - 1) • th (X a)

namespace Bern

variable {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)

def one : H := ∑ w, b.T w

def Faithful : Prop := ∀ x, b.th x * b.one = 0 → x = 0

theorem rel_of_quad {H : Type} [Ring H] [Algebra R H] {q : R} (hq : IsUnit q) (T x y : H)
    (hT : T * T = (q - 1) • T + q • (1 : H)) (h : T * y * T = q • x) :
    T * x = y * T + (q - 1) • x ∧ T * y = x * T - (q - 1) • x := by
  have cancel : ∀ a c : H, q • a = q • c → a = c := by
    intro a c hac
    obtain ⟨u, rfl⟩ := hq
    have := congrArg (fun z => ((u⁻¹ : Rˣ) : R) • z) hac
    simpa [smul_smul] using this
  constructor
  · apply cancel
    rw [← mul_smul_comm, ← h, ← mul_assoc, ← mul_assoc, hT]
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul, h]
    rw [smul_add, smul_comm q (q - 1) x]
    abel
  · apply cancel
    symm
    rw [smul_sub, ← smul_mul_assoc, ← h, mul_assoc (T * y), hT, mul_add, mul_smul_comm,
      mul_smul_comm, mul_one, h, smul_comm q (q - 1) x]
    abel

end Bern

end UpperTheory.V.AlgebraTools.Hk

end
end

section

open Polynomial Matrix IsLocalRing TensorProduct

namespace UpperTheory.V.AlgebraTools

private noncomputable def ilcP (B : Type) [CommRing B] : ℕ → B[X]
  | 0 => X
  | k + 1 => 3 * ilcP B k ^ 2 - 2 * ilcP B k ^ 3

end UpperTheory.V.AlgebraTools

open UpperTheory.V.AlgebraTools in
theorem UpperTheory.V.AlgebraTools.idem_lift_complete :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (I : Ideal B) [IsAdicComplete I E] (z : E) (M : ℕ), (z * z - z) ^ M ∈ I • (⊤ : Submodule B E) → ∃ e : E, IsIdempotentElem e ∧ ∀ N : ℕ, ∃ q : B[X], e - (z + (z * z - z) * aeval z q) ∈ I ^ N • (⊤ : Submodule B E) := by
  intro B E _ _ _ I _ z M hM
  set S : ℕ → Submodule B E := fun n => I ^ n • (⊤ : Submodule B E) with hS
  have L2r : ∀ n (x y : E), x ∈ I ^ n • (⊤ : Submodule B E) →
      x * y ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x y hx
    refine Submodule.smul_induction_on (p := fun x => x * y ∈ I ^ n • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [smul_mul_assoc]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [add_mul]
      exact add_mem h1 h2
  have L2l : ∀ n (x y : E), x ∈ I ^ n • (⊤ : Submodule B E) →
      y * x ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x y hx
    refine Submodule.smul_induction_on (p := fun x => y * x ∈ I ^ n • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [mul_smul_comm]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [mul_add]
      exact add_mem h1 h2
  have L3 : ∀ n (x w : E), x ∈ I • (⊤ : Submodule B E) → w ∈ I ^ n • (⊤ : Submodule B E) →
      x * w ∈ I ^ (n + 1) • (⊤ : Submodule B E) := by
    intro n x w hx hw
    refine Submodule.smul_induction_on
      (p := fun x => x * w ∈ I ^ (n + 1) • (⊤ : Submodule B E)) hx
      (fun a ha m _ => ?_) (fun x1 x2 h1 h2 => ?_)
    · rw [smul_mul_assoc]
      have h := Submodule.smul_mem_smul ha (L2l n w m hw)
      rwa [← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ'] at h
    · rw [add_mul]
      exact add_mem h1 h2
  have Lpow : ∀ n (x : E), x ∈ I • (⊤ : Submodule B E) → x ^ n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n x hx
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    | succ n ih =>
      rw [pow_succ' x n]
      exact L3 n x _ hx ih
  have Mem : ∀ n k, M * n ≤ 2 ^ k → ∀ y : E,
      (z * z - z) ^ (2 ^ k) * y ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n k hk y
    have h : (z * z - z) ^ (2 ^ k) = ((z * z - z) ^ M) ^ n * (z * z - z) ^ (2 ^ k - M * n) := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk]
    rw [h, mul_assoc]
    exact L2r _ _ _ (Lpow n _ hM)
  have hk2 : ∀ k : ℕ, k ≤ 2 ^ k := fun k => (Nat.lt_two_pow_self).le
  have PoincareLelongAlt : ∀ k, ∃ Q : B[X], ilcP B k = X + (X * X - X) * Q := by
    intro k
    induction k with
    | zero => exact ⟨0, by rw [ilcP]; ring⟩
    | succ k ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨Q - (1 + 2 * X * Q + (X * X - X) * Q ^ 2 - Q) * (2 * (X + (X * X - X) * Q) - 1), ?_⟩
      rw [ilcP, hQ]
      ring
  have ProjectiveLineTwo : ∀ k, ∃ W : B[X], ilcP B k * ilcP B k - ilcP B k = (X * X - X) ^ (2 ^ k) * W := by
    intro k
    induction k with
    | zero => exact ⟨1, by rw [ilcP]; ring⟩
    | succ k ih =>
      obtain ⟨W, hW⟩ := ih
      have hid : ∀ P : B[X], (3 * P ^ 2 - 2 * P ^ 3) * (3 * P ^ 2 - 2 * P ^ 3) -
          (3 * P ^ 2 - 2 * P ^ 3) = (P * P - P) ^ 2 * (4 * (P * P - P) - 3) := fun P => by ring
      refine ⟨W ^ 2 * (4 * (X * X - X) ^ (2 ^ k) * W - 3), ?_⟩
      rw [ilcP, hid, hW, pow_succ 2 k, pow_mul]
      ring
  have PL3 : ∀ k, ∃ V : B[X], ilcP B (k + 1) - ilcP B k = (X * X - X) ^ (2 ^ k) * V := by
    intro k
    obtain ⟨W, hW⟩ := ProjectiveLineTwo k
    refine ⟨-(W * (2 * ilcP B k - 1)), ?_⟩
    rw [ilcP]
    linear_combination (-(2 * ilcP B k - 1)) * hW
  have PL4 : ∀ k j, ∃ V : B[X], ilcP B (k + j) - ilcP B k = (X * X - X) ^ (2 ^ k) * V := by
    intro k j
    induction j with
    | zero => exact ⟨0, by simp⟩
    | succ j ih =>
      obtain ⟨V0, hV0⟩ := ih
      obtain ⟨V1, hV1⟩ := PL3 (k + j)
      have hpow : (X * X - X : B[X]) ^ (2 ^ (k + j)) =
          (X * X - X) ^ (2 ^ k) * (X * X - X) ^ (2 ^ (k + j) - 2 ^ k) := by
        rw [← pow_add, Nat.add_sub_cancel' (Nat.pow_le_pow_right (by norm_num) (by omega))]
      refine ⟨(X * X - X) ^ (2 ^ (k + j) - 2 ^ k) * V1 + V0, ?_⟩
      rw [show k + (j + 1) = k + j + 1 by omega]
      linear_combination hV1 + hV0 + V1 * hpow
  have hD : aeval z (X * X - X : B[X]) = z * z - z := by simp
  let f : ℕ → E := fun n => aeval z (ilcP B (M * n))
  have hdiff : ∀ k j, ∃ V : B[X], aeval z (ilcP B (k + j)) - aeval z (ilcP B k) =
      (z * z - z) ^ (2 ^ k) * aeval z V := by
    intro k j
    obtain ⟨V, hV⟩ := PL4 k j
    refine ⟨V, ?_⟩
    have h := congrArg (aeval z) hV
    rwa [map_sub, map_mul, map_pow, hD] at h
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ m • (⊤ : Submodule B E))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    obtain ⟨V, hV⟩ := hdiff (M * m) (M * n - M * m)
    rw [Nat.add_sub_cancel' (Nat.mul_le_mul_left M hmn)] at hV
    have h : f m - f n = -((z * z - z) ^ (2 ^ (M * m)) * aeval z V) := by
      rw [← hV]
      simp only [f]
      abel
    rw [h]
    exact neg_mem (Mem m (M * m) (hk2 _) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I E) hcauchy
  have hd : ∀ n, L - f n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n
    have h := (SModEq.sub_mem).mp (hL n)
    rw [← neg_sub]
    exact neg_mem h
  have hsq : ∀ n, f n * f n - f n ∈ I ^ n • (⊤ : Submodule B E) := by
    intro n
    obtain ⟨W, hW⟩ := ProjectiveLineTwo (M * n)
    have h := congrArg (aeval z) hW
    rw [map_sub, map_mul, map_mul, map_pow, hD] at h
    simp only [f]
    rw [h]
    exact Mem n (M * n) (hk2 _) _
  have hidem : IsIdempotentElem L := by
    have h0 : L * L - L = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff I E)
      intro n
      rw [SModEq.sub_mem, sub_zero]
      have e1 : L * L - L = (f n * f n - f n) + (f n * (L - f n) + (L - f n) * f n +
          (L - f n) * (L - f n) - (L - f n)) := by noncomm_ring
      rw [e1]
      have hdn := hd n
      exact add_mem (hsq n) (sub_mem (add_mem (add_mem (L2l _ _ _ hdn) (L2r _ _ _ hdn))
        (L2r _ _ _ hdn)) hdn)
    exact sub_eq_zero.mp h0
  refine ⟨L, hidem, fun N => ?_⟩
  obtain ⟨Q, hQ⟩ := PoincareLelongAlt (M * N)
  refine ⟨Q, ?_⟩
  have h : f N = z + (z * z - z) * aeval z Q := by
    simp only [f]
    rw [hQ, map_add (f := _), map_mul, hD, aeval_X]
  rw [← h]
  exact hd N
end

section

open IsLocalRing

private theorem exists_field_lift {R S F K L : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Field F] [Field K] [Field L] (c : F →+* K) (d : F →+* L) (a : R →+* F) (b : S →+* K)
    (hab : b.comp (algebraMap R S) = c.comp a)
    {ι : Type} (u : ι → S) (f : ι → Polynomial R) (hu : Algebra.adjoin R (Set.range u) = ⊤)
    (hf : ∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧
      ((f i).map (d.comp a)).Splits) :
    ∃ ψ : S →+* L, ψ.comp (algebraMap R S) = d.comp a ∧
      RingHom.ker ψ = RingHom.ker b := by
  letI : Algebra F K := c.toAlgebra
  letI : Algebra F L := d.toAlgebra
  change b.comp (algebraMap R S) = (algebraMap F K).comp a at hab
  have hab' : ∀ r, b (algebraMap R S r) = algebraMap F K (a r) := fun r => RingHom.congr_fun hab r
  have hT : ∀ s ∈ Set.range (fun i => b (u i)),
      IsIntegral F s ∧ ((minpoly F s).map (algebraMap F L)).Splits := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨h1, h2, h3⟩ := hf i
    have h4 : Polynomial.aeval (b (u i)) ((f i).map a) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hab, ← Polynomial.hom_eval₂,
        ← Polynomial.aeval_def, h2, map_zero]
    refine ⟨⟨_, h1.map a, h4⟩, ?_⟩
    rw [← Polynomial.map_map] at h3
    exact h3.of_dvd ((h1.map a).map _).ne_zero (Polynomial.map_dvd _ (minpoly.dvd F _ h4))
  obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_adjoin_of_splits hT
  have hmem : ∀ s : S, b s ∈ IntermediateField.adjoin F (Set.range (fun i => b (u i))) := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r => rw [hab']; exact IntermediateField.algebraMap_mem _ _
    | add y z _ _ hy hz => rw [map_add b]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  let b' : S →+* IntermediateField.adjoin F (Set.range (fun i => b (u i))) :=
    b.codRestrict _ hmem
  refine ⟨φ.toRingHom.comp b', ?_, ?_⟩
  · ext r
    have : b' (algebraMap R S r) = algebraMap F _ (a r) := Subtype.ext (hab' r)
    change φ (b' (algebraMap R S r)) = algebraMap F L (a r)
    rw [this, AlgHom.commutes]
  · ext s
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change φ (b' s) = 0 ↔ _
    rw [map_eq_zero_iff φ φ.toRingHom.injective]
    exact Subtype.ext_iff

theorem UpperTheory.V.AlgebraTools.exists_lift_ker_eq :
    ∀ (R S A : Type) [CommRing R] [CommRing S] [CommRing A] [IsDomain A] [Algebra R S] (x : R →+* A)
      (ι : Type) (u : ι → S) (f : ι → Polynomial R), Algebra.adjoin R (Set.range u) = ⊤ →
      (∀ i, (f i).Monic ∧ Polynomial.aeval (u i) (f i) = 0 ∧ ((f i).map x).Splits) →
      ∀ P : Ideal S, P.IsPrime → P.comap (algebraMap R S) = RingHom.ker x →
      ∃ x' : S →+* A, x'.comp (algebraMap R S) = x ∧ RingHom.ker x' = P := by
  intro R S A _ _ _ _ _ x ι u f hu hf P hP hPx
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  let j : A →+* FractionRing A := algebraMap A (FractionRing A)
  have hj : Function.Injective j := IsFractionRing.injective A (FractionRing A)
  let b : S →+* FractionRing (S ⧸ P) :=
    (algebraMap (S ⧸ P) (FractionRing (S ⧸ P))).comp (Ideal.Quotient.mk P)
  have hb : RingHom.ker b = P := by
    ext s
    rw [RingHom.mem_ker]
    change algebraMap (S ⧸ P) (FractionRing (S ⧸ P)) (Ideal.Quotient.mk P s) = 0 ↔ _
    rw [map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ P) (FractionRing (S ⧸ P))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hkb : RingHom.ker (b.comp (algebraMap R S)) = RingHom.ker x := by
    rw [← RingHom.comap_ker, hb, hPx]
  have hkj : RingHom.ker (j.comp x) = RingHom.ker x := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot j).1 hj]
    rfl
  let g₁ : R ⧸ RingHom.ker x →+* FractionRing (S ⧸ P) :=
    Ideal.Quotient.lift _ (b.comp (algebraMap R S)) (fun r hr => by
      rw [← hkb] at hr; exact hr)
  let g₂ : R ⧸ RingHom.ker x →+* FractionRing A :=
    Ideal.Quotient.lift _ (j.comp x) (fun r hr => by rw [← hkj] at hr; exact hr)
  have hg₁ : Function.Injective g₁ := RingHom.lift_injective_of_ker_le_ideal _ _ hkb.le
  have hg₂ : Function.Injective g₂ := RingHom.lift_injective_of_ker_le_ideal _ _ hkj.le
  let F := FractionRing (R ⧸ RingHom.ker x)
  let a : R →+* F := (algebraMap (R ⧸ RingHom.ker x) F).comp (Ideal.Quotient.mk _)
  obtain ⟨c, h1⟩ : ∃ c : F →+* FractionRing (S ⧸ P), b.comp (algebraMap R S) = c.comp a :=
    ⟨IsFractionRing.lift hg₁, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₁ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _)).symm⟩
  obtain ⟨d, h2⟩ : ∃ d : F →+* FractionRing A, d.comp a = j.comp x :=
    ⟨IsFractionRing.lift hg₂, RingHom.ext fun r =>
      ((IsFractionRing.lift_algebraMap (K := F) hg₂ (Ideal.Quotient.mk _ r)).trans
        (Ideal.Quotient.lift_mk _ _ _))⟩
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_field_lift c d a b h1 u f hu (fun i =>
    ⟨(hf i).1, (hf i).2.1, by rw [h2, ← Polynomial.map_map]; exact (hf i).2.2.map j⟩)
  rw [h2] at hψ1
  rw [hb] at hψ2
  have hmem : ∀ s : S, ψ s ∈ j.range := by
    intro s
    have hs : s ∈ Algebra.adjoin R (Set.range u) := hu ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨hm, h0, hsp⟩ := hf i
      have h4 : Polynomial.eval₂ j (ψ (u i)) ((f i).map x) = 0 := by
        rw [Polynomial.eval₂_map, ← hψ1, ← Polynomial.hom_eval₂,
          ← Polynomial.aeval_def, h0, map_zero]
      rw [hsp.eq_prod_roots_of_monic (hm.map x), Polynomial.eval₂_multiset_prod,
        Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at h4
      obtain ⟨c, -, hc⟩ := h4
      refine ⟨c, ?_⟩
      simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at hc
      exact (sub_eq_zero.1 hc).symm
    | algebraMap r => exact ⟨x r, (RingHom.congr_fun hψ1 r).symm⟩
    | add y z _ _ hy hz => rw [map_add ψ]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  choose g hg using hmem
  let x' : S →+* A :=
    { toFun := g
      map_one' := hj (by rw [hg, map_one, map_one])
      map_mul' := fun s t => hj (by rw [map_mul, hg, hg, hg, map_mul])
      map_zero' := hj (by rw [hg, map_zero, map_zero])
      map_add' := fun s t => hj (by rw [map_add (f := _), hg, hg, hg, map_add (f := _)]) }
  refine ⟨x', ?_, ?_⟩
  · ext r
    exact hj ((hg _).trans (RingHom.congr_fun hψ1 r))
  · ext s
    rw [← hψ2, RingHom.mem_ker, RingHom.mem_ker, ← hg, map_eq_zero_iff j hj]
    rfl
end
