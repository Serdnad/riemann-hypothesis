module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Mathlib.Data.Matrix.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import ReciprocityTheory.DualLattices.Bundle001

@[expose] public section

section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem eigenvector_mem_span_block_of_basis : ∀ (K C : Type) [Field K] [Field C] (ι : K →+* C) (O A : Type) [Fintype A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → K), Function.Injective em → (∀ x q, (M x).mulVec (fun s => ι (u q s)) = em q.1 x • fun s => ι (u q s)) → (∀ z : Fin d → K, ∃! b : (Σ a : A, Fin (n a)) → K, ∀ s, ∑ q, b q * u q s = z s) → ∀ (a : A) (z : Fin d → C), (∀ x, (M x).mulVec z = em a x • z) → ∃ b : Fin (n a) → C, z = ∑ i, b i • fun s => ι (u ⟨a, i⟩ s) := by
  intro K C _ _ ι O A _ n d M em u hem hM hb a z hz
  classical
  let U : Matrix (Σ a : A, Fin (n a)) (Fin d) K := Matrix.of u
  let W : Matrix (Fin d) (Σ a : A, Fin (n a)) K :=
    Matrix.of fun t => (hb (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hb (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := by
    have h1 : U * W * U = U := by rw [Matrix.mul_assoc, hWU, Matrix.mul_one]
    have h2 : (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) * U = U := Matrix.one_mul _
    ext q q'
    have := (hb (u q)).unique (y₁ := (U * W) q)
      (y₂ := (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) q)
      (fun s => by
        have := congrFun (congrFun h1 q) s
        rw [Matrix.mul_apply] at this
        exact this)
      (fun s => by
        have := congrFun (congrFun h2 q) s
        rw [Matrix.mul_apply] at this
        exact this)
    exact congrFun this q'
  have hWU' : W.map ι * U.map ι = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hUW' : U.map ι * W.map ι = 1 := by
    rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hvm : ∀ c : (Σ a : A, Fin (n a)) → C,
      Matrix.vecMul c (U.map ι) = ∑ q, c q • fun s => ι (u q s) := by
    intro c
    funext s
    simp [Matrix.vecMul, dotProduct, U, Finset.sum_apply]
  have hind : ∀ c : (Σ a : A, Fin (n a)) → C,
      (∑ q, c q • fun s => ι (u q s)) = 0 → c = 0 := by
    intro c hc
    rw [← hvm] at hc
    have : Matrix.vecMul (Matrix.vecMul c (U.map ι)) (W.map ι) = c := by
      rw [Matrix.vecMul_vecMul, hUW', Matrix.vecMul_one]
    rw [← this, hc, Matrix.zero_vecMul]
  obtain ⟨c, hc⟩ : ∃ c : (Σ a : A, Fin (n a)) → C, z = ∑ q, c q • fun s => ι (u q s) := by
    refine ⟨Matrix.vecMul z (W.map ι), ?_⟩
    rw [← hvm, Matrix.vecMul_vecMul, hWU', Matrix.vecMul_one]
  have hzero : ∀ q : (Σ a : A, Fin (n a)), q.1 ≠ a → c q = 0 := by
    intro q hq
    by_contra hcq
    apply hq
    apply hem
    funext x
    have h := hz x
    have h3 : (∑ q : (Σ a : A, Fin (n a)), ((em q.1 x - em a x) * c q) • fun s => ι (u q s)) = 0 := by
      have e1 : (M x).mulVec z
          = ∑ q : (Σ a : A, Fin (n a)), (em q.1 x * c q) • fun s => ι (u q s) := by
        rw [hc, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Matrix.mulVec_smul, hM, smul_smul, mul_comm]
      have e2 : em a x • z
          = ∑ q : (Σ a : A, Fin (n a)), (em a x * c q) • fun s => ι (u q s) := by
        rw [hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul]
      simp only [sub_mul, sub_smul, Finset.sum_sub_distrib]
      rw [← e1, ← e2, h, sub_self]
    have h4 := congrFun (hind _ h3) q
    simp only [Pi.zero_apply, mul_eq_zero] at h4
    exact sub_eq_zero.mp (h4.resolve_right hcq)
  refine ⟨fun i => c ⟨a, i⟩, ?_⟩
  rw [hc, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hzero ⟨a', i⟩ ha', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory
end

section

open ReciprocityTheory.PGsh

noncomputable section

namespace GlobalTheory.PolyPairingAdjoint

open MvPolynomial Finset

variable {R : Type*} [CommRing R] {κ : Type*}

def wt (R : Type*) [CommRing R] (A : κ →₀ ℕ) : R := A.prod fun _ e => (e.factorial : R)

def pair (P Q : MvPolynomial κ R) : R := ∑ A ∈ P.support, AddMonoidAlgebra.coeff P A * wt R A * AddMonoidAlgebra.coeff Q A

theorem wt_add_single (B : κ →₀ ℕ) (v : κ) :
    wt R (B + Finsupp.single v 1) = wt R B * ((B v : R) + 1) := by
  classical
  unfold wt
  have h1 : (B + Finsupp.single v 1).support ⊆ insert v B.support := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    by_cases hxv : x = v
    · simp [hxv]
    · apply Finset.mem_insert_of_mem
      rw [Finsupp.mem_support_iff]
      simpa [Finsupp.single_apply, Ne.symm hxv] using hx
  have h2 : B.support ⊆ insert v B.support := Finset.subset_insert _ _
  rw [Finsupp.prod_of_support_subset _ h1 (fun _ e => (e.factorial : R)) (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ h2 (fun _ e => (e.factorial : R)) (fun _ _ => by simp),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v B.support),
    ← Finset.mul_prod_erase _ (fun x => ((B x).factorial : R)) (Finset.mem_insert_self v B.support)]
  have h3 : ∏ x ∈ (insert v B.support).erase v,
        (((B + Finsupp.single v 1 : κ →₀ ℕ) x).factorial : R) =
      ∏ x ∈ (insert v B.support).erase v, ((B x).factorial : R) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp [Ne.symm hxv]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

theorem pair_eq_sum (P Q : MvPolynomial κ R) (S : Finset (κ →₀ ℕ)) (hS : P.support ⊆ S) :
    pair P Q = ∑ A ∈ S, AddMonoidAlgebra.coeff P A * wt R A * AddMonoidAlgebra.coeff Q A := by
  unfold pair
  apply Finset.sum_subset hS
  intro A _ hA
  rw [MvPolynomial.notMem_support_iff] at hA
  simp [hA]

theorem pair_add_left (P P' Q : MvPolynomial κ R) : pair (P + P') Q = pair P Q + pair P' Q := by
  classical
  rw [pair_eq_sum (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
    pair_eq_sum P Q (P.support ∪ P'.support) Finset.subset_union_left,
    pair_eq_sum P' Q (P.support ∪ P'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  simp only [MvPolynomial.coeff_add]
  ring

theorem pair_C_mul_left (c : R) (P Q : MvPolynomial κ R) : pair (C c * P) Q = c * pair P Q := by
  rw [← smul_eq_C_mul, pair_eq_sum (c • P) Q P.support MvPolynomial.support_smul,
    pair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem pair_C_mul_right (c : R) (P Q : MvPolynomial κ R) : pair P (C c * Q) = c * pair P Q := by
  rw [pair, pair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [coeff_C_mul]
  ring

theorem pair_sum_right {α : Type*} (s : Finset α) (P : MvPolynomial κ R)
    (f : α → MvPolynomial κ R) : pair P (∑ i ∈ s, f i) = ∑ i ∈ s, pair P (f i) := by
  unfold pair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [coeff_sum, Finset.mul_sum]

theorem pair_sum_left {α : Type*} (s : Finset α) (f : α → MvPolynomial κ R)
    (Q : MvPolynomial κ R) : pair (∑ i ∈ s, f i) Q = ∑ i ∈ s, pair (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add_left, ih]

theorem pair_C_left (c : R) (Q : MvPolynomial κ R) : pair (C c) Q = c * constantCoeff Q := by
  classical
  rw [pair_eq_sum (C c) Q {0} (by
    intro A hA
    rw [MvPolynomial.mem_support_iff, coeff_C] at hA
    simp only [Finset.mem_singleton]
    by_contra h
    exact hA (if_neg (Ne.symm h)))]
  simp [wt, constantCoeff_eq]

theorem pair_mul_X (P Q : MvPolynomial κ R) (v : κ) :
    pair (P * X v) Q = pair P (pderiv v Q) := by
  classical
  have hs : (P * X v).support ⊆ P.support.map (addRightEmbedding (Finsupp.single v 1)) := by
    intro A hA
    rw [mem_support_iff, coeff_mul_X'] at hA
    split_ifs at hA with h
    · rw [Finset.mem_map]
      refine ⟨A - Finsupp.single v 1, mem_support_iff.mpr hA, ?_⟩
      rw [addRightEmbedding_apply]
      exact Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp h)
    · exact absurd rfl hA
  rw [pair_eq_sum (P * X v) Q _ hs, Finset.sum_map, pair]
  apply Finset.sum_congr rfl
  intro B _
  simp only [addRightEmbedding_apply, coeff_mul_X, coeff_pderiv, wt_add_single]
  ring

variable [Fintype κ]

def subst (g : κ → κ → R) : MvPolynomial κ R →ₐ[R] MvPolynomial κ R :=
  aeval (fun i => ∑ j, (C (g i j) * X j : MvPolynomial κ R))

theorem subst_X (g : κ → κ → R) (i : κ) : subst g (X i) = ∑ j, C (g i j) * X j := aeval_X _ _

theorem subst_C (g : κ → κ → R) (c : R) : subst g (C c) = C c := by simp [subst]

theorem constantCoeff_subst (g : κ → κ → R) (Q : MvPolynomial κ R) :
    constantCoeff (subst g Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [subst_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp [subst_X]

theorem pderiv_subst (g : κ → κ → R) (j : κ) (Q : MvPolynomial κ R) :
    pderiv j (subst g Q) = ∑ i, C (g i j) * subst g (pderiv i Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a => simp [subst_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have h1 : pderiv j (subst g (X k)) = C (g k j) := by

      rw [subst_X, map_sum, Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [pderiv_X_of_ne hb]
      · simp
    have h2 : ∑ i, C (g i j) * subst g (p * pderiv i (X k)) = subst g p * C (g k j) := by
      rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b _ hb
        simp [pderiv_X_of_ne (Ne.symm hb)]
      · simp
    rw [map_mul, pderiv_mul, h1, hp, ← h2, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pderiv_mul, map_add (f := _), map_mul, mul_add, mul_assoc]

theorem pair_subst (g : κ → κ → R) (P Q : MvPolynomial κ R) :
    pair P (subst g Q) = pair (subst (fun i j => g j i) P) Q := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C a => rw [subst_C, pair_C_left, pair_C_left, constantCoeff_subst]
  | add p q hp hq => rw [map_add (f := _), pair_add_left, pair_add_left, hp, hq]
  | mul_X p k hp =>
    rw [pair_mul_X, pderiv_subst, pair_sum_right, map_mul, subst_X, Finset.mul_sum, pair_sum_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [pair_C_mul_right, hp, mul_left_comm, pair_C_mul_left, pair_mul_X]

end GlobalTheory.PolyPairingAdjoint
end
end

section

open ReciprocityTheory.PGsh

namespace GlobalTheory.LegendreBounds

theorem digitSum_le (l N : ℕ) (hl : 1 < l) :
    (Nat.digits l N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hlen : (Nat.digits l N).length = Nat.log l N + 1 := Nat.length_digits l N hl hN.ne'
    have hd : ∀ d ∈ Nat.digits l N, d ≤ l - 1 := fun d hd => by
      have := Nat.digits_lt_base hl hd
      omega
    calc (Nat.digits l N).sum ≤ (Nat.digits l N).length * (l - 1) := by
          simpa [smul_eq_mul] using List.sum_le_card_nsmul _ _ hd
      _ = (Nat.log l N + 1) * (l - 1) := by rw [hlen]

theorem legendre_real (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) = ((N : ℝ) - ((Nat.digits l N).sum : ℕ)) / (l - 1) := by
  have := Fact.mk hl
  have h1 : (l - 1) * padicValNat l N.factorial = N - (Nat.digits l N).sum :=
    by simpa [Nat.padicValNat_def] using (hl.sub_one_mul_multiplicity_factorial (n := N))
  have h2 : (Nat.digits l N).sum ≤ N := Nat.digit_sum_le l N
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have h3 := congrArg (Nat.cast : ℕ → ℝ) h1
  rw [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_sub h2, Nat.cast_one] at h3
  rw [eq_div_iff (by linarith)]
  linear_combination h3

private theorem digits_sum_div_pred_le_log_add_one (l N : ℕ) (hl : 1 < l) :
    ((Nat.digits l N).sum : ℝ) / (l - 1) ≤ Nat.log l N + 1 := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl
    linarith
  rw [div_le_iff₀ hl1]
  have h := digitSum_le l N hl
  have h' : ((Nat.digits l N).sum : ℝ) ≤ ((Nat.log l N + 1) * (l - 1) : ℕ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hl.le, Nat.cast_one] at h'
  exact h'

private theorem natLog_le_logb_of_le (l N M : ℕ) (hl : 1 < l) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (Nat.log l N : ℝ) ≤ Real.logb l M := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.le_logb_iff_rpow_le hl' hM', Real.rpow_natCast]
  have : l ^ Nat.log l N ≤ M := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using hM
    · exact (Nat.pow_log_le_self l hN.ne').trans hNM
  exact_mod_cast this

theorem lower (l : ℕ) (hl : l.Prime) (N M : ℕ) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (N : ℝ) / (l - 1) - (Real.logb l M + 1) ≤ padicValNat l N.factorial := by
  have h1 := digits_sum_div_pred_le_log_add_one l N hl.one_lt
  have h2 := natLog_le_logb_of_le l N M hl.one_lt hM hNM
  rw [legendre_real l hl N, sub_div]
  linarith

theorem upper (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) ≤ (N : ℝ) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  have : (0 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := Nat.cast_nonneg _
  linarith

theorem upper_of_pos (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : 1 ≤ N) :
    (padicValNat l N.factorial : ℝ) ≤ ((N : ℝ) - 1) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have hN0 : N ≠ 0 := by omega
  have hs : 1 ≤ (Nat.digits l N).sum := by
    have hmem := List.getLast_mem ((Nat.digits_ne_nil_iff_ne_zero (b := l) (n := N)).mpr hN0)
    have hlast := Nat.getLast_digit_ne_zero l hN0
    have := List.le_sum_of_mem hmem
    omega
  have hs' : (1 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := by exact_mod_cast hs
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  linarith

theorem padicValNat_prod_factorial (l : ℕ) (hl : l.Prime) {κ : Type} (s : Finset κ)
    (A : κ → ℕ) :
    (padicValNat l (∏ j ∈ s, (A j).factorial) : ℝ)
      = ∑ j ∈ s, (padicValNat l (A j).factorial : ℝ) := by
  have := Fact.mk hl
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Nat.padicValNat_def]
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _), Nat.cast_add, ih]

theorem legendre_bounds :
  (∀ (l : ℕ), l.Prime → (∀ N : ℕ, 1 ≤ N → (N : ℝ) / (l - 1) - (Real.logb l N + 1) ≤ padicValNat l N.factorial ∧ (padicValNat l N.factorial : ℝ) ≤ (N - 1) / (l - 1)) ∧
    (∀ (κ : Type) [Fintype κ] (A : κ → ℕ), 1 ≤ ∑ j, A j → ((∑ j, A j : ℕ) : ℝ) / (l - 1) - Fintype.card κ * (Real.logb l ((∑ j, A j : ℕ) : ℝ) + 1) ≤ padicValNat l (∏ j, (A j).factorial)) ∧
    ∀ n₀ x : ℕ, (padicValNat l (∏ c ∈ Finset.range n₀, (x + c).factorial) : ℝ) - padicValNat l (∏ c ∈ Finset.range n₀, c.factorial) ≤
      n₀ * x / (l - 1) + n₀ * (Real.logb l n₀ + 1)) := by
  intro l hl
  refine ⟨fun N hN => ⟨lower l hl N N hN le_rfl, upper_of_pos l hl N hN⟩, ?_, ?_⟩
  · intro κ _ A hA
    rw [padicValNat_prod_factorial l hl Finset.univ A]
    have key : ∀ j ∈ (Finset.univ : Finset κ), (A j : ℝ) / (l - 1) - (Real.logb l ((∑ i, A i : ℕ) : ℝ) + 1)
        ≤ padicValNat l (A j).factorial := fun j _ =>
      lower l hl (A j) (∑ i, A i) hA
        (Finset.single_le_sum (fun i _ => Nat.zero_le (A i)) (Finset.mem_univ j))
    have h := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div,
      ← Nat.cast_sum] at h
    linarith
  · intro n₀ x
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn
    · simp
    · have e1 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => x + c)
      have e2 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => c)
      rw [e1, e2, ← Finset.sum_sub_distrib]
      calc _ ≤ ∑ c ∈ Finset.range n₀, ((x : ℝ) / (l - 1) + (Real.logb l n₀ + 1)) :=
            Finset.sum_le_sum fun c hc => by
              have h1 := upper l hl (x + c)
              have h2 := lower l hl c n₀ hn (Finset.mem_range.mp hc).le
              push_cast at h1
              have h3 : ((x : ℝ) + c) / (l - 1) = x / (l - 1) + c / (l - 1) := add_div _ _ _
              linarith
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end GlobalTheory.LegendreBounds
end
