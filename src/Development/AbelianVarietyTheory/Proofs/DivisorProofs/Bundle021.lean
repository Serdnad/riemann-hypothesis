module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

section

open IsLocalRing TensorProduct

namespace GlobalTheory


open MvPolynomial in
noncomputable def coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) : MvPolynomial τ B :=
  ∑ s ∈ p.support, MvPolynomial.monomial s (D (p.coeff s))

open MvPolynomial in
theorem coeff_coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) (m : τ →₀ ℕ) :
    (coeffDerivFun D p).coeff m = D (p.coeff m) := by
  classical
  rw [coeffDerivFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

noncomputable def coeffDerivAddHom {B τ : Type} [CommRing B] (D : Derivation ℤ B B) :
    MvPolynomial τ B →+ MvPolynomial τ B where
  toFun := coeffDerivFun D
  map_zero' := by ext m; simp [coeff_coeffDerivFun]
  map_add' p q := by ext m; simp [coeff_coeffDerivFun]

theorem coeffDerivAddHom_monomial {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (s : τ →₀ ℕ) (a : B) :
    coeffDerivAddHom D (MvPolynomial.monomial s a) = MvPolynomial.monomial s (D a) := by
  classical
  ext m
  change AddMonoidAlgebra.coeff (coeffDerivFun D _) m = _
  rw [coeff_coeffDerivFun, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

theorem coeffDerivAddHom_mul {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      simp only [MvPolynomial.monomial_mul_monomial, coeffDerivAddHom_monomial, Derivation.leibniz,
        smul_eq_mul, map_add, add_comm v u]
    | add q₁ q₂ h₁ h₂ =>
      rw [mul_add, map_add (f := _), h₁, h₂, map_add (f := _)]; ring
  | add p₁ p₂ h₁ h₂ =>
    rw [add_mul, map_add (f := _), h₁, h₂, map_add (f := _)]; ring

theorem derivation_extend_mvPolynomial :
    ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B),
      ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B),
        (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  intro B τ _ D
  refine ⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap
    (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩
  · intro x
    show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)
    exact coeffDerivAddHom_monomial D 0 x
  · intro t
    show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0
    rw [coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory.DegreeBound

variable {K : Type} [Field K] {D : ℕ}

def Good (y : Fin D → K) (j : Fin D) (N : ℕ) (b : K) : Prop :=
  ∃ C : MvPolynomial (Fin D) ℤ, C.totalDegree ≤ N ∧ b * y j ^ N = aeval y C

lemma good_mono {y : Fin D → K} {j : Fin D} {N : ℕ} {b : K} (h : Good y j N b) (M : ℕ) :
    Good y j (N + M) b := by
  obtain ⟨C, hC, he⟩ := h
  refine ⟨C * X j ^ M, (totalDegree_mul _ _).trans (by rw [totalDegree_X_pow]; omega), ?_⟩
  rw [pow_add, ← mul_assoc, he, map_mul, map_pow, aeval_X]

lemma good_le {y : Fin D → K} {j : Fin D} {N N' : ℕ} {b : K} (h : Good y j N b) (hN : N ≤ N') :
    Good y j N' b := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact good_mono h M

lemma good_add {y : Fin D → K} {j : Fin D} {N : ℕ} {b b' : K} (h : Good y j N b)
    (h' : Good y j N b') : Good y j N (b + b') := by
  obtain ⟨C, hC, he⟩ := h
  obtain ⟨C', hC', he'⟩ := h'
  exact ⟨C + C', (totalDegree_add _ _).trans (max_le hC hC'), by rw [add_mul, he, he', map_add (f := _)]⟩

lemma good_mul {y : Fin D → K} {j : Fin D} {N N' : ℕ} {b b' : K} (h : Good y j N b)
    (h' : Good y j N' b') : Good y j (N + N') (b * b') := by
  obtain ⟨C, hC, he⟩ := h
  obtain ⟨C', hC', he'⟩ := h'
  refine ⟨C * C', (totalDegree_mul _ _).trans (add_le_add hC hC'), ?_⟩
  rw [map_mul, ← he, ← he', pow_add]; ring

lemma good_algebraMap (y : Fin D → K) (j : Fin D) (r : ℤ) : Good y j 0 (algebraMap ℤ K r) :=
  ⟨MvPolynomial.C r, by rw [totalDegree_C], by rw [pow_zero, mul_one, aeval_C]⟩

lemma aeval_good {ι : Type} {y : Fin D → K} {j : Fin D} {z : ι → K}
    (hz : ∀ i, ∃ N, Good y j N (z i)) (a : MvPolynomial ι ℤ) : ∃ N, Good y j N (aeval z a) := by
  refine MvPolynomial.induction_on (motive := fun a => ∃ N, Good y j N (aeval z a)) a ?_ ?_ ?_
  · intro r; exact ⟨0, by rw [aeval_C]; exact good_algebraMap y j r⟩
  · rintro p p' ⟨N, hN⟩ ⟨N', hN'⟩
    refine ⟨N + N', ?_⟩
    rw [map_add (f := _)]
    exact good_add (good_mono hN N') (by rw [add_comm]; exact good_mono hN' N)
  · rintro p i ⟨N, hN⟩
    obtain ⟨M, hM⟩ := hz i
    exact ⟨N + M, by rw [map_mul, aeval_X]; exact good_mul hN hM⟩

lemma common_order {y : Fin D → K} {j : Fin D} (c : ℕ → K) (hc : ∀ k, ∃ N, Good y j N (c k))
    (n : ℕ) : ∃ N, ∀ k < n, Good y j N (c k) := by
  induction n with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := hc n
    refine ⟨N + M, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact good_mono (hN k hk) M
    · exact good_le hM (Nat.le_add_left _ _)

end GlobalTheory.DegreeBound


open GlobalTheory.DegreeBound in
theorem GlobalTheory.totalDegree_le_of_integral_at_infinity : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K),
    AlgebraicIndependent ℤ y → ∀ (j : Fin D), y j ≠ 0 → ∀ (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ)
    {ι : Type} (z : ι → K), (∀ i, ∃ (N : ℕ) (C : MvPolynomial (Fin D) ℤ), C.totalDegree ≤ N ∧
    z i * y j ^ N = aeval y C) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic →
    f.eval₂ (aeval z).toRingHom (aeval y T₀ / y j ^ q) = 0 → T₀.totalDegree ≤ q := by
  intro K _ D y hind j hu T₀ q ι z hz f hf heq
  by_contra hlt
  push_neg at hlt
  have hw : y j ^ q ≠ 0 := pow_ne_zero _ hu
  generalize hs : aeval y T₀ / y j ^ q = s at heq
  have ht : aeval y T₀ = s * y j ^ q := by rw [← hs, div_mul_cancel₀ _ hw]
  set c : ℕ → K := fun k => aeval z (f.coeff k) with hc
  have hsum : (∑ k ∈ Finset.range f.natDegree, c k * s ^ k) + s ^ f.natDegree = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree] at heq
    simpa [c] using heq
  generalize hn : f.natDegree = n at hsum
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp at hsum
  obtain ⟨N, hN⟩ := common_order (y := y) (j := j) c (fun k => aeval_good hz (f.coeff k)) n
  have hC : ∀ k, ∃ C : MvPolynomial (Fin D) ℤ, k < n →
      C.totalDegree ≤ N ∧ c k * y j ^ N = aeval y C := by
    intro k
    by_cases hk : k < n
    · obtain ⟨C, h1, h2⟩ := hN k hk; exact ⟨C, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose Cf hCf using hC
  have hT0 : T₀ ≠ 0 := by rintro rfl; simp at hlt
  set A : MvPolynomial (Fin D) ℤ := X j ^ (N * n) * T₀ ^ n with hA
  set B : MvPolynomial (Fin D) ℤ :=
    ∑ k ∈ Finset.range n, Cf k * T₀ ^ k * X j ^ (q * (n - k) + N * (n - 1)) with hB
  have hP : aeval y (B + A) = aeval y (0 : MvPolynomial (Fin D) ℤ) := by
    rw [map_zero]
    have : aeval y (B + A) =
        y j ^ (q * n + N * n) * ((∑ k ∈ Finset.range n, c k * s ^ k) + s ^ n) := by

      rw [mul_add, Finset.mul_sum, map_add (f := _), map_sum]
      congr 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        obtain ⟨m, hm⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
        have h1 : n - k = m + 1 := by omega
        have h2 : n - 1 = k + m := by omega
        rw [map_mul, map_mul, map_pow, map_pow, aeval_X, ht, ← (hCf k hk').2, h1, h2, hm]
        ring
      · rw [hA, map_mul, map_pow, map_pow, aeval_X, ht]
        ring
    rw [this, hsum, mul_zero]
  have hBA : B + A = 0 := algebraicIndependent_iff_injective_aeval.mp hind hP
  have hpow : ∀ m, (T₀ ^ m).totalDegree = m * T₀.totalDegree := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero _ hT0) hT0, ih]; ring
  have hAdeg : A.totalDegree = N * n + n * T₀.totalDegree := by
    rw [hA, totalDegree_mul_of_isDomain (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ hT0),
      totalDegree_X_pow, hpow]
  have hpos : 0 < N * n + n * T₀.totalDegree := by
    have := Nat.mul_pos hnpos (show 0 < T₀.totalDegree by omega); omega
  have hBdeg : B.totalDegree < N * n + n * T₀.totalDegree := by
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hpos)]
    intro k hk
    have hk' := Finset.mem_range.mp hk
    obtain ⟨m, hm⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
    have h1 : n - k = m + 1 := by omega
    have h2 : n - 1 = k + m := by omega
    calc (Cf k * T₀ ^ k * X j ^ (q * (n - k) + N * (n - 1))).totalDegree
        ≤ N + k * T₀.totalDegree + (q * (n - k) + N * (n - 1)) := by
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_X_pow]
          have := (totalDegree_mul (Cf k) (T₀ ^ k)).trans
            (add_le_add (hCf k hk').1 (totalDegree_pow T₀ k))
          linarith
      _ < N * n + n * T₀.totalDegree := by
          rw [h1, h2, hm]
          have h3 : q * (m + 1) < T₀.totalDegree * (m + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.succ_pos m)
          nlinarith
  have hAB : A = -B := eq_neg_of_add_eq_zero_right hBA
  have := congrArg MvPolynomial.totalDegree hAB
  rw [totalDegree_neg, hAdeg] at this
  omega
end

section

open MvPolynomial

namespace GlobalTheory

theorem sumAlgEquiv_rename_inr_eq_C {σ : Type} {L : ℕ} (q : MvPolynomial σ ℂ) :
    MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.rename Sum.inr q) = MvPolynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, sumAlgEquiv_X_inr]

theorem coeff_sumAlgEquiv_mkDerivation_gen {σ : Type} {L : ℕ}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (b : MvPolynomial (Fin L ⊕ σ) ℂ) (m : Fin L →₀ ℕ) :
    AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ
      (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ))
        (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) m =
      D (AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ b) m) := by
  induction b using MvPolynomial.induction_on generalizing m with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Fin L ⊕ σ) ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, map_zero, AddMonoidAlgebra.coeff_zero, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C]
    split_ifs
    · exact (D.map_algebraMap a).symm
    · simp
  | add p q hp hq => simp only [map_add (f := _), MvPolynomial.coeff_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, MvPolynomial.coeff_add]
    rcases i with j | v
    · simp only [mkDerivation_X, Sum.elim_inl, map_zero, mul_zero, AddMonoidAlgebra.coeff_zero,
        sumAlgEquiv_X_inl]
      rw [mul_comm (X j), coeff_mul_X', coeff_mul_X']
      simp only [Finsupp.zero_apply, zero_add]
      split_ifs
      · exact hp _
      · exact (D.map_zero).symm
    · simp only [mkDerivation_X, Sum.elim_inr, sumAlgEquiv_X_inr, sumAlgEquiv_rename_inr_eq_C,
        coeff_C_mul, hp]
      rw [mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (D (X v))),
        mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (X v)), coeff_C_mul, coeff_C_mul,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring

theorem coeff_allOnes_sumAlgEquiv_mkDerivation :
    ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) = D (AddMonoidAlgebra.coeff (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b)) (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ))) :=
  fun D b => coeff_sumAlgEquiv_mkDerivation_gen D b _

end GlobalTheory
end

section

open MvPolynomial

namespace GlobalTheory

theorem optionEquivLeft_rename_some_complex_eq_C {τ : Type} (c : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some c) = Polynomial.C c := by
  induction c using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C, Polynomial.C_eq_algebraMap]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, Polynomial.C_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.optionEquivLeft_X_some, Polynomial.C_mul]

theorem coeff_optionEquivLeft_extDerivation {τ : Type}
    (E : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (k : ℕ) (s : MvPolynomial (Option τ) ℂ) :
    (MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.mkDerivation ℂ (fun w : Option τ => match w with
      | none => (0 : MvPolynomial (Option τ) ℂ)
      | some v => MvPolynomial.rename some (E (MvPolynomial.X v))) s)).coeff k
      = E ((MvPolynomial.optionEquivLeft ℂ τ (s)).coeff k) := by
  induction s using MvPolynomial.induction_on generalizing k with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Option τ) ℂ) = algebraMap ℂ _ a := rfl
    have h2 : (MvPolynomial.C a : MvPolynomial τ ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, ← h1, MvPolynomial.optionEquivLeft_C, Polynomial.coeff_C]
    split_ifs <;> simp [h2, Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p n hp =>
    rw [Derivation.leibniz, MvPolynomial.mkDerivation_X]
    rcases n with _ | v
    · simp only [smul_zero, zero_add, smul_eq_mul, mul_zero, map_mul, MvPolynomial.optionEquivLeft_X_none]
      rcases k with _ | k
      · simp [Polynomial.coeff_mul_X_zero, mul_comm (Polynomial.X) _]
      · rw [mul_comm Polynomial.X, Polynomial.coeff_mul_X, Polynomial.coeff_mul_X, hp]
    · simp only [smul_eq_mul, map_add (f := _), map_mul, MvPolynomial.optionEquivLeft_X_some, optionEquivLeft_rename_some_complex_eq_C,
        Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, hp, Derivation.leibniz]

end GlobalTheory
end

section

namespace GlobalTheory

open MvPolynomial

theorem exists_eval₂_fraction_of_exists_mod_nilpotent : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  intro R B _ _ c J n hn m r hgen
  let S : Subring B :=
    { carrier := {g | ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P}
      mul_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * P₂, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      neg_mem' := by
        rintro a ⟨P, Q, hQ, h⟩
        refine ⟨-P, Q, hQ, ?_⟩
        rw [eval₂_neg, ← h]; ring }
  have hS : ∀ g, g ∈ S ↔ ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P := fun g => Iff.rfl
  have hcS : ∀ a : R, c a ∈ S := fun a => (hS _).2 ⟨C a, 1, by simp, by simp⟩
  set I := Ideal.map c J with hI
  have hdec : ∀ b : B, ∃ s ∈ S, b - s ∈ I := by
    intro b
    obtain ⟨P, Q, hQ, hb⟩ := hgen b
    obtain ⟨u, hu⟩ := hQ
    refine ⟨eval₂ c r P * ↑u⁻¹, (hS _).2 ⟨P, Q, ⟨u, hu⟩, ?_⟩, ?_⟩
    · rw [← hu, mul_assoc, Units.inv_mul, mul_one]
    · have h1 : (↑u⁻¹ : B) * ↑u = 1 := Units.inv_mul u
      have : b - eval₂ c r P * ↑u⁻¹ = ↑u⁻¹ * (b * eval₂ c r Q - eval₂ c r P) := by
        rw [← hu]; linear_combination (-b) * h1
      rw [this]; exact I.mul_mem_left _ hb
  have hstep : ∀ k : ℕ, ∀ x ∈ I ^ k, ∃ s ∈ S, x - s ∈ I ^ (k + 1) := by
    intro k x hx
    have hIk : I ^ k = Ideal.span (c '' ↑(J ^ k)) := by rw [hI, ← Ideal.map_pow]; rfl
    rw [hIk] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, -, rfl⟩ := hy
      exact ⟨c j, hcS j, by simp⟩
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hys⟩ := hy
      obtain ⟨t, ht, hzt⟩ := hz
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      have := Ideal.add_mem _ hys hzt
      convert this using 1; ring
    | smul b y hy ih =>
      obtain ⟨s, hs, hys⟩ := ih
      obtain ⟨t, ht, hbt⟩ := hdec b
      refine ⟨t * s, S.mul_mem ht hs, ?_⟩
      have hy' : y ∈ I ^ k := hIk ▸ hy
      have h1 : (b - t) * y ∈ I ^ (k + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hbt hy'
      have h2 : t * (y - s) ∈ I ^ (k + 1) := Ideal.mul_mem_left _ _ hys
      have := Ideal.add_mem _ h1 h2
      rw [smul_eq_mul]
      convert this using 1; ring
  have hall : ∀ k : ℕ, ∀ g : B, ∃ s ∈ S, g - s ∈ I ^ k := by
    intro k
    induction k with
    | zero => intro g; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro g
      obtain ⟨s, hs, hgs⟩ := ih g
      obtain ⟨t, ht, hxt⟩ := hstep k _ hgs
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      convert hxt using 1; ring
  have hIn : I ^ n = ⊥ := by
    rw [hI, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    exact hn x hx
  intro g
  obtain ⟨s, hs, hgs⟩ := hall n g
  rw [hIn, Ideal.mem_bot, sub_eq_zero] at hgs
  exact (hS g).1 (hgs ▸ hs)

end GlobalTheory
end

section

namespace GlobalTheory.PolynomialEvaluationMembership

theorem pow_apply_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (n : ℕ) :
    ∀ x ∈ W, (g ^ n) x ∈ W := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hW x hx)

theorem aeval_apply_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : Polynomial F) :
    ∀ x ∈ W, (Polynomial.aeval g p) x ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x hx
    rw [map_add (f := _), LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  | monomial n a =>
    intro x hx
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact W.smul_mem a (pow_apply_mem g W hW n x hx)

end GlobalTheory.PolynomialEvaluationMembership
end
