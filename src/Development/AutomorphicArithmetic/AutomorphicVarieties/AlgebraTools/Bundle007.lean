module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle001
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.Idempotents
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle005
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem pullback_fin_relation {k C : Type} [Field k] [CommRing C] [Algebra k C] (S : Subalgebra k C)
    [Module.Finite k S] (T : Set C) (hT : T ⊆ S) (hfg : (Ideal.span T).FG)
    (hI : ∀ x ∈ Ideal.span T, IsUnit (1 - x))
    (hd : ∀ (n : ℕ) (c : C), ∃ a ∈ S, ∃ s ∈ S, IsUnit s ∧ s * c - a ∈ Ideal.span T ^ n) :
    Module.Finite k C := by
  set J := Ideal.span T with hJ
  have hinv : ∀ s ∈ S, IsUnit s → ∃ t ∈ S, t * s = 1 := by
    intro s hsS hs
    let f : S →ₗ[k] S := LinearMap.mulLeft k (⟨s, hsS⟩ : S)
    have hfi : Function.Injective f := by
      intro x y hxy
      have h1 : s * (x : C) = s * (y : C) := congrArg Subtype.val hxy
      exact Subtype.ext (hs.mul_left_cancel h1)
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hfi) 1
    refine ⟨y, y.2, ?_⟩
    have h2 : s * (y : C) = 1 := congrArg Subtype.val hy
    rw [mul_comm]
    exact h2
  have hC : ∀ (n : ℕ) (c : C), ∃ a ∈ S, c - a ∈ J ^ n := by
    intro n c
    obtain ⟨a, haS, s, hsS, hs, hmem⟩ := hd n c
    obtain ⟨t, htS, hts⟩ := hinv s hsS hs
    refine ⟨t * a, S.mul_mem htS haS, ?_⟩
    have e : c - t * a = t * (s * c - a) := by
      calc c - t * a = (t * s) * c - t * a := by rw [hts, one_mul]
        _ = t * (s * c - a) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ t hmem
  let W : ℕ → Submodule k S := fun n =>
    Submodule.comap S.val.toLinearMap ((J ^ n).restrictScalars k)
  have hWmem : ∀ n (x : S), x ∈ W n ↔ (x : C) ∈ J ^ n := fun n x => Iff.rfl
  have hWle : ∀ n, W (n + 1) ≤ W n := by
    intro n x hx
    rw [hWmem] at hx ⊢
    exact Ideal.pow_le_pow_right (Nat.le_succ n) hx
  obtain ⟨n0, hn0⟩ : ∃ n0, W n0 ≤ W (n0 + 1) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ n, Module.finrank k (W (n + 1)) < Module.finrank k (W n) := by
      intro n
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hWle n) (fun h => hcon n h.ge))
    have hbd : ∀ n, n + Module.finrank k (W n) ≤ Module.finrank k (W 0) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        have := hlt m
        omega
    have := hbd (Module.finrank k (W 0) + 1)
    omega
  have hstep : J ^ n0 ≤ J ^ (n0 + 1) := by
    intro x hx
    obtain ⟨a, haS, hxa⟩ := hC (n0 + 1) x
    have haJ : a ∈ J ^ n0 := by
      have h1 : x - a ∈ J ^ n0 := Ideal.pow_le_pow_right (Nat.le_succ n0) hxa
      have h2 := Ideal.sub_mem _ hx h1
      simpa using h2
    have ha1 : a ∈ J ^ (n0 + 1) := (hWmem (n0 + 1) ⟨a, haS⟩).mp (hn0 ((hWmem n0 ⟨a, haS⟩).mpr haJ))
    have h3 := Ideal.add_mem _ hxa ha1
    simpa using h3
  have hzero : J ^ n0 = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot J (J ^ n0) (Ideal.FG.pow (n := n0) hfg)
    · rw [smul_eq_mul, ← pow_succ']
      exact hstep
    · intro x hx
      rw [Ideal.mem_jacobson_bot]
      intro y
      have h := hI (-(x * y)) (J.neg_mem (J.mul_mem_right y hx))
      rw [sub_neg_eq_add, add_comm] at h
      exact h
  have hsurj : Function.Surjective S.val.toLinearMap := by
    intro c
    obtain ⟨a, haS, hca⟩ := hC n0 c
    rw [hzero, Ideal.mem_bot, sub_eq_zero] at hca
    exact ⟨⟨a, haS⟩, hca.symm⟩
  exact Module.Finite.of_surjective _ hsurj
end

section

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section ULim

variable {ι R : Type} [CommRing R] (F : Filter ι) (I : ℕ → Ideal R)
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

def uNull : Submodule R (∀ i, M i) where
  carrier := {p | ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i))}
  add_mem' ha hb j := ((ha j).and (hb j)).mono fun _ h => add_mem h.1 h.2
  zero_mem' _ := Eventually.of_forall fun _ => zero_mem _
  smul_mem' c _ h j := (h j).mono fun _ h => Submodule.smul_mem _ c h


abbrev ULim : Type := (∀ i, M i) ⧸ uNull F I M

def ULim.mk : (∀ i, M i) →ₗ[R] ULim F I M := (uNull F I M).mkQ

theorem ULim.mk_surjective : Function.Surjective (ULim.mk F I M) := Submodule.mkQ_surjective _

variable {F I M} in
theorem ULim.mk_eq_zero {p : ∀ i, M i} :
    ULim.mk F I M p = 0 ↔ ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i)) := by
  show (uNull F I M).mkQ p = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl


variable {I M} in
def ULim.map {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) : ULim F I M →ₗ[R] ULim F I' M' :=
  Submodule.mapQ _ _ (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) fun p hp j =>
    (hp j).mono fun i hi => by
      have h1 : f i (p i) ∈ Submodule.map (f i) (I j • ⊤ : Submodule R (M i)) := ⟨_, hi, rfl⟩
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono (h j) le_top h1

variable {I M} in
theorem ULim.map_mk {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) (p : ∀ i, M i) :
    ULim.map F h f (ULim.mk F I M p) = ULim.mk F I' M' fun i => f i (p i) := rfl

def ULim.scal (r : ι → R) : ULim F I M →ₗ[R] ULim F I M :=
  ULim.map F (fun _ => le_rfl) fun i => r i • LinearMap.id



end ULim

section QReg

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def QRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) (J : Ideal R) (a : ℕ) : Prop :=
  ∀ c : GlobalTheory.MonoDeg σ a → M,
    ∑ α, GlobalTheory.monoVal y α.1 • c α ∈ ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule R M) →
      ∀ α, c α ∈ ((Ideal.span (Set.range y) ⊔ J) • ⊤ : Submodule R M)

theorem isQuasiRegularSeq_iff_qRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) :
    GlobalTheory.IsQuasiRegularSeq M y ↔ ∀ a, QRegAt M y ⊥ a := by
  unfold GlobalTheory.IsQuasiRegularSeq QRegAt
  simp only [sup_bot_eq]

end QReg

end UpperTheory.V.AlgebraTools
end
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_map :
    ∀ {R R' E E' ι : Type} [CommRing R] [CommRing R'] [Ring E] [Ring E'] [Algebra R E] [Algebra R' E'] [Fintype ι] [DecidableEq ι] (φ : R →+* R') (π : E →+* E') (a : ι → R) (P : E), (∀ c, π (algebraMap R E c) = algebraMap R' E' (φ c)) → (∀ i j, i ≠ j → IsUnit (a i - a j)) → ∀ i, π (lag a P i) = lag (fun j => φ (a j)) (π P) i := by
  intro R R' E E' ι _ _ _ _ _ _ _ _ φ π a P hc ha i
  have key : ∀ q : R[X], π (aeval P q) = aeval (π P) (q.map φ) := by
    intro q
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext hc
  have hsm : ∀ (c : R) (x : E), π (c • x) = φ c • π x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
  have h0 := (eq_lag_iff a P i (fun j hj => ha i j (Ne.symm hj)) (lag a P i)).1 rfl
  have h1 := congrArg π h0
  rw [hsm, key] at h1
  simp only [map_prod, Polynomial.map_prod, map_sub, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at h1
  rw [eq_lag_iff (fun j => φ (a j)) (π P) i (fun j hj => by
      rw [← map_sub]; exact (ha i j (Ne.symm hj)).map φ) (π (lag a P i))]
  exact h1
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_coi :
    ∀ {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] (a : ι → R) (P : E), (∀ i j, i ≠ j → IsUnit (a i - a j)) → aeval P (∏ i, (X - C (a i))) = 0 → CompleteOrthogonalIdempotents (lag a P) ∧ (∀ i, P * lag a P i = a i • lag a P i) ∧ (∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i) ∧ ∀ y i, Commute y P → Commute y (lag a P i) := by
  intro R E ι _ _ _ _ _ a P ha hm
  have hc : ∀ i, IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := fun i =>
    IsUnit.prod_iff.2 (fun j hj => ha i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  let L : ι → R[X] := fun i =>
    C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))
  have hL : ∀ i, lag a P i = aeval P (L i) := by
    intro i
    simp only [L, lag, map_mul, aeval_C, Algebra.smul_def]
  have hLe : ∀ i k, (L i).eval (a k) = if i = k then 1 else 0 := by
    intro i k
    simp only [L, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with h
    · subst h
      exact Ring.inverse_mul_cancel _ (hc i)
    · rw [Finset.prod_eq_zero (f := fun j => a k - a j)
        (Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ k⟩) (sub_self (a k)), mul_zero]
  have hroot : ∀ i, aeval P (X - C (a i)) * lag a P i = 0 := by
    intro i
    rw [hL, ← map_mul]
    have : (X - C (a i)) * L i =
        C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j, (X - C (a j)) := by
      simp only [L]
      rw [mul_left_comm, Finset.mul_prod_erase Finset.univ (fun j => X - C (a j)) (Finset.mem_univ i)]
    rw [this, map_mul, hm, mul_zero]
  have hq : ∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i := by
    intro q i
    obtain ⟨g, hg⟩ := (X_sub_C_dvd_sub_C_eval : X - C (a i) ∣ q - C (q.eval (a i)))
    have hq' : q = g * (X - C (a i)) + C (q.eval (a i)) := by
      rw [mul_comm, ← hg]
      ring
    conv_lhs => rw [hq']
    rw [map_add (f := _), map_mul, add_mul, mul_assoc, hroot, mul_zero, zero_add, aeval_C, Algebra.smul_def]
  have hP : ∀ i, P * lag a P i = a i • lag a P i := by
    intro i
    have := hq X i
    rwa [aeval_X, eval_X] at this
  have hcomm : ∀ y i, Commute y P → Commute y (lag a P i) := by
    intro y i hy
    rw [hL]
    generalize L i = f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
    | monomial n c =>
      rw [aeval_monomial]
      exact Commute.mul_right (show Commute y (algebraMap R E c) from (Algebra.commutes c y).symm)
        (hy.pow_right n)
  have hsum : ∑ i, lag a P i = 1 := by
    have h1 : ∏ i, (X - C (a i)) ∣ 1 - ∑ i, L i := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        exact isCoprime_X_sub_C_of_isUnit_sub (ha i j hij)
      · intro k _
        rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_one, eval_finsetSum]
        simp only [hLe, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    obtain ⟨g, hg⟩ := h1
    have h2 := congrArg (aeval P) hg

    rw [map_mul, hm, zero_mul, map_sub, map_one, map_sum, sub_eq_zero] at h2
    simp only [hL]
    exact h2.symm
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, hsum⟩, hP, hq, hcomm⟩
  · show lag a P i * lag a P i = lag a P i
    have := hq (L i) i
    rw [← hL, hLe, if_pos rfl, one_smul] at this
    exact this
  · have := hq (L i) j
    rw [← hL, hLe, if_neg hij, zero_smul] at this
    exact this
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem exists_lt_apply {n : ℕ} (w : Perm (Fin n)) (hw : w ≠ 1) : ∃ i, i < w i := by
  by_contra h
  push_neg at h
  apply hw
  have hs : ∑ i, (w i).val = ∑ i : Fin n, i.val := Equiv.sum_comp w (fun i => i.val)
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), (w i).val ≤ i.val := fun i _ => h i
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hs
  exact Equiv.ext fun i => Fin.ext (by simpa using heq i (Finset.mem_univ _))

theorem UpperTheory.V.AlgebraTools.hkDualEx :
    ∀ (R : Type) [CommRing R] (n : ℕ), ∃ (ι : Type) (_ : Fintype ι) (a b : ι → MvPolynomial (Fin n) R), IsDual a b := by
  intro R _ n
  refine ⟨Finset (Fin n × Fin n), inferInstance,
    fun t => if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0,
    fun t => ∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R), ?_⟩
  intro w
  have hsum : ∑ t : Finset (Fin n × Fin n), (if t ⊆ pairs n then ∏ p ∈ t, (X p.2 : MvPolynomial (Fin n) R) else 0) *
      rename w (∏ p ∈ pairs n \ t, (-X p.1 : MvPolynomial (Fin n) R)) =
      ∏ p ∈ pairs n, ((X p.2 : MvPolynomial (Fin n) R) + -X (w p.1)) := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun t : Finset (Fin n × Fin n) => t ⊆ pairs n) = (pairs n).powerset := by
      ext t
      simp
    rw [hf, Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [map_prod, rename_X]
  refine hsum.trans ?_
  split_ifs with h1
  · subst h1
    rw [De]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [sub_eq_add_neg]
  · obtain ⟨i, hi⟩ := exists_lt_apply w h1
    apply Finset.prod_eq_zero (i := (i, w i))
    · simp [pairs, hi]
    · simp
end

section

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem de_eq_det (R : Type) [CommRing R] (n : ℕ) :
    De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
  rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp

private theorem nn_ne (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) : NN n q ≠ 0 := by
  rw [NN, Finset.prod_ne_zero_iff]
  intro p hp
  have hlt : p.1 < p.2 := by simpa [pairs] using hp
  intro h
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single p.2 1)) h
  rw [MvPolynomial.coeff_sub, coeff_C_mul, coeff_X, coeff_X] at hc
  simp [Finsupp.single_left_inj one_ne_zero, hlt.ne] at hc

theorem UpperTheory.V.AlgebraTools.hkDe :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), De R n ≠ 0 ∧ (∀ w : Perm (Fin n), rename w (De R n) = Perm.sign w • De R n) ∧ ∀ q : R, NN n q ≠ 0 := by
  intro R _ _ n
  refine ⟨?_, ?_, nn_ne R n⟩
  · rw [de_eq_det, Matrix.det_vandermonde_ne_zero_iff]
    exact X_injective
  · intro w
    rw [de_eq_det, AlgHom.map_det]
    have hm : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)) =
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).submatrix w id := by
      ext i j
      simp [Matrix.vandermonde_apply]
    rw [hm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.det_mem_of_rel :
    ∀ (P : Type) [CommRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P)
      (Q : Ideal P), Q.IsPrime → relIdeal z m ≤ Q → (∃ j, m j ∉ Q) → detIdeal z m ≤ Q := by
  intro P _ ι _ _ z m Q hQ hrel ⟨j, hj⟩
  have hzm : ∀ k, z.mulVec m k ∈ Q := fun k => hrel (Ideal.subset_span ⟨k, rfl⟩)
  have hdet : z.det * m j ∈ Q := by
    have h1 : (z.adjugate.mulVec (z.mulVec m)) j = z.det * m j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [← h1, Matrix.mulVec, dotProduct]
    exact Q.sum_mem fun k _ => Q.mul_mem_left _ (hzm k)
  have hd : z.det ∈ Q := (hQ.mem_or_mem hdet).resolve_right hj
  exact sup_le hrel ((Ideal.span_singleton_le_iff_mem _).mpr hd)
end

section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem units_x_mul_ep_and_st_idempotent_identities {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (i : ι) :
    U.x i * U.ep i = U.x i ∧ U.ep (o i) * U.x i = U.x i ∧ T.st (U.x i) * U.ep (o i) = T.st (U.x i) ∧ U.ep i * T.st (U.x i) = T.st (U.x i) := by
  have hr : U.x i * U.ep i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    rw [mul_assoc _ (U.ep i) (U.ep i), (U.coi.idem i).eq]
  have hl : U.ep (o i) * U.x i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    simp only [← mul_assoc, (U.coi.idem (o i)).eq]
  refine ⟨hr, hl, ?_, ?_⟩
  · have h := congrArg T.st hl
    rwa [T.st_mul, U.st_ep] at h
  · have h := congrArg T.st hr
    rwa [T.st_mul, U.st_ep] at h

theorem UpperTheory.V.AlgebraTools.units_basic :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o), (∀ i j, i ≠ j → U.x i * T.st (U.x j) = 0) ∧ ∑ i, T.st (U.x i) * U.x i = 1 ∧ (∀ i j y, i ≠ j → T.tr (U.ep i * y * U.ep j) = 0) ∧ (∀ y, T.tr y = ∑ i, T.tr (U.x i * y * T.st (U.x i))) ∧ (∀ i j y, o i = o j → U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i)) ∧ (∀ y, y = ∑ i, ∑ j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j) ∧ ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
  intro B E _ _ _ T ι _ _ o U
  have key : ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
    intro i j y
    obtain ⟨-, hl, hs, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, hs', -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    simp only [← mul_assoc]
    rw [hl, mul_assoc _ (T.st (U.x j)), hs']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, key⟩
  · intro i j h
    obtain ⟨hr, -, -, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, -, hs⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    rw [← hr, ← hs, mul_assoc, ← mul_assoc (U.ep i), U.coi.ortho h, zero_mul, mul_zero]
  · simp_rw [U.st_mul_x_eq]
    exact U.coi.complete
  · intro i j y h
    rw [T.tr_comm, ← mul_assoc, U.coi.ortho (Ne.symm h), zero_mul, map_zero]
  · intro y
    have h : ∀ i, T.tr (U.x i * y * T.st (U.x i)) = T.tr (U.ep i * y) := by
      intro i
      rw [T.tr_comm, ← mul_assoc, U.st_mul_x_eq]
    simp_rw [h]

    rw [← map_sum, ← Finset.sum_mul, U.coi.complete, one_mul]
  · intro i j y h
    have h7 := key i j y
    rw [← h] at h7
    calc U.x i * y * T.st (U.x j)
        = U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i) := h7.symm
      _ = T.tr (U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i)) • U.ep (o i) := U.corner_eq _ _
      _ = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i) := by rw [h7]
  · intro y
    have h : ∀ i j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j = U.ep i * y * U.ep j := by
      intro i j
      rw [← U.st_mul_x_eq i, ← U.st_mul_x_eq j]
      simp only [mul_assoc]
    simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul, U.coi.complete, mul_one, one_mul]
end
