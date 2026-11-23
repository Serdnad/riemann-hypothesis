module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

section

namespace GlobalTheory.JointEigenSupremum

theorem joint_eigen_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M)
    (hE : ∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y)
    (ψ : ι → ℂ) (x : M) (hx0 : x ≠ (0 : M)) (hx : ∀ i, (op i : M → M) x = ψ i • x)
    (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  classical
  by_contra hne
  push_neg at hne
  have hstab : ∀ (s : Finset κ) (i : ι), ∀ z ∈ ⨆ k ∈ s, E k, (op i : M → M) z ∈ ⨆ k ∈ s, E k := by
    intro s i z hz
    have hle : (⨆ k ∈ s, E k) ≤ (⨆ k ∈ s, E k).comap (op i) := by
      refine iSup₂_le fun k hk y hy => ?_
      rw [Submodule.mem_comap, hE k y hy i]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun k (_ : k ∈ s) => E k) k hk) hy)
    exact hle hz
  have key : ∀ s : Finset κ, ∀ x : M, (∀ i, (op i : M → M) x = ψ i • x) →
      x ∈ ⨆ k ∈ s, E k → x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ h; simpa using h
    | insert k0 s hk0 ih =>
      intro x hx h
      rw [Finset.iSup_insert, Submodule.mem_sup] at h
      obtain ⟨y, hy, z, hz, rfl⟩ := h
      obtain ⟨i, hi⟩ : ∃ i, χ k0 i ≠ ψ i := by
        by_contra h'
        push_neg at h'
        exact hne k0 (funext h')
      have hw : (op i : M → M) z - χ k0 i • z ∈ ⨆ k ∈ s, E k :=
        Submodule.sub_mem _ (hstab s i z hz) (Submodule.smul_mem _ _ hz)
      have h1 := hx i
      rw [map_add (f := _), hE k0 y hy i, smul_add] at h1
      have h2 : (op i : M → M) z = ψ i • y + ψ i • z - χ k0 i • y := by
        rw [← h1]; abel
      have hw' : (op i : M → M) z - χ k0 i • z = (ψ i - χ k0 i) • (y + z) := by
        rw [h2]; module
      rw [hw'] at hw
      have heig : ∀ j, (op j : M → M) ((ψ i - χ k0 i) • (y + z)) = ψ j • ((ψ i - χ k0 i) • (y + z)) := by
        intro j
        rw [map_smul, hx j, smul_comm]
      have h0 := ih _ heig hw
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hi
      · exact h
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  exact hx0 (key s x hx hs)

end GlobalTheory.JointEigenSupremum

theorem GlobalTheory.JointEigenSupremum.target : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M), (∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y) → ∀ (ψ : ι → ℂ) (x : M), x ≠ (0 : M) → (∀ (i : ι), (op i : M → M) x = ψ i • x) → x ∈ ⨆ (k : κ), E k → ∃ (k : κ), χ k = ψ :=
  fun op χ E hE ψ x hx0 hx hmem => GlobalTheory.JointEigenSupremum.joint_eigen_mem_iSup op χ E hE ψ x hx0 hx hmem
end

section

open Matrix

namespace GlobalTheory

theorem rat_mem_span_of_real_mem_span (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ)
    (hv : (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ))) :
    v ∈ Submodule.span ℚ (Set.range w) := by
  by_contra hnot
  obtain ⟨f, hfv, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  classical
  set a : Fin r → ℚ := fun j => f (fun k => if j = k then 1 else 0) with ha
  have hf : ∀ x : Fin r → ℚ, f x = ∑ j, x j * a j := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  have hw : ∀ i, f (w i) = 0 := by
    intro i
    have : f (w i) ∈ (Submodule.span ℚ (Set.range w)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    rw [hfp] at this
    exact (Submodule.mem_bot ℚ).mp this
  let L : (Fin r → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ j, x j * (a j : ℝ)
      map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum, mul_assoc] }
  have hle : Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    show ∑ j, ((w i j : ℚ) : ℝ) * (a j : ℝ) = 0
    have h := hw i
    rw [hf] at h
    have h' : ((∑ j, w i j * a j : ℚ) : ℝ) = 0 := by rw [h]; simp
    push_cast at h'
    exact h'
  have h0 : L (fun j => ((v j : ℚ) : ℝ)) = 0 := LinearMap.mem_ker.mp (hle hv)
  have h1 : ((f v : ℚ) : ℝ) = 0 := by
    rw [hf]
    push_cast
    exact h0
  exact hfv (by exact_mod_cast h1)

end GlobalTheory
end

section

universe u_1
namespace GlobalTheory.AevalTotalDegreeBound
open MvPolynomial

theorem aeval_totalDegree_le {σ : Type u_1} (f : σ → MvPolynomial σ ℂ)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (P : MvPolynomial σ ℂ) :
    (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem main : ∀ {σ : Type u_1} (f : σ → MvPolynomial σ ℂ), (∀ (v : σ), MvPolynomial.totalDegree (f v) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial σ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial σ ℂ → MvPolynomial σ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => aeval_totalDegree_le f hf P

end GlobalTheory.AevalTotalDegreeBound
end

section

namespace GlobalTheory.AevalTotalDegreeLinear

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  have hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (totalDegree_pow _ _).trans ?_
    calc s i * totalDegree (f i) ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = s i := mul_one _
  refine hprod.trans ?_
  exact Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs

theorem main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P

end GlobalTheory.AevalTotalDegreeLinear
end

section

open Matrix

namespace GlobalTheory

theorem laurent_poly_eval_of_laurent :
    ∀ (σ : Type) (g : σ → ℂ → ℂ), (∀ a, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * g a t = p.eval t) →
      ∀ Q : MvPolynomial σ ℂ, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 →
        t ^ N * MvPolynomial.eval (fun a => g a t) Q = p.eval t := by
  intro σ g hg Q
  induction Q using MvPolynomial.induction_on
  · rename_i c
    exact ⟨0, Polynomial.C c, fun t _ => by simp⟩
  · rename_i p q hp hq
    obtain ⟨N₁, P₁, h₁⟩ := hp
    obtain ⟨N₂, P₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, Polynomial.X ^ N₂ * P₁ + Polynomial.X ^ N₁ * P₂, fun t ht => ?_⟩
    simp only [map_add (f := _), Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h₁ t ht, ← h₂ t ht]
    ring
  · rename_i p a hp
    obtain ⟨N, P, h⟩ := hp
    obtain ⟨N', P', h'⟩ := hg a
    refine ⟨N + N', P * P', fun t ht => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, Polynomial.eval_mul]
    rw [← h t ht, ← h' t ht]
    ring

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

def twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  C (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
    bind₁ (fun k : ι × Fin n × Fin n => ∑ j : Fin n,
      C (emb k.1 ((M : Matrix (Fin n) (Fin n) E) k.2.1 j)) * X (k.1, j, k.2.2)) P

def polFun {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K) :
    (ι → Matrix (Fin n) (Fin n) K) → K :=
  fun y => eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem polFun_apply {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K)
    (y : ι → Matrix (Fin n) (Fin n) K) : polFun P y = eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P := rfl

open MvPolynomial in
private lemma eval_bind_eq_eval_comp {K σ τ : Type} [CommRing K] (f : σ → MvPolynomial τ K)
    (x : τ → K) (P : MvPolynomial σ K) :
    eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, aeval_bind₁]

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.eval_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (x : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2)
        (_root_.GlobalTheory.IntegralityCompare.twSub emb M s P) =
      (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
        eval (fun k : ι × Fin n × Fin n =>
          (((M : Matrix (Fin n) (Fin n) E).map (emb k.1)) * x k.1) k.2.1 k.2.2) P := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSub, map_mul, eval_C, eval_bind_eq_eval_comp]
  congr 3
  funext k
  simp [Matrix.mul_apply, eval_sum]

end GlobalTheory.IntegralityCompare

end
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.CayleyBlock

def dList {σ : Type} [DecidableEq σ] (l : List σ) : Module.End ℂ (MvPolynomial σ ℂ) :=
  (l.map fun v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
    MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)).prod

def smallList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (τ b j, j)

def bigList {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : List (Fin q × Fin p × Fin p) :=
  (List.finRange q).flatMap fun b => (List.finRange p).map fun j => (b, τ b j, j)

def blockGraph {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : Fin q × Fin p × Fin p →₀ ℕ :=
  ∑ b, ∑ j, Finsupp.single (b, τ b j, j) 1

def sumMap (p q : ℕ) : MvPolynomial (Fin p × Fin p) ℂ →ₐ[ℂ] MvPolynomial (Fin q × Fin p × Fin p) ℂ :=
  aeval fun x => ∑ b, X (b, x.1, x.2)

def blockEmb {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    Fin q × Fin p × Fin p → Fin (p * q) × Fin (p * q) :=
  fun x => (Fintype.equivFinOfCardEq h1 ((), x.2.1, x.1), Fintype.equivFinOfCardEq h1 ((), x.2.2, x.1))

def sgnProd {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : ℤ := ((∏ b, Equiv.Perm.sign (τ b) : ℤˣ) : ℤ)

end GlobalTheory.CayleyBlock
end
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem mono_char_of_mul_poly_div_pow (χ : ℂ → ℂ)
    (hmul : ∀ s t : ℂ, s ≠ 0 → t ≠ 0 → χ (s * t) = χ s * χ t) (h1 : χ 1 = 1) (N : ℕ)
    (p : Polynomial ℂ) (hp : ∀ t : ℂ, t ≠ 0 → t ^ N * χ t = p.eval t) :
    ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ t = t ^ k := by
  have hne : ∀ t : ℂ, t ≠ 0 → χ t ≠ 0 := by
    intro t ht h
    have := hmul t t⁻¹ ht (inv_ne_zero ht)
    rw [mul_inv_cancel₀ ht, h1, h, zero_mul] at this
    exact one_ne_zero this
  have hp0 : p ≠ 0 := by
    intro h
    have := hp 1 one_ne_zero
    rw [h, eval_zero, one_pow, one_mul, h1] at this
    exact one_ne_zero this
  obtain ⟨q, hpq, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  have hq : ∀ t : ℂ, q.eval t ≠ 0 := by
    intro t ht
    by_cases t0 : t = 0
    · subst t0
      apply hdvd
      rw [dvd_iff_isRoot]
      exact ht
    · have := hp t t0
      rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero, ht, mul_zero] at this
      exact mul_ne_zero (pow_ne_zero _ t0) (hne t t0) this
  have hdeg : q.natDegree = 0 := by
    by_contra hd
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hq 0 (eval_zero)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q (by
      rw [degree_eq_natDegree hq0]
      exact_mod_cast hd)
    exact hq z hz
  rw [eq_C_of_natDegree_eq_zero hdeg] at hpq
  have hc : q.coeff 0 = 1 := by
    have := hp 1 one_ne_zero
    rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, one_pow, one_pow,
      one_mul, one_mul, h1] at this
    exact this.symm
  refine ⟨(rootMultiplicity 0 p : ℤ) - N, fun t ht => ?_⟩
  have := hp t ht
  rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_C, sub_zero, hc, mul_one] at this
  rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ ht), mul_comm, this]

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_common_nonzero_of_polynomial_on_lines (V : Type) [AddCommGroup V] [Module ℝ V]
    (ι : Type) [Finite ι] (f : ι → V → ℂ)
    (hpoly : ∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ))
    (hne : ∀ i, ∃ v, f i v ≠ 0) : ∃ v, ∀ i, f i v ≠ 0 := by
  classical
  have _ := Fintype.ofFinite ι
  have key : ∀ t : Finset ι, ∃ v, ∀ i ∈ t, f i v ≠ 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert j t hj ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨w, hw⟩ := hne j
      choose p hp using fun i => hpoly i v (w - v)
      have hp0 : ∀ i ∈ insert j t, p i ≠ 0 := by
        intro i hi h
        rcases Finset.mem_insert.1 hi with hij | hi
        · subst hij
          apply hw
          have := hp i 1
          simpa [h] using this
        · apply hv i hi
          have := hp i 0
          simpa [h] using this
      have hfin : Set.Finite (⋃ i ∈ (insert j t : Finset ι),
          (fun s : ℝ => (s : ℂ)) ⁻¹' {z | (p i).IsRoot z}) :=
        Set.Finite.biUnion (Finset.finite_toSet _) fun i hi =>
          (Polynomial.finite_setOf_isRoot (hp0 i hi)).preimage Complex.ofReal_injective.injOn
      obtain ⟨s, hs⟩ := hfin.exists_notMem
      refine ⟨v + s • (w - v), fun i hi => ?_⟩
      rw [hp i s]
      intro h0
      apply hs
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨i, hi, h0⟩
  obtain ⟨v, hv⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i)⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace

namespace GlobalTheory


open Scheme.IdealSheafData in
theorem vanishingIdeal_comap_of_isOpenImmersion : ∀ (A X : Scheme.{0}) (g : A ⟶ X) [IsOpenImmersion g] (B : Closeds X) (B' : Closeds A), (∀ x : A, x ∈ B' ↔ g x ∈ B) → (Scheme.IdealSheafData.vanishingIdeal B).comap g = Scheme.IdealSheafData.vanishingIdeal B' := by
  intro A X g _ B B' h
  have hB : (vanishingIdeal B).support = B := by
    ext x
    simp
  have hr : (vanishingIdeal B).radical = vanishingIdeal B := by
    rw [← vanishingIdeal_support, hB]
  have hs : ((vanishingIdeal B).comap g).support = B' := by
    ext x
    simp [support_comap, h]
  rw [← hs, vanishingIdeal_support]
  ext U : 2
  rw [radical_ideal, ideal_comap_of_isOpenImmersion, ← Ideal.comap_radical, ← radical_ideal, hr]

end GlobalTheory
end
