module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

open MvPolynomial

theorem norm_comp_homogeneous_isHomogeneous :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (n d : ℕ)
      (f : MvPolynomial (Fin n) L), f.IsHomogeneous d →
      ∃ F : MvPolynomial (Fin n × Fin (Module.finrank K L)) K,
        F.IsHomogeneous (d * Module.finrank K L) ∧
        ∀ y : Fin n × Fin (Module.finrank K L) → K, MvPolynomial.eval y F =
          Algebra.norm K (MvPolynomial.eval
            (fun i => ∑ j, algebraMap K L (y (i, j)) * Module.finBasis K L j) f) := by
  intro K L _ _ _ _ n d f hf
  classical
  set m := Module.finrank K L
  set b := Module.finBasis K L
  let g : Fin n → MvPolynomial (Fin n × Fin m) L := fun i => ∑ j, X (i, j) * C (b j)
  have hg : ∀ i, (g i).IsHomogeneous 1 := by
    intro i
    refine IsHomogeneous.sum _ _ _ (fun j _ => ?_)
    simpa using (isHomogeneous_X L (i, j)).mul (isHomogeneous_C _ (b j))
  let G : MvPolynomial (Fin n × Fin m) L := bind₁ g f
  have hG : G.IsHomogeneous d := by simpa [G, aeval_eq_bind₁] using hf.aeval g hg
  have hGev : ∀ y : Fin n × Fin m → K, eval (fun p => algebraMap K L (y p)) G =
      eval (fun i => ∑ j, algebraMap K L (y (i, j)) * b j) f := by
    intro y
    have key : ∀ (φ : MvPolynomial (Fin n) L) (x : Fin n × Fin m → L),
        eval x (bind₁ g φ) = eval (fun i => eval x (g i)) φ := by
      intro φ x
      induction φ using MvPolynomial.induction_on <;> simp_all [bind₁_X_right]
    rw [show G = bind₁ g f from rfl, key]
    congr 2
    funext i
    simp [g]
    rfl
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n × Fin m) K) :=
    fun i j => ∑ s ∈ G.support, monomial s (Algebra.leftMulMatrix b (AddMonoidAlgebra.coeff G s) i j)
  have hM : ∀ i j, (M i j).IsHomogeneous d := by
    intro i j
    refine IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ ?_)
    have := hG (mem_support_iff.mp hs)
    rwa [Finsupp.degree_eq_weight_one]
  refine ⟨M.det, ?_, ?_⟩
  · rw [Matrix.det_apply']
    refine IsHomogeneous.sum _ _ _ (fun σ _ => ?_)
    have hp : (∏ i, M (σ i) i).IsHomogeneous (d * m) := by
      have := IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => d) (fun i _ => hM _ _)
      simpa [mul_comm] using this
    have hε : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin m) K).IsHomogeneous 0 := by
      rw [← map_intCast (C : K →+* MvPolynomial (Fin n × Fin m) K)]
      exact isHomogeneous_C _ _
    simpa using hε.mul hp
  · intro y
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b, ← hGev]
    congr 1
    ext i j
    show eval y (M i j) = _

    simp only [M, map_sum, eval_monomial]

    rw [eval_eq' _ G, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : AddMonoidAlgebra.coeff G s * ∏ k, (algebraMap K L (y k)) ^ (s k) = (∏ k, y k ^ s k) • AddMonoidAlgebra.coeff G s := by
      rw [Algebra.smul_def, mul_comm]
      simp [map_prod, map_pow]
    rw [this, map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm, Finsupp.prod_fintype]
    simp

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem exists_linearIndependent_finCons_of_lt {G : Type} [AddCommGroup G] {m k : ℕ}
    (e : Fin m → G) (he : LinearIndependent ℤ e) (f : Fin k → G) (hf : LinearIndependent ℤ f)
    (hmk : m < k) : ∃ j, LinearIndependent ℤ (Fin.cons (f j) e : Fin m.succ → G) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hc : ∀ j, ∃ c : ℤ, c ≠ 0 ∧ c • f j ∈ Submodule.span ℤ (Set.range e) := by
    intro j
    by_contra h
    push_neg at h
    apply hcon j
    refine LinearIndependent.finCons' (f j) e he fun c y hy hxy => ?_
    by_contra hc0
    apply h c hc0
    have : c • f j = -y := eq_neg_of_add_eq_zero_left hxy
    rw [this]
    exact Submodule.neg_mem _ hy
  choose c hc0 hcs using hc
  have hg : LinearIndependent ℤ (fun j => c j • f j) := by
    rw [Fintype.linearIndependent_iff] at hf ⊢
    intro a ha j
    have := hf (fun j => a j * c j) (by simpa [mul_smul] using ha) j
    exact (mul_eq_zero.mp this).resolve_right (hc0 j)
  have hle := linearIndependent_le_span_aux' (fun j => c j • f j) hg (Set.range e)
    (by rintro _ ⟨j, rfl⟩; exact hcs j)
  have h2 : Fintype.card (Set.range e) = m := by
    rw [Set.card_range_of_injective he.injective, Fintype.card_fin]
  rw [h2, Fintype.card_fin] at hle
  omega

theorem exists_linearIndependent_extend_with_levels {G : Type} [AddCommGroup G] (S : ℕ → Set G) {k : ℕ} (f : Fin k → G)
    (hf : LinearIndependent ℤ f) (hfS : ∀ j, f j ∈ S 0) (m : ℕ) (e : Fin m → G) (n : Fin m → ℕ)
    (he : LinearIndependent ℤ e) (heS : ∀ j, e j ∈ S (n j)) :
    ∀ k', m ≤ k' → k' ≤ k → ∃ (e2 : Fin k' → G) (n2 : Fin k' → ℕ), LinearIndependent ℤ e2 ∧
      (∀ j, e2 j ∈ S (n2 j)) ∧ ∑ j, n2 j = ∑ j, n j := by
  intro k' hm
  induction k', hm using Nat.le_induction with
  | base => intro _; exact ⟨e, n, he, heS, rfl⟩
  | succ k' hmk ih =>
    intro hk
    obtain ⟨e2, n2, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨j, hj⟩ := exists_linearIndependent_finCons_of_lt e2 h1 f hf (by omega)
    refine ⟨Fin.cons (f j) e2, Fin.cons 0 n2, hj, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hfS j
      · simpa using h2 i
    · rw [Fin.sum_cons, zero_add, h3]

theorem exists_linearIndependent_adapted_to_decreasing_chain : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ),
    (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) →
    (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ),
      LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧
      ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  intro G _ _ S hS N
  induction N generalizing S with
  | zero =>
    intro r hr _
    obtain ⟨e, he, heS⟩ := hr 0
    exact ⟨e, fun _ => 0, he, heS, by simp⟩
  | succ N ih =>
    intro r hr hrd
    obtain ⟨e', n', he', heS', hsum⟩ := ih (fun i => S (i + 1)) (fun i => hS (i + 1))
      (fun i => r (i + 1)) (fun i => hr (i + 1)) (fun i => hrd (i + 1))
    obtain ⟨f, hf, hfS⟩ := hr 0
    obtain ⟨e, n, he, heS, hn⟩ := exists_linearIndependent_extend_with_levels S f hf hfS (r (0 + 1)) e' (fun j => n' j + 1) he'
      heS' (r 0) (hrd 0) le_rfl
    refine ⟨e, n, he, heS, ?_⟩
    rw [Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum hn ⊢
    omega

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory.TraceGram

theorem pow_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : ∀ i j, g i j ∈ O) (k : ℕ) : ∀ i j, (g ^ k) i j ∈ O := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (ih i l) (hg l j)

theorem adjugate_entry_mem {K : Type} [Field K] (O : Subring K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by
  intro i j
  let G' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨G i j, hG i j⟩
  have h : O.subtype.mapMatrix G' = G := by
    ext i j; rfl
  rw [← h, ← RingHom.map_adjugate]
  exact (G'.adjugate i j).2

theorem entry_mem_of_trace_gram : ∀ {K : Type} [Field K] (O : Subring K) {n : ℕ} (g x : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
    x = ∑ i, c i • g ^ (i : ℕ) → (∀ i j, g i j ∈ O) → (∀ j : Fin n, (x * g ^ (j : ℕ)).trace ∈ O) →
    (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det ≠ 0 →
    ((Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ O → ∀ i j, x i j ∈ O := by
  intro K _ O n g x c hx hg htr hdet hinv
  set G : Matrix (Fin n) (Fin n) K := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hG : ∀ i j, G i j ∈ O := by
    intro i j
    simp only [hGdef, Matrix.of_apply, Matrix.trace, Matrix.diag_apply]
    exact O.sum_mem fun l _ => pow_entry_mem O g hg _ l l
  have hb : ∀ j, (c ᵥ* G) j ∈ O := by
    intro j
    have : (c ᵥ* G) j = (x * g ^ (j : ℕ)).trace := by
      rw [hx, Finset.sum_mul, Matrix.trace_sum]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply, smul_mul_assoc,
        Matrix.trace_smul, smul_eq_mul, pow_add]
    rw [this]; exact htr j
  have hc : ∀ i, c i ∈ O := by
    intro i
    have h1 : (c ᵥ* G) ᵥ* G.adjugate = G.det • c := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have h2 : c i = (G.det)⁻¹ * ((c ᵥ* G) ᵥ* G.adjugate) i := by
      rw [h1, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
    rw [h2]
    refine O.mul_mem hinv ?_
    change ∑ l, (c ᵥ* G) l * G.adjugate l i ∈ O
    exact O.sum_mem fun l _ => O.mul_mem (hb l) (adjugate_entry_mem O G hG l i)
  intro i j
  rw [hx, Matrix.sum_apply]
  refine O.sum_mem fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact O.mul_mem (hc l) (pow_entry_mem O g hg _ i j)

end GlobalTheory.TraceGram
end

section

open Matrix Finset

namespace GlobalTheory.DetDeriv

theorem derivation_prod {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    {ι : Type} [DecidableEq ι] (δ : Derivation K R R) (s : Finset ι) (f : ι → R) :
    δ (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * δ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha, Derivation.leibniz, ih,
      add_comm, Finset.smul_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      smul_eq_mul]
    ring

theorem derivation_det_rows {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ t, (M.updateRow t fun u => δ (M t u)).det := by
  have key : ∀ N : Matrix ι ι R,
      N.det = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, N i (σ i) := by
    intro N
    rw [← det_transpose, det_apply']
    rfl

  simp only [key, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, δ.map_intCast, smul_zero, add_zero, smul_eq_mul, ← Finset.mul_sum,
    derivation_prod]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), updateRow_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [updateRow_ne (Finset.ne_of_mem_erase hi)]

theorem det_updateRow_eq_sum_adjugate {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (t : ι) (v : ι → R) :
    (M.updateRow t v).det = ∑ j, M.adjugate j t * v j := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, mulVec]
  simp [dotProduct, transpose_apply]

theorem derivation_det {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  rw [derivation_det_rows]
  exact Finset.sum_congr rfl fun i _ => det_updateRow_eq_sum_adjugate M i _

theorem main : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R),
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) :=
  fun δ _ _ _ M => derivation_det δ M

end GlobalTheory.DetDeriv
end

section

namespace GlobalTheory.PiolaAlg

open Finset Matrix

variable {K R : Type} [CommRing K] [CommRing R] [Algebra K R]

theorem derivation_prod {ι : Type} [DecidableEq ι] (D : Derivation K R R) (f : ι → R) (s : Finset ι) :
    D (∏ i ∈ s, f i) = ∑ k ∈ s, ∏ i ∈ s, Function.update f k (D (f k)) i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, prod_insert ha, Function.update_self,
      prod_congr rfl (fun i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _)]
    simp only [smul_eq_mul, mul_sum]
    rw [add_comm, mul_comm (∏ i ∈ s, f i)]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [prod_insert ha, Function.update_of_ne (ne_of_mem_of_not_mem hk ha).symm]

theorem derivation_det {ι : Type} [Fintype ι] [DecidableEq ι] (D : Derivation K R R)
    (A : Matrix ι ι R) :
    D A.det = ∑ k, (A.updateRow k fun l => D (A k l)).det := by

  simp only [det_apply, map_sum]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
  · simp only [h, one_smul, Units.neg_smul, map_neg, sum_neg_distrib, neg_inj]
    rw [derivation_prod]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine sum_congr rfl fun k _ => prod_congr rfl fun i _ => ?_
    by_cases hik : i = k
    · subst hik; simp [updateRow_apply]
    · rw [Function.update_of_ne hik, updateRow_apply, if_neg (σ.injective.ne hik)]

theorem piola {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R)
    (M : Matrix ι ι R) (hM : ∀ h i j, δ h (M i j) = δ i (M h j)) (j : ι) :
    ∑ i, δ i (M.adjugate j i) = 0 := by
  set f : ι × ι → R := fun p =>
    ((M.updateRow p.1 (Pi.single j 1)).updateRow p.2
      fun l => δ p.1 ((M.updateRow p.1 (Pi.single j 1)) p.2 l)).det with hf
  have hS : ∑ i, δ i (M.adjugate j i) = ∑ p ∈ univ ×ˢ univ, f p := by
    rw [sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [adjugate_apply, derivation_det]
  have hdiag : ∀ i, f (i, i) = 0 := by
    intro i
    refine det_eq_zero_of_row_eq_zero i fun l => ?_
    simp only [updateRow_self]
    by_cases hl : l = j
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hpair : ∀ i k, i ≠ k → f (i, k) + f (k, i) = 0 := by
    intro i k hik
    set D : ι → R := fun l => δ i (M k l) with hD
    have h1 : f (i, k) = ((M.updateRow i (Pi.single j 1)).updateRow k D).det := by
      simp only [hf]
      congr 2
      funext l
      rw [updateRow_ne (Ne.symm hik)]
    have h2 : f (k, i) = (((M.updateRow i (Pi.single j 1)).updateRow k D).submatrix
        (Equiv.swap i k) id).det := by
      simp only [hf]
      congr 1
      ext a b
      simp only [submatrix_apply, id, updateRow_apply, updateRow_ne hik, hD]
      by_cases hai : a = i
      · subst hai; simp [Equiv.swap_apply_left, hik, Ne.symm hik, hM]
      · by_cases hak : a = k
        · subst hak; simp [Equiv.swap_apply_right, hik, Ne.symm hik]
        · rw [Equiv.swap_apply_of_ne_of_ne hai hak]; simp [hai, hak]
    rw [h1, h2, det_permute, Equiv.Perm.sign_swap hik]
    simp
  rw [hS]
  refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · rintro ⟨i, k⟩ _
    by_cases hik : i = k
    · subst hik; simp [hdiag]
    · exact hpair i k hik
  · rintro ⟨i, k⟩ _ hne heq
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    rw [heq.1] at hne
    exact hne (hdiag i)
  · intro p _; simp
  · intro p _; simp

theorem piola_identity : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (δ : ι → Derivation K R R) (M : Matrix ι ι R),
    (∀ h i j, δ h (M i j) = δ i (M h j)) → ∀ j, ∑ i, δ i (M.adjugate j i) = 0 :=
  fun δ M hM j => piola δ M hM j

end GlobalTheory.PiolaAlg
end

section

namespace GlobalTheory.IntertwinerCoprimeCharpoly

open Polynomial

theorem pow_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (n : ℕ) :
    C * A ^ n = B ^ n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

theorem aeval_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (p : K[X]) :
    C * aeval A p = aeval B p * C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, pow_intertwine A B C h n]

theorem eq_zero_of_intertwine_of_isCoprime_charpoly {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hcop : IsCoprime (Matrix.charpoly A) (Matrix.charpoly B)) (h : C * A = B * C) :
    C = (0 : Matrix (Fin b) (Fin a) K) := by
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B (u * A.charpoly + v * B.charpoly) = 1 := by rw [huv, map_one]
  rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero] at h1
  have h2 : aeval B A.charpoly * C = 0 := by
    rw [← aeval_intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = 1 * C := (Matrix.one_mul C).symm
    _ = (aeval B u * aeval B A.charpoly) * C := by rw [h1]
    _ = aeval B u * (aeval B A.charpoly * C) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h2, Matrix.mul_zero]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) :=
  fun A B C hcop h => eq_zero_of_intertwine_of_isCoprime_charpoly A B C hcop h

end GlobalTheory.IntertwinerCoprimeCharpoly
end
