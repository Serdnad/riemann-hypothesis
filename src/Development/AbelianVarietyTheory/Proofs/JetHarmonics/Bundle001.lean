module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Lagrange
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
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

namespace GlobalTheory

theorem exists_le_sum_eq_of_le_sum (S : Finset ℕ) (e : ℕ → ℕ) :
    ∀ n, n ≤ ∑ k ∈ S, e k →
      ∃ f : ℕ → ℕ, (∀ k, f k ≤ e k) ∧ ∑ k ∈ S, f k = n ∧ ∀ k, k ∉ S → f k = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro n hn
    refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_, fun _ _ => rfl⟩
    simp only [Finset.sum_empty] at hn ⊢
    omega
  | insert a S ha ih =>
    intro n hn
    rw [Finset.sum_insert ha] at hn
    obtain ⟨g, hge, hgs, hgo⟩ := ih (min n (∑ k ∈ S, e k)) (min_le_right _ _)
    refine ⟨fun k => if k = a then n - min n (∑ k ∈ S, e k) else g k, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = a
      · subst hk
        simp only [if_true]
        omega
      · simp only [hk, if_false]
        exact hge k
    · rw [Finset.sum_insert ha, if_pos rfl]
      have hS : ∑ k ∈ S, (if k = a then n - min n (∑ k ∈ S, e k) else g k) = ∑ k ∈ S, g k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have : k ≠ a := fun h => ha (h ▸ hk)
        simp only [this, if_false]
      rw [hS, hgs]
      omega
    · intro k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hka, if_false]
      exact hgo k hkS

theorem exists_cut_into_bounded_groups_finset (S : Finset ℕ) (B : ℕ) :
    ∀ (s : ℕ) (e : ℕ → ℕ), ∑ k ∈ S, e k ≤ s * B →
      ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ S, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ S, pc u k ≤ B) ∧
        ∀ u k, k ∉ S → pc u k = 0 := by
  classical
  intro s
  induction s with
  | zero =>
    intro e he
    refine ⟨fun _ _ => 0, ?_, fun u => u.elim0, fun u => u.elim0⟩
    intro k hk
    simp only [zero_mul, nonpos_iff_eq_zero] at he
    rw [Finset.sum_eq_zero_iff] at he
    simp [he k hk]
  | succ s ih =>
    intro e he
    obtain ⟨f, hfe, hfs, hfo⟩ :=
      exists_le_sum_eq_of_le_sum S e (min B (∑ k ∈ S, e k)) (min_le_right _ _)
    have hsplit : ∑ k ∈ S, (e k - f k) + ∑ k ∈ S, f k = ∑ k ∈ S, e k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hfe k)
    have hmul : (s + 1) * B = s * B + B := by ring
    obtain ⟨pc, hpcs, hpcb, hpco⟩ := ih (fun k => e k - f k) (by omega)
    refine ⟨Fin.cons f pc, ?_, ?_, ?_⟩
    · intro k hk
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hpcs k hk]
      exact Nat.add_sub_cancel' (hfe k)
    · intro u
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        omega
      · simp only [Fin.cons_succ]
        exact hpcb i
    · intro u k hk
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        exact hfo k hk
      · simp only [Fin.cons_succ]
        exact hpco i k hk

theorem exists_cut_columns_bounded_width : ∀ (K s B : ℕ) (e : ℕ → ℕ), ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ Finset.Icc 1 K, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧ ∀ u k, k ∉ Finset.Icc 1 K → pc u k = 0 := by
  intro K s B e h
  exact exists_cut_into_bounded_groups_finset (Finset.Icc 1 K) B s e h

end GlobalTheory
end

section

namespace GlobalTheory.NotLeSqSup

theorem not_le_sq_sup {A : Type} [CommRing A] {m I : Ideal A} {n : ℕ}
    (hn : m ^ (n + 1) = ⊥) (hI : ¬ m ≤ I) : ¬ m ≤ m ^ 2 ⊔ I := by
  intro h
  have key : ∀ j : ℕ, m ≤ m ^ (j + 1) ⊔ I := by
    intro j
    induction j with
    | zero => simpa using (le_sup_left : m ≤ m ⊔ I)
    | succ j ih =>
      calc m ≤ m ^ 2 ⊔ I := h
        _ ≤ m ^ (j + 1 + 1) ⊔ I := by
          refine sup_le ?_ le_sup_right
          calc m ^ 2 = m * m := pow_two m
            _ ≤ m * (m ^ (j + 1) ⊔ I) := Ideal.mul_mono_right ih
            _ = m * m ^ (j + 1) ⊔ m * I := Ideal.mul_sup _ _ _
            _ ≤ m ^ (j + 1 + 1) ⊔ I :=
              sup_le_sup (le_of_eq (pow_succ' m (j + 1)).symm)
                (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs)
  apply hI
  simpa [hn] using key n

theorem main : ∀ {k A : Type} [inst : Field k] [inst_1 : CommRing A] [inst_2 : Algebra k A] (aug : A →ₐ[k] k) {I : Ideal A} {n : ℕ}, RingHom.ker aug ^ (n + (1 : ℕ)) = ⊥ → I ≤ RingHom.ker aug → ¬RingHom.ker aug ≤ I → ∃ (φ : A →ₐ[k] DualNumber k), AlgHom.comp (TrivSqZeroExt.fstHom k k k) φ = aug ∧ (∀ a ∈ I, (φ : A → DualNumber k) a = (0 : DualNumber k)) ∧ ∃ a ∈ RingHom.ker aug, (φ : A → DualNumber k) a ≠ (0 : DualNumber k) := by
  intro k A _ _ _ aug I n hn hIm hmI
  have hx : ¬ RingHom.ker aug ≤ RingHom.ker aug ^ 2 ⊔ I := not_le_sq_sup hn hmI
  obtain ⟨x, hxm, hxN⟩ := Set.not_subset.mp hx
  let N : Submodule k A := (RingHom.ker aug ^ 2 ⊔ I).restrictScalars k
  have hq : N.mkQ x ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxN
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k (A ⧸ N), f (N.mkQ x) ≠ 0 := by
    by_contra h; push_neg at h
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let g : A →ₗ[k] k := f.comp N.mkQ
  have hgN : ∀ a ∈ RingHom.ker aug ^ 2 ⊔ I, g a = 0 := by
    intro a ha
    have : N.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ha
    simp only [g, LinearMap.comp_apply, this, map_zero]
  let D : A →ₗ[k] k := g.comp (LinearMap.id - (Algebra.linearMap k A).comp aug.toLinearMap)
  have hD : ∀ a, D a = g (a - algebraMap k A (aug a)) := fun a => rfl
  have hsub : ∀ a, a - algebraMap k A (aug a) ∈ RingHom.ker aug := by
    intro a; simp [RingHom.mem_ker]
  have hDmul : ∀ a b, D (a * b) = aug a * D b + aug b * D a := by
    intro a b
    have e : a * b - algebraMap k A (aug (a * b)) =
        (a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))
          + aug a • (b - algebraMap k A (aug b)) + aug b • (a - algebraMap k A (aug a)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    have h0 : g ((a - algebraMap k A (aug a)) * (b - algebraMap k A (aug b))) = 0 :=
      hgN _ (Ideal.mem_sup_left (by rw [pow_two]; exact Ideal.mul_mem_mul (hsub a) (hsub b)))
    rw [hD, hD, hD, e, map_add (f := _), map_add (f := _), h0, map_smul, map_smul, smul_eq_mul, smul_eq_mul, zero_add]
  let L : A →ₗ[k] DualNumber k :=
    (Algebra.linearMap k (DualNumber k)).comp aug.toLinearMap + (TrivSqZeroExt.inrHom k k).comp D
  have hLfst : ∀ a, (L a).fst = aug a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  have hLsnd : ∀ a, (L a).snd = D a := by intro a; simp [L, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : A →ₐ[k] DualNumber k := AlgHom.ofLinearMap L
    (by ext <;> simp [hLfst, hLsnd, hD])
    (by intro a b; ext <;> simp [hLfst, hLsnd, hDmul] <;> ring)
  have hφ : ∀ a, φ a = L a := fun a => rfl
  refine ⟨φ, ?_, ?_, x, hxm, ?_⟩
  · ext a; simp [hφ, hLfst]
  · intro a ha
    ext
    · simp [hφ, hLfst]; exact hIm ha
    · simp only [hφ, hLsnd, TrivSqZeroExt.snd_zero]
      rw [hD]
      have : aug a = 0 := hIm ha
      rw [this, map_zero, sub_zero]
      exact hgN a (Ideal.mem_sup_right ha)
  · intro h0
    apply hf
    have := congrArg TrivSqZeroExt.snd h0
    rw [hφ, hLsnd, hD, TrivSqZeroExt.snd_zero, (RingHom.mem_ker).mp hxm, map_zero, sub_zero] at this
    exact this

end GlobalTheory.NotLeSqSup
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem polarisation_on_subspace : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : V → Prop) (B T : V → V → ℂ), (∀ (a : ℂ) x y, S x → S y → S (x + a • y)) → (∀ (a : ℂ) x y, S x → S y → B (x + a • y) (x + a • y) = B x x + a * B y x + (starRingEnd ℂ) a * B x y + a * (starRingEnd ℂ) a * B y y) → (∀ (a : ℂ) x y, S x → S y → T (x + a • y) (x + a • y) = T x x + a * T y x + (starRingEnd ℂ) a * T x y + a * (starRingEnd ℂ) a * T y y) → (∀ x, S x → B x x = T x x) → ∀ x y, S x → S y → B x y = T x y := by
  intro V _ _ S B T hS hB hT hd x y hx hy
  have key : ∀ a : ℂ, a * B y x + (starRingEnd ℂ) a * B x y = a * T y x + (starRingEnd ℂ) a * T x y := by
    intro a
    have h := hd _ (hS a x y hx hy)
    rw [hB a x y hx hy, hT a x y hx hy, hd x hx, hd y hy] at h
    linear_combination h
  have h1 := key 1
  have h2 := key Complex.I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2
    - ((B y x - T y x - B x y + T x y) / 2) * Complex.I_mul_I

end GlobalTheory
end

section

open Finset

namespace GlobalTheory

theorem sum_eigenvectors_of_aeval_prod_linear_eq_zero :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (ν : Fin n → ℂ),
      Function.Injective ν →
      Polynomial.aeval (-Ω) (∏ s, (Polynomial.X + Polynomial.C (ν s))) = 0 →
      ∀ w : N, ∃ v : Fin n → N, (∀ s, Ω (v s) = ν s • v s) ∧ w = ∑ s, v s := by
  intro N _ _ n Ω ν hν h w
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun s => s.elim0, fun s => s.elim0, ?_⟩
    have h1 : (1 : Module.End ℂ N) = 0 := by simpa using h
    have h2 : w = 0 := by
      have := congrArg (fun f : Module.End ℂ N => f w) h1
      simpa using this
    simp [h2]
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hinj : Set.InjOn (fun s => -ν s) (↑(Finset.univ : Finset (Fin n))) := by
      intro a _ b _ hab
      exact hν (neg_injective hab)
    have hsum := Lagrange.sum_basis hinj hne
    refine ⟨fun s => Polynomial.aeval (-Ω) (Lagrange.basis Finset.univ (fun s => -ν s) s) w, ?_, ?_⟩
    · intro s
      have key : (Polynomial.X + Polynomial.C (ν s)) * Lagrange.basis Finset.univ (fun s => -ν s) s
          = (∏ j ∈ Finset.univ.erase s, Polynomial.C ((-ν s - -ν j)⁻¹)) *
            ∏ s, (Polynomial.X + Polynomial.C (ν s)) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun s => Polynomial.X + Polynomial.C (ν s))
          (Finset.mem_univ s), Lagrange.basis]
        simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib, map_neg, sub_neg_eq_add]
        ring
      have h2 := congrArg (Polynomial.aeval (-Ω)) key
      rw [map_mul, map_mul, h, mul_zero] at h2
      have h3 := congrArg (fun f : Module.End ℂ N => f w) h2
      simp only [map_add (f := _), Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
        LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
        LinearMap.zero_apply] at h3
      exact (neg_add_eq_zero.mp h3)
    · have h2 := congrArg (fun p => Polynomial.aeval (-Ω) p w) hsum

      simp only [map_sum, map_one, LinearMap.sum_apply, Module.End.one_apply] at h2
      exact h2.symm

end GlobalTheory
end

section

namespace GlobalTheory.RootProductCoeffBound

open Polynomial

theorem coeff_prod_X_sub_C_norm_le {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : (0 : ℝ) ≤ θ) (h1 : θ ≤ (1 : ℝ)) (S : Finset K)
    (hS : ∀ x ∈ S, ‖x‖ ≤ θ) (a : ℕ) :
    ‖AddMonoidAlgebra.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖
      ≤ θ ^ (Finset.card S - a) := by
  classical
  induction S using Finset.induction_on generalizing a with
  | empty =>
    rcases a with _ | k
    · simp
    · simp [Polynomial.coeff_one]
  | insert y S hy ih =>
    have ihS : ∀ b, ‖(∏ x ∈ S, (X - C x)).coeff b‖ ≤ θ ^ (S.card - b) :=
      fun b => ih (fun x hx => hS x (Finset.mem_insert_of_mem hx)) b
    have hyθ : ‖y‖ ≤ θ := hS y (Finset.mem_insert_self y S)
    rw [Finset.prod_insert hy, Finset.card_insert_of_notMem hy]
    set P := ∏ x ∈ S, (X - C x) with hP
    rw [sub_mul, coeff_sub, coeff_C_mul]
    have hyb : ∀ b, ‖y * P.coeff b‖ ≤ θ ^ (S.card + 1 - (b + 1)) * θ := by
      intro b
      rw [norm_mul, mul_comm]
      refine mul_le_mul ?_ hyθ (norm_nonneg _) (pow_nonneg h0 _)
      simpa using ihS b
    rcases a with _ | k
    · rw [coeff_X_mul_zero, zero_sub, norm_neg]
      calc ‖y * P.coeff 0‖ ≤ θ ^ (S.card + 1 - (0 + 1)) * θ := hyb 0
        _ = θ ^ (S.card + 1 - 0) := by simp [pow_succ]
    · rw [coeff_X_mul]
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ihS k
      · rw [norm_neg]
        calc ‖y * P.coeff (k + 1)‖ ≤ θ ^ (S.card - (k + 1)) * θ := by
              have := hyb (k + 1); simpa using this
          _ = θ ^ (S.card - (k + 1) + 1) := by rw [pow_succ]
          _ ≤ θ ^ (S.card + 1 - (k + 1)) := by
              apply pow_le_pow_of_le_one h0 h1
              omega

theorem main : ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] (θ : ℝ), (0 : ℝ) ≤ θ → θ ≤ (1 : ℝ) → ∀ (S : Finset K), (∀ x ∈ S, ‖x‖ ≤ θ) → ∀ (a : ℕ), ‖AddMonoidAlgebra.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖ ≤ θ ^ (Finset.card S - a) :=
  fun θ h0 h1 S hS a => coeff_prod_X_sub_C_norm_le θ h0 h1 S hS a

end GlobalTheory.RootProductCoeffBound
end

section

open scoped BigOperators

namespace GlobalTheory.CoordProdDeriv

theorem card_filter_cons {g k : ℕ} (a : Fin g) (σ : Fin k → Fin g) (i : Fin g) :
    (Finset.univ.filter (fun j => (Fin.cons a σ : Fin (k + 1) → Fin g) j = i)).card
      = (Finset.univ.filter (fun j => σ j = i)).card + if a = i then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [add_comm]

theorem fderiv_prod_iteratedDeriv {g : ℕ} (f : Fin g → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i))
    (n : Fin g → ℕ) (z : Fin g → ℂ) :
    HasFDerivAt (fun z : Fin g → ℂ => ∏ i, iteratedDeriv (n i) (f i) (z i))
      (∑ a : Fin g, (∏ i, iteratedDeriv (n i + if a = i then 1 else 0) (f i) (z i)) •
        (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin g)),
      HasFDerivAt (fun z : Fin g → ℂ => iteratedDeriv (n i) (f i) (z i))
        (iteratedDeriv (n i + 1) (f i) (z i) •
          (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ)) z := by
    intro i _
    have hd : Differentiable ℂ (iteratedDeriv (n i) (f i)) :=
      ((hf i).contDiff (n := ⊤)).differentiable_iteratedDeriv _ (by
        exact WithTop.coe_lt_top _)
    have h1 : HasDerivAt (iteratedDeriv (n i) (f i)) (iteratedDeriv (n i + 1) (f i) (z i)) (z i) := by
      rw [iteratedDeriv_succ]
      exact (hd (z i)).hasDerivAt
    exact h1.comp_hasFDerivAt z
      (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).hasFDerivAt
  have h2 := HasFDerivAt.finsetProd h
  refine h2.congr_fderiv (Eq.symm ?_)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  congr 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi).symm, add_zero]
  · rw [if_pos rfl]

theorem iteratedFDeriv_prod_coord_at {g : ℕ} (f : Fin g → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (k : ℕ) :
    ∀ (ys : Fin k → Fin g → ℂ) (z : Fin g → ℂ),
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) := by
  have hF : ContDiff ℂ ⊤ (fun z : Fin g → ℂ => ∏ i, f i (z i)) :=
    contDiff_prod fun i _ => ((hf i).contDiff).comp (contDiff_apply ℂ (fun _ => ℂ) i)
  induction k with
  | zero => intro ys z; simp
  | succ k ih =>
    intro ys z
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i))) z :=
      hF.differentiable_iteratedFDeriv (m := k) (by exact WithTop.coe_lt_top _) z
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd]
    have e : (fun z => iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) z (Fin.tail ys))
        = fun z => ∑ σ : Fin k → Fin g, (∏ j, Fin.tail ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) (z i) :=
      funext fun z => ih _ z
    rw [e]
    have h3 := HasFDerivAt.fun_sum (u := Finset.univ) (fun (σ : Fin k → Fin g) _ =>
      (fderiv_prod_iteratedDeriv f hf
        (fun i => (Finset.univ.filter (fun j => σ j = i)).card) z).const_mul
        (∏ j, Fin.tail ys j (σ j)))
    rw [h3.fderiv]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
    have e2 : (Fin.consEquiv (fun _ : Fin (k + 1) => Fin g)) (a, σ) = Fin.cons a σ := rfl
    simp only [e2, card_filter_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ring

theorem iteratedFDeriv_prod_coord :
    ∀ (g k : ℕ) (f : Fin g → ℂ → ℂ) (ys : Fin k → Fin g → ℂ), (∀ i, Differentiable ℂ (f i)) →
      iteratedFDeriv ℂ k (fun z : Fin g → ℂ => ∏ i, f i (z i)) 0 ys
        = ∑ σ : Fin k → Fin g, (∏ j, ys j (σ j)) *
          ∏ i, iteratedDeriv (Finset.univ.filter (fun j => σ j = i)).card (f i) 0 :=
  fun _ k f ys hf => iteratedFDeriv_prod_coord_at f hf k ys 0

end GlobalTheory.CoordProdDeriv
end

section

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem setIntegral_translate_of_periodic {n : Type} [Fintype n] (L : AddSubgroup (n → ℝ))
    [Countable L] (D : Set (n → ℝ)) (g : (n → ℝ) → ℂ)
    (hD : IsAddFundamentalDomain L D volume) (hp : ∀ p ∈ L, ∀ s, g (s + p) = g s)
    (s : n → ℝ) : ∫ t in D, g (s + t) = ∫ t in D, g t := by
  have hsD : IsAddFundamentalDomain L (s +ᵥ D) volume := hD.vadd_of_comm s
  have himg : (fun t => s + t) '' D = s +ᵥ D := by
    change (fun t => s +ᵥ t) '' D = s +ᵥ D
    exact Set.image_vadd
  rw [← (measurePreserving_add_left volume s).setIntegral_image_emb
    (MeasurableEquiv.addLeft s).measurableEmbedding g D, himg]
  refine hsD.setIntegral_eq hD (fun p x => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hp p p.2 x

theorem mean_fundamentalDomain_eq_of_periodic :
    ∀ (n : Type) [Fintype n] (L L' : AddSubgroup (n → ℝ)) [Countable L] [Countable L'] (D D' : Set (n → ℝ)) (g : (n → ℝ) → ℂ), MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain L' D' MeasureTheory.volume → MeasureTheory.volume D < ⊤ → MeasureTheory.volume D' < ⊤ → Continuous g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) → (∀ p ∈ L, ∀ s, g (s + p) = g s) → (∀ p ∈ L', ∀ s, g (s + p) = g s) → ((MeasureTheory.volume D).toReal : ℂ) * ∫ s in D', g s = ((MeasureTheory.volume D').toReal : ℂ) * ∫ s in D, g s := by
  intro n _ L L' _ _ D D' g hD hD' hDfin hD'fin hg ⟨C, hC⟩ hp hp'
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩
  have : IsFiniteMeasure (volume.restrict D') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD'fin⟩
  have hint : Integrable (Function.uncurry fun s t => g (s + t))
      ((volume.restrict D).prod (volume.restrict D')) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => hC _)
    exact (hg.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have h1 : ∫ s in D, ∫ t in D', g (s + t) = ((volume D).toReal : ℂ) * ∫ t in D', g t := by
    simp_rw [setIntegral_translate_of_periodic L' D' g hD' hp']
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  have h2 : ∫ t in D', ∫ s in D, g (s + t) = ((volume D').toReal : ℂ) * ∫ s in D, g s := by
    have : ∀ t, ∫ s in D, g (s + t) = ∫ s in D, g s := fun t => by
      simp_rw [add_comm _ t]
      exact setIntegral_translate_of_periodic L D g hD hp t
    simp_rw [this]
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  rw [← h1, ← h2]
  exact integral_integral_swap hint

end GlobalTheory
end
