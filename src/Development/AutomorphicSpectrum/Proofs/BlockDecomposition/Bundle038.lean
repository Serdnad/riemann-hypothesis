module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle023
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

section

set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatPrime

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem f_mem_IB : f ξ ∈ Lat.IB f ξ := by
  rw [Lat.IB]
  exact Ideal.mem_span_singleton_self _

theorem eta_mem_IB : Lat.η f ξ l M ∈ Lat.IB f ξ := by
  rw [Lat.η, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (f_mem_IB f ξ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  rw [Lat.dpE, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (eta_mem_IB f ξ l M) _ (Nat.succ_pos i))

theorem dpE_zero : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]

theorem exists_sub_mem_IB {x : B} (hx : x ∈ Lat.sub f ξ l M) :
    ∃ a : W, x - f a ∈ Lat.IB f ξ := by
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨w, by rw [sub_self]; exact zero_mem _⟩
    · cases i with
      | zero => exact ⟨1, by rw [dpE_zero, map_one, sub_self]; exact zero_mem _⟩
      | succ i => exact ⟨0, by rw [map_zero, sub_zero]; exact dpE_succ_mem_IB f ξ l M i⟩
  | zero => exact ⟨0, by rw [map_zero, sub_zero]; exact zero_mem _⟩
  | one => exact ⟨1, by rw [map_one, sub_self]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have e : x + y - f (a + b) = (x - f a) + (y - f b) := by rw [map_add (f := _)]; ring
    rw [e]
    exact add_mem ha hb
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    have e : -x - f (-a) = -(x - f a) := by rw [map_neg]; ring
    rw [e]
    exact neg_mem ha
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    have e : x * y - f (a * b) = (x - f a) * y + f a * (y - f b) := by rw [map_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem ι_mem_sub (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := by
  exact (show ↥(Lat.sub f ξ l M) from x).2

theorem dvd_of_mem_IB {m : ℕ} (hyp : Lat.Hyp f ξ l m) {a : W} (ha : f a ∈ Lat.IB f ξ) : ξ ∣ a := by
  rw [Lat.IB, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  have hm : 0 < m := hyp.one_le
  refine hyp.gr 0 hm a b ?_
  rw [pow_zero, mul_one, zero_add, pow_one]
  exact hb

end

theorem I_isPrime : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → (Lat.I f ξ l M).IsPrime := by
  intro W B _ _ _ f ξ l M m hyp
  haveI := hyp.dom
  have key : ∀ a : W, f a ∈ Lat.IB f ξ ↔ ξ ∣ a := by
    intro a
    refine ⟨fun ha => dvd_of_mem_IB f ξ l hyp ha, ?_⟩
    rintro ⟨c, rfl⟩
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (f_mem_IB f ξ)
  have hq : ∀ a : W, ξ ∣ a ↔ Ideal.Quotient.mk (Ideal.span {ξ}) a = 0 := by
    intro a
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨?_, ?_⟩
  · intro htop
    rw [Ideal.eq_top_iff_one] at htop
    simp only [Lat.I, Ideal.mem_comap] at htop
    have h2 : f 1 ∈ Lat.IB f ξ := by rwa [map_one, ← map_one f] at htop
    have h3 := (hq 1).1 ((key 1).1 h2)
    rw [map_one] at h3
    exact one_ne_zero h3
  · intro x y hxy
    simp only [Lat.I, Ideal.mem_comap, map_mul] at hxy ⊢
    obtain ⟨a, ha⟩ := exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M x)
    obtain ⟨b, hb⟩ := exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M y)
    have hab : f (a * b) ∈ Lat.IB f ξ := by
      have e : f (a * b) = Lat.ι f ξ l M x * Lat.ι f ξ l M y
          - ((Lat.ι f ξ l M x - f a) * Lat.ι f ξ l M y + f a * (Lat.ι f ξ l M y - f b)) := by
        rw [map_mul]; ring
      rw [e]
      exact sub_mem hxy (add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb))
    have h := (hq (a * b)).1 ((key _).1 hab)
    rw [map_mul, mul_eq_zero] at h
    rcases h with h | h
    · left
      have hfa : f a ∈ Lat.IB f ξ := (key a).2 ((hq a).2 h)
      have e : Lat.ι f ξ l M x = (Lat.ι f ξ l M x - f a) + f a := by ring
      rw [e]
      exact add_mem ha hfa
    · right
      have hfb : f b ∈ Lat.IB f ξ := (key b).2 ((hq b).2 h)
      have e : Lat.ι f ξ l M y = (Lat.ι f ξ l M y - f b) + f b := by ring
      rw [e]
      exact add_mem hb hfb

end GlobalTheory.CompanionTheory.LatPrime
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.AlgCoproduct

theorem exists_isWP : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (n : ℕ),
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra A K) (ι : Fin n → (B →ₐ[A] K)), IsWP ι := by
  intro A _ B _ _ n
  induction n with
  | zero =>
    refine ⟨A, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    constructor
    · intro T _ x y _
      exact ⟨x, by ext a; rfl, fun i => i.elim0⟩
    · intro T _ z z' h _
      exact h
  | succ n ih =>
    obtain ⟨K, _, _, ι, hι⟩ := ih
    refine ⟨B ⊗[A] K, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (ι i)), ?_⟩
    constructor
    · intro T _ x y hy
      obtain ⟨z, hz, hzi⟩ := hι.ex T x (fun i => y i.succ) (fun i => hy i.succ)
      letI : Algebra A T := x.toAlgebra
      let f : B →ₐ[A] T := { y 0 with commutes' := fun a => RingHom.congr_fun (hy 0) a }
      let g : K →ₐ[A] T := { z with commutes' := fun a => RingHom.congr_fun hz a }
      refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩
      · ext a
        exact (Algebra.TensorProduct.productMap f g).commutes a
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · ext b
          simp [f, g]
        · ext b
          have := RingHom.congr_fun (hzi j) b
          simpa [f, g] using this
    · intro T _ z z' h hi
      have hB : ∀ b : B, z (b ⊗ₜ[A] 1) = z' (b ⊗ₜ[A] 1) := fun b => by
        simpa using RingHom.congr_fun (hi 0) b
      have hK : (z.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom) =
          z'.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom := by
        refine hι.uniq T _ _ ?_ (fun i => ?_)
        · ext a
          have := RingHom.congr_fun h a
          simpa [Algebra.TensorProduct.algebraMap_apply] using this
        · ext b
          simpa using RingHom.congr_fun (hi i.succ) b
      refine RingHom.ext fun t => ?_
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b k =>
        have h1 : b ⊗ₜ[A] k = (b ⊗ₜ[A] (1 : K)) * ((1 : B) ⊗ₜ[A] k) := by simp
        have h2 : z ((1 : B) ⊗ₜ[A] k) = z' ((1 : B) ⊗ₜ[A] k) := RingHom.congr_fun hK k
        rw [h1, map_mul, map_mul, hB, h2]
      | add a b ha hb => simp [ha, hb]

end GlobalTheory.CompanionTheory.AlgCoproduct
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpHomotopy

theorem wp_homotopy : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∃ H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n, (∀ z, H 0 (alt (δ 0) z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (alt (δ n)).lTensor B (H n z) + H (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z := by
  intro A _ B _ _ K _ _ ι δ hW hδ
  have huniq : ∀ (m : ℕ) (T : Type) [CommRing T] [Algebra A T] (f g : K m →ₐ[A] T),
      (∀ i, f.comp (ι m i) = g.comp (ι m i)) → f = g := by
    intro m T _ _ f g hfg
    have key := (hW m).uniq T (f : K m →+* T) (g : K m →+* T)
      (by ext a; simp)
      (fun i => by
        ext b
        exact DFunLike.congr_fun (hfg i) b)
    ext x
    exact DFunLike.congr_fun key x
  have hex : ∀ n, ∃ h : K (n + 1) →ₐ[A] B ⊗[A] K n,
      h.comp (ι (n + 1) 0) = Algebra.TensorProduct.includeLeft ∧
      ∀ i : Fin n, h.comp (ι (n + 1) i.succ) =
        (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i) := by
    intro n
    obtain ⟨z, hz, hzi⟩ := (hW (n + 1)).ex (B ⊗[A] K n) (algebraMap A (B ⊗[A] K n))
      (Fin.cons (α := fun _ => B →+* B ⊗[A] K n)
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] K n) : B →+* B ⊗[A] K n)
        (fun i => (((Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i) :
          B →ₐ[A] B ⊗[A] K n) : B →+* B ⊗[A] K n)))
      (by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · ext a; simp
        · ext a; simp)
    refine ⟨{ z with commutes' := fun a => DFunLike.congr_fun hz a }, ?_, fun i => ?_⟩
    · ext b
      simpa using DFunLike.congr_fun (hzi 0) b
    · ext b
      simpa using DFunLike.congr_fun (hzi i.succ) b
  choose h hl hr using hex
  have h0 : ∀ n, (h n).comp (δ n 0) = (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n) := by
    intro n
    refine huniq n _ _ _ (fun i => ?_)
    rw [AlgHom.comp_assoc, hδ, Fin.succAbove_zero]
    exact hr n i
  have hs : ∀ n (k : Fin (n + 1)), (h (n + 1)).comp (δ (n + 1) k.succ) =
      (Algebra.TensorProduct.map (AlgHom.id A B) (δ n k)).comp (h n) := by
    intro n k
    refine huniq (n + 1) _ _ _ (fun i => ?_)
    rw [AlgHom.comp_assoc, hδ, AlgHom.comp_assoc]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.succ_succAbove_zero, hl, hl]
      ext b
      simp
    · rw [Fin.succ_succAbove_succ, hr, hr, ← AlgHom.comp_assoc]
      have e := hδ n k j
      ext b
      have e' := DFunLike.congr_fun e b
      simp only [AlgHom.comp_apply] at e' ⊢
      simp [e']
  refine ⟨fun n => (h n).toLinearMap, fun z => ?_, fun n z => ?_⟩
  · have e := DFunLike.congr_fun (h0 0) z
    simpa [alt] using e
  · have e0 := DFunLike.congr_fun (h0 (n + 1)) z
    have es : ∀ k : Fin (n + 1), h (n + 1) (δ (n + 1) k.succ z) =
        ((δ n k).toLinearMap.lTensor B) (h n z) := by
      intro k
      have e := DFunLike.congr_fun (hs n k) z
      simp only [AlgHom.comp_apply] at e
      rw [e]
      generalize h n z = t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    have a1 : alt (δ (n + 1)) z = δ (n + 1) 0 z +
        ∑ k : Fin (n + 1), -((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z) := by
      simp [alt, Fin.sum_univ_succ, LinearMap.sum_apply, pow_succ]
    have a2 : ∀ t : B ⊗[A] K n, (alt (δ n)).lTensor B t =
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [alt, LinearMap.lTensor_tmul, LinearMap.sum_apply, LinearMap.smul_apply,
          TensorProduct.tmul_sum, TensorProduct.tmul_smul]
      | add x y hx hy =>
        simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]
    show (alt (δ n)).lTensor B (h n z) + h (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z
    have e1 : h (n + 1) (δ (n + 1) 0 z) = (1 : B) ⊗ₜ[A] z := by
      simpa using e0

    rw [a1, a2, map_add (f := _), e1, map_sum, add_left_comm, ← Finset.sum_add_distrib]
    have : ∀ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) (h n z) +
        h (n + 1) (-((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z)) = 0 := by
      intro k
      rw [map_neg, map_zsmul, es k, add_neg_cancel]
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    simp

end GlobalTheory.CompanionTheory.WpHomotopy
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.RootNear

theorem mul_prod_congr {B ι : Type} [CommRing B] (u : B) (x y : ι → B) (S : Finset ι)
    (h : ∀ j ∈ S, u * x j = u * y j) : u * ∏ j ∈ S, x j = u * ∏ j ∈ S, y j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : u * x a = u * y a := h a (Finset.mem_insert_self a s)
    have h2 : u * ∏ j ∈ s, x j = u * ∏ j ∈ s, y j :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    calc u * (x a * ∏ j ∈ s, x j) = (u * x a) * ∏ j ∈ s, x j := by ring
      _ = (u * y a) * ∏ j ∈ s, x j := by rw [h1]
      _ = y a * (u * ∏ j ∈ s, x j) := by ring
      _ = y a * (u * ∏ j ∈ s, y j) := by rw [h2]
      _ = u * (y a * ∏ j ∈ s, y j) := by ring

theorem exists_shift {B ι : Type} [CommRing B] (I : Ideal B) (c f : ι → B) (S : Finset ι)
    (hf : ∀ j ∈ S, IsIdempotentElem (f j)) (hc : ∀ j ∈ S, f j * c j ∈ I) :
    ∃ s ∈ I, (∏ j ∈ S, (1 - f j)) ∣ ∏ j ∈ S, (c j - s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, htI, hdvd⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hfa : f a * f a = f a := hf a (Finset.mem_insert_self a s)
    have hca : f a * c a ∈ I := hc a (Finset.mem_insert_self a s)
    refine ⟨(1 - f a) * t + f a * c a, I.add_mem (I.mul_mem_left _ htI) hca, ?_⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcong : (1 - f a) * ∏ j ∈ s, (c j - ((1 - f a) * t + f a * c a)) =
        (1 - f a) * ∏ j ∈ s, (c j - t) :=
      mul_prod_congr (1 - f a) _ _ s (fun j _ => by linear_combination (c a - t) * hfa)
    have hfirst : c a - ((1 - f a) * t + f a * c a) = (1 - f a) * (c a - t) := by ring
    rw [hfirst, mul_comm (1 - f a) (c a - t), mul_assoc, hcong]
    exact Dvd.dvd.mul_left (mul_dvd_mul_left (1 - f a) hdvd) _

theorem root_near (B : Type) [CommRing B] (π : B) (hπ : π ∈ nonZeroDivisors B) (hV : VAL π)
    (d M : ℕ) (b : Fin d → B) (a : B) (hd : 0 < d)
    (hprod : ∏ j, (a - b j) ∈ Ideal.span {π ^ (d * M)}) :
    ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ ∏ j, (a₁ - b j) = 0 := by
  classical
  have key : ∀ j : Fin d, ∃ e : B, IsIdempotentElem e ∧ e * (a - b j) ∈ Ideal.span {π ^ M} ∧
      (1 - e) * π ^ M ∈ Ideal.span {a - b j} := fun j =>
    hV (a - b j) (π ^ M) ⟨M, Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  choose e he1 he2 he3 using key
  have hee : ∀ j, e j * e j = e j := fun j => he1 j
  have hr : ∀ j, ∃ r : B, (1 - e j) * π ^ M = (a - b j) * r := fun j =>
    Ideal.mem_span_singleton.mp (he3 j)
  choose r hr using hr
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hprod
  obtain ⟨j0, -⟩ : ∃ j : Fin d, True := ⟨⟨0, hd⟩, trivial⟩
  obtain ⟨E, hEdef⟩ : ∃ E : B, E = ∏ j, (1 - e j) := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hEdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by linear_combination hee j)
  have hEj : ∀ j, E * (1 - e j) = E := by
    intro j
    have hsplit : (1 - e j) * ∏ i ∈ Finset.univ.erase j, (1 - e i) = E := by
      rw [hEdef]; exact Finset.mul_prod_erase _ (fun i => 1 - e i) (Finset.mem_univ j)
    rw [← hsplit]
    linear_combination (∏ i ∈ Finset.univ.erase j, (1 - e i)) * hee j
  have hT : ∀ j, (a - b j) * (E * r j) = E * π ^ M := by
    intro j
    calc (a - b j) * (E * r j) = E * ((a - b j) * r j) := by ring
      _ = E * ((1 - e j) * π ^ M) := by rw [← hr j]
      _ = (E * (1 - e j)) * π ^ M := by ring
      _ = E * π ^ M := by rw [hEj j]
  have hEpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hEE]
  have hEd : E ^ d = E := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', hEpow]
  have hmain : π ^ (d * M) * (q * ∏ j, (E * r j)) = π ^ (d * M) * E := by
    calc π ^ (d * M) * (q * ∏ j, (E * r j)) = (∏ j, (a - b j)) * ∏ j, (E * r j) := by
          rw [hq]; ring
      _ = ∏ j, ((a - b j) * (E * r j)) := Finset.prod_mul_distrib.symm
      _ = ∏ _j : Fin d, (E * π ^ M) := Finset.prod_congr rfl (fun j _ => hT j)
      _ = π ^ (d * M) * E := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, hEd, ← pow_mul,
            mul_comm M d]
          ring
  have hpow : π ^ (d * M) ∈ nonZeroDivisors B := pow_mem hπ _
  have hET : E = q * ∏ j, (E * r j) := by
    have h0 : (q * ∏ j, (E * r j) - E) * π ^ (d * M) = 0 := by linear_combination hmain
    exact (sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpow).2 _ h0)).symm
  have hEa : E * (a - b j0) ∈ Ideal.span {π ^ M} := by
    rw [Ideal.mem_span_singleton]
    have hsplit : (E * r j0) * ∏ i ∈ Finset.univ.erase j0, (E * r i) = ∏ i, (E * r i) :=
      Finset.mul_prod_erase _ (fun i => E * r i) (Finset.mem_univ j0)
    refine ⟨q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E, ?_⟩
    calc E * (a - b j0) = q * (∏ i, (E * r i)) * (a - b j0) := by rw [← hET]
      _ = q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * ((a - b j0) * (E * r j0)) := by
          rw [← hsplit]; ring
      _ = π ^ M * (q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E) := by rw [hT j0]; ring
  obtain ⟨s, hs, w, hw⟩ := exists_shift (Ideal.span {π ^ M}) (fun j => a - b j) e Finset.univ
    (fun j _ => he1 j) (fun j _ => he2 j)
  have hw' : ∏ j, (a - b j - s) = E * w := by rw [hEdef]; exact hw
  obtain ⟨a₁, ha₁⟩ : ∃ x : B, x = (1 - E) * (a - s) + E * b j0 := ⟨_, rfl⟩
  refine ⟨a₁, ?_, ?_⟩
  · have h1 : a₁ - a = (E - 1) * s - E * (a - b j0) := by rw [ha₁]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hs) hEa
  · have hsplit2 : (a₁ - b j0) * ∏ i ∈ Finset.univ.erase j0, (a₁ - b i) = ∏ i, (a₁ - b i) :=
      Finset.mul_prod_erase _ (fun i => a₁ - b i) (Finset.mem_univ j0)
    have hE0 : E * ∏ i, (a₁ - b i) = 0 := by
      rw [← hsplit2]
      linear_combination E * (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * ha₁ +
        (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * (b j0 - (a - s)) * hEE
    have hcong : (1 - E) * ∏ i, (a₁ - b i) = (1 - E) * ∏ i, (a - b i - s) :=
      mul_prod_congr (1 - E) _ _ Finset.univ
        (fun j _ => by linear_combination (1 - E) * ha₁ + (a - s - b j0) * hEE)
    calc ∏ i, (a₁ - b i) = E * ∏ i, (a₁ - b i) + (1 - E) * ∏ i, (a₁ - b i) := by ring
      _ = 0 + (1 - E) * ∏ i, (a - b i - s) := by rw [hE0, hcong]
      _ = 0 := by rw [hw']; linear_combination (-w) * hEE

end GlobalTheory.CompanionTheory.RootNear
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PfCompl

theorem isCompl_existsUnique :
    ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g →
      ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x π}) T₁ →
        ∃! ψ : T →+* T₁, ψ.comp g = x := by
  intro B _ T _ π g h T₁ _ x hc
  exact existsUnique_comp_eq π g h.surj h.inj x hc

end GlobalTheory.CompanionTheory.PfCompl
end
