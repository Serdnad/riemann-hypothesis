module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem span_embeddings_mul_eq_univ_of_injective {O K ι : Type} [CommRing O] [Field K] [Fintype ι] (τ : ι → O →+* K)
    (hτ : Function.Injective τ) (N : O) (hN : ∀ t, τ t N ≠ 0) :
    Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  have hφv : ∀ v : ι → K, φ v = ∑ t, v t * φ (Pi.single t 1) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_eq_mul]
    congr 2
    ext s
    simp [Pi.single_apply, eq_comm]
  have hzero : ∀ x : O, ∑ t, (φ (Pi.single t 1) * τ t N) * τ t x = 0 := by
    intro x
    have hx : (fun t => τ t (N * x)) ∈ Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} :=
      Submodule.subset_span ⟨x, rfl⟩
    have : φ (fun t => τ t (N * x)) = 0 := by
      have h2 := Submodule.mem_map_of_mem (f := φ) hx
      rw [hmap, Submodule.mem_bot] at h2
      exact h2
    rw [hφv] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul]
    ring
  have hli : LinearIndependent K (fun t => ((τ t : O →* K) : O → K)) := by
    refine (linearIndependent_monoidHom O K).comp (fun t => (τ t : O →* K)) ?_
    intro a b hab
    apply hτ
    ext y
    exact DFunLike.congr_fun hab y
  have hc : ∀ t, φ (Pi.single t 1) * τ t N = 0 := by
    refine Fintype.linearIndependent_iff.1 hli _ ?_
    funext x
    simpa [Finset.sum_apply] using hzero x
  apply hφ
  refine LinearMap.ext fun v => ?_
  rw [hφv, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [(mul_eq_zero.1 (hc t)).resolve_right (hN t), mul_zero]

theorem spanTop : SpanTop := by
  classical
  intro O K ι _ _ _ τ hτ N hN k
  have hA := span_embeddings_mul_eq_univ_of_injective τ hτ N hN
  let L : Fin k → (ι → K) →ₗ[K] (ι × Fin k → K) := fun j =>
    LinearMap.pi (fun p => if p.2 = j then LinearMap.proj p.1 else 0)
  have hL : ∀ j w p, L j w p = if p.2 = j then w p.1 else 0 := by
    intro j w p
    simp only [L, LinearMap.pi_apply]
    split_ifs <;> simp
  have hsub : ∀ j, Submodule.map (L j) (Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)}) ≤
      Submodule.span K {x | ∃ β : Fin k → O, x = pt τ fun s ↦ N * β s} := by
    intro j
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨v, ⟨x, rfl⟩, rfl⟩
    refine ⟨Pi.single j x, ?_⟩
    funext p
    rw [hL]
    simp only [pt, Pi.single_apply]
    split_ifs <;> simp_all
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = ∑ j, L j (fun t => v (t, j)) := by
    funext p
    simp [Finset.sum_apply, hL]
  rw [hv]
  refine Submodule.sum_mem _ fun j _ => hsub j ?_
  refine Submodule.mem_map_of_mem ?_
  rw [hA]
  exact Submodule.mem_top

end UpperTheory.Gal.Schur
end
end

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private def latt {O K ι : Type} [CommRing O] [Field K] (τ : ι → (O →+* K)) (N : O) (k : ℕ) :
    AddSubgroup (ι × Fin k → K) where
  carrier := {x | ∃ β : Fin k → O, x = pt τ (fun s => N * β s)}
  add_mem' := by
    rintro _ _ ⟨β, rfl⟩ ⟨β', rfl⟩
    refine ⟨β + β', ?_⟩
    funext p
    simp [pt, mul_add]
  zero_mem' := by
    refine ⟨0, ?_⟩
    funext p
    simp [pt]
  neg_mem' := by
    rintro _ ⟨β, rfl⟩
    refine ⟨-β, ?_⟩
    funext p
    simp [pt]

theorem denseCoset_of : DenseSub → SpanTop → DenseOff → DenseCoset := by
  intro hS hT hO O K ι _ _ _ _ τ hτ N hN k a Q hQ
  have hspan : Submodule.span K ((latt τ N k : AddSubgroup (ι × Fin k → K)) : Set (ι × Fin k → K)) = ⊤ :=
    hT O K ι τ hτ N hN k
  have hd := hS K (ι × Fin k) (latt τ N k) (pt τ a) hspan
  have hd2 := hO K (ι × Fin k) _ hd Q hQ
  intro P hP
  apply hd2
  rintro x ⟨hx, hxQ⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin k → O, x - pt τ a = pt τ (fun s => N * β s) := hx
  have hxe : x = pt τ (fun s => a s + N * β s) := by
    rw [sub_eq_iff_eq_add.mp hβ]
    funext p
    simp [pt, add_comm]
  refine hP x ⟨fun s => a s + N * β s, fun s => ?_, ?_, hxe⟩
  · simp
  · rw [← hxe]
    exact hxQ

end UpperTheory.Gal.Schur
end
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.denseOff :
    DenseOff := by
  intro K σ _ D hD Q hQ P hP
  have hPQ : P * Q = 0 := by
    apply hD
    intro x hx
    by_cases hq : eval x Q = 0
    · rw [map_mul, hq, mul_zero]
    · rw [map_mul, hP x ⟨hx, hq⟩, zero_mul]
  exact (mul_eq_zero.1 hPQ).resolve_right hQ
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairCount_of :
    PairSplit → PairCount := by
  intro hP n i
  have hS : ∑ a : Fin n, (n - 1 - (a : ℕ)) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun a => n - 1 - a), Finset.sum_range_reflect (fun a => a) n,
      Finset.sum_range_id, Nat.choose_two_right]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hC : (m + 1).choose 2 = m.choose 2 + m := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hi : (i : ℕ) ≤ m := by have := i.isLt; omega
  simp only [Nat.add_sub_cancel] at hS ⊢
  refine ⟨?_, ?_⟩
  · have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun k => m - (k : ℕ))
      (Finset.mem_univ i)
    omega
  · have h := hP (Multiplicative ℕ) (m + 1) (fun _ _ => Multiplicative.ofAdd 1) i
    apply_fun Multiplicative.toAdd at h
    simp [toAdd_prod] at h
    omega
end

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem elementary_span_mul (K : Type) [CommRing K] (n k l : ℕ)
    (P Q : MvPolynomial (Fin n) K) (hP : P ∈ eSpan K n k) (hQ : Q ∈ eSpan K n l) :
    P * Q ∈ eSpan K n (k + l) := by
  have hmem : P * Q ∈ eSpan K n k * eSpan K n l := Submodule.mul_mem_mul hP hQ
  have hle : eSpan K n k * eSpan K n l ≤ eSpan K n (k + l) := by
    unfold eSpan
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
    refine ⟨Fin.append m m', ?_⟩
    simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  exact hle hmem

private theorem one_mem_eSpan (K : Type) [CommRing K] (n j : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n j := by
  unfold eSpan
  apply Submodule.subset_span
  refine ⟨fun _ => 0, ?_⟩
  simp [esymm_zero]

theorem eSpanMul : ESpanMul := by
  intro K _ n
  refine ⟨fun k l hkl => ?_, fun k l P Q hP hQ => elementary_span_mul K n k l P Q hP hQ⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  intro P hP
  simpa using elementary_span_mul K n k d P 1 hP (one_mem_eSpan K n d)

end UpperTheory.Gal.Schur
end
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.spanProd_of :
    SpanE → SpanProd := by
  intro hS K ι _ _ _ n P hP
  choose k0 hk0 using fun t => hS K n (P t) (hP t)
  refine ⟨univ.sup k0, fun k hk => ?_⟩
  have hle : ∀ t, k0 t ≤ k := fun t => (le_sup (mem_univ t)).trans hk
  choose w hw using fun t => hk0 t k (hle t)
  refine ⟨fun m => ∏ t, (w t (fun s => m (t, s)) * ∏ s, (-1 : K) ^ ((m (t, s) : Fin (n + 1)) : ℕ)), ?_⟩
  intro R _ _ g
  have step : ∀ t, aeval (g t) (P t) = ∑ m : Fin k → Fin (n + 1),
      (w t m * ∏ s, (-1 : K) ^ (m s : ℕ)) • ∏ s, ((-1) ^ (m s : ℕ) * aeval (g t) (esymm (Fin n) K (m s))) := by
    intro t
    conv_lhs => rw [hw t]

    simp only [map_sum, map_smul, map_prod]
    refine sum_congr rfl fun m _ => ?_
    rw [prod_mul_distrib, Algebra.smul_def, Algebra.smul_def, map_mul, map_prod]
    simp only [map_pow, map_neg, map_one]
    have hc : (∏ s, (-1 : R) ^ (m s : ℕ)) * ∏ s, (-1 : R) ^ (m s : ℕ) = 1 := by
      rw [← prod_mul_distrib]
      simp [← mul_pow]
    linear_combination (-(algebraMap K R (w t m) * ∏ s, aeval (g t) (esymm (Fin n) K (m s)))) * hc
  simp only [step]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.curry ι (Fin k) (Fin (n + 1))).symm _ _ fun M => ?_
  rw [Fintype.prod_prod_type]
  simp only [Equiv.curry_symm_apply, Function.uncurry_apply_pair, Algebra.smul_def, map_prod,
    prod_mul_distrib]
  rw [← map_prod, prod_mul_distrib]
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairSplit :
    PairSplit := by
  intro R _ n F i
  have hA : ∀ a : Fin n, ∏ b ∈ Ioi a, F a b =
      (∏ b ∈ (Ioi a).erase i, F a b) * (if a < i then F a i else 1) := by
    intro a
    split_ifs with h
    · exact (Finset.prod_erase_mul _ _ (by simpa using h)).symm
    · rw [Finset.erase_eq_self.mpr (by simpa using h), mul_one]
  have hL : ∏ a, ∏ b > a, F a b = ∏ a, ∏ b ∈ Ioi a, F a b := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rfl
  have h1 : (univ : Finset (Fin n)).filter (fun a => a < i) = (univ.erase i).filter (fun k => k < i) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
    constructor
    · intro h; exact ⟨ne_of_lt h, h⟩
    · intro h; exact h.2
  have h2 : (univ.erase i).filter (fun k => ¬ k < i) = Ioi i := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, Finset.mem_Ioi, and_true, not_lt]
    constructor
    · intro h; exact lt_of_le_of_ne h.2 (Ne.symm h.1)
    · intro h; exact ⟨ne_of_gt h, le_of_lt h⟩
  rw [hL, Finset.prod_congr rfl fun a _ => hA a, Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
    Finset.erase_eq_self.mpr (by simp), ← Finset.prod_filter, Finset.prod_ite, h1, h2]
  simp only [mul_comm, mul_left_comm, mul_assoc]
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

private lemma one_factor {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (n : ℕ) (x : R)
    (g : Fin n → R) :
    detOne x g = ∑ a : Fin (n + 1), x ^ (a : ℕ) * ((-1) ^ (a : ℕ) * aeval g (esymm (Fin n) K a)) := by
  have key : ∀ a : ℕ, x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a)) =
      ∑ t ∈ powersetCard a (univ : Finset (Fin n)), ∏ j ∈ t, (-(x * g j)) := by
    intro a

    simp only [esymm, map_sum, map_prod, aeval_X, mul_sum]
    refine sum_congr rfl fun t ht => ?_
    rw [prod_neg, prod_mul_distrib, prod_const, (mem_powersetCard.1 ht).2]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun a => x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a))) (n + 1)]
  simp only [key]
  have hc : n + 1 = #(univ : Finset (Fin n)) + 1 := by simp
  rw [hc, ← sum_powerset, ← prod_one_add]
  unfold detOne
  simp only [sub_eq_add_neg]

theorem UpperTheory.Gal.Schur.expand :
    Expand := by
  intro K R π _ _ _ _ _ n x g
  simp only [one_factor (K := K)]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [prod_mul_distrib]
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.offClrPow_of :
    SchurYOffClr → VdmSplit → PairCount → OffClrPow := by
  intro hS hV hP R _ _ n lam g y
  have key : ∀ i : Fin n, vdm (scaleOff y i g) = y ^ (n - 1).choose 2 *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) := by
    intro i
    have h1 : vdmAway i (scaleOff y i g) = y ^ (n - 1).choose 2 * vdmAway i g := by
      rw [← (hP n i).2, ← Finset.prod_pow_eq_pow_sum]
      unfold vdmAway
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha => ?_
      have ha' : a ≠ i := (Finset.mem_erase.mp ha).1
      calc ∏ b ∈ (Finset.Ioi a).erase i, (scaleOff y i g a - scaleOff y i g b)
          = ∏ b ∈ (Finset.Ioi a).erase i, (y * (g a - g b)) := by
            refine Finset.prod_congr rfl fun b hb => ?_
            have hb' : b ≠ i := (Finset.mem_erase.mp hb).1
            simp [scaleOff, ha', hb', mul_sub]
        _ = y ^ ((Finset.Ioi a).erase i).card * ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    have h2 : ∏ k ∈ univ.erase i, (scaleOff y i g i - scaleOff y i g k) =
        ∏ k ∈ univ.erase i, (g i - y * g k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [scaleOff, hk']
    rw [hV R n (scaleOff y i g) i, h1, h2]
    ring
  have hL : y ^ (n - 1).choose 2 * ∑ i, sch lam (scaleOff y i g) *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      ∑ i, sch lam (scaleOff y i g) * vdm (scaleOff y i g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i]
    ring
  have hR : ∀ i : Fin n, y ^ (∑ k ∈ univ.erase i, (lam k + (n - 1 - (k : ℕ)))) =
      y ^ (n - 1).choose 2 * y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by
    intro i
    rw [Finset.sum_add_distrib, (hP n i).1, ← pow_add]
    congr 1
    omega
  rw [hL, hS R n lam g y, Finset.sum_congr rfl fun i _ => hR i, ← Finset.mul_sum]
  ring
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

end UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.offClrRed_of :
    OffClrPow → OffClrRed := by
  intro h R _ _ n lam g y
  have key := h (Polynomial R) n lam (fun k => Polynomial.C (g k)) Polynomial.X
  have key' := (Polynomial.isRegular_X_pow ((n - 1).choose 2)).left key
  let φ : Polynomial R →ₐ[ℚ] R := (Polynomial.evalRingHom y).toRatAlgHom
  have hφ : ∀ (f : Fin n → Polynomial R) (p : MvPolynomial (Fin n) ℚ),
      φ (MvPolynomial.aeval f p) = MvPolynomial.aeval (fun k => φ (f k)) p := by
    intro f p
    rw [← MvPolynomial.comp_aeval]
    rfl
  have hC : ∀ r : R, φ (Polynomial.C r) = r := fun r => by simp [φ]
  have hX : φ Polynomial.X = y := by simp [φ]
  have hs : ∀ i, (fun k => φ (scaleOff Polynomial.X i (fun k => Polynomial.C (g k)) k)) = scaleOff y i g := by
    intro i
    funext k
    simp only [scaleOff]
    split_ifs
    · simp [hC]
    · rw [map_mul, hC, hX]
  have := congrArg φ key'

  simp only [map_sum, map_mul, map_prod, map_pow, map_sub, map_neg, map_one, sch, hφ, vdmAway, vdm,
  hs, hC, hX] at this
  simpa [sch, vdmAway, vdm] using this
end

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYOff_of : OffClrRed → VdmSplit → SchurYOff := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))) * vdm g =
      sch lam g * vdm g * ∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hSplit R n g i]
  have key : (∏ k ∈ univ.erase i, (g i - y * g k) * Ring.inverse (g i - g k)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (g i - y * g k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [mul_assoc, Ring.inverse_mul_cancel _ (by simpa using (hu i k hki).neg), mul_one]
  rw [← key]
  ring

end UpperTheory.Gal.Schur
end
end
