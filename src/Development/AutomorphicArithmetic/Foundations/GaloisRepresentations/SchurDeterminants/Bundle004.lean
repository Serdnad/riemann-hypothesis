module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Bundle002
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
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYClr_of : Comparison₂ → MixDet → SchurYClr ∧ SchurYOffClr := by
  intro hT hM
  constructor
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun a => y ^ shift lam a) (fun _ => 1)
    simp only [Matrix.of_apply, prod_const_one, mul_one] at h
    calc ∑ i, altn (shift lam) (scaleAt y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then y ^ shift lam a else 1) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleAt]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun _ => 1) (fun a => y ^ shift lam a)
    simp only [Matrix.of_apply, one_mul, prod_pow_eq_pow_sum] at h
    calc ∑ i, altn (shift lam) (scaleOff y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then 1 else y ^ shift lam a) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleOff]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring

end UpperTheory.Gal.Schur
end
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.vdmSplit_of :
    PairSplit → VdmSplit := by
  intro h R _ n g i
  have key := h R n (fun a b => g a - g b) i
  have h1 : ∀ k ∈ univ.erase i, (if k < i then g k - g i else g i - g k) =
      (if k < i then (-1 : R) else 1) * (g i - g k) := by
    intro k _
    split_ifs <;> ring
  have h2 : ∏ k ∈ univ.erase i, (if k < i then (-1 : R) else 1) = (-1) ^ (i : ℕ) := by
    have hf : (univ.erase i).filter (· < i) = Finset.Iio i := by
      ext k
      simp only [mem_filter, mem_erase, mem_univ, and_true, mem_Iio]
      exact ⟨fun hk => hk.2, fun hk => ⟨ne_of_lt hk, hk⟩⟩
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one, hf, Fin.card_Iio]
  unfold vdm vdmAway
  rw [key, Finset.prod_congr rfl h1, Finset.prod_mul_distrib, h2]
  ring
end

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem interp_of : SpanProd → Expand → Extract → DenseCoset → Interp := by
  intro hS hE hX hC O K ι _ _ _ _ τ hτ n P hP
  classical
  obtain ⟨k₀, hk₀⟩ := hS K ι n P hP
  refine ⟨k₀, fun k hk N hN a Q hQ => ?_⟩
  obtain ⟨w, hw⟩ := hk₀ k hk
  let A := {α : Fin k → O // (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0}
  let x : A → ι × Fin k → K := fun α => pt τ α.1
  have hdense : ZDense (Set.range x) := by
    have hset : Set.range x =
        {z | ∃ α, (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0 ∧ z = pt τ α} := by
      ext z
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨α.1, α.2.1, α.2.2, rfl⟩
      · rintro ⟨α, h1, h2, rfl⟩
        exact ⟨⟨α, h1, h2⟩, rfl⟩
    rw [hset]
    exact hC O K ι τ hτ N hN k a Q hQ
  have he : Function.Injective
      (fun (m : ι × Fin k → Fin (n + 1)) (p : ι × Fin k) => (m p : ℕ)) := by
    intro m₁ m₂ h
    funext p
    exact Fin.ext (congrFun h p)
  obtain ⟨c, hc⟩ := hX K (ι × Fin k) A (ι × Fin k → Fin (n + 1)) x hdense _ he w
  refine ⟨c.mapDomain Subtype.val, ?_, ?_⟩
  · intro α hα
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hα)
    exact β.2
  · intro R _ _ g
    let F : (Fin k → O) → R := fun α => ∏ t, ∏ s, detOne (algebraMap K R (τ t (α s))) (g t)
    have hmd : ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) =
        c.sum fun β (r : K) => r • F β.1 := by
      apply Finsupp.sum_mapDomain_index
      · intro _
        exact zero_smul K _
      · intro _ r₁ r₂
        exact add_smul r₁ r₂ _
    change ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) = _
    rw [hmd]
    have hexp : ∀ β : A, F β.1 =
        ∑ m : ι × Fin k → Fin (n + 1), algebraMap K R (∏ p, x β p ^ (m p : ℕ)) *
          ∏ p : ι × Fin k, (-1) ^ (m p : ℕ) * aeval (g p.1) (esymm (Fin n) K (m p : ℕ)) := by
      intro β
      have h := hE K R (ι × Fin k) n (fun p => algebraMap K R (pt τ β.1 p)) (fun p => g p.1)
      rw [Fintype.prod_prod_type] at h
      simp only [pt] at h
      simp only [F]
      rw [h]
      apply Finset.sum_congr rfl
      intro m _
      simp only [x, pt, map_prod, map_pow]
    simp only [Finsupp.sum, hexp]
    rw [hw R g]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [← hc m, Finsupp.sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro β _
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    ring

end UpperTheory.Gal.Schur
end
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

private theorem prod_ite_eq_mul_prod_erase {R : Type} [CommRing R] {n : ℕ} (d d' : Fin n → R) (a : Fin n) :
    ∏ b, (if b = a then d b else d' b) = d a * ∏ b ∈ univ.erase a, d' b := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ a), if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [if_neg (Finset.ne_of_mem_erase hb)]

theorem UpperTheory.Gal.Schur.mixDet :
    MixDet := by
  intro R _ n M d d'
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Units.smul_def, zsmul_eq_mul]
  have key : ∀ i, (∏ j, if j = i then d (σ j) else d' (σ j)) =
      ∏ b, (if b = σ i then d b else d' b) := by
    intro i
    rw [← Equiv.prod_comp σ (fun b => if b = σ i then d b else d' b)]
    simp only [σ.injective.eq_iff]
  calc _ = (∑ i, ∏ b, (if b = σ i then d b else d' b)) *
        ((Equiv.Perm.sign σ : ℤ) * ∏ x, M (σ x) x) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [key]
        ring
    _ = _ := by
        congr 1
        rw [Equiv.sum_comp σ (fun a => ∏ b, if b = a then d b else d' b)]
        exact Finset.sum_congr rfl fun a _ => prod_ite_eq_mul_prod_erase d d' a
end

section

open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.schurY_of :
    SchurYClr → VdmSplit → SchurY := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  have hScale : ∀ i, vdm (scaleAt y i g) =
      (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [hSplit R n (scaleAt y i g) i]
    congr 1
    · congr 1
      unfold vdmAway
      refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
      have ha' : a ≠ i := Finset.ne_of_mem_erase ha
      have hb' : b ≠ i := Finset.ne_of_mem_erase hb
      simp [scaleAt, ha', hb']
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := Finset.ne_of_mem_erase hk
      simp [scaleAt, hk']
  have key : ∀ i, (∏ k ∈ univ.erase i, (g k - y * g i) * Ring.inverse (g k - g i)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [show g i - g k = -(g k - g i) by ring, mul_neg, mul_assoc,
      Ring.inverse_mul_cancel _ (hu i k hki), mul_one]
    ring
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))) * vdm g =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ))) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hScale i, hSplit R n g i, ← key i]
  ring
end

section

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem one_mem_eSpan (K : Type) [CommRing K] (n : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n 0 := by
  unfold eSpan
  exact Submodule.subset_span ⟨Fin.elim0, by simp⟩

private theorem esymm_mem_eSpan (K : Type) [CommRing K] (n : ℕ) (i : Fin n) :
    esymm (Fin n) K ((i : ℕ) + 1) ∈ eSpan K n 1 := by
  unfold eSpan
  exact Submodule.subset_span ⟨fun _ => i.succ, by simp⟩

private theorem exists_mem_eSpan (h : ESpanMul) (K : Type) [CommRing K] (n : ℕ)
    (q : MvPolynomial (Fin n) K) :
    ∃ k, aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q ∈ eSpan K n k := by
  obtain ⟨hmono, hmul⟩ := h K n
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    rw [aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (one_mem_eSpan K n)
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨max k l, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hmono _ _ (le_max_left k l) hk) (hmono _ _ (le_max_right k l) hl)
  | mul_X p i hp =>
    obtain ⟨k, hk⟩ := hp
    refine ⟨k + 1, ?_⟩
    rw [map_mul, aeval_X]
    exact hmul _ _ _ _ hk (esymm_mem_eSpan K n i)

theorem spanE_of : ESpanMul → SpanE := by
  intro h K _ n P hP
  obtain ⟨q, hq⟩ := esymmAlgHom_fin_surjective K (le_refl n) ⟨P, (mem_symmetricSubalgebra P).2 hP⟩
  have hq' : aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q = P := by
    have := congrArg Subtype.val hq
    rwa [esymmAlgHom_apply] at this
  obtain ⟨k₀, hk₀⟩ := exists_mem_eSpan h K n q
  refine ⟨k₀, fun k hk => ?_⟩
  have hmem := (h K n).1 _ _ hk hk₀
  rw [hq'] at hmem
  unfold eSpan at hmem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  exact ⟨w, hw.symm⟩

end UpperTheory.Gal.Schur
end
end
