module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem card_doubleCoset_mul_card_inter {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w : G) :
    (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k).card *
      (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card = Nat.card H * Nat.card K := by
  have hmaps : ∀ p ∈ (Finset.univ : Finset (H × K)),
      (p.1 : G) * w * p.2 ∈ Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k := by
    intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun p : H × K => (p.1 : G) * w * p.2) (s := Finset.univ) hmaps
  have hfib : ∀ y ∈ (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k),
      ((Finset.univ : Finset (H × K)).filter fun p => (p.1 : G) * w * p.2 = y).card =
        (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨h0, hh0, k0, hk0, rfl⟩ := hy
    symm
    refine Finset.card_bij'
      (fun t ht => ((⟨h0 * t, H.mul_mem hh0 (Finset.mem_filter.1 ht).2.1⟩ : H),
        (⟨w⁻¹ * t⁻¹ * w * k0, by
          have hinv := K.inv_mem (Finset.mem_filter.1 ht).2.2
          rw [show (w⁻¹ * t * w)⁻¹ = w⁻¹ * t⁻¹ * w by group] at hinv
          exact K.mul_mem hinv hk0⟩ : K)))
      (fun p _ => h0⁻¹ * (p.1 : G)) ?_ ?_ ?_ ?_
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have e : (p.1 : G) = h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹ := by
        rw [← hp]; group
      refine ⟨H.mul_mem (H.inv_mem hh0) p.1.2, ?_⟩
      rw [e, show w⁻¹ * (h0⁻¹ * (h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹)) * w = k0 * (p.2 : G)⁻¹ by group]
      exact K.mul_mem hk0 (K.inv_mem p.2.2)
    · intro t _
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have e : (p.2 : G) = w⁻¹ * (p.1 : G)⁻¹ * (h0 * w * k0) := by
        rw [← hp]; group
      ext
      · simp
      · simp only
        rw [e]
        group
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Fintype.card_prod, ← Finset.card_univ,
    hcard]

private theorem sum_conj_double_coset_eq_of_invariant {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w h k : G)
    (hh : h ∈ H) (hk : k ∈ K) (lam φ : G → ℂ)
    (hlam : ∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x)
    (hφ : ∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) :
    (∑ x : G, if x ∈ H ∧ (h * w * k)⁻¹ * x * (h * w * k) ∈ K then
        lam x * φ ((h * w * k)⁻¹ * x * (h * w * k)) else 0) =
      ∑ x : G, if x ∈ H ∧ w⁻¹ * x * w ∈ K then lam x * φ (w⁻¹ * x * w) else 0 := by
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun x => ?_).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have e1 : (h * w * k)⁻¹ * (h * x * h⁻¹) * (h * w * k) = k⁻¹ * (w⁻¹ * x * w) * k := by group
  simp only [e1]
  have eH : h * x * h⁻¹ ∈ H ↔ x ∈ H := by
    rw [H.mul_mem_cancel_right (H.inv_mem hh), H.mul_mem_cancel_left hh]
  have eK : k⁻¹ * (w⁻¹ * x * w) * k ∈ K ↔ w⁻¹ * x * w ∈ K := by
    rw [K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]
  by_cases hx : x ∈ H ∧ w⁻¹ * x * w ∈ K
  · have hc := hφ k⁻¹ (K.inv_mem hk) _ hx.2
    rw [inv_inv] at hc
    rw [if_pos hx, if_pos ⟨eH.2 hx.1, eK.2 hx.2⟩, hlam h hh x hx.1, hc]
  · rw [if_neg hx, if_neg]
    rintro ⟨h1, h2⟩
    exact hx ⟨eH.1 h1, eK.1 h2⟩

theorem mackey_doubleCoset_pairing : ∀ (G : Type) [Group G] [Fintype G] (H K : Subgroup G) (ι : Type) (R : Finset ι) (w : ι → G), (∀ x : G, ∃! i, i ∈ R ∧ ∃ h ∈ H, ∃ k ∈ K, x = h * w i * k) → ∀ (lam φ : G → ℂ), (∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x) → (∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) → (Nat.card H : ℂ)⁻¹ * ∑ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ * ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) = ∑ i ∈ R, ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ * ∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0 := by
  intro G _ _ H K ι R w hR lam φ hlam hφ
  have hHpos : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hKpos : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : ∀ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ *
        ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) =
      (Nat.card K : ℂ)⁻¹ * ∑ y : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0) := by
    intro x
    by_cases hx : x ∈ H
    · rw [if_pos hx]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y⁻¹ * x * y ∈ K
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]; ring
      · rw [if_neg hy, if_neg (fun hc => hy hc.2)]; ring
    · simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ y : G, (∑ x : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0)) =
      ∑ i ∈ R, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0 := by
    intro y
    obtain ⟨i, ⟨hi, h, hhH, k, hkK, rfl⟩, huniq⟩ := hR y
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [if_pos ⟨h, hhH, k, hkK, rfl⟩]
      exact sum_conj_double_coset_eq_of_invariant H K (w i) h k hhH hkK lam φ hlam hφ
    · intro j hj hji
      rw [if_neg]
      intro hP
      exact hji (huniq j ⟨hj, hP⟩)
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm]
  have h3 : ∀ i ∈ R, (∑ y : G, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0) =
      ((Nat.card H : ℂ) * Nat.card K) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0) := by
    intro i _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w i * k).card : ℂ) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) =
          (Nat.card H : ℂ) * Nat.card K := by
      exact_mod_cast card_doubleCoset_mul_card_inter H K (w i)
    have hI : ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) ≠ 0 := by
      have hmem : (1 : G) ∈ Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K := by
        simp [H.one_mem, K.one_mem]
      exact_mod_cast (Finset.card_pos.2 ⟨1, hmem⟩).ne'
    rw [← hc, mul_inv_cancel_right₀ hI]
  rw [Finset.sum_congr rfl h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (Nat.card H : ℂ)⁻¹ * Nat.card H = 1 := inv_mul_cancel₀ hHpos
  have e2 : (Nat.card K : ℂ)⁻¹ * Nat.card K = 1 := inv_mul_cancel₀ hKpos
  linear_combination
    ((Nat.card K : ℂ)⁻¹ * Nat.card K *
      ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e1 +
    (((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e2

end GlobalTheory.GLm
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem starProjection_eq_add_inf_orthogonal {n : ℕ}
    (U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : U ≤ V) (x : EuclideanSpace ℂ (Fin n)) :
    V.starProjection x = U.starProjection x + (Uᗮ ⊓ V).starProjection x := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact V.add_mem (h (U.starProjection_apply_mem x))
      (((Uᗮ ⊓ V).starProjection_apply_mem x).2)
  · rw [← Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h, ← Submodule.inf_orthogonal,
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h]
    refine ⟨?_, ?_⟩
    · rw [← sub_sub]
      exact Uᗮ.sub_mem (U.sub_starProjection_mem_orthogonal x)
        (((Uᗮ ⊓ V).starProjection_apply_mem x).1)
    · rw [add_comm, ← sub_sub]
      refine (Uᗮ ⊓ V)ᗮ.sub_mem ((Uᗮ ⊓ V).sub_starProjection_mem_orthogonal x) ?_
      exact Submodule.orthogonal_le (inf_le_left (a := Uᗮ) (b := V))
        (U.le_orthogonal_orthogonal (U.starProjection_apply_mem x))

theorem starProjection_flag_eq_sum {n a : ℕ}
    (W : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h0 : W 0 = ⊥) (hm : Monotone W)
    (l : Fin (a + 1)) (x : EuclideanSpace ℂ (Fin n)) :
    (W l).starProjection x = ∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val),
      ((W i.castSucc)ᗮ ⊓ W i.succ).starProjection x := by
  induction l using Fin.induction with
  | zero =>
    have := (W 0).starProjection_apply_mem x
    have h2 : (W 0).starProjection x = 0 := by
      have h3 : (W 0).starProjection x ∈ (⊥ : Submodule ℂ _) := h0 ▸ this
      simpa using h3
    simp [h2]
  | succ i ih =>
    have hf : univ.filter (fun k : Fin a => k.val < i.succ.val)
        = insert i (univ.filter (fun k : Fin a => k.val < i.castSucc.val)) := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.val_succ, Fin.val_castSucc,
        Fin.ext_iff]
      omega
    rw [hf, Finset.sum_insert (by simp), ← ih, add_comm]
    exact starProjection_eq_add_inf_orthogonal _ _ (hm (Fin.castSucc_le_succ i)) x

theorem exists_orthonormal_frame_of_flag (n a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (h0 : W 0 = ⊥) (hm : Monotone W)
    (hj : ∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) :
    ∃ T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ, (∀ i, (T i)ᴴ * T i = 1) ∧
      (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ),
        y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : Fin (a + 1) → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun l => (W l).map e.toLinearMap
  have hV0 : V 0 = ⊥ := by simp [V, h0]
  have hVm : Monotone V := fun l k h => Submodule.map_mono (hm h)
  have hVr : ∀ l, Module.finrank ℂ (V l) = Module.finrank ℂ (W l) :=
    fun l => LinearEquiv.finrank_map_eq e (W l)
  let P : Fin a → Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    fun i => (V i.castSucc)ᗮ ⊓ V i.succ
  have hP : ∀ i, Module.finrank ℂ (P i) = j i := by
    intro i
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Fin.castSucc_le_succ i))
    have h2 := hj i
    rw [hVr, hVr] at h1
    change Module.finrank ℂ ↥((V i.castSucc)ᗮ ⊓ V i.succ) = j i
    omega
  let b : ∀ i, OrthonormalBasis (Fin (j i)) ℂ (P i) :=
    fun i => (stdOrthonormalBasis ℂ (P i)).reindex (finCongr (hP i))
  let T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ :=
    fun i => Matrix.of fun r c => (b i c : EuclideanSpace ℂ (Fin n)) r
  have hT : ∀ i k c d, ((T i)ᴴ * T k) c d
      = inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) := by
    intro i k c d
    simp only [Matrix.mul_apply, conjTranspose_apply, T, of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hlt : ∀ i k : Fin a, i < k → ∀ c d,
      inner ℂ (b i c : EuclideanSpace ℂ (Fin n)) (b k d : EuclideanSpace ℂ (Fin n)) = 0 := by
    intro i k h c d
    have h1 : (b i c : EuclideanSpace ℂ (Fin n)) ∈ V k.castSucc :=
      hVm (Fin.succ_le_castSucc_iff.2 h) (b i c).2.2
    exact Submodule.inner_right_of_mem_orthogonal h1 (b k d).2.1
  have hproj : ∀ i y, (T i * (T i)ᴴ) *ᵥ y = ((P i).starProjection (e y)).ofLp := by
    intro i y
    rw [(b i).starProjection_eq_sum_rankOne, ← Matrix.mulVec_mulVec]
    ext r
    simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply, WithLp.ofLp_sum,
      Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.mulVec, dotProduct, T, of_apply, conjTranspose_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i
    ext c d
    rw [hT, ← Submodule.coe_inner, orthonormal_iff_ite.1 (b i).orthonormal, Matrix.one_apply]
  · intro i k hik
    ext c d
    rw [hT, Matrix.zero_apply]
    rcases lt_or_gt_of_ne hik with h | h
    · exact hlt i k h c d
    · rw [inner_eq_zero_symm]
      exact hlt k i h d c
  · intro l y
    have h1 : y ∈ W l ↔ e y ∈ V l := by
      simp [V]
    rw [h1, ← Submodule.starProjection_eq_self_iff, starProjection_flag_eq_sum V hV0 hVm,
      Matrix.sum_mulVec]
    simp only [hproj]
    constructor
    · intro h
      have h2 := congrArg WithLp.ofLp h
      rw [WithLp.ofLp_sum] at h2
      exact h2
    · intro h
      apply WithLp.ofLp_injective 2
      rw [WithLp.ofLp_sum]
      exact h

end GlobalTheory
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem sum_two_pow_pred_mul_pow_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 4) (q : ℕ) :
    ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * r ^ J ≤ 2 * r * (1 - (1 / 2) ^ q) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have h2 : (2 * r) ^ n ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have h3 : (2 : ℝ) ^ n * r ^ (n + 1) = r * (2 * r) ^ n := by rw [mul_pow]; ring
    have h4 : r * (2 * r) ^ n ≤ r * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left h2 h0
    have h5 : 2 * r * (1 - (1 / 2 : ℝ) ^ (n + 1))
        = 2 * r * (1 - (1 / 2) ^ n) + r * (1 / 2 : ℝ) ^ n := by ring
    rw [h3, h5]
    linarith

theorem sum_two_pow_pred_mul_exp_neg_le :
    ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  intro q x hx
  have hr : ∀ J : ℕ, Real.exp (-(1 / 2 * J * x)) = Real.exp (-(x / 2)) ^ J := by
    intro J
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hr]
  have h0 : 0 < Real.exp (-(x / 2)) := Real.exp_pos _
  have h1 : Real.exp (-(x / 2)) ≤ 1 / 4 := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by norm_num)
    have := Real.add_one_le_exp (x / 2)
    linarith
  refine (sum_two_pow_pred_mul_pow_le _ h0.le h1 q).trans ?_
  have h2 : Real.exp (-(1 / 3 * x)) = Real.exp (x / 6) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (2 : ℝ) ≤ Real.exp (x / 6) := by
    have := Real.add_one_le_exp (x / 6)
    linarith
  have h4 : (0 : ℝ) ≤ (1 / 2) ^ q := by positivity
  rw [h2]
  nlinarith [mul_nonneg h0.le h4, mul_le_mul_of_nonneg_right h3 h0.le]

end GlobalTheory
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem volume_sum_sq_le_sq (d : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = ENNReal.ofReal (s ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have h1 : {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' Metric.closedBall 0 s := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff,
      EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_le_left hs]
  rw [h1, (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, Measure.addHaar_closedBall _ _ hs]
  simp

theorem tendsto_volume_sublevel_div_pow (d : ℕ) (N : (Fin d → ℝ) → ℝ) (hc : ContinuousAt N 0)
    (h0 : N 0 = 0) (hl : ∀ x, ∑ i, x i ^ 2 ≤ N x) (hu : ∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) :
    Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} /
        ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hV
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d) * V) (nhds 1) (nhds V) := by
      have h1 : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d)) (nhds 1) (nhds 1) := by
        have : Continuous (fun t : ℝ => ENNReal.ofReal (t ^ d)) :=
          ENNReal.continuous_ofReal.comp (continuous_pow d)
        simpa using this.tendsto 1
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hVt)
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), a < ENNReal.ofReal (t ^ d) * V ∧ 0 < t :=
      nhdsWithin_le_nhds ((hcont.eventually (lt_mem_nhds ha)).and (lt_mem_nhds one_pos))
    obtain ⟨t, ⟨hta, ht0⟩, ht1⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht1 : t < 1 := ht1
    have hδ : 0 < 4 * (1 - t ^ 2) := by nlinarith
    have hN : ∀ᶠ x in nhds (0 : Fin d → ℝ), N x < 4 * (1 - t ^ 2) :=
      hc.eventually (gt_mem_nhds (by rw [h0]; exact hδ))
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hN
    have hr : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), r < η :=
      nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hr, self_mem_nhdsWithin] with r hrη hr0
    have hr0 : 0 < r := hr0
    refine hta.trans_le ?_
    have hp : ENNReal.ofReal (r ^ d) ≠ 0 := by
      simpa using pow_pos hr0 d
    rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)]
    have e : ENNReal.ofReal (t ^ d) * V * ENNReal.ofReal (r ^ d)
        = volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ (t * r) ^ 2} := by
      rw [volume_sum_sq_le_sq d (by positivity), mul_pow,
        ENNReal.ofReal_mul (by positivity), ← hV]
      ring
    rw [e]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    have htr : t * r < η := by nlinarith
    have hx' : dist x 0 < η := by
      rw [dist_zero_right]
      refine lt_of_le_of_lt ?_ htr
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have : x i ^ 2 ≤ (t * r) ^ 2 :=
        (Finset.single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)).trans hx
      exact abs_le_of_sq_le_sq this (by positivity)
    have h1 := hball hx'
    have h2 := hu x
    have h3 : 0 ≤ N x := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hl x)
    rw [Real.sqrt_le_left hr0.le]
    have h4 : t ^ 2 * N x ≤ t ^ 2 * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1.le h3
      nlinarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with r hr0
    have hr0 : 0 < r := hr0
    refine lt_of_le_of_lt ?_ ha
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm, ← volume_sum_sq_le_sq d hr0.le]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Real.sqrt_le_left hr0.le] at hx
    exact (hl x).trans hx

end GlobalTheory
end
