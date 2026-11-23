module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section split

variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))

theorem ffH_fst' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).1 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).1 * (x l).1 := by
  simp only [ffH, Prod.fst_sum, Prod.fst_mul]

theorem ffH_snd' (y x : Fin M → k × k) :
    (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J y x).2 = ∑ i, ∑ l, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (y i) * J i l).2 * (x l).2 := by
  simp only [ffH, Prod.snd_sum, Prod.snd_mul]

theorem ffH_self_of_snd (x : Fin M → k × k) (h : ∀ l, (x l).2 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

theorem ffH_self_of_fst (x : Fin M → k × k) (h : ∀ l, (x l).1 = 0) : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 := by
  refine Prod.ext ?_ ?_
  · rw [ffH_fst']
    simp [h]
  · rw [ffH_snd']
    simp [h]

theorem notFree_iff (x : Fin M → k × k) :
    (¬ ∀ c : k × k, c • x = 0 → c = 0) ↔ (∀ l, (x l).1 = 0) ∨ (∀ l, (x l).2 = 0) := by
  constructor
  · intro h
    push_neg at h
    obtain ⟨c, hc, hne⟩ := h
    by_cases h1 : c.1 = 0
    · right
      have h2 : c.2 ≠ 0 := fun h2 => hne (Prod.ext h1 h2)
      intro l
      have hl := congrArg Prod.snd (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_mul, Pi.zero_apply, Prod.snd_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h2
    · left
      intro l
      have hl := congrArg Prod.fst (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Pi.zero_apply, Prod.fst_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h1
  · rintro (h | h) hfree
    · have h1 := hfree (1, 0) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1
    · have h1 := hfree (0, 1) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1

theorem perp_surj {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) (w : Fin a' → k × k) :
    ∃ x : Fin M → k × k, ∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = w j := by
  classical
  set c := T0⁻¹.mulVec w with hc
  refine ⟨fun l => ∑ m, Y m l * c m, fun j => ?_⟩

  have h1 : ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j)
      (fun l => ∑ m, Y m l * c m) = ∑ m, T0 j m * c m := by
    rw [← hY]
    simp only [ffGram, ffH, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [h1]
  have h2 : T0.mulVec c = w := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h3 := congrFun h2 j
  simpa [Matrix.mulVec, dotProduct] using h3

private theorem natCard_ker_mul_card_pow_eq_of_surjective [Finite k] {a' : ℕ} (B : Matrix (Fin a') (Fin M) k)
    (hB : Function.Surjective B.mulVec) :
    Nat.card {u : Fin M → k // B.mulVec u = 0} * Nat.card k ^ a' = Nat.card k ^ M := by
  classical
  have _ := Fintype.ofFinite k
  have hs : LinearMap.range (Matrix.mulVecLin B) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ?_
    obtain ⟨u, hu⟩ := hB v
    exact ⟨u, by rw [Matrix.mulVecLin_apply, hu]⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin B)
  rw [hs, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
  have e : {u : Fin M → k // B.mulVec u = 0} ≃ LinearMap.ker (Matrix.mulVecLin B) :=
    Equiv.subtypeEquivRight fun u => by simp [Matrix.mulVecLin_apply]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (Matrix.mulVecLin B)), ← pow_add]
  congr 1
  omega

theorem card_half_snd [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).1
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).1 =
        B.mulVec (fun l => (x l).1) j := by
    intro x j
    rw [ffH_fst']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (w' j, 0))
    exact ⟨fun l => (x l).1, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).2 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).1, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (u.1 l, 0), fun j => by
        refine Prod.ext ?_ ?_
        · rw [hB]
          exact congrFun u.2 j
        · rw [ffH_snd']
          simp, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext rfl (x.2.2 l).symm)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

theorem card_half_fst [Finite k] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} * Nat.card k ^ a' =
      Nat.card k ^ M := by
  classical
  let B : Matrix (Fin a') (Fin M) k := fun j l =>
    ∑ i, ((RingEquiv.prodComm (R := k) (S := k)).toRingHom (Y j i) * J i l).2
  have hB : ∀ (x : Fin M → k × k) j,
      (ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x).2 =
        B.mulVec (fun l => (x l).2) j := by
    intro x j
    rw [ffH_snd']
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsurj : Function.Surjective B.mulVec := by
    intro w'
    obtain ⟨x, hx⟩ := perp_surj J T0 hu Y hY (fun j => (0, w' j))
    exact ⟨fun l => (x l).2, funext fun j => by rw [← hB x j, hx j]⟩
  have e : {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J
      (Y j) x = 0) ∧ ∀ l, (x l).1 = 0} ≃ {u : Fin M → k // B.mulVec u = 0} :=
    { toFun := fun x => ⟨fun l => (x.1 l).2, funext fun j => by
        rw [← hB, x.2.1 j]
        rfl⟩
      invFun := fun u => ⟨fun l => (0, u.1 l), fun j => by
        refine Prod.ext ?_ ?_
        · rw [ffH_fst']
          simp
        · rw [hB]
          exact congrFun u.2 j, fun l => rfl⟩
      left_inv := fun x => Subtype.ext (funext fun l => Prod.ext (x.2.2 l).symm rfl)
      right_inv := fun u => rfl }
  rw [Nat.card_congr e]
  exact natCard_ker_mul_card_pow_eq_of_surjective B hsurj

end split

end PI.OmVe
end
end

section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

theorem ffH_add_right (x y z : Fin M → K) : ffH σ J x (y + z) = ffH σ J x y + ffH σ J x z := by
  simp [ffH, mul_add, Finset.sum_add_distrib]

theorem ffH_smul_right (c : K) (x y : Fin M → K) : ffH σ J x (c • y) = c * ffH σ J x y := by
  unfold ffH
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ffH_zero_right (x : Fin M → K) : ffH σ J x 0 = 0 := by
  simp [ffH]

theorem ffH_zero_left (x : Fin M → K) : ffH σ J 0 x = 0 := by
  simp [ffH]

theorem ffH_sum_right {ι : Type} (s : Finset ι) (c : ι → K) (x : Fin M → K) (y : ι → Fin M → K) :
    ffH σ J x (∑ l ∈ s, c l • y l) = ∑ l ∈ s, c l * ffH σ J x (y l) := by
  classical
  refine Finset.induction_on s (by simp [ffH_zero_right]) ?_
  intro l s hl ih
  rw [Finset.sum_insert hl, Finset.sum_insert hl, ffH_add_right, ffH_smul_right, ih]

theorem ffH_herm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → K) :
    ffH σ J y x = σ (ffH σ J x y) := by
  unfold ffH

  simp only [map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem single_mulVec' {a : ℕ} (i₀ : Fin a) (v : Fin a → K) :
    (Matrix.single i₀ i₀ (1 : K)) *ᵥ v = Pi.single i₀ (v i₀) := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]

theorem indep_iff {a : ℕ} {T : Matrix (Fin a) (Fin a) K} (i₀ : Fin a) (hc : ∀ j, T j i₀ = 0)
    (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (X : Fin a → Fin M → K) (hX : ffGram σ J X = T) :
    LinearIndependent K X ↔ ∀ c : K, c • X i₀ = 0 → c = 0 := by
  classical
  constructor
  · intro hli c hc0
    have := Fintype.linearIndependent_iff.1 hli (Pi.single i₀ c) (by simp [Pi.single_apply, hc0])
    simpa using this i₀
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro g hg

    have hT : T *ᵥ g = 0 := by
      funext j
      have := congrArg (ffH σ J (X j)) hg
      rw [ffH_sum_right σ J Finset.univ g (X j) X, ffH_zero_right] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hX]
      simpa [ffGram, mul_comm] using this
    have hTe : T *ᵥ Pi.single i₀ (g i₀) = 0 := by
      funext j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hc]
    have heq : (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g =
        (T + Matrix.single i₀ i₀ (1 : K)) *ᵥ Pi.single i₀ (g i₀) := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, hT, hTe, single_mulVec', single_mulVec', Pi.single_eq_same]

    have hinv : (T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K)) = 1 :=
      Matrix.nonsing_inv_mul _ hu
    have hg' : g = Pi.single i₀ (g i₀) := by
      calc g = ((T + Matrix.single i₀ i₀ (1 : K))⁻¹ * (T + Matrix.single i₀ i₀ (1 : K))) *ᵥ g := by
            rw [hinv, Matrix.one_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ g) := by
            rw [Matrix.mulVec_mulVec]
        _ = (T + Matrix.single i₀ i₀ (1 : K))⁻¹ *ᵥ ((T + Matrix.single i₀ i₀ (1 : K)) *ᵥ
              Pi.single i₀ (g i₀)) := by rw [heq]
        _ = Pi.single i₀ (g i₀) := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hsum : ∑ i, g i • X i = g i₀ • X i₀ := by
      rw [hg']
      simp [Pi.single_apply]
    have h0 : g i₀ = 0 := h _ (hsum ▸ hg)
    intro i
    rw [hg', h0]
    simp

theorem det_corOne {a : ℕ} (T : Matrix (Fin (a + 1)) (Fin (a + 1)) K) (i₀ : Fin (a + 1))
    (hr : ∀ j, T i₀ j = 0) (t : K) :
    (T + Matrix.single i₀ i₀ t).det = t * (T.submatrix i₀.succAbove i₀.succAbove).det := by

  rw [Matrix.det_succ_row _ i₀, Finset.sum_eq_single i₀
    (fun j _ hj => by simp [hr, Matrix.single_apply, Ne.symm hj]) (by simp)]
  have hsub : (T + Matrix.single i₀ i₀ t).submatrix i₀.succAbove i₀.succAbove =
      T.submatrix i₀.succAbove i₀.succAbove := by
    ext a b
    simp [Matrix.single_apply, (Fin.succAbove_ne i₀ a).symm]
  rw [hsub]
  simp [hr, Matrix.single_apply, ← two_mul, pow_mul]

end gen

end PI.OmVe
end
end
