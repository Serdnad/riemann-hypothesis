module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

theorem keySplit (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - (2 * x ^ (n + 1) - 1) - (x - 1) * (x ^ (2 * n + 1) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - x ^ (-(n : ℤ))) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  field_simp
  ring

theorem dcount_split {k : Type} [Field k] [Finite k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k)) {a' : ℕ}
    (haM : a' ≤ M) (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0} + 1 =
      2 * Nat.card k ^ (M - a') := by
  classical
  have := Fintype.ofFinite k
  have hk0 : 0 < Nat.card k := Nat.card_pos
  have e2 : Nat.card k ^ M = Nat.card k ^ (M - a') * Nat.card k ^ a' := by
    rw [← pow_add, Nat.sub_add_cancel haM]
  have h1 := card_half_snd J T0 hu Y hY
  have h2 := card_half_fst J T0 hu Y hY
  rw [e2] at h1 h2
  have c1 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h1
  have c2 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h2
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at c1 c2 ⊢
  set s1 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0)
  set s2 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0)
  have hs : Finset.univ.filter (fun x : Fin M → k × k =>
      (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0) =
      s1 ∪ s2 := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rw [notFree_iff]
    constructor
    · rintro ⟨hP, _, h | h⟩
      · exact Or.inr ⟨hP, h⟩
      · exact Or.inl ⟨hP, h⟩
    · rintro (⟨hP, h⟩ | ⟨hP, h⟩)
      · exact ⟨hP, ffH_self_of_snd J x h, Or.inr h⟩
      · exact ⟨hP, ffH_self_of_fst J x h, Or.inl h⟩
  have hi : s1 ∩ s2 = {0} := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, ⟨_, h1⟩⟩
      funext l; exact Prod.ext (h1 l) (h2 l)
    · rintro rfl
      exact ⟨⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩, ⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩⟩
  have hu2 := Finset.card_union_add_card_inter s1 s2
  rw [hi, Finset.card_singleton, c1, c2] at hu2
  rw [hs, hu2]
  ring

end PI.OmVe
end
end

section

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

private theorem eq_or_exists_succAbove {n : ℕ} (p i : Fin (n + 1)) :
    i = p ∨ ∃ j, i = p.succAbove j := by
  by_cases h : i = p
  · exact Or.inl h
  · right
    exact (Fin.eq_self_or_eq_succAbove p i).resolve_left h

theorem gram_split (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (t : K) (X : Fin (a' + 1) → Fin M → K) :
    ffGram σ J X = T + Matrix.single i₀ i₀ t ↔
      ffGram σ J (fun j => X (i₀.succAbove j)) = T.submatrix i₀.succAbove i₀.succAbove ∧
        (∀ j, ffH σ J (X (i₀.succAbove j)) (X i₀) = 0) ∧ ffH σ J (X i₀) (X i₀) = t := by
  constructor
  · intro h
    have hh : ∀ i j, PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j :=
      fun i j => congrFun (congrFun h i) j
    refine ⟨?_, fun j => ?_, ?_⟩
    · ext j k
      show PI.VolStabSW.ffH σ J (X (i₀.succAbove j)) (X (i₀.succAbove k)) =
        T (i₀.succAbove j) (i₀.succAbove k)
      have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh]
      simp [hne.symm]
    · have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh, hc]
      simp [hne.symm]
    · rw [hh, hr]
      simp
  · rintro ⟨h1, h2, h3⟩
    ext i j
    show PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j
    rcases eq_or_exists_succAbove i₀ i with hi | ⟨i', hi⟩ <;>
      rcases eq_or_exists_succAbove i₀ j with hj | ⟨j', hj⟩ <;> rw [hi, hj]
    · rw [h3, hr]
      simp
    · have hne : i₀.succAbove j' ≠ i₀ := Fin.succAbove_ne i₀ j'
      rw [ffH_herm σ J hσ hJ (X (i₀.succAbove j')) (X i₀), h2 j', map_zero, hr]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [h2 i', hc]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [show PI.VolStabSW.ffH σ J (X (i₀.succAbove i')) (X (i₀.succAbove j')) =
          T (i₀.succAbove i') (i₀.succAbove j') from congrFun (congrFun h1 i') j']
      simp [hne.symm]

theorem card_split [Finite K] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (t : K) (R : (Fin M → K) → Prop) :
    Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T + Matrix.single i₀ i₀ t ∧ R (X i₀)} =
      Nat.card (Σ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove},
        {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = t ∧ R x}) := by
  have key := fun X => gram_split σ J hσ hJ T i₀ hr hc t X
  apply Nat.card_congr
  refine
    { toFun := fun X => ⟨⟨fun j => X.1 (i₀.succAbove j), ((key X.1).1 X.2.1).1⟩,
        ⟨X.1 i₀, ((key X.1).1 X.2.1).2.1, ((key X.1).1 X.2.1).2.2, X.2.2⟩⟩
      invFun := fun p => ⟨Fin.insertNth (α := fun _ => Fin M → K) i₀ p.2.1 p.1.1,
        (key _).2 ⟨by simpa [Fin.insertNth_apply_succAbove] using p.1.2,
          fun j => by simpa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
            using p.2.2.1 j,
          by simpa [Fin.insertNth_apply_same] using p.2.2.2.1⟩,
        by simpa [Fin.insertNth_apply_same] using p.2.2.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro X
    apply Subtype.ext
    funext i
    rcases eq_or_exists_succAbove i₀ i with hi | ⟨j, hi⟩ <;> rw [hi]
    · simp [Fin.insertNth_apply_same]
    · simp [Fin.insertNth_apply_succAbove]
  · rintro ⟨⟨Y, hY⟩, ⟨x, hx⟩⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      funext j
      simp [Fin.insertNth_apply_succAbove]
    · simp [Fin.insertNth_apply_same]

theorem card_perp [Finite K] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') K) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → K) (hY : ffGram σ J Y = T0) :
    Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y j) x = 0} * Nat.card K ^ a' = Nat.card K ^ M := by
  classical
  let f : (Fin M → K) →+ (Fin a' → K) :=
    AddMonoidHom.mk' (fun x j => PI.VolStabSW.ffH σ J (Y j) x) (fun x y => by
      funext j
      exact ffH_add_right σ J (Y j) x y)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ l, (T0⁻¹ *ᵥ v) l • Y l, ?_⟩
    funext j
    show PI.VolStabSW.ffH σ J (Y j) (∑ l, (T0⁻¹ *ᵥ v) l • Y l) = v j
    rw [ffH_sum_right σ J Finset.univ]
    have hT : ∀ l, PI.VolStabSW.ffH σ J (Y j) (Y l) = T0 j l := fun l => congrFun (congrFun hY j) l
    simp_rw [hT]
    have hinv : T0 *ᵥ (T0⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T0 hu, Matrix.one_mulVec]
    calc ∑ l, (T0⁻¹ *ᵥ v) l * T0 j l = (T0 *ᵥ (T0⁻¹ *ᵥ v)) j := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
      _ = v j := by rw [hinv]
  have hker : Nat.card {x : Fin M → K // ∀ j, PI.VolStabSW.ffH σ J (Y j) x = 0} = Nat.card f.ker := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact ⟨fun h => by ext j; exact h j, fun h j => congrFun h j⟩)
  have hidx : f.ker.index = Nat.card (Fin a' → K) := by
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have hpow : ∀ n : ℕ, Nat.card (Fin n → K) = Nat.card K ^ n := by
    intro n
    rw [Nat.card_fun, Nat.card_fin]
  rw [hker, ← hpow a', ← hidx, AddSubgroup.card_mul_index, hpow M]

theorem card_and_add {α : Type} [Finite α] (G Q : α → Prop) :
    Nat.card {x // G x ∧ Q x} + Nat.card {x // G x ∧ ¬ Q x} = Nat.card {x // G x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr
    (((Equiv.subtypeSubtypeEquivSubtypeInter G Q).symm.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter G (fun x => ¬ Q x)).symm).trans
      (Equiv.sumCompl (fun y : {x // G x} => Q y.1)))

end gen

end PI.OmVe
end
end
