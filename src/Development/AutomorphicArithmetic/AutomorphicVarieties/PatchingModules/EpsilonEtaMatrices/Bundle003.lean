module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern
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
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem up_mul {R : Type} [CommRing R] {n : ℕ} {P Q : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j, j < i → P i j = 0) (hQ : ∀ i j, j < i → Q i j = 0) :
    (∀ i j, j < i → (P * Q) i j = 0) ∧ ∀ i, (P * Q) i i = P i i * Q i i := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c < i
    · rw [hP i c hc, zero_mul]
    · rw [hQ c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP i c h, zero_mul]
    · rw [hQ c i h, mul_zero]

private theorem up_conj {R : Type} [CommRing R] {n : ℕ} {w wi r s y : Matrix (Fin n) (Fin n) R}
    (h1 : wi * w = 1) (h2 : w * wi = 1) (h3 : r * s = 1)
    (hr : ∀ i j, j < i → (wi * r * w) i j = 0) (hs : ∀ i j, j < i → (wi * s * w) i j = 0)
    (hy : ∀ i j, j < i → (wi * y * w) i j = 0) :
    (∀ i j, j < i → (wi * (r * y * s - y) * w) i j = 0) ∧ ∀ i, (wi * (r * y * s - y) * w) i i = 0 := by
  have key : wi * (r * y * s - y) * w = (wi * r * w) * (wi * y * w) * (wi * s * w) - wi * y * w := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc w wi, h2, Matrix.one_mul, ← Matrix.mul_assoc w wi, h2, Matrix.one_mul]
  have hRS : (wi * r * w) * (wi * s * w) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc w wi, h2, Matrix.one_mul, ← Matrix.mul_assoc r s, h3, Matrix.one_mul, h1]
  obtain ⟨hA, hAd⟩ := up_mul hr hy
  obtain ⟨hB, hBd⟩ := up_mul hA hs
  have hRSd := (up_mul hr hs).2
  rw [key]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.sub_apply, hB i j hij, hy i j hij, sub_zero]
  · rw [Matrix.sub_apply, hBd i, hAd i]
    have hi := hRSd i
    rw [hRS, Matrix.one_apply_eq] at hi
    linear_combination (-(wi * y * w) i i) * hi

theorem UpperTheory.V.Pa.bMem :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (m : ℕ) (v : F.Vl) (y : k.M1 (x.Am m)) (β : F.Gv v → k.M1 (x.Am m)), y ∈ k.b1 (x.Am m) v → IsLocallyConstant β → (∀ g, (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = k.ρ1 (x.Am m) (F.φ v g) * y * k.ρ1 (x.Am m) (F.φ v g)⁻¹ - y) → β ∈ k.Zb (x.Am m) v := by
  intro l _ F n x k m v y β hy hβc hβ
  obtain ⟨hone, hmul, -, hw, -⟩ := rho1 l F n x k (x.Am m)
  obtain ⟨h1, h2⟩ := hw v
  have hT := (tri l F n x k (x.Am m) v).1
  have hinv : ∀ g : F.Gv v, k.ρ1 (x.Am m) (F.φ v g) * k.ρ1 (x.Am m) (F.φ v g)⁻¹ = 1 := by
    intro g
    rw [← hmul, mul_inv_cancel, hone]
  have hU : ∀ g : F.Gv v,
      (∀ i j, j < i → (k.wi1 (x.Am m) v * (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i j = 0) ∧
      ∀ i, (k.wi1 (x.Am m) v * (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i i = 0 := by
    intro g
    rw [hβ g]
    refine up_conj h1 h2 (hinv g) (hT g).1 ?_ (fun i j hij => hy i j hij)
    have hg := (hT g⁻¹).1
    rwa [map_inv] at hg
  refine ⟨hβc, fun g h => ?_, fun g => fun i j hij => (hU g).1 i j hij, fun g _ i => (hU g).2 i⟩
  rw [hβ (g * h), hβ g, hβ h, map_mul, hmul, _root_.mul_inv_rev, hmul]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {g n : ℕ}

private def Cnd (lo same : Prop) (d : DD X g) : Prop :=
  (lo → d = 0) ∧ d.ep' = 0 ∧ d.eta = 0 ∧ (same → d.ep = 0) ∧ (¬ same → d.a = 0)

private theorem card_cnd (lo same : Prop) [Decidable lo] [Decidable same] :
    Nat.card {d : DD X g // Cnd lo same d} = Nat.card X ^ (if lo then 0 else if same then 1 else g) := by
  by_cases hlo : lo
  · rw [if_pos hlo, pow_zero, Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩, fun d => Subtype.ext (d.2.1 hlo)⟩
  · by_cases hs : same
    · rw [if_neg hlo, if_pos hs, pow_one]
      exact Nat.card_congr
        { toFun := fun d => d.1.a
          invFun := fun y => ⟨⟨y, 0, 0, 0⟩, fun h => absurd h hlo, rfl, rfl, fun _ => rfl, fun h => absurd hs h⟩
          left_inv := fun d => Subtype.ext (DD.ext rfl (d.2.2.2.2.1 hs).symm d.2.2.1.symm d.2.2.2.1.symm)
          right_inv := fun y => rfl }
    · rw [if_neg hlo, if_neg hs]
      have e : {d : DD X g // Cnd lo same d} ≃ (Fin g → X) :=
        { toFun := fun d => d.1.ep
          invFun := fun f => ⟨⟨0, f, 0, 0⟩, fun h => absurd h hlo, rfl, rfl, fun h => absurd h hs, fun _ => rfl⟩
          left_inv := fun d => Subtype.ext (DD.ext (d.2.2.2.2.2 hs).symm rfl d.2.2.1.symm d.2.2.2.1.symm)
          right_inv := fun f => rfl }
      rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]

private theorem sum_exp (ty : Fin n → Bool) :
    (∑ p : Fin n × Fin n, if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) =
      n + ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ty p.1 = ty p.2).card +
        g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ty p.1 ≠ ty p.2).card) := by
  have h : ∀ p : Fin n × Fin n, (if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) =
      (if p.1 = p.2 then 1 else 0) + ((if p.1 < p.2 ∧ ty p.1 = ty p.2 then 1 else 0) +
        g * (if p.1 < p.2 ∧ ty p.1 ≠ ty p.2 then 1 else 0)) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with hp | hp | hp
    · have h1 : ¬ p.2 < p.1 := not_lt.2 hp.le
      have h2 : p.1 ≠ p.2 := hp.ne
      by_cases ht : ty p.1 = ty p.2 <;> simp [hp, h1, h2, ht]
    · simp [hp]
    · have h1 : ¬ p.1 < p.2 := not_lt.2 hp.le
      have h2 : p.1 ≠ p.2 := hp.ne'
      simp [hp, h1, h2]
  rw [Finset.sum_congr rfl fun p _ => h p, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Nat.cast_id]
  congr 1
  have hd : (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) = Finset.diag Finset.univ := by
    ext p
    simp [Finset.mem_diag]
  rw [hd, Finset.diag_card, Finset.card_univ, Fintype.card_fin]

private theorem card_pat (ty : Fin n → Bool) :
    Nat.card {Z : Matrix (Fin n) (Fin n) (DD X g) // ∀ i j, Cnd (j < i) (ty i = ty j) (Z i j)} =
      Nat.card X ^ (∑ p : Fin n × Fin n, if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) := by
  have e : {Z : Matrix (Fin n) (Fin n) (DD X g) // ∀ i j, Cnd (j < i) (ty i = ty j) (Z i j)} ≃
      ((p : Fin n × Fin n) → {d : DD X g // Cnd (p.2 < p.1) (ty p.1 = ty p.2) d}) :=
    { toFun := fun Z p => ⟨Z.1 p.1 p.2, Z.2 _ _⟩
      invFun := fun f => ⟨fun i j => (f (i, j)).1, fun i j => (f (i, j)).2⟩
      left_inv := fun Z => Subtype.ext rfl
      right_inv := fun f => funext fun p => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact card_cnd _ _

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.bCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (m : ℕ) (v : F.Vl), Nat.card (k.b1 (x.Am m) v) = Nat.card x.K ^ (m * (n + nu n x.a k.g)) := by
  intro l _ F n x k m v
  obtain ⟨_, hK, -⟩ := finAm l F n x m k.g
  obtain ⟨-, hnu, -⟩ := tyCard l F n x v k.g
  obtain ⟨hw, hw'⟩ := (rho1 l F n x k (x.Am m)).2.2.2.1 v
  have hM := (tri l F n x k (x.Am m) v).2
  have c1 : ∀ Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g),
      k.wi1 (x.Am m) v * (k.w1 (x.Am m) v * Y * k.wi1 (x.Am m) v) * k.w1 (x.Am m) v = Y := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hw, Matrix.mul_one, ← Matrix.mul_assoc, hw, Matrix.one_mul]
  have c2 : ∀ Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g),
      k.w1 (x.Am m) v * (k.wi1 (x.Am m) v * Y * k.w1 (x.Am m) v) * k.wi1 (x.Am m) v = Y := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hw', Matrix.mul_one, ← Matrix.mul_assoc, hw', Matrix.one_mul]
  have e : k.b1 (x.Am m) v ≃ {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) //
      ∀ i j, Cnd (j < i) (x.ty v i = x.ty v j) (Y i j)} :=
    { toFun := fun Z => ⟨k.wi1 (x.Am m) v * Z.1.1 * k.w1 (x.Am m) v, fun i j =>
        have hT := (hM Z.1.1).1 Z.1.2 i j
        ⟨Z.2 i j, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2⟩⟩
      invFun := fun Y => ⟨⟨k.w1 (x.Am m) v * Y.1 * k.wi1 (x.Am m) v, (hM _).2 (by
          rw [c1]
          intro i j
          have hc := Y.2 i j
          exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩)⟩, by
          intro i j hij
          show (k.wi1 (x.Am m) v * (k.w1 (x.Am m) v * Y.1 * k.wi1 (x.Am m) v) * k.w1 (x.Am m) v) i j = 0
          rw [c1]
          exact (Y.2 i j).1 hij⟩
      left_inv := fun Z => Subtype.ext (Subtype.ext (c2 _))
      right_inv := fun Y => Subtype.ext (c1 _) }
  rw [Nat.card_congr e, card_pat, sum_exp, hnu, hK, ← pow_mul]
end
