module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle014
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem corner_eq {R : Type} [CommRing R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] {τ : E →ₗ[R] R}
    {e : Fin n → E} (h : IsTrGMA τ e) (i : Fin n) (z : E) (hz : e i * z * e i = z) : z = τ z • e i := by
  have hidem : e i * e i = e i := (h.idem.idem i).eq
  have h1 : e i * z = z := by
    calc e i * z = e i * (e i * z * e i) := by rw [hz]
      _ = e i * z * e i := by rw [← mul_assoc, ← mul_assoc, hidem]
      _ = z := hz
  calc z = e i * z * e i := hz.symm
    _ = τ (e i * z) • e i := h.corner i z
    _ = τ z • e i := by rw [h1]

private theorem tr_single {O : Type} [CommRing O] {n : ℕ} (o i j : Fin n) (c : O) (A : Matrix (Fin n) (Fin n) O) :
    ((c • Matrix.single o i (1 : O)) * A * (c • Matrix.single j o (1 : O))).trace = c ^ 2 * A i j := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.single_mul_mul_single]
  simp [Matrix.trace_smul, pow_two, mul_assoc]

theorem UpperTheory.V.Th.Coc.smat :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {n : ℕ} {E : Type} [Ring E] [Algebra R E] (x : R →ₐ[O] O) (ρ : E →+* Matrix (Fin n) (Fin n) O) (τ : E →ₗ[R] R) (e : Fin n → E) (c : O), 1 ≤ n → IsTrGMA τ e → (∀ i, ρ (e i) = Matrix.single i i 1) → (∀ a, (ρ a).trace = x (τ a)) → (∀ Z, ∃ a, ρ a = c • Z) → ∃ (s : E →ₗ[R] Matrix (Fin n) (Fin n) R) (β : R), x β = c ^ (2 * n) ∧ (∀ a b, s a * s b = β • s (a * b)) ∧ (∀ a, (s a).map x = c ^ (2 * n) • ρ a) ∧ ∀ a, (s a).trace = β * τ a := by
  intro O R _ _ _ n E _ _ x ρ τ e c hn hT hρe htr hsurj
  classical
  obtain ⟨o, -⟩ : ∃ o : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
  have hidem : ∀ i, e i * e i = e i := fun i => (hT.idem.idem i).eq
  have hρE : ∀ (i j : Fin n) (r : O), Matrix.single i i (1 : O) * (r • Matrix.single i j (1 : O)) *
      Matrix.single j j (1 : O) = r • Matrix.single i j (1 : O) := by
    intro i j r
    ext u v
    simp only [Matrix.single_mul_mul_single, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp_all
  choose hh hhρ using fun i : Fin n => hsurj (Matrix.single o i (1 : O))
  choose kk kkρ using fun j : Fin n => hsurj (Matrix.single j o (1 : O))
  obtain ⟨p, hp⟩ : ∃ p : Fin n → E, ∀ i, p i = e o * hh i * e i := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n → E, ∀ j, q j = e j * kk j * e o := ⟨_, fun _ => rfl⟩
  have ρp : ∀ i, ρ (p i) = c • Matrix.single o i (1 : O) := by
    intro i
    simp only [hp, map_mul, hρe, hhρ]
    exact hρE o i c
  have ρq : ∀ j, ρ (q j) = c • Matrix.single j o (1 : O) := by
    intro j
    simp only [hq, map_mul, hρe, kkρ]
    exact hρE j o c
  have hpl : ∀ i, e o * p i = p i := by
    intro i
    simp only [hp, ← mul_assoc, hidem]
  have hpr : ∀ i, p i * e i = p i := by
    intro i
    simp only [hp, mul_assoc, hidem]
  have hql : ∀ j, e j * q j = q j := by
    intro j
    simp only [hq, ← mul_assoc, hidem]
  have hqr : ∀ j, q j * e o = q j := by
    intro j
    simp only [hq, mul_assoc, hidem]
  have hcorner : ∀ i z, e i * z * e i = z → z = τ z • e i := fun i z hz => corner_eq hT i z hz
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → R, ∀ j, γ j = τ (q j * p j) := ⟨_, fun _ => rfl⟩
  have hqp : ∀ j, q j * p j = γ j • e j := by
    intro j
    rw [hγ]
    apply hcorner
    rw [← mul_assoc, hql, mul_assoc, hpr]
  have hxγ : ∀ j, x (γ j) = c ^ 2 := by
    intro j
    rw [hγ, ← htr, map_mul, ρq, ρp]
    have h := tr_single j o o c (1 : Matrix (Fin n) (Fin n) O)
    rw [Matrix.mul_one, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hρs : ∀ r : R, ρ (r • e o) = Matrix.single o o (x r) := by
    intro r
    have hz : e o * (r • e o) * e o = r • e o := by
      rw [mul_smul_comm, smul_mul_assoc, hidem, hidem]
    have h1 : ρ (r • e o) = Matrix.single o o ((ρ (r • e o)) o o) := by
      conv_lhs => rw [← hz]
      rw [map_mul, map_mul, hρe, Matrix.single_mul_mul_single, one_mul, mul_one]
    have h2 : (ρ (r • e o)).trace = x r := by
      rw [htr, map_smul, hT.one, smul_eq_mul, mul_one]
    rw [h1] at h2 ⊢
    congr 1
    simpa [Matrix.trace, Matrix.single_apply] using h2
  obtain ⟨Γj, hΓj⟩ : ∃ Γj : Fin n → R, ∀ j, Γj j = ∏ l ∈ Finset.univ.erase j, γ l := ⟨_, fun _ => rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Fin n → E, ∀ j, q' j = q j * (Γj j • e o) := ⟨_, fun _ => rfl⟩
  have hq'p : ∀ j, q' j * p j = (∏ l, γ l) • e j := by
    intro j
    rw [hq', mul_smul_comm, smul_mul_assoc, hqr, hqp, smul_smul, hΓj,
      Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hsum : ∑ j, q' j * p j = (∏ l, γ l) • (1 : E) := by
    simp_rw [hq'p]
    rw [← Finset.smul_sum, hT.idem.complete]
  have hq'r : ∀ j, q' j * e o = q' j := by
    intro j
    rw [hq', mul_assoc, smul_mul_assoc, hidem]
  have hX : ∀ i j a, p i * a * q' j = τ (p i * a * q' j) • e o := by
    intro i j a
    apply hcorner
    have h : e o * (p i * a * q' j) * e o = (e o * p i) * a * (q' j * e o) := by simp only [mul_assoc]
    rw [h, hpl, hq'r]
  have hτmul : ∀ i k j a b, τ (p i * a * q' k) * τ (p k * b * q' j) =
      τ (p i * a * q' k * (p k * b * q' j)) := by
    intro i k j a b
    have hl : e o * (p k * b * q' j) = p k * b * q' j := by simp only [← mul_assoc, hpl]
    conv_rhs => rw [hX i k a, smul_mul_assoc, hl, map_smul, smul_eq_mul]
  have hρq' : ∀ j, ρ (q' j) = x (Γj j) • (c • Matrix.single j o (1 : O)) := by
    intro j
    rw [hq', map_mul, ρq, hρs]
    ext u v
    simp only [Matrix.smul_mul, Matrix.single_mul_single_same, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> ring
  have hxΓj : ∀ j, x (Γj j) = (c ^ 2) ^ (n - 1) := by
    intro j
    rw [hΓj, map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  let s : E →ₗ[R] Matrix (Fin n) (Fin n) R :=
    { toFun := fun a => Matrix.of fun i j => τ (p i * a * q' j)
      map_add' := by
        intro a b
        ext i j
        simp only [Matrix.of_apply, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
      map_smul' := by
        intro r a
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul,
          RingHom.id_apply] }
  have hs : ∀ a i j, s a i j = τ (p i * a * q' j) := fun _ _ _ => rfl
  refine ⟨s, ∏ l, γ l, ?_, ?_, ?_, ?_⟩
  · rw [map_prod]
    simp_rw [hxγ]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  · intro a b
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, hs, smul_eq_mul]
    simp_rw [hs, hτmul]

    rw [← map_sum]
    have hrw : ∑ k, p i * a * q' k * (p k * b * q' j) = p i * a * (∑ k, q' k * p k) * b * q' j := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [mul_assoc]
    rw [hrw, hsum, mul_smul_comm, mul_one, smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul,
      mul_assoc (p i) a b]
  · intro a
    ext i j
    rw [Matrix.map_apply, hs, Matrix.smul_apply, smul_eq_mul, ← htr, map_mul, map_mul, ρp, hρq',
      Matrix.mul_smul, Matrix.trace_smul, tr_single, smul_eq_mul, hxΓj, ← mul_assoc, ← pow_succ,
      ← pow_mul, Nat.sub_add_cancel hn]
  · intro a
    have hc : ∀ i, τ (p i * a * q' i) = τ (a * (q' i * p i)) := by
      intro i
      rw [mul_assoc, hT.comm, mul_assoc]
    simp only [Matrix.trace, Matrix.diag_apply, hs, hc]

    rw [← map_sum, ← Finset.mul_sum, hsum, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem flagC_up_mul {X : Type} [CommRing X] {n : ℕ} {A B : Matrix (Fin n) (Fin n) X}
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) :
    (∀ i j, j < i → (A * B) i j = 0) ∧ ∀ i, (A * B) i i = A i i * B i i := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k j (lt_of_lt_of_le hij h), mul_zero]
  · intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA i k h, zero_mul]
    · rw [hB k i h, mul_zero]

private theorem flagC_core {X : Type} [CommRing X] {n : ℕ} (A B S T S₁ T₁ r D : Matrix (Fin n) (Fin n) X) (d : X)
    (g a : Fin n → X) (hAS : A * S = d • (1 : Matrix (Fin n) (Fin n) X)) (hTB : T * B = d • (1 : Matrix (Fin n) (Fin n) X))
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (hg : ∀ i, A i i * B i i * g i = d * d)
    (hL : ∀ i j, j < i → (S₁ * T + S * T₁) i j = 0) (hr : ∀ i j, j < i → r i j = 0)
    (hM : ∀ i j, j < i → (S₁ * r * T + S * D * T + S * r * T₁) i j = 0)
    (hMd : ∀ i, (S₁ * r * T + S * D * T + S * r * T₁) i i = g i * a i + r i i * (S₁ * T + S * T₁) i i) :
    (∀ i j, j < i → ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i j = 0) ∧
      ∀ i, ((d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r)) i i = (d * d) * a i := by
  have e1 : A * (S₁ * r * T + S * D * T + S * r * T₁) * B =
      A * S₁ * r * (T * B) + (A * S) * D * (T * B) + (A * S) * r * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have e2 : A * (S₁ * T + S * T₁) * B = A * S₁ * (T * B) + (A * S) * (T₁ * B) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have key : (d * d) • D - (r * (-(d • (T₁ * B))) - (-(d • (T₁ * B))) * r) =
      A * (S₁ * r * T + S * D * T + S * r * T₁) * B - A * (S₁ * T + S * T₁) * B * r := by
    rw [e1, e2, hAS, hTB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_mul, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul]
    abel
  obtain ⟨m1, m2⟩ := flagC_up_mul hA hM
  obtain ⟨m3, m4⟩ := flagC_up_mul m1 hB
  obtain ⟨l1, l2⟩ := flagC_up_mul hA hL
  obtain ⟨l3, l4⟩ := flagC_up_mul l1 hB
  obtain ⟨l5, l6⟩ := flagC_up_mul l3 hr
  rw [key]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.sub_apply, m3 i j hij, l5 i j hij, sub_zero]
  · rw [Matrix.sub_apply, m4, m2, l6, l4, l2, hMd, ← hg i]
    ring

theorem UpperTheory.V.Th.Coc.flagC :
    ∀ {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (S T : Matrix (Fin n) (Fin n) O) (Δ : Fin n → O), (∀ i, Δ i ≠ 0) → (∀ a b, b < a → S a b = 0 ∧ T a b = 0) → (∀ i, S i i = Δ i ∧ T i i = Δ i) → (∀ a b, a ≠ b → (S * T) a b = 0) → ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra O X] (S₁ T₁ : Matrix (Fin n) (Fin n) X), (∀ a b, a ≠ b → (S₁ * bar X T + bar X S * T₁) a b = 0) → ∃ Y : Matrix (Fin n) (Fin n) X, ∀ (r : Matrix (Fin n) (Fin n) O) (D : Matrix (Fin n) (Fin n) X) (a : Fin n → X), (∀ i j, j < i → r i j = 0) → (∀ i j, j < i → (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i j = 0) → (∀ i, (S₁ * bar X r * bar X T + bar X S * D * bar X T + bar X S * bar X r * T₁) i i = (Δ i * Δ i) • a i + r i i • (S₁ * bar X T + bar X S * T₁) i i) → (∀ i j, j < i → (c₁ • D - (bar X r * Y - Y * bar X r)) i j = 0) ∧ ∀ i, (c₁ • D - (bar X r * Y - Y * bar X r)) i i = c₁ • a i := by
  intro O _ _ n S T Δ hΔ hup hdg hST
  have hS : ∀ i j, j < i → S i j = 0 := fun i j h => (hup i j h).1
  have hT : ∀ i j, j < i → T i j = 0 := fun i j h => (hup i j h).2
  obtain ⟨d, e, hd, he⟩ : ∃ (d : O) (e : Fin n → O), d ≠ 0 ∧ ∀ i, Δ i * Δ i * e i = d :=
    ⟨∏ i, Δ i * Δ i, fun i => ∏ k ∈ Finset.univ.erase i, Δ k * Δ k,
      Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hΔ i) (hΔ i),
      fun i => Finset.mul_prod_erase Finset.univ (fun k => Δ k * Δ k) (Finset.mem_univ i)⟩
  have hG : S * T = Matrix.diagonal fun i => Δ i * Δ i := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [(flagC_up_mul hS hT).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2]
    · rw [hST i j h, Matrix.diagonal_apply_ne _ h]
  have hdet : S.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hS i j h)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by rw [(hdg i).1]; exact hΔ i
  have hE : ∀ i j, j < i → Matrix.diagonal e i j = 0 := fun i j h => Matrix.diagonal_apply_ne _ h.ne'
  have h1 : S * T * Matrix.diagonal e = d • (1 : Matrix (Fin n) (Fin n) O) := by
    rw [hG, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    simp only [he]
  have h2 : T * Matrix.diagonal e * S = d • (1 : Matrix (Fin n) (Fin n) O) := by
    have h3 : S.adjugate * (S * T * Matrix.diagonal e * S) = S.det • (T * Matrix.diagonal e * S) := by
      rw [Matrix.mul_assoc S, Matrix.mul_assoc S, ← Matrix.mul_assoc S.adjugate, Matrix.adjugate_mul,
        Matrix.smul_mul, Matrix.one_mul]
    rw [h1, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.adjugate_mul, smul_comm] at h3
    exact (smul_right_injective _ hdet h3).symm
  have hmul : ∀ (X : Type) [CommRing X] [Algebra O X] (P Q : Matrix (Fin n) (Fin n) O),
      bar X P * bar X Q = bar X (P * Q) := fun X _ _ P Q => (Matrix.map_mul).symm
  have hone : ∀ (X : Type) [CommRing X] [Algebra O X],
      bar X (d • (1 : Matrix (Fin n) (Fin n) O)) = algebraMap O X d • (1 : Matrix (Fin n) (Fin n) X) := by
    intro X _ _
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hbar : ∀ (X : Type) [CommRing X] [Algebra O X] (P : Matrix (Fin n) (Fin n) O), (∀ i j, j < i → P i j = 0) →
      ∀ i j, j < i → bar X P i j = 0 := fun X _ _ P hP i j h => by simp [hP i j h]
  refine ⟨d * d, mul_ne_zero hd hd, fun X _ _ S₁ T₁ hL =>
    ⟨-(algebraMap O X d • (T₁ * bar X (Matrix.diagonal e * S))), fun r D a hr hM hMd => ?_⟩⟩
  have := flagC_core (bar X (T * Matrix.diagonal e)) (bar X (Matrix.diagonal e * S)) (bar X S) (bar X T) S₁ T₁ (bar X r) D
    (algebraMap O X d) (fun i => algebraMap O X (Δ i * Δ i)) a (by rw [hmul, h2, hone])
    (by rw [hmul, ← Matrix.mul_assoc, h2, hone]) (hbar X _ (flagC_up_mul hT hE).1) (hbar X _ (flagC_up_mul hE hS).1)
    (fun i => by
      change algebraMap O X ((T * Matrix.diagonal e) i i) * algebraMap O X ((Matrix.diagonal e * S) i i) * _ = _
      rw [← map_mul, ← map_mul, ← map_mul, (flagC_up_mul hT hE).2,
        (flagC_up_mul hE hS).2, Matrix.diagonal_apply_eq, (hdg i).1, (hdg i).2, ← he i]
      congr 1
      ring)
    (fun i j h => hL i j h.ne') (hbar X r hr) hM
    (fun i => by rw [hMd i, Algebra.smul_def, Algebra.smul_def]; rfl)
  rw [← map_mul, algebraMap_smul] at this
  refine ⟨this.1, fun i => ?_⟩
  rw [this.2 i, Algebra.smul_def]
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {n : ℕ}

end SlopeTestRemainingChoices

private theorem dualM_mul_dualM {X : Type} [CommRing X] {n : ℕ} (A B A' B' : Matrix (Fin n) (Fin n) X) :
    dualM A B * dualM A' B' = dualM (A * A') (A * B' + B * A') := by
  ext i j
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.fst_sum]
  · simp [Matrix.mul_apply, dualM, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]

theorem UpperTheory.V.Th.Coc.rel :
    ∀ {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing X] [Algebra O X] {n : ℕ} {G H : Type} [Group G] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (τ : MonoidAlgebra R G → R) (c : O) (d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X) (φ : H → G) (ψ : Fin n → H → R) (g : Fin n → H), IsLift x δ (repR x ρ) τ c d → repR x ρ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → d (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 → (List.ofFn fun i => dualM (bar X (ρ (φ (g i)))) (d (MonoidAlgebra.single (φ (g i)) 1)) - (TrivSqZeroExt.inl (algebraMap O X (x (ψ i (g i)))) + TrivSqZeroExt.inr (c • δ (ψ i (g i))) : DualNumber X) • (1 : Matrix (Fin n) (Fin n) (DualNumber X))).prod = 0 := by
  intro O R X _ _ _ _ _ n G H _ x δ ρ τ c d φ ψ g hL h1 h2
  have hbar1 : bar X (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    simp [bar]
  have hd1 : d 1 = 0 := by
    have := hL.mul 1 1
    simp only [mul_one, map_one, hbar1, one_mul] at this
    have h' : d 1 + d 1 = d 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h'
  have hrep : ∀ (k : G) (r : R), repR x ρ (MonoidAlgebra.single k r) = x r • ρ k := by
    intro k r
    simp [repR, GDet.repAlg]
  have hs : ∀ r : R, MonoidAlgebra.single (1 : G) r = r • (1 : MonoidAlgebra R G) := by
    intro r
    simp [MonoidAlgebra.one_def, MonoidAlgebra.smul_single']
  let Φ : MonoidAlgebra R G →* Matrix (Fin n) (Fin n) (DualNumber X) :=
    { toFun := fun a => dualM (bar X (repR x ρ a)) (d a)
      map_one' := by
        ext i j
        · by_cases hij : i = j <;> simp [dualM, hbar1, Matrix.one_apply, hij]
        · by_cases hij : i = j <;> simp [dualM, hd1, Matrix.one_apply, hij]
      map_mul' := by
        intro a b
        rw [dualM_mul_dualM, hL.mul, map_mul]
        simp [bar, Matrix.map_mul, add_comm] }
  have key := map_list_prod Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i)))
  have hz : Φ (List.ofFn fun i => MonoidAlgebra.single (φ (g i)) (1 : R) - MonoidAlgebra.single 1 (ψ i (g i))).prod = 0 := by
    show dualM _ _ = 0
    rw [h1, h2]
    ext i j <;> simp [dualM, bar]
  rw [hz, List.map_ofFn] at key
  rw [key]
  congr 2
  funext i
  show _ = dualM (bar X (repR x ρ (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))) (d (MonoidAlgebra.single (φ (g i)) 1 - MonoidAlgebra.single 1 (ψ i (g i))))
  rw [map_sub, map_sub, hrep, hrep, hs (ψ i (g i)), hL.smul, hd1, map_one, map_one, map_one, one_smul, hbar1]
  ext a b
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
  · by_cases hab : a = b <;> simp [dualM, bar, Matrix.one_apply, hab]
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem UpperTheory.V.Th.Coc.flagA_full {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) {n : ℕ} (p : Fin n → P) :
    (List.ofFn fun j => φ (p j)).prod = φ (∏ j, p j) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  rfl

private theorem UpperTheory.V.Th.Coc.flagA_split {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) :
    ∀ {n : ℕ} (p : Fin n → P) (F : Fin n → M) (i : Fin n), (∀ j, j ≠ i → F j = φ (p j)) →
      (List.ofFn F).prod = φ (∏ j, if j < i then p j else 1) * F i * φ (∏ j, if i < j then p j else 1) := by
  intro n
  induction n with
  | zero => intro p F i; exact i.elim0
  | succ n ih =>
    intro p F i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro h
      have h1 : (fun j : Fin n => F j.succ) = fun j => φ (p j.succ) := funext fun j => h _ (Fin.succ_ne_zero j)
      rw [List.ofFn_succ, List.prod_cons, h1, flagA_full φ fun j : Fin n => p j.succ]
      simp [Fin.prod_univ_succ]
    · intro h
      rw [List.ofFn_succ, List.prod_cons,
        ih (fun j => p j.succ) (fun j => F j.succ) k (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e))),
        h 0 (Fin.succ_ne_zero k).symm]
      simp [Fin.prod_univ_succ, mul_assoc]

private theorem UpperTheory.V.Th.Coc.flagA_entry {A : Type} [CommRing A] {n : ℕ} (u Z : Matrix (Fin n) (Fin n) A) (α : Fin n → A)
    (a b : Fin n) : (kS u α * Z * kT u α) a b = (kEl u α a * Z * kEl u α b) a b := by
  simp [kS, kT, Matrix.mul_apply]

theorem UpperTheory.V.Th.Coc.flagA :
    ∀ {A H : Type} [CommRing A] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) A) (ψ : Fin n → H → A) (s : H), (∀ g : Fin n → H, (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) A)).prod = 0) → (∀ a b, a ≠ b → (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ g, (∀ a b, b < a → (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ i, (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) i i = ψ i g * (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) i i := by
  intro A H _ n r ψ s hrel
  let φ : Polynomial A →* Matrix (Fin n) (Fin n) A := (Polynomial.aeval (r s)).toRingHom.toMonoidHom
  let p : Fin n → Polynomial A := fun j => Polynomial.X - Polynomial.C (ψ j s)
  have hp : ∀ j, φ (p j) = r s - ψ j s • (1 : Matrix (Fin n) (Fin n) A) := by
    intro j
    simp [φ, p, Algebra.algebraMap_eq_smul_one]
  have hk : ∀ a, kEl (r s) (fun i => ψ i s) a = φ (∏ j ∈ Finset.univ.erase a, p j) := fun a => rfl
  have hfull : φ (∏ j, p j) = 0 := by
    rw [← flagA_full φ p]
    simp only [hp]
    exact hrel fun _ => s
  have h0 : ∀ a b, a ≠ b → kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b = 0 := by
    intro a b hab
    obtain ⟨q, hq⟩ : p a ∣ ∏ j ∈ Finset.univ.erase b, p j := Finset.dvd_prod_of_mem _ (by simp [hab])
    rw [hk, hk, ← map_mul, hq, ← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ a), map_mul, hfull, zero_mul]
  have h1 : ∀ g a b, b ≤ a → kEl (r s) (fun i => ψ i s) a * r g * kEl (r s) (fun i => ψ i s) b =
      ψ a g • (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) := by
    intro g a b hab
    have h := hrel (Function.update (fun _ => s) a g)
    rw [flagA_split φ p _ a (fun j hj => by rw [Function.update_of_ne hj, hp])] at h
    rw [Function.update_self, ← Finset.prod_filter, ← Finset.prod_filter] at h
    obtain ⟨q, hq⟩ : ∏ j ∈ Finset.univ.filter (· < a), p j ∣ ∏ j ∈ Finset.univ.erase a, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hj.ne]
    obtain ⟨q', hq'⟩ : ∏ j ∈ Finset.univ.filter (a < ·), p j ∣ ∏ j ∈ Finset.univ.erase b, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [(lt_of_le_of_lt hab hj).ne']
    have h2 : kEl (r s) (fun i => ψ i s) a * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
        kEl (r s) (fun i => ψ i s) b = 0 := by
      rw [hk, hk, hq, hq', mul_comm _ q, map_mul, map_mul]
      calc _ = φ q * (φ (∏ j ∈ Finset.univ.filter (· < a), p j) * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
            φ (∏ j ∈ Finset.univ.filter (a < ·), p j)) * φ q' := by simp only [mul_assoc]
        _ = 0 := by rw [h, mul_zero, zero_mul]
    rw [mul_sub, sub_mul, sub_eq_zero, mul_smul_comm, mul_one, smul_mul_assoc] at h2
    exact h2
  have he : ∀ a b, (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b =
      (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) a b := by
    intro a b
    simpa using flagA_entry (r s) 1 (fun i => ψ i s) a b
  refine ⟨fun a b hab => ?_, fun g => ⟨fun a b hab => ?_, fun i => ?_⟩⟩
  · rw [he, h0 a b hab]; rfl
  · rw [flagA_entry, h1 g a b hab.le, h0 a b hab.ne', smul_zero]; rfl
  · rw [flagA_entry, h1 g i i le_rfl, he]; rfl
end

section

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.trRep :
    ∀ {O R G : Type} [CommRing O] [CommRing R] [Algebra O R] [Group G] {n : ℕ} (D : GDet n R G) (x : R →ₐ[O] O) (ρ : G →* Matrix (Fin n) (Fin n) O), 1 ≤ n → D.map x.toRingHom = GDet.ofRep ρ → (∀ y, (repR x ρ y).trace = x (D.tr y)) ∧ (∀ (r : R) y, repR x ρ (r • y) = x r • repR x ρ y) ∧ ∃ t : MonoidAlgebra R G →ₗ[R] R, ∀ y, t y = D.tr y := by
  intro O R G _ _ _ _ n D x ρ hn h
  refine ⟨fun y => ?_, fun r y => ?_, ?_⟩
  · have h1 := (((CA.d_gmap D).2.2.1 x.toRingHom y).2 1)
    rw [h] at h1
    have h2 := (CA.d_toDet (GDet.ofRep ρ) (MonoidAlgebra.mapRingHom G x.toRingHom y)).2.2.1
    rw [CA.d_toDet_ofRep.1 ρ, (CA.d_ofRep _ _ _).2.2.1 hn] at h2
    exact h2.trans h1
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | single g a =>
      rw [MonoidAlgebra.smul_single, repR_single, repR_single, smul_eq_mul, map_mul, mul_smul]
  · obtain ⟨t, ht⟩ := (CA.d_tr D.toDet).1 hn
    exact ⟨t, fun y => (ht y).trans (CA.d_toDet D y).2.2.1⟩
end
