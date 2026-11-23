module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Mathlib.Algebra.Group.Commute.Basic

@[expose] public section

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.monoidExt :
    ∀ (T H : Type) [CommGroup T] [Monoid H] (P : Submonoid T) (f : T → H), (∀ t : T, ∃ a ∈ P, ∃ b ∈ P, t = a * b⁻¹) → f 1 = 1 → (∀ a ∈ P, ∀ b ∈ P, f (a * b) = f a * f b) → (∀ a ∈ P, IsUnit (f a)) → ∃! θ : T →* Hˣ, ∀ a ∈ P, (θ a : H) = f a := by
  intro T H _ _ P f hgen h1 hmul hunit
  classical
  let U : T → Hˣ := fun a => if h : a ∈ P then (hunit a h).unit else 1
  have hU : ∀ a ∈ P, (U a : H) = f a := by
    intro a ha
    simp [U, ha]
  have hUmul : ∀ a ∈ P, ∀ b ∈ P, U (a * b) = U a * U b := by
    intro a ha b hb
    ext
    rw [Units.val_mul, hU _ (P.mul_mem ha hb), hU a ha, hU b hb, hmul a ha b hb]
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, Commute (U a) (U b) := by
    intro a ha b hb
    show U a * U b = U b * U a
    rw [← hUmul a ha b hb, ← hUmul b hb a ha, mul_comm a b]
  have hU1 : U 1 = 1 := Units.ext (by rw [hU 1 P.one_mem, h1]; rfl)
  have hwd : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ d ∈ P, a * b⁻¹ = c * d⁻¹ →
      U a * (U b)⁻¹ = U c * (U d)⁻¹ := by
    intro a ha b hb c hc d hd h
    have h' : a * d = c * b := by
      calc a * d = (a * b⁻¹) * (b * d) := by rw [mul_assoc, inv_mul_cancel_left]
        _ = (c * d⁻¹) * (b * d) := by rw [h]
        _ = c * b := by rw [mul_comm b d, mul_assoc, inv_mul_cancel_left]
    have hU' : U a * U d = U c * U b := by
      rw [← hUmul a ha d hd, ← hUmul c hc b hb, h']
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, (hcomm d hd b hb).inv_left.eq, ← mul_assoc,
      eq_mul_inv_iff_mul_eq, hU']
  choose A hA B hB hAB using hgen
  let θ : T →* Hˣ :=
    { toFun := fun t => U (A t) * (U (B t))⁻¹
      map_one' := by
        show U (A 1) * (U (B 1))⁻¹ = 1
        rw [hwd (A 1) (hA 1) (B 1) (hB 1) 1 P.one_mem 1 P.one_mem (by rw [← hAB 1]; simp), hU1]
        simp
      map_mul' := fun t s => by
        show U (A (t * s)) * (U (B (t * s)))⁻¹ = U (A t) * (U (B t))⁻¹ * (U (A s) * (U (B s))⁻¹)
        have he : A (t * s) * (B (t * s))⁻¹ = (A t * A s) * (B t * B s)⁻¹ := by
          rw [← hAB (t * s)]
          calc t * s = A t * (B t)⁻¹ * (A s * (B s)⁻¹) := by rw [← hAB t, ← hAB s]
            _ = A t * A s * (B t * B s)⁻¹ := by
              rw [_root_.mul_inv_rev]
              ac_rfl
        rw [hwd _ (hA _) _ (hB _) _ (P.mul_mem (hA t) (hA s)) _ (P.mul_mem (hB t) (hB s)) he,
          hUmul _ (hA t) _ (hA s), hUmul _ (hB t) _ (hB s), _root_.mul_inv_rev]
        have c1 : Commute (U (B t))⁻¹ (U (A s)) := (hcomm _ (hB t) _ (hA s)).inv_left
        have c2 : Commute (U (B t))⁻¹ (U (B s))⁻¹ := (hcomm _ (hB t) _ (hB s)).inv_inv
        simp only [mul_assoc]
        rw [← mul_assoc (U (B t))⁻¹, c1.eq, mul_assoc, c2.eq] }
  have hθ : ∀ a ∈ P, (θ a : H) = f a := by
    intro a ha
    show ((U (A a) * (U (B a))⁻¹ : Hˣ) : H) = f a
    rw [hwd (A a) (hA a) (B a) (hB a) a ha 1 P.one_mem (by rw [← hAB a]; simp), hU1, inv_one,
      mul_one, hU a ha]
  refine ⟨θ, hθ, fun θ' h' => ?_⟩
  have agree : ∀ a ∈ P, θ' a = θ a := fun a ha => Units.ext ((h' a ha).trans (hθ a ha).symm)
  apply MonoidHom.ext
  intro t
  rw [hAB t, map_mul, map_mul, map_inv, map_inv, agree _ (hA t), agree _ (hB t)]
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

private theorem tamePair_aeval_comm {K A : Type} [CommRing K] [Ring A] [Algebra K A]
    (P X Y : A) (h : P * X = Y * P) (p : Polynomial K) :
    P * Polynomial.aeval X p = Polynomial.aeval Y p * P := by
  have hp : ∀ k : ℕ, P * X ^ k = Y ^ k * P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, pow_succ, mul_assoc]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), mul_add, add_mul, hp, hq]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, hp]

private theorem tamePair_inj {K : Type} [Field K] {n : ℕ} (c : K) (hc : c ≠ 0)
    (P : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)))
    (ha : ∀ i j, a i ≠ c * a j) (Y : Matrix (Fin n) (Fin n) K) (hY : P * Y = Y * (c • P)) :
    Y = 0 := by
  have h1 := tamePair_aeval_comm (K := K) Y (c • P) P hY.symm P.charpoly
  rw [Matrix.aeval_self_charpoly, zero_mul, hP] at h1
  have hu : ∀ i, IsUnit (Polynomial.aeval (c • P) (Polynomial.X - Polynomial.C (a i))) := by
    intro i
    have e : Polynomial.aeval (c • P) (Polynomial.X - Polynomial.C (a i)) =
        (-c) • (Matrix.scalar (Fin n) (a i / c) - P) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      ext k l
      by_cases hkl : k = l
      · subst hkl
        simp [Matrix.algebraMap_matrix_apply]
        field_simp
        ring
      · simp [Matrix.algebraMap_matrix_apply, hkl]
    rw [e, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, ← Matrix.eval_charpoly, hP,
      Polynomial.eval_prod, isUnit_iff_ne_zero]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hc)) (Finset.prod_ne_zero_iff.mpr ?_)
    intro j _ h
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    apply ha i j
    rw [sub_eq_zero, div_eq_iff hc] at h
    rw [h, mul_comm]
  have hs : ∀ s : Finset (Fin n),
      IsUnit (Polynomial.aeval (c • P) (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i)))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, map_mul]; exact (hu i).mul ih
  exact (hs Finset.univ).mul_left_eq_zero.mp h1

private theorem tamePair_binom {K : Type} [CommRing K] (q : ℕ) :
    ∃ r : Polynomial K, (1 + Polynomial.X) ^ q =
      1 + (q : Polynomial K) * Polynomial.X + Polynomial.X ^ 2 * r := by
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨(q : Polynomial K) + r + Polynomial.X * r, ?_⟩
    rw [pow_succ, hr]; push_cast; ring

private theorem tamePair_nil {K A : Type} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] (q : ℕ) (P Q X : A) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hinj : ∀ Y : A, P * Y = Y * ((q : K) • P) → Y = 0)
    (hX : IsNilpotent X) (h : P * (1 + X) = (1 + X) ^ q * P) : X = 0 := by
  obtain ⟨r, hr⟩ := tamePair_binom (K := K) q
  set g : Polynomial K := (q : Polynomial K) * Polynomial.X + Polynomial.X ^ 2 * r with hg
  have h1 : P * X = Polynomial.aeval X g * P := by
    have := congrArg (Polynomial.aeval X) hr
    rw [map_pow, map_add (f := _), map_one, Polynomial.aeval_X, add_assoc, map_add (f := _), map_one, ← hg] at this
    rw [this, mul_add, add_mul, mul_one, one_mul] at h
    exact add_left_cancel h
  have h2 : ∀ p : Polynomial K, P * Polynomial.aeval X p * Q = Polynomial.aeval X (p.comp g) := by
    intro p
    rw [tamePair_aeval_comm P X _ h1, mul_assoc, hPQ, mul_one, Polynomial.aeval_comp]
  let ψ : A →ₗ[K] A := (LinearMap.mulRight K Q).comp (LinearMap.mulLeft K P) - (q : K) • LinearMap.id
  have hψ : ∀ Y, ψ Y = P * Y * Q - (q : K) • Y := fun _ => rfl
  have hψa : ∀ p : Polynomial K, ψ (Polynomial.aeval X p) =
      Polynomial.aeval X (p.comp g - (q : Polynomial K) * p) := by
    intro p
    rw [hψ, h2, map_sub, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hψi : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro Y hY
    apply hinj
    rw [hψ, sub_eq_zero] at hY
    rw [mul_smul_comm, ← smul_mul_assoc, ← hY, mul_assoc, hQP, mul_one]
  let L : Polynomial K →ₗ[K] A :=
    (Polynomial.aeval X).toLinearMap.comp (LinearMap.mulLeft K (Polynomial.X ^ 2))
  have hL : ∀ p, L p = Polynomial.aeval X (Polynomial.X ^ 2 * p) := fun _ => rfl
  have hW : ∀ Y ∈ LinearMap.range L, ψ Y ∈ LinearMap.range L := by
    rintro _ ⟨p, rfl⟩
    refine ⟨((q : Polynomial K) + Polynomial.X * r) ^ 2 * p.comp g - (q : Polynomial K) * p, ?_⟩
    rw [hL, hL, hψa]
    congr 1
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
    generalize p.comp g = t
    rw [hg]; ring
  have hsurj : Function.Surjective (ψ.restrict hW) := by
    apply LinearMap.injective_iff_surjective.mp
    intro x y hxy
    exact Subtype.ext (hψi (congrArg Subtype.val hxy))
  have hXW : ψ X ∈ LinearMap.range L := by
    refine ⟨r, ?_⟩
    have := hψa Polynomial.X
    rw [Polynomial.aeval_X] at this
    rw [this, hL, Polynomial.X_comp]
    congr 1
    rw [hg]; ring
  obtain ⟨⟨_, p, rfl⟩, hw⟩ := hsurj ⟨_, hXW⟩
  have h3 : L p = X := hψi (congrArg Subtype.val hw)
  rw [hL, map_mul, map_pow, Polynomial.aeval_X] at h3
  have hc : Commute X (Polynomial.aeval X p) := tamePair_aeval_comm X X X rfl p
  have hn : IsNilpotent (X * Polynomial.aeval X p) := hc.isNilpotent_mul_right hX
  have h4 : X * (1 - X * Polynomial.aeval X p) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, h3, sub_self]
  exact hn.isUnit_one_sub.mul_left_eq_zero.mp h4

theorem UpperTheory.V.AlgebraTools.tamePair :
    ∀ (K : Type) [Field K] [CharZero K] (n q : ℕ) (P T : GL (Fin n) K) (a : Fin n → K), 2 ≤ q → P * T * P⁻¹ = T ^ q → (P : Matrix (Fin n) (Fin n) K).charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)) → (∀ i j, a i ≠ (q : K) * a j) → IsNilpotent (((T ^ (q - 1) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) → T ^ (q - 1) = 1 ∧ P * T = T * P := by
  intro K _ _ n q P T a hq hPT hP ha hN
  have hq0 : (q : K) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : P * T ^ (q - 1) = (T ^ (q - 1)) ^ q * P := by
    rw [← pow_mul, mul_comm (q - 1) q, pow_mul, ← hPT, conj_pow, inv_mul_cancel_right]
  have h2 := tamePair_nil (K := K) q (P : Matrix (Fin n) (Fin n) K)
    ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) _ (Units.mul_inv P) (Units.inv_mul P)
    (tamePair_inj (q : K) hq0 _ a hP ha) hN (by
      rw [add_sub_cancel, ← Units.val_mul, h1, Units.val_mul, Units.val_pow_eq_pow_val _ q])
  have h3 : T ^ (q - 1) = 1 := Units.ext (sub_eq_zero.mp h2)
  refine ⟨h3, ?_⟩
  have h4 : T ^ q = T := by
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h3
    rw [pow_succ, h3, one_mul]
  rw [h4] at hPT
  exact mul_inv_eq_iff_eq_mul.mp hPT
end
