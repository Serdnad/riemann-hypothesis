module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Ideal.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section

section

namespace Bl.FirstLemmaC

theorem goal1 :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] (L : Subgroup.{0} G),
  IsOpen.{0} (SetLike.coe.{0, 0} L) →
    ∀ (t : G),
      IsCompact.{0} (closure.{0} (SetLike.coe.{0, 0} (Subgroup.zpowers.{0} t))) →
        Exists.{1} fun (k : Nat) ↦ And (LT.lt.{0} 0 k) (Membership.mem.{0, 0} L (HPow.hPow.{0, 0, 0} t k))  := by
  intro G _ _ _ L hL t hK
  have : DiscreteTopology (G ⧸ L) := QuotientGroup.discreteTopology hL
  have hfin : ((QuotientGroup.mk : G → G ⧸ L) '' closure (Subgroup.zpowers t : Set G)).Finite :=
    (hK.image QuotientGroup.continuous_mk).finite_of_discrete
  have := hfin.to_subtype
  let f : ℕ → ((QuotientGroup.mk : G → G ⧸ L) '' closure (Subgroup.zpowers t : Set G)) :=
    fun n => ⟨QuotientGroup.mk (t ^ n), t ^ n, subset_closure (Subgroup.npow_mem_zpowers t n), rfl⟩
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h2 : (t ^ a)⁻¹ * t ^ b ∈ L := QuotientGroup.eq.mp (congrArg Subtype.val he)
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨c + 1, Nat.succ_pos c, ?_⟩
    rwa [add_assoc, pow_add, inv_mul_cancel_left] at h2
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h3 := L.inv_mem h2
    refine ⟨c + 1, Nat.succ_pos c, ?_⟩
    rwa [mul_inv_rev, inv_inv, add_assoc, pow_add, inv_mul_cancel_left] at h3

end Bl.FirstLemmaC
end

section

open Matrix

namespace Bl.FirstLemmaB

theorem goal1 {R : Type*} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R)
    (c : R) (hc : c ∈ nonZeroDivisors R) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) R)) :
    P * Q = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hdet : Q.det * P.det = c ^ n := by
    rw [← det_mul, h, det_smul, det_one, mul_one, Fintype.card_fin]
  have hcn : c ^ n ∈ nonZeroDivisors R := pow_mem hc n
  have hP : P.det ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply (mem_nonZeroDivisors_iff_right.mp hcn) x
    rw [← hdet, mul_comm Q.det P.det, ← mul_assoc, hx, zero_mul]
  have h1 : Q * P * P.adjugate = c • P.adjugate := by
    rw [h, smul_mul_assoc, Matrix.one_mul]
  have h2 : P.det • Q = c • P.adjugate := by
    rw [← h1, Matrix.mul_assoc, mul_adjugate, mul_smul_comm, Matrix.mul_one]
  have key : P.det • (P * Q) = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := by
    calc P.det • (P * Q) = P * (P.det • Q) := (mul_smul_comm _ _ _).symm
      _ = P * (c • P.adjugate) := by rw [h2]
      _ = c • (P * P.adjugate) := mul_smul_comm _ _ _
      _ = c • (P.det • (1 : Matrix (Fin n) (Fin n) R)) := by rw [mul_adjugate]
      _ = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := smul_comm _ _ _
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) key
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  have hz : P.det * ((P * Q) i j - (c • (1 : Matrix (Fin n) (Fin n) R)) i j) = 0 := by
    rw [mul_sub, sub_eq_zero]
    simpa only [Matrix.smul_apply, smul_eq_mul] using hij
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_left.mp hP) _ hz)

end Bl.FirstLemmaB
end

section

namespace Bl.ProductIdentities

private lemma prod_erase_one_perm_apply_eq_zero {n : Type} [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (hσ : σ ≠ 1)
    (k : n) : ∏ j ∈ Finset.univ.erase k, (1 : Matrix n n ℂ) (σ j) j = 0 := by
  have hex : ∃ j, j ≠ k ∧ σ j ≠ j := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    apply hσ
    ext x
    simp only [Equiv.Perm.coe_one, id_eq]
    by_cases hx : x = k
    · subst hx
      by_contra hk
      exact hk (σ.injective (h (σ x) hk))
    · exact h x hx
  obtain ⟨j, hjk, hj⟩ := hex
  apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ _⟩)
  simp [hj]

theorem goal1 :
  ∀ {n : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] (A : Real → Matrix.{0, 0, 0} n n Complex)
  (A' : Matrix.{0, 0, 0} n n Complex),
  Eq.{1} (A 0) 1 →
    (∀ (i j : n), HasDerivAt.{0, 0} (fun (t : Real) ↦ A t i j) (A' i j) 0) →
      HasDerivAt.{0, 0} (fun (t : Real) ↦ Matrix.det.{0, 0} (A t)) (Matrix.trace.{0, 0} A') 0 := by
  intro n _ _ A A' h0 hd
  have key : ∀ σ : Equiv.Perm n, HasDerivAt
      (fun t : ℝ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ k, (∏ j ∈ Finset.univ.erase k, A 0 (σ j) j) • A' (σ k) k) 0 := by
    intro σ
    apply HasDerivAt.const_mul
    exact HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i t => A t (σ i) i)
      (f' := fun i => A' (σ i) i) (fun k _ => hd (σ k) k)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => key σ)
  have hfun : (fun t : ℝ => Matrix.det (A t)) =
      fun t => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i := by
    funext t
    exact Matrix.det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · rw [h0]
    simp [Matrix.trace, Matrix.one_apply]
  · intro σ _ hσ
    rw [h0, Finset.sum_eq_zero (fun k _ => by rw [prod_erase_one_perm_apply_eq_zero σ hσ k, zero_smul]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Bl.ProductIdentities
end

section

namespace Bl.FirstLemmaL

theorem goal1 :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G]
  [LocallyCompactSpace.{0} G] [SecondCountableTopology.{0} G] [T2Space.{0} G] [inst_6 : MeasurableSpace.{0} G]
  [BorelSpace.{0} G] {μ : MeasureTheory.Measure.{0} G} [MeasureTheory.Measure.IsHaarMeasure.{0} μ] {φ : G → Complex},
  MeasureTheory.Integrable.{0, 0} φ μ →
    (∀ (w : G),
        Eq.{1}
          (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
            HMul.hMul.{0, 0, 0} (φ y) (φ (HMul.hMul.{0, 0, 0} (Inv.inv.{0} y) w)))
          (φ w)) →
      ∀ {F : G → Complex},
        Continuous.{0, 0} F →
          ∀ {M : Real},
            (∀ (y : G), LE.le.{0} (Norm.norm.{0} (F y)) M) →
              Eq.{1}
                (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
                  HMul.hMul.{0, 0, 0} (φ y)
                    (MeasureTheory.integral.{0, 0} μ fun (z : G) ↦
                      HMul.hMul.{0, 0, 0} (φ z) (F (HMul.hMul.{0, 0, 0} y z))))
                (MeasureTheory.integral.{0, 0} μ fun (w : G) ↦ HMul.hMul.{0, 0, 0} (φ w) (F w)) := by
  intro G _ _ _ _ _ _ _ _ μ _ φ hφ hid F hF M hM
  have hT : MeasureTheory.MeasurePreserving (MeasurableEquiv.shearMulRight G) (μ.prod μ) (μ.prod μ) :=
    MeasureTheory.measurePreserving_prod_mul μ μ
  have hcomp : ((fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) ∘ (MeasurableEquiv.shearMulRight G))
      = fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2)) := by
    funext p
    simp [MeasurableEquiv.shearMulRight, mul_assoc]
  have hGi : MeasureTheory.Integrable (fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2))) (μ.prod μ) := by
    have h1 : MeasureTheory.Integrable (fun p : G × G => φ p.1 * φ p.2) (μ.prod μ) := hφ.mul_prod hφ
    have h2 := h1.mul_bdd (c := M) (g := fun p : G × G => F (p.1 * p.2))
      ((hF.comp continuous_mul).aestronglyMeasurable) (Filter.Eventually.of_forall fun p => hM _)
    refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [mul_assoc]
  have hHi : MeasureTheory.Integrable (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) (μ.prod μ) := by
    rw [← hT.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp]
    exact hGi
  calc ∫ y, φ y * ∫ z, φ z * F (y * z) ∂μ ∂μ
      = ∫ p, (fun p : G × G => φ p.1 * (φ p.2 * F (p.1 * p.2))) p ∂(μ.prod μ) := by
        rw [MeasureTheory.integral_prod _ hGi]
        congr 1
        funext y
        dsimp only
        exact (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ p, ((fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) ∘ (MeasurableEquiv.shearMulRight G)) p ∂(μ.prod μ) := by
        rw [hcomp]
    _ = ∫ p, (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2) p ∂(μ.prod μ) :=
        hT.integral_comp' (fun p : G × G => φ p.1 * φ (p.1⁻¹ * p.2) * F p.2)
    _ = ∫ w, ∫ y, φ y * φ (y⁻¹ * w) * F w ∂μ ∂μ := MeasureTheory.integral_prod_symm _ hHi
    _ = ∫ w, φ w * F w ∂μ := by
        congr 1
        funext w
        rw [MeasureTheory.integral_mul_const, hid]

end Bl.FirstLemmaL
end

section

namespace Bl.FirstLemmaM

noncomputable def goal1 (K : Type*) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

end Bl.FirstLemmaM
end

section

namespace Bl.FirstLemmaE

theorem goal1 :
  ∀ {L : Type} [inst : NontriviallyNormedField.{0} L] [IsUltrametricDist.{0} L] {ι : Type} (s : Finset.{0} ι)
  (f g : ι → L) {r : Real},
  LE.le.{0} 0 r →
    (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (f i)) 1) →
      (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (g i)) 1) →
        (∀ (i : ι), LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (f i) (g i))) r) →
          LE.le.{0}
            (Norm.norm.{0}
              (HSub.hSub.{0, 0, 0} (Finset.prod.{0, 0} s fun (i : ι) ↦ f i) (Finset.prod.{0, 0} s fun (i : ι) ↦ g i)))
            r := by
  intro L _ _ ι s f g r hr hf hg hfg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hG : ‖∏ i ∈ t, g i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hg i)
    have key : f a * ∏ i ∈ t, f i - g a * ∏ i ∈ t, g i
        = f a * (∏ i ∈ t, f i - ∏ i ∈ t, g i) + (f a - g a) * ∏ i ∈ t, g i := by ring
    rw [key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * ‖∏ i ∈ t, f i - ∏ i ∈ t, g i‖ ≤ 1 * r :=
            mul_le_mul (hf a) ih (norm_nonneg _) zero_le_one
        _ = r := one_mul r
    · rw [norm_mul]
      calc ‖f a - g a‖ * ‖∏ i ∈ t, g i‖ ≤ r * 1 :=
            mul_le_mul (hfg a) hG (norm_nonneg _) hr
        _ = r := mul_one r

end Bl.FirstLemmaE
end

section

namespace Bl.FirstLemmaN

noncomputable def goal1 :
  {n : Nat} → Matrix (Fin n) (Fin n) Complex → Prop := fun {n} A =>
  (∀ i j : Fin n, i < j → A i j = 0) ∧ ∀ i : Fin n, A i i = 1

end Bl.FirstLemmaN
end

section

namespace Bl.FirstLemmaK

theorem goal1 :
  ∀ {α : Type} {S : Set.{0} α},
  Set.Finite.{0} S →
    ∀ (f : α → Real),
      (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} 0 (f x)) →
        Exists.{1} fun (r : Real) ↦
          And (LT.lt.{0} 0 r) (And (LE.le.{0} r 1) (∀ (x : α), Membership.mem.{0, 0} S x → LT.lt.{0} r (f x))) := by
  intro α S hS f hf
  rcases S.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, le_rfl, ?_⟩
    intro x hx
    rw [h] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S f hS hne
    have hfa : 0 < f a := hf a ha
    refine ⟨min (f a) 1 / 2, ?_, ?_, ?_⟩
    · have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith
    · have : min (f a) 1 ≤ 1 := min_le_right _ _
      linarith
    · intro x hx
      have h1 : min (f a) 1 ≤ f a := min_le_left _ _
      have h2 : f a ≤ f x := hmin x hx
      have : 0 < min (f a) 1 := lt_min hfa one_pos
      linarith

end Bl.FirstLemmaK
end

section

universe u_1

namespace Bl.MatrixMapSub

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A)
  (X Y : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSub.hSub.{u_1, u_1, u_1} X Y) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSub.hSub.{u_1, u_1, u_1} (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
      (Matrix.map.{u_1, u_1, 0, 0} Y (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ X Y
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

end Bl.MatrixMapSub
end

section

universe u_1

namespace Bl.MatrixMapSmul

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A) (a : A)
  (X : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSMul.hSMul.{u_1, u_1, u_1} a X) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSMul.hSMul.{u_1, u_1, u_1} (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ a)
      (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ a X
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end Bl.MatrixMapSmul
end

section

universe u_1

namespace Bl.FirstLemmaO

noncomputable def goal1 :
  {A : Type u_1} → [inst : CommRing A] → {d : Nat} → Ideal A → Matrix (Fin d) (Fin d) A → Prop :=
  fun I M => ∀ i j, M i j ∈ I

end Bl.FirstLemmaO
end

section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace Bl.general_b_fact

theorem goal1 {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  classical
  have h1 : (A * B : Matrix (Fin i) (Fin i) R) = fun a => ∑ k, A a k • B k := by
    funext a j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h2 : (A * B).det =
      (detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap
        (fun a => ∑ k, A a k • B k) := by
    rw [Matrix.det, h1]
    rfl

  rw [h2, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

end Bl.general_b_fact
end
