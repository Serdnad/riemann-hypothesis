module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
public import Formalism.SatakeDualWeyl.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

noncomputable section

open scoped TensorProduct
open NumberField Formalism.MainNotions.S Polynomial

namespace PI.UnitaryDimensionFormula

section JacE

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def jaR : Af F →+* E ⊗[F] Af F :=
  (Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F).toRingHom

theorem jaR_apply (a : Af F) : jaR F E a = (1 : E) ⊗ₜ[F] a := by
  rfl

theorem ja_genR (a : Af F) (ha : a ∈ Formalism.UG.intAd F) : jaR F E a ∈ IntAf F E := by
  apply Subring.subset_closure
  exact Set.mem_union_right _ (Set.mem_range.2 ⟨⟨a, ha⟩, rfl⟩)

theorem ja_genL (z : 𝓞 E) : ((z : E) ⊗ₜ[F] (1 : Af F)) ∈ IntAf F E := by
  apply Subring.subset_closure
  exact Set.mem_union_left _ (Set.mem_range.2 ⟨⟨(z : E), RingHom.mem_range.2 ⟨z, rfl⟩⟩, rfl⟩)

def jaT : Subring (IntAf F E) :=
  Subring.comap (IntAf F E).subtype ((Formalism.UG.intAd F).map (jaR F E))

def jaL : 𝓞 E →+* IntAf F E :=
  RingHom.codRestrict (((Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] Af F).toRingHom).comp
    (algebraMap (𝓞 E) E)) (IntAf F E) (fun z => by
      simpa [Algebra.TensorProduct.includeLeft_apply] using ja_genL F E z)

theorem ja_integral (m : IntAf F E) : IsIntegral (jaT F E) m := by

  let S : Subring (E ⊗[F] Af F) :=
    (integralClosure (jaT F E) (IntAf F E)).toSubring.map (IntAf F E).subtype
  have hle : IntAf F E ≤ S := by
    apply Subring.closure_le.2
    rintro x (⟨⟨y, hy⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := RingHom.mem_range.1 hy
      refine Subring.mem_map.2 ⟨jaL F E o, ?_, rfl⟩
      have h0 : IsIntegral ℤ o := by
        first
          | exact Algebra.IsIntegral.isIntegral o
          | exact NumberField.RingOfIntegers.isIntegral o
      have h1 : IsIntegral ℤ (jaL F E o) := h0.map (jaL F E).toIntAlgHom
      show jaL F E o ∈ integralClosure (jaT F E) (IntAf F E)
      exact h1.tower_top
    · have hw : (⟨(1 : E) ⊗ₜ[F] y, ja_genR F E y hy⟩ : IntAf F E) ∈ jaT F E :=
        Subring.mem_comap.2 (Subring.mem_map.2 ⟨y, hy, rfl⟩)
      refine Subring.mem_map.2 ⟨⟨(1 : E) ⊗ₜ[F] y, ja_genR F E y hy⟩, ?_, rfl⟩
      show _ ∈ integralClosure (jaT F E) (IntAf F E)
      exact isIntegral_algebraMap (x := (⟨_, hw⟩ : jaT F E))
  obtain ⟨x, hx, hxm⟩ := Subring.mem_map.1 (hle m.2)
  have hxm' : x = m := Subtype.ext hxm
  subst hxm'
  exact hx


set_option maxHeartbeats 400000 in
theorem ja_key (G : ℕ) (m : IntAf F E) :
    ∃ t : IntAf F E, ∃ c ∈ jaT F E, (1 + (G : IntAf F E) * m) * t = 1 + (G : IntAf F E) * c := by
  set_option synthInstance.maxHeartbeats 400000 in
    obtain ⟨p, hpm, hp⟩ := ja_integral F E m
    rw [Polynomial.eval₂_eq_sum_range] at hp
    obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
    rw [hn] at hp
    have hpn : p.coeff n = 1 := hn ▸ hpm.coeff_natDegree
    obtain ⟨y, hy⟩ : ∃ y : IntAf F E, 1 + (G : IntAf F E) * m = y := ⟨_, rfl⟩
    rw [hy]

    have hw : ∀ i : ℕ, ∃ w : IntAf F E, (y - 1) ^ i = (-1) ^ i + y * w := by
      intro i
      obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow (y - 1) (-1) i
      refine ⟨w, ?_⟩
      have h1 : y - 1 - -1 = y := by ring
      rw [h1] at hw
      linear_combination hw
    choose w hw using hw
    have hym : y - 1 = (G : IntAf F E) * m := by rw [← hy]; ring

    have hE0 : ∑ i ∈ Finset.range (n + 1),
        algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (y - 1) ^ i = 0 := by
      have h2 : ∑ i ∈ Finset.range (n + 1),
          algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (y - 1) ^ i =
          (G : IntAf F E) ^ n * ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * m ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [hym, mul_pow]
        calc algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * ((G : IntAf F E) ^ i * m ^ i)
            = algebraMap (jaT F E) (IntAf F E) (p.coeff i) * ((G : IntAf F E) ^ (n - i) * (G : IntAf F E) ^ i) * m ^ i := by ring
          _ = (G : IntAf F E) ^ n * (algebraMap (jaT F E) (IntAf F E) (p.coeff i) * m ^ i) := by
            rw [← pow_add, Nat.sub_add_cancel hin]; ring
      rw [h2, hp, mul_zero]
    have hE : ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (-1) ^ i +
        y * ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * w i = 0 := by
      have h3 : ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (-1) ^ i +
          y * ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * w i =
          ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (y - 1) ^ i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hw i]; ring
      rw [h3, hE0]

    obtain ⟨c0, hc0⟩ : ∃ c0 : jaT F E,
        c0 = ∑ i ∈ Finset.range n, p.coeff i * (G : jaT F E) ^ (n - 1 - i) * (-1) ^ i := ⟨_, rfl⟩
    have hS : ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (-1) ^ i =
        (G : IntAf F E) * algebraMap (jaT F E) (IntAf F E) c0 + (-1) ^ n := by
      simp only [Finset.sum_range_succ, hpn, map_one, Nat.sub_self, pow_zero, one_mul]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc0, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i < n := Finset.mem_range.1 hi
      have h4 : n - i = (n - 1 - i) + 1 := by omega
      simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
      rw [h4, pow_succ]
      ring
    have hsq : ((-1 : IntAf F E) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    refine ⟨(-1) ^ n * -(∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * w i),
      algebraMap (jaT F E) (IntAf F E) ((-1) ^ n * c0), ((-1) ^ n * c0).2, ?_⟩
    rw [map_mul, map_pow, map_neg, map_one]
    linear_combination (-(-1 : IntAf F E) ^ n) * hE + (-1 : IntAf F E) ^ n * hS + hsq

end JacE

theorem idxDJacE : IdxDJacE := by
  intro F E _ _ _ _ _ g e he m hm
  obtain ⟨t, c, hc, htc⟩ := ja_key F E g ⟨m, hm⟩
  obtain ⟨c', hc', hcc⟩ := Subring.mem_map.1 (Subring.mem_comap.1 hc)
  obtain ⟨y', hy', hey⟩ := he.2.2.2 c' hc'
  refine ⟨(t : E ⊗[F] Af F) * jaR F E y', mul_mem t.2 (ja_genR F E y' hy'), ?_⟩
  have h1 : (1 + (g : E ⊗[F] Af F) * m) * (t : E ⊗[F] Af F) =
      1 + (g : E ⊗[F] Af F) * jaR F E c' := by
    have h2 := congrArg Subtype.val htc
    push_cast at h2
    rw [h2]
    exact congrArg (fun z => 1 + (g : E ⊗[F] Af F) * z) hcc.symm
  calc ((1 : E) ⊗ₜ[F] e) * (1 + (g : E ⊗[F] Af F) * m) * ((t : E ⊗[F] Af F) * jaR F E y')
      = jaR F E e * ((1 + (g : E ⊗[F] Af F) * m) * (t : E ⊗[F] Af F)) * jaR F E y' := by
        simp only [jaR_apply]; ring
    _ = jaR F E (e * (1 + (g : Af F) * c') * y') := by
        rw [h1]; simp only [map_mul, map_add (f := _), map_one, map_natCast]
    _ = (1 : E) ⊗ₜ[F] e := by rw [hey, jaR_apply]

end PI.UnitaryDimensionFormula
end
end

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mat_idem_mul {Rg : Type} [Ring Rg] (E a b : Rg) (hE : E * E = E) (hc : ∀ x : Rg, E * x = x * E) :
    (E * a + (1 - E)) * (E * b + (1 - E)) = E * (a * b) + (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : E * a * (E * b) = E * (a * b) := by
    rw [mul_assoc, ← mul_assoc a E b, ← hc a, ← mul_assoc, ← mul_assoc, hE, mul_assoc]
  have e2 : E * a * (1 - E) = 0 := by
    have : a * (1 - E) = (1 - E) * a := by rw [mul_sub, sub_mul, mul_one, one_mul, hc a]
    rw [mul_assoc, this, ← mul_assoc, h1, zero_mul]
  have e3 : (1 - E) * (E * b) = 0 := by rw [← mul_assoc, h2, zero_mul]
  rw [add_mul, mul_add, mul_add, e1, e2, e3, h3, add_zero, zero_add]

theorem mat_lift_core {O : Type} [CommRing O] {k : ℕ} (gO eO wO : O) (he2 : eO * eO = eO) (hw2 : wO * wO = wO)
    (Mo No tt : Matrix (Fin k) (Fin k) O) (htt : ∀ i j, wO * (No * Mo - 1) i j = gO * tt i j)
    (hJ : ∀ m : O, ∃ y : O, eO * (1 + gO * m) * y = eO) :
    ∃ C C' : Matrix (Fin k) (Fin k) O, C' * C = 1 ∧ ∀ i j, (eO * wO) * C i j = (eO * wO) * Mo i j := by
  set Q : Matrix (Fin k) (Fin k) O := 1 + gO • tt with hQdef
  obtain ⟨m, hm⟩ : ∃ m : O, Q.det = 1 + gO * m := by
    have hQ : (Ideal.Quotient.mk (Ideal.span {gO})).mapMatrix Q = 1 := by
      have hπg : Ideal.Quotient.mk (Ideal.span {gO}) gO = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [hQdef, map_add (f := _), map_one]
      ext i j
      simp [hπg]
    have h1 : Ideal.Quotient.mk (Ideal.span {gO}) (Q.det - 1) = 0 := by
      rw [map_sub, RingHom.map_det, hQ, det_one, map_one, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    refine ⟨a, ?_⟩
    rw [mul_comm, ha]; ring
  obtain ⟨yO, hey0⟩ := hJ m
  have hey : eO * Q.det * yO = eO := by rw [hm]; exact hey0
  set εO := eO * wO with hεdef
  set E : Matrix (Fin k) (Fin k) O := εO • 1 with hEdef
  have hEc : ∀ x : Matrix (Fin k) (Fin k) O, E * x = x * E := by
    intro x; simp [hEdef]
  have hε2 : εO * εO = εO := by
    calc εO * εO = (eO * eO) * (wO * wO) := by rw [hεdef]; ring
      _ = εO := by rw [he2, hw2]
  have hE2 : E * E = E := by simp [hEdef, smul_smul, hε2]
  have hEQ : E * (No * Mo) = E * Q := by
    ext i j
    simp only [hEdef, Matrix.smul_mul, one_mul, Matrix.smul_apply, smul_eq_mul, hQdef, Matrix.add_apply]
    have h1 : (No * Mo) i j = (No * Mo - 1) i j + (1 : Matrix (Fin k) (Fin k) O) i j := by
      rw [Matrix.sub_apply]; ring
    have h2 : wO * (gO * tt i j) = gO * tt i j := by
      rw [← htt i j, ← mul_assoc, hw2]
    have key : εO * (No * Mo - 1) i j = εO * (gO • tt) i j := by
     calc εO * (No * Mo - 1) i j = eO * (wO * (No * Mo - 1) i j) := by rw [hεdef]; ring
      _ = eO * (wO * (gO * tt i j)) := by rw [htt i j, h2]
      _ = εO * (gO * tt i j) := by rw [hεdef]; ring
      _ = εO * (gO • tt) i j := by rw [Matrix.smul_apply, smul_eq_mul]
    rw [h1, mul_add, mul_add, key, Matrix.smul_apply, smul_eq_mul]; ring
  set P : Matrix (Fin k) (Fin k) O := yO • Q.adjugate with hPdef
  have hEPQ : E * (P * Q) = E := by
    have : P * Q = (yO * Q.det) • (1 : Matrix (Fin k) (Fin k) O) := by
      rw [hPdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    rw [this, hEdef, smul_mul_smul, one_mul]
    congr 1
    calc εO * (yO * Q.det) = wO * (eO * Q.det * yO) := by rw [hεdef]; ring
      _ = εO := by rw [hey, hεdef, mul_comm]
  refine ⟨E * Mo + (1 - E), E * (P * No) + (1 - E), ?_, ?_⟩
  · rw [mat_idem_mul E _ _ hE2 hEc]
    have : E * (P * No * Mo) = E := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc E, hEc P, Matrix.mul_assoc, hEQ, ← Matrix.mul_assoc, ← hEc P,
        Matrix.mul_assoc, hEPQ]
    rw [this, add_sub_cancel]
  · intro i j
    have hEC : E * (E * Mo + (1 - E)) = E * Mo := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hE2, Matrix.mul_sub, Matrix.mul_one, hE2, sub_self, add_zero]
    have := congrFun (congrFun hEC i) j
    simpa [hEdef, Matrix.smul_mul] using this

theorem idxDMat_of (hJ : IdxDJacE) : IdxDMat := by
  intro D X TR e he A
  have heO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨e, he.1⟩, rfl⟩)
  obtain ⟨t, ht, het⟩ := he.2.2.1
  have htO : ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) ∈ IntAf X.B.I.F X.B.I.E :=
    Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)
  let eO : IntAf X.B.I.F X.B.I.E := ⟨_, heO⟩
  let wO : IntAf X.B.I.F X.B.I.E := ⟨X.ew, X.ew_int⟩
  let tO : IntAf X.B.I.F X.B.I.E := ⟨_, htO⟩
  let gO : IntAf X.B.I.F X.B.I.E := X.B.g
  have hgO : ((gO : IntAf X.B.I.F X.B.I.E) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    simp [gO]
  have kerZ : ∀ x : IntAf X.B.I.F X.B.I.E, (∀ v, TR.res v x = 0) →
      ∃ t : IntAf X.B.I.F X.B.I.E, wO * x = gO * t := by
    intro x hx
    obtain ⟨t, ht, he'⟩ := (TR.res_ker x).1 hx
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change X.ew * (x : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t
    rw [hgO]; exact he'
  have resG : ∀ v, TR.res v gO = 0 := by
    refine (TR.res_ker gO).2 ⟨X.ew, X.ew_int, ?_⟩
    rw [hgO, mul_comm]
  have heq : eO = 1 - gO * tO := by
    apply Subtype.ext
    change (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e = 1 - (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t)
    rw [hgO]
    have h1 : e = 1 - (X.B.g : Af X.B.I.F) * t := by rw [← het]; ring
    rw [h1, TensorProduct.tmul_sub]
    congr 1
    rw [← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E) (B := Af X.B.I.F)) X.B.g]
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have resE : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * x) = TR.res v x := by
    intro v x
    rw [heq, sub_mul, one_mul, map_sub, mul_assoc, map_mul, resG, zero_mul, sub_zero]
  have resEps : ∀ v (x : IntAf X.B.I.F X.B.I.E), TR.res v (eO * wO * x) = TR.res v x := by
    intro v x
    rw [mul_assoc, resE]
    exact TR.res_ew v x
  choose a0 ha0 using fun i j => TR.res_joint (fun v => (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j)
  choose b0 hb0 using fun i j => TR.res_joint
    (fun v => ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) i j)
  let Mo : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of a0
  let No : Matrix (Fin D.R.k) (Fin D.R.k) (IntAf X.B.I.F X.B.I.E) := Matrix.of b0
  have hNM : ∀ v i j, TR.res v ((No * Mo - 1) i j) = 0 := by
    intro v i j
    have hM : (TR.res v).mapMatrix Mo = (A v : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (ha0 i j) v
    have hN : (TR.res v).mapMatrix No = ((A v)⁻¹ : GL (Fin D.R.k) (TR.Fq v)) := by
      ext i j; exact congrFun (hb0 i j) v
    have : (TR.res v).mapMatrix (No * Mo - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one, sub_self]
    exact congrFun (congrFun this i) j
  choose tt htt using fun i j => kerZ _ (fun v => hNM v i j)
  have hw2 : wO * wO = wO := Subtype.ext X.ew_idem
  have he2 : eO * eO = eO := Subtype.ext (by
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) = (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, he.2.1])
  have hJO : ∀ m : IntAf X.B.I.F X.B.I.E, ∃ y : IntAf X.B.I.F X.B.I.E, eO * (1 + gO * m) * y = eO := by
    intro m
    obtain ⟨y, hy, hyeq⟩ := hJ X.B.I.F X.B.I.E X.B.g e he (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) m.2
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] e) * (1 + (gO : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * m) * y =
      (1 : X.B.I.E) ⊗ₜ[X.B.I.F] e
    rw [hgO]; exact hyeq
  obtain ⟨CO, C'O, hCC, hent⟩ := mat_lift_core gO eO wO he2 hw2 Mo No (Matrix.of tt) (fun i j => htt i j) hJO
  refine ⟨CO.map (IntAf X.B.I.F X.B.I.E).subtype, C'O.map (IntAf X.B.I.F X.B.I.E).subtype, ?_,
    fun i j => ⟨(CO i j).2, (C'O i j).2⟩, ?_⟩
  · rw [← Matrix.map_mul, hCC, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro v i j
    have hmem : epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j ∈ IntAf X.B.I.F X.B.I.E :=
      (eO * wO * CO i j).2
    unfold resT
    rw [dite_eq_left hmem]
    have : (⟨epsX X e * (CO.map (IntAf X.B.I.F X.B.I.E).subtype) i j, hmem⟩ : IntAf X.B.I.F X.B.I.E) =
        eO * wO * Mo i j := by
      rw [← hent i j]; rfl
    rw [this, resEps]
    exact congrFun (ha0 i j) v

end PI.UnitaryDimensionFormula
end
end

section

noncomputable section

open scoped Classical TensorProduct
open NumberField IsDedekindDomain

namespace PI.UnitaryDimensionFormula

section
variable {F : Type} [Field F] [NumberField F]

theorem adAd_natCast_apply (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (g : FiniteAdeleRing (𝓞 F) F) v = (g : v.adicCompletion F) :=
  map_natCast (Formalism.UG.evalV F v) g

theorem adAd_val_g (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (g : v.adicCompletion F) = v.intValuation (g : 𝓞 F) := by
  have e1 : (g : v.adicCompletion F) = ((g : F) : v.adicCompletion F) := by
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have e2 : (g : F) = algebraMap (𝓞 F) F (g : 𝓞 F) := (map_natCast _ g).symm
  rw [e2, HeightOneSpectrum.valuation_of_algebraMap]

theorem adAd_val_lt (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  rw [adAd_val_g]; exact (v.intValuation_lt_one_iff_mem _).2 h

theorem adAd_val_one (g : ℕ) (v : HeightOneSpectrum (𝓞 F)) (h : (g : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) = 1 := by
  rw [adAd_val_g]
  exact (v.intValuation_eq_one_iff_mem_primeCompl _).2 h

def adOfInt (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨f, Filter.Eventually.of_forall hf⟩

theorem adOfInt_int (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ v, f v ∈ v.adicCompletionIntegers F) : adOfInt f hf ∈ Formalism.UG.intAd F := hf

end

theorem idxDAd : IdxDAd := by
  intro F _ _ g
  let P : HeightOneSpectrum (𝓞 F) → Prop := fun v => (g : 𝓞 F) ∈ v.asIdeal
  have h01 : ∀ v : HeightOneSpectrum (𝓞 F),
      (if P v then (1 : v.adicCompletion F) else 0) ∈ v.adicCompletionIntegers F := by
    intro v; split_ifs
    · exact one_mem _
    · exact zero_mem _
  let e := adOfInt (fun v => if P v then (1 : v.adicCompletion F) else 0) h01
  refine ⟨e, adOfInt_int _ _, ?_, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (if P v then 1 else 0) = if P v then 1 else 0
    split_ifs <;> simp
  · have ht : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (0 : v.adicCompletion F) else (g : v.adicCompletion F)⁻¹) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · exact zero_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, adAd_val_one g v hv, inv_one]
    refine ⟨adOfInt _ ht, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (1 : v.adicCompletion F) - (if P v then 1 else 0) =
      (g : FiniteAdeleRing (𝓞 F) F) v * (if P v then 0 else (g : v.adicCompletion F)⁻¹)
    rw [adAd_natCast_apply]
    split_ifs with hv
    · simp
    · have hne : (g : v.adicCompletion F) ≠ 0 := by
        intro h0
        have := adAd_val_one g v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [sub_zero, mul_inv_cancel₀ hne]
  · intro c hc
    have hu : ∀ v : HeightOneSpectrum (𝓞 F), P v →
        Valued.v (1 + (g : v.adicCompletion F) * c v) = 1 := by
      intro v hv
      have hlt : Valued.v ((g : v.adicCompletion F) * c v) < 1 := by
        rw [map_mul]
        have hcv : Valued.v (c v) ≤ 1 := hc v
        calc Valued.v (g : v.adicCompletion F) * Valued.v (c v) ≤ Valued.v (g : v.adicCompletion F) * 1 :=
              mul_le_mul' le_rfl hcv
          _ < 1 := by rw [mul_one]; exact adAd_val_lt g v hv
      rw [Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hlt), map_one]
    have hy : ∀ v : HeightOneSpectrum (𝓞 F),
        (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) ∈ v.adicCompletionIntegers F := by
      intro v
      split_ifs with hv
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu v hv, inv_one]
      · exact zero_mem _
    refine ⟨adOfInt _ hy, adOfInt_int _ _, ?_⟩
    refine FiniteAdeleRing.ext _ fun v => ?_
    show (if P v then (1 : v.adicCompletion F) else 0) * (1 + (g : FiniteAdeleRing (𝓞 F) F) v * c v) *
      (if P v then (1 + (g : v.adicCompletion F) * c v)⁻¹ else 0) = if P v then 1 else 0
    rw [adAd_natCast_apply]
    split_ifs with hv
    · have hne : (1 + (g : v.adicCompletion F) * c v) ≠ 0 := by
        intro h0
        have := hu v hv
        rw [h0, map_zero] at this
        exact zero_ne_one this
      rw [one_mul, mul_inv_cancel₀ hne]
    · simp

end PI.UnitaryDimensionFormula
end
end
