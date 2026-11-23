module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Algebra.Polynomial.Inductions
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

section

namespace GlobalTheory.CoefficientMembership

theorem aeval_mem {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Module.End O V)
    (Z : Submodule O V) (hZ : ∀ z ∈ Z, T z ∈ Z) (q : Polynomial O) :
    ∀ w ∈ Z, (Polynomial.aeval T q) w ∈ Z := by
  intro w hw
  have hpow : ∀ k : ℕ, (T ^ k) w ∈ Z := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hZ _ ih
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact Z.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Z.smul_mem a (hpow n)

theorem coeff_zero_smul_mem_map : ∀ {O V : Type} [inst : CommRing O] [inst_1 : AddCommGroup V] [inst_2 : Module O V] (T : Module.End O V) (Rp : Polynomial O), (Polynomial.aeval T : Polynomial O → Module.End O V) Rp * T = (0 : Module.End O V) → ∀ (Z : Submodule O V), (∀ z ∈ Z, (T : V → V) z ∈ Z) → ∀ w ∈ Z, w ∈ LinearMap.range T → _root_.AddMonoidAlgebra.coeff (M := ℕ) Rp (0 : ℕ) • w ∈ Submodule.map T Z := by
  intro O V _ _ _ T Rp hR Z hZ w hw hwr
  obtain ⟨v, rfl⟩ := hwr
  have key : (Polynomial.aeval T Rp) (T v) =
      T ((Polynomial.aeval T Rp.divX) (T v)) + Rp.coeff 0 • T v := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add Rp]
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply]
  have h0 : (Polynomial.aeval T Rp) (T v) = 0 := by
    have := congrArg (fun f : Module.End O V => f v) hR
    simpa using this
  rw [h0] at key
  refine Submodule.mem_map.mpr ⟨-(Polynomial.aeval T Rp.divX) (T v),
    Z.neg_mem (aeval_mem T Z hZ _ _ hw), ?_⟩
  rw [map_neg]
  exact neg_eq_of_add_eq_zero_right key.symm

end GlobalTheory.CoefficientMembership
end

section

namespace GlobalTheory.NonUnitShift

open Polynomial

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isUnit_aeval (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) :
    ∀ (n : ℕ) (p : ℂ[X]), p.natDegree = n → p ≠ 0 → IsUnit (aeval T p) := by
  intro n
  induction n with
  | zero =>
    intro p hp hp0
    have hc : p.coeff 0 ≠ 0 := by
      intro h0
      apply hp0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hp, h0, map_zero]
    rw [Polynomial.eq_C_of_natDegree_eq_zero hp, Polynomial.aeval_C]
    exact (isUnit_iff_ne_zero.2 hc).map (algebraMap ℂ (Module.End ℂ V))
  | succ n ih =>
    intro p hp hp0
    have hdeg : 0 < p.degree := by
      rw [Polynomial.degree_eq_natDegree hp0, hp]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg.ne'
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.2 hr
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hp0 hq
    have hqdeg : q.natDegree = n := by
      have h2 := congrArg Polynomial.natDegree hq
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0, Polynomial.natDegree_X_sub_C, hp] at h2
      omega
    rw [hq, map_mul]
    refine IsUnit.mul ?_ (ih q hqdeg hq0)
    simpa [map_sub] using h r

theorem linearIndependent_resolvent (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) (v : V) (hv : v ≠ 0)
    (w : ℂ → V) (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  set q : ℂ[X] := ∑ j ∈ s, C (g j) * ∏ k ∈ s.erase j, (X - C k) with hq
  have key : aeval T q v = 0 := by
    have h1 : aeval T (∏ k ∈ s, (X - C k)) (∑ j ∈ s, g j • w j) = 0 := by
      rw [hs, map_zero]

    rw [← h1, hq, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul s _ hj, map_mul, map_mul, aeval_C, map_sub, aeval_X, aeval_C,
      map_smul, Module.End.mul_apply, Module.End.mul_apply, hw, Module.algebraMap_end_apply]
  have hq0 : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval T h _ q rfl hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [key, map_zero]))
  have h2 : eval i q = g i * ∏ k ∈ s.erase i, (i - k) := by
    rw [hq, eval_finsetSum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro j _ hji
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hji.symm, hi⟩) (by simp),
        mul_zero]
    · intro h3
      exact absurd hi h3
  rw [hq0, eval_zero] at h2
  rcases mul_eq_zero.1 h2.symm with h3 | h3
  · exact h3
  · obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.1 h3
    exact absurd (sub_eq_zero.1 hk0).symm (Finset.mem_erase.1 hk).1

theorem exists_not_isUnit_sub : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] [Nontrivial V], Module.rank ℂ V ≤ Cardinal.aleph0 → ∀ (T : Module.End ℂ V), ∃ (c : ℂ), ¬IsUnit (T - (Algebra.algebraMap ℂ (Module.End ℂ V) : ℂ → Module.End ℂ V) c) := by
  intro V _ _ _ hrank T
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let w : ℂ → V := fun c => (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) v
  have hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v := fun c => by
    have h1 : ((hcon c).unit : Module.End ℂ V) * (((hcon c).unit⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = 1 :=
      (hcon c).unit.mul_inv
    rw [IsUnit.unit_spec] at h1
    have h2 := congrArg (fun f : Module.End ℂ V => f v) h1
    simp only [Module.End.mul_apply, Module.End.one_apply] at h2
    exact h2
  have hli := linearIndependent_resolvent T hcon v hv w hw
  have h1 : Cardinal.mk ℂ ≤ Cardinal.aleph0 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

end GlobalTheory.NonUnitShift
end

section

open Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem baseChange_polynomial_kills_descent (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB]
    [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB) (hrd : ∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a)
    (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X])
    (hq : ∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) :
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  classical

  let rdL : L0 →ₗ[Ks] KB :=
    { toFun := rd
      map_add' := rd.map_add
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, map_mul, hrd, RingHom.id_apply] }
  let R : L0 ⊗[Ks] WK →ₗ[Ks] KB ⊗[Ks] WK := LinearMap.rTensor WK rdL
  have hRt : ∀ (c : L0) (w : WK), R (c ⊗ₜ[Ks] w) = rd c ⊗ₜ[Ks] w := fun c w => rfl

  have hRs : ∀ (c : L0) (z : L0 ⊗[Ks] WK), R (c • z) = rd c • R z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => simp [TensorProduct.smul_tmul', hRt]
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

  set B0 := LinearMap.baseChange L0 T0 with hB0
  set B := LinearMap.baseChange KB T0 with hB
  have hRB : ∀ z, R (B0 z) = B (R z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x w => simp [hB0, hB, hRt]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hRpow : ∀ (n : ℕ) z, R ((B0 ^ n) z) = (B ^ n) (R z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hRB]
  have hRq : ∀ (p : L0[X]) z, Polynomial.aeval B (p.map rd) (R z) = R (Polynomial.aeval B0 p z) := by
    intro p z
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hr]
    | monomial n c =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [Module.End.mul_apply, Module.algebraMap_end_apply, hRs, hRpow]

  have hE : ∀ (c : KB) (f : WK),
      (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)) (c ⊗ₜ[Ks] f)
        = c • R ((∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)) ((1 : L0) ⊗ₜ[Ks] f)) := by
    intro c f

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul, map_sum,
    hRs, hRt, map_one, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [mul_comm]
  rintro y ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c f =>
    rw [hE, map_smul, hRq, hq _ ⟨_, rfl⟩, map_zero, smul_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem exists_denominator_aeval_elem (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A)
    (h : ∀ x : A, ∃ p : E[X], aeval g p = x) (x : A) :
    ∃ c : O, c ≠ 0 ∧ ∃ p : O[X], aeval g p = c • x := by
  obtain ⟨q, rfl⟩ := h x
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors O) q, ?_⟩
  rw [← aeval_map_algebraMap E, hq, ← algebraMap_smul E b q, map_smul, algebraMap_smul]

theorem exists_common_denominator_aeval_of_fg (O E A : Type) [CommRing O] [IsDomain O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] (g : A) (h : ∀ x : A, ∃ p : E[X], aeval g p = x)
    (S : Submodule O A) (hS : S.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  classical
  obtain ⟨s, rfl⟩ := hS
  have key : ∃ c : O, c ≠ 0 ∧ ∀ x ∈ s, ∃ p : O[X], aeval g p = c • x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      obtain ⟨d, hd, p, hp⟩ := exists_denominator_aeval_elem O E A g h a
      refine ⟨c * d, mul_ne_zero hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨c • p, by rw [map_smul, hp, mul_smul]⟩
      · obtain ⟨q, hq⟩ := hs x hx
        exact ⟨d • q, by rw [map_smul, hq, mul_comm, mul_smul]⟩
  obtain ⟨c, hc, hs⟩ := key
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add (f := _), hp, hq, smul_add]⟩
  | smul a x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨a • p, by rw [map_smul, hp, smul_comm]⟩

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem rcout_coeff_succ {K : Type} [NormedField K] (g : K[X]) (a : K) (k : ℕ) :
    ((X - C a) * g).coeff (k + 1) = g.coeff k - a * g.coeff (k + 1) := by
  rw [mul_comm, coeff_mul_X_sub_C]; ring

theorem rcout_coeff_zero {K : Type} [NormedField K] (g : K[X]) (a : K) :
    ((X - C a) * g).coeff 0 = -(a * g.coeff 0) := by
  rw [mul_coeff_zero]; simp

theorem rcout_ultra {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem newton_step_root_outside_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  intro K _ _ g a ρ d hρ ha hle hlt
  set M := ‖g.coeff d‖ * ρ ^ d with hM
  have hMpos : 0 < M := by
    have := hlt (d + 1) (Nat.lt_succ_self d)
    exact lt_of_le_of_lt (by positivity) this
  have hapos : 0 < ‖a‖ := hρ.trans ha

  have hshift : ∀ k, ‖g.coeff k‖ * ρ ^ (k + 1) ≤ ρ * M := by
    intro k
    have := hle k
    calc ‖g.coeff k‖ * ρ ^ (k + 1) = ρ * (‖g.coeff k‖ * ρ ^ k) := by ring
      _ ≤ ρ * M := mul_le_mul_of_nonneg_left this hρ.le
  have hρM : ρ * M < ‖a‖ * M := mul_lt_mul_of_pos_right ha hMpos

  have haterm : ∀ j, ‖a * g.coeff j‖ * ρ ^ j = ‖a‖ * (‖g.coeff j‖ * ρ ^ j) := by
    intro j; rw [norm_mul]; ring

  have hup : ∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖a‖ * M := by
    intro j
    have hpj : 0 ≤ ρ ^ j := by positivity
    cases j with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
      exact mul_le_mul_of_nonneg_left (hle 0) hapos.le
    | succ k =>
      rw [rcout_coeff_succ]
      calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
          ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
        _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
            max_mul_of_nonneg _ _ hpj
        _ ≤ ‖a‖ * M := by
            apply max_le
            · exact (hshift k).trans hρM.le
            · rw [haterm]; exact mul_le_mul_of_nonneg_left (hle (k + 1)) hapos.le

  have hupl : ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖a‖ * M := by
    intro j hj
    have hpj : 0 ≤ ρ ^ j := by positivity
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [rcout_coeff_succ]
    calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hpj
      _ < ‖a‖ * M := by
          apply max_lt
          · exact lt_of_le_of_lt (hshift k) hρM
          · rw [haterm]; exact mul_lt_mul_of_pos_left (hlt (k + 1) hj) hapos

  have hlow : ‖a‖ * M ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
    have hpd : 0 < ρ ^ d := by positivity
    cases d with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
    | succ k =>
      rw [rcout_coeff_succ]
      set c := g.coeff k - a * g.coeff (k + 1)
      have key : a * g.coeff (k + 1) = g.coeff k - c := by simp [c]
      have h1 : ‖a‖ * M = ‖g.coeff k - c‖ * ρ ^ (k + 1) := by
        rw [← key, haterm]
      have h2 : ‖g.coeff k - c‖ * ρ ^ (k + 1) ≤
          max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖c‖ * ρ ^ (k + 1)) := by
        rw [← max_mul_of_nonneg _ _ hpd.le]
        exact mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpd.le
      rcases le_max_iff.mp (h1 ▸ h2 : ‖a‖ * M ≤ _) with h | h
      · exact absurd (lt_of_le_of_lt ((hshift k)) hρM) (not_lt.mpr h)
      · exact h
  exact ⟨fun j => (hup j).trans hlow, fun j hj => (hupl j hj).trans_le hlow⟩

end GlobalTheory
end

section

universe u_1 u_2

namespace GlobalTheory.ProductDegreeCoefficient

open Polynomial

theorem natDegree_le_and_coeff_prod_pow {B : Type u_1} [CommRing B] {T : Type u_2}
    (s : Finset T) (p : T → Polynomial B) (e : T → ℕ)
    (h : ∀ t : T, (p t).natDegree ≤ 1) :
    (∏ t ∈ s, p t ^ e t).natDegree ≤ ∑ t ∈ s, e t ∧
      (∏ t ∈ s, p t ^ e t).coeff (∑ t ∈ s, e t) = ∏ t ∈ s, (p t).coeff 1 ^ e t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (p a ^ e a).natDegree ≤ e a := by
      have := Polynomial.natDegree_pow_le_of_le (e a) (h a)
      simpa using this
    have h2 : (p a ^ e a).coeff (e a) = (p a).coeff 1 ^ e a := by
      have := Polynomial.coeff_pow_of_natDegree_le (m := e a) (h a)
      simpa using this
    refine ⟨Polynomial.natDegree_mul_le_of_le h1 ih1, ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih1, h2, ih2]

end GlobalTheory.ProductDegreeCoefficient
end

section

namespace GlobalTheory.EvalNatCastZero

open Polynomial

theorem eq_zero_of_eval_natCast_add {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (n : ℕ) (F : Polynomial R) (hF : F.natDegree ≤ n)
    (m : ℕ) (h : ∀ k : ℕ, Polynomial.eval ((m + k : ℕ) : R) F = 0) : F = 0 := by
  nontriviality R
  induction n generalizing F m with
  | zero =>
    have h0 := h 0
    rw [eq_C_of_natDegree_le_zero hF] at h0 ⊢
    rw [eval_C] at h0
    rw [h0, C_0]
  | succ n ih =>
    have hroot : F.IsRoot (m : R) := by simpa using h 0
    have hfac : (X - C (m : R)) * (F /ₘ (X - C (m : R))) = F :=
      mul_divByMonic_eq_iff_isRoot.2 hroot
    have hdeg : (F /ₘ (X - C (m : R))).natDegree ≤ n := by
      rw [natDegree_divByMonic F (monic_X_sub_C _), natDegree_X_sub_C]
      omega
    have hG : F /ₘ (X - C (m : R)) = 0 := by
      refine ih _ hdeg (m + 1) fun k => ?_
      have h1 := h (k + 1)
      rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h1
      have e1 : ((m + (k + 1) : ℕ) : R) - (m : R) = ((k + 1 : ℕ) : R) := by push_cast; ring
      have e2 : m + 1 + k = m + (k + 1) := by ring
      rw [e1] at h1
      rw [e2]
      exact (hR (k + 1) (Nat.succ_ne_zero k)).mul_right_eq_zero.1 h1
    rw [← hfac, hG, mul_zero]

end GlobalTheory.EvalNatCastZero
end
