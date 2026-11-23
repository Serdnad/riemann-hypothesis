module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma

open Polynomial


open Matrix MeasureTheory in
open Polynomial in
theorem _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (f : Module.End E V) (h : (LinearMap.charpoly f).Separable) :
    LinearMap.charpoly f ∣ minpoly E f := by
  set L := AlgebraicClosure E
  have hinj : Function.Injective (algebraMap E L) := (algebraMap E L).injective
  rw [← map_dvd_map (algebraMap E L) hinj (LinearMap.charpoly_monic f)]
  have hm0 : (minpoly E f).map (algebraMap E L) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral f))
  have hroot : ∀ r ∈ ((LinearMap.charpoly f).map (algebraMap E L)).roots,
      r ∈ ((minpoly E f).map (algebraMap E L)).roots := by
    intro r hr
    rw [mem_roots hm0]
    rw [mem_roots (Polynomial.map_ne_zero (LinearMap.charpoly_monic f).ne_zero),
      ← LinearMap.charpoly_baseChange, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hr
    obtain ⟨v, hv⟩ := hr.exists_hasEigenvector
    have hzero : aeval (f.baseChange L) ((minpoly E f).map (algebraMap E L)) = 0 := by
      rw [aeval_map_algebraMap]
      have hφ := Polynomial.aeval_algHom_apply (Module.End.baseChangeHom E L V) f (minpoly E f)
      rw [minpoly.aeval, map_zero] at hφ
      exact hφ
    have hv' :=
      Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E f).map (algebraMap E L)) hv
    rw [hzero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at hv'
    exact hv'.resolve_right hv.2
  have hsplit := IsAlgClosed.splits ((LinearMap.charpoly f).map (algebraMap E L))
  rw [hsplit.eq_prod_roots_of_monic ((LinearMap.charpoly_monic f).map _),
    Multiset.prod_X_sub_C_dvd_iff_le_roots hm0, Multiset.le_iff_subset (nodup_roots h.map)]
  exact hroot


open Matrix MeasureTheory in
open Polynomial in
theorem _root_.GlobalTheory.UnitLemma.exists_basis_pow_of_separable : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K), B.P.Separable →
    ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E
      B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  intro K B hsep
  set g := B.g
  have hmin : minpoly K.E (LinearMap.mulLeft K.E g) = minpoly K.E g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A)
      (fun x y hxy => by simpa using congrArg (fun φ => φ 1) hxy) g
  have hdvd := _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable _ hsep
  rw [hmin] at hdvd
  have hdeg : (minpoly K.E g).natDegree =
      Module.finrank K.E B.A := by
    apply le_antisymm (minpoly.natDegree_le g)
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E g)]
    exact natDegree_le_of_dvd hdvd (minpoly.ne_zero (Algebra.IsIntegral.isIntegral g))
  have hli : LinearIndependent K.E
      (fun i : Fin (Module.finrank K.E B.A) => g ^ (i : ℕ)) :=
    (linearIndependent_pow g).comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (Fintype.card_fin _),
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩

end GlobalTheory.UnitLemma
end

section

open scoped NNReal

namespace GlobalTheory.BSP.DiscDomain

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A] {u : A} {ρ : ℝ≥0}

private theorem gauge_mul_le_of_mem_ball (y z : PreDisc l u ρ) {s : ℝ} (hs : 0 < s) (hz : z ∈ ball l u ρ s) :
    gauge l u ρ (y * z) ≤ gauge l u ρ y * s := by
  have key : ∀ r, gauge l u ρ y < r → gauge l u ρ (y * z) / s ≤ r := by
    intro r hr
    have hr0 : 0 < r := (gauge_nonneg l u ρ y).trans_lt hr
    rw [div_le_iff₀ hs]
    exact gauge_le l u ρ (mul_pos hr0 hs)
      (mul_mem_ball l u ρ hr0.le (mem_ball_of_gauge_lt l u ρ hr) hz)
  rw [← div_le_iff₀ hs]
  exact le_of_forall_gt_imp_ge_of_dense key

private theorem algebraMap_natCast_mem_ball_inv (hl0 : (0 : ℝ) < l) :
    algebraMap A (PreDisc l u ρ) (l : A) ∈ ball l u ρ ((l : ℝ)⁻¹) := by
  refine Submodule.subset_span ?_
  rw [monos, Set.mem_setOf_eq]
  refine ⟨1, 0, 0, ?_, ?_⟩
  · rw [pow_zero, pow_zero, pow_one, one_mul, inv_mul_cancel₀ hl0.ne']
  · simp

private theorem invSelf_mem_ball :
    (IsLocalization.Away.invSelf (l : A) : PreDisc l u ρ) ∈ ball l u ρ (l : ℝ) := by
  refine Submodule.subset_span ?_
  rw [monos, Set.mem_setOf_eq]
  refine ⟨0, 0, 1, ?_, ?_⟩
  · simp
  · simp

theorem norm_mul_l (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A)‖ * l = ‖y‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  rw [norm_preDisc, norm_preDisc]
  apply le_antisymm
  · have h := gauge_mul_le_of_mem_ball y _ (inv_pos.mpr hl0) (algebraMap_natCast_mem_ball_inv (u := u) (ρ := ρ) hl0)
    calc gauge l u ρ (y * algebraMap A (PreDisc l u ρ) (l : A)) * l
        ≤ gauge l u ρ y * (l : ℝ)⁻¹ * l := mul_le_mul_of_nonneg_right h hl0.le
      _ = gauge l u ρ y := by rw [mul_assoc, inv_mul_cancel₀ hl0.ne', mul_one]
  · have h := gauge_mul_le_of_mem_ball (y * algebraMap A (PreDisc l u ρ) (l : A)) _ hl0
      (invSelf_mem_ball (u := u) (ρ := ρ))
    rwa [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one] at h

theorem norm_mul_l_pow (n : ℕ) (y : PreDisc l u ρ) :
    ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n‖ * (l : ℝ) ^ n = ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := norm_mul_l (y * algebraMap A (PreDisc l u ρ) (l : A) ^ n)
    calc ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ (n + 1)‖ * (l : ℝ) ^ (n + 1)
        = ‖y * algebraMap A (PreDisc l u ρ) (l : A) ^ n * algebraMap A (PreDisc l u ρ) (l : A)‖ * l
            * (l : ℝ) ^ n := by
          rw [pow_succ, pow_succ, mul_assoc y]; ring
      _ = ‖y‖ := by rw [h, ih]

private theorem exists_mul_pow_eq_algebraMap (p : PreDisc l u ρ) :
    ∃ (a : A) (k : ℕ), p * algebraMap A (PreDisc l u ρ) (l : A) ^ k = algebraMap A (PreDisc l u ρ) a := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (l : A)) p
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  refine ⟨a, k, ?_⟩
  rw [← map_pow, hk]
  exact h

private theorem norm_ofPre_eq_mul_pow {p : PreDisc l u ρ} {a : A} {k : ℕ}
    (h : p * algebraMap A (PreDisc l u ρ) (l : A) ^ k = algebraMap A (PreDisc l u ρ) a) :
    ‖ofPre l u ρ p‖ = ‖toDisc l u ρ a‖ * (l : ℝ) ^ k := by
  have e : ‖toDisc l u ρ a‖ = ‖algebraMap A (PreDisc l u ρ) a‖ := by
    rw [toDisc, RingHom.comp_apply, norm_ofPre, norm_preDisc]
  rw [e, ← h, norm_mul_l_pow, norm_ofPre, norm_preDisc]

private theorem sq_mul_norm_mul_norm_le_norm_mul (N : A → ℝ) (c : ℝ) (hc : 0 < c) (hmul : ∀ x y, N (x * y) = N x * N y)
    (hle : ∀ x, N x ≤ ‖toDisc l u ρ x‖) (hge : ∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) (p q : PreDisc l u ρ) :
    c ^ 2 * (‖ofPre l u ρ p‖ * ‖ofPre l u ρ q‖) ≤ ‖ofPre l u ρ p * ofPre l u ρ q‖ := by
  obtain ⟨a, k, hp⟩ := exists_mul_pow_eq_algebraMap p
  obtain ⟨b, m, hq⟩ := exists_mul_pow_eq_algebraMap q
  have hpq : p * q * algebraMap A (PreDisc l u ρ) (l : A) ^ (k + m) =
      algebraMap A (PreDisc l u ρ) (a * b) := by
    rw [map_mul, ← hp, ← hq, pow_add]; ring
  rw [← map_mul, norm_ofPre_eq_mul_pow hp, norm_ofPre_eq_mul_pow hq, norm_ofPre_eq_mul_pow hpq, pow_add]
  have hab : N a * N b ≤ ‖toDisc l u ρ (a * b)‖ := by rw [← hmul]; exact hle _
  have h0 : 0 ≤ c * ‖toDisc l u ρ a‖ := mul_nonneg hc.le (norm_nonneg _)
  have h1 : 0 ≤ c * ‖toDisc l u ρ b‖ := mul_nonneg hc.le (norm_nonneg _)
  have key : c * ‖toDisc l u ρ a‖ * (c * ‖toDisc l u ρ b‖) ≤ ‖toDisc l u ρ (a * b)‖ :=
    (mul_le_mul (hge a) (hge b) h1 (h0.trans (hge a))).trans hab
  have hpow : 0 ≤ (l : ℝ) ^ k * (l : ℝ) ^ m := by positivity
  calc c ^ 2 * (‖toDisc l u ρ a‖ * (l : ℝ) ^ k * (‖toDisc l u ρ b‖ * (l : ℝ) ^ m))
      = c * ‖toDisc l u ρ a‖ * (c * ‖toDisc l u ρ b‖) * ((l : ℝ) ^ k * (l : ℝ) ^ m) := by ring
    _ ≤ ‖toDisc l u ρ (a * b)‖ * ((l : ℝ) ^ k * (l : ℝ) ^ m) := mul_le_mul_of_nonneg_right key hpow

theorem isDomain_disc (l : ℕ) [hl : Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0) (N : A → ℝ) (c : ℝ)
    (hc : 0 < c) (hmul : ∀ x y, N (x * y) = N x * N y) (_hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hNl : N (l : A) = (l : ℝ)⁻¹) (hle : ∀ x, N x ≤ ‖toDisc l u ρ x‖) (hge : ∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) :
    IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
  have hmain : ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
    intro x y
    refine (denseRange_ofPre l u ρ).induction_on₂
      (p := fun x y : Disc l u ρ => c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ?_ ?_ x y
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro p q
      exact sq_mul_norm_mul_norm_le_norm_mul N c hc hmul hle hge p q
  have hlinv : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hl.out.pos)
  have hne : toDisc l u ρ (l : A) ≠ 0 := by
    intro h
    have h' := hle (l : A)
    rw [h, norm_zero, hNl] at h'
    linarith
  haveI : Nontrivial (Disc l u ρ) := ⟨⟨_, _, hne⟩⟩
  haveI : NoZeroDivisors (Disc l u ρ) := by
    refine ⟨fun {x y} hxy => ?_⟩
    have h := hmain x y
    rw [hxy, norm_zero] at h
    have hc2 : 0 < c ^ 2 := by positivity
    have hn : ‖x‖ * ‖y‖ ≤ 0 := by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg y)]
    rcases mul_eq_zero.mp (le_antisymm hn (mul_nonneg (norm_nonneg _) (norm_nonneg _))) with h | h
    · exact Or.inl (norm_eq_zero.mp h)
    · exact Or.inr (norm_eq_zero.mp h)
  exact ⟨NoZeroDivisors.to_isDomain (α := Disc l u ρ), hmain⟩

end GlobalTheory.BSP.DiscDomain
end

section

namespace GlobalTheory.BSP

section TopFree

variable {A Q : Type} [CommRing A] [CommRing Q] {i : A →+* Q} {J : Ideal A} {ι : Type}

theorem TopBasis.eq_zero_of_forall_mem (B : TopBasis i J ι) {x : Q} (h : ∀ n : ℕ, x ∈ (J ^ n).map i) :
    x = 0 := by
  have := B.complete
  refine IsHausdorff.haus (I := J.map i) this.toIsHausdorff x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow]
  exact h n

theorem TopBasis.eq_zero_of_coeff (B : TopBasis i J ι) {x : Q} (h : ∀ k, B.c k x = 0) : x = 0 :=
  B.eq_zero_of_forall_mem fun n => by
    simpa using B.approx x n ∅ fun k _ => by rw [h k]; exact zero_mem _

theorem TopBasis.exists_sum (B : TopBasis i J ι) (z : ι → A) (hz : ∀ n : ℕ, {k | z k ∉ J ^ n}.Finite) :
    ∃ y : Q, ∀ n : ℕ, (∑ k ∈ (hz n).toFinset, i (z k) * B.b k) - y ∈ (J ^ n).map i := by
  classical
  have hc := B.complete
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (I := J.map i) hc.toIsPrecomplete
    (f := fun n => ∑ k ∈ (hz n).toFinset, i (z k) * B.b k) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow]
      have hsub : (hz m).toFinset ⊆ (hz n).toFinset := fun k hk => by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk ⊢
        exact fun h => hk (Ideal.pow_le_pow_right hmn h)
      rw [← Finset.sum_sdiff hsub, sub_add_cancel_right]
      refine neg_mem (Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      have := (Finset.mem_sdiff.1 hk).2
      simpa using this)
  refine ⟨y, fun n => ?_⟩
  have := hy n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] at this

theorem exists_eq_of_mem_pow_succ_pair (a d : A) (n : ℕ) {x : A}
    (hx : x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1)) :
    ∃ u : A, ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + 1) * u + d * w := by
  first
  | exact @_root_.GlobalTheory.PowerBound.main
  | exact _root_.GlobalTheory.PowerBound.main
  | (apply _root_.GlobalTheory.PowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerBound.main ..)

theorem mem_pow_of_mul_mem_pow_pair (a d : A) (N : ℕ) (hd : d ∈ nonZeroDivisors A)
    (hN : ∀ (x : A) (m : ℕ), a ^ m * x ∈ Ideal.span {d} → a ^ N * x ∈ Ideal.span {d}) (n : ℕ) {z : A}
    (hz : d * z ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + N + 1)) :
    z ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by
  have ha : a ∈ Ideal.span {a} ⊔ Ideal.span {d} := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
  obtain ⟨u, w, hw, e⟩ := exists_eq_of_mem_pow_succ_pair a d (n + N) hz
  have h1 : a ^ (n + N + 1) * u ∈ Ideal.span {d} :=
    Ideal.mem_span_singleton'.2 ⟨z - w, by linear_combination e⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hN u _ h1)
  have h2 : d * (z - (a ^ n * (a * v) + w)) = 0 := by
    linear_combination e - a ^ n * a * hv
  have h3 := (mem_nonZeroDivisors_iff.1 hd).1 _ h2
  rw [sub_eq_zero.1 h3]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha _))
    (Ideal.pow_le_pow_right (Nat.le_add_right n N) hw)

end TopFree

theorem TopBasis.regular_and_torsion_bounded (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q]
    (i : A →+* Q) (d : A) (N : ℕ) (ι : Type) (hd : d ∈ nonZeroDivisors A)
    (hN : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d})
    (B : TopBasis i (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ι) :
    i d ∈ nonZeroDivisors Q ∧
      ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  have hl : ∀ (m : ℕ) (k : ι) (x : Q), B.c k ((l : Q) ^ m * x) = (l : A) ^ m * B.c k x := fun m k x => by
    rw [← B.c_mul, map_pow, map_natCast]
  have hreg : ∀ x : Q, i d * x = 0 → x = 0 := fun x hx =>
    B.eq_zero_of_coeff fun k => (mem_nonZeroDivisors_iff.1 hd).1 _ (by rw [← B.c_mul, hx, map_zero])
  refine ⟨mem_nonZeroDivisors_iff.2 ⟨hreg, fun x hx => hreg x (by rwa [mul_comm])⟩, fun x m hx => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : ∀ k, ∃ z : A, d * z = B.c k ((l : Q) ^ N * x) := fun k => by
    have : (l : A) ^ m * B.c k x ∈ Ideal.span {d} := by
      rw [← hl, ← hy, mul_comm, B.c_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (hN _ _ this)
    exact ⟨z, by rw [hl, ← hz, mul_comm]⟩
  choose z hz using h1
  have hfin : ∀ n : ℕ, {k | z k ∉ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n}.Finite := fun n =>
    (B.fin ((l : Q) ^ N * x) (n + N + 1)).subset fun k hk h =>
      hk (mem_pow_of_mul_mem_pow_pair _ d N hd hN n (by rwa [hz]))
  obtain ⟨w, hw⟩ := B.exists_sum z hfin
  have key : (l : Q) ^ N * x - i d * w = 0 := B.eq_zero_of_forall_mem fun n => by
    have h2 := B.approx ((l : Q) ^ N * x) n (hfin n).toFinset fun k hk => by
      rw [← hz]
      refine Ideal.mul_mem_left _ _ ?_
      simpa using hk
    have h3 := add_mem h2 (Ideal.mul_mem_left _ (i d) (hw n))
    convert h3 using 1
    simp only [← hz, map_mul, mul_sub, Finset.mul_sum, mul_assoc]
    ring
  rw [sub_eq_zero.1 key]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.BSP
end

section

namespace GlobalTheory.BK.DivApprox

open PowerSeries GlobalTheory.BK

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_mul_le' {f g : K⟦X⟧} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ ≤ a) (hg : ∀ n, ‖coeff n g‖ ≤ b) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ a * b := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    ha hb (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

omit [IsUltrametricDist K] in
theorem eq_low_add_high (f : K⟦X⟧) (n₀ : ℕ) :
    f = (PowerSeries.mk fun n => if n < n₀ then coeff n f else 0) +
      X ^ n₀ * PowerSeries.mk fun n => coeff (n + n₀) f := by
  ext n
  rw [map_add (f := _), coeff_mk, coeff_X_pow_mul', coeff_mk]
  by_cases h : n < n₀
  · rw [if_pos h, if_neg (not_le.2 h), add_zero]
  · rw [if_neg h, if_pos (not_lt.1 h), zero_add, Nat.sub_add_cancel (not_lt.1 h)]

theorem exists_inv_mem_A {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {u : K⟦X⟧}
    (hu : u ∈ A O K) (h0 : ‖coeff 0 u‖ = 1) : ∃ w ∈ A O K, u * w = 1 := by
  obtain ⟨v, hv⟩ := (equivA O K).surjective ⟨u, hu⟩
  have hv' : PowerSeries.map (algebraMap O K) v = u := by
    rw [← coe_equivA, hv]
  have hc : algebraMap O K (constantCoeff v) = coeff 0 u := by
    rw [← hv', coeff_map, coeff_zero_eq_constantCoeff_apply]
  have hne : coeff 0 u ≠ 0 := by
    intro h
    rw [h, norm_zero] at h0
    exact zero_ne_one h0
  obtain ⟨c, hc'⟩ := (IsUnitBall.mem_range_iff (O := O) (coeff 0 u)⁻¹).2
    (by rw [norm_inv, h0, inv_one])
  have hunit : IsUnit (constantCoeff v) := by
    refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (O := O) (K := K) ?_)
    rw [map_mul, hc, hc', map_one, mul_inv_cancel₀ hne]
  obtain ⟨w, hw⟩ := (isUnit_iff_constantCoeff.2 hunit).exists_right_inv
  refine ⟨equivA O K w, (equivA O K w).2, ?_⟩
  rw [coe_equivA, ← hv', ← map_mul, hw, map_one]

theorem step {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ t) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ t) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ t) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ t * ρ := by
  have hfe := eq_low_add_high f n₀
  set r : K⟦X⟧ := PowerSeries.mk fun n => if n < n₀ then coeff n f else 0 with hr
  set fh : K⟦X⟧ := PowerSeries.mk fun n => coeff (n + n₀) f with hfh
  have hq : ∀ n, ‖coeff n (w * fh)‖ ≤ t := fun n => by
    have := norm_coeff_mul_le' zero_le_one ht hw (g := fh)
      (fun m => by rw [hfh, coeff_mk]; exact hf _) n
    rwa [one_mul] at this
  refine ⟨w * fh, r, hq, fun i hi => ?_, fun i => ?_, fun n => ?_⟩
  · rw [hr, coeff_mk, if_neg (not_lt.2 hi)]
  · rw [hr, coeff_mk]
    split_ifs
    · exact hf _
    · rwa [norm_zero]
  · have : f - w * fh * g - r = -(w * fh * p) := by
      rw [hg]
      linear_combination hfe - X ^ n₀ * fh * huw
    rw [this, map_neg, norm_neg]
    exact norm_coeff_mul_le' ht hρ hq hp n

theorem iterate {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k : ℕ) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ ρ ^ k := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp, by simp, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨q, r, hq, hr0, hr, he⟩ := ih
    obtain ⟨q', r', hq', hr0', hr', he'⟩ := step hρ (pow_nonneg hρ k) hg huw hw hp _ he
    have h1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ hρ1
    refine ⟨q + q', r + r', fun n => ?_, fun i hi => ?_, fun n => ?_, fun n => ?_⟩
    · rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hq n) ((hq' n).trans h1))
    · rw [map_add (f := _), hr0 i hi, hr0' i hi, add_zero]
    · rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr n) ((hr' n).trans h1))
    · have : f - (q + q') * g - (r + r') = f - q * g - r - q' * g - r' := by ring
      rw [this, pow_succ]
      exact he' n

theorem exists_div_approx (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧) (hg : g ∈ A O K) (n₀ : ℕ)
    (h1 : ‖coeff n₀ g‖ = 1) (hlt : ∀ i < n₀, ‖coeff i g‖ < 1) (δ : ℝ) (hδ : 0 < δ)
    (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧
      ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  set ρ : NNReal := (Finset.range n₀).sup (fun i => ‖coeff i g‖₊) with hρ
  have hρ1 : ρ < 1 := by
    rw [hρ, Finset.sup_lt_iff (by simp)]
    intro i hi
    exact_mod_cast hlt i (Finset.mem_range.1 hi)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  obtain ⟨w, hw, huw⟩ := exists_inv_mem_A (O := O)
    (u := PowerSeries.mk fun n => coeff (n + n₀) g)
    (fun n => by rw [coeff_mk]; exact hg _) (by rw [coeff_mk, zero_add, h1])
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hρ1'
  obtain ⟨q, r, hq, hr0, hr, he⟩ := iterate ρ.2 hρ1'.le (eq_low_add_high g n₀) huw hw
    (fun n => by
      rw [coeff_mk]
      split_ifs with h
      · exact_mod_cast Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 h)
      · rw [norm_zero]; exact ρ.2) f hf k
  exact ⟨q, hq, r, hr0, hr, fun n => (he n).trans hk.le⟩

end GlobalTheory.BK.DivApprox
end
