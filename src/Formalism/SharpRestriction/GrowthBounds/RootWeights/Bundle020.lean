module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.TraceProjectionIsInvProj
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle018
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle006
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle011
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle015

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem rootWeight_apply_first {n : ℕ} {a c : Fin n} (h : a ≠ c) : rootW a c a = 1 := by
  simp [rootW, Pi.single_apply, h]

theorem rootWeight_apply_second {n : ℕ} {a c : Fin n} (h : a ≠ c) : rootW a c c = -1 := by
  simp [rootW, Pi.single_apply, h.symm]

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem integral_operator_pow_shifts_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (a c : Fin n) (j : ℕ) : ((E a c) ^ j) x ∈ weightSp E (nu + (j : ℤ) • rootW a c) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := gl_rep_operator_weight_shift hE ih a c
    have e : nu + ((j + 1 : ℕ) : ℤ) • rootW a c = nu + (j : ℤ) • rootW a c + rootW a c := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [e]; exact h

theorem offdiag_operator_nilpotent_on_weight [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) {a c : Fin n} (hac : a ≠ c) :
    ∃ j : ℕ, ((E a c) ^ j) x = 0 := by
  obtain ⟨F, hF⟩ := findim_exists_finite_weights E hE.2.2
  by_contra hcon
  push Not at hcon
  have hin : ∀ j : ℕ, nu + (j : ℤ) • rootW a c ∈ F := by
    intro j
    by_contra hj
    exact hcon j (weight_support_sum_eq_zero (O := O) E (fun mu => mu ∈ F) (integral_operator_pow_shifts_weight hE hx a c j) (hF Submodule.mem_top) hj)
  have hinj : Function.Injective (fun j : ℕ => (⟨nu + (j : ℤ) • rootW a c, hin j⟩ : F)) := by
    intro i j hij
    have h1 := congrFun (congrArg Subtype.val hij) a
    simp only [Pi.add_apply, Pi.smul_apply, rootWeight_apply_first hac, smul_eq_mul, mul_one] at h1
    omega
  exact not_injective_infinite_finite _ hinj

theorem offdiag_string_reaches_top_nonzero [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) {a c : Fin n} (hac : a ≠ c) :
    ∃ j : ℕ, ((E a c) ^ j) x ≠ 0 ∧ E a c (((E a c) ^ j) x) = 0 := by
  obtain ⟨j, h1, h2⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists (p := fun j => ((E a c) ^ j) x = 0)
    (by simpa using h0) (offdiag_operator_nilpotent_on_weight hE hx hac)
  refine ⟨j, h1, ?_⟩
  rw [pow_succ', Module.End.mul_apply] at h2
  exact h2

theorem weight_entries_between_extreme_highest [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (h0 : x ≠ 0) (a : Fin n) : lam (lastIdx n) ≤ nu a ∧ nu a ≤ lam 0 := by
  constructor
  · by_cases ha : a = lastIdx n
    · subst ha; exact (irreducible_weight_end_bounds hI hx h0).2
    · have hla : lastIdx n ≠ a := fun e => ha e.symm
      obtain ⟨j, h1, h2⟩ := offdiag_string_reaches_top_nonzero hI.1 hx h0 hla
      have hw := integral_operator_pow_shifts_weight hI.1 hx (lastIdx n) a j
      obtain ⟨m, hm, h3, -⟩ := sl2_string_nonvanishing hI.1.1 hla h1 hw h2
      have hz := (irreducible_weight_end_bounds hI (integral_operator_pow_shifts_weight hI.1 hw a (lastIdx n) m) h3).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rootWeight_apply_first hla, rootWeight_apply_second hla, rootWeight_apply_second ha] at hm hz
      omega
  · by_cases ha : a = 0
    · subst ha; exact (irreducible_weight_end_bounds hI hx h0).1
    · obtain ⟨j, h1, h2⟩ := offdiag_string_reaches_top_nonzero hI.1 hx h0 ha
      have hw := integral_operator_pow_shifts_weight hI.1 hx a 0 j
      obtain ⟨m, hm, h3, -⟩ := sl2_string_nonvanishing hI.1.1 ha h1 hw h2
      have h0a : (0 : Fin n) ≠ a := fun e => ha e.symm
      have hz := (irreducible_weight_end_bounds hI (integral_operator_pow_shifts_weight hI.1 hw 0 a m) h3).1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rootWeight_apply_first ha, rootWeight_apply_second ha, rootWeight_apply_first h0a] at hm hz
      omega

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_C (E : GLOps n K V) : Module.End K V := ∑ a : Fin n, ∑ b : Fin n, E a b * E b a

theorem cr_C_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) : cr_C E * E c d = E c d * cr_C E := by
  classical
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
    intro a b
    rw [← hR b a c d, ← hR a b c d]; noncomm_ring
  have S1 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_ite]
  have S2 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_ite]
  have S3 : ∑ a : Fin n, ∑ b : Fin n, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [ite_mul]
  have S4 : ∑ a : Fin n, ∑ b : Fin n, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ite_mul]
  rw [← sub_eq_zero, cr_C, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have : ∀ a : Fin n, (∑ b : Fin n, E a b * E b a) * E c d - E c d * ∑ b : Fin n, E a b * E b a =
      ∑ b : Fin n, (E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    intro a
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => key a b
  rw [Finset.sum_congr rfl fun a _ => this a]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4]
  abel

theorem cr_C_comm_apply (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) (x : V) :
    cr_C E (E c d x) = E c d (cr_C E x) := by
  have := congrArg (fun f : Module.End K V => f x) (cr_C_comm E hR c d)
  simpa using this

theorem cr_sym {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, F a a + ∑ a, ∑ b, if a < b then F a b + F b a else 0 :=
  _root_.UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal.main F

theorem cr_C_wt (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x = ((cr_c mu : ℤ) : K) • x + (2 : K) • ∑ a : Fin n, ∑ b : Fin n, if a < b then E b a (E a b x) else 0 := by
  classical
  have hx' := (v2rep_mem_weightSp E mu x).1 hx
  have e0 : cr_C E x = ∑ a : Fin n, ∑ b : Fin n, E a b (E b a x) := by
    simp [cr_C, LinearMap.sum_apply]
  have e1 : ∀ a, E a a (E a a x) = ((mu a : K) ^ 2) • x := by
    intro a
    rw [hx' a, map_smul, hx' a, smul_smul, sq]
  have e2 : ∀ a b : Fin n, E a b (E b a x) + E b a (E a b x) =
      (2 : K) • E b a (E a b x) + ((mu a : K) - (mu b : K)) • x := by
    intro a b
    rw [v2rep_comm E hR a b b a x]
    simp only [if_true, hx' a, hx' b, sub_smul, two_smul]
    abel
  rw [e0, cr_sym, Finset.sum_congr rfl fun a _ => e1 a]
  have e3 : ∀ a b : Fin n, (if a < b then E a b (E b a x) + E b a (E a b x) else 0) =
      (2 : K) • (if a < b then E b a (E a b x) else 0) + (if a < b then ((mu a : K) - (mu b : K)) else 0) • x := by
    intro a b
    split_ifs
    · exact e2 a b
    · simp
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e3 a b]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul]
  have e4 : ((cr_c mu : ℤ) : K) = ∑ a, (mu a : K) ^ 2 + ∑ a : Fin n, ∑ b : Fin n,
      (if a < b then ((mu a : K) - (mu b : K)) else 0) := by
    simp only [cr_c, cr_h]
    push_cast
    rfl
  rw [e4, add_smul]
  abel

theorem cr_C_hwv (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) :
    cr_C E v = ((cr_c mu : ℤ) : K) • v := by
  rw [cr_C_wt E hR mu v hv.2.1]
  have : ∑ a : Fin n, ∑ b : Fin n, (if a < b then E b a (E a b v) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · rw [hv.2.2 a b h, map_zero]
    · rfl
  rw [this, smul_zero, add_zero]

theorem cr_C_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (x : V) (hx : x ∈ W) :
    cr_C E x ∈ W := by
  simp only [cr_C, LinearMap.sum_apply, Module.End.mul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hW a b _ (hW b a _ hx)

theorem cr_C_weightSp (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x ∈ weightSp E mu := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro a
  rw [← cr_C_comm_apply E hR, hx a, map_smul]

end Formalism.MainNotions.G.GLWeightTheory
end
end
