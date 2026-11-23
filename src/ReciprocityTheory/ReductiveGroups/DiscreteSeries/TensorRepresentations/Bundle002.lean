module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Lemmata.MiscLemmasP.Imports
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def oppCount (ε : Fin n → Bool) (a : Fin n) : ℕ := (univ.filter fun b => ε b ≠ ε a).card

theorem dot_root_right (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_boole]

theorem dot_sum_root_right (u : Fin n → ℝ) (Ph : Finset (Fin n × Fin n)) :
    dot u (∑ x ∈ Ph, root x.1 x.2) = ∑ x ∈ Ph, (u x.1 - u x.2) := by
  have h := fun x : Fin n × Fin n => dot_root_right u x.1 x.2
  simp only [dot] at h ⊢
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => h x

theorem oppCount_add (ε : Fin n → Bool) {a b : Fin n} (hab : ε a ≠ ε b) :
    (oppCount ε a : ℝ) + oppCount ε b = n := by
  have key : oppCount ε a + oppCount ε b = n := by
    unfold oppCount
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have hc : ∀ c : Fin n, ((if ε c ≠ ε a then 1 else 0) + (if ε c ≠ ε b then 1 else 0) : ℕ) = 1 := by
      intro c
      revert hab
      cases ε a <;> cases ε b <;> cases ε c <;> simp
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact_mod_cast key

theorem sum_root_apply (Ph : Finset (Fin n × Fin n)) (c : Fin n) :
    (∑ x ∈ Ph, root x.1 x.2) c =
      ((Ph.filter fun x => x.1 = c).card : ℝ) - ((Ph.filter fun x => x.2 = c).card : ℝ) := by
  rw [Finset.sum_apply]
  simp only [root, Pi.sub_apply, Finset.sum_sub_distrib, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x.1 = c
    · rw [h]; simp
    · have h' : ¬ c = x.1 := fun e => h e.symm
      simp [Pi.single_apply, h, h']
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x.2 = c
    · rw [h]; simp
    · have h' : ¬ c = x.2 := fun e => h e.symm
      simp [Pi.single_apply, h, h']

theorem card_fst_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (c : Fin n) :
    (Ph.filter fun x => x.1 = c).card ≤ oppCount ε c := by
  unfold oppCount
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have h1 := hnc x hx.1
    rw [hx.2] at h1
    exact Ne.symm h1
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy

theorem card_snd_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (c : Fin n) :
    (Ph.filter fun x => x.2 = c).card ≤ oppCount ε c := by
  unfold oppCount
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have h1 := hnc x hx.1
    rw [hx.2] at h1
    exact h1
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact Prod.ext hxy (hx.2.trans hy.2.symm)

theorem nsq_sum_root_le (ε : Fin n → Bool) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) :
    nsq (∑ x ∈ Ph, root x.1 x.2) ≤ n * Ph.card := by
  have hpt : ∀ c, (∑ x ∈ Ph, root x.1 x.2) c * (∑ x ∈ Ph, root x.1 x.2) c ≤
      (((Ph.filter fun x => x.1 = c).card : ℝ) + ((Ph.filter fun x => x.2 = c).card : ℝ)) *
        (oppCount ε c : ℝ) := by
    intro c
    rw [sum_root_apply]
    have h1 : ((Ph.filter fun x => x.1 = c).card : ℝ) ≤ oppCount ε c := by
      exact_mod_cast card_fst_le ε Ph hnc c
    have h2 : ((Ph.filter fun x => x.2 = c).card : ℝ) ≤ oppCount ε c := by
      exact_mod_cast card_snd_le ε Ph hnc c
    have h3 : (0 : ℝ) ≤ ((Ph.filter fun x => x.1 = c).card : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((Ph.filter fun x => x.2 = c).card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h3 h4, mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 h4]
  have hfib : ∀ g : Fin n × Fin n → Fin n,
      ∑ c, ((Ph.filter fun x => g x = c).card : ℝ) * (oppCount ε c : ℝ) =
        ∑ x ∈ Ph, (oppCount ε (g x) : ℝ) := by
    intro g
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  calc nsq (∑ x ∈ Ph, root x.1 x.2)
        = ∑ c, (∑ x ∈ Ph, root x.1 x.2) c * (∑ x ∈ Ph, root x.1 x.2) c := rfl
    _ ≤ ∑ c, (((Ph.filter fun x => x.1 = c).card : ℝ) + ((Ph.filter fun x => x.2 = c).card : ℝ)) *
          (oppCount ε c : ℝ) := Finset.sum_le_sum fun c _ => hpt c
    _ = ∑ c, ((Ph.filter fun x => x.1 = c).card : ℝ) * (oppCount ε c : ℝ) +
          ∑ c, ((Ph.filter fun x => x.2 = c).card : ℝ) * (oppCount ε c : ℝ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ x ∈ Ph, (oppCount ε x.1 : ℝ) + ∑ x ∈ Ph, (oppCount ε x.2 : ℝ) := by
        rw [hfib Prod.fst, hfib Prod.snd]
    _ = ∑ x ∈ Ph, (n : ℝ) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x hx => oppCount_add ε (hnc x hx)
    _ = n * Ph.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem kernel_lemma (ε : Fin n → Bool) (μ : Fin n → ℝ) {h : ℝ} (_hh : 0 < h) (Ph : Finset (Fin n × Fin n))
    (hnc : ∀ x ∈ Ph, ε x.1 ≠ ε x.2) (hpos : ∀ x ∈ Ph, h ≤ μ x.1 - μ x.2) :
    nsq (μ - ∑ x ∈ Ph, root x.1 x.2) ≤ nsq μ - (2 * h - n) * Ph.card := by
  have hexp : nsq (μ - ∑ x ∈ Ph, root x.1 x.2) =
      nsq μ - 2 * dot μ (∑ x ∈ Ph, root x.1 x.2) + nsq (∑ x ∈ Ph, root x.1 x.2) := by
    simp only [nsq, dot, Pi.sub_apply, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hd : h * Ph.card ≤ dot μ (∑ x ∈ Ph, root x.1 x.2) := by
    rw [dot_sum_root_right]
    have h2 : ∑ _x ∈ Ph, h ≤ ∑ x ∈ Ph, (μ x.1 - μ x.2) := Finset.sum_le_sum fun x hx => hpos x hx
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    linarith
  have hn := nsq_sum_root_le ε Ph hnc
  rw [hexp]
  linarith

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def coordV (c : Fin n) : (Fin n → M) →ₗ[ℂ] M := LinearMap.proj c

def tensV (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) + if c = a then coordV b else 0

def tensVd (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) - if c = b then coordV a else 0

def eeV (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun s => ∑ r, (E r s).comp (coordV r)

def eeVd (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun r => -∑ s, (E r s).comp (coordV s)

def diagOp (A : Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => A.comp (coordV c)

theorem tensV_coord (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + if c = a then f b else 0 := by
  simp only [tensV, coordV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]

theorem tensVd_coord (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - if c = b then f a else 0 := by
  simp only [tensVd, coordV, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]

theorem eeV_coord (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (s : Fin n) :
    eeV E f s = ∑ r, E r s (f r) := by
  simp [eeV, coordV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem eeVd_coord (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (r : Fin n) :
    eeVd E f r = -∑ s, E r s (f s) := by
  simp [eeVd, coordV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem diagOp_coord (A : Module.End ℂ M) (f : Fin n → M) (c : Fin n) :
    diagOp (n := n) A f c = A (f c) := by
  simp [diagOp, coordV]

theorem isGlRep_apply_swap {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b c d : Fin n) (v : M) :
    E a b (E c d v) = E c d (E a b v) + ((if b = c then E a d v else 0) - (if d = a then E c b v else 0)) := by
  have h := LinearMap.congr_fun (hE a b c d) v
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add'] at h
  rw [h]; congr 1
  split_ifs <;> simp

theorem ite_end_coord (p : Prop) [Decidable p] (A : Module.End ℂ (Fin n → M)) (f : Fin n → M) (x : Fin n) :
    (if p then A else 0) f x = if p then A f x else 0 := by
  split_ifs <;> rfl

theorem tensV_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, tensV_coord, map_add (f := _),
    isGlRep_apply_swap hE a b c d, ite_end_coord]
  split_ifs <;> subst_vars <;>
    simp only [map_zero, add_zero, sub_zero, zero_sub, sub_self] <;> abel

theorem tensVd_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, tensVd_coord, map_sub,
    isGlRep_apply_swap hE a b c d, ite_end_coord]
  split_ifs <;> subst_vars <;>
    simp only [map_zero, add_zero, sub_zero, zero_sub, sub_self] <;> first | (exfalso; simp_all; done) | abel

theorem casimir_tensV {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensV E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeV E := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [casimir, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, diagOp_coord, eeV_coord, tensV_coord, map_add,
    Module.End.one_apply]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ g : Fin n → Fin n → M, (∑ i, ∑ j, if x = i then g i j else 0) = ∑ j, g x j := by
    intro g
    rw [Finset.sum_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  rw [key (fun i j => E j i (f j) + f i)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul, two_smul]
  abel

theorem casimir_tensVd {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensVd E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeVd E := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [casimir, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, diagOp_coord, eeVd_coord, tensVd_coord, map_sub,
    Module.End.one_apply]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ g : Fin n → Fin n → M, (∑ i, ∑ j, if x = i then g i j else 0) = ∑ j, g x j := by
    intro g
    rw [Finset.sum_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  rw [key (fun i j => E i j (f j))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul, two_smul]
  abel

theorem eeV_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensV E a b * eeV E = eeV E * tensV E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_

  simp only [Module.End.mul_apply, tensV_coord, eeV_coord, map_sum, map_add (f := _), isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = a
  · subst h; simp only [if_true]; abel
  · simp only [h, if_false, Finset.sum_const_zero, sub_zero, add_zero]

theorem eeVd_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensVd E a b * eeVd E = eeVd E * tensVd E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_

  simp only [Module.End.mul_apply, tensVd_coord, eeVd_coord, map_sum, map_neg, map_sub, isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = b
  · subst h; simp only [if_true]; abel
  · have h' : ¬ b = x := fun e => h e.symm
    simp only [h, h', if_false, Finset.sum_const_zero, sub_zero, zero_sub]
    abel

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def ePow (E : Fin n → Fin n → Module.End ℂ M) : ℕ → Fin n → Fin n → Module.End ℂ M :=
  Bl.ThirdBlockLemmaA.goal1 E

def gelfand (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) : Module.End ℂ M :=
  ∑ a, ePow E k a a

theorem commutator_mul_right (X Y Z : Module.End ℂ M) :
    X * (Y * Z) - Y * Z * X = (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by
  noncomm_ring

theorem ePow_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    E a b * ePow E k c d - ePow E k c d * E a b =
      (if b = c then ePow E k a d else 0) - (if d = a then ePow E k c b else 0) := by
  have hz : ∀ c d, ePow E 0 c d = if c = d then 1 else 0 := fun c d => rfl
  have hs : ∀ k c d, ePow E (k + 1) c d = ∑ e, E c e * ePow E k e d := by
    intro k c d
    unfold ePow Bl.ThirdBlockLemmaA.goal1
    simp [pow_succ', Matrix.mul_apply]
  induction k generalizing c d with
  | zero =>
    simp only [hz]
    split_ifs <;> subst_vars <;> simp_all
  | succ k ih =>
    rw [hs, hs, hs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [commutator_mul_right, hE a b c, ih]
    by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp [hbc, hda, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq', mul_assoc] <;> abel

theorem gelfand_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b : Fin n) :
    E a b * gelfand E k = gelfand E k * E a b := by
  have h : E a b * gelfand E k - gelfand E k * E a b = 0 := by
    unfold gelfand
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [ePow_comm hE]
    simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  exact sub_eq_zero.mp h

end ReciprocityTheory.ChartRestriction.DS
end
end
