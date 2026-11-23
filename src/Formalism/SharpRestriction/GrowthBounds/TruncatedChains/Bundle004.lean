module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalEigen
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorCoeffSuccIndex
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem raising_lowering_mul_comm_add {E : GLOps n K V} (hE : IsGLRep E) (a b : Fin n) :
    E a b * E b a = E b a * E a b + (E a a - E b b) := by
  have h := hE.1 a b b a
  simp only [if_true] at h
  exact eq_add_of_sub_eq' h

theorem cartan_raising_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) :
    (E a a - E b b) * E a b = E a b * (E a a - E b b) + (2 : K) • E a b := by
  have h1 := hE.1 a a a b
  have h2 := hE.1 b b a b
  simp only [if_true, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2
  rw [sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]
  abel

theorem cartan_lowering_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) :
    (E a a - E b b) * E b a = E b a * (E a a - E b b) - (2 : K) • E b a := by
  have h1 := hE.1 a a b a
  have h2 := hE.1 b b b a
  simp only [if_true, if_neg hab, if_neg (Ne.symm hab), sub_zero, zero_sub] at h1 h2
  rw [sub_mul, mul_sub, two_smul, eq_add_of_sub_eq' h1, eq_add_of_sub_eq' h2]
  abel

theorem cartan_difference_apply_weight (E : GLOps n K V) (a b : Fin n) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    (E a a - E b b) x = ((ν a : K) - (ν b : K)) • x := by
  have hw : ∀ c, E c c x = (ν c : K) • x := fun c => by
    have h := (Submodule.mem_iInf _).1 hx c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at h
    exact h
  rw [LinearMap.sub_apply, hw a, hw b, sub_smul]

theorem raising_projector_factor_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) (ν : Fin n → ℤ) (s T : ℕ)
    (hnil : (E a b) ^ T = 0) (x : V) (hx : x ∈ weightSp E ν) :
    E a b (pf E a b s T x) =
      (((s : K) - ((ν a : K) - (ν b : K)) - 1) / ((s : K) + 1)) • pf E a b (s + 1) T (E a b x) := by
  rw [pf_eq_P, pf_eq_P]
  exact R1 (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_lowering_commute hE hab) (cartan_difference_apply_weight E a b ν x hx) s T hnil

theorem projector_factor_lowering_commute {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b) (ν : Fin n → ℤ) (s T : ℕ)
    (hnil : (E a b) ^ T = 0) (z : V) (hz : z ∈ weightSp E ν) :
    pf E a b s T (E b a z) =
      (((s : K) + 1 - ((ν a : K) - (ν b : K))) / ((s : K) + 1)) • E b a (pf E a b (s + 1) T z) := by
  rw [pf_eq_P, pf_eq_P]
  exact sl2_projector_apply_f_eq_smul_f_projector_succ (raising_lowering_mul_comm_add hE a b) (cartan_raising_commute hE hab) (cartan_difference_apply_weight E a b ν z hz) s T hnil

theorem projector_factor_mem_weight_space {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (ν : Fin n → ℤ) (a b : Fin n) (c T : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : pf E a b c T x ∈ weightSp E ν := by
  have hpow : ∀ (a' b' : Fin n) (k : ℕ) (μ : Fin n → ℤ) (y : V), y ∈ weightSp E μ →
      ((E a' b') ^ k) y ∈ weightSp E (μ + k • rootW a' b') := by
    intro a' b' k
    induction k with
    | zero =>
      intro μ y hy
      simpa using hy
    | succ k ih =>
      intro μ y hy
      rw [pow_succ', Module.End.mul_apply, succ_nsmul, ← add_assoc]
      exact hs a' b' _ _ (ih μ y hy)
  rw [pf_eq, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [Module.End.mul_apply]
  have h1 := hpow b a k _ _ (hpow a b k ν x hx)
  have e : ν + k • rootW a b + k • rootW b a = ν := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, rootW, Pi.sub_apply, smul_eq_mul]
    ring
  rwa [e] at h1

end

theorem restKill : RestKill := by
  intro K V _ _ _ _ _ n E hE a b hab ν s hs T hT x hx
  have hnil := restNil K V n E hE a b hab T hT
  rw [raising_projector_factor_commute hE hab ν s T hnil x hx]
  have h0 : ((s : K) - ((ν a : K) - (ν b : K)) - 1) = 0 := by
    have h1 : ((s : ℤ) : K) = ((ν a - ν b + 1 : ℤ) : K) := by rw [hs]
    push_cast at h1
    rw [h1]
    ring
  rw [h0, zero_div, zero_smul]

theorem restPair : RestPair := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s u hsu T hT w hw
  have hsh := gl_rep_shifts_weights hE
  have n1 := restNil K V n E hE a b hab T hT
  have n3 := restNil K V n E hE a c hac T hT
  have c1 := fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ab hE hab hac hbc s T n1)
  have c3 := fun y : V => congrArg (fun g : Module.End K V => g y) (cross_ac hE hab hac hbc u T n3)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at c1 c3
  have hz : pf E a c (u + 1) T (E a c w) ∈ weightSp E (ν + rootW a c) :=
    projector_factor_mem_weight_space hsh _ a c _ T _ (hsh a c ν w hw)
  rw [c1, c3, raising_projector_factor_commute hE hac ν u T n3 w hw, map_sub, map_smul, map_smul, map_smul,
    projector_factor_lowering_commute hE hab _ s T n1 _ hz]
  generalize E b a (pf E a b (s + 1) T (pf E a c (u + 1) T (E a c w))) = Y
  rw [smul_smul, smul_smul, sub_add, sub_eq_self, ← sub_smul]
  have hs1 : (s : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  have hu1 : (u : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero u
  have hK : (u : K) - ((ν a : K) - (ν c : K)) - 1 = (s : K) - ((ν a : K) - (ν b : K)) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : K)) hsu
  have ra : (ν + rootW a c) a = ν a + 1 := by simp [rootW, hac]
  have rb : (ν + rootW a c) b = ν b := by simp [rootW, hab.symm, hbc]
  rw [ra, rb, hK]
  convert zero_smul K Y using 2
  push_cast
  field_simp
  ring

end Formalism.MainNotions.G.ExtremalProjector
end
end

section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section Tens

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def zSub (K V : Type*) [Field K] [AddCommGroup V] [Module K V] {n : ℕ} (j : Fin n) : Submodule K (Fin n → V) :=
  LinearMap.ker (LinearMap.proj j : (Fin n → V) →ₗ[K] V)

theorem mem_zSub (j : Fin n) (w : Fin n → V) : w ∈ zSub K V j ↔ w j = 0 := by
  simp [zSub]

theorem ev_pf_ne (E : GLOps n K V) (a x y : Fin n) (hx : x ≠ a) (hy : y ≠ a) (c T : ℕ) (w : Fin n → V) :
    (pf (tensOps E) x y c T w) a = pf E x y c T (w a) := by
  refine pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) ⊤ x y (fun _ _ => trivial)
    (fun w _ => ?_) (fun w => ?_) c T w trivial
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hx.symm, add_zero]
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]

theorem ev_pf_a (E : GLOps n K V) (a y : Fin n) (hy : y ≠ a) (c T : ℕ) (w : Fin n → V) (hw : w y = 0) :
    (pf (tensOps E) a y c T w) a = pf E a y c T (w a) := by
  refine pf_intertw (tensOps E) E (LinearMap.proj a : (Fin n → V) →ₗ[K] V) (zSub K V y) a y (fun w hw => ?_)
    (fun w hw => ?_) (fun w => ?_) c T w ((mem_zSub y w).2 hw)
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hy, hw, map_zero, add_zero]
  · rw [mem_zSub] at hw
    rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_pos rfl, hw, add_zero]
  · rw [LinearMap.proj_apply, LinearMap.proj_apply, tensOps_apply, if_neg hy.symm, add_zero]

theorem z_pf (E : GLOps n K V) (j x y : Fin n) (hx : j ≠ x) (hy : j ≠ y) (c T : ℕ) (w : Fin n → V) (hw : w j = 0) :
    (pf (tensOps E) x y c T w) j = 0 := by
  rw [← mem_zSub (K := K)]
  refine pf_mem (tensOps E) (zSub K V j) x y (fun w hw => ?_) (fun w hw => ?_) c T w ((mem_zSub j w).2 hw)
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hx, hw, map_zero, add_zero]
  · rw [mem_zSub] at hw ⊢
    rw [tensOps_apply, if_neg hy, hw, map_zero, add_zero]

theorem zz_pf (E : GLOps n K V) (b c : Fin n) (s T : ℕ) (w : Fin n → V) (hb : w b = 0) (hc : w c = 0) :
    (pf (tensOps E) b c s T w) b = 0 ∧ (pf (tensOps E) b c s T w) c = 0 := by
  have key : ∀ x y : Fin n, (x = b ∨ x = c) → (y = b ∨ y = c) → ∀ w ∈ zSub K V b ⊓ zSub K V c,
      tensOps E x y w ∈ zSub K V b ⊓ zSub K V c := by
    intro x y _ hy w hw
    rw [Submodule.mem_inf, mem_zSub, mem_zSub] at hw ⊢
    have hwy : w y = 0 := by rcases hy with rfl | rfl; exacts [hw.1, hw.2]
    rw [tensOps_apply, tensOps_apply, hw.1, hw.2, hwy]
    simp
  have := pf_mem (tensOps E) (zSub K V b ⊓ zSub K V c) b c (key b c (Or.inl rfl) (Or.inr rfl))
    (key c b (Or.inr rfl) (Or.inl rfl)) s T w
    (by rw [Submodule.mem_inf, mem_zSub, mem_zSub]; exact ⟨hb, hc⟩)
  rwa [Submodule.mem_inf, mem_zSub, mem_zSub] at this

end Tens

theorem ybat_step (sg ta : ℕ) (h : YBat sg ta) : YBat (sg + 1) ta := by
  intro K V _ _ _ _ _ n E hE a b c hab hac hbc ν s t hs ht T hT x hx
  have hA : IsGLRep (tensOps E) := tens_isGLRep hE
  obtain ⟨T', hT0, hT2⟩ : ∃ T' : ℕ, T ≤ T' ∧ Module.finrank K (Fin n → V) ≤ T' :=
    ⟨max T (Module.finrank K (Fin n → V)), le_max_left _ _, le_max_right _ _⟩
  have hT1 : Module.finrank K V ≤ T' := hT.trans hT0
  have hw0 : (Pi.single a x : Fin n → V) ∈ weightSp (tensOps E) (ν + Pi.single a 1) := tens_single_wt E ν a x hx
  have e1 : (s : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) a - (ν + Pi.single a 1 : Fin n → ℤ) b + sg + 1 := by
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.symm, hs]
    push_cast
    ring
  have e2 : (t : ℤ) = (ν + Pi.single a 1 : Fin n → ℤ) b - (ν + Pi.single a 1 : Fin n → ℤ) c + ta + 1 := by
    rw [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hab.symm, Pi.single_eq_of_ne hac.symm, ht]
    ring
  have key := h K (Fin n → V) n (tensOps E) hA a b c hab hac hbc (ν + Pi.single a 1) s t e1 e2 T' hT2 _ hw0
  have key' := congrArg (fun w : Fin n → V => w a) key
  have z0b : (Pi.single a x : Fin n → V) b = 0 := by rw [Pi.single_apply, if_neg hab.symm]
  have z0c : (Pi.single a x : Fin n → V) c = 0 := by rw [Pi.single_apply, if_neg hac.symm]
  have z0a : (Pi.single a x : Fin n → V) a = x := by rw [Pi.single_apply, if_pos rfl]
  obtain ⟨z1b, z1c⟩ := zz_pf E b c t T' _ z0b z0c
  have z2b := z_pf E b a c hab.symm hbc (s + t) T' _ z1b
  have y1c := z_pf E c a b hac.symm hbc.symm s T' _ z0c
  rw [ev_pf_a E a b hab.symm s T' _ z2b, ev_pf_a E a c hac.symm (s + t) T' _ z1c,
    ev_pf_ne E a b c hab.symm hac.symm t T', ev_pf_ne E a b c hab.symm hac.symm t T',
    ev_pf_a E a c hac.symm (s + t) T' _ y1c, ev_pf_a E a b hab.symm s T' _ z0b, z0a] at key'
  rw [pf_trunc E hE a b hab s T T' hT hT1, pf_trunc E hE a c hac (s + t) T T' hT hT1,
    pf_trunc E hE b c hbc t T T' hT hT1]
  exact key'

theorem restYB_of (base : YBat 0 0) (symm : ∀ sg ta, YBat sg ta → YBat ta sg) : RestYB := by
  have h1 : ∀ sg, YBat sg 0 := by
    intro sg
    induction sg with
    | zero => exact base
    | succ k ih => exact ybat_step k 0 ih
  intro sg ta
  induction ta with
  | zero => exact h1 sg
  | succ k ih => exact symm _ _ (ybat_step k sg (symm _ _ ih))

end Formalism.MainNotions.G.ExtremalProjector
end
end
