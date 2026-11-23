module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

def Pn {N : ℕ} (ν : Fin N → ℕ) : ℕ := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (ν i - ν j + (j - i) : ℕ)

def Qn {N : ℕ} (ν : Fin N → ℕ) : ℕ := ∏ i : Fin N, (ν i + (N - 1 - i)).factorial

theorem Pn_succ_shift {N : ℕ} (μ : Fin N → ℕ) : Pn (fun i => μ i + 1) = Pn μ := by
  unfold Pn
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  dsimp only
  omega

theorem Qn_succ_shift {N : ℕ} (μ : Fin N → ℕ) :
    Qn (fun i => μ i + 1) = (∏ i : Fin N, (μ i + N - i)) * Qn μ := by
  unfold Qn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have e : μ i + 1 + (N - 1 - (i : ℕ)) = (μ i + (N - 1 - (i : ℕ))) + 1 := by omega
  have e2 : μ i + N - (i : ℕ) = μ i + (N - 1 - (i : ℕ)) + 1 := by omega
  rw [e, e2, Nat.factorial_succ]

theorem Ioi_eq_filter {m : ℕ} (x : Fin m) : Finset.Ioi x = Finset.univ.filter (fun j => x < j) := by
  ext j
  simp

theorem prod_Ioi_castSucc {M : Type*} [CommMonoid M] (n : ℕ) (i : Fin n) (g : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Ioi (Fin.castSucc i), g j = (∏ j ∈ Finset.Ioi i, g (Fin.castSucc j)) * g (Fin.last n) := by
  rw [Ioi_eq_filter, Ioi_eq_filter, Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, if_true]

theorem Pn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Pn ν = Pn (fun i : Fin n => ν (Fin.castSucc i)) * ∏ i : Fin n, (ν (Fin.castSucc i) + (n - i)) := by
  unfold Pn
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last n), (ν (Fin.last n) - ν j + ((j : ℕ) - ((Fin.last n : Fin (n + 1)) : ℕ))) = 1 := by
    rw [Finset.eq_empty_of_forall_notMem fun j hj => absurd (Finset.mem_Ioi.mp hj) (not_lt.mpr (Fin.le_last j)), Finset.prod_empty]
  rw [hlast, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [prod_Ioi_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, h]
  congr 1 <;> omega

theorem Qn_last_zero (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Qn ν = (∏ i : Fin n, (ν (Fin.castSucc i) + (n - i))) * Qn (fun i : Fin n => ν (Fin.castSucc i)) := by
  unfold Qn
  rw [Fin.prod_univ_castSucc, h, ← Finset.prod_mul_distrib]
  have hl : (0 + (n + 1 - 1 - ((Fin.last n : Fin (n + 1)) : ℕ))).factorial = 1 := by
    simp
  rw [hl, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  simp only [Fin.coe_castSucc]
  have e : ν (Fin.castSucc i) + (n + 1 - 1 - (i : ℕ)) = (ν (Fin.castSucc i) + (n - 1 - (i : ℕ))) + 1 := by omega
  rw [e, Nat.factorial_succ]
  congr 1
  omega

theorem castSucc2_injective (n : ℕ) :
    Function.Injective (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) := by
  intro a b h
  simp only [Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2

theorem hook_norm : HookNormOf := by
  intro hR hH hL hS
  suffices key : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
    intro N ν hν
    have := key N ν hν
    unfold Pn Qn at this
    simp only [Nat.cast_prod] at this
    exact this
  intro N
  induction N with
  | zero => intro ν _; simp [Pn, Qn, hw, fockQ]
  | succ n ih =>
    suffices hk : ∀ (k : ℕ) (ν : Fin (n + 1) → ℕ), Antitone ν → ν (Fin.last n) = k →
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) * (Pn ν : ℚ) = (Qn ν : ℚ) by
      intro ν hν; exact hk _ ν hν rfl
    intro k
    induction k with
    | zero =>
      intro ν hν h0
      have hν' : Antitone (fun i : Fin n => ν i.castSucc) :=
        fun a b hab => hν (Fin.castSucc_le_castSucc_iff.2 hab)
      rw [hL n ν hν h0, hR _ _ _ (castSucc2_injective n), Pn_last_zero n ν h0, Qn_last_zero n ν h0,
        Nat.cast_mul, Nat.cast_mul, ← ih _ hν']
      ring
    | succ k ihk =>
      intro ν hν hk
      have hge : ∀ i, 1 ≤ ν i := fun i => by have := hν (Fin.le_last i); omega
      obtain ⟨μ, rfl⟩ : ∃ μ : Fin (n + 1) → ℕ, ν = fun i => μ i + 1 :=
        ⟨fun i => ν i - 1, funext fun i => by have := hge i; show ν i = ν i - 1 + 1; omega⟩
      have hμ : Antitone μ := fun a b hab => by have := hν hab; simp only at this; omega
      have hμk : μ (Fin.last n) = k := by simp only at hk; omega
      rw [Pn_succ_shift, Qn_succ_shift, hH _ μ hμ, hS _ μ hμ, Nat.cast_mul, Nat.cast_prod,
        ← ihk μ hμ hμk]
      ring

end PI.HookSteps
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

theorem highest_weight_det_mul : HwDetMul := by
  intro N ν _
  cases N with
  | zero => simp [hw, detX]
  | succ n =>
    simp only [hw]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have hlast : ∀ μ : Fin (n + 1) → ℕ, nuNext μ (Fin.last n) = 0 := by
      intro μ; simp [nuNext]
    have hcs : ∀ s : Fin n, (ν s.castSucc + 1) - nuNext (fun i => ν i + 1) s.castSucc =
        ν s.castSucc - nuNext ν s.castSucc := by
      intro s
      have hs := s.isLt
      simp only [nuNext, Fin.val_castSucc]
      rw [dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega), dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega)]
      omega
    simp only [hlast, hcs, Nat.sub_zero]
    have hL : lpMinor ℚ ((Fin.last n : ℕ) + 1) (r := n + 1) (n := n + 1) (by simp) (by simp) =
        detX (n + 1) := rfl
    rw [hL, pow_succ]
    ring

theorem lpMinor_rename (n s : ℕ) (h1 h2 : s ≤ n) (h3 h4 : s ≤ n + 1) :
    rename (fun v : Fin n × Fin n => (Fin.castSucc v.1, Fin.castSucc v.2)) (lpMinor ℚ s h1 h2) =
      lpMinor ℚ s h3 h4 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X]
  rfl

theorem highest_weight_last_zero : HwLastZero := by
  intro n ν _ hl
  simp only [hw]
  rw [Fin.prod_univ_castSucc, map_prod]
  have hlast : nuNext ν (Fin.last n) = 0 := by simp [nuNext]
  rw [hlast, hl, Nat.sub_zero, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hs := s.isLt
  rw [map_pow, lpMinor_rename n ((s : ℕ) + 1) _ _ (by omega) (by omega)]
  congr 1
  simp only [nuNext, Fin.val_castSucc]
  rw [dite_eq_left (show (s : ℕ) + 1 < n + 1 by omega)]
  by_cases h : (s : ℕ) + 1 < n
  · rw [dite_eq_left h]; rfl
  · rw [dite_eq_right h]
    have : (⟨s.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
    rw [this, hl]

theorem rename_isomorphism : RenameIso := by
  intro σ τ φ hφ f g
  classical
  unfold fockQ
  rw [support_rename_of_injective hφ, Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hφ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_rename_mapDomain φ hφ, coeff_rename_mapDomain φ hφ]
  congr 2
  rw [Finsupp.mapDomain_support_of_injective hφ, Finset.prod_image (fun a _ b _ h => hφ h)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hφ]

end PI.HookSteps
end
end

section

namespace PI.HookSteps

theorem hookBound_of_steps (hB : HookBoundOf) (hN : HookNormOf) (hS : DetShiftNormOf)
    (hR : RenameIso) (hH : HwDetMul) (hL : HwLastZero) (hA : DetAdj) (hD : DetDetId)
    (hP : PolEqRowDiv) : PI.HookBound :=
  hB (hN hR hH hL (hS hA hD hP hH))

end PI.HookSteps
end

section

noncomputable section

namespace PI.HookSteps.Cap

open MvPolynomial

section Abs

variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]

def xw (x : I → S → 𝒰) {k : ℕ} (r : Fin k → I) (s : Fin k → S) : 𝒰 :=
  (List.ofFn fun j => x (r j) (s j)).prod

def dw (d : I → S → 𝒰) {k : ℕ} (g : Fin k → I) (s : Fin k → S) : 𝒰 :=
  (List.ofFn fun j => d (g j) (s j)).prod

def Pn (x d : I → S → 𝒰) {k : ℕ} (r g : Fin k → I) : 𝒰 :=
  ∑ s : Fin k → S, xw x r s * dw d g s

def Eop (x d : I → S → 𝒰) (a b : I) : 𝒰 := ∑ t : S, x a t * d b t

def Lw (x d : I → S → 𝒰) {k : ℕ} (r g : Fin k → I) : 𝒰 :=
  (List.ofFn fun j : Fin k =>
    Eop x d (r j) (g j) + if r j = g j then ((k : 𝒰) - 1 - ((j : ℕ) : 𝒰)) else 0).prod

end Abs

def CapAbsMain : Prop :=
  ∀ (𝒰 : Type) [Ring 𝒰] (I S : Type) [DecidableEq I] [Fintype S] [DecidableEq S]
    (x d : I → S → 𝒰), (∀ a s b t, x a s * x b t = x b t * x a s) →
    (∀ a s b t, d b t * x a s = x a s * d b t + if a = b ∧ s = t then 1 else 0) →
    ∀ (k : ℕ) (r g : Fin k → I),
      ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        (Lw x d (fun j => r (σ j)) g - Pn x d (fun j => r (σ j)) g) = 0

def xo (N : ℕ) (a s : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  LinearMap.mulLeft ℚ (X (a, s))

def dop (N : ℕ) (b s : Fin N) : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
  (pderiv (b, s) : Derivation ℚ _ _).toLinearMap

def CapSquare : Prop :=
  ∀ N : ℕ, LinearMap.mulLeft ℚ (detX N) * detD N =
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • Pn (xo N) (dop N) (fun j => σ j) id

def CapLeft : Prop :=
  ∀ N : ℕ, Formalism.CohomologicalDescent.HeightDescentMinors.capelli (polE N) (algebraMap ℚ _ ((N : ℚ) - 1)) =
    ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • Lw (xo N) (dop N) (fun j => σ j) id

def CapRel : Prop :=
  ∀ N : ℕ, (∀ a s b t, xo N a s * xo N b t = xo N b t * xo N a s) ∧
    (∀ a s b t, dop N b t * xo N a s = xo N a s * dop N b t + if a = b ∧ s = t then 1 else 0)

theorem detDetId_of (hA : CapAbsMain) (hS : CapSquare) (hL : CapLeft) (hR : CapRel) :
    DetDetId := by
  intro N
  obtain ⟨h1, h2⟩ := hR N
  have h := hA (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) (Fin N) (Fin N) (xo N) (dop N)
    h1 h2 N id id
  simp only [id_eq, smul_sub, Finset.sum_sub_distrib] at h
  rw [hS N, hL N]
  exact (sub_eq_zero.1 h).symm

end PI.HookSteps.Cap
end
end
