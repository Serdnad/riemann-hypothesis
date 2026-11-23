module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle001
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.HookKeyOrderGeOne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Lemma44IdentityOfRawTail
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DegSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem wh_aeval {K : Type} [CommRing K] {σ τ : Type} (ω : τ → ℕ) (f : σ → τ) (lev : σ → ℕ) (u : MvPolynomial σ K) (n : ℕ)
    (h : IsWeightedHomogeneous (fun v => lev v * ω (f v)) u n) :
    IsWeightedHomogeneous ω (aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u) n := by
  have e : aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) u =
      ∑ μ ∈ u.support, aeval (fun v => (X (f v) : MvPolynomial τ K) ^ lev v) (monomial μ (u.coeff μ)) := by
    conv_lhs => rw [← support_sum_monomial_coeff u]

    rw [map_sum]
  rw [e]
  refine IsWeightedHomogeneous.sum _ _ _ fun μ hμ => ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
  have hw : Finsupp.weight (fun v => lev v * ω (f v)) μ = n := h (mem_support_iff.1 hμ)
  have h1 := IsWeightedHomogeneous.prod μ.support (fun v => ((X (f v) : MvPolynomial τ K) ^ lev v) ^ μ v) _
    (fun v _ => ((isWeightedHomogeneous_X K ω (f v)).pow (lev v)).pow (μ v))
  have h2 := (isWeightedHomogeneous_C ω (u.coeff μ)).mul h1
  refine wh_congr h2 ?_
  rw [zero_add, ← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul]

theorem sum_chain {s : ℕ} (f : Fin (2 * s + 1) → ℕ) :
    ∑ a, f a = ∑ i : Fin s, (f ⟨2 * i.val, by omega⟩ + f ⟨2 * i.val + 1, by omega⟩) + f ⟨2 * s, by omega⟩ := by
  let F : ℕ → ℕ := fun k => if h : k < 2 * s + 1 then f ⟨k, h⟩ else 0
  have e1 : ∑ a, f a = ∑ k ∈ Finset.range (2 * s + 1), F k := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [F]
    rw [dite_eq_left a.2]
  have e2 : ∀ n, ∑ k ∈ Finset.range (2 * n + 1), F k = ∑ i ∈ Finset.range n, (F (2 * i) + F (2 * i + 1)) + F (2 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring
  rw [e1, e2 s, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := i.2
    simp only [F]
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
  · simp only [F]
    rw [dite_eq_left (by omega)]

theorem sum_uTop {s : ℕ} (S : SegData s) (g : Fin s → ℕ) :
    ∑ l : Fin S.t, g (uTop S l) = ∑ i : Fin s, if S.sigma ≤ i.val then g i else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun l => uTop S l) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro l _
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩
  · intro l _ l' _ h
    apply Fin.ext
    have h' : S.sigma + l.val = S.sigma + l'.val := congrArg Fin.val h
    omega
  · intro i hi
    have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    have := i.2
    exact ⟨⟨i.val - S.sigma, by unfold SegData.t; omega⟩, Finset.mem_coe.2 (Finset.mem_univ _),
      Fin.ext (by show S.sigma + (i.val - S.sigma) = i.val; omega)⟩

section Sym

variable (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))

theorem sv_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) = ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) l), !β), 0) := by
  simp only [symVar]
  rw [dite_eq_left (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem sl_Z (l : Fin (X.seg C0 CE1 CE2 j).t) (β : Bool) :
    symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.castSucc l, β)) =
      (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) l) := by
  simp only [symLev]
  rw [dite_eq_left (show ((Fin.castSucc l : Fin _) : ℕ) < _ from l.2)]
  rfl

theorem symbol_variable_last (β : Bool) :
    symVar C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = ((topEnd X j, !β), 0) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_level_last (β : Bool) : symLev X.p C0 CE1 CE2 X j (Sum.inr (Fin.last _, β)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ ((Fin.last (X.seg C0 CE1 CE2 j).t : Fin _) : ℕ) < _; exact lt_irrefl _)]

theorem symbol_variable_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, true), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dite_eq_left (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  have e2 : decide ((2 * i.val) % 2 = 0) = true := by simp
  show ((topOdd X j ⟨(2 * i.val) / 2, _⟩, decide ((2 * i.val) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem symbol_level_lower_letter (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dite_eq_left (hc := by show 2 * i.val < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val) / 2, by omega⟩ : Fin (segS X.TT j)) = i := Fin.ext (by show 2 * i.val / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val) / 2, _⟩ = _
  rw [e1]

theorem sv_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topOdd X j i, false), c.succ) := by
  have hi := i.2
  simp only [symVar]
  rw [dite_eq_left (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  have e2 : decide ((2 * i.val + 1) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]
    omega
  show ((topOdd X j ⟨(2 * i.val + 1) / 2, _⟩, decide ((2 * i.val + 1) % 2 = 0)), c.succ) = _
  rw [e1, e2]

theorem sl_E (i : Fin (segS X.TT j)) (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * i.val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      (X.seg C0 CE1 CE2 j).P X.p i := by
  have hi := i.2
  simp only [symLev]
  rw [dite_eq_left (hc := by show 2 * i.val + 1 < 2 * segS X.TT j; omega)]
  have e1 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin (segS X.TT j)) = i :=
    Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  show (X.seg C0 CE1 CE2 j).P X.p ⟨(2 * i.val + 1) / 2, _⟩ = _
  rw [e1]

theorem sv_U (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) =
      ((topEnd X j, true), c.succ) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]
  show ((topEnd X j, decide (2 * segS X.TT j = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_U (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.castSucc (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)), c)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j < 2 * segS X.TT j; exact lt_irrefl _)]

theorem sv_xi (c : Fin X.m) :
    symVar C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = ((topEnd X j, false), c.succ) := by
  simp only [symVar]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]
  show ((topEnd X j, decide (2 * segS X.TT j + 1 = 2 * segS X.TT j)), c.succ) = _
  simp

theorem sl_xi (c : Fin X.m) :
    symLev X.p C0 CE1 CE2 X j (Sum.inl (Fin.last (2 * segS X.TT j + 1), c)) = 1 := by
  simp only [symLev]
  rw [dite_eq_right (hnc := by show ¬ 2 * segS X.TT j + 1 < 2 * segS X.TT j; omega)]

end Sym

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def topStart (X : Loc) (j : Fin (numSeg X.TT)) : X.TT := ⟨segStart X.TT j, (start_mem X.TT j).1⟩

abbrev RHH (O : Type) [CommRing O] [IsDomain O] (X : Loc) := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)

def kSkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : RHH O X :=
  ∑ a : Fin (X.m + 1), MvPolynomial.X ((topStart X j, true), a) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), a)

def kWkey (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (c : Fin (X.m + 1)) : RHH O X :=
  MvPolynomial.X ((topOdd X j i, true), c) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
    MvPolynomial.X ((topOdd X j i, true), 0) * MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ (segDists X.TT j).get i)

def locC (O : Type) [CommRing O] [IsDomain O] (X : Loc) (c : Fin (X.m + 1)) : RHH O X :=
  ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ segG X.TT j - 1)

def locR (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j0 : Fin (numSeg X.TT)) : RHH O X :=
  MvPolynomial.X ((topStart X j0, true), 0) * ∏ c : Fin X.m, locC O X c.succ

def CoarseMultiplicityBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      (∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1) ∧
      liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
        S.w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
              MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) ∧
      ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
        S.w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
          S.w ^ (X.p ^ (segDists X.TT j).get i - 1) •
            (MvPolynomial.X ((topOdd X j i, true), 0) *
              MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X)

def LocalBoundAtIdentity : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    (∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1) ∧
    ∀ c : Fin X.m, liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        S.w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X)

def AsmRTAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  CoarseMultiplicityBoundAtIdentity → LocalBoundAtIdentity → RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def RestAsmRT : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restRawTail1_of (h3 : CoarseMultiplicityBoundAtIdentity) (h4 : LocalBoundAtIdentity) (hA : RestAsmRT) : RestRawTail1 :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => h h3 h4) hA

section Fac

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

structure IsFac (w : O) (f : RHH O X) (o : ℕ) (sg : RHH O X) : Prop where
  inA : InA f
  ord : ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f o
  sym : InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) (o + 1)
  sgInt : InA sg

theorem isGLW_one' (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF X.p X.n')) := by
  unfold IsGLW
  rw [Matrix.det_one]
  exact isUnit_one

theorem IsFac.mul {w : O} {f f' sg sg' : RHH O X} {o o' : ℕ} (h : IsFac w f o sg) (h' : IsFac w f' o' sg') :
    IsFac w (f * f') (o + o') (sg * sg') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (inA_iff_wj w).2 (inWj_mul ((inA_iff_wj w).1 h.inA) ((inA_iff_wj w).1 h'.inA))
  · exact fun g hg => inWjRg_mul (h.ord g hg) (h'.ord g hg)
  · have e : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (f * f') - (w ^ (o + o')) • (sg * sg') =
        (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) *
            liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' +
          ((w ^ o) • sg) * (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f' - (w ^ o') • sg') := by
      rw [map_mul, pow_add, mul_smul_mul_comm]
      ring
    rw [e]
    have a1 := inWj_mul h.sym (h'.ord 1 (isGLW_one' _))
    have a2 := inWj_mul (wj_smul_pow ((inA_iff_wj w).1 h.sgInt) o) h'.sym
    have e1 : o + 1 + o' = o + o' + 1 := by ring
    have e2 : 0 + o + (o' + 1) = o + o' + 1 := by ring
    rw [e1] at a1
    rw [e2] at a2
    exact (wjSub w (o + o' + 1)).add_mem a1 a2
  · exact (inA_iff_wj w).2 (inWj_mul ((inA_iff_wj w).1 h.sgInt) ((inA_iff_wj w).1 h'.sgInt))

end Fac

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev BV (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :=
  BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t

abbrev bD (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (mm : ℝ) (b : SegBlock (segS X.TT j) X.m) :
    BlockData (2 * segS X.TT j + 1) :=
  blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b

abbrev sszB (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (mm : ℝ)
    (b : SegBlock (segS X.TT j) X.m) : Submodule O (MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) :=
  (bD C0 CE1 CE2 X j mm b).SSZ O (r := X.m)

def baseExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ :=
  (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
    (Finsupp.single ((topOdd X j i, true), c) (b.rz i c) + Finsupp.single ((topOdd X j i, false), c) (b.ry i c))) +
  ∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) +
      Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i)
  else 0

def ioExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ :=
  baseExp C0 CE1 CE2 X j b +
    μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)

def gOp {O : Type} [CommRing O] [IsDomain O] {σ : Type} (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O)
    (u : MvPolynomial σ (KK O)) : MvPolynomial σ (KK O) :=
  ∑ ν ∈ T, q ν • (monomial ν (1 : KK O) * divDer ν u)

def gEv {O : Type} [CommRing O] {σ : Type} (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O) (μ : σ →₀ ℕ) : O :=
  ∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : O)

def Balanced {s : ℕ} (r : ℕ) (S : SegData s) (ω : BVar (2 * s + 1) r S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ) : Prop :=
  (∀ a c, ω (Sum.inl (a, c)) = ωL a) ∧
  (∀ l : Fin S.t, ω (Sum.inr (Fin.castSucc l, false)) + ω (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) ∧
  ω (Sum.inr (Fin.last S.t, false)) + ω (Sum.inr (Fin.last S.t, true)) =
      ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)

def HomExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) : Prop :=
  ∀ (ω : BV C0 CE1 CE2 X j → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ), Balanced X.m (X.seg C0 CE1 CE2 j) ω ωL →
    ∑ v, μ v * ω v = OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω ωL

def letterOf (X : Loc) (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1 + 1)) : X.TT × Bool :=
  if h : (a : ℕ) < 2 * segS X.TT j then (topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0))
  else (topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j))


open Classical in
def lamW (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (x : X.TT × Bool) : BV C0 CE1 CE2 X j → ℕ :=
  fun v => if (symVar C0 CE1 CE2 X j v).1 = x then 1 else 0

open Classical in
def lamL (X : Loc) (j : Fin (numSeg X.TT)) (x : X.TT × Bool) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if letterOf X j a = x then 1 else 0

def cdeg (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) : ℕ :=
  OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (lamW C0 CE1 CE2 X j x) (lamL X j x)

def Nblk (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) * specConst X.p (X.seg C0 CE1 CE2 j) b

def IsOddVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) : BV C0 CE1 CE2 X j → Prop
  | Sum.inl (a, _) => (a : ℕ) < 2 * segS X.TT j
  | Sum.inr (l, _) => (l : ℕ) < (X.seg C0 CE1 CE2 j).t

def IoFockAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) (K : Type) [Field K], 0 < X.p → ∀ (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u u' : MvPolynomial (BV C0 CE1 CE2 X j) K),
    fock (ioBlock K X.p C0 CE1 CE2 X j b u) (ioBlock K X.p C0 CE1 CE2 X j b u') =
      ∑ μ ∈ u.support, u.coeff μ * u'.coeff μ * (expFact (ioExp C0 CE1 CE2 X j b μ) : K)

def EigAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O)
    (u : MvPolynomial σ (KK O)) (μ : σ →₀ ℕ),
    (gOp T q u).coeff μ = algebraMap O (KK O) (gEv T q μ) * u.coeff μ

def HomAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b → ∀ (mm : ℝ),
      ∀ u ∈ Submodule.span (KK O) (sszB O C0 CE1 CE2 X j mm b : Set (MvPolynomial (BV C0 CE1 CE2 X j) (KK O))),
      ∀ μ ∈ u.support, HomExp C0 CE1 CE2 X j b μ

def DvdAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
    Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    ∀ μ, HomExp C0 CE1 CE2 X j b μ → expFact μ * specConst X.p (X.seg C0 CE1 CE2 j) b ∣ Nblk C0 CE1 CE2 X j b

def SatAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N r : ℕ) [NeZero r] (D : BlockData N),
    ∀ x ∈ Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
        Set (MvPolynomial (BVar N r D.T.t) (KK O))),
      x ∈ IntPol O (BVar N r D.T.t) → x ∈ D.SSZ O (r := r)

def GThetaAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero (KK O)] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
    Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    ∀ (c : ℕ) (T : Finset (BV C0 CE1 CE2 X j →₀ ℕ)) (q : (BV C0 CE1 CE2 X j →₀ ℕ) → O),
      (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * c ∧ ∀ v ∈ ν.support, IsOddVar C0 CE1 CE2 X j v) →
      ∀ (mm : ℝ), ∀ u ∈ sszB O C0 CE1 CE2 X j mm b, gOp T q u ∈ sszB O C0 CE1 CE2 X j (mm - 4 * (c : ℝ)) b

def FactAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O),
    Irreducible w → w ^ 2 = (X.p : O) → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∃ (κ : O) (T : Finset (BV C0 CE1 CE2 X j →₀ ℕ)) (q : (BV C0 CE1 CE2 X j →₀ ℕ) → O),
        κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * X.c ∧ ∀ v ∈ ν.support, IsOddVar C0 CE1 CE2 X j v) ∧
        ∀ μ, HomExp C0 CE1 CE2 X j b μ → ∃ h : O,
          zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) *
              (expFact (ioExp C0 CE1 CE2 X j b μ) : KK O) * algebraMap O (KK O) (gEv T q μ) =
            algebraMap O (KK O) κ * ((expFact μ : KK O) * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O)) *
              algebraMap O (KK O) (1 + w ^ X.c * h)

end Formalism.MainNotions.ColumnSystems.Pf
end
end
