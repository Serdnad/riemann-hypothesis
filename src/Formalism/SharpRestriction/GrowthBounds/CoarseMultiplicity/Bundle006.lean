module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle005
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem symVar_inj (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    Function.Injective (symVar C0 CE1 CE2 X j) := by
  rintro (⟨a, c⟩ | ⟨l, b⟩) (⟨a', c'⟩ | ⟨l', b'⟩) h
  · simp only [symVar] at h
    have ha2 := a.2
    have ha2' := a'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, e3⟩ := h
      have e1' : (a : ℕ) / 2 = (a' : ℕ) / 2 := congrArg Fin.val (topOdd_inj X j e1)
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, e3⟩ := h
      have e2' := decide_eq_decide.1 e2
      have hc : c = c' := Fin.succ_injective _ e3
      have ha : a = a' := Fin.ext (by omega)
      rw [ha, hc]
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2
  · exfalso
    simp only [symVar] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> exact Fin.succ_ne_zero _ h.2.symm
  · simp only [symVar] at h
    have hl2 := l.2
    have hl2' := l'.2
    split_ifs at h with h1 h2 h2
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, e2⟩, -⟩ := h
      have e1' : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (X.seg C0 CE1 CE2 j).sigma + (l' : ℕ) :=
        congrArg Fin.val (topOdd_inj X j e1)
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1 (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.1.symm (topOdd_ne_end X j _)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨⟨-, e2⟩, -⟩ := h
      have hl : l = l' := Fin.ext (by omega)
      have hb : b = b' := by simpa using e2
      rw [hl, hb]

theorem symLev_pos (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (v : BV C0 CE1 CE2 X j) :
    0 < symLev X.p C0 CE1 CE2 X j v := by
  rcases v with ⟨a, c⟩ | ⟨l, b⟩
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos
  · simp only [symLev]
    split_ifs
    · exact pow_pos hp _
    · exact one_pos

theorem coarse_eval (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (v0 : BV C0 CE1 CE2 X j) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      (symVar C0 CE1 CE2 X j v0) = symLev X.p C0 CE1 CE2 X j v0 * μ v0 := by
  classical
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_eq_single v0]
  · simp
  · intro v _ hv
    rw [if_neg fun e => hv (symVar_inj C0 CE1 CE2 X j e)]
  · intro hv
    simp [Finsupp.notMem_support_iff.1 hv]

theorem ioExp_inj (C0 CE1 CE2 : ℝ) (X : Loc) (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    Function.Injective (ioExp C0 CE1 CE2 X j b) := by
  intro μ μ' h
  unfold ioExp at h
  have h' := add_left_cancel h
  ext v0
  have := DFunLike.congr_fun h' (symVar C0 CE1 CE2 X j v0)
  rw [coarse_eval, coarse_eval] at this
  exact Nat.eq_of_mul_eq_mul_left (symLev_pos C0 CE1 CE2 X hp j v0) this

theorem ioBlock_monomial (C0 CE1 CE2 : ℝ) (X : Loc) (K : Type) [Field K] (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (μ : BV C0 CE1 CE2 X j →₀ ℕ) (c : K) :
    ioBlock K X.p C0 CE1 CE2 X j b (monomial μ c) = monomial (ioExp C0 CE1 CE2 X j b μ) c := by
  classical
  have hd : digitMon K C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
      (Finsupp.single ((topOdd X j i, true), c) (b.rz i c) + Finsupp.single ((topOdd X j i, false), c) (b.ry i c))) 1 := by
    unfold digitMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  have hs : sTopMon K X.p C0 CE1 CE2 X j b = monomial (∑ i : Fin (segS X.TT j),
      if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
            ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) +
          Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i)
      else 0) 1 := by
    unfold sTopMon
    rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
    · simp
  have ha : aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
      MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v) (monomial μ c) =
      monomial (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) c := by
    rw [aeval_monomial, monomial_finsupp_sum_index]
    congr 1
    refine Finsupp.prod_congr fun v _ => ?_
    rw [← pow_mul, X_pow_eq_monomial]
  unfold ioBlock ioExp baseExp
  rw [hd, hs, ha, monomial_mul, monomial_mul, one_mul, one_mul]

theorem ioFockAt : IoFockAt := by
  intro C0 CE1 CE2 X K _ hp j b u u'
  let f : MvPolynomial (BV C0 CE1 CE2 X j) K →ₗ[K] MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
    (LinearMap.mulLeft K (digitMon K C0 CE1 CE2 X j b * sTopMon K X.p C0 CE1 CE2 X j b)).comp
      (aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) :
        MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^ symLev X.p C0 CE1 CE2 X j v)).toLinearMap
  exact fock_monoMap f (ioExp C0 CE1 CE2 X j b) (ioExp_inj C0 CE1 CE2 X hp j b)
    (fun μ c => ioBlock_monomial C0 CE1 CE2 X K j b μ c) u u'

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  ∑ b : Fin (X.m + 1), C (dW O w (hhLetters X.TT) 1 (topStart X j, true) b) * MvPolynomial.X ((topStart X j, true), b) *
    C (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ b a))

def locExpr (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j0 : Fin (numSeg X.TT)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  xvL X O w g j0 0 * ∏ c : Fin X.m, (∏ j : Fin (numSeg X.TT), xvL X O w g j 0 ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), xvL X O w g j c.succ ^ (X.p ^ segG X.TT j - 1))

theorem liftSubst_start (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (MvPolynomial.X ((topStart X j, true), a)) =
      MvPolynomial.map (algebraMap O (KK O)) (xvL X O w g j a) := by
  rw [liftSubst_X_vec X.p X.n' O w (hhLetters X.TT) 1 g hg (topStart X j, true) a rfl]

  simp only [xvL, map_sum, map_mul, map_C, map_X, sigMat_apply]
  rfl

theorem locR_lift (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j0 : Fin (numSeg X.TT)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (locR O X j0) =
      MvPolynomial.map (algebraMap O (KK O)) (locExpr X O w g j0) := by
  unfold locR locC locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, liftSubst_start X O w g hg]

def LocalDivisibilityBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      (C S.w : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O) ∣ locExpr X O S.w g j0

theorem loc4Ord_of (h : LocalDivisibilityBound) : LocalOrderBound := by
  intro X _ O _ _ _ _ S hS hD h2 j0 g hg hpl
  obtain ⟨Q, hQ⟩ := h X O S hS hD h2 j0 g hg hpl
  unfold InWjRg
  rw [locR_lift X O S.w g hg j0, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Cth

variable {K : Type} [Field K] {σ : Type}

def cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  monomial (Finsupp.single v n) (1 : K) * divDer (Finsupp.single v n) F

theorem coeff_cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (cth v n F) μ = AddMonoidAlgebra.coeff F μ * (((μ v).choose n : ℕ) : K) := by
  unfold cth
  rw [eig_one]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Finsupp.prod_single_index (by simp)]

theorem cth_add (v : σ) (n : ℕ) (F G : MvPolynomial σ K) : cth v n (F + G) = cth v n F + cth v n G := by
  ext μ
  simp only [coeff_cth, MvPolynomial.coeff_add, add_mul]

theorem cth_smul (v : σ) (n : ℕ) (c : K) (F : MvPolynomial σ K) : cth v n (c • F) = c • cth v n F := by
  ext μ
  simp only [coeff_cth, MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

def cthL (v : σ) (n : ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K where
  toFun := cth v n
  map_add' := cth_add v n
  map_smul' := cth_smul v n

theorem cth_monomial (v : σ) (n : ℕ) (e : σ →₀ ℕ) (c : K) :
    cth v n (monomial e c) = monomial e (c * (((e v).choose n : ℕ) : K)) := by
  classical
  ext μ
  rw [coeff_cth, coeff_monomial, coeff_monomial]
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

theorem cth_zero (v : σ) (F : MvPolynomial σ K) : cth v 0 F = F := by
  ext μ
  simp [coeff_cth]

theorem cth_mul (v : σ) (n : ℕ) (F G : MvPolynomial σ K) :
    cth v n (F * G) = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, cth v ab.1 F * cth v ab.2 G := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add F F' hF hF' =>
    rw [add_mul, cth_add, hF, hF', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, add_mul]
  | monomial e c =>
    induction G using MvPolynomial.induction_on' with
    | add G G' hG hG' =>
      rw [mul_add, cth_add, hG, hG', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, mul_add]
    | monomial e' c' =>

      rw [monomial_mul, cth_monomial, Finsupp.add_apply, Nat.add_choose_eq, Nat.cast_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [cth_monomial, cth_monomial, monomial_mul]
      congr 1
      push_cast
      ring

theorem cth_free (v : σ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) {n : ℕ} (hn : n ≠ 0) :
    cth v n F = 0 := by
  ext μ
  rw [coeff_cth]
  change F.coeff μ * (((μ v).choose n : ℕ) : K) = 0
  by_cases h : μ ∈ F.support
  · rw [hF μ h, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hn)]
    simp
  · rw [notMem_support_iff.1 h, zero_mul]

theorem cth_mul_free (v : σ) (n : ℕ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) (G : MvPolynomial σ K) :
    cth v n (F * G) = F * cth v n G := by
  classical
  rw [cth_mul, Finset.sum_eq_single (0, n)]
  · rw [cth_zero]
  · rintro ⟨a, b⟩ hab hne
    have ha : a ≠ 0 := by
      rintro rfl
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      simp only [zero_add] at hab
      exact hne (by rw [hab])
    rw [cth_free v hF ha, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

theorem cth_pow (v : σ) {E m : MvPolynomial σ K} (h1 : cth v 1 E = m) (h2 : ∀ a, 2 ≤ a → cth v a E = 0) (j l : ℕ) :
    cth v l (E ^ j) = ((j.choose l : ℕ) : K) • (E ^ (j - l) * m ^ l) := by
  classical
  induction j generalizing l with
  | zero =>
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero]
    · rw [pow_zero, Nat.choose_eq_zero_of_lt hl, Nat.cast_zero, zero_smul]
      refine cth_free v ?_ hl.ne'
      intro μ hμ
      have : μ = 0 := by
        by_contra hne
        rw [mem_support_iff, coeff_one, if_neg (Ne.symm hne)] at hμ
        exact hμ rfl
      rw [this]; rfl
  | succ j ih =>
    rw [pow_succ, cth_mul]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero, pow_succ]
    · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
      have hsub : ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal (l' + 1), ab ≠ (l' + 1, 0) → ab ≠ (l', 1) →
          cth v ab.1 (E ^ j) * cth v ab.2 E = 0 := by
        rintro ⟨a, b⟩ hab hn1 hn2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
        simp only at hab
        have hb : 2 ≤ b := by
          by_contra hb
          have : b = 0 ∨ b = 1 := by omega
          rcases this with rfl | rfl
          · exact hn1 (by simp at hab; rw [hab])
          · exact hn2 (by have : a = l' := by omega
                          rw [this])
        rw [h2 b hb, mul_zero]
      have hne : ((l' + 1, 0) : ℕ × ℕ) ≠ (l', 1) := by simp
      rw [← Finset.sum_subset (s₁ := {(l' + 1, 0), (l', 1)})
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [Finset.HasAntidiagonal.mem_antidiagonal])
        (by
          intro x hx hx'
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
          exact hsub x hx hx'.1 hx'.2),
        Finset.sum_pair hne]
      simp only
      rw [ih, ih, cth_zero, h1, Nat.choose_succ_succ' j l']
      by_cases hlj : l' + 1 ≤ j
      · have e1 : j + 1 - (l' + 1) = (j - (l' + 1)) + 1 := by omega
        have e2 : j - l' = (j - (l' + 1)) + 1 := by omega
        rw [e1, e2]
        push_cast
        simp only [smul_eq_C_mul, pow_succ, map_add (f := _)]
        ring
      · have e0 : j.choose (l' + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have e1 : j + 1 - (l' + 1) = j - l' := by omega
        rw [e0, e1]
        simp only [Nat.cast_zero, zero_smul, zero_mul, zero_add, add_zero, smul_eq_C_mul, pow_succ]
        ring

end Cth

end Formalism.MainNotions.ColumnSystems.Pf
end
end
