module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.DensitySumsAndDomination
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColDef
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXNum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXPH
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSeg
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IoDChain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem ycond_congr {K : Type} [CommRing K] {N r : ℕ} [NeZero r] {LL LL' : ChainLetters N} (h : LL.vec = LL'.vec) (j : ℕ)
    (M : WithTop ℤ) : YCond K (r := r) LL j M = YCond K (r := r) LL' j M := by
  simp only [YCond, chWt, chStable, h]

section E

variable {s r : ℕ}

theorem chW_ne_chE (i i' : Fin s) : chW i ≠ chE i' := by
  simp only [chW, chE, ne_eq, Fin.mk.injEq]
  omega

theorem chW_ne_chU (i : Fin s) : chW i ≠ chU s := by
  simp only [chW, chU, ne_eq, Fin.mk.injEq]
  have := i.2
  omega

theorem chE_ne_chU (i : Fin s) : chE i ≠ chU s := by
  simp only [chE, chU, ne_eq, Fin.mk.injEq]
  have := i.2
  omega

theorem chW_inj {i i' : Fin s} (h : chW i = chW i') : i = i' := by
  simp only [chW, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

theorem chE_inj {i i' : Fin s} (h : chE i = chE i') : i = i' := by
  simp only [chE, Fin.mk.injEq] at h
  exact Fin.ext (by omega)

def eCh (a0 : Fin (2 * s + 1)) : Fin (2 * s + 1) → ℕ := fun a => if a = a0 then 1 else 0

def dEps (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) : Fin (2 * s + 1) → ℕ :=
  (∑ i, ∑ c, (ez i c • eCh (chW i) + ey i c • eCh (chE i))) + ∑ c, ax c • eCh (chU s)

theorem mEps_pol (K : Type) [CommRing K] [Nontrivial K] (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps K ez ey ax ∈ Pol K r (dEps ez ey ax) := by
  classical
  unfold mEps dEps
  refine hom_Pol_mul K (pol_prod' _ _ _ fun i _ => pol_prod' _ _ _ fun c _ => ?_) (pol_prod' _ _ _ fun c _ => ?_)
  · exact hom_Pol_mul K (pol_pow' (pol_X' (chW i) c) _) (pol_pow' (pol_X' (chE i) c) _)
  · exact pol_pow' (pol_X' (chU s) c) _

theorem dEps_chW_eq_sum (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) (i : Fin s) : dEps ez ey ax (chW i) = ∑ c, ez i c := by
  have hWW : ∀ c, chW i = chW c ↔ i = c := fun c => ⟨chW_inj, fun h => h ▸ rfl⟩
  simp only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hWW, chW_ne_chE i,
    chW_ne_chU i, if_false, mul_zero, add_zero, Finset.sum_const_zero, mul_ite, mul_one]
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm))
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem dEps_E (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) (i : Fin s) : dEps ez ey ax (chE i) = ∑ c, ey i c := by
  have hEE : ∀ c, chE i = chE c ↔ i = c := fun c => ⟨chE_inj, fun h => h ▸ rfl⟩
  have hEW : ∀ c, chE i = chW c ↔ False := fun c => ⟨fun h => chW_ne_chE c i h.symm, False.elim⟩
  simp only [dEps, eCh, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hEE, hEW,
    chE_ne_chU i, if_false, mul_zero, add_zero, zero_add, Finset.sum_const_zero, mul_ite, mul_one]
  rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun c _ => if_neg (fun h => hb h.symm))
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem dEps_U (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) : dEps ez ey ax (chU s) = ∑ c, ax c := by
  have hUW : ∀ c, chU s = chW c ↔ False := fun c => ⟨fun h => chW_ne_chU c h.symm, False.elim⟩
  have hUE : ∀ c, chU s = chE c ↔ False := fun c => ⟨fun h => chE_ne_chU c h.symm, False.elim⟩
  simp [dEps, eCh, hUW, hUE]

theorem mEps_int {O : Type} [CommRing O] [IsDomain O] (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps (KK O) ez ey ax ∈ IntPol O (Fin (2 * s + 1) × Fin r) :=
  ⟨mEps O ez ey ax, by simp [mEps]⟩

variable {K : Type} [Field K] [CharZero K] [NeZero r]

theorem ycond_mEps (LL : ChainLetters (2 * s + 1)) (J : ℕ) (hE : ∀ i : Fin s, LL.vec (chE i) = false)
    (ez ey : Fin s → Fin r → ℕ) (ax : Fin r → ℕ) :
    mEps K ez ey ax ∈ YCond K (r := r) LL J
      (((∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) + ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  unfold mEps
  rw [WithTop.coe_add]
  refine ycond_mul LL J _ _ (ycond_prod LL J _ _ _ fun i _ => ?_) ?_
  · have h1 := ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ez i c : ℤ) * (vWt LL J (chW i) : ℤ))
      (fun c => X (chW i, c) ^ ez i c * X (chE i, c) ^ ey i c) (fun c _ => by
        have a1 := ycond_pow LL J _ (ycond_X (K := K) LL J (chW i) c) (ez i c)
        have a2 := ycond_pow LL J _ (ycond_X (K := K) LL J (chE i) c) (ey i c)
        have hv : vWt LL J (chE i) = 0 := by unfold vWt; rw [if_neg]; rw [hE i]; simp
        rw [hv] at a2
        have := ycond_mul LL J _ _ a1 a2
        rw [← WithTop.coe_add] at this
        simpa using this)
    rw [← Finset.sum_mul] at h1
    rw [Nat.cast_sum]
    exact h1
  · have h1 := ycond_prod (K := K) LL J Finset.univ (fun c : Fin r => (ax c : ℤ) * (vWt LL J (chU s) : ℤ))
      (fun c => X (chU s, c) ^ ax c) (fun c _ => ycond_pow LL J _ (ycond_X (K := K) LL J (chU s) c) (ax c))
    rw [← Finset.sum_mul] at h1
    rw [Nat.cast_sum]
    exact h1

theorem ycond_pairs (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) (hW : ∀ i : Fin s, LL.vec (chW i) = true)
    (hE : ∀ i : Fin s, LL.vec (chE i) = false) (k : Fin S.t → ℕ) :
    ∏ l, pairU K r S l ^ k l ∈ YCond K (r := r) LL J
      ((∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) : ℤ) : WithTop ℤ) :=
  ycond_prod LL J _ _ _ fun l _ => ycond_pow LL J _ (ycond_pair LL J _ _ (hW _) (hE _)) (k l)

theorem pWt_sum_le (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) :
    (∑ l : Fin S.t, pWt J (chW (uTop S l)) (chE (uTop S l))) + vWt LL J (chU s) ≤ 1 := by
  have hu : ∀ l : Fin S.t, ((uTop S l : Fin s) : ℕ) = S.sigma + l := fun l => rfl
  have hlt : ∀ l : Fin S.t, S.sigma + (l : ℕ) < s := fun l => by rw [← hu]; exact (uTop S l).2
  by_cases hJ : ∃ l : Fin S.t, J = 2 * (S.sigma + (l : ℕ)) + 1
  · obtain ⟨l0, hl0⟩ := hJ
    have hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 1 := by
      rw [Finset.sum_eq_single l0]
      · simp only [pWt, chW, chE, hu]
        rw [if_pos]
        constructor <;> omega
      · intro l _ hl
        simp only [pWt, chW, chE, hu]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hl
        exact Fin.ext (by omega)
      · intro h
        exact absurd (Finset.mem_univ l0) h
    have hv : vWt LL J (chU s) = 0 := by
      simp only [vWt, chU]
      have := hlt l0
      apply ite_eq_right_iff.mpr
      intro h
      exact absurd h.2 (by omega)
    omega
  · have hsum : ∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      simp only [pWt, chW, chE, hu]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hJ ⟨l, by omega⟩
    have hv : vWt LL J (chU s) ≤ 1 := by
      unfold vWt
      split_ifs <;> omega
    omega

theorem rowInc_le (S : SegData s) (LL : ChainLetters (2 * s + 1)) (J : ℕ) (ez : Fin s → Fin r → ℕ) (ax : Fin r → ℕ)
    (k : Fin S.t → ℕ) (Qe : ℕ) (h1 : ∀ i, ∑ c, ez i c ≤ Qe) (h2 : ∑ c, ax c ≤ Qe) (h3 : ∀ l, k l ≤ Qe) :
    ((∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) + ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ)) +
      ∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) ≤ ((s : ℤ) + 1) * Qe := by
  have hv : ∀ a, (vWt LL J a : ℤ) ≤ 1 := fun a => by
    unfold vWt
    split_ifs <;> simp
  have hA : (∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) ≤ (s : ℤ) * Qe := by
    calc (∑ i, ((∑ c, ez i c : ℕ) : ℤ) * (vWt LL J (chW i) : ℤ)) ≤ ∑ _i : Fin s, (Qe : ℤ) :=
          Finset.sum_le_sum fun i _ => by
            have e1 : ((∑ c, ez i c : ℕ) : ℤ) ≤ Qe := by exact_mod_cast h1 i
            have e2 := hv (chW i)
            have e3 : (0 : ℤ) ≤ ((∑ c, ez i c : ℕ) : ℤ) := Nat.cast_nonneg _
            have e4 : (0 : ℤ) ≤ (vWt LL J (chW i) : ℤ) := Nat.cast_nonneg _
            nlinarith
      _ = (s : ℤ) * Qe := by simp
  have hpw := pWt_sum_le S LL J
  have e3 : ((∑ l, pWt J (chW (uTop S l)) (chE (uTop S l)) : ℕ) : ℤ) + (vWt LL J (chU s) : ℤ) ≤ 1 := by
    exact_mod_cast hpw
  push_cast at e3
  have eB : ((∑ c, ax c : ℕ) : ℤ) * (vWt LL J (chU s) : ℤ) ≤ (Qe : ℤ) * (vWt LL J (chU s) : ℤ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast h2) (Nat.cast_nonneg _)
  have eC : ∑ l, (k l : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) ≤
      ∑ l, (Qe : ℤ) * (pWt J (chW (uTop S l)) (chE (uTop S l)) : ℤ) :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (by exact_mod_cast h3 l) (Nat.cast_nonneg _)
  rw [← Finset.mul_sum] at eC
  have eQ := mul_le_mul_of_nonneg_left e3 (Nat.cast_nonneg Qe : (0 : ℤ) ≤ Qe)
  nlinarith

end E

def capIdx {s : ℕ} (S : SegData s) (k : Fin (S.t + 1)) : ℕ := if h : (k : ℕ) < S.t then (uTop S ⟨k, h⟩ : ℕ) else s

theorem thr_eq {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (mu : ℝ) (b : SegBlock s r) (k : Fin (S.t + 1)) :
    (blockData p S aTop aPlus mu b).T.thr k = ((⌊((cap p S b (capIdx S k) : ℤ) : ℝ) - mu⌋ : ℤ) : WithTop ℤ) := by
  show (segmentCapacities p S b k).map (fun x : ℤ => ⌊(x : ℝ) - mu⌋) = _
  unfold segmentCapacities capIdx
  split_ifs with h <;> rfl

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col Formalism.MainNotions.ColumnSystems.Pf.ColF Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

theorem col_lamS_vec {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X} (L : LvDat C0 CE1 CE2 mu X β)
    (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1)) : (lamS X j a.succ).2 = (L.LL j).vec a := by
  show _ = decide ((a : ℕ) % 2 = 0)
  by_cases h : (a : ℕ) < 2 * segS X.TT j
  · rw [lamS_succ_lt X j a h]
  · rw [lamS_succ_ge X j a h]
    have : (a : ℕ) = 2 * segS X.TT j := by have := a.2; omega
    simp [this]

theorem column_kappa_nonneg (X : Loc) : 0 ≤ ka1 X := by
  unfold ka1 Loc.k Loc.Q
  positivity

theorem colsAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hNum : ColumnNumericsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hS hD hH hC mm hmm n hn1 hnc β hβ L j y hy
  obtain ⟨hnum1, hnum2⟩ := hNum X hD hH hC mm hmm n hn1 hnc j (β j) (hβ j)
  have h2 : 2 ≤ numSeg X.TT := hH.1.2.2.2.1
  have hG : segG X.TT j ≤ X.G' := (hH.1.2.2.2.2.1 j).1
  have hs : segS X.TT j ≤ X.N1 := (hH.1.2.2.2.2.1 j).2
  have hN : 2 * X.N1 + 2 ≤ X.m := hH.1.2.2.2.2.2.2.1
  have hm : 2 * segS X.TT j + 1 < X.m := by omega
  have hn' : 1 ≤ X.n' := by have := hD.2.2.1; omega
  have hp : 0 < X.p := hD.1.pos
  have h := ph_seg L j y hy (hβ j) hnum1 hnum2 hm
  have hvec := col_lamS_vec L j
  have hmu : 0 ≤ mm + (n : ℝ) * ka1 X := by
    have h1 : 0 ≤ mm := by
      rcases hmm with h | h
      · rw [h]
      · rw [h]; positivity
    have h3 := column_kappa_nonneg X
    positivity
  exact ⟨{
    ι := ↥(colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
    fin := inferInstance
    Kc := fun c => Kcol (KK O) y.1.1.mu c.1 (2 * segS X.TT j + 1) (y.1.2 c.1)
    dK := fun c => dKS X j y.1.1.mu c.1
    pl := fun c => plS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j c.1
    fC := fun c => fCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu O y.1.2 c.1
    oC := fun c => oCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c.1
    dgC := fun c => dgCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c.1
    a0 := (a0Z C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).toNat
    KInt := fun c => colKInt y.1.1.mu c.1 _
    KPol := fun c => colKPol j y.1.1.mu c.1 _
    digit_le_one := fun c i => by unfold dKS; split_ifs <;> omega
    dKsum := fun i => by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu) (fun c => dKS X j y.1.1.mu c i)]
      exact dKsum_seg L j y h i
    Kprod := by
      rw [Finset.prod_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => Kcol (KK O) y.1.1.mu c (2 * segS X.TT j + 1) (y.1.2 c))]
      exact Kprod_seg L j y (KK O)
    facC := fun c => colFac j y.1.1.mu y.1.2 S hS hn' h2 h hvec c.1
    homC := fun c => colHomC j y.1.1.mu h (fun a => (hvec a).symm) c.1 _
    fPol := fun c => colFPol j y.1.1.mu h2 y.1.2 c.1
    polC := fun c => colPolC j y.1.1.mu h c.1 _
    plQ := fun c l => colPlQ j hp h2 hG c.1 l
    dgCQ := fun c l => colDgQ j y.1.1.mu hp h2 hG c.1 l
    dgCY := fun c j' => colDgY j y.1.1.mu c.1 j'
    a0le := by
      have h0 : 0 ≤ a0Z C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j := sub_nonneg.2 hnum1
      rw [Int.toNat_of_nonneg h0]
      unfold a0Z
      rw [sub_add_cancel]
      have h1 : ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ ≤
          ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ)⌋ := Int.floor_le_floor (by linarith)
      rwa [Int.floor_intCast] at h1
    plSum := by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => plS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j c)]
      exact plSum_seg L j y h
    oSum := by
      rw [Finset.sum_coe_sort (colsS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu)
        (fun c => oCS C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j y.1.1.mu c)]
      exact oSum_seg L j y h }⟩

theorem restCols : RestCols :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => colsAt_of h) column_numerics_holds

end Formalism.MainNotions.ColumnSystems.Pf
end
end
