module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
public import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.LvlDef
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle002
public import Formalism.MahlerMeasure.MahlerMeasureProofs.SSDirect
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ValFactSumLe
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.Bundle001
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.SmulMemOfNorm
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle009
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle004
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality Formalism.MainNotions.G.SymmetricFormBlocks
open scoped Nat

section Lat

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem Ljj_le (S : Submodule ℤ_[p] (MvPolynomial (M.BVar N r G.T.t) ℚ_[p])) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (h : ∀ y ∈ M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∀ g ∈ M.XiPolZ p N r G.T.t (G.B - jp),
      rename (M.chainEmb N r G.T.t) y * g ∈ S) : Ljj p (r := r) G j jp ≤ S := by
  unfold Ljj
  rw [Submodule.span_le]
  rintro x ⟨y, hy, g, hg, rfl⟩
  exact h y hy g hg

theorem Ljj_int (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) : Bnd 1 v := by
  have h := Ljj_le p G (M.IntPol p (M.BVar N r G.T.t)) j jp
    (fun y hy g hg => M.intPol_mul' (M.intPol_rename' _ hy.2.2) hg.2) hv
  exact (Formalism.InvariantFactorPaths.KP.LL.intPol_iff_bnd v).1 h

def dJ (j : Fin G.T.t → ℕ) (jp : ℕ) (a : Fin (N + 1)) : ℕ :=
  chDeg (G.lettersAt j jp) a + (if Fin.last N = a then G.B - jp else 0)

theorem Ljj_hom (a : Fin (N + 1)) (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) : IsWeightedHomogeneous (wL (r := r) G a) v (dJ G j jp a) := by
  have key : Ljj p (r := r) G j jp ≤
      (weightedHomogeneousSubmodule ℚ_[p] (wL (r := r) G a) (dJ G j jp a)).restrictScalars ℤ_[p] := by
    refine Ljj_le p G _ j jp ?_
    intro y hy g hg
    exact (hom_chain p G a _ y hy.2.1).mul (hom_xi p G a _ g hg)
  exact key hv

theorem prod_dJ (j : Fin G.T.t → ℕ) (jp : ℕ) : ∏ a, (dJ G j jp a)! = degFact G j jp := by
  unfold dJ degFact chDeg
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro a0 _
    simp [Fin.castSucc_inj, (Fin.castSucc_lt_last a0).ne']
  · simp [Fin.castSucc_ne_last]

theorem lettersAt_le (j : Fin G.T.t → ℕ) (jp : ℕ) (a0 : Fin N) : (G.lettersAt j jp).deg a0 ≤ G.LL.deg a0 := by
  unfold M.BlockData.lettersAt
  exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem dJ_le (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (a : Fin (N + 1)) : dJ G j jp a ≤ 2 * A := by
  unfold dJ chDeg
  by_cases ha : Fin.last N = a
  · subst ha
    simp [Fin.castSucc_ne_last]
    omega
  · rw [if_neg ha]
    obtain ⟨a0, rfl⟩ : ∃ a0, Fin.castSucc a0 = a := Fin.exists_castSucc_eq.2 (Ne.symm ha)
    have h1 := lettersAt_le G j jp a0
    have h2 := hdeg a0
    simp [Fin.castSucc_inj]
    omega

theorem log_le_lgN (A x : ℕ) (hx : x ≤ 8 * A + r) : Nat.log p x + 1 ≤ lgN p A r := by
  unfold lgN
  have h1 := Nat.log_mono_right (b := p) hx
  omega

theorem Ljj_val (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A) (j : Fin G.T.t → ℕ) (jp : ℕ)
    (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hv : v ∈ Ljj p (r := r) G j jp) :
    ∀ m ∈ v.support, padicValNat p (degFact G j jp) ≤
      padicValNat p (m.prod fun _ i => i !) + ((N + 1) * r + (G.T.t + 1) * 2) * lgN p A r := by
  intro m hm
  rw [← prod_dJ G j jp]
  have hw : ∀ a, Finsupp.weight (wL (r := r) G a) m = dJ G j jp a :=
    fun a => Ljj_hom p G a j jp v hv (mem_support_iff.mp hm)
  refine val_letters_le p G m (dJ G j jp) hw (lgN p A r) (fun a => ?_)
  have h1 := dJ_le G A hdeg hBa j jp a
  have h2 := log_le_lgN p (r := r) A (dJ G j jp a) (by omega)
  omega

theorem lettersAt_uPos (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) :
    (G.lettersAt j jp).deg G.uPos = G.LL.deg G.uPos - jp := by
  obtain ⟨-, hpos, -, -⟩ := hB
  have hz : (∑ i : Fin G.T.t, if (G.uPos : ℕ) = G.T.pos i ∨ (G.uPos : ℕ) = G.T.pos i + 1 then j i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => if_neg (by have := hpos i; omega)
  change (List.map (fun i : Fin G.T.t => if (G.uPos : ℕ) = G.T.pos i ∨ (G.uPos : ℕ) = G.T.pos i + 1 then j i else 0) (List.finRange G.T.t)).sum = 0 at hz
  unfold M.BlockData.lettersAt
  simp only [hz, ite_true, Nat.sub_zero]

theorem Ljj_biHom (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hv : v ∈ Ljj p (r := r) G j jp) :
    BiHom (fun c => (Sum.inl (Fin.castSucc G.uPos, c) : M.BVar N r G.T.t)) (fun c => M.xiVar N r G.T.t c)
      (G.LL.deg G.uPos - jp) (G.B - jp) v := by
  have h1 := Formalism.InvariantFactorPaths.KP.LL.biHom_plus (p := p) (r := r) (D := G) j jp v hv
  rw [lettersAt_uPos G hB j jp] at h1
  exact h1

end Lat

end Formalism.MainNotions.G.GramWindowAlt

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.MainNotions.G.SymmetricFormBlocks

theorem segG_pos {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : 1 ≤ segG TT j := by
  unfold segG
  split_ifs with h
  · exact (segStart TT j).pos
  · exact Nat.one_le_iff_ne_zero.mpr h

theorem cap_le' {s r p : ℕ} (S : SegData s) (b : SegBlock s r) (B : ℝ) (hB : ∀ i, (S.bTop i : ℝ) ≤ B) (l : ℕ) :
    (cap p S b l : ℝ) ≤ S.A0 p + s * B := by
  unfold cap
  push_cast
  refine add_le_add le_rfl ((Finset.sum_le_card_nsmul _ _ B ?_).trans ?_)
  · intro i _
    have hc : coarseA p S b i ≤ S.bTop i := by
      unfold coarseA
      exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hcR : (coarseA p S b i : ℝ) ≤ B := (Nat.cast_le.mpr hc).trans (hB i)
    have h0 : (0 : ℝ) ≤ B := (Nat.cast_nonneg _).trans (hB i)
    have hoe : (0 : ℝ) ≤ (oEff S b i : ℝ) := Nat.cast_nonneg _
    split_ifs <;> linarith
  · simp

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section Deg

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem first_coefficient_le_div : (((X.S C0 CE1 CE2).A0 X.p : ℤ) : ℝ) ≤ X.L.a / 25 := by
  unfold SegData.A0
  refine (Int.floor_le _).trans ?_
  have hp25 := p25 hS.hF
  have hp1 : 1 ≤ X.p := X.std.1.prime.one_lt.le
  have hQ : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ) := by
    show (X.p : ℝ) ≤ ((X.p ^ segG X.L.TT X.j : ℕ) : ℝ)
    have : X.p ^ 1 ≤ X.p ^ segG X.L.TT X.j := Nat.pow_le_pow_right hp1 (segG_pos _ _)
    rw [pow_one] at this
    exact_mod_cast this
  have hQ25 : (25 : ℝ) ≤ ((X.S C0 CE1 CE2).Qj X.p : ℝ) := hp25.trans hQ
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hE := hS.E0
  have ha : (((X.S C0 CE1 CE2).a : ℕ) : ℝ) = X.L.a := rfl
  rw [ha, div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

private theorem geo_lemma (n : ℕ) (p : ℝ) (hp : 1 < p) (f : Fin n → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∀ i, f i ≤ 1) (hs : ∀ i j : Fin n, i < j → p * f i ≤ f j) : ∑ i, f i ≤ p / (p - 1) := by
  cases n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact div_nonneg (by linarith) (by linarith)
  | succ n =>
    have hA := Fin.sum_univ_castSucc f
    have hB := Fin.sum_univ_succ f
    have hC : ∑ i : Fin n, p * f i.castSucc ≤ ∑ i : Fin n, f i.succ :=
      Finset.sum_le_sum (fun i _ => hs _ _ Fin.castSucc_lt_succ)
    rw [← Finset.mul_sum] at hC
    have hf0 := h0 0
    have hfl := h1 (Fin.last n)
    rw [le_div_iff₀ (by linarith)]
    nlinarith

theorem oplus_le_a (b : SegBlock X.s X.r) (a : Fin X.s → ℕ) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) :
    b.oPlus ≤ X.L.a := by
  have hF := hS.hF
  have hK4 := hK.2.2.2
  unfold Oplus at hK4
  have hcap := cap_le' (p := X.p) (X.S C0 CE1 CE2) b (5 / 2 * X.L.b') hS.bTop X.s
  have hA0 := first_coefficient_le_div hS
  have hm4 : (4 : ℝ) ≤ X.L.m := by exact_mod_cast hF.m4
  have hpg := hF.p_ge
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith
  have hb0 := hF.b0
  have hkb : ((X.L.m : ℝ) + 1) * X.L.b' ≤ X.L.a / 4 := hS.kb
  have hs : 2 * (X.s : ℝ) + 2 ≤ X.L.m := by exact_mod_cast hF.s_le
  have hsb : (X.s : ℝ) * X.L.b' ≤ X.L.a / 8 := by nlinarith
  have hLa0 : 0 ≤ X.L.La C0 := hF.La0
  have hLa4 : 4 * X.L.La C0 < (X.L.m : ℝ) + 1 := hS.La4
  have hc1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hq : 4 / (X.L.p : ℝ) ^ 2 ≤ 4 / 625 := by
    gcongr
    nlinarith
  have hq0 : 0 ≤ 4 / (X.L.p : ℝ) ^ 2 := by positivity
  have hPpos : ∀ i, (0 : ℝ) < (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := fun i => by
    exact_mod_cast twoPow_pos C0 CE1 CE2 X i
  have hg := geo_lemma hS X.s (X.L.p : ℝ) (by linarith)
    (fun i => 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)) (fun i => (one_div_pos.mpr (hPpos i)).le)
    (fun i => by
      have := hS.P1 i
      rw [div_le_one (hPpos i)]
      exact_mod_cast this)
    (fun i j hij => by
      have h1 := P_step (C0 := C0) (CE1 := CE1) (CE2 := CE2) i j hij
      have h1' : (X.L.p : ℝ) * (SegData.P X.p (X.S C0 CE1 CE2) j : ℝ) ≤ (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
        exact_mod_cast h1
      rw [mul_one_div, div_le_div_iff₀ (hPpos i) (hPpos j)]
      linarith)
  have hgeo : (X.L.p : ℝ) / ((X.L.p : ℝ) - 1) ≤ 25 / 24 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hTe : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      = 2 * (X.L.a : ℝ) * ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hT0 : 0 ≤ ∑ i, 1 / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) :=
    Finset.sum_nonneg (fun i _ => (one_div_pos.mpr (hPpos i)).le)
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hT : ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) ≤ 2 * X.L.a * (25 / 24) := by
    rw [hTe]
    exact mul_le_mul_of_nonneg_left (hg.trans hgeo) (by positivity)
  have hT0' : 0 ≤ ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ) := by
    rw [hTe]
    positivity
  have hmemT : ∀ x ∈ evenTops X.L.TT, x ∈ X.L.TT := fun x hx => by
    unfold evenTops at hx
    rw [Finset.mem_sort] at hx
    exact (Finset.mem_filter.mp hx).1
  have hmem : segNext X.L.TT X.j ∈ X.L.TT := by
    unfold segNext
    exact hmemT _ (List.get_mem _ _)
  have hbP : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := hF.bT_le _ hmem
  have hbP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ) := Nat.cast_nonneg _
  have hLb : X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1)
      ≤ 1 / 4 * ((X.S C0 CE1 CE2).bPlus : ℝ) := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hc1 hbP0
  have hcT : (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2)
      * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      ≤ (1 / 4 + 4 / 625) * (2 * X.L.a * (25 / 24)) :=
    mul_le_mul (by linarith) hT hT0' (by norm_num)
  have hK5 : (b.oPlus : ℝ) ≤ ((cap X.p (X.S C0 CE1 CE2) b X.s : ℤ) : ℝ)
      + (X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2)
        * ∑ i, 2 * (X.L.a : ℝ) / (SegData.P X.p (X.S C0 CE1 CE2) i : ℝ)
      + X.L.La C0 * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.L.m : ℝ) + 1) := hK4
  have hfin : (b.oPlus : ℝ) ≤ X.L.a := by nlinarith
  exact_mod_cast hfin

theorem a_mem_win : X.L.a ∈ X.winA := by
  unfold flipOneThree.Inst.winA
  rw [Finset.mem_Icc]
  refine ⟨le_rfl, Nat.le_floor ?_⟩
  have h1 : (0 : ℝ) ≤ (X.L.a : ℝ) / (X.L.k * X.L.Y) := by
    have hk : (0 : ℝ) ≤ X.L.k := by
      show (0 : ℝ) ≤ (X.L.m : ℝ) + 1
      positivity
    have := hS.Y1
    positivity
  linarith [hS.xa0]

end Deg

theorem eps_num (Y D1 κ q h x0l fl E : ℝ) (hY : 1 ≤ Y) (hκ : 0 < κ) (hD : κ ≤ D1) (hq0 : 0 ≤ q) (hq : q ≤ 1 / (2 * Y))
    (hh0 : 0 ≤ h) (hh : h ≤ κ) (hx : x0l ≤ κ) (hfl : fl ≤ D1) (hE : Y * D1 ≤ E) :
    q + (x0l + fl + q * h) / E ≤ 5 / Y := by
  have hD1 : 0 < D1 := lt_of_lt_of_le hκ hD
  have hY0 : 0 < Y := by linarith
  have hYD : 0 < Y * D1 := mul_pos hY0 hD1
  have hE0 : 0 < E := lt_of_lt_of_le hYD hE
  have hq1 : q ≤ 1 := by
    have : 1 / (2 * Y) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hqh : q * h ≤ D1 := by nlinarith [mul_le_mul_of_nonneg_right hq1 hh0]
  have hnum : x0l + fl + q * h ≤ 3 * D1 := by linarith
  have h1 : (x0l + fl + q * h) / E ≤ 3 / Y := by
    rw [div_le_div_iff₀ hE0 hY0]
    nlinarith [mul_le_mul_of_nonneg_right hnum hY0.le]
  have h2 : q ≤ 1 / Y := by
    have : 1 / (2 * Y) ≤ 1 / Y := by
      gcongr
      linarith
    linarith
  have h3 : 1 / Y + 3 / Y ≤ 5 / Y := by
    rw [← add_div]
    gcongr
    norm_num
  linarith

end Formalism.MainNotions.G.GramWindowAlt

end
end
