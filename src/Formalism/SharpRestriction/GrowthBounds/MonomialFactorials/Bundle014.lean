module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LettersExt
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ExponentMatrixFirstDepthEq
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

section Deg

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem window_entry_le_two_mul_a (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (l : Fin X.s) :
    (a l : ℝ) ≤ 2 * X.L.a := by
  have h2 := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT l)).2
  have h3 : (a l : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
  exact (h3.trans (Nat.floor_le hS.hF.win0)).trans hS.hF.win_le

theorem r5 : (5 : ℝ) ≤ (X.r : ℝ) + 1 := by
  have : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hS.hF.m4
  show (5 : ℝ) ≤ (X.L.m : ℝ) + 1
  linarith

theorem b_small : 5 / 2 * X.L.b' ≤ X.L.a / 8 := by
  have h1 := hS.kb
  have h2 := r5 hS
  have hb := hS.hF.b0
  nlinarith

theorem chain_wt (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) ≠ 2 * X.s) :
    ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) * ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) ≤ 2 * X.L.a := by
  have hA : ∀ l, (coarseA X.p (X.S C0 CE1 CE2) b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := fun l =>
    (coarseA_upper hS b l).trans (by have := b_small hS; have : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _; linarith)
  have hC : ∀ l, (coarseC X.p (X.S C0 CE1 CE2) a b l : ℝ) * ((X.S C0 CE1 CE2).P X.p l : ℝ) ≤ 2 * X.L.a := by
    intro l
    have h1 : coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l ≤ a l :=
      (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    have h2 : ((coarseC X.p (X.S C0 CE1 CE2) a b l * (X.S C0 CE1 CE2).P X.p l : ℕ) : ℝ) ≤ (a l : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (window_entry_le_two_mul_a hS a hT l)
  have hP0 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := Nat.cast_nonneg _
  have key : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) ∨
      (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) := by
    unfold segChain
    dsimp only
    rw [dite_eq_right hq]
    split_ifs with h2 h3 h3
    · exact Or.inl (hK.2.2.1 _ h3).2.1
    · exact Or.inl (hK.2.1 _ (not_lt.mp h3)).1
    · exact Or.inr (Nat.sub_le _ _)
    · exact Or.inr le_rfl
  rcases key with h | h
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseA X.p (X.S C0 CE1 CE2) b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hA _)
  · have : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ (coarseC X.p (X.S C0 CE1 CE2) a b (topOf q hq) : ℝ) := by
      exact_mod_cast h
    exact (mul_le_mul_of_nonneg_right this hP0).trans (hC _)

theorem oplus_le (b : SegBlock X.s X.r) (a : Fin X.s → ℕ) (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) :
    (b.oPlus : ℝ) ≤ 2 * X.L.a := by
  have h0 := hK.2.2.2
  unfold Oplus at h0
  have hp1 : 1 ≤ X.p := X.std.1.prime.one_lt.le
  have hB : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b' := hS.bTop
  have hcap := cap_le (p := X.p) (X.S C0 CE1 CE2) b hp1 hS.E0 (5 / 2 * X.L.b') hB X.s
  have hr5 := r5 hS
  have hs : 2 * (X.s : ℝ) + 2 ≤ (X.r : ℝ) := by exact_mod_cast hS.hF.s_le
  have hp : ((X.r : ℝ) + 1) ^ 2 ≤ (X.p : ℝ) := hS.hF.p_ge
  have hb := hS.hF.b0
  have hkb := hS.kb
  have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
  have hLa0 := hS.hF.La0
  have hLa : X.L.La C0 / ((X.r : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith [hS.La4]
  have hp0 : (0 : ℝ) < (X.p : ℝ) := by nlinarith
  have hp5 : (5 : ℝ) ≤ (X.p : ℝ) := by nlinarith
  have h4 : 4 / (X.p : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsum : (∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ)) ≤ (X.s : ℝ) * (2 * X.L.a / X.p) := by
    have : ∀ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 2 * X.L.a / X.p := by
      intro i
      have hP : (X.p : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p i : ℝ) := by exact_mod_cast p_le_P i
      show 2 * (X.L.a : ℝ) / _ ≤ _
      exact div_le_div_of_nonneg_left (by positivity) hp0 hP
    calc _ ≤ ∑ _i : Fin X.s, 2 * (X.L.a : ℝ) / X.p := Finset.sum_le_sum fun i _ => this i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsp : (X.s : ℝ) * (2 * X.L.a / X.p) ≤ X.L.a / 5 := by
    rw [mul_div_assoc', div_le_div_iff₀ hp0 (by norm_num)]
    have h10 : 10 * (X.s : ℝ) ≤ (X.p : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left h10 ha0
    linarith
  have hsum0 : 0 ≤ ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  have hmid : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2 := by
    show X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 / 2
    linarith
  have hmid0 : 0 ≤ (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 := by
    show 0 ≤ X.L.La C0 / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2
    positivity
  have hT2 : ((X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2) *
      ∑ i, 2 * ((X.S C0 CE1 CE2).a : ℝ) / ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.a / 10 := by
    have := mul_le_mul hmid (hsum.trans hsp) hsum0 (by norm_num)
    linarith
  have hBp : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 5 / 2 * X.L.b' := hS.hF.bT_le _ (segNext_mem X.L.TT X.j)
  have hT3 : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) ≤ X.L.a / 10 := by
    have e : (X.S C0 CE1 CE2).La * ((X.S C0 CE1 CE2).bPlus : ℝ) / ((X.r : ℝ) + 1) =
        X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) := by
      show X.L.La C0 * _ / _ = _
      ring
    rw [e]
    have h5 := b_small hS
    have h6 : (0 : ℝ) ≤ ((X.S C0 CE1 CE2).bPlus : ℝ) := Nat.cast_nonneg _
    have h7 : X.L.La C0 / ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ 1 / 4 * (5 / 2 * X.L.b') :=
      mul_le_mul hLa hBp h6 (by norm_num)
    linarith
  have hsB : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ X.L.a / 2 := by
    have h1 : (X.s : ℝ) ≤ ((X.r : ℝ) + 1) / 2 := by linarith
    have h2 : (X.s : ℝ) * (5 / 2 * X.L.b') ≤ ((X.r : ℝ) + 1) / 2 * (5 / 2 * X.L.b') :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    linarith
  have ha : (X.S C0 CE1 CE2).a = X.L.a := rfl
  rw [ha] at hcap
  linarith

theorem lLL_deg_le_chain (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ (segChain X.p (X.S C0 CE1 CE2) a b).deg q :=
  (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem lLL_deg_le (a : Fin X.s → ℕ) (hT : a ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (b : SegBlock X.s X.r)
    (hK : Kept X.p X.r (X.S C0 CE1 CE2) a b) (x : Lv C0 CE1 CE2 X) (q : Fin (2 * X.s + 1)) :
    (lLL C0 CE1 CE2 X a b x).deg q ≤ 2 * X.L.a := by
  have h1 := lLL_deg_le_chain hS a b x q
  have h2 : ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) ≤ 2 * X.L.a := by
    by_cases hq : (q : ℕ) = 2 * X.s
    · have e := segChain_deg_last (p := X.p) (X.S C0 CE1 CE2) a b q hq
      rw [e]
      exact oplus_le hS b a hK
    · have hw := chain_wt hS a hT b hK q hq
      have hP : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (topOf q hq) : ℝ) := by exact_mod_cast hS.P1 _
      have h0 : (0 : ℝ) ≤ ((segChain X.p (X.S C0 CE1 CE2) a b).deg q : ℝ) := Nat.cast_nonneg _
      nlinarith
  have h3 : (segChain X.p (X.S C0 CE1 CE2) a b).deg q ≤ 2 * X.L.a := by exact_mod_cast h2
  omega

end Deg

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Hyp

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestTMSize : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    (∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i) ∧
    (∀ y, ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top).deg y ≤ 2 * X.L.a) ∧
    (∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.z i ≤ 2 * X.L.a) ∧
    (∑ y, ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top).deg y) ≤ 8 * X.L.a ∧
    1 ≤ X.L.a

variable {C0 CE1 CE2 X}

theorem lgA_ge_one (p a r : ℕ) (hp : 1 < p) (hr : 1 ≤ r) : 1 ≤ lgA p a r := by
  unfold lgA
  have : 0 ≤ Real.logb p (8 * a + r) := by
    apply Real.logb_nonneg (by exact_mod_cast hp)
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  linarith

theorem r_ge_two {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : 2 ≤ X.r := by
  have h := hH.1.2.2.2.2.2.2.1
  have h1 := hH.1.2.2.2.2.2.1
  show 2 ≤ X.L.m
  omega

theorem p_ne_two {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : X.p ≠ 2 := by
  have h5 := X.std.1.five_le
  show X.L.p ≠ 2
  omega

private theorem setTies_deg_succ_pos_eq_of_strictMono {N : ℕ} (LL : GM.M.Letters N) (T : GM.M.TieData) (n : Fin T.t → ℕ)
    (hT : StrictMono T.pos) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ = n i := by
  have hex : ∃ j : Fin T.t, T.pos j + 1 = T.pos i + 1 := ⟨i, rfl⟩
  have hc : Classical.choose hex = i := hT.injective (by have := Classical.choose_spec hex; omega)
  show (if h' : ∃ j : Fin T.t, T.pos j + 1 = T.pos i + 1 then n (Classical.choose h')
    else LL.deg ⟨T.pos i + 1, h⟩) = n i
  rw [dite_eq_left hex, hc]



theorem restTMHyp_of {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : RestTMSize C0 CE1 CE2 X) : RestTMHyp C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  obtain ⟨hS1, hS2, hS3, hS4, hS5⟩ := hS dl hdl a ha x hx
  have hY : 1 ≤ X.L.Y := by
    obtain ⟨⟨hY, -⟩, -⟩ := hH
    exact hY
  set M := XMof C0 CE1 CE2 X dl a x.fst x.snd with hM
  have hpos : ∀ l : Fin M.T.t, M.T.pos l = 2 * ((uTop (X.S C0 CE1 CE2) l : Fin X.s) : ℕ) := fun l => rfl
  have hlt : ∀ l : Fin M.T.t, M.T.pos l + 1 < 2 * M.s + 1 := by
    intro l
    rw [hpos l]
    have := (uTop (X.S C0 CE1 CE2) l).isLt
    show _ < 2 * X.s + 1
    omega
  have hmono : StrictMono M.T.pos := by
    intro i j hij
    rw [hpos i, hpos j]
    have : (i : ℕ) < j := hij
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) < 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ))
    omega
  have hvec : ∀ y, M.LL.vec y = decide ((y : ℕ) % 2 = 0) := fun y => rfl
  have htop : ∀ i, M.top i ≤ 2 * X.L.a := by
    intro i
    have := hS2 ⟨M.T.pos i + 1, hlt i⟩
    rwa [setTies_deg_succ_pos_eq_of_strictMono _ _ _ hmono i (hlt i)] at this
  have hdd : ∀ i, M.dd i = 1 := fun i => rfl
  have hYl : ∀ i, M.Yl i = (Nl C0 CE1 CE2 X dl x.snd i).sup id
      - sInf ↑(Nl C0 CE1 CE2 X dl x.snd i) + 1 := fun i => rfl
  have hYl1 : ∀ i, 1 ≤ M.Yl i := fun i => by rw [hYl i]; omega
  have htop' : ∀ i, M.top i = M.n₀ i + (M.Yl i - 1) := fun i => by
    show M.n₀ i + M.dd i * (M.Yl i - 1) = _
    rw [hdd, one_mul]
  have hr2 : 2 ≤ X.r := r_ge_two hH
  have key : ∀ n : ℕ, n ≤ 8 * X.L.a + X.r → (n : ℝ) ≤ 8 * M.a + M.r := by
    intro n hn
    rw [show M.a = (X.L.a : ℝ) from rfl, show M.r = X.r from rfl]
    exact_mod_cast hn
  have hd : ∀ j, M.degAt j ≤ 2 * X.L.a := by
    intro j
    unfold InstM.degAt
    split
    · exact hS2 _
    · omega
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hS1, ?_⟩
  · exact p_ne_two hH
  · exact hr2
  · refine ⟨hmono, fun i => ⟨hlt i, ?_, ?_⟩, fun i => ⟨⟨i, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩⟩
    · rw [hvec]
      simp only [decide_eq_true_eq]
      rw [hpos]
      omega
    · rw [hvec]
      simp only [decide_eq_false_iff_not]
      rw [hpos]
      omega
    · show (if h : (i : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨i, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = M.T.pos i + 1
      rw [dite_eq_left (show (i : ℕ) < (X.S C0 CE1 CE2).t from i.isLt)]
      rfl
  · intro y
    rfl
  · intro k
    by_cases hk : (k : ℕ) < (X.S C0 CE1 CE2).t
    · right
      refine ⟨⟨k, hk⟩, ?_⟩
      show (if h : (k : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨k, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = _
      rw [dite_eq_left hk]
      rfl
    · left
      show (if h : (k : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨k, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = _
      rw [dite_eq_right hk]
      rfl
  · show (1 : ℝ) ≤ X.L.a
    exact_mod_cast hS5
  · show 1 ≤ X.L.Y * kapS X
    have hp1 : 1 < X.p := by
      have := X.std.1.five_le
      show 1 < X.L.p
      omega
    have hl := lgA_ge_one X.p X.L.a X.r hp1 (by omega)
    have hr2' : (2 : ℝ) ≤ X.r := by exact_mod_cast hr2
    have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
    unfold kapS
    have h1 : (1 : ℝ) ≤ 3 * (↑X.s + 2) * ↑X.r ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ 3 * (↑X.s + 2) * ↑X.r ^ 2 * lgA X.p X.L.a X.r := by nlinarith
    nlinarith
  · intro i
    refine ⟨hYl1 i, ?_, ?_⟩
    · rw [hdd]
      norm_num
    · rw [hdd, Nat.cast_one]
      exact isCoprime_one_left
  · refine ⟨?_, fun i => ⟨?_, ?_, ?_⟩⟩
    · apply key
      have : M.LLt.total ≤ 8 * X.L.a := hS4
      omega
    · apply key
      have h1 := hd (M.T.pos i)
      have h2 := hd (M.T.pos i + 1)
      have h3 := hS3 i
      have : M.r = X.r := rfl
      omega
    · apply key
      have := htop i
      have := htop' i
      omega
    · apply key
      have h1 : M.Si i ≤ M.n₀ i := hS1 i
      have := htop i
      have := htop' i
      omega

end Hyp

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
