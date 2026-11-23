module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle010
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FactorActionAlgebra
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Psmall
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.PCandTb

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

set_option linter.unusedSectionVars false

theorem isLev_of {a b : ℕ} (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (Q : Finset (Pl E))
    (h : ∀ w, LocOk.IsLv (U w)) (hout : ∀ w ∉ Q, U w = K2 a b w) : IsLev U := by
  refine ⟨fun w => ?_, Filter.eventually_cofinite.2 (Q.finite_toSet.subset fun w hw => ?_)⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := h w
    rw [he]
    exact LocOk.prod_open_le h₁ h₂
  · by_contra hq
    exact hw (hout w hq)

variable {n : ℕ} (d : LocData E n) {a : ℕ}

theorem isLev_lev (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev_lv d hd ha) fun _ hw =>
    LocOk.lev_out d (LocOk.out3 d hw).1 (LocOk.out3 d hw).2

theorem isLev_lev₂ (hd : d.Ok) (ha : a ≤ n) : IsLev (d.lev₂ a) :=
  isLev_of _ (d.T ∪ d.S₀ ∪ d.Bad) (LocOk.lev₂_lv d hd ha) fun _ hw => LocOk.lev₂_out d (LocOk.out3 d hw).2

theorem betaL_H (hd : d.Ok) (ha : a ≤ n) {u : Pl E} (hu : u ∈ d.P) (x y : d.kap u) :
    IsHecke (d.lev a u) ((d.betaL a ha).m u x y) := by
  show IsHecke _ (if u ∈ d.T then d.diag (fun x => d.qT a u x.1.1) x y else d.mac a ha u (d.e u) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d u z.1.1) x y
  · have hS : u ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hu
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

theorem gap_restr {m : ℕ} {x : Fin n → ℤ} (hx : x ∈ coneGL n 2) (S : Finset (Fin n)) (h : S.card = m) :
    Gap (PositivityTheory.Rg.Bc.ArchbcB.B.restr x S h) := by
  intro p q hpq
  have := hx _ _ ((S.orderEmbOfFin h).strictMono hpq)
  show x _ + 1 ≤ x _
  omega

theorem unrAt_pow {μ : HChar E} {w : Pl E} (h : μ.UnrAt w) (k : ℕ) : (μ ^ k).UnrAt w := by
  induction k with
  | zero => intro x _; rw [pow_zero]; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ]
    show (μ ^ k).loc w x * μ.loc w x = 1
    rw [ih x hx, h x hx, one_mul]

end PositivityTheory.Rg.BcB.F.PCandTb

namespace PositivityTheory.Rg.BcB.F

open PCandTb

theorem candT_of (h1 : Tail.ReadT) (h2 : Tail.ExpRead) (h3 : RS.JoinSat) : CandT := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwT hunr hns
  have hd := F.ok
  have hwd : w ∈ F.d.T := F.T_le w hwT hunr hns
  have hwSec : w ∈ F₀.Sec := (F.T_in w hwd).1
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h | h
    · exact (F.T_in u h).1
    · rw [F.same.1] at h
      exact (F₀.S₀ u h).1
  have hwP : w ∈ F.d.P := Finset.mem_union_left _ hwd
  obtain ⟨α, x, hx⟩ := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i)
    (Equiv.refl _) F₀.hSec hP (F.d.lev (F₀.C.a i)) (F.d.lev₂ (F₀.C.a i)) (F.d.betaL _ (F₀.C.le i)) A G F.m
    (isLev_lev F.d hd (F₀.C.le i)) (isLev_lev₂ F.d hd (F₀.C.le i))
    (locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 E n F.d hd _ (F₀.C.le i)).2.1 (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => (betaL_H F.d hd (F₀.C.le i) hu x y).2 k hk g) hl hne ⟨w, hwP⟩
  have hm : (F.d.betaL _ (F₀.C.le i)).m w = fun x y => if x = y then F.d.qT (F₀.C.a i) w x.1.1 else 0 := by
    funext x y
    show (if w ∈ F.d.T then _ else _) = _
    rw [if_pos hwd]
    rfl
  let G' : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ := fun y => G (α, Function.update x ⟨w, hwP⟩ y)
  change (locM w ((F.d.betaL _ (F₀.C.le i)).m w))^[F.m] G' ≠ 0 at hx
  rw [hm] at hx
  have hfix : ∀ y, G' y ∈ fixed (pairRt (F₀.C.a i) (n - F₀.C.a i) w) (I2 (F₀.C.a i) (n - F₀.C.a i) w) := fun y => by
    have h := ((hl (α, Function.update x ⟨w, hwP⟩ y)).2 w hwSec).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  have hIo : IsOpen (I2 (F₀.C.a i) (n - F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) := by
    have h := ((isLev_lev F.d hd (F₀.C.le i)).1 w).1
    rwa [LocOk.level_eq_iwahori_pair_at_bad_places F.d hwd] at h
  obtain ⟨s, hs⟩ := (locPow_holds E _ _ w _ _ G' F.m hIo hfix).2 (fun x => F.d.qT (F₀.C.a i) w x.1.1) (by convert hx)
  by_cases hadm : LocData.admitted n (F₀.C.a i) s.1.1
  swap
  · exfalso
    have h0 : F.d.qT (F₀.C.a i) w s.1.1 = 0 := by
      funext y
      simp only [LocData.qT, dif_neg hadm]
      rfl
    obtain ⟨k, hk⟩ : ∃ k, F.m = k + 1 := ⟨F.m - 1, by have := F.m_pos; omega⟩
    rw [h0, hk, Function.iterate_succ_apply', Psmall.actP_zero] at hs
    exact hs rfl
  have hq : F.d.qT (F₀.C.a i) w s.1.1 = fun g => ∑ j : (F.d.c w).support,
      (F.d.c w j * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf (j : Fin n → ℤ)) s.1.1) *
        (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ)) *
      dc2 w (F.d.ϖ w) (restr (j : Fin n → ℤ) _ hadm.2.1) (restr (j : Fin n → ℤ) _ hadm.2.2) g := by
    funext g
    simp only [LocData.qT, dif_pos hadm, Finsupp.sum]
    rw [← Finset.sum_coe_sort]
  rw [hq] at hs
  obtain ⟨ξa, ξb, hJ, hsum⟩ := h1 E n (F₀.C.a i) (n - F₀.C.a i) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F.d.ϖ w)
    (F.d.c w).support _ (fun j => restr (j : Fin n → ℤ) _ hadm.2.1) (fun j => restr (j : Fin n → ℤ) _ hadm.2.2) F.m (G' s)
    (hd.unif w)
    (fun j => ⟨gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _, gap_restr (hd.cone w hwd (Finset.mem_coe.2 j.2)) _ _⟩)
    ((F.choiceM i s₁ s₂ Pa Pb D hc).2 w hwd) (hG _) (hfix s) hs
  have hsum' : ((F.d.c w).sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s.1.1) *
      ev2 w ξa ξb (restr x _ hadm.2.1) (restr x _ hadm.2.2)) ≠ 0 := by
    intro h0
    rw [Finsupp.sum, ← Finset.sum_coe_sort] at h0
    apply hsum
    rw [show (0 : ℂ) = (((I2 (F₀.C.a i) (n - F₀.C.a i) w).relIndex (K2 (F₀.C.a i) (n - F₀.C.a i) w) : ℕ) : ℂ) * 0 by ring,
      ← h0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ' : JEig Pa Pb w (F₀.d₀.ϖ w) ξa ξb := by
    rw [← F.same.2.2.2.1]
    exact hJ
  obtain ⟨hma, hmb, hbc⟩ := F.choiceT i s₁ s₂ Pa Pb D hc w hwd s.1.1 hadm ξa ξb hJ' hsum'
  obtain ⟨hSa, hSb⟩ := h2 E (F₀.C.a i) (n - F₀.C.a i) Pa Pb w (F.d.ϖ w) ξa ξb (hd.unif w) hma hmb hJ
  have hS0 : w ∉ F₀.d₀.S₀ := by
    rw [← F.same.1]
    exact Finset.disjoint_left.1 hd.disj.1 hwd
  have hBad : w ∉ F₀.d₀.Bad := by
    rw [← F.same.2.1]
    exact Finset.disjoint_left.1 hd.disj.2.1 hwd
  have hμ := (F₀.good w hwSec hS0 hBad).2
  have hDs := h3 E n (F₀.C.a i) (n - F₀.C.a i) (F₀.μ ^ (n - F₀.C.a i)) (F₀.μ ^ F₀.C.a i) Pa Pb D w _ _ hc.ctx.join
    (unrAt_pow hμ _) (unrAt_pow hμ _) hSa hSb
  refine ⟨_, hDs, fun s' ϖ q hs' hq' α' hα' => ?_⟩
  have e := LemB.cjEq E w hns s' hs'
  subst e
  exact hbc ϖ q hq' α' hα'

end PositivityTheory.Rg.BcB.F

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Tr pairSpace)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS
open scoped Classical



namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PCandSb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isLev_lev (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : Tail.IsLev (d.lev a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := LocOk.lev_lv d hd ha w
    rw [he]; exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev_out d (LocOk.out3 d h).1 (LocOk.out3 d h).2)

theorem isLev_lev₂ (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) : Tail.IsLev (d.lev₂ a) := by
  refine ⟨fun w => ?_, ?_⟩
  · obtain ⟨K₁, K₂, h₁, h₂, he⟩ := LocOk.lev₂_lv d hd ha w
    rw [he]; exact LocOk.prod_open_le h₁ h₂
  · refine Filter.eventually_cofinite.2 ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.subset fun w hw => ?_)
    by_contra h
    exact hw (LocOk.lev₂_out d (LocOk.out3 d h).2)

theorem betaL_H (d : LocData E n) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) (hw : w ∈ d.P) (x y : d.kap w) :
    IsHecke (d.lev a w) ((d.betaL a ha).m w x y) := by
  show IsHecke _ (if w ∈ d.T then d.diag (fun x => d.qT a w x.1.1) x y else d.mac a ha w (d.e w) x.1.2 y.1.2)
  split_ifs with hT
  · rw [LocOk.level_eq_iwahori_pair_at_bad_places d hT]
    exact LocOk.diagH d _ (fun z => LocOk.qT_H d w z.1.1) x y
  · have hS : w ∈ d.S₀ := by
      simp only [LocData.P, Finset.mem_union] at hw
      tauto
    rw [LocOk.lev_S d hT (Finset.mem_union_left _ hS)]
    exact LocOk.mac_H d PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha hS (LocOk.kap_X d hT hS x) (LocOk.kap_X d hT hS y)

theorem locM_iter_equiv {a b : ℕ} {k k' : Type} [Fintype k] [Fintype k'] (w : Pl E) (σ : k ≃ k')
    (M : k' → k' → LF a b w) (G : k' → H E a b → ℂ) (m : ℕ) :
    (locM w (fun x y => M (σ x) (σ y)))^[m] (G ∘ σ) = ((locM w M)^[m] G) ∘ σ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    funext x
    simp only [locM, Function.comp_apply]
    exact Equiv.sum_comp σ (fun y => actP w (M (σ x) y) (((locM w M)^[m] G) y))

def kapEquiv (d : LocData E n) {w : Pl E} (hT : w ∉ d.T) (hS : w ∈ d.S₀) : d.kap w ≃ d.X w where
  toFun x := ⟨x.1.2, LocOk.kap_X d hT hS x⟩
  invFun y := ⟨(∅, y.1), by unfold LocData.idx; rw [if_neg hT, if_pos hS]; simp [y.2]⟩
  left_inv x := by
    obtain ⟨⟨s, g⟩, hx⟩ := x
    have : s = ∅ := by
      unfold LocData.idx at hx; rw [if_neg hT, if_pos hS] at hx
      simpa using (Finset.mem_product.1 hx).1
    subst this
    rfl
  right_inv y := rfl

end PCandSb

open PCandSb in
theorem candS_of (h : Tail.ReadS) : CandS := by
  intro hR E _ _ _ hE n hn π hπ S T F₀ F hF i s₁ s₂ Pa Pb D A G hc hG hl hne w hwS hsp
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  have hd : F.d.Ok := F.ok
  have hw0 : w ∈ F₀.d₀.S₀ := F₀.S_le w hwS hsp
  have hwd : w ∈ F.d.S₀ := F.same.1 ▸ hw0
  have hwT : w ∉ F.d.T := fun h' => Finset.disjoint_left.1 hd.disj.1 h' hwd
  have hwP : w ∈ F.d.P := Finset.mem_union_right _ hwd
  have hwSec : w ∈ F₀.Sec := (F₀.S₀ w hw0).1
  have hPS : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := by
    intro u hu
    rcases Finset.mem_union.1 hu with h1 | h1
    · exact (F.T_in u h1).1
    · exact (F₀.S₀ u (F.same.1 ▸ h1)).1
  obtain ⟨α, x, hx⟩ := FA.fmPow_of intHint slots BlockFiniteConvolution.finConv' BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i)
    (Equiv.refl _) F₀.hSec hPS (F.d.lev _) (F.d.lev₂ _) (F.d.betaL _ ha) A G F.m (isLev_lev F.d hd ha)
    (isLev_lev₂ F.d hd ha) (LocOk.betaL_ok F.d idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3 hd ha) (fun _ => rfl) (fun _ => rfl)
    (fun u hu x y k hk g => (betaL_H F.d hd ha u hu x y).2 k hk g) hl hne ⟨w, hwP⟩
  obtain ⟨P, hPc, hkill⟩ := F.choiceS w hw0
  refine ⟨P, ?_, hPc⟩
  obtain ⟨hO, hle, hN, hX, hU, hHk⟩ := hd.K' w hwd
  have hK' : F.d.K' w = F₀.d₀.K' w := congrFun F.same.2.2.2.2.1 w
  have hμ : F.d.μ w = F₀.μ.loc w := (congrFun F.same.2.2.1 w).trans (F₀.μloc w)
  have hLo : IsOpen (F.d.lev (F₀.C.a i) w : Set (GLw (F₀.C.a i) w × GLw (n - F₀.C.a i) w)) :=
    ((isLev_lev F.d hd ha).1 w).1
  let σ := kapEquiv F.d hwT hwd
  let G₀ : F.d.kap w → H E (F₀.C.a i) (n - F₀.C.a i) → ℂ :=
    fun y => G (α, (Equiv.refl _).symm (Function.update x ⟨w, hwP⟩ y))
  have hfix : ∀ y, G₀ y ∈ fixed (pairRt (F₀.C.a i) (n - F₀.C.a i) w) (F.d.lev (F₀.C.a i) w) :=
    fun y => ((hl _).2 w hwSec).1
  let M : F.d.X w → F.d.X w → LF (F₀.C.a i) (n - F₀.C.a i) w :=
    fun u v => phiMu (Nat.add_sub_of_le ha) w (F₀.μ.loc w) (F.d.e w) u v
  have hm : (F.d.betaL _ ha).m w = fun u v => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • M (σ u) (σ v) := by
    funext u v
    show (if w ∈ F.d.T then _ else _) = _
    rw [if_neg hwT]
    funext z
    show _ * phiMu (Nat.add_sub_of_le ha) w (F.d.μ w) (F.d.e w) _ _ z = _
    rw [hμ]
    rfl
  have hx' : (locM w fun u v => (F.d.sgn (F₀.C.a i) w * ((F.d.X w).card : ℂ))⁻¹ • M (σ u) (σ v))^[F.m] G₀ ≠ 0 := by
    rw [← hm]; exact hx
  have h1 : (locM w fun u v => M (σ u) (σ v))^[F.m] G₀ ≠ 0 :=
    (locPow_holds E _ _ w (F.d.kap w) _ G₀ F.m hLo hfix).1 _ (fun u v => M (σ u) (σ v)) hx'
  have h2 : (locM w M)^[F.m] (G₀ ∘ σ.symm) ≠ 0 := by
    intro h0
    apply h1
    have e1 := locM_iter_equiv w σ M (G₀ ∘ σ.symm) F.m
    have e2 : (G₀ ∘ σ.symm) ∘ σ = G₀ := by funext y; simp
    rw [e2] at e1
    rw [e1, h0]; rfl
  exact h E n (F₀.C.a i) (n - F₀.C.a i) (Nat.add_sub_of_le ha) F₀.μ s₁ s₂ Pa Pb D hc.ctx w (F.d.K' w) (F.d.X w)
    (F.d.lev _ w) (F.d.e w) P F.m (G₀ ∘ σ.symm) hO hle hN hX hU hLo hHk
    (fun τ hτ hne' v hv => by rw [hK'] at hv ⊢; exact hkill i s₁ s₂ Pa Pb D hc τ hτ hne' v hv)
    (by rw [hK']; exact (F.choiceM i s₁ s₂ Pa Pb D hc).1 w hw0)
    (fun y => ⟨hG _, hfix _⟩) h2

end PositivityTheory.Rg.BcB.F

end
end
