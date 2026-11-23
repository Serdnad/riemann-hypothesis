module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle687
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

open GlobalTheory.Unf

theorem colcon_splitFam_append {T : Type} {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : p.Fam S) (e : q.Fam S), splitFam q (Path.Fam.append (q := q) d e) = (d, e)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
      show ((splitFam q (Path.Fam.append (q := q) d e.1)).1, ((splitFam q (Path.Fam.append (q := q) d e.1)).2, e.2)) = (d, e)
      rw [colcon_splitFam_append q d e.1]
      rfl

theorem colcon_getD_downFam {T : Type} {S : Arrow T → Type} (t : T) (i : ℕ) :
    ∀ (n : ℕ) (f : ∀ j : Fin n, S (.down t i j)) (j : ℕ) (hj : j < n), getD t i n (downFam t i n f) j hj = f ⟨j, hj⟩
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, f, j, hj => by
      unfold getD
      have hs := colcon_splitFam_append (p := Path.one (.down t i n)) (downPath t i n) ((), f (Fin.last n))
        (downFam t i n fun j => f j.castSucc)
      rw [downFam]
      split_ifs with h
      · erw [hs]
        exact colcon_getD_downFam t i n _ j h
      · have hnj : n = j := by omega
        subst j
        change (splitFam (p := Path.one (.down t i n)) (downPath t i n) _).1.2 =
          f (Fin.last n)
        rw [hs]

theorem colcon_nIter_congr {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
    {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) {q q' : (∀ i, H i) → ℂ} :
    ∀ (l : List ι) (h : ∀ i, H i) (z : ℂ), NIter ρ μ q l h z →
      (∀ h' : ∀ i, H i, (∀ i, i ∉ l → h' i = h i) → q h' = q' h') → NIter ρ μ q' l h z
  | [], h, z, hz, hq => (show z = q h from hz).trans (hq h fun _ _ => rfl)
  | i :: l, h, z, ⟨f, hf, hr⟩, hq => ⟨f, hf, fun g => colcon_nIter_congr ρ μ l _ _ (hr g) fun h' hh' => hq h' fun k hk => by
      rw [hh' k fun hl => hk (List.mem_cons_of_mem _ hl), Function.update_of_ne fun e => hk (by simp [e])]⟩

theorem colcon_quot {G : Type} [Group G] [MeasurableSpace G] {R R' : Subgroup G} (e : R = R') {ρ : Measure R} {ρ' : Measure R'}
    (hh : HEq ρ ρ') {μ : Measure G} {f : G → ℂ} {z : ℂ} (h : IsQuotIntL1 ρ' μ f z) : IsQuotIntL1 ρ μ f z := by
  subst e
  obtain rfl := eq_of_heq hh
  exact h

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem colcon_rowGrp_jac {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (jacAt G hM j σ hj).d := by
  unfold rowGrp
  rw [dite_eq_left (by omega)]
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  rfl

theorem colcon_rowGrp_bes {t : T} {M : Vol G} (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m)
    (vN : VolN (besDecAt G j σ hj)) :
    rowGrp G j = besGrp (besAt G hM j σ hj vN).d (besAt G hM j σ hj vN).o := by
  unfold rowGrp
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  rfl

theorem colcon_gen (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t)
    (F : Fn G (.grid D.R.m D.R.m)) (ρ : ∀ j, Measure (rowGrp G j))
    (hJ : ∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR)
    (hB : ∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) (h : Pts G) (g : GA D (G.V (.grid D.R.m j)))
      (φ : GA D (G.V (.top j)) → ℂ) (z : ℂ), g = h j →
      (chainFrom G W t hM σ j hj vN).Iter
        (colPer W hM σ j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) σ j hj vN) F φ g) z →
      NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h' => jPer W M t (conAt W hM Φ h') F σ j hj φ)
        (List.range' (j + 1) (2 * σ)) h z := fun
  | 0, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hc : conAt W hM Φ h j = lastDat W hM j hj vN (h j) (Φ ⟨j, by omega⟩)
          (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)) := by
        unfold conAt
        rw [dite_eq_left hj]
        rfl
      have hz' : z = colPer W hM 0 j hj vN (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) 0 j hj vN) F φ (h j) () := hz
      show z = jPer W M t (conAt W hM Φ h) F 0 j hj φ
      rw [hz']
      show _ = ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * biL W M t j φ (conAt W hM Φ h j)
        (GlobalTheory.RowChain.topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m)
      rw [hc]
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom]
      rw [colcon_getD_downFam, colcon_getD_downFam]
      rfl
  | σ + 1, j, hj, vN, h, g, φ, z, hg, hz => by
      subst hg
      have hj' : j + 1 + 1 + 2 * σ + 2 = D.R.m := by omega
      let vN' := (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ hj')).some
      have hstep : ∃ (f₁ : GA D (G.V (.grid D.R.m (j + 1))) → ℂ)
          (f₂ : GA D (G.V (.grid D.R.m (j + 1))) → GA D (G.V (.grid D.R.m (j + 1 + 1))) → ℂ),
        IsQuotIntL1 (jacAt G hM (j + 1) (σ + 1) (by omega)).μR
          (M.ν (.grid D.R.m (j + 1))) f₁ z ∧
        ∀ a, IsQuotIntL1 (besAt G hM (j + 1 + 1) σ hj' vN').μR
          (M.ν (.grid D.R.m (j + 1 + 1))) (f₂ a) (f₁ a) ∧
          ∀ b, (chainFrom G W t hM σ (j + 1 + 1) hj' vN').Iter
            (fun rest => colPer W hM (σ + 1) j hj vN
              (dataFrom G W t hM (downFam t D.R.m D.R.m Φ) (σ + 1) j hj vN)
              F φ (h j) (a, b, rest)) (f₂ a b) := hz
      rcases hstep with ⟨f₁, f₂, h1, h2⟩
      have hl : List.range' (j + 1) (2 * (σ + 1)) = (j + 1) :: (j + 1 + 1) :: List.range' (j + 1 + 1 + 1) (2 * σ) := by
        rw [show 2 * (σ + 1) = 2 * σ + 1 + 1 by ring, List.range'_succ, List.range'_succ]
      rw [hl]
      have hjJ : j + 1 + 2 * (σ + 1) + 1 = D.R.m := by omega
      refine ⟨f₁, colcon_quot (colcon_rowGrp_jac hM (j + 1) (σ + 1) hjJ)
        (hJ (j + 1) (σ + 1) hjJ) h1, fun a => ?_⟩
      refine ⟨f₂ a, colcon_quot (colcon_rowGrp_bes hM (j + 1 + 1) σ hj' vN')
        (hB (j + 1 + 1) σ hj') (h2 a).1,
        fun b => ?_⟩
      have hi := (h2 a).2 b
      dsimp only [GlobalTheory.RowChain.colPer, dataFrom] at hi
      have ih := colcon_gen G W t hM Φ F ρ hJ hB σ (j + 1 + 1) hj' vN'
        (Function.update (Function.update h (j + 1) a) (j + 1 + 1) b) b _ (f₂ a b) (by simp) hi
      refine colcon_nIter_congr _ _ _ _ _ ih fun h' hh' => ?_
      have e0 : h' j = h j := (hh' j (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _))
      have e1 : h' (j + 1) = a := (hh' (j + 1) (by simp only [List.mem_range'_1]; omega)).trans
        ((Function.update_of_ne (by omega) _ _).trans (Function.update_self _ _ _))
      have e2 : h' (j + 1 + 1) = b := (hh' (j + 1 + 1) (by simp only [List.mem_range'_1]; omega)).trans (Function.update_self _ _ _)
      change _ = jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) hj'
        (biL W M t j φ (conAt W hM Φ h' j))
      apply congrArg (jPer W M t (conAt W hM Φ h') F σ (j + 1 + 1) hj')
      have hx : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
      have hlast : ¬ (j + 2 * 0 + 2 = D.R.m) := by omega
      have hC : conAt W hM Φ h' j = _ :=
        (dite_eq_right hlast).trans (dite_eq_left hx)
      rw [hC]
      obtain rfl : σ = (D.R.m - 4 - j) / 2 := by omega
      simp only [e0, e1, e2, colcon_getD_downFam]
      -- These projections of the Bessel data are independent of the choice of vN.
      dsimp only [biL, GlobalTheory.SeeSaw.biLift, volAt, contr, flatBF, flatFB, Link.κ,
        stepAt, linkAt, besAt, jacAt]
      rfl

theorem nIter_conAt_of_colPer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) (Φ : SchDown G t) (F : Fn G (.grid D.R.m D.R.m)) (φ : Fn G (.top 0)) (z : ℂ), (chain G W t hM).Iter (colPer W hM _ 0 top_idx (topVN hM) (chainData G W t hM (downFam t D.R.m D.R.m Φ)) F φ 1) z → ∀ (ρ : ∀ j, Measure (rowGrp G j)), (∀ j σ (hj : j + 2 * σ + 1 = D.R.m), HEq (ρ j) (jacAt G hM j σ hj).μR) → (∀ j σ (hj : j + 2 * σ + 2 = D.R.m), HEq (ρ j) (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR) → NIter ρ (fun j => M.ν (.grid D.R.m j)) (fun h => jPer W M t (conAt W hM Φ h) F _ 0 top_idx φ) (idx D) 1 z := by
  intro D T L sc G W t M hM Φ F φ z hz ρ hJ hB
  have e : List.range' (0 + 1) (2 * ((D.R.m - 2) / 2)) = idx D := by
    unfold idx
    have := top_idx (D := D)
    congr 1
    omega
  rw [← e]
  exact colcon_gen G W t hM Φ F ρ hJ hB _ 0 top_idx (topVN hM) 1 1 φ z rfl hz

end GlobalTheory.RowVal
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def colCoef (ch : Choice R) (t : T) (β : CosFam ch.G t) (j : ℕ) : ℚ :=
  ∏ w : locPl ch.G t, if h : j < D.R.m then
    invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) else 1

theorem coef_prod (ch : Choice R) (t : T) (Φ : ch.G.Datum) (β : CosFam ch.G t) :
    ∏ w, ((ch.S.term t Φ β w).coef : ℂ) = ((idx D).map fun j => (colCoef ch t β j : ℂ)).prod := by
  have hw : ∀ w, (ch.S.term t Φ β w).coef = ∏ i : Fin (D.R.m - 2), (if h : 1 + (i : ℕ) < D.R.m then
      invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := 1 + (i : ℕ)) h) else 1) := by
    intro w
    have hj : ∀ (j j' : ℕ) (_ : j = j') (h : j < D.R.m) (h' : j' < D.R.m),
        invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) =
          invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j') h') := by
      rintro j _ rfl h h'
      rfl
    show ∏ i : Fin (D.R.m - 2), invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w))
      (j := (i : ℕ) + 1) (show (i : ℕ) + 1 < D.R.m by have := i.isLt; omega)) = _
    exact Finset.prod_congr rfl fun i _ => by
      rw [dite_eq_left (show 1 + (i : ℕ) < D.R.m by have := i.isLt; omega)]
      exact hj _ _ (Nat.add_comm _ _) _ _
  have key : ∏ w, (ch.S.term t Φ β w).coef = ((idx D).map fun j => colCoef ch t β j).prod := by
    simp only [hw]
    rw [Finset.prod_comm]
    simp only [idx, List.range'_eq_map_range, List.map_map]
    rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => rfl
  have := congrArg (Rat.cast : ℚ → ℂ) key
  rw [Rat.cast_prod, Rat.cast_list_prod, List.map_map] at this
  exact this

end GlobalTheory.RowWt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColComb

variable {D : D7}

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ u ∈ c.support, c u * (ψ (symplOH S T w u) * f (w + u)) := by
  unfold comb
  rw [Finset.sum_apply]
  rfl

theorem comb_comm (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c₂ (fun v' => comb ψ A S c₁ (fun u' => G u' v') u) v =
      comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (G u') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ c₁' c₁'' : WO A S →₀ ℂ) (c₂ c₂' c₂'' : WO S A' →₀ ℂ)
    (h₁ : ∀ f, comb ψ A S c₁'' f = comb ψ A S c₁ (comb ψ A S c₁' f))
    (h₂ : ∀ f, comb ψ S A' c₂'' f = comb ψ S A' c₂ (comb ψ S A' c₂' f)) (F : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c₁ c₂ (biComb ψ A S A' c₁' c₂' F) = biComb ψ A S A' c₁'' c₂'' F := by
  funext u v
  show comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (fun v' => comb ψ A S c₁' (fun u'' => comb ψ S A' c₂' (F u'') v') u') v) u =
    comb ψ A S c₁'' (fun u' => comb ψ S A' c₂'' (F u') v) u
  rw [h₁]
  congr 1
  funext u'
  rw [comb_comm]
  simp only [h₂]

end GlobalTheory.ColComb

open GlobalTheory.ColComb in
theorem GlobalTheory.ColComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (c : Combs ch.G) (c' c'' : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ j, j < D.R.m → ∀ f, comb ch.W.ψ _ _ (c'' j) f = comb ch.W.ψ _ _ (c.1 j) (comb ch.W.ψ _ _ (c' j) f)) → ∀ (C : BiFam ch.G) (u : ColPt ch.G), evT (combC ch.W c (combC ch.W (c', 0) C)) 1 u 0 = evT (combC ch.W (c'', 0) C) 1 u 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ ch _ _
  beta_reduce
  intro c c' c'' hc C u
  unfold evT
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k + 1 < D.R.m := by
    have := Finset.mem_range.mp hk
    omega
  simp only [combC]
  rw [biComb_biComb (h₁ := hc (2 * k) (by omega)) (h₂ := hc (2 * k + 1) hk')]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

private theorem B_update_mul_eq_mul {X : ℕ → Type} (B : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (j : ℕ)
    (a : (∀ i, X i) → X j → ℂ) (R : (∀ i, X i) → ℂ)
    (ha : ∀ u x, a (Function.update u j x) = a u) (hR : ∀ u x, R (Function.update u j x) = R u)
    (u : ∀ i, X i) :
    B j (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) (u j) =
      B j (a u) (u j) * R u := by
  have hfun : (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) =
      R u • a u := by
    funext x
    rw [ha, hR, Function.update_self, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hfun, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prod_op {X : ℕ → Type} (A : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (n : ℕ) :
    ∃ Tc : ((∀ j, X j) → ℂ) →ₗ[ℂ] ((∀ j, X j) → ℂ), ∀ (C : ∀ j, X j → X (j + 1) → ℂ) (g : (∀ j, X j) → ℂ),
      (∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g u = g u') →
      (fun u : ∀ j, X j => (∏ k ∈ Finset.range n,
          A (2 * k) (fun x => A (2 * k + 1) (C (2 * k) x) (u (2 * k + 1))) (u (2 * k))) * g u) =
        Tc (fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) := by
  classical

  let op : ∀ j, ((∀ i, X i) → ℂ) →ₗ[ℂ] ((∀ i, X i) → ℂ) := fun j =>
    { toFun := fun F u => A j (fun x => F (Function.update u j x)) (u j)
      map_add' := fun F G => by
        funext u
        have e : (fun x => (F + G) (Function.update u j x)) =
            (fun x => F (Function.update u j x)) + (fun x => G (Function.update u j x)) := rfl
        rw [e, map_add (f := _)]
        rfl
      map_smul' := fun c F => by
        funext u
        have e : (fun x => (c • F) (Function.update u j x)) = c • (fun x => F (Function.update u j x)) := rfl
        rw [e, map_smul]
        rfl }
  induction n with
  | zero => exact ⟨LinearMap.id, fun C g _ => by simp⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T ∘ₗ op (2 * n) ∘ₗ op (2 * n + 1), fun C g hg => ?_⟩

    obtain ⟨R, hRR⟩ : ∃ R : (∀ j, X j) → ℂ,
        R = fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u := ⟨_, rfl⟩
    have hR : ∀ j, 2 * n ≤ j → j < 2 * n + 2 → ∀ (u : ∀ i, X i) x, R (Function.update u j x) = R u := by
      intro j hj1 hj2 u x
      subst hRR
      dsimp only
      congr 1
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · exact hg _ _ fun i hi => Function.update_of_ne (by omega) _ _

    obtain ⟨g', hgG⟩ : ∃ g' : (∀ j, X j) → ℂ,
        g' = fun u => A (2 * n) (fun x => A (2 * n + 1) (C (2 * n) x) (u (2 * n + 1))) (u (2 * n)) * g u :=
      ⟨_, rfl⟩
    have hg' : ∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g' u = g' u' := by
      intro u u' h
      subst hgG
      dsimp only
      rw [h (2 * n) le_rfl, h (2 * n + 1) (by omega), hg u u' fun j hj => h j (by omega)]

    have h1 : op (2 * n + 1) (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
        fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u := by
      have hF : (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
          fun u => (fun w : ∀ j, X j => C (2 * n) (w (2 * n))) u (u (2 * n + 1)) * R u := by
        funext u
        subst hRR
        simp only [Finset.prod_range_succ]
        ring
      rw [hF]
      funext v
      refine B_update_mul_eq_mul A (2 * n + 1) (fun w => C (2 * n) (w (2 * n))) R ?_ (hR _ (by omega) (by omega)) v
      intro w x
      show C (2 * n) (Function.update w (2 * n + 1) x (2 * n)) = C (2 * n) (w (2 * n))
      rw [Function.update_of_ne (by omega)]

    have h2 : op (2 * n) (fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u) =
        fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g' u := by
      funext v
      have e := B_update_mul_eq_mul A (2 * n) (fun w x => A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))) R
        (fun w y => by
          funext x
          show A (2 * n + 1) (C (2 * n) x) (Function.update w (2 * n) y (2 * n + 1)) = A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))
          rw [Function.update_of_ne (by omega)])
        (hR _ le_rfl (by omega)) v
      refine e.trans ?_
      subst hRR hgG
      dsimp only
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, ← hT C g' hg']
    funext u
    subst hgG
    simp only [Finset.prod_range_succ]
    ring

noncomputable def combLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem exists_comb_op : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ => ?_⟩⟩
  intro c
  obtain ⟨Tc, hTc⟩ := exists_prod_op (X := fun j => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
    (fun j => combLin ch.W.ψ _ _ (c.1 j)) (D.R.m / 2)
  refine ⟨Tc, fun C => ?_⟩
  exact hTc C (fun _ => ∏ i, (1 : SchRow ch.G) i ((0 : RowPt ch.G) i)) fun _ _ _ => rfl

end GlobalTheory.LocAsm
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)


open Classical in
def PlaceCl (s : ℤˣ) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (ζ : ℂ) : Prop :=
  ∀ e, IsIdemSum e {w} → ∀ (M : Vol ch.G) (hM : M.Is t) (r r₀ h : Pts ch.G),
    OneLoc t w e r (fun j => if j ∈ idx D then sgnAt ch.G t s w j * (repsAt ch.G t w).elt β (D.R.m, j) else 1) →
    OneLoc t w e r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) j)⁻¹ else 1) →
    (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.under (𝓞 D.host.F))) →
    ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w).rank b.tgt)) (Fin ((locGrid ch.G t w).rank b.src)) (Kw w) → ℂ),
      (∀ i j x, φ (.ex i j) x = 1) → ∀ v f : SchDown ch.G t, (∀ j, IsThetaFunO ch.W.ψ _ _ (v j)) →
      (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (v j) (fun y => if IsHalf e y then φ (.theta D.R.m j)
        (ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩
          (y.map fun a => cpt w (toEAf D a))) else 0) (f j)) →
      ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G),
        (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = e ∧ IsCombOf ch.W (d i j) ((c i).1 j)) →
        (∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (y j)) →
          ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w) (unitVol w)
            (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt β)
              ((locGrid ch.G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.toGridChoice.colAt t w y) 0) →
        ∀ u, evT (conAt ch.W hM f (h * r)) 1 u 0 = ζ * ∑ i ∈ S, x i * evT (combC ch.W (c i) (conAt ch.W hM v (h * r₀))) 1 u 0

theorem placeAt_iff (s : ℤˣ) : PlaceAt ch s ↔ ∃ (κ : Pl D.host.E → ℂ) (z : T → Pl D.host.E → ℂˣ),
    (∀ t w, z t w ∈ xiVals R.toLevCh t) ∧ (∀ w, w ∉ ch.G.pl.W0 → κ w = 1) ∧
    ∀ t, ∀ w ∈ locPl ch.G t, ∀ β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w), ∃ ζ : ℂ,
      ((w ∈ ch.G.pl.W0 → ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) (i + 1))) →
        ζ = κ w * (z t w : ℂ)⁻¹) ∧ PlaceCl ch s t w β ζ := Iff.rfl

end GlobalTheory.LocAsm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  first | exact @GlobalTheory.FirstRowLevel.levRow_zero_le | exact GlobalTheory.FirstRowLevel.levRow_zero_le | (intros; apply GlobalTheory.FirstRowLevel.levRow_zero_le <;> assumption)
end
