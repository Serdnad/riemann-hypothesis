module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedLagrangianOppositeLagrangianChart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle109
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseFlatMapBand
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle410
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle462
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle463
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockRepr

theorem expand_real (κ : Type) [Fintype κ] (x : κ → ℝ) :
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℝ)) (Real.exp (∑ k, x k)) := by
  have h := GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum κ (fun k => (x k : ℂ))
  rw [← Complex.ofReal_sum, ← Complex.ofReal_exp] at h
  refine Complex.hasSum_ofReal.mp ?_
  convert h using 1
  funext m
  simp [Finsupp.prod]

theorem conjMono_continuous {ι : Type} [Fintype ι] {a b : ℕ} (m : DVar ι a b →₀ ℕ) : Continuous (conjMono m) := by
  unfold conjMono Finsupp.prod; fun_prop

theorem gq_continuous {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) : Continuous (gq (a := a) (b := b) c) := by
  unfold gq; fun_prop

theorem bargmann_repr : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ z₀, G z₀ = ((∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) : ℂ) * ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ z₀
  have hbk : ∀ z, bk c z₀ z = ∑ k : DVar ι a b, (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2) := by
    intro z; simp only [bk, Fintype.sum_prod_type]
  let coef : (DVar ι a b →₀ ℕ) → ℂ := fun m => m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2) ^ n / (n.factorial : ℂ)
  have hcm : ∀ (m : DVar ι a b →₀ ℕ) z, coef m * conjMono m z = m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ) := by
    intro m z
    simp only [coef, conjMono, ← Finsupp.prod_mul]
    refine Finset.prod_congr rfl fun k _ => ?_
    ring
  let F : (DVar ι a b →₀ ℕ) → VCx ι a b → ℂ := fun m z => coef m * (conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hlim : ∀ z, HasSum (fun m => F m z) (Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) := by
    intro z
    have := (GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum (DVar ι a b) (fun k => (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2))).mul_right ((Real.exp (-gq c z) : ℂ) * G z)
    rw [← hbk] at this
    have e : (fun m => F m z) = fun m => (m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ)) * ((Real.exp (-gq c z) : ℂ) * G z) := by
      funext m
      rw [← hcm]
      simp only [F]
      ring
    rw [e, mul_assoc]
    exact this
  have hnorm : ∀ m z, ‖F m z‖ = (m.prod fun k n => (‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) ^ n / (n.factorial : ℝ)) * (Real.exp (-gq c z) * ‖G z‖) := by
    intro m z
    have e1 : F m z = (coef m * conjMono m z) * ((Real.exp (-gq c z) : ℂ) * G z) := by simp only [F]; ring
    rw [e1, hcm, norm_mul, norm_mul, Finsupp.prod, Finsupp.prod, norm_prod, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  have hnsum : ∀ z, HasSum (fun m => ‖F m z‖) (Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)) := by
    intro z
    simp only [hnorm]
    exact (expand_real (DVar ι a b) _).mul_right _
  have hGc : Continuous G := hG.continuous
  have hFc : ∀ m, Continuous (F m) := by
    intro m
    have h1 := conjMono_continuous m
    have h2 := gq_continuous (a := a) (b := b) c
    simp only [F]
    fun_prop
  have hS : Continuous fun z : VCx ι a b => ∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖ := by
    fun_prop
  have hint : Integrable (fun z => ∑' m, ‖F m z‖) := by
    have e : (fun z => ∑' m, ‖F m z‖) = fun z => Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖) := by
      funext z; exact (hnsum z).tsum_eq
    rw [e]
    refine ((GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix ι a b c hc z₀).const_mul M).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h2 := gq_continuous (a := a) (b := b) c
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hz := hM z
      calc Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)
          ≤ Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * (M * Real.exp (gq c z / 2))) := by
            gcongr
        _ = M * Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
            rw [show (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2
              = (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) + (-gq c z) + gq c z / 2 by ring,
              Real.exp_add, Real.exp_add]
            ring
  have hsumI : HasSum (fun m => ∫ z, F m z) (∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) :=
    hasSum_integral_of_dominated_convergence (fun m z => ‖F m z‖) (fun m => (hFc m).aestronglyMeasurable)
      (fun m => Filter.Eventually.of_forall fun z => le_rfl) (Filter.Eventually.of_forall fun z => (hnsum z).summable)
      hint (Filter.Eventually.of_forall hlim)
  set P : ℝ := ∏ τ, (Real.pi / c τ) ^ (a * b) with hP
  have hFm : ∀ m, ∫ z, F m z = (P : ℂ) * ((m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) := by
    intro m
    simp only [F]
    rw [MeasureTheory.integral_const_mul, GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient ι a b c hc G hG ⟨M, hM⟩ m]
    have hc' : coef m * (((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ)) : ℂ) = m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ) := by
      simp only [coef, Finsupp.prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have : (c k.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hc k.1).ne'
      push_cast
      rw [mul_pow, mul_div_assoc, mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ this, one_pow, one_mul]
    rw [← hc']
    ring
  have hT := (GlobalTheory.T.hasSum_taylorSeries_derivAtOrigin_coordinateSpace ι a b G hG z₀).mul_left (P : ℂ)
  simp only [← hFm] at hT
  have heq := hsumI.unique hT
  rw [heq, ← mul_assoc]
  have h1 : (∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) * P = 1 := by
    rw [hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← mul_pow]
    have : c τ ≠ 0 := (hc τ).ne'
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [show c τ / Real.pi * (Real.pi / c τ) = 1 by field_simp, one_pow]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul]

end GlobalTheory.FockRepr
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch


theorem _root_.GlobalTheory.T.mixedLagrangian_oppositeLagrangian_chart : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) := by
  first | exact @GlobalTheory.FlipMatch.chartOpp_isMixChart | exact GlobalTheory.FlipMatch.chartOpp_isMixChart | (intros; apply GlobalTheory.FlipMatch.chartOpp_isMixChart <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.ChiGrid GlobalTheory.RowReal
open Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.RowReal.WeightsX

open GlobalTheory.SignedHC

theorem mem_listBlock_iff {c x : ℚ} {n : ℕ} : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n ↔ x ∈ TPar.block c n := by
  rw [GlobalTheory.SignedHC.mem_block]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block, List.mem_map, List.mem_range]
  exact ⟨fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩, fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩⟩

theorem pairwise_listBlock (c : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := n)).imp fun {a b} h => ?_
  have : (a : ℚ) < b := by exact_mod_cast h
  linarith

theorem psiPar_eq (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar =
    (num D C τ).a 0 :: ((List.finRange D.R.m).flatMap (fun i : Fin D.R.m =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++ [(num D C τ).a ((i : ℕ) + 1)]) ++
      (List.finRange (D.R.k - 1)).map fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)) := rfl

theorem psiPar_props (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    (rowEntries D C τ).psiPar.Pairwise (· > ·) ∧ ∀ x ∈ (rowEntries D C τ).psiPar, x ∈ (num D C τ).weightX 0 := by
  have hm : (num D C τ).NearMid := num_nearMid D C τ
  have hs : 1 ≤ (num D C τ).s := (odd_sLen D).pos
  have hg : (num D C τ).s < (num D C τ).ga := sLen_lt_gap D C
  have hGm : (num D C τ).m = D.R.m := rfl
  have hGk : (num D C τ).k = D.R.k := rfl
  have hga : (0 : ℚ) < (num D C τ).ga := by exact_mod_cast (by omega : 0 < (num D C τ).ga)
  have hle : ∀ {i j : ℕ}, i ≤ j → (num D C τ).a j ≤ (num D C τ).a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := num D C τ) h]
  have hB : ∀ (i : Fin D.R.m) x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) →
      (num D C τ).a ((i : ℕ) + 1) < x ∧ x < (num D C τ).a ((i : ℕ) + 1) + (num D C τ).ga := fun i x hx =>
    blockC'_between hm hs hg (by omega) (by have := i.2; omega) (mem_listBlock_iff.1 hx)
  have piece : ∀ (i : Fin D.R.m) y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++
      [(num D C τ).a ((i : ℕ) + 1)] → (num D C τ).a ((i : ℕ) + 1) ≤ y ∧ y < (num D C τ).a i := by
    intro i y hy
    rw [(num D C τ).a_eq_succ_add i]
    rcases List.mem_append.1 hy with h | h
    · have := hB i y h; exact ⟨this.1.le, this.2⟩
    · rw [List.mem_singleton] at h; subst h
      exact ⟨le_rfl, by linarith⟩
  have hU : ∀ y ∈ (List.finRange (D.R.k - 1)).map (fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)),
      y ∈ (num D C τ).cloudHalf := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GridData.mem_cloudHalf.2 ⟨(i : ℕ) + 2, by omega, by have := i.2; omega, rfl⟩
  rw [psiPar_eq]
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_cons, List.pairwise_append, List.pairwise_flatMap, List.pairwise_map]
    refine ⟨?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · intro y hy
      rcases List.mem_append.1 hy with h | h
      · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
        have := piece i y h
        linarith [hle (Nat.zero_le (i : ℕ))]
      · have := cloudHalf_lt (hU y h)
        linarith [hle (Nat.zero_le (num D C τ).m)]
    · intro i _
      rw [List.pairwise_append]
      refine ⟨pairwise_listBlock _ _, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      exact (hB i x hx).1
    · refine (List.pairwise_lt_finRange D.R.m).imp fun {i j} hij => ?_
      intro x hx y hy
      have h1 := piece i x hx
      have h2 := piece j y hy
      have h3 : (i : ℕ) + 1 ≤ j := hij
      linarith [hle h3]
    · refine (List.pairwise_lt_finRange (D.R.k - 1)).imp fun {i j} hij => ?_
      have hij' : (i : ℕ) < j := hij
      have := (num D C τ).v_anti ((i : ℕ) + 2) ((j : ℕ) + 2) (by omega) (by omega) (by have := j.2; omega)
      have h' : ((num D C τ).v ((j : ℕ) + 2) : ℚ) < (num D C τ).v ((i : ℕ) + 2) := by exact_mod_cast this
      simp only [GridData.vHalf]; linarith
    · intro x hx y hy
      obtain ⟨i, -, h⟩ := List.mem_flatMap.1 hx
      have h1 := piece i x h
      have h2 := cloudHalf_lt (hU y hy)
      have h3 : (i : ℕ) + 1 ≤ (num D C τ).m := by have := i.2; omega
      linarith [hle h3]
  · intro y hy
    rw [GridData.mem_weightX]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
      rcases List.mem_append.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨(i : ℕ) + 1, by omega, by have := i.2; omega, mem_listBlock_iff.1 h⟩))
      · rw [List.mem_singleton] at h; subst h
        exact Or.inl (GridData.mem_tops.2 ⟨(i : ℕ) + 1, by have := i.2; omega, rfl⟩)
    · exact Or.inr (Or.inl (hU y h))

theorem length_psiPar (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar.length = rankP D D.R.m := by
  rw [length_psi, rowSizes_nR]; simp [rankX]

end GlobalTheory.RowReal.WeightsX

namespace GlobalTheory.RowReal

open GlobalTheory.SignedHC GlobalTheory.RowReal.WeightsX

end GlobalTheory.RowReal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal.BaseWeights

theorem mem_tparBlock {c x : ℚ} {n : ℕ} (h : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n) : x ∈ TPar.block c n := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  exact Finset.mem_image.2 ⟨a, Finset.mem_range.2 (List.mem_range.1 ha), rfl⟩

theorem basePar_sublist {S : Sizes} (P : Entries S) : P.basePar.Sublist P.orderList := by
  have h1 : ∀ l : List (Fin (S.k - 1)),
      (l.map fun i => (P.v i : ℚ)).Sublist (l.flatMap fun i => [(P.v i : ℚ), P.u i]) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.nil_append]
      exact (ih.cons _).cons₂ _
  unfold Entries.basePar Entries.orderList
  exact List.Sublist.append ((h1 _).trans (List.sublist_append_right _ _)) (List.Sublist.refl _)

theorem base_mem_Dpar (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    ∀ x ∈ (rowEntries D C τ).basePar, ∃ s, (x, s) ∈ (Ptw D).Dpar D.R.m τ := by
  have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.2 D.R.m_even
  obtain ⟨hv, hb, he⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  intro x hx
  simp only [Entries.basePar, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.mem_finRange,
    true_and] at hx
  unfold TPar.Dpar
  rcases hx with ⟨i, rfl⟩ | ⟨j, h | h⟩
  · refine ⟨true, Finset.mem_image.2 ⟨((Ptw D).v τ i, true), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    · simp only [hodd, if_false, add_zero]
      exact Prod.ext (hv i) rfl
  · refine ⟨decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m)), Finset.mem_image.2 ⟨(-(Ptw D).b τ j, decide ((j : ℕ) ≤ D.R.m ∨ Even ((j : ℕ) - D.R.m))), ?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    · simp only [hodd, if_false, add_zero]
      refine Prod.ext ?_ rfl
      rw [h]
      show -(D.hc τ).b j = _
      rw [hb j]; rfl
  · refine ⟨true, Finset.mem_image.2 ⟨(x, true), ?_, ?_⟩⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, j.2⟩, ?_⟩)
      refine Finset.mem_image.2 ⟨x, ?_, rfl⟩
      have hx' := mem_tparBlock h
      have : (-(Ptw D).e τ j) = -(((rowEntries D C τ).e j : ℤ) : ℚ) := by
        show -(D.hc τ).e j = _
        rw [he j]; rfl
      rw [this]
      exact hx'
    · simp only [hodd, if_false, add_zero]

end GlobalTheory.RowReal.BaseWeights

namespace GlobalTheory.RowReal

open GlobalTheory.RowReal.BaseWeights

theorem hw_basePar_eq_neg_lowK : ∀ (D : D7) (C : ℝ)
    (M : Formalism.IndefR.Mult.DSModel D.sp.X' (Formalism.IndefR.Mult.parB (Ptw D) D.R.m)) (τ : D.what₂.Tau)
    (i : Fin D.sp.X'.rank),
    (hw (rowEntries D C τ).basePar i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i) := by
  intro D C M τ i
  have hlen : (rowEntries D C τ).basePar.length = D.sp.X'.rank := by
    rw [length_base, D.sp.X'_rank]
    simp [Sizes.nC, rowSizes, Ranks.rankX', Ranks.r]
  have hε : M.ε τ = Formalism.MainNotions.S.allPos _ := funext fun a => GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) M τ a
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hqa : StrictAnti q := fun a b h => by
    have := hanti h
    rw [hq, hq] at this
    exact_mod_cast this
  have hinj : Function.Injective fun a => -q a := fun a b h => hqa.injective (neg_injective h)
  have hE : (Finset.univ.image fun a => -q a).card = D.sp.X'.rank := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  have hpw := (rowEntries_good D C τ).order.sublist (basePar_sublist (rowEntries D C τ))
  let f : Fin D.sp.X'.rank → ℚ := fun j => (rowEntries D C τ).basePar[(j : ℕ)]'(by rw [hlen]; exact j.2)
  have hf : StrictAnti f := fun a b hab => List.pairwise_iff_getElem.1 hpw _ _ _ _ hab
  have hfm : ∀ j, f j ∈ Finset.univ.image fun a => -q a := by
    intro j
    obtain ⟨s, hs⟩ := base_mem_Dpar D C τ _ (List.getElem_mem (by rw [hlen]; exact j.2))
    have h2 : (-(f j), s) ∈ Formalism.IndefR.Mult.parB (Ptw D) D.R.m τ := Finset.mem_image.2 ⟨_, hs, rfl⟩
    rw [hS] at h2
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h2
    refine Finset.mem_image.2 ⟨a, Finset.mem_univ _, ?_⟩
    have h3 := congrArg Prod.fst ha
    simp only at h3
    rw [h3, neg_neg]
  let g : Fin D.sp.X'.rank → ℚ := fun j => -q j.rev
  have hg : StrictAnti g := fun a b hab => by
    simp only [g, neg_lt_neg_iff]
    exact hqa (Fin.rev_lt_rev.2 hab)
  have hgm : ∀ j, g j ∈ Finset.univ.image fun a => -q a := fun j => Finset.mem_image.2 ⟨j.rev, Finset.mem_univ _, rfl⟩
  have hfg : f = g := (GlobalTheory.SignedHC.descEnum_unique hE hf hfm).symm.trans (GlobalTheory.SignedHC.descEnum_unique hE hg hgm)
  have hi : (i : ℕ) < (rowEntries D C τ).basePar.length := by rw [hlen]; exact i.2
  have key : (rowEntries D C τ).basePar[(i : ℕ)] = -q i.rev := congrFun hfg i
  have h1 := hw_base _ i hi
  have hl : (((rowEntries D C τ).basePar.length : ℕ) : ℚ) = (D.sp.X'.rank : ℚ) := by rw [hlen]
  rw [hl, key] at h1
  rw [hε, GlobalTheory.ConjTypeW.lowK_allPos, hq]
  have h4 : (hw (rowEntries D C τ).basePar i : ℝ) = (((hw (rowEntries D C τ).basePar i : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h4, h1, Fin.val_rev]
  have h5 : (i : ℕ) + 1 ≤ D.sp.X'.rank := i.2
  rw [Nat.cast_sub h5]
  push_cast
  ring

end GlobalTheory.RowReal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.exists_isRigIso_of_baseChange' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (k : ℤ), IsBC φ f g → IsMonHom f → (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj w w' g.left) k β) → ∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) k β := by
  first | exact @GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange | exact GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange | (intros; apply GlobalTheory.RigIsoDescent.exists_isRigIso_of_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.isProper_model_of_extends_fibreIsogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  first | exact @GlobalTheory.HkIntegral.isProper_of_ext | exact GlobalTheory.HkIntegral.isProper_of_ext | (intros; apply GlobalTheory.HkIntegral.isProper_of_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.lie_image_compatible_with_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (p : ℕ) (v u : Sp (DualNumber K) ⟶ Xo.univ.t.G.left), IsBC φ f g → IsTanAt x v → (IsLieImageH p f.left v u ↔ IsLieImageH p g.left (spMap (dualMap φ) ≫ v) (spMap (dualMap φ) ≫ u)) := by
  first | exact @GlobalTheory.LieImageBC.isLieImageH_baseChange | exact GlobalTheory.LieImageBC.isLieImageH_baseChange | (intros; apply GlobalTheory.LieImageBC.isLieImageH_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.exists_pull_isTranslSum_of_isThetaTrace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K), IsPair (p ^ 2) f f' → (∀ i, s'.f i = scal x' a i * s₀.f i) → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s' → ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  first | exact @GlobalTheory.HkIntegral.thetaTrace_isTranslSum | exact GlobalTheory.HkIntegral.thetaTrace_isTranslSum | (intros; apply GlobalTheory.HkIntegral.thetaTrace_isTranslSum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

theorem _root_.GlobalTheory.T.exists_ext_pair_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x), IsMonHom f → IsMonHom f' → ∃ (F : G.G ⟶ G'.G) (F' : G'.G ⟶ G.G), IsMonHom F ∧ IsMonHom F' ∧ Ext m₁ m₂ n₁ n₂ f F ∧ Ext n₁ n₂ m₁ m₂ f' F' ∧ (∀ N : ℕ, f ≫ f' = 𝟙 _ ^ N → F ≫ F' = 𝟙 _ ^ N) ∧ (∀ N : ℕ, f' ≫ f = 𝟙 _ ^ N → F' ≫ F = 𝟙 _ ^ N) ∧ (Lin f → ∀ a, G.act.act a ≫ F = F ≫ G'.act.act a) ∧ (Lin f' → ∀ a, G'.act.act a ≫ F' = F' ≫ G.act.act a) := by
  first | exact @GlobalTheory.HkIntegral.exists_ext_pair | exact GlobalTheory.HkIntegral.exists_ext_pair | (intros; apply GlobalTheory.HkIntegral.exists_ext_pair <;> assumption)
end
