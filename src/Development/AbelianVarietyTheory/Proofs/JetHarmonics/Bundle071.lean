module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
public import Development.AutomorphicArithmetic.OrbitLabellings.FnumEqRhoMulSumOfDemandRatioLe
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle060
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ContentValue

lemma lpF_nonneg (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (hl : 2 ≤ l) (hD : ∀ a, 0 ≤ D a) : 0 ≤ lpF l d D := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hS : 0 ≤ ∑ a, D a := Finset.sum_nonneg fun a _ => hD a
  have hq : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hg : 0 ≤ (l : ℝ) / ((l : ℝ) ^ 2 - 1) * ∑ a, D a := by positivity
  unfold lpF
  rw [sub_nonneg]
  refine Real.sSup_le ?_ hg
  rintro t ⟨x, h0, h1, h2, rfl⟩
  have := (GlobalTheory.FlowProgramme.duality l d D hl x ⟨h0, fun a i h => ?_, h2⟩).1
  · have ht : 0 ≤ ∑ s, ∑ i ∈ Finset.range d, x s i :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => h0 s i
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    nlinarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ l - 1 by linarith)]
  · by_contra hc
    refine h (h1 a i ?_)
    by_cases ho : Odd i
    · exact Or.inr (not_lt.1 fun hh => hc ⟨ho, hh⟩)
    · exact Or.inl ho

lemma two_le_ordP (N : NumDatum) (l : ℕ) (hc : Inert N l) (hn : ¬ PhiC N l) : 2 ≤ N.ordP l := by
  unfold NumDatum.ordP
  split
  · have := addOrderOf_pos (2 • N.hP l)
    omega
  · rename_i hs
    have h0 : N.hP l ≠ 0 := fun h => hn ⟨Or.resolve_right hc hs, h⟩
    have h1 : addOrderOf (N.hP l) ≠ 1 := fun h => h0 (AddMonoid.addOrderOf_eq_one_iff.1 h)
    have := addOrderOf_pos (N.hP l)
    omega

lemma rho_bound (k w l : ℝ) (hk : 1 ≤ k) (hw : 0 ≤ w) (hl : 2 ≤ l) :
    (k - 1) * w / (l ^ 2 - 1) ≤ 2 * (k * w / l ^ 2) := by
  have h4 : 4 ≤ l ^ 2 := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : 0 ≤ k * w := by positivity
  nlinarith [mul_nonneg h1 (show 0 ≤ l ^ 2 - 2 by linarith), mul_nonneg hw (show 0 ≤ l ^ 2 by linarith)]

theorem main : ∀ (N : NumDatum) (j l : ℕ), l.Prime → l ∉ N.H.small → l ≠ N.q → l ≠ N.d → l ≠ N.g 0 → l ≠ N.g 1 → (∀ z, 0 ≤ N.w j z) → (∀ z z', N.w j z' ≤ N.sc.X'' N.R.n * N.w j z) →
  0 ≤ N.FjP j l ∧ (Inert N l ∨ N.cls l = PrimeClass.splitK) ∧ ParOK (parOf N j l) ∧
  (PhiC N l → ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ∧
  (Inert N l → ¬ PhiC N l → ∀ Z : Finset (RPl N.R), RF.IsReps (parOf N j l) Z →
    (∑ z ∈ Z, Fnum l (N.ordP l) fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) := by
  classical
  intro N j l hp h2 hq hd hg0 hg1 hw hr
  have hl : 2 ≤ l := hp.two_le
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hk : (1 : ℝ) ≤ N.R.k := by
    have := N.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ N.R.k)
  have hq2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hS : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hw z
  have hcls : Inert N l ∨ N.cls l = PrimeClass.splitK := by
    unfold Inert NumDatum.cls primeClass
    rw [if_neg h2, if_neg hq, if_neg hd]
    split_ifs <;> simp
  have hnd : N.cls l ≠ PrimeClass.ramD := by
    rcases hcls with (h | h) | h <;> rw [h] <;> simp
  have hF : N.FjP j l = if Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n then N.FInert j l else 0 := by
    unfold NumDatum.FjP
    rw [if_neg (by tauto), if_neg hnd]
    by_cases h : Inert N l ∧ (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [if_pos h]; exact if_pos h
    · rw [if_neg h]; exact if_neg h
  have hD : ∀ z, 0 ≤ ((N.R.k : ℝ) - 1) * N.w j z := fun z => mul_nonneg (by linarith) (hw z)
  have hI : 0 ≤ N.FInert j l := by
    unfold NumDatum.FInert
    split_ifs
    · exact Finset.sum_nonneg fun z _ => div_nonneg (hD z) hq2.le
    · exact div_nonneg (Finset.sum_nonneg fun z _ => lpF_nonneg _ _ _ hl fun a => hD _) (Nat.cast_nonneg _)
  have hb := rho_bound N.R.k _ l hk hS hl'
  refine ⟨?_, hcls, ?_, ?_, ?_⟩
  · rw [hF]
    split_ifs
    · exact hI
    · exact le_rfl
  · have h3 := N.R.m_add_three_le_k
    have h4 := N.R.two_le_m
    refine ⟨?_, ?_, h3, ?_, ?_⟩
    · show Fintype.card (RPl N.R) = N.R.f
      have := Formalism.HC.Frame.card_A N.R.toFrame
      simpa [Ranks.f, Ranks.n] using this
    · show 1 ≤ N.R.m
      omega
    · show N.R.r = N.R.k - 1 + N.R.m
      unfold Ranks.r
      omega
    · show 0 ≤ N.Sc + N.eta
      unfold NumDatum.Sc NumDatum.eta
      positivity
  · intro hc
    have hi : Inert N l := Or.inl hc.1
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      unfold NumDatum.FInert
      rw [if_pos (show N.cls l = PrimeClass.inertClass ∧ N.hP l = 0 from hc), ← Finset.sum_div, ← Finset.mul_sum]
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      exact hb
  · intro hi hc Z hZ
    have hZ' : Formalism.L2.FormalSeriesBounds.IsReps N l Z := hZ
    by_cases hX : (l : ℝ) ≤ N.sc.X'' N.R.n
    · rw [hF, if_pos ⟨hi, hX⟩, if_neg (not_lt.2 hX), add_zero]
      exact (GlobalTheory.LevelsOrbits.fInertReps N j l Z hZ' hi hc).1.ge
    · rw [hF, if_neg (fun h => hX h.2), if_pos (not_le.1 hX), zero_add]
      refine le_trans (le_of_eq ?_) hb
      have ho2 := two_le_ordP N l hi hc
      have hl3 : 3 ≤ l := by
        have := ne_two_of_not_small h2
        omega
      have hbal : ∀ z z', N.w j z' ≤ l * N.w j z := fun z z' =>
        (hr z z').trans (mul_le_mul_of_nonneg_right (not_le.1 hX).le (hw z))
      rw [GlobalTheory.LevelsOrbits.sum_reps N l Z hZ' (N.w j), Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [UpperTheory.fnum_eq_rho_mul_sum_of_demand_ratio_le l (N.ordP l) hl3 ho2 _ (fun a => hD _) (fun a a' => ?_), ← Finset.mul_sum]
      · unfold Formalism.IncomingBounds.rho
        ring
      · have := mul_le_mul_of_nonneg_left (hbal (N.pos l z a.val) (N.pos l z a'.val))
          (show (0 : ℝ) ≤ N.R.k - 1 by linarith)
        linarith

end GlobalTheory.ContentValue
end

section

open Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth
open scoped BigOperators

namespace GlobalTheory.SplitPackageBound

theorem sum_reps {M : Type} [AddCommMonoid M] (P : RF.Par) (Z : Finset P.Pl)
    (h : RF.IsReps P Z) (W : P.Pl → M) :
    ∑ z ∈ Z, ∑ a, RF.alongOrb P z W a = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩
      ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) :
    Z.card * Fintype.card (ZMod P.d) = Fintype.card P.Pl := by
  have := sum_reps P Z h (fun _ => (1 : ℕ))
  simpa [RF.alongOrb] using this

theorem deg_le {d : ℕ} [NeZero d] (rk : Fin 2 → ZMod d → ℕ) (n K : ℕ)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    (∑ a, monDeg K (rk 0 a) (fun k => if k = n then 0 else ga 0 a k)) +
      (∑ a, monDeg K (rk 1 a) (ga 1 a)) ≤ RF.restDeg (fun _ => 0) n ga K := by
  have hsub : ∀ r, Finset.Icc 1 (min K r) ⊆ Finset.Icc 1 K := fun r =>
    Finset.Icc_subset_Icc_right (min_le_left _ _)
  unfold RF.restDeg monDeg
  rw [Fin.sum_univ_two]
  refine Nat.add_le_add (Finset.sum_le_sum (N := ℕ) fun a _ => ?_)
    (Finset.sum_le_sum (N := ℕ) fun a _ => ?_)
  · refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = n <;> simp [hk]
  · refine le_trans (Finset.sum_le_sum_of_subset (M := ℕ) (hsub _)) (le_of_eq ?_)
    simp

theorem nu_le (hC : RF.CHSupply) (hM : RF.MONSupply) (P : RF.Par) (l : ℕ) (C1 : ℝ) (hP : ParOK P)
    (hl : l.Prime) (Pk : RF.PkgSplit P l C1) :
    Pk.ν ≤ (∑ z, (Pk.W z : ℝ)) * P.m / ((l : ℝ) - 1) + Pk.rest / ((l : ℝ) - 1) := by
  obtain ⟨R, Z, hZ, hbig, ga, W, nW, T, θ, rest, ν, hW, hr, hD, hV⟩ := Pk
  dsimp only
  have hVl := R.hVl
  have hl' : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    linarith
  have hk := hP.mk_le
  have hrr := hP.r_eq
  let e0 : P.Pl → ZMod P.d → ℕ → ℕ := fun z a k =>
    if k = P.k - 1 then 0 else ga z 0 a k
  have := hV (fun z =>
    (RF.GlobalTheory.mon 0 (e0 z) P.r, (RF.monDegAll (R.X z) 0 (e0 z) P.r : ℝ) / ((R.V.l : ℝ) - 1)) ::
    (RF.GlobalTheory.mon 1 (ga z 1) P.r, (RF.monDegAll (R.X z) 1 (ga z 1) P.r : ℝ) / ((R.V.l : ℝ) - 1)) ::
    (Finset.univ : Finset (ZMod P.d)).toList.map fun a =>
      (RF.GlobalTheory.ch 0 a (RF.alongOrb P z W a),
        ((RF.alongOrb P z W a : ℕ) : ℝ) * ((R.X z).m / ((R.V.l : ℝ) - 1)))) ?_ ?_ ?_
  · refine this.trans ?_
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, hVl]
    rw [hW.rest_eq, ← sum_reps P Z hZ (fun z => (W z : ℝ)), Finset.sum_mul, Finset.sum_div,
      Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z hz => ?_
    rw [(R.hn z).2, ← add_assoc, add_comm, ← Finset.sum_mul, mul_div_assoc, ← add_div]
    refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hl'.le)
    have h := deg_le (R.X z).rkF (P.k - 1) P.r (ga z)
    simp only [Nat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
    exact_mod_cast h
  · intro z hz p hp
    simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨a, -, rfl⟩
    · exact (hM R.C R.V _ _ _ (R.X z) (R.F z) 0 _ _).1
    · exact (hM R.C R.V _ _ _ (R.X z) (R.F z) 1 _ _).1
    · exact (hC R.C R.V _ _ _ (R.X z) (R.F z) 0 a (hbig z hz a) _).2 (hbig z hz)
  · simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ]
    have hc := card_reps P Z hZ
    rw [hP.card] at hc
    have hpos : 1 ≤ Fintype.card (ZMod P.d) := Fintype.card_pos
    calc _ ≤ ∑ z ∈ Z, 3 * P.r * Fintype.card (ZMod P.d) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have : (R.X z).n ≤ P.r := by rw [(R.hn z).1]; omega
          nlinarith
      _ = 3 * P.r * P.f := by
          rw [Finset.sum_const, smul_eq_mul, ← hc]; ring
      _ ≤ nW := by nlinarith
  · intro z hz g a k
    simp only [List.map_cons, List.sum_cons, List.map_map, Finset.sum_map_toList,
      Function.comp_def, RF.GlobalTheory.wt]
    obtain ⟨hn, hm⟩ := R.hn z
    have hb := hbig z hz
    have hm' : (R.X z).j + (R.X z).j' = P.m := hm
    have h0 : (R.X z).rkF 0 a = (R.X z).n + (R.X z).j := (R.X z).rk_big 0 a (hb a)
    have h1 : (R.X z).rkF 1 a = (R.X z).j' :=
      (R.X z).rk_small 1 a fun h => ((R.X z).big_compl 0 a).1 (by simpa using h) (hb a)
    have hs := hW.supp z hz g a k
    have hmain := hW.main z hz a
    fin_cases g
    · simp only [Fin.zero_eta, true_and, zero_ne_one, false_and, if_false, zero_add] at hs hmain ⊢
      by_cases hkn : k = P.k - 1
      · subst hkn
        rw [hmain]
        simp [e0, hn]
      · have : k ≠ (R.X z).n := by omega
        by_cases hz0 : ga z 0 a k = 0
        · simp [e0, hkn, this, hz0]
        · have h2 := hs hz0
          rw [if_pos (by omega)]
          simp [e0, hkn, this]
    · simp only [Fin.mk_one, true_and, one_ne_zero, false_and, if_false, zero_add,
        Finset.sum_const_zero, add_zero] at hs ⊢
      by_cases hz0 : ga z 1 a k = 0
      · simp [hz0]
      · have h2 := hs hz0
        rw [if_pos (by omega)]

theorem splitBd_of_supplies (hC : RF.CHSupply) (hM : RF.MONSupply) : SplitBd := by
  intro C1 hC1
  refine ⟨2 * (1 + 2 * C1), by positivity, fun P l hP hl Pk => ?_⟩
  have hν := nu_le hC hM P l C1 hP hl Pk
  have hD := Pk.deg
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl' : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hT : 0 ≤ Pk.T := le_trans zero_le_one hD.T_one
  have hSE := hP.SE_nonneg
  have h1 : Pk.T * ∑ z, (Pk.W z : ℝ) ≤ ∑ z, P.w z + P.f * (C1 * P.SE) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun z _ => hD.TW_hi z).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hP.card, nsmul_eq_mul]
  have hw : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (hD.w_pos z).le
  have hm : (0 : ℝ) ≤ P.m := Nat.cast_nonneg _
  have hmk : (P.m : ℝ) ≤ P.k := by exact_mod_cast (by have := hP.mk_le; omega : P.m ≤ P.k)
  have hf : (0 : ℝ) ≤ P.f := Nat.cast_nonneg _
  set A : ℝ := P.m * ∑ z, P.w z with hA
  set B : ℝ := P.f * P.k * P.SE with hB
  have hA0 : 0 ≤ A := mul_nonneg hm hw
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hf (Nat.cast_nonneg _)) hSE
  have h3 : Pk.T * ((∑ z, (Pk.W z : ℝ)) * P.m + Pk.rest) ≤ (1 + 2 * C1) * (A + B) := by
    have e1 := mul_le_mul_of_nonneg_right h1 hm
    have e2 : P.f * (C1 * P.SE) * P.m ≤ C1 * B := by
      have := mul_le_mul_of_nonneg_left hmk (mul_nonneg hf (mul_nonneg hC1 hSE))
      calc _ ≤ _ := this
        _ = _ := by rw [hB]; ring
    have e3 := hD.rest_le
    have e4 := mul_nonneg hC1 hA0
    nlinarith
  have h4 : 0 ≤ (1 + 2 * C1) * (A + B) := by positivity
  refine (mul_le_mul_of_nonneg_left hν hT).trans ?_
  rw [← add_div, ← mul_div_assoc, ← mul_div_assoc]
  refine (div_le_div_of_nonneg_right h3 hl'.le).trans ?_
  rw [div_le_div_iff₀ hl' (by linarith)]
  nlinarith

end GlobalTheory.SplitPackageBound

theorem GlobalTheory.GoodDepth.splitBd : SplitBd :=
  GlobalTheory.SplitPackageBound.splitBd_of_supplies GlobalTheory.CharBlock.chSupply.2 GlobalTheory.T.monomialBlock_supply_both_typings.2
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivPow

variable {V : Type} [CommRing V]

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (g : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) =
    Spec.map (CommRingCat.ofHom ((g.comp f : A →ₐ[V] C) : A →+* C))
  rw [← Spec.map_comp]
  rfl

theorem jet_ext {κ : Type} {m : ℕ} {B : Type} [CommRing B] [Algebra V B] (f g : Jet V κ m →ₐ[V] B)
    (h : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) = g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

theorem jetCopy_X {n d m : ℕ} (i : Fin n) (p : Fin 1 × Fin d) :
    (jetCopy d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, p.2)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun p : Fin 1 × Fin d =>
    (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) V)) (MvPolynomial.X p : MvPolynomial _ V)) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i : MvPolynomial κ V) = 0
  rw [MvPolynomial.aeval_X]

theorem jetTrunc_mk {κ : Type} {m : ℕ} (p : MvPolynomial κ V) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

theorem zV_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n d : ℕ} (pG : IsPowGrp G' G n)
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) (i : Fin n) :
    zV pG xT m ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m i) ≫ xT m :=
  pG.lim.fac _ ⟨i⟩

theorem pow_ext {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)}
    (f g : T ⟶ G') (h : ∀ i, f ≫ pG.pr i = g ≫ pG.pr i) : f = g :=
  pG.lim.hom_ext fun i => h i.as

theorem one_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)} (i : Fin n) :
    (1 : T ⟶ G') ≫ pG.pr i = 1 := by
  haveI := pG.hom i
  exact MonObj.one_comp _

end GlobalTheory.PowGerm.UnivPow

namespace GlobalTheory.PowGerm
open UnivPow

theorem univPow : UnivPowSt := by
  intro V _ G G' _ _ n d pG xT ⟨hT, hA, hU⟩
  refine ⟨fun m => pow_ext pG _ _ fun i => ?_, fun m => pow_ext pG _ _ fun i => ?_, ?_⟩
  · rw [Category.assoc, zV_pr, zV_pr, ← hT m, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetCopy_X, jetTrunc_mk, jetTrunc_mk, jetCopy_X]
  · rw [Category.assoc, zV_pr, one_pr, ← hA m, ← Category.assoc, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
  · intro A _ _ aug m hm y hy
    have hi : ∀ i : Fin n, ∃! ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
        aug.comp ψ = jetAug ∧ y ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ xT m := fun i =>
      hU A aug m hm (y ≫ pG.pr i) (by rw [← Category.assoc, hy, one_pr])
    choose ψ hψ hψu using hi
    let a : Fin n × Fin d → A := fun p => ψ p.1 (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))
    have ha : ∀ p, aug (a p) = 0 := fun p => by
      have := congrArg (fun f : Jet V (Fin 1 × Fin d) m →ₐ[V] V =>
        f (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))) (hψ p.1).1
      simp only [AlgHom.comp_apply, jetAug_X] at this
      exact this
    have hsp : Ideal.span (Set.range fun p => (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A)
        (MvPolynomial.X p)) ^ (m + 1) = ⊥ := by
      apply le_bot_iff.1
      rw [← hm]
      apply Ideal.pow_right_mono
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      simp only [MvPolynomial.aeval_X]
      exact ha p
    let Ψ : Jet V (Fin n × Fin d) m →ₐ[V] A := liftJet (MvPolynomial.aeval a) hsp
    have hΨ : ∀ p, Ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = a p := fun p => by
      show (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A) (MvPolynomial.X p) = a p
      rw [MvPolynomial.aeval_X]
    have hc : ∀ i, Ψ.comp (jetCopy d m i) = ψ i := fun i => by
      apply jet_ext
      rintro ⟨u, j⟩
      obtain rfl : u = 0 := Subsingleton.elim _ _
      rw [AlgHom.comp_apply, jetCopy_X, hΨ]
    refine ⟨Ψ, ⟨?_, pow_ext pG _ _ fun i => ?_⟩, ?_⟩
    · apply jet_ext
      intro p
      rw [AlgHom.comp_apply, hΨ, ha, jetAug_X]
    · rw [Category.assoc, zV_pr, ← Category.assoc, homAt_comp, hc]
      exact (hψ i).2
    · rintro Φ ⟨h1, h2⟩
      have hd : ∀ i, Φ.comp (jetCopy d m i) = ψ i := fun i => by
        apply hψu i
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, h1]
          apply jet_ext
          intro p
          rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
        · rw [h2, Category.assoc, zV_pr, ← Category.assoc, homAt_comp]
      apply jet_ext
      rintro ⟨i, j⟩
      rw [hΨ]
      show _ = ψ i _
      rw [← hd i, AlgHom.comp_apply, jetCopy_X]

end GlobalTheory.PowGerm
end
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.sum_normSq_projections_tensor_unitary_gl_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.sum_normSq_proj_single_le | exact GlobalTheory.sum_normSq_proj_single_le | (intros; apply GlobalTheory.sum_normSq_proj_single_le <;> assumption)
end
