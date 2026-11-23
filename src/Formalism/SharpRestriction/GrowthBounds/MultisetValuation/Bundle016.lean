module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle014
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle015
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle002
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def PriceBoundLargePrimes (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.Pr1 → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      L.sc.p0 D.R.k ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

def PriceBoundSmallPrimes : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem priceBound_of_largePrimes_of_smallPrimes (C₀ : ℝ) (h1 : PriceBoundLargePrimes C₀) (h2 : PriceBoundSmallPrimes) : PriceBound C₀ := by
  intro D L X Y K hK1 hK2 hS hT hL u w hg _ t0 ht0 j hj
  rcases le_or_gt (L.sc.p0 D.R.k) ((D.what₂.places.resChar w : ℕ) : ℝ) with h | h
  · exact h1 D L X Y K hK1 hS hT hL u w hg h t0 ht0 j hj
  · exact h2 D L X Y K hK2 hS hT hL u w hg h t0 ht0 j hj

variable {n' k1 : ℕ}

theorem ne_abs (t r j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A Bt : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ Bt)
    (h : ∀ s : Fin n', IsOddPos s → (r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      A + (if s ∈ TT then Bt else 0)) :
    Pr t r lam0 w j ≤ n' * A + TT.card * Bt + (n' : ℝ) * r * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      ((r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  have h2 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) ≤
      ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => by split_ifs <;> linarith)
  have h3 : ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) = n' * A + TT.card * Bt := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  linarith

theorem price_sum_single_edge (t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A : ℝ) (E : Fin n' → ℝ) (hA : 0 ≤ A)
    (h : ∀ s : Fin n', IsOddPos s → ((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      if s ∈ TT then E s else A) :
    Pr t 1 lam0 w j ≤ ∑ s ∈ TT.filter IsOddPos, E s + n' * A + (n' : ℝ) * ((1 : ℕ) : ℝ) * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      (((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (if s ∈ TT then E s else A) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  rw [Finset.sum_ite] at h1
  have e1 : (univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∈ TT) = TT.filter IsOddPos := by
    ext s; simp [and_comm]
  rw [e1, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : (((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT)).card : ℝ) ≤ n' := by
    have := Finset.card_le_univ ((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT))
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 hA
  exact add_le_add (le_trans h1 (add_le_add le_rfl h3)) le_rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser IsLawOfLog cob at1 in3 d1 swap2 DivAB BetaHyp)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable (p : ℕ) [hp : Fact p.Prime]

theorem sx_X_dvd_lX {σ : Type} (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) ∣ sx_lX p i := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (sx_logF_const p)
  refine ⟨PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) g, ?_⟩
  unfold sx_lX
  rw [hg, PowerSeries.subst_mul hs, PowerSeries.subst_X hs]

theorem sx_divAB {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) : DivAB (inParam p be) := by
  intro n hn
  have hdvd : ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ inParam p be := by
    intro i
    have hb : (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 p)) ∣ be := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      by_contra hne
      have := h.ab m hne
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue] at hm
        omega
      · simp only [Fin.mk_one, Fin.isValue] at hm
        omega
    obtain ⟨g, hg⟩ := hb
    rw [hg, sx_inParam_mul, sx_inParam_X]
    exact Dvd.dvd.mul_right (sx_X_dvd_lX p i) _
  rcases hn with h0 | h1
  · exact MvPowerSeries.X_dvd_iff.1 (hdvd 0) n h0
  · exact MvPowerSeries.X_dvd_iff.1 (hdvd 1) n h1

variable {p}

theorem sx_two {τ : Type} {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem sx_log_law {F : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) {τ : Type} (u v : MvPowerSeries τ (K0 p))
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![u, v] F) (logF p) =
      PowerSeries.subst u (logF p) + PowerSeries.subst v (logF p) := by
  have hs : MvPowerSeries.HasSubst ![u, v] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩)
  have hc : PowerSeries.subst F (lgF (K0 p) p) = at1 0 (lgF (K0 p) p) + at1 1 (lgF (K0 p) p) := by
    have h0 := hF.2.2
    unfold cob at h0
    linear_combination h0
  have e := congrArg (MvPowerSeries.subst ![u, v]) hc
  rw [sx_subst_ps p hs hF.1, MvPowerSeries.subst_add hs, at1, at1,
    sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 0), sx_subst_ps p hs (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs] at e
  rw [sx_logF_eq]
  simpa using e

theorem sx_law_const {F : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) {τ : Type} (u v : MvPowerSeries τ (K0 p))
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![u, v] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨hu, hv⟩))
    (Fin.forall_fin_two.2 ⟨hu, hv⟩) hF.1

theorem param_substitution_pair {τ : Type} [Finite τ] (be : MvPowerSeries (Fin 2) (K0 p)) (x y x' y' : MvPowerSeries τ (K0 p))
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (hx' : MvPowerSeries.constantCoeff x' = 0) (hy' : MvPowerSeries.constantCoeff y' = 0)
    (ex : PowerSeries.subst x' (logF p) = inParam p x) (ey : PowerSeries.subst y' (logF p) = inParam p y) :
    inParam p (sub2 p be x y) = MvPowerSeries.subst ![x', y'] (inParam p be) := by
  show inParam p (MvPowerSeries.subst ![x, y] be) = _
  apply sx_inParam_subst
  · intro i
    fin_cases i
    · simpa using hx
    · simpa using hy
  · intro i
    fin_cases i
    · simpa using hx'
    · simpa using hy'
  · intro i
    fin_cases i
    · simpa using ex
    · simpa using ey

theorem sx_eX {τ : Type} [Finite τ] (i : τ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries τ (K0 p)) (logF p) = inParam p (MvPowerSeries.X i) := by
  rw [sx_inParam_X]
  rfl

theorem sx_cX {τ : Type} (i : τ) : MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries τ (K0 p)) = 0 :=
  MvPowerSeries.constantCoeff_X i

theorem biadditive_first_variable {F be : MvPowerSeries (Fin 2) (K0 p)} (hF : IsLawOfLog p F) (h : BeProp p be) :
    Formalism.InvariantFactorPaths.G7.Simeq (d1 F (inParam p be)) 0 := by
  have hX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) (K0 p)) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hin3 : MvPowerSeries.constantCoeff (in3 F) = 0 := sx_law_const hF _ _ (hX 0) (hX 1)
  have h01 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p)) = 0 := by
    rw [map_add (f := _), hX 0, hX 1, add_zero]
  have ex : PowerSeries.subst (in3 F) (logF p) =
      inParam p (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) (K0 p)) := by
    rw [in3, sx_log_law hF _ _ (hX 0) (hX 1), sx_inParam_add, ← sx_eX, ← sx_eX]
  have e1 := param_substitution_pair be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) (in3 F) (MvPowerSeries.X 2)
    h01 (hX 2) hin3 (hX 2) ex (sx_eX 2)
  have e2 := param_substitution_pair be (MvPowerSeries.X 0) (MvPowerSeries.X 2) (MvPowerSeries.X 0) (MvPowerSeries.X 2)
    (hX 0) (hX 2) (hX 0) (hX 2) (sx_eX 0) (sx_eX 2)
  have e3 := param_substitution_pair be (MvPowerSeries.X 1) (MvPowerSeries.X 2) (MvPowerSeries.X 1) (MvPowerSeries.X 2)
    (hX 1) (hX 2) (hX 1) (hX 2) (sx_eX 1) (sx_eX 2)
  have key : d1 F (inParam p be) = inParam p
      (sub2 p be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) -
        sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2) -
        sub2 p be (MvPowerSeries.X 1) (MvPowerSeries.X 2)) := by
    rw [th_inParam_sub, th_inParam_sub, e1, e2, e3]
    rfl
  rw [key]
  first
    | exact equiv_zero_of_integralExp p (integralExp_param_of_equiv_zero p h.add1)
    | exact equiv_zero_of_integralExp (integralExp_param_of_equiv_zero p h.add1)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
