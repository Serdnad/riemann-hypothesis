module

public import Formalism.RealPlaceAnalysis.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelGenA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Pre

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def preUnits (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V)) : Fin n → Fin n → Module.End ℂ V :=
  fun a b => ((dτ (Matrix.single a b 1) : V →L[ℂ] V) : Module.End ℂ V)

variable [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
  (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)


include hcont hder in
theorem pre_kRel : Formalism.REAL.KRel ε (preUnits dτ) := by
  intro a b c d hab hcd
  have hbr := pre_dτ_bracket_single τ dτ hder hab hcd
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1 h2; simp [Matrix.single_mul_single_same]
    · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
    · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
    · simp [Matrix.single_mul_single_of_ne, Matrix.single_mul_single_of_ne, h1, h2]
  rw [hm] at hbr
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun F : V →L[ℂ] V => F x) hbr
  have e : ∀ A B : V →L[ℂ] V, (A * B) x = A (B x) := fun _ _ => rfl
  simp only [_root_.sub_apply, e, map_sub] at hx
  simp only [preUnits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
  rw [hx]
  split_ifs <;> simp

include hcont hder in
theorem pre_kUnit : Formalism.REAL.KUnit ε (preUnits dτ) := by
  intro a b hab x y
  show ⟪dτ (Matrix.single a b 1) x, y⟫_ℂ = ⟪x, dτ (Matrix.single b a 1) y⟫_ℂ
  rw [← pre_star_dτ_single τ dτ hder hab, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem pre_dτ_stable_of_kStable (W : Submodule ℂ V) (hW : Formalism.REAL.KStable ε (preUnits dτ) W) :
    ∀ Y, inK ε Y → ∀ v ∈ W, dτ Y v ∈ W := by
  intro Y hY v hv

  rw [Matrix.matrix_eq_sum_single Y, map_sum, _root_.sum_apply]
  refine W.sum_mem fun a _ => ?_

  rw [map_sum, _root_.sum_apply]
  refine W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · have e : Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 := by
      ext i j; simp [Matrix.single_apply]
    rw [e, map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab v hv)
  · have e : Matrix.single a b (Y a b) = 0 := by
      rw [inK_entry_eq_zero hY hab]; ext i j; simp [Matrix.single_apply]
    rw [e, map_zero, _root_.zero_apply]
    exact W.zero_mem


include hcont hder in
theorem pre_kStable_of_stable (W : Submodule ℂ V)
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) :
    Formalism.REAL.KStable ε (preUnits dτ) W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := hder X hX γ hγ
    have hdv : HasDerivAt (fun t : ℝ => preOp τ (γ t) v) (dτ X v) 0 := by
      have := ((ContinuousLinearMap.apply ℂ V v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    rw [hasDerivAt_iff_tendsto_slope] at hdv
    have hcl : IsClosed (W : Set V) := W.closed_of_finiteDimensional
    refine hcl.mem_of_tendsto hdv (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module, SetLike.mem_coe]
    exact Submodule.smul_of_tower_mem W _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  show dτ (Matrix.single a b 1) v ∈ W
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.single b a 1
  have hA : A * Jm ε = Jm ε * A := single_mul_Jm_comm hab 1
  have hB : B * Jm ε = Jm ε * B := single_mul_Jm_comm hab.symm 1
  have hAB : Aᴴ = B := by
    ext i j
    simp only [A, B, Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]
  have hBA : Bᴴ = A := by rw [← hAB, Matrix.conjTranspose_conjTranspose]
  have h1 : inK ε (A - B) := inK_of_skew_comm (by rw [Matrix.conjTranspose_sub, hAB, hBA, neg_sub])
    (by rw [sub_mul, mul_sub, hA, hB])
  have h2 : inK ε (Complex.I • (A + B)) := inK_of_skew_comm
    (by rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hAB, hBA, Complex.star_def,
      Complex.conj_I, add_comm, neg_smul])
    (by rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hA, hB])
  have e : A = (1 / 2 : ℂ) • (A - B) - (Complex.I / 2) • (Complex.I • (A + B)) := by
    rw [smul_smul, show Complex.I / 2 * Complex.I = -(1 / 2 : ℂ) by
      rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring]
    module
  rw [e, map_sub, map_smul, map_smul, _root_.sub_apply, _root_.smul_apply,
    _root_.smul_apply]
  exact W.sub_mem (W.smul_mem _ (hK _ h1 v hv)) (W.smul_mem _ (hK _ h2 v hv))


include hcont hder in
theorem pre_kSpan_stable (x : V) (k : KG ε) :
    ∀ v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x,
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x := by
  have hS : Formalism.REAL.KStable ε (preUnits dτ) (Formalism.REAL.kSpan ε (preUnits dτ) x) := by
    intro a b hab y hy
    unfold Formalism.REAL.kSpan at hy ⊢
    rw [Submodule.mem_sInf] at hy ⊢
    intro S hS
    exact hS.2 a b hab y (hy S hS)
  obtain ⟨Y, hY, he⟩ := pre_op_eq_exp' τ dτ hder k
  rw [show ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = NormedSpace.exp (dτ Y) from he]
  exact exp_mem_of_stable _ _ (pre_dτ_stable_of_kStable dτ _ hS Y hY)


include hcont hder in
theorem irred_of_gen {Λ : Fin n → ℝ} (w : V)
    (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) :
    ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hx : w ∈ Formalism.REAL.kSpan ε (preUnits dτ) w := by
    unfold Formalism.REAL.kSpan
    rw [Submodule.mem_sInf]
    intro S hS
    exact hS.1
  have htop : Formalism.REAL.kSpan ε (preUnits dτ) w = ⊤ :=
    hgen _ (pre_kSpan_stable τ hcont dτ hder w) hx
  have hhi : Formalism.REAL.KHighest ε (preUnits dτ) Λ w :=
    ⟨fun a => hwt a, fun a b hab he => hhw a b hab he⟩
  have := Formalism.REAL.kIrr V n ε (preUnits dτ) Λ w inferInstance (pre_kRel τ hcont dτ hder)
    (pre_kUnit τ hcont dτ hder) hhi W (htop ▸ le_top) (pre_kStable_of_stable τ hcont dτ hder W hW)
  rwa [htop] at this

end Pre

def kTypeOfGen {ε : Fin n → Bool} {Λ : Fin n → ℝ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
    (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)
    (w : V) (hw : ‖w‖ = 1) (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) : KType ε Λ where
  V := V
  τ := τ
  cont := hcont
  irred := irred_of_gen τ hcont dτ hder w hwt hhw hgen
  dτ := dτ
  hasDeriv := hder
  w := w
  w_norm := hw
  w_wt := hwt
  w_hw := hhw

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem KType.kHighest_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KHighest ε (kunits T) Λ T.w := ⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩

theorem KType.w_ne_zero {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem KType.kSpan_eq_top {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.kSpan ε (kunits T) T.w = ⊤ := by
  rcases KType.dτ_irred T (Formalism.REAL.kSpan ε (kunits T) T.w)
    (fun a b hab v hv => Formalism.REAL.compact_span_stable T.w a b hab v hv) with h | h
  · exfalso
    have hw := Formalism.REAL.mem_compact_span_self (ε := ε) (F := kunits T) T.w
    rw [h, Submodule.mem_bot] at hw
    exact (KType.w_ne_zero T) hw
  · exact h

theorem KType.hw_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ν : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (h : IsKHWVec ε (kunits T) ν v) : ν = Λ ∧ ∃ c : ℂ, v = c • T.w := by
  have hmem : v ∈ Formalism.REAL.kSpan ε (kunits T) T.w := by rw [KType.kSpan_eq_top T]; trivial
  rcases Formalism.REAL.kHiUniq T.V n ε (kunits T) Λ ν T.w v (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hmem h with h0 | h1
  · exact absurd h0 hv
  · exact h1

theorem wtw_eq_sum (w : List (Fin n × Fin n)) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → (b, a) ∈ w) ∧
      -Formalism.REAL.wordWeightShift w = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, heq⟩ := ih
    refine ⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, ?_, ?_⟩
    · intro a b hab
      change c a b + (if a = p.2 ∧ b = p.1 then 1 else 0) ≠ 0 at hab
      by_cases h : c a b = 0
      · rw [h, zero_add] at hab
        split_ifs at hab with h2
        · obtain ⟨rfl, rfl⟩ := h2
          simp
        · exact absurd rfl hab
      · exact List.mem_cons_of_mem _ (hc a b h)
    · have hs : ∑ a, ∑ b, (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2, Finset.sum_eq_single p.1]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · intro a _ ha
          apply Finset.sum_eq_zero
          intro b _
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ _) h
      have e : ∀ a b, (((c a b + if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b =
          (c a b : ℝ) • root a b + (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b :=
        fun a b => by rw [Nat.cast_add, add_smul]
      simp only [e, Finset.sum_add_distrib, hs, ← heq]
      simp only [Formalism.REAL.wordWeightShift, root]
      abel

theorem KType.weight_le {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {μ : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (hμ : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
      Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  have hmem : v ∈ Formalism.REAL.lowSpan ε (kunits T) T.w := by
    rw [← Formalism.REAL.compact_span_eq_lowering (KType.kRel T) (KType.kHighest_w T), KType.kSpan_eq_top T]; trivial
  obtain ⟨w, hw, hwμ⟩ : ∃ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧
      Λ + Formalism.REAL.wordWeightShift w = μ := by
    by_contra hne
    push Not at hne
    apply hv
    have horth : ∀ y ∈ Formalism.REAL.lowSpan ε (kunits T) T.w, inner ℂ v y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro z ⟨w, hw, rfl⟩
        have hwt := Formalism.REAL.word_action_weight (KType.kRel T) (KType.kHighest_w T).1 w (fun q hq => (hw q hq).1)
        exact Formalism.REAL.kWtOrth T.V n ε (kunits T) μ _ v _ (KType.kUnit T) (fun a => hμ a) hwt
          (fun h => hne w hw h.symm)
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    exact inner_self_eq_zero.mp (horth v hmem)
  obtain ⟨c, hc, he⟩ := wtw_eq_sum (n := n) w
  refine ⟨c, fun a b hab => ?_, ?_⟩
  · have := hw _ (hc a b hab)
    exact ⟨this.2, this.1.symm⟩
  · rw [← he, ← hwμ]; abel

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
