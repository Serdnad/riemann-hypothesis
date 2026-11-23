module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

theorem rep_eq (ω : D.Om) (u : Gf) (hu : (u : Gf ⧸ D.H) = ω) : ∃ h : D.H, D.rep ω = u * h := by
  have h1 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  refine ⟨⟨u⁻¹ * D.rep ω, QuotientGroup.eq.1 (hu.trans h1.symm)⟩, ?_⟩
  simp

theorem ee_mul (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) * (D.χ h : ℂ) = D.ee u := by
  unfold Dat.ee
  by_cases hu : u ∈ D.H
  · have hu' : (h : Gf)⁻¹ * u ∈ D.H := D.H.mul_mem (D.H.inv_mem h.2) hu
    rw [dite_eq_left hu', dite_eq_left hu, mul_comm, ← Units.val_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp
  · have hu' : (h : Gf)⁻¹ * u ∉ D.H := fun hh => hu (by simpa using D.H.mul_mem h.2 hh)
    rw [dite_eq_right hu', dite_eq_right hu, zero_mul]

theorem ee_one : D.ee 1 = 1 := by
  unfold Dat.ee
  rw [dite_eq_left D.H.one_mem]
  exact congrArg Units.val (map_one D.χ)

theorem smul_fst (γ : PG F) (ω : D.Om) : γ • ω = (((D.j γ.out * D.rep ω : Gf)) : Gf ⧸ D.H) := by
  have h2 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  conv_lhs => rw [← QuotientGroup.out_eq' γ, ← h2]
  exact D.mk_smulO γ.out (D.rep ω)

theorem smul_snd (γ : PG F) (w : D.Xs) : γ • w = D.act γ.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact D.mk_smulX γ.out w

variable [Fintype I]

theorem term (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (γ : PG F) (y : D.Y) :
    D.ee ((D.rep (γ • y).1)⁻¹ * x) * (qq k z (γ • y).2 * f ((γ • y).2, D.rep (γ • y).1)) =
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (qq k z (D.act γ.out y.2) * D.J k γ.out y.2) * f (y.2, D.rep y.1) := by
  obtain ⟨h, hh⟩ := rep_eq D (γ • y).1 (D.j γ.out * D.rep y.1) (by rw [Prod.smul_fst, smul_fst])
  have hs2 : (γ • y).2 = D.act γ.out y.2 := by rw [Prod.smul_snd, smul_snd]
  have key : (D.j γ.out * D.rep y.1 * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ * ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) := by
    group
  rw [hh, hs2, hf.lev, show f (D.act γ.out y.2, D.j γ.out * D.rep y.1) = D.J k γ.out y.2 * f (y.2, D.rep y.1) from hf.aut _ _ _, key, ← ee_mul D h ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)]
  ring

open Classical in
theorem supp (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (y : D.Y) :
    D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) =
      if y.1 = ((x : Gf) : Gf ⧸ D.H) then qq k z y.2 * f (y.2, x) else 0 := by
  split_ifs with hy
  · obtain ⟨h, hh⟩ := rep_eq D y.1 x hy.symm
    have he := ee_mul D h 1
    rw [ee_one, mul_one] at he
    have key : (x * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ := by group
    rw [hh, show f (y.2, x * (h : Gf)) = (D.χ h : ℂ) * f (y.2, x) from hf.lev _ _ _, key]
    calc _ = (D.ee ((h : Gf)⁻¹) * (D.χ h : ℂ)) * (qq k z y.2 * f (y.2, x)) := by ring
      _ = _ := by rw [he, one_mul]
  · have hn : (D.rep y.1)⁻¹ * x ∉ D.H := by
      intro hm
      apply hy
      have h1 : ((D.rep y.1 : Gf) : Gf ⧸ D.H) = y.1 := QuotientGroup.out_eq' _
      exact h1.symm.trans (QuotientGroup.eq.2 hm)
    have h0 : D.ee ((D.rep y.1)⁻¹ * x) = 0 := by
      unfold Dat.ee
      rw [dite_eq_right hn]
    rw [h0, zero_mul]

end UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk UpperTheory.Esk.ReproducingKernelExpansion in
theorem UpperTheory.Esk.e5_of_reproducing_formula : UpperTheory.Esk.B1b → UpperTheory.Esk.C3 → UpperTheory.Esk.E0a → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.MultivariableReproducingFormula → UpperTheory.Esk.E5 := by
  intro hB1 hC3 hE0 _hE4 hB3 F I Gf _ _ _ D hAx k hk _hcomp b hb f hf p
  obtain ⟨z, x⟩ := p
  obtain ⟨hcount, hsf, -, hpres, -, -, hborel, -⟩ := hE0 F I Gf D hAx
  have := hcount
  have := hsf
  have := hborel
  have := hAx.cO
  let ω₀ : D.Om := ((x : Gf) : Gf ⧸ D.H)
  let a : D.Om → ℂ := ({ω₀} : Set D.Om).indicator fun _ => (1 : ℂ)
  let h0 : D.Xs → ℂ := fun w => qq k z w * f (w, x)
  let G : D.Y → ℂ := fun y => D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1))
  have hG : G = fun y => a y.1 * h0 y.2 := by
    funext y
    change D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) = a y.1 * h0 y.2
    rw [supp D k f hf z x y]
    by_cases hy : y.1 = ((x : Gf) : Gf ⧸ D.H)
    · rw [if_pos hy]
      have ha : a y.1 = 1 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_pos (show y.1 ∈ ({ω₀} : Set D.Om) from hy)]
      rw [ha, one_mul]
    · rw [if_neg hy]
      have ha : a y.1 = 0 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_neg (show y.1 ∉ ({ω₀} : Set D.Om) from hy)]
      rw [ha, zero_mul]
  have hqc : Continuous fun w : X I => qq k z w := by
    unfold qq
    exact continuous_finsetProd _ fun v _ =>
      (hB1.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))
  have hh0c : Continuous fun w : X I => qq k z w * f (w, x) := hqc.mul (hf.hol x).1
  have hh0m : Measurable h0 := hh0c.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hB := hB3 I k hk (fun w => f (w, x)) (hf.hol x) ⟨C, fun w => hC w x⟩ z
  have hh0i : Integrable h0 := hB.1
  have ham : Measurable a := measurable_const.indicator (MeasurableSet.of_discrete)
  have hai : Integrable a Measure.count :=
    (integrable_indicator_iff (MeasurableSet.of_discrete)).2
      ((integrableOn_singleton_iff (by simp)).2 (Or.inr (by simp)))
  have ha1 : ∫ ω, a ω ∂Measure.count = 1 := by
    simp only [a]
    rw [integral_indicator (MeasurableSet.of_discrete)]
    simp
  have hGm : Measurable G := by
    rw [hG]
    exact (ham.comp measurable_fst).mul (hh0m.comp measurable_snd)
  have hGi : Integrable G D.μY := by
    rw [hG]
    unfold Dat.μY
    exact MeasureTheory.Integrable.mul_prod hai hh0i
  have hKf : ∀ y : D.Y, D.Kern k y (z, x) * f (y.2, D.rep y.1) = ∑' γ : PG F, G (γ • y) := by
    intro y
    unfold Dat.Kern
    rw [← tsum_mul_right]
    refine tsum_congr fun γ => ?_
    exact (term D k f hf z x γ y).symm
  have hCC := hC3 (PG F) D.Y D.μY hpres b hb G hGm hGi
  calc ∫ y, b y • (D.Kern k y (z, x) * f (y.2, D.rep y.1)) ∂D.μY
      = ∫ y, b y • ∑' γ : PG F, G (γ • y) ∂D.μY := by simp_rw [hKf]
    _ = ∫ y, G y ∂D.μY := hCC.2
    _ = ∫ y, a y.1 * h0 y.2 ∂(Measure.count.prod volume) := by rw [hG]; rfl
    _ = (∫ ω, a ω ∂Measure.count) * ∫ w, h0 w := integral_prod_mul _ _
    _ = f (z, x) := by rw [ha1, one_mul]; exact hB.2
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk

def iN : P := ⟨-Complex.I, by simp⟩

def bs {I : Type} (e : I → Bool) : X I := fun v => if e v then iP else iN

theorem kap_pos (a z : P) (ha : a.1.im = 1 ∨ a.1.im = -1) (h : 0 < a.1.im * z.1.im) : 0 < kap a z := by
  unfold kap
  rw [if_pos h]
  apply div_pos (by linarith)
  apply pow_pos
  apply norm_pos_iff.2
  intro h0
  have h1 := congrArg Complex.im h0
  simp at h1
  rcases ha with ha | ha <;> rw [ha] at h h1 <;> nlinarith

theorem kap_bs_pos {I : Type} (z : X I) (v : I) :
    0 < kap (bs (fun i => decide (0 < (z v).1.im)) v) (z v) := by
  have hz := (z v).2
  unfold bs
  by_cases h : 0 < (z v).1.im
  · simp only [h, decide_true, if_true]
    exact kap_pos _ _ (Or.inl (by simp [iP])) (by simpa [iP] using h)
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    have h' : (z v).1.im < 0 := lt_of_le_of_ne (not_lt.1 h) hz
    exact kap_pos _ _ (Or.inr (by simp [iN])) (by simp [iN]; linarith)

theorem Kap_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hk0 _ _) _


open Classical in
def uX {I : Type} [Fintype I] (z : X I) : ℝ := by
  classical
  exact ∑ e : I → Bool, Kap (fun _ => 4) (bs e) z

theorem uX_nonneg {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 ≤ uX z :=
  Finset.sum_nonneg fun e _ => Kap_nonneg hk0 _ _ _

theorem uX_pos {I : Type} [Fintype I] (hk0 : ∀ z w : P, 0 ≤ kap z w) (z : X I) : 0 < uX z := by
  classical
  unfold uX
  refine Finset.sum_pos' (fun e _ => Kap_nonneg hk0 _ _ _) ⟨fun v => decide (0 < (z v).1.im), Finset.mem_univ _, ?_⟩
  exact Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (kap_bs_pos z v) _

theorem uX_cont {I : Type} [Fintype I] (hkc : Continuous fun p : P × P => kap p.1 p.2) :
    Continuous (uX : X I → ℝ) := by
  unfold uX Kap
  refine continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun v _ => ?_
  exact (hkc.comp (continuous_const.prodMk (continuous_apply v))).rpow_const fun _ => Or.inr (by positivity)

theorem tsum_le_fiber {G Ω : Type} (φ : G → Ω) (w : Ω → ℝ≥0∞) (K : G → ℝ≥0∞) (M : ℝ≥0∞)
    (hK : ∀ ω', ∑' g : {g // φ g = ω'}, K g.1 ≤ M) : ∑' g, w (φ g) * K g ≤ (∑' ω', w ω') * M := by
  rw [← ENNReal.tsum_fiberwise _ φ, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun ω' => ?_
  calc ∑' b : φ ⁻¹' {ω'}, w (φ b) * K b = ∑' b : φ ⁻¹' {ω'}, w ω' * K b :=
        tsum_congr fun b => by rw [show φ b = ω' from b.2]
    _ = w ω' * ∑' b : φ ⁻¹' {ω'}, K b := ENNReal.tsum_mul_left
    _ ≤ w ω' * M := by gcongr; exact hK ω'

end UpperTheory.Esk.TruncationKernelLemmas

open UpperTheory.Esk in
open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_Ecut : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.Ecut := by
  classical
  intro _ hB hC hE _ hK F I Gf _ _ _ D hax
  obtain ⟨hcount, -, hpres, -⟩ := hE F I Gf D hax
  have : Countable (PG F) := hcount
  have : Countable D.Om := hax.cO
  obtain ⟨hk0', -, -, -, hkc, -⟩ := hB
  have hk0 : ∀ z w : P, 0 ≤ kap z w := fun z w => (hk0' z w).1
  obtain ⟨c₀, hc₀, hmk⟩ := hax.mink
  obtain ⟨C, hCK⟩ := hK F I Gf D hax (fun _ => 4) (fun _ => le_rfl) c₀ hc₀
  have hmX : ∀ g : PG F, Measurable fun z : D.Xs => g • z := fun g => (hpres g).measurable
  have hfib : ∀ y : D.Y, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ (e : I → Bool) (ω' : D.Om),
      ∑' γ : {γ : PG F // γ • y.1 = ω'}, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • y.2 : D.Xs)) ≤ M := by
    intro y
    obtain ⟨s, hs, hsy⟩ := hmk y.2 (D.rep y.1)
    exact ⟨_, ENNReal.ofReal_ne_top, fun e ω' => hCK y s hs hsy ω' (TruncationKernelLemmas.bs e)⟩
  have hucont : Continuous (TruncationKernelLemmas.uX : X I → ℝ) := TruncationKernelLemmas.uX_cont hkc
  have hsplit : ∀ z : X I, ENNReal.ofReal (TruncationKernelLemmas.uX z) =
      ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) z) := by
    intro z
    rw [TruncationKernelLemmas.uX, ENNReal.ofReal_sum_of_nonneg (fun e _ => TruncationKernelLemmas.Kap_nonneg hk0 _ _ _)]
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Om
  set w : D.Om → ℝ := fun ω => (1 / 2 : ℝ) ^ f ω with hw
  have hW : ∑' ω, ENNReal.ofReal (w ω) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (1 / 2 : ℝ) ^ n))
      ((ENNReal.tsum_comp_le_tsum_of_injective hf (fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n))).trans (le_of_eq ?_))
    exact (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two).symm
  refine ⟨?_, ?_⟩
  · refine (hC (PG F) D.Y).1 ?_ (fun y => w y.1 * TruncationKernelLemmas.uX y.2) ?_ ?_ ?_ ?_
    · intro g
      exact (Measurable.of_discrete.comp measurable_fst).prodMk ((hmX g).comp measurable_snd)
    · have h1 : Measurable fun y : D.Y => w y.1 := (Measurable.of_discrete (f := w)).comp measurable_fst
      have h2 : Measurable fun y : D.Y => TruncationKernelLemmas.uX (y.2 : X I) := hucont.measurable.comp measurable_snd
      exact h1.mul h2
    · exact fun y => mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _)
    · exact fun y => ⟨1, by simpa using mul_pos (by positivity : (0 : ℝ) < w y.1) (TruncationKernelLemmas.uX_pos hk0 y.2)⟩
    · intro y
      obtain ⟨M, hM, hMb⟩ := hfib y
      have hle : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≤
          ∑ e : I → Bool, (∑' ω, ENNReal.ofReal (w ω)) * M := by
        calc ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2)
            = ∑' g : PG F, ∑ e : I → Bool, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) := by
              refine tsum_congr fun g => ?_
              exact (ENNReal.ofReal_mul (by positivity)).trans
                ((congrArg (fun t => ENNReal.ofReal (w (g • y.1)) * t) (hsplit _)).trans (by rw [Finset.mul_sum]; rfl))
          _ = ∑ e : I → Bool, ∑' g : PG F, ENNReal.ofReal (w (g • y.1)) *
                ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ => TruncationKernelLemmas.tsum_le_fiber (fun g : PG F => g • y.1)
                (fun ω => ENNReal.ofReal (w ω))
                (fun g : PG F => ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • y.2 : D.Xs))) M (hMb e)
      have hfin : ∑' g : PG F, ENNReal.ofReal (w (g • y).1 * TruncationKernelLemmas.uX (g • y).2) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => ENNReal.mul_lt_top hW.lt_top hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (mul_nonneg (by positivity) (TruncationKernelLemmas.uX_nonneg hk0 _))
  · intro ω S hS
    refine (hC S D.Xs).1 ?_ TruncationKernelLemmas.uX ?_ ?_ ?_ ?_
    · intro g
      exact hmX (g : PG F)
    · exact hucont.measurable
    · exact TruncationKernelLemmas.uX_nonneg hk0
    · exact fun z => ⟨1, by simpa using TruncationKernelLemmas.uX_pos hk0 z⟩
    · intro z
      obtain ⟨M, hM, hMb⟩ := hfib ((ω, z) : D.Y)
      have hinj : Function.Injective (fun g : S => (⟨(g : PG F), hS g.2⟩ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω})) := by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} => x.1) h
      have hle : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≤ ∑ e : I → Bool, M := by
        calc ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs))
            = ∑' g : S, ∑ e : I → Bool, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              tsum_congr fun g => hsplit _
          _ = ∑ e : I → Bool, ∑' g : S, ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (g • z : D.Xs)) :=
              Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
          _ ≤ _ := Finset.sum_le_sum fun e _ =>
              (ENNReal.tsum_comp_le_tsum_of_injective hinj
                (fun γ : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} =>
                  ENNReal.ofReal (Kap (fun _ => 4) (TruncationKernelLemmas.bs e) (γ.1 • ((ω, z) : D.Y).2 : D.Xs)))).trans (hMb e ω)
      have hfin : ∑' g : S, ENNReal.ofReal (TruncationKernelLemmas.uX (g • z : D.Xs)) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun e _ => hM.lt_top).ne hle
      refine (ENNReal.summable_toReal hfin).congr fun g => ?_
      exact ENNReal.toReal_ofReal (TruncationKernelLemmas.uX_nonneg hk0 _)
end
end
