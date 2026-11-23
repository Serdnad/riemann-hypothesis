module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle230
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.continuousAt_polarisedTopChernCoeff : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {K : V n → Fin n → EndValuedForm11Coeffs n r} {v : V n}, (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) → ContinuousAt (fun x => mixTop (K x)) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_mixTop | exact GlobalTheory.GoodTop.continuousAt_mixTop | (intros; apply GlobalTheory.GoodTop.continuousAt_mixTop <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.goodPatch_chart_image_properties : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → IsOpen (e '' W) ∧ e '' (ptsIn X.str σ O ∩ W) = offHyp S (e '' W) ∧ ∀ K : Set (CxPts X.str σ), IsClosed K → K ⊆ W → IsCompact (e '' K) := by
  first | exact @GlobalTheory.GoodTop.goodPatch_image | exact GlobalTheory.GoodTop.goodPatch_image | (intros; apply GlobalTheory.GoodTop.goodPatch_image <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_zero : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y), HasInt e (fun _ _ => 0) S 0 := by
  first | exact @GlobalTheory.GoodTop.hasInt_zero | exact GlobalTheory.GoodTop.hasInt_zero | (intros; apply GlobalTheory.GoodTop.hasInt_zero <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_conj : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (P : Matrix r r ℂ), IsUnit P.det → mixTop (fun i a b => P⁻¹ * K i a b * P) = mixTop K := by
  first | exact @GlobalTheory.GoodTop.mixTop_conj | exact GlobalTheory.GoodTop.mixTop_conj | (intros; apply GlobalTheory.GoodTop.mixTop_conj <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_update_add : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r), mixTop (Function.update K j (L + L')) = mixTop (Function.update K j L) + mixTop (Function.update K j L') := by
  first | exact @GlobalTheory.GoodTop.mixTop_update_add | exact GlobalTheory.GoodTop.mixTop_update_add | (intros; apply GlobalTheory.GoodTop.mixTop_update_add <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_update_smul : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (j : Fin n) (t : ℂ) (L : EndValuedForm11Coeffs n r), mixTop (Function.update K j (t • L)) = t * mixTop (Function.update K j L) := by
  first | exact @GlobalTheory.GoodTop.mixTop_update_smul | exact GlobalTheory.GoodTop.mixTop_update_smul | (intros; apply GlobalTheory.GoodTop.mixTop_update_smul <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ}, (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  first | exact @GlobalTheory.GoodTop.hasInt_congr_on | exact GlobalTheory.GoodTop.hasInt_congr_on | (intros; apply GlobalTheory.GoodTop.hasInt_congr_on <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.polarisedTopChernCoeff_linear_substitution : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (J J' : Matrix (Fin n) (Fin n) ℂ), mixTop (fun i a b => ∑ c, ∑ d, (J c a * J' d b) • K i c d) = J.det * J'.det * mixTop K := by
  first | exact @GlobalTheory.GoodTop.mixTop_subst | exact GlobalTheory.GoodTop.mixTop_subst | (intros; apply GlobalTheory.GoodTop.mixTop_subst <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.transgressionTopCoeffComplex_germ_congr : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ} {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n}, ρ =ᶠ[𝓝 v] ρ' → G₀ =ᶠ[𝓝 v] G₀' → G₁ =ᶠ[𝓝 v] G₁' → corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  first | exact @GlobalTheory.GoodTop.corrC_germ_congr | exact GlobalTheory.GoodTop.corrC_germ_congr | (intros; apply GlobalTheory.GoodTop.corrC_germ_congr <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem hasInt_of_chart : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d : κ → Y → ℝ} (e' : OpenPartialHomeomorph Y (V n)) (W : Set Y) (g : V n → ℝ), IsOpen W → W ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → IsTopForm e d S → (∀ i y, y ∈ S → y ∉ W → y ∈ (e i).source → d i y = 0) → (∀ j y, y ∈ S → y ∈ W → y ∈ (e j).source → g (e' y) = ‖transDet e' (e j) y‖ ^ 2 * d j y) → IntegrableOn g (e' '' (S ∩ W)) → HasInt e d S (∫ v in e' '' (S ∩ W), g v) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d e' W g hW hWe hd' hT h0 hg hint
  have hSW : MeasurableSet (S ∩ W) := hS.inter hW.measurableSet
  have hsub : S ∩ W ⊆ e'.source := Set.inter_subset_right.trans hWe
  have key : ∀ ε : ℝ, glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) S =
      ∫⁻ v in e' '' (S ∩ W), ENNReal.ofReal (ε * g v) := by
    intro ε
    have hD : MeasurableSet (S \ W) := hS.diff hW.measurableSet
    have hz := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := fun i y => ENNReal.ofReal (ε * d i y))
      (ρ' := fun i y => ENNReal.ofReal (ε * d i y)) (c := 0) ENNReal.zero_ne_top hD
      (fun i y hi hy => by rw [h0 i y hy.1 hy.2 hi]; simp)
    have hz' : glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) (S \ W) = 0 := by
      have := congrArg (fun μ : Measure Y => μ (S \ W)) hz
      simpa only [Measure.restrict_apply_self, zero_smul, Measure.coe_zero, Pi.zero_apply] using this
    rw [← measure_inter_add_diff S hW.measurableSet, hz', add_zero,
      glueMeas_eq_chartMeas_of_compat_on e hd hcov hSW e' (fun y => ENNReal.ofReal (ε * g (e' y))) hsub hd'
        (fun i j y hy hi hj => by
          rw [hT.trans i j y hy.1 hi hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm])
        (fun j y hy hj => by
          rw [hg j y hy.1 hy.2 hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]),
      chartMeas_apply_of_subset _ _ hSW hsub]
    refine setLIntegral_congr_fun (measurableSet_image e' hSW hsub) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [e'.left_inv (hsub hy)]
  refine ⟨fun ε => ?_, ?_⟩
  · rw [key]
    exact (Integrable.const_mul hint _).lintegral_lt_top.ne
  · rw [measureReal_def, measureReal_def, key, key,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
    simp

end GlobalTheory.GoodTop
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

private theorem glue_mono {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y} (hS : MeasurableSet S) {ρ ρ' : κ → Y → ℝ≥0∞}
    (h : ∀ i y, ρ i y ≤ ρ' i y) : glueMeas e ρ S ≤ glueMeas e ρ' S := by
  have key : glueMeas e ρ ≤ glueMeas e ρ' := by
    refine iSup_mono fun i => Measure.le_iff.2 fun B hB => ?_
    rw [chartMeas_apply _ _ hB, chartMeas_apply _ _ hB]
    exact lintegral_mono fun v => h i _
  exact Measure.le_iff.1 key S hS

private theorem ofReal_balance (a b : ℝ) :
    ENNReal.ofReal (1 * (a + b)) + (ENNReal.ofReal (-1 * a) + ENNReal.ofReal (-1 * b)) =
      ENNReal.ofReal (-1 * (a + b)) + (ENNReal.ofReal (1 * a) + ENNReal.ofReal (1 * b)) := by
  have hm : ∀ v : ℝ, ENNReal.ofReal v = ENNReal.ofReal (max v 0) := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  have conv : ∀ x y z : ℝ, ENNReal.ofReal x + (ENNReal.ofReal y + ENNReal.ofReal z) =
      ENNReal.ofReal (max x 0 + (max y 0 + max z 0)) := fun x y z => by
    rw [ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _) (le_max_right _ _)),
      ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), ← hm, ← hm, ← hm]
  have hs : ∀ v : ℝ, max (1 * v) 0 - max (-1 * v) 0 = v := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [conv, conv]
  congr 1
  linarith [hs a, hs b, hs (a + b)]

theorem hasInt_add : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {s t : ℝ}, IsTopForm e d S → IsTopForm e d' S → HasInt e d S s → HasInt e d' S t → HasInt e (fun i y => d i y + d' i y) S (s + t) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d d' s t hf hf' hi hi'
  have hsum : IsTopForm e (fun i y => d i y + d' i y) S :=
    ⟨fun i j y hy h1 h2 => by rw [hf.trans i j y hy h1 h2, hf'.trans i j y hy h1 h2, mul_add],
      fun i => (hf.meas i).add (hf'.meas i)⟩
  have comp : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i j y, y ∈ S → y ∈ (e i).source →
      y ∈ (e j).source → ENNReal.ofReal (c * f i y) =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (c * f j y) := by
    intro f h c i j y hy h1 h2
    rw [h.trans i j y hy h1 h2, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  have meas : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i,
      AEMeasurable (fun v => ENNReal.ofReal (c * f i ((e i).symm v)))
        (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S)) := fun h c i =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((h.meas i).const_mul c)
  have h2 : ∀ c : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * d i y) + ENNReal.ofReal (c * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * d i y)) S +
        glueMeas e (fun i y => ENNReal.ofReal (c * d' i y)) S := fun c =>
    glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hf c) (comp hf' c) (meas hf c)
  have h3 : ∀ c c' : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y)) +
      (ENNReal.ofReal (c' * d i y) + ENNReal.ofReal (c' * d' i y))) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y))) S +
        (glueMeas e (fun i y => ENNReal.ofReal (c' * d i y)) S +
          glueMeas e (fun i y => ENNReal.ofReal (c' * d' i y)) S) := fun c c' => by
    rw [← h2]
    refine glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hsum c) ?_ (meas hsum c)
    intro i j y hy h1 h2
    rw [comp hf c' i j y hy h1 h2, comp hf' c' i j y hy h1 h2, mul_add]
  have hfin : ∀ ε : ℤˣ,
      glueMeas e (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (d i y + d' i y))) S ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hi.1 ε, hi'.1 ε⟩) ?_
    rw [← h2]
    refine glue_mono e hS fun i y => ?_
    rw [mul_add]
    exact ENNReal.ofReal_add_le
  refine ⟨hfin, ?_⟩
  have hbal := h3 1 (-1)
  simp only [ofReal_balance] at hbal
  rw [h3] at hbal
  have a1 := hfin 1
  have a2 := hfin (-1)
  have b1 := hi.1 1
  have b2 := hi.1 (-1)
  have c1 := hi'.1 1
  have c2 := hi'.1 (-1)
  have e1 := hi.2
  have e2 := hi'.2
  simp only [measureReal_def, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg] at a1 a2 b1 b2 c1 c2 e1 e2 ⊢
  have hr := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add a2 (ENNReal.add_ne_top.2 ⟨b1, c1⟩), ENNReal.toReal_add b1 c1,
    ENNReal.toReal_add a1 (ENNReal.add_ne_top.2 ⟨b2, c2⟩), ENNReal.toReal_add b2 c2] at hr
  linarith

end GlobalTheory.GoodTop
end
end

section

noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes

theorem isOpen_of_padicLattice {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    [FiniteDimensional ℚ_[p] V] [TopologicalSpace V] [IsModuleTopology ℚ_[p] V]
    (A : AddSubgroup V) (hA : ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ v ∈ A, c • v ∈ A)
    (hN : ∀ v : V, ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ A) : IsOpen (A : Set V) := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[p] V
  let b := Module.finBasis ℚ_[p] V
  choose N hN' using fun i => hN (b i)
  set M := ∑ i, N i with hMdef
  have hp1 : ‖(p : ℚ_[p])‖ ≤ 1 := Padic.norm_p_lt_one.le
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hb : ∀ i, (p : ℚ_[p]) ^ M • b i ∈ A := by
    intro i
    have hle : N i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact hA _ (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1) _ (hN' i)
  have hpos : 0 < ‖(p : ℚ_[p]) ^ M‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  let U : Set V := ⋂ i, (fun v => b.coord i v) ⁻¹' Metric.closedBall 0 ‖(p : ℚ_[p]) ^ M‖
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hpos.ne').preimage
      (IsModuleTopology.continuous_of_linearMap (b.coord i))
  have hUA : U ⊆ A := by
    intro v hv
    simp only [U, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hv
    rw [← b.sum_repr v]
    refine A.sum_mem fun i _ => ?_
    have : b.repr v i • b i = (b.repr v i / (p : ℚ_[p]) ^ M) • ((p : ℚ_[p]) ^ M • b i) := by
      rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    rw [this]
    refine hA _ ?_ _ (hb i)
    rw [norm_div, div_le_one hpos]
    exact hv i
  have h0 : (0 : V) ∈ U := by
    simp [U, hpos.le]
  exact AddSubgroup.isOpen_of_mem_nhds A (Filter.mem_of_superset (hU.mem_nhds h0) hUA)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem exists_pow_smul_norm_le_one (z : PadicAlgCl p) : ∃ N : ℕ, ‖(p : ℚ_[p]) ^ N • z‖ ≤ 1 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hz') (Padic.norm_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  rw [Algebra.smul_def, norm_mul, map_pow, norm_pow, PadicAlgCl.norm_extends]
  calc ‖(p : ℚ_[p])‖ ^ N * ‖z‖ ≤ ‖z‖⁻¹ * ‖z‖ := by gcongr
    _ = 1 := inv_mul_cancel₀ hz'.ne'

theorem algebraMap_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) :
    algebraMap ℚ_[p] (KQ p K r) c ∈ intKQ p K r := by
  have hK : algebraMap ℚ_[p] K c ∈ GlobalTheory.LKLoc.intK p K := by
    show algebraMap K (PadicAlgCl p) (algebraMap ℚ_[p] K c) ∈ Obar p
    rw [← IsScalarTower.algebraMap_apply, mem_Obar_iff]
    exact (PadicAlgCl.norm_extends (p := p) c).le.trans hc
  exact Subring.subset_closure (Or.inl ⟨⟨_, hK⟩, rfl⟩)

theorem smul_mem_intKQ (r : ℕ) (c : ℚ_[p]) (hc : ‖c‖ ≤ 1) (v : KQ p K r) (hv : v ∈ intKQ p K r) :
    c • v ∈ intKQ p K r := by
  rw [Algebra.smul_def]
  exact mul_mem (algebraMap_mem_intKQ p K r c hc) hv

theorem exists_pow_smul_mem_intKQ (r : ℕ) (v : KQ p K r) :
    ∃ N : ℕ, (p : ℚ_[p]) ^ N • v ∈ intKQ p K r := by
  have hp1 : ∀ k : ℕ, ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le
  induction (v : K ⊗[ℚ_[p]] Qr p r) using TensorProduct.induction_on with
  | zero => exact ⟨0, by show (p : ℚ_[p]) ^ 0 • (0 : KQ p K r) ∈ intKQ p K r; rw [smul_zero]; exact zero_mem _⟩
  | tmul x y =>
    obtain ⟨N₁, h₁⟩ := exists_pow_smul_norm_le_one p (x : PadicAlgCl p)
    obtain ⟨N₂, h₂⟩ := exists_pow_smul_norm_le_one p (y : PadicAlgCl p)
    have hx : (p : ℚ_[p]) ^ N₁ • x ∈ GlobalTheory.LKLoc.intK p K := by
      show (((p : ℚ_[p]) ^ N₁ • x : K) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₁
    have hy : (p : ℚ_[p]) ^ N₂ • y ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
      show (((p : ℚ_[p]) ^ N₂ • y : Qr p r) : PadicAlgCl p) ∈ Obar p
      rw [IntermediateField.coe_smul, mem_Obar_iff]; exact h₂
    refine ⟨N₁ + N₂, ?_⟩
    have key : ((p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y) : K ⊗[ℚ_[p]] Qr p r) =
        (((p : ℚ_[p]) ^ N₁ • x) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : ℚ_[p]) ^ N₂ • y)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul_smul, pow_add]
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) =
        inclK p K r ((p : ℚ_[p]) ^ N₁ • x) * inclQ p K r ((p : ℚ_[p]) ^ N₂ • y) := key
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (x ⊗ₜ[ℚ_[p]] y : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hx⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, hy⟩, rfl⟩))
  | add a b ha hb =>
    obtain ⟨N₁, h₁⟩ := ha
    obtain ⟨N₂, h₂⟩ := hb
    refine ⟨N₁ + N₂, ?_⟩
    have e : (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b) =
        (p : ℚ_[p]) ^ N₂ • ((p : ℚ_[p]) ^ N₁ • a) + (p : ℚ_[p]) ^ N₁ • ((p : ℚ_[p]) ^ N₂ • b) := by
      rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_comm N₂ N₁]
    show (p : ℚ_[p]) ^ (N₁ + N₂) • (a + b : KQ p K r) ∈ intKQ p K r
    rw [e]
    exact add_mem (smul_mem_intKQ p K r _ (hp1 _) _ h₁) (smul_mem_intKQ p K r _ (hp1 _) _ h₂)

end GlobalTheory.LKRes

namespace GlobalTheory.LKRes

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isOpen_intKQ (hK : FiniteDimensional ℚ_[p] K) (r : ℕ) (hr : 0 < r) :
    IsOpen (intKQ p K r : Set (KQ p K r)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : FiniteDimensional ℚ_[p] (KQ p K r) :=
    inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsModuleTopology ℚ_[p] (KQ p K r) := ⟨rfl⟩
  exact isOpen_of_padicLattice (intKQ p K r).toAddSubgroup
    (fun c hc v hv => smul_mem_intKQ p K r c hc v hv) (exists_pow_smul_mem_intKQ p K r)

theorem mem_Kres_iff (n r : ℕ) (g : GL (Fin n) (KQ p K r)) :
    g ∈ Kres p K n r ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r ∧
      ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j ∈ intKQ p K r := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    exact ⟨((h : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2,
      (((h⁻¹ : GL (Fin n) (intKQ p K r)) : Matrix (Fin n) (Fin n) (intKQ p K r)) i j).2⟩
  · intro H
    let A : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).1⟩
    let B : Matrix (Fin n) (Fin n) (intKQ p K r) := Matrix.of fun i j => ⟨_, (H i j).2⟩
    have hA : A.map (intKQ p K r).subtype = (g : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hB : B.map (intKQ p K r).subtype =
        ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) := by ext i j; rfl
    have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intKQ p K r) => M.map (intKQ p K r).subtype :=
      Matrix.map_injective Subtype.val_injective
    have h1 : A * B = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.mul_inv g)
    have h2 : B * A = 1 := hinj (by
      simp only
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hB]
      exact Units.inv_mul g)
    exact ⟨⟨A, B, h1, h2⟩, Units.ext hA⟩

theorem isOpen_Kres : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → IsOpen (Kres p K n r : Set (GL (Fin n) (KQ p K r))) := by
  intro p _ K hK n r hr
  have hS := isOpen_intKQ p K hK r hr
  have e : (Kres p K n r : Set (GL (Fin n) (KQ p K r))) = ⋂ i, ⋂ j,
      ((fun g : GL (Fin n) (KQ p K r) => (g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _) ∩
       (fun g : GL (Fin n) (KQ p K r) =>
          ((g⁻¹ : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j) ⁻¹' (intKQ p K r : Set _)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    exact mem_Kres_iff p K n r g
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (hS.preimage (Units.continuous_val.matrix_elem i j)).inter
    (hS.preimage (Units.continuous_coe_inv.matrix_elem i j))

end GlobalTheory.LKRes
end
end
