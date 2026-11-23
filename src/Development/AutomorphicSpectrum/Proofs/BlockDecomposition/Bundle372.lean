module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle358
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle359
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle314
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RayClassConeParametrization
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.exists_lattice_periodicity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → ∃ c : k, c ≠ 0 ∧ ∀ o ∈ Lc t c, ∀ v, φ (v + o.toAdd) = φ v := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.LatInv.exists_Lc_invariant <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.finite_jacquet_kernel_common_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (S : Set X), S.Finite → (∀ x ∈ S, x ∈ twKer ρ ⊤ 1) → ∃ c : k, c ≠ 0 ∧ ∀ x ∈ S, x ∈ twKer ρ (Lc n c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_Lc_finite_twKer <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.closure_kernel_mem_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.coset_function_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (z : Z), z ∈ twKer ρ₀ ⊤ 1 → cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.coset_function_translate_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (a : Fin t → k) (z : Z), cosetFn t hc a z - cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.integral_coset_indicator_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → ∀ (A : Finset (Fin t → k)) (z : (Fin t → k) → Z), smInt μ (fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => z a) v) = (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) • ∑ a ∈ A, z a := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum.smInt_sum_coset | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum.smInt_sum_coset | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum.smInt_sum_coset <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.jacquet_kernel_lattice_conj_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist.twKer_Lc_le_twist <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.smooth_fibre_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z), IsSmooth ρ₀ → IsSmooth (fibAct t ρ₀) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_antitone_filtration_of_chain : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (R : ℕ → GRep k n → Prop) (Z : ℕ → Prop) (a b : ℕ) (X : GRep k n), Chain R Z a b X → ∃ F : ℕ → Subrepresentation X.ρ, Antitone F ∧ F a = ⊤ ∧ F b = ⊥ ∧ ∀ i, a ≤ i → i < b → (∃ A, R i A ∧ Nonempty ((subQuot (F i) (F (i + 1))).Equiv A.ρ)) ∨ (Z i ∧ F i = F (i + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.ChainFilt.exists_filtration | exact GlobalTheory.CompanionTheory.LeibOrd.ChainFilt.exists_filtration | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.ChainFilt.exists_filtration <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem eq_at_neg_of_eq_right (k p : ℕ) (hp : p < k) (T G : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ) (hG : DifferentiableOn ℂ G {s | -(k : ℝ) < s.re})
    (h : ∀ s : ℂ, 1 < s.re → T s = G s) : T (-(p : ℂ)) = G (-(p : ℂ)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le p) hp)
  have hpk : (p : ℝ) < k := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set C₁ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | 0 < s.im} with hC₁
  set C₂ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | s.re < 1} with hC₂
  have hO₁ : IsOpen C₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hO₂ : IsOpen C₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV₁ : Convex ℝ C₁ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)
  have hV₂ : Convex ℝ C₂ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hs₁ : C₁ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hs₂ : C₂ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hAT₁ : AnalyticOnNhd ℂ T C₁ := (hT.mono hs₁).analyticOnNhd hO₁
  have hAG₁ : AnalyticOnNhd ℂ G C₁ :=
    (hG.mono (show C₁ ⊆ {s | -(k : ℝ) < s.re} from fun _ hs => hs.1)).analyticOnNhd hO₁
  have hAT₂ : AnalyticOnNhd ℂ T C₂ := (hT.mono hs₂).analyticOnNhd hO₂
  have hAG₂ : AnalyticOnNhd ℂ G C₂ :=
    (hG.mono (show C₂ ⊆ {s | -(k : ℝ) < s.re} from fun _ hs => hs.1)).analyticOnNhd hO₂
  have hz₁ : (2 + Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₁ : T =ᶠ[nhds (2 + Complex.I : ℂ)] G := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re})] with s hs
    exact h s hs
  have hE₁ : Set.EqOn T G C₁ :=
    hAT₁.eqOn_of_preconnected_of_eventuallyEq hAG₁ hV₁.isPreconnected hz₁ hev₁
  have hz₂ : (Complex.I : ℂ) ∈ C₂ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hz₂' : (Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₂ : T =ᶠ[nhds (Complex.I : ℂ)] G := by
    filter_upwards [hO₁.mem_nhds hz₂'] with s hs
    exact hE₁ hs
  have hE₂ : Set.EqOn T G C₂ :=
    hAT₂.eqOn_of_preconnected_of_eventuallyEq hAG₂ hV₂.isPreconnected hz₂ hev₂
  refine hE₂ ?_
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith

theorem abelValue_mem_zInv (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (w : (Fin r → ℕ) → ℚ) (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i)
    (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (hz : ∀ m, ∃ z : ℤ, w m = z) (T : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ)
    (hS : ∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) (p : ℕ)
    (hp : ∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) :
    ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  obtain ⟨Q, _, cs, u, K, hu, hc, hK, hid⟩ :=
    GlobalTheory.T.weighted_sum_decomposition_denominators r l (Fintype.card ι * (p + 1) + 2) w hl hw hz
  set G : ℂ → ℂ := fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m with hGdef
  have hG : DifferentiableOn ℂ G {s | -((p + 1 : ℕ) : ℝ) < s.re} := by
    refine DifferentiableOn.fun_sum fun q _ => ?_
    exact GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb (p + 1) _ (cs q) (u q) le_rfl (hu q) (hc q)
  have hTG : ∀ s : ℂ, 1 < s.re → T s = G s := by
    intro s hs
    rw [← (hS s hs).tsum_eq]
    exact hid _ (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)
  have hval := eq_at_neg_of_eq_right (p + 1) p (Nat.lt_succ_self p) T G hT hG hTG
  choose ρ ζ hρ hζ using fun q => GlobalTheory.T.cone_series_special_value_rational ι r a b (u q) (cs q) p K l hl (hK q) hp
  refine ⟨∑ q, ρ q, K, ∑ q, ζ q, ?_, ?_⟩
  · rw [hval, hGdef]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hρ q
  · rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hζ q

theorem abelValue_mem_zInv' : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r l a b w hr hl ha hb hw hz T hT hS p hp
  exact abelValue_mem_zInv ι r l a b w hr hl ha hb hw hz T hT hS p hp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_classParam_sup_eq_top : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  intro F _ _ _ 𝔣 h𝔣 𝔞 h𝔞
  obtain ⟨ι, _, r, v, hdom⟩ := exists_coneDomain F 𝔣 h𝔣
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e, hb.2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section

noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_section : PositivityTheory.PfSWUS.SchInf.SecInf := by
  first | exact @GlobalTheory.CompanionTheory.SecInf.secInf | exact GlobalTheory.CompanionTheory.SecInf.secInf | (intros; apply GlobalTheory.CompanionTheory.SecInf.secInf <;> assumption)
end
end
