module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Trigonometric
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

section

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

def aff (α β γ : ℝ) (l : ℂ × ℂ) : ℂ := (α : ℂ) * l.1 + (β : ℂ) * l.2 + (γ : ℂ)

def affR (α β γ : ℝ) (x : ℝ × ℝ) : ℝ := α * x.1 + β * x.2 + γ

def chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (l : ℂ × ℂ) : ℂ × ℂ := (aff α₁ β₁ γ₁ l, aff α₂ β₂ γ₂ l)

def chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (affR α₁ β₁ γ₁ x, affR α₂ β₂ γ₂ x)

lemma aff_re (α β γ : ℝ) (l : ℂ × ℂ) : (aff α β γ l).re = affR α β γ (l.1.re, l.2.re) := by
  simp [aff, affR]

lemma aff_line (α β γ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    aff α β γ (p + τ • v) = aff α β γ p + τ * ((α : ℂ) * v.1 + (β : ℂ) * v.2) := by
  simp only [aff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma continuous_aff (α β γ : ℝ) : Continuous (aff α β γ) := by
  unfold aff; fun_prop

lemma continuous_affR (α β γ : ℝ) : Continuous (affR α β γ) := by
  unfold affR; fun_prop

lemma continuous_chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chg α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_aff _ _ _).prodMk (continuous_aff _ _ _)

lemma continuous_chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chgR α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_affR _ _ _).prodMk (continuous_affR _ _ _)

lemma differentiable_aff_line (α β γ : ℝ) (p v : ℂ × ℂ) :
    Differentiable ℂ fun τ : ℂ => aff α β γ (p + τ • v) := by
  simp only [aff_line]
  fun_prop

lemma mem_tube_chg {Ω : Set (ℝ × ℝ)} {α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ} {l : ℂ × ℂ} :
    l ∈ tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) ↔ chg α₁ β₁ γ₁ α₂ β₂ γ₂ l ∈ tube Ω := by
  simp only [tube, Set.mem_setOf_eq, Set.mem_preimage, chg, chgR, aff_re]

lemma chg_line (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    chg α₁ β₁ γ₁ α₂ β₂ γ₂ (p + τ • v) = chg α₁ β₁ γ₁ α₂ β₂ γ₂ p +
      τ • ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2) := by
  simp only [chg, aff_line]
  rfl

section Good

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma lineHol_chg {F : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hF : LineHol F (tube Ω))
    (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    LineHol (fun l => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l)) (tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω)) := by
  intro p v
  have h := hF (chg α₁ β₁ γ₁ α₂ β₂ γ₂ p)
    ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2)
  simp only [mem_tube_chg, chg_line]
  exact h

theorem TubeGood_chg {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    TubeGood (fun l g => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l) g) (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) := by
  refine ⟨fun g => lineHol_chg (hF.hol g) _ _ _ _ _ _, ?_, ?_⟩
  · have hc : Continuous fun y : (ℂ × ℂ) × T => (chg α₁ β₁ γ₁ α₂ β₂ γ₂ y.1, y.2) :=
      ((continuous_chg _ _ _ _ _ _).comp continuous_fst).prodMk continuous_snd
    refine hF.cont.comp hc.continuousOn ?_
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact ⟨mem_tube_chg.1 hl, Set.mem_univ _⟩
  · intro C hC hCc g
    obtain ⟨U, hU, M, hM⟩ := hF.bdd (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ '' C)
      (by rintro _ ⟨x, hx, rfl⟩; exact hC hx) (hCc.image (continuous_chgR _ _ _ _ _ _)) g
    refine ⟨U, hU, M, fun l hl g' hg' => hM _ ?_ g' hg'⟩
    have : (l.1.re, l.2.re) ∈ C := hl
    refine ⟨_, this, ?_⟩
    simp only [chg, chgR, aff_re]

lemma TubeGood_mono {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω Ω' : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (h : Ω' ⊆ Ω) : TubeGood F Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  refine ⟨fun g p v => ?_, hF.cont.mono (Set.prod_mono ht subset_rfl),
    fun C hC => hF.bdd C (hC.trans h)⟩
  exact (hF.hol g p v).mono fun τ hτ => ht hτ

structure Fac (A : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol A (tube Ω)
  cont : ContinuousOn A (tube Ω)
  bdd : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C, ‖A l‖ ≤ M

lemma exists_bounds {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hne : C.Nonempty) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : ∃ x ∈ C, ∃ y ∈ C, ∀ u ∈ C, f x ≤ f u ∧ f u ≤ f y := by
  obtain ⟨x, hx, hx'⟩ := hC.exists_isMinOn hne hf.continuousOn
  obtain ⟨y, hy, hy'⟩ := hC.exists_isMaxOn hne hf.continuousOn
  exact ⟨x, hx, y, hy, fun u hu => ⟨hx' hu, hy' hu⟩⟩

theorem Fac_left {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) (α β γ : ℝ) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, affR α β γ x < a) : Fac (fun l => f (aff α β γ l)) Ω := by
  have hre : ∀ l ∈ tube Ω, (aff α β γ l).re < a := fun l hl => by
    rw [aff_re]; exact h _ hl
  refine ⟨fun p v => ?_, ?_, fun C hC hCc => ?_⟩
  · refine hf.1.comp (differentiable_aff_line α β γ p v).differentiableOn ?_
    intro τ hτ
    exact hre _ hτ
  · exact hf.1.continuousOn.comp (continuous_aff _ _ _).continuousOn fun l hl => hre l hl
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, hy, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y) (h y (hC hy))
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

theorem Fac_strip {f : ℂ → X} (hf : StripEntire f) (α β γ : ℝ) (Ω : Set (ℝ × ℝ)) :
    Fac (fun l => f (aff α β γ l)) Ω := by
  refine ⟨fun p v => ?_, ?_, fun C _ hCc => ?_⟩
  · exact (hf.1.comp (differentiable_aff_line α β γ p v)).differentiableOn
  · exact (hf.1.continuous.comp (continuous_aff _ _ _)).continuousOn
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, -, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y)
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

theorem Fac_smul {f : ℂ × ℂ → ℂ} {A : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hA : Fac A Ω) :
    Fac (fun l => f l • A l) Ω := by
  refine ⟨fun p v => (hf.hol p v).smul (hA.hol p v), hf.cont.smul hA.cont, fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => ?_⟩
  rw [norm_smul]
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem Fac_mul {f f' : ℂ × ℂ → ℂ} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hf' : Fac f' Ω) :
    Fac (fun l => f l * f' l) Ω :=
  Fac_smul hf hf'

theorem TubeGood_smul {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    {f : ℂ × ℂ → ℂ} (hf : Fac f Ω) (hF : TubeGood F Ω) :
    TubeGood (fun l g => f l • F l g) Ω := by
  refine ⟨fun g p v => (hf.hol p v).smul (hF.hol g p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.smul (hf.cont.comp continuousOn_fst ?_) hF.cont
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
    obtain ⟨U, hU, M₂, h₂⟩ := hF.bdd C hC hCc g
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => ?_⟩
    rw [norm_smul]
    exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl g' hg').trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Good

section Comp

variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]

theorem Fac_comp {A : ℂ × ℂ → E₂ →L[ℂ] E₃} {B : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)}
    (hA : Fac A Ω) (hB : Fac B Ω) : Fac (fun l => (A l).comp (B l)) Ω := by
  refine ⟨fun p v => (hA.hol p v).clm_comp (hB.hol p v), hA.cont.clm_comp hB.cont,
    fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hA.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hB.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem TubeGood_comp {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → E₂ →L[ℂ] E₃}
    {A : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)} (hF : TubeGood F Ω) (hA : Fac A Ω) :
    TubeGood (fun l g => (F l g).comp (A l)) Ω := by
  refine ⟨fun g p v => (hF.hol g p v).clm_comp (hA.hol p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.clm_comp hF.cont (hA.cont.comp continuousOn_fst ?_)
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨U, hU, M₁, h₁⟩ := hF.bdd C hC hCc g
    obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' =>
      (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
    exact mul_le_mul ((h₁ l hl g' hg').trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Comp

end GlobalTheory.CompanionTheory.RgEisGal
end
end

section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.Eis

theorem tube_isOpen {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) :=
    (Complex.continuous_re.comp continuous_fst).prodMk (Complex.continuous_re.comp continuous_snd)
  exact hc.isOpen_preimage Ω hΩ

theorem line_tube_convex {Ω : Set (ℝ × ℝ)} (hc : Convex ℝ Ω) (p v : ℂ × ℂ) :
    Convex ℝ {τ : ℂ | p + τ • v ∈ tube Ω} := by
  intro x hx y hy a b ha hb hab
  have key := hc hx hy ha hb hab
  simp only [tube, Set.mem_ofPred_eq] at hx hy key ⊢
  convert key using 1
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.fst_add, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.1.re) * hab
  · simp only [Prod.snd_add, Prod.smul_snd, Complex.add_re, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Prod.smul_mk, Prod.mk_add_mk]
    linear_combination (-p.2.re) * hab

theorem idTube : IdTube := by
  intro X _ _ _ Ω Ω' F F' hΩ hc hΩ' hne hsub hF hF' heq z hz
  obtain ⟨ω, hω⟩ := hne
  set z0 : ℂ × ℂ := ((ω.1 : ℂ), (ω.2 : ℂ)) with hz0
  have hz0' : z0 ∈ tube Ω' := by simpa [tube, hz0] using hω
  have hline : Continuous fun τ : ℂ => z0 + τ • (z - z0) := by fun_prop
  have hDo : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := (tube_isOpen hΩ).preimage hline
  have hDc : Convex ℝ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := line_tube_convex hc z0 (z - z0)
  have h0 : (0 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by
    show z0 + (0 : ℂ) • (z - z0) ∈ tube Ω
    rw [zero_smul, add_zero]
    exact hsub hz0'
  have h1 : (1 : ℂ) ∈ {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω} := by simpa using hz
  have hA := (hF z0 (z - z0)).analyticOnNhd hDo
  have hA' := (hF' z0 (z - z0)).analyticOnNhd hDo
  have hev : (fun τ : ℂ => F (z0 + τ • (z - z0))) =ᶠ[𝓝 0] (fun τ : ℂ => F' (z0 + τ • (z - z0))) := by
    have hO' : IsOpen {τ : ℂ | z0 + τ • (z - z0) ∈ tube Ω'} := (tube_isOpen hΩ').preimage hline
    filter_upwards [hO'.mem_nhds (by simpa using hz0')] with τ hτ
    exact heq hτ
  have := hA.eqOn_of_preconnected_of_eventuallyEq hA' hDc.isPreconnected h0 hev h1
  simpa using this

end GlobalTheory.CompanionTheory.Eis
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEis


open PositivityTheory.RgEis in
theorem cross_stage_pos : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  open PositivityTheory.RgEis in
  intro hS G _ Γ Q P ξ lam t hPQ hξ hlam hc g
  have key := (hS G ℝ P (Γ ⊓ Q) Γ (fun x => Real.exp (lam x + t * ξ x)) inf_le_left
    (fun γ h1 h2 => ⟨h1, hPQ h2⟩)
    (fun γ h1 h2 x => by
      show Real.exp (lam (γ * x) + t * ξ (γ * x)) = Real.exp (lam x + t * ξ x)
      rw [hlam γ h1 h2 x, hξ γ h1 (hPQ h2) x]) g
    (by
      have h := hc g
      refine h.congr (fun q => ?_)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])).2.1
  refine key.congr (fun r => ?_)
  rw [pos, ← tsum_mul_left]
  refine tsum_congr (fun q => ?_)
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hξ _ hq.1 hq.2, ← Real.exp_add, add_comm]

end GlobalTheory.CompanionTheory.RgEis
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross


open PositivityTheory.RgEis in
theorem stage_eis : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by
  intro hSt G _ W _ _ _ Γ K Q P c ρ ξ lam Λ s w Ms hPQ hξ hΛ hsec hMs hconv hre g
  set f : G → W := fun x => Complex.exp (Λ x + s * ξ x) • sec K P c ρ x w with hf
  have hfinv : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro γ hγ hP x
    simp only [hf]
    rw [hΛ γ hγ hP x, hξ γ hγ (hPQ hP) x, hsec γ hγ hP x]
  have hnorm : ∀ x, ‖f x‖ ≤ Ms * Real.exp (lam x) := by
    intro x
    simp only [hf]
    rw [norm_smul, Complex.norm_exp, hre x, mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right (hMs x) (Real.exp_pos _).le
  have hsum : Summable fun q : Cos P Γ => ‖f (rep q * g)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hnorm _) ((hconv g).mul_left Ms)
  obtain ⟨-, -, hstage⟩ := hSt G W P (Γ ⊓ Q) Γ f inf_le_left (fun γ hγ hP => ⟨hγ, hPQ hP⟩) hfinv g hsum
  have hR : eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w = ∑' q : Cos P Γ, f (rep q * g) := rfl
  rw [hR, hstage]
  unfold eis
  refine tsum_congr fun r => ?_
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  simp only [hf]
  rw [hξ _ (Subgroup.mem_inf.mp hq).1 (Subgroup.mem_inf.mp hq).2, Complex.exp_add, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisCross
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem tubeGood_tsum (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace T] (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ))
    (hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g)
    (hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2)
    (hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) :
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) := by fun_prop
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g p v τ₀ hτ₀
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hτ₀ g
    have hline : Continuous fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re) :=
      hc.comp (by fun_prop : Continuous fun τ : ℂ => p + τ • v)
    have hS : (fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re)) ⁻¹' V ∈ 𝓝 τ₀ :=
      hline.continuousAt.preimage_mem_nhds hV
    obtain ⟨S, hSsub, hSo, hτS⟩ := mem_nhds_iff.1 hS
    have hd : DifferentiableOn ℂ (fun τ : ℂ => ∑' r, t r (p + τ • v) g) S :=
      Complex.differentiableOn_tsum_of_summable_norm hu
        (fun r => (hhol r g p v).differentiableOn) hSo
        (fun r τ hτ => hb _ (hSsub hτ) g (mem_of_mem_nhds hU) r)
    exact ((hd τ₀ hτS).differentiableAt (hSo.mem_nhds hτS)).differentiableWithinAt
  · rintro ⟨l₀, g₀⟩ ⟨hl₀, -⟩
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl₀ g₀
    have hVl : (fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V ∈ 𝓝 l₀ :=
      hc.continuousAt.preimage_mem_nhds hV
    have hS : ((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U ∈ 𝓝 (l₀, g₀) :=
      prod_mem_nhds hVl hU
    have hd : ContinuousOn (fun y : (ℂ × ℂ) × T => ∑' r, t r y.1 y.2)
        (((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U) :=
      continuousOn_tsum (fun r => (hcont r).continuousOn) hu
        (fun r y hy => hb _ hy.1 _ hy.2 r)
    exact (hd.continuousAt hS).continuousWithinAt
  · intro C hCΩ hC g
    refine hC.induction_on
      (p := fun S => ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ PositivityTheory.RgEis.tube S, ∀ g' ∈ U,
        ‖∑' r, t r l g'‖ ≤ M) ?_ ?_ ?_ ?_
    · exact ⟨Set.univ, univ_mem, 0, fun l hl => hl.elim⟩
    · rintro s s' hss ⟨U, hU, M, hM⟩
      exact ⟨U, hU, M, fun l hl g' hg' => hM l (hss hl) g' hg'⟩
    · rintro s s' ⟨U, hU, M, hM⟩ ⟨U', hU', M', hM'⟩
      refine ⟨U ∩ U', inter_mem hU hU', max M M', ?_⟩
      rintro l (hl | hl) g' hg'
      · exact (hM l hl g' hg'.1).trans (le_max_left _ _)
      · exact (hM' l hl g' hg'.2).trans (le_max_right _ _)
    · intro x hx
      obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom x (hCΩ hx) g
      exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, U, hU, ∑' r, u r, fun l hl g' hg' =>
        tsum_of_norm_bounded hu.hasSum (fun r => hb l hl g' hg' r)⟩
  · intro l hl g
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl g
    exact Summable.of_nonneg_of_le (fun r => norm_nonneg _)
      (fun r => hb l (show (l.1.re, l.2.re) ∈ V from mem_of_mem_nhds hV) g (mem_of_mem_nhds hU) r) hu

end GlobalTheory.CompanionTheory.RgEisCross
end

section

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe

theorem hs_mul_le_mul {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  have key : ∀ i j, ‖(P * Q) i j‖ ^ 2 ≤ (∑ k, ‖P i k‖ ^ 2) * (∑ k, ‖Q k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(P * Q) i j‖ ≤ ∑ k, ‖P i k‖ * ‖Q k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have hQ : Formalism.REAL.hs Q = ∑ j, ∑ k, ‖Q k j‖ ^ 2 := by
    unfold Formalism.REAL.hs
    exact Finset.sum_comm
  rw [hQ]
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j

end GlobalTheory.CompanionTheory.RgHe
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitian_psd_isotropic_radical : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ v, B v v = 0 → ∀ w, B v w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | exact GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd | (intros; apply GlobalTheory.CompanionTheory.HermitianForm.pairing_eq_zero_of_psd <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitian_semidefinite_null_radical : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v w, B w v = starRingEnd ℂ (B v w)) → (∀ v, 0 ≤ (B v v).re) → ∀ x, (B x x).re = 0 → ∀ w, B x w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | exact GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic | (intros; apply GlobalTheory.CompanionTheory.Herm.apply_eq_zero_of_isotropic <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ v, B v v = 0) → B = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | exact GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero <;> assumption)
end
