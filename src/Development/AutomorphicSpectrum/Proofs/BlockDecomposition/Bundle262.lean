module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle242
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle248
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle244
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem prod_eq_t_mul_unit_count : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  intro l _ ι s t i₀ hi₀ u hprod h0 μ hμ
  have hmax : IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) = Ideal.span {GroundTheory.PAdicHodge.tBdR l} :=
    GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
      GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2 hmax
  have hFB : ∀ k, FB l k = Ideal.span {GroundTheory.PAdicHodge.tBdR l ^ k} := fun k => by
    rw [FB, ker_thB_eq, hmax, Ideal.span_singleton_pow]
  have hnot : ¬ (GroundTheory.PAdicHodge.tBdR l ^ 2 ∣ ∏ μ ∈ s, t μ) := by
    rw [hprod, pow_two]
    intro h
    have h1 : GroundTheory.PAdicHodge.tBdR l ∣ (u : Formalism.Per6.BdRp l) :=
      (mul_dvd_mul_iff_left htirr.ne_zero).1 h
    exact htirr.not_isUnit (isUnit_of_dvd_unit h1 u.isUnit)
  have hi : GroundTheory.PAdicHodge.tBdR l ∣ t i₀ := by
    have : t i₀ ∈ FB l 1 := by
      rw [FB, pow_one, RingHom.mem_ker]; exact h0
    rw [hFB, pow_one] at this
    exact Ideal.mem_span_singleton.1 this
  refine ⟨fun e hm => hnot ?_, fun hne hm => hnot ?_⟩
  · subst e
    rw [hFB] at hm
    exact (Ideal.mem_span_singleton.1 hm).trans (Finset.dvd_prod_of_mem t hμ)
  · rw [hFB, pow_one] at hm
    have hd := Ideal.mem_span_singleton.1 hm
    have hμ' : μ ∈ s.erase i₀ := Finset.mem_erase.2 ⟨hne, hμ⟩
    rw [← Finset.mul_prod_erase s t hi₀, ← Finset.mul_prod_erase (s.erase i₀) t hμ', pow_two, ← mul_assoc]
    exact (mul_dvd_mul hi hd).mul_right _

end GlobalTheory.CompanionTheory.LTPer
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.teichmuller_near_power_exists : ∀ {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)), (∀ a, wB l a ∈ S) → ∀ (ϖ : Formalism.Per6.BdRp l),
    thB l ϖ ≠ 0 → ∀ x : Tl l, ‖thB l (tch l x)‖ < 1 → ∃ M : ℕ, 0 < M ∧ Near S ϖ (FB l 1) 1 (tch l x ^ M) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.TopNil.main | exact GlobalTheory.CompanionTheory.LTPer.TopNil.main | (intros; apply GlobalTheory.CompanionTheory.LTPer.TopNil.main <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem latS_finite_span {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] K'] :
    ∃ T : Finset (Formalism.Per6.BdRp l), (∀ t ∈ T, t ∈ latS K') ∧
      ∀ s ∈ latS K', ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t) := by
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K' (integralClosure ℤ_[l] K')
  have htow : IsScalarTower ℤ_[l] K' (Om l) := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K']
    rfl)
  obtain ⟨b₀, hb₀⟩ := hfin.fg_top
  let ι : ↥(integralClosure ℤ_[l] K') → Formalism.Per6.BdRp l := fun b => rB l ((b : K') : Om l)
  let _ : Algebra (Wl l) (Formalism.Per6.BdRp l) := (wB l).toAlgebra
  have hsm : ∀ (a : Wl l) (x : Formalism.Per6.BdRp l), a • x = wB l a * x := fun a x => Algebra.smul_def a x
  let T : Finset (Formalism.Per6.BdRp l) := b₀.image ι
  let N : Submodule (Wl l) (Formalism.Per6.BdRp l) := Submodule.span (Wl l) (T : Set (Formalism.Per6.BdRp l))
  have hZ : ∀ c : ℤ_[l], rB l (algebraMap ℤ_[l] (Om l) c) =
      wB l (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) := by
    intro c
    have h := GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l c
    have h2 := (GroundTheory.PAdicHodge.algClToBdR l).commutes (c : ℚ_[l])
    exact h2.trans h
  have hιmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => by simp [ι]
  have hO : ∀ z, ι z ∈ N := by
    intro z
    have hz : z ∈ Submodule.span ℤ_[l] (b₀ : Set ↥(integralClosure ℤ_[l] K')) := hb₀ ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
    | zero => simp [ι]
    | add x y _ _ hx hy =>
      have e : ι (x + y) = ι x + ι y := by simp [ι]
      rw [e]; exact N.add_mem hx hy
    | smul c x _ hx =>
      have e : ι (c • x) = (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) • ι x := by
        rw [hsm, ← hZ]
        have e2 : (((c • x : ↥(integralClosure ℤ_[l] K')) : K') : Om l) =
            algebraMap ℤ_[l] (Om l) c * ((x : K') : Om l) := by
          have : ((c • x : ↥(integralClosure ℤ_[l] K')) : K') = c • (x : K') := rfl
          rw [this, Algebra.smul_def, IntermediateField.coe_mul]
          exact congrArg (· * ((x : K') : Om l)) (IsScalarTower.algebraMap_apply ℤ_[l] K' (Om l) c).symm
        simp only [ι, e2, map_mul]
      rw [e]; exact N.smul_mem _ hx
  have hmul : N * N ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    change ι b * ι b' ∈ N
    rw [← hιmul]
    exact hO _
  have h1 : (1 : Formalism.Per6.BdRp l) ∈ N := by
    have := hO 1
    simpa [ι] using this
  have hint : ∀ b : ↥(integralClosure ℤ_[l] K'), IsIntegral ℤ_[l] ((b : K') : Om l) := fun b =>
    (isIntegral_algebraMap_iff (A := K') (B := Om l) ).2 b.2
  have hS : ∀ x ∈ latS K', x ∈ N := by
    intro x hx
    unfold latS at hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨y, ⟨hyK, hyI⟩, rfl⟩
      · have := N.smul_mem a h1
        rwa [hsm, mul_one] at this
      · have hz : IsIntegral ℤ_[l] (⟨y, hyK⟩ : K') :=
          (isIntegral_algebraMap_iff (A := K') (B := Om l) ).1 hyI
        exact hO ⟨⟨y, hyK⟩, hz⟩
    | zero => exact N.zero_mem
    | one => exact h1
    | add _ _ _ _ hx hy => exact N.add_mem hx hy
    | neg _ _ hx => exact N.neg_mem hx
    | mul _ _ _ _ hx hy => exact hmul (Submodule.mul_mem_mul hx hy)
  refine ⟨T, ?_, ?_⟩
  · intro t ht
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ht
    exact rB_mem_latS K' (b : K').2 (hint b)
  · intro x hx
    obtain ⟨f, _, hf⟩ := Submodule.mem_span_finset.1 (hS x hx)
    exact ⟨f, by rw [← hf]; exact Finset.sum_congr rfl (fun t _ => by rw [hsm, mul_comm])⟩

end GlobalTheory.CompanionTheory.LTPer
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma sr_window {R a : ℝ} (h : R < a) : ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ (∀ s, 0 ≤ β s) ∧ 0 < β a ∧
    (∀ s, s ≤ R → β s = 0) ∧ ∀ s, a + 1 ≤ s → β s = 0 := by
  refine ⟨fun s => Real.smoothTransition (s - R) * Real.smoothTransition (a + 1 - s), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
  · intro s
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
      (Real.smoothTransition.pos_of_pos (by linarith))
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show s - R ≤ 0 by linarith), zero_mul]
  · intro s hs
    simp only [Real.smoothTransition.zero_of_nonpos (show a + 1 - s ≤ 0 by linarith), mul_zero]

lemma sr_inner_cls {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {f g : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hg : MemLp (fun y : G n => g y.val) 2 μ) :
    Integrable (fun y : G n => ⟪f y.val, g y.val⟫_ℂ) μ ∧
      ⟪cls μ f, cls μ g⟫_ℂ = ∫ y : G n, ⟪f y.val, g y.val⟫_ℂ ∂μ := by
  have e1 : cls μ f = hf.toLp _ := dif_pos hf
  have e2 : cls μ g = hg.toLp _ := dif_pos hg
  have hae : (fun y : G n => ⟪(hf.toLp _ : Lp V 2 μ) y, (hg.toLp _ : Lp V 2 μ) y⟫_ℂ) =ᵐ[μ]
      fun y : G n => ⟪f y.val, g y.val⟫_ℂ := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y a b
    rw [a, b]
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) (hf.toLp _) (hg.toLp _)).congr hae, ?_⟩
  rw [e1, e2, L2.inner_def]
  exact integral_congr_ae hae

lemma sr_val_mem {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

lemma sr_eq_zero {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {ψ : G n → ℝ} (hc : Continuous ψ) (h0 : ∀ y, 0 ≤ ψ y) (hi : Integrable ψ μ) (hz : ∫ y, ψ y ∂μ = 0) :
    ∀ y, ψ y = 0 := by
  have hae : ψ =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg h0 hi).1 hz
  have := (Continuous.ae_eq_iff_eq μ hc continuous_zero).1 hae
  intro y
  rw [this]
  rfl

theorem supportRow : SupportRow := by
  intro n _ _ μ _ E _ Ω T F c hStd g T₀ h hg hh H
  obtain ⟨hLg, hUn, hRC, hSobG, hAlg, hWS, hWC, hCS, hSO, hPW, -, -, -, -, hOm, -⟩ := hStd
  have hCptSob : CptSob := hCS.2.2.2.2.2.2.1
  obtain ⟨c₀, hc₀⟩ := hWS n
  refine ⟨|c₀| * (1 + |T₀|), ?_⟩
  intro v f hRow y₀ hy₀ hR
  obtain ⟨hfSob, hfSec, hfRow⟩ := hRow
  obtain ⟨β, hβs, hβ0, hβpos, hβlo, hβhi⟩ := sr_window hR
  obtain ⟨-, -, hLk, hLs, -, -, -⟩ := hLg n
  set φ : Mat n → E.V := fun y => ((β (lg y) : ℝ) : ℂ) • f y with hφ

  have hφs : ContDiffOn ℝ ∞ φ (GLs n) := by
    have h1 : ContDiffOn ℝ ∞ (fun y : Mat n => ((β (lg y) : ℝ) : ℂ)) (GLs n) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hβs.comp_contDiffOn hLs)
    exact h1.smul hfSob.1
  have hφsec : IsSec E φ := by
    intro y hy k
    have hl : lg (y * k.1) = lg y := by
      have := hLk y hy 1 k
      simpa using this
    simp only [hφ, hl, hfSec y hy k, map_smul]
  have hφc : Cpt φ := by
    refine ⟨lg y₀ + 1, fun y _ hy => ?_⟩
    simp only [hφ, hβhi _ hy.le, Complex.ofReal_zero, zero_smul]
  have hφCE : φ ∈ CE E := ⟨hφs, hφsec⟩
  have hφSob : Sob μ φ := (hCptSob n μ E.V hLg hRC φ hφs hφc).1
  obtain ⟨u, huW, hu0⟩ := hWC n E φ hφCE hφc
  obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSobG hAlg hCS hOm h hh
  obtain ⟨f', hf'Sob, hf'Sec, hf'cls, -⟩ := hC (cls μ φ) (subset_closure ⟨φ, hφSob, hφsec, rfl⟩)
  have h1G : (1 : Mat n) ∈ GLs n := by
    show (1 : Mat n).det ≠ 0
    simp

  have hf'1 : f' 1 = 0 := by
    rw [← H φ hφCE hφc u huW hu0 f' hf'Sob hf'Sec hf'cls 1 h1G]
    have : ∀ t, (g t : ℂ) • u t 1 = 0 := by
      intro t
      by_cases hgt : g t = 0
      · simp [hgt]
      · have ht : |t| ≤ T₀ := by
          by_contra hcon
          exact hgt (hg.2.2 t (not_le.1 hcon))
        have hut : u t 1 = 0 := by
          refine hc₀ E u huW t 1 h1G fun y hy hly => ?_
          rw [one_mul, hu0 y hy]
          have hb : lg y ≤ |c₀| * (1 + |T₀|) := by
            refine hly.trans ?_
            have h1 : c₀ ≤ |c₀| := le_abs_self _
            have h2 : |t| ≤ |T₀| := ht.trans (le_abs_self _)
            have h3 : 0 ≤ |c₀| := abs_nonneg _
            have h4 : 0 ≤ |t| := abs_nonneg _
            nlinarith
          simp only [hφ, hβlo _ hb, Complex.ofReal_zero, zero_smul]
        simp [hut]
    simp [this]
  have hzero : ⟪cls μ f, cls μ φ⟫_ℂ = 0 := by
    rw [hfRow φ f' hφSob hφsec hf'Sob hf'Sec hf'cls, hf'1, inner_zero_right]

  have hfL : MemLp (fun y : G n => f y.val) 2 μ := hfSob.2 []
  have hφL : MemLp (fun y : G n => φ y.val) 2 μ := hφSob.2 []
  obtain ⟨hI, hE⟩ := sr_inner_cls μ hfL hφL
  set ψ : G n → ℝ := fun y => β (lg y.val) * ‖f y.val‖ ^ 2 with hψ
  have hpt : ∀ y : G n, ⟪f y.val, φ y.val⟫_ℂ = (ψ y : ℂ) := by
    intro y
    simp only [hφ, hψ, inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hψi : Integrable ψ μ := by
    have := hI.re
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [hpt y]
  have hψz : ∫ y, ψ y ∂μ = 0 := by
    have h2 : ((∫ y, ψ y ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hzero, hE]
      exact integral_congr_ae (Eventually.of_forall fun y => (hpt y).symm)
    exact_mod_cast h2
  have hlc : Continuous (fun y : G n => lg y.val) :=
    hLs.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hfc : Continuous (fun y : G n => f y.val) :=
    hfSob.1.continuousOn.comp_continuous Units.continuous_val sr_val_mem
  have hψc : Continuous ψ := (hβs.continuous.comp hlc).mul (hfc.norm.pow 2)
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (hβ0 _) (by positivity)
  have hall := sr_eq_zero μ hψc hψ0 hψi hψz
  have := hall (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀)
  have hval : (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ hy₀ : G n).val = y₀ := rfl
  simp only [hψ, hval] at this
  rcases mul_eq_zero.1 this with h' | h'
  · exact absurd h' hβpos.ne'
  · simpa using h'

end GlobalTheory.CompanionTheory.KerFc
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTranslateSobolev

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem val_mem (x : G n) : x.val ∈ GLs n := by
  have h := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  exact h.ne_zero

def mulL (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := fun y z => Matrix.mul_add a y z
      map_smul' := fun c y => Matrix.mul_smul a c y }

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (lTr x f) (GLs n) :=
  hf.comp (mulL x.val).contDiff.contDiffOn (fun _ hy => mul_mem (val_mem x) hy)

theorem Rd_lTr (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n)
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (lTr x f) g = Rd X f (x.val * g) := by
  have hxg : x.val * g ∈ GLs n := mul_mem (val_mem x) hg
  have hd : DifferentiableAt ℝ f (mulL x.val g) :=
    (hf.contDiffAt ((isOpen_GLs n).mem_nhds hxg)).differentiableAt (by simp)
  have hc : fderiv ℝ (f ∘ mulL x.val) g = (fderiv ℝ f (mulL x.val g)).comp (mulL x.val) :=
    (hd.hasFDerivAt.comp g (mulL x.val).hasFDerivAt).fderiv
  show fderiv ℝ (f ∘ mulL x.val) g (g * X) = fderiv ℝ f (x.val * g) (x.val * g * X)
  rw [hc]
  simp [mulL, Matrix.mul_assoc]

theorem contDiffOn_Rw (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact ((hR n).1 V (Rw w f) ih).1 (bs p)

theorem Rw_lTr (hR : RCalc) (x : G n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Bool × Fin n × Fin n)) : ∀ g ∈ GLs n, Rw w (lTr x f) g = Rw w f (x.val * g) := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have he : Rw w (lTr x f) =ᶠ[𝓝 g] lTr x (Rw w f) :=
      Filter.eventuallyEq_of_mem ((isOpen_GLs n).mem_nhds hg) (fun y hy => ih y hy)
    show Rd (bs p) (Rw w (lTr x f)) g = Rd (bs p) (Rw w f) (x.val * g)
    rw [← Rd_lTr x (contDiffOn_Rw hR hf w) (bs p) hg]
    show fderiv ℝ (Rw w (lTr x f)) g (g * bs p) = fderiv ℝ (lTr x (Rw w f)) g (g * bs p)
    rw [he.fderiv_eq]

end LeftTranslateSobolev


open LeftTranslateSobolev in
theorem ltSob : LtSob := by
  intro n _ _ μ _ V _ _ _ _ hR x f hf
  refine ⟨⟨contDiffOn_lTr x hf.1, fun w => ?_⟩, fun g hg => ?_⟩
  · have h := (hf.2 w).comp_measurePreserving (measurePreserving_mul_left μ x)
    have he : (fun y : G n => Rw w (lTr x f) y.val) = (fun y : G n => Rw w f y.val) ∘ (fun y => x * y) :=
      funext fun y => Rw_lTr hR x hf.1 w y.val (val_mem y)
    rw [he]
    exact h
  · have ht : ∀ s, gel s 2 (lTr x f) g = gel s 2 f (x.val * g) := fun s =>
      (((hR n).1 V f hf.1).2.2.2 s 2 x.val (val_mem x) g hg).1
    simp only [Om, Pi.smul_apply, Pi.add_apply, ht]

end GlobalTheory.CompanionTheory.KerFc
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowExists_of_factor (hFac : FactorRapid) (hEv : EvAdj) : RowExists := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  have hS' := hS
  obtain ⟨hLg, hUn, hRC, hSG, hAE, -, -, hCS, hSO, -, -, -, -, -, hOm, -⟩ := hS'
  obtain ⟨h₁, h₂, r₁, r₂, r₂s, rfl⟩ := hFac h hh
  obtain ⟨κ, hκ, hrow⟩ := hEv n μ E Ω T F c hS h₁ r₁ v
  obtain ⟨C₁, hC₁⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (star h₂) r₂s
  obtain ⟨C₂, hC₂⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h₂ r₂
  obtain ⟨f, hfS, hfE, hfc, -⟩ := hC₁ κ hκ
  refine ⟨f, hfS, hfE, ?_⟩
  intro φ f' hφS hφE hf'S hf'E hf'
  obtain ⟨φ₂, hφ₂S, hφ₂E, hφ₂c, -⟩ := hC₂ (cls μ φ) (subset_closure ⟨φ, hφS, hφE, rfl⟩)
  have hmul : cls μ f' = F.Φ h₁ (cls μ φ₂) := by
    rw [hf', F.map_mul, hφ₂c]
    rfl
  rw [hfc, F.map_star, ContinuousLinearMap.adjoint_inner_left, ← hφ₂c]
  exact hrow φ₂ f' hφ₂S hφ₂E hf'S hf'E hmul

end GlobalTheory.CompanionTheory.KerFc
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.compatible_roots_lift_to_tilt : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U), (∀ i, u (i + 1) ^ l = u i) → ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp | exact GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp | (intros; apply GlobalTheory.CompanionTheory.Untilt.exists_compatible_roots_of_sharp <;> assumption)
end
