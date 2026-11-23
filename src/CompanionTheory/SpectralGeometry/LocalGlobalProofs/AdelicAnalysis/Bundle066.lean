module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle065
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle064
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle031
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.denominator_power_summable : ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.DenSum.summable_den | exact GlobalTheory.CompanionTheory.SW.DenSum.summable_den | (intros; apply GlobalTheory.CompanionTheory.SW.DenSum.summable_den <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageMeasure

theorem measurable_consTup {K : Type} [Zero K] [One K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (consTup : (Fin n → Fin M → K) → Fin (n + 1) → Fin (M + 1) → K) := by
  refine measurable_pi_iff.2 fun a => ?_
  refine Fin.cases ?_ (fun a => ?_) a
  · exact measurable_const
  · refine measurable_pi_iff.2 fun i => ?_
    refine Fin.cases ?_ (fun i => ?_) i
    · exact measurable_const
    · exact (measurable_pi_apply i).comp (measurable_pi_apply a)

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_first (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (s : E) :
    gramR R σ (blockOne s J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      fun _ _ => inclR R s := by
  funext a b
  simp only [gramR, hR, hform]
  rw [Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ, JR, blockOne]

theorem inclR_algebraMap (R : Type) [CommRing R] [Algebra F R] (t : F) :
    inclR (F := F) (E := E) R (algebraMap F E t) = algebraMap F R t ⊗ₜ[F] (1 : E) := by
  show (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory.CompanionTheory.SW.StageMeasure

namespace GlobalTheory.CompanionTheory.SW


open GlobalTheory.CompanionTheory.SW.StageMeasure in

theorem fibre_block_stages : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hTd hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hJ t ht
  obtain ⟨g₁, g₂, g₃, g₄, g₅, gAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hJ' R
  obtain ⟨u₁, u₂, u₃, u₄, u₅, uAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ R
  have hgram : gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    rw [gram_first, inclR_algebraMap]
    rfl
  have hunit : IsUnit (gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))).det := by
    rw [gram_first]
    have e := Matrix.det_fin_one (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t))
    show IsUnit (Matrix.det (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t)))
    rw [e]
    exact ((isUnit_iff_ne_zero.2 (by simpa using ht)).map (inclR (F := F) R))
  obtain ⟨s, hsm, hs₁, hs₂⟩ := GlobalTheory.T.rank_one_gram_measurable_section F E σ hCM (M + 1) _ hJ' R hR _ hunit
  have hs₁' := fun y (hy : gramR R σ (blockOne (algebraMap F E t) J) y =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1)) => hs₁ y (hy.trans hgram.symm)
  have hs₂' : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
      ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
        gramR R σ (blockOne (algebraMap F E t) J) y =
          (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C' := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hs₂ C hC
    exact ⟨C', hC', fun y hy hg => h y hy (hg.trans hgram.symm)⟩
  obtain ⟨B, hBo, hTB, hBu, fib, hfib, hfibT⟩ := GlobalTheory.T.exists_fibre_family_block_one_eq_map_prod F E σ hCM M J hJ t ht n T hT hTd hT' R hR
    d b lam hlam m₁ m' hm₁ hm' c hc s hsm hs₁' hs₂'
  obtain ⟨h₁, h₂, h₃, h₄, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hlift (M + 1) _ hJ'
  have hB₀ : IsOpen {S : HermR R σ (n + 1) | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det} := by
    have hop : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM R hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    exact hop.preimage (Continuous.matrix_det continuous_subtype_val)
  have hWn := hW (n + 1) (M + 1)
  have hHn := hH (n + 1)
  have hBn := hBorel (n + 1) (M + 1)
  have hU : {X | IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} =
      g ⁻¹' {S : HermR R σ (n + 1) | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det} := by
    ext X
    simp [hg X]
  have hU' : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B) = g ⁻¹' B := by
    ext X
    simp [hg X]
  have hm₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val
      (g ⁻¹' {S : HermR R σ (n + 1) | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det})
      (coordHerm R σ b lam (n + 1)) {S | IsUnit (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)).det} m := by
    rw [← hU]
    exact hm
  rw [hU'] at hfib
  have hmT : fib (hermOf R σ _ hT') = m (hermOf R σ _ hT') :=
    GlobalTheory.T.fibre_family_eq_on_open_subset _ _ _ (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) g Subtype.val Subtype.val_injective hgc hg _ B hB₀ hBo hBu
      m fib hm₀ hfib _ hTB
  have hBa := hBorel (n + 1) (M + 1)
  have hBb := hBorel n M
  have hact : Measurable fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ p.1 p.2 := (gAct (n + 1)).1.measurable
  have hactu : ∀ u : HA R σ J, Measurable (actW R σ J u : (Fin n → Fin M → R ⊗[F] E) → Fin n → Fin M → R ⊗[F] E) :=
    fun u => ((uAct n).1.comp (Continuous.prodMk_right u)).measurable
  have hframe : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      actW R σ _ (s p.1) (consTup p.2) :=
    hact.comp ((hsm.comp measurable_fst).prodMk (measurable_consTup.comp measurable_snd))
  have hF : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      φ (actW R σ _ (s p.1) (consTup p.2)) := hφ.comp hframe
  have hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ R hR n _ _ m' (hW n M) (hH n) hm' (hermOf R σ T hT)).1
  refine ⟨fun y => ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT)),
    hF.lintegral_prod_right', ?_, ?_⟩
  · intro h
    obtain ⟨ι, -, hιm, hιr, -, hιa⟩ := GlobalTheory.CompanionTheory.SW.StabFirst.stab_first F E σ hCM M J hJ t ht R
    have hy := hs₁' (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0)))
      (((gAct 1).2.2.2 h _).trans hgram)
    set y := actW R σ _ h (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) with hydef
    have hfix : actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      calc actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))
          = actW R σ _ (s y)⁻¹ y := (gAct 1).2.2.1 _ _ _
        _ = actW R σ _ (s y)⁻¹ (actW R σ _ (s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))) := by
            rw [hy]
        _ = actW R σ _ ((s y)⁻¹ * s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) :=
            ((gAct 1).2.2.1 _ _ _).symm
        _ = _ := by rw [inv_mul_cancel, (gAct 1).2.1]
    obtain ⟨u, hu⟩ := (hιr _).2 hfix
    have hh : h = s y * ι u := by rw [hu, mul_inv_cancel_left]
    have hX : ∀ X : Fin n → Fin M → R ⊗[F] E,
        actW R σ _ h (consTup X) = actW R σ _ (s y) (consTup (actW R σ J u X)) := by
      intro X
      rw [hh, (gAct (n + 1)).2.2.1, hιa]
    have hinv := GlobalTheory.T.gram_fiber_measures_invariant F E σ hCM M J hJ R hR n _ _ m' (hW n M) (hH n) hm' u (hermOf R σ T hT)
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => φ (actW R σ _ (s y) (consTup X)) :=
      hφ.comp (hact.comp ((measurable_const (a := s y)).prodMk measurable_consTup))
    calc ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT))
        = ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂((m' (hermOf R σ T hT)).map (actW R σ J u)) := by rw [hinv]
      _ = ∫⁻ X, φ (actW R σ _ (s y) (consTup (actW R σ J u X))) ∂(m' (hermOf R σ T hT)) :=
          lintegral_map hmeas (hactu u)
      _ = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT)) := by simp only [hX]
  · rw [← hmT, hfibT, lintegral_smul_measure, lintegral_map hφ hframe, lintegral_prod _ hF.aemeasurable]
    simp [ENNReal.smul_def]

end GlobalTheory.CompanionTheory.SW
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.trace_form_rational_theta_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) → ∀ (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (a : ℕ), 0 < a → ∀ β : F, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}}, ENNReal.ofReal (gaussQ e b Pm (projInf X)) ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β}) = ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : Fin M × Fin d → F | ∀ i v, ((a : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf e σ J b ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂(prH μ 𝓕) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss | exact GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ThetaGauss.lintegral_thetaMeas_gauss <;> assumption)
end

end

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.local_density_block_one_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.fibre_block_stages | exact GlobalTheory.CompanionTheory.SW.fibre_block_stages | (intros; apply GlobalTheory.CompanionTheory.SW.fibre_block_stages <;> assumption)

end
end
