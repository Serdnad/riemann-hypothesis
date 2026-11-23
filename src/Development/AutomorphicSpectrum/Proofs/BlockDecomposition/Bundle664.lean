module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductPushforward
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle651
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle535
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle575
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle504
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle652
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle653
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle655
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle656
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.FoldF

theorem foldF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ S, ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∂(coordHerm R σ b lam (n + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hσ := D.hCM
  have hlam := D.hlam
  haveI := hlam
  obtain ⟨hKring, hKlc, hKsc, hKt2, hsig, htr, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hKring
  haveI := hKlc
  haveI := hKsc
  haveI := hKt2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hκh, -, hνh⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam hlam
  haveI := hκh
  haveI hHb : ∀ m, BorelSpace (HermR R σ m) := fun _ => ⟨rfl⟩
  haveI hHlc : ∀ m, LocallyCompactSpace (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).1
  haveI hHsc : ∀ m, SecondCountableTopology (HermR R σ m) := fun m =>
    (GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R m).2.1
  haveI : (coordHerm R σ b lam n).IsAddHaarMeasure := hνh n
  haveI : SigmaFinite (coordK R b lam) := inferInstance
  haveI : SigmaFinite (coordHerm R σ b lam n) := inferInstance
  obtain ⟨e, he00, he0j, heij, hemap⟩ := GlobalTheory.T.coordinate_homeomorph_tensor_product_measure F E σ hσ R d b lam hlam n
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hs0c, hacS, hcvc, hschc, -⟩ :=
    GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hBopen : IsOpen (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := D.hB₀.preimage hs0c
  have hGon0 := GlobalTheory.T.fibre_measure_extension_by_one_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hmeas := GlobalTheory.T.fibre_measure_extension_symmetric F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  have hsubst := GlobalTheory.T.lintegral_coordK_coordHerm_scale_shear F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hGoff0 : ∀ S, S ∉ BsetF R σ B₀ →
      ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = 0 := by
    intro S hS
    have h0 : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = 0 := by
      unfold fibSF
      exact Set.indicator_of_notMem hS _
    rw [h0, lintegral_zero_measure]
  obtain ⟨G, hG⟩ : ∃ G : HermR R σ (n + 1) → ℝ≥0∞,
      G = fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) := ⟨_, rfl⟩
  have hGoff : ∀ S, S ∉ BsetF R σ B₀ → G S = 0 := by
    intro S hS
    rw [hG]
    exact hGoff0 S hS
  have hGon : ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), G S =
      (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) *
      (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n *
      Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R)
        (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
    intro S hS
    rw [hG]
    exact hGon0 S hS
  show ∫⁻ S, (fun S => ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S)) S ∂(coordHerm R σ b lam (n + 1)) = _
  rw [← hG]
  clear hGon0 hGoff0 hG
  have hGm : Measurable G := by
    refine measurable_of_restrict_of_restrict_compl hBopen.measurableSet ?_ ?_
    · have hsub : (BsetF R σ B₀ : Set (HermR R σ (n + 1))) ⊆
          {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S h => h
      have hk := continuousOn_iff_continuous_restrict.1 (hacS.mono hsub)
      have hc := continuousOn_iff_continuous_restrict.1 (hcvc.mono hsub)
      have hw := continuousOn_iff_continuous_restrict.1 (hschc.mono hsub)
      have hP := hmeas.comp (((Units.continuous_val.comp hk).prodMk (hc.prodMk hw)).measurable)
      have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1))).domRestrict G = _ :=
        funext fun S => hGon S S.2
      rw [hE]
      exact (((ENNReal.continuous_coe.comp (D.hκc.comp hk)).measurable).mul
        (((ENNReal.continuous_coe.comp (D.hcmc.comp hk)).measurable).pow_const n)).mul hP
    · have hE : (BsetF R σ B₀ : Set (HermR R σ (n + 1)))ᶜ.domRestrict G = fun _ => 0 :=
        funext fun S => hGoff S S.2
      rw [hE]
      exact measurable_const
  have hL : ∫⁻ S, G S ∂(coordHerm R σ b lam (n + 1)) =
      ∫⁻ x, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := by
    have hGe : Measurable (fun p => G (e p)) := hGm.comp e.continuous.measurable
    rw [← hemap, lintegral_map hGm e.continuous.measurable, lintegral_prod _ hGe.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact lintegral_prod _ (hGe.comp measurable_prodMk_left).aemeasurable
  have hs0 : ∀ p, s0 R (e p : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = p.1 :=
    fun p => Fold.corner_half_trace_of_cm_pure_tensor R σ hσ _ _ (he00 p)
  have hoff : ∀ x, x ∉ B₀ → ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = 0 := by
    intro x hx
    have h0 : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) = 0 := by
      intro r S''
      refine hGoff _ fun h => hx ?_
      have h1 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ := h
      rwa [hs0] at h1
    simp [h0]
  have hon : ∀ x ∈ B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
      ∂(Measure.pi fun _ => coordK R b lam) = (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E,
        ∫⁻ S', Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) := by
    intro x hx
    obtain ⟨u, hu⟩ : ∃ u : Rˣ, u = a x := ⟨_, rfl⟩
    rw [← hu]
    obtain ⟨cr, hcrdef⟩ : ∃ cr : (Fin n → R ⊗[F] E) → Fin n → R ⊗[F] E,
        cr = fun r j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) := ⟨_, rfl⟩
    have hcr : Continuous cr := by
      rw [hcrdef]
      exact continuous_pi fun j => continuous_const.mul (continuous_apply j)
    let w : (Fin n → R ⊗[F] E) → HermR R σ n := fun r => ⟨Fold.qM R σ t (cr r), Fold.qM_mem R σ hσ t _⟩
    have hw : Measurable w := by
      have hwc : Continuous w := by
        refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
        exact ((hsig.comp ((continuous_apply i).comp hcr)).mul continuous_const).mul
          ((continuous_apply j).comp hcr)
      exact hwc.measurable
    let f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞ := fun z =>
      Pint σ J t m₁ m' s φ (u : R) z.1 z.2
    have hf : Measurable f :=
      hmeas.comp (measurable_const.prodMk measurable_id)
    have hpt : ∀ (r : Fin n → R ⊗[F] E) (S'' : HermR R σ n), G (e (x, r, S'')) =
        ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r) := by
      intro r S''
      have h0 : s0 R (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = x := hs0 _
      have h1 : cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = cr r := by
        funext j
        rw [hcrdef]
        show ((((a (s0 R _))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * _ = _
        rw [h0, he0j, ← hu]
      have h2 : schur R σ t a (e (x, r, S'')) = S'' - w r := by
        rw [Fold.schur_split R σ hσ t a (e (x, r, S'')) S'' (heij (x, r, S''))]
        have h3 : (⟨Fold.qM R σ t (cvec R t a (e (x, r, S'') : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))),
            Fold.qM_mem R σ hσ t _⟩ : HermR R σ n) = w r := Subtype.ext (congrArg (Fold.qM R σ t) h1)
        rw [h3]
      have hB : e (x, r, S'') ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := by
        show s0 R _ ∈ B₀
        rw [h0]
        exact hx
      rw [hGon _ hB, h0, h1, h2, ← hu]
    have hC : ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hS : ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) =
        (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by
      rw [hcrdef]
      exact hsubst u w hw f hf
    calc ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam)
        = ∫⁻ r, ∫⁻ S'', ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [hpt]
      _ = ((κ₁ u : ℝ≥0∞) * (cm u : ℝ≥0∞) ^ n) * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
          simp only [lintegral_const_mul' _ _ hC]
      _ = (κ₁ u : ℝ≥0∞) * ((cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (cr r, S'' - w r)
          ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam)) := mul_assoc _ _ _
      _ = (κ₁ u : ℝ≥0∞) * ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n)
          ∂(Measure.pi fun _ => coordK R b lam) := by rw [hS]
      _ = _ := rfl
  rw [hL]
  unfold MidF
  calc _ = ∫⁻ x, B₀.indicator (fun x => ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam)) x ∂lam := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ B₀
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hoff x hx]
    _ = ∫⁻ x in B₀, ∫⁻ r, ∫⁻ S'', G (e (x, r, S'')) ∂(coordHerm R σ b lam n)
        ∂(Measure.pi fun _ => coordK R b lam) ∂lam := lintegral_indicator D.hB₀.measurableSet _
    _ = _ := setLIntegral_congr_fun D.hB₀.measurableSet hon

end GlobalTheory.CompanionTheory.SW.StageF.FoldF
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Isotypic

variable {n : ℕ}

theorem exists_map_out (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (d : H) (hd : Formalism.REAL.KHighest (fun _ => true) G μ d) :
    ∃ T : L →ₗ[ℂ] H, T v = d ∧ ∀ a b w, T (K a b w) = G a b (T w) := by
  have hsp : ∀ x ∈ Submodule.span ℂ {v}, Formalism.REAL.KHighest (fun _ => true) K μ x := by
    intro x hx
    have hvm : v ∈ hwOf K μ := hv
    have : x ∈ hwOf K μ := (Submodule.span_singleton_le_iff_mem v (hwOf K μ)).2 hvm hx
    exact this
  let f : (Submodule.span ℂ {v}) →ₗ[ℂ] H :=
    ((innerₛₗ ℂ v).comp (Submodule.subtype _)).smulRight ((⟪v, v⟫_ℂ)⁻¹ • d)
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) G μ (f x) := by
    intro x
    have hdm : d ∈ hwOf G μ := hd
    have : f x ∈ hwOf G μ := by
      simp only [f, LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hdm)
    exact this
  obtain ⟨T, hT, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition L H K G μ hK hG hKs hGs (Submodule.span ℂ {v}) hsp f hf
  refine ⟨T, ?_, hi⟩
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have := hT ⟨v, Submodule.mem_span_singleton_self v⟩
  simp only at this
  rw [this]
  simp only [f, LinearMap.smulRight_apply, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply]
  rw [smul_smul, mul_inv_cancel₀ hvv, one_smul]

theorem exists_map_in (H L : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ : Fin n → ℝ)
    (hG : Formalism.REAL.GlRel G) (hK : Formalism.REAL.GlRel K)
    (hGs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ)
    (v : L) (hv : Formalism.REAL.KHighest (fun _ => true) K μ v)
    (D : Submodule ℂ H) (hD : ∀ x ∈ D, Formalism.REAL.KHighest (fun _ => true) G μ x) (φ : D →ₗ[ℂ] ℂ) :
    ∃ P : H →ₗ[ℂ] L, (∀ d : D, P d = φ d • v) ∧ ∀ a b w, P (G a b w) = K a b (P w) := by
  have hf : ∀ x, Formalism.REAL.KHighest (fun _ => true) K μ (φ.smulRight v x) := by
    intro x
    have hvm : v ∈ hwOf K μ := hv
    have : φ.smulRight v x ∈ hwOf K μ := by
      simp only [LinearMap.smulRight_apply]
      exact Submodule.smul_mem _ _ hvm
    exact this
  obtain ⟨P, hP, hi⟩ := GlobalTheory.T.highest_weight_tensor_decomposition H L G K μ hG hK hGs hKs D hD (φ.smulRight v) hf
  exact ⟨P, fun d => by rw [hP d, LinearMap.smulRight_apply], hi⟩

theorem eq_smul_id_of_apply (L : Type) [NormedAddCommGroup L] [InnerProductSpace ℂ L] [FiniteDimensional ℂ L]
    (K : Fin n → Fin n → Module.End ℂ L) (hK : Formalism.REAL.GlRel K)
    (hKs : ∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) (v : L)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (R : L →ₗ[ℂ] L) (hR : ∀ a b w, R (K a b w) = K a b (R w)) (r : ℂ) (hr : R v = r • v) :
    R = r • LinearMap.id := by
  have h0 := GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest L L K K hK hKs (R - r • LinearMap.id)
    (fun a b w => by simp [hR, map_smul]) (fun μ w hw => by
      obtain ⟨c, rfl⟩ := huniq w (fun a b hab => hw.2 a b hab rfl)
      simp [hr, smul_comm c r])
  exact sub_eq_zero.1 h0

theorem map_highest_eq_zero {H L : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup L] [Module ℂ L]
    (G : Fin n → Fin n → Module.End ℂ H) (K : Fin n → Fin n → Module.End ℂ L) (μ μ' : Fin n → ℝ)
    (v : L) (hv0 : v ≠ 0) (hv : Formalism.REAL.KHighest (fun _ => true) K μ' v)
    (huniq : ∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v)
    (P : H →ₗ[ℂ] L) (hP : ∀ a b w, P (G a b w) = K a b (P w))
    (hne : μ ≠ μ') (w : H) (hw : Formalism.REAL.KHighest (fun _ => true) G μ w) : P w = 0 := by
  obtain ⟨c, hc⟩ := huniq (P w) (fun a b hab => by rw [← hP, hw.2 a b hab rfl, map_zero])
  by_contra hne0
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne0 (by simpa using hc)
  apply hne
  funext a
  have h1 : K a a (P w) = (μ a : ℂ) • P w := by rw [← hP, hw.1 a, map_smul]
  rw [hc, map_smul, hv.1 a, smul_comm] at h1
  have h2 : ((μ' a : ℂ) - (μ a : ℂ)) • (c • v) = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : (μ' a : ℂ) - (μ a : ℂ) = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h (smul_ne_zero hc0 hv0)
  have h4 : (μ' a : ℂ) = (μ a : ℂ) := sub_eq_zero.1 h3
  exact (Complex.ofReal_injective h4).symm

theorem map_mem_hwOf {H : Type} [AddCommGroup H] [Module ℂ H]
    (G : Fin n → Fin n → Module.End ℂ H) (μ : Fin n → ℝ) (S : H →ₗ[ℂ] H)
    (hS : ∀ a b w, S (G a b w) = G a b (S w)) (x : H) (hx : x ∈ hwOf G μ) : S x ∈ hwOf G μ :=
  ⟨fun a => by rw [← hS, hx.1 a, map_smul],
    fun a b hab he => by rw [← hS, hx.2 a b hab he, map_zero]⟩

theorem exists_isotypic_projection {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H))
    (G : Fin n → Fin n → Module.End ℂ H) (ν : Fin n → ℤ) :
    Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) →
    (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) →
    Antitone ν →
    ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧ (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  intro hG hGs hder hν
  obtain ⟨L, _, _, _, σ, K, v, hK, hKs, hσ, hv0, hv, huniq, htr⟩ := GlobalTheory.T.exists_highest_weight_hermitian_derivation ν hν
  have hD : ∀ x ∈ hwOf G (wtR ν), Formalism.REAL.KHighest (fun _ => true) G (wtR ν) x := fun x hx => hx
  let b := Module.finBasis ℂ (hwOf G (wtR ν))
  have ex1 : ∀ j, ∃ T : L →ₗ[ℂ] H, T v = (b j : H) ∧ ∀ a c w, T (K a c w) = G a c (T w) := fun j =>
    exists_map_out H L G K (wtR ν) hG hK hGs hKs v hv0 hv (b j : H) (b j).2
  choose T hTv hTi using ex1
  have ex2 : ∀ j, ∃ P : H →ₗ[ℂ] L, (∀ d : hwOf G (wtR ν), P d = b.coord j d • v) ∧
      ∀ a c w, P (G a c w) = K a c (P w) := fun j =>
    exists_map_in H L G K (wtR ν) hG hK hGs hKs v hv _ hD (b.coord j)
  choose P hPd hPi using ex2
  have hPk : ∀ j k w, P j (ρ k w) = σ k (P j w) := fun j =>
    GlobalTheory.T.derivative_unitary_action H L ρ G hder σ K hσ hKs (P j) (hPi j)
  have hp : ∀ w, (∑ j, T j ∘ₗ P j) w = ∑ j, T j (P j w) := fun w => by
    simp [LinearMap.sum_apply]
  refine ⟨∑ j, T j ∘ₗ P j, ?_, ?_, ?_, ?_⟩
  · intro a c w

    rw [hp, hp, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hPi, hTi]
  · intro d hd
    rw [hp]
    have h1 : ∀ j, T j (P j d) = b.coord j ⟨d, hd⟩ • (b j : H) := fun j => by
      have := hPd j ⟨d, hd⟩
      simp only at this
      rw [this, map_smul, hTv]
    simp only [h1]
    have h2 : ∑ j, b.coord j ⟨d, hd⟩ • b j = ⟨d, hd⟩ := b.sum_repr _
    calc ∑ j, b.coord j ⟨d, hd⟩ • (b j : H)
        = ((∑ j, b.coord j ⟨d, hd⟩ • b j : hwOf G (wtR ν)) : H) := by
          simp only [Submodule.coe_sum, Submodule.coe_smul]
      _ = d := by rw [h2]
  · intro μ w hne hw
    rw [hp]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_highest_eq_zero G K μ (wtR ν) v hv0 hv huniq (P j) (hPi j) hne w hw, map_zero]
  · intro S hS k z hk hz
    have hSD : ∀ x ∈ hwOf G (wtR ν), S x ∈ hwOf G (wtR ν) := map_mem_hwOf G (wtR ν) S hS
    have hj : ∀ j, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j)) =
        b.coord j ⟨S (b j), hSD _ (b j).2⟩ * weylChar ν z := by
      intro j
      have hR : P j ∘ₗ S ∘ₗ T j = b.coord j ⟨S (b j), hSD _ (b j).2⟩ • LinearMap.id := by
        refine eq_smul_id_of_apply L K hK hKs v huniq _ (fun a c w => ?_) _ ?_
        · simp only [LinearMap.comp_apply]
          rw [hTi, hS, hPi]
        · simp only [LinearMap.comp_apply]
          rw [hTv]
          exact hPd j ⟨S (b j), hSD _ (b j).2⟩
      have e1 : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) = ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) ∘ₗ P j := rfl
      have e2 : P j ∘ₗ ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ T j) = σ k ∘ₗ (P j ∘ₗ S ∘ₗ T j) := by
        ext w
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        exact hPk j k _
      rw [e1, LinearMap.trace_comp_comm', e2, hR, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
        htr k z hk hz, smul_eq_mul]
    have hsum : (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (∑ j, T j ∘ₗ P j) =
        ∑ j, (ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ (T j ∘ₗ P j) := by
      ext w

      simp [LinearMap.sum_apply, map_sum]

    rw [hsum, map_sum, Finset.sum_congr rfl fun j _ => hj j, ← Finset.sum_mul]
    congr 1
    unfold trOn
    rw [dite_eq_left hSD, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    rfl

end GlobalTheory.CompanionTheory.RealCountG.Isotypic
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_compact_set_density_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ S : Set (Fin n → Fin M → Ainf F ⊗[F] E), IsCompact S → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam n) (GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F)) S C := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_inf | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_inf | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_inf <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lattice_gram_integral_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Grams.sub_gramH_mem_latH <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.contragredient_product_irreducible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

theorem _root_.GlobalTheory.T.socle_of_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | exact GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | (intros; apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

theorem _root_.GlobalTheory.T.word_occurs_irreducible_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL (k := k)), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  first | exact @GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | exact GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | (intros; apply GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd <;> assumption)
end
