module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle171
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle158
import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle164
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle155
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle176
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumInvariantUnderUnipotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
open scoped ENNReal

noncomputable section

namespace GlobalTheory.PiCoord

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  apply GlobalTheory.HaarPi.lintegral_pi_fin <;> assumption

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e)
      (Measure.pi fun _ : Fin (Fintype.card ι) => μ) (Measure.pi fun _ : ι => μ) :=
    measurePreserving_piCongrLeft (fun _ : ι => μ) e
  calc ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ)
      = ∫⁻ y : Fin (Fintype.card ι) → E, ∏ j, f (e j) (y j) ∂(Measure.pi fun _ => μ) := by
        rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        refine lintegral_congr fun y => ?_
        rw [← e.prod_comp]
        simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    _ = ∏ j, ∫⁻ t, f (e j) t ∂μ := lintegral_pi_fin _ μ _ fun j => hf (e j)
    _ = ∏ i, ∫⁻ t, f i t ∂μ := e.prod_comp fun i => ∫⁻ t, f i t ∂μ

theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  apply GlobalTheory.HaarPi.pi_withDensity <;> assumption

private theorem lintegral_indicator_one_mul_eq_setLIntegral {X : Type*} [MeasurableSpace X] (m : Measure X) {t : Set X}
    (ht : MeasurableSet t) (w : X → ℝ≥0∞) :
    ∫⁻ x, t.indicator 1 x * w x ∂m = ∫⁻ x in t, w x ∂m := by
  rw [← lintegral_indicator ht]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ t
  · simp [hx]
  · simp [hx]

theorem pi_change {ι P D : Type*} [Fintype ι] [MeasurableSpace P] [MeasurableSpace D]
    (μ : Measure P) (ν : Measure D) [SigmaFinite μ] [SigmaFinite ν] (c : P → D) (hc : Measurable c)
    (ρ : D → ℝ) (σ : P → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ g, 0 ≤ ρ g) (hσ0 : ∀ h, 0 ≤ σ h)
    (H : ∀ φ : D → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g * ENNReal.ofReal (ρ g) ∂ν = ∫⁻ p, φ (c p) * ENNReal.ofReal (σ p) ∂μ)
    (φ : (ι → D) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν) =
      ∫⁻ p : ι → P, φ (fun i => c (p i)) * ENNReal.ofReal (∏ i, σ (p i)) ∂(Measure.pi fun _ => μ) := by
  have hρm : Measurable fun g => ENNReal.ofReal (ρ g) := hρ.ennreal_ofReal
  have hσm : Measurable fun p => ENNReal.ofReal (σ p) := hσ.ennreal_ofReal
  have hmap : ν.withDensity (fun g => ENNReal.ofReal (ρ g)) =
      (μ.withDensity fun p => ENNReal.ofReal (σ p)).map c := by
    ext s hs
    rw [withDensity_apply _ hs, Measure.map_apply hc hs, withDensity_apply _ (hc hs)]
    have h1 := H (s.indicator 1) (measurable_one.indicator hs)
    rw [lintegral_indicator_one_mul_eq_setLIntegral ν hs] at h1
    have hpre : ∀ p, s.indicator (1 : D → ℝ≥0∞) (c p) = (c ⁻¹' s).indicator 1 p := by
      intro p
      by_cases hp : c p ∈ s
      · simp [hp]
      · simp [hp]
    simp_rw [hpre] at h1
    rw [lintegral_indicator_one_mul_eq_setLIntegral μ (hc hs)] at h1
    exact h1
  have hcm : Measurable fun (p : ι → P) (i : ι) => c (p i) :=
    Measurable.of_eval fun i => hc.comp (measurable_pi_apply i)
  have : SigmaFinite ((μ.withDensity fun p => ENNReal.ofReal (σ p)).map c) := by
    rw [← hmap]; infer_instance
  have hprodρ : ∀ g : ι → D, ENNReal.ofReal (∏ i, ρ (g i)) = ∏ i, ENNReal.ofReal (ρ (g i)) :=
    fun g => ENNReal.ofReal_prod_of_nonneg fun i _ => hρ0 _
  have hprodσ : ∀ p : ι → P, ENNReal.ofReal (∏ i, σ (p i)) = ∏ i, ENNReal.ofReal (σ (p i)) :=
    fun p => ENNReal.ofReal_prod_of_nonneg fun i _ => hσ0 _
  have hdρ : Measurable fun g : ι → D => ∏ i, ENNReal.ofReal (ρ (g i)) :=
    Finset.measurable_prod _ fun i _ => hρm.comp (measurable_pi_apply i)
  have hdσ : Measurable fun p : ι → P => ∏ i, ENNReal.ofReal (σ (p i)) :=
    Finset.measurable_prod _ fun i _ => hσm.comp (measurable_pi_apply i)
  calc ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν)
      = ∫⁻ g, ((fun g : ι → D => ∏ i, ENNReal.ofReal (ρ (g i))) * φ) g ∂(Measure.pi fun _ => ν) := by
        refine lintegral_congr fun g => ?_
        rw [hprodρ, Pi.mul_apply, mul_comm]
    _ = ∫⁻ g, φ g ∂((Measure.pi fun _ : ι => ν).withDensity fun g => ∏ i, ENNReal.ofReal (ρ (g i))) :=
        (lintegral_withDensity_eq_lintegral_mul _ hdρ hφ).symm
    _ = ∫⁻ g, φ g ∂(Measure.pi fun _ : ι => ν.withDensity fun g => ENNReal.ofReal (ρ g)) := by
        rw [pi_withDensity ν _ hρm]
    _ = ∫⁻ g, φ g ∂(Measure.pi fun _ : ι => (μ.withDensity fun p => ENNReal.ofReal (σ p)).map c) := by
        rw [hmap]
    _ = ∫⁻ g, φ g ∂((Measure.pi fun _ : ι => μ.withDensity fun p => ENNReal.ofReal (σ p)).map
          fun (p : ι → P) (i : ι) => c (p i)) := by
        rw [Measure.pi_map_pi fun _ => hc.aemeasurable]
    _ = ∫⁻ p, φ (fun i => c (p i)) ∂(Measure.pi fun _ : ι => μ.withDensity fun p => ENNReal.ofReal (σ p)) :=
        lintegral_map hφ hcm
    _ = ∫⁻ p, φ (fun i => c (p i)) ∂((Measure.pi fun _ : ι => μ).withDensity
          fun p => ∏ i, ENNReal.ofReal (σ (p i))) := by
        rw [pi_withDensity μ _ hσm]
    _ = ∫⁻ p : ι → P, φ (fun i => c (p i)) * ENNReal.ofReal (∏ i, σ (p i)) ∂(Measure.pi fun _ => μ) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hdσ
          (show Measurable fun p : ι → P => φ (fun i => c (p i)) from hφ.comp hcm)]
        refine lintegral_congr fun p => ?_
        rw [hprodσ, Pi.mul_apply, mul_comm]

theorem lintegral_pi_prod_two {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (F : (ι → A × B) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F p ∂(Measure.pi fun _ => μ.prod ν) =
      ∫⁻ a : ι → A, ∫⁻ b : ι → B, F (fun i => (a i, b i)) ∂(Measure.pi fun _ => ν)
        ∂(Measure.pi fun _ => μ) := by
  have hp : MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow A B ι)
      (Measure.pi fun _ : ι => μ.prod ν) ((Measure.pi fun _ : ι => μ).prod (Measure.pi fun _ : ι => ν)) :=
    measurePreserving_arrowProdEquivProdArrow A B ι (fun _ => μ) (fun _ => ν)
  rw [← hp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
    lintegral_prod (fun z => F ((MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm z))
      (show Measurable fun z => F ((MeasurableEquiv.arrowProdEquivProdArrow A B ι).symm z) from
        hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
  rfl

theorem pi_change_three {ι A B C D : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (α : Measure A) (β : Measure B) (γ : Measure C) (ν : Measure D)
    [SigmaFinite α] [SigmaFinite β] [SigmaFinite γ] [SigmaFinite ν]
    (c : A → B → C → D) (hc : Measurable fun p : A × B × C => c p.1 p.2.1 p.2.2)
    (ρ : D → ℝ) (σ : B → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ g, 0 ≤ ρ g) (hσ0 : ∀ h, 0 ≤ σ h)
    (H : ∀ φ : D → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g * ENNReal.ofReal (ρ g) ∂ν =
        ∫⁻ x, ∫⁻ h, ∫⁻ T, φ (c x h T) * ENNReal.ofReal (σ h) ∂γ ∂β ∂α)
    (φ : (ι → D) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) ∂(Measure.pi fun _ => ν) =
      ∫⁻ x : ι → A, ∫⁻ h : ι → B, ∫⁻ T : ι → C,
        φ (fun i => c (x i) (h i) (T i)) * ENNReal.ofReal (∏ i, σ (h i))
        ∂(Measure.pi fun _ => γ) ∂(Measure.pi fun _ => β) ∂(Measure.pi fun _ => α) := by
  have hσ' : Measurable fun p : A × B × C => σ p.2.1 := hσ.comp (measurable_fst.comp measurable_snd)
  have H' : ∀ ψ : D → ℝ≥0∞, Measurable ψ → ∫⁻ g, ψ g * ENNReal.ofReal (ρ g) ∂ν =
      ∫⁻ p, ψ (c p.1 p.2.1 p.2.2) * ENNReal.ofReal (σ p.2.1) ∂(α.prod (β.prod γ)) := by
    intro ψ hψ
    have m1 : Measurable fun p : A × B × C => ψ (c p.1 p.2.1 p.2.2) * ENNReal.ofReal (σ p.2.1) :=
      (hψ.comp hc).mul hσ'.ennreal_ofReal
    rw [H ψ hψ, lintegral_prod _ m1.aemeasurable]
    refine lintegral_congr fun x => ?_
    exact (lintegral_prod (fun q : B × C => ψ (c x q.1 q.2) * ENNReal.ofReal (σ q.1))
      (m1.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
  rw [pi_change (α.prod (β.prod γ)) ν (fun p => c p.1 p.2.1 p.2.2) hc ρ (fun p => σ p.2.1) hρ hσ'
    hρ0 (fun p => hσ0 _) H' φ hφ]
  have hF : Measurable fun p : ι → A × B × C =>
      φ (fun i => c (p i).1 (p i).2.1 (p i).2.2) * ENNReal.ofReal (∏ i, σ (p i).2.1) :=
    (hφ.comp (Measurable.of_eval fun i => hc.comp (measurable_pi_apply i))).mul
      (Finset.measurable_prod _ fun i _ => hσ'.comp (measurable_pi_apply i)).ennreal_ofReal
  rw [lintegral_pi_prod_two α (β.prod γ) _ hF]
  refine lintegral_congr fun x => ?_
  have hG : Measurable fun q : ι → B × C =>
      φ (fun i => c (x i) (q i).1 (q i).2) * ENNReal.ofReal (∏ i, σ (q i).1) :=
    hF.comp (Measurable.of_eval fun i => (measurable_const.prodMk (measurable_pi_apply i)))
  exact lintegral_pi_prod_two β γ _ hG

theorem piCoord : ∀ (ι : Type) [Fintype ι] (k : ℕ) (c : (Fin (k + 1) → ℂ) → (Fin k → Fin k → ℂ) → (Fin k → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ), Measurable (fun p : (Fin (k + 1) → ℂ) × (Fin k → Fin k → ℂ) × (Fin k → ℂ) => c p.1 p.2.1 p.2.2) → ∀ (ρ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ℝ) (σ : (Fin k → Fin k → ℂ) → ℝ), Measurable ρ → Measurable σ → (∀ g, 0 ≤ ρ g) → (∀ h, 0 ≤ σ h) → (∀ φ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal (ρ g) = ∫⁻ x, ∫⁻ h, ∫⁻ T, φ (c x h T) * ENNReal.ofReal (σ h)) → ∀ φ : (ι → Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal (∏ i, ρ (g i)) = ∫⁻ x : ι → Fin (k + 1) → ℂ, ∫⁻ h : ι → Fin k → Fin k → ℂ, ∫⁻ T : ι → Fin k → ℂ, φ (fun i => c (x i) (h i) (T i)) * ENNReal.ofReal (∏ i, σ (h i)) := by
  intro ι _ k c hc ρ σ hρ hσ hρ0 hσ0 H φ hφ
  exact pi_change_three volume volume volume volume c hc ρ σ hρ hσ hρ0 hσ0 H φ hφ

end GlobalTheory.PiCoord
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.continuousDensity_selfDualLatticeIndicator_at_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v → ∀ ψ : AddChar (Fv F v) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsLocalChar v ψ → ∀ n : ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.DualExponent v ψ n → ∀ L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L → ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), SdW F E σ M J (Fv F v) ψ 1 μ → SdR (Fv F v) ψ ν → ∀ g : Fv F v → ℂ, IsContDensityOn μ (fun X => qR (Fv F v) σ J (X 0)) id ν {c | c ≠ 0} ({X | X 0 ∈ L}.indicator 1) g → ∀ β : Fv F v, Valued.v β = 1 → g β = (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.LatticeContDensity.contDensity_unit | exact GlobalTheory.LatticeContDensity.contDensity_unit | (intros; apply GlobalTheory.LatticeContDensity.contDensity_unit <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem satIn_of_trace (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (h : ∀ y, y ∈ S ↔ y ∈ lamX I x ∧ y ∈ Submodule.span I.E (S : Set (Fin I.n → I.E))) :
    GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S := by
  have := GlobalTheory.StepDualityCompare.totallyComplex I

  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span I.E (S : Set (Fin I.n → I.E)))
  let φ : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E) := q.subtype ∘ₗ Submodule.linearProjOfIsCompl q _ hq.symm
  have hker : LinearMap.ker φ = Submodule.span I.E (S : Set (Fin I.n → I.E)) := by
    rw [LinearMap.ker_comp_of_ker_eq_bot _ q.ker_subtype]
    exact Submodule.linearProjOfIsCompl_ker _
  have hX : ∀ v, IsUnit (frm I x v).det := GlobalTheory.StepDualityCompare.frm_det I x
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat := (Formalism.HN.htImage I.E (Fin I.n → I.E) (Fin I.n) (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x)
    (bas I) (frm I x) hX hX φ (lamX I x) hfg).1
  have hS : lamX I x ⊓ (LinearMap.ker φ).restrictScalars (𝓞 I.E) = S := by
    ext y
    rw [hker, Submodule.mem_inf, Submodule.restrictScalars_mem, h]
  rw [hS] at hsat
  exact hsat

theorem sizeQ_flag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  intro I x a j S hS i
  obtain ⟨-, hmono, -, htr, -⟩ := hS
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x (S i.castSucc) := satIn_of_trace I x _ (htr i.castSucc)
  have hle : S i.succ ≤ lamX I x := fun y hy => ((htr i.succ y).1 hy).1
  have hmn : S i.castSucc ≤ S i.succ := hmono (Fin.castSucc_le_succ i)
  have hpos := GlobalTheory.StepDualityCompare.htQ_pos I x hfg _ _ hsat hle hmn
  unfold Formalism.HN.sizeQ
  exact Real.rpow_pos_of_pos hpos _

end GlobalTheory.LeviIso
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CovolIdx

theorem tsum_cosets {G : Type} [Group G] (C H : Subgroup G) (hC : C ≤ H) (f : G → ℝ≥0∞) :
    ∑' h : H, f h = ∑' q : H ⧸ C.subgroupOf H, ∑' c : C, f ((q.out : H) * (c : G)) := by
  rw [← ENNReal.tsum_prod]
  let e : (H ⧸ C.subgroupOf H) × C → H := fun p => p.1.out * ⟨p.2, hC p.2.2⟩
  have hmk : ∀ p, (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = p.1 := by
    intro p
    have : (QuotientGroup.mk (e p) : H ⧸ C.subgroupOf H) = QuotientGroup.mk p.1.out := by
      symm
      rw [QuotientGroup.eq]
      simp [e, Subgroup.mem_subgroupOf]
    rw [this, QuotientGroup.out_eq']
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨q, c⟩ ⟨q', c'⟩ h
      have h1 : q = q' := by
        have := hmk (q, c)
        rw [h, hmk] at this
        exact this.symm
      subst h1
      have h2 := mul_left_cancel h
      have h3 : c = c' := Subtype.ext (congrArg Subtype.val h2 :)
      rw [h3]
    · intro h
      have hm : ((QuotientGroup.mk h : H ⧸ C.subgroupOf H).out)⁻¹ * h ∈ C.subgroupOf H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      refine ⟨(QuotientGroup.mk h, ⟨_, Subgroup.mem_subgroupOf.1 hm⟩), ?_⟩
      apply Subtype.ext
      simp [e]
  exact ((Equiv.ofBijective e he).tsum_eq (fun h : H => f h)).symm

theorem measure_eq_tsum_inter {G α : Type} [Group G] [MulAction G α] [MeasurableSpace α]
    (μ : Measure α) (R : Set α) (A : Subgroup G) [Countable A] (Ω S : Set α)
    (hm : ∀ s : G, Measurable fun x : α => s • x) (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) :
    μ S = ∑' a : A, μ ((fun x => (a : G) • x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((hm a hΩ).inter hS).nullMeasurableSet

theorem measure_eq_invVol_mul : ∀ (G α : Type) [Group G] [MulAction G α] [MeasurableSpace α] (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α), (∀ s : G, Measurable fun x : α => s • x) → Countable A → Countable B → μ Rᶜ = 0 → (∀ s ∈ A ⊔ B, (∀ x ∈ R, s • x ∈ R) ∧ μ.map (fun x => s • x) = μ) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → MeasurableSet Ω → MeasurableSet K → (∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) → (∀ x ∈ R, ∃! s, s ∈ B ∧ s • x ∈ K) → μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  intro G α _ _ _ μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB
  have hpre : ∀ s ∈ A ⊔ B, ∀ S, MeasurableSet S → μ ((fun x => s • x) ⁻¹' S) = μ S := by
    intro s hs S hS
    rw [← Measure.map_apply (hm s) hS, (hinv s hs).2]
  let F : G → G → ℝ≥0∞ := fun a b => μ ((fun x => a • x) ⁻¹' Ω ∩ (fun x => b • x) ⁻¹' K)
  have hF : ∀ a b c : G, c ∈ A ⊓ B → F (a * c) b = F a (b * c⁻¹) := by
    intro a b c hc
    refine Eq.trans ?_ (hpre c (Subgroup.mem_sup_left hc.1) _ ((hm a hΩ).inter (hm (b * c⁻¹) hK)))
    simp only [F]
    congr 1
    ext x
    simp [mul_smul]
  have h1 : ∀ b ∈ B, μ K = ∑' a : A, F a b := by
    intro b hb
    rw [← hpre b (Subgroup.mem_sup_right hb) K hK]
    exact measure_eq_tsum_inter μ R A Ω _ hm hR hΩ (hm b hK) fA
  have h2 : ∀ a ∈ A, μ Ω = ∑' b : B, F a b := by
    intro a ha
    rw [← hpre a (Subgroup.mem_sup_left ha) Ω hΩ,
      measure_eq_tsum_inter μ R B K _ hm hR hK (hm a hΩ) fB]
    simp only [F, Set.inter_comm]
  have key : ∑' _q : B ⧸ (A ⊓ B).subgroupOf B, μ K = ∑' _p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω := by
    have e1 : ∀ q : B ⧸ (A ⊓ B).subgroupOf B, μ K =
        ∑' p : A ⧸ (A ⊓ B).subgroupOf A, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro q
      rw [h1 _ q.out.2, tsum_cosets (A ⊓ B) A inf_le_left (fun a => F a (q.out : B))]
      refine tsum_congr fun p => ?_
      rw [← (Equiv.inv (A ⊓ B : Subgroup G)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [hF _ _ _ (Subtype.property _)]
      simp
    have e2 : ∀ p : A ⧸ (A ⊓ B).subgroupOf A, μ Ω =
        ∑' q : B ⧸ (A ⊓ B).subgroupOf B, ∑' c : (A ⊓ B : Subgroup G),
          F (p.out : A) ((q.out : B) * (c : G)) := by
      intro p
      rw [h2 _ p.out.2, tsum_cosets (A ⊓ B) B inf_le_right (fun b => F (p.out : A) b)]
    rw [tsum_congr e1, tsum_congr e2, ENNReal.tsum_comm]
  rw [Subgroup.inf_subgroupOf_right, Subgroup.inf_subgroupOf_left, ENNReal.tsum_const, ENNReal.tsum_const] at key
  have fq : Finite (B ⧸ A.subgroupOf B) := Subgroup.fintypeOfIndexNeZero hAB |>.finite
  have fp : Finite (A ⧸ B.subgroupOf A) := Subgroup.fintypeOfIndexNeZero hBA |>.finite
  have key' : (A.relIndex B : ℝ≥0∞) * μ K = (B.relIndex A : ℝ≥0∞) * μ Ω := by
    simpa [ENat.card_eq_coe_natCard, Subgroup.relIndex, Subgroup.index] using key
  have hv : ENNReal.ofReal (GlobalTheory.HL.invVol A B) = (A.relIndex B : ℝ≥0∞)⁻¹ * (B.relIndex A : ℝ≥0∞) := by
    unfold GlobalTheory.HL.invVol
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hAB), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [hv, mul_assoc, ← key', ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hAB) (ENNReal.natCast_ne_top _), one_mul]

end GlobalTheory.CovolIdx
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PrincipalMinorExterior

theorem pairing_eq_leading_minor : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp l (Formalism.QuantumDeterminants.Hpk k r))
      (cmp l g *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z' (Fin.castLE hl a))))
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) =
      ((Formalism.QuantumDeterminants.Zhat k r z z' g).submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  intro k r l hl z z' g
  rw [Formalism.QuantumDeterminants.herm, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge, GlobalTheory.TopMinorWedge.cmp_mulVec_wedge,
    GlobalTheory.TopMinorWedge.star_wedge_dot]
  rfl

end GlobalTheory.PrincipalMinorExterior
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.DeepStep

theorem step_bound (B : RowsAut) (b ρ M : ℝ) (P : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hM : 0 ≤ M)
    (hb : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B (P + 1), ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
  intro y hy u hu
  have hvv : ∀ z : B.I.GA, ‖vv B Fr u z‖ = Real.sqrt (∑ i, ‖Fr i u z‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hvvs : ∀ z : B.I.GA, ‖vv B Fr u z - vv B Fr u x‖ = Real.sqrt (∑ i, ‖Fr i u z - Fr i u x‖ ^ 2) := by
    intro z
    simp [vv, EuclideanSpace.norm_eq]
  have hnear := GlobalTheory.T.representativeValuesVector_variation_unipotentOrbit B b ρ M P D T Fr x W hS hR hM hb
  have hcusp := GlobalTheory.T.cuspidalSubspace_closed_rightTranslation_stable B
  obtain ⟨L, hL, -, -, hLf⟩ := hcusp
  have hrep : ∀ i, GlobalTheory.Dec.IsContRep B (T i u) (Fr i u) := fun i => (hR i P u hu).1
  have hx : ‖vv B Fr u x‖ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by
    rw [hvv]
    refine GlobalTheory.MeanZero.norm_le_of_cusp B.I B.μf B.g W D (fun i => Fr i u) x (fun i => Fr i u x) _ hg hW ?_ ?_
    · intro i
      obtain ⟨hc, hl, hae⟩ := hrep i
      refine ⟨hc, hl, (hR i P u hu).2.1, ?_⟩
      have h1 := ((GlobalTheory.T.continuous_representative_properties B).2.2.2 _ _ (hrep i)).1
      exact (hLf (T i u) (Fr i u) hl hc h1).1 ((hL _).2 (hC i u))
    · intro ν hν
      obtain ⟨γ, hγ, k, hk, z, hz, he⟩ := hcov ν hν
      have hval : ∀ i, Fr i u (((ν, 1) : B.I.GA) * x) = Fr i u z := by
        intro i
        rw [he, (hR i P u hu).2.1 k hk, (hrep i).2.1 γ hγ]
      simp only [hval]
      rw [← hvvs]
      exact hnear z hz u hu
  calc ‖vv B Fr u y‖ = ‖(vv B Fr u y - vv B Fr u x) + vv B Fr u x‖ := by rw [sub_add_cancel]
    _ ≤ ‖vv B Fr u y - vv B Fr u x‖ + ‖vv B Fr u x‖ := norm_add_le _ _
    _ ≤ ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ + ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ :=
        add_le_add (hnear y hy u hu) hx
    _ = 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * M * ‖u‖ := by ring

end GlobalTheory.DeepStep
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.embeddedDatum_invariant_under_unipotent : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by
  first | exact @GlobalTheory.DegAsm.datOf_move | exact GlobalTheory.DegAsm.datOf_move | (intros; apply GlobalTheory.DegAsm.datOf_move <;> assumption)
end
