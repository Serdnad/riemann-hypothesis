module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle512
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeCharacterIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingMeasureByUnit
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle513
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle526
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBound
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430

@[expose] public section

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_lattice_quadratic_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT | exact GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT | (intros; apply GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.compact_set_contained_in_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (O : Subring (Fv F v ⊗[F] E)), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → ∃ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) ∧ IsOpen (L : Set (Fv F v ⊗[F] E)) ∧ A ⊆ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.exists_lattice_tupIn | exact GlobalTheory.CompanionTheory.AvgFree.exists_lattice_tupIn | (intros; apply GlobalTheory.CompanionTheory.AvgFree.exists_lattice_tupIn <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_lattice_volume_order_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M j : ℕ), IsCompact (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ∧ IsOpen (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen | exact GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen | (intros; apply GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_order_conjugation_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n M : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → MeasurePreserving (fun X : (Fin n → Fin M → (Fv F v ⊗[F] E)) => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a)) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving | exact GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving | (intros; apply GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_order_stable_integral_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) = (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | exact GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | (intros; apply GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_scaling_volume_by_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n M : ℕ) (l : Fin n) (D : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), MeasurableSet D → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) {X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) ∈ D} = ((θ : ℝ≥0∞) ^ M)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) D := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale | exact GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale | (intros; apply GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_lattice_character_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), 0 < n → ∀ p ∈ S, ∀ θ : ℝ≥0, (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (p.1 : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ j : ℕ, ∃ G : Finset (Fin n × (Fin n → (Fv F v ⊗[F] E))), ((G.card : ℝ≥0) ≤ n * (θ⁻¹) ^ (j * n)) ∧ (∀ q ∈ G, (∀ i, q.2 i ∈ O) ∧ q.2 q.1 = 1) ∧ ∀ X ∈ nearNF (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) (p.1 : (Fv F v ⊗[F] E)) j, ∃ q ∈ G, GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) q.1 q.2 * dMat (Fv F v) q.1 ((p.1 ^ j)⁻¹ : (Fv F v ⊗[F] E)ˣ)) ∈ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.nearNF_cover | exact GlobalTheory.CompanionTheory.AvgFree.nearNF_cover | (intros; apply GlobalTheory.CompanionTheory.AvgFree.nearNF_cover <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_scaling_measure_by_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n : ℕ) (l : Fin n) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) Y) = ((θ : ℝ≥0∞) ^ n)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.cjPre_dMat_scale | exact GlobalTheory.CompanionTheory.AvgFree.cjPre_dMat_scale | (intros; apply GlobalTheory.CompanionTheory.AvgFree.cjPre_dMat_scale <;> assumption)
end

section

open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory


theorem _root_.GlobalTheory.T.local_lattice_gauss_sum_estimate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), Monotone (fun j => (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j)) ∧ ∀ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.goodT_mono_free | exact GlobalTheory.CompanionTheory.AvgFree.goodT_mono_free | (intros; apply GlobalTheory.CompanionTheory.AvgFree.goodT_mono_free <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.dual_operator_commutes_lie : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G → ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G | exact GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G | (intros; apply GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G <;> assumption)
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem dualFam_exists : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  intro n E
  obtain ⟨e, ρ', hc, hiso, hint⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨F, hgl, -, hder⟩ := GlobalTheory.T.exists_compact_lie_action _ ρ' hc hiso
  refine ⟨fun a b => e.symm.toLinearMap ∘ₗ F a b ∘ₗ e.toLinearMap, ?_, ?_⟩
  · intro a b c d
    ext1 ξ
    have h := LinearMap.congr_fun (hgl a b c d) (e ξ)
    apply e.injective
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_sub] at h ⊢
    rw [h]
    split_ifs <;> simp
  · intro X γ hX hγ ξ
    let eL : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] (E.V →L[ℂ] ℂ) :=
      LinearMap.toContinuousLinearMap e.symm.toLinearMap
    have heL : ∀ w, eL w = e.symm w := fun _ => rfl
    have h := (eL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder X γ hX hγ (e ξ))
    have hf : (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) = (eL.restrictScalars ℝ) ∘ fun t : ℝ => ρ' (γ t) (e ξ) := by
      funext t
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', heL, ← hint,
        LinearEquiv.symm_apply_apply]
    rw [hf]
    refine h.congr_deriv ?_

    simp only [ContinuousLinearMap.coe_restrictScalars', map_sum, map_smul, heL, LinearMap.comp_apply,
    LinearEquiv.coe_coe]

end GlobalTheory.CompanionTheory.RealCountG
end
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.harmonic_of_norm_bound : ∀ {n : ℕ} (lam : Fin n → ℤ), Antitone lam → ∀ ν : Fin n → ℤ, Antitone ν → DomLE (wtR ν) (m0 lam) → ∀ w : Equiv.Perm (Fin n), Antitone (fun a => wtR ν (w a) - rhoV n (w a)) → ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (wtR ν (w a) - rhoV n (w a) + rhoV n a) ^ 2 → ν ∈ harmZ lam := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | exact GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge | (intros; apply GlobalTheory.CompanionTheory.RealCountG.mem_harmZ_of_norm_ge <;> assumption)
end
