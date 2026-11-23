module

import CompanionTheory.AutomorphicTheory.ThetaDilations.ContinuousPm
public import Development.WeilBound.CoreStatements.ThetaDilations.ParAlg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaLint
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  (R : Type) [CommRing R] [Algebra F R]

theorem exists_anti (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.exists_anti <;> assumption

theorem norm_sigR (h : IsCMExt F E σ) (a : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.norm R a) = a * sigR R σ a := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.norm_sigR <;> assumption

theorem cT_JR {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : cT (sigR R σ) (JR R J) = JR R J := by
  ext i j; simp [cT, JR, sigR, inclR, hJ.1]

theorem hform_conj {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J : Matrix (Fin M) (Fin M) K} (hs : ∀ x, s (s x) = x)
    (hJ : cT s J = J) (x y : Fin M → K) : s (hform s J x y) = hform s J y x := by
  have : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j

  simp only [hform, map_sum, map_mul, hs, this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hform_add {K : Type} [CommRing K] {M : ℕ} (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (x y : Fin M → K) :
    hform s J (x + y) (x + y) = hform s J x x + hform s J x y + hform s J y x + hform s J y y := by
  have e : (s : K → K) ∘ (x + y) = s ∘ x + s ∘ y := funext fun _ => map_add s _ _
  simp only [hform_eq, e, Matrix.add_vecMul, add_dotProduct, dotProduct_add]; ring

theorem hform_U {K : Type} [CommRing K] {M : ℕ} {s : K →+* K} {J U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J)
    (x : Fin M → K) : hform s J (U *ᵥ x) (U *ᵥ x) = hform s J x x := by
  have e : (s : K → K) ∘ (U *ᵥ x) = (s ∘ x) ᵥ* cT s U := by
    funext i; simp [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, mul_comm]
  rw [hform_eq, hform_eq, e, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hU]

theorem hyp_inv {K : Type} [CommRing K] {M : ℕ} {J Ji : Matrix (Fin M) (Fin M) K} (h : Ji * J = 1) :
    hypJ Ji * hypJ J = 1 := by
  rw [← pm_one]
  simp [hypJ_eq, blk_mul, pm, h]

theorem continuous_pm {X K : Type} [TopologicalSpace X] [CommRing K] [TopologicalSpace K] {M : ℕ} {a b d : X → K}
    {r w : X → Fin M → K} {U : X → Matrix (Fin M) (Fin M) K} (ha : Continuous a) (hb : Continuous b)
    (hr : Continuous r) (hd : Continuous d) (hw : Continuous w) (hU : Continuous U) :
    Continuous fun x => pm (a x) (b x) (r x) (d x) (w x) (U x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  exacts [ha, hb, (continuous_apply j).comp hr, continuous_const, hd, continuous_const, continuous_const,
    (continuous_apply i).comp hw, hU.matrix_elem i j]


end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem theta_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ 𝓕 hμ h𝓕 n S Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  have hm : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  rw [thetaMeas, lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul,
    lintegral_tsum (f := fun (X : S) h => Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)))
      fun X => (hΦ.comp (hm _)).aemeasurable]
  simp only [lintegral_map hΦ (hm _)]

theorem theta_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.theta_int <;> assumption

theorem act_rat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E) :
    ∃ X' : Fin n → Fin M → E, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm

  simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem theta_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}) ∧ thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 := by
  apply CompanionTheory.PlacePermOperatorBicommutantSpan.theta_inv <;> assumption

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end
