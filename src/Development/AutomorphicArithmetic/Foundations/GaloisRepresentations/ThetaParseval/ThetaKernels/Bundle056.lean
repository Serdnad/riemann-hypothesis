module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle542
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle543
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle042
import Development.WeilBound.ThetaLifts.LeviDeterminants.ContinuousOfMem
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle001
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowHt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle040
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle019
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle001
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem finRatF_mem_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ := _root_.PositivityTheory.ThKW.AutLatA.mem_iff_k C hR hA y
theorem finite_lat_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧ ‖infRatF (tauB B) y‖ ≤ R}.Finite :=
  _root_.PositivityTheory.ThKW.AutLatA.finLat_k hB hG R
theorem finite_data_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| :=
  _root_.PositivityTheory.ThKW.AutLatA.data_k C hG hR hO ha hb hΔ hd
end PositivityTheory.ThKW
end
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
namespace GlobalTheory.ThetaSchurF
section Lemmas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}
end Lemmas
theorem schur_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ M hM hc hn
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hskew := GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv nS nT JS JT hJS hJT ξ₀ hσξ
  have hann := _root_.GlobalTheory.T.rational_lattice_self_dual F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ
  have hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w f) :=
    fun w f hf => _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ w f hf
  have h2 : ∀ f f', IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ hskew hann hth M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisOF, add_sub_cancel, star_mul'] at h
    linear_combination B.ψ (symplOHF σ JS JT ξ₀ x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ.2.1 (symplOHF σ JS JT ξ₀ x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), fun f hf => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]
end GlobalTheory.ThetaSchurF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
theorem unit_coef_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))), μW.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (w₀ : WOF F E nS (nT + nT)) (f : WOF F E nS (nT + nT) → ℂ),
        IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h w₀) (ωd (1, h) f) w *
            starRingEnd ℂ (ωd (1, h) f w) ∂μW =
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w₀ f w * starRingEnd ℂ (f w) ∂μW := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS ωd hω μ 𝓕 hμ h𝓕 h w₀ f hf
  rw [← hω.om_heis 1 h w₀ f hf]
  exact GlobalTheory.ThetaSchurF.scalar_eq hω.std.1.2.1 μ 𝓕 hμ h𝓕 (ωd (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _
    (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ w₀ f hf) hf
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem schA_facts_k {B : Base F E} {σ : E →ₐ[F] E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (N : ℕ) (μN : Measure (Fin N → AF F))
    (hμN : μN.IsAddHaarMeasure) (Φ : (Fin N → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin N)) :
    Continuous Φ ∧ Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μN ∧
      ∀ b : Fin N → AF F, (fun x => B.ψ (x ⬝ᵥ b) * Φ x) ∈ schA F (Fin N) := by
  refine ⟨GlobalTheory.ThKOp.continuous_of_mem_schA hΦ, ?_, fun b => ?_⟩
  · haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    haveI : BorelSpace (AF F) := ⟨rfl⟩
    have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
    have key : ∀ (m : MeasurableSpace (Fin N → AF F)), m = borel _ → ∀ μ : @Measure _ m,
        @Measure.IsAddHaarMeasure _ _ _ m μ → Integrable (fun x => Φ x * starRingEnd ℂ (Φ x)) μ := by
      rintro m rfl μ hμ
      have hm := GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ
      have hi := (hm.integrable_norm_pow two_ne_zero).ofReal (𝕜 := ℂ)
      refine hi.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; rfl
    exact key _ hb μN hμN
  · have h := GlobalTheory.WeylFour.SchrKeep.schr_mem_schA F B.ψ hB.std (Fin N) (0, b) Φ hΦ
    convert h using 1
    funext x
    simp [GlobalTheory.WeilM.schr]
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end

section



section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

theorem _root_.GlobalTheory.T.lintegral_enorm_sq_latRep_apply_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  first | exact @_root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | exact _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | (intros; apply _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem _root_.GlobalTheory.T.hecke_character_trivial_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 →
        ν x = 1) → ∀ x, ν x = 1 := by
  first | exact @_root_.GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split_k | exact _root_.GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split_k | (intros; apply _root_.GlobalTheory.HeckeSplitBase.heckeChar_eq_one_of_split_k <;> assumption)
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem siegelMult_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hn : 1 ≤ n) (χ : Chr F E) (hχ : IsHecke F E χ) (c : ℕ)
    (hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c) {b : GL (Fin n ⊕ Fin n) E}
    {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a)
    (s₁ : ℂ) (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ (A : ℂ → ℂ) (H : ℂ → modFun σ Y) (t : ℝ), Differentiable ℂ A ∧ (∃ z, A z ≠ 0) ∧
      (∀ μ, IsGrowForm μ → Differentiable ℂ (fun s => μ (H s))) ∧
      ∀ s : ℂ, t < s.re → ∀ x, HasSum (fun q => A s * eisTerm (flat a f s₁ s) x q) ((H s).1 x) := by
  have hSec : SecLaw := Hd.secLaw
  have hWL : WallLaw := Hd.wallLaw_of Hd.secLaw
  have hD : Dict := Hd.dict
  have hDI : DictInf := Hd.dictInf
  have hCM : CMGood := Hd.cmGood_of Hd.stdGood Hd.dict Hd.dictInf
  have hGT : GrpTop := Hd.grpTop
  have hBd : BdetLaw := Hd.bdetLaw
  have hPar : ParLaw := Hd.parLaw_of Hd.bdetLaw Hd.extLaw Hd.grpTop
  have hSg : SgAll := Hd.sgAll
  obtain ⟨⟨ε, hε⟩, t₀, ht₀⟩ := hb
  have hb' : IsFrame2 σ Y b := ⟨⟨ε, hε⟩, t₀, ht₀⟩
  have hcm := hB.cm
  have hunr := hB.unram
  have hgood : (adCM σ χ).Good := hCM F E σ χ c hcm hunr hχ hres
  obtain ⟨-, -, -, ht2', hlc', hsc', hKc⟩ := hGT E (AE F E) (adCM σ χ) hgood (Fin n) ε
  let Φ := frameEquiv (Y := Y) χ ε b hε
  have hΓ : ∀ x, x ∈ rat2 σ Y ↔ Φ x ∈ (adCM σ χ).uΓ ε (Fin n) := rat_iff χ ε b hε
  have hKK : ∀ x, x ∈ K ↔ Φ x ∈ (adCM σ χ).uK ε (Fin n) := fun x => GlobalTheory.T.standard_compact_frame_equiv F E σ n Y hD hDI hcm χ ε b hε B K hK x
  have hIP : ∀ x, (∃ t, IsPar x t) ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := GlobalTheory.T.parabolic_iff_frame_parabolic F E σ n Y χ ε b hε t₀ ht₀
  have hPP : ∀ x, x ∈ par2 σ Y ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
    intro x
    constructor
    · intro hx
      have : par2 σ Y ≤ ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))).comap Φ.toMonoidHom :=
        (Subgroup.closure_le _).2 fun p hp => (hIP p).1 hp
      exact this hx
    · intro hx
      exact Subgroup.subset_closure ((hIP x).2 hx)
  have hH := fun x => uH_eq hD hBd χ hgood ε b hε t₀ ht₀ K hKK a ha x
  have hiwa : Iwa ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))) ((adCM σ χ).uK ε (Fin n)) := by
    intro y
    obtain ⟨p, t, hp, k, hk, e⟩ := ha.iwa (Φ.symm y)
    refine ⟨Φ p, (hIP p).1 ⟨t, hp⟩, Φ k, (hKK k).1 hk, ?_⟩
    rw [← map_mul, ← e, MulEquiv.apply_symm_apply]
  obtain ⟨-, hparU⟩ := hPar E (AE F E) (adCM σ χ) hgood (Fin n) ε (Set.univ : Set (Fin n))
  obtain ⟨hIP', hIH, -⟩ := hparU (by rwa [inf_idem])
  rw [inf_idem] at hIP'
  haveI := ht2'
  haveI := hlc'
  have hW := hSg F E σ χ c hcm hunr hχ hres ε (Fin n) (by simpa using hn) hiwa
  obtain ⟨σ₀, hσ₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k hB hb' hK ha
  refine eis_from_U hSec hWL Φ (continuous_frameEquiv χ ε b hε) _ _ _ ((adCM σ χ).uC ε (Fin n))
    ((adCM σ χ).uH ε (Set.univ : Set (Fin n))) hKc hIP' hIH ?_ K a χ s₁ f hf hΓ hKK hPP hIP hH
    (continuous_frameEquiv_symm χ ε b hε) ?_ ⟨σ₀, fun σ' h => ?_⟩
  · simpa using hW
  · intro p t hp
    refine ⟨?_, ?_⟩
    · show (((adCM σ χ).χ (bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hε p).1) : Circle) : ℂ) = _
      rw [GlobalTheory.T.block_det_parabolic_frame F E σ n Y χ ε b hε t₀ ht₀ p t hp]
      rfl
    · have := ha.val p t hp 1 (one_mem _)
      rwa [mul_one] at this
  · obtain ⟨C, N, h⟩ := hσ₀ σ' h
    exact ⟨C, N, fun x => (h x).2⟩
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

section



section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
theorem PositivityTheory.ThKF0.weil_schwartz_decay_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k :=
  _root_.PositivityTheory.ThKF0.Grow.schwartz_decay_uniform PositivityTheory.ThKF0.Grow.htBd PositivityTheory.ThKF0.Grow.finInv
    (PositivityTheory.ThKF0.Grow.sob_of PositivityTheory.ThKF0.Grow.derivOK) PositivityTheory.ThKF0.Grow.trBd
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ : Type} [Fintype κ] {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} {B : Base F E} {ψ : AddChar (AF F) ℂ}
variable {dd} {χ : Chr F E} {om S l}
theorem sw_transl_k (h1 : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) {r s r' s'} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hm : 1 ≤ m) (hn : 1 ≤ n) (h0 : min r s = 0)
    (hA : A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') (hχ : IsHecke F E χ)
    (hc : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m) {dd om S l}
    (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l) {K a} (hK : IsStab2 B K) (ha : IsHgt K a)
    {μ : Measure (UA σ A.J)} {D : Set (UA σ A.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ A.J) D μ)
    {Φ} (hΦ : Φ ∈ kfin om K) : EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
      fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  obtain ⟨N, _, n0, n1, n2⟩ := hΦ
  obtain ⟨b, K₀, p, t, hb, hK₀, hp, hk⟩ := h2 F E σ B n Y r' s' hB (hA.symm.imp And.right And.right) K hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = absE F E (Matrix.GeneralLinearGroup.det t) := ⟨_, rfl⟩
  have d0 : 0 < d := hd ▸ absE_pos _
  have a0 : ∀ x, 0 < a x := fun x => by
    obtain ⟨q, u, hq, k, hk, rfl⟩ := ha.iwa x
    exact ha.val q u hq k hk ▸ absE_pos _
  have hk' : ∀ k ∈ K₀, p * k * p⁻¹ ∈ K := fun k h => (hk _).2 (by simpa [mul_assoc] using h)
  have ha₀ : IsHgt K₀ fun x => d * a (x * p⁻¹) := by
    refine ⟨fun x => ?_, fun q u hq k h => ?_⟩
    · obtain ⟨q, u, hq, k, h, e⟩ := ha.iwa (x * p⁻¹)
      exact ⟨q * p, _, hq.mul hp, _, (hk k).1 h, by rw [mul_inv_eq_iff_eq_mul.1 e]; group⟩
    · rw [show q * k * p⁻¹ = q * p⁻¹ * (p * k * p⁻¹) by group, ha.val _ _ (hq.mul hp.inv) _ (hk' k h), map_mul, map_mul, map_inv,
        map_inv, NNReal.coe_mul, NNReal.coe_inv, ← hd]
      field_simp
  have mul : ∀ x y Ψ, om x (om y Ψ) = om (x * y) Ψ := fun x y Ψ => by rw [map_mul, Module.End.mul_apply]
  intro x
  obtain ⟨e, e1, ⟨t₁, e2⟩, e3, e4⟩ := h1 F E σ B m n A Y r s r' s' hB hm hn h0 hA χ hχ hc _ dd om S l h b K₀ _ hb hK₀ ha₀ μ D hμ hD
    (om p⁻¹ Φ) (h.weil.2.1.pres _ _ (n0 n1)) (Submodule.finiteDimensional_of_le (S₂ := N.map (om p⁻¹)) (Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, n2 _ (hk' k k.2) Φ n1, by simp only [mul]; congr 2; group⟩))) (x * p)
  have dc : Differentiable ℂ fun z : ℂ => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) :=
    (differentiable_id.const_sub _).const_cpow (.inl (Complex.ofReal_ne_zero.2 d0.ne'))
  refine ⟨fun z => (d : ℂ) ^ (((m : ℂ) - n) / 2 - z) * e z, fun z hz => (dc.analyticAt z).meromorphicAt.mul (e1 z hz),
    ⟨t₁, fun z hz => ?_⟩, (dc.analyticAt _).mul e3, ?_⟩
  · refine (congrArg (HasSum · _) (funext fun q => ?_)).mpr ((e2 z hz).mul_left ((d : ℂ) ^ (((m : ℂ) - n) / 2 - z)))
    simp only [eisTerm, flat, mul, ← mul_assoc, mul_inv_cancel_right]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg d0.le (a0 _).le, ← mul_assoc,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 d0.ne')]
    simp
  · simp only [e4, sub_self, Complex.cpow_zero, one_mul, ← dbl_comm hB.std h hp.inv _ (n0 n1), mul, mul_inv_cancel_right]
theorem _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of_k (h1 : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k) (h2 : _root_.GlobalTheory.ThK.Dbl.FrameConj_k) (hL : _root_.GlobalTheory.ThK.Dbl.FinLevel_k) (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) :
    _root_.GlobalTheory.ThK.Dbl.SiegelWeilAniso_k := by
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hc dd om S l hd h K a hK ha Φ₁ p1 Φ₂ p2
    refine _root_.GlobalTheory.ThK.Dbl.Box.sw_transl_k h1 h2 hB hm hn h0 (.inl ⟨hA, hY⟩) hχ hc h hK ha hM.haar hM.dom
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
    · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf
  · intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hn hd' hX hW h0 hM χ hχ hc dd om S l ⟨d', ht, hd⟩ h K a hK ha μ D hμ hD Φ₁ p1 Φ₂ p2
    have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
      rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
    refine _root_.GlobalTheory.ThK.Dbl.Box.sw_transl_k h1 h2 hB hd' hn h0 (.inr ⟨hW, hX⟩) hχ hc h hK ha hμ hD
      (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
      h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
        fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) p1 p2)
    · have er : Rel B.emb ε X.θ W.θ uᵀ u'ᵀ := fun w => by
        simpa [Matrix.transpose_map, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose (e w)
      have he := hε uᵀ u'ᵀ (tr hu) (tr hu') er _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
      have ht1 : d'.e u = M.co.e uᵀ := by simpa using ht uᵀ
      have ht2 : d'.e u' = M.co.e u'ᵀ := by simpa using ht u'ᵀ
      rw [ht1, ht2]
      change dop (aOf M u'ᵀ) (lOf M u'ᵀ) f = Complex.I • dop (aOf M uᵀ) (lOf M uᵀ) f
      exact he
    · rw [actsD_unique' M hB.std hu e]
      have := n2 uᵀ (tr hu) f hf
      rwa [ht] at this
end GlobalTheory.ThK.Dbl.Box
end
end
end
