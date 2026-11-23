module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle009
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle007
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section



section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Pair
variable {n d : ℕ}
variable {X : Spc F E n} {W : Spc F E d}
end Pair
def EpsOf_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (n : ℕ) (X : Spc F E n) (r s : ℕ), (X.IsHerm σ B r s ∨ X.IsSkew σ B r s) → EpsHerm σ X.J ∧ r + s = n ∧ ∀ fr : Frame σ X.J, fr.IsGood → fr.r ≤ min r s
def CoefEq_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ (g : UA σ X.J) (h : UA σ W.J) (z : Ten F E n d), coef F B.ψ μ (om (g, h) Φ₁) (om (g, h) Φ₂) (M.co.e z) = coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * z * (mat h⁻¹)ᵀ))
def CoefBd_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ μ : Measure (Fin n × Fin d → AF F), μ.IsAddHaarMeasure → ∀ φ₁ ∈ SB (Fin n × Fin d → Af F), ∀ φ₂ ∈ SB (Fin n × Fin d → Af F), ∀ N : ℕ, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧ IsCompact C ∧ ∀ (f₁ f₂ : SInf F (Fin n × Fin d)) (z : Ten F E n d), ‖coef F B.ψ μ (pureA F f₁ φ₁) (pureA F f₂ φ₂) (M.co.e z)‖ ≤ p f₁ * p f₂ * maj B.emb C N z
end PositivityTheory.ThKEst
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
def SiegelWeilAniso_k : Prop := _root_.GlobalTheory.ThK.Dbl.SWAniso_k ∧ _root_.GlobalTheory.ThK.Dbl.SWAnisoX_k
def EisBL_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U
def FrameConj_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → ∃ b K₀ p t, IsFrame2 σ Y b ∧ IsStdK B b K₀ ∧ IsPar p t ∧ ∀ k, k ∈ K ↔ p⁻¹ * k * p ∈ K₀
end GlobalTheory.ThK.Dbl
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
namespace GlobalTheory.SplitLagrF
open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}
variable {B : Base F E}
theorem prof_add_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f g : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (hg : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g) (y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (f + g) y = prof σ JS JT ξ₀ B.ψ ν 𝓕 f y + prof σ JS JT ξ₀ B.ψ ν 𝓕 g y := by
  unfold prof
  rw [GlobalTheory.WeilPartsF.heisOF_add]
  exact integral_add
    (integrableOn_dC hν h𝓕 (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf))
    (integrableOn_dC hν h𝓕 (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) g hg))
theorem prof_heis_dC_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (a y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * a) f) y =
      commF σ JS JT ξ₀ B.ψ y (a + a) * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  unfold prof
  rw [heisOF_comm, lagrInt_smul, commF_aC_dC, _root_.GlobalTheory.SplitLagrF.lagrInt_heis_dC_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 _
    (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf)]
theorem prof_heis_lift_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (g y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f) y =
      commF σ JS JT ξ₀ B.ψ g y * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  rw [_root_.GlobalTheory.SplitLagrF.prof_heis_dC_k hB hS hT hξ hσξ hν h𝓕 hf, neg_hlf_add, GlobalTheory.SplitVacF.commF_swap]
end GlobalTheory.SplitLagrF
end
end
end
