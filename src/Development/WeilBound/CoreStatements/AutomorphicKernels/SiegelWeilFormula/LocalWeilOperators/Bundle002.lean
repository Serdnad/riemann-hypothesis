module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle001
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle014
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Cx

variable {n : ℕ}

def wM {R : Type} [CommRing R] (n : ℕ) (e : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := Matrix.fromBlocks 0 1 (e • 1) 0

theorem wM_sq {R : Type} [CommRing R] (e : R) : wM n e * wM n e = e • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
  rw [wM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  simp

theorem wM_four {R : Type} [CommRing R] (e : R) (he : e * e = 1) : wM n e * wM n e * wM n e * wM n e = 1 := by
  rw [Matrix.mul_assoc (wM n e * wM n e), wM_sq, smul_mul_smul_comm, Matrix.one_mul, he, one_smul]

theorem dZ_mul (a b : ℂ) : dZ n a * dZ n b = dZ n (a * b) := by
  simp [dZ, Matrix.fromBlocks_multiply, smul_smul]
  rw [mul_comm]

theorem dZ_one : dZ n 1 = 1 := by
  simp [dZ, Matrix.fromBlocks_one]

theorem dZ_conj_nU {ζ : ℂ} (h : ζ ≠ 0) (x : Matrix (Fin n) (Fin n) ℂ) : dZ n ζ⁻¹ * nU x * dZ n ζ = nU (ζ • x) := by
  simp [dZ, nU, Matrix.fromBlocks_multiply, smul_smul, mul_inv_cancel₀ h]

theorem dZ_conj_nb {ζ : ℂ} (h : ζ ≠ 0) (c : Matrix (Fin n) (Fin n) ℂ) :
    dZ n ζ⁻¹ * nbLoc c * dZ n ζ = nbLoc (ζ⁻¹ • c) := by
  simp [dZ, nbLoc, Matrix.fromBlocks_multiply, smul_smul, mul_inv_cancel₀ h]

theorem weyl_cube_conj_unipotent (e : ℂ) (he : e * e = 1) (x : Matrix (Fin n) (Fin n) ℂ) :
    wM n e * wM n e * wM n e * nU x * wM n e = nbLoc (e • x) := by
  rw [wM_sq]
  simp [wM, nU, nbLoc, Matrix.fromBlocks_multiply, smul_smul, he]
  rw [Matrix.fromBlocks_smul]
  simp [smul_smul, he]

end Cx

end PositivityTheory.SiegelWeilFormula

end
end

section

noncomputable section

open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev SD.LF (d : SD σ) : Type := (Fin d.m → Fin d.n → ℂ) → ℂ

abbrev SD.MF (d : SD σ) : Type := Mx F E d.m d.n → ℂ

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

def StepOK (x : d.G) (A : d.LF → d.LF) (B : d.MF → d.MF) : Prop :=
  (∀ f, IsSw f → IsSw (A f)) ∧ ∀ Ψ, d.IsAwayW w Ψ → d.IsAwayW w (B Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w (A f) (B Ψ)

def Good (y : GR d.n) (g f : d.LF) : Prop :=
  ∀ Ψ, d.IsAwayW w Ψ → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w g Ψ

def OkY (y : GR d.n) : Prop := ∀ f, IsSw f → ∃ g, IsSw g ∧ R.Good w y g f

def Lc (y : GR d.n) (f : d.LF) : d.LF := if h : ∃ g, IsSw g ∧ R.Good w y g f then h.choose else 0

theorem isLocOp_of_ok (h : ∀ y, R.OkY w y) : R.IsLocOp w (R.Lc w) := by
  intro y f hf
  have hx := h y f hf
  have e : R.Lc w y f = hx.choose := by simp only [Lc, dif_pos hx]
  rw [e]
  exact ⟨hx.choose_spec.1, fun Ψ hΨ Φ hΦ hT => hx.choose_spec.2 Ψ hΨ Φ hΦ hT⟩

theorem ok_of_step {y : GR d.n} {A : d.LF → d.LF} (h : R.StepOK w (R.ι w y) A id) : R.OkY w y := by
  intro f hf
  exact ⟨A f, h.1 f hf, fun Ψ hΨ Φ hΦ hT => (h.2 Ψ hΨ).2 f hf Φ hΦ hT⟩

theorem step_comp (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {x x' : d.G} {A A' : d.LF → d.LF}
    {B B' : d.MF → d.MF} (h : R.StepOK w x A B) (h' : R.StepOK w x' A' B') :
    R.StepOK w (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun Ψ hΨ => ⟨(h.2 _ (h'.2 Ψ hΨ).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 Ψ hΨ).2 f hf Φ hΦ hT
  have e2 := (h.2 (B' Ψ) (h'.2 Ψ hΨ).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (hsch x' Φ hΦ) e1
  rw [map_mul, Module.End.mul_apply]
  exact e2

theorem ok_mul (hsch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch) {y y' : GR d.n} (h : R.OkY w y)
    (h' : R.OkY w y') : R.OkY w (y * y') := by
  intro f hf
  obtain ⟨g', hg', hG'⟩ := h' f hf
  obtain ⟨g, hg, hG⟩ := h g' hg'
  refine ⟨g, hg, fun Ψ hΨ Φ hΦ hT => ?_⟩
  rw [map_mul, map_mul, Module.End.mul_apply]
  exact hG Ψ hΨ _ (hsch _ Φ hΦ) (hG' Ψ hΨ Φ hΦ hT)

end RD

end PositivityTheory.SiegelWeilFormula

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Alg

theorem gram_loc {m n : ℕ} (fr : Matrix (Fin m) (Fin m) ℂ) (J : Matrix (Fin m) (Fin m) ℂ) (ζ s : ℂ) (hζ : ζ ≠ 0)
    (hfr : ζ • (frᵀ * J * fr.map star) = s • 1) (u : Matrix (Fin m) (Fin n) ℂ) :
    (fr * u.map star)ᵀ * J * (fr * u.map star).map star = (ζ⁻¹ * s) • (uᴴ * u) := by
  have h1 : frᵀ * J * fr.map star = (ζ⁻¹ * s) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [mul_smul, ← hfr, smul_smul, inv_mul_cancel₀ hζ, one_smul]
  have hmap : (fr * u.map star).map star = fr.map star * u := by
    ext i j
    simp [Matrix.mul_apply, star_sum]
  rw [hmap, Matrix.transpose_mul]
  calc (u.map star)ᵀ * frᵀ * J * (fr.map star * u)
        = (u.map star)ᵀ * (frᵀ * J * fr.map star) * u := by simp only [Matrix.mul_assoc]
    _ = (ζ⁻¹ * s) • (uᴴ * u) := by
        rw [h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        rfl

theorem trace_herm_real {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (((A * B).trace.re : ℝ) : ℂ) = (A * B).trace := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB, Matrix.trace_mul_comm]
  have him : (A * B).trace.im = 0 := by
    have h' := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at h'
    linarith
  exact Complex.ext (by simp) (by simp [him])

end Alg

end PositivityTheory.SiegelWeilFormula

end
end
