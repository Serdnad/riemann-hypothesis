module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsIsoPair {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (u : Fin 2 → Fin r → E) : Prop :=
  (∀ i k, herm G (u i) (u k) = 0) ∧ LinearIndependent E u

def IsHermFam {ι : Type} (b : ι → Fin 2 → Fin 2 → ℂ) : Prop := ∀ τ i k, b τ k i = conj (b τ i k)

def dEnat (E : Type) [Field E] [NumberField E] : ℕ := (NumberField.discr E).natAbs

namespace Data

variable {r : ℕ} (X : Data E r)

def zmat (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => (if a = j then 1 else 0) -
    I * X.c τ * ∑ i, ∑ k, b τ i k * emb τ.1 (u i) a * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)

def Zb (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (X.zmat u b τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def pairR (χ b : X.Ψ → Fin 2 → Fin 2 → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re

def embH (β : Matrix (Fin 2) (Fin 2) E) : X.Ψ → Fin 2 → Fin 2 → ℂ := fun τ i k => τ.1 (β i k)

def LZ (g : ℕ) : Set (X.Ψ → Fin 2 → Fin 2 → ℂ) :=
  {b | ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧
    (∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((g * dEnat E : ℕ) : E) / 2 * γ) ∧ b = X.embH β}

def IsFreqZ (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ b ∈ X.LZ g, ∃ k : ℤ, 2 * X.pairR χ b = k

def IsLZBasis (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ) : Prop :=
  (∀ j, ω j ∈ X.LZ g) ∧ (∀ b ∈ X.LZ g, ∃! n : Fin (4 * Fintype.card X.Ψ) → ℤ, b = ∑ j, (n j : ℂ) • ω j) ∧
    LinearIndependent ℝ ω


open scoped Classical in
open Classical in
def fz (u : Fin 2 → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (G : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℂ :=
  if IsHermFam χ ∧ X.IsFreqZ g χ then
    if h : ∃ ω, X.IsLZBasis g ω then
      ∫ t in Set.pi Set.univ (fun _ : Fin (4 * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1),
        G (X.Zb u (∑ j, (t j : ℂ) • h.choose j) x) *
          cexp (-(4 * Real.pi * I) * X.pairR χ (∑ j, (t j : ℂ) • h.choose j))
    else 0
  else 0

def chiAt (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (a : X.Ψ → Fin 2 → ℂ) (τ : X.Ψ) : ℂ :=
  ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)

def uvec (u : Fin 2 → Fin r → E) (a : X.Ψ → Fin 2 → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => ∑ i, a τ i • emb τ.1 (u i)

end Data

def UnipotentVectorGroup : Prop :=
  ∀ (r : ℕ) (X : Data E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u →
    (∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x) ∧
    ∀ b, IsHermFam b →
      X.IsUnitaryC (X.zmat u b) ∧ (∀ τ i, Matrix.mulVec (X.zmat u b τ) (Data.emb τ.1 (u i)) = Data.emb τ.1 (u i)) ∧
      (∀ τ, (X.zmat u b τ).det = 1) ∧
      (∀ x ∈ X.dom, X.Zb u b x ∈ X.dom) ∧ (∀ x x', X.SameFlag x x' → X.SameFlag (X.Zb u b x) (X.Zb u b x')) ∧
      (∀ (la : Wt X.Ψ r) x, x ∈ X.dom → X.nfac la (X.Zb u b x) = X.nfac la x) ∧
      (∀ x τ, x ∈ X.dom → X.maj (X.Zb u b x) τ (Data.emb τ.1 (u 0)) = X.maj x τ (Data.emb τ.1 (u 0))) ∧
      (∀ x ∈ X.FramesOverBasis (u 0), X.Zb u b x ∈ X.FramesOverBasis (u 0)) ∧
      (∀ (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℂ) x, X.Zb u b (X.flowV (X.uvec u a) s x) =
        X.flowV (X.uvec u a) s (X.Zb u b x))
    ∧ ∀ (a : X.Ψ → Fin 2 → ℂ) (s : X.Ψ → ℝ) x,
      X.flowV (X.uvec u a) (fun τ => (s τ : ℂ)) x =
        X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) x

def UnipotentLatticeLift : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    (∀ b ∈ X.LZ X.g, ∃ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.zmat u b τ) ∧
    (∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
      (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
      ∀ b ∈ X.LZ X.g, ∀ x ∈ X.dom, P (X.Zb u b x) = P x) ∧
    ∀ χ, IsHermFam χ → X.IsFreqZ X.g χ → ∃ β : Matrix (Fin 2) (Fin 2) E,
      (∀ i k, cc (β i k) = β k i) ∧ χ = X.embH β ∧
      ∀ i k, IsIntegral ℤ (((X.g * dEnat E ^ 2 : ℕ) : E) * β i k)

def FourierCoefficientProperties : Prop :=
  ∀ (r : ℕ) (X : Data E r) (u : Fin 2 → Fin r → E) (g : ℕ), IsIsoPair X.Gm u → 0 < g →
    ∀ (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ), DifferentiableOn ℂ G X.dom →
    (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = bchar la b * G x) →
    (∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ,
      (DifferentiableOn ℂ (X.fz u g χ G) X.dom ∧
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.fz u g χ G (rmul x b) = bchar la b * X.fz u g χ G x) ∧
        ∀ b, IsHermFam b → ∀ x ∈ X.dom,
          X.fz u g χ G (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * X.fz u g χ G x) ∧
      (∀ x ∈ X.dom, ∀ M : ℝ, (∀ b, IsHermFam b → X.pnorm la G (X.Zb u b x) ≤ M) →
        X.pnorm la (X.fz u g χ G) x ≤ M)
    ∧ (∀ x ∈ X.dom, Summable (fun χ : X.Ψ → Fin 2 → Fin 2 → ℂ => ‖X.fz u g χ G x‖) →
        HasSum (fun χ : X.Ψ → Fin 2 → Fin 2 → ℂ => X.fz u g χ G x) (G x))

def FourierCoefficientSupport : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ (ν : X.Ψ → ℝ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ), ∀ x ∈ X.dom,
      X.fz u X.g χ (X.fj la (u 0) ν P) x =
        if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P x else 0

def HolomorphicPeriodicityExtension : Prop :=
  ∀ (r : ℕ) (X : Data E r) (e : X.Ψ → Fin r → ℂ), X.IsIsoV e → ∀ G : Frame X.Ψ r → ℂ,
    DifferentiableOn ℂ G X.dom → ∀ (m : X.Ψ → ℂ), ∀ x ∈ X.dom,
    (∀ s : X.Ψ → ℝ, G (X.flowV e (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, m τ * s τ) * G x) →
    ∀ s : X.Ψ → ℂ, X.flowV e s x ∈ X.dom →
      G (X.flowV e s x) = cexp (4 * Real.pi * I * ∑ τ, m τ * s τ) * G x

def NonvanishingCoefficientPositivity : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (u : Fin 2 → Fin r → E), IsIsoPair X.Gm u → (∀ i, u i ∈ X.Λ) →
    ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la →
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, (∃ x ∈ X.dom, X.fz u X.g χ P x ≠ 0) →
      ∀ τ, (Matrix.of (χ τ)).PosDef

def IsotropicFlowSetting {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ) : Prop :=
  ShortVectorHypotheses X la P ξ ν c1 w z0 ∧ x ∈ X.L' ∧ herm X.Gm x ξ = 0 ∧ herm X.Gm x x = 0 ∧ (∀ e : E, x ≠ e • ξ) ∧
    (∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0) ∧
    ∀ τ, X.uvec ![ξ, (X.NC : E) • x] a τ =
      ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
        X.ucomp z0 ξ (X.embV x) τ

def CoefficientIndexLowerBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ) (ε : ℝ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a → 0 < ε →
    (∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) ≤ ε) →
    ∀ χ : X.Ψ → Fin 2 → Fin 2 → ℂ, (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x] X.g χ (X.fj la ξ ν P) y ≠ 0) →
      (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) ≤
        2 * ∑ τ, (X.chiAt χ a τ).re

def CoefficientHeightBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ)
    (c1 w : ℝ) (z0 : Frame X.Ψ r) (x : Fin r → E) (a : X.Ψ → Fin 2 → ℂ),
    IsotropicFlowSetting X la P ξ ν c1 w z0 x a →
    (∀ τ, X.c τ * X.maj z0 τ (Data.emb τ.1 ((X.NC : E) • x)) ≤
      (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) →
    ∀ t : ℝ, 1 ≤ t →
      let K2 := 1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
        (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)
      let S := {χ : X.Ψ → Fin 2 → Fin 2 → ℂ | (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x] X.g χ
        (X.fj la ξ ν P) y ≠ 0) ∧ 2 * ∑ τ, (X.chiAt χ a τ).re ≤ t}
      S.Finite ∧ (S.ncard : ℝ) ≤ (K2 * t) ^ (4 * fdeg E)

def CountingExponentialSum : Prop :=
  ∀ (K N w : ℝ), 1 ≤ K → 1 ≤ N → 0 ≤ w → ∀ (ι : Type) (t : ι → ℝ),
    (∀ j, w + N * Real.log (2 * K * N) + N + 2 < t j) →
    (∀ t0 : ℝ, 1 ≤ t0 → {j | t j ≤ t0}.Finite ∧ ({j | t j ≤ t0}.ncard : ℝ) ≤ (K * t0) ^ N) →
    Summable (fun j => Real.exp (-Real.pi * t j)) ∧
      2 ^ (w / 2) * ∑' j, Real.exp (-Real.pi * t j) < 1 / 2

def IsotropicOutsideLine : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ → ∀ z0 ∈ X.FramesOverBasis ξ, ∀ x ∈ X.L',
    herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) → (∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) < 1) →
    herm X.Gm x x = 0 ∧ ∃ α : 𝓞 E,
      let x' := x + ((X.NA : E) * α) • ξ
      x' ∈ X.L' ∧ herm X.Gm x' ξ = 0 ∧ X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) ∧
      (∀ τ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤
        2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA) ∧
      ∀ τ, X.c τ * X.maj z0 τ (Data.emb τ.1 ((X.NC : E) • x')) ≤
        (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_kappa (X : Data E r) (τ : X.Ψ) : τ.1 X.κ0 = -(I * X.c τ) := by

  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by
      have hξ : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      rw [← emb_cc']
      rcases X.κ0_xi with h | h <;> rw [h] <;> simp [cc, hξ, map_mul, map_neg, map_ofNat]
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hz : τ.1 X.κ0 = ((τ.1 X.κ0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := by
    conv_lhs => rw [hz]
    simp
  have hnorm : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> rw [h] <;> simp [norm_mul, map_ofNat]
  have him := X.κ0_sign τ
  rw [hn, abs_of_neg him] at hnorm
  rw [hz, ← hnorm]
  push_cast
  ring

lemma transvMat_mul (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α β : E) : transvMat G ξ α * transvMat G ξ β = transvMat G ξ (α + β) := by
  set w : Fin r → E := fun b => ∑ k, G b k * cc (ξ k) with hw
  have hA : ∀ γ, transvMat G ξ γ = 1 + γ • Matrix.vecMulVec ξ w := by
    intro γ
    ext a b
    simp only [transvMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, hw]
    ring
  have h0 : ∑ j, w j * ξ j = 0 := by
    rw [← hξ]
    unfold herm
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hw, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

  have hAA : Matrix.vecMulVec ξ w * Matrix.vecMulVec ξ w = 0 := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    calc ∑ j, ξ a * w j * (ξ j * w b) = ξ a * w b * ∑ j, w j * ξ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  rw [hA, hA, hA, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, smul_mul_smul_comm, hAA,
    smul_zero, add_zero, add_smul]
  abel

lemma transvMat_zero (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : transvMat G ξ 0 = 1 := by
  ext a b
  simp [transvMat, Matrix.one_apply]

lemma transvMat_pow (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : herm G ξ ξ = 0)
    (α : E) (n : ℕ) : transvMat G ξ α ^ n = transvMat G ξ (n * α) := by
  induction n with
  | zero => simp [transvMat_zero]
  | succ k ih =>
    rw [pow_succ, ih, transvMat_mul G hξ]
    congr 1
    push_cast
    ring

lemma transvMat_map (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ) (α : E) (s : ℂ)
    (hs : τ.1 α = -(I * X.c τ * s)) :
    (transvMat X.Gm ξ α).map τ.1 = X.flowMat ξ τ s := by
  ext a b
  simp only [Matrix.map_apply, transvMat, Data.flowMat, Matrix.of_apply]
  split_ifs <;> simp [map_sum, emb_cc', hs] <;> ring

variable (X : Data E r)

def cR (p : X.Ψ → ℝ) : X.Ψ → ℂ := fun τ => (p τ : ℂ)

lemma flow_real_mem_dom {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (p : X.Ψ → ℝ) (y : Frame X.Ψ r)
    (hy : y ∈ X.dom) : X.flow ξ (cR X p) y ∈ X.dom := by
  have h0 := (flow_mem_dom_iff X hξ y hy 0).1 (by rw [flow_zero]; exact hy)
  have e : (fun τ => (cR X p τ).im) = fun τ => ((0 : X.Ψ → ℂ) τ).im := by
    funext τ
    simp [cR]
  rw [flow_mem_dom_iff X hξ y hy, e]
  exact h0

lemma chi_pow (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (n : ℕ) :
    X.χ la (γ ^ n) = X.χ la γ ^ n := by
  have h1 : X.χ la 1 = 1 := by
    obtain ⟨N, hN, hfin⟩ := X.χ_fin la
    have hne : X.χ la 1 ≠ 0 := by
      intro h
      have := hfin 1 X.Γ.one_mem
      rw [h, zero_pow hN.ne'] at this
      exact zero_ne_one this
    have hsq := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
    rw [mul_one] at hsq
    exact mul_left_cancel₀ hne (hsq.symm.trans (mul_one _).symm)
  induction n with
  | zero => simp [h1]
  | succ k ih => rw [pow_succ, X.χ_mul la _ (X.Γ.pow_mem hγ k) _ hγ, ih, pow_succ]

lemma sec_periodic_gen (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a)
    (y : Frame X.Ψ r) (hy : y ∈ X.dom) :
    P (X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y) = P y := by
  obtain ⟨γ0, hγ0, hγ0m⟩ := X.transv ξ hξΛ hξ a ha hai
  have hγ : γ0 ^ X.chiOrd la ∈ X.Γ := X.Γ.pow_mem hγ0 _
  have hχ : X.χ la (γ0 ^ X.chiOrd la) = 1 := by
    rw [chi_pow X la hγ0]
    exact (X.χ_fin la).choose_spec.2 γ0 hγ0
  have hmat : ((γ0 ^ X.chiOrd la : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      transvMat X.Gm ξ ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) := by
    rw [Units.val_pow_eq_pow_val, hγ0m, transvMat_pow X.Gm hξ]

  have hlact : lact (γ0 ^ X.chiOrd la) y =
      X.flow ξ (cR X fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) y := by
    funext τ
    have hta : τ.1 a = ((τ.1 a).re : ℂ) := by
      have h := emb_cc' τ.1 a
      rw [ha] at h
      apply Complex.ext
      · simp
      · have := congrArg Complex.im h
        simp at this
        simp
        linarith
    have hs : τ.1 ((X.chiOrd la : E) * ((X.m : E) * a * X.κ0)) =
        -(I * X.c τ * cR X (fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re) τ) := by
      rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, emb_kappa X τ]
      conv_lhs => rw [hta]
      simp only [cR]
      push_cast
      ring
    simp only [lact, Data.flow]
    rw [hmat, transvMat_map X ξ τ _ _ hs]
  rw [← hlact, hP.2.2 _ hγ y hy, hχ, one_mul]

lemma cR_add (p q : X.Ψ → ℝ) : cR X (p + q) = cR X p + cR X q := by
  funext τ
  simp [cR]

lemma cR_zero : cR X 0 = 0 := by
  funext τ
  simp [cR]

lemma sec_periodic (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0) {p : X.Ψ → ℝ} (hp : p ∈ X.periods la) :
    ∀ y ∈ X.dom, P (X.flow ξ (cR X p) y) = P y := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨a, ha, hai, rfl⟩ := hp
    exact fun y hy => sec_periodic_gen X la P hP hξΛ hξ a ha hai y hy
  | zero =>
    intro y _
    rw [cR_zero, flow_zero]
  | add p q _ _ hp hq =>
    intro y hy
    rw [cR_add, ← flow_flow X hξ, hp _ (flow_real_mem_dom X hξ q y hy), hq y hy]
  | neg p _ hp =>
    intro y hy
    have hz := flow_real_mem_dom X hξ (-p) y hy
    have e : X.flow ξ (cR X p) (X.flow ξ (cR X (-p)) y) = y := by
      rw [flow_flow X hξ, ← cR_add, add_neg_cancel, cR_zero, flow_zero]
    rw [← hp _ hz, e]

end ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
end
