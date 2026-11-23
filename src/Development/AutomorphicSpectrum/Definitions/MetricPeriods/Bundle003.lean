module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.LineModel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mem_of_aeval (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]

theorem eval_map_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def]; rfl

theorem ptsOver_complex (P : Ideal (MRing ι)) : ptsOver ℂ P = mcPts P := by
  ext z
  simp only [ptsOver, mcPts, Set.mem_setOf_eq, eval_map_eq]

theorem hasVal_unique (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {w w' : 𝕜}
    (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, e1, n1, v1⟩ := h
  obtain ⟨dg', dh', g', h', hg', hh', hd', e1', n1', v1'⟩ := h'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have := hd k; have := hd' k
    simp only [Pi.add_apply]; omega
  have hom : IsMultiHomog (g * h' + -(g' * h)) (dg + dh') :=
    ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg (hdeg ▸ ProjLine.mhMul hg' hh))
  have h0 := hz.2 _ (mem_of_aeval y hom (by simp only [map_add (f := _), map_neg, map_mul, e1, e1']; ring))
  simp only [map_add (f := _), map_neg, map_mul, v1, v1'] at h0
  have : (w - w') * (aeval z h * aeval z h') = 0 := by linear_combination h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero n1 n1'))

end General

open ProjLine

end GlobalTheory.CompanionTheory.Ar.Small.LineModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

structure GroupDict (F : UnivFam (E := E) Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  M : Majorant h (Pi.basisFun E (Fin (j + j')))

  κ : ℝ
  κ_pos : 0 < κ

  π : archUnitary h (Pi.basisFun E (Fin (j + j'))) → Fin n → ℂ
  π_cont : Continuous π
  π_range : Set.range π = ballDom F.q
  π_fibre : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ M.stab
  len : ∀ a x, (F.R (π a)).normSq x = κ * M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (e x))) ^ 2

  α : latticeStab h e.range ≃* autGrp (E := E) F.form
  α_eq : ∀ γ x, e ((α γ).1 x) = ((γ : h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (e x)
  α_act : ∀ (γ : latticeStab h e.range) a,
    (F.R (π a)).EqvBy (F.R (π (archEmbed h (Pi.basisFun E (Fin (j + j'))) γ * a))) (α γ).1
  act : ∀ a₀, ∃ (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ A (ballDom F.q) ∧
    DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ a, π (a₀ * a) = A (π a)) ∧
    ∀ t ∈ ballDom F.q, ballPot F.q (A t) = ballPot F.q t + (G t).re

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.AI

def polar {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) (c : Fin n → σ → ℝ) : ℝ :=
  ∑ w : Fin n → σ, (∏ r, c r (w r)) * a w

namespace AnSq

variable {d : ℕ} {σ : Type} [Fintype σ] {SY : AnSys (d + 1) σ} {a₀ : σ} {ε : σ → ℤ} (Q : AnSq SY a₀ ε)

def pull0 (_Q : AnSq SY a₀ ε) (c : σ → ℝ) : Option σ → ℝ := fun o => o.elim 0 c


open Classical in
def pull1 (_Q : AnSq SY a₀ ε) (c : σ → ℝ) : Option σ → ℝ :=
  fun o => o.elim (c a₀) fun a => if a = a₀ then 0 else c a

def wcoef (c : σ → ℝ) (k i : ℕ) : Fin (d + 2) → Option σ → ℝ :=
  Fin.cons (α := fun _ => Option σ → ℝ) (Q.pull0 (fun a => (ε a : ℝ)) - Q.pull1 fun a => (ε a : ℝ))
    (word (d + 1) k i (Q.pull0 fun a => (ε a : ℝ)) (Q.pull1 fun a => (ε a : ℝ)) (Q.pull0 c))

def gT (t : ℝ) (x : Q.SW.X) : ℝ :=
  logNormSec Q.L' Q.v x + Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) * (SY.phT a t (Q.q 0 x) + SY.phT a t (Q.q 1 x))

def gH (x : Q.SW.X) : ℝ :=
  logNormSec Q.L' Q.v x + Q.cst + (1 / 2) * ∑ a, (ε a : ℝ) * (SY.ph a (Q.q 0 x) + SY.ph a (Q.q 1 x))

end AnSq

end GlobalTheory.CompanionTheory.Ar.PB
end
end
