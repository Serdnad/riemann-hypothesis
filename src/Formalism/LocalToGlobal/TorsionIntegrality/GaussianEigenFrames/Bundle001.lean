module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementF
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
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

@[expose] public section

section

noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4)
open Formalism.L2.Th1.Top (phC)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer)
open Formalism.L2.Th1.G (betaPair)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

def IsEigenFrame {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (th0 : ℂ_[p]) {n J H : Type} [Fintype n]
    [DecidableEq n] [Fintype J] {N0 N1 : ℕ} (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (E : Type) [Field E] [NumberField E] (cE s : E ≃+* E) (δ : E) (emb : Bool × H → (E →+* ℂ_[p]))
    (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)) (v : J → n → ℂ) (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) : Prop :=
  δ ^ 2 = -(p : E) ∧ cE δ = -δ ∧ s δ = -δ ∧ (∀ y, cE (cE y) = y) ∧ (∀ y, s (s y) = y) ∧
  (∀ y, s (cE y) = cE (s y)) ∧ Function.Injective emb ∧ (∀ τ ρ, emb τ δ = emb ρ δ) ∧
  (∀ t y, emb (true, t) y = emb (false, t) (s (cE y))) ∧ (∀ τ (y : E), s y = y → emb τ y ∈ MaximalUnramifiedExtension p) ∧
  (∀ e e' : 𝓞 E, (e' : E) = cE (e : E) → ∀ x y, matH h (act e x) y = matH h x (act e' y)) ∧
  (∀ e, ∀ x ∈ Λ, act e x ∈ Λ) ∧ (∀ j, InMul L Λ (v j)) ∧ (∀ j x, ‖A j x‖ ≤ 1) ∧
  (∀ (e : 𝓞 E) x i, mapVec (ι : ℂ →+* ℂ_[p]) (act e) (fun i' => frameM (ι : ℂ →+* ℂ_[p]) v A i' x) i =
    emb x.1 (e : E) * frameM (ι : ℂ →+* ℂ_[p]) v A i x) ∧
  ∀ (t : H) (ab ab' : Fin N0 × Fin N1), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
    ∑ j, ∑ k, A j ((false, t), ab) * ι (hOK L h (v j) (v k)) * A k ((true, t), ab') =
      (if ab = ab' then u t else 0) + th0 * e

def ShapeEigenLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime], p ∣ dK → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p])
    (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (cE s : E ≃+* E) (δ : E)
    (emb : Bool × H → (E →+* ℂ_[p])) (act : 𝓞 E → (n → ℂ) →ₗ[ℂ] (n → ℂ)),
    IsEigenFrame ι (cmL a₀ b₀ dK ha hdK lam hlam) (ι (Complex.I * ((Real.sqrt dK : ℝ) : ℂ))) h Λ E cE s δ emb act v A u →
    ‖(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)‖ ≤ ‖(dK : ℂ_[p])‖ ^ (-(1 / 2 : ℝ)) ∧
    ∃ sg : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p], JetsIntegral sg ∧
      (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) =
        Formalism.DworkPowerSeriesWeights.mvExp ((-(Formalism.L2.Th1.C.jet (logSer (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι)) (phC p (cmL a₀ b₀ dK ha hdK lam hlam) ι) 2)) • betaPair H N0 N1 u) * sg

end Formalism.L2.Th1.GD
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH thetaZ)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

def TensZ : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (ε : ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ¬ p ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    relIdx (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) ≠ 0 →
    ‖ι ε‖ ≤ 1 →
    Formalism.L2.Th1.H.tens4 θ = ε • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₁ →
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ p ∣ N → (N : ℂ) • t ∈ Λ →
    ∃ (κ : Type) (_ : Fintype κ) (r : κ → ℂ_[p]) (s : κ → Fin 4 × n → ℂ) (N' : ℕ),
      (∀ k, ‖r k‖ ≤ 1) ∧ 0 < N' ∧ ¬ p ∣ N' ∧ (∀ k w, (N' : ℂ) * s k w ∈ (cmL a₀ b₀ dK ha hdK lam hlam).lattice) ∧
      linSub (fun w w' => ι (g₁.symm (Pi.single w' 1) w))
          (Formalism.L2.Th1.G.tens4 (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv (opU (matH h) t θ)))) =
        thetaZ p (cmL a₀ b₀ dK ha hdK lam hlam) ι (lam * a₀) r s

def JetsLinZ : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (n : Type) [Fintype n] (T : MvPowerSeries n K) (γ : Fin 4 × n → Fin 4 × n → K),
    JetsIntegral (linSub γ (Formalism.L2.Th1.G.tens4 T)) →
    ∀ (ν : Type) [Fintype ν] (M : n → ν → K) (Cm : Fin 4 × n → Fin 4 × ν → K),
    (∀ w x, ‖Cm w x‖ ≤ 1) →
    (∀ (a : Fin 4) (i : n) (b : Fin 4) (x : ν),
      ∑ w, γ (a, i) w * Cm w (b, x) = if a = b then M i x else 0) →
    JetsIntegral (linSub M T)

def IntOpTwoLoc : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)),
    IsSelfDual (matH h) Λ → (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) →
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
  ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 (cmL a₀ b₀ dK ha hdK lam hlam) ι W → IntCurve W → ‖W.a₁‖ = 1 →
    LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ 2 ι →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[2]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 2 ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[2]), (∀ j x, ‖A j x‖ ≤ 1) →
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[2]) h θ r t (frameM (ι : ℂ →+* ℂ_[2]) v A)) ∧
    ∀ P : MvPolynomial ν ℂ_[2], (∀ k, ‖AddMonoidAlgebra.coeff P k‖ ≤ 1) →
      ‖jetPair P (thetaLin (ι : ℂ →+* ℂ_[2]) h θ r t (frameM (ι : ℂ →+* ℂ_[2]) v A))‖ ≤ 1

end Formalism.L2.Th1.GD
end
end
