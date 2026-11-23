module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle005
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelConditionEquivalent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def LocBasisMM : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    ∃ b : Fin (Fintype.card D.what₂.Tau) → Matrix (Fin 1) (Fin 1) D.host.E,
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) b ∧
      ‖(Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E))).det‖ = 1 ∧
      (Matrix.of fun (τ τ' : D.what₂.Tau) =>
        lamC lam (embT D τ (b (Fintype.equivFin D.what₂.Tau τ') 0 0))).det ≠ 0

def RatCoord : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
      Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.matH (Formalism.L2.Th1.H.blk4 (hOne B.L D.what₂.Tau)))
        (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) →
      ¬ p ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) →
      Formalism.L2.Th1.H.relIdx
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))
        (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 →
    ∀ b : Fin (Fintype.card D.what₂.Tau) → Matrix (Fin 1) (Fin 1) D.host.E,
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) b →
    ∃ c : Fin 4 × D.what₂.Tau → Fin 4 → Fin (Fintype.card D.what₂.Tau) → D.host.K,
      (∀ w i' τ, g₁.symm (Pi.single w 1) (i', τ) =
        ∑ m, D.host.φ₀ ((c w i' m : D.host.K) : D.host.E) * embT D τ (b m 0 0)) ∧
      (∀ w i' m, ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : D.host.K) * c w i' m)) ∧
      ∀ w w', ∑ i', ∑ m, ∑ n, ((c w i' m : D.host.K) : D.host.E) * ((hYY D (b m) (b n) : D.host.K) : D.host.E) *
        D.host.conj ((c w' i' n : D.host.K) : D.host.E) = if w = w' then 1 else 0

def FixConj : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ → ∀ y : MaximalUnramifiedExtension p, σ (σ y) = y →
      (y : ℂ_[p]) ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))) ∧
      ∀ σp : ℂ_[p] →+* ℂ_[p], IsConjP D lam σp → σp (y : ℂ_[p]) = ((σ y : MaximalUnramifiedExtension p) : ℂ_[p])

end Formalism.L2.KerInert
end
end

section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def ConjExt : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ lam : Qbar →+* ℂ_[p], ∃ σ : ℂ_[p] →+* ℂ_[p], IsConjP D lam σ

def FrameONB : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∀ g₁ : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
      Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.matH (Formalism.L2.Th1.H.blk4 (hOne B.L D.what₂.Tau)))
        (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) →
      ¬ p ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) →
      Formalism.L2.Th1.H.relIdx
        (Formalism.L2.Th1.H.imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))
        (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 →
    ∀ σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p, Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ →
    ∀ (γ : Matrix (Fin 4 × D.what₂.Tau) (Fin 4 × D.what₂.Tau) (MaximalUnramifiedExtension p)) (B' : Matrix D.what₂.Tau D.what₂.Tau ℂ_[p]),
      Formalism.L2.Th1.Top.IsFrameH σ ι g₁ γ B' →
    ∀ σp : ℂ_[p] →+* ℂ_[p], IsConjP D lam σp →
      IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σp
        (fun i k => B' k.1 ((Fintype.equivFin D.what₂.Tau).symm i))

end Formalism.L2.KerInert
end
end

section

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (thetaS)
open Formalism.L2.Th1.Top (IsLTNorm phL)

def ReadTh1 (p : ℕ) [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n] (B' : Matrix n n ℂ_[p])
    (F : MvPowerSeries n ℂ_[p]) : MvPowerSeries n ℂ_[p] :=
  MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (B' i j) * Formalism.InvariantFactorPaths.G7.at1 j (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) F

def liftT (D : D7) {p : ℕ} [Fact p.Prime] (F : MvPowerSeries D.what₂.Tau ℂ_[p]) :
    MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p] :=
  MvPowerSeries.subst (fun τ : D.what₂.Tau => (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p])) F

def OneCopyTh1 : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι →
    ∃ (g2 g3 ε s2 : MaximalUnramifiedExtension p) (σ : ℂ_[p] →+* ℂ_[p]) (r : ℕ) (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p]))
      (e : D.what₂.Tau ≃ Fin r),
      IsLTNorm p B.L ι g2 g3 s2 ε ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖(g2 : ℂ_[p]) ^ 3 - 27 * (g3 : ℂ_[p]) ^ 2‖ = 1 ∧ ‖ε‖ = 1 ∧
      (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) ∧
      IsConjP D lam σ ∧ IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σ v ∧
      ∀ (t : D.what₂.Tau → ℂ) (N : ℕ), 0 < N → ¬ p ∣ N → (N : ℂ) • t ∈ B.lamM →
        Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries D.what₂.Tau ℂ_[p]) *
          ReadTh1 p (fun τ j => v (e j) (τ, 0, 0))
            (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
              (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM))))

def CoordTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι → ∀ s : VC D 1 1,
      TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) s →
      pSer D lam (U D B.tor s (B.thZero 1 1)) =
        liftT D (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM))) ∧
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (N : ℂ) • (fun τ => s τ 0 0) ∈ B.lamM

end Formalism.L2.KerInert
end
end
