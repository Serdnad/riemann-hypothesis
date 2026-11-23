module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle053
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def ConvRight : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n →
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∀ g, GlobalTheory.Eis.CosetConv (P D n) (GF D n) (sect ω H Φ z) g

def ThLin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ Φ', PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ →
    PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ' → PositivityTheory.PfSWUS.InRange V n →
    ∀ g, thetaInt ω ν (Φ + Φ') g = thetaInt ω ν Φ g + thetaInt ω ν Φ' g

def GLamBd : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ L ∈ lamSet (n := n) ψ,
    (∀ (a : ℂ) (F F' : G D n → ℂ), Continuous F → Continuous F' → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ GF D n, ∀ g, F' (γ * g) = F' g) → L (a • F + F') = a * L F + L F') ∧
    ∃ C : Set (G D n), IsCompact C ∧ ∀ (F : G D n → ℂ) (M : ℝ), Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ x ∈ C, ‖F x‖ ≤ M) → ‖L F‖ ≤ M

def GLsing : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsCharAF D.host.F ψ →
    IsInfFam θ → IsPlaceEmb θ τ ι → ∀ F : G D n → ℂ, Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
    (∀ L ∈ lamSet (n := n) ψ, L F = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ (nb : (Fin n → Fin n → ℝ) → GR n), (∀ x, mR (nb x) = nU (herm x)) →
      ∀ (g : G D n) (a b : GR n), ∫ x, F (g * ι (a * nb x * b)) * ψ₀ x = 0

def LNZ : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def MainSt : Prop :=
  AbsThm → SFrame → SEmb → SigOK → SplitFock → TensMem → LocOpEx → LocInst → LinSec → GSplit → GIauto → GIk → GIinv →
    GIdil → EisStrong → GLamBd → GLsing → PositivityTheory.PfSWUS.CoefND → ConvRight → ThLin → LNZ →
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (s0 V n) (thetaInt ω ν Φ g)

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIk : GIk := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι _hC L hL ρ hρ Ψ hΨ P g k hk
  have key : ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P) = phiS θ τ fr (cLoc l τ) Ψ (ρ k P) := by
    have h1 := hL k Ψ hΨ P
    rw [hρ k P hk] at h1
    have hmem : tens θ τ fr (fP (cLoc l τ) (ρ k P)) Ψ ∈ schwartzA θ V.rank n := by
      rw [← h1]; exact (ω (ι k) (phiS θ τ fr (cLoc l τ) Ψ P)).2
    apply Subtype.ext
    rw [h1]
    unfold phiS
    rw [dite_eq_left hmem]
  unfold thF thetaInt theta
  simp only [map_mul, Module.End.mul_apply, key]

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem phiS_eq' {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ}
    {Ψ : Mx D m n → ℂ} {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS
  rw [dite_eq_left h]

theorem herm_smul_one (t : ℝ) : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def CompInj : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (x y : Mx D m n), (∀ τ, compAt θ τ x = compAt θ τ y) →
    x.map (finPart D) = y.map (finPart D) → x = y

def WEx : Prop := ∀ (D : D7) (n : ℕ), ∃ W : G D n, mat W = blk4 0 1 (-1) 0

def UnipTau : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ (Φ : schwartzA θ V.rank n) (x : Mx D V.rank n),
      (ω (ι y) Φ).1 x = Complex.exp (Complex.I * tLoc l τ * (b * gramX ε (fr⁻¹ * compAt θ τ x)).trace) * Φ.1 x

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def sLd {m : ℕ} (L : GR n → ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (c : ℝ) (P : PX m n) (y : GR n) : ℂ :=
  L y (fP c P) 0

def pqOf {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : ℕ × ℕ :=
  if 0 < l τ then (cnt ε true, cnt ε false) else (cnt ε false, cnt ε true)

def LIl : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → l τ ≠ 0

def LIlin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    (∀ (y : GR n) (a : ℂ) (P Q : PX V.rank n), L y (fP (cLoc l τ) (a • P + Q)) = a • L y (fP (cLoc l τ) P) + L y (fP (cLoc l τ) Q)) ∧
    ∀ P : PX V.rank n, L 1 (fP (cLoc l τ) P) = fP (cLoc l τ) P

def LIlaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ e : ℤ, ∀ (P : PX V.rank n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLd L (cLoc l τ) P (y * g) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e y * sLd L (cLoc l τ) P g

def LIcell : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ (P : PX V.rank n) (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sLd L (cLoc l τ) P g = C * secN ε (cLoc l τ) (tLoc l τ) P b

def LIcont : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ P : PX V.rank n, Continuous (sLd L (cLoc l τ) P)

def LIrho : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) ∧
      ∀ P, ∃ W : Submodule ℂ (PX V.rank n), FiniteDimensional ℂ W ∧ P ∈ W ∧ (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) ∧
        ∀ Q ∈ W, ∀ l' : PX V.rank n →ₗ[ℂ] ℂ, ContinuousOn (fun k : GR n => l' (ρ k Q)) {k | InK (mR k)}

def LIkact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) →
      ∀ P (g k : GR n), InK (mR k) → sLd L (cLoc l τ) P (g * k) = sLd L (cLoc l τ) (ρ k P) g

def LIvac : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ), 0 < c →
    ((t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true)) →
    ∀ (S : GR n → ℂ) (C : ℂ), Continuous S → S 1 = 1 →
      (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → S (y * g) = F0 p q e y * S g) →
      (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b → S g = C * secN ε c t (1 : PX m n) b) →
      ∀ g, S g = F0 p q e g

def LIkvac : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ e : ℤ, (∀ g : GR n, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g) →
    ∀ k : GR n, InK (mR k) → L k (fP (cLoc l τ) 1) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k • fP (cLoc l τ) 1

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def nbar (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks 1 0 c 1

def mM (a : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks a 0 0 (aᴴ)⁻¹

def IsSch {m : ℕ} (f : (Fin m → Fin n → ℂ) → ℂ) : Prop := ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑S = f

def AwayCls {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (Ψ : Mx D m n → ℂ) : Prop :=
  (∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) →
    Ψ x = Ψ x') ∧ ∀ f, IsSch f → tens θ τ fr f Ψ ∈ schwartzA θ m n

def Decomp : Prop :=
  ∀ (n : ℕ) (y : GR n), ∃ y₁ y₂ y₃ y₄ : GR n, y = y₁ * y₂ * y₃ * y₄ ∧
    (∃ t : ℝ, mR y₁ = nU ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) ∧ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y₂ = nbar c) ∧
    (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y₃ = mM a) ∧ (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y₄ = nU b)

def LNe : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def AwayIn : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → (∀ τ', l τ' ≠ 0) → ∀ Ψ ∈ awayA θ V n l s τ,
      AwayCls θ τ fr Ψ

def SchFP : Prop := ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, IsSch (fP c P)

def OpGen : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {n : ℕ}

def reIm {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
  else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def reImInv {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
  else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem evX_eq_zero {m : ℕ} (P : PX m n) (h : ∀ u : Fin m → Fin n → ℂ, evX P u = 0) : P = 0 := by
  have h2 : (C (1 / 2 : ℂ) + C (1 / 2) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = 1 := by
    rw [← C_add, ← C_1]
    norm_num
  have hI : (C Complex.I * C (1 / (2 * Complex.I)) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = C (1 / 2) := by
    rw [← C_mul]
    congr 1
    field_simp
  have hinv : ∀ k, bind₁ reImInv (reIm (n := n) (m := m) k) = X k := by
    rintro ⟨a, i, b⟩
    cases b
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination (X (a, i, false) - X (a, i, true)) * hI + X (a, i, false) * h2
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hI + X (a, i, true) * h2
  have hQ : bind₁ reIm P = 0 := by
    apply GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real
    intro u
    let z : Fin m → Fin n → ℂ := fun a i => (u (a, i, false) : ℂ) + Complex.I * (u (a, i, true) : ℂ)
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ reIm P) = 0
    rw [eval₂Hom_bind₁]
    have hf : (fun k => eval₂Hom (RingHom.id ℂ) (fun v => ((u v : ℝ) : ℂ)) (reIm (n := n) (m := m) k)) =
        fun k => if k.2.2 = true then star (z k.1 k.2.1) else z k.1 k.2.1 := by
      funext ⟨a, i, b⟩
      cases b
      · simp [reIm, z]
      · apply Complex.ext <;> simp [reIm, z]
    rw [hf]
    exact h z
  calc P = bind₁ reImInv (bind₁ reIm P) := by
        rw [bind₁_bind₁]
        simp only [hinv]
        rw [bind₁_X_left]
        rfl
    _ = 0 := by rw [hQ, map_zero]

theorem gs_ne_zero {m : ℕ} (c : ℝ) (u : Fin m → Fin n → ℂ) : gs c u ≠ 0 := Complex.exp_ne_zero _

theorem fP_inj {m : ℕ} (c : ℝ) {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  have h0 : P - Q = 0 := by
    apply evX_eq_zero
    intro u
    have := congrFun h u
    unfold fP at this
    have h2 := mul_right_cancel₀ (gs_ne_zero c u) this
    unfold evX at h2 ⊢
    rw [map_sub, h2, sub_self]
  exact sub_eq_zero.1 h0

theorem fP_add_smul {m : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add (f := _), MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

section

noncomputable section

open Filter Topology MvPolynomial Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def matLin (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) where
  toFun y := fun a i => ∑ c, M a c * y c i
  map_add' y z := by funext a i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext a i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Complex.real_smul, Complex.real_smul]; ring

def matL (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (matLin M)

theorem matL_apply (M : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    matL M y a i = ∑ c, M a c * y c i := rfl

theorem matL_mul (M N : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → Fin n → ℂ) : matL (M * N) y = matL M (matL N y) := by
  funext a i
  simp only [matL_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matL_one (y : Fin m → Fin n → ℂ) : matL (1 : Matrix (Fin m) (Fin m) ℂ) y = y := by
  funext a i
  simp [matL_apply, Matrix.one_apply]

theorem contDiff_A (X : Matrix (Fin m) (Fin m) ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => matL (n := n) (NormedSpace.exp ((t : ℂ) • X))) := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let Lm : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ((Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ)) :=
    { toFun := matL
      map_add' := fun M N => by ext y a i; simp [matL_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r M => by
        ext y a i
        simp only [matL_apply, Matrix.smul_apply, RingHom.id_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply,
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Complex.real_smul, Complex.real_smul]; ring }
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp ∘ (fun t : ℝ => t • X) := by
      funext t; simp only [Function.comp_apply, Complex.coe_smul]
    rw [e]
    exact (contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt).comp
      (contDiff_id.smul contDiff_const)
  exact (LinearMap.toContinuousLinearMap Lm).contDiff.comp hexp

theorem hasDerivAt_entry (X : Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) (X a c) 0 := by
  letI : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  let ent : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ))
  have h2 := (LinearMap.toContinuousLinearMap ent).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c) =
      (LinearMap.toContinuousLinearMap ent) ∘ (fun u : ℝ => NormedSpace.exp (u • X)) := by
    funext t; simp only [Function.comp_apply, Complex.coe_smul]; rfl
  have h3 : HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) a c)
      ((LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 := by
    rw [e]; exact h2
  have h4 : (LinearMap.toContinuousLinearMap ent) (NormedSpace.exp ((0 : ℝ) • X) * X) = X a c := by
    rw [zero_smul, NormedSpace.exp_zero, one_mul]; rfl
  rw [h4] at h3
  exact h3

theorem exists_gs (c : ℝ) (hc : 0 < c) : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, g u = gs c u := by
  obtain ⟨g0, hg0⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_gauss (m := m) (n := n)
  set s : ℝ := Real.sqrt (c / (2 * Real.pi)) with hs
  have hs0 : s ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  let L : (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) :=
    (LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs0).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L g0, fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg0]
  have key : 2 * Real.pi * ∑ a, ∑ i, ‖(L u) a i‖ ^ 2 = c * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
    have h1 : ∀ a i, ‖(L u) a i‖ ^ 2 = s ^ 2 * ‖u a i‖ ^ 2 := fun a i => by
      change ‖(s • u) a i‖ ^ 2 = _
      rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [h1, ← Finset.mul_sum]
    rw [hs, Real.sq_sqrt (by positivity)]
    field_simp
  unfold gs
  rw [key]

theorem exists_fP (c : ℝ) (hc : 0 < c) (P : PX m n) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, φ u = fP c P u := by
  obtain ⟨g, hg⟩ := exists_gs (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) P) g,
    fun u => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.PolyGaussSchwartz.eval_temperate P), hg, smul_eq_mul]
  rfl

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end
