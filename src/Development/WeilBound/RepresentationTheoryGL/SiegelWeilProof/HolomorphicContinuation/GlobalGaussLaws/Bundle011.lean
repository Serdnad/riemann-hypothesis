module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle010
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

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

variable {D : D7} {n : ℕ}

def reidx (y : M2 n) : Matrix (Fin (n + n)) (Fin (n + n)) ℂ := y.submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def IsPlaceEmb (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n) : Prop :=
  Continuous ι ∧ ∀ y : GR n, compAt θ τ (mat (ι y)) = reidx (mR y) ∧
    (∀ τ', τ' ≠ τ → compAt θ τ' (mat (ι y)) = 1) ∧ (mat (ι y)).map (finPart D) = 1

def IsTauFrame (V : HSp D) (τ : D.what₂.Tau) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Prop :=
  IsUnit fr.det ∧ frᴴ * gramAt D V τ * fr = Matrix.diagonal (sgn ε) ∧ frᴴ * (gramAt D V τ * s τ) * fr = 1

def cLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : ℝ := 2 * Real.pi * |l τ|

def tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : ℝ := 2 * Real.pi * l τ


open Classical in
def gAway (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * ∑ τ' ∈ Finset.univ.filter (fun τ' => τ' ≠ τ),
    ((|l τ'| : ℝ) : ℂ) * Matrix.trace ((z τ')ᴴ * (gramAt D V τ' * s τ') * z τ'))

def awayA (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Submodule ℂ (Mx D V.rank n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧ (∀ v ∈ p.vars, v.1 ≠ τ) ∧
      φ = fun x => evalPoly p (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
        g (fun i j => finPart D (x i j))}

def tens {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ)
    (Ψ : Mx D m n → ℂ) : Mx D m n → ℂ :=
  fun x => f (fr⁻¹ * compAt θ τ x) * Ψ x

def fP {m : ℕ} (c : ℝ) (P : PX m n) : (Fin m → Fin n → ℂ) → ℂ := fun u => evX P u * gs c u


open Classical in
def phiS {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (P : PX m n) : schwartzA θ m n :=
  if h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n then ⟨_, h⟩ else 0

def secF {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℝ) (Ψ : Mx D V.rank n → ℂ) (P : PX V.rank n) (g : G D n) : ℂ :=
  (ω g (phiS θ τ fr c Ψ P)).1 0

def thF {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℝ) (Ψ : Mx D V.rank n → ℂ) (P : PX V.rank n)
    (g : G D n) : ℂ :=
  thetaInt ω ν (phiS θ τ fr c Ψ P) g

def lamSet (ψ : AddChar (AF D.host.F) ℂ) : Set ((G D n → ℂ) → ℂ) :=
  {L | ∃ (nb : hermA D n → G D n) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n)) (β : HermE D n) (g : G D n), PositivityTheory.PfSWUS.CoefData (D := D) (n := n) nb lam 𝓖 ∧ β.1.det ≠ 0 ∧
    L = fun F => PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb F β g}

structure Cx (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ν : Measure (GA D V))
    (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n) : Prop where
  hψ : IsCharAF D.host.F ψ
  hχ : IsHeckeChar D χ
  hη : ResEta D χ V.rank
  hθ : IsInfFam θ
  hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕
  hω : IsWeilSch ψ χ θ V μ ω
  hH : IsHeight H
  hl : HasRealPar ψ θ l
  hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)
  hν : ν.IsHaarMeasure
  hr : PositivityTheory.PfSWUS.InRange V n
  hn : 1 ≤ n
  hfr : IsTauFrame V τ s ε fr
  hι : IsPlaceEmb θ τ ι
  hsig : GoodSig n (cnt ε true) (cnt ε false)

def IsLocOp {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (ι : GR n →* G D n) (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)) : Prop :=
  ∀ (y : GR n), ∀ Ψ ∈ awayA θ V n l s τ, ∀ P : PX V.rank n,
    (ω (ι y) (phiS θ τ fr (cLoc l τ) Ψ P)).1 = tens θ τ fr (L y (fP (cLoc l τ) P)) Ψ

def SFrame : Prop :=
  ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsCartanInv (gramAt D V τ) (s τ) → ∃ ε fr, IsTauFrame V τ s ε fr

def SEmb : Prop := ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau), IsInfFam θ → ∃ ι : GR n →* G D n, IsPlaceEmb θ τ ι

def SigOK : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), PositivityTheory.PfSWUS.InRange V n →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ τ, ∀ ε fr, IsTauFrame V τ s ε fr → GoodSig n (cnt ε true) (cnt ε false)

def SplitFock : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → IsTauFrame V τ s ε fr →
    ∀ Φ ∈ fockA θ V n l s, ∃ (k : ℕ) (Pi : Fin k → PX V.rank n) (Ψi : Fin k → Mx D V.rank n → ℂ),
      (∀ i, Ψi i ∈ awayA θ V n l s τ) ∧ Φ = ∑ i, tens θ τ fr (fP (cLoc l τ) (Pi i)) (Ψi i)

def TensMem : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → (∀ τ, l τ ≠ 0) →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → ∀ Ψ ∈ awayA θ V n l s τ, ∀ P : PX V.rank n,
      tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ schwartzA θ V.rank n ∧ tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s

def LocOpEx : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∃ L, IsLocOp ω l s τ fr ι L

def LocInst : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ (sL : PX V.rank n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n) (p q : ℕ) (e : ℤ),
      GoodSig n p q ∧ LocData ε (cLoc l τ) (tLoc l τ) p q e sL ρ ∧ (∀ P y, sL P y = L y (fP (cLoc l τ) P) 0) ∧
      ∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)

def LinSec : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∃ sec I : PX V.rank n →ₗ[ℂ] (G D n → ℂ), (∀ P, sec P = secF ω τ fr (cLoc l τ) Ψ P) ∧
      ∀ P, I P = thF ω ν τ fr (cLoc l τ) Ψ P

def GSplit : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ Ψ ∈ awayA θ V n l s τ, ∀ g : G D n, ∃ (x : G D n) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
      ∀ y' : GR n, (H (x * ι y') : ℝ) = r * hLoc y' ∧
        ∀ P, secF ω τ fr (cLoc l τ) Ψ P (x * ι y') = S * L y' (fP (cLoc l τ) P) 0

def GIauto : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    Continuous (thF ω ν τ fr (cLoc l τ) Ψ 1) ∧ ∀ γ ∈ GF D n, ∀ g, thF ω ν τ fr (cLoc l τ) Ψ 1 (γ * g) = thF ω ν τ fr (cLoc l τ) Ψ 1 g

def GIk : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) →
    ∀ Ψ ∈ awayA θ V n l s τ, ∀ P g (k : GR n), InK (mR k) →
      thF ω ν τ fr (cLoc l τ) Ψ P (g * ι k) = thF ω ν τ fr (cLoc l τ) Ψ (ρ k P) g

def GIinv : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∀ g a b P, thF ω ν τ fr (cLoc l τ) Ψ (hOp ε (cLoc l τ) a b P) g = 0

def GIdil : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∀ (g : G D n) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (F : GR n → ℂ → ℂ), IsOpen U ∧
      (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (Set.univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (F y) U ∧
        (∀ t : ℝ, F y t = thF ω ν τ fr (cLoc l τ) Ψ 1 (g * ι (y * a t))) ∧
        ∀ r : ℕ, iteratedDeriv r (F y) 0 = thF ω ν τ fr (cLoc l τ) Ψ ((dil (cLoc l τ) X ^ r) 1) (g * ι y)

def EisStrong : Prop :=
  ∀ (D : D7) (n : ℕ), 0 < n → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D χ → ResEta D χ b →
  ∀ H : G D n → ℝ≥0, IsHeight H → ∀ (s₁ : ℂ) (φ : G D n → ℂ), IsSection χ s₁ φ → ∀ s₀ : ℂ,
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (σ : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧
      (∀ g, DifferentiableOn ℂ (E · g) U) ∧ ContinuousOn (fun y : ℂ × G D n => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ γ ∈ GF D n, ∀ g, E z (γ * g) = E z g) ∧
      ∀ z : ℂ, σ < z.re → (∀ C : Set (G D n), IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (P D n) (GF D n) → ℝ, Summable u ∧
          ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (P D n) (GF D n) (fun x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x) g q‖ ≤ u q) ∧
        ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum (P D n) (GF D n) (fun x => ((H x : ℝ) : ℂ) ^ (z - s₁) * φ x) g

def FourierZeroN : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ nb lam 𝓖, PositivityTheory.PfSWUS.CoefData (D := D) (n := n) nb lam 𝓖 → ∀ f : G D n → ℂ, Continuous f →
    (∀ b : hermA D n, (∃ β : HermE D n, b.1 = β.1.map (incA D)) → ∀ g, f (nb b * g) = f g) →
    (∀ β g, PositivityTheory.PfSWUS.fc ψ lam 𝓖 nb f β g = 0) → f = 0

def DenseTau : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsInfFam θ → IsPlaceEmb θ τ ι →
    ∀ (y : GR n) (O : Set (GR n)), IsOpen O → y ∈ O → ∃ γ ∈ GF D n, ∃ y' ∈ O, ∃ x : G D n, γ = x * ι y' ∧
      ∀ y'' : GR n, x * ι y'' = ι y'' * x

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_cT (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) : (Formalism.UG.cT σ a).det = σ a.det := by
  unfold Formalism.UG.cT; rw [det_transpose, det_map]

theorem cT_cT (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) {m p : Type} (a : Matrix m p R) :
    Formalism.UG.cT σ (Formalism.UG.cT σ a) = a := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_inv (σ : R →+* R) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Formalism.UG.cT σ a⁻¹ = (Formalism.UG.cT σ a)⁻¹ := by
  unfold Formalism.UG.cT; rw [map_nonsing_inv σ a ha, transpose_nonsing_inv]

theorem uni_levi (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (a : Matrix (Fin n) (Fin n) R) (ha : IsUnit a.det) :
    Uni σ (GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹) := by
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact ha.map σ
  apply bf_injective
  unfold J2
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  rw [cT_inv σ _ hca, cT_cT σ hσ]
  have hc0 : Formalism.UG.cT σ (0 : Matrix (Fin n) (Fin n) R) = 0 := by ext; simp [Formalism.UG.cT]
  simp only [hc0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, mul_nonsing_inv _ hca, nonsing_inv_mul _ ha, neg_zero]

theorem eI_mul_eI (I : Finset (Fin n)) : (eI I : Matrix (Fin n) (Fin n) R) * eI I = eI I := by
  unfold eI; rw [diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> simp

theorem cT_eI (σ : R →+* R) (I : Finset (Fin n)) : Formalism.UG.cT σ (eI I : Matrix (Fin n) (Fin n) R) = eI I := by
  unfold Formalism.UG.cT; rw [eI_map, eI, diagonal_transpose]

theorem uni_wIm (σ : R →+* R) (I : Finset (Fin n)) : Uni σ (wIm I : Matrix (Fin (n + n)) (Fin (n + n)) R) := by
  apply bf_injective
  unfold J2 wIm
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, block_matrix_to_fromBlocks, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
  have h1 : Formalism.UG.cT σ (1 - eI I : Matrix (Fin n) (Fin n) R) = 1 - eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_sub _ (map_sub σ), Matrix.map_one _ (map_zero σ) (map_one σ), eI_map, transpose_sub,
      transpose_one, eI, diagonal_transpose]
  have h2 : Formalism.UG.cT σ (-eI I : Matrix (Fin n) (Fin n) R) = -eI I := by
    unfold Formalism.UG.cT; rw [Matrix.map_neg _ (map_neg σ), eI_map, transpose_neg, eI, diagonal_transpose]
  rw [h1, h2, cT_eI]
  have hE := eI_mul_eI (R := R) I
  congr 1 <;> simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero,
    zero_add, neg_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, hE] <;> abel_nf

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

def xyC (Z : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) (b : Bool) : PX m n :=
  ∑ c, C (Z a c) * MvPolynomial.X (c, i, b)

def vfC (c : ℝ) (Zh Za : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : PX m n :=
  ∑ a, ∑ i, (xyC Zh a i false * pderiv (a, i, false) P + xyC Za a i true * pderiv (a, i, true) P -
    C (c : ℂ) * (xyC Zh a i false * MvPolynomial.X (a, i, true) + xyC Za a i true * MvPolynomial.X (a, i, false)) * P)

theorem vfX_eq (c : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : vfX c Z P = vfC c Z (Z.map star) P := by
  have h1 : ∀ a (i : Fin n), xyP Z a i false = xyC Z a i false := fun a i => by simp [xyP, xyC]
  have h2 : ∀ a (i : Fin n), xyP Z a i true = xyC (Z.map star) a i true := fun a i => by simp [xyP, xyC, Matrix.map_apply]
  simp only [vfX, vfC, h1, h2]

theorem xyC_add_smul (Z Z' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    xyC (Z + r • Z') a i b = xyC Z a i b + C r * xyC Z' a i b := by
  simp only [xyC, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem vfC_lin (c : ℝ) (Zh Za Zh' Za' : Matrix (Fin m) (Fin m) ℂ) (r : ℂ) (P : PX m n) :
    vfC c Zh Za P + r • vfC c Zh' Za' P = vfC c (Zh + r • Zh') (Za + r • Za') P := by
  simp only [vfC, xyC_add_smul, smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem xyC_single (a b a' : Fin m) (r : ℂ) (i : Fin n) (β : Bool) :
    xyC (r • Matrix.single a b (1 : ℂ)) a' i β = if a' = a then C r * MvPolynomial.X (b, i, β) else 0 := by
  by_cases h : a' = a
  · subst h
    simp only [xyC, Matrix.smul_apply, Matrix.single_apply, true_and, smul_eq_mul, mul_ite, mul_one,
      mul_zero, if_true]
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [xyC, Matrix.single_apply, h, Ne.symm h]

theorem sgn_star (ε : Fin m → Bool) (a : Fin m) : star (sgn ε a) = sgn ε a := by
  unfold sgn; split_ifs <;> simp

theorem zRe_add_zIm (ε : Fin m → Bool) (a b : Fin m) :
    zRe ε a b + Complex.I • zIm ε a b = (1 : ℂ) • Matrix.single a b (1 : ℂ) := by
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem zRe_add_zIm_star (ε : Fin m → Bool) (a b : Fin m) :
    (zRe ε a b).map star + Complex.I • (zIm ε a b).map star = (-(sgn ε a * sgn ε b)) • Matrix.single b a (1 : ℂ) := by
  have hs : (starRingEnd ℂ) (sgn ε a) = sgn ε a := sgn_star ε a
  have ht : (starRingEnd ℂ) (sgn ε b) = sgn ε b := sgn_star ε b
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  ext i j
  simp only [zRe, zIm, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply,
    smul_eq_mul, Matrix.neg_apply, Matrix.single_apply, Complex.star_def]
  split_ifs <;> simp [map_add (f := _), map_mul, map_neg, map_sub, hs, ht, h2, Complex.conj_I] <;> ring_nf <;>
    simp [Complex.I_sq] <;> ring

theorem hOp_eq (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (P : PX m n) :
    hOp ε c a b P = vfX c (zRe ε a b) P + Complex.I • vfX c (zIm ε a b) P := by
  rw [vfX_eq, vfX_eq, vfC_lin, zRe_add_zIm, zRe_add_zIm_star]
  unfold vfC hOp
  simp only [xyC_single]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, add_mul, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [map_neg, map_one, map_mul, map_sub]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH
end
end
