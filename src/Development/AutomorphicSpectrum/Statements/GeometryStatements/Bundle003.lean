module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle001
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

def KeyOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R K : Type} [CommRing R] [Field K]
    (f : R →+* K) (t : SAB H (Sp R)) (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)) : Prop :=
  ∃ (φ : x.P.A.left ⟶ t.G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec t.G) (w : LB.Iso x.P.L (t.PP.L.pull φ)),
    IsGrpPullback x.P.A t.G (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he t.PP.L t.PP.rig) ∧
    (∀ (j : (t.PP.L.pull φ).ι) (i : x.P.L.ι) (h : (t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ t.PP.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (th.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap f) ≫ (v i).left

def KeyBadSt : Prop :=
  ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ →
    GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (t : SAB H (Sp R))
      (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)),
      KeyOver (algebraMap R K) t th x v → IsLieBasis v →
      (∀ (d : R) (th' : t.PP.L.Sec), (∀ i, th.f i = constFn t.G.hom _ d * th'.f i) → IsUnit d) →
      (κ K x : K) ∈ Set.range (algebraMap R K)

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

def PropFTop : Prop :=
  PtsIntegrableStatement → MetricLocalStatement → DegreeStatement →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
      (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (rd Lval : ℝ),
      IsIntersectionSystem II → T.Conv II → T.Proportional → T.Prop6 II frob → 1 ≤ rd → (∀ p ∈ T.bad, p.Prime) →
      (∀ c τ, ∃ R : RootFlat (T.M 2 c) τ, NearRecord N T.bad rd Lval R.ht) → T.PropF II 4 rd Lval

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

def AgreementPos : Prop :=
  Inputs → ∀ (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (abelian₂ : ℝ), 0 < S.t₀ → ∃ C₃ s₀ : ℝ, 0 < s₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P),
      (∀ w, Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w))) ∧
      ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, ∑ a, |c a| ≤ abelian₂ →
        |eval c (Re.FT II (Real.exp (-(s ^ 2)⁻¹))) - eval c (Re.PB II)| ≤ C₃ * s

end GlobalTheory.CompanionTheory.Ar.PB
end
end
