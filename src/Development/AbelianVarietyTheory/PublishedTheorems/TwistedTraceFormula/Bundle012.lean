module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
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

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open scoped ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chamber

def ExpFamilyIntegral : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ X, IsOrth 𝔞 X → IsGMFam 𝔞 (expFam X) ∧ ∀ Q ∈ parF 𝔞 ∅,
    (Integrable (fun H : aMQ 𝔞 Q => gamM 𝔞 Q X H) ∧
      ∀ l, cM 𝔞 Q (expFam X) l = eL l (X Q) * ∫ H : aMQ 𝔞 Q, eL l H * gamM 𝔞 Q X H) ∧
    (Integrable (fun H : aMQ (aP Q) ∅ => gamP Q ∅ (X Q) H) ∧
      ∀ l, cP Q ∅ (expFam X) l = ∫ H : aMQ (aP Q) ∅, eL l H * gamP Q ∅ (X Q) H)

def FamilySmooth : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c, IsGMFam 𝔞 c → ∀ Q ∈ parF 𝔞 ∅,
    (ContDiff ℝ ∞ (cM 𝔞 Q c) ∧ Set.EqOn (cM 𝔞 Q c) (sumM 𝔞 Q c) (generic k)) ∧
    ∀ R ⊆ Q, ContDiff ℝ ∞ (cP Q R c) ∧ Set.EqOn (cP Q R c) (sumP Q R c) (generic k)

def FamilyProduct : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c d, IsGMFam 𝔞 c → IsGMFam 𝔞 d → ∀ R ∈ parF 𝔞 ∅, ∀ l,
    cM 𝔞 R (c * d) l = ∑ Q ∈ parF 𝔞 R, cM 𝔞 Q c l * cP Q R d l

end GlobalTheory.Chamber

namespace GlobalTheory.TruncKer

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V)) (μ : Measure (GA D V))

def OrthogonalY : Prop :=
  ∀ x T, IsOrth ⊤ (Yfam Φ K x T) ∧
    ∀ π ε w, Φ.IsWeylRep D.sp.cm π ε w → Yfam Φ K x T (weylPar π ε) = Ys Φ K π ε w x T

def KernelConvergence : Prop :=
  ∀ f ∈ CcGA V, ∃ c : ℝ, ∀ T, Regular c T →
    (∀ 𝔬, IsSSClass 𝔬 → Integrable (descend (GQ V) (kT Φ K 𝔬 f T)) (autMeasure V μ)) ∧
    {𝔬 | IsSSClass 𝔬 ∧ ∫ q, ‖descend (GQ V) (kT Φ K 𝔬 f T) q‖ ∂autMeasure V μ ≠ 0}.Finite

def WeightedOrbital : Prop :=
  ∀ f ∈ CcGA V, ∀ γ : GF V, IsRegSS γ.1.1 → ∀ P, IsMinLevi Φ γ P →
    ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], ∃ c : ℝ, ∀ T, Regular c T →
      Integrable (descend (cent (rat V γ)) fun x => (weight Φ K (aP P) T x : ℂ) * conjFn (rat V γ) f x)
        (quotMeas (cent (rat V γ)) dt μ) ∧
      ∫ q, descend (GQ V) (kT Φ K {δ | IsConj γ δ} f T) q ∂autMeasure V μ =
        volA Φ K (aP P) (cent (rat V γ)) dt *
          wOrbInt (cent (rat V γ)) dt μ (rat V γ) (fun x => weight Φ K (aP P) T x) f

end GlobalTheory.TruncKer

namespace GlobalTheory.Published

def LabesseWaldspurger : Prop :=
  (ExpFamilyIntegral ∧ FamilySmooth ∧ FamilyProduct) ∧
  ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    OrthogonalY Φ (levelAll D.sp.cm.sig V.gram L a) ∧
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure],
      KernelConvergence Φ (levelAll D.sp.cm.sig V.gram L a) μ ∧ WeightedOrbital Φ (levelAll D.sp.cm.sig V.gram L a) μ

end GlobalTheory.Published

end
end

section

noncomputable section

open scoped ComplexConjugate
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D} (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (m : Measure (GA D A))

def thetaLift (Φ : WO A B → ℂ) (f : GA D A → ℂ) : GA D B → ℂ :=
  fun h => petersson A m (fun g => thetaKO ω g h Φ) f

def LiftConv (Φ : WO A B → ℂ) (f : GA D A → ℂ) : Prop :=
  ∀ h, Integrable (descend (GQ A) fun g => thetaKO ω g h Φ * conj (f g)) (autMeasure A m)

def LowerLiftsZero (ψ : AddChar (AF D.host.F) ℂ) (B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (π : Submodule ℂ (GA D A → ℂ)) : Prop :=
  ∀ (i : ℕ) (B' : HSp D), 1 ≤ i → IsWittLower B B' i → B'.SigOK →
    ∀ ω' : GA D A × GA D B' →* Module.End ℂ (WO A B' → ℂ), IsWeilDatumO ψ A B' χA χB ω' →
      ∀ Φ, IsThetaFunO ψ A B' Φ → ∀ f ∈ π, LiftConv ω' m Φ f → thetaLift ω' m Φ f = 0

end GlobalTheory.RallisIP

namespace GlobalTheory.Published

open GlobalTheory.RallisIP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause)

def RallisInnerProductConvergent : Prop :=
  ∀ (D : D7) (A B : HSp D), A.rank < B.rank → B.rank ≤ 2 * A.rank →
    (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle)
    (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
    (ωd : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ A B χA χB ω → IsWeilDatumO ψ (dblSp A) B 1 χB ωd → ThetaClause ψ A B χB ω ωd →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ (θ : InfF D) (C : CptF A), IsInfFam θ → A.SigOK → IsCartanFrame A C →
  ∀ (m : Measure (GA D A)) [m.IsHaarMeasure] [m.IsMulRightInvariant] (mH : Measure (GA D B)), mH.IsHaarMeasure →
  ∀ U : Submodule ℂ (DividedPowerChartLift A m), IsIrredSubrep (RG A m) U → U ≤ L2cusp A m →
    LowerLiftsZero m ψ B χA χB (AutMult.formsIn A m (A0 θ A C) U) →
  ∀ Φ₁ Φ₂, IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → IsKFinVec ωd (Khat A a) (delta A B Φ₁ Φ₂) →
  ∀ f₁ ∈ AutMult.formsIn A m (A0 θ A C) U, ∀ f₂ ∈ AutMult.formsIn A m (A0 θ A C) U,
    (LiftConv ω m Φ₁ f₁ ∧ MemL2Quotient (GQ B) mH (thetaLift ω m Φ₁ f₁)) ∧
    (LiftConv ω m Φ₂ f₂ ∧ MemL2Quotient (GQ B) mH (thetaLift ω m Φ₂ f₂)) ∧
    ZetaValueAt A χB⁻¹ m (flat A a (swSec A B ωd ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B)) f₁ f₂ (sZero A B)
      ((((autMeasure B mH).real Set.univ : ℝ) : ℂ)⁻¹ * petersson B mH (thetaLift ω m Φ₁ f₁) (thetaLift ω m Φ₂ f₂))

end GlobalTheory.Published

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D}

theorem wittIdx_eq_wittIndex (B : HSp D) : Formalism.MainNotions.SchurIrreducible.wittIdx B = wittIndex B := by
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx wittIndex
  congr 1
  ext k
  refine exists_congr fun W => and_comm.trans (and_congr_left' ⟨fun h y hy => mem_perp.2 fun x hx => ?_, fun h x hx y hy => ?_⟩)
  · exact h x hx y hy
  · exact mem_perp.1 (h hy) x hx

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)} {Φ : WO A B → ℂ} {f : GA D A → ℂ}

end GlobalTheory.RallisIP

end
end
