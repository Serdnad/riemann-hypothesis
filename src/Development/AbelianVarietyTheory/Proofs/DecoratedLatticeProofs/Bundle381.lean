module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle352
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle351
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QVal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def places {r : ℕ} (Q : Fin r → QStep S) : GlobalTheory.FinPl.Pl D → Prop := fun v => ∃ i, (Q i).q.v = v

def integrand {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  GlobalTheory.PosOne.comb (conv (List.ofFn fun i => (Q i).e₀.mapDomain (Q i).gl₀)) fun a =>
    S.val c₁ c₂ (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
      φ f (g * a) (h₁ * x) (h₂ * y)

def value {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : ℂ :=
  (∏ i, (Q i).volJ) * ∑ γ : ∀ i, (Q i).A₁, ∑ β : ∀ i, (Q i).A₂, (∏ i, (Q i).w₁ (γ i) * (Q i).w₂ (β i)) *
    S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ (γ i))) (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ (γ i) (β i))) f₁ f₂ φ
      (trc (conv (List.ofFn fun i => ((Q i).e₂ (β i)).mapDomain (Q i).gl₂)) f) g h₁ h₂

def innerVal {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  (Q 0).volJ * ∑ γ : (Q 0).A₁, ∑ β : (Q 0).A₂, ((Q 0).w₁ γ * (Q 0).w₂ β) *
    integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ x y

def Hyps {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : Prop :=
  (∀ i, (Q i).Away c₁ ∧ (Q i).Away c₂) ∧ IsThetaFunO ψ _ _ f₁ ∧ IsThetaFunO ψ _ _ f₂ ∧ (∀ i, (Q i).Vac f₁ f₂) ∧
    IsContAut S.B.A φ ∧ IsContAut S.B'.V f ∧ (∀ i, (Q i).Typed f) ∧ g ∈ GlobalTheory.FinPl.grpOff S.B.V (places Q) ∧
    h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (places Q) ∧ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (places Q)

def Norm {r : ℕ} (Q : Fin r → QStep S) (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q)))
    (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q)))) (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))) : Prop :=
  μ₁.IsHaarMeasure ∧ ρ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ ρ₂.IsHaarMeasure ∧
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 ∧ ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 ∧
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 ∧ ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1

def LocNorm (Q₀ : QStep S) (m₁ : Measure (GL (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1)) Q₀.k)) (s₁ : Measure (RFJ Q₀.k Q₀.n₁ (Q₀.c + 1 + 1) (σ + 1)))
    (m₂ : Measure (GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)) (s₂ : Measure (R Q₀.k Q₀.n₂ (Q₀.c + 1) (σ + 1))) : Prop :=
  m₁.IsHaarMeasure ∧ m₁ (KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))) = 1 ∧ s₁.IsHaarMeasure ∧
    s₁ {x | x.1 ∈ KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))} = 1 ∧ m₂.IsHaarMeasure ∧ m₂ (KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))) = 1 ∧
    s₂.IsHaarMeasure ∧ s₂ {x | x.1 ∈ KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))} = 1

def levJ {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.J.W (places Q)) :=
  (⨆ i, (Q i).L₁.J.map (Q i).gl₁).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))

def levB {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) :=
  (⨆ i, (Q i).L₂.J.map (Q i).gl₂).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q))

end GlobalTheory.QVal

namespace GlobalTheory.QVal

def ValQr (D : D7) (r : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) →
  ∀ (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))))
    (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ →
  ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ →
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)

theorem valQ_of_valQr (D : D7) (h : ∀ r, ValQr D r) : ValQ D := by
  intro ψ hψ σ S r Q hinj P hP μ₁ ρ₁ μ₂ ρ₂ a1 a2 a3 a4 a5 a6 a7 a8 c₁ c₂ hc f₁ f₂ t1 t2 hv φ f hφ hf ht g hg h₁ hh₁ h₂ hh₂
  have e : P = places Q := funext fun v => propext (hP v)
  subst e
  exact h r ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ c₁ c₂ f₁ f₂ φ f g h₁ h₂
    ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩

end GlobalTheory.QVal

namespace GlobalTheory.QVal
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def pint {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V)
    (x : GlobalTheory.FinPl.grpAt S.J.W (places fun i => Q i.succ) × GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)
    (y : GlobalTheory.FinPl.grpAt S.B'.V (places fun i => Q i.succ) × GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) : ℂ :=
  integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)
end GlobalTheory.QVal

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrTheta

theorem continuous_linkKappa {D : D7} {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_restrict_of_bdd {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : μ s = 1) (f : X → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (μ.restrict s) := by
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ, hs]; exact ENNReal.one_lt_top⟩
  exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hC x)

theorem contr_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → (∀ v, IsThetaFunO ψ B.A J.W₀ fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) ∧ ∀ p, (IsThetaFunO ψ J.W₀ B'.A fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) ∧ ∀ v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) * oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' _ _ hoa _ _ _ Ξ₁ Ξ₂ hΞ₁ hΞ₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  haveI hbor : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  have hκ : Continuous (l.κ J.W₀) := continuous_linkKappa l J.W₀
  have hκm : Measurable (l.κ J.W₀) := hκ.measurable
  have hvol : vL.μ vL.𝓕 = 1 := vL.covol.2.2
  have ha : ∀ v, Integrable (fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w))) (vL.μ.restrict vL.𝓕) := by
    intro v
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd Ξ₂ hΞ₂
    exact integrable_restrict_of_bdd _ _ hvol _ (hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp
      (Continuous.prodMk continuous_const continuous_id))) C (fun w => hC _)
  have hG : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2)))
      (B.o.resS J.W₀ x).1) := fun p =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha 0) p).1
  have hb : ∀ p, Integrable (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0)
      (vL.μ.restrict vL.𝓕) := by
    intro p
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hstd _ (hG p)
    have heq : (fun w => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0) = fun w =>
        (fun x => oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, (B.o.resS J.W₀ x).2))) (B.o.resS J.W₀ x).1)
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) := by
      funext w; simp only [AddEquiv.apply_symm_apply]
    rw [heq]
    exact integrable_restrict_of_bdd _ _ hvol _ ((hG p).cont.comp ((OrthDec.continuous_resS_symm _ _).comp
      (Continuous.prodMk continuous_const hκ))) C (fun w => hC _)
  have hcom : ∀ p v, oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 = ∫ w in vL.𝓕, Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) *
      oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 ∂vL.μ := fun p v =>
    (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v) p).2 0
  refine ⟨fun v => ?_, fun p => ⟨?_, hcom p⟩⟩
  · exact GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hstd B.V₀ B.A B.L J.W₀ B.o Ξ₁ hΞ₁ _ (vL.μ.restrict vL.𝓕) (l.κ J.W₀) _ hκm (ha v)
  · have h := GlobalTheory.T.isThetaFun_superposition_target_orthSummand D ψ hstd B'.V₀ B'.A B'.L J.W₀ B'.o Ξ₂ hΞ₂ _ (vL.μ.restrict vL.𝓕) id _ measurable_id (hb p)
    have heq : (fun v => oma p (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) = fun v =>
        ∫ w, oma p (fun u => Ξ₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w))) 0 * Ξ₂ ((B'.o.resT J.W₀).symm (v, id w))
          ∂(vL.μ.restrict vL.𝓕) := by
      funext v; rw [hcom]; congr 1; funext w; rw [mul_comm]; rfl
    rw [heq]; exact h

end GlobalTheory.ContrTheta

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevPrimeData

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_fin_int (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem splitPlace_valuation_cmImaginaryGenerator_eq_one (p : SplitPt D k) (hp : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  obtain ⟨h1, h2⟩ := hp.1 _ (e_mem_intAt p)
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h3 := pr_mem_of_fin_int p h1.2
  have h4 := pr_mem_of_fin_int p h2.2
  rw [RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff] at h3 h4
  have h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
      RingHom.map_one, map_one]
  refine le_antisymm h3 ?_
  rw [← h5]
  exact mul_le_of_le_one_right' h4

theorem splitPlace_valuation_neg_cmGenerator_pow_eq_one (p : SplitPt D k) (hp : p.UnitAA) (n : ℕ) :
    valuation k (p.pr (incA D (-D.host.xi0 ^ n))) = 1 ∧ valuation k (p.pr (incA D (star (-D.host.xi0 ^ n)))) = 1 := by
  have h := splitPlace_valuation_cmImaginaryGenerator_eq_one p hp
  refine ⟨?_, ?_⟩
  · rw [RingHom.map_neg, RingHom.map_neg, RingHom.map_pow, RingHom.map_pow, Valuation.map_neg, map_pow, h, one_pow]
  · rw [star_neg, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, RingHom.map_neg, RingHom.map_pow, RingHom.map_pow,
      RingHom.map_neg, RingHom.map_neg, Valuation.map_neg, map_pow, Valuation.map_neg, h, one_pow]

end GlobalTheory.LevPrimeData
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.MiStar.normLast_valuation : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (S A L : HSp D) (o : OrthDec S A L), 0 < S.rank → S.gram = 1 → ∀ (ζ : Fin L.rank → D.host.E) (π : D.host.E), (∀ r : Fin S.rank, vecB o ζ r = if r.1 + 1 = S.rank then π else 0) → valuation k (p.pr (incA D π)) = valuation k ((q.1 : 𝒪[k]) : k) → valuation k (p.pr (incA D (star π))) = 1 → valuation k (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ))) = valuation k ((q.1 : 𝒪[k]) : k) := by
  intro D k _ _ _ _ p q S A L o hpos hS ζ π hv h1 h2
  have key : star ζ ⬝ᵥ L.gram *ᵥ ζ = star π * π := by
    have hB := o.isoB
    rw [hS, Matrix.mul_one] at hB
    rw [← hB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hfun : o.iB *ᵥ ζ = fun r : Fin S.rank => if r.1 + 1 = S.rank then π else 0 := by
      funext r; exact hv r
    rw [hfun]
    let r0 : Fin S.rank := ⟨S.rank - 1, by omega⟩
    have hr : ∀ r : Fin S.rank, (r.1 + 1 = S.rank) ↔ r = r0 := by
      intro r; constructor
      · intro h; ext; simp [r0]; omega
      · intro h; subst h; simp [r0]; omega
    simp only [dotProduct, Pi.star_apply, hr]
    simp [apply_ite star]
  rw [key, map_mul, map_mul, map_mul, h2, h1, one_mul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl.CoreMat

theorem mt_emb_mulVec_ratV_vecB {D : D7} {ρ : ℕ} (B : BesLev D ρ) (κ : GA D B.A) :
    Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1)) *ᵥ ratV (vecB B.o B.ζ) =
      ratV (vecB B.o B.ζ) := by
  have hv : ratV (vecB B.o B.ζ) = B.o.jB *ᵥ ratV B.ζ :=
    funext fun i => RingHom.map_mulVec (incA D) B.o.iB B.ζ i
  have hB : Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1)) ⬝ B.o.jB = B.o.jB := by
    rw [B.o.emb_jB]
    have h1 : Formalism.L2.Theta.mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.mul_one]
  rw [hv, Matrix.mulVec_mulVec, hB]

theorem coreMat : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n]
    [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (β : GlobalTheory.FinPl.Frame p B.A n)
    (β₀ : GlobalTheory.FinPl.Frame p B.V₀ (n ⊕ Fin 1)),
    GlobalTheory.FinPl.IsSumFrame B.o B.ζ β β₀ → ∀ (κ : GA D B.A) (g : GL n k),
    (Formalism.L2.Theta.mt B.A κ).map p.pr = β.b * g.val * β.b' →
    (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr =
      β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by
  intro D k _ _ _ _ p n _ _ ρ B β β₀ hS κ g hg
  have hA : Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1)) ⬝ B.o.jA =
      B.o.jA ⬝ Formalism.L2.Theta.mt B.A κ := B.o.emb_jA κ 1
  have hv := mt_emb_mulVec_ratV_vecB B κ
  have key : (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr * β₀.b =
      β₀.b * (GlobalTheory.RootEx.embX 1 g).val := by
    rw [hS]
    have hX : ((GlobalTheory.RootEx.embX 1 g).val : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
    rw [hX]
    rw [Matrix.mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, Matrix.mul_zero, zero_add,
      Matrix.mul_one]
    congr 1
    · rw [← Matrix.mul_assoc, ← Matrix.map_mul, hA, Matrix.map_mul, Matrix.mul_assoc, hg, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
    · ext i j
      have := congrFun hv i

      simp only [Matrix.mul_apply, replicateCol_apply, Matrix.map_apply, ← map_mul, ← map_sum]
      rw [← this]
      rfl
  calc (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr
      = (Formalism.L2.Theta.mt B.V₀ (GlobalTheory.MixModel.OrthDec.emb B.o (κ, 1))).map p.pr * β₀.b * β₀.b' := by
        rw [Matrix.mul_assoc, β₀.bb', Matrix.mul_one]
    _ = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by rw [key]

end GlobalTheory.FinPl.CoreMat

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDatum

theorem vac_true_mono {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (P : GlobalTheory.FinPl.Pl D → Prop) {F : WO S T → ℂ} (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) F) :
    GlobalTheory.FinPl.Vac ψ S T LS LT P F := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

end GlobalTheory.MidDatum
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.splitPlaceProjection_eq_of_primeComponent_eq : ∀ {D : Formalism.BasicNotions.D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (z : Formalism.L2.Theta.AE D) (x : D.host.E), GlobalTheory.Mem.Col2.adAt D.host.F PP (Formalism.IndefR.Datum.toEAf D z) = algebraMap D.host.E (PP.adicCompletion D.host.E) x → q.pr z = q.pr (Formalism.L2.Theta.incA D x) := by
  first | exact @GlobalTheory.SplitProj.pr_eq_of_adAt | exact GlobalTheory.SplitProj.pr_eq_of_adAt | (intros; apply GlobalTheory.SplitProj.pr_eq_of_adAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamPlaced

section Prim

open GlobalTheory.FinPl

theorem incA_mul_mem_intAt {D : D7} (v : GlobalTheory.FinPl.Pl D) (c : D.host.E) (N : ℤ) (hint : IsIntegral ℤ (N • c))
    (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) {a : AE D} (ha : a ∈ intAt D (· = v)) : incA D c * a ∈ intAt D (· = v) := by
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, AeUnit.inv_smul_singleV_mem v N hv, ⟨N • c, hint⟩, ?_⟩
  exact AeUnit.tmul_eq_inv_smul_tmul N hNF _ c

theorem prim_std {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : ∀ x, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i)) (v : GlobalTheory.FinPl.Pl D)
    (z : Fin S.rank → D.host.E) (hz : ∀ i, IsIntegral ℤ (z i)) (i₀ : Fin S.rank) (π' : D.host.E) (hπ' : IsIntegral ℤ π') (N : ℤ)
    (hπ : z i₀ * π' = (N : D.host.E)) (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) (a : AE D) (ha : a ∈ idAt D (· = v)) :
    a • ratV z ∈ GlobalTheory.FinPl.latV S L (· = v) ↔ a ∈ intAt D (· = v) := by
  have hL' : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i := fun x => by
    rw [hL x]
    exact ⟨fun h i => ⟨⟨x i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNE : (N : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hN
  have hz0 : z i₀ ≠ 0 := fun h => hNE (by rw [← hπ, h, zero_mul])
  have h1 : ((1 : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rw [Int.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  rw [GlobalTheory.FinPl.Model.mem_latV_std S L hL' v]
  constructor
  · intro h
    have hi : a * incA D (z i₀) ∈ intAt D (· = v) := h i₀
    have hint : IsIntegral ℤ (N • (z i₀)⁻¹) := by
      have : N • (z i₀)⁻¹ = π' := by
        rw [zsmul_eq_mul, ← hπ, mul_comm (z i₀), mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      rw [this]; exact hπ'
    have h2 := incA_mul_mem_intAt v (z i₀)⁻¹ N hint hv hi
    rwa [mul_comm a, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul] at h2
  · intro h i
    show a * incA D (z i) ∈ intAt D (· = v)
    rw [mul_comm]
    exact incA_mul_mem_intAt v (z i) 1 (by rw [one_smul]; exact hz i) h1 h

end Prim

end GlobalTheory.FamPlaced
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.latticeCompletion_eq_of_local_agreement : ∀ {D : D7} (S : HSp D) (L N : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop), Submodule.IsLattice D.host.E L → Submodule.IsLattice D.host.E N → (∀ w, P w → GlobalTheory.FinPl.latV S L (· = w) = GlobalTheory.FinPl.latV S N (· = w)) → GlobalTheory.FinPl.latV S L P = GlobalTheory.FinPl.latV S N P := by
  intro D S L N P hL hN hP
  ext y
  rw [GlobalTheory.FinPlLoc.part_lat P S L y hL,
    GlobalTheory.FinPlLoc.part_lat P S N y hN]
  constructor <;> rintro ⟨hs, hl⟩ <;> refine ⟨hs, fun v hv e he => ?_⟩
  · rw [← hP v hv]
    exact hl v hv e he
  · rw [hP v hv]
    exact hl v hv e he
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_split_datum_completed_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k),
      IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
        (extFun α β Ψ) := by
  first | exact @GlobalTheory.FinPl.SBHalfAt.isSBHalf_extFun_latO | exact GlobalTheory.FinPl.SBHalfAt.isSBHalf_extFun_latO | (intros; apply GlobalTheory.FinPl.SBHalfAt.isSBHalf_extFun_latO <;> assumption)
end

section

alias GlobalTheory.T.threeOrbits_gluedCore_atPlace := GlobalTheory.FinPl.orbitGlued
end
