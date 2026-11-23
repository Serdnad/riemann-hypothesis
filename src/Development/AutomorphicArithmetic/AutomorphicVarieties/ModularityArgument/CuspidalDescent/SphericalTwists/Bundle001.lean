module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Z.Win
open UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {σ : SmIrr (GL (Fin n) (w.adicCompletion F))}

theorem lgAway' (H : LocGlobT ι r w σ) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h) (hrc : IsRecT h rc) : WDT ι r (rc (algNorm σ)) := (H A h rc hrc).1 hw

end UpperTheory.V.Z.Desc.W
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.W

def TypeGd : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecT h rc → ∀ χ : Fin n → _root_.Formalism.ConjugateSelfDual.G E Ω →* ℂˣ,
      Hi.IsTypeWD h (fun i => (χ i).comp (Ine (F := E) A).subtype) (rc (algNorm σ)) →
      Good (IrrGL.of σ.ρ σ.smooth σ.irred) ∧ Gd (rc (algNorm σ))

def TwAway : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ)
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (R : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Qbar l)), Continuous R →
    ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ) (μ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → Continuous μ →
    IsLAdicOf art ι κ m μ → ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal →
    ∀ τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K)), Good (IrrGL.of τ.ρ τ.smooth τ.irred) →
    Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) →
    ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc →
      IsWDOf ι R (rc (algNorm τ)) → IsWDOf ι (tw R μ) (rc (algNorm τ'))

def OrdTw : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ)
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (art : Ideles K →* Gab K Ω) (κ : HChar K) (μ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (Qbar l)ˣ),
    IsGlobalArtin art → Continuous μ → IsLAdicOf art ι κ 0 μ → ∀ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω)
    (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : Weil h →* (w.adicCompletion K)ˣ), IsLocalArtin h a →
    ∀ (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (ω : Fin n → (w.adicCompletion K)ˣ →* ℂˣ) (hh : Fin n → (K →+* Qbar l) → ℤ)
      (ψ : Fin n → _root_.ReciprocityTheory.Gal.Dec (F := K) A →* (Qbar l)ˣ), Nonempty (τ.ρ.Equiv (Hi.PS ω)) → (∀ i, Hi.OrdChar ι a (ω i) (hh i) (ψ i)) →
      Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) →
      ∃ ω' : Fin n → (w.adicCompletion K)ˣ →* ℂˣ, Nonempty (τ'.ρ.Equiv (Hi.PS ω')) ∧
        ∀ i, Hi.OrdChar ι a (ω' i) (hh i) (ψ i * μ.comp (_root_.ReciprocityTheory.Gal.Dec (F := K) A).subtype)

end UpperTheory.V.Z.Desc.W
end
end
