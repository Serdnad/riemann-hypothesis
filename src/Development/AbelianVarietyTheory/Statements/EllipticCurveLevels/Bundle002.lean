module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DeRhamOfPlainTorus

def R1 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin n) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), π.IsLocComp w σ → PlainTor (algNorm σ) →
      (∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w),
        (wdOf h hl ι r).mono0 ∧ ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → wdOf h hl ι r = rc (algNorm σ)) ∧
      (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ClauseAt .dR π ι r w ∧
        ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
        ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
          (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw),
          IsPstAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧ (wdAt P ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)).mono0 ∧
          ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc →
            ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)).charPol g = (rc (algNorm σ)).charPol g)

def IsQg {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ (g : ℕ) (hg : Fact g.Prime), ∃ i : (@Padic g hg) ≃+* w.adicCompletion E, Continuous i

end GlobalTheory.DeRhamOfPlainTorus

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace GlobalTheory.RoadW

def RowStarCore : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∃ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Weak π ι r ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), (CG.mk π).HasSat w B →
        GlobalTheory.RoadU.SphAt .unr π ι r w B ∧ GlobalTheory.RoadU.SphAt .dR π ι r w B ∧ GlobalTheory.RoadU.SphAt .crys π ι r w B ∧
          GlobalTheory.RoadU.SphAt .phi π ι r w B

end GlobalTheory.RoadW

end
end
