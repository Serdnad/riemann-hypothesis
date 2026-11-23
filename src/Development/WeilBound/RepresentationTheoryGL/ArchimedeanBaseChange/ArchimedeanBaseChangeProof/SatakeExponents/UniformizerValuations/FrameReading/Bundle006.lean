module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ConjFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ),
  (∀ (w u : Pl E) (G : H E a b → ℂ), IsSplitAt w → ConjPl w u → G ∈ fixed (pairRtT a b w) (K2 a b w) →
    G ∈ fixed (pairRt a b u) (K2 a b u)) ∧
  ∀ S : Set (Pl E), IsSection S → (∀ u, IsSplitAt u → u ∈ S ∨ ∃ w ∈ S, IsSplitAt w ∧ ConjPl w u) ∧
    ∀ X : Finset (Pl E), {u | ∃ w ∈ X, ConjPl w u}.Finite

def USat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E)
  (σ : SmIrr (UL n w)), IsSplitAt w → IsCompU π w σ → fixed σ.ρ (KL n w) ≠ ⊥ →
  ∃ B, SatAtU π w B ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ k ≤ n,
    twTr σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id = satEig (qV E w) n B k

def CtHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
  (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E) (k : ℕ), IsSplitAt w → IsUnifV E w ϖ →
  (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → ν u = 1) →
  HasCompactSupport (ctT h w ν ϖ k) ∧ (∀ y ∈ K2 a b w, ∀ g, ctT h w ν ϖ k (g * y) = ctT h w ν ϖ k g) ∧ ν ((-1) ^ (a * b)) = 1

def USatOf : Prop := SplitDict → USat

end PositivityTheory.Rg.BcB.F.FG

end
end

section

noncomputable section

namespace PositivityTheory.Rg.BcB.F.Rd

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

def blockEvaluation (s : ι) : Prod' H d →⋆ₐ[ℂ] (H s →L[ℂ] H s) where
  toFun a := a.1 s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem projAdjoin (gen : Γ → Prod' H d) (s : ι) (X : H s →L[ℂ] H s) :
    StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X}) =
      StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {X}) := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    rintro y (⟨a, rfl⟩ | hy)
    · have hmem : blockEvaluation (H := H) (d := d) s (a : Prod' H d) ∈
          StarSubalgebra.map (blockEvaluation (H := H) (d := d) s) (StarAlgebra.adjoin ℂ (Set.range gen)) :=
        StarSubalgebra.mem_map.2 ⟨a, a.2, rfl⟩
      rw [StarAlgHom.map_adjoin] at hmem
      have hle : StarAlgebra.adjoin ℂ (⇑(blockEvaluation (H := H) (d := d) s) '' Set.range gen) ≤
          StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {X}) := by
        apply StarAlgebra.adjoin_mono
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        exact Or.inl ⟨x, rfl⟩
      exact hle hmem
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr hy)
  · apply StarAlgebra.adjoin_mono
    rintro y (⟨x, rfl⟩ | hy)
    · exact Or.inl ⟨⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩, rfl⟩
    · exact Or.inr hy

end PositivityTheory.Rg.BcB.F.Rd

end
end
