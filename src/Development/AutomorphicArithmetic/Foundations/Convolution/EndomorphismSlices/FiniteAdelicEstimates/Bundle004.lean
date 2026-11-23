module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem locAlg : LocAlg := by
  intro E _ _ _ a b Z L w
  have hK2 : K2 a b w = (KGL w (n := a)).prod (KGL w (n := b)) := rfl
  have hop : IsOpen (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (L.open₁ w).prod (L.open₂ w)
  have hle : (L.L₁ w).prod (L.L₂ w) ≤ K2 a b w := Subgroup.prod_mono (L.le₁ w) (L.le₂ w)
  have hKop : IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [hK2, Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  have hln : L.ln w = idem ((L.L₁ w).prod (L.L₂ w)) := rfl
  have hKi : idem (K2 a b w) = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
    funext y
    simp only [idem, Subgroup.relIndex_self, Nat.cast_one]
    rfl
  obtain ⟨h1, h2, h3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hop hle
  obtain ⟨-, -, k3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hKop le_rfl
  refine ⟨hln ▸ h1, hln ▸ h2, fun hw => ?_, fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨e₁, e₂⟩ := L.off w hw
    rw [hln, e₁, e₂, ← hK2, hKi]
  · rw [hln]
    exact ⟨(h3 f hf).2.1, (h3 f hf).1⟩
  · rw [← hKi]
    exact ⟨(k3 f hf).2.1, (k3 f hf).1, (k3 f hf).2.2⟩

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem zVal_ite' {m : ℕ} (c : Prop) [Decidable c] (L : List (Bool × ℕ)) (χ : Inf m) :
    zVal (if c then L else []) χ = if c then zVal L χ else 1 := by
  split_ifs
  · rfl
  · simp [zVal]

private theorem zVal_one' {m : ℕ} (r : Bool) (k : ℕ) (χ : Inf m) :
    zVal [(r, k)] χ = GlobalTheory.Dec.gelfVal (χ r) k := by
  simp [zVal]

theorem infLimit : InfLimit := by
  intro E _ _ _ a b l₁ l₂ D A S Z L T e₁ e₂ s sk χa χb hs hsk ha hb
  obtain ⟨-, -, -, hone, hpt⟩ := ptOk E a b l₁ l₂ D A
  have h0 : s (.inl ()) = 1 := by
    rw [hs (.inl ()) trivial]
    exact hone _
  have hv₁ : ∀ v r m, s (.inr (.inl (v, r, m, false))) = GlobalTheory.Dec.gelfVal (chi l₁ v r) m := by
    intro v r m
    rw [hs (.inr (.inl (v, r, m, false))) trivial]
    show (A.pt _ _ (A.idm S L)).val _ _ = _
    rw [hpt, hone]
    simp only [zVal_ite']
    simp [zVal_one']
  have hv₂ : ∀ v r m, s (.inr (.inl (v, r, m, true))) = GlobalTheory.Dec.gelfVal (chi l₂ v r) m := by
    intro v r m
    rw [hs (.inr (.inl (v, r, m, true))) trivial]
    show (A.pt _ _ (A.idm S L)).val _ _ = _
    rw [hpt, hone]
    simp only [zVal_ite']
    simp [zVal_one']
  have hne : s (.inl ()) ≠ 0 := by rw [h0]; exact one_ne_zero
  have hc₁ : ∀ v r m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χa k v r) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (chi l₁ v r) m)) := by
    intro v r m
    have h := (hsk (.inr (.inl (v, r, m, false)))).div (hsk (.inl ())) hne
    rw [h0, div_one, hv₁] at h
    exact h.congr fun k => (ha k v r m).symm
  have hc₂ : ∀ v r m, Tendsto (fun k => GlobalTheory.Dec.gelfVal (χb k v r) m) atTop (𝓝 (GlobalTheory.Dec.gelfVal (chi l₂ v r) m)) := by
    intro v r m
    have h := (hsk (.inr (.inl (v, r, m, true)))).div (hsk (.inl ())) hne
    rw [h0, div_one, hv₂] at h
    exact h.congr fun k => (hb k v r m).symm
  refine ⟨h0, fun τ ε hε => ?_, fun τ ε hε => ?_⟩
  · exact infConv a (fun k => χa k (InfinitePlace.mk τ) _) (chi l₁ (InfinitePlace.mk τ) _) (hc₁ _ _) ε hε
  · exact infConv b (fun k => χb k (InfinitePlace.mk τ) _) (chi l₂ (InfinitePlace.mk τ) _) (hc₂ _ _) ε hε

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

section

theorem UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 :
    UpperTheory.Zero.ConvolutionTheory.EB.SphComm2 := by
  intro E _ _ _ a b w f f' hf hf'
  exact PositivityTheory.Rg.BcB.F.sphComm E a b w f f' hf hf'
end
