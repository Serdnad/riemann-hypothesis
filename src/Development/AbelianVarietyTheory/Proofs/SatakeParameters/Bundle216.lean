module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

open GlobalTheory.DefU

namespace GlobalTheory.Cong

theorem ofType_of_finPart_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n)
    (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) →
    OfType (fun τ => W.at τ) K π.V := by
  intro E _ _ _ n π W K f hf hf0 hK
  refine ⟨π.isAut, fun τ => ?_, ?_⟩
  · have h : (AU.mk π).HasWt (InfinitePlace.mk τ).embedding (W (InfinitePlace.mk τ)) :=
      hasWeightAt_of_finPart π W hf hf0 (InfinitePlace.mk τ)
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · have h' := h
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), e] at h'
      exact h'
    · have h2 := h.conjugate
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ] at h2
      exact h2
  · have hne : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (LinearMap.ext hc)
    refine ⟨f.1 v, AutSub.mem_finPart.1 hf v, hv, fun x hx => ?_⟩
    funext g
    rw [RU_apply]
    exact hK x hx v g

end GlobalTheory.Cong

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem datLoc_homRe : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (M : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin b' → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a' b' → ℂ), HEq N M → HEq N' M' → DatLoc D cc SS cl M M' Ξ → DatLoc D cc SS cl N N' (fun z => Ξ (homRe ha hb z)) := by
  intro D cc SS cl a b a' b' ha hb N N' M M' Ξ hN hN' h
  subst ha hb
  cases eq_of_heq hN
  cases eq_of_heq hN'
  have hx : (fun z => Ξ (homRe rfl rfl z)) = Ξ := by
    funext z
    congr 1
  rw [hx]
  exact h

end GlobalTheory.TwU
end
