module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace

@[expose] public section

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.decSplit :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω), Dec (F := Lp L) A ≤ (resP L Ω).range → ∃ α : Dec (F := L) A ≃ₜ* Dec (F := Lp L) A, ∀ g, (α g : G (Lp L) Ω) = resP L Ω (g : G L Ω) := by
  intro L Ω _ _ _ _ _ _ A hA
  have hinj : Function.Injective (resP L Ω) := by
    intro a b h
    ext x
    exact congrArg (fun f : G (Lp L) Ω => f x) h
  have hmap : ∀ g : Dec (F := L) A, resP L Ω (g : G L Ω) ∈ Dec (F := Lp L) A := by
    intro g
    have hg := mem_Dec.mp g.2
    exact mem_Dec.mpr hg
  let f : Dec (F := L) A →* Dec (F := Lp L) A :=
    { toFun := fun g => ⟨resP L Ω g, hmap g⟩
      map_one' := by ext1; exact map_one (resP L Ω)
      map_mul' := fun a b => by ext1; exact map_mul (resP L Ω) a.1 b.1 }
  have hbij : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), fun t => ?_⟩
    obtain ⟨s, hs⟩ := hA t.2
    have hsA : s ∈ Dec (F := L) A := by
      apply mem_Dec.mpr
      have := mem_Dec.mp (hs ▸ t.2)
      exact this
    exact ⟨⟨s, hsA⟩, Subtype.ext hs⟩
  let e : Dec (F := L) A ≃* Dec (F := Lp L) A := MulEquiv.ofBijective f hbij
  have hcont : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_resP.comp continuous_subtype_val
  haveI : CompactSpace (Dec (F := L) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Dec (F := L) A).isCompact
  let h := hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)
  refine ⟨{ e with continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }, fun g => rfl⟩
end

section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cc_at (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : InfinitePlace F) (hw : w.IsReal) : ∃ c : G F Ω, IsCCAt w c := by
  classical
  let φ : F →+* ℂ := w.embedding
  have hφ : ∀ x, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    exact RingHom.congr_fun h x
  letI : Algebra F ℂ := φ.toAlgebra
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
  let κ : ℂ ≃ₐ[F] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => hφ x)
  refine ⟨κ.restrictNormal Ω, j.toRingHom, fun x => ?_, ?_⟩
  · exact AlgEquiv.restrictNormal_commutes κ Ω x
  · have e : j.toRingHom.comp (algebraMap F Ω) = φ := by
      ext x
      exact j.commutes x
    rw [e]
    exact InfinitePlace.mk_embedding w

theorem UpperTheory.V.Pa.ccEx :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ w : InfinitePlace (Lp L), ∃ c : G (Lp L) Ω, IsCCAt w c) ∧ ∀ c : G (Lp L) Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → c * c = 1 ∧ c ∉ (resP L Ω).range ∧ cycZ (Lp L) Ω l c = -1 := by
  intro l _ L Ω _ _ _ _ _ _
  haveI : Algebra.IsAlgebraic (Lp L) L := Algebra.IsAlgebraic.of_finite (Lp L) L
  haveI : IsAlgClosure (Lp L) Ω := IsAlgClosure.ofAlgebraic (Lp L) L Ω
  refine ⟨fun w => cc_at (Lp L) Ω w (IsTotallyReal.isReal w), ?_⟩
  rintro c ⟨j, hj⟩
  refine ⟨?_, ?_, ?_⟩
  · apply AlgEquiv.ext
    intro x
    apply j.injective
    show j (c (c x)) = j x
    rw [hj, hj, Complex.conj_conj]
  · rintro ⟨σ, hσ⟩
    have hfix : ∀ y : L, c (algebraMap L Ω y) = algebraMap L Ω y := by
      intro y
      rw [← hσ]
      exact σ.commutes y
    let ψ : L →+* ℂ := j.comp (algebraMap L Ω)
    have hreal : ComplexEmbedding.IsReal ψ := by
      rw [ComplexEmbedding.isReal_iff]
      ext y
      show starRingEnd ℂ (j (algebraMap L Ω y)) = j (algebraMap L Ω y)
      rw [← hj, hfix]
    have hR : (InfinitePlace.mk ψ).IsReal := InfinitePlace.isReal_mk_iff.mpr hreal
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _)) hR
  · exact UpperTheory.V.IsConjOm.cyc (E := L) (σ := MulSemiringAction.toRingAut (G (Lp L) Ω) Ω c) ⟨j, hj⟩
end
