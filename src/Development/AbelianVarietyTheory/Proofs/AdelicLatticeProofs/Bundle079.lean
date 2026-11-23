module

public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
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
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CNorm

theorem exists_isReal_embedding_eq_hom {F : Type} [Field F] (σ : F →+* ℝ) :
    ∃ (v : InfinitePlace F) (hv : v.IsReal), InfinitePlace.embedding_of_isReal hv = σ := by
  have hr : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hv : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := ⟨_, hr, rfl⟩
  refine ⟨_, hv, ?_⟩
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hr]
  rfl

theorem hasseNorm : GlobalTheory.Published.HasseNorm := by
  intro K L _ _ _ _ _ hG hC a ha hf hi
  refine GlobalTheory.T.hasseNormPrinciple_of_isCyclic K L hG hC a ha ⟨hf, fun alg => ?_⟩
  obtain ⟨v, hv, hσ⟩ := exists_isReal_embedding_eq_hom (algebraMap K ℝ)
  let φ : v.Completion →ₐ[K] ℝ :=
    { InfinitePlace.Completion.extensionEmbeddingOfIsReal hv with
      commutes' := fun x => by
        rw [← hσ]
        rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
          Algebra.algebraMap_self_apply]
        exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x) }
  exact (GlobalTheory.T.isNormFromBaseChange_base_change_properties K L).1 v.Completion ℝ φ a (hi v)

end GlobalTheory.CNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ x : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ)) := by
  first | exact @GlobalTheory.StdRat.stdChar_fin_rat | exact GlobalTheory.StdRat.stdChar_fin_rat | (intros; apply GlobalTheory.StdRat.stdChar_fin_rat <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_galoisConjugates_heckeChar_trivialOnRealIdeles : ∀ (D : D7) (Q : Par D) (χ₀ : (AE D)ˣ →* Circle), IsHeckeChar D χ₀ → (∀ a, χ₀ (idF D a) = 1) → (∀ x, FinUnit x → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = Q.c.F.val.toRingHom y) → ∃ χ : (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle, χ Q.c.F.val.toRingHom = χ₀ ∧ ∀ σ, IsHeckeChar D (χ σ) ∧ (∀ a, χ σ (idF D a) = 1) ∧ MuConj Q.c.F.val.toRingHom σ χ₀ (χ σ) := by
  first | exact @GlobalTheory.HeckeConj.exists_conjugates | exact GlobalTheory.HeckeConj.exists_conjugates | (intros; apply GlobalTheory.HeckeConj.exists_conjugates <;> assumption)
end
