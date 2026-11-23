module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle109
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle111
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle057
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle112
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem GlobalTheory.Member.Ctx.exists_isDict : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∃ dict, C.IsDict dict := by
  intro D H Dw l Xo c σ V r C hC
  classical
  choose k₀ γ₀ h₀ using GlobalTheory.T.exists_component_lattice_marking_adelic D H Dw l Xo c σ V r C hC
  refine ⟨fun h => if hk : ∃ k, C.Mark h k 1 then ⟨hk.choose, C.fr h hk.choose⟩
    else ⟨k₀ h, C.fr (γ₀ h * h) (k₀ h)⟩, ?_, ?_⟩
  · intro h
    by_cases hk : ∃ k, C.Mark h k 1
    · refine ⟨1, ?_⟩
      beta_reduce
      rw [dite_eq_left hk]
      exact ⟨hk.choose_spec, by rw [one_mul]⟩
    · refine ⟨γ₀ h, ?_⟩
      beta_reduce
      rw [dite_eq_right hk]
      exact ⟨h₀ h, rfl⟩
  · intro k
    obtain ⟨h, hf, hm⟩ := GlobalTheory.T.exists_finiteAdelic_element_marking_component D H Dw l Xo c σ V r C hC k
    have hk : ∃ k, C.Mark h k 1 := ⟨k, hm⟩
    refine ⟨h, ?_⟩
    beta_reduce
    rw [dite_eq_left hk]
    have e : hk.choose = k :=
      (GlobalTheory.T.marking_component_unique_frame_unique_arithmeticGroup D H Dw l Xo c σ V r C hC h).1 _ _ _ _ hk.choose_spec hm
    rw [e]
    have := (GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC 1 k).2.2.2.2.1 h hf
    rw [one_mul] at this
    rw [this]
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_framesOK : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), Formalism.L2.PjFree.GoodEmb c σ → ModelBase M → NegXi M → ∃ un, FramesOK e F M un := by
  intro hB hT E _ _ _ H Dw l Xo c σ g e F r M hσ hM hξ
  have T : ∀ k, ThetaData e F M k := fun k =>
    (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F r M k (T k)
  exact ⟨un,
    fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
    fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
    fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩

end GlobalTheory.FrameUnif
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

theorem _root_.GlobalTheory.T.exists_orthogonal_idempotentSections_periodSpaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : Fin F.n → Rul Xo c, (∀ i, χ i ∈ sec Xo c 0 0) ∧ (∀ i, χ i * χ i = χ i) ∧ (∀ i i', i ≠ i' → χ i * χ i' = 0) ∧ ∑ i, χ i = 1 ∧ ∀ (y : FrPt Xo c (CAt σ)) (i i' : Fin F.n) P, IsPeriod (F.Di i') ty P → y.x = F.u i' P → toC (evR Xo c (χ i) y) = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompSystem.exists_orthogonal_idempotents | exact GlobalTheory.CompSystem.exists_orthogonal_idempotents | (intros; apply GlobalTheory.CompSystem.exists_orthogonal_idempotents <;> assumption)
end
