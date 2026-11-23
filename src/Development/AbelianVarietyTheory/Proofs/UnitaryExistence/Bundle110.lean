module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle107
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle108
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
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

@[expose] public section

section

noncomputable section

namespace GlobalTheory.GalTw.CharSec

section General

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sec_eq_zero_of_complex (σ : c.F →+* ℂ) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c}
    (hg : g ∈ sec Xo c a n) (h : ∀ y : FrPt Xo c (CAt σ), evR Xo c g y = 0) : g = 0 := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW := (GlobalTheory.Frames.algebraic_laws hS E H Dw l Xo c).2.2.1
  funext p y
  have : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  letI : Algebra c.F ℂ := σ.toAlgebra
  refine GlobalTheory.FiniteOrderRule.eq_zero_of_forall_algHom (K := c.F) (Ω := ℂ) (g p y) ?_
  intro φ
  let φ' : p.R →ₐ[c.F] CAt σ := φ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R (CAt σ) φ' y
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ', y, hz⟩
  have h0 := h z
  unfold evR evalAt at h0
  rw [dite_eq_left hT, ← hW g hg.1 (CAt σ) p _ φ' _ y _ z hz hT.choose_spec.choose_spec.choose_spec] at h0
  exact h0

theorem conj_value (σ σ' : c.F →+* ℂ) (τ : ℂ ≃+* ℂ) (hσ : σ' = (τ : ℂ →+* ℂ).comp σ) {f : Rul Xo c}
    (hf : f ∈ sec Xo c 0 0) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt σ'))
    (h : y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x) : toC (evR Xo c f y') = τ (toC (evR Xo c f y)) := by
  subst hσ
  exact GlobalTheory.T.weightZeroSection_value_conj_point E H Dw l Xo c σ τ f hf y y' h

theorem exists_conj_point (σ : c.F →+* ℂ) {ta : c.F ≃+* c.F} (hta : Fixes c ta) (τ : ℂ ≃+* ℂ)
    (hτ : ∀ a, τ (σ a) = σ (ta a)) (y : FrPt Xo c (CAt σ)) :
    ∃ y₀ : FrPt Xo c (CAt σ), y.x = spMap (τ : ℂ →+* ℂ) ≫ y₀.x ∧
      ∀ f ∈ sec Xo c 0 0, toC (evR Xo c (galRul hta f) y) = τ (toC (evR Xo c f y₀)) := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  let φ : CAt (σ.comp ta.toRingHom) →ₐ[c.F] CAt σ :=
    { toRingHom := (τ.symm : ℂ →+* ℂ)
      commutes' := fun a => by
        show τ.symm (σ (ta a)) = σ a
        rw [← hτ, RingEquiv.symm_apply_apply] }
  let y' : FrPt Xo c (CAt (σ.comp ta.toRingHom)) := twPt hta y
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ φ y'
  have hx : y.x = spMap (τ : ℂ →+* ℂ) ≫ z.x := by
    have h1 : z.x = spMap (τ.symm : ℂ →+* ℂ) ≫ y.x := hz.1
    have h2 : spMap (τ : ℂ →+* ℂ) ≫ spMap (τ.symm : ℂ →+* ℂ) = 𝟙 _ := by
      unfold spMap
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      simp
    rw [h1]
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ y.x) h2).trans (Category.id_comp _))).symm
  refine ⟨z, hx, fun f hf => ?_⟩
  have e1 := (((GlobalTheory.T.conjugateSection_values_semilinear E H Dw l Xo c ta hta).1 0 0 f hf).2 (CAt σ) y)
  have e2 := conj_value σ (σ.comp ta.toRingHom) τ (RingHom.ext fun a => (hτ a).symm) hf z y' hx
  rw [e1]
  exact e2

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat GlobalTheory.GalTw

end GlobalTheory.GalTw.CharSec
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_uniformisationData_nonempty_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Nonempty U.Comp := by
  first | exact @GlobalTheory.exists_unf_nonempty_comp | exact GlobalTheory.exists_unf_nonempty_comp | (intros; apply GlobalTheory.exists_unf_nonempty_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.supNorm_definite_on_cuspForms_goodEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → Formalism.L2.PjFree.SupDef Xo c U := by
  first | exact @GlobalTheory.supNorm_definite_on_cusp | exact GlobalTheory.supNorm_definite_on_cusp | (intros; apply GlobalTheory.supNorm_definite_on_cusp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

theorem _root_.GlobalTheory.T.framedUniformisation_components_periodSpaces_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), 1 ≤ r → GoodEmb c σ → IsUnf U → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) → (∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ), (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧ IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((U.un k x).u τ i)) → Function.Bijective ik := by
  first | exact @GlobalTheory.CompBij.ik_bijective | exact GlobalTheory.CompBij.ik_bijective | (intros; apply GlobalTheory.CompBij.ik_bijective <;> assumption)
end
