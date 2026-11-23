module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle046
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructure
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle048
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.dual_map_of_field_extension : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V'), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V', ∀ w e, jd w (j e) = i (w e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DualExt.dual_ext | exact GlobalTheory.CompanionTheory.Ar.DualExt.dual_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.DualExt.dual_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.different_scaled_lattice_extension : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (W : Submodule Ω V) (W' : Submodule Ω' V') (O : Type) [CommRing O] (σ : O →+* Ω) (𝔡 : Ideal O) (d₀ : O) (D : Submodule R V) (D' : Submodule R' V'), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → W' = Submodule.span Ω' (j '' (W : Set V)) → d₀ ∈ 𝔡 → σ d₀ ≠ 0 → (∀ d ∈ 𝔡, σ d / σ d₀ ∈ R) → (∀ e ∈ D, e ∈ W) → D' = Submodule.span R' (j '' (D : Set V)) → Submodule.span R' {e | e ∈ W' ∧ ∀ d ∈ 𝔡, (i.comp σ) d • e ∈ D'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.scale_pull_ext | exact GlobalTheory.CompanionTheory.Ar.scale_pull_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.scale_pull_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.dual_lattice_basis_extension : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (ω : Submodule R (Module.Dual Ω V)) (ω' : Submodule R' (Module.Dual Ω' V')) (r : ℕ) (b : Fin r → Module.Dual Ω W), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (0 < r → ω' = Submodule.span R' (jd '' (ω : Set (Module.Dual Ω V)))) → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = ⊤ → ω.map (W.dualRestrict.restrictScalars R) = Submodule.span R (Set.range b) → Submodule.span R' {e | e ∈ W' ∧ ∀ w ∈ ω', w e ∈ R'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ w ∈ ω, w e ∈ R} : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptPull.dual_pull | exact GlobalTheory.CompanionTheory.Ar.HcptPull.dual_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptPull.dual_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.log_periods_module_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ))), (∀ c x, DifferentiableOn ℂ (fun z => B z c x) (Metric.ball 0 1)) → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ c x, ∃ y, L.P w y = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x)) → ∃ _ : Module (𝓞 E) Λ, ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ (c : 𝓞 E) x, L.P w (c • x) = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action | exact GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.generic_flag_field_change : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | exact GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.generic_flag_over_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E), (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.flag_chart_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (p' : Cpt ξ') (c₁ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), InChart ξ' (flagCoord κ x φ c) ((c₁, J) : FlagIx κ n r) p' → algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 ∧ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p' ∧ ∀ q : Σ s, Fin (r s), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 ∧ ∀ l j, ((flagMat φ c q.1).submatrix (Function.update (J q) l j) (Fin.castLE q.2.2)).det / ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ∈ regAt ξ' p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_flagCoord_ratios <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.frame_matrix_chart_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S] (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → (∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) → ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | exact GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem val_appLE_of_dominates {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
    (hd : Dominates ξ' ξ f i) {U : X.Opens} {W : X'.Opens} (e : W ≤ f ⁻¹ᵁ U) (hW : genPt ξ' ∈ W)
    (hU : genPt ξ ∈ U) (t : Γ(X, U)) :
    (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) =
      i ((X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t) := by
  have hfq : f (genPt ξ') ∈ U := e hW
  have hp : genPt ξ ⤳ f (genPt ξ') := by rw [RegAtDom.map_genPt hd]
  have h := RegAtDom.genMap_stalkMap hd (genPt ξ') specializes_rfl hp
    ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t)
  have l1 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ f.stalkMap (genPt ξ') =
      f.appLE U W e ≫ X'.presheaf.germ W (genPt ξ') hW := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have l2 : X'.presheaf.germ W (genPt ξ') hW ≫ X'.presheaf.stalkSpecializes specializes_rfl =
      X'.presheaf.germ W (genPt ξ') hW := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have l3 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ X.presheaf.stalkSpecializes hp =
      X.presheaf.germ U (genPt ξ) hU := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have a1 : (f.stalkMap (genPt ξ')).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t) :=
    congrArg (fun g => g.hom t) l1
  have a2 : ∀ s, (X'.presheaf.stalkSpecializes specializes_rfl).hom
      ((X'.presheaf.germ W (genPt ξ') hW).hom s) = (X'.presheaf.germ W (genPt ξ') hW).hom s :=
    fun s => congrArg (fun g => g.hom s) l2
  have a3 : (X.presheaf.stalkSpecializes hp).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU).hom t := congrArg (fun g => g.hom t) l3
  rw [a1] at h
  have b1 : genMap ξ' ⟨genPt ξ', specializes_rfl⟩ ((X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t)) =
      (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) := by
    exact congrArg (Scheme.stalkClosedPointTo ξ').hom (a2 _)
  have b2 : genMap ξ ⟨f (genPt ξ'), hp⟩ ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t := by
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom a3
  rw [← b1, h, b2]

theorem smooth_of_pieces : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i →
    (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C),
      IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧
      ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hg hg' hd h
  refine (HasRingHomProperty.iff_exists_appLE (P := @Smooth) (Q := RingHom.Smooth)
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1).2 fun p' => ?_
  obtain ⟨U, W, R, C, hRC, hU, hW, e, hp, hs⟩ := h p'
  refine ⟨⟨U, hU.affine⟩, ⟨W, hW.affine⟩, hp, e, ?_⟩
  have hWg : genPt ξ' ∈ W := (hW.spec p' hp).mem_open W.isOpen hp
  have hUg : genPt ξ ∈ U := by
    have h1 : f (genPt ξ') ∈ U := e hWg
    rwa [RegAtDom.map_genPt hd] at h1
  obtain ⟨injU, ranU⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hg U hUg hU.spec
  obtain ⟨injW, ranW⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X' Ω' ξ' hg' W hWg hW.spec
  have memR : ∀ t, (X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom t ∈ R :=
    fun t => (hU.ring _).2 ((ranU _).1 ⟨t, rfl⟩)
  have memC : ∀ t, (X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom t ∈ C :=
    fun t => (hW.ring _).2 ((ranW _).1 ⟨t, rfl⟩)
  let eU : Γ(X, U) ≃+* R := RingEquiv.ofBijective
    ((X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom.codRestrict R memR)
    ⟨fun a b hab => injU (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranU r.1).2 ((hU.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  let eW : Γ(X', W) ≃+* C := RingEquiv.ofBijective
    ((X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom.codRestrict C memC)
    ⟨fun a b hab => injW (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranW r.1).2 ((hW.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  have hval : ∀ t, eW ((f.appLE U W e).hom t) =
      ((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)) (eU t) :=
    fun t => Subtype.ext (val_appLE_of_dominates hd e hWg hUg t)
  have key : (f.appLE U W e).hom = (eW.symm : C →+* Γ(X', W)).comp
      (((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)).comp (eU : Γ(X, U) →+* R)) :=
    RingHom.ext fun t => (eW.symm_apply_eq.2 (hval t).symm).symm
  show RingHom.Smooth (f.appLE U W e).hom
  rw [key]
  exact RingHom.Smooth.comp (RingHom.Smooth.comp (RingHom.Smooth.of_bijective eU.bijective) hs)
    (RingHom.Smooth.of_bijective eW.symm.bijective)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem smooth_of_away_mvPolynomial {R L ι : Type} [CommRing R] [CommRing L] [Finite ι]
    (g : R →+* L) (ψ : MvPolynomial ι R →+* L) (hg : ψ.comp MvPolynomial.C = g) (f : MvPolynomial ι R)
    (hl : @IsLocalization.Away _ _ f L _ ψ.toAlgebra) : g.Smooth := by
  letI := ψ.toAlgebra
  haveI := hl
  have h1 : ψ.Smooth := (Algebra.Smooth.of_isLocalization_Away f : Algebra.Smooth (MvPolynomial ι R) L)
  have h2 : (algebraMap R (MvPolynomial ι R)).Smooth :=
    RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  rw [MvPolynomial.algebraMap_eq] at h2
  rw [← hg]
  exact RingHom.Smooth.comp h2 h1

def evalSub {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω) (v : ι → K) :
    MvPolynomial ι R →+* K :=
  MvPolynomial.eval₂Hom ((algebraMap Ω K).comp R.subtype) v

theorem evalSub_injective {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) (hv : AlgebraicIndependent Ω v) : Function.Injective (evalSub R v) := by
  have e : evalSub R v =
      (MvPolynomial.aeval v : MvPolynomial ι Ω →ₐ[Ω] K).toRingHom.comp (MvPolynomial.map R.subtype) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evalSub]
    · intro i
      simp [evalSub]
  rw [e]
  exact fun p q hpq => MvPolynomial.map_injective _ R.subtype_injective
    (algebraicIndependent_iff_injective_aeval.1 hv hpq)

theorem evalSub_range {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) : (evalSub R v).range =
      Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    induction a using MvPolynomial.induction_on with
    | C a =>
      refine Subring.subset_closure (Or.inl ⟨a, a.2, ?_⟩)
      simp [evalSub]
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subring.subset_closure (Or.inr ⟨i, ?_⟩))
      simp [evalSub]
  · refine Subring.closure_le.2 ?_
    rintro x (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [evalSub]⟩
    · exact ⟨MvPolynomial.X i, by simp [evalSub]⟩

theorem smooth_locSub_closure : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  intro Ω K _ _ _ ι _ R v hv ℓ hℓ h0 h
  have hr := evalSub_range R v
  generalize Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) = B at *
  subst hr
  have hinj := evalSub_injective R v hv
  have hmem : ∀ a, evalSub R v a ∈ locSub (evalSub R v).range ℓ :=
    fun a => le_locSub _ _ ⟨a, rfl⟩
  obtain ⟨f, hf⟩ := hℓ
  refine smooth_of_away_mvPolynomial _ ((evalSub R v).codRestrict _ hmem) ?_ f ?_
  · ext a
    change evalSub R v (MvPolynomial.C a) = algebraMap Ω K a
    simp [evalSub]
  · letI := ((evalSub R v).codRestrict _ hmem).toAlgebra
    have hval : ∀ a : MvPolynomial ι R,
        ((algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) a : locSub (evalSub R v).range ℓ) : K)
          = evalSub R v a := fun a => rfl
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨_, n, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) f) := by
        refine IsUnit.of_mul_eq_one ⟨ℓ⁻¹, inv_mem_locSub _ _⟩ (Subtype.ext ?_)
        simp [hval, hf, h0]
      simpa using hu.pow n
    · rintro ⟨z, hz⟩
      obtain ⟨k, hk⟩ := (mem_locSub_iff (RingHom.mem_range.2 ⟨f, hf⟩) h0 z).1 hz
      obtain ⟨a, ha⟩ := RingHom.mem_range.1 hk
      refine ⟨⟨a, ⟨f ^ k, k, rfl⟩⟩, Subtype.ext ?_⟩
      simp [hval, hf, ha, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [hinj (congrArg Subtype.val hxy)]⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem chartSub_div_mem {F : Type} [Field F] {κ : Type} (x : κ → F) (c j : κ) :
    x j / x c ∈ chartSub x c :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem chartSub_le_of_forall {F : Type} [Field F] {κ : Type} {x : κ → F} {c : κ} {T : Subring F}
    (h : ∀ j, x j / x c ∈ T) : chartSub x c ≤ T := by
  intro a ha
  have ha' : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := ha
  induction ha' using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    exact h j
  | algebraMap n => simpa using intCast_mem T n
  | add b d _ _ hb hd => exact T.add_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))
  | mul b d _ _ hb hd => exact T.mul_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))

theorem locSub_le_of {F : Type} [Field F] {R T : Subring F} {a : F} (h : R ≤ T) (ha : a⁻¹ ∈ T) :
    locSub R a ≤ T :=
  Subring.closure_le.2 (Set.union_subset h (Set.singleton_subset_iff.2 ha))

theorem flagCoord_div_eq {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type}
    (x : κ → Ω) {S : Type} [Fintype S] {r n m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω}
    {c₀ : κ} (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (hx : x c₀ ≠ 0)
    (h : ∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) (k : κ)
    (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc ((k, J') : FlagIx κ n r) / flagCoord κ x φ cc ((c₀, J) : FlagIx κ n r) =
      algebraMap Ω (GenField Ω r) (x k / x c₀) *
        ∏ q : (Σ s, Fin (r s)), stepMinor (flagB M T q.1) q.2 (J' q) / stepMinor (flagB M T q.1) q.2 (J q) := by
  have hi : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := (map_ne_zero _).2 hx
  rw [flagCoord_eq x h k J', flagCoord_eq x h c₀ J, map_div₀, mul_div_mul_comm,
    ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hi))

theorem chartRing_eq_ratioRing : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type)
    (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω)
    (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 →
    g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) →
    (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) →
    algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧
    locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) =
      ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  intro Ω _ E _ _ κ x S _ r n m φ cc M T c₀ J g hx hg hg0 h hJ
  classical
  set A := chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) with hA
  have hdiv := fun k J' => flagCoord_div_eq (m := m) x J hx h k J'

  have h1 : ∀ k, algebraMap Ω (GenField Ω r) (x k / x c₀) ∈ A := by
    intro k
    have e := hdiv k J
    have e1 : ∏ q : (Σ s, Fin (r s)),
        stepMinor (flagB M T q.1) q.2 (J q) / stepMinor (flagB M T q.1) q.2 (J q) = 1 :=
      Finset.prod_eq_one fun q _ => div_self (hJ q)
    rw [e1, _root_.mul_one] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ((k, J) : FlagIx κ n r)

  have h2 : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A := by
    intro q J'
    have e := hdiv c₀ (Function.update J q J')
    rw [div_self hx, map_one, _root_.one_mul, Finset.prod_div_distrib,
      prod_update_div (β := fun q : (Σ s, Fin (r s)) => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => stepMinor (flagB M T q.1) q.2 b) J hJ q J'] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)
      ((c₀, Function.update J q J') : FlagIx κ n r)
  have himg : chartSub x c₀ ≤ A.comap (algebraMap Ω (GenField Ω r)) :=
    chartSub_le_of_forall fun j => h1 j
  have hgA : algebraMap Ω (GenField Ω r) g ∈ A := himg hg
  refine ⟨hgA, le_antisymm ?_ ?_⟩
  ·
    set R' := locSub (chartSub x c₀) g with hR'
    have him : ∀ b ∈ R', algebraMap Ω (GenField Ω r) b ∈ ratioRing R' (flagB M T) J := fun b hb =>
      Subring.subset_closure (Or.inl ⟨b, hb, rfl⟩)
    refine locSub_le_of (chartSub_le_of_forall ?_) ?_
    · rintro ⟨k, J'⟩
      rw [hdiv k J']
      refine Subring.mul_mem _ (him _ (le_locSub _ _ (chartSub_div_mem x c₀ k))) ?_
      exact Subring.prod_mem _ fun q _ => Subring.subset_closure (Or.inr ⟨q, J' q, rfl⟩)
    · rw [← map_inv₀]
      exact him _ (inv_mem_locSub _ _)
  · refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨b, hb, rfl⟩
      have hle : locSub (chartSub x c₀) g ≤
          (locSub A (algebraMap Ω (GenField Ω r) g)).comap (algebraMap Ω (GenField Ω r)) := by
        refine locSub_le_of (himg.trans fun a ha => le_locSub _ _ ha) ?_
        show algebraMap Ω (GenField Ω r) g⁻¹ ∈ locSub A (algebraMap Ω (GenField Ω r) g)
        rw [map_inv₀]
        exact inv_mem_locSub _ _
      exact hle hb
    · rintro _ ⟨q, J', rfl⟩
      exact le_locSub _ _ (h2 q J')

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.smooth_adjoin_inverse : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → Algebra.Smooth ℚ A → Algebra.Smooth ℚ (Mdl.invAdj A g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj <;> assumption)
end
