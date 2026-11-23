module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle003
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle266
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubspaceTrivialOutsideSplitPlac
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle267
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.mem_heckeSplitPlaceSet_iff_doubleCoset : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L) (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k, ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧ ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := by
  exact GlobalTheory.TSetDoubleCoset.mem_tSet_iff
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n), ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ g = x * y := by
  first | exact @GlobalTheory.PlaceDecomp.decomp | exact GlobalTheory.PlaceDecomp.decomp | (intros; apply GlobalTheory.PlaceDecomp.decomp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  first | exact @GlobalTheory.realUnif_split | exact GlobalTheory.realUnif_split | (intros; apply GlobalTheory.realUnif_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_irreducible_subspace_trivialOutside_splitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (B : π.S → π.S → ℂ), (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) → (∀ x y, B x y = starRingEnd ℂ (B y x)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x → (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) → ∀ s : SplitPlace L, ∃ W : Submodule ℂ (GAf L n → ℂ), W ≤ π.S ∧ W ≠ ⊥ ∧ (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W) ∧ ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W := by
  first | exact @GlobalTheory.exists_irreducible_sub_trivOutside_split | exact GlobalTheory.exists_irreducible_sub_trivOutside_split | (intros; apply GlobalTheory.exists_irreducible_sub_trivOutside_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_realSubfield_place_in_ramified_set : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  first | exact @GlobalTheory.GeoUnder.exists_under_in_qPl | exact GlobalTheory.GeoUnder.exists_under_in_qPl | (intros; apply GlobalTheory.GeoUnder.exists_under_in_qPl <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongSplitBoth

open GlobalTheory.IdemSplit GlobalTheory.CongSplit

theorem split_cong_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n), NG.Cong L n N κ → ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ NG.Cong L n N x ∧ NG.Cong L n N y ∧ κ = x * y := by
  intro L _ _ _ n N v κ hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ κ, gaFold he' hσ' κ, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_one_apply]
    simp [he_def, compAt_idemAt_self]
  · refine ⟨gaFold_mem_Umax L he hσ hei κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨e * y, Subring.mul_mem _ hei hy, ?_⟩
    rw [gaFold_val, fold_apply]
    linear_combination e * hEq
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · apply Subtype.ext; apply Units.ext
    show (κ.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.CongSplitBoth
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

theorem _root_.GlobalTheory.T.congruence_element_decompose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  first | exact @GlobalTheory.CongSplit.decomp | exact GlobalTheory.CongSplit.decomp | (intros; apply GlobalTheory.CongSplit.decomp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.doubleCosetOperator_translate_deeper_level_eq_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (h : GAf L n), J' ≤ J → (∀ κ ∈ J', h⁻¹ * κ * h ∈ J) → {c : GAf L n ⧸ J' | ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ J') = c}.Finite → ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ J, NG.rt L n κ f = f) → NG.heckeD J' (J : Set (GAf L n)) (NG.rt L n h f) = (m : ℂ) • NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'} f := by
  first | exact @GlobalTheory.HeckeAverage.heckeD_rt_eq_smul | exact GlobalTheory.HeckeAverage.heckeD_rt_eq_smul | (intros; apply GlobalTheory.HeckeAverage.heckeD_rt_eq_smul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.equivariant_iso_of_translationStable_graph : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρa : Representation ℂ (GQ L n) A) (ρb : Representation ℂ (GQ L n) B) (S₁ : Submodule ℂ (GAf L n → A)) (S₂ : Submodule ℂ (GAf L n → B)) (W : Submodule ℂ ((GAf L n → A) × (GAf L n → B))), NG.IsIrrRep ρa S₁ → NG.IsIrrRep ρb S₂ → (∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂) → (∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W) → (∀ u, ((0 : GAf L n → A), u) ∈ W → u = 0) → (∀ u, (u, (0 : GAf L n → B)) ∈ W → u = 0) → W ≠ ⊥ → NG.IsoRep S₁ S₂ := by
  first | exact @GlobalTheory.isoRep_of_stable_graph | exact GlobalTheory.isoRep_of_stable_graph | (intros; apply GlobalTheory.isoRep_of_stable_graph <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.exists_deeper_congruence_conj_into_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (g : GAf L n), 0 < N → ∃ M : ℕ, 0 < M ∧ ∀ κ, NG.Cong L n (N * M) κ → NG.Cong L n N (g⁻¹ * κ * g) := by
  first | exact @GlobalTheory.ConjCong.exists_cong_conj | exact GlobalTheory.ConjCong.exists_cong_conj | (intros; apply GlobalTheory.ConjCong.exists_cong_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f) → ∀ f ∈ NG.isoTyp ρ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  first | exact @GlobalTheory.RtSumScalar.rtSum_isoTyp | exact GlobalTheory.RtSumScalar.rtSum_isoTyp | (intros; apply GlobalTheory.RtSumScalar.rtSum_isoTyp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v → s.w = w ∨ IsConjPl D.host w s.w := by
  first | exact @GlobalTheory.SplitPlaceOver.eq_or_isConjPl | exact GlobalTheory.SplitPlaceOver.eq_or_isConjPl | (intros; apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl <;> assumption)
end
