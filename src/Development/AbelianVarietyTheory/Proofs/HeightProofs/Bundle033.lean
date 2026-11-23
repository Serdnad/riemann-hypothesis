module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CuspAlgComparison

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions NumberField GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TotallyPositiveExponents
open Matrix hiding vec
open scoped ComplexOrder

section Host

variable {R : Ranks} (H : Host R)

theorem tau_injective : Function.Injective (tau H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

theorem tau_sqrt (τ : Pl R) : tau H τ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) :=
  ((factEmb R H).2 _).2 τ.2

theorem sqrt_d_pos : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)

theorem emb_cases (σ : H.E →+* ℂ) :
    ∃ τ : Pl R, σ = tau H τ ∨ σ = (starRingEnd ℂ).comp (tau H τ) := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  by_cases hg : g ∈ R.Psi
  · exact ⟨⟨g, hg⟩, Or.inl rfl⟩
  · rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, not_not] at hg
    refine ⟨⟨_, hg⟩, Or.inr (RingHom.ext fun x => ?_)⟩
    change H.emb g x = starRingEnd ℂ (H.emb (g * R.cc) x)
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    change _ = starRingEnd ℂ (H.emb g (H.conj x))
    rw [show H.emb g (H.conj x) = _ from H.conjE_apply _ x]
    simp

theorem tau_ne_conj (τ τ' : Pl R) : tau H τ ≠ (starRingEnd ℂ).comp (tau H τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h H.sqrtMinusD)
  rw [RingHom.comp_apply, tau_sqrt, tau_sqrt] at h1
  have := sqrt_d_pos H
  simp at h1
  linarith

end Host

section Forms

variable {R : Ranks} {H : Host R} {n : ℕ}


end Forms

end GlobalTheory.CuspAlgComparison

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.normInf_submultiplicative_le_adelicHeight : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧ ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  first | exact @GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | exact GlobalTheory.SmoothForms.normInf_mul_le_and_le_height | (intros; apply GlobalTheory.SmoothForms.normInf_mul_le_and_le_height <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem _root_.GlobalTheory.T.unitaryAdelicHeight_coset_le_normInf_pow : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  first | exact @GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | exact GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow | (intros; apply GlobalTheory.SmoothForms.HeightCoset.height_le_normInf_pow <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.FockCompare

section General

open NumberField GlobalTheory.InfAdeleCM
open scoped TensorProduct

theorem exists_real_chart_general {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {I : Type}
    (σ : I → (F →+* ℂ)) (hb : Function.Bijective fun i => InfinitePlace.mk (σ i)) :
    ∃ ρ : (I → ℝ) →+ InfiniteAdeleRing F, Continuous ρ ∧ (∀ x i, ext (σ i) (ρ x) = (x i : ℂ)) ∧
      ∀ a : InfiniteAdeleRing F, (∀ i, ext (σ i) a = 0) → a = 0 := by
  let e : I ≃ InfinitePlace F := Equiv.ofBijective _ hb
  let r : ∀ v : InfinitePlace F, v.Completion ≃+* ℝ := fun v =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v, Continuous (r v).symm := fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous
  refine ⟨{ toFun := fun x v => (r v).symm (x (e.symm v))
            map_zero' := funext fun v => map_zero (r v).symm
            map_add' := fun x y => funext fun v => map_add (r v).symm _ _ }, ?_, ?_, ?_⟩
  · exact continuous_pi fun v => (hr v).comp (continuous_apply _)
  · intro x i
    rw [ext_eq_ofReal]
    congr 1
    have h := (r (e i)).apply_symm_apply (x (e.symm (e i)))
    refine Eq.trans h ?_
    rw [e.symm_apply_apply]
  · intro a ha
    funext v
    obtain ⟨i, rfl⟩ := hb.2 v
    exact (InfinitePlace.Completion.extensionEmbedding _).injective ((ha i).trans (map_zero _).symm)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_real_chart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) → ∃ ρ : (D.what₂.Tau → ℝ) →+ Ainf D.host.F, Continuous ρ ∧ (∀ x τ, θ τ (ρ x ⊗ₜ[D.host.F] (1 : D.host.E)) = (x τ : ℂ)) ∧ ∀ a : Ainf D.host.F, (∀ τ, θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 0) → a = 0 := by
  intro D θ hθ hb
  haveI := D.sp.cm.totReal
  obtain ⟨ρ, h1, h2, h3⟩ := exists_real_chart_general (F := D.host.F)
    (fun τ : D.what₂.Tau => (tauE D τ).comp (algebraMap D.host.F D.host.E)) hb
  have key : ∀ τ (a : Ainf D.host.F), θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) =
      GlobalTheory.InfAdeleCM.ext ((tauE D τ).comp (algebraMap D.host.F D.host.E)) a := fun τ a => by
    have := GlobalTheory.InfAdeleCM.hom_tmul (tauE D τ) (θ τ) (hθ τ).1 (hθ τ).2 a 1
    rw [RingHom.map_one, mul_one] at this
    exact this
  exact ⟨ρ, h1, fun x τ => (key τ _).trans (h2 x τ), fun a ha => h3 a fun τ => (key τ a).symm.trans (ha τ)⟩

end GlobalTheory.FockCompare

end
end
