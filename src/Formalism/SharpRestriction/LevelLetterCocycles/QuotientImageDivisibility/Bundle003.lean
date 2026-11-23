module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
import Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd

@[expose] public section

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section CritB

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem hasSubst_pi0_series (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries.HasSubst W.π₀₁ :=
  PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)

def at0Hom (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries O →+* LetA O n :=
  Pi.ringHom fun _ => (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)).toRingHom

theorem at0Hom_apply (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f : PowerSeries O) :
    at0Hom W hR f = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
  funext i
  show (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)) f = PowerSeries.subst W.π₀₁ f
  rw [PowerSeries.coe_substAlgHom]

theorem evalZero_X_eq_pi0 (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  exact PowerSeries.subst_X (hasSubst_pi0_series W hR)

theorem evalZero_C (o : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C o) = algebraMap O (LetA O n) o := by
  funext i
  simp [Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0, PowerSeries.subst_C, PowerSeries.algebraMap_eq]
  rfl

theorem evalZero_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  rw [← at0Hom_apply W hR, ← at0Hom_apply W hR, ← at0Hom_apply W hR, map_mul]

theorem qp_unit_EE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπ₀ : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  obtain ⟨U, hU⟩ := hπ₀
  haveI := W.EE_complete
  have hJ : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
      (Ideal.subset_span (Set.mem_singleton _))
  have h1 : IsUnit (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) :=
    Ideal.mem_jacobson_bot.1 hJ _
  have e : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) =
      (U : W.EE) * (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (U : W.EE), mul_assoc, Units.mul_inv, mul_one, hU]
    simp [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast, add_comm]
  rw [e]
  exact U.isUnit.mul h1

theorem qp_pow_cancel (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (k : ℕ)
    {x y : W.DD T} (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = Formalism.MainNotions.LiftingTheory.qp W ^ k • y) : x = y := by
  have hu : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k)) := by
    rw [map_pow]; exact (qp_unit_EE W hR).pow _
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x,
    ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) y] at h
  exact hu.smul_left_cancel.1 h

end CritB

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

def GenUnitsC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤

section Parts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤

end Parts

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
end
end
