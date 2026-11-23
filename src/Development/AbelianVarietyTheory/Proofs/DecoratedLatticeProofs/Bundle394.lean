module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

variable {D : D7}

theorem rank_Yc_le_succ (j : ℕ) : (Yc D j).rank ≤ (Yc D (j + 1)).rank := by
  rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.Y_rank _ (min_le_right _ _)]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_min_right D.R.m (Nat.le_succ j))) _

end GlobalTheory.BaseChain

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseChain

def levAt {D : D7} {T : Type} (L : LevCh D T) (t : T) : LevCh D Unit :=
  { L with xiH := fun _ => L.xiH t, xi := fun _ => L.xi t, Q := fun _ => L.Q t, xiR := fun _ => L.xiR t }

theorem levAt_is {D : D7} {T : Type} {L : LevCh D T} {t : T} (h : L.Is t) : (levAt L t).Is () :=
  { mu0 := h.mu0, eta := h.eta, xi := fun _ => h.xi t, xi_inj := fun _ _ _ => rfl, xi_base := h.xi_base,
    xi_fin := fun _ => h.xi_fin t, xi_triv := fun _ => h.xi_triv t, xi_tame := fun _ => h.xi_tame t, Pg := h.Pg,
    Q_pl := fun _ => h.Q_pl t, Q_off := fun _ => h.Q_off t,
    Q_de := fun p hp => (h.Q_de p hp).imp fun _ H _ => H t,
    Q_ram := fun _ => h.Q_ram t, chi := h.chi, xiR := fun _ => h.xiR t, βY := h.βY, βX := h.βX, βV := h.βV, βW := h.βW }

theorem chrEq_mu_base {D : D7} {T : Type} {L : LevCh D T} {t : T} (h : L.Is t) (j : Fin D.R.m) :
    ChrEq (L.mu t ((j : ℕ) + 1)) (L.C.mu0 j) := by
  have h1 := GlobalTheory.Mem.TupChar.chrEq_mul (h.mu0 j) (h.xi t)
  rw [h.xi_base, mul_one] at h1
  exact h1

end GlobalTheory.BaseChain
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP.IoLevPf

theorem multT_val {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : SmT M) :
    (∀ γ ∈ GQ V, ∀ g, u v (γ * g) = u v g) ∧ ∀ k ∈ J, ∀ g, u v (g * k) = χ k * u v g := by
  have h1 := (mem_multT θ M J χ u).1 hu
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h2 := GlobalTheory.mult_value_left_cont_level θ M J χ _ h1 f
    have h3 : ∀ g, u (PiTensorProduct.tprod ℂ f) g = (PiTensorProduct.lift.symm u) f g := fun g => by simp
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.1 γ hγ g]
    · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h3, h3, h2.2.2 k hk g, smul_eq_mul, smul_eq_mul]
      ring
  | add x y hx hy =>
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_⟩
    · rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx.1 γ hγ g, hy.1 γ hγ g]
    · rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx.2 k hk g, hy.2 k hk g]
      ring

end GlobalTheory.StepLevelP.IoLevPf

namespace GlobalTheory.StepLevelP


end GlobalTheory.StepLevelP

end
end
