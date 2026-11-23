module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD
public import Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle018
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle025
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle791
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle018
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

@[expose] public section

section



section
noncomputable section
namespace GlobalTheory.SerSys
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
variable {g : ℕ} [Fact g.Prime]
local instance  (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
def LocalCompatibility (D : D7) (rc : Corr D) : Prop :=
  (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) ∧
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ),
    TamePart μ χ ∧ D.naut.locG (D.naut.muC i) (D.naut.plGw k v) = rc k v 1 (Rep.of (Model.detRep 1 μ)) ∧
    ∀ P : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧
      D.naut.locV i P (D.naut.plGw k v) = rc k v D.R.nV π ∧
      ActsThrough π D.R.r D.R.t χ (D.naut.typeV i P) fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v a)
namespace Loc
section Det
end Det
end Loc
end GlobalTheory.SerSys
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open GlobalTheory.TameRecord
theorem tame_param_le_of_tame_coupled : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ (L : ∀ k, LabelDatum (D.host.g k)) (k : Fin 2) (v : D.nd.PlG k) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen → DiscreteGroups.sglob.DzType.Rt.TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hDZ hL D T I rc hrc L k v κ hκ ρ hb hρ τ P hP hinf
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, π⟩ := ρ
  have hs : GlobalTheory.PRep.IsSmooth π.ρ := hρ.2.2.1
  set σ := transRep I k v π hρ.2.1 hs
  have hsc : GlobalTheory.PRep.IsSupercuspidal σ.ρ :=
    isSupercuspidal_comp π.ρ _ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)
      (continuous_glMap _ (continuous_symm _ (I.i k v) (I.cont k v))) (continuous_glMap _ (I.cont k v))
      (glMap_apply_symm (I.i k v)) (glMap_symm_apply (I.i k v)) hρ.2.2
  have hcusp : (GlobalTheory.LocLanglands.cls σ).IsCusp := GlobalTheory.LocGL.IrrGL.isCusp_of.2 ⟨hρ.1, GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal _ n _ σ.ρ hsc⟩
  have hinf' : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)) τ := by
    rw [transRep_comp]; exact hinf
  show D.naut.inePol (rc k v n π) (D.ntypes.tg k v) = _
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), hrc k v n σ π (iso_pull I k v π hρ.2.1 hs)]
  exact hDZ D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) (I.i k v) (I.cont k v) κ (L k) _ (D.ntypes.tg_mem k v) hκ n (Or.inr (DiscreteGroups.sglob.DzType.big_of_le_nV D k hb)) σ hcusp
    τ P hP hinf'
end DiscreteGroups.sglob.DzType.Rt
end
end
end
