module

public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle224
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle159
import Formalism.LocalToGlobal.IndefiniteReal.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle292
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle294
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle297
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.Divisibility.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.flagPairingVectors_integral_inFrame : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β₀ : GL (Fin (Yc D 0).rank) (EAf D)), Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 = GlobalTheory.NormSum.AdLattice.lat β₀ → ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank), ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjRead.flag_pair_int | exact GlobalTheory.SeeConjRead.flag_pair_int | (intros; apply GlobalTheory.SeeConjRead.flag_pair_int <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.residue_idempotent_conj_at_levelPlace : ∀ {D : D7} (g : ℕ) (ew : (II D).E ⊗[(II D).F] Af (II D).F), ew * ew = ew → ew * sigA (II D) ew = 0 → ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → (∀ y ∈ (II D).Lf, (1 - ew - sigA (II D) ew) • y ∈ mL (II D) g) → ∀ PP : Pl D.host.E, ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ (h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h2 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (GlobalTheory.StdFrames.cpt PP ew = 1 → resS D.host.F PP ⟨ew, h1⟩ = 1 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 0) ∧ (GlobalTheory.StdFrames.cpt PP ew ≠ 1 → resS D.host.F PP ⟨ew, h1⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) ew, h2⟩ = 1) := by
  first | exact @GlobalTheory.SeeConjIdem.resS_idem_conj | exact GlobalTheory.SeeConjIdem.resS_idem_conj | (intros; apply GlobalTheory.SeeConjIdem.resS_idem_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.exists_frame_lifting_prescribed_reductions : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (S : Finset (Pl D.host.E)) (W : Pl D.host.E → Fin n → Fin n → EAf D), (∀ Q ∈ S, ∀ i j, ((β₀⁻¹).val * colMat (W Q)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ Q ∈ S, Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (W Q)).det) = 1) → ∃ β : GL (Fin n) (EAf D), GlobalTheory.NormSum.AdLattice.lat β = GlobalTheory.NormSum.AdLattice.lat β₀ ∧ ∀ Q ∈ S, RedIs β Q (W Q) := by
  first | exact @GlobalTheory.SeeConjRead.exists_lift_redIs | exact GlobalTheory.SeeConjRead.exists_lift_redIs | (intros; apply GlobalTheory.SeeConjRead.exists_lift_redIs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.flagPairingTable_idempotentComponent_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  first | exact @GlobalTheory.SeeConjRead.pairTable_of_cpt_one | exact GlobalTheory.SeeConjRead.pairTable_of_cpt_one | (intros; apply GlobalTheory.SeeConjRead.pairTable_of_cpt_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.residue_conjugatePlace_hermitianForm_adjoint : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) (κ : GA D (Yc D 0)) (x y : Fin (Yc D 0).rank → EAf D), (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y)) = GlobalTheory.SeeConjChar.conjRes PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x))) := by
  first | exact @GlobalTheory.SeeConjAdj.resCP_adjoint | exact GlobalTheory.SeeConjAdj.resCP_adjoint | (intros; apply GlobalTheory.SeeConjAdj.resCP_adjoint <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.flagPairingTable_idempotentComponent_ne_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  first | exact @GlobalTheory.SeeConjRead.pairTable_rev | exact GlobalTheory.SeeConjRead.pairTable_rev | (intros; apply GlobalTheory.SeeConjRead.pairTable_rev <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.divisibility_typeProduct_read_levelPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsGrp F → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ (c : EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc' : sigA (II D) c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ R.Pg, resS D.host.F PP ⟨c, hc⟩ = 0 ∧ resS D.host.F PP ⟨sigA (II D) c, hc'⟩ = 0) → ZMod' (II D) (D.host.g 0 * D.host.g 1) c := by
  first | exact @GlobalTheory.SeeConjZMod.main | exact GlobalTheory.SeeConjZMod.main | (intros; apply GlobalTheory.SeeConjZMod.main <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.RowsNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K G X H E : Type} [Field K] [Group G] [Fintype G] [AddCommGroup X] [Module K X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]


omit [Fintype G] in
theorem mem_range_adjoint (ρ : Representation ℂ G H) (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E)
    (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖) (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y)) (g : G) {y : H}
    (hy : y ∈ LinearMap.range (LinearMap.adjoint Θ)) : ρ g y ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  rw [← LinearMap.orthogonal_ker, Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  have h1 : ρ g (ρ g⁻¹ u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have h2 : inner ℂ (ρ g (ρ g⁻¹ u)) (ρ g y) = inner ℂ (ρ g⁻¹ u) y := LinearIsometry.inner_map_map ⟨ρ g, hρ g⟩ _ _
  rw [← h1, h2]
  refine hy _ ?_
  rw [LinearMap.mem_ker] at hu ⊢
  rw [hΘ, hu, map_zero]

theorem exists_rational {σ : K →+* ℂ} (j : X →ₛₗ[σ] H) (r : Representation K G X) (ρ : Representation ℂ G H)
    (π : Representation ℂ G E) (Θ : H →ₗ[ℂ] E) (hj : ∀ g z, j (r g z) = ρ g (j z)) (hρ : ∀ g y, ‖ρ g y‖ = ‖y‖)
    (hΘ : ∀ g y, Θ (ρ g y) = π g (Θ y))
    (hrat : LinearMap.range (LinearMap.adjoint Θ) ≤
      Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}))
    (a b : G → K) {x u : E} (hx : x ≠ 0) (hu : Θ (LinearMap.adjoint Θ u) = x)
    (ha : ∑ g, σ (a g) • π g x = x) (hb : ∑ g, σ (b g) • π g x = x) :
    ∃ z, (∑ g, a g • r g) ((∑ g, b g • r g) z) ≠ 0 ∧
      j ((∑ g, a g • r g) ((∑ g, b g • r g) z)) ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  have hop : ∀ (c : G → K) z, j ((∑ g, c g • r g) z) = ∑ g, σ (c g) • ρ g (j z) := fun c z => by

    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hj]
  have hst : ∀ (c : G → K) z, j z ∈ LinearMap.range (LinearMap.adjoint Θ) →
      j ((∑ g, c g • r g) z) ∈ LinearMap.range (LinearMap.adjoint Θ) := fun c z hz => by
    rw [hop]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (mem_range_adjoint ρ π Θ hρ hΘ g hz)
  have hth : ∀ (c : G → K) z, Θ (j ((∑ g, c g • r g) z)) = (∑ g, σ (c g) • π g) (Θ (j z)) := fun c z => by
    rw [hop]

    simp only [map_sum, map_smul, hΘ, LinearMap.sum_apply, LinearMap.smul_apply]
  by_contra hn
  push Not at hn
  have hker : Submodule.span ℂ (j '' {z | j z ∈ LinearMap.range (LinearMap.adjoint Θ)}) ≤
      LinearMap.ker ((∑ g, σ (a g) • π g) ∘ₗ (∑ g, σ (b g) • π g) ∘ₗ Θ) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    have h0 : (∑ g, a g • r g) ((∑ g, b g • r g) z) = 0 := by
      by_contra h0
      exact hn z h0 (hst a _ (hst b z hz))
    show (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (j z))) = 0
    rw [← hth, ← hth, h0, map_zero, map_zero]
  have h1 : (∑ g, σ (a g) • π g) ((∑ g, σ (b g) • π g) (Θ (LinearMap.adjoint Θ u))) = 0 := hker (hrat ⟨u, rfl⟩)
  simp only [hu, LinearMap.sum_apply, LinearMap.smul_apply, hb, ha] at h1
  exact hx h1


omit [FiniteDimensional ℂ E] in
theorem sum_lvlIdem {σ : K →+* ℂ} (π : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) {x : E}
    (hx : ∀ g : P, π (g : G) x = σ ((ψ g : Kˣ) : K) • x) : ∑ g, σ ((lvlIdem P ψ).coeff g) • π g x = x := by
  classical
  have hc : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h1 : ∀ (h : G) (c : K), ∑ g, σ ((MonoidAlgebra.single h c).coeff g) • π g x = σ c • π h x := fun h c => by
    rw [Finset.sum_eq_single h]
    · simp
    · intro g _ hg
      simp [Finsupp.single_eq_of_ne hg]
    · simp
  have h2 : ∀ h : P, σ ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • π (h : G) x = (Nat.card P : ℂ)⁻¹ • x := fun h => by
    rw [hx h, smul_smul, ← map_mul, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one,
      map_inv₀, map_natCast]
  unfold lvlIdem

  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [h1, h2, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Nat.card_eq_fintype_card, mul_inv_cancel₀ hc, one_smul]

end Abstract

section Hecke

open GlobalTheory.HeckeModel GlobalTheory.SphericalOps

variable {D : D7}

variable {V : HSp D} {S : D.what₂.Tau → SPar} {β : GL (Fin V.rank) (Lev.EAf D)}

end Hecke

section Rows

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem dZ_pos {K : Type} [Field K] [NumberField K] [StarRing K] (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)
    {z : B.S.Forms} (h0 : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ≠ 0)
    (hZ : B.S.gaOp B.r (idemOf ℓ.X) (B.S.gaOp B.r (lvlIdem ℓ.P ℓ.ψ) z) ∈ Z) : 0 < B.dZ ℓ Z := by
  rw [← B.gaOp_mul, ← goodAt] at h0 hZ
  have hV : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  obtain ⟨u, hu⟩ : B.S.basis.equivFun (B.S.gaOp B.r (goodAt ℓ.X ℓ.P ℓ.ψ) z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
    rw [hV]
    exact ⟨B.S.basis.equivFun z, by rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun]⟩
  rw [Matrix.mulVecLin_apply] at hu
  refine Nat.pos_of_ne_zero fun h => h0 ?_
  have h1 : u ∈ B.Z0 ℓ Z := by
    rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
    exact hZ
  rw [Submodule.finrank_eq_zero.1 h, Submodule.mem_bot] at h1
  rw [h1, Matrix.mulVec_zero] at hu
  exact B.S.basis.equivFun.map_eq_zero_iff.1 hu.symm

end Rows

end GlobalTheory.RowsNonzero

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.InertEigScalar

theorem conjIdeal_eq_of_conjPl {D : D7} (P : Pl D.host.E) (hc : Formalism.DivisionValues.conjPl P = P) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal := by
  have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    show _ = Ideal.span _
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hr⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change _ = (algebraMap (𝓞 D.host.E) D.host.E r)
      rw [hr]
      rfl
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [h1]
  exact congrArg HeightOneSpectrum.asIdeal hc



theorem inert_label_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → Formalism.DivisionValues.conjPl P = P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC _hEx _hH _hPG j c h hh _hN P hP hc d hd
  have hlab := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) P d).1 hd
  obtain ⟨s', hs2, hsp, hspos, rfl⟩ :=
    (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank d).1 ⟨hlab.1, hlab.2.1, hlab.2.2 hc⟩
  have hPg : P ∉ R.Pg := fun hm => (hP P (Or.inl hm)).1 rfl
  have hPQ : P ∉ R.Q A3.A.fam.μ0 := fun hm => (hP P (Or.inr hm)).1 rfl
  have hfix := conjIdeal_eq_of_conjPl P hc
  have hSb : P ∉ R.Sb := by
    have e : R.Sb = R.Pg := hC.allPl
    rw [e]; exact hPg
  have hoff : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := ⟨hfix, fun hm => hSb (Finset.mem_coe.1 hm)⟩
  have honto : R.in_onto := hC.inert.onto
  have hex : ∃ Q, R.plI Q = P := honto P hoff
  obtain ⟨Q, hQ⟩ := hex
  have hQok : Q ∈ A3.okI A3.A.fam.μ0 := by
    refine (hC.inert.tie.okI A3.A.fam.μ0 Q).2 ⟨?_, ?_⟩
    · rw [hQ]; exact hfix
    · rw [hQ, hC.allPl]
      simp only [Set.mem_union, Finset.mem_coe]
      tauto
  subst hQ
  have hLt : R.in_L := hC.inert.hL
  have hn := hLt j A3.A.fam.μ0
  obtain ⟨Comparison₂⟩ := hn
  let inR' : ↥(A3.okI A3.A.fam.μ0) × List ℕ → Prop :=
    fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 ∧ R.plI k.1 = R.plI Q
  let Tie' : Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j A3.A.fam.μ0).pres (A3.heckeLI j A3.A.fam.μ0) inR'
      (fun k => GlobalTheory.Hk3.IsLabElt (Vc D j) (R.plI k.1) (GlobalTheory.Hk3.labIn (Vc D j).rank k.2))
      (fun k => GlobalTheory.Hk3.IsLocElt (Vc D j) (R.plI k.1)) :=
    { hx := Comparison₂.hx, hA := Comparison₂.hA, hx_ok := fun i hi => Comparison₂.hx_ok i hi.1, hA_loc := fun i hi => Comparison₂.hA_loc i hi.1,
      chi_loc := fun i hi => Comparison₂.chi_loc i hi.1, hDC := fun i hi => Comparison₂.hDC i hi.1, op_eq := fun i hi => Comparison₂.op_eq i hi.1 }
  let k : ↥(A3.okI A3.A.fam.μ0) × List ℕ := (⟨Q, hQok⟩, s')
  have hk : inR' k := ⟨⟨hsp, hspos, hs2⟩, rfl⟩
  have hin : ∀ i, inR' i → GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 (R.plI i.1) ∧ Formalism.DivisionValues.conjPl (R.plI i.1) = R.plI i.1 ∧
      (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    rintro ⟨Q', t'⟩ ⟨hty, hpl⟩
    simp only at hpl ⊢
    rw [hpl]
    exact ⟨hP, hc, ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨t', hty.2.2, hty.1, hty.2.1, rfl⟩).2.1⟩
  have key := (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models j
    A3.A.fam.μ0 _ (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.fam.μ0) inR'
    hin Tie' k hk).2.2.2 h hh
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hC.base.models
  have hop : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s') 1)) := by
    apply LinearMap.ext_on_range (hK j A3.A.fam.μ0).2
    intro b
    rw [← Formalism.IndefR.Cx.CxData.jL_opL (R.toCx3 F) hK]
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j A3.A.fam.μ0 (A3.heckeLI j A3.A.fam.μ0 k _)) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) _ (R.jV j A3.A.fam.μ0 _))
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (key _)
  refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inr k)), fun x hx => ?_⟩
  have hx' : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) x = c (Sum.inr k) • x :=
    (Formalism.IndefR.U2.mem_eigPart.1 hx) (Sum.inr k)
  rw [hop] at hx'
  exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0)) hx'

end GlobalTheory.InertEigScalar
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix


theorem _root_.GlobalTheory.T.finiteMatrix_iota_eq_finitePart : ∀ {D : D7} (κ : GA D (Yc D 0)), (GlobalTheory.SeeConjGroup.II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := by
  first | exact @GlobalTheory.SeeConjGroup.fmat_iota_eq_finE | exact GlobalTheory.SeeConjGroup.fmat_iota_eq_finE | (intros; apply GlobalTheory.SeeConjGroup.fmat_iota_eq_finE <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta

theorem GlobalTheory.HeckeDC.exists_rep : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))) (e : AE D) (ϖ : 𝓞 D.host.E) (a₀ : GA D (Wc D i)),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt (Wc D i) e (ϖ : D.host.E) k a₀ →
    ∃ a ∈ Rc, a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc e ϖ a₀ hso hα hRc he hϖ hϖ2 ha₀
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨Lp, -, -, -, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨e', ϖ', he', h1', h2', hαe'⟩ := hα
  have hee : e' = e := idem_unique (Wc D i) he he'
  rw [hee] at hαe'
  obtain ⟨-, -, hloc⟩ := GlobalTheory.SplitPlace.split_local (Wc D i) P e he
  obtain ⟨x, hx, y, hy, hxy⟩ := ((hloc ϖ' h1' h2').2 k α hαe').2 ϖ a₀ hϖ hϖ2 ha₀
  obtain ⟨a, ⟨haR, haK⟩, -⟩ := hRc.2 a₀ ⟨⟨x, ((hK x).1 hx).1⟩, ⟨y, ((hK y).1 hy).1⟩, hxy⟩
  exact ⟨a, haR, haK⟩
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicitySpace_eq_zero_of_apply_nonzero_tensor_zero : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 → ∀ u ∈ MultT θ M J χ, ∀ x : ⨂[ℂ] τ, M.sm τ, x ≠ 0 → u x = 0 → u = 0 := by
  first | exact @GlobalTheory.multT_eq_zero_of_apply_eq_zero | exact GlobalTheory.multT_eq_zero_of_apply_eq_zero | (intros; apply GlobalTheory.multT_eq_zero_of_apply_eq_zero <;> assumption)
end
