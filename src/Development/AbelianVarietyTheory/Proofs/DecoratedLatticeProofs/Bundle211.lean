module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Aesop.Main
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle364
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsGlOfEquiv

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

theorem symplOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem symplOH_zero_left (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

theorem heis_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (a : WO B.A S)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ B.A S a (fun u' => contr l S vL f₁ f₂ u' v) u =
      contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) f₁) f₂ u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B.o.resS S).symm (u, l.κ S w) + (B.o.resS S).symm (a, 0) = (B.o.resS S).symm (u + a, l.κ S w) := by
    rw [← map_add (f := _)]; simp
  rw [B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

theorem heis_right {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (l : Link B B'.L B'.ζ)
    (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) (b : WO S B'.A)
    (u : WO B.A S) (v : WO S B'.A) :
    heisO ψ S B'.A b (contr l S vL f₁ f₂ u) v =
      contr l S vL f₁ (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) f₂) u v := by
  simp only [heisO, contr]
  rw [← integral_const_mul]
  congr 1
  funext w
  have h1 : (B'.o.resT S).symm (v, w) + (B'.o.resT S).symm (b, 0) = (B'.o.resT S).symm (v + b, w) := by
    rw [← map_add (f := _)]; simp
  rw [B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_right, add_zero, h1]
  ring

end GlobalTheory.ContrComb
end

noncomputable section
namespace GlobalTheory.ContrComb

variable {D : D7}

def extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO A S →+ WO V₀ S :=
  (o.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

def extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : WO S A →+ WO S V₀ :=
  (o.resT S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem extL_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) : extL (S := S) o u = (o.resS S).symm (u, 0) := rfl

theorem extR_apply {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) : extR (S := S) o u = (o.resT S).symm (u, 0) := rfl

theorem continuous_extL {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extL (S := S) o) :=
  (o.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)

theorem continuous_extR {V₀ A L S : HSp D} (o : OrthDec V₀ A L) : Continuous (extR (S := S) o) :=
  (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)

theorem extL_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO A S) (h : u.map (infPart D) = 0) :
    (extL (S := S) o u).map (infPart D) = 0 := by
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change (u * o.pA).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.zero_mul]

theorem extR_inf {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (u : WO S A) (h : u.map (infPart D) = 0) :
    (extR (S := S) o u).map (infPart D) = 0 := by
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change (o.jA * u).map (infPart D) = 0
  rw [Matrix.map_mul, h, Matrix.mul_zero]

theorem extL_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO A S) (h : IsHalf e u) :
    IsHalf e (extL (S := S) o u) := by
  intro i j
  rw [extL_apply, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  change e * (u * o.pA) i j = (u * o.pA) i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i]

theorem extR_half {V₀ A L S : HSp D} (o : OrthDec V₀ A L) (e : AE D) (u : WO S A) (h : IsHalf e u) :
    IsHalf e (extR (S := S) o u) := by
  intro i j
  rw [extR_apply, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
  change e * (o.jA * u) i j = (o.jA * u) i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

end GlobalTheory.ContrComb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselQuot

theorem besGrp_quotient : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  intro D ρ B
  obtain ⟨-, hcl, hHaar⟩ := GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L ρ B.d B.o B.vN.ν B.vN.𝓝 B.vN.unit
  have hμR : B.μR.IsHaarMeasure := hHaar B.vA.μ B.vA.haar
  obtain ⟨hsc, hNcl, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨⟨KN, hKN, hKNcov⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (GlobalTheory.MixPer.isIsoSub_e B.d)
  obtain ⟨KA, hKA, hKAcov⟩ := B.cpt
  have hγA : ∀ γ ∈ GQ B.A, embA B.d B.o γ ∈ GQ B.V := fun γ hγ => by
    have h1 := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    simpa using h1
  set Ω : Set (GA D B.V) := (fun p : GA D B.V × GA D B.A => p.1 * embA B.d B.o p.2) '' ((Subtype.val '' KN) ×ˢ KA) with hΩ
  have hΩc : IsCompact Ω :=
    ((hKN.image continuous_subtype_val).prod hKA).image (continuous_fst.mul (hsc.comp continuous_snd))
  have hΩsub : Ω ⊆ (besGrp B.d B.o : Set (GA D B.V)) := by
    rintro _ ⟨⟨_, a⟩, ⟨⟨k, hk, rfl⟩, -⟩, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hcov : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω := by
    intro s hs
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s).1 hs
    obtain ⟨γA, hγAQ, hγAK⟩ := hKAcov a
    have hn1 : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ ∈ flagN B.d := hnorm n hn γA
    obtain ⟨γN, hγN, k, hk, he⟩ := hKNcov ⟨_, hn1⟩
    have he' : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ = γN.1 * k.1 := congrArg Subtype.val he
    have hk1 : k.1 = γN.1⁻¹ * (embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹) := eq_inv_mul_of_mul_eq he'.symm
    have hQ : γN.1⁻¹ * embA B.d B.o γA ∈ GQ B.V :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hγN)) (hγA γA hγAQ)
    have hR : γN.1⁻¹ * embA B.d B.o γA ∈ besGrp B.d B.o :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left γN.2)) (Subgroup.mem_sup_right ⟨γA, rfl⟩)
    refine ⟨γN.1⁻¹ * embA B.d B.o γA, Subgroup.mem_inf.2 ⟨hQ, hR⟩, ?_⟩
    refine ⟨(k.1, γA * a), ⟨⟨k, hk, rfl⟩, hγAK⟩, ?_⟩
    simp only [hk1, map_mul]
    group
  have hcovA : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ k ∈ KA, g = γ * k := fun g => by
    obtain ⟨γ, hγ, hk⟩ := hKAcov g
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, γ * g, hk, by group⟩
  have := B.vA.haar
  have hFfin : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hKA hcovA B.vA.μ B.vA.fund
  have hNfin : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  obtain ⟨𝓡, hfd, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hsc hNcl hnorm huniq hrat B.vA
    B.vN.ν B.vN.𝓝 B.vN.unit.1 B.vN.unit.2.1 hμR
  have : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hFfin.ne
  have : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hNfin.ne
  refine ⟨hμR, hcl, ⟨Ω, hΩc, hcov⟩, 𝓡, ?_, ?_, ?_⟩
  · rw [← Subgroup.inf_subgroupOf_right]; exact hfd
  · have h1 := (hint (fun _ => (1 : ℂ)) measurable_const).1.2 (integrable_const _)
    exact ((integrableOn_const_iff).1 h1).resolve_left (by simp)
  · intro F hF hinv
    classical
    set F' : GA D B.V → ℂ := (besGrp B.d B.o : Set (GA D B.V)).piecewise F 0 with hF'
    have hF'm : Measurable F' := hF.measurable_piecewise continuousOn_const hcl.measurableSet
    obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn (hF.mono hΩsub)
    have hb : ∀ x, ‖F' x‖ ≤ max C 0 := by
      intro x
      by_cases hx : x ∈ (besGrp B.d B.o : Set (GA D B.V))
      · obtain ⟨γ, hγ, hγx⟩ := hcov x hx
        rw [hF', Set.piecewise_eq_of_mem _ _ _ hx, ← hinv γ hγ x hx]
        exact (hC _ hγx).trans (le_max_left _ _)
      · rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; simp
    have hAC : AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h n => F' (n.1 * embA B.d B.o h) := by
      refine Integrable.of_bound ?_ (max C 0) (Filter.Eventually.of_forall fun p => hb _)
      exact (hF'm.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hsc.comp continuous_fst)).measurable).aestronglyMeasurable
    have hpt : ∀ r : ↥(flagN B.d ⊔ (embA B.d B.o).range), F' r = F r := fun r => Set.piecewise_eq_of_mem _ _ _ r.2
    have hpt2 : ∀ a (n : flagN B.d), F' (n.1 * embA B.d B.o a) = F (n.1 * embA B.d B.o a) := fun a n =>
      Set.piecewise_eq_of_mem _ _ _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨a, rfl⟩))
    obtain ⟨hi1, hi2⟩ := hint F' hF'm
    have e1 : (fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F' r) =
        fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F r := funext hpt
    have e2 : (fun a => ∫ n in B.vN.𝓝, F' (n.1 * embA B.d B.o a) ∂B.vN.ν) =
        fun a => ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν := funext fun a => by simp only [hpt2]
    refine ⟨?_, ?_⟩
    · have h3 := hi1.2 hAC
      rw [e1] at h3
      exact h3
    · have h3 := hi2 hAC
      rw [e1, e2] at h3
      exact h3

end GlobalTheory.BesselQuot
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem doubleSum_eq_dotProduct_mapMatrix_mulVec {R K : Type*} [CommRing R] {m n : ℕ} (g : R → R) (f : K → R)
    (s : Fin m → R) (G : Matrix (Fin m) (Fin n) K) (v : Fin n → R) :
    (∑ i, ∑ j, g (s i) * f (G i j) * v j) = (fun i => g (s i)) ⬝ᵥ (G.map f *ᵥ v) := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem ringHom_conjTranspose_smul_dotProduct_adjoint {R : Type*} [CommRing R] {m n : ℕ} (σ : R →+* R) (c : R)
    (s : Fin m → R) (Y : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin n) (Fin n) R)
    (a : Fin n → R) :
    (fun i => σ (s i)) ⬝ᵥ ((c • ((Y.map σ)ᵀ * G)) *ᵥ a)
      = c * ((fun k => σ ((Y *ᵥ s) k)) ⬝ᵥ (G *ᵥ a)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 2
  funext k

  simp [vecMul, mulVec, dotProduct, map_sum, map_mul, mul_comm]



theorem kappa_adj : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  intro D ρ B L' ζ' l S x a s
  simp only [Link.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  have hG : gA S * giA S = 1 := by
    have h := Matrix.mul_nonsing_inv (HSpace.gram S) (gram_isUnit_det S)
    have h2 : (HSpace.gram S * (HSpace.gram S)⁻¹).map (incA D)
        = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) := by rw [h]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  rw [doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D) s, doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D)]
  rw [show (HSpace.gram S).map (incA D) = gA S from rfl,
    show (HSpace.gram B.L).map (incA D) = gA B.L from rfl]
  have hG' : ∀ N : Mx D S.rank B.L.rank, HMul.hMul (gA S) (HMul.hMul (giA S) N) = N := by
    intro N
    rw [← Matrix.mul_assoc, hG]
    exact Matrix.one_mul N
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, hG']
  exact ringHom_conjTranspose_smul_dotProduct_adjoint (cA D) _ s _ _ a

end GlobalTheory
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIrred

theorem prod_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (v : VolM D T.rank S.rank)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (horth : ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) (u x : WO S T) :
    f x * star (heisO ψ S T u g x) = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hμ : v.μ.IsAddHaarMeasure := v.covol.1
  have h𝓕 : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hu := hth u g hg
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    v.μ v.𝓕 hμ h𝓕 (fun x => f x * star (heisO ψ S T u g x))
    (hf.cont.mul hu.cont.star)
    (fun γ hγ x => GlobalTheory.ThetaSchur.prod_periodic hψ hf hu hγ x)
    (fun γ => by
      have hneg : ∀ x, symplO S T x ((-γ : ratL T S) : WO S T) = -symplO S T x (γ : WO S T) := by
        intro x
        have h0 := l2 x (γ : WO S T) (-(γ : WO S T))
        rw [add_neg_cancel, GlobalTheory.WeilVacMove.symplOH_zero_right] at h0
        simp only [← l4, AddSubgroup.coe_neg]
        linear_combination (-2 : AF D.host.F) * h0
      have e : (fun x => ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x))) = fun x =>
          star (ψ (symplOH S T (-(γ : WO S T)) u)) * (f x * star (heisO ψ S T (-(γ : WO S T) + u) g x)) := by
        funext x
        have E := congrFun (hcomp (-(γ : WO S T)) u g) x
        rw [GlobalTheory.ThetaSchur.heisO_rat hu (neg_mem γ.2) x, Pi.smul_apply, smul_eq_mul] at E
        have E' := congrArg star E
        rw [star_mul', star_mul'] at E'
        have hs : star (ψ (-symplO S T x (γ : WO S T))) = ψ (symplO S T x (γ : WO S T)) := by
          have h1 := GlobalTheory.ThetaSchur.mul_star_psi hψ (-symplO S T x (γ : WO S T))
          have h2 : ψ (-symplO S T x (γ : WO S T)) * ψ (symplO S T x (γ : WO S T)) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination ψ (symplO S T x (γ : WO S T)) * h1 - star (ψ (-symplO S T x (γ : WO S T))) * h2
        have hn := hneg x
        simp only [AddSubgroup.coe_neg] at hn
        rw [hn] at E'
        linear_combination (f x) * E' - (f x * star (heisO ψ S T u g x)) * hs
      show ∫ x in v.𝓕, ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x)) ∂v.μ = 0
      rw [e, integral_const_mul]
      have := horth (-(γ : WO S T) + u)
      unfold thPair at this
      rw [this, mul_zero])
  exact congrFun key x

theorem eq_zero_of_orth_heis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  intro D ψ hψ S T v f g hf hg hg0 horth
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg0
  funext x
  have h := prod_eq_zero hψ v hf hg horth (y - x) x
  have hz : ψ (symplOH S T x (y - x)) ≠ 0 := fun h0 => by
    have := hψ.1.2.1 (symplOH S T x (y - x))
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  simp only [heisO, add_sub_cancel, star_mul'] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (star_eq_zero.1 h) hz
    · exact absurd (star_eq_zero.1 h) hy

end GlobalTheory.ThetaIrred

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf




namespace GlobalTheory.HaarCoordsUnit

theorem eq_of_rightInvariant_of_fundamentalDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] (ν m : Measure G) (𝓝 𝓕 : Set G)
    (h1 : ν.IsHaarMeasure) (h2 : IsFundamentalDomain Γ 𝓝 ν) (h3 : ν 𝓝 = 1) (k0 : SigmaFinite m) (k1 : m.IsMulRightInvariant)
    (k2 : IsFundamentalDomain Γ 𝓕 m) (k3 : m 𝓕 = 1) : m = ν := by
  open scoped Pointwise in
  haveI : ν.IsMulRightInvariant := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain Γ ν h2
    (by rw [h3]; exact one_ne_zero) (by rw [h3]; exact ENNReal.one_ne_top)
  have hinv : ν.inv 𝓝⁻¹ = 1 := by rw [Measure.inv_apply, inv_inv, h3]
  have e1 := measure_eq_div_smul m.inv ν.inv (s := 𝓝⁻¹) (by rw [hinv]; exact one_ne_zero) (by rw [hinv]; exact ENNReal.one_ne_top)
  rw [hinv, div_one, Measure.inv_apply, inv_inv] at e1
  set κ := m 𝓝 with hκ
  have e2 : m = κ • ν := by
    ext s -
    have := congrArg (fun μ : Measure G => μ s⁻¹) e1
    simpa only [Measure.inv_apply, inv_inv, Measure.smul_apply] using this
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at e2
    rw [e2] at k3
    simp at k3
  haveI : m.IsMulLeftInvariant := by rw [e2]; infer_instance
  have h2' : IsFundamentalDomain Γ 𝓝 m := h2.mono (by rw [e2]; exact Measure.smul_absolutelyContinuous)
  have h4 : m 𝓝 = 1 := (h2'.measure_eq k2).trans k3
  have hk1 : κ = 1 := by rw [hκ]; exact h4
  rw [e2, hk1, one_smul]

theorem volN_eq_map_coords : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → lC 𝓒 = 1 → vN.ν = (lC.prod (vb.μ.prod vU.ν)).map e := by
  intro D V V₀ ρ d vN vb vU e he lC 𝓒 hC hCs hCF hC1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hU, 𝓤, hU𝓤, hU1⟩ := vU.unit
  obtain ⟨hb, hbF, hb1⟩ := vb.covol
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨-, m2, m3, m4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨-, n2, n3, n4, -⟩ := lattice_Mx D ρ ρ
  haveI := vN.unit.1
  have hcl : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite lC := inferInstance
  haveI : SigmaFinite vb.μ := inferInstance
  haveI hSigmaU : SigmaFinite vU.ν := Measure.IsHaarMeasure.sigmaFinite vU.ν
  haveI : SFinite vU.ν := @MeasureTheory.instSFiniteOfSigmaFinite _ _ vU.ν hSigmaU
  haveI : SFinite (vb.μ.prod vU.ν) := Measure.prod.instSFinite
  haveI hm : SigmaFinite ((lC.prod (vb.μ.prod vU.ν)).map e) := e.sigmaFinite_map
  have hR := GlobalTheory.T.isMulRightInvariant_map_wittFlagCoordinates_haar D V V₀ ρ d vb vU e he lC hC hCs
  have hF := GlobalTheory.T.isFundamentalDomain_flagUnipotent_coords D V V₀ ρ d vb vU e he lC 𝓒 𝓤 hC hCs hCF hU𝓤
  have h1 : (lC.prod (vb.μ.prod vU.ν)).map e (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ 𝓤))) = 1 := by
    rw [MeasurableEquiv.map_apply, e.preimage_image, Measure.prod_prod, Measure.prod_prod, hC1, hb1, hU1, one_mul, one_mul]
  exact (eq_of_rightInvariant_of_fundamentalDomain (NFlagQ V d.e) vN.ν _ vN.𝓝 _ vN.unit.1 vN.unit.2.1 vN.unit.2.2 hm hR hF h1).symm

end GlobalTheory.HaarCoordsUnit

end
end
