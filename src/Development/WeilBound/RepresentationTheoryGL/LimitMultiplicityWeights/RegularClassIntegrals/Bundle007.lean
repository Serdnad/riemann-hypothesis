module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ArchUnimod
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle557
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle690
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle686
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle660
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing GlobalTheory.Proof.parabolic_and_constant_term
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem MainStatements.WeightKernel.cuspAny : MainStatements.WeightKernel.CuspAny := by
  intro D V hodd T U hNoFixed μf hμf ff hff fa hA 𝔉 hP
  have := hμf
  have hH := (GlobalTheory.T.typeHypothesis_forms_agree D V T hNoFixed).1
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
  exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
    ν x y).2

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay.NearCusp
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem nearCusp : NearCusp := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW Cm c U hCm hc hU s
  have hσ := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2
  let Cf : Set (GFin σ J) := (fun z : GAd σ J => projFin σ J z) '' Cm
  have hCf : IsCompact Cf := hCm.image (continuous_projFin σ J)
  let Uf : Set (GFin σ J) := ofFin σ J ⁻¹' (U : Set (GAd σ J))
  have hUf : Uf ∈ 𝓝 (1 : GFin σ J) :=
    (hU.preimage (continuous_ofFin σ J)).mem_nhds (by simp only [Set.mem_preimage, map_one]; exact U.one_mem)
  let Wn : Set (GFin σ J) := {x | ∀ h ∈ Cf, h⁻¹ * x * h ∈ Uf}
  have hWn : Wn ∈ 𝓝 (1 : GFin σ J) := conj_mem_nhds hCf hUf
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.T.unipotent_radical_compact_fundamental_domain F E σ hCM n J hJ _ (pre X s) hC Wn hWn
  obtain ⟨M₁, hM₁, hM₁b⟩ := GlobalTheory.T.torus_conjugate_unipotent_bounded F E σ hCM n J hJ r X Y hW Q c hQ hc s
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_archMat (σ := σ) (J := J) hCm
  refine ⟨C₀ * M₁, mul_nonneg hC₀ hM₁, ?_⟩
  intro t ht a ha k hk m hm
  obtain ⟨γ, hγ, q, hqQ, hqU, hqW, rfl⟩ := hQm m hm
  have hγU : γ ∈ unipRad σ J (pre X s) := by
    have := mul_mem hm (inv_mem hqU)
    rwa [mul_inv_cancel_right] at this
  have hfa : projFin σ J a = 1 := mem_infPts.1 ha.1
  refine ⟨γ, ⟨hγ, hγU⟩, ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))),
    ofFin σ J (projFin σ J ((a * k)⁻¹ * q * (a * k))), ⟨mem_infPts.2 (projFin_ofInf σ J _), ?_⟩, ?_,
    mem_finPts.2 (projInf_ofFin σ J _), ?_⟩
  · intro w τ i j
    have hN := hM₁b q hqQ hqU t ht a ha w τ
    have ev : (a * k)⁻¹ * q * (a * k) = k⁻¹ * (a⁻¹ * q * a) * k := by group
    have hB : archMat σ J τ (projArch σ J w k⁻¹) * archMat σ J τ (projArch σ J w k) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have key : archMat σ J τ (projArch σ J w (ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))))) - 1 =
        archMat σ J τ (projArch σ J w k⁻¹) * (archMat σ J τ (projArch σ J w (a⁻¹ * q * a)) - 1) *
          archMat σ J τ (projArch σ J w k) := by
      rw [projArch_ofInf, projInfArch_projInf, ev, map_mul (projArch σ J w) _ k, map_mul (projArch σ J w) k⁻¹,
        map_mul (archMat σ J τ), map_mul (archMat σ J τ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB]
    rw [key]
    refine (GlobalTheory.CuspGeo.norm_mul_mul_apply_le _ _ _ _ hN i j).trans ?_
    rw [mul_div_assoc C₀]
    exact mul_le_mul_of_nonneg_right (hC₀b k hk w τ i j) (div_nonneg hM₁ (ratio_pos ht s).le)
  · have hh : projFin σ J k ∈ Cf := ⟨k, hk, rfl⟩
    have e : projFin σ J ((a * k)⁻¹ * q * (a * k)) =
        (projFin σ J k)⁻¹ * projFin σ J q * projFin σ J k := by
      simp only [map_mul, map_inv, hfa, one_mul]
    have := hqW _ hh
    rw [← e] at this
    exact this
  · rw [mul_assoc (γ * (a * k)), ofInf_projInf_mul_ofFin_projFin]
    group

end MainStatements.WeightKernel.Dec
end
end
