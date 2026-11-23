module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

theorem _root_.GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (e : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (N : ℕ), 1 ≤ N →
    ∃ (C : ℝ) (k : ℕ), ∀ (g : GL (Fin n) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)), ∃ m : ℕ, 1 ≤ m ∧
      (m : ℝ) ≤ C * ((heightGL F g : ℝ) * heightGL F h) ^ k ∧ ∀ i j : κ,
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).1 j) ∧
        GlobalTheory.FinSupp.FinDiv F N ((m : AF F) *
          (e (((g⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * e.symm (0, Pi.single i 1) *
            (((h⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ)).2 j) := by
  first | exact @GlobalTheory.MovedLat.exists_scale | exact GlobalTheory.MovedLat.exists_scale | (intros; apply GlobalTheory.MovedLat.exists_scale <;> assumption)
end

section

noncomputable section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem lintegral_rhoBF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ) (u : WOF F E nS nT)
    (G : BBF σ JS JT ξ₀ ψ) :
    ∫⁻ w in 𝓕, ‖(rhoBF σ JS JT ξ₀ ψ hψ u G).1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖G.1 w‖ₑ ^ 2 ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have key : ∀ H : BBF σ JS JT ξ₀ ψ, ∫⁻ w in 𝓕, ‖H.1 w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ w in 𝓕, ‖H.1 w‖ ^ 2 ∂μ) := by
    intro H
    rw [ofReal_integral_eq_lintegral_ofReal _ (Filter.Eventually.of_forall fun w => by positivity)]
    · simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    · exact Integrable.of_bound (H.1.continuous.norm.pow 2).aestronglyMeasurable (‖H‖ ^ 2)
        (Filter.Eventually.of_forall fun w => by
          rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_ev_le w H) 2)
  rw [key, key, coe_rhoBF]
  simp only [norm_heisOF hψ]
  rw [GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕 (fun w => ‖G.1 w‖ ^ 2)
    (fun γ hγ w => by rw [BBF_norm_periodic hψ G γ hγ]) u]

theorem lintegral_eq_of_normsF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ), ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f f' : BBF σ JS JT ξ₀ ψ,
      (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ : BBF σ JS JT ξ₀ ψ →L[ℂ] H),
        (∀ w g, ‖Φ (rhoBF σ JS JT ξ₀ ψ hψ w g)‖ = ‖Φ g‖) → ‖Φ f'‖ = ‖Φ f‖) →
      ∫⁻ w in 𝓕, ‖f'.1 w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f.1 w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ μ 𝓕 hμ h𝓕 f f' hn
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hlt := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hc μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  rw [lintegral_norm_sq_eq_toL2, lintegral_norm_sq_eq_toL2, enorm_sq_inj]
  refine hn _ (toL2 _ _ (μ.restrict 𝓕)) fun v G => ?_
  rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
  exact lintegral_rhoBF hψ μ 𝓕 hμ h𝓕 _ G

end GlobalTheory.RealWeilF

end
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem exists_compact_cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) : ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

theorem continuous_rhoBF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := by
  intro f
  obtain ⟨K, hK, hc⟩ := exists_compact_cover F E nS nT
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let G : C(WOF F E nS nT × K, ℂ) := ⟨fun p => heisOF σ JS JT ξ₀ ψ p.1 f.1 p.2,
    (hψ.1.comp (continuous_symplOHF σ JS JT ξ₀ (continuous_subtype_val.comp continuous_snd) continuous_fst)).mul
      (f.1.continuous.comp ((continuous_subtype_val.comp continuous_snd).add continuous_fst))⟩
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (G.curry.continuous.tendsto w₀)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) h1)
  refine norm_QB_le _ (norm_nonneg _) fun x => ?_
  obtain ⟨γ, hγ, h⟩ := hc x
  rw [← BBF_norm_periodic hψ _ γ hγ]
  exact (G.curry w - G.curry w₀).norm_coe_le_norm ⟨γ + x, h⟩

end GlobalTheory.RealWeilF
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem exists_realZero_add_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E), IsChartF θ ι →
      ∀ w : WOF F E nS nT, ∃ (u : WOF F E nS nT) (v : IxF F nS nT → ℂ), u.map (infPartF F E) = 0 ∧ w = u + iotaVF ι v := by
  intro F E _ _ _ _ _ nS nT θ ι hι w
  refine ⟨w - iotaVF ι (piWF θ w), piWF θ w, ?_, by abel⟩
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  set a := infPartF F E ((w - iotaVF ι (piWF θ w)) i j) with ha
  have hθ : ∀ w', θ w' a = 0 := by
    intro w'
    rw [ha, Matrix.sub_apply, map_sub, map_sub]
    simp only [iotaVF, piWF, Matrix.of_apply]
    rw [hι.comp]
    exact sub_self _
  have h0 := hι.ext (Formalism.L2.Fam.ThC.pairE a 0) (Formalism.L2.Fam.ThC.snd_pairE a 0) (by
    intro w'
    have : infPartF F E (Formalism.L2.Fam.ThC.pairE a 0) = a := Formalism.L2.Fam.ThC.fst_pairE a 0
    rw [this]; exact hθ w')
  have : infPartF F E (Formalism.L2.Fam.ThC.pairE a 0) = a := Formalism.L2.Fam.ThC.fst_pairE a 0
  rw [← this, h0, map_zero]

end GlobalTheory.RealWeilF
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegelUnfold

open MeasureTheory



theorem diag_theta_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
            @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
            ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
              GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) =
                c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ S T JA JB ξ hJA hJB κ _ co hrat ν 𝓕 hν μ hμ
  letI mV : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  letI mVV : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  have hψc : IsCharAF D.host.F ψ := hψ.1
  obtain ⟨lam, 𝓖, hlam, h𝓖, -, htr⟩ := GlobalTheory.T.darbouxCoords_transport_covolumeOne_haar D S T κ co.e (GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair D S T κ co.e hrat) ν 𝓕 hν
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.RatVecDomain.exists_fundamentalDomain D.host.F κ μ hμ
  obtain ⟨c₁, hc₁, hiter⟩ := GlobalTheory.T.integral_ratPairFundamentalDomain_adelic_iterated D.host.F κ μ hμ lam hlam 𝓖 h𝓖 𝓕₁ h𝓕₁ htop
  have hpos : 0 < μ.real 𝓕₁ := ENNReal.toReal_pos h0 htop
  refine ⟨((c₁ * μ.real 𝓕₁ : ℝ) : ℂ), Complex.ofReal_ne_zero.mpr (mul_pos hc₁ hpos).ne', fun Φ hΦ => ?_⟩

  set G : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ := fun p =>
    GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) Φ) with hGdef
  have hdiag : ∀ w, GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ (GlobalTheory.DiagSiegel.diagMat w) =
      G (co.e w) := by
    intro w
    have h1 : (GlobalTheory.DblSchr.ddr co).e (GlobalTheory.DiagSiegel.diagMat w) =
        (Sum.elim (co.e w).1 (co.e w).1, Sum.elim (co.e w).2 (-(co.e w).2)) := by
      rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e]
      have h2 : (GlobalTheory.DiagSiegel.diagMat w).submatrix id finSumFinEquiv.symm.symm = Matrix.fromCols w w := by
        ext i j
        simp only [GlobalTheory.DiagSiegel.diagMat, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.symm_apply_apply, id]
      rw [h2]
      rfl
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, h1, hGdef]

  obtain ⟨B, hB⟩ := GlobalTheory.T.tsum_norm_adelicSchwartz_rationalTranslates_le D.host.F (κ ⊕ κ) Φ hΦ
  have hsumΦ : ∀ z : κ ⊕ κ → AF D.host.F, Summable fun ξ : κ ⊕ κ → D.host.F =>
      ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + z)‖ := fun z => by
    have h1 := GlobalTheory.WeilM.summable_norm_of_mem_schA D.host.F (GlobalTheory.SchwartzTranslate.schA_translate D.host.F z hΦ)
    exact h1
  have hGbd : ∃ B : ℝ, ∀ w, ‖G w‖ ≤ B := by
    refine ⟨B, fun w => ?_⟩
    have hn : ∀ ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ =
        ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ := by
      intro ξ
      simp only [GlobalTheory.WeilM.schr, norm_mul, hψc.2.1, one_mul]
    have hs : Summable fun ξ : κ ⊕ κ → D.host.F => ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
        (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := by
      simp_rw [hn]
      exact hsumΦ _
    calc ‖G w‖ ≤ ∑' ξ : κ ⊕ κ → D.host.F, ‖GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ
          (fun i => algebraMap D.host.F (AF D.host.F) (ξ i))‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' ξ : κ ⊕ κ → D.host.F, ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim w.1 w.1)‖ :=
          tsum_congr hn
      _ ≤ B := hB _
  have hGm : Measurable G := by
    letI mW : MeasurableSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := borel _
    haveI : BorelSpace ((κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := ⟨rfl⟩
    have hm := GlobalTheory.ThetaTransformMeas.main D.host.F ψ hψc (κ ⊕ κ) Φ hΦ
    have hc : Continuous fun p : (κ → AF D.host.F) × (κ → AF D.host.F) =>
        ((Sum.elim p.1 p.1, Sum.elim p.2 (-p.2)) : (κ ⊕ κ → AF D.host.F) × (κ ⊕ κ → AF D.host.F)) := by
      refine Continuous.prodMk (continuous_pi fun i => ?_) (continuous_pi fun i => ?_) <;> rcases i with i | i
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_fst
      · exact (continuous_apply i).comp continuous_snd
      · exact ((continuous_apply i).comp continuous_snd).neg
    exact hm.comp hc.measurable
  have hGper : ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, ∀ w, G (γ + w) = G w :=
    fun γ hγ w => GlobalTheory.T.diagonalThetaSum_rationalPair_invariant D.host.F ψ hψc κ Φ γ hγ w

  set h : (κ → AF D.host.F) → ℂ := fun u => Φ (Sum.elim u u) with hhdef
  have hcont : Continuous h :=
    (GlobalTheory.ThetaUnfold.schA_continuous D.host.F hΦ).comp
      (continuous_pi fun i => by rcases i with i | i <;> exact continuous_apply i)
  have hhbd : ∃ B : ℝ, ∀ x : κ → AF D.host.F, Summable (fun η : κ → D.host.F =>
      ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖) ∧
      ∑' η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ ≤ B := by
    refine ⟨B, fun x => ?_⟩
    have hj : Function.Injective fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F) := by
      intro η η' e
      funext i
      exact congrFun e (Sum.inl i)
    have key : ∀ η : κ → D.host.F, ‖h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x)‖ =
        ((fun ξ : κ ⊕ κ → D.host.F => ‖Φ ((fun i => algebraMap D.host.F (AF D.host.F) (ξ i)) + Sum.elim x x)‖) ∘
          fun η : κ → D.host.F => (Sum.elim η η : κ ⊕ κ → D.host.F)) η := by
      intro η
      simp only [hhdef, Function.comp_apply]
      congr 2
      funext i
      rcases i with i | i <;> rfl
    simp_rw [key]
    exact ⟨(hsumΦ _).comp_injective hj,
      (tsum_comp_le_tsum_of_inj (hsumΦ _) (fun _ => norm_nonneg _) hj).trans (hB _)⟩
  have hinner : ∀ x, ∫ y in 𝓕₁, G (x, y) ∂μ = (μ.real 𝓕₁ : ℂ) *
      ∑' η : κ → D.host.F, h ((fun i => algebraMap D.host.F (AF D.host.F) (η i)) + x) := by
    intro x
    exact GlobalTheory.T.integral_diagonalTheta_secondVariable_diagonal D.host.F ψ hψc κ μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ x
  calc GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)
      = ∫ w in 𝓕, G (co.e w) ∂ν := by
        unfold GlobalTheory.DiagSiegel.thetaDiagInt
        simp_rw [hdiag]
    _ = ∫ p in 𝓖, G p ∂lam := htr G
    _ = c₁ * ∫ x in 𝓕₁, ∫ y in 𝓕₁, G (x, y) ∂μ ∂μ := hiter G hGm hGper hGbd
    _ = c₁ * ((μ.real 𝓕₁ : ℂ) * ∫ u, h u ∂μ) := by
        simp_rw [hinner]
        rw [integral_const_mul, GlobalTheory.T.integral_fundamentalDomain_tsum_rationalTranslates D.host.F κ μ hμ 𝓕₁ h𝓕₁ htop h hcont hhbd]
    _ = ((c₁ * μ.real 𝓕₁ : ℝ) : ℂ) * GlobalTheory.DiagSiegel.diagInt μ Φ := by
        push_cast
        rw [mul_assoc]
        rfl

end GlobalTheory.DiagSiegelUnfold

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.continuous_thetaTransform_rationalDarboux_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  first | exact @GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm | exact GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm | (intros; apply GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.thetaTransform_rationalDarboux_quasiInvariant_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ w := by
  first | exact @GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi | exact GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi | (intros; apply GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi <;> assumption)
end

section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  first | (exact @GlobalTheory.AfPCpctDen.main) | (exact GlobalTheory.AfPCpctDen.main) | (intros; apply GlobalTheory.AfPCpctDen.main  <;> assumption)
end

section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p → ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.ratDen_pow_of_intAfP) | (exact GlobalTheory.ratDen_pow_of_intAfP) | (intros; apply GlobalTheory.ratDen_pow_of_intAfP  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.placeIdempotent_components_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  first | exact @GlobalTheory.ConjVal.components_and_conj_valuation | exact GlobalTheory.ConjVal.components_and_conj_valuation | (intros; apply GlobalTheory.ConjVal.components_and_conj_valuation <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

theorem _root_.GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L → Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.relAmple_rigTransl_point | exact GlobalTheory.RigidTranslate.relAmple_rigTransl_point | (intros; apply GlobalTheory.RigidTranslate.relAmple_rigTransl_point <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

theorem _root_.GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.kTriv_rigTransl_any | exact GlobalTheory.RigidTranslate.kTriv_rigTransl_any | (intros; apply GlobalTheory.RigidTranslate.kTriv_rigTransl_any <;> assumption)
end
