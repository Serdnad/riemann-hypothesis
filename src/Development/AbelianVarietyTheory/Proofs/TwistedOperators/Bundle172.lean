module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle052
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle015
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumLeOfLatticeCoordsQuadraticDecay
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PsiFinAlgebraic

theorem exists_pow_psi_fin_eq_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : ∃ M : ℕ, 0 < M ∧ ψ (pairA F 0 y) ^ M = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F {c | ψ (pairA F 0 c) = 1}
    (GlobalTheory.FinTranslate.eventually_fin_eq_one hψ)
  obtain ⟨m, hm, hy⟩ := GlobalTheory.UnRep.SmallMat.exists_nsmul_integral y
  refine ⟨N * m, Nat.mul_pos hN (Nat.pos_of_ne_zero hm), ?_⟩
  have h1 : ψ (pairA F 0 (N • m • y)) = 1 := h _ hy
  have e : pairA F 0 (N • m • y) = (N * m) • pairA F 0 y :=
    Prod.ext (smul_zero (N * m)).symm (mul_smul N m y).symm
  rwa [e, AddChar.map_nsmul_eq_pow] at h1

theorem isAlgebraic_psi_fin {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ)
    (y : Af F) : IsAlgebraic ℚ (ψ (pairA F 0 y)) := by
  obtain ⟨M, hM, h⟩ := exists_pow_psi_fin_eq_one hψ y
  refine IsAlgebraic.of_pow hM ?_
  rw [h]
  exact isAlgebraic_one

theorem isAlgebraic_psi_symplOH : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (u v : WO S T),
    u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)) := by
  intro D ψ hψ S T u v hu _
  have e : pairA D.host.F 0 (sndA D.host.F (symplOH S T u v)) = symplOH S T u v :=
    Prod.ext (GlobalTheory.WeilVacMove.fst_symplOH S T u v (Or.inl hu)).symm rfl
  rw [← e]
  exact isAlgebraic_psi_fin hψ.1 _

end GlobalTheory.PsiFinAlgebraic
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDeriv

theorem compAt_mt_eq_infMat {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) = infMat D.sp.cm.sig V.gram (θ τ) g := by
  ext i j
  simp only [compAt, Formalism.L2.Theta.mt, infMat, matHom, Matrix.map_apply]
  rfl

theorem om_dRho_infMat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (g : GA D S) (h : GA D T) τ z f, IsThetaFunO ψ S T f → om (g, h) (Datum.dRho (heisO ψ S T) θ τ z f) = Datum.dRho (heisO ψ S T) θ τ (infMat D.sp.cm.sig T.gram (θ τ) h * z * infMat D.sp.cm.sig S.gram (θ τ) g⁻¹) (om (g, h) f) := by
  intro D ψ S T χS χT om hW θ hθ g h τ z f hf
  rw [← compAt_mt_eq_infMat θ τ T h, ← compAt_mt_eq_infMat θ τ S g⁻¹]
  exact GlobalTheory.WeilVacMove.om_dRho hW hθ g h τ z hf

end GlobalTheory.WeilDeriv
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSqInt

theorem thetaO_norm_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → (∀ γ ∈ ratL T S, ∀ w, ‖F (γ + w)‖ = ‖F w‖) ∧ ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≠ ⊤ ∧ ∫ x in 𝓕, F x * starRingEnd ℂ (F x) ∂μ = (((∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  intro D ψ hψ S T μ 𝓕 hC F hF
  haveI hB : BorelSpace (WO S T) := ⟨rfl⟩
  haveI hO : OpensMeasurableSpace (WO S T) := BorelSpace.opensMeasurable
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ w
    obtain ⟨ξ, rfl⟩ := hγ
    have hq := hF.quasi ξ w
    have e : ((incA D).toAddMonoidHom.mapMatrix ξ : WO S T) = ratW T S ξ := rfl
    rw [e, hq, norm_mul, hn, one_mul]
  · obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hF
    have hle : ∫⁻ x in 𝓕, ‖F x‖ₑ ^ 2 ∂μ ≤ ∫⁻ _x in 𝓕, ENNReal.ofReal M ^ 2 ∂μ := by
      refine lintegral_mono fun x => ?_
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM x)
    rw [setLIntegral_const, hC.2.2, mul_one] at hle
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hle
  · have h1 : ∀ x, F x * starRingEnd ℂ (F x) = (((‖F x‖ ^ 2 : ℝ)) : ℂ) := fun x => by
      rw [Complex.mul_conj']; push_cast; rfl
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg ‖F x‖)
      ((hF.cont.norm.pow 2).measurable.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

end GlobalTheory.ThetaSqInt
end

section

open MeasureTheory

namespace GlobalTheory.UnfoldNormal

theorem unfold_zero_mean : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ K F : H → ℂ, Measurable K → Measurable F → (∀ n ∈ N, ∀ h, K (n * h) = K h) → (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ h, ∫ n in 𝓝, F ((n : H) * h) ∂κ = 0) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → IntegrableOn (fun h => K h * F h) 𝓕 ν → ∫ h in 𝓕, K h * F h ∂ν = 0 := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t K F hKm hFm hKN hKΓ hFΓ h0 𝓕 h𝓕 hint
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaCompactSpace N := inferInstance
  haveI : SigmaFinite κ := inferInstance
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun y : Γ => (y : H)) hab
  have hR : ∀ n₀ : N, κ.map (· * n₀) = κ := GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain H Γ N hΓ hNc κ 𝓝 hκ h𝓝 h𝓝t
  have hI : κ.map (fun n => n⁻¹) = κ := by
    haveI : κ.IsMulRightInvariant := ⟨hR⟩
    exact (GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant κ).inv_eq_self
  have hC : ∀ γ (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ :=
    GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self H Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t
  have hemb : MeasurableEmbedding (shear N) := measurableEmbedding_shear hNc
  set G := pairGroup Γ N hN with hG
  set μ := (κ.prod ν).map (shear N) with hμ
  haveI : Countable G := by
    refine Function.Injective.countable (f := fun g : G => ((⟨(g : H × H).1, g.2.1⟩ : Γ), (⟨(g : H × H).2, g.2.2.1⟩ : Γ))) ?_
    intro a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    exact Subtype.ext (Prod.ext hab.1 hab.2)
  haveI : MeasurableConstSMul G (H × H) := inferInstance
  haveI : SMulInvariantMeasure G (H × H) μ := GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup H ν Γ N hNc hN κ hκ hC
  have hS : IsFundamentalDomain G (shear N '' (𝓝 ×ˢ 𝓕)) μ :=
    ⟨nullMeasurableSet_shear_image hNc κ ν h𝓝.nullMeasurableSet h𝓕.nullMeasurableSet,
      GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕, GlobalTheory.T.aedisjoint_pairGroup_smul_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕⟩
  have hsw : μ.map Prod.swap = μ := GlobalTheory.T.map_swap_sheared_product_measure_unimodular H ν N hNc κ hκ hI
  set S := shear N '' (𝓝 ×ˢ 𝓕) with hSdef
  set f : H → ℂ := fun x => K x * F x with hf
  have hmp : MeasurePreserving (shear N) (κ.prod ν) μ := ⟨hemb.measurable, rfl⟩
  have hsp : MeasurePreserving (Prod.swap : H × H → H × H) μ μ := ⟨measurable_swap, hsw⟩
  have hswemb : MeasurableEmbedding (Prod.swap : H × H → H × H) := MeasurableEquiv.prodComm.measurableEmbedding
  let e : G → G := fun g => ⟨(g : H × H).swap, by
    obtain ⟨h1, h2, h3⟩ := g.2
    refine ⟨h2, h1, ?_⟩
    have : (g : H × H).2 * ((g : H × H).1)⁻¹ = ((g : H × H).1 * ((g : H × H).2)⁻¹)⁻¹ := by group
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [this]; exact N.inv_mem h3⟩
  have he : Function.Bijective e := by
    have : Function.Involutive e := fun g => Subtype.ext (Prod.swap_swap _)
    exact this.bijective
  have hS2 : IsFundamentalDomain G (Prod.swap ⁻¹' S) μ := by
    refine hS.preimage_of_equiv hsp.quasiMeasurePreserving he fun g x => ?_
    rfl
  have hΦ : ∀ (g : G) (p : H × H), f (g • p).1 = f p.1 := by
    intro g p
    have hu : (g : H × H).1 ∈ Γ := g.2.1
    change K ((g : H × H).1 * p.1) * F ((g : H × H).1 * p.1) = K p.1 * F p.1
    rw [hKΓ _ hu, hFΓ _ hu]
  have step1 : ∫ p in S, f p.1 ∂μ = ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ :=
    hS.setIntegral_eq hS2 (f := fun p => f p.1) hΦ
  have step2 : ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ = ∫ p in S, f p.2 ∂μ :=
    hsp.setIntegral_preimage_emb hswemb (fun p => f p.2) S
  have step3 : ∀ g : H × H → ℂ, ∫ p in S, g p ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, g (shear N q) ∂(κ.prod ν) :=
    fun g => hmp.setIntegral_image_emb hemb g _

  have hint2 : IntegrableOn (fun p : H × H => f p.1) S μ := by
    rw [hS.integrableOn_iff hS2 (f := fun p => f p.1) hΦ]
    have h2 : IntegrableOn (fun p : H × H => f p.2) S μ := by
      rw [hmp.integrableOn_image hemb]
      haveI : IsFiniteMeasure (κ.restrict 𝓝) := isFiniteMeasure_restrict.2 h𝓝t
      change Integrable (fun q : N × H => f q.2) ((κ.prod ν).restrict (𝓝 ×ˢ 𝓕))
      rw [← Measure.prod_restrict]
      exact hint.comp_snd (κ.restrict 𝓝)
    exact (hsp.integrableOn_comp_preimage hswemb).2 h2
  have hint3 : Integrable (fun q : N × H => f ((q.1 : H) * q.2)) ((κ.restrict 𝓝).prod (ν.restrict 𝓕)) := by
    rw [Measure.prod_restrict]
    exact (hmp.integrableOn_image hemb).1 hint2
  have lhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) = 0 := by
    rw [← Measure.prod_restrict]
    change ∫ q : N × H, f ((q.1 : H) * q.2) ∂((κ.restrict 𝓝).prod (ν.restrict 𝓕)) = 0
    rw [integral_prod_symm _ hint3]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [shear, hf, Pi.zero_apply]
    have : ∀ x : N, K ((x : H) * y) * F ((x : H) * y) = K y * F ((x : H) * y) := fun x => by rw [hKN _ x.2]
    simp_rw [this]
    rw [integral_const_mul, h0, mul_zero]
  have rhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) = (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν := by
    rw [← Measure.prod_restrict]
    simp only [shear]
    rw [integral_fun_snd, measureReal_restrict_apply_univ]
    rfl
  have key : (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν = 0 := by
    have e1 : ∫ p in S, f p.1 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) := step3 _
    have e2 : ∫ p in S, f p.2 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) := step3 _
    rw [← rhs, ← e2, ← step2, ← step1, e1, lhs]
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hpos : (κ 𝓝).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hne, h𝓝t⟩
  exact (smul_eq_zero.1 key).resolve_left hpos

end GlobalTheory.UnfoldNormal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.tsum_le_of_lattice_coords_quadraticDecay : ∀ {Y : Type} (n N : ℕ), 0 < N → ∀ (a : Y → ENNReal) (T : Fin n → Y → ℝ), (∀ y y', a y ≠ 0 → a y' ≠ 0 → (∀ j, T j y = T j y') → y = y') → (∀ y, a y ≠ 0 → ∀ j, ∃ c : ℤ, (N : ℝ) * T j y = c) → ∀ S : ENNReal, (∀ y, a y * ∏ j, ENNReal.ofReal (1 + T j y ^ 2) ≤ S) → ∑' y, a y ≤ S * ENNReal.ofReal ((5 * (N : ℝ) ^ 2) ^ n) := by
  first | exact @GlobalTheory.TwBoundFour.tsum_le | exact GlobalTheory.TwBoundFour.tsum_le | (intros; apply GlobalTheory.TwBoundFour.tsum_le <;> assumption)
end
