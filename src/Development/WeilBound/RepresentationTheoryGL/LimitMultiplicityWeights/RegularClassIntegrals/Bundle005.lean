module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem variation : Variation := by
  intro F E _ _ _ _ _ σ hCM n J hJ k C hC f hf hfs hV z g e he
  have := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J C) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  have hcl : IsClosed (unipRad σ J C : Set (GAd σ J)) :=
    GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) C 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma hCM) hC _
  let ν : Measure (unipRad σ J C) := Measure.haar
  have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)) ν
  have hfin : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ ⊤ := hc.measure_ne_top h𝓕
  have hpos : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  let h : unipRad σ J C → ℂ := fun m => f (z * m * g)
  have hcont : Continuous h := by fun_prop
  let T := (Homeomorph.mulLeft z).trans (Homeomorph.mulRight g)
  have hK : IsCompact (T ⁻¹' tsupport f) := T.isCompact_preimage.2 hfs
  have hsupp : HasCompactSupport h :=
    HasCompactSupport.intro' (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
      ((isClosed_tsupport f).preimage (T.continuous.comp continuous_subtype_val))
      fun x hx => image_eq_zero_of_notMem_tsupport (f := f) (x := z * (x : GAd σ J) * g) hx
  have hint : Integrable h ν := hcont.integrable_of_hasCompactSupport hsupp
  have hV0 : ∫ m, h m ∂ν = 0 := hV ν z g
  let F' : (ratPts σ J).subgroupOf (unipRad σ J C) → unipRad σ J C → ℂ := fun γ x => h (γ • x)
  have hmeas : ∀ γ, AEStronglyMeasurable (F' γ) (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    fun γ => (hcont.comp (continuous_const_smul γ)).aestronglyMeasurable
  have hlin : ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
    have hl : ∫⁻ x, ‖h x‖ₑ ∂ν = ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν := by
      rw [h𝓕.lintegral_eq_tsum' (fun x => ‖h x‖ₑ), ← (Equiv.inv _).tsum_eq]; simp [F']
    rw [← hl]; exact hint.2.ne
  have e1 : ∫ m, h m ∂ν = ∑' γ, ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), F' γ x ∂ν := by
    rw [h𝓕.integral_eq_tsum' h hint, ← (Equiv.inv _).tsum_eq]; simp [F']
  have e2 := integral_tsum hmeas hlin
  have hΨ : ∀ x : unipRad σ J C, ∑' γ, F' γ x = nsum (NF σ J C) f z ((x : GAd σ J) * g) := fun x => by
    let eq : (ratPts σ J).subgroupOf (unipRad σ J C) ≃ NF σ J C :=
      { toFun := fun γ => ⟨γ.1.1, γ.2, γ.1.2⟩, invFun := fun ν => ⟨⟨ν.1, ν.2.2⟩, ν.2.1⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [nsum, ← eq.tsum_eq]
    congr 1; funext γ
    show f (z * ((γ • x : unipRad σ J C) : GAd σ J) * g) = _
    rw [Subgroup.smul_def]; simp [eq, mul_assoc]
  have hzero : ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
      nsum (NF σ J C) f z ((x : GAd σ J) * g) ∂ν = 0 := by
    simp_rw [← hΨ]; rw [e2]; exact e1.symm.trans hV0
  have hae : ∀ᵐ x ∂(ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))),
      HasSum (fun γ => F' γ x) (∑' γ, F' γ x) := by
    have h1 : ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ∑' γ, ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
      rw [lintegral_tsum (fun γ => (hmeas γ).enorm)]; exact hlin
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).enorm) h1] with x hx
    have hs : Summable fun γ => ‖F' γ x‖₊ :=
      ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm_eq_nnnorm] using hx.ne)
    exact (Summable.of_norm (NNReal.summable_coe.2 hs)).hasSum
  have hΨm : AEStronglyMeasurable (fun x : unipRad σ J C => ∑' γ, F' γ x)
      (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s => by first
        | exact Finset.aestronglyMeasurable_fun_sum s fun γ _ => hmeas γ
        | exact Finset.aestronglyMeasurable_sum s fun γ _ => hmeas γ) hae
  haveI : IsFiniteMeasure (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    isFiniteMeasure_restrict.2 hfin
  have hΨi : IntegrableOn (fun x : unipRad σ J C => nsum (NF σ J C) f z ((x : GAd σ J) * g))
      (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ν := by
    refine Integrable.of_bound (C := e + ‖nsum (NF σ J C) f z g‖) ?_ (.of_forall fun x => ?_)
    · simpa only [hΨ] using hΨm
    · have := he x x.2
      calc _ = ‖(nsum (NF σ J C) f z ((x : GAd σ J) * g) - nsum (NF σ J C) f z g) + nsum (NF σ J C) f z g‖ := by
              rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  have key : ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) • nsum (NF σ J C) f z g =
      ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
        (nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) ∂ν := by
    rw [integral_sub (integrable_const _) hΨi, hzero, setIntegral_const, sub_zero]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := ν) hfin.lt_top
    (f := fun x : unipRad σ J C => nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) (C := e)
    (fun x _ => by rw [norm_sub_rev]; exact he x x.2)
  rw [← key, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hb
  have hp : 0 < ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) := ENNReal.toReal_pos hpos hfin
  nlinarith [norm_nonneg (nsum (NF σ J C) f z g)]

end MainStatements.WeightKernel.Dec
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem level_of_mem {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, b, hb, rfl⟩ := hx
    obtain ⟨V, hV, hVb⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩
    show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)
    rw [map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by
      simp only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩

end MainStatements.WeightKernel.Dec.DLevel

theorem MainStatements.WeightKernel.Dec.level : MainStatements.WeightKernel.Dec.Level := by
  intro F E _ _ _ _ _ σ _ n J _ f hf
  exact MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem bridge : Bridge := by
  intro D V r X Y hW j
  rw [NA_frameFlag]
  rfl

end MainStatements.WeightKernel.Dec

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

namespace DDecay

theorem tsum_eq (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r)
    (hB : NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j))
    (g : GA D V → ℂ) :
    ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν) =
      ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := by
  have hS : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)) =
      rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) : Set (GF V)) := by
    rw [← Subgroup.coe_map, map_unipRat, hB]; rfl
  calc ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν)
      = ∑' b : (rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) :
          Set (GF V))), g b := (tsum_image g (ratEmb_injective _ _).injOn).symm
    _ = ∑' c : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)),
          g (Set.equivOfEq hS c) := (Equiv.tsum_eq (Set.equivOfEq hS) (fun b => g b)).symm
    _ = ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := rfl

end DDecay

theorem decay : Core → Bridge → Decay := by
  intro hCore hBridge D V r X Y hW c hc j f hf hU C W hC hW'
  obtain ⟨A, hA⟩ := hCore D V r X Y hW c hc j
  have hB := hBridge D V r X Y hW j
  have hV : Van (unipRad D.sp.cm.sig V.gram (pre X j)) f := by
    have h0 : Van (NA (frameFlag (isIsoFrame_firstCols hW j))) f := fun ν _ x y => (hU ν x y).2
    rw [hB] at h0
    exact h0
  refine ⟨A, fun m => ?_⟩
  obtain ⟨B, hBd⟩ := hA m f hf hV C W hC hW'
  refine ⟨B, fun t ht a ha x hx y hy => ?_⟩
  have h1 := hBd t ht a ha x hx y hy
  have h2 : ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
      f (x * (a⁻¹ * rat V ν * a) * y) = nsum (NF D.sp.cm.sig V.gram (pre X j)) f (x * a⁻¹) (a * y) := by
    rw [nsum, ← DDecay.tsum_eq D V r X Y hW j hB (fun g => f (x * a⁻¹ * g * (a * y)))]
    congr 1; funext ν; congr 1; group
  rw [h2]
  exact h1

end MainStatements.WeightKernel.Dec
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem smOf : SmOf := by
  intro F E _ _ _ _ _ σ h n J _ f hf k γ hγ g
  exact (GlobalTheory.Orb.isSmoothRealFam_prod (fun i =>
    (GlobalTheory.ThK.CuspTransfer.Smooth.line_fam h (hγ i)).1.comp (contDiff_apply ℝ (fun _ => ℝ) i))).contDiff hf g

end MainStatements.WeightKernel.Dec

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DSumSm

lemma loc_fin {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (z : G)
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] {φ : X → G} (hφ : Continuous φ) (x₀ : X) :
    ∃ S : Finset Γ, ∀ᶠ x in 𝓝 x₀, ∀ ν : Γ, ν ∉ S → f (z * ν * φ x) = 0 := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
  have hfin := GlobalTheory.AutomorphicL2KernelContinuous.finite_contributing (Γ := Γ) hf (isCompact_singleton (x := z⁻¹))
    (hK.image hφ)
  refine ⟨hfin.toFinset, Filter.mem_of_superset hKn fun x hx ν hν => ?_⟩
  by_contra h
  apply hν
  rw [Set.Finite.mem_toFinset]
  exact ⟨z⁻¹, rfl, φ x, ⟨x, hx, rfl⟩, by simpa using h⟩

lemma cont_prod {G : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] :
    ∀ (k : ℕ) (γ : Fin k → ℝ → G), (∀ i, Continuous (γ i)) →
      Continuous fun t : Fin k → ℝ => (List.ofFn fun i => γ i (t i)).prod
  | 0, γ, _ => by simpa using continuous_const
  | k + 1, γ, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((h 0).comp (continuous_apply 0)).mul
      ((cont_prod k (fun i => γ i.succ) (fun i => h i.succ)).comp
        (continuous_pi fun i => continuous_apply i.succ))

end MainStatements.WeightKernel.Dec.DSumSm

namespace MainStatements.WeightKernel.Dec

open DSumSm in
theorem sumSm : SmOf → SumSm := by
  intro hSm F E _ _ _ _ _ σ h n J hJ Γ hΓ f hf z
  have : DiscreteTopology Γ :=
    DiscreteTopology.of_subset (t := (Γ : Set (GAd σ J))) (s := (ratPts σ J : Set (GAd σ J)))
      (inferInstance : DiscreteTopology (ratPts σ J)) hΓ
  have hs : GlobalTheory.UAut.IsSm σ J f := hSm F E σ h n J hJ f hf
  have hcs : HasCompactSupport f := (continuous_of_mem_ccAd hf).2
  refine ⟨?_, ?_⟩
  · intro k γ hγ g
    rw [contDiff_iff_contDiffAt]
    intro t₀
    have hφ : Continuous fun t : Fin k → ℝ => g * (List.ofFn fun i => γ i (t i)).prod :=
      continuous_const.mul (cont_prod k γ fun i =>
        GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J (γ i) (hγ i))
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) hcs z hφ t₀
    have hsum : ContDiffAt ℝ ∞ (fun t : Fin k → ℝ =>
        ∑ ν ∈ S, f (z * ν * (g * (List.ofFn fun i => γ i (t i)).prod))) t₀ := by
      refine ContDiff.contDiffAt (ContDiff.sum fun ν _ => ?_)
      have := hs k γ hγ (z * ν * g)
      simpa only [mul_assoc] using this
    refine hsum.congr_of_eventuallyEq (hS.mono fun t ht => ?_)
    exact tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
  · intro b hb
    funext g
    have hbc := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) (φ := fun t : ℝ => g * b t) hcs z (continuous_const.mul hbc) 0
    have hline : ∀ x : GAd σ J, ContDiff ℝ ∞ fun t : ℝ => f (x * b t) := by
      intro x
      have := (hs 1 (fun _ => b) (fun _ => hb) x).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
      convert this using 2
      simp [List.ofFn_succ]
    have e1 : (fun t => nsum Γ f z (g * b t)) =ᶠ[𝓝 0]
        fun t => ∑ ν ∈ S, f (z * ν * (g * b t)) :=
      hS.mono fun t ht => tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
    have e2 : ∀ ν ∉ S, lineDer b f (z * ν * g) = 0 := by
      intro ν hν
      show deriv (fun t => f (z * ν * g * b t)) 0 = 0
      have : (fun t => f (z * ν * g * b t)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
        hS.mono fun t ht => by simpa only [mul_assoc] using ht ν hν
      rw [this.deriv_eq, deriv_const]
    show deriv (fun t => nsum Γ f z (g * b t)) 0 = ∑' ν : Γ, lineDer b f (z * ν * g)
    rw [e1.deriv_eq, tsum_eq_sum (s := S) e2, deriv_fun_sum]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      show _ = deriv (fun t => f (z * ν * g * b t)) 0
      simp only [mul_assoc]
    · intro ν _
      have := ((hline (z * ν * g)).differentiable (by simp)) 0
      simpa only [mul_assoc] using this

end MainStatements.WeightKernel.Dec

end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerVan

theorem mem_aux {G : Type*} [Group G] (K : Set G) (B : Set ℝ) (c : ℝ → G) (x y m : G) (t : ℝ)
    (hk : x * m * (y * c t) ∈ K) (ht : t ∈ B) :
    m ∈ (fun p : G × ℝ => x⁻¹ * p.1 * (y * c p.2)⁻¹) '' (K ×ˢ B) :=
  ⟨(x * m * (y * c t), t), ⟨hk, ht⟩, by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]⟩

end MainStatements.WeightKernel.Dec.DDerVan

theorem MainStatements.WeightKernel.Dec.derVan : MainStatements.WeightKernel.Dec.SmOf → MainStatements.WeightKernel.Dec.DerMem → MainStatements.WeightKernel.Dec.DerVan := by
  intro hSm hDer F E _ _ _ _ _ σ h n J hJ N hN f hf b hb hV ν _ x y
  have hfc := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) hf
  have hf'c := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) (hDer F E σ h n J hJ f hf b hb)
  have hs := hSm F E σ h n J hJ f hf
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hK : IsCompact (tsupport f ∪ tsupport (lineDer b f)) := IsCompact.union hfc.2 hf'c.2
  have hS : IsCompact ((fun p : GAd σ J × ℝ => x⁻¹ * p.1 * (y * b p.2)⁻¹) ''
      ((tsupport f ∪ tsupport (lineDer b f)) ×ˢ Metric.closedBall (0 : ℝ) 1)) :=
    (hK.prod (isCompact_closedBall 0 1)).image
      ((continuous_const.mul continuous_fst).mul ((continuous_const.mul (hbc.comp continuous_snd)).inv))
  have hC := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have key := GlobalTheory.LaurentAut.hasDerivAt_integral_cpt (𝕜 := ℝ) ν (x₀ := 0)
    (Φ := fun t (m : N) => f (x * m * (y * b t))) (Φ' := fun t (m : N) => lineDer b f (x * m * (y * b t))) hC ?_ ?_ ?_ ?_
  · have h0 : (fun t : ℝ => ∫ m : N, f (x * m * (y * b t)) ∂ν) = fun _ => 0 := funext fun t => hV ν x (y * b t)
    rw [h0] at key
    have e := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simpa [GlobalTheory.UAut.ConstAut.realLine_zero h hb] using e
  · intro t
    exact hfc.1.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  · exact hf'c.1.comp ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_const.mul (hbc.comp continuous_fst)))
  · intro t ht m hm
    have hnot : x * ↑m * (y * b t) ∉ tsupport f ∪ tsupport (lineDer b f) := fun hk =>
      hm (MainStatements.WeightKernel.Dec.DDerVan.mem_aux _ _ b x y (↑m) t hk ht)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inl h')),
      image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inr h'))⟩
  · intro t m
    have := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hb (x * ↑m * y) t
    simpa [mul_assoc] using this
end
end
