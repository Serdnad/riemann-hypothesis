module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle164
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle165
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField


theorem _root_.GlobalTheory.T.one_sub_idempotent_smul_mem_completion_prime_mul : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  first | exact @GlobalTheory.ComplOffPlace.one_sub_smul_mem | exact GlobalTheory.ComplOffPlace.one_sub_smul_mem | (intros; apply GlobalTheory.ComplOffPlace.one_sub_smul_mem <;> assumption)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.norm_rightConvolution_le_adelic_height_pow : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Ω : Set (GA D V)}, IsCompact Ω → (∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A)) → ∃ (A : ℕ) (C : ℝ), ∀ f' : GA D V → ℂ, Continuous f' → tsupport f' ⊆ Ω → ∀ M : ℝ, (∀ y, ‖f' y‖ ≤ M) → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (g : GA D V), ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g‖ ≤ C * M * ‖F‖ * GlobalTheory.Grow.height V g ^ A := by
  first | exact @GlobalTheory.ConvGrowth.norm_convR_le_height | exact GlobalTheory.ConvGrowth.norm_convR_le_height | (intros; apply GlobalTheory.ConvGrowth.norm_convR_le_height <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LFun.UnitaryParam

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.LFun.ConjPlace

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) :
    (s.map (starRingEnd ℂ)).esymm j = starRingEnd ℂ (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, map_multiset_sum, map_multiset_prod, Multiset.map_map,
    Function.comp_def]

theorem satEig_map_star (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    satEig q n (B.map star) j = starRingEnd ℂ (satEig q n B j) := by
  have h : ((q : ℂ)).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h2 := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) h
  rw [satEig, satEig, map_mul, ← esymm_map_conj, Multiset.map_map, Multiset.map_map]
  congr 1
  rw [map_natCast, map_div₀, map_mul, map_sub, map_natCast, map_natCast, map_ofNat] at h2
  exact h2

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x : V}

theorem form_heckeVec_comp (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K)
    (β : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hβ : ∀ v w, β w v = starRingEnd ℂ (β v w))
    (hi : ∀ g v w, β (ρ g v) (ρ g w) = β v w) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (hr : ∀ g, starRingEnd ℂ (h g) = h g)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t = t⁻¹ ∧ g = a * t * b) :
    β (heckeVec (ρ.comp θ) K h x) x = starRingEnd ℂ (β (heckeVec ρ K h x) x) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (ρ (a * t * b) x) x = β (ρ t x) x := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hf a ha).symm).trans (hi a _ _)
  have inv : ∀ t, β (ρ t⁻¹ x) x = starRingEnd ℂ (β (ρ t x) x) := fun t => by
    rw [← hβ, ← hi t]; simp
  have e1 := (β.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh (ρ.comp θ) x)
  have e2 := ((starRingEnd ℂ).toAddMonoidHom.comp (β.flip x).toAddMonoidHom).map_finsum (finite_heckeVec hK hh ρ x)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • ρ (θ c.out) x) x = starRingEnd ℂ (β (h c.out • ρ c.out x) x)
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hr]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, map_mul θ, map_mul θ, bi _ (hθ a ha) _ (hθ b hb), bi _ ha _ hb, htt, inv]

end General

theorem map_star_eq_map_inv (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (B : Multiset ℂˣ) (hU : GlobalTheory.LGrp.IsUnitarisable ρ) (hx : IsSatVecGL w ρ x B) :
    B.map star = B.map (·⁻¹) := by
  classical
  obtain ⟨β, hβ, hpos, hi⟩ := hU
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hx' := isSatVecGL_invT c hc rfl hx
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have hne : β x x ≠ 0 := fun h0 => by simpa [h0] using hpos x hx.1
  refine eq_of_satEig_eq (qV_ne_zero w) (by simpa using hx.2.2.1) hx'.2.2.1 fun j hj => ?_
  have key := form_heckeVec_comp (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 β hβ hi
    (invT c n).symm.toMonoidHom (fun k hk => (hK _).2 (by simpa using hk))
    (fun g => by rw [Tj_apply]; split_ifs <;> simp)
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, (invT c n).symm_apply_eq.2 (invT_dGL c ϖ j).symm, e⟩)
  rw [hx'.2.2.2 _ hp j hj, hx.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, ← hβ] at key
  rw [satEig_map_star]
  exact (mul_right_cancel₀ hne key).symm

end GlobalTheory.LFun.UnitaryParam

end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.AvgHecke

open GlobalTheory.PRep

theorem exists_hecke_of_mem_span : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  classical
  intro G _ K hK M _ _ ρ s w hs hw hspan
  have hx : s ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hs
  have hy : w ∈ fixed ρ K := GlobalTheory.LGrp.mem_fixed.2 hw
  have hr : w ∈ LinearMap.range (GlobalTheory.LFun.HeckeScalar.orbitMap ρ K s) := by
    refine Submodule.span_le.2 ?_ hspan
    rintro _ ⟨g, rfl⟩
    exact ⟨Finsupp.single (g : G ⧸ K) 1, by rw [GlobalTheory.LFun.HeckeScalar.orbitMap_single hx, one_smul]⟩
  obtain ⟨φ, rfl⟩ := hr
  obtain ⟨ψ, hψ, e⟩ := GlobalTheory.LFun.HeckeScalar.exists_fixed_preimage _ (GlobalTheory.LFun.HeckeScalar.orbitMap_permRep hx)
    (GlobalTheory.LFun.HeckeScalar.mem_finOrbit hK φ) hy
  refine ⟨fun g => ψ g, ⟨fun a b g => ?_, ψ.support.image Quotient.out, fun g hg => ?_⟩, ?_⟩
  · have := GlobalTheory.LFun.HeckeScalar.permRep_apply (a : G) ψ (g : G ⧸ K)
    rw [GlobalTheory.LGrp.mem_fixed.1 hψ _ a.2] at this
    simpa using this
  · obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨_, Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hg), 1, j⁻¹, by simp [hj]⟩
  · rw [← e, heckeVec, GlobalTheory.LFun.HeckeScalar.orbitMap, Finsupp.linearCombination_apply, Finsupp.sum,
      finsum_eq_sum_of_support_subset (s := ψ.support)]
    · simp
    · intro c hc
      by_contra h
      exact hc (by simp [Finsupp.notMem_support_iff.1 h])

end GlobalTheory.SphTheta.AvgHecke

end
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.WeightUnfold

theorem exists_weight (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H) (hcomm : IsMulCommutative (cent γ)) (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)) (hfd : IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt) :
    ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  have hTcl : IsClosed ((cent γ : Subgroup H) : Set H) := Set.isClosed_centralizer _
  have hc : ∀ a b : cent γ, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  haveI : LocallyCompactSpace (cent γ) := hTcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : dt.IsMulRightInvariant := ⟨fun g => by
    have : (fun x : cent γ => x * g) = (fun x => g * x) := funext fun x => hc x g
    rw [this]; exact map_mul_left_eq_self dt g⟩
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat (T := cent γ) hTcl dt
  have hprod : Measurable fun p : H × cent γ => β (((p.2 : cent γ) : H) * p.1) :=
    hβm.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
  have hsec : ∀ x : H, Measurable fun t : cent γ => β ((t : H) * x) := fun x =>
    hβm.comp (measurable_subtype_coe.mul_const x)
  refine ⟨fun y => ∫⁻ t in 𝓣, β ((t : H) * y) ∂dt, ?_, ?_, ?_⟩
  · exact hprod.lintegral_prod_right'
  · intro y
    haveI : Countable Γ := by
      haveI : TopologicalSpace.SeparableSpace Γ := inferInstance
      exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance
    haveI : Countable (Γ.subgroupOf (cent γ)) := by
      refine Function.Injective.countable (f := fun h : Γ.subgroupOf (cent γ) => (⟨((h : cent γ) : H), h.2⟩ : Γ)) ?_
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hab
    rw [← hβ y, hfd.lintegral_eq_tsum'' (fun t : cent γ => β ((t : H) * y))]
    refine tsum_congr fun h => lintegral_congr fun t => ?_
    congr 1
    have e : ((h • t : cent γ) : H) = ((h : cent γ) : H) * (t : H) := rfl
    rw [e, ← mul_assoc, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]
  · intro ψ hψm hψ
    haveI : dt.IsMulLeftInvariant := inferInstance
    have hq := isQuotMeasure_quotMeas (T := cent γ) dt μ hTcl

    have hinner : ∀ t : cent γ, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ = ∫⁻ y, β y * ψ y ∂μ := by
      intro t
      have : (fun y => β ((t : H) * y) * ψ y) = fun y => (fun z => β z * ψ z) ((t : H) * y) := by
        funext y; show _ = β _ * ψ _; rw [hψ (t : H) t.2 y]
      rw [this]; exact lintegral_mul_left_eq_self (fun z => β z * ψ z) (t : H)
    have hC : ∫⁻ y, β y * ψ y ∂μ = ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
      rw [hq (fun y => β y * ψ y) (hβm.mul hψm)]
      refine lintegral_congr fun q => ?_
      have : (fun t : cent γ => β ((t : H) * Quotient.out q) * ψ ((t : H) * Quotient.out q)) = fun t : cent γ => β ((t : H) * Quotient.out q) * ψ (Quotient.out q) := by
        funext t; rw [hψ (t : H) t.2]
      rw [this, lintegral_mul_const _ (hsec _), hβ, one_mul]
      rfl
    calc ∫⁻ y, (∫⁻ t in 𝓣, β ((t : H) * y) ∂dt) * ψ y ∂μ
        = ∫⁻ y, ∫⁻ t in 𝓣, β ((t : H) * y) * ψ y ∂dt ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_mul_const _ (hsec y)]
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β ((t : H) * y) * ψ y ∂μ ∂dt := by
          refine lintegral_lintegral_swap ?_
          exact (hprod.mul (hψm.comp measurable_fst)).aemeasurable
      _ = ∫⁻ t in 𝓣, ∫⁻ y, β y * ψ y ∂μ ∂dt := by
          refine lintegral_congr fun t => hinner t
      _ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
          rw [lintegral_const, Measure.restrict_apply_univ, hC, mul_comm]

end GlobalTheory.WeightUnfold
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Orb

theorem isMulRightInvariant_of_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] : μ.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun x : G => x * g) = fun x => g * x := funext fun x => IsMulCommutative.is_comm.comm x g
    rw [this]
    exact map_mul_left_eq_self μ g⟩

section Weight

variable {H : Type} [Group H]

theorem exists_nt_mul {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (p q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((p.1 : H) * p.2) * ((q.1 : H) * q.2) :=
  ⟨(p.1 * ⟨(p.2 : H) * q.1 * (p.2 : H)⁻¹, hnorm _ p.2.2 _ q.1.2⟩, p.2 * q.2), by simp [mul_assoc]⟩

theorem exists_nt_inv {T N : Subgroup H} (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (q : N × T) :
    ∃ r : N × T, (r.1 : H) * r.2 = ((q.1 : H) * q.2)⁻¹ :=
  ⟨(⟨(q.2 : H)⁻¹ * (q.1 : H)⁻¹ * (q.2 : H)⁻¹⁻¹, hnorm _ (inv_mem q.2.2) _ (inv_mem q.1.2)⟩, q.2⁻¹), by
    simp only [Subgroup.coe_inv, inv_inv, mul_inv_rev]; group⟩

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem exists_weight_nt (T N : Subgroup H) (hT : IsClosed (T : Set H)) (hN : IsClosed (N : Set H))
    (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hj : Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2))
    (dt : Measure T) [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
    (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] :
    ∃ β : H → ℝ≥0∞, Measurable β ∧ (∀ x, β x ≠ ∞) ∧ (∀ n ∈ N, ∀ x, β (n * x) = β x) ∧
      ∀ x, ∫⁻ t : T, β (t * x) ∂dt = 1 := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  set j : N × T → H := fun p => (p.1 : H) * p.2 with hjdef
  have hjc : Continuous j := hj.continuous
  let K := CompactExhaustion.choice H
  let W : ℕ → Set H := fun k => interior (K (k + 1))
  have hWo : ∀ k, IsOpen (W k) := fun k => isOpen_interior
  let U : ℕ → Set H := fun k => {x | ∃ p : N × T, j p * x ∈ W k}
  have hUfwd : ∀ k q x, x ∈ U k → j q * x ∈ U k := by
    rintro k q x ⟨p, hp⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    obtain ⟨s, hs⟩ := exists_nt_mul hnorm p r
    refine ⟨s, ?_⟩
    have e : j s * (j q * x) = j p * x := by
      rw [show j s = j p * j r from hs, show j r = (j q)⁻¹ from hr]; group
    rw [e]; exact hp
  have hU : ∀ k q x, j q * x ∈ U k ↔ x ∈ U k := by
    refine fun k q x => ⟨fun h => ?_, hUfwd k q x⟩
    obtain ⟨r, hr⟩ := exists_nt_inv hnorm q
    have := hUfwd k r _ h
    rwa [show j r = (j q)⁻¹ from hr, inv_mul_cancel_left] at this
  have hUo : ∀ k, IsOpen (U k) := fun k => by
    have : U k = ⋃ p : N × T, (fun x => j p * x) ⁻¹' W k := by ext x; simp [U]
    rw [this]
    exact isOpen_iUnion fun p => (hWo k).preimage (continuous_const_mul _)
  have hcov : ∀ x, ∃ k, x ∈ U k := fun x => by
    obtain ⟨k, hk⟩ := K.exists_mem x
    exact ⟨k, (1, 1), by simpa [j] using K.subset_interior_succ k hk⟩
  let P : ℕ → Set H := disjointed U
  have hPm : ∀ k, MeasurableSet (P k) := MeasurableSet.disjointed fun k => (hUo k).measurableSet
  have hP : ∀ k q x, j q * x ∈ P k ↔ x ∈ P k := fun k q x => by
    simp only [P, disjointed_eq_inter_compl, mem_inter_iff, mem_iInter, mem_compl_iff, hU]
  have hPcov : ∀ x, ∃ k, x ∈ P k := fun x => by
    have : x ∈ ⋃ k, P k := by rw [iUnion_disjointed]; exact mem_iUnion.2 (hcov x)
    exact mem_iUnion.1 this
  have hPd : ∀ k k' x, x ∈ P k → x ∈ P k' → k = k' := fun k k' x h h' => by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_disjointed U hne) h h'
  let h : H → ℝ≥0∞ := fun x => ∑' k, (P k).indicator ((W k).indicator 1) x
  have hh : Measurable h := Measurable.tsum fun k =>
    (measurable_one.indicator (hWo k).measurableSet).indicator (hPm k)
  have hval : ∀ k x, x ∈ P k → ∀ q, h (j q * x) = (W k).indicator 1 (j q * x) := by
    intro k x hx q
    have hx' := (hP k q x).2 hx
    refine (tsum_eq_single k fun k' hk' => ?_).trans (indicator_of_mem hx' _)
    exact indicator_of_notMem (fun h' => hk' (hPd _ _ _ h' hx')) _
  let g : H → ℝ≥0∞ := fun x => ∫⁻ n : N, h (n * x) ∂dn
  let I : H → ℝ≥0∞ := fun x => ∫⁻ t : T, g (t * x) ∂dt
  have hg : Measurable g := measurable_fiber hh
  have hI : Measurable I := measurable_fiber hg
  have hgN : ∀ n ∈ N, ∀ x, g (n * x) = g x := fun n hn x => by
    simpa [g, mul_assoc] using lintegral_mul_right_eq_self (μ := dn) (fun m : N => h (m * x)) ⟨n, hn⟩
  have hIN : ∀ n ∈ N, ∀ x, I (n * x) = I x := fun n hn x => by
    refine lintegral_congr fun t => ?_
    have e : (t : H) * (n * x) = ((t : H) * n * (t : H)⁻¹) * (t * x) := by group
    rw [e, hgN _ (hnorm _ t.2 _ hn)]
  have hIT : ∀ s ∈ T, ∀ x, I (s * x) = I x := fun s hs x => by
    simpa [I, mul_assoc] using lintegral_mul_right_eq_self (μ := dt) (fun t : T => g (t * x)) ⟨s, hs⟩
  have hIprod : ∀ x, I x = ∫⁻ p, h (j p * x) ∂(dn.prod dt) := fun x => by
    rw [lintegral_prod_symm (fun p => h (j p * x)) (hh.comp (hjc.measurable.mul_const x)).aemeasurable]
    simp [I, g, j, mul_assoc]
  have hcpt : ∀ k x, IsCompact ((fun y => y * x) ⁻¹' K (k + 1)) := fun k x => by
    have := (Homeomorph.mulRight x).isCompact_preimage.2 (K.isCompact (k + 1))
    simpa using this
  have hIpos : ∀ x, I x ≠ 0 ∧ I x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set E := (fun p => j p * x) ⁻¹' W k with hEdef
    have hE : IsOpen E := (hWo k).preimage (hjc.mul continuous_const)
    have e : I x = dn.prod dt E := by
      rw [hIprod, ← lintegral_indicator_one hE.measurableSet]
      exact lintegral_congr fun p => by rw [hval k x hk p]; rfl
    obtain ⟨p, hp⟩ := disjointed_subset U k hk
    refine ⟨e ▸ hE.measure_ne_zero _ ⟨p, hp⟩, e ▸ ?_⟩
    refine (measure_mono (μ := dn.prod dt) (s := E) (t := j ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))) ?_).trans_lt
      (hj.isCompact_preimage (hcpt k x)).measure_lt_top |>.ne
    intro q hq
    exact interior_subset (s := K (k + 1)) hq
  have hgfin : ∀ x, g x ≠ ∞ := fun x => by
    obtain ⟨k, hk⟩ := hPcov x
    set C : Set N := (↑) ⁻¹' ((fun y => y * x) ⁻¹' K (k + 1))
    have hC : IsCompact C := hN.isClosedEmbedding_subtypeVal.isCompact_preimage (hcpt k x)
    refine ne_of_lt (lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := dn)))
    rw [← lintegral_indicator_one hC.measurableSet]
    refine lintegral_mono fun n => ?_
    have e : h ((n : H) * x) = (W k).indicator 1 ((n : H) * x) := by
      simpa [j] using hval k x hk (n, 1)
    rw [e]
    by_cases hn : (n : H) * x ∈ W k
    · rw [indicator_of_mem hn, indicator_of_mem (show n ∈ C from interior_subset (s := K (k + 1)) hn)]; exact le_rfl
    · rw [indicator_of_notMem hn]; exact zero_le
  refine ⟨fun x => g x * (I x)⁻¹, hg.mul hI.inv, fun x => ENNReal.mul_ne_top (hgfin x)
    (ENNReal.inv_ne_top.2 (hIpos x).1), fun n hn x => by simp only [hgN n hn, hIN n hn], fun x => ?_⟩
  have e : ∀ t : T, g (t * x) * (I (t * x))⁻¹ = g (t * x) * (I x)⁻¹ := fun t => by rw [hIT _ t.2]
  simp_rw [e]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (hIpos x).1)]
  exact ENNReal.mul_inv_cancel (hIpos x).1 (hIpos x).2

end Weight

theorem quotInt_eq_zero_of_integral_coset_eq_zero : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T →
    (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) →
    ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure]
    [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ →
    Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  intro H _ _ _ _ _ _ _ _ T N hT hN hc hnorm hj dh _ dt _ dn _ _ φ hφ hφT hint h0
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_of_isMulCommutative dt
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  obtain ⟨β, hβm, hβf, hβN, hβ1⟩ := exists_weight_nt T N hT hN hnorm hj dt dn
  have hν : quotMeas T dt dh = (dh.withDensity β).map (mk T) :=
    (isQuotMeasure_quotMeas dt dh hT).eq_map hβm hβ1
  have hlt : ∀ᵐ x ∂dh, β x < ∞ := .of_forall fun x => lt_top_iff_ne_top.2 (hβf x)
  have hD : Measurable (descend T φ) := measurable_descend hφT hφ
  have hcomp : descend T φ ∘ mk T = φ := funext hφT.descend_mk
  have hφβ : Integrable φ (dh.withDensity β) := by
    rw [hν] at hint
    have := (integrable_map_measure hD.aestronglyMeasurable measurable_mk.aemeasurable).1 hint
    rwa [hcomp] at this
  have hF : Integrable (fun x => (β x).toReal • φ x) dh :=
    (integrable_withDensity_iff_integrable_smul' hβm hlt).1 hφβ
  have e1 : quotInt T dt dh φ = ∫ x, (β x).toReal • φ x ∂dh := by
    rw [quotInt, hν, integral_map measurable_mk.aemeasurable hD.aestronglyMeasurable,
      ← integral_withDensity_eq_integral_toReal_smul hβm hlt]
    exact integral_congr_ae (.of_forall fun x => hφT.descend_mk x)
  have hW := (weil_integral (dt := dn) hN hF).2
  have e2 : (fun x => ∫ n : N, (β (n * x)).toReal • φ (n * x) ∂dn) = fun _ => (0 : ℂ) := funext fun x => by
    have e : ∀ n : N, (β (n * x)).toReal • φ (n * x) = (β x).toReal • φ (n * x) := fun n => by
      rw [hβN _ n.2 x]
    simp_rw [e]
    rw [integral_smul, h0 x, smul_zero]
  rw [e1, ← hW.2, e2]
  simp [quotInt, descend]

end GlobalTheory.Orb
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.typePrime_large_and_one_mod_sixteen_q_d : ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → ∀ k : Fin 2, Module.finrank ℚ D.host.E * D.R.r + 1 < D.host.g k ∧ GlobalTheory.BadShare.PrimeOK (D.host.g k) D.host.q D.host.d := by
  first | exact @GlobalTheory.TypePrimeSize.typePrime_large_and_ok | exact GlobalTheory.TypePrimeSize.typePrime_large_and_ok | (intros; apply GlobalTheory.TypePrimeSize.typePrime_large_and_ok <;> assumption)
end
