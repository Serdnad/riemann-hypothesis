module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle575
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.jetMap_coeffSpace_of_jetStepPartitionTriples : ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (a b : ℕ), a < b → ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
  first | exact @GlobalTheory.ColNorms.jetInVV_of_stepWeights | exact GlobalTheory.ColNorms.jetInVV_of_stepWeights | (intros; apply GlobalTheory.ColNorms.jetInVV_of_stepWeights <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.weil_representation_preserves_schwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      M.co.rho ψ γ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  first | exact @GlobalTheory.HeisSchA.rho_mem_schA | exact GlobalTheory.HeisSchA.rho_mem_schA | (intros; apply GlobalTheory.HeisSchA.rho_mem_schA <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RestPure

theorem evFin_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (v : Pl (F := F)) (i : κ) :
    evFin F v (z i) = 0 := by

  have hu : evI F (pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v 1 = 1
    exact map_one _
  have h := congrFun (hz _ hu) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  have h2 := congrArg (evFin F v) h
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem rest_evI_finprod : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ f : SInf F κ, Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  intro F _ _ κ _ φ hφ hcof f
  refine ⟨fun x z hz => ?_, ?_⟩
  ·
    have hc : ∀ v i, evFin F v ((x + z) i) = evFin F v (x i) := fun v i => by
      rw [Pi.add_apply, map_add (f := _), evFin_eq_zero z hz v i, add_zero]
    simp only [hc]
  ·
    have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
        SB (κ → FiniteAdeleRing (𝓞 F) F) :=
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
        GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩
    show _ ∈ Submodule.span ℂ _
    exact Submodule.subset_span ⟨f, _, hg, rfl⟩

end GlobalTheory.RestPure
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.NuGood

theorem not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h v hv t k hk hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl (F := F))) := by
    intro hmem
    exact hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.T.unramified_character_at_uniformizer F E X.ν v t hunr] at hpow
  have hHecke : IsHecke F E X.ν := by
    refine ⟨?_, fun x => ?_⟩
    · exact (h.chars.heckeα.1.div' h.chars.heckeβ.1 :)
    · rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.T.hecke_character_of_idele_class F E σ h.base.cm X.ν hHecke
  have hexp : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
    intro z hz
    have h1 := h.chars.expα z hz
    have h2 := h.chars.expβ z hz
    show (((X.α z / X.β z : Circle)) : ℂ) = _
    rw [Circle.coe_div, h1, h2, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
    have hne' : piInf (B.emb w) z / (‖piInf (B.emb w) z‖ : ℂ) ≠ 0 :=
      div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne))
    rw [zpow_sub₀ hne']
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.T.split_prime_degree_one F E (splitPrime t) (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.T.hecke_value_not_finite_order F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ hexp) (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

end GlobalTheory.NuGood
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaPosIso

theorem disc (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ D ∈ nhds (0 : κ → AF F), ∀ ξ : κ → F, (fun i => algebraMap F (AF F) (ξ i)) ∈ D → ξ = 0 := by
  have hd := GroundTheory.Global.discreteTopology_principalSubgroup F
  have ho : IsOpen ({0} : Set (AdeleRing.principalSubgroup (𝓞 F) F)) := isOpen_discrete _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp ho
  refine ⟨Set.pi Set.univ fun _ => t, set_pi_mem_nhds Set.finite_univ fun _ _ => ht.mem_nhds ?_, ?_⟩
  · have h0 : ((0 : AdeleRing.principalSubgroup (𝓞 F) F) : AF F) ∈ t := by
      have : (0 : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := by rw [hpre]; rfl
      exact this
    simpa using h0
  · intro ξ hξ
    funext i
    have hm : algebraMap F (AF F) (ξ i) ∈ AdeleRing.principalSubgroup (𝓞 F) F := ⟨ξ i, rfl⟩
    have : (⟨_, hm⟩ : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := hξ i (Set.mem_univ _)
    rw [hpre] at this
    have h2 : algebraMap F (AF F) (ξ i) = 0 := congrArg Subtype.val this
    exact (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (h2.trans (map_zero _).symm)



theorem exists_theta_re_nonneg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    (∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2) →
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ Φ ∈ schA F κ, Continuous (fun w => thetaSum F (schr ψ w Φ)) ∧
      (∀ s ∈ S, 0 ≤ (thetaSum F (schr ψ s Φ)).re) ∧ 0 < (thetaSum F (schr ψ 0 Φ)).re := by
  intro F _ _ ψ hψ κ _ S hiso hspan
  classical
  obtain ⟨P, Q, hP, hQ, hker⟩ := GlobalTheory.T.exists_rational_projection_section_isotropicSpan F κ S hspan
  obtain ⟨D, hD, hDξ⟩ := disc F κ
  set PA := P.map (algebraMap F (AF F)) with hPA
  set QA := Q.map (algebraMap F (AF F)) with hQA
  obtain ⟨g, hgdef⟩ : ∃ g : (κ → AF F) → ℂ, g = fun x => ψ (⅟(2 : AF F) * (x ⬝ᵥ (QA *ᵥ x))) := ⟨_, rfl⟩
  have hg : Continuous g := by
    rw [hgdef]
    exact hψ.1.comp (continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))
  have hg0 : 0 < (g 0).re := by simp [hgdef]
  obtain ⟨V₀, hV₀, hq⟩ := exists_nhds_zero_quarter hD
  obtain ⟨V, hV, hVm⟩ : ∃ V ∈ nhds (0 : κ → AF F), ∀ x ∈ V, x ∈ V₀ ∧ -x ∈ V₀ ∧ PA *ᵥ x ∈ D ∧ 0 < (g x).re := by
    open scoped Pointwise in
    refine ⟨((V₀ ∩ -V₀) ∩ (fun x => PA *ᵥ x) ⁻¹' D) ∩ {x | 0 < (g x).re}, ?_, fun x hx => ⟨hx.1.1.1, Set.mem_neg.mp hx.1.1.2, hx.1.2, hx.2⟩⟩
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hV₀ (neg_mem_nhds_zero _ hV₀)) ?_) ?_
    · exact (continuous_const.matrix_mulVec continuous_id).tendsto' (0 : κ → AF F) 0 (by simp) hD
    · exact ((Complex.continuous_re.comp hg).tendsto 0).eventually (lt_mem_nhds hg0)
  obtain ⟨Φ, hΦS, hΦc, hΦV, hΦr, hΦ0⟩ := GlobalTheory.T.exists_nonneg_adelicSchwartz_bump_test F κ V hV
  have hsub : ∀ ξ ξ' : κ → F, (fun i => algebraMap F (AF F) ((ξ - ξ') i)) =
      (fun i => algebraMap F (AF F) (ξ i)) - (fun i => algebraMap F (AF F) (ξ' i)) := by
    intro ξ ξ'; funext i; simp [map_sub]
  have KEY : ∀ ξ : κ → F, ∀ v₁ ∈ V, ∀ v₂ ∈ V, ∀ v₃ ∈ V, ∀ v₄ ∈ V,
      (fun i => algebraMap F (AF F) (ξ i)) = v₁ - v₂ - (v₃ - v₄) → ξ = 0 := by
    intro ξ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ he
    apply hDξ
    rw [he, show v₁ - v₂ - (v₃ - v₄) = v₁ + -v₂ + -v₃ + v₄ by abel]
    exact hq (hVm _ h₁).1 (hVm _ h₂).2.1 (hVm _ h₃).2.1 (hVm _ h₄).1
  have hV0 : (0 : κ → AF F) ∈ V := mem_of_mem_nhds hV
  have LOC : ∀ a₀ : κ → AF F, ∃ ξ₀ : κ → F, ∀ᶠ a in nhds a₀, ∀ ξ : κ → F, ξ ≠ ξ₀ →
      Φ ((fun i => algebraMap F (AF F) (ξ i)) + a) = 0 := by
    intro a₀
    have hnear : ∀ᶠ a in nhds a₀, a - a₀ ∈ V :=
      (continuous_id.sub continuous_const).tendsto' a₀ 0 (sub_self a₀) hV
    by_cases h : ∃ ξ₀ : κ → F, ∃ v₁ ∈ V, ∃ v₂ ∈ V, (fun i => algebraMap F (AF F) (ξ₀ i)) + a₀ = v₁ - v₂
    · obtain ⟨ξ₀, v₁, h₁, v₂, h₂, he⟩ := h
      refine ⟨ξ₀, ?_⟩
      filter_upwards [hnear] with a ha ξ hne
      by_contra hz
      apply hne
      rw [← sub_eq_zero]
      refine KEY _ _ (hΦV _ hz) _ ha _ h₁ _ h₂ ?_
      rw [hsub, ← he]; abel
    · refine ⟨0, ?_⟩
      filter_upwards [hnear] with a ha ξ _
      by_contra hz
      exact h ⟨ξ, _, hΦV _ hz, _, ha, by abel⟩
  have THETA : ∀ w : (κ → AF F) × (κ → AF F), ∃ ξ₀ : κ → F, ∀ᶠ w' in nhds w,
      thetaSum F (schr ψ w' Φ) = ψ ((fun i => algebraMap F (AF F) (ξ₀ i)) ⬝ᵥ w'.2 + ⅟(2 : AF F) * (w'.1 ⬝ᵥ w'.2)) *
        Φ ((fun i => algebraMap F (AF F) (ξ₀ i)) + w'.1) := by
    intro w
    obtain ⟨ξ₀, h⟩ := LOC w.1
    refine ⟨ξ₀, ?_⟩
    filter_upwards [(continuous_fst.tendsto w).eventually h] with w' hw'
    exact tsum_eq_single ξ₀ fun ξ hne => mul_eq_zero_of_right _ (hw' ξ hne)
  have htwo : ⅟(2 : AF F) = algebraMap F (AF F) (2⁻¹ : F) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨Φ, hΦS, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun w => ?_
    obtain ⟨ξ₀, h⟩ := THETA w
    refine ContinuousAt.congr ?_ (h.mono fun _ h => h.symm)
    refine Continuous.continuousAt ?_
    exact (hψ.1.comp ((continuous_const.dotProduct continuous_snd).add
      (continuous_const.mul (continuous_fst.dotProduct continuous_snd)))).mul
      (hΦc.comp (continuous_const.add continuous_fst))
  · intro s hs
    obtain ⟨ξ₀, h⟩ := THETA s
    rw [h.self_of_nhds]
    set e : κ → AF F := fun i => algebraMap F (AF F) (ξ₀ i) with he
    by_cases hz : Φ (e + s.1) = 0
    · simp [hz]
    have hx : e + s.1 ∈ V := hΦV _ hz
    have hP0 : P *ᵥ ξ₀ = 0 := by
      apply hDξ
      have h1 := (hVm _ hx).2.2.1
      simp only [Matrix.mulVec_add, hP s hs, add_zero] at h1
      convert h1 using 1
      funext i
      exact RingHom.map_mulVec _ _ _ _
    set f : κ → AF F := fun i => algebraMap F (AF F) ((Q *ᵥ ξ₀) i) with hf
    have hef : (e, f) ∈ S := hker ξ₀ hP0
    have hac : (s.1, QA *ᵥ s.1) ∈ S := hQ s hs
    have hQe : QA *ᵥ e = f := by
      funext i
      exact (RingHom.map_mulVec _ _ _ _).symm
    have h1 := hiso s hs _ hac
    have h2 := hiso _ hef s hs
    have h3 := hiso _ hef _ hac
    simp only at h1 h2 h3
    have hrat : e ⬝ᵥ f = algebraMap F (AF F) (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)) := (RingHom.map_dotProduct _ _ _).symm
    have hinv : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
    have phase : e ⬝ᵥ s.2 + ⅟(2 : AF F) * (s.1 ⬝ᵥ s.2) =
        ⅟(2 : AF F) * ((e + s.1) ⬝ᵥ (QA *ᵥ (e + s.1))) + algebraMap F (AF F) (-(2⁻¹ * (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)))) := by
      rw [Matrix.mulVec_add, hQe, add_dotProduct, dotProduct_add, dotProduct_add, map_neg, map_mul, ← htwo, ← hrat]
      linear_combination h2 - ⅟(2 : AF F) * h3 - ⅟(2 : AF F) * h1 - (s.1 ⬝ᵥ f) * hinv
    rw [phase, AddChar.map_add_eq_mul, hψ.2.1, mul_one, Complex.mul_re, (hΦr _).1, mul_zero, sub_zero]
    have hpos := (hVm _ hx).2.2.2
    rw [hgdef] at hpos
    exact mul_nonneg (le_of_lt hpos) (hΦr _).2
  · have hz : ∀ ξ : κ → F, ξ ≠ 0 → Φ ((fun i => algebraMap F (AF F) (ξ i)) + (0 : (κ → AF F) × (κ → AF F)).1) = 0 := by
      intro ξ hne
      by_contra hz
      exact hne (KEY ξ _ (hΦV _ hz) 0 hV0 0 hV0 0 hV0 (by simp))
    have e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0 := by funext i; simp
    have hsum : thetaSum F (schr ψ 0 Φ) = schr ψ 0 Φ (fun i => algebraMap F (AF F) ((0 : κ → F) i)) :=
      tsum_eq_single 0 fun ξ hne => mul_eq_zero_of_right _ (hz ξ hne)
    rw [hsum, e0]
    simp only [schr, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul, hΦ0, Complex.one_re]
    norm_num

end GlobalTheory.ThetaPosIso
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.TameHeckeIntegral

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_onId (E : Type) [Field E] [NumberField E] (ψ : HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ)
    (n : I → ℤ) (hinf : ψ.HasInf φs n) (ht : ∀ v, ψ.TameAt v) (b : ℕ) (hb : b ≠ 0)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) (cc : Ideal (𝓞 E)) (hcc : cc ≠ ⊥)
    (hcop : cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤) :
    UnitOff (Ideal.absNorm cc) ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ) := by
  classical
  have hb0 : (b : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hfin : {w | ¬ ψ.UnrAt w}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(b : 𝓞 E)}) (by simpa using hb0)).subset fun w hw => ?_
    have hbw : (b : 𝓞 E) ∈ w.asIdeal := by
      by_contra h
      exact hw (hu w h)
    show w.asIdeal ∣ Ideal.span {(b : 𝓞 E)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hbw
  have hcc0 : cc ≠ 0 := hcc
  unfold HChar.onId
  refine finprod_induction (fun u : ℂˣ => UnitOff (Ideal.absNorm cc) (u : ℂ)) (by simpa using unitOff_one _)
    (fun x y hx hy => by simpa [Units.val_mul] using unitOff_mul hx hy) fun v => ?_
  show UnitOff _ (((ψ.val v ^ FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ)) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]
  by_cases hdv : v.asIdeal ∣ cc
  · have hle : cc ≤ v.asIdeal := Ideal.le_of_dvd hdv
    have hbv : (b : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top (by
      rw [eq_top_iff, ← hcop]
      exact sup_le hle (by rw [Ideal.span_singleton_le_iff_mem]; exact h))
    have hq : ((Ideal.absNorm cc : ℕ) : 𝓞 E) ∈ v.asIdeal := hle (Ideal.absNorm_mem cc)
    exact unitOff_zpow (GlobalTheory.ValUnit.unitOff_val E ψ I φs n v _ hinf hfin ht (hu v hbv) hq) _
  · have h0 : FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0 := by
      rw [FractionalIdeal.count_coe E v hcc0, Nat.cast_eq_zero]
      by_contra h
      exact hdv ((Associates.count_ne_zero_iff_dvd hcc0 (HeightOneSpectrum.prime v).irreducible).1 h)
    rw [h0, zpow_zero]
    exact unitOff_one _

theorem isIntegral_absNorm_pow_mul_onId : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  intro E _ _ ψ I _ φs n hinf ht b hb hu cc hcc hcop
  obtain ⟨_, K, hK, _⟩ := unitOff_onId E ψ I φs n hinf ht b hb hu cc hcc hcop
  exact ⟨K, hK⟩

end GlobalTheory.TameHeckeIntegral
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.NormHasseFixed

theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval A p) = aeval (cT σ A) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
    unfold cT
    rw [Matrix.map_smul' _ _ _ (fun x y => map_mul σ x y), Matrix.map_pow, Matrix.transpose_smul, Matrix.transpose_pow]

theorem aeval_mulVec {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} (N : Matrix (Fin n) (Fin n) L)
    (μ : L) (v : Fin n → L) (hv : N *ᵥ v = μ • v) (p : K[X]) : (aeval N p) *ᵥ v = aeval μ p • v := by
  have hpow : ∀ k : ℕ, (N ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, Matrix.smul_mulVec, hpow,
      smul_assoc]

theorem aeval_inv_map_eq {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (γ : GL (Fin n) E)
    (hγ : cT σ γ.val * 1 * γ.val = 1) (m : E[X]) (hm : cT σ (aeval γ.val m) = aeval γ.val m)
    {L : Type} [Field L] [Algebra E L] (α : L) (hα0 : α ≠ 0) (hroot : aeval α γ.val.charpoly = 0) :
    aeval α⁻¹ (m.map σ) = aeval α m := by
  have hU' : cT σ γ.val = (γ⁻¹).val := by
    have h := congrArg (· * (γ⁻¹).val) hγ
    simpa [Matrix.mul_assoc] using h
  rw [aeval_def, ← eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : (γ.val.map (algebraMap E L)) *ᵥ v = α • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hBA : ((γ⁻¹).val.map (algebraMap E L)) * (γ.val.map (algebraMap E L)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBv : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ v = α⁻¹ • v := by
    have h : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ ((γ.val.map (algebraMap E L)) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [hAv, Matrix.mulVec_smul] at h
    conv_rhs => rw [← h, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hmap : ∀ (M : Matrix (Fin n) (Fin n) E) (p : E[X]),
      (aeval M p).map (algebraMap E L) = aeval (M.map (algebraMap E L)) p := by
    intro M p
    have h := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E L)) M p
    have e : (⇑(Algebra.ofId E L) : E → L) = algebraMap E L := rfl
    simpa [AlgHom.mapMatrix_apply, e] using h.symm
  have h1 : (cT σ (aeval γ.val m)).map (algebraMap E L) *ᵥ v = (aeval γ.val m).map (algebraMap E L) *ᵥ v := by
    rw [hm]
  rw [cT_aeval, hU', hmap, hmap, aeval_mulVec _ _ v hBv, aeval_mulVec _ _ v hAv] at h1
  exact smul_left_injective L hv0 h1


open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField in
theorem invol_mk_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ.val m) = aeval γ.val m → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ hγ _ m hm r Q hQ
  have hγ' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1 := hγ
  have hroot : aeval (AdjoinRoot.root Q.1) γ.val.charpoly = 0 := by
    obtain ⟨c, hc⟩ := hQ
    rw [hc, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have h := aeval_inv_map_eq (IsCMField.complexConj E).toRingEquiv.toRingHom γ hγ' m hm (AdjoinRoot.root Q.1) (root_ne_zero Q) hroot
  rw [aeval_def, eval₂_map, AdjoinRoot.aeval_eq] at h
  refine Eq.trans ?_ h
  show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
    (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
  rw [AdjoinRoot.lift_mk]
  rfl

end GlobalTheory.NormHasseFixed
end
end
