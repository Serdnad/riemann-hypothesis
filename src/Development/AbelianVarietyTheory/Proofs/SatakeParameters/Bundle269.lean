module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RtSumScalar

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rtSum_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (f' : GAf L n → W) (hf' : f' ∈ S') (hfix : ∀ κ ∈ K, NG.rt L n κ f' = f') :
    ∑ γ ∈ R, NG.rt L n γ f' = c • f' := by
  classical
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : GAf L n, ((T ⟨NG.rt L n h f, hS.stable h _ f.2⟩ : S') : GAf L n → W) = NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ K, NG.rt L n κ (f : GAf L n → W) = f := by
    intro κ hκ
    have h1 := hrt κ
    rw [hfix κ hκ] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨NG.rt L n γ f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f := by
    rw [Submodule.coe_sum]
  have hTσ : ((T σ : S') : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f' := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt γ
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem rtSum_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ K, NG.rt L n κ y = y := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ K, NG.rt L n κ z = z := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _), hyfix κ hκ] at e
        exact add_left_cancel e
      have e1 := rtSum_iso hS.1 haF.2 K R c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

end Main

theorem rtSum_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f) → ∀ f ∈ NG.isoTyp ρ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS K R c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact rtSum_finset_sum hS K R c hc t ht f hft hfix

end GlobalTheory.RtSumScalar
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceOver

theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem eq_or_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v →
    s.w = w ∨ IsConjPl D.host w s.w := by
  intro D s w hov
  let cO := IsCMField.ringOfIntegersComplexConj D.host.E
  have cc (x : 𝓞 D.host.E) : cO (cO x) = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
    exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)
  let Q : PlE D.host := {
    asIdeal := s.w.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
    isPrime := Ideal.comap_isPrime _ _
    ne_bot := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.w.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
      · show (cO : 𝓞 D.host.E →+* 𝓞 D.host.E) (cO y) ∈ s.w.asIdeal
        rw [RingHom.coe_coe, cc]; exact hy
      · intro h0
        apply hy0
        rw [← cc y, h0, map_zero] }
  have hQ (x : 𝓞 D.host.E) : x ∈ Q.asIdeal ↔ cO x ∈ s.w.asIdeal := Iff.rfl
  have he : w = s.w ∨ w = Q := by
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2⟩ := hne
    have nle : ∀ P : PlE D.host, w ≠ P → ¬ w.asIdeal ≤ P.asIdeal := fun P h hle =>
      h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top hle))
    obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle s.w h1)
    obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q h2)
    have key : ∃ x ∈ w.asIdeal, x ∉ s.w.asIdeal ∧ x ∉ Q.asIdeal := by
      by_cases haQ : a ∈ Q.asIdeal
      · by_cases hbP : b ∈ s.w.asIdeal
        · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
          · simpa using s.w.asIdeal.sub_mem h hbP
          · simpa using Q.asIdeal.sub_mem h haQ
        · exact ⟨b, hb, hbP, hbQ⟩
      · exact ⟨a, ha, haP, haQ⟩
    obtain ⟨x, hx, hxP, hxQ⟩ := key
    rw [hQ] at hxQ
    have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, cc, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
    rw [hov.trans s.w_under.symm, Ideal.mem_comap, hy] at hyw
    rcases s.w.isPrime.mem_or_mem hyw with h | h
    · exact hxP h
    · exact hxQ h
  rcases he with e | e
  · exact Or.inl e.symm
  · right
    intro x y hxy
    have hy : y = cO x := by
      apply RingOfIntegers.ext
      rw [hxy, IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
    rw [e, hQ, hy]

end GlobalTheory.SplitPlaceOver
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open Formalism.IndefR Formalism.IndefR.Mult Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.MinfCusp

theorem minf_val_autCusp : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : Formalism.BasicNotions.TH.HSp D}
    {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S),
    ∀ T ∈ principalLevelFrame.Minf θ P M, ∀ v : M.Vec, IsAutFunSm θ V (T v) ∧ IsCuspFun V (T v) := by
  intro D θ V S n P M T hT v
  obtain ⟨N, hN⟩ := (principalLevelFrame.mem_Minf (θ := θ) (P := P) (M := M)).1 hT
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hN
  exact ⟨h.aut v, h.cusp v⟩

end GlobalTheory.MinfCusp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem not_isSplitPl_of_isInertAt (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (h : Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp) : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  rintro ⟨x, hx, hy⟩
  have hc : (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    have key : ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) = ((a : ↥D.host.F) : D.host.E) := rfl
    have h0 := (D.host.conjE_mem_hostF_iff _).1 (a : ↥D.host.F).2
    show (D.host.conj ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E)) = _
    rw [key]; exact h0
  have hmem : NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x ∈ Pp.asIdeal := by
    unfold Formalism.UG.IsInertAt at h
    rw [← h] at hx ⊢
    have := Ideal.mem_map_of_mem (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)) hx
    rwa [Ideal.map_map, hc] at this
  exact hy _ rfl hmem

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.ThetaIntegralCont

theorem continuous_theta_integral_vector : ∀ {D : D7} (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    IsWeilDatumO ψ V W χS χT om → (∀ τ, (gramAt D V τ).PosDef) →
    ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO V W → ℂ)),
    (∀ x, IsThetaFunO ψ V W (L x)) → ∀ u : GA D V → X, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) →
    Continuous (fun g => ∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν) := by
  intro D ψ V W χS χT om hom hV ν 𝓕 hν h𝓕 X _ _ _ L hL u hu hinv
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact V hV
  let b := Module.finBasis ℂ X
  have e : ∀ g h, thetaKO om h g (L (u h)) = ∑ k, b.coord k (u h) * om (h, g) (L (b k)) 0 := by
    intro g h
    conv_lhs => rw [← b.sum_repr (u h)]

    simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  have hK : Continuous fun p : GA D W × GA D V => thetaKO om p.2 p.1 (L (u p.2)) := by
    simp only [e]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ ?_
    · exact (b.coord k).continuous_of_finiteDimensional.comp (hu.comp continuous_snd)
    · exact (hom.om_cont _ (hL (b k)) 0).comp (continuous_snd.prodMk continuous_fst)
  have hKinv : ∀ γ ∈ GQ V, ∀ g h, thetaKO om (γ * h) g (L (u (γ * h))) = thetaKO om h g (L (u h)) := by
    intro γ hγ g h
    have e : (γ * h, g) = ((γ, 1) : GA D V × GA D W) * (h, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [hinv γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hL _))
  exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ V) ν 𝓕 C h𝓕 hC hcov
    (fun g h => thetaKO om h g (L (u h))) hK hKinv

end GlobalTheory.ThetaIntegralCont
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowModCanon

open MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace
open scoped InnerProductSpace

theorem ipM_smul_measure {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (hne : SmNonzero M) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) {a : ℝ} (ha : 0 ≤ a) (T T' : MMap M)
    (h : ∃ c, IsMultIP M ν 𝓕 T T' c) :
    ipM M (ENNReal.ofReal a • ν) 𝓕 T T' = (a : ℂ) * ipM M ν 𝓕 T T' := by
  have h1 := ipM_spec M ν 𝓕 T T' h
  have h2 : IsMultIP M (ENNReal.ofReal a • ν) 𝓕 T T' ((a : ℂ) * ipM M ν 𝓕 T T') := by
    intro v v'
    obtain ⟨hi, he⟩ := h1 v v'
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn, Measure.restrict_smul]
      exact hi.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  have h3 := ipM_spec M _ 𝓕 T T' ⟨_, h2⟩
  choose w hw using hne
  have hw' : ∀ τ, (w τ : M.H τ) ≠ 0 := fun τ h => hw τ (Submodule.coe_eq_zero.1 h)
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hw' τ)
  exact hasPeterssonInner_unique M _ 𝓕 T T' w hv0 h3 h2

end GlobalTheory.RowModCanon

namespace GlobalTheory.RowModCanon

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie


end GlobalTheory.RowModCanon
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitPlaceConj

theorem isSplitPl_w : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  intro D s
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep D.host.E s
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) := rfl
  refine ⟨c e, (s.split_mem_ideal _).2 (by rw [hce]; exact he'), fun y hy hm => ?_⟩
  have hye : (y : D.host.E) = (e : D.host.E) := by
    rw [hy, hce, ← hc, IsCMField.complexConj_apply_apply]
  have h1 := (s.split_mem_ideal y).1 hm
  rw [hye, he] at h1
  exact lt_irrefl _ h1

end GlobalTheory.SplitPlaceConj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowUnitProof

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x, hx, hy⟩ := hw
  have hc : IsSplitPl D.host (GlobalTheory.SplitConjPlace.conjPlE w) := by
    refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E x, ?_, fun y hy' => ?_⟩
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]; exact hx
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
      apply hy
      rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, hy', hstar, IsCMField.coe_ringOfIntegersComplexConj,
        IsCMField.complexConj_apply_apply]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hc
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have h1 := hs (IsCMField.ringOfIntegersComplexConj D.host.E y) y (by
    rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply])
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO] at h1
  exact h1.symm

end GlobalTheory.RowUnitProof

namespace GlobalTheory.RowUnitProof

end GlobalTheory.RowUnitProof

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AutomorphismSplitting

theorem isCSD_inv' {R : Ranks} {H : Host R} {χ : HChar H.E} (h : IsCSD H χ) : IsCSD H χ⁻¹ :=
  ⟨fun w w' hw k => congrArg (·⁻¹) (h.1 w w' hw k), fun k => congrArg (·⁻¹) (h.2 k)⟩

theorem hasInf_inv {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L}
    (h : χ.HasInf φ (fun _ => 1)) : (χ⁻¹).HasInf φ (fun _ => -1) := by
  intro k
  have hk := h k
  show (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = _
  rw [Units.val_inv_eq_inv_val, hk, ← Finset.prod_inv_distrib]
  simp

end GlobalTheory.AutomorphismSplitting
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieFrob

theorem xi_eq_of_heq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (Tp : TupTied D C nch)
    (Tp' : TupTied D C' nch) (e : HEq Tp Tp') : Tp.xi = Tp'.xi := by
  subst h; cases e; rfl

end GlobalTheory.TieFrob
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDatumChars

theorem xi_eq_of_heq {D : D7} {C C' : Formalism.L2.Host.CharFrame D} {n : NChoice D} (h : C = C')
    (T : Formalism.L2.Host.TupTied D C n) (T' : Formalism.L2.Host.TupTied D C' n) (hT : HEq T T') : T.xi = T'.xi := by
  subst h; rw [eq_of_heq hT]

end GlobalTheory.WeilDatumChars
end
