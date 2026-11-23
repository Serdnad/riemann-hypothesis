module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Formalism.LocalRingCardinality.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle755
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle072
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle743
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle106
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle776
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle769
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle771
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedOfAcrisPeriods
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.LiftPoint

noncomputable section

namespace GlobalTheory.ResLoc

theorem exists_point (D : D7) (M : MtFam D) (HT : HeckeTied D M) (AV : AVTied D M) (NL : NormalizedLocalCompatibility D M) (hstd : HeckeStdTw NL.B)
    (i : D.nd.Loc) (P : D.naut.AV i) : ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      ∃ (hμ' : D.nd.mu i = D.nd.mu i') (hj' : D.nd.j i = D.nd.j i') (P' : D.naut.AV i') (x' : D.nd.X i'),
        (D.naut.typeV i P).map (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ' hj').toLinearMap = D.naut.typeV i' P' ∧
        D.naut.ptV i' P' = some x' := by
  classical
  have h : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hj1 := (D.nd.j_range i).1
  have hj2 := (D.nd.j_range i).2
  have hw : LocPl D (D.nd.j i) (D.nd.w i) := locPl_of_mem D h
  have hμ : D.nd.mu i = D.what₂.muTw (D.nd.w i) := D.nd.mu_w i
  obtain ⟨y0, hy0, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have hr0 : (M.loc i).real y0 ≠ 0 := fun h0 => hy0ne ((M.loc i).real_inj (h0.trans (map_zero _).symm))

  have hinjO : Function.Injective (iotaO D.nd D.naut i) := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i).injective.comp ((D.naut.iotaQ i).injective.comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))))
  have hiotaC : ∀ z, iotaO D.nd D.naut i z = NL.iotaC _ _ (NL.phO _ _ i h z) := NL.iotaC_coh _ _ i h
  have hinjC : Function.Injective (NL.iotaC (D.nd.j i) (D.nd.w i)) := by
    intro a b hab
    have e2 : (NL.phO _ _ i h).symm a = (NL.phO _ _ i h).symm b := hinjO (by
      rw [hiotaC, hiotaC, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab)
    simpa using congrArg (NL.phO _ _ i h) e2
  let φ : FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = NL.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (NL.phK _ _ i h).toRingHom = (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, NL.phK_alg, hφalg]
    rw [← hiotaC]
    rfl
  have hφ : ∀ y, φ (NL.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← NL.phK_emb _ _ i h y, ← D.naut.iota_LL i y]
    exact congrArg (fun f : FractionRing (D.nd.O i) →+* ℂ => f (D.nd.embK i y)) hφK

  have HS := GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M HT AV i
  have key : ∀ v k, GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k →
      ∃ κ : NL.B.Oc (D.nd.j i) (D.nd.w i), ∀ (s : SplitPlace D.host.E)
        (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
        ∀ y ∈ D.naut.typeV i P, NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = φ (algebraMap _ _ κ) • (M.loc i).real y := by
    intro v k hvk
    obtain ⟨hv, hk1, hk2⟩ := (genAt_iff NL h v k).2 hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
    obtain ⟨c, hcP⟩ := HS P v k s ϖ hv hc hu hk1 hk2
    obtain ⟨tC, htC1, htC2⟩ := tC_exists D M NL.B hstd (D.nd.j i) (D.nd.w i) (D.nd.mu i) hμ hj1 hj2 hw φ hφ v k hvk
    have ht0 : tC y0 = c • y0 := by
      apply (M.loc i).real_inj
      have e0 := htC2 s ϖ hc hu (tN_lin D M HT NL h v k s ϖ hvk hc hu) y0
      change NG.tN (M.loc i).J s ϖ k ((M.loc i).real y0) = (M.loc i).real (tC y0) at e0
      rw [← e0, hcP y0 hy0, map_smul]
    obtain ⟨κ, hκ⟩ := htC1 c y0 hy0ne ht0
    refine ⟨κ, fun s' ϖ' hc' hu' y hy => ?_⟩
    obtain ⟨c', hcP'⟩ := HS P v k s' ϖ' hv hc' hu' hk1 hk2
    have e1 := htC2 s' ϖ' hc' hu' (tN_lin D M HT NL h v k s' ϖ' hvk hc' hu') y0
    change NG.tN (M.loc i).J s' ϖ' k ((M.loc i).real y0) = (M.loc i).real (tC y0) at e1
    rw [hcP' y0 hy0, ht0, map_smul] at e1
    have hcc : c' = c := smul_left_injective ℂ hr0 e1
    rw [hcP' y hy, hcc, hκ]
  let κF : PlE D.host → ℕ → NL.B.Oc (D.nd.j i) (D.nd.w i) := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k then
      Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ∀ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
        ∀ y ∈ D.naut.typeV i P, NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) =
          φ (algebraMap _ _ (κF v k)) • (M.loc i).real y := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)

  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M NL.B (D.nd.j i) (D.nd.w i) (D.nd.mu i) hj1 hj2 hμ φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y0 hy0ne (by
      intro v k hvk
      obtain ⟨hv, -, -⟩ := (genAt_iff NL h v k).2 hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
      exact ⟨s, ϖ, hc, hu, tN_lin D M HT NL h v k s ϖ hvk hc hu, hκF v k hvk s ϖ hc hu y0 hy0⟩)
  have hinjK : Function.Injective (algebraMap (NL.B.Oc (D.nd.j i) (D.nd.w i))
      (FractionRing (NL.B.Oc (D.nd.j i) (D.nd.w i)))) := IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens NL.B (D.nd.j i) (D.nd.w i)) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar (D.nd.w i)) (NL.B.Qc (D.nd.j i) (D.nd.w i)) v k),
      ψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have h1 := hψ ⟨NL.B.hK _ _ v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have h2 := he v k hvk
    change NL.B.hK _ _ v k e = _ at h1
    rw [h2] at h1
    exact (smul_left_injective _ hene h1).symm
  have hW : NCov.W (heckeAlg NL.B _ _) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3

  obtain ⟨i', hi', hmx⟩ := NL.mx_all (D.nd.j i) (D.nd.w i) hj1 hj2 (D.nd.w_tw i) (NCov.cls ψ)
    (NCov.cls_isMaximal ψ)
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hμ' : D.nd.mu i = D.nd.mu i' := by rw [D.nd.mu_w i, D.nd.mu_w i', e2]
  have hj' : D.nd.j i = D.nd.j i' := e1.symm
  let x' : D.nd.X i' := (NL.ptX _ _ i' hi').symm ⟨ψ, hmx.symm, hW⟩
  obtain ⟨P', hP'⟩ := GlobalTheory.EtaJoin.TypeSum.typeV_of_transport AV i' hμ' hj' hj1 hj2 (AV.S i P) (AV.irr i P)
    (by
      change (NG.isoTyp (M.loc i).wt.ρ (AV.S i P)).comap (M.loc i).real ≠ ⊥
      rw [← AV.typeV i P]; exact D.naut.typeV_ne i P)
  change Submodule.map _ ((NG.isoTyp (M.loc i).wt.ρ (AV.S i P)).comap (M.loc i).real) = _ at hP'
  rw [← AV.typeV i P] at hP'
  refine ⟨i', hi', hμ', hj', P', x', hP', ?_⟩
  refine ptV_of_transport AV i' P' x' hμ' hj' hj1 hj2 _ hP' ?_
  intro v k s ϖ hv' hc hu hk1 hk2 y hy
  have hvk := (genAt_iff NL hi' v k).1 ⟨hv', hk1, hk2⟩
  change NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = _ • (M.loc i).real y
  rw [hκF v k hvk s ϖ hc hu y hy]
  congr 1
  rw [NL.iotaC_coh _ _ i' hi', NL.ptX_hT _ _ i' hi' x' v k hvk]
  show φ (algebraMap _ _ (κF v k)) = NL.iotaC _ _ (((NL.ptX _ _ i' hi') ((NL.ptX _ _ i' hi').symm ⟨ψ, hmx.symm, hW⟩)).1 _)
  rw [Equiv.apply_symm_apply, hφalg]
  show NL.iotaC _ _ (κF v k) = NL.iotaC _ _ (ψ ⟨NL.B.hK _ _ v k, _⟩)
  rw [hψv v k hvk]

theorem pairs_of_transport {D : D7} (i' : D.nd.Loc) (P' : D.naut.AV i') {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = D.nd.mu i')
    (hj : j = D.nd.j i') (V : Submodule ℂ (D.what₂.Mt μ j))
    (hV : V.map (GlobalTheory.EtaJoin.TypeSum.eqvMt hμ hj).toLinearMap = D.naut.typeV i' P') {σ : D.what₂.FT}
    (h : ∃ f ∈ D.what₂.isot j σ, ∃ F ∈ V, inner ℂ F (D.what₂.thetaT μ j f) ≠ 0) : GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' := by
  subst hμ; subst hj
  rw [GlobalTheory.EtaJoin.TypeSum.map_eqvMt_self] at hV
  subst hV
  exact h

theorem exists_pair_point (D : D7) (M : MtFam D) (HT : HeckeTied D M) (AV : AVTied D M) (NL : NormalizedLocalCompatibility D M)
    (hstd : HeckeStdTw NL.B) (i : D.nd.Loc) (σ : D.what₂.FT)
    (h : ∃ f ∈ D.what₂.isot (D.nd.j i) σ, D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f ≠ 0) :
    ∃ (i' : D.nd.Loc) (P' : D.naut.AV i') (x' : D.nd.X i'), D.nd.j i' = D.nd.j i ∧ D.nd.w i' = D.nd.w i ∧
      GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  obtain ⟨f, hf, hθ⟩ := h
  obtain ⟨P, F, hF, hFf⟩ := GlobalTheory.Proof.HoweThetaLiftComponents.exists_inner_ne_zero (D.naut.typeV i) (D.naut.typeV_top i) _ hθ
  obtain ⟨i', hi', hμ, hj, P', x', hP', hx'⟩ := exists_point D M HT AV NL hstd i P
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem _ _ i').1 hi'
  exact ⟨i', P', x', e1, e2, pairs_of_transport i' P' hμ hj _ hP' ⟨f, hf, F, hF, hFf⟩, hx'⟩

theorem exists_thetaT_ne {D : D7} (hd : DV.LamDef D) {μ : D.what₂.Tup} {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {σ : D.what₂.FT}
    (hσ : D.what₂.isot j σ ≠ ⊥) (hp : 0 < D.what₂.lamP μ j σ) : ∃ f ∈ D.what₂.isot j σ, D.what₂.thetaT μ j f ≠ 0 := by
  by_contra hn
  push Not at hn
  rw [hd μ j h1 h2 σ hσ, DV.lamTr_of_scalar D μ j σ 0 hσ fun x hx => by rw [hn x hx]; simp] at hp
  exact lt_irrefl _ hp

end GlobalTheory.ResLoc

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdjUp

theorem ip_eq_mul_integral_val : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
    IsUnitVec R i v → ∃ P : ℝ, 0 ≤ P ∧ ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL i v hv
  obtain ⟨-, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i

  set Q : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ) with hQ
  have hQc : (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) = (Q : ℂ) := by
    rw [hQ, Complex.ofReal_prod]; rfl

  have key : ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (Q : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
    intro y z
    obtain ⟨c, hc⟩ := hS hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 _ (hmem y) _ (hmem z)
    have hex : ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e y)
        ((R.HW i (sg0 D A)).e z) c := ⟨c, hc⟩
    have hv1 := (hex.choose_spec (fun ρ => v ρ) (fun ρ => v ρ)).2
    have hprod : (∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) = 1 := by
      refine Finset.prod_eq_one fun ρ _ => ?_
      rw [inner_self_eq_norm_sq_to_K, hv ρ]
      norm_num
    rw [hip, ipAt, hQc, ipM, dite_eq_left hex]
    unfold val
    rw [hv1, hprod, mul_one]
  by_cases h0 : 0 ≤ Q
  · exact ⟨Q, h0, key⟩
  ·
    refine ⟨0, le_rfl, fun y z => ?_⟩
    have hy : y = 0 := by
      have e1 := key y y
      have hnn : 0 ≤ ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) :=
        MeasureTheory.setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity)
      have hI : (∫ g in R.fdW i, star (val R i v y g) * val R i v y g ∂(R.νW i)) =
          ((∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only
        rw [Complex.ofReal_pow, ← Complex.conj_mul']
        rfl
      rw [hI] at e1
      have e2 : ‖y‖ ^ 2 = Q * ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) := by
        have := congrArg Complex.re e1
        rw [inner_self_eq_norm_sq_to_K] at this
        simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using this
      have hle : ‖y‖ ^ 2 ≤ 0 := by
        rw [e2]; exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 h0)) hnn
      have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
      exact norm_eq_zero.1 this
    rw [hy, inner_zero_left, Complex.ofReal_zero, zero_mul]

end GlobalTheory.AdjUp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PartsSpanProof

theorem exists_isFinIdem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v, IsFinIdem D v f := by
  rcases h with ⟨⟨⟨-, -, v, ε, hv, he⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hv, rfl⟩, -⟩
  · exact ⟨v, ε, hv, he⟩
  · exact ⟨v, ε, hv, rfl⟩

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]



theorem partsSpan : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i S, PartsSpan R i S := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF i S
  have hLP := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF i
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i
  obtain ⟨inj, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  let ι := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Wc D i)) //
    Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S
      x.1 x.2.1 x.2.2}
  have keep : ∀ x : ι, ∀ U ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) x.1.2.2 U ∈ R.Wall i (sg0 D A) := by
    rintro ⟨⟨P, d, B⟩, e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hB, hc⟩ U hU
    obtain ⟨v, hv⟩ := exists_isFinIdem hP
    exact GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall hLP v f hv α hα B hB hc U hU
  have hex : ∀ x : ι, ∃ h : Module.End ℂ (R.HW i (sg0 D A)).H, ∀ y,
      (R.HW i (sg0 D A)).e (h y) = heckeOn (R.MW i (sg0 D A)) x.1.2.2 ((R.HW i (sg0 D A)).e y) :=
    fun x => exists_lift _ inj _ fun y => hr ▸ keep x _ (hmem y)
  choose op hop using hex
  have hcomm : Formalism.L2.Col.PairComm op := fun x x' => by
    refine LinearMap.ext fun y => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hop, hop, hop, hop]
    exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (J := levW R i)
      (GlobalTheory.HeckeAdjoint.realUnif D _) x.2 x'.2 (hlv y v)
  have hadj : ∀ x : ι, ∃ x', op x' = LinearMap.adjoint (op x) := by
    intro x
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D x.1.1) x.2
    let x' : ι := ⟨(x.1.1, dualLab x.1.2.1, B'), hB'⟩
    refine ⟨x', ?_⟩
    rw [LinearMap.eq_adjoint_iff]
    intro a b
    rw [hip, hip, hop, hop]
    unfold ipAt
    congr 1
    exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab D (Wc D i) _ R.θ (R.MW i (sg0 D A)) (levW R i) _ S (R.νW i) (R.fdW i)
      hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 hS x.1.1 (dualLab x.1.2.1) B' x.1.2.2 hB'
      (by rw [dualLab_dualLab]; exact x.2) _ (hmem a) _ (hmem b) (keep x' _ (hmem a)) (keep x _ (hmem b))
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition op hcomm hadj
  classical
  unfold PartsSpan
  refine eq_top_iff.2 (h2 ▸ iSup_le fun y => ?_)
  refine le_iSup_of_le (fun P d => if h : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B then y ⟨(P, d, h.choose), h.choose_spec⟩ else 0) ?_
  intro x hx
  rw [h1, Submodule.mem_iInf] at hx
  show (R.HW i (sg0 D A)).e x ∈ partFull _ _ _ _ _ _
  unfold partFull
  refine Submodule.mem_inf.2 ⟨hmem x, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  have hE : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B := ⟨B, hB⟩
  rw [dite_eq_left hE]
  have e1 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d, hE.choose), hE.choose_spec⟩)
  have e2 := congrArg (R.HW i (sg0 D A)).e e1
  rw [hop, map_smul] at e2
  rw [← e2]
  exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.labelUnique (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D)
    P d B _ hB hE.choose_spec _ (hlv x v)

end GlobalTheory.PartsSpanProof

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.goodTypes_exclude_levelCharacter : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodNoChi R i t := by
  first | exact @GlobalTheory.GoodTypeNoChi.goodNoChi | exact GlobalTheory.GoodTypeNoChi.goodNoChi | (intros; apply GlobalTheory.GoodTypeNoChi.goodNoChi <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k k' : ℕ) (β β' : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → F.IsBeta m k' β' → ∀ i j, bk.E ^ m ∣ ((l : bk.S) ^ k' • β - (l : bk.S) ^ k • β') i j := by
  first | exact @GlobalTheory.BKLim.beta_unique | exact GlobalTheory.BKLim.beta_unique | (intros; apply GlobalTheory.BKLim.beta_unique <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistableSeed_module_lAdic_closed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  first | exact @GlobalTheory.BKLim.wseed_module_lAdic_closed | exact GlobalTheory.BKLim.wseed_module_lAdic_closed | (intros; apply GlobalTheory.BKLim.wseed_module_lAdic_closed <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.rel_galois_comparison_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  first | exact @GlobalTheory.BSP.Height.rel_gal | exact GlobalTheory.BSP.Height.rel_gal | (intros; apply GlobalTheory.BSP.Height.rel_gal <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_basis_of_etale_invariant_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (T A0 A0' : Matrix (Fin d) (Fin d) (WCb l)) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T.map (frobW l) = T * A0 → A0 * A0' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T) → Y.map (inclW l) = inclW l τ ^ N • T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → ∃ F : Pre bk N d ρ, F.T = T := by
  first | exact @GlobalTheory.BKLim.pre_of_etale | exact GlobalTheory.BKLim.pre_of_etale | (intros; apply GlobalTheory.BKLim.pre_of_etale; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  first | (exact @GlobalTheory.BKLim.BetaDiv.isBeta_div) | (exact GlobalTheory.BKLim.BetaDiv.isBeta_div) | (intros; apply GlobalTheory.BKLim.BetaDiv.isBeta_div  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_etale_OE_basis_of_isogenous_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ'' : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ) (f : Matrix (Fin d) (Fin d) (ℤ_[l])), f.det ≠ 0 → (∀ g, IsUnit (ρ'' g)) → (∀ g, f * ρ'' g = ρ g * f) → ∃ T'' P : Matrix (Fin d) (Fin d) (WCb l), IsUnit T'' ∧ (∀ i j, P i j ∈ bk.OE) ∧ zW f * T'' = F.T * P := by
  first | exact @GlobalTheory.EtBasis.main | exact GlobalTheory.EtBasis.main | (intros; apply GlobalTheory.EtBasis.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.latticeApproximation_mittagLeffler : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (tw.d' n) → bk.S, ∃ s' : Fin (tw.d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i := by
  first | (exact @GlobalTheory.BKLim.mittagLeffler_approx) | (exact GlobalTheory.BKLim.mittagLeffler_approx) | (intros; apply GlobalTheory.BKLim.mittagLeffler_approx  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistableSeed_of_acris_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), (F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m) → Nonempty (WSeed bk d ρ τ) := by
  first | exact @GlobalTheory.BKLim.wseed_of_periods | exact GlobalTheory.BKLim.wseed_of_periods | (intros; apply GlobalTheory.BKLim.wseed_of_periods <;> assumption)
end
