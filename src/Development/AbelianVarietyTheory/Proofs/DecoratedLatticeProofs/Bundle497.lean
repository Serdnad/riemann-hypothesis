module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle489
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle492
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle490
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle632
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle018
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumChangeAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProof
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.EulerProd

open Filter Topology

theorem limit_eq_prod_mul {ι : Type} (S : Finset ι) (f : ι → ℂ) (I : Finset ι → ℂ) {P J : ℂ}
    (hP : HasProd (fun v : {v : ι // v ∉ (S : Set ι)} => f v.1) P) (hJ : Tendsto I atTop (𝓝 J))
    (h : ∀ T U : Finset ι, Disjoint S T → (∀ u, u ∈ U ↔ u ∈ S ∨ u ∈ T) → I U = (∏ v ∈ T, f v) * I S) :
    J = P * I S := by
  classical
  let e : {v : ι // v ∉ (S : Set ι)} ↪ ι := Function.Embedding.subtype _
  have ht : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => S ∪ T.map e) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop (b.subtype fun v => v ∉ (S : Set ι))).mono fun T hT u hu => ?_
    by_cases hS : u ∈ S
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨u, hS⟩, hT (Finset.mem_subtype.2 hu), rfl⟩)
  have h1 := hJ.comp ht
  have h2 : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => (∏ v ∈ T, f v.1) * I S) atTop (𝓝 (P * I S)) :=
    Tendsto.mul_const _ hP
  refine tendsto_nhds_unique h1 (h2.congr fun T => ?_)
  rw [Function.comp_apply, h (T.map e) _ ?_ fun u => Finset.mem_union, Finset.prod_map]
  · rfl
  · refine Finset.disjoint_left.2 fun u hu hu' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hu'
    exact w.2 hu

theorem bounded_of_isParamFun (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} (hB : ParamBoundOn D (fun _ => True))
    {θ : InfFam D} {A : HSp D} {cA : CptF A} {L : Lat A} (hθ : IsInfFam θ) (hL : IsSelfDualC A L)
    (m : Measure (GA D A)) (hm : m.IsHaarMeasure) {Sf : Finset (FinPl D)} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA)
    {par : GlobalTheory.LFun.Fam D.host.E} (hpar : GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u par) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sf : Set (FinPl D))) par A.rank ((A.rank : ℝ) / 2) := by
  intro w hw
  have hv : w.under (𝓞 D.host.F) ∉ Sf := hw
  have h0 : u ≠ 0 := (hpar _ hw w rfl).ne_zero
  have hs : SphFun A L Sf u := fun v hv k hk g => by
    obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v := by
      have := v.isMaximal
      obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
        (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
          (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
      refine ⟨⟨Q, hQ.isPrime, fun hb => v.ne_bot ?_⟩, HeightOneSpectrum.ext e⟩
      rw [← e, hb, Ideal.under_bot]
    exact (congrFun ((hpar v hv w' hw').mem_fixed ⟨k, hk⟩) g).trans (by simp)
  have hc := GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified hP D θ A cA L hθ m hm Sf u hu u hu par hpar hs _ hv 1 (map_one _)
  have h1 : MemL2Quotient (GQ A) m u := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu).1
  have hpos := petersson_self_pos h1 (mem_cuspForms.1 hu).1.1.toIsAutFun.cont h0
  have hne : rcoef m u u (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) ≠ 0 := by
    have e : rTr A (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) u = u := funext fun g => by
      simp only [rTr, map_one, mul_one]
    rw [rcoef, e]
    intro h
    rw [h] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨h2, h3⟩ := hB A L hL _ trivial par _ hc hne w rfl
  exact ⟨h2.le, h3⟩

theorem eulerRight : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) →
    ParamBoundOn D (fun _ => True) → EulerRight D := by
  intro hP D hS hZ hB ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph
    s hs hint
  have ha : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  have hb := bounded_of_isParamFun hP hB hp.setting.2.2.2.1 hU.sdA m hm hu₁ hpar
  have hL := GlobalTheory.T.hasProd_partialLFunctionTwistedByChar_local_factors D Sf par χB _ _ hb (s + 1 / 2) (by
    have : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by simp
    rw [this]; linarith)
  obtain ⟨hd0, hdv, hd⟩ := (GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank).2 s (by linarith)
  refine limit_eq_prod_mul Sf
    (fun v => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s)
    (fun S => ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) ?_
    (GlobalTheory.T.tendsto_setIntegral_unramifiedOutsideOpenSubset D A LA hU.sdA m _ hint) fun T U hT hTU =>
      GlobalTheory.T.setIntegral_unramified_places_union_eq_local_factors hP D hS hZ ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par
        hpar hsph s (by linarith) hint Sf T le_rfl hT U hTU
  exact (Tendsto.div hL hd hd0).congr fun T => (Finset.prod_div_distrib _ _).symm

end GlobalTheory.Core.Rk.EulerProd

end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP
variable {D : D7} (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D))

theorem hgtL_eq_prod (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g = (∏ w, hgtArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf _ _ w) a)
      (ioH _ D.sp.cm.sig (gram_hdbl A) (projArch D.sp.cm.sig A.gram w g, 1))) *
      ∏ᶠ v, hgtFin D.sp.cm.sig (dblSp A).gram L v (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1)) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  simpa only [hgtL, io, proj_ioH, projArch_ioH, map_one] using
    hI.hgtAd_eq (isCMExt_host D) (io A (g, 1))

theorem isOpen_openOff (hL : IsSelfDualC A L) (Sf : Finset (FinPl D)) : IsOpen (openOff A L Sf) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  let H : Subgroup (GA D A) := ⨅ (v) (_ : v ∉ Sf), (stabLoc D.sp.cm.sig A.gram L v).comap (proj D.sp.cm.sig A.gram v)
  have hH : (H : Set (GA D A)) = openOff A L Sf := by
    ext g
    simp [H, openOff, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [← hH]
  refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) (fun g hg => ?_) (isOpen_levelOpen _ _ _)
  simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact fun v _ => (mem_levelOpen.1 hg) v

theorem continuous_hgtL (hL : IsSelfDualC A L) (ha : IsMaj A a) : Continuous (hgtL A L a) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  exact (hI.continuous_hgtH continuous_absE (isCompact_KAd (isCMExt_host D))).comp
    ((continuous_io A).comp (continuous_id.prodMk continuous_const))

theorem hgtL_le_one (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g ≤ 1 := by
  rw [hgtL_eq_prod A L a hL ha g]
  refine mul_le_one' (Finset.prod_le_one' fun w _ => ?_) ?_
  · have := GlobalTheory.T.doublingHeightAtRealPlace_le_one D A a ha w (projArch D.sp.cm.sig A.gram w g)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW] using this
  · by_cases hf : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
        (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))).Finite
    · rw [finprod_eq_prod _ hf]
      exact Finset.prod_le_one' fun v _ => GlobalTheory.T.siegelHeightFinitePlace_doublingEmbedding_le_one D A L hL v _
    · rw [finprod_of_infinite_mulSupport hf]

theorem hgtL_eq_prod_off (hL : IsSelfDualC A L) (ha : IsMaj A a) (Sf : Finset (FinPl D)) (g : GA D A)
    (hg : g ∈ openOff A L Sf) : (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) *
      ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  rw [hgtL_eq_prod A L a hL ha g]
  have hsub : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
      (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))) ⊆ (Sf : Set (FinPl D)) := by
    intro v hv
    by_contra hvS
    exact hv (hgtH_of_mem (continuous_absEv v) (isCompact_KFin v)
      ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hg v hvS, one_mem _⟩))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  push_cast
  rfl

theorem hgtL_props : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → Continuous (hgtL A L a) ∧ (∀ g, 0 < hgtL A L a g ∧ hgtL A L a g ≤ 1) ∧ ∀ (Sf : Finset (FinPl D)), IsOpen (openOff A L Sf) ∧ ∀ g ∈ openOff A L Sf, (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  intro D A L a hL ha
  exact ⟨continuous_hgtL A L a hL ha, fun g => ⟨hgtH_pos _, hgtL_le_one A L a hL ha g⟩,
    fun Sf => ⟨isOpen_openOff A L hL Sf, fun g hg => hgtL_eq_prod_off A L a hL ha Sf g hg⟩⟩

end GlobalTheory.Core.Rk.IP
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.linearModel_twistPlace_in_thetaFunctions : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P, ∃ (W : Submodule ℂ (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ)) (hW : ∀ g h, ∀ u ∈ W, GlobalTheory.ParHecke.omTwo μS μT g h u ∈ W) (hΦ : datum ξl⁻¹ ∈ W) (T : W →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ ∀ g h (u : W), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩ := by
  first | exact @GlobalTheory.ChainTw.linModel_theta | exact GlobalTheory.ChainTw.linModel_theta | (intros; apply GlobalTheory.ChainTw.linModel_theta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevProd.OffTwist



theorem bc_prV_eq_one (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (κ : GA D S)
    (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hg : GlobalTheory.AdForm.finM S hn κ = g.1) (v w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v)
    (hκ : κ ∈ GlobalTheory.FinPl.grpAt S (· = v)) : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g = 1 := by
  subst hn
  have h1 : GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ = 1 :=
    ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff S _ κ).1 hκ).2 w hw
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram w κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ)).val i j =
        GlobalTheory.StabConjIndex.swap w ((GlobalTheory.AdelicU.matHom (Fv D.host.F w) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV w (g.1 i j) = GlobalTheory.StabConjIndex.swap w (GlobalTheory.AdelicU.compFin _ _ w _)
    rw [← hij]
    exact GlobalTheory.FamTrace.prV_toEAf_eq_swap D w _
  rw [hE, h1, map_one]



theorem exists_mem_level (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (K : StepLevel D.host.F D.host.E (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (t : 𝓞 D.host.E) (ht : t ∣ (T : 𝓞 D.host.E))
    (hLb : ∀ x, x ∈ K.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r))
    (L : GlobalTheory.FinPl.Lat S) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hb : v ∉ bad) (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal)
    (κ : GA D S) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S (· = v)) (hm : GlobalTheory.FinPl.Moves S κ L L (· = v)) :
    ∃ x : K.U, x.1.1 = GlobalTheory.AdForm.finM S hn κ := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ Formalism.UG.UPts (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM S hn κ = g.1 := by
    obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D S n hn
    have hf := GlobalTheory.FinPl.SetCut.grpAt_le_GfC S _ hκ
    exact ⟨(e ⟨κ, hf⟩).1, (e ⟨κ, hf⟩).2, (he ⟨κ, hf⟩).symm⟩
  refine ⟨⟨g, (K.U_eq _).2 ⟨hgU, fun w => ?_⟩⟩, hg.symm⟩
  by_cases hw : w = v
  · subst hw
    subst hn
    have key : ∀ j i : Fin S.rank, ∃ r : 𝓞 D.host.E,
        (Pi.single j (T : D.host.E) : Fin S.rank → D.host.E) i = (r : D.host.E) ∧ t ∣ r := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact ⟨T, (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) T).symm, ht⟩
      · exact ⟨0, rfl, dvd_zero _⟩
    have e := GlobalTheory.FamTrace.levelVL_eq_of_std (sigD D) (S.gram.reindex (finCongr rfl) (finCongr rfl)) (Lb := K.Lb) (Λ := L) hT
      (fun x hx j => let ⟨r, hr, _⟩ := (hLb x).1 hx j; ⟨r, hr⟩)
      (fun j => (hLb _).2 fun i => let ⟨r, hr, hd⟩ := key j i; ⟨r, hr, fun _ => hd⟩)
      (fun x hx => (hL x).1 hx) (fun j => (hL _).2 fun i => let ⟨r, hr, _⟩ := key j i; ⟨r, hr⟩)
    rw [K.Uloc_hyp w hb hT, e]
    exact GlobalTheory.FamTrace.bc_prV_mem_levelVL_of_moves D S _ rfl L L hfg (fun _ => Iff.rfl) κ g hg w hm
  · rw [bc_prV_eq_one D S n hn κ g hg v w hw hκ]
    exact one_mem _


end GlobalTheory.LevProd.OffTwist
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge.SuppLev



theorem bc_prV_eq_one_of_not (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (κ : GA D S)
    (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hg : GlobalTheory.AdForm.finM S hn κ = g.1) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : HeightOneSpectrum (𝓞 D.host.F))
    (hw : ¬ P w) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P) : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g = 1 := by
  subst hn
  have h1 : GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ = 1 :=
    ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff S _ κ).1 hκ).2 w hw
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram w κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ)).val i j =
        GlobalTheory.StabConjIndex.swap w ((GlobalTheory.AdelicU.matHom (Fv D.host.F w) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV w (g.1 i j) = GlobalTheory.StabConjIndex.swap w (GlobalTheory.AdelicU.compFin _ _ w _)
    rw [← hij]
    exact GlobalTheory.FamTrace.prV_toEAf_eq_swap D w _
  rw [hE, h1, map_one]



theorem exists_mem_level_set (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (K : StepLevel D.host.F D.host.E (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (t : 𝓞 D.host.E) (ht : t ∣ (T : 𝓞 D.host.E))
    (hLb : ∀ x, x ∈ K.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r))
    (L : GlobalTheory.FinPl.Lat S) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (κ : GA D S) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P)
    (hP : ∀ v, P v → v ∉ bad ∧ (T : 𝓞 D.host.F) ∉ v.asIdeal ∧ GlobalTheory.FinPl.Moves S κ L L (· = v)) :
    ∃ x : K.U, x.1.1 = GlobalTheory.AdForm.finM S hn κ := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ Formalism.UG.UPts (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM S hn κ = g.1 := by
    obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D S n hn
    have hf := GlobalTheory.FinPl.SetCut.grpAt_le_GfC S _ hκ
    exact ⟨(e ⟨κ, hf⟩).1, (e ⟨κ, hf⟩).2, (he ⟨κ, hf⟩).symm⟩
  refine ⟨⟨g, (K.U_eq _).2 ⟨hgU, fun w => ?_⟩⟩, hg.symm⟩
  by_cases hw : P w
  · obtain ⟨hb, hT, hm⟩ := hP w hw
    subst hn
    have key : ∀ j i : Fin S.rank, ∃ r : 𝓞 D.host.E,
        (Pi.single j (T : D.host.E) : Fin S.rank → D.host.E) i = (r : D.host.E) ∧ t ∣ r := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact ⟨T, (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) T).symm, ht⟩
      · exact ⟨0, rfl, dvd_zero _⟩
    have e := GlobalTheory.FamTrace.levelVL_eq_of_std (sigD D) (S.gram.reindex (finCongr rfl) (finCongr rfl)) (Lb := K.Lb) (Λ := L) hT
      (fun x hx j => let ⟨r, hr, _⟩ := (hLb x).1 hx j; ⟨r, hr⟩)
      (fun j => (hLb _).2 fun i => let ⟨r, hr, hd⟩ := key j i; ⟨r, hr, fun _ => hd⟩)
      (fun x hx => (hL x).1 hx) (fun j => (hL _).2 fun i => let ⟨r, hr, _⟩ := key j i; ⟨r, hr⟩)
    rw [K.Uloc_hyp w hb hT, e]
    exact GlobalTheory.FamTrace.bc_prV_mem_levelVL_of_moves D S _ rfl L L hfg (fun _ => Iff.rfl) κ g hg w hm
  · rw [bc_prV_eq_one_of_not D S n hn κ g hg P w hw hκ]
    exact one_mem _

end GlobalTheory.PenBridge.SuppLev


end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacFixP

theorem idAt_eq_bot {D : D7} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) : idAt D P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  refine GlobalTheory.FinPlLoc.eq_zero_of_comp x hx.1 fun w => ?_
  exact (Submodule.mem_iInf _).1 hx.2 ⟨w, hP w⟩

theorem eq_one_of_grpAt {D : D7} {S : HSp D} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {κ : GA D S}
    (h : κ ∈ grpAt S P) : κ = 1 := by
  unfold grpAt congGrp at h
  rw [idAt_eq_bot hP, MonoidHom.mem_ker, MonoidHom.comp_apply] at h
  have h2 : matHom S κ = 1 := by
    apply Units.ext
    ext i j
    have := congrArg (fun g : GL (Fin S.rank) (AE D ⧸ (⊥ : Ideal (AE D))) => g.val i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [Units.val_one]
    rw [Matrix.one_apply] at this ⊢
    have h1 : ((if i = j then 1 else 0 : AE D ⧸ (⊥ : Ideal (AE D)))) = Ideal.Quotient.mk ⊥ (if i = j then 1 else 0) := by
      split_ifs <;> simp
    rw [h1, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at this
    exact this
  unfold matHom at h2
  exact Subgroup.subtype_injective _ (h2.trans (map_one _).symm)

theorem vac_fix_on : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT P hP f hf κ κ' hκ hκ'
  by_cases hex : ∃ v, P v
  · obtain ⟨v, hv⟩ := hex
    obtain ⟨hS, hT, -⟩ := hP v hv
    exact GlobalTheory.T.selfDualLatticeStabilizers_fix_weilVacuum_on_placeSet D ψ S T χS χT om hW LS LT hS hT P (fun w hw => (hP w hw).2.2) f hf κ κ' hκ hκ'
  · push_neg at hex
    rw [eq_one_of_grpAt hex hκ.1, eq_one_of_grpAt hex hκ'.1, Prod.mk_one_one, map_one]
    rfl

end GlobalTheory.VacFixP
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D)), IsClosed (grpAt V (· ∈ Q) : Set (GA D V)) ∧ IsClosed (grpAt V (· ∉ Q) : Set (GA D V)) ∧ grpAt V (· ∈ Q) ≤ GfC V ∧ grpAt V (· ∉ Q) ≤ GfC V ∧ (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b = b * a) ∧ (∃ e : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V, ∀ p, (e p : GA D V) = p.1 * p.2) ∧ (∀ P P' : Pl D → Prop, (∀ p, P p → ¬ P' p) → grpAt V P ≤ grpOff V P') ∧ (∀ P : Pl D → Prop, GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p) ∧ (∀ (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, (∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P))) ∧ ∀ κ, InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  first | exact @GlobalTheory.FinPl.SetCut.grp_split | exact GlobalTheory.FinPl.SetCut.grp_split | (intros; apply GlobalTheory.FinPl.SetCut.grp_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.scalarForm_transportedColumn_stepZero_standard : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  first | exact @GlobalTheory.Fam.rd_zero_std | exact GlobalTheory.Fam.rd_zero_std | (intros; apply GlobalTheory.Fam.rd_zero_std <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.vacuumChangeAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.RebaseAll D := by
  first | exact @GlobalTheory.FinPl.RebaseProof.rebaseAll | exact GlobalTheory.FinPl.RebaseProof.rebaseAll | (intros; apply GlobalTheory.FinPl.RebaseProof.rebaseAll <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.gluedPlaceSourceConstant_proof : ∀ D : D7, GlobalTheory.FinPl.SourceExact D := by
  first | exact @GlobalTheory.FinPl.sourceExact | exact GlobalTheory.FinPl.sourceExact | (intros; apply GlobalTheory.FinPl.sourceExact <;> assumption)
end
