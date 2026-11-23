module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle247
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalComponentAtPlaceDetermined
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle245
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle101
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.InducesOfIsInduced
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle006
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle233
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle266
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle269
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle234
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle244
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902

@[expose] public section

section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChoiceRead.exists_stC_choice_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi, c.ch.twI = ch.twI := by
  intro hCo hCW hHM hPr hSer hL
  refine (_root_.GlobalTheory.T.local_component_at_place_determined_alt hCo hCW hHM hPr hSer hL).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok
  have hc := H P x l ch tp hxi hpsi hQ hk hside hok
  choose e u hb hl hth using hc
  let G : ∀ v, (Dof x).what₂.muAt v ≠ (Dof x).what₂.mu0 → ∀ i : Fin (Dof x).R.m,
      (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1) :=
    fun v hv i => (((u v hv i)⁻¹ : (FractionRing (ch.Oe v))ˣ) : FractionRing (ch.Oe v)) • e v hv i
  have HB := GlobalTheory.ChoiceRead.pick_prop ch G (fun v j E => GlobalTheory.ChoiceRead.BasisAt ch v j E)
    (fun v hv i => (hb v hv i).smul _)
  have HL := GlobalTheory.ChoiceRead.pick_prop ch G
    (fun v j E => Submodule.span (ch.Oe v) (E '' GlobalTheory.ChoiceRead.latS v j) = GlobalTheory.ChoiceRead.latT ch v j)
    (fun v hv i => GlobalTheory.ChoiceRead.LatAt.smul_inv _ (hl v hv i))
  refine ⟨⟨GlobalTheory.ChoiceRead.withE ch (GlobalTheory.ChoiceRead.pick ch G) HB HL, GlobalTheory.ChoiceRead.tupWithE tp _ HB HL, hxi, hpsi, hQ, hk,
    GlobalTheory.ChoiceRead.choiceSide_withE hside _ HB HL, hok, ?_⟩, rfl⟩
  refine GlobalTheory.ChoiceRead.emtTheta_withE _ HB HL fun v i hv => ?_
  rw [GlobalTheory.ChoiceRead.pick_eq ch G v hv i]
  exact (hth v hv i).smul_inv _
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nonGalois_exists_choice_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∃ c : _root_.GlobalTheory.HeightCounting.HeightCountingCharacterData l.mt l.b T.k T.psi, c.ch.twI = ch.twI := by
  first | exact @_root_.GlobalTheory.ChoiceRead.exists_stC_choice_alt | exact _root_.GlobalTheory.ChoiceRead.exists_stC_choice_alt | (intros; apply _root_.GlobalTheory.ChoiceRead.exists_stC_choice_alt <;> assumption)
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS.Prod
open GlobalTheory GlobalTheory.GalFirstClause Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
theorem core_data_of_point (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {a : ℕ}
    (π : D.naut.CG a) [IsCMField D.host.E] (π₀ : CuspSub D.host.E a)
    (hmk : CG.mk π₀ = (P.cg.e a π).1) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar (maximalRealSubfield D.host.E)} {r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (D.host.E →+* Qbar l) → Multiset ℤ} (H : _root_.UpperTheory.GalS.IsGalUAlt π₀ χ ι r wt HT) :
    (∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))) := by
  have hloc0 : ∀ w : PlE D.host, P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w) := fun w => by
    rw [P.cg.loc, hmk]
    rfl
  have haw : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) := fun w hl => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
    rw [P.T.tw, hloc0, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ]
    exact H.aw hl (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL _) hσ
  exact haw

theorem galRep_rankTwo_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CarUAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (i : D.nd.Loc) (a : ℕ), 2 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) ∧ (∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (D.naut.locG π w) → D.naut.IsdRW i ρ w ∧ (∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.jumpsInf i π τ) ∧ UpperTheory.GalN.CuspA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) := by
  intro hF hC hL D P i a ha π hc hr
  have := host_isCMField D.host
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (P.cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨r, wt, HT, H, hLG⟩ := hC D.host.E D.nd.Om (D.nd.l i) (D.naut.iotaQC i) a ha π₀ hc₀ hr₀
  have hcont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i))) := Units.continuous_val.comp H.cont
  have hloc : ∀ (w : PlE D.host) (u : ℝ), P.T.e w (D.naut.lpTw (D.naut.locG π w) u) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw u := fun w u => by
    rw [P.T.tw, P.cg.loc, hmk]
    rfl
  have haw := _root_.UpperTheory.GalS.Prod.core_data_of_point hF hL D P π π₀ hmk H
  obtain ⟨K, ρ, hρc, hρ⟩ := finextRep (D.nd.l i) D.host.E D.nd.Om a r hcont
  have hncw : ∀ w, Nc D.nd D.naut (D.naut.locG π w) →
      NcW ((_root_.GlobalTheory.CuspRep.ParLawsT.locParT hL (CG.mk π₀) (D.nd.plOm.2 w)).lpTw ((1 - (a : ℝ)) / 2)) := fun w k => by
    rw [← hloc]; exact ncW_of_nc P.T ((nc_tw _ _).2 k)
  have hside : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), Nc D.nd D.naut (D.naut.locG π w) → P.wd.IsdRW (D.nd.l i) (D.naut.iotaQC i) r w ∧
      ∀ τ : D.host.E →+* Qbar (D.nd.l i), (∀ (A : ValuationSubring D.nd.Om), IsPlaceOver A w →
        ∀ (O : Type) [CommRing O] [Algebra ℤ_[D.nd.l i] O] [TopologicalSpace O]
          (Bw : LocBridge (D.nd.l i) D.host.E D.nd.Om (Dec (F := D.host.E) A) O),
          Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥Bw.LL.1, IsInduced Bw τ τ') →
        P.wd.jumpsW (D.nd.l i) (D.naut.iotaQC i) r τ = HT τ := by
    intro w hw hn
    have hni := _root_.UpperTheory.GalS.nice_of_loc_par hL hF (D.nd.plOm.2 w) (hncw w hn)
    obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge (D.nd.l i) D.host.E D.nd.Om w (D.nd.plOm.1 w) hw
      (D.nd.plOm.2 w)
    obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
    have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
    let LL' : FinExt (D.nd.l i) := supExt K Bw.LL
    have hK : K.1 ≤ LL'.1 := le_sup_left
    have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
    let ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
    have hρ' : mapRep (algebraMap ↥LL'.1 (Om (D.nd.l i))) ρ' = r := by
      rw [← hρ]
      ext g i k
      rfl
    have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin a) (Fin a) ↥LL'.1) := by
      have hi : Continuous (IntermediateField.inclusion hK) :=
        continuous_induced_rng.2 continuous_subtype_val
      exact hρc.matrix_map hi
    have hmodel : IsModel Bw (resDec D.nd.plOm.1 r w) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      ⟨hB, by rw [← hρ']; rfl⟩
    let φ : ↥(OL L0) →+* Qbar (D.nd.l i) := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
    have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om (D.nd.l i)) := fun x => (hBto x).symm
    have hcl := (P.wd.loc (D.nd.l i) (D.naut.iotaQC i) w hw _ Bw hind φ hφ).2 LL' hB a ρ' hρ'c
    rw [hρ'] at hcl
    have hab := H.above (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) ⟨D.locT (D.nd.l i)⟩ w (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw hind
    have hdR : Bw.IsdRE (D.loc (D.nd.l i)) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
      (hmodel.isdRAt_iff (D.loc (D.nd.l i))).1 (hab.deRham hni)
    refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
    obtain ⟨τ₀, hτ₀⟩ := hτ _ (D.nd.plOm.2 w) _ Bw hind
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
    have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
    have hJ := hab.jumps hni τ LL' τ'' hτ''
    ext n
    apply Nat.cast_injective (R := ℤ)
    rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc (D.nd.l i)) hmodel hτ'' hJ n]
  refine ⟨r, hcont, H.ss, fun w hw => ?_, fun w hw hn => ⟨?_, fun τ hτw => ?_, ?_⟩⟩
  · refine relW_of_aw P.T ?_
    rw [(P.wdOf i a r w).1, P.wd.away _ _ r w hw]
    exact haw w hw
  · exact ((P.wdOf i a r w).2.2.2.1).2 (hside w hw hn).1
  · obtain ⟨w', hw', hτ⟩ := existsIsInduced (D.nd.l i) D.host.E D.nd.Om τ
    obtain rfl : w' = w := by
      obtain ⟨LL, Bw', hj', -⟩ := P.wd.above _ (D.naut.iotaQC i) r w' hw'
      obtain ⟨τ', h'⟩ := hτ _ (D.nd.plOm.2 w') _ Bw' hj'
      exact HeightOneSpectrum.ext (Ideal.ext fun x => (induces_of_isInduced (D.nd.plOm.2 w') hj' h' x).symm.trans (hτw x))
    rw [(P.wdOf i a r w').2.2.2.2 τ, (hside w' hw' hn).2 τ hτ]
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights, D.naut.jumpsInf_def i π τ hr, hinf]
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  · rw [(P.wdOf i a r w).1]
    obtain ⟨LL, Bw', hj', he⟩ := P.wd.above _ (D.naut.iotaQC i) r w hw
    obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hF _ _ π₀ w
    have h2 := hLG (D.loc _) (D.locA _)
      ⟨D.locT _⟩ w hw (D.nd.plOm.1 w) (D.nd.plOm.2 w) _ Bw' hj' σ₀ hσ₀ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w))
    refine cuspA_of_ab P.T (by rw [D.naut.lpDim_tw, D.naut.locG_dim]; omega) ?_
    have e2 : _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (algNorm σ₀) =
        P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) := by
      rw [_root_.GlobalTheory.GalOfCusp.rec_algNorm_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)) σ₀, hloc, _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ₀ (D.nd.plOm.2 w)]
      rfl
    rw [he, ← e2]
    exact h2 (by rw [e2]; exact ncW_of_nc P.T ((nc_tw _ _).2 hn))
theorem automorphic_galois_admissible_of_theta_local_inputs (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hC : _root_.UpperTheory.GalS.CarUAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    AutomorphicGaloisAdmissible D.nd D.naut := by
  intro i
  refine ⟨fun a ha π hc hr => ?_, fun a π hr => _root_.GlobalTheory.GalClose.purity_alt hPr.clo hL D P a π hr, fun χ s hs => ?_⟩
  · rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · obtain rfl : a = 1 := by omega
      obtain ⟨ρ, c, s, o, u⟩ := _root_.GlobalTheory.GalClose.rankOne_galois_closure_geometric_alt hPr hL D P i π hr
      refine ⟨ρ, c, s, fun w hw => RelW.of_eq (o w hw).1, fun w hw _ => ⟨(u w hw).1, (u w hw).2.1, UpperTheory.GalN.CuspA.of_eq (u w hw).2.2⟩, fun _ w => ?_⟩
      by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
      · exact (u w hw).2.2
      · exact (o w hw).1
    · obtain ⟨ρ, c, s, o, u⟩ := _root_.UpperTheory.GalS.Prod.galRep_rankTwo_alt hPr.fin hC hL D P i a ha2 π hc hr
      exact ⟨ρ, c, s, o, fun w hw k => u w hw (k.resolve_left (by omega)), fun e => absurd e (by omega)⟩
  · exact _root_.GlobalTheory.T.exists_galois_character_of_algebraic_alt hPr.fin hPr.art hPr.chA hPr.chP hL D P i χ s hs
end UpperTheory.GalS.Prod
end
end
end
